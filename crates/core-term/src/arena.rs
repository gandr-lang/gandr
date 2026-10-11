//! The append-only core arena: the single owner of every core term and type
//! node, addressed by four typed `u32`-backed node ids.
//!
//! # Why an arena rather than owned trees
//!
//! A deep uniquely-owned tree still recurses on destruction, so an elaborator
//! that builds a deep term overflows the stack *dropping* it even when every
//! walk over it was iterative. The arena dissolves that obligation rather than
//! managing it: ids are `Copy`, teardown is a flat per-family vector drop with
//! no recursive drop glue, and the derived equality, hashing and debug
//! instances are shallow over ids.
//!
//! # Constructor discipline and wholesale truncation
//!
//! - **Constructor-only minting.** Opaque ids originate in [`CoreArena`]
//!   constructors. Callers supply live children from the same arena and keep
//!   family indices within their representable limit. Under that discipline,
//!   each same-family child precedes its parent; cross-family acyclicity
//!   follows from minting order, not numeric comparison. Constructors record
//!   ids but do not validate their provenance or allocation generation.
//! - **Wholesale truncation.** [`CoreArena::watermark`] snapshots the four
//!   family lengths and [`CoreArena::truncate_to`] restores them, so a pass's
//!   intermediates allocate past a mark and are dropped in one step afterwards.
//!
//! # The honest cost
//!
//! An id can name no current node or the same numeric slot in another arena.
//! Checked lookup rejects an out-of-bounds slot, not a foreign origin. A later
//! allocation can reuse a truncated slot, so the caller must discard ids and
//! edges to removed nodes rather than treating an id as a permanent identity.

use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Side;

use crate::classifier::Sort;
use crate::syntax::CompType;
use crate::syntax::Computation;
use crate::syntax::Value;
use crate::syntax::ValueType;
use crate::syntax::Zone;

/// The id of a [`Value`] node in a [`CoreArena`].
///
/// An arena-relative allocation index, valid while its node remains live.
/// With live children from the same arena and representable family indices,
/// a newly minted id exceeds its same-family children. Neither provenance
/// nor allocation generation is encoded; truncation can permit index reuse.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ValueId(u32);

/// The id of a [`Computation`] node in a [`CoreArena`].
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ComputationId(u32);

/// The id of a [`ValueType`] node in a [`CoreArena`].
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ValueTypeId(u32);

/// The id of a [`CompType`] node in a [`CoreArena`].
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CompTypeId(u32);

/// The number of nodes allocated in one arena family.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ArenaLength(usize);

/// The stored index of one node within its arena family.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ArenaIndex(u32);

/// Widen an arena length to the `u32` an id wraps, saturating at the ceiling.
///
/// # Specification
/// - requires: `length` is a family length within an arena.
/// - ensures: `|ret| ret.0 == u32::try_from(length.0).unwrap_or(u32::MAX)` —
///   the equal index below the `u32` ceiling. **At and above the ceiling every
///   further mint returns the same id and later nodes alias**, so the
///   saturation is a documented ceiling rather than a safe fallback.
/// - provides: the total, panic-free length-to-index widening. The requirement
///   stays prose: every `usize` an arena can reach is a family length, so a
///   predicate over the argument would state nothing.
/// - fails: never; saturation keeps the arithmetic total but cannot preserve
///   fresh allocation identity beyond the representable family-index limit.
///   Memory availability is not evidence that the limit cannot be reached.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — zero, an interior index and the u32 ceiling distinguish
///   round-trip identity from off-by-one and truncating conversions; an
///   over-ceiling usize, where representable, distinguishes saturation.
/// - witness: `arena::tests::index_boundaries_preserve_identity_or_saturate`
#[inline]
#[spec(ensures: |ret| ret.0 == u32::try_from(length.0).unwrap_or(u32::MAX))]
fn id_index(length: ArenaLength) -> ArenaIndex
{
    ArenaIndex(u32::try_from(length.0).unwrap_or(u32::MAX))
}

/// Narrow an id's index to the offset a checked vector read takes.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `|ret| ret.0 == usize::try_from(index.0).unwrap_or(usize::MAX)` —
///   the equal offset, lossless on every supported platform of at least 32
///   bits.
/// - provides: the total, panic-free index-to-offset narrowing.
/// - fails: never; it saturates at the offset ceiling, which a checked read
///   then rejects.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — zero, an interior index and the u32 ceiling distinguish
///   round-trip identity from off-by-one and truncating conversions; an
///   over-ceiling usize, where representable, distinguishes saturation.
/// - witness: `arena::tests::index_boundaries_preserve_identity_or_saturate`
#[inline]
#[spec(ensures: |ret| ret.0 == usize::try_from(index.0).unwrap_or(usize::MAX))]
fn id_offset(index: ArenaIndex) -> ArenaLength
{
    ArenaLength(usize::try_from(index.0).unwrap_or(usize::MAX))
}

/// A snapshot of the four family lengths.
///
/// Restoring an arena to a watermark drops exactly the nodes allocated after
/// it, as four flat vector truncations. The default is the empty arena's
/// watermark.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ArenaWatermark
{
    /// The [`Value`] family length.
    values: usize,
    /// The [`Computation`] family length.
    computations: usize,
    /// The [`ValueType`] family length.
    value_types: usize,
    /// The [`CompType`] family length.
    comp_types: usize,
}

/// The append-only arena owning every core term and type node of one run.
///
/// The four families are parallel append-only vectors and a node's children are
/// ids into the same arena, so cloning or dropping a whole arena is a flat
/// per-family vector operation, total on any term depth.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct CoreArena
{
    /// The value nodes, in allocation order, which is child-before-parent.
    values: Vec<Value>,
    /// The computation nodes.
    computations: Vec<Computation>,
    /// The value-type nodes.
    value_types: Vec<ValueType>,
    /// The computation-type nodes.
    comp_types: Vec<CompType>,
}

impl CoreArena
{
    /// The native rows carried by this arena, in allocation order with repeats.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn native_primitives(&self) -> impl Iterator<Item = crate::primitive::Primitive> + '_
    {
        self.values
            .iter()
            .filter_map(|value| match *value {
                | Value::Primitive { primitive, .. } => Some(primitive),
                | _ => None,
            })
            .chain(
                self.computations
                    .iter()
                    .filter_map(|computation| match *computation {
                        | Computation::Primitive { primitive, .. } => Some(primitive),
                        | _ => None,
                    }),
            )
    }
    /// An empty arena.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new() -> Self
    {
        Self::default()
    }

    /// The current watermark: the four family lengths.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn watermark(&self) -> ArenaWatermark
    {
        ArenaWatermark {
            values: self.values.len(),
            computations: self.computations.len(),
            value_types: self.value_types.len(),
            comp_types: self.comp_types.len(),
        }
    }

    /// Truncate every family back to `watermark`, dropping later allocations.
    ///
    /// # Specification
    /// - requires: retained graph content does not depend on nodes that the
    ///   truncation removes. A stale larger mark is admissible and does not
    ///   grow any family; discarded ids may still be queried for absence.
    /// - ensures: `self.watermark() == ArenaWatermark { values:
    ///   watermark.values.min(entry.values), computations:
    ///   watermark.computations.min(entry.computations), value_types:
    ///   watermark.value_types.min(entry.value_types), comp_types:
    ///   watermark.comp_types.min(entry.comp_types) }` — each family holds
    ///   exactly its watermark-many leading nodes, and a mark above the entry
    ///   lengths leaves that family where it was. Removed nodes no longer
    ///   resolve immediately after truncation; later allocation can reuse their
    ///   indices, so the caller discards the corresponding ids.
    /// - provides: the wholesale truncation a per-run arena is torn down by.
    ///   The clause checks the four family lengths, including the documented
    ///   stale-mark no-op. Arena provenance and the unreachability the
    ///   requirement names stay prose: a watermark carries no arena identity,
    ///   and what the caller still retains is not an observation of the arena.
    /// - fails: never — a truncation past the end is a no-op, so a stale
    ///   watermark cannot grow the arena.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the truncation has one decision surface per family,
    ///   separated by a mark below the current length and a mark at it, with
    ///   the post-truncation lookup of a dropped id asserted to be absent.
    /// - witness: `arena::tests::truncating_to_a_watermark_drops_later_nodes`
    /// - witness: `arena::tests::all_families_truncate_without_resurrecting_nodes`
    #[inline]
    #[spec(
        captures: entry = self.watermark(),
        ensures: self.watermark()
            == ArenaWatermark {
                values: watermark.values.min(entry.values),
                computations: watermark.computations.min(entry.computations),
                value_types: watermark.value_types.min(entry.value_types),
                comp_types: watermark.comp_types.min(entry.comp_types),
            },
    )]
    pub fn truncate_to(
        &mut self,
        watermark: ArenaWatermark,
    )
    {
        self.values.truncate(watermark.values);
        self.computations.truncate(watermark.computations);
        self.value_types.truncate(watermark.value_types);
        self.comp_types.truncate(watermark.comp_types);
    }

    /// Resolve a value id, or `None` when it dangles.
    ///
    /// # Specification
    /// - requires: nothing; a dangling id is admissible.
    /// - ensures: the current value node at the index carried by `id`, or
    ///   `None` when that index is outside the family. A truncated index can be
    ///   reused by later allocation; ids do not carry generations.
    /// - provides: the read side of the value family.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct nodes at both ends of each family,
    ///   truncation to zero, and a later stale mark distinguish wrong-slot
    ///   lookup, surviving removed nodes and accidental growth.
    /// - witness: `arena::tests::all_families_truncate_without_resurrecting_nodes`
    #[spec(ensures: |ret| match (ret, self.values.get(id_offset(ArenaIndex(id.0)).0)) {
        | (Some(actual), Some(expected)) => core::ptr::eq(core::ptr::from_ref(actual), core::ptr::from_ref(expected)),
        | (None, None) => true,
        | (Some(_), None) | (None, Some(_)) => false,
    })]
    #[inline]
    #[must_use]
    pub fn value(
        &self,
        id: ValueId,
    ) -> Option<&Value>
    {
        self.values.get(id_offset(ArenaIndex(id.0)).0)
    }

    /// Resolve a computation id, or `None` when it dangles.
    ///
    /// # Specification
    /// - requires: nothing; a dangling id is admissible.
    /// - ensures: the current computation node at the index carried by `id`, or
    ///   `None` when that index is outside the family. A truncated index can be
    ///   reused by later allocation; ids do not carry generations.
    /// - provides: the read side of the computation family.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct nodes at both ends of each family,
    ///   truncation to zero, and a later stale mark distinguish wrong-slot
    ///   lookup, surviving removed nodes and accidental growth.
    /// - witness: `arena::tests::all_families_truncate_without_resurrecting_nodes`
    #[spec(ensures: |ret| match (ret, self.computations.get(id_offset(ArenaIndex(id.0)).0)) {
        | (Some(actual), Some(expected)) => core::ptr::eq(core::ptr::from_ref(actual), core::ptr::from_ref(expected)),
        | (None, None) => true,
        | (Some(_), None) | (None, Some(_)) => false,
    })]
    #[inline]
    #[must_use]
    pub fn computation(
        &self,
        id: ComputationId,
    ) -> Option<&Computation>
    {
        self.computations.get(id_offset(ArenaIndex(id.0)).0)
    }

    /// Resolve a value-type id, or `None` when it dangles.
    ///
    /// # Specification
    /// - requires: nothing; a dangling id is admissible.
    /// - ensures: the current value-type node at the index carried by `id`, or
    ///   `None` when that index is outside the family. A truncated index can be
    ///   reused by later allocation; ids do not carry generations.
    /// - provides: the read side of the value-type family.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct nodes at both ends of each family,
    ///   truncation to zero, and a later stale mark distinguish wrong-slot
    ///   lookup, surviving removed nodes and accidental growth.
    /// - witness: `arena::tests::all_families_truncate_without_resurrecting_nodes`
    #[spec(ensures: |ret| match (ret, self.value_types.get(id_offset(ArenaIndex(id.0)).0)) {
        | (Some(actual), Some(expected)) => core::ptr::eq(core::ptr::from_ref(actual), core::ptr::from_ref(expected)),
        | (None, None) => true,
        | (Some(_), None) | (None, Some(_)) => false,
    })]
    #[inline]
    #[must_use]
    pub fn value_type(
        &self,
        id: ValueTypeId,
    ) -> Option<&ValueType>
    {
        self.value_types.get(id_offset(ArenaIndex(id.0)).0)
    }

    /// Resolve a computation-type id, or `None` when it dangles.
    ///
    /// # Specification
    /// - requires: nothing; a dangling id is admissible.
    /// - ensures: the current computation-type node at the index carried by
    ///   `id`, or `None` when that index is outside the family. A truncated
    ///   index can be reused by later allocation; ids do not carry generations.
    /// - provides: the read side of the computation-type family.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct nodes at both ends of each family,
    ///   truncation to zero, and a later stale mark distinguish wrong-slot
    ///   lookup, surviving removed nodes and accidental growth.
    /// - witness: `arena::tests::all_families_truncate_without_resurrecting_nodes`
    #[spec(ensures: |ret| match (ret, self.comp_types.get(id_offset(ArenaIndex(id.0)).0)) {
        | (Some(actual), Some(expected)) => core::ptr::eq(core::ptr::from_ref(actual), core::ptr::from_ref(expected)),
        | (None, None) => true,
        | (Some(_), None) | (None, Some(_)) => false,
    })]
    #[inline]
    #[must_use]
    pub fn comp_type(
        &self,
        id: CompTypeId,
    ) -> Option<&CompType>
    {
        self.comp_types.get(id_offset(ArenaIndex(id.0)).0)
    }

    /// Append a value node and return its fresh id.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: appends `value` to the value family and returns the id at the
    ///   family's previous end, which is above every value id already minted.
    /// - provides: the single append point every value constructor goes
    ///   through.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — unequal children and distinct formers exercise append
    ///   identity, family separation and child order; truncation then
    ///   reallocation separates fresh allocation from a stale-slot alias.
    /// - witness: `arena::tests::distinct_children_survive_every_compound_former`
    /// - witness: `arena::tests::all_families_truncate_without_resurrecting_nodes`
    #[spec(
        captures: [entry = self.values.len(), kind = core::mem::discriminant(&value)],
        ensures: |ret| entry.checked_add(1) == Some(self.values.len())
            && ret.0 == u32::try_from(entry).unwrap_or(u32::MAX)
            && self.values.last().is_some_and(|node| core::mem::discriminant(node) == kind),
    )]
    #[inline]
    fn alloc_value(
        &mut self,
        value: Value,
    ) -> ValueId
    {
        let id = ValueId(id_index(ArenaLength(self.values.len())).0);
        self.values.push(value);
        id
    }

    /// Append a computation node and return its fresh id.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: appends `computation` to the computation family and returns
    ///   the id at the family's previous end, which is above every computation
    ///   id already minted.
    /// - provides: the single append point every computation constructor goes
    ///   through.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — unequal children and distinct formers exercise append
    ///   identity, family separation and child order; truncation then
    ///   reallocation separates fresh allocation from a stale-slot alias.
    /// - witness: `arena::tests::distinct_children_survive_every_compound_former`
    /// - witness: `arena::tests::all_families_truncate_without_resurrecting_nodes`
    #[spec(
        captures: [entry = self.computations.len(), kind = core::mem::discriminant(&computation)],
        ensures: |ret| entry.checked_add(1) == Some(self.computations.len())
            && ret.0 == u32::try_from(entry).unwrap_or(u32::MAX)
            && self.computations.last().is_some_and(|node| core::mem::discriminant(node) == kind),
    )]
    #[inline]
    fn alloc_computation(
        &mut self,
        computation: Computation,
    ) -> ComputationId
    {
        let id = ComputationId(id_index(ArenaLength(self.computations.len())).0);
        self.computations.push(computation);
        id
    }

    /// Mint a saturated native call; the checker validates its arguments.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn computation_primitive(
        &mut self,
        primitive: crate::primitive::Primitive,
        arguments: crate::primitive::Arguments,
    ) -> ComputationId
    {
        self.alloc_computation(Computation::Primitive {
            primitive,
            arguments,
        })
    }

    /// Mint the table-typed thunk produced by the primitive constructor.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn value_primitive(
        &mut self,
        primitive: crate::primitive::Primitive,
        body: ComputationId,
    ) -> ValueId
    {
        self.alloc_value(Value::Primitive { primitive, body })
    }

    /// Append a value-type node and return its fresh id.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: appends `value_type` to the value-type family and returns the
    ///   id at the family's previous end, which is above every value-type id
    ///   already minted.
    /// - provides: the single append point every value-type constructor goes
    ///   through.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — unequal children and distinct formers exercise append
    ///   identity, family separation and child order; truncation then
    ///   reallocation separates fresh allocation from a stale-slot alias.
    /// - witness: `arena::tests::distinct_children_survive_every_compound_former`
    /// - witness: `arena::tests::all_families_truncate_without_resurrecting_nodes`
    #[spec(
        captures: [entry = self.value_types.len(), kind = core::mem::discriminant(&value_type)],
        ensures: |ret| entry.checked_add(1) == Some(self.value_types.len())
            && ret.0 == u32::try_from(entry).unwrap_or(u32::MAX)
            && self.value_types.last().is_some_and(|node| core::mem::discriminant(node) == kind),
    )]
    #[inline]
    fn alloc_value_type(
        &mut self,
        value_type: ValueType,
    ) -> ValueTypeId
    {
        let id = ValueTypeId(id_index(ArenaLength(self.value_types.len())).0);
        self.value_types.push(value_type);
        id
    }

    /// Append a computation-type node and return its fresh id.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: appends `comp_type` to the computation-type family and
    ///   returns the id at the family's previous end, which is above every
    ///   computation-type id already minted.
    /// - provides: the single append point every computation-type constructor
    ///   goes through.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — unequal children and distinct formers exercise append
    ///   identity, family separation and child order; truncation then
    ///   reallocation separates fresh allocation from a stale-slot alias.
    /// - witness: `arena::tests::distinct_children_survive_every_compound_former`
    /// - witness: `arena::tests::all_families_truncate_without_resurrecting_nodes`
    #[spec(
        captures: [entry = self.comp_types.len(), kind = core::mem::discriminant(&comp_type)],
        ensures: |ret| entry.checked_add(1) == Some(self.comp_types.len())
            && ret.0 == u32::try_from(entry).unwrap_or(u32::MAX)
            && self.comp_types.last().is_some_and(|node| core::mem::discriminant(node) == kind),
    )]
    #[inline]
    fn alloc_comp_type(
        &mut self,
        comp_type: CompType,
    ) -> CompTypeId
    {
        let id = CompTypeId(id_index(ArenaLength(self.comp_types.len())).0);
        self.comp_types.push(comp_type);
        id
    }

    // Value constructors. Each mints over already-allocated children, which is
    // what makes a child id strictly less than its parent's.

    /// Mint a bound value variable in a named zone.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn value_variable(
        &mut self,
        zone: Zone,
        index: DeBruijnIndex,
    ) -> ValueId
    {
        self.alloc_value(Value::Variable { zone, index })
    }

    /// Mint a constant reference to a prior declaration.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn value_constant(
        &mut self,
        index: ConstantIndex,
    ) -> ValueId
    {
        self.alloc_value(Value::Constant(index))
    }

    /// Mint the unit value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn value_unit(&mut self) -> ValueId
    {
        self.alloc_value(Value::Unit)
    }

    /// Mint a base-type literal value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn value_literal(
        &mut self,
        literal: Literal,
    ) -> ValueId
    {
        self.alloc_value(Value::Literal(literal))
    }

    /// Mint a pair over two already-allocated value children.
    ///
    /// # Specification
    /// - requires: `first` and `second` name value nodes already allocated in
    ///   this arena.
    /// - ensures: appends the pair and returns a fresh id strictly above both
    ///   children.
    /// - provides: the only way to mint this former, which is what keeps a
    ///   child id below its parent's.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct child ids, unequal branch bodies and both
    ///   injection sides distinguish swapped or dropped children and confused
    ///   formers. Readback observes the minted node rather than merely its id.
    /// - witness: `arena::tests::distinct_children_survive_every_compound_former`
    #[spec(ensures: |ret| self.value(ret) == Some(&Value::Pair(first, second)))]
    #[inline]
    pub fn value_pair(
        &mut self,
        first: ValueId,
        second: ValueId,
    ) -> ValueId
    {
        self.alloc_value(Value::Pair(first, second))
    }

    /// Mint a sum injection over an already-allocated value body.
    ///
    /// # Specification
    /// - requires: `body` names a value node already allocated in this arena.
    /// - ensures: appends the injection and returns a fresh id strictly above
    ///   `body`.
    /// - provides: the only way to mint this former, which is what keeps a
    ///   child id below its parent's.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct child ids, unequal branch bodies and both
    ///   injection sides distinguish swapped or dropped children and confused
    ///   formers. Readback observes the minted node rather than merely its id.
    /// - witness: `arena::tests::distinct_children_survive_every_compound_former`
    #[spec(ensures: |ret| self.value(ret) == Some(&Value::Injection(side, body)))]
    #[inline]
    pub fn value_injection(
        &mut self,
        side: Side,
        body: ValueId,
    ) -> ValueId
    {
        self.alloc_value(Value::Injection(side, body))
    }

    /// Mint a thunk over an already-allocated computation body.
    ///
    /// # Specification
    /// - requires: `body` names a computation node already allocated in this
    ///   arena.
    /// - ensures: appends the thunk and returns a fresh value id.
    /// - provides: the only way to mint this former; the child is in the
    ///   computation family, so the two id spaces stay independent.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct child ids, unequal branch bodies and both
    ///   injection sides distinguish swapped or dropped children and confused
    ///   formers. Readback observes the minted node rather than merely its id.
    /// - witness: `arena::tests::distinct_children_survive_every_compound_former`
    #[spec(ensures: |ret| self.value(ret) == Some(&Value::Thunk(body)))]
    #[inline]
    pub fn value_thunk(
        &mut self,
        body: ComputationId,
    ) -> ValueId
    {
        self.alloc_value(Value::Thunk(body))
    }

    /// Mint a value lift over an already-allocated value body.
    ///
    /// # Specification
    /// - requires: `body` names a value node already allocated in this arena.
    /// - ensures: appends the lift at `target` and returns a fresh id strictly
    ///   above `body`.
    /// - provides: the only way to mint this former, which is what keeps a
    ///   child id below its parent's.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a nonzero target and an already allocated child
    ///   distinguish a lost level, the wrong child and a lift confused with its
    ///   underlying node; the executable predicate observes the former and
    ///   child only.
    /// - witness: `arena::tests::distinct_children_survive_every_compound_former`
    #[spec(ensures: |ret| matches!(self.value(ret), Some(Value::Lift { body: actual, .. }) if *actual == body))]
    #[inline]
    pub fn value_lift(
        &mut self,
        target: Level,
        body: ValueId,
    ) -> ValueId
    {
        self.alloc_value(Value::Lift { target, body })
    }

    /// Mint the quote of an already-allocated value type: its code.
    ///
    /// # Specification
    /// - requires: `quoted` names a value-type node already allocated in this
    ///   arena.
    /// - ensures: appends the quote and returns a fresh value id.
    /// - provides: the only way to mint this former; the child is in the
    ///   value-type family, so the two id spaces stay independent.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct child ids, unequal branch bodies and both
    ///   injection sides distinguish swapped or dropped children and confused
    ///   formers. Readback observes the minted node rather than merely its id.
    /// - witness: `arena::tests::distinct_children_survive_every_compound_former`
    #[spec(ensures: |ret| self.value(ret) == Some(&Value::Quote(quoted)))]
    #[inline]
    pub fn value_quote(
        &mut self,
        quoted: ValueTypeId,
    ) -> ValueId
    {
        self.alloc_value(Value::Quote(quoted))
    }

    /// Mint the quote of an already-allocated computation type: its code.
    ///
    /// # Specification
    /// - requires: `quoted` names a computation-type node already allocated in
    ///   this arena.
    /// - ensures: appends the quote and returns a fresh value id.
    /// - provides: the only way to mint this former; the child is in the
    ///   computation-type family, so the two id spaces stay independent.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct child ids, unequal branch bodies and both
    ///   injection sides distinguish swapped or dropped children and confused
    ///   formers. Readback observes the minted node rather than merely its id.
    /// - witness: `arena::tests::distinct_children_survive_every_compound_former`
    #[spec(ensures: |ret| self.value(ret) == Some(&Value::QuoteComputation(quoted)))]
    #[inline]
    pub fn value_quote_computation(
        &mut self,
        quoted: CompTypeId,
    ) -> ValueId
    {
        self.alloc_value(Value::QuoteComputation(quoted))
    }

    /// Mint a static lambda over an already-allocated value body, scoped under
    /// the one binder the lambda opens.
    ///
    /// # Specification
    /// - requires: `body` names a value node already allocated in this arena;
    ///   that it reads the binder at a static classifier is a typing fact this
    ///   constructor does not decide.
    /// - ensures: appends the static lambda and returns a fresh id strictly
    ///   above `body`.
    /// - provides: the only way to mint this former, which is what keeps a
    ///   child id below its parent's.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a static lambda as one argument shape among the six a
    ///   static family takes, read back as minted beneath its application.
    /// - witness: `arena::tests::flat_arena_round_trips_all_static_argument_shapes`
    #[inline]
    #[spec(ensures: |ret| self.value(ret) == Some(&Value::StaticLambda(body)))]
    pub fn value_static_lambda(
        &mut self,
        body: ValueId,
    ) -> ValueId
    {
        self.alloc_value(Value::StaticLambda(body))
    }

    /// Mint a static application over an already-allocated head and argument.
    ///
    /// Minting reduces nothing: a static lambda at the head is a redex the
    /// normaliser fires, so the redex is representable and the reduction is
    /// a step a certificate can name.
    ///
    /// # Specification
    /// - requires: `head` and `argument` name value nodes already allocated in
    ///   this arena; that the head inhabits a static Pi the argument suits is a
    ///   typing fact this constructor does not decide.
    /// - ensures: appends the static application and returns a fresh id
    ///   strictly above `head` and `argument`.
    /// - provides: the only way to mint this former, which is what keeps a
    ///   child id below its parent's.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every argument shape a static family takes, a quote,
    ///   a computation quote, a variable, a constant, a static lambda and a
    ///   nested application, reads back as minted with a lambda head left
    ///   unreduced; and a spine fifty thousand applications deep is built,
    ///   rewritten and walked inside a small stack.
    /// - witness: `arena::tests::flat_arena_round_trips_all_static_argument_shapes`
    /// - witness: `deep_static::deep_static::flat_arena_round_trips_deep_static_family_without_stack_recursion`
    #[inline]
    #[spec(ensures: |ret| self.value(ret) == Some(&Value::StaticApplication(head, argument)))]
    pub fn value_static_application(
        &mut self,
        head: ValueId,
        argument: ValueId,
    ) -> ValueId
    {
        self.alloc_value(Value::StaticApplication(head, argument))
    }

    // Computation constructors.

    /// Mint a lambda over an already-allocated computation body.
    ///
    /// # Specification
    /// - requires: `body` names a computation node already allocated in this
    ///   arena.
    /// - ensures: appends the lambda and returns a fresh id strictly above
    ///   `body`.
    /// - provides: the only way to mint this former, which is what keeps a
    ///   child id below its parent's.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct child ids, unequal branch bodies and both
    ///   injection sides distinguish swapped or dropped children and confused
    ///   formers. Readback observes the minted node rather than merely its id.
    /// - witness: `arena::tests::distinct_children_survive_every_compound_former`
    #[spec(ensures: |ret| self.computation(ret) == Some(&Computation::Lambda(body)))]
    #[inline]
    pub fn computation_lambda(
        &mut self,
        body: ComputationId,
    ) -> ComputationId
    {
        self.alloc_computation(Computation::Lambda(body))
    }

    /// Mint an application over an already-allocated head and argument.
    ///
    /// # Specification
    /// - requires: `head` names a computation node and `argument` a value node,
    ///   both already allocated in this arena.
    /// - ensures: appends the application and returns a fresh id strictly above
    ///   `head`.
    /// - provides: the only way to mint this former, which is what keeps a
    ///   child id below its parent's.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct child ids, unequal branch bodies and both
    ///   injection sides distinguish swapped or dropped children and confused
    ///   formers. Readback observes the minted node rather than merely its id.
    /// - witness: `arena::tests::distinct_children_survive_every_compound_former`
    #[spec(ensures: |ret| self.computation(ret) == Some(&Computation::Application(head, argument)))]
    #[inline]
    pub fn computation_application(
        &mut self,
        head: ComputationId,
        argument: ValueId,
    ) -> ComputationId
    {
        self.alloc_computation(Computation::Application(head, argument))
    }

    /// Mint a returner over an already-allocated value.
    ///
    /// # Specification
    /// - requires: `value` names a value node already allocated in this arena.
    /// - ensures: appends the returner and returns a fresh computation id.
    /// - provides: the only way to mint this former; the child is in the value
    ///   family, so the two id spaces stay independent.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct child ids, unequal branch bodies and both
    ///   injection sides distinguish swapped or dropped children and confused
    ///   formers. Readback observes the minted node rather than merely its id.
    /// - witness: `arena::tests::distinct_children_survive_every_compound_former`
    #[spec(ensures: |ret| self.computation(ret) == Some(&Computation::Return(value)))]
    #[inline]
    pub fn computation_return(
        &mut self,
        value: ValueId,
    ) -> ComputationId
    {
        self.alloc_computation(Computation::Return(value))
    }

    /// Mint a bind over an already-allocated bound computation and body.
    ///
    /// # Specification
    /// - requires: `bound` and `body` name computation nodes already allocated
    ///   in this arena.
    /// - ensures: appends the bind and returns a fresh id strictly above both
    ///   children.
    /// - provides: the only way to mint this former, which is what keeps a
    ///   child id below its parent's.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct child ids, unequal branch bodies and both
    ///   injection sides distinguish swapped or dropped children and confused
    ///   formers. Readback observes the minted node rather than merely its id.
    /// - witness: `arena::tests::distinct_children_survive_every_compound_former`
    #[spec(ensures: |ret| self.computation(ret) == Some(&Computation::Bind(bound, body)))]
    #[inline]
    pub fn computation_bind(
        &mut self,
        bound: ComputationId,
        body: ComputationId,
    ) -> ComputationId
    {
        self.alloc_computation(Computation::Bind(bound, body))
    }

    /// Mint a force over an already-allocated value.
    ///
    /// # Specification
    /// - requires: `value` names a value node already allocated in this arena.
    /// - ensures: appends the force and returns a fresh computation id.
    /// - provides: the only way to mint this former; the child is in the value
    ///   family, so the two id spaces stay independent.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct child ids, unequal branch bodies and both
    ///   injection sides distinguish swapped or dropped children and confused
    ///   formers. Readback observes the minted node rather than merely its id.
    /// - witness: `arena::tests::distinct_children_survive_every_compound_former`
    #[spec(ensures: |ret| self.computation(ret) == Some(&Computation::Force(value)))]
    #[inline]
    pub fn computation_force(
        &mut self,
        value: ValueId,
    ) -> ComputationId
    {
        self.alloc_computation(Computation::Force(value))
    }

    /// Mint a case over an already-allocated scrutinee and two branches.
    ///
    /// # Specification
    /// - requires: `scrutinee` names a value node, and `on_left` and `on_right`
    ///   computation nodes, all already allocated in this arena.
    /// - ensures: appends the case and returns a fresh id strictly above both
    ///   branches.
    /// - provides: the only way to mint this former, which is what keeps a
    ///   child id below its parent's.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct child ids, unequal branch bodies and both
    ///   injection sides distinguish swapped or dropped children and confused
    ///   formers. Readback observes the minted node rather than merely its id.
    /// - witness: `arena::tests::distinct_children_survive_every_compound_former`
    #[spec(ensures: |ret| self.computation(ret) == Some(&Computation::Case { scrutinee, on_left, on_right }))]
    #[inline]
    pub fn computation_case(
        &mut self,
        scrutinee: ValueId,
        on_left: ComputationId,
        on_right: ComputationId,
    ) -> ComputationId
    {
        self.alloc_computation(Computation::Case {
            scrutinee,
            on_left,
            on_right,
        })
    }

    // Value-type constructors.

    /// Mint a base value type.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn value_type_base(
        &mut self,
        base: BaseType,
    ) -> ValueTypeId
    {
        self.alloc_value_type(ValueType::Base(base))
    }

    /// Mint the unit value type.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn value_type_unit(&mut self) -> ValueTypeId
    {
        self.alloc_value_type(ValueType::Unit)
    }

    /// Mint a product over two already-allocated value types.
    ///
    /// # Specification
    /// - requires: `first` and `second` name value-type nodes already allocated
    ///   in this arena.
    /// - ensures: appends the product and returns a fresh id strictly above
    ///   both children.
    /// - provides: the only way to mint this former, which is what keeps a
    ///   child id below its parent's.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct child ids, unequal branch bodies and both
    ///   injection sides distinguish swapped or dropped children and confused
    ///   formers. Readback observes the minted node rather than merely its id.
    /// - witness: `arena::tests::distinct_children_survive_every_compound_former`
    #[spec(ensures: |ret| self.value_type(ret) == Some(&ValueType::Product(first, second)))]
    #[inline]
    pub fn value_type_product(
        &mut self,
        first: ValueTypeId,
        second: ValueTypeId,
    ) -> ValueTypeId
    {
        self.alloc_value_type(ValueType::Product(first, second))
    }

    /// Mint a sum over two already-allocated value types.
    ///
    /// # Specification
    /// - requires: `first` and `second` name value-type nodes already allocated
    ///   in this arena.
    /// - ensures: appends the sum and returns a fresh id strictly above both
    ///   children.
    /// - provides: the only way to mint this former, which is what keeps a
    ///   child id below its parent's.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct child ids, unequal branch bodies and both
    ///   injection sides distinguish swapped or dropped children and confused
    ///   formers. Readback observes the minted node rather than merely its id.
    /// - witness: `arena::tests::distinct_children_survive_every_compound_former`
    #[spec(ensures: |ret| self.value_type(ret) == Some(&ValueType::Sum(first, second)))]
    #[inline]
    pub fn value_type_sum(
        &mut self,
        first: ValueTypeId,
        second: ValueTypeId,
    ) -> ValueTypeId
    {
        self.alloc_value_type(ValueType::Sum(first, second))
    }

    /// Mint a thunk type over an already-allocated computation type.
    ///
    /// # Specification
    /// - requires: `body` names a computation-type node already allocated in
    ///   this arena.
    /// - ensures: appends the thunk type and returns a fresh value-type id.
    /// - provides: the only way to mint this former; the child is in the
    ///   computation-type family, so the two id spaces stay independent.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct child ids, unequal branch bodies and both
    ///   injection sides distinguish swapped or dropped children and confused
    ///   formers. Readback observes the minted node rather than merely its id.
    /// - witness: `arena::tests::distinct_children_survive_every_compound_former`
    #[spec(ensures: |ret| self.value_type(ret) == Some(&ValueType::Thunk(body)))]
    #[inline]
    pub fn value_type_thunk(
        &mut self,
        body: CompTypeId,
    ) -> ValueTypeId
    {
        self.alloc_value_type(ValueType::Thunk(body))
    }

    /// Mint the universe of one sort at a canonical level.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn value_type_universe(
        &mut self,
        sort: Sort,
        level: Level,
    ) -> ValueTypeId
    {
        self.alloc_value_type(ValueType::Universe { sort, level })
    }

    /// Mint a reference to a sealed abstract type by its declaration's
    /// admission position.
    ///
    /// Minting does not check the position: whether it names an admitted
    /// abstract-type declaration is a typing fact, so an unadmitted position is
    /// a rejection downstream rather than an unrepresentable node here.
    ///
    /// # Specification
    /// - requires: nothing; whether `atom` names an admitted abstract-type
    ///   declaration is a typing fact this constructor does not decide.
    /// - ensures: appends the reference and returns a fresh value-type id.
    /// - provides: the representation of a sealed abstract type, with its
    ///   admission left to the judgement that owns it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct child ids, unequal branch bodies and both
    ///   injection sides distinguish swapped or dropped children and confused
    ///   formers. Readback observes the minted node rather than merely its id.
    /// - witness: `arena::tests::distinct_children_survive_every_compound_former`
    #[spec(ensures: |ret| self.value_type(ret) == Some(&ValueType::Abstract(atom)))]
    #[inline]
    pub fn value_type_abstract(
        &mut self,
        atom: ConstantIndex,
    ) -> ValueTypeId
    {
        self.alloc_value_type(ValueType::Abstract(atom))
    }

    /// Mint the value type a code denotes, over an already-allocated code
    /// value, decoding a quote on the spot.
    ///
    /// Decode-on-mint is the one computation rule types obey by construction:
    /// `El ⌜A⌝` is `A`, so a decode whose code is a value-type quote answers
    /// the quoted type itself and no node is minted. Every other code — a
    /// variable, a constant, a computation-type quote of the wrong sort — is
    /// represented as it stands, and whether it inhabits `Type[+, target]` is
    /// a typing fact rather than a representation one.
    ///
    /// # Specification
    /// - requires: `code` names a value node already allocated in this arena;
    ///   that it inhabits `Type[+, target]` is a typing fact this constructor
    ///   does not decide.
    /// - ensures: the quoted type when `code` resolves to a value-type quote,
    ///   and a freshly appended element type otherwise.
    /// - provides: the type a code denotes, with decoding a quote total and
    ///   inhabitation left to the judgement that owns it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one decision surface, the code's former: a quote of
    ///   the matching sort decodes, a quote of the other sort and a non-quote
    ///   code are minted as they stand.
    /// - witness: `arena::tests::a_decoded_quote_is_the_quoted_type`
    #[spec(ensures: |ret| if let Some(&Value::Quote(quoted)) = self.value(code) {
        ret == quoted
    } else {
        matches!(self.value_type(ret), Some(ValueType::Element { code: actual, .. }) if *actual == code)
    })]
    #[inline]
    pub fn value_type_element(
        &mut self,
        code: ValueId,
        target: Level,
    ) -> ValueTypeId
    {
        if let Some(&Value::Quote(quoted)) = self.value(code) {
            return quoted;
        }
        self.alloc_value_type(ValueType::Element { code, target })
    }

    /// Mint a value-type lift over an already-allocated inner value type.
    ///
    /// # Specification
    /// - requires: `inner` names a value-type node already allocated in this
    ///   arena.
    /// - ensures: appends the lift at `target` and returns a fresh id strictly
    ///   above `inner`.
    /// - provides: the only way to mint this former, which is what keeps a
    ///   child id below its parent's.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a nonzero target and an already allocated child
    ///   distinguish a lost level, the wrong child and a lift confused with its
    ///   underlying node; the executable predicate observes the former and
    ///   child only.
    /// - witness: `arena::tests::distinct_children_survive_every_compound_former`
    #[spec(ensures: |ret| matches!(self.value_type(ret), Some(ValueType::Lift { inner: actual, .. }) if *actual == inner))]
    #[inline]
    pub fn value_type_lift(
        &mut self,
        inner: ValueTypeId,
        target: Level,
    ) -> ValueTypeId
    {
        self.alloc_value_type(ValueType::Lift { inner, target })
    }

    /// Mint a static Pi over an already-allocated domain and codomain, both in
    /// the ambient context.
    ///
    /// # Specification
    /// - requires: `domain` and `codomain` name value-type nodes already
    ///   allocated in this arena; that both are static classifiers is a typing
    ///   fact this constructor does not decide.
    /// - ensures: appends the static Pi and returns a fresh id strictly above
    ///   `domain` and `codomain`.
    /// - provides: the only way to mint this former, which is what keeps a
    ///   child id below its parent's.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one static Pi over the value universe, read back as
    ///   minted; the static Pi's own decision surface is the typing
    ///   judgement's.
    /// - witness: `arena::tests::flat_arena_round_trips_all_static_argument_shapes`
    #[inline]
    #[spec(ensures: |ret| self.value_type(ret) == Some(&ValueType::StaticPi { domain, codomain }))]
    pub fn value_type_static_pi(
        &mut self,
        domain: ValueTypeId,
        codomain: ValueTypeId,
    ) -> ValueTypeId
    {
        self.alloc_value_type(ValueType::StaticPi { domain, codomain })
    }

    // Computation-type constructors.

    /// Mint a returner type over an already-allocated value type.
    ///
    /// # Specification
    /// - requires: `result` names a value-type node already allocated in this
    ///   arena.
    /// - ensures: appends the returner type and returns a fresh
    ///   computation-type id.
    /// - provides: the only way to mint this former; the child is in the
    ///   value-type family, so the two id spaces stay independent.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct child ids, unequal branch bodies and both
    ///   injection sides distinguish swapped or dropped children and confused
    ///   formers. Readback observes the minted node rather than merely its id.
    /// - witness: `arena::tests::distinct_children_survive_every_compound_former`
    #[spec(ensures: |ret| self.comp_type(ret) == Some(&CompType::Returner(result)))]
    #[inline]
    pub fn comp_type_returner(
        &mut self,
        result: ValueTypeId,
    ) -> CompTypeId
    {
        self.alloc_comp_type(CompType::Returner(result))
    }

    /// Mint an arrow type over an already-allocated domain and codomain.
    ///
    /// # Specification
    /// - requires: `domain` names a value-type node and `codomain` a
    ///   computation-type node, both already allocated in this arena.
    /// - ensures: appends the arrow and returns a fresh id strictly above
    ///   `codomain`.
    /// - provides: the only way to mint this former, which is what keeps a
    ///   child id below its parent's.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct child ids, unequal branch bodies and both
    ///   injection sides distinguish swapped or dropped children and confused
    ///   formers. Readback observes the minted node rather than merely its id.
    /// - witness: `arena::tests::distinct_children_survive_every_compound_former`
    #[spec(ensures: |ret| self.comp_type(ret) == Some(&CompType::Arrow { domain, codomain }))]
    #[inline]
    pub fn comp_type_arrow(
        &mut self,
        domain: ValueTypeId,
        codomain: CompTypeId,
    ) -> CompTypeId
    {
        self.alloc_comp_type(CompType::Arrow { domain, codomain })
    }

    /// Mint a dependent arrow over an already-allocated domain and a codomain
    /// scoped under the domain's binder.
    ///
    /// Minting does not check the scoping: whether the codomain reads the
    /// binder is a typing fact, so a codomain that ignores it is
    /// representable here.
    ///
    /// # Specification
    /// - requires: `domain` names a value-type node and `codomain` a
    ///   computation-type node, both already allocated in this arena; whether
    ///   the codomain reads the domain's binder is a typing fact this
    ///   constructor does not decide.
    /// - ensures: appends the dependent arrow and returns a fresh id strictly
    ///   above `codomain`.
    /// - provides: the only way to mint this former, which is what keeps a
    ///   child id below its parent's.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct child ids, unequal branch bodies and both
    ///   injection sides distinguish swapped or dropped children and confused
    ///   formers. Readback observes the minted node rather than merely its id.
    /// - witness: `arena::tests::distinct_children_survive_every_compound_former`
    #[spec(ensures: |ret| self.comp_type(ret) == Some(&CompType::Pi { domain, codomain }))]
    #[inline]
    pub fn comp_type_pi(
        &mut self,
        domain: ValueTypeId,
        codomain: CompTypeId,
    ) -> CompTypeId
    {
        self.alloc_comp_type(CompType::Pi { domain, codomain })
    }

    /// Mint the computation type a code denotes, over an already-allocated
    /// code value, decoding a quote on the spot.
    ///
    /// The computation-sort twin of [`Self::value_type_element`]: a code that
    /// is a computation-type quote answers the quoted type, and every other
    /// code is represented as it stands.
    ///
    /// # Specification
    /// - requires: `code` names a value node already allocated in this arena;
    ///   that it inhabits `Type[-, target]` is a typing fact this constructor
    ///   does not decide.
    /// - ensures: the quoted computation type when `code` resolves to a
    ///   computation-type quote, and a freshly appended element type otherwise.
    /// - provides: the computation decode, with decoding a quote total and
    ///   inhabitation left to the judgement that owns it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the same decision surface as the value decode, over
    ///   the other sort's quote.
    /// - witness: `arena::tests::a_decoded_quote_is_the_quoted_type`
    #[spec(ensures: |ret| if let Some(&Value::QuoteComputation(quoted)) = self.value(code) {
        ret == quoted
    } else {
        matches!(self.comp_type(ret), Some(CompType::Element { code: actual, .. }) if *actual == code)
    })]
    #[inline]
    pub fn comp_type_element(
        &mut self,
        code: ValueId,
        target: Level,
    ) -> CompTypeId
    {
        if let Some(&Value::QuoteComputation(quoted)) = self.value(code) {
            return quoted;
        }
        self.alloc_comp_type(CompType::Element { code, target })
    }
    /// Mint a native universe-path classifier; admission checks its codes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn value_type_path_universe(
        &mut self,
        source: ValueId,
        target: ValueId,
    ) -> ValueTypeId
    {
        self.alloc_value_type(ValueType::PathUniverse(source, target))
    }

    /// Mint native reflexivity.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn value_path_refl(
        &mut self,
        code: ValueId,
    ) -> ValueId
    {
        self.alloc_value(Value::PathRefl(code))
    }
    /// Apply a nominal declaration to its telescope arguments.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn value_type_data(
        &mut self,
        declaration: gandr_kernel_term::ConstantIndex,
        arguments: alloc::vec::Vec<ValueId>,
    ) -> ValueTypeId
    {
        self.alloc_value_type(ValueType::Data {
            declaration,
            arguments,
        })
    }

    /// Form a structural record classifier in canonical label order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn value_type_record(
        &mut self,
        fields: alloc::collections::BTreeMap<gandr_kernel_term::FieldLabel, ValueTypeId>,
    ) -> ValueTypeId
    {
        self.alloc_value_type(ValueType::Record(fields))
    }

    /// Introduce a nominal constructor with explicit application and fields.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn value_constructor(
        &mut self,
        datatype: ValueTypeId,
        tag: gandr_kernel_term::ConstructorTag,
        fields: alloc::vec::Vec<ValueId>,
    ) -> ValueId
    {
        self.alloc_value(Value::Constructor {
            datatype,
            tag,
            fields,
        })
    }

    /// Introduce a structural record.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn value_record(
        &mut self,
        fields: alloc::collections::BTreeMap<gandr_kernel_term::FieldLabel, ValueId>,
    ) -> ValueId
    {
        self.alloc_value(Value::Record(fields))
    }

    /// Eliminate nominal data with an explicit motive and field functions.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn computation_data_case(
        &mut self,
        scrutinee: ValueId,
        motive: CompTypeId,
        branches: alloc::vec::Vec<ComputationId>,
    ) -> ComputationId
    {
        self.alloc_computation(Computation::DataCase {
            scrutinee,
            motive,
            branches,
        })
    }

    /// Return the selected field of a record.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn computation_record_projection(
        &mut self,
        record: ValueId,
        label: gandr_kernel_term::FieldLabel,
    ) -> ComputationId
    {
        self.alloc_computation(Computation::RecordProjection(record, label))
    }

    /// Mint the componentwise product of two paths.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn value_path_product(
        &mut self,
        first: ValueId,
        second: ValueId,
    ) -> ValueId
    {
        self.alloc_value(Value::PathProduct(first, second))
    }

    /// Mint an equivalence whose evidence remains untrusted until admission.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn value_path_equiv(
        &mut self,
        path_type: ValueTypeId,
        forward: ValueId,
        backward: ValueId,
        evidence: alloc::sync::Arc<gandr_kernel_term::PathEvidence>,
    ) -> ValueId
    {
        self.alloc_value(Value::PathEquiv {
            path_type,
            forward,
            backward,
            evidence,
        })
    }

    /// Mint a native transport computation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn computation_transport(
        &mut self,
        path: ValueId,
        value: ValueId,
    ) -> ComputationId
    {
        self.alloc_computation(Computation::Transport(path, value))
    }
}

#[cfg(test)]
mod tests
{
    use gandr_kernel_strata::Level;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::GroundSort;

    use super::ArenaWatermark;
    use super::CoreArena;
    use super::ValueId;
    use crate::classifier::Sort;
    use crate::syntax::CompType;
    use crate::syntax::Value;
    use crate::syntax::ValueType;
    use crate::syntax::Zone;

    #[test]
    fn flat_arena_distinguishes_type_plus_zero_and_type_minus_zero()
    {
        let mut arena = CoreArena::new();
        let value_universe =
            arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let computation_universe =
            arena.value_type_universe(Sort::Ground(GroundSort::Computation), Level::zero());
        assert_ne!(
            value_universe, computation_universe,
            "the two families at one level are two nodes"
        );
        assert_ne!(
            arena.value_type(value_universe),
            arena.value_type(computation_universe),
            "and two different nodes, not two ids over one"
        );
    }

    #[test]
    fn flat_arena_round_trips_universe_classifier_and_level()
    {
        let mut arena = CoreArena::new();
        let one = Level::zero().succ().expect("one is representable");
        let value_universe =
            arena.value_type_universe(Sort::Ground(GroundSort::Value), one.clone());
        let computation_universe =
            arena.value_type_universe(Sort::Ground(GroundSort::Computation), Level::zero());
        assert_eq!(
            Some(&ValueType::Universe {
                sort: Sort::Ground(GroundSort::Value),
                level: one,
            }),
            arena.value_type(value_universe),
            "the value universe reads back with its sort and level"
        );
        assert_eq!(
            Some(&ValueType::Universe {
                sort: Sort::Ground(GroundSort::Computation),
                level: Level::zero(),
            }),
            arena.value_type(computation_universe),
            "and so does the computation universe"
        );
    }

    #[test]
    fn a_decoded_quote_is_the_quoted_type()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let returner = arena.comp_type_returner(integer);
        let value_code = arena.value_quote(integer);
        let computation_code = arena.value_quote_computation(returner);
        let mark = arena.watermark();
        assert_eq!(
            integer,
            arena.value_type_element(value_code, Level::zero()),
            "the value decode of a value quote is the quoted type"
        );
        assert_eq!(
            returner,
            arena.comp_type_element(computation_code, Level::zero()),
            "the computation decode of a computation quote is the quoted type"
        );
        assert_eq!(mark, arena.watermark(), "neither decode minted a node");

        let mismatched = arena.comp_type_element(value_code, Level::zero());
        assert_eq!(
            Some(&CompType::Element {
                code: value_code,
                target: Level::zero(),
            }),
            arena.comp_type(mismatched),
            "a quote of the other sort is not decoded"
        );
        let variable = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let neutral = arena.value_type_element(variable, Level::zero());
        assert_eq!(
            Some(&ValueType::Element {
                code: variable,
                target: Level::zero(),
            }),
            arena.value_type(neutral),
            "a code that is not a quote stands"
        );
    }

    #[test]
    fn a_child_id_is_strictly_below_its_parent()
    {
        let mut arena = CoreArena::new();
        let unit = arena.value_unit();
        let pair = arena.value_pair(unit, unit);
        assert!(
            unit < pair,
            "constructor-only minting orders child below parent"
        );
    }

    #[test]
    fn truncating_to_a_watermark_drops_later_nodes()
    {
        let mut arena = CoreArena::new();
        let kept = arena.value_unit();
        let mark = arena.watermark();
        let dropped = arena.value_unit();
        arena.truncate_to(mark);
        assert!(
            arena.value(kept).is_some(),
            "content below the mark survives"
        );
        assert!(
            arena.value(dropped).is_none(),
            "an id minted past the mark dangles after truncation"
        );
        arena.truncate_to(mark);
        assert!(
            arena.value(kept).is_some(),
            "truncating twice to the same mark is a no-op"
        );
    }

    #[test]
    fn a_dangling_id_resolves_to_nothing()
    {
        let arena = CoreArena::new();
        assert!(
            arena.value(ValueId(7)).is_none(),
            "an unresolvable id yields no node rather than panicking"
        );
    }

    #[test]
    fn the_default_watermark_is_the_empty_arena()
    {
        let arena = CoreArena::new();
        assert_eq!(
            ArenaWatermark::default(),
            arena.watermark(),
            "an empty arena sits at the floor"
        );
    }

    #[test]
    fn a_variable_records_the_zone_it_counts_in()
    {
        let mut arena = CoreArena::new();
        let index = DeBruijnIndex::from(0_u32);
        let structural = arena.value_variable(Zone::Intuitionistic, index);
        let linear = arena.value_variable(Zone::Linear, index);
        assert_eq!(
            Some(&Value::Variable {
                zone: Zone::Intuitionistic,
                index,
            }),
            arena.value(structural),
            "the intuitionistic occurrence keeps its zone"
        );
        assert_ne!(
            arena.value(structural),
            arena.value(linear),
            "one index in two zones is two different occurrences"
        );
    }

    #[test]
    fn flat_arena_round_trips_all_static_argument_shapes()
    {
        let mut arena = CoreArena::new();
        let family = arena.value_constant(ConstantIndex::from(0_usize));
        let integer = arena.value_type_base(BaseType::Integer);
        let returner = arena.comp_type_returner(integer);
        let quote = arena.value_quote(integer);
        let computation_quote = arena.value_quote_computation(returner);
        let variable = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let constant = arena.value_constant(ConstantIndex::from(1_usize));
        let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let lambda = arena.value_static_lambda(bound);
        let nested = arena.value_static_application(constant, quote);
        for argument in [quote, computation_quote, variable, constant, lambda, nested] {
            let applied = arena.value_static_application(family, argument);
            assert_eq!(
                Some(&Value::StaticApplication(family, argument)),
                arena.value(applied),
                "the family applied to {:?} reads back with its head and argument",
                arena.value(argument)
            );
        }
        assert_eq!(
            Some(&Value::StaticLambda(bound)),
            arena.value(lambda),
            "the static lambda reads back over its body"
        );

        let redex = arena.value_static_application(lambda, quote);
        assert_eq!(
            Some(&Value::StaticApplication(lambda, quote)),
            arena.value(redex),
            "a lambda head is left unreduced: the redex is representable"
        );

        let universe = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let pi = arena.value_type_static_pi(universe, universe);
        assert_eq!(
            Some(&ValueType::StaticPi {
                domain: universe,
                codomain: universe,
            }),
            arena.value_type(pi),
            "the static Pi reads back with its domain and codomain"
        );
    }
    #[test]
    fn index_boundaries_preserve_identity_or_saturate()
    {
        for raw in [0_u32, 1, u32::MAX] {
            let offset = super::id_offset(super::ArenaIndex(raw));
            assert_eq!(usize::try_from(raw).unwrap_or(usize::MAX), offset.0);
            assert_eq!(raw, super::id_index(offset).0);
        }
        if let Some(above) = usize::try_from(u32::MAX)
            .ok()
            .and_then(|limit| limit.checked_add(1))
        {
            assert_eq!(u32::MAX, super::id_index(super::ArenaLength(above)).0);
        }
    }

    #[test]
    fn all_families_truncate_without_resurrecting_nodes()
    {
        let mut arena = CoreArena::new();
        let kept_value = arena.value_unit();
        let kept_type = arena.value_type_unit();
        let kept_comp = arena.computation_return(kept_value);
        let kept_comp_type = arena.comp_type_returner(kept_type);
        let mark = arena.watermark();
        let dropped_value = arena.value_constant(ConstantIndex::from(17_usize));
        let dropped_type = arena.value_type_base(BaseType::Integer);
        let dropped_comp = arena.computation_force(dropped_value);
        let dropped_comp_type = arena.comp_type_arrow(dropped_type, kept_comp_type);
        let later = arena.watermark();
        assert_eq!(
            Some(&Value::Constant(ConstantIndex::from(17_usize))),
            arena.value(dropped_value)
        );
        assert_eq!(
            Some(&ValueType::Base(BaseType::Integer)),
            arena.value_type(dropped_type)
        );
        assert_eq!(
            Some(&crate::Computation::Force(dropped_value)),
            arena.computation(dropped_comp)
        );
        assert_eq!(
            Some(&CompType::Arrow {
                domain: dropped_type,
                codomain: kept_comp_type
            }),
            arena.comp_type(dropped_comp_type)
        );
        arena.truncate_to(mark);
        assert_eq!(Some(&Value::Unit), arena.value(kept_value));
        assert_eq!(Some(&ValueType::Unit), arena.value_type(kept_type));
        assert_eq!(
            Some(&crate::Computation::Return(kept_value)),
            arena.computation(kept_comp)
        );
        assert_eq!(
            Some(&CompType::Returner(kept_type)),
            arena.comp_type(kept_comp_type)
        );
        assert_eq!(None, arena.value(dropped_value));
        assert_eq!(None, arena.value_type(dropped_type));
        assert_eq!(None, arena.computation(dropped_comp));
        assert_eq!(None, arena.comp_type(dropped_comp_type));
        arena.truncate_to(later);
        assert_eq!(mark, arena.watermark());
        let replacement = arena.value_pair(kept_value, kept_value);
        assert_eq!(dropped_value, replacement);
        assert_eq!(
            Some(&Value::Pair(kept_value, kept_value)),
            arena.value(replacement)
        );
        arena.truncate_to(ArenaWatermark::default());
        arena.truncate_to(later);
        assert_eq!(ArenaWatermark::default(), arena.watermark());
        assert_eq!(None, arena.value(kept_value));
        assert_eq!(None, arena.value_type(kept_type));
        assert_eq!(None, arena.computation(kept_comp));
        assert_eq!(None, arena.comp_type(kept_comp_type));
    }

    #[test]
    fn distinct_children_survive_every_compound_former()
    {
        let mut arena = CoreArena::new();
        let first = arena.value_unit();
        let second = arena.value_constant(ConstantIndex::from(17_usize));
        let left = arena.computation_return(first);
        let right = arena.computation_return(second);
        let domain = arena.value_type_unit();
        let other = arena.value_type_base(BaseType::Integer);
        let result = arena.comp_type_returner(other);
        let level = Level::zero().succ().expect("one");
        let values = [
            (arena.value_pair(first, second), Value::Pair(first, second)),
            (
                arena.value_injection(gandr_kernel_term::Side::Left, first),
                Value::Injection(gandr_kernel_term::Side::Left, first),
            ),
            (
                arena.value_injection(gandr_kernel_term::Side::Right, second),
                Value::Injection(gandr_kernel_term::Side::Right, second),
            ),
            (arena.value_thunk(right), Value::Thunk(right)),
            (arena.value_lift(level.clone(), second), Value::Lift {
                target: level.clone(),
                body: second,
            }),
            (arena.value_quote(other), Value::Quote(other)),
            (
                arena.value_quote_computation(result),
                Value::QuoteComputation(result),
            ),
        ];
        for (id, node) in values {
            assert!(id > second);
            assert_eq!(Some(&node), arena.value(id));
        }
        let computations = [
            (
                arena.computation_lambda(right),
                crate::Computation::Lambda(right),
            ),
            (
                arena.computation_application(left, second),
                crate::Computation::Application(left, second),
            ),
            (
                arena.computation_return(second),
                crate::Computation::Return(second),
            ),
            (
                arena.computation_bind(left, right),
                crate::Computation::Bind(left, right),
            ),
            (
                arena.computation_force(second),
                crate::Computation::Force(second),
            ),
            (
                arena.computation_case(first, left, right),
                crate::Computation::Case {
                    scrutinee: first,
                    on_left: left,
                    on_right: right,
                },
            ),
        ];
        for (id, node) in computations {
            assert!(id > right);
            assert_eq!(Some(&node), arena.computation(id));
        }
        let types = [
            (
                arena.value_type_product(domain, other),
                ValueType::Product(domain, other),
            ),
            (
                arena.value_type_sum(domain, other),
                ValueType::Sum(domain, other),
            ),
            (arena.value_type_thunk(result), ValueType::Thunk(result)),
            (
                arena.value_type_lift(other, level.clone()),
                ValueType::Lift {
                    inner: other,
                    target: level,
                },
            ),
            (
                arena.value_type_abstract(ConstantIndex::from(23_usize)),
                ValueType::Abstract(ConstantIndex::from(23_usize)),
            ),
        ];
        for (id, node) in types {
            assert!(id > other);
            assert_eq!(Some(&node), arena.value_type(id));
        }
        let comp_types = [
            (arena.comp_type_returner(domain), CompType::Returner(domain)),
            (arena.comp_type_arrow(domain, result), CompType::Arrow {
                domain,
                codomain: result,
            }),
            (arena.comp_type_pi(other, result), CompType::Pi {
                domain: other,
                codomain: result,
            }),
        ];
        for (id, node) in comp_types {
            assert!(id > result);
            assert_eq!(Some(&node), arena.comp_type(id));
        }
    }
}
