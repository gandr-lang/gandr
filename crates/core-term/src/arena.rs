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
//!
//! # Quotes and decode-on-mint
//!
//! `Value::Quote` names a value type as a code and `Value::QuoteComputation` a
//! computation type; `ValueType::Element` and `CompType::Element` read a code
//! back as the type it names. `CoreArena::value_type_element` and
//! `CoreArena::comp_type_element` decode on mint: given a quote of the matching
//! family as the code, they return the quoted type itself rather than minting a
//! decode of it, so `El(⌜A⌝)` and `A` are one id and no conversion ever meets
//! the redex. The level a decode carries is the code's universe level, and a
//! decode of a quote ignores it: the quoted type has its own.
//!
//! Alternatives: a decode node kept over a quote and the β-rule left to
//! conversion, which every comparison of a type then pays and the kernel would
//! have to fire too. Reversal: a decode whose quote is only known after
//! substitution still meets the rule, so a machine that substitutes a quote for
//! a code variable re-mints the decode through the same constructor
//! (`instantiate_comp_type` does).
//!
//! # Arena ownership
//!
//! A constructor records child ids supplied by its caller. Keeping those
//! children live in the same arena, within the representable family-index
//! limit, makes a same-family child strictly earlier than its parent;
//! cross-family acyclicity follows from minting order rather than numeric
//! comparison. The ids carry neither arena identity nor allocation generation.
//! A lookup checks the current family bounds, not provenance: truncation
//! removes nodes, but later allocation can reuse their indices. The caller
//! therefore discards ids to removed nodes. `CoreArena::watermark` snapshots
//! the four family lengths and `CoreArena::truncate_to` drops later nodes
//! without growing a family when given a stale larger mark. Each walk over
//! arena edges belongs to the consumer that needs it.

use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Summand;

use crate::classifier::Sort;
use crate::hole::HoleId;
use crate::hole::MarkIndex;
use crate::syntax::CompType;
use crate::syntax::ComponentCount;
use crate::syntax::Computation;
use crate::syntax::SplitMotive;
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
                Value::Primitive { primitive, .. } => Some(primitive),
                Value::PathRefl(_)
                | Value::PathProduct(..)
                | Value::PathEquiv { .. }
                | Value::Here(_)
                | Value::Univalence(..)
                | Value::Funext(..)
                | Value::Equiv(..)
                | Value::Ua { .. }
                | Value::SessionRelated { .. }
                | Value::Stay(_)
                | Value::Then(..)
                | Value::FlowProduct(..)
                | Value::Forward(_)
                | Value::FunctionFlow(..)
                | Value::Recorded(_)
                | Value::Returned(_)
                | Value::Nested(_)
                | Value::Run(_)
                | Value::Variable { .. }
                | Value::Constant(_)
                | Value::Literal(_)
                | Value::Tuple(_)
                | Value::Injection(..)
                | Value::ListNil
                | Value::ListCons(..)
                | Value::Thunk(_)
                | Value::Lift { .. }
                | Value::Quote(_)
                | Value::QuoteComputation(_)
                | Value::StaticLambda(_)
                | Value::StaticApplication(..)
                | Value::Constructor { .. }
                | Value::Record(_)
                | Value::Hole(_)
                | Value::Mark { .. }
                | Value::Reify(_) => None,
            })
            .chain(
                self.computations
                    .iter()
                    .filter_map(|computation| match *computation {
                        Computation::Primitive { primitive, .. } => Some(primitive),
                        Computation::Transport(..)
                        | Computation::PathTransport { .. }
                        | Computation::Ride { .. }
                        | Computation::TelescopeTransport { .. }
                        | Computation::Lambda(_)
                        | Computation::Fixpoint { .. }
                        | Computation::Application(..)
                        | Computation::Return(_)
                        | Computation::Bind(..)
                        | Computation::Ascribe { .. }
                        | Computation::Force(_)
                        | Computation::Case { .. }
                        | Computation::Split { .. }
                        | Computation::DataCase { .. }
                        | Computation::RecordProjection(..)
                        | Computation::TupleProjection(..)
                        | Computation::Hole(_)
                        | Computation::Mark { .. }
                        | Computation::ListFold { .. }
                        | Computation::Perform { .. }
                        | Computation::Handle { .. }
                        | Computation::Exercise { .. }
                        | Computation::Scope { .. }
                        | Computation::Resume(..)
                        | Computation::Reset(_)
                        | Computation::Shift(_)
                        | Computation::With(..)
                        | Computation::Project(..)
                        | Computation::Session(_)
                        | Computation::Memory(_)
                        | Computation::World(_) => None,
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

    /// The value ids allocated after `after`, in allocation order.
    ///
    /// A mark beyond the current family answers no ids; truncation neither
    /// authenticates an old mark nor resurrects discarded allocations.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: exactly the current value suffix beginning at the mark.
    /// - provides: the nodes a rewrite minted, for a caller that records where
    ///   each came from.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the specification facade cannot expand an opaque
    ///   iterator return type; the witness checks exact ids across truncation.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — allocations in every family before and after the
    ///   mark, and a truncation below it, separate each family's suffix from
    ///   the others and from a stale mark.
    /// - witness: `arena::tests::allocation_suffixes_keep_their_family`
    #[inline]
    #[must_use]
    pub fn values_since(
        &self,
        after: ArenaWatermark,
    ) -> impl ExactSizeIterator<Item = ValueId> + use<>
    {
        (after.values .. self.values.len()).map(|index| ValueId(id_index(ArenaLength(index)).0))
    }

    /// The computation ids allocated after `after`, in allocation order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: exactly the current computation suffix beginning at the mark;
    ///   none for a mark beyond the family.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — as [`Self::values_since`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::values_since`].
    /// - witness: `arena::tests::allocation_suffixes_keep_their_family`
    #[inline]
    #[must_use]
    pub fn computations_since(
        &self,
        after: ArenaWatermark,
    ) -> impl ExactSizeIterator<Item = ComputationId> + use<>
    {
        (after.computations .. self.computations.len())
            .map(|index| ComputationId(id_index(ArenaLength(index)).0))
    }

    /// The value-type ids allocated after `after`, in allocation order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: exactly the current value-type suffix beginning at the mark;
    ///   none for a mark beyond the family.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — as [`Self::values_since`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::values_since`].
    /// - witness: `arena::tests::allocation_suffixes_keep_their_family`
    #[inline]
    #[must_use]
    pub fn value_types_since(
        &self,
        after: ArenaWatermark,
    ) -> impl ExactSizeIterator<Item = ValueTypeId> + use<>
    {
        (after.value_types .. self.value_types.len())
            .map(|index| ValueTypeId(id_index(ArenaLength(index)).0))
    }

    /// The computation-type ids allocated after `after`, in allocation order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: exactly the current computation-type suffix beginning at the
    ///   mark; none for a mark beyond the family.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — as [`Self::values_since`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::values_since`].
    /// - witness: `arena::tests::allocation_suffixes_keep_their_family`
    #[inline]
    #[must_use]
    pub fn comp_types_since(
        &self,
        after: ArenaWatermark,
    ) -> impl ExactSizeIterator<Item = CompTypeId> + use<>
    {
        (after.comp_types .. self.comp_types.len())
            .map(|index| CompTypeId(id_index(ArenaLength(index)).0))
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
    pub(crate) fn alloc_value(
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
    pub(crate) fn alloc_computation(
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
    pub(crate) fn alloc_value_type(
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
    pub(crate) fn alloc_comp_type(
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

    /// Mint the unit value, the tuple of no components.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: appends `Tuple([])` and returns its fresh id.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the unit is the empty tuple, not a former of its own,
    ///   so the two spellings mint equal nodes.
    /// - witness: `arena::tests::distinct_children_survive_every_compound_former`
    #[spec(ensures: |ret| self.value(ret).is_some_and(|held| matches!(*held, Value::Tuple(ref components) if components.is_empty())))]
    #[inline]
    pub fn value_unit(&mut self) -> ValueId
    {
        self.value_tuple(&[])
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

    /// Mint a tuple over already-allocated value children, in order.
    ///
    /// # Specification
    /// - requires: every component names a value node already allocated in this
    ///   arena.
    /// - ensures: appends the tuple of `components`, in order, and returns a
    ///   fresh id strictly above every component.
    /// - provides: the only way to mint this former, which is what keeps a
    ///   child id below its parent's.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct child ids at arities zero, two and three,
    ///   unequal branch bodies and distinct summands distinguish swapped,
    ///   dropped or merged children and confused formers. Readback observes the
    ///   minted node rather than merely its id.
    /// - witness: `arena::tests::distinct_children_survive_every_compound_former`
    #[spec(ensures: |ret| self.value(ret).is_some_and(|held| matches!(*held, Value::Tuple(ref minted) if **minted == *components)))]
    #[inline]
    pub fn value_tuple(
        &mut self,
        components: &[ValueId],
    ) -> ValueId
    {
        self.alloc_value(Value::Tuple(components.into()))
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
    /// - hypothesis: L3 — distinct child ids, unequal branch bodies and
    ///   distinct summands distinguish swapped or dropped children and confused
    ///   formers. Readback observes the minted node rather than merely its id.
    /// - witness: `arena::tests::distinct_children_survive_every_compound_former`
    #[spec(ensures: |ret| self.value(ret) == Some(&Value::Injection(summand, body)))]
    #[inline]
    pub fn value_injection(
        &mut self,
        summand: Summand,
        body: ValueId,
    ) -> ValueId
    {
        self.alloc_value(Value::Injection(summand, body))
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
    /// - witness: `tests::deep_static::flat_arena_round_trips_deep_static_family_without_stack_recursion`
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

    /// Mint a fixpoint over an already-allocated body, carrying its
    /// termination claim.
    ///
    /// # Specification
    /// - requires: `body` names a computation node already allocated in this
    ///   arena, scoped under the self binder.
    /// - ensures: appends the fixpoint and returns a fresh id strictly above
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
    #[spec(ensures: |ret| self.computation(ret) == Some(&Computation::Fixpoint { body, evidence }))]
    #[inline]
    pub fn computation_fixpoint(
        &mut self,
        body: ComputationId,
        evidence: gandr_kernel_term::FixpointEvidence,
    ) -> ComputationId
    {
        self.alloc_computation(Computation::Fixpoint { body, evidence })
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

    /// Mint an ascription of the computation `body` to the type `ty`.
    ///
    /// # Specification
    /// - requires: `body` names a computation node and `ty` a computation type
    ///   already allocated in this arena.
    /// - ensures: appends the ascription and returns a fresh computation id.
    /// - provides: the only way to mint this former.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::computation_bind`]: the minted node holds
    ///   both children, unswapped.
    /// - witness: `arena::tests::distinct_children_survive_every_compound_former`
    #[spec(ensures: |ret| self.computation(ret) == Some(&Computation::Ascribe { body, ty }))]
    #[inline]
    pub fn computation_ascribe(
        &mut self,
        body: ComputationId,
        ty: CompTypeId,
    ) -> ComputationId
    {
        self.alloc_computation(Computation::Ascribe { body, ty })
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

    /// Mint a case over an already-allocated scrutinee and one branch per
    /// summand.
    ///
    /// # Specification
    /// - requires: `scrutinee` names a value node, and every branch a
    ///   computation node, all already allocated in this arena.
    /// - ensures: appends the case with `branches` in order and returns a fresh
    ///   id strictly above every branch.
    /// - provides: the only way to mint this former, which is what keeps a
    ///   child id below its parent's.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct child ids, unequal branch bodies and
    ///   distinct summands distinguish swapped or dropped children and confused
    ///   formers. Readback observes the minted node rather than merely its id.
    /// - witness: `arena::tests::distinct_children_survive_every_compound_former`
    #[spec(ensures: |ret| self.computation(ret).is_some_and(|held| matches!(*held, Computation::Case { scrutinee: minted, branches: ref minted_branches } if minted == scrutinee && **minted_branches == *branches)))]
    #[inline]
    pub fn computation_case(
        &mut self,
        scrutinee: ValueId,
        branches: &[ComputationId],
    ) -> ComputationId
    {
        self.alloc_computation(Computation::Case {
            scrutinee,
            branches: branches.into(),
        })
    }

    /// Mint a split of an already-allocated scrutinee into a body under one
    /// binder per component, checked against the ambient type.
    ///
    /// # Specification
    /// - requires: `scrutinee` names a value node and `body` a computation
    ///   node, both already allocated in this arena.
    /// - ensures: appends the split of `arity` components with the ambient
    ///   motive and returns a fresh id strictly above its children.
    /// - provides: one of the two ways to mint this former, which is what keeps
    ///   a child id below its parent's.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct child ids and an arity other than the body's
    ///   distinguish swapped children, a dropped arity and confused formers.
    /// - witness: `arena::tests::distinct_children_survive_every_compound_former`
    #[spec(ensures: |ret| self.computation(ret).is_some_and(|held| *held == Computation::Split { scrutinee, arity, motive: SplitMotive::Ambient, body }))]
    #[inline]
    pub fn computation_split(
        &mut self,
        scrutinee: ValueId,
        arity: ComponentCount,
        body: ComputationId,
    ) -> ComputationId
    {
        self.alloc_computation(Computation::Split {
            scrutinee,
            arity,
            motive: SplitMotive::Ambient,
            body,
        })
    }

    /// Mint a split of an already-allocated scrutinee into a body under one
    /// binder per component, checked against a motive under one binder of the
    /// scrutinee.
    ///
    /// # Specification
    /// - requires: `scrutinee` names a value node, `motive` a computation-type
    ///   node and `body` a computation node, all already allocated in this
    ///   arena; whether the motive reads its binder is a typing fact this
    ///   constructor does not decide.
    /// - ensures: appends the split of `arity` components with the scrutinee
    ///   motive `motive` and returns a fresh id strictly above its children.
    /// - provides: one of the two ways to mint this former, which is what keeps
    ///   a child id below its parent's.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct child ids, an arity and a motive distinguish
    ///   a dropped motive, swapped children and confused formers.
    /// - witness: `arena::tests::distinct_children_survive_every_compound_former`
    #[spec(ensures: |ret| self.computation(ret).is_some_and(|held| *held == Computation::Split { scrutinee, arity, motive: SplitMotive::Scrutinee(motive), body }))]
    #[inline]
    pub fn computation_dependent_split(
        &mut self,
        scrutinee: ValueId,
        arity: ComponentCount,
        motive: CompTypeId,
        body: ComputationId,
    ) -> ComputationId
    {
        self.alloc_computation(Computation::Split {
            scrutinee,
            arity,
            motive: SplitMotive::Scrutinee(motive),
            body,
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

    /// Mint the unit value type, the product of no components.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: appends `Product([])` and returns its fresh id.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the unit is the empty product, not a former of its
    ///   own, so the two spellings mint equal nodes.
    /// - witness: `arena::tests::distinct_children_survive_every_compound_former`
    #[spec(ensures: |ret| self.value_type(ret).is_some_and(|held| matches!(*held, ValueType::Product(ref components) if components.is_empty())))]
    #[inline]
    pub fn value_type_unit(&mut self) -> ValueTypeId
    {
        self.value_type_product(&[])
    }

    /// Mint a product over already-allocated value types, in order.
    ///
    /// # Specification
    /// - requires: every component names a value-type node already allocated in
    ///   this arena.
    /// - ensures: appends the product of `components`, in order, and returns a
    ///   fresh id strictly above every component.
    /// - provides: the only way to mint this former, which is what keeps a
    ///   child id below its parent's.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct child ids at arities zero, two and three
    ///   distinguish swapped, dropped or merged components and confused
    ///   formers. Readback observes the minted node rather than merely its id.
    /// - witness: `arena::tests::distinct_children_survive_every_compound_former`
    #[spec(ensures: |ret| self.value_type(ret).is_some_and(|held| matches!(*held, ValueType::Product(ref minted) if **minted == *components)))]
    #[inline]
    pub fn value_type_product(
        &mut self,
        components: &[ValueTypeId],
    ) -> ValueTypeId
    {
        self.alloc_value_type(ValueType::Product(components.into()))
    }

    /// Mint a dependent pair over an already-allocated first factor and a
    /// second factor scoped under the first's binder.
    ///
    /// Minting does not check the scoping: whether the second factor reads the
    /// binder is a typing fact, so a second factor that ignores it is
    /// representable here.
    ///
    /// # Specification
    /// - requires: `first` and `second` name value-type nodes already allocated
    ///   in this arena; whether `second` reads the binder is a typing fact this
    ///   constructor does not decide.
    /// - ensures: appends the dependent pair and returns a fresh id strictly
    ///   above both factors.
    /// - provides: the only way to mint this former, which is what keeps a
    ///   child id below its parent's.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct child ids distinguish swapped or dropped
    ///   factors and a dependent pair confused with the product of the same two
    ///   factors.
    /// - witness: `arena::tests::distinct_children_survive_every_compound_former`
    #[spec(ensures: |ret| self.value_type(ret) == Some(&ValueType::Sigma { first, second }))]
    #[inline]
    pub fn value_type_sigma(
        &mut self,
        first: ValueTypeId,
        second: ValueTypeId,
    ) -> ValueTypeId
    {
        self.alloc_value_type(ValueType::Sigma { first, second })
    }

    /// Mint a sum over already-allocated value types, in order.
    ///
    /// # Specification
    /// - requires: every summand names a value-type node already allocated in
    ///   this arena.
    /// - ensures: appends the sum of `summands`, in order, and returns a fresh
    ///   id strictly above every summand.
    /// - provides: the only way to mint this former, which is what keeps a
    ///   child id below its parent's.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct child ids at arities zero, two and three
    ///   distinguish swapped, dropped or merged summands and confused formers.
    ///   Readback observes the minted node rather than merely its id.
    /// - witness: `arena::tests::distinct_children_survive_every_compound_former`
    #[spec(ensures: |ret| self.value_type(ret).is_some_and(|held| matches!(*held, ValueType::Sum(ref minted) if **minted == *summands)))]
    #[inline]
    pub fn value_type_sum(
        &mut self,
        summands: &[ValueTypeId],
    ) -> ValueTypeId
    {
        self.alloc_value_type(ValueType::Sum(summands.into()))
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

    /// Mint `base` refined at `stage`, the refinement of a staged `base`
    /// replacing its stage.
    ///
    /// # Specification
    /// - requires: `base` names a value-type node already allocated in this
    ///   arena.
    /// - ensures: a fresh staged node at `stage` whose base is `base`, or the
    ///   base `base` refines when `base` is itself staged; never a stage over a
    ///   stage.
    /// - provides: the only way to mint this former.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a plain base and a staged one separate the
    ///   replacement from a nested stage.
    /// - witness: `arena::tests::a_stage_refines_its_base_once`
    #[spec(ensures: |ret| matches!(self.value_type(ret), Some(&ValueType::Staged { base: minted, stage: held }) if held == stage && !matches!(self.value_type(minted), Some(ValueType::Staged { .. }))))]
    #[inline]
    pub fn value_type_staged(
        &mut self,
        base: ValueTypeId,
        stage: gandr_kernel_term::Stage,
    ) -> ValueTypeId
    {
        let base = match self.value_type(base) {
            Some(&ValueType::Staged { base: refined, .. }) => refined,
            Some(_) | None => base,
        };
        self.alloc_value_type(ValueType::Staged { base, stage })
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
    #[spec(ensures: |ret| self.comp_type(ret) == Some(&CompType::Returner { result, effects: crate::effect::EffectRow::EMPTY }))]
    #[inline]
    pub fn comp_type_returner(
        &mut self,
        result: ValueTypeId,
    ) -> CompTypeId
    {
        self.comp_type_returner_with_effects(result, crate::effect::EffectRow::EMPTY)
    }

    /// Mint a returner with its closed set of permitted effect interfaces.
    ///
    /// # Specification
    /// - requires: the result and every operation type belong to this arena.
    /// - ensures: preserves the result type and the complete effect row.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nested thunk signatures retain row types
    ///   independently of the ids at which their equal children were allocated.
    /// - witness: `effect::tests::signature_inclusion_ignores_allocation_identity`
    #[spec(captures: expected = effects.clone(), ensures: |ret| self.comp_type(ret) == Some(&CompType::Returner { result, effects: expected.clone() }))]
    #[inline]
    pub fn comp_type_returner_with_effects(
        &mut self,
        result: ValueTypeId,
        effects: crate::effect::EffectRow,
    ) -> CompTypeId
    {
        self.alloc_comp_type(CompType::Returner { result, effects })
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

    /// Return the component of a tuple at a position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn computation_tuple_projection(
        &mut self,
        tuple: ValueId,
        component: gandr_kernel_term::Component,
    ) -> ComputationId
    {
        self.alloc_computation(Computation::TupleProjection(tuple, component))
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

    /// Mint the element identity `Path(A, a, b)`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn value_type_path(
        &mut self,
        carrier: ValueTypeId,
        left: ValueId,
        right: ValueId,
    ) -> ValueTypeId
    {
        self.alloc_value_type(ValueType::Path {
            carrier,
            left,
            right,
        })
    }

    /// Mint reflexivity `here(a)`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn value_here(
        &mut self,
        point: ValueId,
    ) -> ValueId
    {
        self.alloc_value(Value::Here(point))
    }

    /// Mint function extensionality `funext(f, g)`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn value_funext(
        &mut self,
        left: ValueId,
        right: ValueId,
    ) -> ValueId
    {
        self.alloc_value(Value::Funext(left, right))
    }

    /// Mint a universe equivalence `equiv(f, g)`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn value_equiv(
        &mut self,
        forward: ValueId,
        backward: ValueId,
    ) -> ValueId
    {
        self.alloc_value(Value::Equiv(forward, backward))
    }

    /// Mint univalence `ua(e)` over a bi-invertible record and its derived
    /// forward map.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn value_univalence(
        &mut self,
        equivalence: ValueId,
        forward: ValueId,
    ) -> ValueId
    {
        self.alloc_value(Value::Univalence(equivalence, forward))
    }

    /// Mint univalence at a stratum, `ua[n, k](a, b, f, g)`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn value_ua(
        &mut self,
        stratum: crate::ua::Stratum,
        sides: alloc::sync::Arc<crate::ua::Sides>,
        forward: ValueId,
        backward: ValueId,
    ) -> ValueId
    {
        self.alloc_value(Value::Ua {
            stratum,
            sides,
            forward,
            backward,
        })
    }

    /// Mint a session identity statement, `bisim(a, b)` or `sim(a, b)`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn value_session_related(
        &mut self,
        relation: crate::session::SessionRelation,
        source: ValueId,
        target: ValueId,
    ) -> ValueId
    {
        self.alloc_value(Value::SessionRelated {
            relation,
            source,
            target,
        })
    }

    /// Mint directed reflexivity `stay(a)`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn value_stay(
        &mut self,
        point: ValueId,
    ) -> ValueId
    {
        self.alloc_value(Value::Stay(point))
    }

    /// Mint directed composition `then(f, g)`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn value_then(
        &mut self,
        first: ValueId,
        second: ValueId,
    ) -> ValueId
    {
        self.alloc_value(Value::Then(first, second))
    }

    /// Mint the componentwise product `flowProduct(p, q)` of two universe
    /// flows.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn value_flow_product(
        &mut self,
        first: ValueId,
        second: ValueId,
    ) -> ValueId
    {
        self.alloc_value(Value::FlowProduct(first, second))
    }

    /// Mint the forward flow `forward(f)`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn value_forward(
        &mut self,
        translator: ValueId,
    ) -> ValueId
    {
        self.alloc_value(Value::Forward(translator))
    }

    /// Mint the function flow `arrow(d, c)` over a domain and a codomain flow.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn value_function_flow(
        &mut self,
        domain: ValueId,
        codomain: ValueId,
    ) -> ValueId
    {
        self.alloc_value(Value::FunctionFlow(domain, codomain))
    }

    /// Mint the recorded run of `moves`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn value_recorded(
        &mut self,
        moves: alloc::sync::Arc<[crate::session::RecordedMove]>,
    ) -> ValueId
    {
        self.alloc_value(Value::Recorded(moves))
    }

    /// Mint the directed identity `Flow(A, a, b)`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn value_type_flow(
        &mut self,
        carrier: ValueTypeId,
        source: ValueId,
        target: ValueId,
    ) -> ValueTypeId
    {
        self.alloc_value_type(ValueType::Flow {
            carrier,
            source,
            target,
        })
    }

    /// Mint the run type `Run(s)` of the session code `s`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn value_type_run(
        &mut self,
        session: ValueId,
    ) -> ValueTypeId
    {
        self.alloc_value_type(ValueType::Run(session))
    }

    /// Mint directed transport `ride(P, f, x)`, the motive under one
    /// intuitionistic binder.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn computation_ride(
        &mut self,
        motive: ValueTypeId,
        flow: ValueId,
        value: ValueId,
    ) -> ComputationId
    {
        self.alloc_computation(Computation::Ride {
            motive,
            flow,
            value,
        })
    }

    /// Mint the value a pure computation returns, standing as a value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn value_returned(
        &mut self,
        computation: ComputationId,
    ) -> ValueId
    {
        self.alloc_value(Value::Returned(computation))
    }

    /// Mint a computation written where a value is read, which elaboration runs
    /// or suspends by the type expected there.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn value_nested(
        &mut self,
        computation: ComputationId,
    ) -> ValueId
    {
        self.alloc_value(Value::Nested(computation))
    }

    /// Mint a written `run c` standing where a value is read.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn value_run(
        &mut self,
        computation: ComputationId,
    ) -> ValueId
    {
        self.alloc_value(Value::Run(computation))
    }

    /// Mint transport `tr(P, p, x)` along an element path, the motive under
    /// one intuitionistic binder.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn computation_path_transport(
        &mut self,
        motive: ValueTypeId,
        path: ValueId,
        value: ValueId,
    ) -> ComputationId
    {
        self.alloc_computation(Computation::PathTransport {
            motive,
            path,
            value,
        })
    }

    /// Mint transport over a two-entry telescope, the motive the dependent
    /// arrow `Π (y : A). Π (z : B). F C`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn computation_telescope_transport(
        &mut self,
        motive: CompTypeId,
        path: ValueId,
        start: ValueId,
        over: ValueId,
        value: ValueId,
    ) -> ComputationId
    {
        self.alloc_computation(Computation::TelescopeTransport {
            motive,
            path,
            start,
            over,
            value,
        })
    }

    /// Mint a typed hole in value position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn value_hole(
        &mut self,
        hole: HoleId,
    ) -> ValueId
    {
        self.alloc_value(Value::Hole(hole))
    }

    /// Mint a marked value over an already-allocated body.
    ///
    /// # Specification
    /// - requires: `body` names a value node already allocated in this arena.
    /// - ensures: appends the mark and returns a fresh id strictly above
    ///   `body`.
    /// - provides: the only way to mint this former, which is what keeps a
    ///   child id below its parent's.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two marks over unequal bodies and indices distinguish
    ///   a dropped index, a swapped body and a confused former.
    /// - witness: `arena::tests::a_mark_keeps_its_index_and_its_body`
    #[spec(ensures: |ret| self.value(ret) == Some(&Value::Mark { mark, body }))]
    #[inline]
    pub fn value_mark(
        &mut self,
        mark: MarkIndex,
        body: ValueId,
    ) -> ValueId
    {
        self.alloc_value(Value::Mark { mark, body })
    }

    /// Mint a typed hole in computation position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn computation_hole(
        &mut self,
        hole: HoleId,
    ) -> ComputationId
    {
        self.alloc_computation(Computation::Hole(hole))
    }

    /// Mint a marked computation over an already-allocated body.
    ///
    /// # Specification
    /// - requires: `body` names a computation node already allocated in this
    ///   arena.
    /// - ensures: appends the mark and returns a fresh id strictly above
    ///   `body`.
    /// - provides: the only way to mint this former, which is what keeps a
    ///   child id below its parent's.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two marks over unequal bodies and indices distinguish
    ///   a dropped index, a swapped body and a confused former.
    /// - witness: `arena::tests::a_mark_keeps_its_index_and_its_body`
    #[spec(ensures: |ret| self.computation(ret) == Some(&Computation::Mark { mark, body }))]
    #[inline]
    pub fn computation_mark(
        &mut self,
        mark: MarkIndex,
        body: ComputationId,
    ) -> ComputationId
    {
        self.alloc_computation(Computation::Mark { mark, body })
    }

    /// Mint the unknown value type.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn value_type_unknown(&mut self) -> ValueTypeId
    {
        self.alloc_value_type(ValueType::Unknown)
    }

    /// Mint the unknown computation type.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn comp_type_unknown(&mut self) -> CompTypeId
    {
        self.alloc_comp_type(CompType::Unknown)
    }

    /// Mint a native List type over an existing element type.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn value_type_list(
        &mut self,
        element: ValueTypeId,
    ) -> ValueTypeId
    {
        self.alloc_value_type(ValueType::List(element))
    }

    /// Mint the empty native list.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn value_list_nil(&mut self) -> ValueId
    {
        self.alloc_value(Value::ListNil)
    }

    /// Mint a native list cell.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn value_list_cons(
        &mut self,
        head: ValueId,
        tail: ValueId,
    ) -> ValueId
    {
        self.alloc_value(Value::ListCons(head, tail))
    }

    /// Mint a pure right fold; the cell branch binds head then folded result.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn computation_list_fold(
        &mut self,
        element: ValueTypeId,
        result: ValueTypeId,
        list: ValueId,
        on_nil: ComputationId,
        on_cons: ComputationId,
    ) -> ComputationId
    {
        self.alloc_computation(Computation::ListFold {
            element,
            result,
            list,
            on_nil,
            on_cons,
        })
    }
}

#[cfg(test)]
mod tests;
