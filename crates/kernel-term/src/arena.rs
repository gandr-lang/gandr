//! The append-only term arena: the single owner of every term and type node,
//! addressed by four typed `u32`-backed node ids.
//!
//! # Why an arena rather than owned trees
//!
//! A deep uniquely-owned tree still recurses on destruction, and a decoder can
//! build an arbitrarily deep graph from bytes: an adversary offers one, has it
//! rejected, and overflows the stack *dropping* it. Iterative decode and
//! iterative checking do not cover deallocation, so under owned pointers the
//! answer is a hand-written iterative destructor that becomes a permanent
//! fixture of the trusted base.
//!
//! The arena **dissolves** that obligation rather than managing it. Ids are
//! `Copy`, so no deep clone exists to make iterative; teardown is a flat vector
//! drop with no recursive drop glue; and the derived equality, hashing and
//! debug instances are shallow over ids. This is also the sanctioned form of
//! the flat-representation rule: recursive owned data is id-addressed, so the
//! type plane has no owning-pointer cycle to reject.
//!
//! # The two disciplines, both enforced rather than documented
//!
//! - **Constructor-only minting.** An id is produced only by a [`TermArena`]
//!   constructor over already-allocated children, so a child id always resolves
//!   and is always strictly less than its parent's — acyclic by construction,
//!   and the same strictly-earlier invariant the subterm table relies on.
//! - **The admission watermark.** [`TermArena::watermark`] snapshots the four
//!   family lengths and [`TermArena::truncate_to`] restores them, so a
//!   checker's intermediates allocate past a mark and are dropped after the
//!   verdict — on rejection and on success alike, leaving the persistent arena
//!   holding only admitted content.
//!
//! # The honest cost
//!
//! An owned tree cannot be ill-formed; a `u32` id *can* name no node, or a node
//! in another arena. The mitigations that keep that fail-closed are
//! constructor-only minting, one arena per environment, a checked lookup
//! returning an option rather than an index, and decode-side validation of
//! every child reference before it mints.

use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_strata::Level;

use crate::base::BaseType;
use crate::base::Literal;
use crate::term::Computation;
use crate::term::ConstantIndex;
use crate::term::DeBruijnIndex;
use crate::term::Side;
use crate::term::Value;
use crate::types::CompType;
use crate::types::ValueType;

/// The id of a [`Value`] node in a [`TermArena`].
///
/// Minted only by a [`TermArena`] constructor over already-allocated children,
/// so it always resolves and is strictly greater than every child id.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ValueId(u32);

/// The id of a [`Computation`] node in a [`TermArena`].
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ComputationId(u32);

/// The id of a [`ValueType`] node in a [`TermArena`].
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ValueTypeId(u32);

/// The id of a [`CompType`] node in a [`TermArena`].
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CompTypeId(u32);

/// A cross-family node reference: the work item every walk over the arena's
/// edge relation carries.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum AnyNode
{
    /// A value node.
    Value(ValueId),
    /// A computation node.
    Computation(ComputationId),
    /// A value-type node.
    ValueType(ValueTypeId),
    /// A computation-type node.
    CompType(CompTypeId),
}

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
/// - ensures: the equal index, or the `u32` ceiling when the arena exceeded the
///   id space — about four billion nodes, far above the decode entry cap, so
///   the saturation is a documented ceiling rather than a reachable path.
/// - provides: the total, panic-free length-to-index widening. Arena provenance
///   stays prose: the length carries no arena identity.
/// - fails: never; it saturates.
/// - panics: none.
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
/// - ensures: the equal offset, lossless on every supported platform of at
///   least 32 bits.
/// - provides: the total, panic-free index-to-offset narrowing.
/// - fails: never; it saturates at the offset ceiling, which a checked read
///   then rejects.
/// - panics: none.
#[inline]
#[spec(ensures: |ret| ret.0 == usize::try_from(index.0).unwrap_or(usize::MAX))]
fn id_offset(index: ArenaIndex) -> ArenaLength
{
    ArenaLength(usize::try_from(index.0).unwrap_or(usize::MAX))
}

/// Clamp one family length into an inclusive length interval.
///
/// # Specification
/// - requires: nothing — a `low` above `high` is admissible and resolves to
///   `low`, so the result is defined on every input rather than on a
///   precondition the caller carries.
/// - ensures: `low` when `value` is below it, `high` when `value` is above it,
///   and `value` otherwise.
/// - provides: the per-family step of [`ArenaWatermark::clamped_into`]. The
///   const API stays unannotated: the pinned `anodized` expansion calls a
///   non-const evaluator (`E0015`).
/// - fails: never.
/// - panics: none — unlike the standard clamp, which panics on an inverted
///   interval.
#[inline]
const fn clamp_length(
    value: ArenaLength,
    low: ArenaLength,
    high: ArenaLength,
) -> ArenaLength
{
    let capped = if value.0 < high.0 { value.0 } else { high.0 };
    ArenaLength(if capped > low.0 { capped } else { low.0 })
}

/// A snapshot of the four family lengths: the admission watermark.
///
/// Restoring an arena to a watermark drops exactly the nodes allocated after
/// it, as four flat vector truncations. The default is the empty arena's
/// watermark, which is the floor an environment starts at.
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

impl ArenaWatermark
{
    /// Clamp this watermark, family by family, into the inclusive interval
    /// `[low, high]`.
    ///
    /// This is the rollback mark an admission choke point truncates to when it
    /// rejects: the declaration's content-start mark, clamped between the
    /// admission floor and the mark taken on entry. The clamp is what stops a
    /// rollback from reaching below content a prior admission committed when
    /// staging order is not admission order, and from leaving an intermediate
    /// behind when the content-start mark is not the one the arena grew from.
    ///
    /// # Specification
    /// - requires: nothing — every combination is defined, including a `low`
    ///   above `high`, which yields `low`, so no caller carries an ordering
    ///   precondition.
    /// - ensures: each family length is `low`'s when this one is below it,
    ///   `high`'s when this one is above it, and this one otherwise; `self`
    ///   unchanged when it lies within the interval in every family.
    /// - provides: the rejection rollback mark of an admission choke point. The
    ///   const API stays unannotated: the pinned `anodized` expansion calls a
    ///   non-const evaluator (`E0015`).
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — four independent clamps with one decision surface
    ///   each, separated by a below-interval, an above-interval, an
    ///   inside-interval and an inverted-interval mark, each asserted exactly.
    /// - witness: `arena::tests::a_watermark_clamps_into_its_interval`
    #[inline]
    #[must_use]
    pub const fn clamped_into(
        self,
        low: Self,
        high: Self,
    ) -> Self
    {
        Self {
            values: clamp_length(
                ArenaLength(self.values),
                ArenaLength(low.values),
                ArenaLength(high.values),
            )
            .0,
            computations: clamp_length(
                ArenaLength(self.computations),
                ArenaLength(low.computations),
                ArenaLength(high.computations),
            )
            .0,
            value_types: clamp_length(
                ArenaLength(self.value_types),
                ArenaLength(low.value_types),
                ArenaLength(high.value_types),
            )
            .0,
            comp_types: clamp_length(
                ArenaLength(self.comp_types),
                ArenaLength(low.comp_types),
                ArenaLength(high.comp_types),
            )
            .0,
        }
    }
}

/// The append-only arena owning every term and type node of one environment.
///
/// The four families are parallel append-only vectors and a node's children are
/// ids into the same arena. The node enums derive shallow clone and drop, so
/// cloning or dropping a whole arena is a flat per-family vector operation,
/// total on any term depth.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct TermArena
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

impl TermArena
{
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
    /// - requires: nothing.
    /// - ensures: returns the four families' current lengths.
    /// - provides: the mark [`Self::truncate_to`] takes, truncating each family
    ///   to `min(current_len, mark)`, so a checker's intermediates are dropped
    ///   after a verdict. The mark carries no arena identity, so pairing it
    ///   with the arena it came from is the caller's.
    /// - panics: none.
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

    /// Truncate each family to `min(current_len, watermark)`, dropping later
    /// allocations.
    ///
    /// # Specification
    /// - requires: `watermark` was taken from this arena, and every id minted
    ///   after it is unreachable from content the caller retains, which the
    ///   admission discipline establishes. A family already shorter than the
    ///   mark is admissible: its truncation is a no-op.
    /// - ensures: each family's length becomes `min(entry_len, watermark)` —
    ///   the mark's length where the family is longer, the length it already
    ///   has where it is shorter; an id whose index is at or past the resulting
    ///   length dangles, and a lookup of one fails closed rather than resolving
    ///   to a later node.
    /// - provides: the truncation an admission choke point performs after a
    ///   verdict, on rejection and on success alike. The clause checks family
    ///   lengths, including the stale-mark no-op. Arena provenance,
    ///   retained-node identity and external reachability stay prose: the
    ///   watermark has no arena identity, and checking retained nodes would
    ///   require an owned arena snapshot.
    /// - fails: never — a truncation past the end is a no-op, so a stale
    ///   watermark cannot grow the arena.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the truncation has one decision surface per family,
    ///   separated by a mark below the current length and a mark at it, with
    ///   the post-truncation lookup of a dropped id asserted to be absent.
    /// - witness: `arena::tests::truncating_to_a_watermark_drops_later_nodes`
    #[inline]
    #[spec(
        captures: entry_watermark = self.watermark(),
        ensures: self.watermark()
            == watermark.clamped_into(ArenaWatermark::default(), entry_watermark),
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
    /// - requires: nothing; a dangling or foreign id is admissible input.
    /// - ensures: returns the value node `id` names, and `None` exactly when
    ///   the id's index is past this family's length — after a truncation past
    ///   it, or for an id this arena never minted.
    /// - provides: the checked lookup that keeps a `u32` id fail-closed; no
    ///   unchecked resolution path exists.
    /// - panics: none.
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
    /// - requires: nothing; a dangling or foreign id is admissible input.
    /// - ensures: returns the computation node `id` names, and `None` exactly
    ///   when the id's index is past this family's length.
    /// - provides: the checked lookup that keeps a `u32` id fail-closed; no
    ///   unchecked resolution path exists.
    /// - panics: none.
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
    /// - requires: nothing; a dangling or foreign id is admissible input.
    /// - ensures: returns the value-type node `id` names, and `None` exactly
    ///   when the id's index is past this family's length.
    /// - provides: the checked lookup that keeps a `u32` id fail-closed; no
    ///   unchecked resolution path exists.
    /// - panics: none.
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
    /// - requires: nothing; a dangling or foreign id is admissible input.
    /// - ensures: returns the computation-type node `id` names, and `None`
    ///   exactly when the id's index is past this family's length.
    /// - provides: the checked lookup that keeps a `u32` id fail-closed; no
    ///   unchecked resolution path exists.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub fn comp_type(
        &self,
        id: CompTypeId,
    ) -> Option<&CompType>
    {
        self.comp_types.get(id_offset(ArenaIndex(id.0)).0)
    }

    /// Append a value node and return the id that names it.
    ///
    /// # Specification
    /// - requires: every child id inside `value` resolves in this arena.
    /// - ensures: appends the node and returns the value family's length before
    ///   the push, saturated at the `u32` ceiling; while that length fits `u32`
    ///   the id names the appended node and is greater than every value id
    ///   currently live in this arena.
    /// - provides: the single minting site for a [`ValueId`], which is what
    ///   puts constructor-only minting in one checkable place. An id is a
    ///   family index, so [`Self::truncate_to`] makes index reuse a supported
    ///   path: after a truncation the next push mints an id equal to one minted
    ///   before it; and above the ceiling [`id_index`] saturates at, the
    ///   returned id no longer names the appended node.
    /// - panics: none.
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

    /// Append a computation node and return the id that names it.
    ///
    /// # Specification
    /// - requires: every child id inside `computation` resolves in this arena.
    /// - ensures: appends the node and returns the computation family's length
    ///   before the push, saturated at the `u32` ceiling; while that length
    ///   fits `u32` the id names the appended node and is greater than every
    ///   computation id currently live in this arena.
    /// - provides: the single minting site for a [`ComputationId`].
    /// - panics: none.
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

    /// Append a value-type node and return the id that names it.
    ///
    /// # Specification
    /// - requires: every child id inside `value_type` resolves in this arena.
    /// - ensures: appends the node and returns the value-type family's length
    ///   before the push, saturated at the `u32` ceiling; while that length
    ///   fits `u32` the id names the appended node and is greater than every
    ///   value-type id currently live in this arena.
    /// - provides: the single minting site for a [`ValueTypeId`].
    /// - panics: none.
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

    /// Append a computation-type node and return the id that names it.
    ///
    /// # Specification
    /// - requires: every child id inside `comp_type` resolves in this arena.
    /// - ensures: appends the node and returns the computation-type family's
    ///   length before the push, saturated at the `u32` ceiling; while that
    ///   length fits `u32` the id names the appended node and is greater than
    ///   every computation-type id currently live in this arena.
    /// - provides: the single minting site for a [`CompTypeId`].
    /// - panics: none.
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

    /// Mint a bound value variable.
    ///
    /// # Specification
    /// - requires: nothing; a de Bruijn index is an inline payload, and whether
    ///   it names an enclosing binder is a typing fact.
    /// - ensures: appends the node and returns the value family's length before
    ///   the push, saturated at the `u32` ceiling; while that length fits `u32`
    ///   the id names the appended node and is greater than every value id
    ///   currently live in this arena.
    /// - provides: the only way to obtain a [`ValueId`] for a bound variable.
    /// - panics: none.
    #[inline]
    pub fn value_variable(
        &mut self,
        index: DeBruijnIndex,
    ) -> ValueId
    {
        self.alloc_value(Value::Variable(index))
    }

    /// Mint a constant reference to a prior declaration.
    ///
    /// # Specification
    /// - requires: nothing; whether the admission position names an admitted
    ///   declaration is a typing fact, refused at the choke point rather than
    ///   here.
    /// - ensures: appends the node and returns the value family's length before
    ///   the push, saturated at the `u32` ceiling; while that length fits `u32`
    ///   the id names the appended node and is greater than every value id
    ///   currently live in this arena.
    /// - provides: the only way to obtain a [`ValueId`] for a constant
    ///   reference.
    /// - panics: none.
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
    /// - requires: nothing.
    /// - ensures: appends the node and returns the value family's length before
    ///   the push, saturated at the `u32` ceiling; while that length fits `u32`
    ///   the id names the appended node and is greater than every value id
    ///   currently live in this arena.
    /// - provides: the only way to obtain a [`ValueId`] for the unit value.
    /// - panics: none.
    #[inline]
    pub fn value_unit(&mut self) -> ValueId
    {
        self.alloc_value(Value::Unit)
    }

    /// Mint a base-type literal value.
    ///
    /// # Specification
    /// - requires: nothing; the literal is an inline payload, and whether it
    ///   inhabits its base type is a typing fact.
    /// - ensures: appends the node and returns the value family's length before
    ///   the push, saturated at the `u32` ceiling; while that length fits `u32`
    ///   the id names the appended node and is greater than every value id
    ///   currently live in this arena.
    /// - provides: the only way to obtain a [`ValueId`] for a literal.
    /// - panics: none.
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
    /// - requires: `first` and `second` resolve in this arena.
    /// - ensures: appends the node and returns the value family's length before
    ///   the push, saturated at the `u32` ceiling; while that length fits `u32`
    ///   the id names the appended node and is strictly greater than both child
    ///   ids, which the precondition keeps live.
    /// - provides: the pair node, acyclic by construction; the id ordering is
    ///   what the subterm table's strictly-earlier invariant rests on.
    /// - panics: none.
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
    /// - requires: `body` resolves in this arena.
    /// - ensures: appends the node on the named side and returns the value
    ///   family's length before the push, saturated at the `u32` ceiling; while
    ///   that length fits `u32` the id names the appended node and is strictly
    ///   greater than `body`, which the precondition keeps live.
    /// - provides: the injection node, acyclic by construction; which summand
    ///   the side selects is a typing fact.
    /// - panics: none.
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
    /// - requires: `body` resolves in this arena's computation family.
    /// - ensures: appends the node and returns the value family's length before
    ///   the push, saturated at the `u32` ceiling; while that length fits `u32`
    ///   the id names the appended node and is greater than every value id
    ///   currently live in this arena.
    /// - provides: the one value form embedding a computation, which suspends
    ///   rather than runs it. The child crosses families, so the two ids share
    ///   no allocation order and none is claimed.
    /// - panics: none.
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
    /// - requires: `body` resolves in this arena; whether its type's level sits
    ///   strictly below `target` is a typing fact.
    /// - ensures: appends the node and returns the value family's length before
    ///   the push, saturated at the `u32` ceiling; while that length fits `u32`
    ///   the id names the appended node and is strictly greater than `body`,
    ///   which the precondition keeps live.
    /// - provides: the written lift; there is no implicit cumulativity, so a
    ///   lift exists only where a producer minted one.
    /// - panics: none.
    #[inline]
    pub fn value_lift(
        &mut self,
        target: Level,
        body: ValueId,
    ) -> ValueId
    {
        self.alloc_value(Value::Lift { target, body })
    }

    // Computation constructors.

    /// Mint a lambda over an already-allocated computation body.
    ///
    /// # Specification
    /// - requires: `body` resolves in this arena.
    /// - ensures: appends the node and returns the computation family's length
    ///   before the push, saturated at the `u32` ceiling; while that length
    ///   fits `u32` the id names the appended node and is strictly greater than
    ///   `body`, which the precondition keeps live.
    /// - provides: the lambda node, acyclic by construction; the binder is
    ///   positional, so no name is represented.
    /// - panics: none.
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
    /// - requires: `head` and `argument` resolve in this arena, in its
    ///   computation and value families respectively.
    /// - ensures: appends the node and returns the computation family's length
    ///   before the push, saturated at the `u32` ceiling; while that length
    ///   fits `u32` the id names the appended node and is greater than every
    ///   computation id currently live in this arena, `head` included.
    /// - provides: the application node; whether the argument matches the
    ///   head's domain is a typing fact.
    /// - panics: none.
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
    /// - requires: `value` resolves in this arena's value family.
    /// - ensures: appends the node and returns the computation family's length
    ///   before the push, saturated at the `u32` ceiling; while that length
    ///   fits `u32` the id names the appended node and is greater than every
    ///   computation id currently live in this arena.
    /// - provides: the returner node. The child crosses families, so the two
    ///   ids share no allocation order and none is claimed.
    /// - panics: none.
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
    /// - requires: `bound` and `body` resolve in this arena.
    /// - ensures: appends the node and returns the computation family's length
    ///   before the push, saturated at the `u32` ceiling; while that length
    ///   fits `u32` the id names the appended node and is strictly greater than
    ///   both child ids, which the precondition keeps live.
    /// - provides: the sequencing node; the value `bound` returns is bound
    ///   positionally in `body`.
    /// - panics: none.
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
    /// - requires: `value` resolves in this arena's value family.
    /// - ensures: appends the node and returns the computation family's length
    ///   before the push, saturated at the `u32` ceiling; while that length
    ///   fits `u32` the id names the appended node and is greater than every
    ///   computation id currently live in this arena.
    /// - provides: the force node. Whether `value` is a thunk is a typing fact,
    ///   and the child crosses families, so no id ordering is claimed.
    /// - panics: none.
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
    /// - requires: `scrutinee`, `on_left`, and `on_right` resolve in this
    ///   arena, the scrutinee in its value family and the branches in its
    ///   computation family.
    /// - ensures: appends the node and returns the computation family's length
    ///   before the push, saturated at the `u32` ceiling; while that length
    ///   fits `u32` the id names the appended node and is strictly greater than
    ///   both branch ids, which the precondition keeps live.
    /// - provides: the sum elimination; each branch is checked with the
    ///   injected value bound, which is a typing fact rather than a
    ///   representation one.
    /// - panics: none.
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
    /// - requires: nothing; the base type is an inline payload.
    /// - ensures: appends the node and returns the value-type family's length
    ///   before the push, saturated at the `u32` ceiling; while that length
    ///   fits `u32` the id names the appended node and is greater than every
    ///   value-type id currently live in this arena.
    /// - provides: the only way to obtain a [`ValueTypeId`] for a base type.
    /// - panics: none.
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
    /// - requires: nothing.
    /// - ensures: appends the node and returns the value-type family's length
    ///   before the push, saturated at the `u32` ceiling; while that length
    ///   fits `u32` the id names the appended node and is greater than every
    ///   value-type id currently live in this arena.
    /// - provides: the only way to obtain a [`ValueTypeId`] for the unit type.
    /// - panics: none.
    #[inline]
    pub fn value_type_unit(&mut self) -> ValueTypeId
    {
        self.alloc_value_type(ValueType::Unit)
    }

    /// Mint a product over two already-allocated value types.
    ///
    /// # Specification
    /// - requires: `first` and `second` resolve in this arena.
    /// - ensures: appends the node and returns the value-type family's length
    ///   before the push, saturated at the `u32` ceiling; while that length
    ///   fits `u32` the id names the appended node and is strictly greater than
    ///   both child ids, which the precondition keeps live.
    /// - provides: the product type, acyclic by construction.
    /// - panics: none.
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
    /// - requires: `first` and `second` resolve in this arena.
    /// - ensures: appends the node and returns the value-type family's length
    ///   before the push, saturated at the `u32` ceiling; while that length
    ///   fits `u32` the id names the appended node and is strictly greater than
    ///   both child ids, which the precondition keeps live.
    /// - provides: the sum type, acyclic by construction; the summand order is
    ///   the order the two arguments are given in.
    /// - panics: none.
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
    /// - requires: `body` resolves in this arena's computation-type family.
    /// - ensures: appends the node and returns the value-type family's length
    ///   before the push, saturated at the `u32` ceiling; while that length
    ///   fits `u32` the id names the appended node and is greater than every
    ///   value-type id currently live in this arena.
    /// - provides: the thunk type `U C`. The child crosses families, so the two
    ///   ids share no allocation order and none is claimed.
    /// - panics: none.
    #[inline]
    pub fn value_type_thunk(
        &mut self,
        body: CompTypeId,
    ) -> ValueTypeId
    {
        self.alloc_value_type(ValueType::Thunk(body))
    }

    /// Mint a universe value type at a canonical level.
    ///
    /// # Specification
    /// - requires: `level` is a canonical level; the arena stores it as given.
    /// - ensures: appends the node and returns the value-type family's length
    ///   before the push, saturated at the `u32` ceiling; while that length
    ///   fits `u32` the id names the appended node and is greater than every
    ///   value-type id currently live in this arena.
    /// - provides: the universe type at that level.
    /// - panics: none.
    #[inline]
    pub fn value_type_universe(
        &mut self,
        level: Level,
    ) -> ValueTypeId
    {
        self.alloc_value_type(ValueType::Universe(level))
    }

    /// Mint a reference to a sealed abstract type by its declaration's
    /// admission position.
    ///
    /// Minting does not check the position: whether it names an admitted
    /// abstract-type declaration is a typing fact, so an unadmitted position is
    /// a rejection at the choke point rather than an unrepresentable node here.
    ///
    /// # Specification
    /// - requires: nothing; the admission position is checked at the choke
    ///   point rather than here.
    /// - ensures: appends the node and returns the value-type family's length
    ///   before the push, saturated at the `u32` ceiling; while that length
    ///   fits `u32` the id names the appended node and is greater than every
    ///   value-type id currently live in this arena.
    /// - provides: the reference to a sealed abstract type, representable
    ///   whether or not the position is admitted.
    /// - panics: none.
    #[inline]
    pub fn value_type_abstract(
        &mut self,
        atom: ConstantIndex,
    ) -> ValueTypeId
    {
        self.alloc_value_type(ValueType::Abstract(atom))
    }

    /// Mint the type a code denotes, over an already-allocated code value.
    ///
    /// Minting checks neither the code nor the level: that the code inhabits
    /// `Universe target` is a typing fact, so a mismatched pair is a rejection
    /// at the choke point rather than an unrepresentable node here.
    ///
    /// # Specification
    /// - requires: `code` resolves in this arena's value family; whether it
    ///   inhabits `Universe target` is checked at the choke point.
    /// - ensures: appends the node and returns the value-type family's length
    ///   before the push, saturated at the `u32` ceiling; while that length
    ///   fits `u32` the id names the appended node and is greater than every
    ///   value-type id currently live in this arena.
    /// - provides: the type a code denotes. The child crosses families, so the
    ///   two ids share no allocation order and none is claimed.
    /// - panics: none.
    #[inline]
    pub fn value_type_element(
        &mut self,
        code: ValueId,
        target: Level,
    ) -> ValueTypeId
    {
        self.alloc_value_type(ValueType::Element { code, target })
    }

    /// Mint a value-type lift over an already-allocated inner value type.
    ///
    /// # Specification
    /// - requires: `inner` resolves in this arena.
    /// - ensures: appends the node and returns the value-type family's length
    ///   before the push, saturated at the `u32` ceiling; while that length
    ///   fits `u32` the id names the appended node and is strictly greater than
    ///   `inner`, which the precondition keeps live.
    /// - provides: the written type-level lift; whether `inner`'s level sits
    ///   below `target` is a typing fact.
    /// - panics: none.
    #[inline]
    pub fn value_type_lift(
        &mut self,
        inner: ValueTypeId,
        target: Level,
    ) -> ValueTypeId
    {
        self.alloc_value_type(ValueType::Lift { inner, target })
    }

    // Computation-type constructors.

    /// Mint a returner type over an already-allocated value type.
    ///
    /// # Specification
    /// - requires: `result` resolves in this arena's value-type family.
    /// - ensures: appends the node and returns the computation-type family's
    ///   length before the push, saturated at the `u32` ceiling; while that
    ///   length fits `u32` the id names the appended node and is greater than
    ///   every computation-type id currently live in this arena.
    /// - provides: the returner type `F A`. The child crosses families, so the
    ///   two ids share no allocation order and none is claimed.
    /// - panics: none.
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
    /// - requires: `domain` and `codomain` resolve in this arena, in its
    ///   value-type and computation-type families respectively.
    /// - ensures: appends the node and returns the computation-type family's
    ///   length before the push, saturated at the `u32` ceiling; while that
    ///   length fits `u32` the id names the appended node and is strictly
    ///   greater than `codomain`, which the precondition keeps live.
    /// - provides: the non-dependent arrow, where the codomain does not read
    ///   the domain's binder.
    /// - panics: none.
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
    /// binder is a typing fact rather than a representation one, so a
    /// codomain that ignores it is representable here and is the producer's
    /// obligation rather than an unrepresentable node.
    ///
    /// # Specification
    /// - requires: `domain` and `codomain` resolve in this arena, in its
    ///   value-type and computation-type families respectively.
    /// - ensures: appends the node and returns the computation-type family's
    ///   length before the push, saturated at the `u32` ceiling; while that
    ///   length fits `u32` the id names the appended node and is strictly
    ///   greater than `codomain`, which the precondition keeps live.
    /// - provides: the dependent arrow. Whether the codomain reads the domain's
    ///   binder is the producer's obligation, not a representation one, so a
    ///   codomain that ignores it is still representable.
    /// - panics: none.
    #[inline]
    pub fn comp_type_pi(
        &mut self,
        domain: ValueTypeId,
        codomain: CompTypeId,
    ) -> CompTypeId
    {
        self.alloc_comp_type(CompType::Pi { domain, codomain })
    }

    /// The immediate child references of `node`, in the order the format writes
    /// them.
    ///
    /// # Specification
    /// - requires: nothing — a dangling id is admissible input.
    /// - ensures: the node's child ids in wire order, each strictly less than
    ///   the node's own id under the minting invariant; the empty list for a
    ///   leaf and for a dangling id, which is the fail-closed reading.
    /// - provides: the edge relation every walk over the arena follows, and the
    ///   arities the node-tag table is pinned against. The clause checks the
    ///   exact wire-ordered children without allocation. Strictly-earlier
    ///   minting stays prose: ids from different families have no shared
    ///   allocation-order index.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the tag table's declared arities are differentially
    ///   compared against this function over one node of every former, so a
    ///   dropped or reordered child arm changes an arity or a wire image; the
    ///   L3 residue is the dangling id, asserted to yield no child.
    /// - witness: `arena::tests::a_dangling_node_has_no_children`
    /// - witness: `tags::tests::the_tag_table_matches_the_wire_arities`
    #[must_use]
    #[spec(ensures: |ret| match node {
        AnyNode::Value(id) => match self.value(id) {
            Some(&Value::Variable(_) | &Value::Constant(_) | &Value::Unit | &Value::Literal(_))
            | None => ret.is_empty(),
            Some(&Value::Pair(first, second)) =>
                ret.as_slice() == [AnyNode::Value(first), AnyNode::Value(second)],
            Some(&Value::Injection(_, body) | &Value::Lift { body, .. }) =>
                ret.as_slice() == [AnyNode::Value(body)],
            Some(&Value::Thunk(body)) => ret.as_slice() == [AnyNode::Computation(body)],
        },
        AnyNode::Computation(id) => match self.computation(id) {
            None => ret.is_empty(),
            Some(&Computation::Lambda(body)) => ret.as_slice() == [AnyNode::Computation(body)],
            Some(&Computation::Application(head, argument)) =>
                ret.as_slice() == [AnyNode::Computation(head), AnyNode::Value(argument)],
            Some(&Computation::Return(value) | &Computation::Force(value)) =>
                ret.as_slice() == [AnyNode::Value(value)],
            Some(&Computation::Bind(bound, body)) =>
                ret.as_slice() == [AnyNode::Computation(bound), AnyNode::Computation(body)],
            Some(&Computation::Case { scrutinee, on_left, on_right }) =>
                ret.as_slice() == [
                    AnyNode::Value(scrutinee),
                    AnyNode::Computation(on_left),
                    AnyNode::Computation(on_right),
                ],
        },
        AnyNode::ValueType(id) => match self.value_type(id) {
            Some(&ValueType::Base(_) | &ValueType::Unit | &ValueType::Universe(_) | &ValueType::Abstract(_))
            | None => ret.is_empty(),
            Some(&ValueType::Product(first, second) | &ValueType::Sum(first, second)) =>
                ret.as_slice() == [AnyNode::ValueType(first), AnyNode::ValueType(second)],
            Some(&ValueType::Thunk(body)) => ret.as_slice() == [AnyNode::CompType(body)],
            Some(&ValueType::Lift { inner, .. }) => ret.as_slice() == [AnyNode::ValueType(inner)],
            Some(&ValueType::Element { code, .. }) => ret.as_slice() == [AnyNode::Value(code)],
        },
        AnyNode::CompType(id) => match self.comp_type(id) {
            None => ret.is_empty(),
            Some(&CompType::Returner(result)) => ret.as_slice() == [AnyNode::ValueType(result)],
            Some(&CompType::Arrow { domain, codomain } | &CompType::Pi { domain, codomain }) =>
                ret.as_slice() == [AnyNode::ValueType(domain), AnyNode::CompType(codomain)],
        },
    })]
    pub(crate) fn children_of(
        &self,
        node: AnyNode,
    ) -> Vec<AnyNode>
    {
        let mut children: Vec<AnyNode> = Vec::new();
        match node {
            | AnyNode::Value(id) => match self.value(id) {
                | Some(
                    &Value::Variable(_) | &Value::Constant(_) | &Value::Unit | &Value::Literal(_),
                )
                | None => {},
                | Some(&Value::Pair(first, second)) => {
                    children.push(AnyNode::Value(first));
                    children.push(AnyNode::Value(second));
                },
                | Some(&Value::Injection(_, body) | &Value::Lift { body, .. }) => {
                    children.push(AnyNode::Value(body));
                },
                | Some(&Value::Thunk(body)) => children.push(AnyNode::Computation(body)),
            },
            | AnyNode::Computation(id) => match self.computation(id) {
                | None => {},
                | Some(&Computation::Lambda(body)) => children.push(AnyNode::Computation(body)),
                | Some(&Computation::Application(head, argument)) => {
                    children.push(AnyNode::Computation(head));
                    children.push(AnyNode::Value(argument));
                },
                | Some(&Computation::Return(value) | &Computation::Force(value)) => {
                    children.push(AnyNode::Value(value));
                },
                | Some(&Computation::Bind(bound, body)) => {
                    children.push(AnyNode::Computation(bound));
                    children.push(AnyNode::Computation(body));
                },
                | Some(&Computation::Case {
                    scrutinee,
                    on_left,
                    on_right,
                }) => {
                    children.push(AnyNode::Value(scrutinee));
                    children.push(AnyNode::Computation(on_left));
                    children.push(AnyNode::Computation(on_right));
                },
            },
            | AnyNode::ValueType(id) => match self.value_type(id) {
                | Some(
                    &ValueType::Base(_)
                    | &ValueType::Unit
                    | &ValueType::Universe(_)
                    | &ValueType::Abstract(_),
                )
                | None => {},
                | Some(&ValueType::Product(first, second) | &ValueType::Sum(first, second)) => {
                    children.push(AnyNode::ValueType(first));
                    children.push(AnyNode::ValueType(second));
                },
                | Some(&ValueType::Thunk(body)) => children.push(AnyNode::CompType(body)),
                | Some(&ValueType::Lift { inner, .. }) => children.push(AnyNode::ValueType(inner)),
                // The one edge that leaves the type language: a code is a value,
                // which is what lets a type mention a bound variable at all.
                | Some(&ValueType::Element { code, .. }) => children.push(AnyNode::Value(code)),
            },
            | AnyNode::CompType(id) => match self.comp_type(id) {
                | None => {},
                | Some(&CompType::Returner(result)) => children.push(AnyNode::ValueType(result)),
                | Some(
                    &CompType::Arrow { domain, codomain } | &CompType::Pi { domain, codomain },
                ) => {
                    children.push(AnyNode::ValueType(domain));
                    children.push(AnyNode::CompType(codomain));
                },
            },
        }
        children
    }
}

#[cfg(test)]
mod tests
{
    use super::AnyNode;
    use super::ArenaWatermark;
    use super::TermArena;
    use super::ValueId;

    #[test]
    fn a_child_id_is_strictly_below_its_parent()
    {
        let mut arena = TermArena::new();
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
        let mut arena = TermArena::new();
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
    fn a_watermark_clamps_into_its_interval()
    {
        let mut arena = TermArena::new();
        let low = arena.watermark();
        let _first = arena.value_unit();
        let middle = arena.watermark();
        let _second = arena.value_unit();
        let high = arena.watermark();

        assert_eq!(
            low,
            low.clamped_into(low, high),
            "a mark at the floor holds"
        );
        assert_eq!(
            middle,
            middle.clamped_into(low, high),
            "a mark inside the interval holds"
        );
        assert_eq!(
            middle,
            high.clamped_into(low, middle),
            "a mark above the ceiling clamps down"
        );
        assert_eq!(
            middle,
            low.clamped_into(middle, high),
            "a mark below the floor clamps up"
        );
        assert_eq!(
            high,
            middle.clamped_into(high, low),
            "an inverted interval resolves to its floor"
        );
    }

    #[test]
    fn a_dangling_node_has_no_children()
    {
        let arena = TermArena::new();
        let dangling = AnyNode::Value(ValueId(7));
        assert!(
            arena.children_of(dangling).is_empty(),
            "an unresolvable id yields no children rather than panicking"
        );
    }

    #[test]
    fn the_default_watermark_is_the_empty_arena()
    {
        let arena = TermArena::new();
        assert_eq!(
            ArenaWatermark::default(),
            arena.watermark(),
            "an empty arena sits at the admission floor"
        );
    }
}
