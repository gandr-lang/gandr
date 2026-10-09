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
//! # The two disciplines, both enforced rather than documented
//!
//! - **Constructor-only minting.** An id is produced only by a [`CoreArena`]
//!   constructor over already-allocated children, so a child id always
//!   resolves. **Within one family** it is also strictly less than its
//!   parent's, which is what makes that family acyclic by construction. Across
//!   families the ordering says nothing — the four id spaces are independent
//!   indices — so acyclicity of the whole graph rests on the minting order
//!   alone: a constructor cannot name a node that does not exist yet, whichever
//!   family it is in.
//! - **Wholesale truncation.** [`CoreArena::watermark`] snapshots the four
//!   family lengths and [`CoreArena::truncate_to`] restores them, so a pass's
//!   intermediates allocate past a mark and are dropped in one step afterwards.
//!
//! # The honest cost
//!
//! An owned tree cannot be ill-formed; a `u32` id *can* name no node, or a node
//! in another arena. What keeps that fail-closed is constructor-only minting,
//! one arena per elaboration run, and a checked lookup returning an option
//! rather than an index.

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
/// Minted only by a [`CoreArena`] constructor over already-allocated children,
/// so it always resolves, and is strictly greater than every child id **of its
/// own family**. A cross-family child is ordered by minting time rather than by
/// id, because the families index independently.
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
/// - fails: never, which is the honest cost of infallible constructors: the
///   ceiling is not reachable at any memory an arena can occupy — four billion
///   nodes of the smallest family is on the order of a hundred gigabytes — and
///   the term crate's arena takes the same posture, so the two do not diverge
///   on a condition neither can reach.
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
/// - ensures: `|ret| ret.0 == usize::try_from(index.0).unwrap_or(usize::MAX)` —
///   the equal offset, lossless on every supported platform of at least 32
///   bits.
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
    /// - requires: `watermark` was taken from this arena and no family has
    ///   since shrunk below it; every id minted after it is unreachable from
    ///   content the caller retains.
    /// - ensures: `self.watermark() == ArenaWatermark { values:
    ///   watermark.values.min(entry.values), computations:
    ///   watermark.computations.min(entry.computations), value_types:
    ///   watermark.value_types.min(entry.value_types), comp_types:
    ///   watermark.comp_types.min(entry.comp_types) }` — each family holds
    ///   exactly its watermark-many leading nodes, and a mark above the entry
    ///   lengths leaves that family where it was. Every id minted after the
    ///   watermark then dangles, and a lookup of one fails closed rather than
    ///   resolving to a later node.
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
    /// - ensures: `Some(node)` exactly when `id` names a value node this arena
    ///   still holds, `None` otherwise — an id past the end, or one a
    ///   truncation dropped, fails closed rather than resolving to another
    ///   node.
    /// - provides: the read side of the value family.
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
    /// - requires: nothing; a dangling id is admissible.
    /// - ensures: `Some(node)` exactly when `id` names a computation node this
    ///   arena still holds, `None` otherwise — an id past the end, or one a
    ///   truncation dropped, fails closed rather than resolving to another
    ///   node.
    /// - provides: the read side of the computation family.
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
    /// - requires: nothing; a dangling id is admissible.
    /// - ensures: `Some(node)` exactly when `id` names a value-type node this
    ///   arena still holds, `None` otherwise — an id past the end, or one a
    ///   truncation dropped, fails closed rather than resolving to another
    ///   node.
    /// - provides: the read side of the value-type family.
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
    /// - requires: nothing; a dangling id is admissible.
    /// - ensures: `Some(node)` exactly when `id` names a computation-type node
    ///   this arena still holds, `None` otherwise — an id past the end, or one
    ///   a truncation dropped, fails closed rather than resolving to another
    ///   node.
    /// - provides: the read side of the computation-type family.
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

    /// Append a value node and return its fresh id.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: appends `value` to the value family and returns the id at the
    ///   family's previous end, which is above every value id already minted.
    /// - provides: the single append point every value constructor goes
    ///   through.
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
    #[inline]
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
    #[inline]
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
}
