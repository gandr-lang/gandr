//! The per-run domain arena: the single owner of every glued node one
//! evaluation run produces, addressed by six typed `u32`-backed id families.
//!
//! # Per-run, and torn down wholesale
//!
//! A domain arena belongs to one run and dies with it. Nothing here is
//! persisted, nothing is shared between runs, and teardown is nine flat vector
//! drops — six families and three guard vectors — in any order. The teardown
//! suite releases a deep chain in both orders
//! inside a small stack and observes the release through a handle that does
//! not keep the chain alive.
//!
//! [`DomainArena::truncate_to`] is the same operation at a mark rather than at
//! the floor, so a speculative evaluation allocates past a watermark and is
//! discarded in one step.
//!
//! # Constructor-only minting
//!
//! An id is produced only by a constructor over already-allocated children, so
//! a child id always resolves and is strictly less than its parent's **within
//! its family**; across families the six id spaces index independently, so
//! acyclicity rests on the minting order rather than on the ordering of ids.
//!
//! **Two conditions are not structural, and both are checked rather than
//! assumed**, because a condition held by convention is held until the first
//! arm forgets it:
//!
//! - [`DomainArena::value_neutral`] refuses a neutral carrying a spine. The
//!   term vocabulary has no value eliminator, so a spined value neutral would
//!   be a stuck computation standing in a value slot.
//! - [`DomainArena::neutral_node`] refuses a head that cannot unfold paired
//!   with a body to unfold. A bound variable and a module form have no
//!   definition behind them, so an unfolding face on one names a body that does
//!   not exist, and a consumer that forced it would be reducing the neutral to
//!   something no rule produced.
//!
//! # The honest cost: this arena holds another arena's ids
//!
//! A glued node names core-language nodes it does not own — the source term its
//! [term face] caches, the literal payload it points at, and the body every
//! closure suspends. Those ids resolve in the [`CoreArena`] the run is
//! evaluating, and this arena has no way to check one.
//!
//! **The precondition every constructor inherits is therefore one sentence: the
//! core arena outlives the domain arena and is not truncated below any node the
//! domain holds.** A run that violated it would leave a term face naming a node
//! that does not exist, which is a *wrong* readback rather than a slow one —
//! the same failure the face's own documentation names. The mitigation is the
//! run discipline rather than a check: one domain arena per evaluation run,
//! over one core arena, torn down together.
//!
//! # Levels live in their own family
//!
//! A level is a vector of atoms. Storing one inline would make every lifted
//! domain value a heap-owning node, so lifts name a level in the run's level
//! table and the domain node stays `Copy`.
//!
//! # Every value, computation and neutral carries its guard
//!
//! The cached word step 2 of conversion reads is minted with the node, from
//! the node's kind, payload and children's words, so reading it is one vector
//! access. It lives beside its family in a vector of equal length, and
//! truncation cuts both at one mark. A child that does not resolve at mint
//! makes its parent's word [`Guard::Flexible`], the direction that decides
//! nothing: the dangling child surfaces where it is read.
//!
//! # Per-run arena
//!
//! A `DomainArena` belongs to one run: nothing is persisted or shared between
//! runs. Six id families — values, computations, neutrals, both closure spaces
//! and levels — are minted only over children already minted. Cached words sit
//! beside their node families; levels and native fields occupy flat side
//! tables. `DomainArena::truncate_to` restores every family, cache and
//! field-span watermark. Teardown drops these flat vectors without following
//! recursive ownership.
//!
//! [term face]: crate::domain::TermFace
//! [`CoreArena`]: gandr_core_term::CoreArena

use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::ComputationId;
use gandr_core_term::ValueId;
use gandr_kernel_strata::Level;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Summand;

use crate::closure::CompClosure;
use crate::closure::Environment;
use crate::closure::ValueClosure;
use crate::domain::CompTermFace;
use crate::domain::DomainComp;
use crate::domain::DomainValue;
use crate::domain::Elimination;
use crate::domain::ForceRefusal;
use crate::domain::Glued;
use crate::domain::LevelEntry;
use crate::domain::LiftTarget;
use crate::domain::Neutral;
use crate::domain::NeutralHead;
use crate::domain::TermFace;
use crate::domain::Unfolding;
use crate::guard::Guard;
use crate::guard::GuardTag;

/// The id of a [`DomainValue`] in a [`DomainArena`].
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DomainValueId(u32);

/// The id of a [`DomainComp`] in a [`DomainArena`].
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DomainCompId(u32);

/// The id of a [`Neutral`] in a [`DomainArena`].
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct NeutralId(u32);

/// The id of a [`ValueClosure`] in a [`DomainArena`].
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ValueClosureId(u32);

/// The id of a [`CompClosure`] in a [`DomainArena`].
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CompClosureId(u32);

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
/// - ensures: the equal index below the `u32` ceiling. **At and above the
///   ceiling every further mint returns the same id and later nodes alias**, so
///   the saturation is a documented ceiling rather than a safe fallback.
/// - provides: the total, panic-free length-to-index widening.
/// - fails: never, which is the honest cost of infallible constructors: the
///   ceiling is not reachable at any memory an arena can occupy, and the core
///   and kernel arenas take the same posture, so the three do not diverge on a
///   condition none can reach.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — zero, one and both sides of the index ceiling distinguish
///   exact minting from premature saturation; widening each representable
///   result must recover the input.
/// - witness: `arena::tests::index_conversion_preserves_the_range_before_saturating`
#[inline]
#[spec(ensures: |ret| u32::try_from(length.0)
    .map_or(ret.0 == u32::MAX, |index| ret.0 == index))]
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
///
/// # Adequacy
/// - hypothesis: L2 — zero, one and the last two indices widen without
///   aliasing, so narrowing or prematurely saturating an offset changes a
///   boundary observation.
/// - witness: `arena::tests::index_conversion_preserves_the_range_before_saturating`
#[inline]
#[spec(ensures: |ret| usize::try_from(index.0)
    .map_or(ret.0 == usize::MAX, |offset| ret.0 == offset))]
fn id_offset(index: ArenaIndex) -> ArenaLength
{
    ArenaLength(usize::try_from(index.0).unwrap_or(usize::MAX))
}

/// Why a domain node could not be minted or reached.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum DomainFault
{
    /// The id names no node of its family in this arena.
    Dangling,
    /// A neutral whose spine stacks a computation eliminator was offered for a
    /// value position. The vocabulary's one value eliminator is the static
    /// application, so a neutral stacking anything else is a stuck
    /// computation and cannot stand where a value is expected.
    ValueNeutralEliminatesComputation,
    /// A neutral with nothing to unfold was asked to record a forced body.
    NeutralIsRigid,
    /// A neutral whose body was already forced was asked to record another.
    NeutralAlreadyForced,
    /// A head that cannot unfold was paired with a body to unfold. Only a
    /// declaration reference can carry an unfolding face; a bound variable and
    /// a module form have no definition behind them.
    RigidHeadCarriesBody,
}

impl From<ForceRefusal> for DomainFault
{
    /// Translate a neutral's own force refusal into an arena fault.
    ///
    /// # Specification
    /// - requires: nothing; both refusals translate.
    /// - ensures: [`ForceRefusal::Rigid`] becomes
    ///   [`DomainFault::NeutralIsRigid`] and [`ForceRefusal::AlreadyForced`]
    ///   becomes [`DomainFault::NeutralAlreadyForced`], so no refusal collapses
    ///   into another.
    /// - provides: the one spelling of "this arena refused", so a caller never
    ///   reads an `Option` around a `Result`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — forcing a rigid neutral and forcing a loaded neutral
    ///   twice distinguish both translated refusals from dangling resolution
    ///   and successful forcing.
    /// - witness: `arena::tests::forcing_a_dangling_neutral_is_refused`
    #[inline]
    #[spec(ensures: |ret| matches!((refusal, ret),
        (ForceRefusal::Rigid, Self::NeutralIsRigid)
        | (ForceRefusal::AlreadyForced, Self::NeutralAlreadyForced)))]
    fn from(refusal: ForceRefusal) -> Self
    {
        match refusal {
            ForceRefusal::Rigid => Self::NeutralIsRigid,
            ForceRefusal::AlreadyForced => Self::NeutralAlreadyForced,
        }
    }
}

/// A half-open range of native fields in one domain arena.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FieldSpan
{
    /// First field offset.
    start: usize,
    /// Exclusive final field offset.
    end: usize,
}

impl FieldSpan
{
    /// The span of no fields, which every arena resolves.
    pub const EMPTY: Self = Self { start: 0, end: 0 };
}

/// A half-open range of case-branch closures in one domain arena.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BranchSpan
{
    /// First branch offset.
    start: usize,
    /// Exclusive final branch offset.
    end: usize,
}

/// A snapshot of the six family lengths and the two side tables.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RunWatermark
{
    /// The [`DomainValue`] family length.
    values: usize,
    /// The [`DomainComp`] family length.
    computations: usize,
    /// The [`Neutral`] family length.
    neutrals: usize,
    /// The [`ValueClosure`] family length.
    value_closures: usize,
    /// The [`CompClosure`] family length.
    comp_closures: usize,
    /// The level-table length.
    levels: usize,
    /// The native field-table length.
    fields: usize,
    /// The case-branch table length.
    branches: usize,
}

/// The per-run arena owning every glued node one evaluation run produces.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct DomainArena
{
    /// The domain values, in allocation order.
    values: Vec<DomainValue>,
    /// Each value's guard, at the value's own offset.
    value_guards: Vec<Guard>,
    /// The weak-head domain computations.
    computations: Vec<DomainComp>,
    /// Each computation's guard, at the computation's own offset.
    comp_guards: Vec<Guard>,
    /// The neutrals.
    neutrals: Vec<Neutral>,
    /// Each neutral's guard, at the neutral's own offset.
    neutral_guards: Vec<Guard>,
    /// The value closures.
    value_closures: Vec<ValueClosure>,
    /// The computation closures.
    comp_closures: Vec<CompClosure>,
    /// The levels a lift names.
    levels: Vec<LevelEntry>,
    /// Native constructor, record and tuple fields, stored without per-node
    /// vectors.
    fields: Vec<DomainValueId>,
    /// Stuck sum cases' branch closures, stored without per-node vectors.
    branches: Vec<CompClosureId>,
}

impl DomainArena
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

    /// The current watermark: the six family lengths.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each component of the returned mark equals the current length
    ///   of the family it names — values, computations, neutrals, value
    ///   closures, computation closures, levels — so the mark is an exact
    ///   snapshot of the arena as it stands at this call, and nothing is
    ///   claimed relating it to a mark taken at another call.
    /// - provides: the entry mark a speculative evaluation is discarded back to
    ///   by [`DomainArena::truncate_to`], and the only value that truncation
    ///   accepts.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a populated mark covers all six families, a retained
    ///   prefix survives truncation and a stale later mark cannot regrow it;
    ///   omitting a family or restoring the wrong boundary changes a lookup.
    /// - witness: `arena::tests::truncating_to_the_floor_empties_every_family`
    /// - witness: `arena::tests::truncating_to_a_watermark_drops_later_nodes`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.values == self.values.len()
        && ret.computations == self.computations.len()
        && ret.neutrals == self.neutrals.len()
        && ret.value_closures == self.value_closures.len()
        && ret.comp_closures == self.comp_closures.len()
        && ret.fields == self.fields.len()
        && ret.branches == self.branches.len()
        && ret.levels == self.levels.len())]
    pub fn watermark(&self) -> RunWatermark
    {
        RunWatermark {
            values: self.values.len(),
            computations: self.computations.len(),
            neutrals: self.neutrals.len(),
            value_closures: self.value_closures.len(),
            comp_closures: self.comp_closures.len(),
            levels: self.levels.len(),
            fields: self.fields.len(),
            branches: self.branches.len(),
        }
    }

    /// Truncate every family back to `watermark`, dropping later allocations.
    ///
    /// # Specification
    /// - requires: `watermark` was taken from this arena and no family has
    ///   since shrunk below it; every id minted after it is unreachable from
    ///   content the caller retains.
    /// - ensures: each family holds exactly its watermark-many leading nodes,
    ///   and a lookup of any id minted after the mark fails closed rather than
    ///   resolving to a later node.
    /// - provides: the wholesale truncation a speculative evaluation is
    ///   discarded by, and — at the default watermark — the whole run's
    ///   teardown as nine flat vector drops in any order. The clause states
    ///   each family's resulting length against the mark and the entry mark,
    ///   which is the documented no-op rather than a panic on a stale mark;
    ///   that no id minted after the mark resolves is a per-id statement over
    ///   the dropped range and stays prose.
    /// - fails: never — a truncation past the end is a no-op.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one decision surface per family, separated by a mark
    ///   below the current length and a mark at it, with the post-truncation
    ///   lookup of a dropped id asserted absent in each family a node was
    ///   minted into. Retaining any dropped family or guard, or regrowing a
    ///   stale mark, changes the post-truncation lookups.
    /// - witness: `arena::tests::truncating_to_a_watermark_drops_later_nodes`
    /// - witness: `arena::tests::truncating_to_the_floor_empties_every_family`
    #[inline]
    #[spec(
        captures: entry_mark = self.watermark(),
        ensures: self.values.len() == watermark.values.min(entry_mark.values)
            && self.computations.len() == watermark.computations.min(entry_mark.computations)
            && self.neutrals.len() == watermark.neutrals.min(entry_mark.neutrals)
            && self.value_closures.len() == watermark.value_closures.min(entry_mark.value_closures)
            && self.comp_closures.len() == watermark.comp_closures.min(entry_mark.comp_closures)
            && self.fields.len() == watermark.fields.min(entry_mark.fields)
            && self.branches.len() == watermark.branches.min(entry_mark.branches)
            && self.levels.len() == watermark.levels.min(entry_mark.levels),
    )]
    pub fn truncate_to(
        &mut self,
        watermark: RunWatermark,
    )
    {
        self.values.truncate(watermark.values);
        self.value_guards.truncate(watermark.values);
        self.computations.truncate(watermark.computations);
        self.comp_guards.truncate(watermark.computations);
        self.neutrals.truncate(watermark.neutrals);
        self.neutral_guards.truncate(watermark.neutrals);
        self.value_closures.truncate(watermark.value_closures);
        self.comp_closures.truncate(watermark.comp_closures);
        self.levels.truncate(watermark.levels);
        self.fields.truncate(watermark.fields);
        self.branches.truncate(watermark.branches);
    }

    /// Resolve a domain value id, or `None` when it dangles.
    ///
    /// # Specification
    /// - requires: nothing — an id from another arena, and one minted after a
    ///   truncation, are both admissible input.
    /// - ensures: the value this arena holds for `id`, for every id below the
    ///   family length.
    /// - provides: the checked resolution every reader of a value id goes
    ///   through, so the dangling case is decided once.
    /// - fails: yields nothing at or above the family length. An id from
    ///   another arena that is nevertheless in range resolves to this arena's
    ///   node there; an id carries no arena provenance.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — live entries resolve before teardown and the same ids
    ///   fail after their family is truncated; retaining a dropped entry or
    ///   rejecting an allocated entry changes the boundary observation.
    /// - witness: `arena::tests::truncating_to_the_floor_empties_every_family`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.is_some() == usize::try_from(id.0)
        .is_ok_and(|offset| offset < self.values.len()))]
    pub fn value(
        &self,
        id: DomainValueId,
    ) -> Option<&DomainValue>
    {
        self.values.get(id_offset(ArenaIndex(id.0)).0)
    }

    /// Resolve a domain computation id, or `None` when it dangles.
    ///
    /// # Specification
    /// - requires: nothing — an id from another arena, and one minted after a
    ///   truncation, are both admissible input.
    /// - ensures: the computation this arena holds for `id`, for every id below
    ///   the family length.
    /// - provides: the checked resolution every reader of a computation id goes
    ///   through.
    /// - fails: yields nothing at or above the family length; an id carries no
    ///   arena provenance, so an in-range foreign id resolves here.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — live entries resolve before teardown and the same ids
    ///   fail after their family is truncated; retaining a dropped entry or
    ///   rejecting an allocated entry changes the boundary observation.
    /// - witness: `arena::tests::truncating_to_the_floor_empties_every_family`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.is_some() == usize::try_from(id.0)
        .is_ok_and(|offset| offset < self.computations.len()))]
    pub fn computation(
        &self,
        id: DomainCompId,
    ) -> Option<&DomainComp>
    {
        self.computations.get(id_offset(ArenaIndex(id.0)).0)
    }

    /// Resolve a neutral id, or `None` when it dangles.
    ///
    /// # Specification
    /// - requires: nothing — an id from another arena, and one minted after a
    ///   truncation, are both admissible input.
    /// - ensures: the neutral this arena holds for `id`, for every id below the
    ///   family length.
    /// - provides: the checked resolution the spine and unfolding guards are
    ///   both built on.
    /// - fails: yields nothing at or above the family length; an id carries no
    ///   arena provenance, so an in-range foreign id resolves here.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — live entries resolve before teardown and the same ids
    ///   fail after their family is truncated; retaining a dropped entry or
    ///   rejecting an allocated entry changes the boundary observation.
    /// - witness: `arena::tests::truncating_to_the_floor_empties_every_family`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.is_some() == usize::try_from(id.0)
        .is_ok_and(|offset| offset < self.neutrals.len()))]
    pub fn neutral(
        &self,
        id: NeutralId,
    ) -> Option<&Neutral>
    {
        self.neutrals.get(id_offset(ArenaIndex(id.0)).0)
    }

    /// Resolve a value-closure id, or `None` when it dangles.
    ///
    /// # Specification
    /// - requires: nothing — an id from another arena, and one minted after a
    ///   truncation, are both admissible input.
    /// - ensures: the value closure this arena holds for `id`, for every id
    ///   below the family length.
    /// - provides: the checked resolution an application reads a closure
    ///   through.
    /// - fails: yields nothing at or above the family length; an id carries no
    ///   arena provenance, so an in-range foreign id resolves here.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — live entries resolve before teardown and the same ids
    ///   fail after their family is truncated; retaining a dropped entry or
    ///   rejecting an allocated entry changes the boundary observation.
    /// - witness: `arena::tests::truncating_to_the_floor_empties_every_family`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.is_some() == usize::try_from(id.0)
        .is_ok_and(|offset| offset < self.value_closures.len()))]
    pub fn value_closure(
        &self,
        id: ValueClosureId,
    ) -> Option<&ValueClosure>
    {
        self.value_closures.get(id_offset(ArenaIndex(id.0)).0)
    }

    /// Resolve a computation-closure id, or `None` when it dangles.
    ///
    /// # Specification
    /// - requires: nothing — an id from another arena, and one minted after a
    ///   truncation, are both admissible input.
    /// - ensures: the computation closure this arena holds for `id`, for every
    ///   id below the family length.
    /// - provides: the checked resolution a force and a lambda application both
    ///   read a body through.
    /// - fails: yields nothing at or above the family length; an id carries no
    ///   arena provenance, so an in-range foreign id resolves here.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — live entries resolve before teardown and the same ids
    ///   fail after their family is truncated; retaining a dropped entry or
    ///   rejecting an allocated entry changes the boundary observation.
    /// - witness: `arena::tests::truncating_to_the_floor_empties_every_family`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.is_some() == usize::try_from(id.0)
        .is_ok_and(|offset| offset < self.comp_closures.len()))]
    pub fn comp_closure(
        &self,
        id: CompClosureId,
    ) -> Option<&CompClosure>
    {
        self.comp_closures.get(id_offset(ArenaIndex(id.0)).0)
    }

    /// Resolve a lift target to the level it names, or `None` when it dangles.
    ///
    /// # Specification
    /// - requires: nothing — a target from another arena, and one minted after
    ///   a truncation, are both admissible input.
    /// - ensures: the level entry this arena holds for `target`, for every
    ///   target below the table length.
    /// - provides: the checked resolution a universe lift reads its level
    ///   through, so a lift never carries the level itself.
    /// - fails: yields nothing at or above the table length; a target carries
    ///   no arena provenance, so an in-range foreign one resolves here.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — live entries resolve before teardown and the same ids
    ///   fail after their family is truncated; retaining a dropped entry or
    ///   rejecting an allocated entry changes the boundary observation.
    /// - witness: `arena::tests::truncating_to_the_floor_empties_every_family`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.is_some() == usize::try_from(u32::from(target))
        .is_ok_and(|offset| offset < self.levels.len()))]
    pub fn level(
        &self,
        target: LiftTarget,
    ) -> Option<&LevelEntry>
    {
        self.levels.get(id_offset(ArenaIndex(u32::from(target))).0)
    }

    /// The guard minted with a domain value.
    ///
    /// # Specification
    /// - requires: nothing — an id from another arena, and one minted after a
    ///   truncation, are both admissible input.
    /// - ensures: the word minted with the value `id` names, for every id below
    ///   the family length.
    /// - provides: the constant-time read step 2 of conversion makes.
    /// - fails: [`DomainFault::Dangling`] at or above the family length.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DomainFault::Dangling`] — the id names no value.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — allocated words disappear with their nodes at
    ///   teardown; loaded heads and closure-bearing spines remain flexible, so
    ///   stale guard entries or a false rigid answer are observable.
    /// - witness: `arena::tests::truncating_to_the_floor_empties_every_family`
    /// - witness: `arena::tests::a_neutral_is_rigid_only_without_a_body_or_a_closure`
    /// - witness: `arena::tests::guard_flexibility_survives_the_entire_spine`
    #[inline]
    #[spec(ensures: |ret| ret.is_ok() == self.value(id).is_some())]
    pub fn value_guard(
        &self,
        id: DomainValueId,
    ) -> Result<Guard, DomainFault>
    {
        self.value_guards
            .get(id_offset(ArenaIndex(id.0)).0)
            .copied()
            .ok_or(DomainFault::Dangling)
    }

    /// The guard minted with a domain computation.
    ///
    /// # Specification
    /// - requires: nothing — a foreign or truncated id is admissible input.
    /// - ensures: the word minted with the computation `id` names, for every id
    ///   below the family length.
    /// - provides: the constant-time read step 2 of conversion makes.
    /// - fails: [`DomainFault::Dangling`] at or above the family length.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DomainFault::Dangling`] — the id names no computation.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — allocated words disappear with their nodes at
    ///   teardown; loaded heads and closure-bearing spines remain flexible, so
    ///   stale guard entries or a false rigid answer are observable.
    /// - witness: `arena::tests::truncating_to_the_floor_empties_every_family`
    /// - witness: `arena::tests::a_neutral_is_rigid_only_without_a_body_or_a_closure`
    /// - witness: `arena::tests::guard_flexibility_survives_the_entire_spine`
    #[inline]
    #[spec(ensures: |ret| ret.is_ok() == self.computation(id).is_some())]
    pub fn comp_guard(
        &self,
        id: DomainCompId,
    ) -> Result<Guard, DomainFault>
    {
        self.comp_guards
            .get(id_offset(ArenaIndex(id.0)).0)
            .copied()
            .ok_or(DomainFault::Dangling)
    }

    /// The guard minted with a neutral.
    ///
    /// # Specification
    /// - requires: nothing — a foreign or truncated id is admissible input.
    /// - ensures: the word minted with the neutral `id` names, for every id
    ///   below the family length; forcing the neutral leaves it unchanged,
    ///   because an unforced and a forced face are both flexible.
    /// - provides: the constant-time read step 2 of conversion makes.
    /// - fails: [`DomainFault::Dangling`] at or above the family length.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DomainFault::Dangling`] — the id names no neutral.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — allocated words disappear with their nodes at
    ///   teardown; loaded heads and closure-bearing spines remain flexible, so
    ///   stale guard entries or a false rigid answer are observable.
    /// - witness: `arena::tests::truncating_to_the_floor_empties_every_family`
    /// - witness: `arena::tests::a_neutral_is_rigid_only_without_a_body_or_a_closure`
    /// - witness: `arena::tests::guard_flexibility_survives_the_entire_spine`
    #[inline]
    #[spec(ensures: |ret| ret.is_ok() == self.neutral(id).is_some())]
    pub fn neutral_guard(
        &self,
        id: NeutralId,
    ) -> Result<Guard, DomainFault>
    {
        self.neutral_guards
            .get(id_offset(ArenaIndex(id.0)).0)
            .copied()
            .ok_or(DomainFault::Dangling)
    }

    /// A child value's guard as its parent folds it: flexible when the child
    /// does not resolve.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`DomainArena::value_guard`] for a resolving id, and
    ///   [`Guard::Flexible`] for a dangling one.
    /// - provides: the fail-closed direction the infallible constructors fold a
    ///   child through: a word over a dangling child decides nothing.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a rigid argument, a closure-bearing argument and a
    ///   dangling argument separate preservation of a usable word from
    ///   conservative flexibility; losing flexibility later in the spine
    ///   changes the final guard.
    /// - witness: `arena::tests::a_neutral_is_rigid_only_without_a_body_or_a_closure`
    /// - witness: `arena::tests::guard_flexibility_survives_the_entire_spine`
    #[inline]
    #[spec(ensures: |ret| self.value_guard(id)
        .map_or(ret == Guard::Flexible, |guard| ret == guard))]
    fn folded_value_guard(
        &self,
        id: DomainValueId,
    ) -> Guard
    {
        self.value_guard(id).unwrap_or(Guard::Flexible)
    }

    /// The guard a neutral is minted with.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Guard::Flexible`] when the unfolding face is loaded, when
    ///   the head is a hole or a mark, or when the spine stacks a bind, a case,
    ///   a transport, a fixpoint, or an argument whose word is flexible;
    ///   otherwise the fold of the head and each elimination in spine order.
    /// - provides: the rigidity rule for a stuck node: a head with a body to
    ///   unfold, a head a fill can still decide, or an elimination holding a
    ///   closure, can change the answer. Its cost is the spine's length, which
    ///   the spine copy every extension makes already pays.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surfaces are the loaded face, the
    ///   closure-holding eliminations and the argument's word, separated by a
    ///   rigid variable applied to a rigid argument, the same head carrying an
    ///   unforced body, and a spine stacking a bind; a static family's word is
    ///   separated by head index, by arity and by argument. A flexible argument
    ///   or a case before a later rigid elimination must not become rigid
    ///   again; losing its flexibility changes the final word. A hole head and
    ///   a mark head over an empty spine separate an indeterminate head from a
    ///   rigid one.
    /// - witness: `arena::tests::guard_flexibility_survives_the_entire_spine`
    /// - witness: `arena::tests::a_neutral_is_rigid_only_without_a_body_or_a_closure`
    /// - witness: `conv::tests::family_spines_are_separated_by_head_index_and_arity`
    /// - witness: `arena::tests::a_hole_or_mark_head_is_never_rigid`
    #[spec(ensures: |ret| matches!(ret, Guard::Flexible) ==
        (!matches!(unfolding, Unfolding::Rigid) || matches!(head, NeutralHead::Hole { .. } | NeutralHead::Mark { .. } | NeutralHead::Returned(_)) || spine.iter().any(|elimination| match *elimination {
            Elimination::Apply(argument) | Elimination::StaticApply(argument) =>
                !matches!(self.value_guard(argument), Ok(Guard::Rigid(_))),
            Elimination::ListFold { .. } | Elimination::ListCase { .. } | Elimination::Transport(_) | Elimination::ProductTransport(_) | Elimination::PathTransport { .. } | Elimination::Ride { .. } | Elimination::TelescopeTransport { .. } | Elimination::Bind(_) | Elimination::Case { .. } | Elimination::DataCase(_) | Elimination::Split(_) | Elimination::Projection(_) | Elimination::Fixpoint{ .. } => true,
            Elimination::Force => false,
        })))]
    fn neutral_word(
        &self,
        head: NeutralHead,
        spine: &[Elimination],
        unfolding: Unfolding,
    ) -> Guard
    {
        let mut word = match (head, unfolding) {
            (_, Unfolding::Unforced(_) | Unfolding::Forced(_))
            | (
                NeutralHead::Hole { .. } | NeutralHead::Mark { .. } | NeutralHead::Returned(_),
                Unfolding::Rigid,
            ) => {
                return Guard::Flexible;
            },
            (NeutralHead::Variable { zone, level }, Unfolding::Rigid) => {
                Guard::compose(GuardTag::Variable, &(zone, level), &[])
            },
            (NeutralHead::Constant(constant), Unfolding::Rigid) => {
                Guard::compose(GuardTag::Constant, &constant, &[])
            },
            (NeutralHead::Module(module), Unfolding::Rigid) => {
                Guard::compose(GuardTag::Module, &module, &[])
            },
        };
        for &elimination in spine {
            word = match elimination {
                Elimination::Apply(argument) => Guard::compose(GuardTag::Apply, &(), &[
                    word,
                    self.folded_value_guard(argument),
                ]),
                Elimination::StaticApply(argument) => {
                    Guard::compose(GuardTag::StaticApply, &(), &[
                        word,
                        self.folded_value_guard(argument),
                    ])
                },
                Elimination::Force => Guard::compose(GuardTag::Force, &(), &[word]),
                Elimination::Transport(_)
                | Elimination::DataCase(_)
                | Elimination::Split(_)
                | Elimination::Projection(_)
                | Elimination::ProductTransport(_)
                | Elimination::PathTransport { .. }
                | Elimination::Ride { .. }
                | Elimination::TelescopeTransport { .. }
                | Elimination::Bind(_)
                | Elimination::ListFold { .. }
                | Elimination::ListCase { .. }
                | Elimination::Case { .. }
                | Elimination::Fixpoint { .. } => return Guard::Flexible,
            };
        }
        word
    }

    /// Append a domain value and return its fresh id.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the value is appended after every value this arena already
    ///   holds, and the returned id resolves to it — below the `u32` ceiling
    ///   the family length can reach.
    /// - provides: the single append every value mint below goes through, so
    ///   the ceiling is documented in one place. At and above the ceiling
    ///   `id_index` saturates and later nodes alias, which is the ceiling that
    ///   item states rather than a fallback.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — distinct child and parent ids remain ordered,
    ///   reconstructed terms retain their operands, and truncation removes
    ///   nodes together with their words; aliasing an earlier allocation or
    ///   desynchronizing guards changes an observation.
    /// - witness: `arena::tests::a_child_id_is_strictly_below_its_parent`
    /// - witness: `arena::tests::truncating_to_the_floor_empties_every_family`
    /// - witness: `readback::tests::a_pair_and_an_injection_rebuild_from_their_children`
    /// - witness: `readback::tests::a_thunk_reads_back_through_the_body_it_suspends`
    #[inline]
    #[spec(
        captures: entry_length = self.values.len(),
        ensures: |ret| self.values.len().checked_sub(1) == Some(entry_length)
            && self.value_guards.len() == self.values.len()
            && u32::try_from(entry_length).map_or(ret.0 == u32::MAX, |index|
                ret.0 == index && self.value(ret) == Some(&value)),
    )]
    fn alloc_value(
        &mut self,
        value: DomainValue,
        guard: Guard,
    ) -> DomainValueId
    {
        let id = DomainValueId(id_index(ArenaLength(self.values.len())).0);
        self.values.push(value);
        self.value_guards.push(guard);
        id
    }

    /// Append a domain computation and return its fresh id.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the computation is appended after every computation this
    ///   arena already holds, and the returned id resolves to it — below the
    ///   `u32` ceiling the family length can reach.
    /// - provides: the single append every computation mint below goes through;
    ///   `id_index` states the aliasing at and above the ceiling.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — distinct child and parent ids remain ordered,
    ///   reconstructed terms retain their operands, and truncation removes
    ///   nodes together with their words; aliasing an earlier allocation or
    ///   desynchronizing guards changes an observation.
    /// - witness: `arena::tests::a_child_id_is_strictly_below_its_parent`
    /// - witness: `arena::tests::truncating_to_the_floor_empties_every_family`
    /// - witness: `readback::tests::a_pair_and_an_injection_rebuild_from_their_children`
    /// - witness: `readback::tests::a_thunk_reads_back_through_the_body_it_suspends`
    #[inline]
    #[spec(
        captures: entry_length = self.computations.len(),
        ensures: |ret| self.computations.len().checked_sub(1) == Some(entry_length)
            && self.comp_guards.len() == self.computations.len()
            && u32::try_from(entry_length).map_or(ret.0 == u32::MAX, |index|
                ret.0 == index && self.computation(ret) == Some(&computation)),
    )]
    fn alloc_computation(
        &mut self,
        computation: DomainComp,
        guard: Guard,
    ) -> DomainCompId
    {
        let id = DomainCompId(id_index(ArenaLength(self.computations.len())).0);
        self.computations.push(computation);
        self.comp_guards.push(guard);
        id
    }

    /// Hold a level and return the lift target naming it.
    ///
    /// # Specification
    /// - requires: nothing; every level is admissible.
    /// - ensures: the level is appended to the table and the returned target
    ///   resolves to it — below the `u32` ceiling the table length can reach.
    /// - provides: the indirection that keeps a lift's payload one `u32` wide
    ///   however large a level grows; `id_index` states the aliasing at and
    ///   above the ceiling.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — rebuilding a lift recovers its nonzero level and body
    ///   through the level table, while teardown makes the target dangle; a
    ///   wrong slot or discarded level changes the reconstructed term.
    /// - witness: `readback::tests::the_leaf_and_lift_arms_read_back_into_the_core_arena`
    /// - witness: `arena::tests::truncating_to_the_floor_empties_every_family`
    #[inline]
    #[spec(
        captures: entry_length = self.levels.len(),
        ensures: |ret| self.levels.len().checked_sub(1) == Some(entry_length)
            && u32::try_from(entry_length).map_or_else(|_| u32::from(ret) == u32::MAX,
                |index| u32::from(ret) == index),
    )]
    pub fn hold_level(
        &mut self,
        level: Level,
    ) -> LiftTarget
    {
        let target = LiftTarget::from(id_index(ArenaLength(self.levels.len())).0);
        self.levels.push(LevelEntry::new(level));
        target
    }

    /// Mint a neutral over a head, a spine and an unfolding face.
    ///
    /// # Specification
    /// - requires: nothing — a head that cannot unfold paired with a body to
    ///   unfold is admissible input and is refused.
    /// - ensures: on success a neutral whose unfolding face is loaded only if
    ///   its head is a declaration reference, which is the only head a
    ///   definition can stand behind.
    /// - provides: the second of the domain's two non-structural
    ///   well-formedness conditions, checked at the only site that can violate
    ///   it — the sibling being the spine condition on a value-position
    ///   neutral.
    /// - fails: [`DomainFault::RigidHeadCarriesBody`] when a bound variable or
    ///   a module form is paired with anything but [`Unfolding::Rigid`].
    ///   Forcing such a face would reduce the neutral to something no rule
    ///   produced, so the refusal is at the mint rather than at the force.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DomainFault::RigidHeadCarriesBody`] — the head has no definition
    ///   behind it and cannot carry an unfolding.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surface is the head-against-face table,
    ///   separated by a declaration head at each of the three faces, and by a
    ///   variable head and a module head at each of the two loaded faces, all
    ///   asserted by variant. Accepting a loaded non-declaration or refusing a
    ///   declaration face changes the refusal table.
    /// - witness: `arena::tests::a_head_that_cannot_unfold_carries_no_body`
    #[inline]
    #[spec(
        captures: [
            entry_unfoldable = matches!(head, NeutralHead::Constant(_)),
            entry_loaded = matches!(unfolding, Unfolding::Unforced(_) | Unfolding::Forced(_)),
        ],
        ensures: |ret| ret.is_ok() == (entry_unfoldable || !entry_loaded),
    )]
    pub fn neutral_node(
        &mut self,
        head: NeutralHead,
        spine: Vec<Elimination>,
        unfolding: Unfolding,
    ) -> Result<NeutralId, DomainFault>
    {
        let unfoldable = match head {
            NeutralHead::Constant(_) => true,
            NeutralHead::Variable { .. }
            | NeutralHead::Module(_)
            | NeutralHead::Hole { .. }
            | NeutralHead::Mark { .. }
            | NeutralHead::Returned(_) => false,
        };
        let loaded = match unfolding {
            Unfolding::Rigid => false,
            Unfolding::Unforced(_) | Unfolding::Forced(_) => true,
        };
        if loaded && !unfoldable {
            return Err(DomainFault::RigidHeadCarriesBody);
        }
        let guard = self.neutral_word(head, &spine, unfolding);
        let id = NeutralId(id_index(ArenaLength(self.neutrals.len())).0);
        self.neutrals.push(Neutral::new(head, spine, unfolding));
        self.neutral_guards.push(guard);
        Ok(id)
    }

    /// Close a core value body over an environment.
    ///
    /// # Specification
    /// - requires: `body` names a live value node of the core arena the run
    ///   evaluates against, and `environment` binds every occurrence free in
    ///   it; neither claim is checkable here, since a core id and an
    ///   environment carry no arena provenance.
    /// - ensures: the closure is appended to its family and the returned id
    ///   resolves to it, carrying exactly the body and environment offered.
    /// - provides: the delayed substitution the domain represents a binder by,
    ///   so no core term is ever rewritten.
    /// - fails: never — a body that dangles surfaces where a caller resolves
    ///   it, not here.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — readback opens a captured body under binders and
    ///   recovers the original variable indices; swapping the body, dropping
    ///   the environment or returning an earlier closure changes the
    ///   reconstructed binding.
    /// - witness: `readback::tests::a_quote_reads_back_through_its_environment`
    #[inline]
    #[spec(
        captures: entry_length = self.value_closures.len(),
        ensures: |ret| self.value_closures.len().checked_sub(1) == Some(entry_length)
            && self.value_closure(ret).is_some_and(|closure| closure.body() == body),
    )]
    pub fn value_closure_node(
        &mut self,
        body: crate::closure::ValueBody,
        environment: Environment,
    ) -> ValueClosureId
    {
        let id = ValueClosureId(id_index(ArenaLength(self.value_closures.len())).0);
        self.value_closures
            .push(ValueClosure::new(body, environment));
        id
    }

    /// Close a core computation body over an environment.
    ///
    /// # Specification
    /// - requires: `body` names a live computation node of the core arena the
    ///   run evaluates against, and `environment` binds every occurrence free
    ///   in it; neither claim is checkable here.
    /// - ensures: the closure is appended to its family and the returned id
    ///   resolves to it, carrying exactly the body and environment offered.
    /// - provides: the suspended computation a thunk and a lambda are both
    ///   built over.
    /// - fails: never — a body that dangles surfaces where a caller resolves
    ///   it, not here.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — readback opens a captured body under binders and
    ///   recovers the original variable indices; swapping the body, dropping
    ///   the environment or returning an earlier closure changes the
    ///   reconstructed binding.
    /// - witness: `readback::tests::nested_binders_read_back_as_the_indices_that_name_them`
    /// - witness: `eval::tests::native_transport_sequences_product_components`
    #[inline]
    #[spec(
        captures: entry_length = self.comp_closures.len(),
        ensures: |ret| self.comp_closures.len().checked_sub(1) == Some(entry_length)
            && self.comp_closure(ret).is_some_and(|closure| closure.body() == crate::closure::CompBody::Source(body)),
    )]
    pub fn comp_closure_node(
        &mut self,
        body: ComputationId,
        environment: Environment,
    ) -> CompClosureId
    {
        let id = CompClosureId(id_index(ArenaLength(self.comp_closures.len())).0);
        self.comp_closures.push(CompClosure::new(
            crate::closure::CompBody::Source(body),
            environment,
        ));
        id
    }

    /// Hold a native continuation without manufacturing source syntax.
    ///
    /// # Specification
    /// - requires: nothing; referenced values and closures are checked when the
    ///   body runs.
    /// - ensures: a fresh computation closure holds `body` with no bindings.
    /// - provides: the continuations of ordered native product transport, of
    ///   the constructorwise rows of transport and ride, and of the commuting
    ///   conversions of `F`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — both product components can be stuck independently;
    ///   the captured continuation must retain the first result and transport
    ///   the second component before pairing them in source order. The identity
    ///   continuation must return what it binds, and a fused pair of
    ///   continuations must run the inner before the outer.
    /// - witness: `eval::tests::native_transport_sequences_product_components`
    /// - witness: `machine::tests::the_laws_of_bind_convert_by_their_decisions`
    #[inline]
    #[spec(captures: entry_length = self.comp_closures.len(), ensures: |ret|
        self.comp_closures.len().checked_sub(1) == Some(entry_length)
            && self.comp_closure(ret).is_some_and(|closure| closure.body() == body
                && [gandr_core_term::Zone::Intuitionistic, gandr_core_term::Zone::Linear].iter().all(|&zone| closure.environment().bindings(zone).is_empty())))]
    pub(crate) fn native_continuation(
        &mut self,
        body: crate::closure::CompBody,
    ) -> CompClosureId
    {
        let id = CompClosureId(id_index(ArenaLength(self.comp_closures.len())).0);
        self.comp_closures
            .push(CompClosure::new(body, Environment::new()));
        id
    }

    /// Hold a native continuation over the values bound before it.
    ///
    /// # Specification
    /// - requires: nothing; referenced values and closures are checked when the
    ///   body runs.
    /// - ensures: a fresh computation closure holds `body` over exactly
    ///   `environment`.
    /// - provides: the continuation of a componentwise move, whose environment
    ///   holds the components moved so far, as the binds of the kernel's reduct
    ///   hold them.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a three-component product motive moves its components
    ///   in order and returns them in source order; a lost or reordered binding
    ///   changes the read-back tuple.
    /// - witness: `identity::tests::a_product_motive_binds_each_component_before_the_next`
    #[inline]
    #[spec(captures: [entry_length = self.comp_closures.len(), depth = environment.depth(gandr_core_term::Zone::Intuitionistic)], ensures: |ret|
        self.comp_closures.len().checked_sub(1) == Some(entry_length)
            && self.comp_closure(ret).is_some_and(|closure| closure.body() == body
                && closure.environment().depth(gandr_core_term::Zone::Intuitionistic) == depth))]
    pub(crate) fn native_continuation_over(
        &mut self,
        body: crate::closure::CompBody,
        environment: Environment,
    ) -> CompClosureId
    {
        let id = CompClosureId(id_index(ArenaLength(self.comp_closures.len())).0);
        self.comp_closures.push(CompClosure::new(body, environment));
        id
    }

    /// Mint the unit value: the tuple of no components.
    ///
    /// # Specification
    /// - requires: nothing; unit carries no component that could dangle.
    /// - ensures: a fresh tuple node over an empty field span at `face`,
    ///   appended after every value this arena already holds.
    /// - provides: the domain form a unit introduction evaluates to.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — unit beneath a pair is rebuilt as unit rather than a
    ///   different leaf; a wrong former, payload or source face changes the
    ///   observed term.
    /// - witness: `readback::tests::a_pair_and_an_injection_rebuild_from_their_children`
    #[inline]
    #[spec(ensures: |ret| self.value(ret).and_then(|value| self.components(value)).is_some_and(<[DomainValueId]>::is_empty))]
    pub fn value_unit(
        &mut self,
        face: TermFace,
    ) -> DomainValueId
    {
        self.value_tuple([], face)
    }

    /// Mint a literal value, whose payload stays in the core arena.
    ///
    /// # Specification
    /// - requires: `literal` names a live literal node of the core arena the
    ///   run evaluates against, and `payload` is the literal that node holds.
    /// - ensures: a fresh value node carrying that payload id and `face`; the
    ///   payload itself is referenced rather than copied, and only its hash
    ///   enters the node's guard.
    /// - provides: the domain form a literal evaluates to, with the payload's
    ///   representation left to the core arena that owns it.
    /// - fails: never — a payload that dangles surfaces at readback, not here.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — a literal retains its payload id through rebuilding
    ///   rather than being replaced or copied; a wrong former, payload or
    ///   source face changes the observed term.
    /// - witness: `readback::tests::the_leaf_and_lift_arms_read_back_into_the_core_arena`
    #[inline]
    #[spec(ensures: |ret| self.value(ret) == Some(&DomainValue::Literal { literal, face }))]
    pub fn value_literal(
        &mut self,
        literal: ValueId,
        payload: &Literal,
        face: TermFace,
    ) -> DomainValueId
    {
        let guard = Guard::compose(GuardTag::Literal, payload, &[]);
        self.alloc_value(DomainValue::Literal { literal, face }, guard)
    }

    /// Mint a tuple over already-allocated components, in their given order.
    ///
    /// # Specification
    /// - requires: every component names a live value node of this arena.
    /// - ensures: a fresh value node whose field span holds exactly the
    ///   components in order, at `face`.
    /// - provides: the domain form a tuple introduction evaluates to, with the
    ///   components shared rather than copied.
    /// - fails: never — a component that dangles surfaces at readback, not
    ///   here.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — different left and right children are reconstructed
    ///   in their original order; a wrong former, payload or source face
    ///   changes the observed term.
    /// - witness: `readback::tests::a_pair_and_an_injection_rebuild_from_their_children`
    #[inline]
    #[spec(captures: start = self.fields.len(), ensures: |ret| self.value(ret).and_then(|value| self.components(value)).is_some_and(|held| held.len() == self.fields.len().saturating_sub(start)))]
    pub fn value_tuple<Components>(
        &mut self,
        components: Components,
        face: TermFace,
    ) -> DomainValueId
    where
        Components: IntoIterator<Item = DomainValueId>,
    {
        let fields = self.hold_fields(components);
        let held = self
            .fields
            .get(fields.start .. fields.end)
            .unwrap_or_default();
        let guard = Guard::compose(
            GuardTag::Tuple,
            &held.len(),
            held.iter().map(|&id| self.folded_value_guard(id)),
        );
        self.alloc_value(DomainValue::Tuple { fields, face }, guard)
    }

    /// The components of a tuple, in order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the tuple's held fields for a tuple whose span is live, and
    ///   nothing for every other former or an invalidated span.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — as [`Self::value_tuple`].
    /// - witness: `readback::tests::a_pair_and_an_injection_rebuild_from_their_children`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| match *value { DomainValue::Tuple { fields, .. } => ret == self.fields(fields).ok(), DomainValue::Constructor { .. } | DomainValue::Record { .. } | DomainValue::PathCertificate { .. } | DomainValue::PathProduct { .. } | DomainValue::Here { .. } | DomainValue::Univalence { .. } | DomainValue::HeldTransport { .. } | DomainValue::Flow { .. } | DomainValue::Literal { .. } | DomainValue::ListNil { .. } | DomainValue::ListCons { .. } | DomainValue::Injection { .. } | DomainValue::Thunk { .. } | DomainValue::Lift { .. } | DomainValue::Neutral { .. } | DomainValue::Code { .. } | DomainValue::StaticLambda { .. } => ret.is_none() })]
    pub fn components(
        &self,
        value: &DomainValue,
    ) -> Option<&[DomainValueId]>
    {
        match *value {
            DomainValue::Tuple { fields, .. } => self.fields(fields).ok(),
            DomainValue::Constructor { .. }
            | DomainValue::Record { .. }
            | DomainValue::PathCertificate { .. }
            | DomainValue::PathProduct { .. }
            | DomainValue::Here { .. }
            | DomainValue::Univalence { .. }
            | DomainValue::HeldTransport { .. }
            | DomainValue::Flow { .. }
            | DomainValue::Literal { .. }
            | DomainValue::ListNil { .. }
            | DomainValue::ListCons { .. }
            | DomainValue::Injection { .. }
            | DomainValue::Thunk { .. }
            | DomainValue::Lift { .. }
            | DomainValue::Neutral { .. }
            | DomainValue::Code { .. }
            | DomainValue::StaticLambda { .. } => None,
        }
    }

    /// Mint the empty native list with its source face.
    ///
    /// # Specification
    /// - ensures: returns the native empty-list former with the supplied face.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — List fold readback separates native lists from sums.
    /// - witness: `readback::tests::native_lists_and_folds_read_back_without_sum_encoding`
    #[spec(ensures: |ret| self.value(ret) == Some(&DomainValue::ListNil { face }))]
    #[inline]
    pub fn value_list_nil(
        &mut self,
        face: TermFace,
    ) -> DomainValueId
    {
        self.alloc_value(
            DomainValue::ListNil { face },
            Guard::compose(GuardTag::ListNil, &(), &[]),
        )
    }

    /// Mint a native cell over its evaluated head and list tail.
    ///
    /// # Specification
    /// - requires: both children resolve in this arena.
    /// - ensures: preserves head, tail and source face.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — List fold readback separates native lists from sums.
    /// - witness: `readback::tests::native_lists_and_folds_read_back_without_sum_encoding`
    #[spec(ensures: |ret| self.value(ret) == Some(&DomainValue::ListCons { first, second, face }))]
    #[inline]
    pub fn value_list_cons(
        &mut self,
        first: DomainValueId,
        second: DomainValueId,
        face: TermFace,
    ) -> DomainValueId
    {
        let guard = Guard::compose(GuardTag::ListCons, &(), &[
            self.folded_value_guard(first),
            self.folded_value_guard(second),
        ]);
        self.alloc_value(
            DomainValue::ListCons {
                first,
                second,
                face,
            },
            guard,
        )
    }

    /// Mint a sum injection over an already-allocated body.
    ///
    /// # Specification
    /// - requires: `body` names a live value node of this arena.
    /// - ensures: a fresh value node carrying the summand, the body id, and
    ///   `face`.
    /// - provides: the domain form a sum introduction evaluates to; the summand
    ///   is what a case elimination selects on.
    /// - fails: never — a body that dangles surfaces at readback, not here.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — a right injection retains its side and ordered pair
    ///   payload; a wrong former, payload or source face changes the observed
    ///   term.
    /// - witness: `readback::tests::a_pair_and_an_injection_rebuild_from_their_children`
    #[inline]
    #[spec(ensures: |ret| self.value(ret) == Some(&DomainValue::Injection { summand, body, face }))]
    pub fn value_injection(
        &mut self,
        summand: Summand,
        body: DomainValueId,
        face: TermFace,
    ) -> DomainValueId
    {
        let guard = Guard::compose(GuardTag::Injection, &summand, &[
            self.folded_value_guard(body)
        ]);
        self.alloc_value(
            DomainValue::Injection {
                summand,
                body,
                face,
            },
            guard,
        )
    }

    /// Mint reflexivity of an element path over an already-allocated point.
    ///
    /// # Specification
    /// - requires: `point` names a live value node of this arena.
    /// - ensures: a fresh value node carrying the point id and `face`, guarded
    ///   by the point's own word under the reflexivity tag.
    /// - provides: the domain form `here(a)` evaluates to, which transport
    ///   reads as its identity case.
    /// - fails: never — a point that dangles surfaces at readback, not here.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — transport along reflexivity returns its operand
    ///   unchanged, and two reflexivities compare by their points; a wrong
    ///   former or point changes the transported result or the verdict.
    /// - witness: `identity::tests::transport_along_here_is_the_identity`
    /// - witness: `identity::tests::reflexivities_convert_by_their_points`
    #[inline]
    #[spec(ensures: |ret| self.value(ret) == Some(&DomainValue::Here { point, face }))]
    pub fn value_here(
        &mut self,
        point: DomainValueId,
        face: TermFace,
    ) -> DomainValueId
    {
        let guard = Guard::compose(GuardTag::Here, &(), &[self.folded_value_guard(point)]);
        self.alloc_value(DomainValue::Here { point, face }, guard)
    }

    /// Mint univalence `ua(e)` at an already-allocated record and its forward
    /// map.
    ///
    /// # Specification
    /// - requires: `record` and `forward` name live value nodes of this arena.
    /// - ensures: appends the node under a guard composed of the record's and
    ///   the forward map's own words under the univalence tag.
    /// - provides: the domain form `ua(e)` evaluates to, which native transport
    ///   reads through the forward map.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — transport along univalence applies the forward map to
    ///   the operand; a wrong part changes the transported result.
    /// - witness: `identity::tests::transport_along_univalence_applies_the_forward_map`
    #[inline]
    #[spec(ensures: |ret| self.value(ret) == Some(&DomainValue::Univalence { record, forward, face }))]
    pub fn value_univalence(
        &mut self,
        record: DomainValueId,
        forward: DomainValueId,
        face: TermFace,
    ) -> DomainValueId
    {
        let guard = Guard::compose(GuardTag::Univalence, &(), &[
            self.folded_value_guard(record),
            self.folded_value_guard(forward),
        ]);
        self.alloc_value(
            DomainValue::Univalence {
                record,
                forward,
                face,
            },
            guard,
        )
    }

    /// Mint a path held as the transport that formed it, over its motive
    /// closure and its already-allocated path and operand.
    ///
    /// Its guard is flexible: the motive is a closure, which the comparison
    /// reads rather than a content hash.
    ///
    /// # Specification
    /// - requires: `motive` names a live value closure of this arena, and
    ///   `path` and `value` live value nodes.
    /// - ensures: a fresh value node carrying the three parts and `face`.
    /// - provides: the domain form `back(p)` and `q then p` evaluate to when
    ///   `p` is a universe path, which transport at the universe's decode reads
    ///   back along `p`, or along `q` and then `p`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — transport along the held `back` of `ua(e)` applies
    ///   the record's left inverse; a wrong part changes the transported
    ///   result.
    /// - witness: `identity::tests::transport_back_along_univalence_applies_the_left_inverse`
    #[inline]
    #[spec(ensures: |ret| self.value(ret) == Some(&DomainValue::HeldTransport { motive, path, value, face }))]
    pub fn value_held_transport(
        &mut self,
        motive: ValueClosureId,
        path: DomainValueId,
        value: DomainValueId,
        face: TermFace,
    ) -> DomainValueId
    {
        self.alloc_value(
            DomainValue::HeldTransport {
                motive,
                path,
                value,
                face,
            },
            Guard::Flexible,
        )
    }

    /// Mint a flow introduction over its already-allocated parts, in written
    /// order.
    ///
    /// # Specification
    /// - requires: every part names a live value node of this arena, as many as
    ///   `former` holds.
    /// - ensures: a fresh value node carrying `former`, a field span holding
    ///   exactly the parts in order, and `face`, guarded by the parts' words
    ///   under the flow tag and the former.
    /// - provides: the domain form `stay`, `forward`, `then` and `arrow`
    ///   evaluate to, which a ride reads row by row.
    /// - fails: never — a part that dangles surfaces at readback, not here.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a stay and a composite read back as their own former
    ///   over their parts, and two flows of one former compare by their parts.
    /// - witness: `identity::tests::flows_read_back_and_compare_by_their_parts`
    #[inline]
    #[spec(captures: start = self.fields.len(), ensures: |ret| matches!(self.value(ret), Some(&DomainValue::Flow { former: held, parts, .. }) if held == former && self.fields(parts).is_ok_and(|kept| kept.len() == self.fields.len().saturating_sub(start))))]
    pub fn value_flow<Parts>(
        &mut self,
        former: crate::domain::FlowFormer,
        parts: Parts,
        face: TermFace,
    ) -> DomainValueId
    where
        Parts: IntoIterator<Item = DomainValueId>,
    {
        let parts = self.hold_fields(parts);
        let held = self
            .fields
            .get(parts.start .. parts.end)
            .unwrap_or_default();
        let guard = Guard::compose(
            GuardTag::Flow,
            &former,
            held.iter().map(|&id| self.folded_value_guard(id)),
        );
        self.alloc_value(
            DomainValue::Flow {
                former,
                parts,
                face,
            },
            guard,
        )
    }

    /// Mint a thunk over an already-allocated computation closure.
    ///
    /// # Specification
    /// - requires: `body` names a live computation closure of this arena.
    /// - ensures: a fresh value node carrying that closure id and `face`.
    /// - provides: the value a suspended computation inhabits, so a thunk
    ///   crosses into value position without running.
    /// - fails: never — a closure that dangles surfaces where a force resolves
    ///   it, not here.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — retaining a closed thunk reuses its source while
    ///   rebuilding enters the suspended returner; a wrong former, payload or
    ///   source face changes the observed term.
    /// - witness: `readback::tests::a_thunk_reads_back_through_the_body_it_suspends`
    #[inline]
    #[spec(ensures: |ret| self.value(ret) == Some(&DomainValue::Thunk { body, face }))]
    pub fn value_thunk(
        &mut self,
        body: CompClosureId,
        face: TermFace,
    ) -> DomainValueId
    {
        self.alloc_value(DomainValue::Thunk { body, face }, Guard::Flexible)
    }

    /// Mint a universe lift over an already-allocated body and a held level.
    ///
    /// # Specification
    /// - requires: `target` names a live level entry of this arena and `body` a
    ///   live value node of it.
    /// - ensures: a fresh value node carrying both ids and `face`.
    /// - provides: the domain form a universe lift evaluates to, with the level
    ///   held in the table rather than inline.
    /// - fails: never — either id dangling surfaces at readback, not here.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — a lifted unit recovers the nonzero level from the
    ///   table and rebuilds the correct body; a wrong former, payload or source
    ///   face changes the observed term.
    /// - witness: `readback::tests::the_leaf_and_lift_arms_read_back_into_the_core_arena`
    #[inline]
    #[spec(ensures: |ret| self.value(ret) == Some(&DomainValue::Lift { target, body, face }))]
    pub fn value_lift(
        &mut self,
        target: LiftTarget,
        body: DomainValueId,
        face: TermFace,
    ) -> DomainValueId
    {
        let guard = self.level(target).map_or(Guard::Flexible, |entry| {
            Guard::compose(GuardTag::Lift, entry.level(), &[
                self.folded_value_guard(body)
            ])
        });
        self.alloc_value(DomainValue::Lift { target, body, face }, guard)
    }

    /// Mint a code over an already-allocated value closure whose body is a
    /// quote.
    ///
    /// A code's guard is flexible: whether two codes are apart depends on the
    /// constants their types decode, which the comparison reads rather than a
    /// content hash.
    ///
    /// # Specification
    /// - requires: `code` names a live value closure of this arena whose body
    ///   is a quote.
    /// - ensures: a fresh value node carrying that closure id and `face`.
    /// - provides: the domain form a quote evaluates to.
    /// - fails: never — a closure that dangles surfaces where it is read.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — a quote under a lambda reads the captured binder back
    ///   as the original index; a wrong former, payload or source face changes
    ///   the observed term.
    /// - witness: `readback::tests::a_quote_reads_back_through_its_environment`
    #[inline]
    #[spec(ensures: |ret| self.value(ret) == Some(&DomainValue::Code { code, face }))]
    pub fn value_code(
        &mut self,
        code: ValueClosureId,
        face: TermFace,
    ) -> DomainValueId
    {
        self.alloc_value(DomainValue::Code { code, face }, Guard::Flexible)
    }

    /// Store a sequence of evaluated native fields once, in its supplied order.
    ///
    /// # Specification
    /// - requires: field ids belong to this arena.
    /// - ensures: the span covers exactly the newly appended fields.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — field order survives evaluation and later truncation
    ///   invalidates the span.
    /// - witness: `arena::tests::native_field_spans_obey_truncation`
    #[spec(captures: start = self.fields.len(), ensures: |ret| ret.start == start && ret.end == self.fields.len())]
    #[inline]
    pub fn hold_fields<Fields>(
        &mut self,
        fields: Fields,
    ) -> FieldSpan
    where
        Fields: IntoIterator<Item = DomainValueId>,
    {
        let start = self.fields.len();
        self.fields.extend(fields);
        FieldSpan {
            start,
            end: self.fields.len(),
        }
    }

    /// Resolve a native field span, refusing an invalidated range.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns exactly the stored slice, or a dangling-domain
    ///   refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `DomainFault::Dangling` when truncation removed the range.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — retained and truncated spans remain distinguishable.
    /// - witness: `arena::tests::native_field_spans_obey_truncation`
    #[spec(ensures: |ret| ret.as_ref().ok().copied() == self.fields.get(span.start..span.end))]
    #[inline]
    pub fn fields(
        &self,
        span: FieldSpan,
    ) -> Result<&[DomainValueId], DomainFault>
    {
        self.fields
            .get(span.start .. span.end)
            .ok_or(DomainFault::Dangling)
    }

    /// Store a stuck sum case's branch closures once, in summand order.
    ///
    /// # Specification
    /// - requires: closure ids belong to this arena.
    /// - ensures: the span covers exactly the newly appended branches.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a retained span reads back its branches, a span
    ///   minted past a watermark dangles after truncation, and a replacement
    ///   leaves the retained span intact.
    /// - witness: `arena::tests::case_branch_spans_obey_truncation`
    #[spec(captures: start = self.branches.len(), ensures: |ret| ret.start == start && ret.end == self.branches.len())]
    #[inline]
    pub fn hold_branches<Branches>(
        &mut self,
        branches: Branches,
    ) -> BranchSpan
    where
        Branches: IntoIterator<Item = CompClosureId>,
    {
        let start = self.branches.len();
        self.branches.extend(branches);
        BranchSpan {
            start,
            end: self.branches.len(),
        }
    }

    /// Resolve a case-branch span, refusing an invalidated range.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the branches the span covers, in summand order.
    /// - fails: [`DomainFault::Dangling`] when the span reaches past the table.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DomainFault::Dangling`] — the span was invalidated by truncation.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::hold_branches`].
    /// - witness: `arena::tests::case_branch_spans_obey_truncation`
    #[spec(ensures: |ret| ret.as_ref().ok().copied() == self.branches.get(span.start..span.end))]
    #[inline]
    pub fn branches(
        &self,
        span: BranchSpan,
    ) -> Result<&[CompClosureId], DomainFault>
    {
        self.branches
            .get(span.start .. span.end)
            .ok_or(DomainFault::Dangling)
    }

    /// Retain a nominal constructor without copying its fields or classifier.
    ///
    /// The classifier is a suspended type, so its guard is flexible like a
    /// code's.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn value_constructor(
        &mut self,
        datatype: ValueClosureId,
        tag: gandr_core_term::ConstructorTag,
        fields: FieldSpan,
        face: TermFace,
    ) -> DomainValueId
    {
        self.alloc_value(
            DomainValue::Constructor {
                datatype,
                tag,
                fields,
                face,
            },
            Guard::Flexible,
        )
    }

    /// Retain a record with a guard over its ordered evaluated fields.
    ///
    /// Labels are compared by decomposition; leaving them out of the guard can
    /// only make that early refutation inconclusive.
    ///
    /// # Specification
    /// - requires: the source record supplies the labels in field order.
    /// - ensures: success retains the exact source, span and face.
    /// - fails: a dangling field span.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `DomainFault::Dangling` when the span does not resolve.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — native record readback retains labels and ordered
    ///   fields.
    /// - witness: `eval::tests::native_records_and_cases_compute`
    #[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|id| self.value(*id) == Some(&DomainValue::Record {source,fields,face})))]
    #[inline]
    pub fn value_record(
        &mut self,
        source: ValueId,
        fields: FieldSpan,
        face: TermFace,
    ) -> Result<DomainValueId, DomainFault>
    {
        let values = self.fields(fields)?;
        let guard = Guard::compose(
            GuardTag::Record,
            &values.len(),
            values.iter().map(|id| self.folded_value_guard(*id)),
        );
        Ok(self.alloc_value(
            DomainValue::Record {
                source,
                fields,
                face,
            },
            guard,
        ))
    }

    /// Preserve a closed native certificate as syntax, without evaluating maps.
    ///
    /// # Specification
    /// - requires: nothing; certificate syntax is checked by its consumer.
    /// - ensures: a fresh value retains `certificate` and `face` with a
    ///   flexible guard, so syntax rather than an arena id decides path
    ///   equality.
    /// - provides: a suspended native certificate without map evaluation.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — extensionally equal translator programs can differ
    ///   syntactically, while distinct evidence can describe the same maps.
    ///   Collapsing the programs or hashing certificate ids changes equality.
    /// - witness: `eval::tests::native_certificate_conversion_retains_map_syntax`
    #[inline]
    #[spec(captures: entry_length = self.values.len(), ensures: |ret|
        self.values.len().checked_sub(1) == Some(entry_length)
            && self.value(ret) == Some(&DomainValue::PathCertificate { certificate, face })
            && matches!(self.value_guard(ret), Ok(Guard::Flexible)))]
    pub fn value_path_certificate(
        &mut self,
        certificate: ValueId,
        face: TermFace,
    ) -> DomainValueId
    {
        self.alloc_value(
            DomainValue::PathCertificate { certificate, face },
            Guard::Flexible,
        )
    }

    /// Build a semantic product path from its evaluated components.
    ///
    /// # Specification
    /// - requires: nothing; dangling components are checked by their consumer.
    /// - ensures: a fresh, flexibly guarded path retains both components in
    ///   order and the supplied source face.
    /// - provides: a semantic product without reducing either translator.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — first and second components independently become
    ///   neutral or reduce. Swapping components or dropping either continuation
    ///   changes the final pair or its stuck spine.
    /// - witness: `eval::tests::native_transport_sequences_product_components`
    #[inline]
    #[spec(captures: entry_length = self.values.len(), ensures: |ret|
        self.values.len().checked_sub(1) == Some(entry_length)
            && self.value(ret) == Some(&DomainValue::PathProduct { first, second, face })
            && matches!(self.value_guard(ret), Ok(Guard::Flexible)))]
    pub fn value_path_product(
        &mut self,
        first: DomainValueId,
        second: DomainValueId,
        face: TermFace,
    ) -> DomainValueId
    {
        self.alloc_value(
            DomainValue::PathProduct {
                first,
                second,
                face,
            },
            Guard::Flexible,
        )
    }

    /// Mint a type operator over an already-allocated value closure whose body
    /// is a static lambda.
    ///
    /// An operator's guard is flexible, as a code's is: whether two operators
    /// are apart depends on the bodies they close over, which the comparison
    /// reads rather than a content hash.
    ///
    /// # Specification
    /// - requires: `lambda` names a live value closure of this arena whose body
    ///   is a static lambda.
    /// - ensures: a fresh value node carrying that closure id and `face`.
    /// - provides: the domain form a static lambda evaluates to.
    /// - fails: never — a closure that dangles surfaces where it is read.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one operator evaluated from a static lambda and read
    ///   by variant before its body is read back under a fresh binder. Swapping
    ///   the nested binders or losing the source face changes the retained id
    ///   or the rebuilt indices.
    /// - witness: `readback::tests::a_static_lambda_reads_back_with_its_binder_as_an_index`
    #[inline]
    #[spec(ensures: |ret| matches!(
        self.value(ret),
        Some(&DomainValue::StaticLambda { lambda: held, .. }) if held == lambda
    ) && matches!(self.value_guard(ret), Ok(Guard::Flexible)))]
    pub fn value_static_lambda(
        &mut self,
        lambda: ValueClosureId,
        face: TermFace,
    ) -> DomainValueId
    {
        self.alloc_value(DomainValue::StaticLambda { lambda, face }, Guard::Flexible)
    }

    /// Mint a stuck **value** over an already-allocated neutral.
    ///
    /// # Specification
    /// - requires: nothing — a dangling neutral and one stacking a computation
    ///   eliminator are both admissible input and both refused.
    /// - ensures: on success a value node standing for the neutral, whose spine
    ///   the arena has checked holds static applications alone.
    /// - provides: the one well-formedness condition of the domain that is not
    ///   structural, checked at the only site that can violate it.
    /// - fails: [`DomainFault::Dangling`] when the neutral does not resolve,
    ///   and [`DomainFault::ValueNeutralEliminatesComputation`] when its spine
    ///   stacks an application, a force, a bind or a case — the static
    ///   application is the vocabulary's one value eliminator, so any other is
    ///   a stuck computation and cannot stand in a value slot.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DomainFault::Dangling`] — the neutral id names no node.
    /// - [`DomainFault::ValueNeutralEliminatesComputation`] — the neutral
    ///   stacks a computation eliminator.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the two decision surfaces are the resolution guard
    ///   and the spine guard, separated by a spineless neutral, a neutral
    ///   carrying one static application, a neutral carrying one application,
    ///   and an id past the family, each asserted by variant. Confusing static
    ///   with computation application, or accepting a dangling id, changes the
    ///   named outcome.
    /// - witness: `arena::tests::a_value_neutral_refuses_a_computation_spine`
    #[inline]
    #[spec(ensures: |ret| match ret {
        | Ok(id) => self.neutral(neutral).is_some_and(|node| node.spine().iter().all(
                |elimination| matches!(elimination, Elimination::StaticApply(_))))
            && self.value(id).is_some_and(|value| {
                matches!(*value, DomainValue::Neutral { neutral: stored, face: stored_face }
                    if stored == neutral && stored_face == face)
            }),
        | Err(DomainFault::Dangling) => self.neutral(neutral).is_none(),
        | Err(DomainFault::ValueNeutralEliminatesComputation) =>
            self.neutral(neutral).is_some_and(|node| node.spine().iter().any(
                |elimination| !matches!(elimination, Elimination::StaticApply(_)))),
        | Err(_) => false,
    })]
    pub fn value_neutral(
        &mut self,
        neutral: NeutralId,
        face: TermFace,
    ) -> Result<DomainValueId, DomainFault>
    {
        let Some(node) = self.neutral(neutral)
        else {
            return Err(DomainFault::Dangling);
        };
        if node
            .spine()
            .iter()
            .any(|elimination| !matches!(elimination, Elimination::StaticApply(_)))
        {
            return Err(DomainFault::ValueNeutralEliminatesComputation);
        }
        let word = self.neutral_guard(neutral).unwrap_or(Guard::Flexible);
        let guard = Guard::compose(GuardTag::ValueNeutral, &(), &[word]);
        Ok(self.alloc_value(DomainValue::Neutral { neutral, face }, guard))
    }

    /// Mint a lambda over an already-allocated computation closure.
    ///
    /// # Specification
    /// - requires: `body` names a live computation closure of this arena.
    /// - ensures: a fresh computation node carrying that closure id and `face`.
    /// - provides: the weak-head form a lambda evaluates to, with the body left
    ///   unevaluated under its environment.
    /// - fails: never — a closure that dangles surfaces where an application
    ///   resolves it, not here.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — opening an identity lambda reconstructs its bound
    ///   variable rather than substituting another body; a wrong former,
    ///   payload or source face changes the observed term.
    /// - witness: `readback::tests::a_lambda_reads_back_with_its_binder_as_an_index`
    #[inline]
    #[spec(ensures: |ret| self.computation(ret) == Some(&DomainComp::Lambda { body, face }))]
    pub fn comp_lambda(
        &mut self,
        body: CompClosureId,
        face: CompTermFace,
    ) -> DomainCompId
    {
        self.alloc_computation(DomainComp::Lambda { body, face }, Guard::Flexible)
    }

    /// Mint a returner over an already-allocated value.
    ///
    /// # Specification
    /// - requires: `value` names a live value node of this arena.
    /// - ensures: a fresh computation node carrying that value id and `face`.
    /// - provides: the weak-head form a returner evaluates to, which is where a
    ///   computation's result crosses back into value position.
    /// - fails: never — a value that dangles surfaces at readback, not here.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — rebuilding a suspended returner produces the unit
    ///   held by its result; a wrong former, payload or source face changes the
    ///   observed term.
    /// - witness: `readback::tests::a_thunk_reads_back_through_the_body_it_suspends`
    #[inline]
    #[spec(ensures: |ret| self.computation(ret) == Some(&DomainComp::Return { value, face }))]
    pub fn comp_return(
        &mut self,
        value: DomainValueId,
        face: CompTermFace,
    ) -> DomainCompId
    {
        let guard = Guard::compose(GuardTag::Return, &(), &[self.folded_value_guard(value)]);
        self.alloc_computation(DomainComp::Return { value, face }, guard)
    }

    /// Mint a stuck computation over an already-allocated neutral.
    ///
    /// Unlike a value neutral this checks nothing, and the spine condition it
    /// does not check is the sibling of the one that does. A neutral's head is
    /// always a value — a variable, a declaration, a module form — and the term
    /// vocabulary has no computation-position reference former, so a
    /// computation neutral needs a spine whose first elimination carries it
    /// into computation position. Evaluation only ever mints one through
    /// [`DomainArena::neutral_node`] with an elimination already appended, so
    /// it produces no empty-spine computation neutral; a caller that builds
    /// one directly gets a node no readback can rebuild, which readback
    /// refuses by name rather than guessing at.
    ///
    /// # Specification
    /// - requires: `neutral` names a live neutral of this arena whose spine
    ///   carries at least one elimination; the paragraph above states why
    ///   neither half is checked here.
    /// - ensures: a fresh computation node carrying that neutral id and `face`,
    ///   whatever the neutral's spine holds.
    /// - provides: the stuck computation an eliminated neutral evaluates to.
    /// - fails: never — a spineless or dangling neutral yields a node readback
    ///   refuses by name rather than a refusal here.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — a force followed by an application is rebuilt with
    ///   the original argument and elimination order; a wrong former, payload
    ///   or source face changes the observed term.
    /// - witness: `readback::tests::a_stuck_spine_reads_back_as_its_eliminations`
    #[inline]
    #[spec(ensures: |ret| self.computation(ret) == Some(&DomainComp::Neutral { neutral, face }))]
    pub fn comp_neutral(
        &mut self,
        neutral: NeutralId,
        face: CompTermFace,
    ) -> DomainCompId
    {
        let word = self.neutral_guard(neutral).unwrap_or(Guard::Flexible);
        let guard = Guard::compose(GuardTag::CompNeutral, &(), &[word]);
        self.alloc_computation(DomainComp::Neutral { neutral, face }, guard)
    }

    /// Record that a neutral's body has been forced to `glued`.
    ///
    /// # Specification
    /// - requires: nothing — a dangling, a rigid and an already-forced neutral
    ///   are all admissible input.
    /// - ensures: on success the neutral's unfolding face is forced and its
    ///   head and spine are untouched.
    /// - provides: the arena-side entry to the unfolding face's one transition,
    ///   so a caller never needs a mutable neutral. The clause states the
    ///   forced face, the unchanged head, the spine's unchanged length, and the
    ///   dangling refusal; the spine's contents would need an owned entry
    ///   snapshot, which the pinned expansion evaluates even in a non-enforcing
    ///   build.
    /// - fails: [`DomainFault::Dangling`] when the id resolves to nothing, and
    ///   the neutral's own refusal translated into the same vocabulary — one
    ///   spelling of "this arena refused" rather than an `Option` around a
    ///   `Result`.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DomainFault::Dangling`] — the neutral id names no node.
    /// - [`DomainFault::NeutralIsRigid`] — the neutral has no body to force.
    /// - [`DomainFault::NeutralAlreadyForced`] — the body was forced before.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surface is the resolution guard, the
    ///   neutral's own three-state match being witnessed at its own item;
    ///   separated by forcing a resolvable neutral and an id past the family,
    ///   each asserted by variant. Collapsing either forcing refusal into
    ///   dangling, or permitting a second force, changes the returned variant.
    /// - witness: `arena::tests::forcing_a_dangling_neutral_is_refused`
    #[inline]
    #[spec(
        captures: [
            entry_head = self.neutral(neutral).map(Neutral::head),
            entry_spine = self.neutral(neutral).map(|node| node.spine().len()),
        ],
        ensures: |ret| [
            ret.is_err()
                || self
                    .neutral(neutral)
                    .is_some_and(|node| matches!(node.unfolding(), Unfolding::Forced(_))),
            self.neutral(neutral).map(Neutral::head) == entry_head,
            self.neutral(neutral).map(|node| node.spine().len()) == entry_spine,
            (ret == Err(DomainFault::Dangling)) == self.neutral(neutral).is_none(),
        ],
    )]
    pub fn force_neutral(
        &mut self,
        neutral: NeutralId,
        glued: Glued,
    ) -> Result<(), DomainFault>
    {
        let node = self
            .neutrals
            .get_mut(id_offset(ArenaIndex(neutral.0)).0)
            .ok_or(DomainFault::Dangling)?;
        let forced = node.force_to(glued);
        forced.map_err(DomainFault::from)
    }

    /// Mint a fixpoint over its own closed source node, applied to `leading`.
    ///
    /// # Specification
    /// - requires: `recursive` closes a source fixpoint over its environment,
    ///   and `leading` holds no more arguments than the binders before its
    ///   staged one.
    /// - ensures: a fresh computation node carrying that closure id, the
    ///   leading arguments and `face`.
    /// - provides: the weak-head form a fixpoint evaluates to, inert until a
    ///   gate observes it; the comparison opens it like a lambda, so its guard
    ///   is flexible.
    /// - fails: never — a closure that dangles surfaces where a gate resolves
    ///   it, not here.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a bare fixpoint reads back as itself, and a stuck one
    ///   keeps its binder; a wrong closure or face changes the observed term.
    /// - witness: `readback::tests::a_fixpoint_reads_back_with_its_self_binder`
    /// - witness: `eval::tests::a_fixpoint_staged_past_its_first_binder_carries_its_leading_arguments_626`
    #[inline]
    #[spec(ensures: |ret| self.computation(ret) == Some(&DomainComp::Fixpoint { recursive, leading, face }))]
    pub fn comp_fixpoint(
        &mut self,
        recursive: CompClosureId,
        leading: FieldSpan,
        face: CompTermFace,
    ) -> DomainCompId
    {
        self.alloc_computation(
            DomainComp::Fixpoint {
                recursive,
                leading,
                face,
            },
            Guard::Flexible,
        )
    }
}

#[cfg(test)]
mod tests;
