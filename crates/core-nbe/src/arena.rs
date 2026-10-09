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
//! that no longer exists, which is a *wrong* readback rather than a slow one —
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
//! [term face]: crate::domain::TermFace
//! [`CoreArena`]: gandr_core_term::CoreArena

use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::ComputationId;
use gandr_core_term::ValueId;
use gandr_kernel_strata::Level;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Side;

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
#[inline]
#[spec(ensures: |ret| usize::try_from(ret.0).is_ok_and(|widened| widened == length.0)
    || ret.0 == u32::MAX)]
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
#[spec(ensures: |ret| u32::try_from(ret.0).is_ok_and(|narrowed| narrowed == index.0)
    || ret.0 == usize::MAX)]
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
    #[inline]
    fn from(refusal: ForceRefusal) -> Self
    {
        match refusal {
            | ForceRefusal::Rigid => Self::NeutralIsRigid,
            | ForceRefusal::AlreadyForced => Self::NeutralAlreadyForced,
        }
    }
}

/// A snapshot of the six family lengths.
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
    #[inline]
    #[must_use]
    pub fn watermark(&self) -> RunWatermark
    {
        RunWatermark {
            values: self.values.len(),
            computations: self.computations.len(),
            neutrals: self.neutrals.len(),
            value_closures: self.value_closures.len(),
            comp_closures: self.comp_closures.len(),
            levels: self.levels.len(),
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
    ///   minted into.
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
    #[inline]
    #[must_use]
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
    #[inline]
    #[must_use]
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
    #[inline]
    #[must_use]
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
    #[inline]
    #[must_use]
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
    #[inline]
    #[must_use]
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
    #[inline]
    #[must_use]
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
    #[inline]
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
    /// - ensures: [`Guard::Flexible`] when the unfolding face is loaded, or
    ///   when the spine stacks a bind, a case, or an argument whose word is
    ///   flexible; otherwise the fold of the head and each elimination in spine
    ///   order.
    /// - provides: the rigidity rule for a stuck node: a head with a body to
    ///   unfold, or an elimination holding a closure, can change the answer.
    ///   Its cost is the spine's length, which the spine copy every extension
    ///   makes already pays.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surfaces are the loaded face, the
    ///   closure-holding eliminations and the argument's word, separated by a
    ///   rigid variable applied to a rigid argument, the same head carrying an
    ///   unforced body, and a spine stacking a bind; a static family's word is
    ///   separated by head index, by arity and by argument.
    /// - witness: `arena::tests::a_neutral_is_rigid_only_without_a_body_or_a_closure`
    /// - witness: `conv::tests::family_spines_are_separated_by_head_index_and_arity`
    fn neutral_word(
        &self,
        head: NeutralHead,
        spine: &[Elimination],
        unfolding: Unfolding,
    ) -> Guard
    {
        let mut word = match (head, unfolding) {
            | (_, Unfolding::Unforced(_) | Unfolding::Forced(_)) => return Guard::Flexible,
            | (NeutralHead::Variable { zone, level }, Unfolding::Rigid) => {
                Guard::compose(GuardTag::Variable, &(zone, level), &[])
            },
            | (NeutralHead::Constant(constant), Unfolding::Rigid) => {
                Guard::compose(GuardTag::Constant, &constant, &[])
            },
            | (NeutralHead::Module(module), Unfolding::Rigid) => {
                Guard::compose(GuardTag::Module, &module, &[])
            },
        };
        for &elimination in spine {
            word = match elimination {
                | Elimination::Apply(argument) => Guard::compose(GuardTag::Apply, &(), &[
                    word,
                    self.folded_value_guard(argument),
                ]),
                | Elimination::StaticApply(argument) => {
                    Guard::compose(GuardTag::StaticApply, &(), &[
                        word,
                        self.folded_value_guard(argument),
                    ])
                },
                | Elimination::Force => Guard::compose(GuardTag::Force, &(), &[word]),
                | Elimination::Bind(_) | Elimination::Case { .. } => return Guard::Flexible,
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    ///   asserted by variant.
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
            | NeutralHead::Constant(_) => true,
            | NeutralHead::Variable { .. } | NeutralHead::Module(_) => false,
        };
        let loaded = match unfolding {
            | Unfolding::Rigid => false,
            | Unfolding::Unforced(_) | Unfolding::Forced(_) => true,
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
    #[inline]
    pub fn value_closure_node(
        &mut self,
        body: ValueId,
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
    #[inline]
    pub fn comp_closure_node(
        &mut self,
        body: ComputationId,
        environment: Environment,
    ) -> CompClosureId
    {
        let id = CompClosureId(id_index(ArenaLength(self.comp_closures.len())).0);
        self.comp_closures.push(CompClosure::new(body, environment));
        id
    }

    /// Mint the unit value.
    ///
    /// # Specification
    /// - requires: nothing; unit carries no component that could dangle.
    /// - ensures: a fresh value node standing for unit at `face`, appended
    ///   after every value this arena already holds.
    /// - provides: the domain form a unit introduction evaluates to.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    pub fn value_unit(
        &mut self,
        face: TermFace,
    ) -> DomainValueId
    {
        let guard = Guard::compose(GuardTag::Unit, &(), &[]);
        self.alloc_value(DomainValue::Unit { face }, guard)
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
    #[inline]
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

    /// Mint a pair over two already-allocated components.
    ///
    /// # Specification
    /// - requires: `first` and `second` name live value nodes of this arena.
    /// - ensures: a fresh value node carrying both component ids in that order
    ///   and `face`.
    /// - provides: the domain form a pair introduction evaluates to, with the
    ///   components shared rather than copied.
    /// - fails: never — a component that dangles surfaces at readback, not
    ///   here.
    /// - panics: none.
    #[inline]
    pub fn value_pair(
        &mut self,
        first: DomainValueId,
        second: DomainValueId,
        face: TermFace,
    ) -> DomainValueId
    {
        let guard = Guard::compose(GuardTag::Pair, &(), &[
            self.folded_value_guard(first),
            self.folded_value_guard(second),
        ]);
        self.alloc_value(
            DomainValue::Pair {
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
    /// - ensures: a fresh value node carrying the side, the body id, and
    ///   `face`.
    /// - provides: the domain form a sum introduction evaluates to; the side is
    ///   what a case elimination selects on.
    /// - fails: never — a body that dangles surfaces at readback, not here.
    /// - panics: none.
    #[inline]
    pub fn value_injection(
        &mut self,
        side: Side,
        body: DomainValueId,
        face: TermFace,
    ) -> DomainValueId
    {
        let guard = Guard::compose(GuardTag::Injection, &side, &[self.folded_value_guard(body)]);
        self.alloc_value(DomainValue::Injection { side, body, face }, guard)
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
    #[inline]
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
    #[inline]
    pub fn value_lift(
        &mut self,
        target: LiftTarget,
        body: DomainValueId,
        face: TermFace,
    ) -> DomainValueId
    {
        let guard = match self.level(target) {
            | Some(entry) => Guard::compose(GuardTag::Lift, entry.level(), &[
                self.folded_value_guard(body)
            ]),
            | None => Guard::Flexible,
        };
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
    #[inline]
    pub fn value_code(
        &mut self,
        code: ValueClosureId,
        face: TermFace,
    ) -> DomainValueId
    {
        self.alloc_value(DomainValue::Code { code, face }, Guard::Flexible)
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
    #[inline]
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
    ///   and an id past the family, each asserted by variant.
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    ///   each asserted by variant.
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
}

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;

    use gandr_core_term::CoreArena;
    use gandr_core_term::Zone;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::GlobalIndex;

    use super::DomainArena;
    use super::DomainFault;
    use super::NeutralId;
    use super::RunWatermark;
    use crate::closure::Environment;
    use crate::domain::BinderLevel;
    use crate::domain::CompTermFace;
    use crate::domain::Elimination;
    use crate::domain::Glued;
    use crate::domain::NeutralHead;
    use crate::domain::TermFace;
    use crate::domain::Unfolding;
    use crate::guard::Guard;

    #[test]
    fn a_child_id_is_strictly_below_its_parent()
    {
        let mut arena = DomainArena::new();
        let unit = arena.value_unit(TermFace::Reduced);
        let pair = arena.value_pair(unit, unit, TermFace::Reduced);
        assert!(
            unit < pair,
            "constructor-only minting orders child below parent"
        );
    }

    #[test]
    fn truncating_to_a_watermark_drops_later_nodes()
    {
        let mut arena = DomainArena::new();
        let kept = arena.value_unit(TermFace::Reduced);
        let mark = arena.watermark();
        let dropped = arena.value_unit(TermFace::Reduced);
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
    fn truncating_to_the_floor_empties_every_family()
    {
        let mut arena = DomainArena::new();
        let floor = arena.watermark();
        let neutral = arena
            .neutral_node(
                NeutralHead::Constant(ConstantIndex::from(0_usize)),
                Vec::new(),
                Unfolding::Unforced(GlobalIndex::from(0_u32)),
            )
            .expect("a declaration head may carry a body");
        let mut core = CoreArena::new();
        let produced = core.value_unit();
        let body = core.computation_return(produced);
        let closure = arena.comp_closure_node(body, Environment::new());
        let unit = arena.value_unit(TermFace::Reduced);
        let thunk = arena.value_thunk(closure, TermFace::Reduced);
        let returner = arena.comp_return(unit, CompTermFace::Reduced);

        arena.truncate_to(floor);
        assert_eq!(
            RunWatermark::default(),
            arena.watermark(),
            "the floor is the empty arena, which is what a run's teardown is"
        );
        assert!(arena.value(unit).is_none());
        assert!(arena.value(thunk).is_none());
        assert!(arena.computation(returner).is_none());
        assert!(arena.neutral(neutral).is_none());
        assert!(arena.comp_closure(closure).is_none());
    }

    #[test]
    fn a_value_neutral_refuses_a_computation_spine()
    {
        let mut arena = DomainArena::new();
        let spineless = arena
            .neutral_node(
                NeutralHead::Module(ConstantIndex::from(0_usize)),
                Vec::new(),
                Unfolding::Rigid,
            )
            .expect("a module form is a rigid head");
        let stood = arena.value_neutral(spineless, TermFace::Reduced);
        assert!(
            stood.is_ok(),
            "a module form stands in a value position as a rigid neutral"
        );

        let unit = arena.value_unit(TermFace::Reduced);
        let operated = arena
            .neutral_node(
                NeutralHead::Constant(ConstantIndex::from(1_usize)),
                Vec::from([Elimination::StaticApply(unit)]),
                Unfolding::Rigid,
            )
            .expect("a statically applied neutral mints");
        assert!(
            arena.value_neutral(operated, TermFace::Reduced).is_ok(),
            "a static application is the one value eliminator, so its neutral stands as a value"
        );
        let applied = arena
            .neutral_node(
                NeutralHead::Constant(ConstantIndex::from(1_usize)),
                Vec::from([Elimination::Apply(unit)]),
                Unfolding::Rigid,
            )
            .expect("a spined neutral mints; it just cannot stand in a value slot");
        assert_eq!(
            Err(DomainFault::ValueNeutralEliminatesComputation),
            arena.value_neutral(applied, TermFace::Reduced),
            "an applied neutral is a stuck computation and cannot stand in a value slot"
        );
        assert_eq!(
            Err(DomainFault::Dangling),
            arena.value_neutral(NeutralId(99_u32), TermFace::Reduced),
            "and an unresolvable neutral is refused rather than minted over"
        );
    }

    #[test]
    fn a_head_that_cannot_unfold_carries_no_body()
    {
        let mut arena = DomainArena::new();
        let unit = arena.value_unit(TermFace::Reduced);
        let bound = NeutralHead::Variable {
            zone: Zone::Intuitionistic,
            level: BinderLevel::from(0_u32),
        };
        let module = NeutralHead::Module(ConstantIndex::from(0_usize));
        let declaration = NeutralHead::Constant(ConstantIndex::from(0_usize));
        let loaded = [
            Unfolding::Unforced(GlobalIndex::from(0_u32)),
            Unfolding::Forced(Glued::Value(unit)),
        ];

        for head in [bound, module] {
            assert!(
                arena
                    .neutral_node(head, Vec::new(), Unfolding::Rigid)
                    .is_ok(),
                "a head with no definition behind it mints rigid"
            );
            for face in loaded {
                assert_eq!(
                    Err(DomainFault::RigidHeadCarriesBody),
                    arena.neutral_node(head, Vec::new(), face),
                    "and is refused a body it could not have, at either loaded face"
                );
            }
        }
        assert!(
            arena
                .neutral_node(declaration, Vec::new(), Unfolding::Rigid)
                .is_ok(),
            "a declaration head mints rigid — an axiom, or a definition sealed here"
        );
        for face in loaded {
            assert!(
                arena.neutral_node(declaration, Vec::new(), face).is_ok(),
                "and it is the one head a body may stand behind"
            );
        }
    }

    #[test]
    fn forcing_a_dangling_neutral_is_refused()
    {
        let mut arena = DomainArena::new();
        let unit = arena.value_unit(TermFace::Reduced);
        assert_eq!(
            Err(DomainFault::Dangling),
            arena.force_neutral(NeutralId(4_u32), Glued::Value(unit)),
            "an unresolvable neutral is refused under the same vocabulary as any other \
             unresolvable id"
        );
        let rigid = arena
            .neutral_node(
                NeutralHead::Constant(ConstantIndex::from(0_usize)),
                Vec::new(),
                Unfolding::Rigid,
            )
            .expect("an opaque declaration is a rigid head");
        assert_eq!(
            Err(DomainFault::NeutralIsRigid),
            arena.force_neutral(rigid, Glued::Value(unit)),
            "and a resolvable neutral's own refusal arrives translated, not nested"
        );
        let unforced = arena
            .neutral_node(
                NeutralHead::Constant(ConstantIndex::from(1_usize)),
                Vec::new(),
                Unfolding::Unforced(GlobalIndex::from(0_u32)),
            )
            .expect("a declaration head may carry a body");
        assert_eq!(Ok(()), arena.force_neutral(unforced, Glued::Value(unit)));
        assert_eq!(
            Err(DomainFault::NeutralAlreadyForced),
            arena.force_neutral(unforced, Glued::Value(unit)),
            "as does the second-force refusal"
        );
    }

    #[test]
    fn a_neutral_is_rigid_only_without_a_body_or_a_closure()
    {
        let mut core = CoreArena::new();
        let mut arena = DomainArena::new();
        let argument = arena.value_unit(TermFace::Reduced);
        let head = NeutralHead::Variable {
            zone: Zone::Intuitionistic,
            level: BinderLevel::from(0_u32),
        };
        let applied = arena
            .neutral_node(
                head,
                Vec::from([Elimination::Apply(argument)]),
                Unfolding::Rigid,
            )
            .expect("a variable head stands rigid");
        assert!(
            matches!(arena.neutral_guard(applied), Ok(Guard::Rigid(_))),
            "a rigid head applied to a rigid argument is rigid"
        );

        let defined = arena
            .neutral_node(
                NeutralHead::Constant(ConstantIndex::from(0_usize)),
                Vec::from([Elimination::Apply(argument)]),
                Unfolding::Unforced(GlobalIndex::from(0_u32)),
            )
            .expect("a declaration head may carry a body");
        assert_eq!(
            Ok(Guard::Flexible),
            arena.neutral_guard(defined),
            "a head with a body to unfold is flexible"
        );
        let unit = core.value_unit();
        let body = core.computation_return(unit);
        let continuation = arena.comp_closure_node(body, Environment::new());
        let bound = arena
            .neutral_node(
                head,
                Vec::from([
                    Elimination::Apply(argument),
                    Elimination::Bind(continuation),
                ]),
                Unfolding::Rigid,
            )
            .expect("a variable head stands rigid");
        assert_eq!(
            Ok(Guard::Flexible),
            arena.neutral_guard(bound),
            "and so is a spine stacking a closure"
        );
        let stuck = arena.comp_neutral(bound, CompTermFace::Reduced);
        assert_eq!(
            Ok(Guard::Flexible),
            arena.comp_guard(stuck),
            "and the computation standing for it inherits the word"
        );
    }
}
