//! **Conversion replay**: the kernel's sequential recheck of a conversion
//! engine's trace, under a three-valued verdict.
//!
//! # What the replay trusts, and what it does not
//!
//! An engine outside the trusted base decides conversion by a concurrent search
//! and records the derivation it found as a sequence of
//! [`ConversionDecision`]s. The replay takes that sequence, the engine's claim
//! and the two sides, and **re-derives the claim one decision at a time**,
//! firing every step itself: a β-step, a δ-step on the constant the trace
//! names, a force, an η-expansion, a decomposition. A decision chooses among
//! the rules a goal admits; it never stands in for one. Nothing else the engine
//! computed is read, so a wrong engine produces a trace that fails to replay
//! rather than a wrong verdict.
//!
//! # Search-free, by expectation
//!
//! Every goal carries the verdict its derivation owes. A convertibility
//! derivation discharges every premise of a decomposition; a refutation names
//! the one premise that fails by a negative subgoal, and the replay checks only
//! that one. A refutation reached through a frozen constant or through the
//! shortcut over two applications of one constant is not authoritative —
//! failing to convert a frozen pair proves nothing about the unfolded one — so
//! those two decisions are refused under a refutation. Where the vocabulary
//! leaves a rule implicit, the replay applies the rule the two shapes force;
//! where the shapes admit a choice, it reads the next decision and applies only
//! that. Nothing is tried and undone.
//!
//! Both sides are first put in weak head form by the reductions that need no
//! choice — β, a forced thunk, a returner met by a bind, an injection met by a
//! case, never a δ-step. Then:
//!
//! | goal | what the replay reads |
//! | --- | --- |
//! | any | `ComparedShared` closes it when the sides are α-equal, or rigid and α-distinct |
//! | a defined constant at either head | `Unfold` and the reduction naming its side, with `Postpone` before it; `Freeze`; `ConstShortcut` |
//! | a thunk against a thunk or a neutral value | two `Force`s |
//! | a lambda against a neutral computation | `EtaExpand` on the neutral side |
//! | anything else | a leaf decides it or a decomposition pushes its premises; under a refutation, `NegativeSubgoal` picks the one premise |
//!
//! A rigid term is built only of formers, variables and constants without a
//! body: nothing in it can reduce, so two α-distinct rigid terms never convert.
//!
//! # Three verdicts
//!
//! [`KernelVerdict::Convertible`] and [`KernelVerdict::NotConvertible`] are
//! certified: the replay re-derived the claim. [`KernelVerdict::Declined`] is
//! neither — the engine declined, the step budget ran out, or the trace did not
//! replay — and a decline is never read as a refutation. A run the engine's
//! schedule starved declines the same way: the kernel has no search of its own
//! to recover with, and a decline costs completeness, never soundness.
//!
//! # The arena is restored
//!
//! The replay mints its reducts in the caller's arena, past the watermark it
//! found there, and truncates back to that watermark before it returns, so the
//! caller's arena holds exactly what it held before.
//!
//! # Totality
//!
//! Every loop is iterative over an explicit stack, and every step the replay
//! takes is charged to a [`ReplayBudget`], so a trace of any length and a term
//! that reduces forever both end in a verdict.

use alloc::vec::Vec;
use core::iter::Peekable;

use anodized::spec;
use gandr_kernel_check_memo::NullMemo;
use gandr_kernel_conversion_trace::ConversionDecision;
use gandr_kernel_conversion_trace::ConversionSide;
use gandr_kernel_term::AnyNode;
use gandr_kernel_term::CompType;
use gandr_kernel_term::Computation;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::Side;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;

use crate::conv::Convertibility;
use crate::conv::equal_computations;
use crate::conv::equal_values;
use crate::encoding::ContentTable;
use crate::rewrite::BinderDepth;
use crate::rewrite::shift_computation;
use crate::rewrite::shift_value;
use crate::rewrite::substitute_computation;
use crate::rewrite::substitute_value;

/// What the replay reads of a trace identifier: the constant it names, if
/// any. A caller maps its own identifiers into this before replaying.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ReplayNode
{
    /// The identifier names the constant at this admission position.
    Constant(ConstantIndex),
    /// The identifier names a node the replay does not read.
    Other,
}

/// Whether a constant has a body the replay may unfold.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Unfoldable
{
    /// The constant is defined by this closed value.
    Body(ValueId),
    /// The constant is a type operator: a value under `parameters` static
    /// binders, the innermost binder its last parameter, closed beyond them.
    ///
    /// The kernel has no static lambda, so an operator's body is handed over
    /// with its binders stripped, and unfolding it at a static application
    /// instantiates them at the application's arguments: the δβ-step a static
    /// definition's certificate replays.
    Operator
    {
        /// How many static binders the body stands under.
        parameters: ParameterCount,
        /// The body, with its parameters as its innermost free variables.
        body: ValueId,
    },
    /// The constant has no body: an axiom, an atom, or a declaration the
    /// replay was not given.
    Opaque,
}

/// How many static parameters an operator's body stands under.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ParameterCount(u32);

impl From<u32> for ParameterCount
{
    /// The parameter count of a raw count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: u32) -> Self
    {
        Self(count)
    }
}

impl From<ParameterCount> for u32
{
    /// The raw count of a parameter count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: ParameterCount) -> Self
    {
        count.0
    }
}

/// The definitions a replay may unfold, by admission position.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct Unfoldings
{
    /// The unfolding of each constant, at its admission position.
    bodies: Vec<Unfoldable>,
}

impl Unfoldings
{
    /// The unfoldings `bodies` lists, the constant at each position defined by
    /// the entry at that position.
    ///
    /// # Specification
    /// - requires: every body is a value in the arena the replay runs in,
    ///   minted below the watermark the replay finds: closed for
    ///   [`Unfoldable::Body`], closed beyond its parameters for
    ///   [`Unfoldable::Operator`].
    /// - ensures: [`Self::unfolding`] answers the entry at a constant's
    ///   position, and [`Unfoldable::Opaque`] past the end.
    /// - provides: the δ- and δβ-rules a replay may fire; a constant left
    ///   opaque is compared by name only.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the sole surface is the position lookup, separated by
    ///   a listed constant and one past the end.
    /// - witness: `replay::tests::an_unfolding_fires_only_where_the_trace_names_its_head`
    /// - witness: `replay::tests::an_operator_unfolds_by_instantiating_its_parameters_in_order`
    #[inline]
    #[must_use]
    pub const fn new(bodies: Vec<Unfoldable>) -> Self
    {
        Self { bodies }
    }

    /// How the constant `constant` unfolds.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the entry at `constant`'s position, or [`Unfoldable::Opaque`]
    ///   when the list does not reach it.
    /// - provides: the δ-rule lookup the replay runs before every unfolding.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::new`].
    /// - witness: `replay::tests::an_unfolding_fires_only_where_the_trace_names_its_head`
    #[inline]
    #[must_use]
    pub fn unfolding(
        &self,
        constant: ConstantIndex,
    ) -> Unfoldable
    {
        self.bodies
            .get(usize::from(constant))
            .copied()
            .unwrap_or(Unfoldable::Opaque)
    }
}

/// The two sides a replay compares, of one polarity.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ReplaySides
{
    /// Two values.
    Values(ValueId, ValueId),
    /// Two computations.
    Computations(ComputationId, ComputationId),
}

/// The verdict an engine claims for the trace it hands over.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum EngineClaim
{
    /// The engine found a convertibility derivation.
    Convertible,
    /// The engine found a refutation.
    NotConvertible,
    /// The engine reached no verdict.
    Declined,
}

/// The most steps one replay takes before it declines.
///
/// A step is one turn of the replay's goal loop or one weak head reduction
/// step, so the budget bounds both a long trace and a term that reduces
/// forever.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ReplayBudget(u64);

impl ReplayBudget
{
    /// A budget no well-sized conversion exhausts.
    pub const DEFAULT: Self = Self(0x0010_0000);
}

impl Default for ReplayBudget
{
    /// The [`Self::DEFAULT`] budget.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `ret == ReplayBudget::DEFAULT`.
    /// - provides: the budget a caller with no measured bound passes.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    fn default() -> Self
    {
        Self::DEFAULT
    }
}

impl From<u64> for ReplayBudget
{
    /// A budget of `steps` steps.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `u64::from(ret) == steps`.
    /// - provides: the budget's construction.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    fn from(steps: u64) -> Self
    {
        Self(steps)
    }
}

impl From<ReplayBudget> for u64
{
    /// The steps `budget` allows.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: inverse of `ReplayBudget::from`.
    /// - provides: the budget's count.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    fn from(budget: ReplayBudget) -> Self
    {
        budget.0
    }
}

/// Where a decision stands in a trace, counted from zero.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TracePosition(usize);

impl From<usize> for TracePosition
{
    /// The decision at `position`, counted from zero.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `usize::from(ret) == position`.
    /// - provides: the position's construction.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    fn from(position: usize) -> Self
    {
        Self(position)
    }
}

impl From<TracePosition> for usize
{
    /// The count `position` carries.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: inverse of `TracePosition::from`.
    /// - provides: the position's count.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    fn from(position: TracePosition) -> Self
    {
        position.0
    }
}

/// Why a trace failed to replay.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ReplayRefusal
{
    /// The trace ended while a goal still needed a decision.
    Exhausted,
    /// Every goal closed with decisions still unread, the first at `at`.
    Leftover
    {
        /// The first unread decision.
        at: TracePosition,
    },
    /// The decision at `at` names a rule the goal it was read at does not
    /// admit.
    Inapplicable
    {
        /// The decision that does not apply.
        at: TracePosition,
    },
    /// The decision at `at` would carry a refutation through a frozen constant
    /// or a shortcut, which proves nothing.
    NonAuthoritative
    {
        /// The decision that cannot refute.
        at: TracePosition,
    },
    /// A goal closed against the verdict its derivation owes.
    Contradicted
    {
        /// The next unread decision when the goal closed.
        at: TracePosition,
    },
    /// A term the replay reached does not resolve in the arena, or is in no
    /// shape a rule reads.
    Unreadable,
}

/// Why the kernel declined a claim.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ReplayDecline
{
    /// The engine claimed no verdict, so there is nothing to replay.
    EngineDeclined,
    /// The replay's step budget ran out.
    Budget,
    /// The trace did not replay.
    Refused(ReplayRefusal),
}

/// The kernel's verdict on a replayed claim.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum KernelVerdict
{
    /// Certified: the replay re-derived convertibility.
    Convertible,
    /// Certified: the replay re-derived a refutation.
    NotConvertible,
    /// No verdict, and no evidence for either.
    Declined(ReplayDecline),
}

/// Replay `trace` against `claim` for the two `sides`, firing every step in
/// `arena` and unfolding only what `unfoldings` defines.
///
/// # Specification
/// - requires: the two sides and every body in `unfoldings` live in `arena`.
/// - ensures: [`KernelVerdict::Convertible`] or
///   [`KernelVerdict::NotConvertible`] exactly when `trace` replays as a
///   derivation of `claim`: every decision applies, in order, to the goal it is
///   read at, every goal closes at the verdict its derivation owes, and no
///   decision is left over. An engine decline answers
///   [`ReplayDecline::EngineDeclined`] without reading the trace; a budget
///   exhausted answers [`ReplayDecline::Budget`]; anything else answers the
///   refusal. `arena` holds what it held on entry.
/// - provides: the certified recheck of an untrusted engine's conversion
///   verdict, search-free and sequential.
/// - fails: never — a refusal is a verdict.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the surfaces are the rule table's rows, the refusal kinds
///   and the two decline sources, each separated by a hand-written trace that
///   takes it. The traces an engine produces are replayed end to end by that
///   engine's own tests, which sit above this crate.
/// - witness: `replay::tests::a_compared_pair_closes_on_alpha_equality_or_rigid_separation`
/// - witness: `replay::tests::the_replay_reduces_before_it_reads_a_decision`
/// - witness: `replay::tests::an_unfolding_fires_only_where_the_trace_names_its_head`
/// - witness: `replay::tests::a_refutation_follows_its_negative_subgoal`
/// - witness: `replay::tests::a_frozen_branch_cannot_carry_a_refutation`
/// - witness: `replay::tests::eta_and_force_open_the_suspended_sides`
/// - witness: `replay::tests::the_replay_refuses_a_trace_that_does_not_replay`
/// - witness: `replay::tests::an_engine_decline_and_an_exhausted_budget_decline`
#[inline]
#[must_use]
pub fn replay<I>(
    arena: &mut TermArena,
    unfoldings: &Unfoldings,
    sides: ReplaySides,
    claim: EngineClaim,
    trace: I,
    budget: ReplayBudget,
) -> KernelVerdict
where
    I: IntoIterator<Item = ConversionDecision<ReplayNode>>,
{
    let expect = match claim {
        | EngineClaim::Convertible => Expect::Convertible,
        | EngineClaim::NotConvertible => Expect::NotConvertible,
        | EngineClaim::Declined => return KernelVerdict::Declined(ReplayDecline::EngineDeclined),
    };
    let (left, right) = match sides {
        | ReplaySides::Values(left, right) => (Term::Value(left), Term::Value(right)),
        | ReplaySides::Computations(left, right) => {
            (Term::Computation(left), Term::Computation(right))
        },
    };
    let watermark = arena.watermark();
    let mut run = Replay {
        arena,
        unfoldings,
        trace: trace.into_iter().peekable(),
        position: 0,
        spent: 0,
        budget: u64::from(budget),
        table: ContentTable::new(),
        memo: NullMemo,
    };
    let outcome = run.drive(Goal::premise(Premise { left, right }, expect));
    run.arena.truncate_to(watermark);
    match outcome {
        | Ok(()) => match expect {
            | Expect::Convertible => KernelVerdict::Convertible,
            | Expect::NotConvertible => KernelVerdict::NotConvertible,
        },
        | Err(Stop::Budget) => KernelVerdict::Declined(ReplayDecline::Budget),
        | Err(Stop::Refused(refusal)) => KernelVerdict::Declined(ReplayDecline::Refused(refusal)),
    }
}

/// Why a replay stopped short of a certified verdict.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Stop
{
    /// The step budget ran out.
    Budget,
    /// The trace did not replay.
    Refused(ReplayRefusal),
}

/// One side of a goal.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Term
{
    /// A value.
    Value(ValueId),
    /// A computation.
    Computation(ComputationId),
}

/// The verdict a goal's derivation owes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Expect
{
    /// The derivation proves the sides convertible.
    Convertible,
    /// The derivation refutes them.
    NotConvertible,
}

/// The constants each side has frozen since its goal's last decomposition.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct Frozen
{
    /// The left side's frozen constants.
    left: Vec<ConstantIndex>,
    /// The right side's frozen constants.
    right: Vec<ConstantIndex>,
}

impl Frozen
{
    /// The constants `side` has frozen.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the list [`Self::freeze`] built for `side`.
    /// - provides: the frozen test a head's status reads.
    /// - fails: never.
    /// - panics: none.
    fn side(
        &self,
        side: ConversionSide,
    ) -> &[ConstantIndex]
    {
        match side {
            | ConversionSide::Left => &self.left,
            | ConversionSide::Right => &self.right,
        }
    }

    /// Freeze `constant` on `side`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `self.side(side)` contains `constant`.
    /// - provides: the effect of a `Freeze` decision.
    /// - fails: never.
    /// - panics: none.
    fn freeze(
        &mut self,
        side: ConversionSide,
        constant: ConstantIndex,
    )
    {
        match side {
            | ConversionSide::Left => self.left.push(constant),
            | ConversionSide::Right => self.right.push(constant),
        }
    }
}

/// Two terms of one polarity, compared.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Premise
{
    /// The left side.
    left: Term,
    /// The right side.
    right: Term,
}

impl Premise
{
    /// Two values.
    ///
    /// # Specification
    /// trivial.
    const fn values(
        left: ValueId,
        right: ValueId,
    ) -> Self
    {
        Self {
            left: Term::Value(left),
            right: Term::Value(right),
        }
    }

    /// Two computations.
    ///
    /// # Specification
    /// trivial.
    const fn computations(
        left: ComputationId,
        right: ComputationId,
    ) -> Self
    {
        Self {
            left: Term::Computation(left),
            right: Term::Computation(right),
        }
    }
}

/// A goal awaiting its derivation.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Goal
{
    /// The left side.
    left: Term,
    /// The right side.
    right: Term,
    /// What each side froze since the goal's last decomposition.
    frozen: Frozen,
    /// The verdict the derivation owes.
    expect: Expect,
}

impl Goal
{
    /// A fresh goal over `premise`, with nothing frozen.
    ///
    /// # Specification
    /// trivial.
    fn premise(
        premise: Premise,
        expect: Expect,
    ) -> Self
    {
        Self {
            left: premise.left,
            right: premise.right,
            frozen: Frozen::default(),
            expect,
        }
    }

    /// The term on `side`.
    ///
    /// # Specification
    /// trivial.
    const fn side(
        &self,
        side: ConversionSide,
    ) -> Term
    {
        match side {
            | ConversionSide::Left => self.left,
            | ConversionSide::Right => self.right,
        }
    }

    /// Replace the term on `side` with `term`.
    ///
    /// # Specification
    /// trivial.
    const fn set(
        &mut self,
        side: ConversionSide,
        term: Term,
    )
    {
        match side {
            | ConversionSide::Left => self.left = term,
            | ConversionSide::Right => self.right = term,
        }
    }
}

/// How a constant at a head may be read on one side.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Status
{
    /// It has a body, and the side has not frozen it.
    Defined,
    /// It has a body the side froze.
    Frozen,
    /// It has no body.
    Opaque,
}

/// The head of a neutral term.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Head
{
    /// A bound variable.
    Variable(DeBruijnIndex),
    /// A constant, with its status on the side it stands on.
    Constant(ConstantIndex, Status),
}

/// One elimination of a neutral's spine.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Elimination
{
    /// The head forced.
    Force,
    /// An application to this argument.
    Apply(ValueId),
    /// A bind into this continuation.
    Bind(ComputationId),
    /// A case into these two branches.
    Case(ComputationId, ComputationId),
    /// A static application to this code: the one value elimination.
    StaticApply(ValueId),
}

/// A side's shape in weak head form.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Shape
{
    /// A unit, literal, pair, injection, lift or code.
    Former,
    /// A thunk of this computation.
    Thunk(ComputationId),
    /// A lambda over this body.
    Lambda(ComputationId),
    /// A returner of this value.
    Return(ValueId),
    /// A head under its spine, innermost elimination first; a value's spine
    /// holds static applications only.
    Neutral(Head, Vec<Elimination>),
}

/// The rule a goal's two shapes select.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Rule
{
    /// A defined constant stands at a head: the trace chooses a δ-rule.
    Constants,
    /// A thunk meets a thunk or a neutral value: both sides are forced.
    Force,
    /// A lambda meets a neutral computation on this side: it is η-expanded.
    Eta(ConversionSide),
    /// Neither side admits a choice: a leaf or a decomposition.
    Structural,
}

/// What a structural rule makes of a goal.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Structure
{
    /// The goal closes at this verdict.
    Leaf(Expect),
    /// The goal holds exactly when every premise does; never empty.
    Premises(Vec<Premise>),
}

impl Structure
{
    /// The decomposition into `premises`, a leaf when there are none.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Leaf(Convertible)` when `premises` is empty, `Premises`
    ///   otherwise.
    /// - provides: the invariant that a decomposition always has a premise to
    ///   refute through.
    /// - fails: never.
    /// - panics: none.
    fn of(premises: Vec<Premise>) -> Self
    {
        if premises.is_empty() {
            return Self::Leaf(Expect::Convertible);
        }
        Self::Premises(premises)
    }
}

/// What a compared pair closes to.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Compared
{
    /// The sides are α-equal.
    Equal,
    /// The sides are rigid and α-distinct.
    Separated,
    /// Neither: the comparison decides nothing.
    Open,
}

/// Whether a term can reduce anywhere inside it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Rigidity
{
    /// Built only of formers, variables and constants without a body.
    Rigid,
    /// It holds a thunk, a binder or a defined constant.
    Flexible,
}

/// A constant the trace postponed, awaiting the unfolding on the other side.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Postponed
{
    /// No postponement is pending.
    Nothing,
    /// The other side's head constant was postponed.
    Constant(ConstantIndex),
}

/// The next decision, or the trace's end.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Next
{
    /// The decision at the current position.
    Decision(ConversionDecision<ReplayNode>),
    /// The trace is spent.
    End,
}

/// A frame on a computation's head path.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Frame
{
    /// An application to this argument.
    Apply(ValueId),
    /// A bind into this continuation.
    Bind(ComputationId),
}

/// Whether a weak head walk reduced anything.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Progress
{
    /// The term was already in weak head form.
    Unchanged,
    /// At least one step fired.
    Reduced,
}

/// What a constants step did to its goal.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Flow
{
    /// The goal stays, rewritten.
    Continue,
    /// The goal closed or decomposed.
    Settled,
}

/// The other side.
///
/// # Specification
/// trivial.
const fn opposite(side: ConversionSide) -> ConversionSide
{
    match side {
        | ConversionSide::Left => ConversionSide::Right,
        | ConversionSide::Right => ConversionSide::Left,
    }
}

/// The refusal for an unreadable term.
///
/// # Specification
/// trivial.
const fn unreadable() -> Stop
{
    Stop::Refused(ReplayRefusal::Unreadable)
}

/// One replay in flight.
struct Replay<'run, I>
where
    I: Iterator<Item = ConversionDecision<ReplayNode>>,
{
    /// The arena reducts are minted in.
    arena: &'run mut TermArena,
    /// The δ-rules the replay may fire.
    unfoldings: &'run Unfoldings,
    /// The decisions still unread.
    trace: Peekable<I>,
    /// The position of the next unread decision.
    position: usize,
    /// The steps taken.
    spent: u64,
    /// The steps allowed.
    budget: u64,
    /// The content table the rewrite machines run against.
    table: ContentTable,
    /// The rewrite memo: off, since nothing here reuses a rewrite.
    memo: NullMemo,
}

impl<I> Replay<'_, I>
where
    I: Iterator<Item = ConversionDecision<ReplayNode>>,
{
    /// Replay the derivation of `root`, then require the trace spent.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Ok` exactly when every goal closed at its owed verdict and
    ///   no decision is left.
    /// - provides: the replay's driver.
    /// - fails: [`Stop::Budget`] or the first refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Budget`] when the steps run out; [`Stop::Refused`] when the
    /// trace does not replay.
    ///
    /// # Termination
    /// - reason: the `while let Some(goal) = goals.pop()` loop over an explicit
    ///   stack of goals, not recursion.
    /// - measure: the budget left: every goal's settling charges at least one
    ///   step, and the loop stops at the first charge past the budget.
    fn drive(
        &mut self,
        root: Goal,
    ) -> Result<(), Stop>
    {
        let mut goals = Vec::from([root]);
        while let Some(goal) = goals.pop() {
            self.settle(goal, &mut goals)?;
        }
        match self.peek() {
            | Next::End => Ok(()),
            | Next::Decision(_) => Err(Stop::Refused(ReplayRefusal::Leftover { at: self.at() })),
        }
    }

    /// Replay one goal until it closes or decomposes into `goals`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Ok` when the goal closed at its owed verdict or pushed the
    ///   premises its derivation owes.
    /// - provides: one goal's turn through the rule table.
    /// - fails: [`Stop::Budget`] or the first refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// As [`Self::drive`].
    ///
    /// # Termination
    /// - reason: the `loop` below, which rewrites the goal in place, not
    ///   recursion.
    /// - measure: the budget left: every iteration charges one step.
    fn settle(
        &mut self,
        mut goal: Goal,
        goals: &mut Vec<Goal>,
    ) -> Result<(), Stop>
    {
        let mut postponed = Postponed::Nothing;
        loop {
            self.charge()?;
            let left = self.whnf(goal.left)?;
            let right = self.whnf(goal.right)?;
            goal.left = left;
            goal.right = right;
            let left_shape = self.shape(goal.left, &goal.frozen, ConversionSide::Left)?;
            let right_shape = self.shape(goal.right, &goal.frozen, ConversionSide::Right)?;
            let next = self.peek();
            if postponed != Postponed::Nothing
                && !matches!(next, Next::Decision(ConversionDecision::Unfold { .. }))
            {
                return Err(self.refuse(next));
            }
            if matches!(
                next,
                Next::Decision(ConversionDecision::ComparedShared { .. })
            ) {
                let compared = self.compared(&goal)?;
                match compared {
                    | Compared::Equal => {
                        self.take();
                        return self.close(goal.expect, Expect::Convertible);
                    },
                    | Compared::Separated => {
                        self.take();
                        return self.close(goal.expect, Expect::NotConvertible);
                    },
                    | Compared::Open => {},
                }
            }
            match rule(&left_shape, &right_shape) {
                | Rule::Constants => {
                    let flow = self.constants(
                        &mut goal,
                        [&left_shape, &right_shape],
                        &mut postponed,
                        goals,
                    )?;
                    if flow == Flow::Settled {
                        return Ok(());
                    }
                },
                | Rule::Force => self.force(&mut goal)?,
                | Rule::Eta(side) => self.eta(&mut goal, side)?,
                | Rule::Structural => {
                    return self.structural(&goal, &left_shape, &right_shape, goals);
                },
            }
        }
    }

    /// Apply the δ-rule decision the trace names at a goal with a defined
    /// head.
    ///
    /// # Specification
    /// - requires: `shapes` are the goal's left and right shapes, at least one
    ///   with a defined head.
    /// - ensures: an `Unfold` and its reduction replace that side's head by its
    ///   body; a `Postpone` waits for the unfolding on the other side; a
    ///   `Freeze` freezes a defined head; a `ConstShortcut` over one constant
    ///   with agreeing spines pushes the spines' premises into `goals`.
    /// - provides: the replay of every two-sided constant rule.
    /// - fails: a refusal when the decision does not apply, or would refute
    ///   through a freeze or a shortcut.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Refused`].
    fn constants(
        &mut self,
        goal: &mut Goal,
        shapes: [&Shape; 2],
        postponed: &mut Postponed,
        goals: &mut Vec<Goal>,
    ) -> Result<Flow, Stop>
    {
        let [left, right] = shapes;
        let shape_of = |side: ConversionSide| match side {
            | ConversionSide::Left => left,
            | ConversionSide::Right => right,
        };
        let next = self.peek();
        let Next::Decision(decision) = next
        else {
            return Err(self.refuse(next));
        };
        match decision {
            | ConversionDecision::Unfold {
                constant: ReplayNode::Constant(name),
            } => {
                self.take();
                let reduction = self.peek();
                let side = match reduction {
                    | Next::Decision(ConversionDecision::ReduceLeft { redex })
                        if redex == ReplayNode::Constant(name) =>
                    {
                        ConversionSide::Left
                    },
                    | Next::Decision(ConversionDecision::ReduceRight { redex })
                        if redex == ReplayNode::Constant(name) =>
                    {
                        ConversionSide::Right
                    },
                    | Next::Decision(_) | Next::End => return Err(self.refuse(reduction)),
                };
                let unfolds = matches!(shape_of(side), &Shape::Neutral(Head::Constant(head, Status::Defined), _) if head == name);
                let waits = match *postponed {
                    | Postponed::Nothing => true,
                    | Postponed::Constant(other) => matches!(
                        shape_of(opposite(side)),
                        &Shape::Neutral(Head::Constant(head, Status::Defined), _) if head == other
                    ),
                };
                if !(unfolds && waits) {
                    return Err(self.refuse(reduction));
                }
                self.take();
                self.unfold(goal, side, name)?;
                *postponed = Postponed::Nothing;
                Ok(Flow::Continue)
            },
            | ConversionDecision::Postpone {
                constant: ReplayNode::Constant(name),
            } if *postponed == Postponed::Nothing => {
                self.take();
                *postponed = Postponed::Constant(name);
                Ok(Flow::Continue)
            },
            | ConversionDecision::Freeze {
                constant: ReplayNode::Constant(name),
                side,
            } => {
                if goal.expect == Expect::NotConvertible {
                    return Err(Stop::Refused(ReplayRefusal::NonAuthoritative {
                        at: self.at(),
                    }));
                }
                if !matches!(shape_of(side), &Shape::Neutral(Head::Constant(head, Status::Defined), _) if head == name)
                {
                    return Err(self.refuse(next));
                }
                self.take();
                goal.frozen.freeze(side, name);
                Ok(Flow::Continue)
            },
            | ConversionDecision::ConstShortcut {
                constant: ReplayNode::Constant(name),
            } => {
                if goal.expect == Expect::NotConvertible {
                    return Err(Stop::Refused(ReplayRefusal::NonAuthoritative {
                        at: self.at(),
                    }));
                }
                let (
                    &Shape::Neutral(
                        Head::Constant(left_head, Status::Defined | Status::Frozen),
                        ref left_spine,
                    ),
                    &Shape::Neutral(
                        Head::Constant(right_head, Status::Defined | Status::Frozen),
                        ref right_spine,
                    ),
                ) = (left, right)
                else {
                    return Err(self.refuse(next));
                };
                if left_head != name || right_head != name {
                    return Err(self.refuse(next));
                }
                self.take();
                let premises = match spines(left_spine, right_spine) {
                    | Structure::Leaf(verdict) => {
                        return self.close(goal.expect, verdict).map(|()| Flow::Settled);
                    },
                    | Structure::Premises(premises) => premises,
                };
                goals.extend(
                    premises
                        .into_iter()
                        .rev()
                        .map(|premise| Goal::premise(premise, Expect::Convertible)),
                );
                Ok(Flow::Settled)
            },
            | ConversionDecision::ReduceLeft { .. }
            | ConversionDecision::ReduceRight { .. }
            | ConversionDecision::ConstShortcut { .. }
            | ConversionDecision::Unfold { .. }
            | ConversionDecision::Postpone { .. }
            | ConversionDecision::Freeze { .. }
            | ConversionDecision::EtaExpand { .. }
            | ConversionDecision::Force { .. }
            | ConversionDecision::ComparedShared { .. }
            | ConversionDecision::NegativeSubgoal { .. } => Err(self.refuse(next)),
        }
    }

    /// Force both sides of a thunk goal on the trace's two `Force`s.
    ///
    /// # Specification
    /// - requires: the goal is a thunk against a thunk or a neutral value.
    /// - ensures: a thunk side becomes its body, a neutral side its force.
    /// - provides: the replay of the force rule.
    /// - fails: a refusal unless the next two decisions are `Force`s.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Refused`].
    fn force(
        &mut self,
        goal: &mut Goal,
    ) -> Result<(), Stop>
    {
        for _ in [ConversionSide::Left, ConversionSide::Right] {
            let next = self.peek();
            if !matches!(next, Next::Decision(ConversionDecision::Force { .. })) {
                return Err(self.refuse(next));
            }
            self.take();
        }
        let left = self.forced(goal.left)?;
        let right = self.forced(goal.right)?;
        goal.left = left;
        goal.right = right;
        Ok(())
    }

    /// The computation `term` runs when forced.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a thunk's body, or the force of a variable or a constant.
    /// - provides: one side of the force rule.
    /// - fails: [`ReplayRefusal::Unreadable`] on any other term.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Refused`].
    fn forced(
        &mut self,
        term: Term,
    ) -> Result<Term, Stop>
    {
        let Term::Value(value) = term
        else {
            return Err(unreadable());
        };
        match self.arena.value(value) {
            | Some(&Value::Thunk(body)) => Ok(Term::Computation(body)),
            | Some(&(Value::Variable(_) | Value::Constant(_))) => {
                Ok(Term::Computation(self.arena.computation_force(value)))
            },
            | Some(
                &(Value::Unit
                | Value::Literal(_)
                | Value::Pair(..)
                | Value::Injection(..)
                | Value::Lift { .. }
                | Value::Quote(_)
                | Value::QuoteComputation(_)
                | Value::StaticApplication(..)),
            )
            | None => Err(unreadable()),
        }
    }

    /// η-expand the neutral `side` of a lambda goal on the trace's
    /// `EtaExpand`.
    ///
    /// # Specification
    /// - requires: `side` is a neutral computation and the other side a lambda.
    /// - ensures: the neutral side becomes its shift applied to the fresh
    ///   variable, and the lambda side its body.
    /// - provides: the replay of the η rule.
    /// - fails: a refusal unless the next decision is an `EtaExpand` naming
    ///   `side`.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Refused`].
    fn eta(
        &mut self,
        goal: &mut Goal,
        side: ConversionSide,
    ) -> Result<(), Stop>
    {
        let next = self.peek();
        if !matches!(next, Next::Decision(ConversionDecision::EtaExpand { side: named, .. }) if named == side)
        {
            return Err(self.refuse(next));
        }
        let (Term::Computation(neutral), Term::Computation(lambda)) =
            (goal.side(side), goal.side(opposite(side)))
        else {
            return Err(unreadable());
        };
        let Some(&Computation::Lambda(body)) = self.arena.computation(lambda)
        else {
            return Err(unreadable());
        };
        self.take();
        let shifted = shift_computation(
            self.arena,
            &mut self.table,
            &mut self.memo,
            neutral,
            BinderDepth::default(),
            BinderDepth::from(1),
        );
        let variable = self.arena.value_variable(DeBruijnIndex::from(0));
        let applied = self.arena.computation_application(shifted, variable);
        goal.set(side, Term::Computation(applied));
        goal.set(opposite(side), Term::Computation(body));
        Ok(())
    }

    /// Close or decompose a goal no decision is needed to rewrite.
    ///
    /// # Specification
    /// - requires: the goal selected [`Rule::Structural`].
    /// - ensures: a leaf closes at its verdict; a decomposition owing
    ///   convertibility pushes every premise, and one owing a refutation pushes
    ///   the premise the next `NegativeSubgoal` names.
    /// - provides: the rules the vocabulary leaves implicit.
    /// - fails: a refusal on a leaf against the owed verdict, or a refutation
    ///   without its negative subgoal.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Refused`].
    fn structural(
        &mut self,
        goal: &Goal,
        left: &Shape,
        right: &Shape,
        goals: &mut Vec<Goal>,
    ) -> Result<(), Stop>
    {
        let structure = self.decompose(goal, left, right)?;
        let premises = match structure {
            | Structure::Leaf(verdict) => return self.close(goal.expect, verdict),
            | Structure::Premises(premises) => premises,
        };
        match goal.expect {
            | Expect::Convertible => {
                goals.extend(
                    premises
                        .into_iter()
                        .rev()
                        .map(|premise| Goal::premise(premise, Expect::Convertible)),
                );
                Ok(())
            },
            | Expect::NotConvertible => {
                let next = self.peek();
                let Next::Decision(ConversionDecision::NegativeSubgoal { position }) = next
                else {
                    return Err(self.refuse(next));
                };
                let Some(&premise) = usize::try_from(u32::from(position))
                    .ok()
                    .and_then(|index| premises.get(index))
                else {
                    return Err(self.refuse(next));
                };
                self.take();
                goals.push(Goal::premise(premise, Expect::NotConvertible));
                Ok(())
            },
        }
    }

    /// The structural rule two shapes force.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: two formers of one kind decompose child by child, or close on
    ///   their payloads; two codes close on α-equality or rigid separation; two
    ///   returners, two lambdas, and two neutrals with one head and agreeing
    ///   spines decompose; every other pair is a refuting leaf.
    /// - provides: the leaf and decomposition rules.
    /// - fails: [`ReplayRefusal::Unreadable`] on a dangling former.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Refused`].
    fn decompose(
        &self,
        goal: &Goal,
        left: &Shape,
        right: &Shape,
    ) -> Result<Structure, Stop>
    {
        let structure = match (left, right) {
            | (&Shape::Former, &Shape::Former) => {
                let (Term::Value(left_value), Term::Value(right_value)) = (goal.left, goal.right)
                else {
                    return Err(unreadable());
                };
                return self.formers(left_value, right_value);
            },
            | (&Shape::Return(left_value), &Shape::Return(right_value)) => {
                Structure::of(Vec::from([Premise::values(left_value, right_value)]))
            },
            | (&Shape::Lambda(left_body), &Shape::Lambda(right_body)) => {
                Structure::of(Vec::from([Premise::computations(left_body, right_body)]))
            },
            | (
                &Shape::Neutral(left_head, ref left_spine),
                &Shape::Neutral(right_head, ref right_spine),
            ) if left_head == right_head => spines(left_spine, right_spine),
            | (
                &(Shape::Former
                | Shape::Thunk(_)
                | Shape::Lambda(_)
                | Shape::Return(_)
                | Shape::Neutral(..)),
                _,
            ) => Structure::Leaf(Expect::NotConvertible),
        };
        Ok(structure)
    }

    /// The structural rule over two value formers.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`Self::decompose`], over the value formers.
    /// - provides: the former half of [`Self::decompose`].
    /// - fails: [`ReplayRefusal::Unreadable`] on a dangling id.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Refused`].
    fn formers(
        &self,
        left: ValueId,
        right: ValueId,
    ) -> Result<Structure, Stop>
    {
        let (Some(one), Some(other)) = (self.arena.value(left), self.arena.value(right))
        else {
            return Err(unreadable());
        };
        let structure = match (one, other) {
            | (&Value::Unit, &Value::Unit) => Structure::Leaf(Expect::Convertible),
            | (&Value::Literal(_), &Value::Literal(_)) if one == other => {
                Structure::Leaf(Expect::Convertible)
            },
            | (&Value::Pair(left_first, left_second), &Value::Pair(right_first, right_second)) => {
                Structure::of(Vec::from([
                    Premise::values(left_first, right_first),
                    Premise::values(left_second, right_second),
                ]))
            },
            | (
                &Value::Injection(left_side, left_body),
                &Value::Injection(right_side, right_body),
            ) if left_side == right_side => {
                Structure::of(Vec::from([Premise::values(left_body, right_body)]))
            },
            | (
                &Value::Lift {
                    target: ref left_target,
                    body: left_body,
                },
                &Value::Lift {
                    target: ref right_target,
                    body: right_body,
                },
            ) if left_target == right_target => {
                Structure::of(Vec::from([Premise::values(left_body, right_body)]))
            },
            // A code's children are types, which no value premise can carry,
            // so a pair of codes closes here as the shared comparison would:
            // α-equal codes convert, rigid α-distinct codes are apart, and a
            // pair neither settles is refused rather than guessed at.
            | (&Value::Quote(_), &Value::Quote(_))
            | (&Value::QuoteComputation(_), &Value::QuoteComputation(_)) => {
                if equal_values(self.arena, left, right) == Convertibility::Convertible {
                    Structure::Leaf(Expect::Convertible)
                }
                else if matches!(
                    (
                        self.rigidity(Term::Value(left)),
                        self.rigidity(Term::Value(right))
                    ),
                    (Rigidity::Rigid, Rigidity::Rigid)
                ) {
                    Structure::Leaf(Expect::NotConvertible)
                }
                else {
                    return Err(unreadable());
                }
            },
            | (
                &(Value::Variable(_)
                | Value::Constant(_)
                | Value::Unit
                | Value::Literal(_)
                | Value::Pair(..)
                | Value::Injection(..)
                | Value::Thunk(_)
                | Value::Lift { .. }
                | Value::Quote(_)
                | Value::QuoteComputation(_)
                | Value::StaticApplication(..)),
                _,
            ) => Structure::Leaf(Expect::NotConvertible),
        };
        Ok(structure)
    }

    /// Close a `ComparedShared` goal, or report that it decides nothing.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Compared::Equal`] when the sides are α-equal,
    ///   [`Compared::Separated`] when both are rigid and α-distinct,
    ///   [`Compared::Open`] otherwise.
    /// - provides: the replay of a closing on two shared nodes.
    /// - fails: [`ReplayRefusal::Unreadable`] on sides of two polarities.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Refused`].
    fn compared(
        &self,
        goal: &Goal,
    ) -> Result<Compared, Stop>
    {
        let equality = match (goal.left, goal.right) {
            | (Term::Value(left), Term::Value(right)) => equal_values(self.arena, left, right),
            | (Term::Computation(left), Term::Computation(right)) => {
                equal_computations(self.arena, left, right)
            },
            | (Term::Value(_), Term::Computation(_)) | (Term::Computation(_), Term::Value(_)) => {
                return Err(unreadable());
            },
        };
        if equality == Convertibility::Convertible {
            return Ok(Compared::Equal);
        }
        match (self.rigidity(goal.left), self.rigidity(goal.right)) {
            | (Rigidity::Rigid, Rigidity::Rigid) => Ok(Compared::Separated),
            | (Rigidity::Rigid | Rigidity::Flexible, _) => Ok(Compared::Open),
        }
    }

    /// Whether anything inside `term` can reduce.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Rigidity::Rigid`] exactly when `term` holds no thunk, no
    ///   lambda, no bind or case, and no constant with a body or an operator
    ///   body — through the types its quotes hold, the codes those types decode
    ///   as, and the heads and arguments of its static applications as well —
    ///   and resolves throughout. No static lambda exists, so a static
    ///   application over an opaque head is rigid.
    /// - provides: the separation half of [`Self::compared`].
    /// - fails: never — a dangling id is flexible.
    /// - panics: none.
    ///
    /// # Termination
    /// - reason: the `while let Some(next) = work.pop()` loop over an explicit
    ///   worklist, not recursion.
    /// - measure: the multiset of arena positions on the worklist: a node is
    ///   replaced by its children, which the arena minted before it within a
    ///   family; a crossing between families is to a node the quote or the
    ///   decode holds, and the arena is finite and acyclic across them.
    fn rigidity(
        &self,
        term: Term,
    ) -> Rigidity
    {
        let mut work = Vec::from([match term {
            | Term::Value(value) => AnyNode::Value(value),
            | Term::Computation(computation) => AnyNode::Computation(computation),
        }]);
        while let Some(next) = work.pop() {
            match next {
                | AnyNode::Value(value) => match self.arena.value(value) {
                    | Some(&(Value::Unit | Value::Literal(_) | Value::Variable(_))) => {},
                    | Some(
                        &(Value::Pair(first, second) | Value::StaticApplication(first, second)),
                    ) => {
                        work.extend([AnyNode::Value(first), AnyNode::Value(second)]);
                    },
                    | Some(&(Value::Injection(_, body) | Value::Lift { body, .. })) => {
                        work.push(AnyNode::Value(body));
                    },
                    | Some(&Value::Constant(constant)) => {
                        if self.unfoldings.unfolding(constant) != Unfoldable::Opaque {
                            return Rigidity::Flexible;
                        }
                    },
                    | Some(&Value::Quote(quoted)) => work.push(AnyNode::ValueType(quoted)),
                    | Some(&Value::QuoteComputation(quoted)) => {
                        work.push(AnyNode::CompType(quoted));
                    },
                    | Some(&Value::Thunk(_)) | None => return Rigidity::Flexible,
                },
                | AnyNode::Computation(computation) => match self.arena.computation(computation) {
                    | Some(&(Computation::Return(value) | Computation::Force(value))) => {
                        work.push(AnyNode::Value(value));
                    },
                    | Some(&Computation::Application(head, argument)) => {
                        work.extend([AnyNode::Computation(head), AnyNode::Value(argument)]);
                    },
                    | Some(
                        &(Computation::Lambda(_)
                        | Computation::Bind(..)
                        | Computation::Case { .. }),
                    )
                    | None => {
                        return Rigidity::Flexible;
                    },
                },
                | AnyNode::ValueType(value_type) => match self.arena.value_type(value_type) {
                    | Some(
                        &(ValueType::Base(_)
                        | ValueType::Unit
                        | ValueType::Universe { .. }
                        | ValueType::Abstract(_)),
                    ) => {},
                    | Some(
                        &(ValueType::Product(first, second)
                        | ValueType::Sum(first, second)
                        | ValueType::StaticPi {
                            domain: first,
                            codomain: second,
                        }),
                    ) => {
                        work.extend([AnyNode::ValueType(first), AnyNode::ValueType(second)]);
                    },
                    | Some(&ValueType::Thunk(body)) => work.push(AnyNode::CompType(body)),
                    | Some(&ValueType::Lift { inner, .. }) => work.push(AnyNode::ValueType(inner)),
                    | Some(&ValueType::Element { code, .. }) => work.push(AnyNode::Value(code)),
                    | None => return Rigidity::Flexible,
                },
                | AnyNode::CompType(comp_type) => match self.arena.comp_type(comp_type) {
                    | Some(&CompType::Returner(result)) => work.push(AnyNode::ValueType(result)),
                    | Some(
                        &(CompType::Arrow { domain, codomain } | CompType::Pi { domain, codomain }),
                    ) => {
                        work.extend([AnyNode::ValueType(domain), AnyNode::CompType(codomain)]);
                    },
                    | Some(&CompType::Element { code, .. }) => work.push(AnyNode::Value(code)),
                    | None => return Rigidity::Flexible,
                },
            }
        }
        Rigidity::Rigid
    }

    /// The shape of `term` in weak head form, with each constant head's status
    /// on `side`.
    ///
    /// # Specification
    /// - requires: `term` is in weak head form.
    /// - ensures: a value's former, thunk, or head under its static
    ///   applications, innermost first; a computation's lambda, returner, or
    ///   head under its spine, innermost first.
    /// - provides: what the rule table dispatches on.
    /// - fails: [`ReplayRefusal::Unreadable`] on a dangling id or a head no
    ///   rule reads.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Refused`].
    ///
    /// # Termination
    /// - reason: the `loop` below, which descends a computation's head path,
    ///   and the `while let` loop descending a value's static applications, not
    ///   recursion.
    /// - measure: the arena position of the focus, which falls at every descent
    ///   because a child is minted before its parent.
    fn shape(
        &self,
        term: Term,
        frozen: &Frozen,
        side: ConversionSide,
    ) -> Result<Shape, Stop>
    {
        let start = match term {
            | Term::Value(value) => {
                return match self.arena.value(value) {
                    | Some(&Value::Variable(index)) => {
                        Ok(Shape::Neutral(Head::Variable(index), Vec::new()))
                    },
                    | Some(&Value::Constant(constant)) => Ok(Shape::Neutral(
                        self.head(constant, frozen, side),
                        Vec::new(),
                    )),
                    | Some(&Value::Thunk(body)) => Ok(Shape::Thunk(body)),
                    | Some(&Value::StaticApplication(..)) => {
                        let mut spine = Vec::new();
                        let mut focus = value;
                        while let Some(&Value::StaticApplication(head, argument)) =
                            self.arena.value(focus)
                        {
                            spine.push(Elimination::StaticApply(argument));
                            focus = head;
                        }
                        spine.reverse();
                        let head = self.value_head(focus, frozen, side)?;
                        Ok(Shape::Neutral(head, spine))
                    },
                    | Some(
                        &(Value::Unit
                        | Value::Literal(_)
                        | Value::Pair(..)
                        | Value::Injection(..)
                        | Value::Lift { .. }
                        | Value::Quote(_)
                        | Value::QuoteComputation(_)),
                    ) => Ok(Shape::Former),
                    | None => Err(unreadable()),
                };
            },
            | Term::Computation(computation) => computation,
        };
        let mut spine = Vec::new();
        let mut focus = start;
        let head = loop {
            match self.arena.computation(focus) {
                | Some(&Computation::Lambda(body)) if spine.is_empty() => {
                    return Ok(Shape::Lambda(body));
                },
                | Some(&Computation::Return(value)) if spine.is_empty() => {
                    return Ok(Shape::Return(value));
                },
                | Some(&Computation::Application(head, argument)) => {
                    spine.push(Elimination::Apply(argument));
                    focus = head;
                },
                | Some(&Computation::Bind(bound, body)) => {
                    spine.push(Elimination::Bind(body));
                    focus = bound;
                },
                | Some(&Computation::Force(value)) => {
                    spine.push(Elimination::Force);
                    let head = self.value_head(value, frozen, side)?;
                    break head;
                },
                | Some(&Computation::Case {
                    scrutinee,
                    on_left,
                    on_right,
                }) => {
                    spine.push(Elimination::Case(on_left, on_right));
                    let head = self.value_head(scrutinee, frozen, side)?;
                    break head;
                },
                | Some(&(Computation::Lambda(_) | Computation::Return(_))) | None => {
                    return Err(unreadable());
                },
            }
        };
        spine.reverse();
        Ok(Shape::Neutral(head, spine))
    }

    /// The head a forced, scrutinized or statically applied value stands for.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a variable's or a constant's head.
    /// - provides: the head half of [`Self::shape`].
    /// - fails: [`ReplayRefusal::Unreadable`] on any other value.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Refused`].
    fn value_head(
        &self,
        value: ValueId,
        frozen: &Frozen,
        side: ConversionSide,
    ) -> Result<Head, Stop>
    {
        match self.arena.value(value) {
            | Some(&Value::Variable(index)) => Ok(Head::Variable(index)),
            | Some(&Value::Constant(constant)) => Ok(self.head(constant, frozen, side)),
            | Some(
                &(Value::Unit
                | Value::Literal(_)
                | Value::Pair(..)
                | Value::Injection(..)
                | Value::Thunk(_)
                | Value::Lift { .. }
                | Value::Quote(_)
                | Value::QuoteComputation(_)
                | Value::StaticApplication(..)),
            )
            | None => Err(unreadable()),
        }
    }

    /// The head `constant` makes on `side`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Status::Opaque`] without a body, [`Status::Frozen`] when
    ///   `side` froze it, [`Status::Defined`] otherwise; an operator body is a
    ///   body.
    /// - provides: the status the constant rules read.
    /// - fails: never.
    /// - panics: none.
    fn head(
        &self,
        constant: ConstantIndex,
        frozen: &Frozen,
        side: ConversionSide,
    ) -> Head
    {
        let status = match self.unfoldings.unfolding(constant) {
            | Unfoldable::Opaque => Status::Opaque,
            | Unfoldable::Body(_) | Unfoldable::Operator { .. }
                if frozen.side(side).contains(&constant) =>
            {
                Status::Frozen
            },
            | Unfoldable::Body(_) | Unfoldable::Operator { .. } => Status::Defined,
        };
        Head::Constant(constant, status)
    }

    /// Replace the head constant `constant` on `side` by its body.
    ///
    /// # Specification
    /// - requires: `side`'s head is `constant`, defined.
    /// - ensures: a value side becomes its δ- or δβ-reduct, as
    ///   [`Self::unfold_value`] gives it; a computation side keeps its spine
    ///   over the body.
    /// - provides: the δ-step, and the δβ-step of a static definition.
    /// - fails: a refusal when `constant` has no body, the side has no head, or
    ///   an operator heads a computation.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Refused`].
    ///
    /// # Termination
    /// - reason: the `loop` descending the head path and the `while let` loop
    ///   rebuilding it, not recursion.
    /// - measure: the focus's arena position while descending, and the frames
    ///   left while rebuilding.
    fn unfold(
        &mut self,
        goal: &mut Goal,
        side: ConversionSide,
        constant: ConstantIndex,
    ) -> Result<(), Stop>
    {
        let unfolding = self.unfoldings.unfolding(constant);
        let start = match goal.side(side) {
            | Term::Value(value) => {
                let reduct = self.unfold_value(value, unfolding)?;
                goal.set(side, Term::Value(reduct));
                return Ok(());
            },
            | Term::Computation(computation) => computation,
        };
        // An operator classifies codes, so it is never forced or scrutinized:
        // only a body stands at a computation's head.
        let Unfoldable::Body(body) = unfolding
        else {
            return Err(unreadable());
        };
        let mut frames = Vec::new();
        let mut focus = start;
        let mut rebuilt = loop {
            match self.arena.computation(focus) {
                | Some(&Computation::Application(head, argument)) => {
                    frames.push(Frame::Apply(argument));
                    focus = head;
                },
                | Some(&Computation::Bind(bound, next)) => {
                    frames.push(Frame::Bind(next));
                    focus = bound;
                },
                | Some(&Computation::Force(_)) => break self.arena.computation_force(body),
                | Some(&Computation::Case {
                    on_left, on_right, ..
                }) => {
                    break self.arena.computation_case(body, on_left, on_right);
                },
                | Some(&(Computation::Lambda(_) | Computation::Return(_))) | None => {
                    return Err(unreadable());
                },
            }
        };
        while let Some(frame) = frames.pop() {
            rebuilt = self.wrap(rebuilt, frame);
        }
        goal.set(side, Term::Computation(rebuilt));
        Ok(())
    }

    /// The reduct of a value side headed by a defined constant, under the
    /// side's static applications.
    ///
    /// # Specification
    /// - requires: `unfolding` is how the constant at `value`'s head unfolds.
    /// - ensures: for a body, the body under every static application of the
    ///   side, in order; for an operator of `n` parameters, its body with its
    ///   binders instantiated at the side's first `n` arguments — the last
    ///   argument at the innermost binder, each argument shifted past the
    ///   binders still standing outside it — under the remaining applications.
    /// - provides: δ at a value, and the δβ-step of a static definition: one
    ///   saturated instance of the operator, reduced by substitution.
    /// - fails: [`ReplayRefusal::Unreadable`] when the head is not a constant,
    ///   the constant is opaque, or an operator has fewer arguments than
    ///   parameters.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Refused`].
    ///
    /// # Termination
    /// - reason: the `while let` loop descending the head path and the two
    ///   `for` loops over finite argument slices, not recursion.
    /// - measure: the focus's arena position while descending; then the
    ///   arguments left.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — separated by an operator of two parameters at its two
    ///   arguments, in order and swapped, at an argument open in the ambient
    ///   context, through an alias whose body stands under the spine, and short
    ///   of its arguments.
    /// - witness: `replay::tests::an_operator_unfolds_by_instantiating_its_parameters_in_order`
    #[spec(ensures: |ret| match ret {
        | Ok(reduct) => self.arena.value(reduct).is_some(),
        | Err(_) => true,
    })]
    fn unfold_value(
        &mut self,
        value: ValueId,
        unfolding: Unfoldable,
    ) -> Result<ValueId, Stop>
    {
        let mut arguments = Vec::new();
        let mut focus = value;
        while let Some(&Value::StaticApplication(head, argument)) = self.arena.value(focus) {
            arguments.push(argument);
            focus = head;
        }
        arguments.reverse();
        if !matches!(self.arena.value(focus), Some(&Value::Constant(_))) {
            return Err(unreadable());
        }
        let (mut reduct, consumed) = match unfolding {
            | Unfoldable::Opaque => return Err(unreadable()),
            | Unfoldable::Body(body) => (body, 0_usize),
            | Unfoldable::Operator { parameters, body } => {
                let count =
                    usize::try_from(u32::from(parameters)).map_err(|_overflow| unreadable())?;
                let Some(instantiated) = arguments.get(.. count)
                else {
                    return Err(unreadable());
                };
                let mut reduct = body;
                for (outside, &argument) in instantiated.iter().enumerate().rev() {
                    let binders = u32::try_from(outside).map_err(|_overflow| unreadable())?;
                    let carried = shift_value(
                        self.arena,
                        &mut self.table,
                        &mut self.memo,
                        argument,
                        BinderDepth::default(),
                        BinderDepth::from(binders),
                    );
                    reduct = substitute_value(
                        self.arena,
                        &mut self.table,
                        &mut self.memo,
                        reduct,
                        carried,
                    );
                }
                (reduct, count)
            },
        };
        for &argument in arguments.get(consumed ..).unwrap_or_default() {
            reduct = self.arena.value_static_application(reduct, argument);
        }
        Ok(reduct)
    }

    /// Put `term` in weak head form by the reductions that need no choice.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a value unchanged; a computation reduced by β, a forced
    ///   thunk, a returner met by a bind and an injection met by a case until
    ///   none fires at its head, and the original id when none fired at all.
    /// - provides: the search-free reductions the trace never records.
    /// - fails: [`Stop::Budget`] on a term that reduces past the budget;
    ///   [`ReplayRefusal::Unreadable`] on a dangling id.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Budget`] or [`Stop::Refused`].
    ///
    /// # Termination
    /// - reason: the `loop` below, which takes one step per iteration, and the
    ///   `while let` loop rebuilding the head path, not recursion.
    /// - measure: the budget left, which every iteration charges; then the
    ///   frames left.
    fn whnf(
        &mut self,
        term: Term,
    ) -> Result<Term, Stop>
    {
        let Term::Computation(start) = term
        else {
            return Ok(term);
        };
        let mut frames: Vec<Frame> = Vec::new();
        let mut focus = start;
        let mut progress = Progress::Unchanged;
        loop {
            self.charge()?;
            match self.arena.computation(focus) {
                | Some(&Computation::Application(head, argument)) => {
                    frames.push(Frame::Apply(argument));
                    focus = head;
                },
                | Some(&Computation::Bind(bound, body)) => {
                    frames.push(Frame::Bind(body));
                    focus = bound;
                },
                | Some(&Computation::Force(value)) => match self.arena.value(value) {
                    | Some(&Value::Thunk(body)) => {
                        focus = body;
                        progress = Progress::Reduced;
                    },
                    | Some(_) => break,
                    | None => return Err(unreadable()),
                },
                | Some(&Computation::Case {
                    scrutinee,
                    on_left,
                    on_right,
                }) => match self.arena.value(scrutinee) {
                    | Some(&Value::Injection(side, payload)) => {
                        let branch = match side {
                            | Side::Left => on_left,
                            | Side::Right => on_right,
                        };
                        focus = self.instantiate(branch, payload);
                        progress = Progress::Reduced;
                    },
                    | Some(_) => break,
                    | None => return Err(unreadable()),
                },
                | Some(&Computation::Lambda(body)) => match frames.last() {
                    | Some(&Frame::Apply(argument)) => {
                        frames.pop();
                        focus = self.instantiate(body, argument);
                        progress = Progress::Reduced;
                    },
                    | Some(&Frame::Bind(_)) | None => break,
                },
                | Some(&Computation::Return(value)) => match frames.last() {
                    | Some(&Frame::Bind(body)) => {
                        frames.pop();
                        focus = self.instantiate(body, value);
                        progress = Progress::Reduced;
                    },
                    | Some(&Frame::Apply(_)) | None => break,
                },
                | None => return Err(unreadable()),
            }
        }
        if progress == Progress::Unchanged {
            return Ok(term);
        }
        while let Some(frame) = frames.pop() {
            focus = self.wrap(focus, frame);
        }
        Ok(Term::Computation(focus))
    }

    /// `body` with its innermost binder instantiated at `value`.
    ///
    /// # Specification
    /// trivial.
    fn instantiate(
        &mut self,
        body: ComputationId,
        value: ValueId,
    ) -> ComputationId
    {
        substitute_computation(self.arena, &mut self.table, &mut self.memo, body, value)
    }

    /// `computation` under `frame`.
    ///
    /// # Specification
    /// trivial.
    fn wrap(
        &mut self,
        computation: ComputationId,
        frame: Frame,
    ) -> ComputationId
    {
        match frame {
            | Frame::Apply(argument) => self.arena.computation_application(computation, argument),
            | Frame::Bind(body) => self.arena.computation_bind(computation, body),
        }
    }

    /// Close a goal owing `owed` at `verdict`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Ok` exactly when the two agree.
    /// - provides: every leaf's check against its owed verdict.
    /// - fails: [`ReplayRefusal::Contradicted`] when they differ.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Refused`].
    fn close(
        &self,
        owed: Expect,
        verdict: Expect,
    ) -> Result<(), Stop>
    {
        if owed == verdict {
            return Ok(());
        }
        Err(Stop::Refused(ReplayRefusal::Contradicted { at: self.at() }))
    }

    /// Charge one step.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the steps taken rise by one, saturating.
    /// - provides: the replay's single bound.
    /// - fails: [`Stop::Budget`] once the steps taken pass the budget.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Budget`].
    fn charge(&mut self) -> Result<(), Stop>
    {
        self.spent = self.spent.saturating_add(1);
        if self.spent > self.budget {
            return Err(Stop::Budget);
        }
        Ok(())
    }

    /// The next decision, unread.
    ///
    /// # Specification
    /// trivial.
    fn peek(&mut self) -> Next
    {
        match self.trace.peek() {
            | Some(&decision) => Next::Decision(decision),
            | None => Next::End,
        }
    }

    /// Read past the next decision.
    ///
    /// # Specification
    /// trivial.
    fn take(&mut self)
    {
        if self.trace.next().is_some() {
            self.position = self.position.saturating_add(1);
        }
    }

    /// The position of the next unread decision.
    ///
    /// # Specification
    /// trivial.
    const fn at(&self) -> TracePosition
    {
        TracePosition(self.position)
    }

    /// The refusal for `next` read where it does not apply.
    ///
    /// # Specification
    /// trivial.
    const fn refuse(
        &self,
        next: Next,
    ) -> Stop
    {
        match next {
            | Next::Decision(_) => Stop::Refused(ReplayRefusal::Inapplicable { at: self.at() }),
            | Next::End => Stop::Refused(ReplayRefusal::Exhausted),
        }
    }
}

/// The rule two shapes select.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`Rule::Constants`] when either head is a defined constant; else
///   [`Rule::Force`] for a thunk against a thunk or a neutral; [`Rule::Eta`]
///   for a lambda against a neutral; else [`Rule::Structural`].
/// - provides: the rule table's dispatch, in the engine's order.
/// - fails: never.
/// - panics: none.
fn rule(
    left: &Shape,
    right: &Shape,
) -> Rule
{
    let defined = |shape: &Shape| {
        matches!(
            shape,
            &Shape::Neutral(Head::Constant(_, Status::Defined), _)
        )
    };
    if defined(left) || defined(right) {
        return Rule::Constants;
    }
    match (left, right) {
        | (&Shape::Thunk(_), &(Shape::Thunk(_) | Shape::Neutral(..)))
        | (&Shape::Neutral(..), &Shape::Thunk(_)) => Rule::Force,
        | (&Shape::Lambda(_), &Shape::Neutral(..)) => Rule::Eta(ConversionSide::Right),
        | (&Shape::Neutral(..), &Shape::Lambda(_)) => Rule::Eta(ConversionSide::Left),
        | (
            &(Shape::Former
            | Shape::Thunk(_)
            | Shape::Lambda(_)
            | Shape::Return(_)
            | Shape::Neutral(..)),
            _,
        ) => Rule::Structural,
    }
}

/// The premises two spines decompose into, innermost elimination first.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a refuting leaf when the spines differ in length or in any
///   elimination's kind; else an application's or a static application's
///   arguments, a bind's continuations and a case's two branches, in spine
///   order, a force contributing none.
/// - provides: the decomposition of two neutrals over one head.
/// - fails: never.
/// - panics: none.
fn spines(
    left: &[Elimination],
    right: &[Elimination],
) -> Structure
{
    if left.len() != right.len() {
        return Structure::Leaf(Expect::NotConvertible);
    }
    let mut premises = Vec::new();
    for (&one, &other) in left.iter().zip(right) {
        match (one, other) {
            | (Elimination::Force, Elimination::Force) => {},
            | (Elimination::Apply(left_argument), Elimination::Apply(right_argument))
            | (
                Elimination::StaticApply(left_argument),
                Elimination::StaticApply(right_argument),
            ) => {
                premises.push(Premise::values(left_argument, right_argument));
            },
            | (Elimination::Bind(left_body), Elimination::Bind(right_body)) => {
                premises.push(Premise::computations(left_body, right_body));
            },
            | (
                Elimination::Case(left_on_left, left_on_right),
                Elimination::Case(right_on_left, right_on_right),
            ) => {
                premises.push(Premise::computations(left_on_left, right_on_left));
                premises.push(Premise::computations(left_on_right, right_on_right));
            },
            | (
                Elimination::Force
                | Elimination::Apply(_)
                | Elimination::Bind(_)
                | Elimination::Case(..)
                | Elimination::StaticApply(_),
                _,
            ) => return Structure::Leaf(Expect::NotConvertible),
        }
    }
    Structure::of(premises)
}

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;

    use gandr_kernel_conversion_trace::ConversionDecision;
    use gandr_kernel_conversion_trace::ConversionSide;
    use gandr_kernel_conversion_trace::SubgoalPosition;
    use gandr_kernel_strata::Level;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::Side;
    use gandr_kernel_term::TermArena;

    use super::EngineClaim;
    use super::KernelVerdict;
    use super::ParameterCount;
    use super::ReplayBudget;
    use super::ReplayDecline;
    use super::ReplayNode;
    use super::ReplayRefusal;
    use super::ReplaySides;
    use super::TracePosition;
    use super::Unfoldable;
    use super::Unfoldings;
    use super::replay;

    /// Replay `trace` for `sides` under the default budget.
    ///
    /// # Specification
    /// trivial.
    fn run(
        arena: &mut TermArena,
        unfoldings: &Unfoldings,
        sides: ReplaySides,
        claim: EngineClaim,
        trace: &[ConversionDecision<ReplayNode>],
    ) -> KernelVerdict
    {
        replay(
            arena,
            unfoldings,
            sides,
            claim,
            trace.iter().copied(),
            ReplayBudget::DEFAULT,
        )
    }

    /// The verdict a refused trace declines with.
    ///
    /// # Specification
    /// trivial.
    const fn refused(refusal: ReplayRefusal) -> KernelVerdict
    {
        KernelVerdict::Declined(ReplayDecline::Refused(refusal))
    }

    /// The decision closing a goal on two shared nodes.
    const SHARED: ConversionDecision<ReplayNode> = ConversionDecision::ComparedShared {
        left: ReplayNode::Other,
        right: ReplayNode::Other,
    };

    /// A decision forcing a thunk.
    const FORCE: ConversionDecision<ReplayNode> = ConversionDecision::Force {
        thunk: ReplayNode::Other,
    };

    #[test]
    fn a_compared_pair_closes_on_alpha_equality_or_rigid_separation()
    {
        let mut arena = TermArena::new();
        let none = Unfoldings::default();
        let unit = arena.value_unit();
        let near = arena.value_variable(DeBruijnIndex::from(0));
        let far = arena.value_variable(DeBruijnIndex::from(1));
        let left = arena.value_pair(unit, near);
        let same = arena.value_pair(unit, near);
        let apart = arena.value_pair(unit, far);
        let pairs = |right| ReplaySides::Values(left, right);

        assert_eq!(
            run(&mut arena, &none, pairs(same), EngineClaim::Convertible, &[
                SHARED
            ]),
            KernelVerdict::Convertible
        );
        assert_eq!(
            run(
                &mut arena,
                &none,
                pairs(apart),
                EngineClaim::NotConvertible,
                &[SHARED]
            ),
            KernelVerdict::NotConvertible
        );
        let after = refused(ReplayRefusal::Contradicted {
            at: TracePosition::from(1),
        });
        assert_eq!(
            run(
                &mut arena,
                &none,
                pairs(same),
                EngineClaim::NotConvertible,
                &[SHARED]
            ),
            after
        );
        assert_eq!(
            run(
                &mut arena,
                &none,
                pairs(apart),
                EngineClaim::Convertible,
                &[SHARED]
            ),
            after
        );

        // A thunk and a defined constant can still reduce, so their
        // α-distinctness separates nothing and the closing does not apply.
        let first = arena.computation_return(unit);
        let second = arena.computation_return(near);
        let thunk = arena.value_thunk(first);
        let other_thunk = arena.value_thunk(second);
        let defined = Unfoldings::new(Vec::from([Unfoldable::Body(unit)]));
        let constant = arena.value_constant(ConstantIndex::from(0_usize));
        let open = refused(ReplayRefusal::Inapplicable {
            at: TracePosition::from(0),
        });
        for sides in [
            ReplaySides::Values(thunk, other_thunk),
            ReplaySides::Values(constant, near),
        ] {
            assert_eq!(
                run(&mut arena, &defined, sides, EngineClaim::NotConvertible, &[
                    SHARED
                ]),
                open
            );
        }
    }

    #[test]
    fn the_replay_reduces_before_it_reads_a_decision()
    {
        let mut arena = TermArena::new();
        let none = Unfoldings::default();
        let unit = arena.value_unit();
        let bound = arena.value_variable(DeBruijnIndex::from(0));
        let returned_bound = arena.computation_return(bound);
        let returned_unit = arena.computation_return(unit);
        let identity = arena.computation_lambda(returned_bound);
        let applied = arena.computation_application(identity, unit);
        let sequenced = arena.computation_bind(returned_unit, returned_bound);
        let pair = arena.value_pair(unit, unit);
        let returned_pair = arena.computation_return(pair);
        let injected = arena.value_injection(Side::Right, unit);
        let cased = arena.computation_case(injected, returned_pair, returned_bound);
        let mark = arena.watermark();

        for redex in [applied, sequenced, cased] {
            let sides = ReplaySides::Computations(redex, returned_unit);
            assert_eq!(
                run(&mut arena, &none, sides, EngineClaim::Convertible, &[]),
                KernelVerdict::Convertible
            );
        }
        let refutation = [ConversionDecision::NegativeSubgoal {
            position: SubgoalPosition::from(0),
        }];
        let sides = ReplaySides::Computations(applied, returned_pair);
        assert_eq!(
            run(
                &mut arena,
                &none,
                sides,
                EngineClaim::NotConvertible,
                &refutation
            ),
            KernelVerdict::NotConvertible
        );
        assert_eq!(arena.watermark(), mark, "every reduct is truncated away");
    }

    #[test]
    fn an_unfolding_fires_only_where_the_trace_names_its_head()
    {
        let mut arena = TermArena::new();
        let unit = arena.value_unit();
        let first = ConstantIndex::from(0_usize);
        let second = ConstantIndex::from(1_usize);
        let defined = arena.value_constant(first);
        let opaque = arena.value_constant(second);
        let unfoldings = Unfoldings::new(Vec::from([Unfoldable::Body(unit)]));
        let unfold = |constant, reduce: fn(ReplayNode) -> ConversionDecision<ReplayNode>| {
            [
                ConversionDecision::Unfold {
                    constant: ReplayNode::Constant(constant),
                },
                reduce(ReplayNode::Constant(constant)),
            ]
        };
        let left = |redex| ConversionDecision::ReduceLeft { redex };
        let right = |redex| ConversionDecision::ReduceRight { redex };
        let sides = ReplaySides::Values(defined, unit);
        let at = |position| {
            refused(ReplayRefusal::Inapplicable {
                at: TracePosition::from(position),
            })
        };

        assert_eq!(
            run(
                &mut arena,
                &unfoldings,
                sides,
                EngineClaim::Convertible,
                &unfold(first, left)
            ),
            KernelVerdict::Convertible
        );
        assert_eq!(
            run(&mut arena, &unfoldings, sides, EngineClaim::Convertible, &[
            ]),
            refused(ReplayRefusal::Exhausted)
        );
        assert_eq!(
            run(
                &mut arena,
                &unfoldings,
                sides,
                EngineClaim::Convertible,
                &unfold(first, right)
            ),
            at(1)
        );
        assert_eq!(
            run(
                &mut arena,
                &unfoldings,
                sides,
                EngineClaim::Convertible,
                &unfold(second, left)
            ),
            at(1)
        );

        // Past the list a constant is opaque: compared by name, never
        // unfolded, so its leaf decides before any decision is read.
        assert_eq!(unfoldings.unfolding(second), Unfoldable::Opaque);
        let opaque_sides = ReplaySides::Values(opaque, unit);
        assert_eq!(
            run(
                &mut arena,
                &unfoldings,
                opaque_sides,
                EngineClaim::NotConvertible,
                &[]
            ),
            KernelVerdict::NotConvertible
        );
        assert_eq!(
            run(
                &mut arena,
                &unfoldings,
                opaque_sides,
                EngineClaim::Convertible,
                &unfold(second, left)
            ),
            refused(ReplayRefusal::Contradicted {
                at: TracePosition::from(0),
            })
        );
    }

    #[test]
    fn an_operator_unfolds_by_instantiating_its_parameters_in_order()
    {
        let mut arena = TermArena::new();
        let operator = ConstantIndex::from(0_usize);
        let alias = ConstantIndex::from(1_usize);
        // `F := λA. λB. ⌜El A × El B⌝` with its binders stripped: `A` is
        // index 1 and `B` index 0.
        let outer = arena.value_variable(DeBruijnIndex::from(1));
        let inner = arena.value_variable(DeBruijnIndex::from(0));
        let outer_type = arena.value_type_element(outer, Level::zero());
        let inner_type = arena.value_type_element(inner, Level::zero());
        let parameters = arena.value_type_product(outer_type, inner_type);
        let body = arena.value_quote(parameters);
        let head = arena.value_constant(operator);
        let unfoldings = Unfoldings::new(Vec::from([
            Unfoldable::Operator {
                parameters: ParameterCount::from(2),
                body,
            },
            Unfoldable::Body(head),
        ]));
        let integer = arena.value_type_base(BaseType::Integer);
        let string = arena.value_type_base(BaseType::String);
        let integer_code = arena.value_quote(integer);
        let string_code = arena.value_quote(string);
        let in_order_type = arena.value_type_product(integer, string);
        let in_order = arena.value_quote(in_order_type);
        let swapped_type = arena.value_type_product(string, integer);
        let swapped = arena.value_quote(swapped_type);
        let partial = arena.value_static_application(head, integer_code);
        let instance = arena.value_static_application(partial, string_code);
        let unfold = |constant| {
            [
                ConversionDecision::Unfold {
                    constant: ReplayNode::Constant(constant),
                },
                ConversionDecision::ReduceLeft {
                    redex: ReplayNode::Constant(constant),
                },
            ]
        };

        // The last argument meets the innermost binder.
        assert_eq!(
            run(
                &mut arena,
                &unfoldings,
                ReplaySides::Values(instance, in_order),
                EngineClaim::Convertible,
                &unfold(operator)
            ),
            KernelVerdict::Convertible
        );
        assert_eq!(
            run(
                &mut arena,
                &unfoldings,
                ReplaySides::Values(instance, swapped),
                EngineClaim::NotConvertible,
                &unfold(operator)
            ),
            KernelVerdict::NotConvertible
        );

        // An argument open in the ambient context is carried past the outer
        // parameter: `F(⌜Integer⌝, x)` is `⌜Integer × El x⌝`, where an
        // uncarried `x` would be captured as `A` and give `Integer × Integer`.
        let ambient = arena.value_variable(DeBruijnIndex::from(0));
        let open_instance = arena.value_static_application(partial, ambient);
        let ambient_type = arena.value_type_element(ambient, Level::zero());
        let open_type = arena.value_type_product(integer, ambient_type);
        let open = arena.value_quote(open_type);
        assert_eq!(
            run(
                &mut arena,
                &unfoldings,
                ReplaySides::Values(open_instance, open),
                EngineClaim::Convertible,
                &unfold(operator)
            ),
            KernelVerdict::Convertible
        );

        // A body standing at a static spine keeps the spine over it.
        let alias_head = arena.value_constant(alias);
        let alias_partial = arena.value_static_application(alias_head, integer_code);
        let alias_instance = arena.value_static_application(alias_partial, string_code);
        let mut through_alias = Vec::from(unfold(alias));
        through_alias.extend(unfold(operator));
        assert_eq!(
            run(
                &mut arena,
                &unfoldings,
                ReplaySides::Values(alias_instance, in_order),
                EngineClaim::Convertible,
                &through_alias
            ),
            KernelVerdict::Convertible
        );

        // An operator short of its arguments has no δβ-reduct.
        assert_eq!(
            run(
                &mut arena,
                &unfoldings,
                ReplaySides::Values(partial, in_order),
                EngineClaim::Convertible,
                &unfold(operator)
            ),
            refused(ReplayRefusal::Unreadable)
        );
    }

    #[test]
    fn a_refutation_follows_its_negative_subgoal()
    {
        let mut arena = TermArena::new();
        let none = Unfoldings::default();
        let unit = arena.value_unit();
        let bound = arena.value_variable(DeBruijnIndex::from(0));
        let left = arena.value_pair(unit, unit);
        let right = arena.value_pair(unit, bound);
        let sides = ReplaySides::Values(left, right);
        let negative = |position| {
            [ConversionDecision::NegativeSubgoal {
                position: SubgoalPosition::from(position),
            }]
        };

        assert_eq!(
            run(
                &mut arena,
                &none,
                sides,
                EngineClaim::NotConvertible,
                &negative(1)
            ),
            KernelVerdict::NotConvertible
        );
        assert_eq!(
            run(
                &mut arena,
                &none,
                sides,
                EngineClaim::NotConvertible,
                &negative(0)
            ),
            refused(ReplayRefusal::Contradicted {
                at: TracePosition::from(1),
            })
        );
        assert_eq!(
            run(
                &mut arena,
                &none,
                sides,
                EngineClaim::NotConvertible,
                &negative(2)
            ),
            refused(ReplayRefusal::Inapplicable {
                at: TracePosition::from(0),
            })
        );
        assert_eq!(
            run(&mut arena, &none, sides, EngineClaim::NotConvertible, &[]),
            refused(ReplayRefusal::Exhausted)
        );
        assert_eq!(
            run(&mut arena, &none, sides, EngineClaim::Convertible, &[]),
            refused(ReplayRefusal::Contradicted {
                at: TracePosition::from(0),
            })
        );
    }

    #[test]
    fn a_frozen_branch_cannot_carry_a_refutation()
    {
        let mut arena = TermArena::new();
        let unit = arena.value_unit();
        let pair = arena.value_pair(unit, unit);
        let first = ConstantIndex::from(0_usize);
        let second = ConstantIndex::from(1_usize);
        let third = ConstantIndex::from(2_usize);
        let named_first = arena.value_constant(first);
        let named_second = arena.value_constant(second);
        let named_third = arena.value_constant(third);
        let unfoldings = Unfoldings::new(Vec::from([
            Unfoldable::Body(unit),
            Unfoldable::Body(named_first),
            Unfoldable::Body(pair),
        ]));
        let node = ReplayNode::Constant;
        let unfold_second = [
            ConversionDecision::Unfold {
                constant: node(second),
            },
            ConversionDecision::ReduceLeft {
                redex: node(second),
            },
        ];
        let shortcut = ConversionDecision::ConstShortcut {
            constant: node(first),
        };
        let chain = ReplaySides::Values(named_second, named_first);

        // Convertibility through either branch: freeze the right's head and
        // unfold the left's, or postpone the right's and unfold the left's.
        for branch in [
            ConversionDecision::Freeze {
                constant: node(first),
                side: ConversionSide::Right,
            },
            ConversionDecision::Postpone {
                constant: node(first),
            },
        ] {
            let trace = [branch, unfold_second[0], unfold_second[1], shortcut];
            assert_eq!(
                run(
                    &mut arena,
                    &unfoldings,
                    chain,
                    EngineClaim::Convertible,
                    &trace
                ),
                KernelVerdict::Convertible
            );
        }

        // A refutation through a freeze or a shortcut is refused; through the
        // two unfoldings it is certified.
        let apart = ReplaySides::Values(named_first, named_third);
        let unauthorised = refused(ReplayRefusal::NonAuthoritative {
            at: TracePosition::from(0),
        });
        let frozen = ConversionDecision::Freeze {
            constant: node(first),
            side: ConversionSide::Left,
        };
        for decision in [frozen, shortcut] {
            assert_eq!(
                run(
                    &mut arena,
                    &unfoldings,
                    apart,
                    EngineClaim::NotConvertible,
                    &[decision]
                ),
                unauthorised
            );
        }
        let unfolded = [
            ConversionDecision::Unfold {
                constant: node(first),
            },
            ConversionDecision::ReduceLeft { redex: node(first) },
            ConversionDecision::Unfold {
                constant: node(third),
            },
            ConversionDecision::ReduceRight { redex: node(third) },
        ];
        assert_eq!(
            run(
                &mut arena,
                &unfoldings,
                apart,
                EngineClaim::NotConvertible,
                &unfolded
            ),
            KernelVerdict::NotConvertible
        );
    }

    #[test]
    fn eta_and_force_open_the_suspended_sides()
    {
        let mut arena = TermArena::new();
        let none = Unfoldings::default();
        let free = arena.value_variable(DeBruijnIndex::from(0));
        let free_under_binder = arena.value_variable(DeBruijnIndex::from(1));
        let bound = arena.value_variable(DeBruijnIndex::from(0));
        let forced = arena.computation_force(free_under_binder);
        let applied = arena.computation_application(forced, bound);
        let lambda = arena.computation_lambda(applied);
        let expanded = arena.value_thunk(lambda);
        let sides = ReplaySides::Values(expanded, free);
        let eta = |side| ConversionDecision::EtaExpand {
            side,
            variable: ReplayNode::Other,
        };

        assert_eq!(
            run(&mut arena, &none, sides, EngineClaim::Convertible, &[
                FORCE,
                FORCE,
                eta(ConversionSide::Right)
            ]),
            KernelVerdict::Convertible
        );
        assert_eq!(
            run(&mut arena, &none, sides, EngineClaim::Convertible, &[
                FORCE, FORCE
            ]),
            refused(ReplayRefusal::Exhausted)
        );
        assert_eq!(
            run(&mut arena, &none, sides, EngineClaim::Convertible, &[
                FORCE,
                FORCE,
                eta(ConversionSide::Left)
            ]),
            refused(ReplayRefusal::Inapplicable {
                at: TracePosition::from(2),
            })
        );
        assert_eq!(
            run(&mut arena, &none, sides, EngineClaim::Convertible, &[
                FORCE,
                eta(ConversionSide::Right)
            ]),
            refused(ReplayRefusal::Inapplicable {
                at: TracePosition::from(1),
            })
        );
    }

    #[test]
    fn the_replay_refuses_a_trace_that_does_not_replay()
    {
        let mut arena = TermArena::new();
        let unit = arena.value_unit();
        let other_unit = arena.value_unit();
        let first = ConstantIndex::from(0_usize);
        let named = arena.value_constant(first);
        let unfoldings = Unfoldings::new(Vec::from([Unfoldable::Body(unit)]));
        let units = ReplaySides::Values(unit, other_unit);
        let stray = ConversionDecision::ReduceLeft {
            redex: ReplayNode::Constant(first),
        };

        // A leaf decides silently, so a decision past it is left over.
        assert_eq!(
            run(&mut arena, &unfoldings, units, EngineClaim::Convertible, &[
                SHARED, SHARED
            ]),
            refused(ReplayRefusal::Leftover {
                at: TracePosition::from(1),
            })
        );
        assert_eq!(
            run(&mut arena, &unfoldings, units, EngineClaim::Convertible, &[
                stray
            ]),
            refused(ReplayRefusal::Leftover {
                at: TracePosition::from(0),
            })
        );

        // A reduction is read only after its unfolding, and a postponement
        // only before one.
        let defined = ReplaySides::Values(named, unit);
        assert_eq!(
            run(
                &mut arena,
                &unfoldings,
                defined,
                EngineClaim::Convertible,
                &[stray]
            ),
            refused(ReplayRefusal::Inapplicable {
                at: TracePosition::from(0),
            })
        );
        let postponed = [
            ConversionDecision::Postpone {
                constant: ReplayNode::Constant(first),
            },
            FORCE,
        ];
        assert_eq!(
            run(
                &mut arena,
                &unfoldings,
                defined,
                EngineClaim::Convertible,
                &postponed
            ),
            refused(ReplayRefusal::Inapplicable {
                at: TracePosition::from(1),
            })
        );
    }

    #[test]
    fn an_engine_decline_and_an_exhausted_budget_decline()
    {
        let mut arena = TermArena::new();
        let none = Unfoldings::default();
        let unit = arena.value_unit();
        let returned_unit = arena.computation_return(unit);

        let units = ReplaySides::Values(unit, unit);
        assert_eq!(
            run(&mut arena, &none, units, EngineClaim::Declined, &[SHARED]),
            KernelVerdict::Declined(ReplayDecline::EngineDeclined)
        );

        // Ω: a self-application that reduces to itself forever.
        let bound = arena.value_variable(DeBruijnIndex::from(0));
        let forced = arena.computation_force(bound);
        let self_applied = arena.computation_application(forced, bound);
        let lambda = arena.computation_lambda(self_applied);
        let suspended = arena.value_thunk(lambda);
        let omega = arena.computation_application(lambda, suspended);
        let mark = arena.watermark();
        let verdict = replay(
            &mut arena,
            &none,
            ReplaySides::Computations(omega, returned_unit),
            EngineClaim::Convertible,
            [],
            ReplayBudget::from(64_u64),
        );
        assert_eq!(verdict, KernelVerdict::Declined(ReplayDecline::Budget));
        assert_eq!(arena.watermark(), mark, "every reduct is truncated away");
    }
}
