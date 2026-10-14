//! **Conversion replay**: the kernel's sequential recheck of a conversion
//! engine's trace, under a three-valued verdict.
//!
//! Term conversion with δ-, β- and η-rules is proof search, and a concurrent
//! search is too large to trust. Courant and Leroy instrument their checker to
//! emit a trace of its decisions and recheck the trace sequentially
//! (Nathanaëlle Courant and Xavier Leroy, "A Lazy, Concurrent Convertibility
//! Checker", POPL 2026, §9, `doi:10.1145/3776695`). [`replay()`] is that
//! recheck: the engine's search stays outside the trusted base, and what the
//! kernel trusts is a loop that fires every step itself and reads the trace
//! only where a rule leaves a choice.
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
//! case, a lazy pairing met by a projection, an elimination met by a returned
//! endpoint, never a δ-step. Then:
//!
//! | goal | what the replay reads |
//! | --- | --- |
//! | any | `ComparedShared` closes it when the sides are α-equal, or rigid and α-distinct |
//! | a defined constant at either head | `Unfold` and the reduction naming its side, with `Postpone` before it; `Freeze`; `ConstShortcut` |
//! | a thunk against a thunk or a neutral value | two `Force`s |
//! | a lambda against a neutral computation | `EtaExpand` on the neutral side |
//! | a lazy pairing against a neutral computation | nothing for the η step: both projections of the neutral are compared with the components; under a refutation, `NegativeSubgoal` picks one |
//! | two neutrals over one head whose binds differ | `Reassociate` on a side stacking two binds, else `ReturnEta` on the side one bind short |
//! | anything else | a leaf decides it or a decomposition pushes its premises; under a refutation, `NegativeSubgoal` picks the one premise |
//!
//! The bind row comes before any decomposition of the pair, explicit or
//! implicit: a pair still owing a commuting conversion of `F` is not in the
//! form its positions compare in, so a `Decompose` there refuses, and a
//! refutation through its positions is never reached.
//!
//! A rigid term is built only of formers, variables and constants without a
//! body: nothing in it can reduce, so two α-distinct rigid terms never convert.
//!
//! A decision anchored at [`ReplayNode::Other`] names no constant, which is
//! how persisted evidence carries its dialogues: the wire keeps a decision's
//! kind and side but no identifier. Every constant decision reads its constant
//! off the shapes where an anchored one would name it. An anchor-free
//! `Unfold`, with the reduction naming its side anchor-free too, unfolds the
//! defined constant the side's head holds; a `Freeze` freezes the defined
//! head of the side it names; a `ConstShortcut` takes the head both sides
//! share, and refuses when they differ; a `Postpone` defers to the `Unfold`
//! that follows it, whose opposite side must hold a defined head. A side
//! headed by anything else refuses the decision. Each step is the one an
//! anchored decision would name, since a side has one head, so the trace
//! still chooses only whether, where and how δ fires.
//!
//! **Alternatives.** Persisting the constant's position in every decision
//! widens the evidence wire for a name the term already holds; keeping
//! `Postpone`, `Freeze` and `ConstShortcut` anchored strands every persisted
//! dialogue that compares two applications of one definition, as an
//! associativity law does. **Reversal.** A decision whose constant the shapes
//! do not determine — a rule over two heads at once that names only one —
//! takes the constant's position on the wire.
//!
//! # The lazy product's η
//!
//! A lazy pairing against a neutral computation is the η law of `C & D`
//! (Levy's computation product): the neutral is the pairing of its two
//! projections, so the goal decomposes into each projection of the neutral
//! against the matching component, left first. The two shapes force the rule
//! and nothing in it is chosen, so no decision names it and the vocabulary is
//! unchanged; a refutation names its premise by `NegativeSubgoal`, as any
//! decomposition's does. `Decompose` is refused there, as at the arrow's η, so
//! the step has one trace.
//!
//! **Alternatives.** Reading `EtaExpand` at the step would give that decision
//! a second meaning: its payload names the fresh variable the arrow's η
//! introduces, and the product's η introduces none. A decision of its own
//! would widen the vocabulary the engine and the kernel share by a step with
//! no choice in it. **Reversal.** A second rule the same two shapes admit
//! would make the step a choice, and the choice would take a decision.
//!
//! # The returned endpoint
//!
//! A returned endpoint stands for the value its pure computation returns, and
//! a pure computation returns `v` exactly when it converts with `return v`. A
//! value goal with a returned endpoint on either side is therefore read as the
//! goal between the endpoint's computation and the other side's: the other
//! endpoint's computation, or the `return` of the other value. An elimination
//! that meets a returned endpoint in weak head form runs its computation
//! first, `E[c] ⇝ c to x. E[x]`. The shapes force both steps, so no decision
//! names them and the vocabulary is unchanged.
//!
//! [`convert`] fires both steps unread and unfolds no constant: the forced loop
//! stays δ-free. A returned endpoint a mode switch's structural type comparison
//! leaves apart is read rather than compared: [`read_endpoints`] normalizes it
//! by the kernel's own evaluator, this module's weak head reduction with one
//! δ-step wherever the computation is stuck at a head naming an admitted
//! definition, and the normal forms go back through [`convert_values`], the one
//! conversion. The reading takes no trace: the reduction of one computation to
//! `return v` chooses nothing — β and the forced steps are determined, and a
//! stuck defined head admits exactly its own δ-step — so a trace could only
//! restate the term. That δ-step is the kernel's own, as readmission's
//! unfolding of a crossed definition is.
//!
//! At reflexivity the endpoint's relation to the point is replayed instead:
//! the `here` carries the engine's dialogue for each endpoint, and [`replay()`]
//! runs it with the admitted definitions unfoldable. The engine holds a
//! returned endpoint at the definition it calls, so the dialogue names each
//! δ-step, the ones under a binder that evaluation never reaches among them.
//!
//! **Alternatives.** A reading without δ would leave every endpoint over a
//! named function — `cong(f, p)` for a defined `f`, every law a model proves —
//! apart from its value. A δ rule inside [`convert`] would make the forced loop
//! choose where to unfold, which is the engine's to say. Normalising the
//! endpoint in the producer would make the producer's normaliser trusted
//! computation. **Reversal.** A mode switch whose comparison the reading cannot
//! settle by normalizing one side — two stuck neutrals equal only after
//! unfolding — carries a dialogue as reflexivity does.
//!
//! # The kernel's own conversion
//!
//! [`convert`] is the same loop with no trace: each rule the shapes force —
//! weak head reduction, the two forces, both η laws, the two bind laws, a
//! returned endpoint read as its computation, a decomposition — fires unread,
//! no constant unfolds and no refutation is certified. It is the equality a
//! judgement the kernel decides alone reads, reflexivity's endpoints first,
//! so the kernel admits what the engine's normalizer admits by the same laws
//! without asking an engine for a trace.
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
//!
//! A `ComparedShared` met at a decomposable goal closes that goal when it can
//! and otherwise passes to the first premise; the engine emits an agreeing
//! decomposition it settled equal as that one closing, so the two readings
//! coincide.
//!
//! # Codes and static operators
//!
//! The replay closes a comparison of two codes as the untrusted engine's
//! shared comparison does: α-equal codes convert, codes whose quoted types
//! hold nothing that could still unfold are apart, and any other pair is
//! refused rather than guessed at. Rigidity reads through quoted types and the
//! codes they decode, so the engine's verdict of apart is one the kernel
//! reaches in its own terms.
//!
//! A static definition's certificate unfolds one instance of an operator.
//! [`Unfoldable::Operator`] hands the replay the operator's body with its
//! [`ParameterCount`] binders stripped, the innermost binder its last
//! parameter; unfolding a value headed by it instantiates the binders at the
//! side's first arguments, innermost first, each argument shifted past the
//! parameters still standing outside it, and keeps any further applications
//! over the reduct. A body standing at a static spine keeps the spine. An
//! operator short of its arguments has no reduct and refuses as unreadable. A
//! kernel static lambda would turn this δβ into a δ-step followed by a β-rule
//! at values, owing a reduction the kernel otherwise never fires; stripping
//! the binders keeps the substitution the kernel already trusts for
//! computations as the only rewrite. When a static lambda arrives (see
//! `gandr-kernel-term`), the operator unfolding becomes a body unfolding and
//! the weak head form fires static β like the computational one.
//!
//! # Alternatives and reversal
//!
//! **Alternatives.** Running the engine's search inside the kernel would
//! certify by trusting the search. Trusting the engine's verdict would certify
//! nothing. Replaying a refuted decomposition without its negative subgoal
//! means trying every premise, which is search. Memoizing replayed
//! sub-derivations would let a trace refer back to a shared one; the engine
//! emits a derivation shared by two parents once under each, so the trace is
//! the derivation's expansion as a tree and the replay needs no table.
//!
//! **Reversal.** A back-reference decision, with a replay-side table keyed on
//! the goal it names, replaces the expansion once a measured trace of a deeply
//! shared proof outgrows the replay budget. A closing the kernel cannot
//! reproduce, because the engine's structural equality and the kernel's
//! α-equality disagree on a pair, shows up as a refusal on an engine trace and
//! moves the tie-break into the vocabulary.
//!
//! # Laws and evidence
//!
//! The unit and purity specifications, their named witnesses and the
//! goal-refinement composition shape live on [`replay()`]. [`KernelVerdict`]
//! carries the refusal class table and the certified fragment's
//! partial-equivalence scope. The `replay_laws` integration test generates 256
//! recipes, checking each claim twice and in a cloned arena, with exact
//! unit-law goldens and rollback checks.
//!
//! **Property-test dependency.** Dev-only `proptest` uses the workspace's 1.11
//! version range, defaults off and only `std` for generation, shrinking and
//! persistence. It reuses the workspace's runner without expanding the shipped
//! kernel dependencies. The `quickcheck` crate would add a second runner;
//! hand-written enumeration would lose shrinking of generated term recipes.
//! Reconsider on an unmaintained release, a high-risk advisory or a need the
//! existing strategy API cannot express.

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
use gandr_kernel_term::Exhausted;
use gandr_kernel_term::FixpointEvidence;
use gandr_kernel_term::RewriteFuel;
use gandr_kernel_term::Side;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;

use crate::conv::Convertibility;
use crate::conv::convert_values;
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

/// The definitions a replay may unfold, by admission position, and the
/// presented types whose terms it rewrites.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Unfoldings
{
    /// The unfolding of each constant, at its admission position.
    bodies: Vec<Unfoldable>,
    /// The rules of every presented type the replay's terms may hold.
    presentations: crate::presented::Presentations,
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
    /// - executable: none — provenance and closure require the replay arena,
    ///   which construction does not receive; lookup is the executable observer
    ///   of the transferred vector.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the sole surface is the position lookup, separated by
    ///   a listed constant and one past the end.
    /// - witness: `replay::tests::an_unfolding_fires_only_where_the_trace_names_its_head`
    /// - witness: `replay::tests::an_operator_unfolds_by_instantiating_its_parameters_in_order`
    #[inline]
    #[must_use]
    pub fn new(bodies: Vec<Unfoldable>) -> Self
    {
        Self {
            bodies,
            presentations: crate::presented::Presentations::default(),
        }
    }

    /// These unfoldings, the replay rewriting every presented type's terms by
    /// `presentations`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn presenting(
        self,
        presentations: crate::presented::Presentations,
    ) -> Self
    {
        Self {
            presentations,
            ..self
        }
    }

    /// The presented types the replay rewrites by.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn presentations(&self) -> &crate::presented::Presentations
    {
        &self.presentations
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
    #[spec(ensures: |ret| ret == self.bodies.get(usize::from(constant)).copied().unwrap_or(Unfoldable::Opaque))]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3: accepted, contradicted, and malformed finite traces
    ///   run with the default budget; the numerical default is not pinned.
    /// - witness: `replay::tests::a_compared_pair_closes_on_alpha_equality_or_rigid_separation`
    /// - witness: `replay::tests::the_replay_refuses_a_trace_that_does_not_replay`
    #[spec(ensures: |ret| ret.0 == Self::DEFAULT.0)]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3: zero, one, and maximum budgets preserve the admission
    ///   boundary through the public count wrapper.
    /// - witness: `replay::tests::budget_exhaustion_survives_the_counter_ceiling`
    #[spec(ensures: |ret| ret.0 == steps)]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3: zero, one, and maximum budgets preserve the admission
    ///   boundary through the public count wrapper.
    /// - witness: `replay::tests::budget_exhaustion_survives_the_counter_ceiling`
    #[spec(ensures: |ret| ret == budget.0)]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3: refusals at positions zero, one, and two retain their
    ///   exact decision index; no larger trace is claimed.
    /// - witness: `replay::tests::the_replay_refuses_a_trace_that_does_not_replay`
    /// - witness: `replay::tests::eta_and_force_open_the_suspended_sides`
    #[spec(ensures: |ret| ret.0 == position)]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3: consuming a decision at the position ceiling cannot
    ///   wrap its reported index; consuming the end leaves it unchanged.
    /// - witness: `replay::tests::trace_consumption_preserves_the_end_and_position_ceiling`
    #[spec(ensures: |ret| ret == position.0)]
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
    /// A fixpoint without termination evidence stood at its unfolding gate:
    /// conversion never unfolds a partial fixpoint, so it neither converts
    /// nor refutes.
    PartialFixpoint,
    /// The trace did not replay.
    Refused(ReplayRefusal),
}

/// The kernel's verdict on a replayed claim.
///
/// # Specification
/// - provides: two certified verdicts and a decline carrying its reason. For
///   fixed sides, unfoldings and budget, traces carrying the same claim are
///   equivalent evidence only when both replay to a certified verdict. A
///   declining trace is not equivalent to itself: this is a partial
///   equivalence, distinct from this enum's Rust equality. The unit and
///   composition laws quantify over certified verdicts only. Purity also
///   preserves declines, without making them certified evidence.
/// - executable: none — evidence equivalence needs two traces and their replay
///   context, not one stored verdict.
///
/// | Class | Verdict or reason |
/// | --- | --- |
/// | Ill-formed query | `Refused(Unreadable)` |
/// | Foreign answer | `Refused(Inapplicable { at })`, `Refused(NonAuthoritative { at })` |
/// | Path disagreement | `Refused(Contradicted { at })`, `Refused(Exhausted)`, `Refused(Leftover { at })` |
/// | No dialogue | `EngineDeclined` |
/// | Budget | `Budget` |
/// | Partial recursion | `PartialFixpoint` |
/// | Certified negative | `NotConvertible`: an element, never a refusal |
///
/// Refused reasons are [`ReplayRefusal`] variants inside
/// [`ReplayDecline::Refused`]; every decline is inside [`Self::Declined`].
///
/// # Adequacy
/// - hypothesis: L3 — a pinned table of replay inputs separates every refusal
///   variant; the unit witnesses distinguish both certified answers from
///   disagreement and budget exhaustion.
/// - witness: `replay_laws::laws::every_replay_refusal_carries_its_pinned_class`
/// - witness: `replay::tests::a_compared_pair_closes_on_alpha_equality_or_rigid_separation`
/// - witness: `replay::tests::an_engine_decline_and_an_exhausted_budget_decline`
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
/// Composition has the shape of goal refinement: decisions rewriting a goal
/// precede the rewritten goal's dialogue. A decomposed pair visits its first
/// component before its second; a leading `ComparedShared` can instead close
/// an alpha-equal pair whole. There is no certificate-composition operation,
/// and traces for `a = b` and `b = c` do not supply a trace for `a = c`.
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
/// - ensures: unit — on the budget-terminating fragment, the one-decision trace
///   `[ComparedShared]` certifies `Convertible` on alpha-equal sides and
///   `NotConvertible` on rigid alpha-distinct sides, under the matching claim.
///   Weak head reduction precedes that decision; a divergent side declines with
///   [`ReplayDecline::Budget`], even against itself.
/// - ensures: purity — the verdict depends only on the sides' content,
///   unfoldings, claim, trace and budget. Replaying twice or in a cloned arena
///   gives the same verdict and restores the entry watermark on every return.
///   No verdict adds data to the classified object.
/// - provides: the certified recheck of an untrusted engine's conversion
///   verdict, search-free and sequential.
/// - fails: never — a refusal is a verdict.
/// - panics: none.
/// - intension: each active replay uses a fresh content table and no memo
///   shared with another call; temporary reducts are discarded.
///
/// # Adequacy
/// - hypothesis: L3 — the surfaces are the rule table's rows, the refusal kinds
///   and the two decline sources, each separated by a hand-written trace that
///   takes it. The traces an engine produces are replayed end to end by that
///   engine's own tests, which sit above this crate. L2/L3 — generated rigid
///   terms, beta redexes, static unfoldings and a divergent term exercise
///   repeat/clone invariance and rollback, with independent unit-law goldens
///   preventing agreement on a constant verdict.
/// - witness: `replay::tests::a_compared_pair_closes_on_alpha_equality_or_rigid_separation`
/// - witness: `replay::tests::the_replay_reduces_before_it_reads_a_decision`
/// - witness: `replay::tests::an_unfolding_fires_only_where_the_trace_names_its_head`
/// - witness: `replay::tests::a_refutation_follows_its_negative_subgoal`
/// - witness: `replay::tests::a_frozen_branch_cannot_carry_a_refutation`
/// - witness: `replay::tests::eta_and_force_open_the_suspended_sides`
/// - witness: `replay::tests::the_replay_refuses_a_trace_that_does_not_replay`
/// - witness: `replay::tests::an_engine_decline_and_an_exhausted_budget_decline`
/// - witness: `replay_laws::laws::replay_is_pure_across_repeated_and_cloned_arenas`
/// - witness: `replay::tests::engine_decline_and_zero_budget_do_not_read_the_trace`
/// - witness: `replay::tests::reduced_heads_retain_application_and_bind_frames`
// Unit and cross-run purity are witnessed relations, not predicates over one
// result. The executable clause checks their per-call boundary: rollback and
// preservation of the claimed verdict, including the no-dialogue case.
#[spec(
    captures: before = arena.watermark(),
    ensures: |ret| arena.watermark() == before && match (claim, ret) {
        (EngineClaim::Declined, KernelVerdict::Declined(ReplayDecline::EngineDeclined)) => true,
        (EngineClaim::Declined, _) | (_, KernelVerdict::Declined(ReplayDecline::EngineDeclined)) => false,
        (EngineClaim::Convertible, KernelVerdict::Convertible)
        | (EngineClaim::NotConvertible, KernelVerdict::NotConvertible)
        | (_, KernelVerdict::Declined(ReplayDecline::Refused(_) | ReplayDecline::PartialFixpoint)) => budget.0 > 0,
        (_, KernelVerdict::Declined(ReplayDecline::Budget)) => true,
        _ => false,
    },
)]
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
    let (left, right) = terms(sides);
    let watermark = arena.watermark();
    let mut run = Replay {
        arena,
        unfoldings,
        trace: trace.into_iter().peekable(),
        reading: Reading::Recorded,
        position: 0,
        spent: 0,
        budget: u64::from(budget),
        table: ContentTable::new(),
        memo: NullMemo,
    };
    let outcome = run.drive(Goal::premise(Premise { left, right }, expect));
    run.arena.truncate_to(watermark);
    concluded(outcome, expect)
}

/// The kernel's own conversion of two terms: the replay with no trace, every
/// rule the shapes force fired unread.
///
/// The rules that fire are the ones no choice stands behind: weak head
/// reduction, a presented type's terms rewritten to normal form by
/// `presentations`, forcing two thunks, η for a lambda against a neutral, the
/// two commuting conversions of `F`, a returned endpoint taken as its
/// computation, and every structural decomposition. No constant unfolds, so a
/// constant is compared by name, and no refutation is certified: a pair this
/// cannot relate declines rather than separating.
///
/// # Specification
/// - requires: the two sides live in `arena`.
/// - ensures: [`KernelVerdict::Convertible`] exactly when the forced rules
///   derive the two sides convertible within `budget`; otherwise a
///   [`KernelVerdict::Declined`], never [`KernelVerdict::NotConvertible`].
///   `arena` holds what it held on entry.
/// - provides: the conversion a judgement the kernel decides by itself reads,
///   with no engine to supply a trace: reflexivity's endpoints first of all.
/// - fails: never — a decline is a verdict.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an η-expanded pair, a reassociated pair and a pair apart
///   in one continuation separate a conversion that fires the forced rules from
///   one that compares syntax, and from one that relates everything.
/// - witness: `replay::tests::the_kernel_converts_by_the_forced_rules_alone`
/// - witness: `element_identity::tests::reflexivity_converts_its_endpoints_by_the_laws_of_bind`
#[spec(
    captures: before = arena.watermark(),
    ensures: |ret| arena.watermark() == before && ret != KernelVerdict::NotConvertible,
)]
#[inline]
#[must_use]
pub fn convert(
    arena: &mut TermArena,
    presentations: &crate::presented::Presentations,
    sides: ReplaySides,
    budget: ReplayBudget,
) -> KernelVerdict
{
    let (left, right) = terms(sides);
    let watermark = arena.watermark();
    let none = Unfoldings::default().presenting(presentations.clone());
    let mut run = Replay {
        arena,
        unfoldings: &none,
        trace: core::iter::empty().peekable(),
        reading: Reading::Forced,
        position: 0,
        spent: 0,
        budget: u64::from(budget),
        table: ContentTable::new(),
        memo: NullMemo,
    };
    let outcome = run.drive(Goal::premise(Premise { left, right }, Expect::Convertible));
    run.arena.truncate_to(watermark);
    concluded(outcome, Expect::Convertible)
}

/// What reading a goal's returned endpoints comes to.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum EndpointReading
{
    /// Every pair converts once its returned endpoints are read.
    Converts,
    /// Some pair stays apart.
    Apart,
}

/// What `pending` comes to once its returned endpoints are normalized: each
/// side normalized as [`Replay::normalize_returned`] gives it, and the normal
/// forms converted by [`convert_values`], the kernel's one conversion.
///
/// # Specification
/// - requires: every pair's values and every body in `unfoldings` live in
///   `arena`.
/// - ensures: [`EndpointReading::Converts`] exactly when, within `budget`,
///   every pair's normal forms convert under [`convert_values`]; a
///   normalization that stops short of a value — budget, a partial fixpoint, an
///   unreadable node — leaves its pair apart, and so does a pair whose normal
///   forms do not convert. `arena` holds what it held on entry.
/// - provides: the checker's reading of a returned endpoint at a mode switch.
/// - fails: never — a normalization that stops is an apart answer.
/// - panics: none.
///
/// # Termination
/// - reason: the `for` loop over the pending pairs, not recursion.
/// - measure: the pairs left; each normalization is bounded by `budget`.
///
/// # Adequacy
/// - hypothesis: L3 — an endpoint returning its value through a definition
///   converts, a stuck endpoint converts only with an equal one, and an
///   endpoint returning a different value stays apart; the arena's watermark is
///   restored.
/// - witness: `element_identity::tests::a_returned_endpoint_reads_at_a_mode_switch`
/// - witness: `element_identity::tests::a_certificate_with_a_returned_endpoint_decodes_checks_and_replays`
#[spec(captures: before = arena.watermark(), ensures: arena.watermark() == before)]
#[must_use]
pub(crate) fn read_endpoints(
    arena: &mut TermArena,
    unfoldings: &Unfoldings,
    pending: &[(ValueId, ValueId)],
    budget: ReplayBudget,
) -> EndpointReading
{
    let watermark = arena.watermark();
    let mut run = Replay {
        arena,
        unfoldings,
        trace: core::iter::empty().peekable(),
        reading: Reading::Forced,
        position: 0,
        spent: 0,
        budget: u64::from(budget),
        table: ContentTable::new(),
        memo: NullMemo,
    };
    let mut reading = EndpointReading::Converts;
    for &(left, right) in pending {
        let (Ok(left_normal), Ok(right_normal)) =
            (run.normalize_returned(left), run.normalize_returned(right))
        else {
            reading = EndpointReading::Apart;
            break;
        };
        if convert_values(
            run.arena,
            run.unfoldings.presentations(),
            left_normal,
            right_normal,
        ) != Convertibility::Convertible
        {
            reading = EndpointReading::Apart;
            break;
        }
    }
    run.arena.truncate_to(watermark);
    reading
}

/// The two sides as goal terms.
///
/// # Specification
/// trivial.
const fn terms(sides: ReplaySides) -> (Term, Term)
{
    match sides {
        | ReplaySides::Values(left, right) => (Term::Value(left), Term::Value(right)),
        | ReplaySides::Computations(left, right) => {
            (Term::Computation(left), Term::Computation(right))
        },
    }
}

/// The verdict a finished run owes `expect`.
///
/// # Specification
/// trivial.
const fn concluded(
    outcome: Result<(), Stop>,
    expect: Expect,
) -> KernelVerdict
{
    match outcome {
        | Ok(()) => match expect {
            | Expect::Convertible => KernelVerdict::Convertible,
            | Expect::NotConvertible => KernelVerdict::NotConvertible,
        },
        | Err(Stop::Budget) => KernelVerdict::Declined(ReplayDecline::Budget),
        | Err(Stop::PartialFixpoint) => KernelVerdict::Declined(ReplayDecline::PartialFixpoint),
        | Err(Stop::Refused(refusal)) => KernelVerdict::Declined(ReplayDecline::Refused(refusal)),
    }
}

/// Why a replay stopped short of a certified verdict.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Stop
{
    /// The step budget ran out.
    Budget,
    /// A partial fixpoint stood at its unfolding gate.
    PartialFixpoint,
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
    ///
    /// # Adequacy
    /// - hypothesis: L3: a defined head is frozen only on the selected side,
    ///   while an opaque head stays opaque on both sides.
    /// - witness: `replay::tests::frozen_heads_are_side_local_and_opacity_takes_precedence`
    #[spec(ensures: |ret| {
        let selected = match side {
            ConversionSide::Left => &self.left,
            ConversionSide::Right => &self.right,
        };
        ret.len() == selected.len() && core::ptr::eq(ret.as_ptr(), selected.as_ptr())
    })]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3: freezing either side changes only that side of a
    ///   defined head; freezing an opaque head cannot make it unfoldable. A
    ///   freeze appends, so the predicate reads the side's length and its last
    ///   constant rather than searching it.
    /// - witness: `replay::tests::frozen_heads_are_side_local_and_opacity_takes_precedence`
    #[spec(
        captures: [own_count = self.side(side).len(), other_count = self.side(opposite(side)).len()],
        ensures: self.side(side).len() == own_count.saturating_add(1)
            && self.side(side).last() == Some(&constant)
            && self.side(opposite(side)).len() == other_count,
    )]
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
    /// Nominal elimination; the arena node retains its motive and branches.
    DataCase(ComputationId),
    /// Dependent split; the arena node retains its motive and body. Only the
    /// body is compared: the motive is a typing annotation that no reduction
    /// reads.
    SigmaSplit(ComputationId),
    /// Record projection; the arena node retains its exact label.
    RecordProjection(ComputationId),
    /// Tuple projection; the arena node retains its component.
    TupleProjection(ComputationId),
    /// Lazy product projection of this side.
    Project(Side),
    /// Transport under a neutral path head, retaining its operand.
    Transport(ValueId),
    /// Product transport waiting for a neutral pair operand.
    ProductTransport(ValueId),
    /// A ride along a neutral flow head; the arena node retains its motive
    /// and its value.
    Ride(ComputationId),
    /// The head forced.
    Force,
    /// An application to this argument.
    Apply(ValueId),
    /// A bind into this continuation.
    Bind(ComputationId),
    /// A sum case; the arena node retains its branches, none for the empty
    /// sum's elimination.
    Case(ComputationId),
    /// A native List fold's branches; checked element and result annotations
    /// erase.
    ListFold(ComputationId, ComputationId),
    /// A static application to this code: the one value elimination.
    StaticApply(ValueId),
    /// A fixpoint applied to the neutral head; the arena node is the
    /// fixpoint itself, compared as a computation.
    Fixpoint(ComputationId),
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
    /// A lazy pairing of these two components.
    With(ComputationId, ComputationId),
    /// A fixpoint over this body, standing at no gate.
    Fixpoint(ComputationId),
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
    /// A lazy pairing meets a neutral computation on this side: the neutral
    /// is projected on both sides and each projection compared with the
    /// pairing's component.
    ProductEta(ConversionSide),
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
    ///
    /// # Adequacy
    /// - hypothesis: L3: empty neutral spines close positively, while ordered
    ///   case and application premises admit only the selected refuting
    ///   subgoal.
    /// - witness: `replay::tests::neutral_spines_keep_subgoal_order_and_reject_kind_mismatches`
    #[spec(
        captures: count = premises.len(),
        ensures: |ret| match ret {
            Self::Leaf(Expect::Convertible) => count == 0,
            Self::Premises(ref children) => count > 0 && children.len() == count,
            Self::Leaf(Expect::NotConvertible) => false,
        },
    )]
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
    /// An anchor-free postponement: the unfolding that follows names its
    /// side, and the other side's head, whichever defined constant it holds,
    /// is the one postponed.
    Opposite,
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
    /// A projection of this side of a lazy pairing.
    Project(Side),
}

/// Where a goal's forced one-sided rewrites are read from.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Reading
{
    /// The trace names each one, and a missing or different name refuses.
    Recorded,
    /// Each fires where the shapes force it, reading nothing: the kernel's own
    /// conversion, which has no trace.
    Forced,
}

/// A one-sided rewrite the shapes force, as the trace names it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Forced
{
    /// One side of a thunk goal forced.
    Force,
    /// The neutral side of a lambda goal applied to a fresh variable.
    Eta(ConversionSide),
    /// The side read as its bind into `return`.
    ReturnEta(ConversionSide),
    /// The two binds nearest the side's head made one.
    Reassociate(ConversionSide),
}

/// Which commuting conversion of `F` two neutral shapes over one head still
/// owe before their spines decompose.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum BindRule
{
    /// Neither spine stacks two binds in a row, and neither stops one bind
    /// short of the other: the spines compare position by position.
    Normal,
    /// The side whose spine stacks two binds in a row, the left first.
    Reassociate(ConversionSide),
    /// The side whose spine stops one bind short of the other's.
    ReturnEta(ConversionSide),
}

/// What stands at a fixpoint's unfolding gate.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Gate
{
    /// An application to a constructor: the `<` direction at data.
    Constructor,
    /// An application to another canonical value.
    Canonical,
    /// A bind or a projection observing the fixpoint's result: the `>`
    /// direction.
    Observed,
    /// No elimination, or an application to a neutral value.
    Shut,
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
    /// Whether forced rewrites are read off the trace or fired unread.
    reading: Reading,
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
    ///
    /// # Adequacy
    /// - hypothesis: L3: accepted finite traces, leftover decisions,
    ///   contradictory claims, and a diverging term separate the driver
    ///   outcomes; the bound is the charged steps, not elapsed time.
    /// - witness: `replay::tests::a_compared_pair_closes_on_alpha_equality_or_rigid_separation`
    /// - witness: `replay::tests::the_replay_refuses_a_trace_that_does_not_replay`
    /// - witness: `replay::tests::an_engine_decline_and_an_exhausted_budget_decline`
    #[spec(ensures: |ret| match ret {
        Ok(()) => self.trace.size_hint() == (0, Some(0)),
        Err(Stop::Refused(ReplayRefusal::Leftover { at })) => at.0 == self.position && self.trace.size_hint().0 > 0,
        Err(Stop::Budget) => self.spent >= self.budget,
        Err(Stop::Refused(_) | Stop::PartialFixpoint) => true,
    })]
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
    ///   premises its derivation owes. A value goal with a returned endpoint on
    ///   either side is first read as the goal between computations
    ///   ([`Self::open_returned`]), a forced step no decision records.
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
    ///
    /// # Adequacy
    /// - hypothesis: L3: shared comparison, force, eta, and positive or
    ///   negative decomposition preserve the owed verdict of every scheduled
    ///   premise; finite traces and the budget witness do not establish
    ///   completeness of conversion.
    /// - witness: `replay::tests::a_compared_pair_closes_on_alpha_equality_or_rigid_separation`
    /// - witness: `replay::tests::a_refutation_follows_its_negative_subgoal`
    /// - witness: `replay::tests::eta_and_force_open_the_suspended_sides`
    /// - witness: `replay::tests::an_engine_decline_and_an_exhausted_budget_decline`
    /// - witness: `replay::tests::the_replay_refuses_a_trace_that_does_not_replay`
    #[spec(
        captures: before = (self.spent, goals.len(), goal.expect),
        ensures: |ret| {
            let (spent, previous_goals, owed) = before;
            self.spent >= spent
                && (!matches!(ret, Err(Stop::Budget)) || self.spent >= self.budget)
                && (ret.is_err() || (self.spent > spent && self.spent <= self.budget
                    && goals.get(previous_goals..).is_some_and(|pending| pending.iter().all(|next| next.expect == owed))))
        },
    )]
    fn settle(
        &mut self,
        mut goal: Goal,
        goals: &mut Vec<Goal>,
    ) -> Result<(), Stop>
    {
        let mut postponed = Postponed::Nothing;
        loop {
            self.charge()?;
            self.open_returned(&mut goal);
            let left = self.whnf(goal.left)?;
            let right = self.whnf(goal.right)?;
            goal.left = self.present(left)?;
            goal.right = self.present(right)?;
            let left_shape = self.shape(goal.left, &goal.frozen, ConversionSide::Left)?;
            let right_shape = self.shape(goal.right, &goal.frozen, ConversionSide::Right)?;
            let next = self.peek();
            if postponed != Postponed::Nothing
                && !matches!(next, Next::Decision(ConversionDecision::Unfold { .. }))
            {
                return Err(self.refuse(next));
            }
            let bind = bind_rule(&left_shape, &right_shape);
            if matches!(next, Next::Decision(ConversionDecision::Decompose)) {
                if !matches!(rule(&left_shape, &right_shape), Rule::Structural)
                    || bind != BindRule::Normal
                {
                    return Err(self.refuse(next));
                }
                return self.structural(&goal, &left_shape, &right_shape, goals);
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
            match bind {
                | BindRule::Normal => {},
                | BindRule::Reassociate(side) => {
                    let held = match side {
                        | ConversionSide::Left => &left_shape,
                        | ConversionSide::Right => &right_shape,
                    };
                    let Shape::Neutral(_, ref spine) = *held
                    else {
                        return Err(unreadable());
                    };
                    self.reassociate(&mut goal, side, spine)?;
                    continue;
                },
                | BindRule::ReturnEta(side) => {
                    self.return_eta(&mut goal, side)?;
                    continue;
                },
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
                | Rule::ProductEta(side) => return self.product_eta(&goal, side, goals),
                | Rule::Structural => {
                    return self.structural(&goal, &left_shape, &right_shape, goals);
                },
            }
        }
    }

    /// Read a value goal with a returned endpoint on either side as the goal
    /// between computations: a returned endpoint by its computation, any
    /// other value by its `return`.
    ///
    /// A pure computation returns `v` exactly when it converts with
    /// `return v`, so the rewritten goal owes the verdict the value goal owed,
    /// and no rule leaves a choice: the step is forced, and no decision of the
    /// trace vocabulary records it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a goal between two values, one of them a returned endpoint,
    ///   becomes the goal between two computations, each side its returned
    ///   endpoint's computation or the `return` of its value; every other goal
    ///   is unchanged, and so is the owed verdict.
    /// - provides: the replay's reading of the returned endpoint.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a returned endpoint against its value, against
    ///   another returned endpoint and against a different value separate the
    ///   two rewrites from an untouched goal.
    /// - witness: `element_identity::tests::a_returned_endpoint_replays_as_its_computation`
    #[spec(
        captures: before = (goal.left, goal.right, goal.expect),
        ensures: goal.expect == before.2 && match before {
            (Term::Value(left), Term::Value(right), _)
                if matches!(self.arena.value(left), Some(&Value::Returned(_)))
                    || matches!(self.arena.value(right), Some(&Value::Returned(_))) =>
                matches!((goal.left, goal.right), (Term::Computation(_), Term::Computation(_))),
            _ => goal.left == before.0 && goal.right == before.1,
        },
    )]
    fn open_returned(
        &mut self,
        goal: &mut Goal,
    )
    {
        let (Term::Value(left), Term::Value(right)) = (goal.left, goal.right)
        else {
            return;
        };
        let returned = |arena: &TermArena, value| match arena.value(value) {
            | Some(&Value::Returned(computation)) => Some(computation),
            | _ => None,
        };
        if returned(self.arena, left).is_none() && returned(self.arena, right).is_none() {
            return;
        }
        for (side, value) in [(ConversionSide::Left, left), (ConversionSide::Right, right)] {
            let computation = match returned(self.arena, value) {
                | Some(computation) => computation,
                | None => self.arena.computation_return(value),
            };
            goal.set(side, Term::Computation(computation));
        }
    }

    /// A value headed by a constructor of a presented type, rewritten to its
    /// normal form; every other term unchanged.
    ///
    /// The rules are the type's definition, applied by one fixed strategy, so
    /// the step chooses nothing and no decision of the trace records it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`crate::presented::normal_form`] of a value under the
    ///   unfoldings' presentations, a computation unchanged; every node the
    ///   rewriting compared or copied charged to the budget.
    /// - provides: the presented half of weak head form, before any rule of the
    ///   table reads a value goal.
    /// - fails: [`Stop::Budget`] when the rewriting outruns the budget.
    /// - panics: none.
    ///
    /// # Errors
    /// As `- fails:`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the circle's words convert by their normal forms in
    ///   the forced loop, which compares a free type's constructors as before.
    /// - witness: `presented::tests::the_forced_loop_converts_circle_words_by_their_normal_forms`
    #[spec(
        captures: before = self.spent,
        ensures: |ret| self.spent >= before
            && (!matches!(term, Term::Computation(_)) || ret == Ok(term))
            && (!matches!(ret, Err(Stop::Budget)) || self.spent >= self.budget),
    )]
    fn present(
        &mut self,
        term: Term,
    ) -> Result<Term, Stop>
    {
        let Term::Value(value) = term
        else {
            return Ok(term);
        };
        let mut fuel = RewriteFuel::from(self.budget.saturating_sub(self.spent));
        let before = u64::from(fuel);
        let normal = crate::presented::normal_form(
            self.arena,
            self.unfoldings.presentations(),
            value,
            &mut fuel,
        );
        self.spent = self
            .spent
            .saturating_add(before.saturating_sub(u64::from(fuel)));
        match normal {
            | Ok(normal) => Ok(Term::Value(normal)),
            | Err(Exhausted) => {
                self.spent = self.budget;
                Err(Stop::Budget)
            },
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
    ///   with agreeing spines pushes the spines' premises into `goals`. An
    ///   anchor-free decision names the constant the shapes hold where an
    ///   anchored one would name it: the unfolded or frozen side's head, the
    ///   head the two shortcut sides share, and for a `Postpone` the head
    ///   opposite the unfolding that follows.
    /// - provides: the replay of every two-sided constant rule.
    /// - fails: a refusal when the decision does not apply, or would refute
    ///   through a freeze or a shortcut.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Refused`].
    ///
    /// # Adequacy
    /// - hypothesis: L3: named-head unfolding and postponed-head traces
    ///   distinguish side and name mismatches; freeze and shortcut traces
    ///   reject negative authority before consumption; anchor-free freeze,
    ///   postponement and shortcut replay the anchored chain and refuse a side
    ///   with no defined head or two heads that differ. These fixtures bound
    ///   dispatch, not every possible spine.
    /// - witness: `replay::tests::an_unfolding_fires_only_where_the_trace_names_its_head`
    /// - witness: `replay::tests::a_frozen_branch_cannot_carry_a_refutation`
    /// - witness: `replay::tests::anchor_free_constant_decisions_read_their_constant_off_the_shapes`
    #[spec(
        requires: shapes.iter().any(|shape| matches!(shape, &&Shape::Neutral(Head::Constant(_, Status::Defined), _))),
        captures: before = (self.position, goals.len()),
        ensures: |ret| self.position >= before.0 && self.position <= before.0.saturating_add(2)
            && match ret {
                Ok(Flow::Settled) => goal.expect == Expect::Convertible
                    && self.position == before.0.saturating_add(1)
                    && goals.get(before.1..).is_some_and(|pending| pending.iter().all(|next| next.expect == Expect::Convertible)),
                Ok(Flow::Continue) => self.position > before.0
                    && (self.position != before.0.saturating_add(2) || *postponed == Postponed::Nothing),
                Err(Stop::Refused(ReplayRefusal::NonAuthoritative { at })) =>
                    goal.expect == Expect::NotConvertible && at.0 == before.0 && self.position == before.0,
                Err(_) => true,
            },
    )]
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
            | ConversionDecision::Unfold { constant } => {
                self.take();
                let reduction = self.peek();
                let side = match reduction {
                    | Next::Decision(ConversionDecision::ReduceLeft { redex })
                        if redex == constant =>
                    {
                        ConversionSide::Left
                    },
                    | Next::Decision(ConversionDecision::ReduceRight { redex })
                        if redex == constant =>
                    {
                        ConversionSide::Right
                    },
                    | Next::Decision(_) | Next::End => return Err(self.refuse(reduction)),
                };
                // An anchor-free decision, as persisted evidence carries it,
                // names no constant: it unfolds the one the side's head holds.
                let name = match (constant, shape_of(side)) {
                    | (ReplayNode::Constant(name), _)
                    | (
                        ReplayNode::Other,
                        &Shape::Neutral(Head::Constant(name, Status::Defined), _),
                    ) => name,
                    | (ReplayNode::Other, _) => return Err(self.refuse(reduction)),
                };
                let unfolds = matches!(shape_of(side), &Shape::Neutral(Head::Constant(head, Status::Defined), _) if head == name);
                let waits = match *postponed {
                    | Postponed::Nothing => true,
                    | Postponed::Constant(other) => matches!(
                        shape_of(opposite(side)),
                        &Shape::Neutral(Head::Constant(head, Status::Defined), _) if head == other
                    ),
                    | Postponed::Opposite => matches!(
                        shape_of(opposite(side)),
                        &Shape::Neutral(Head::Constant(_, Status::Defined), _)
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
            | ConversionDecision::Postpone { constant } if *postponed == Postponed::Nothing => {
                self.take();
                *postponed = match constant {
                    | ReplayNode::Constant(name) => Postponed::Constant(name),
                    | ReplayNode::Other => Postponed::Opposite,
                };
                Ok(Flow::Continue)
            },
            | ConversionDecision::Freeze { constant, side } => {
                if goal.expect == Expect::NotConvertible {
                    return Err(Stop::Refused(ReplayRefusal::NonAuthoritative {
                        at: self.at(),
                    }));
                }
                let &Shape::Neutral(Head::Constant(head, Status::Defined), _) = shape_of(side)
                else {
                    return Err(self.refuse(next));
                };
                if matches!(constant, ReplayNode::Constant(name) if name != head) {
                    return Err(self.refuse(next));
                }
                self.take();
                goal.frozen.freeze(side, head);
                Ok(Flow::Continue)
            },
            | ConversionDecision::ConstShortcut { constant } => {
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
                let named = match constant {
                    | ReplayNode::Constant(name) => name == left_head,
                    | ReplayNode::Other => true,
                };
                if !named || left_head != right_head {
                    return Err(self.refuse(next));
                }
                self.take();
                let premises = match spines(self.arena, left_spine, right_spine)? {
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
            | ConversionDecision::Postpone { .. }
            | ConversionDecision::EtaExpand { .. }
            | ConversionDecision::ReturnEta { .. }
            | ConversionDecision::Reassociate { .. }
            | ConversionDecision::Force { .. }
            | ConversionDecision::ComparedShared { .. }
            | ConversionDecision::Decompose
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
    ///
    /// # Adequacy
    /// - hypothesis: L3: a thunk against a neutral consumes two force decisions
    ///   before eta; a wrong second decision refuses at its position without
    ///   replacing either side.
    /// - witness: `replay::tests::eta_and_force_open_the_suspended_sides`
    #[spec(
        captures: before = (self.position, goal.left, goal.right),
        ensures: |ret| if ret.is_ok() {
            let agrees = |source, result| match (source, result) {
                (Term::Value(value), Term::Computation(computation)) => match self.arena.value(value) {
                    Some(&Value::Thunk(body)) => computation == body,
                    Some(&(Value::Variable(_) | Value::Constant(_))) => self.arena.computation(computation) == Some(&Computation::Force(value)),
                    _ => false,
                },
                _ => false,
            };
            self.position == before.0.saturating_add(match self.reading { Reading::Recorded => 2, Reading::Forced => 0 })
                && agrees(before.1, goal.left) && agrees(before.2, goal.right)
        } else {
            goal.left == before.1 && goal.right == before.2
                && self.position >= before.0 && self.position <= before.0.saturating_add(2)
        },
    )]
    fn force(
        &mut self,
        goal: &mut Goal,
    ) -> Result<(), Stop>
    {
        for _ in [ConversionSide::Left, ConversionSide::Right] {
            self.read(Forced::Force)?;
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
    ///
    /// # Adequacy
    /// - hypothesis: L3: replaying a suspended lambda against a free variable
    ///   distinguishes opening a thunk from allocating a neutral force; other
    ///   root classes are bounded by the executable local match.
    /// - witness: `replay::tests::eta_and_force_open_the_suspended_sides`
    /// - witness: `path_universe::tests::no_k`
    #[spec(ensures: |ret| match term {
        Term::Value(value) => match self.arena.value(value) {
            Some(&Value::Thunk(body)) => ret == Ok(Term::Computation(body)),
            Some(&(Value::Variable(_) | Value::Constant(_))) => matches!(ret, Ok(Term::Computation(computation)) if self.arena.computation(computation) == Some(&Computation::Force(value))),
            _ => ret == Err(unreadable()),
        },
        Term::Computation(_) => ret == Err(unreadable()),
    })]
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
                &(Value::PathRefl(_)
                | Value::Constructor { .. }
                | Value::Record(_)
                | Value::PathProduct(..)
                | Value::SessionPath { .. }
                | Value::SessionFlow { .. }
                | Value::PathEquiv { .. }
                | Value::Here { .. }
                | Value::Stay { .. }
                | Value::ForwardFlow { .. }
                | Value::FunctionFlow { .. }
                | Value::Then { .. }
                | Value::FlowProduct(..)
                | Value::Higher { .. }
                | Value::HigherEvaluation { .. }
                | Value::QuantifiedEvaluation { .. }
                | Value::Literal(_)
                | Value::Tuple(..)
                | Value::ListNil
                | Value::ListCons(..)
                | Value::Injection(..)
                | Value::Lift { .. }
                | Value::Quote(_)
                | Value::QuoteComputation(_)
                | Value::StaticApplication(..)
                | Value::Returned(_)),
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
    ///
    /// # Adequacy
    /// - hypothesis: L3: eta on the neutral side opens the opposite lambda and
    ///   introduces variable zero; a missing or wrong-side decision refuses
    ///   after the same force prefix. The witness does not cover arbitrary open
    ///   binder depths.
    /// - witness: `replay::tests::eta_and_force_open_the_suspended_sides`
    #[spec(
        captures: before = (self.position, goal.side(side), goal.side(opposite(side))),
        ensures: |ret| if ret.is_ok() {
            self.position == before.0.saturating_add(match self.reading { Reading::Recorded => 1, Reading::Forced => 0 })
                && match (before.2, goal.side(opposite(side)), goal.side(side)) {
                    (Term::Computation(lambda), Term::Computation(body), Term::Computation(applied)) =>
                        self.arena.computation(lambda) == Some(&Computation::Lambda(body))
                        && matches!(self.arena.computation(applied), Some(&Computation::Application(_, variable))
                            if self.arena.value(variable) == Some(&Value::Variable(DeBruijnIndex::from(0)))),
                    _ => false,
                }
        } else {
            self.position == before.0 && goal.side(side) == before.1 && goal.side(opposite(side)) == before.2
        },
    )]
    fn eta(
        &mut self,
        goal: &mut Goal,
        side: ConversionSide,
    ) -> Result<(), Stop>
    {
        let (Term::Computation(neutral), Term::Computation(lambda)) =
            (goal.side(side), goal.side(opposite(side)))
        else {
            return Err(unreadable());
        };
        let Some(&Computation::Lambda(body)) = self.arena.computation(lambda)
        else {
            return Err(unreadable());
        };
        self.read(Forced::Eta(side))?;
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

    /// Decompose a lazy pairing goal by projecting its neutral `side` on both
    /// sides of the lazy product.
    ///
    /// # Specification
    /// - requires: `side` is a neutral computation and the other side a lazy
    ///   pairing.
    /// - ensures: the premises are the neutral's left projection against the
    ///   pairing's left component, then its right projection against the right
    ///   component, each kept on the goal's own sides, scheduled as
    ///   [`Self::schedule`] states. No decision names the η step: the two
    ///   shapes force it and nothing about it is chosen.
    /// - provides: the replay of the lazy product's η rule, `M = ⟨π₁ M, π₂ M⟩`.
    /// - fails: [`ReplayRefusal::Unreadable`] when the sides are not a
    ///   computation and a lazy pairing; a refusal when a refutation's next
    ///   decision is not a `NegativeSubgoal` naming one of the two premises.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Refused`].
    ///
    /// # Adequacy
    /// - hypothesis: L3: the pairing of a variable's two projections converts
    ///   with that variable on either side with an empty trace; a pairing whose
    ///   right component differs refutes through `NegativeSubgoal` at position
    ///   one and not at position zero; an `EtaExpand` there is never read and
    ///   is left over, and a `Decompose` there is inapplicable.
    /// - witness: `replay::tests::a_lazy_pairing_meets_a_neutral_by_its_projections`
    #[spec(
        captures: before = goals.len(),
        ensures: |ret| match ret {
            Ok(()) => goals.get(before..).is_some_and(|pending| {
                pending.len() == match goal.expect { Expect::Convertible => 2_usize, Expect::NotConvertible => 1_usize }
                    && pending.iter().all(|next| next.expect == goal.expect && matches!(next.side(side), Term::Computation(projected)
                        if matches!(self.arena.computation(projected), Some(&Computation::Project(_, neutral)) if goal.side(side) == Term::Computation(neutral))))
            }),
            Err(_) => goals.len() == before,
        },
    )]
    fn product_eta(
        &mut self,
        goal: &Goal,
        side: ConversionSide,
        goals: &mut Vec<Goal>,
    ) -> Result<(), Stop>
    {
        let (Term::Computation(neutral), Term::Computation(pairing)) =
            (goal.side(side), goal.side(opposite(side)))
        else {
            return Err(unreadable());
        };
        let Some(&Computation::With(first, second)) = self.arena.computation(pairing)
        else {
            return Err(unreadable());
        };
        let first_projection = self.arena.computation_project(Side::Left, neutral);
        let second_projection = self.arena.computation_project(Side::Right, neutral);
        let premises = match side {
            | ConversionSide::Left => Vec::from([
                Premise::computations(first_projection, first),
                Premise::computations(second_projection, second),
            ]),
            | ConversionSide::Right => Vec::from([
                Premise::computations(first, first_projection),
                Premise::computations(second, second_projection),
            ]),
        };
        self.schedule(goal.expect, premises, goals)
    }

    /// Read the decision naming `wanted` off the trace, or fire it unread.
    ///
    /// # Specification
    /// - requires: the shapes force `wanted` at the current goal.
    /// - ensures: under [`Reading::Recorded`], `Ok` after consuming exactly one
    ///   decision when the next one names `wanted`, side and all; under
    ///   [`Reading::Forced`], `Ok` without reading.
    /// - provides: the one place a forced rewrite meets the trace.
    /// - fails: a refusal when the trace names anything else or has ended.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Refused`].
    ///
    /// # Adequacy
    /// - hypothesis: L3: a missing or wrong-side decision refuses where the
    ///   recorded replay reads it, and the forced conversion relates the same
    ///   pair with no trace at all.
    /// - witness: `replay::tests::eta_and_force_open_the_suspended_sides`
    /// - witness: `replay::tests::the_laws_of_bind_replay_by_name`
    /// - witness: `replay::tests::the_kernel_converts_by_the_forced_rules_alone`
    #[spec(
        captures: before = self.position,
        ensures: |ret| match (self.reading, ret) {
            (Reading::Forced, Ok(())) | (Reading::Recorded, Err(_)) => self.position == before,
            (Reading::Recorded, Ok(())) => self.position == before.saturating_add(1),
            (Reading::Forced, Err(_)) => false,
        },
    )]
    fn read(
        &mut self,
        wanted: Forced,
    ) -> Result<(), Stop>
    {
        if self.reading == Reading::Forced {
            return Ok(());
        }
        let next = self.peek();
        let named = match (wanted, next) {
            | (Forced::Force, Next::Decision(ConversionDecision::Force { .. })) => true,
            | (
                Forced::Eta(side),
                Next::Decision(ConversionDecision::EtaExpand { side: named, .. }),
            )
            | (
                Forced::ReturnEta(side),
                Next::Decision(ConversionDecision::ReturnEta { side: named }),
            )
            | (
                Forced::Reassociate(side),
                Next::Decision(ConversionDecision::Reassociate { side: named }),
            ) => named == side,
            | (
                Forced::Force | Forced::Eta(_) | Forced::ReturnEta(_) | Forced::Reassociate(_),
                Next::Decision(_) | Next::End,
            ) => false,
        };
        if !named {
            return Err(self.refuse(next));
        }
        self.take();
        Ok(())
    }

    /// Read the computation on `side` as its bind into `return`.
    ///
    /// # Specification
    /// - requires: [`bind_rule`] answered [`BindRule::ReturnEta`] naming
    ///   `side`.
    /// - ensures: `side` becomes `M to x. return x` over the `M` it held, the
    ///   other side unchanged.
    /// - provides: the replay of the η-rule of `F`.
    /// - fails: a refusal unless the trace names `ReturnEta` on `side`, or when
    ///   the side is not a computation.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Refused`].
    ///
    /// # Adequacy
    /// - hypothesis: L3: a neutral against its own bind into `return` converts
    ///   only through this rewrite, and the same trace naming the other side
    ///   refuses.
    /// - witness: `replay::tests::the_laws_of_bind_replay_by_name`
    #[spec(
        captures: before = (goal.side(side), goal.side(opposite(side))),
        ensures: |ret| goal.side(opposite(side)) == before.1 && if ret.is_ok() {
            matches!((before.0, goal.side(side)), (Term::Computation(held), Term::Computation(expanded))
                if matches!(self.arena.computation(expanded), Some(&Computation::Bind(bound, returned))
                    if bound == held && matches!(self.arena.computation(returned), Some(&Computation::Return(variable))
                        if self.arena.value(variable) == Some(&Value::Variable(DeBruijnIndex::from(0))))))
        } else {
            goal.side(side) == before.0
        },
    )]
    fn return_eta(
        &mut self,
        goal: &mut Goal,
        side: ConversionSide,
    ) -> Result<(), Stop>
    {
        let Term::Computation(held) = goal.side(side)
        else {
            return Err(unreadable());
        };
        self.read(Forced::ReturnEta(side))?;
        let variable = self.arena.value_variable(DeBruijnIndex::from(0));
        let returned = self.arena.computation_return(variable);
        let expanded = self.arena.computation_bind(held, returned);
        goal.set(side, Term::Computation(expanded));
        Ok(())
    }

    /// Make the two binds nearest the head of `side` one.
    ///
    /// # Specification
    /// - requires: [`bind_rule`] answered [`BindRule::Reassociate`] naming
    ///   `side`, and `spine` is that side's spine.
    /// - ensures: the node `(M to x. N) to y. P` that holds the pair becomes `M
    ///   to x. (N to y. P')`, with `P'` the continuation shifted past the new
    ///   binder, and every application, bind and projection above it is rebuilt
    ///   unchanged; the other side is unchanged.
    /// - provides: the replay of bind associativity.
    /// - fails: a refusal unless the trace names `Reassociate` on `side`, or
    ///   when the side's term does not hold the pair the spine says it does.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Refused`].
    ///
    /// # Termination
    /// - reason: the `for` loops below walk a bounded count of frames, not
    ///   recursion.
    /// - measure: the frames between the root and the pair, fewer than the
    ///   spine's length.
    ///
    /// # Adequacy
    /// - hypothesis: L3: a left-nested pair of binds under an application
    ///   converts to its right-nested twin only through this rewrite, and a
    ///   continuation reading the outer binder separates a shift from none.
    /// - witness: `replay::tests::the_laws_of_bind_replay_by_name`
    #[spec(
        captures: before = (goal.side(side), goal.side(opposite(side))),
        ensures: |ret| goal.side(opposite(side)) == before.1
            && (ret.is_ok() || goal.side(side) == before.0),
    )]
    fn reassociate(
        &mut self,
        goal: &mut Goal,
        side: ConversionSide,
        spine: &[Elimination],
    ) -> Result<(), Stop>
    {
        let Term::Computation(root) = goal.side(side)
        else {
            return Err(unreadable());
        };
        let pair = spine
            .windows(2)
            .position(|pair| matches!(pair, &[Elimination::Bind(_), Elimination::Bind(_)]))
            .ok_or_else(unreadable)?;
        let above = spine
            .len()
            .checked_sub(pair)
            .and_then(|rest| rest.checked_sub(2))
            .ok_or_else(unreadable)?;
        let mut frames = Vec::with_capacity(above);
        let mut focus = root;
        for _ in 0 .. above {
            match self.arena.computation(focus) {
                | Some(&Computation::Application(head, argument)) => {
                    frames.push(Frame::Apply(argument));
                    focus = head;
                },
                | Some(&Computation::Bind(bound, body)) => {
                    frames.push(Frame::Bind(body));
                    focus = bound;
                },
                | Some(&Computation::Project(projected, pair)) => {
                    frames.push(Frame::Project(projected));
                    focus = pair;
                },
                | Some(_) | None => return Err(unreadable()),
            }
        }
        let Some(&Computation::Bind(inner, outer)) = self.arena.computation(focus)
        else {
            return Err(unreadable());
        };
        let Some(&Computation::Bind(head, first)) = self.arena.computation(inner)
        else {
            return Err(unreadable());
        };
        self.read(Forced::Reassociate(side))?;
        let then = shift_computation(
            self.arena,
            &mut self.table,
            &mut self.memo,
            outer,
            BinderDepth::from(1),
            BinderDepth::from(1),
        );
        let fused = self.arena.computation_bind(first, then);
        let mut rebuilt = self.arena.computation_bind(head, fused);
        for &frame in frames.iter().rev() {
            rebuilt = self.wrap(rebuilt, frame);
        }
        goal.set(side, Term::Computation(rebuilt));
        Ok(())
    }

    /// Close or decompose a goal no decision is needed to rewrite.
    ///
    /// # Specification
    /// - requires: the goal selected [`Rule::Structural`].
    /// - ensures: a leaf closes at its verdict without consuming a decision. A
    ///   decomposition may consume a leading `Decompose`; one owing
    ///   convertibility pushes every premise, and one owing a refutation also
    ///   consumes the `NegativeSubgoal` naming its selected premise. A refused
    ///   negative subgoal leaves an already consumed `Decompose` consumed.
    /// - provides: implicit structural rules and their optional trace marker.
    /// - fails: a refusal on a leaf against the owed verdict, or a refutation
    ///   without its negative subgoal.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Refused`].
    ///
    /// # Adequacy
    /// - hypothesis: L3: a pair and a case/application spine distinguish
    ///   selecting the refuting premise from accepting a positive sibling or an
    ///   out-of-range position; newly scheduled goals owe the parent verdict.
    ///   Native path and flow fixtures separate an explicit decomposition from
    ///   its subsequent refusal without restoring the consumed prefix.
    /// - witness: `replay::tests::a_refutation_follows_its_negative_subgoal`
    /// - witness: `replay::tests::neutral_spines_keep_subgoal_order_and_reject_kind_mismatches`
    /// - witness: `path_universe::tests::it_computes_through_a_former`
    /// - witness: `flow_universe::tests::formation_boundaries_refuse`
    #[spec(
        requires: rule(left, right) == Rule::Structural,
        captures: before = (goals.len(), self.position),
        ensures: |ret| self.position >= before.1 && if ret.is_ok() {
            goals.get(before.0..).is_some_and(|pending| {
                pending.iter().all(|next| next.expect == goal.expect && next.frozen.left.is_empty() && next.frozen.right.is_empty())
                    && if pending.is_empty() {
                        self.position == before.1
                    } else {
                        match goal.expect {
                            Expect::Convertible => self.position <= before.1.saturating_add(1),
                            Expect::NotConvertible => pending.len() == 1
                                && self.position >= before.1.saturating_add(1)
                                && self.position <= before.1.saturating_add(2),
                        }
                    }
            })
        } else {
            goals.len() == before.0 && self.position <= before.1.saturating_add(1)
        },
    )]
    fn structural(
        &mut self,
        goal: &Goal,
        left: &Shape,
        right: &Shape,
        goals: &mut Vec<Goal>,
    ) -> Result<(), Stop>
    {
        let structure = self.decompose(goal, left, right)?;
        let next = self.peek();
        if matches!(next, Next::Decision(ConversionDecision::Decompose)) {
            if !matches!(structure, Structure::Premises(_)) {
                return Err(self.refuse(next));
            }
            self.take();
        }
        // A refutation over a presented type's term is not authoritative: a
        // leaf of its normal form may unfold into a redex, so two normal forms
        // apart here may still be one term.
        let presentations = self.unfoldings.presentations();
        let presented = |term: Term| match term {
            | Term::Value(value) => match self.arena.value(value) {
                | Some(&Value::Constructor { datatype, .. }) => matches!(
                    self.arena.value_type(datatype),
                    Some(&ValueType::Data { declaration, .. })
                        if presentations.presented(declaration).is_some()
                ),
                | _ => false,
            },
            | Term::Computation(_) => false,
        };
        if goal.expect == Expect::NotConvertible
            && structure == Structure::Leaf(Expect::NotConvertible)
            && (presented(goal.left) || presented(goal.right))
        {
            return Err(Stop::Refused(ReplayRefusal::NonAuthoritative {
                at: self.at(),
            }));
        }
        let premises = match structure {
            | Structure::Leaf(verdict) => return self.close(goal.expect, verdict),
            | Structure::Premises(premises) => premises,
        };
        self.schedule(goal.expect, premises, goals)
    }

    /// Schedule a decomposition's premises at the verdict its goal owes.
    ///
    /// # Specification
    /// - requires: `premises` is non-empty.
    /// - ensures: owing convertibility, every premise is pushed, the first on
    ///   top, and no decision is read; owing a refutation, the premise the next
    ///   `NegativeSubgoal` names is pushed alone and that decision consumed.
    ///   Every pushed goal owes `expect` with nothing frozen.
    /// - provides: the premise half shared by structural decomposition and the
    ///   lazy product's η.
    /// - fails: a refusal when a refutation's next decision is not a
    ///   `NegativeSubgoal` naming one of `premises`.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Refused`].
    ///
    /// # Adequacy
    /// - hypothesis: L3: a pair and a lazy pairing against a neutral
    ///   distinguish selecting the refuting premise from accepting a positive
    ///   sibling or an out-of-range position, and a missing `NegativeSubgoal`
    ///   from a present one.
    /// - witness: `replay::tests::a_refutation_follows_its_negative_subgoal`
    /// - witness: `replay::tests::a_lazy_pairing_meets_a_neutral_by_its_projections`
    #[spec(
        captures: before = (goals.len(), self.position, premises.len()),
        ensures: |ret| match ret {
            Ok(()) => goals.get(before.0..).is_some_and(|pending| {
                pending.iter().all(|next| next.expect == expect && next.frozen == Frozen::default())
                    && match expect {
                        Expect::Convertible => pending.len() == before.2 && self.position == before.1,
                        Expect::NotConvertible => pending.len() == 1_usize && self.position == before.1.saturating_add(1),
                    }
            }),
            Err(_) => goals.len() == before.0 && self.position == before.1,
        },
    )]
    fn schedule(
        &mut self,
        expect: Expect,
        premises: Vec<Premise>,
        goals: &mut Vec<Goal>,
    ) -> Result<(), Stop>
    {
        match expect {
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
    ///   returners, two lambdas, two lazy pairings, and two neutrals with one
    ///   head and agreeing spines decompose; every other pair is a refuting
    ///   leaf.
    /// - provides: the leaf and decomposition rules.
    /// - fails: [`ReplayRefusal::Unreadable`] on a dangling former.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Refused`].
    ///
    /// # Adequacy
    /// - hypothesis: L3: return, lambda, lazy pairing, pair, and neutral-spine
    ///   fixtures distinguish ordered same-polarity premises from rigidly
    ///   distinct leaves. The observer is the replayed positive or selected
    ///   negative derivation, not a general normalization proof.
    /// - witness: `replay::tests::the_replay_reduces_before_it_reads_a_decision`
    /// - witness: `replay::tests::eta_and_force_open_the_suspended_sides`
    /// - witness: `replay::tests::a_refutation_follows_its_negative_subgoal`
    /// - witness: `replay::tests::neutral_spines_keep_subgoal_order_and_reject_kind_mismatches`
    /// - witness: `replay::tests::a_lazy_pairing_meets_a_neutral_by_its_projections`
    #[spec(ensures: |ret| match (left, right) {
        (&Shape::Return(one), &Shape::Return(other)) => matches!(ret, Ok(Structure::Premises(ref premises)) if premises.as_slice() == [Premise::values(one, other)]),
        (&Shape::Lambda(one), &Shape::Lambda(other)) | (&Shape::Fixpoint(one), &Shape::Fixpoint(other)) => matches!(ret, Ok(Structure::Premises(ref premises)) if premises.as_slice() == [Premise::computations(one, other)]),
        (&Shape::With(one_first, one_second), &Shape::With(other_first, other_second)) => matches!(ret, Ok(Structure::Premises(ref premises))
            if premises.as_slice() == [Premise::computations(one_first, other_first), Premise::computations(one_second, other_second)]),
        (&Shape::Former, &Shape::Former) => true,
        (&Shape::Neutral(one, _), &Shape::Neutral(other, _)) if one == other => match ret {
            Ok(Structure::Premises(ref premises)) => !premises.is_empty() && premises.iter().all(|premise|
                matches!((premise.left, premise.right), (Term::Value(_), Term::Value(_)) | (Term::Computation(_), Term::Computation(_)))),
            Ok(Structure::Leaf(_)) | Err(Stop::Refused(ReplayRefusal::Unreadable)) => true,
            Err(_) => false,
        },
        _ => ret == Ok(Structure::Leaf(Expect::NotConvertible)),
    })]
    fn decompose(
        &mut self,
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
            | (&Shape::Lambda(left_body), &Shape::Lambda(right_body))
            | (&Shape::Fixpoint(left_body), &Shape::Fixpoint(right_body)) => {
                Structure::of(Vec::from([Premise::computations(left_body, right_body)]))
            },
            | (&Shape::With(left_first, left_second), &Shape::With(right_first, right_second)) => {
                Structure::of(Vec::from([
                    Premise::computations(left_first, right_first),
                    Premise::computations(left_second, right_second),
                ]))
            },
            | (
                &Shape::Neutral(left_head, ref left_spine),
                &Shape::Neutral(right_head, ref right_spine),
            ) if left_head == right_head => spines(self.arena, left_spine, right_spine)?,
            | (
                &(Shape::Former
                | Shape::Thunk(_)
                | Shape::Lambda(_)
                | Shape::With(..)
                | Shape::Fixpoint(_)
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
    /// - ensures: as [`Self::decompose`], over the value formers; two
    ///   reflexivities decompose to their points. A returned endpoint never
    ///   reaches here: [`Self::settle`] reads it first.
    /// - provides: the former half of [`Self::decompose`].
    /// - fails: [`ReplayRefusal::Unreadable`] on a dangling id or a returned
    ///   endpoint.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Refused`].
    ///
    /// # Adequacy
    /// - hypothesis: L3: pair refutations select the differing component and
    ///   reject a positive sibling or an absent index; unit and distinct rigid
    ///   leaves close at opposite verdicts; two reflexivities one unfolding
    ///   apart convert by the unfolding their points need and refuse it read on
    ///   the other side. Quotes and larger former combinations are not claimed
    ///   by these fixtures. Native path witnesses separate evidence from
    ///   syntax; their predicate observes identity and root family without
    ///   repeating conversion.
    /// - witness: `replay::tests::a_refutation_follows_its_negative_subgoal`
    /// - witness: `replay::tests::a_compared_pair_closes_on_alpha_equality_or_rigid_separation`
    /// - witness: `path_universe::tests::certificate_identity_stays_out_of_conversion`
    /// - witness: `replay::tests::two_reflexivities_decompose_to_their_points`
    #[spec(ensures: |ret| { let (matched_left_value, matched_right_value) = (self.arena.value(left), self.arena.value(right));
if let Some(matched_left_node) = matched_left_value && let Value::Constructor { datatype:a,tag:a_tag,fields:ref a_fields } = *matched_left_node && let Some(matched_right_node) = matched_right_value && let Value::Constructor { datatype:b,tag:b_tag,fields:ref b_fields } = *matched_right_node { {
            if a_tag != b_tag || a_fields.len() != b_fields.len() { ret == Ok(Structure::Leaf(Expect::NotConvertible)) }
            else { matches!(&ret,Ok(Structure::Premises(premises)) if premises.len() == a_fields.len().saturating_add(1_usize)
                && premises.first().is_some_and(|premise| matches!((premise.left,premise.right), (Term::Value(left),Term::Value(right)) if self.arena.value(left) == Some(&Value::Quote(a)) && self.arena.value(right) == Some(&Value::Quote(b))))
                && premises.iter().skip(1).copied().eq(a_fields.iter().zip(b_fields).map(|(a,b)| Premise::values(*a,*b)))) }
        } }
 else if let Some(matched_left_node) = matched_left_value && let Value::Record(ref a) = *matched_left_node && let Some(matched_right_node) = matched_right_value && let Value::Record(ref b) = *matched_right_node { {
            if a.keys().eq(b.keys()) { ret == Ok(Structure::of(a.values().zip(b.values()).map(|(a,b)| Premise::values(*a,*b)).collect())) } else { ret == Ok(Structure::Leaf(Expect::NotConvertible)) }
        } }
 else if matched_left_value.is_none() || matched_right_value.is_none() || matches!(matched_left_value, Some(&Value::Returned(_))) || matches!(matched_right_value, Some(&Value::Returned(_))) { ret == Err(unreadable()) }
 else if let (Some(&Value::Here { point: one_point, .. }), Some(&Value::Here { point: other_point, .. })) = (matched_left_value, matched_right_value) { matches!(ret, Ok(Structure::Premises(ref premises)) if premises.as_slice() == [Premise::values(one_point, other_point)]) }
 else if let Some(matched_left_node) = matched_left_value && let ref one @ (Value::PathRefl(_) | Value::PathProduct(..) | Value::PathEquiv { .. } | Value::Here { .. } | Value::Stay { .. } | Value::ForwardFlow { .. } | Value::FunctionFlow { .. } | Value::Then { .. } | Value::FlowProduct(..) | Value::Higher { .. } | Value::HigherEvaluation { .. } | Value::QuantifiedEvaluation { .. }) = *matched_left_node && let Some(other) = matched_right_value { matches!(ret, Ok(Structure::Leaf(verdict)) if (left != right || verdict == Expect::Convertible)
                && (core::mem::discriminant(one) == core::mem::discriminant(other) || verdict == Expect::NotConvertible)) }
 else if matches!((matched_left_value, matched_right_value), (Some(&Value::ListNil), Some(&Value::ListNil))) { ret == Ok(Structure::Leaf(Expect::Convertible)) }
 else if let (Some(one), Some(other)) = (matched_left_value.and_then(Value::components), matched_right_value.and_then(Value::components)) { if one.len() == other.len() { ret == Ok(Structure::of(one.iter().zip(other.iter()).map(|(&a, &b)| Premise::values(a, b)).collect())) } else { ret == Ok(Structure::Leaf(Expect::NotConvertible)) } }
 else if let Some(matched_left_node) = matched_left_value && let ref one @ Value::Literal(_) = *matched_left_node && let Some(matched_right_node) = matched_right_value && let ref other @ Value::Literal(_) = *matched_right_node { ret == Ok(Structure::Leaf(if one == other { Expect::Convertible } else { Expect::NotConvertible })) }
 else if let (Some(&Value::ListCons(one_first, one_second)), Some(&Value::ListCons(other_first, other_second))) = (matched_left_value, matched_right_value) { matches!(ret, Ok(Structure::Premises(ref premises)) if premises.as_slice() == [Premise::values(one_first, other_first), Premise::values(one_second, other_second)]) }
 else if let Some(matched_left_node) = matched_left_value && let Value::Injection(one_side, one_body) = *matched_left_node && let Some(matched_right_node) = matched_right_value && let Value::Injection(other_side, other_body) = *matched_right_node && (one_side == other_side) { matches!(ret, Ok(Structure::Premises(ref premises)) if premises.as_slice() == [Premise::values(one_body, other_body)]) }
 else if let Some(matched_left_node) = matched_left_value && let Value::Lift { target: ref one_target, body: one_body } = *matched_left_node && let Some(matched_right_node) = matched_right_value && let Value::Lift { target: ref other_target, body: other_body } = *matched_right_node && (one_target == other_target) { matches!(ret, Ok(Structure::Premises(ref premises)) if premises.as_slice() == [Premise::values(one_body, other_body)]) }
 else if (matched_left_value.is_some_and(|node| matches!(*node, Value::Quote(_))) && matched_right_value.is_some_and(|node| matches!(*node, Value::Quote(_)))) || (matched_left_value.is_some_and(|node| matches!(*node, Value::QuoteComputation(_))) && matched_right_value.is_some_and(|node| matches!(*node, Value::QuoteComputation(_)))) { matches!(ret, Ok(Structure::Leaf(_)) | Err(Stop::Refused(ReplayRefusal::Unreadable))) }
 else { ret == Ok(Structure::Leaf(Expect::NotConvertible)) }
})]
    fn formers(
        &mut self,
        left: ValueId,
        right: ValueId,
    ) -> Result<Structure, Stop>
    {
        let (Some(one), Some(other)) = (self.arena.value(left), self.arena.value(right))
        else {
            return Err(unreadable());
        };
        let structure = match (one, other) {
            | (&Value::Returned(_), _) | (_, &Value::Returned(_)) => return Err(unreadable()),
            | (
                &Value::Constructor {
                    datatype: a,
                    tag: one_tag,
                    fields: ref a_fields,
                },
                &Value::Constructor {
                    datatype: b,
                    tag: other_tag,
                    fields: ref b_fields,
                },
            ) => {
                if one_tag != other_tag || a_fields.len() != b_fields.len() {
                    return Ok(Structure::Leaf(Expect::NotConvertible));
                }
                let count = a_fields.len();
                let a_quote = self.arena.value_quote(a);
                let b_quote = self.arena.value_quote(b);
                let mut premises = Vec::with_capacity(count.saturating_add(1_usize));
                premises.push(Premise::values(a_quote, b_quote));
                let (Some(left_node), Some(right_node)) =
                    (self.arena.value(left), self.arena.value(right))
                else {
                    return Err(unreadable());
                };
                let Value::Constructor {
                    fields: ref a_fields,
                    ..
                } = *left_node
                else {
                    return Err(unreadable());
                };
                let Value::Constructor {
                    fields: ref b_fields,
                    ..
                } = *right_node
                else {
                    return Err(unreadable());
                };
                premises.extend(
                    a_fields
                        .iter()
                        .zip(b_fields)
                        .map(|(a, b)| Premise::values(*a, *b)),
                );
                Structure::of(premises)
            },
            | (&Value::Record(ref a), &Value::Record(ref b)) => {
                if a.len() != b.len() || !a.keys().eq(b.keys()) {
                    Structure::Leaf(Expect::NotConvertible)
                }
                else {
                    Structure::of(
                        a.values()
                            .zip(b.values())
                            .map(|(a, b)| Premise::values(*a, *b))
                            .collect(),
                    )
                }
            },
            // Two reflexivities convert exactly when their points do; the
            // dialogues they carry are evidence for their endpoints, never
            // part of the value.
            | (
                &Value::Here {
                    point: left_point, ..
                },
                &Value::Here {
                    point: right_point, ..
                },
            ) => Structure::of(Vec::from([Premise::values(left_point, right_point)])),
            | (
                &(Value::PathRefl(_)
                | Value::PathProduct(..)
                | Value::SessionPath { .. }
                | Value::SessionFlow { .. }
                | Value::PathEquiv { .. }
                | Value::Here { .. }
                | Value::Stay { .. }
                | Value::ForwardFlow { .. }
                | Value::FunctionFlow { .. }
                | Value::Then { .. }
                | Value::FlowProduct(..)
                | Value::Higher { .. }
                | Value::HigherEvaluation { .. }
                | Value::QuantifiedEvaluation { .. }),
                _,
            ) => Structure::Leaf(
                if equal_values(self.arena, left, right) == Convertibility::Convertible {
                    Expect::Convertible
                }
                else {
                    Expect::NotConvertible
                },
            ),
            | (&Value::ListNil, &Value::ListNil) => Structure::Leaf(Expect::Convertible),
            // Two tuples of one arity compare component by component; a
            // different arity separates them.
            | (&Value::Tuple(ref left), &Value::Tuple(ref right)) => {
                if left.len() == right.len() {
                    Structure::of(
                        left.iter()
                            .zip(right.iter())
                            .map(|(&left, &right)| Premise::values(left, right))
                            .collect(),
                    )
                }
                else {
                    Structure::Leaf(Expect::NotConvertible)
                }
            },
            | (&Value::Literal(_), &Value::Literal(_)) if one == other => {
                Structure::Leaf(Expect::Convertible)
            },
            | (
                &Value::ListCons(left_first, left_second),
                &Value::ListCons(right_first, right_second),
            ) => Structure::of(Vec::from([
                Premise::values(left_first, right_first),
                Premise::values(left_second, right_second),
            ])),
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
                | Value::Constructor { .. }
                | Value::Record(_)
                | Value::Constant(_)
                | Value::Literal(_)
                | Value::Tuple(..)
                | Value::ListNil
                | Value::ListCons(..)
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
    ///
    /// # Adequacy
    /// - hypothesis: L3: equal pairs, distinct rigid variables, thunks, and
    ///   defined constants separate equality, rigid separation, and undecided
    ///   comparison under both engine claims. Only root identity and polarity
    ///   are executable here; the recursive relation is not rerun.
    /// - witness: `replay::tests::a_compared_pair_closes_on_alpha_equality_or_rigid_separation`
    #[spec(ensures: |ret| match (goal.left, goal.right) {
        (Term::Value(left), Term::Value(right)) if left == right =>
            ret == Ok(if self.arena.value(left).is_some() { Compared::Equal } else { Compared::Open }),
        (Term::Computation(left), Term::Computation(right)) if left == right =>
            ret == Ok(if self.arena.computation(left).is_some() { Compared::Equal } else { Compared::Open }),
        (Term::Value(_), Term::Computation(_)) | (Term::Computation(_), Term::Value(_)) => ret == Err(unreadable()),
        _ => ret.is_ok(),
    })]
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
    /// - ensures: native path introductions are rigid records: comparison never
    ///   descends into their translator programs. Every other term is rigid
    ///   exactly when it resolves throughout and contains no reducible thunk,
    ///   returned endpoint, lambda, bind, case, transport or defined constant,
    ///   including through quoted types, decoded codes and static application
    ///   operands. A static application over an opaque head is rigid.
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
    ///
    /// # Adequacy
    /// - hypothesis: L3: units and distinct variables are rigid while thunks
    ///   and defined constants prevent a shared comparison from closing
    ///   negatively. This observer covers the root barriers and named pair
    ///   fixtures, not every quoted type graph.
    /// - witness: `replay::tests::a_compared_pair_closes_on_alpha_equality_or_rigid_separation`
    /// - witness: `path_universe::tests::certificate_identity_stays_out_of_conversion`
    #[spec(ensures: |ret| match term {
        Term::Value(value) => match self.arena.value(value) {
            Some(&(Value::Literal(_) | Value::Variable(_) | Value::PathRefl(_) | Value::PathProduct(..) | Value::PathEquiv { .. } | Value::Here { .. } | Value::Stay { .. } | Value::ForwardFlow { .. } | Value::FunctionFlow { .. } | Value::Then { .. } | Value::FlowProduct(..) | Value::Higher { .. } | Value::HigherEvaluation { .. } | Value::QuantifiedEvaluation { .. })) => ret == Rigidity::Rigid,
            Some(held) if held.components() == Some(&[]) => ret == Rigidity::Rigid,
            Some(&Value::Constant(constant)) => (ret == Rigidity::Rigid) == (self.unfoldings.unfolding(constant) == Unfoldable::Opaque),
            Some(&(Value::Thunk(_) | Value::Returned(_))) | None => ret == Rigidity::Flexible,
            _ => true,
        },
        Term::Computation(computation) => match self.arena.computation(computation) {
            Some(&(Computation::Transport(..) | Computation::PathTransport { .. } | Computation::TelescopeTransport { .. } | Computation::Ride { .. } | Computation::TelescopeRide { .. } | Computation::RelatedApplication { .. } | Computation::Lambda(_) | Computation::Bind(..) | Computation::Case { .. } | Computation::With(..) | Computation::Project(..))) | None => ret == Rigidity::Flexible,
            _ => true,
        },
    })]
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
                    | Some(&Value::Constructor {
                        datatype,
                        ref fields,
                        ..
                    }) => {
                        // A presented type's constructor may be a redex, or
                        // become one when a leaf unfolds.
                        if let Some(&ValueType::Data { declaration, .. }) =
                            self.arena.value_type(datatype)
                            && self
                                .unfoldings
                                .presentations()
                                .presented(declaration)
                                .is_some()
                        {
                            return Rigidity::Flexible;
                        }
                        work.extend(
                            core::iter::once(AnyNode::ValueType(datatype))
                                .chain(fields.iter().copied().map(AnyNode::Value)),
                        );
                    },
                    | Some(&Value::Record(ref fields)) => {
                        work.extend(fields.values().copied().map(AnyNode::Value));
                    },
                    | Some(
                        &(Value::Literal(_)
                        | Value::ListNil
                        | Value::Variable(_)
                        | Value::PathRefl(_)
                        | Value::PathProduct(..)
                        | Value::SessionPath { .. }
                        | Value::SessionFlow { .. }
                        | Value::PathEquiv { .. }
                        | Value::Here { .. }
                        | Value::Stay { .. }
                        | Value::ForwardFlow { .. }
                        | Value::FunctionFlow { .. }
                        | Value::Then { .. }
                        | Value::FlowProduct(..)
                        | Value::Higher { .. }
                        | Value::HigherEvaluation { .. }
                        | Value::QuantifiedEvaluation { .. }),
                    ) => {},
                    | Some(
                        &(Value::ListCons(first, second) | Value::StaticApplication(first, second)),
                    ) => {
                        work.extend([AnyNode::Value(first), AnyNode::Value(second)]);
                    },
                    | Some(&Value::Tuple(ref components)) => {
                        work.extend(components.iter().copied().map(AnyNode::Value));
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
                    | Some(&(Value::Thunk(_) | Value::Returned(_))) | None => {
                        return Rigidity::Flexible;
                    },
                },
                | AnyNode::Computation(computation) => match self.arena.computation(computation) {
                    | Some(&(Computation::Return(value) | Computation::Force(value))) => {
                        work.push(AnyNode::Value(value));
                    },
                    | Some(&Computation::Application(head, argument)) => {
                        work.extend([AnyNode::Computation(head), AnyNode::Value(argument)]);
                    },
                    | Some(
                        &(Computation::Transport(..)
                        | Computation::PathTransport { .. }
                        | Computation::TelescopeTransport { .. }
                        | Computation::Ride { .. }
                        | Computation::TelescopeRide { .. }
                        | Computation::RelatedApplication { .. }
                        | Computation::DataCase { .. }
                        | Computation::SigmaSplit { .. }
                        | Computation::RecordProjection(..)
                        | Computation::TupleProjection(..)
                        | Computation::Lambda(_)
                        | Computation::Fixpoint { .. }
                        | Computation::ListFold { .. }
                        | Computation::Bind(..)
                        | Computation::Case { .. }
                        | Computation::With(..)
                        | Computation::Project(..)),
                    )
                    | None => {
                        return Rigidity::Flexible;
                    },
                },
                | AnyNode::ValueType(value_type) => match self.arena.value_type(value_type) {
                    | Some(&ValueType::Data { ref arguments, .. }) => {
                        work.extend(arguments.iter().copied().map(AnyNode::Value));
                    },
                    | Some(&ValueType::Record(ref fields)) => {
                        work.extend(fields.values().copied().map(AnyNode::ValueType));
                    },
                    | Some(
                        &(ValueType::Base(_) | ValueType::Universe { .. } | ValueType::Abstract(_)),
                    ) => {},
                    | Some(&(ValueType::Product(ref parts) | ValueType::Sum(ref parts))) => {
                        work.extend(parts.iter().copied().map(AnyNode::ValueType));
                    },
                    | Some(
                        &ValueType::PathUniverse(source, target)
                        | &ValueType::FlowUniverse(source, target),
                    ) => {
                        work.extend([AnyNode::Value(source), AnyNode::Value(target)]);
                    },
                    | Some(
                        &ValueType::Path {
                            domain,
                            left,
                            right,
                        }
                        | &ValueType::Flow {
                            domain,
                            source: left,
                            target: right,
                        },
                    ) => {
                        work.extend([
                            AnyNode::ValueType(domain),
                            AnyNode::Value(left),
                            AnyNode::Value(right),
                        ]);
                    },
                    | Some(
                        &ValueType::StaticPi {
                            domain: first,
                            codomain: second,
                        }
                        | &ValueType::Sigma { first, second },
                    ) => {
                        work.extend([AnyNode::ValueType(first), AnyNode::ValueType(second)]);
                    },
                    | Some(&ValueType::Thunk(body)) => work.push(AnyNode::CompType(body)),
                    | Some(
                        &ValueType::Session {
                            payloads: inner, ..
                        }
                        | &ValueType::Lift { inner, .. }
                        | &ValueType::List(inner),
                    ) => {
                        work.push(AnyNode::ValueType(inner));
                    },
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
                    | Some(&CompType::With(left, right)) => {
                        work.extend([AnyNode::CompType(left), AnyNode::CompType(right)]);
                    },
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
    ///   applications, innermost first; a computation's lambda, lazy pairing,
    ///   returner, or head under its spine, innermost first. A transport's path
    ///   and a ride's flow stand at the head of their elimination.
    /// - provides: what the rule table dispatches on.
    /// - fails: [`ReplayRefusal::Unreadable`] on a dangling id, a head no rule
    ///   reads, or a returned endpoint, which [`Self::settle`] reads first.
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
    ///
    /// # Adequacy
    /// - hypothesis: L3: force/eta traces and neutral case/application spines
    ///   distinguish head classes and the order of their premises; static
    ///   operator traces cover static application heads; a ride over a named
    ///   flow offers that flow's unfolding on its own side only. The executable
    ///   observer checks root shape and the outermost elimination without
    ///   repeating the head walk.
    /// - witness: `replay::tests::eta_and_force_open_the_suspended_sides`
    /// - witness: `replay::tests::neutral_spines_keep_subgoal_order_and_reject_kind_mismatches`
    /// - witness: `replay::tests::an_operator_unfolds_by_instantiating_its_parameters_in_order`
    /// - witness: `path_universe::tests::refl_collapses`
    /// - witness: `replay::tests::a_projection_runs_its_side_of_a_pairing`
    /// - witness: `replay::tests::a_ride_unfolds_its_flow_where_the_dialogue_names_it`
    #[spec(ensures: |ret| match term {
        Term::Value(value) => match self.arena.value(value) {
            Some(&Value::Variable(index)) => matches!(ret, Ok(Shape::Neutral(Head::Variable(found), ref spine)) if found == index && spine.is_empty()),
            Some(&Value::Constant(constant)) => matches!(ret, Ok(Shape::Neutral(head, ref spine)) if head == self.head(constant, frozen, side) && spine.is_empty()),
            Some(&Value::Thunk(body)) => ret == Ok(Shape::Thunk(body)),
            Some(&Value::Returned(_)) | None => ret == Err(unreadable()),
            Some(&Value::StaticApplication(_, argument)) => match ret {
                Ok(Shape::Neutral(_, ref spine)) => spine.last() == Some(&Elimination::StaticApply(argument))
                    && spine.iter().all(|elimination| matches!(elimination, &Elimination::StaticApply(_))),
                Err(Stop::Refused(ReplayRefusal::Unreadable)) => true,
                _ => false,
            },
            Some(_) => ret == Ok(Shape::Former),
        },
        Term::Computation(computation) => match self.arena.computation(computation) {
            Some(&Computation::Lambda(body)) => ret == Ok(Shape::Lambda(body)),
            Some(&Computation::With(first, second)) => ret == Ok(Shape::With(first, second)),
            Some(&Computation::Fixpoint { body, .. }) => ret == Ok(Shape::Fixpoint(body)),
            Some(&Computation::Return(value)) => ret == Ok(Shape::Return(value)),
            Some(node) => match ret {
                Ok(Shape::Neutral(_, ref spine)) => match *node {
                    Computation::Application(head, argument) => spine.last() == Some(&Elimination::Apply(argument))
                        || (matches!(self.arena.computation(head), Some(&Computation::Fixpoint { .. })) && spine.last() == Some(&Elimination::Fixpoint(head))),
                    Computation::Bind(_, body) => spine.last() == Some(&Elimination::Bind(body)),
                    Computation::Force(_) => spine.as_slice() == [Elimination::Force],
                    Computation::Transport(path, value) => if matches!(self.arena.value(path), Some(&Value::PathProduct(..))) {
                        spine.as_slice() == [Elimination::ProductTransport(path)]
                    } else { spine.as_slice() == [Elimination::Transport(value)] },
                    Computation::Ride { .. } => spine.as_slice() == [Elimination::Ride(computation)],
                    Computation::Case { .. } => spine.as_slice() == [Elimination::Case(computation)],
                    Computation::DataCase { .. } => spine.as_slice() == [Elimination::DataCase(computation)],
                    Computation::SigmaSplit { .. } => spine.as_slice() == [Elimination::SigmaSplit(computation)],
                    Computation::RecordProjection(..) => spine.as_slice() == [Elimination::RecordProjection(computation)],
                    Computation::TupleProjection(..) => spine.as_slice() == [Elimination::TupleProjection(computation)],
                    Computation::Project(side, _) => spine.last() == Some(&Elimination::Project(side)),
                    Computation::ListFold { on_nil, on_cons, .. } => spine.as_slice() == [Elimination::ListFold(on_nil, on_cons)],
                    _ => false,
                },
                Err(Stop::Refused(ReplayRefusal::Unreadable)) => true,
                _ => false,
            },
            None => ret == Err(unreadable()),
        },
    })]
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
                    | Some(&Value::Returned(_)) | None => Err(unreadable()),
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
                        &(Value::PathRefl(_)
                        | Value::Constructor { .. }
                        | Value::Record(_)
                        | Value::PathProduct(..)
                        | Value::SessionPath { .. }
                        | Value::SessionFlow { .. }
                        | Value::PathEquiv { .. }
                        | Value::Literal(_)
                        | Value::Tuple(..)
                        | Value::ListNil
                        | Value::ListCons(..)
                        | Value::Injection(..)
                        | Value::Lift { .. }
                        | Value::Quote(_)
                        | Value::QuoteComputation(_)
                        | Value::Here { .. }
                        | Value::Stay { .. }
                        | Value::ForwardFlow { .. }
                        | Value::FunctionFlow { .. }
                        | Value::Then { .. }
                        | Value::FlowProduct(..)
                        | Value::Higher { .. }
                        | Value::HigherEvaluation { .. }
                        | Value::QuantifiedEvaluation { .. }),
                    ) => Ok(Shape::Former),
                };
            },
            | Term::Computation(computation) => computation,
        };
        let mut spine = Vec::new();
        let mut focus = start;
        let head = loop {
            match self.arena.computation(focus) {
                | Some(&Computation::DataCase { scrutinee, .. }) => {
                    spine.push(Elimination::DataCase(focus));
                    break self.value_head(scrutinee, frozen, side)?;
                },
                | Some(&Computation::SigmaSplit { scrutinee, .. }) => {
                    spine.push(Elimination::SigmaSplit(focus));
                    break self.value_head(scrutinee, frozen, side)?;
                },
                | Some(&Computation::RecordProjection(record, _)) => {
                    spine.push(Elimination::RecordProjection(focus));
                    break self.value_head(record, frozen, side)?;
                },
                | Some(&Computation::TupleProjection(tuple, _)) => {
                    spine.push(Elimination::TupleProjection(focus));
                    break self.value_head(tuple, frozen, side)?;
                },
                | Some(&Computation::ListFold {
                    list,
                    on_nil,
                    on_cons,
                    ..
                }) => {
                    spine.push(Elimination::ListFold(on_nil, on_cons));
                    break self.value_head(list, frozen, side)?;
                },
                | Some(&Computation::Transport(path, value)) => {
                    if matches!(self.arena.value(path), Some(&Value::PathProduct(..))) {
                        spine.push(Elimination::ProductTransport(path));
                        break self.value_head(value, frozen, side)?;
                    }
                    spine.push(Elimination::Transport(value));
                    break self.value_head(path, frozen, side)?;
                },
                // A ride stuck at the table stands on its flow: a defined
                // flow unfolds where the dialogue names it, as a transport's
                // path does.
                | Some(&Computation::Ride { flow, .. }) => {
                    spine.push(Elimination::Ride(focus));
                    break self.value_head(flow, frozen, side)?;
                },
                | Some(&Computation::Lambda(body)) if spine.is_empty() => {
                    return Ok(Shape::Lambda(body));
                },
                | Some(&Computation::With(first, second)) if spine.is_empty() => {
                    return Ok(Shape::With(first, second));
                },
                | Some(&Computation::Fixpoint { body, .. }) if spine.is_empty() => {
                    return Ok(Shape::Fixpoint(body));
                },
                // A fixpoint applied to a neutral argument is stuck on that
                // argument's head: the application directly over it becomes the
                // fixpoint's elimination, and the argument's head the neutral's.
                | Some(&Computation::Fixpoint { .. }) => {
                    let Some(Elimination::Apply(argument)) = spine.pop()
                    else {
                        return Err(unreadable());
                    };
                    spine.push(Elimination::Fixpoint(focus));
                    break self.value_head(argument, frozen, side)?;
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
                | Some(&Computation::Project(side, pair)) => {
                    spine.push(Elimination::Project(side));
                    focus = pair;
                },
                | Some(&Computation::Force(value)) => {
                    spine.push(Elimination::Force);
                    let head = self.value_head(value, frozen, side)?;
                    break head;
                },
                | Some(&Computation::Case { scrutinee, .. }) => {
                    spine.push(Elimination::Case(focus));
                    let head = self.value_head(scrutinee, frozen, side)?;
                    break head;
                },
                // A transport in a motive, a telescope ride or a related
                // application that did not reduce has no trace alphabet of its
                // own: the replay reads it as unreadable.
                | Some(
                    &(Computation::Lambda(_)
                    | Computation::With(..)
                    | Computation::Return(_)
                    | Computation::PathTransport { .. }
                    | Computation::TelescopeTransport { .. }
                    | Computation::TelescopeRide { .. }
                    | Computation::RelatedApplication { .. }),
                )
                | None => {
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
    ///
    /// # Adequacy
    /// - hypothesis: L3: a forced variable and a statically applied defined
    ///   constant replay as neutral heads; a non-head value is refused by the
    ///   local observer. The witnesses distinguish variable identity from the
    ///   named constant rule.
    /// - witness: `replay::tests::eta_and_force_open_the_suspended_sides`
    /// - witness: `replay::tests::an_operator_unfolds_by_instantiating_its_parameters_in_order`
    /// - witness: `path_universe::tests::no_k`
    #[spec(ensures: |ret| ret == match self.arena.value(value) {
        Some(&Value::Variable(index)) => Ok(Head::Variable(index)),
        Some(&Value::Constant(constant)) => Ok(self.head(constant, frozen, side)),
        _ => Err(unreadable()),
    })]
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
                &(Value::PathRefl(_)
                | Value::Constructor { .. }
                | Value::Record(_)
                | Value::PathProduct(..)
                | Value::SessionPath { .. }
                | Value::SessionFlow { .. }
                | Value::PathEquiv { .. }
                | Value::Literal(_)
                | Value::Tuple(..)
                | Value::ListNil
                | Value::ListCons(..)
                | Value::Injection(..)
                | Value::Thunk(_)
                | Value::Lift { .. }
                | Value::Quote(_)
                | Value::QuoteComputation(_)
                | Value::StaticApplication(..)
                | Value::Here { .. }
                | Value::Stay { .. }
                | Value::ForwardFlow { .. }
                | Value::FunctionFlow { .. }
                | Value::Then { .. }
                | Value::FlowProduct(..)
                | Value::Higher { .. }
                | Value::HigherEvaluation { .. }
                | Value::QuantifiedEvaluation { .. }
                | Value::Returned(_)),
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
    ///
    /// # Adequacy
    /// - hypothesis: L3: body, operator, explicit opaque, and out-of-range
    ///   entries are observed on both sides before and after freezing; opacity
    ///   takes precedence over frozen membership.
    /// - witness: `replay::tests::frozen_heads_are_side_local_and_opacity_takes_precedence`
    #[spec(ensures: |ret| ret == Head::Constant(constant,
        if self.unfoldings.unfolding(constant) == Unfoldable::Opaque { Status::Opaque }
        else if frozen.side(side).contains(&constant) { Status::Frozen }
        else { Status::Defined }))]
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
    /// # Adequacy
    /// - hypothesis: L3: named-head traces distinguish the rewritten side and
    ///   preserve the opposite side; operator instantiation preserves parameter
    ///   order and ambient indices. The postcondition frames polarity and the
    ///   untouched side without replaying substitution.
    /// - witness: `replay::tests::an_unfolding_fires_only_where_the_trace_names_its_head`
    /// - witness: `replay::tests::an_operator_unfolds_by_instantiating_its_parameters_in_order`
    #[spec(
        captures: before = (goal.side(side), goal.side(opposite(side))),
        ensures: |ret| goal.side(opposite(side)) == before.1 && if ret.is_ok() {
            self.unfoldings.unfolding(constant) != Unfoldable::Opaque
                && matches!((before.0, goal.side(side)), (Term::Value(_), Term::Value(_)) | (Term::Computation(_), Term::Computation(_)))
        } else { goal.side(side) == before.0 },
    )]
    fn unfold(
        &mut self,
        goal: &mut Goal,
        side: ConversionSide,
        constant: ConstantIndex,
    ) -> Result<(), Stop>
    {
        let reduct = self.unfold_term(goal.side(side), constant)?;
        goal.set(side, reduct);
        Ok(())
    }

    /// The δ- or δβ-reduct of `term`, whose head is the defined `constant`:
    /// the one δ-step a trace's `Unfold` and the endpoint reading both fire.
    ///
    /// # Specification
    /// - requires: `term`'s head is `constant`, defined.
    /// - ensures: a value its δ- or δβ-reduct, as [`Self::unfold_value`] gives
    ///   it; a computation its spine over the body, a ride's body standing as
    ///   its flow; of `term`'s polarity either way.
    /// - provides: the term half of [`Self::unfold`], shared with
    ///   [`Self::normalize_returned`].
    /// - fails: as [`Self::unfold`].
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the trace's named-head unfoldings of
    ///   [`Self::unfold`], a ride's named flow among them, and a definition at
    ///   a returned endpoint's head, read at a mode switch.
    /// - witness: `replay::tests::an_unfolding_fires_only_where_the_trace_names_its_head`
    /// - witness: `replay::tests::a_ride_unfolds_its_flow_where_the_dialogue_names_it`
    /// - witness: `element_identity::tests::a_certificate_with_a_returned_endpoint_decodes_checks_and_replays`
    #[spec(ensures: |ret| match ret {
        Ok(reduct) => self.unfoldings.unfolding(constant) != Unfoldable::Opaque
            && matches!((term, reduct), (Term::Value(_), Term::Value(_)) | (Term::Computation(_), Term::Computation(_))),
        Err(_) => true,
    })]
    fn unfold_term(
        &mut self,
        term: Term,
        constant: ConstantIndex,
    ) -> Result<Term, Stop>
    {
        let unfolding = self.unfoldings.unfolding(constant);
        let start = match term {
            | Term::Value(value) => return Ok(Term::Value(self.unfold_value(value, unfolding)?)),
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
                | Some(&Computation::DataCase {
                    motive,
                    ref branches,
                    ..
                }) => {
                    break self
                        .arena
                        .computation_data_case(body, motive, branches.clone());
                },
                | Some(&Computation::SigmaSplit {
                    motive,
                    body: split,
                    ..
                }) => {
                    break self.arena.computation_sigma_split(body, motive, split);
                },
                | Some(&Computation::RecordProjection(_, ref label)) => {
                    break self
                        .arena
                        .computation_record_projection(body, label.clone());
                },
                | Some(&Computation::TupleProjection(_, component)) => {
                    break self.arena.computation_tuple_projection(body, component);
                },
                | Some(&Computation::ListFold {
                    element,
                    result,
                    on_nil,
                    on_cons,
                    ..
                }) => {
                    break self
                        .arena
                        .computation_list_fold(element, result, body, on_nil, on_cons);
                },
                | Some(&Computation::Transport(path, value)) => {
                    break if matches!(self.arena.value(path), Some(&Value::PathProduct(..))) {
                        self.arena.computation_transport(path, body)
                    }
                    else {
                        self.arena.computation_transport(body, value)
                    };
                },
                | Some(&Computation::Ride { motive, value, .. }) => {
                    break self.arena.computation_ride(motive, body, value);
                },
                | Some(&Computation::Application(head, argument)) => {
                    frames.push(Frame::Apply(argument));
                    focus = head;
                },
                | Some(&Computation::Bind(bound, next)) => {
                    frames.push(Frame::Bind(next));
                    focus = bound;
                },
                | Some(&Computation::Project(side, pair)) => {
                    frames.push(Frame::Project(side));
                    focus = pair;
                },
                | Some(&Computation::Force(_)) => break self.arena.computation_force(body),
                | Some(&Computation::Case { ref branches, .. }) => {
                    let branches = branches.clone();
                    break self.arena.computation_case(body, &branches);
                },
                // A stuck fixpoint's head is its argument: the constant
                // unfolds in the application directly over the fixpoint.
                | Some(&Computation::Fixpoint { .. }) => {
                    let Some(Frame::Apply(_)) = frames.pop()
                    else {
                        return Err(unreadable());
                    };
                    break self.arena.computation_application(focus, body);
                },
                | Some(
                    &(Computation::Lambda(_)
                    | Computation::With(..)
                    | Computation::Return(_)
                    | Computation::PathTransport { .. }
                    | Computation::TelescopeTransport { .. }
                    | Computation::TelescopeRide { .. }
                    | Computation::RelatedApplication { .. }),
                )
                | None => {
                    return Err(unreadable());
                },
            }
        };
        while let Some(frame) = frames.pop() {
            rebuilt = self.wrap(rebuilt, frame);
        }
        Ok(Term::Computation(rebuilt))
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
    ///   thunk, a returner met by a bind, an injection met by a case, a lazy
    ///   pairing met by a projection, a fixpoint carrying replayed
    ///   structural-descent evidence applied to a constructor, an elimination
    ///   met by a returned endpoint, which binds the endpoint's computation and
    ///   eliminates what it returns, and the element-identity transport and
    ///   related application steps of [`crate::element_identity`], until none
    ///   fires at its head, and the original id when none fired at all.
    /// - provides: the search-free reductions the trace never records.
    /// - fails: [`Stop::Budget`] on a term that reduces past the budget;
    ///   [`Stop::PartialFixpoint`] when a fixpoint without evidence stands at
    ///   its gate — applied to a canonical argument, under a bind or under a
    ///   projection; [`ReplayRefusal::Unreadable`] on a dangling computation or
    ///   a value inspected by its reduction; a value root itself is left for
    ///   shape checking.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Budget`], [`Stop::PartialFixpoint`] or [`Stop::Refused`].
    ///
    /// # Termination
    /// - reason: the `loop` below, which takes one step per iteration, and the
    ///   `while let` loop rebuilding the head path, not recursion.
    /// - measure: the budget left, which every iteration charges; then the
    ///   frames left.
    ///
    /// # Adequacy
    /// - hypothesis: L3: beta, force, bind, and injection reductions settle
    ///   before decisions; a reduced head retains application and bind frames,
    ///   while a self-application exhausts a finite budget. These observations
    ///   bound weak-head behavior, not normalization completeness.
    /// - witness: `replay::tests::the_replay_reduces_before_it_reads_a_decision`
    /// - witness: `replay::tests::reduced_heads_retain_application_and_bind_frames`
    /// - witness: `replay::tests::an_engine_decline_and_an_exhausted_budget_decline`
    /// - witness: `recursive_data::recursive_data::a_fixpoint_computes_at_a_constructor_and_replays`
    /// - witness: `recursive_data::recursive_data::a_partial_fixpoint_declines_at_its_gate`
    /// - witness: `path_universe::tests::transport_computes`
    /// - witness: `path_universe::tests::refl_collapses`
    /// - witness: `replay::tests::native_list_fold_reduces_without_capturing_outer_variables`
    /// - witness: `replay::tests::a_projection_runs_its_side_of_a_pairing`
    #[spec(
        captures: before = self.spent,
        ensures: |ret| match term {
            Term::Value(_) => ret == Ok(term) && self.spent == before,
            Term::Computation(_) => match ret {
                Ok(Term::Computation(computation)) => self.spent > before && self.spent <= self.budget && self.arena.computation(computation).is_some(),
                Err(Stop::Budget) => self.spent >= self.budget,
                Err(Stop::Refused(_) | Stop::PartialFixpoint) => true,
                Ok(Term::Value(_)) => false,
            },
        },
    )]
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
            // An elimination meeting a returned endpoint runs the endpoint's
            // computation and eliminates what it returns: `E[c] ⇝ c to x. E[x]`.
            if let Some(
                &(Computation::DataCase {
                    scrutinee: inspected,
                    ..
                }
                | Computation::Case {
                    scrutinee: inspected,
                    ..
                }
                | Computation::SigmaSplit {
                    scrutinee: inspected,
                    ..
                }
                | Computation::ListFold {
                    list: inspected, ..
                }
                | Computation::RecordProjection(inspected, _)
                | Computation::TupleProjection(inspected, _)
                | Computation::Force(inspected)),
            ) = self.arena.computation(focus)
                && let Some(&Value::Returned(returned)) = self.arena.value(inspected)
            {
                focus = self.bind_returned(focus, returned)?;
                progress = Progress::Reduced;
                continue;
            }
            match self.arena.computation(focus) {
                | Some(&Computation::DataCase {
                    scrutinee,
                    ref branches,
                    ..
                }) => match self.arena.value(scrutinee) {
                    | Some(&Value::Constructor {
                        tag, ref fields, ..
                    }) => {
                        let branch = *branches.get(usize::from(tag)).ok_or_else(unreadable)?;
                        let field_count = fields.len();
                        focus = branch;
                        for position in 0 .. field_count {
                            self.charge()?;
                            let Some(matched_native_node) = self.arena.value(scrutinee)
                            else {
                                return Err(unreadable());
                            };
                            let Value::Constructor { ref fields, .. } = *matched_native_node
                            else {
                                return Err(unreadable());
                            };
                            let field = *fields.get(position).ok_or_else(unreadable)?;
                            focus = self.arena.computation_application(focus, field);
                        }
                        progress = Progress::Reduced;
                    },
                    | Some(_) => break,
                    | None => return Err(unreadable()),
                },
                // A dependent split of a pair enters its body with the two
                // components for its two binders, the outer binder first.
                | Some(&Computation::SigmaSplit {
                    scrutinee, body, ..
                }) => match self.arena.value(scrutinee).map(Value::components) {
                    | Some(Some(&[first, second])) => {
                        let opened = crate::rewrite::substitute_fold_head(
                            self.arena,
                            &mut self.table,
                            &mut self.memo,
                            body,
                            first,
                        );
                        focus = self.instantiate(opened, second);
                        progress = Progress::Reduced;
                    },
                    | Some(None) => break,
                    | Some(Some(_)) | None => return Err(unreadable()),
                },
                | Some(&Computation::RecordProjection(record, ref label)) => {
                    match self.arena.value(record) {
                        | Some(&Value::Record(ref fields)) => {
                            let value = *fields.get(label).ok_or_else(unreadable)?;
                            focus = self.arena.computation_return(value);
                            progress = Progress::Reduced;
                        },
                        | Some(_) => break,
                        | None => return Err(unreadable()),
                    }
                },
                | Some(&Computation::TupleProjection(tuple, component)) => {
                    match self.arena.value(tuple).map(Value::components) {
                        | Some(Some(components)) => {
                            let value = *components
                                .get(usize::from(component))
                                .ok_or_else(unreadable)?;
                            focus = self.arena.computation_return(value);
                            progress = Progress::Reduced;
                        },
                        | Some(None) => break,
                        | None => return Err(unreadable()),
                    }
                },
                | Some(&Computation::ListFold {
                    element,
                    result,
                    list,
                    on_nil,
                    on_cons,
                }) => match self.arena.value(list) {
                    | Some(&Value::ListNil) => {
                        focus = on_nil;
                        progress = Progress::Reduced;
                    },
                    | Some(&Value::ListCons(head, tail)) => {
                        let branch = crate::rewrite::substitute_fold_head(
                            self.arena,
                            &mut self.table,
                            &mut self.memo,
                            on_cons,
                            head,
                        );
                        frames.push(Frame::Bind(branch));
                        focus = self
                            .arena
                            .computation_list_fold(element, result, tail, on_nil, on_cons);
                        progress = Progress::Reduced;
                    },
                    | Some(_) => break,
                    | None => return Err(unreadable()),
                },
                | Some(&Computation::Transport(path, value)) => {
                    match crate::path_universe::beta(self.arena, crate::path_universe::Transport {
                        path,
                        value,
                    })
                    .map_err(|_unreadable_term| unreadable())?
                    {
                        | crate::path_universe::Reduction::Reduced(reduct) => {
                            focus = reduct;
                            progress = Progress::Reduced;
                        },
                        | crate::path_universe::Reduction::Stuck => break,
                    }
                },
                | Some(&Computation::PathTransport {
                    motive,
                    path,
                    value,
                }) => {
                    let term = crate::element_identity::ElementTransport {
                        motive,
                        path,
                        value,
                    };
                    match crate::element_identity::transport_beta(
                        self.arena,
                        &mut self.table,
                        &mut self.memo,
                        term,
                    )
                    .map_err(|_unreadable_term| unreadable())?
                    {
                        | crate::path_universe::Reduction::Reduced(reduct) => {
                            focus = reduct;
                            progress = Progress::Reduced;
                        },
                        | crate::path_universe::Reduction::Stuck => break,
                    }
                },
                | Some(&Computation::TelescopeTransport {
                    motive,
                    path,
                    start,
                    over,
                    value,
                }) => {
                    let term = crate::element_identity::TelescopeStep {
                        motive,
                        path,
                        start,
                        over,
                        value,
                    };
                    match crate::element_identity::telescope_beta(
                        self.arena,
                        &mut self.table,
                        &mut self.memo,
                        term,
                    )
                    .map_err(|_unreadable_term| unreadable())?
                    {
                        | crate::path_universe::Reduction::Reduced(reduct) => {
                            focus = reduct;
                            progress = Progress::Reduced;
                        },
                        | crate::path_universe::Reduction::Stuck => break,
                    }
                },
                | Some(&Computation::Ride {
                    motive,
                    flow,
                    value,
                }) => {
                    let term = crate::flow_universe::reduce::RideStep {
                        motive,
                        flow,
                        value,
                    };
                    match crate::flow_universe::reduce::ride_beta(
                        self.arena,
                        &mut self.table,
                        &mut self.memo,
                        term,
                    )
                    .map_err(|_unreadable_term| unreadable())?
                    {
                        | crate::path_universe::Reduction::Reduced(reduct) => {
                            focus = reduct;
                            progress = Progress::Reduced;
                        },
                        | crate::path_universe::Reduction::Stuck => break,
                    }
                },
                | Some(&Computation::TelescopeRide {
                    motive,
                    flow,
                    over,
                    value,
                    ..
                }) => {
                    let term = crate::flow_universe::reduce::TelescopeRideStep {
                        motive,
                        flow,
                        over,
                        value,
                    };
                    match crate::flow_universe::reduce::telescope_ride_beta(
                        self.arena,
                        &mut self.table,
                        &mut self.memo,
                        term,
                    )
                    .map_err(|_unreadable_term| unreadable())?
                    {
                        | crate::path_universe::Reduction::Reduced(reduct) => {
                            focus = reduct;
                            progress = Progress::Reduced;
                        },
                        | crate::path_universe::Reduction::Stuck => break,
                    }
                },
                | Some(&Computation::RelatedApplication {
                    path,
                    left,
                    right,
                    body,
                    ..
                }) => {
                    let term = crate::element_identity::RelatedStep {
                        path,
                        left,
                        right,
                        body,
                    };
                    match crate::element_identity::related_beta(
                        self.arena,
                        &mut self.table,
                        &mut self.memo,
                        term,
                    )
                    .map_err(|_unreadable_term| unreadable())?
                    {
                        | crate::path_universe::Reduction::Reduced(reduct) => {
                            focus = reduct;
                            progress = Progress::Reduced;
                        },
                        | crate::path_universe::Reduction::Stuck => break,
                    }
                },
                | Some(&Computation::Application(head, argument)) => {
                    frames.push(Frame::Apply(argument));
                    focus = head;
                },
                | Some(&Computation::Bind(bound, body)) => {
                    frames.push(Frame::Bind(body));
                    focus = bound;
                },
                | Some(&Computation::Project(side, pair)) => {
                    frames.push(Frame::Project(side));
                    focus = pair;
                },
                // A projection of a lazy pairing runs the side it names; a
                // pairing under no projection is in weak head form.
                | Some(&Computation::With(first, second)) => match frames.last() {
                    | Some(&Frame::Project(side)) => {
                        frames.pop();
                        focus = match side {
                            | Side::Left => first,
                            | Side::Right => second,
                        };
                        progress = Progress::Reduced;
                    },
                    | Some(&(Frame::Apply(_) | Frame::Bind(_))) | None => break,
                },
                | Some(&Computation::Force(value)) => match self.arena.value(value) {
                    | Some(&Value::Thunk(body)) => {
                        focus = body;
                        progress = Progress::Reduced;
                    },
                    | Some(_) => break,
                    | None => return Err(unreadable()),
                },
                // A case over an injection selects the branch its summand
                // names; the empty sum's elimination has none and stays stuck.
                | Some(&Computation::Case {
                    scrutinee,
                    ref branches,
                }) => match self.arena.value(scrutinee) {
                    | Some(&Value::Injection(summand, payload)) => {
                        let Some(&branch) = branches.get(usize::from(summand))
                        else {
                            break;
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
                    | Some(&(Frame::Bind(_) | Frame::Project(_))) | None => break,
                },
                // A fixpoint unfolds at its gate: applied to a canonical
                // argument, the `<` direction, or under a bind or a projection
                // observing its result, the `>` direction. Conversion unfolds
                // only a fixpoint whose structural-descent evidence replayed,
                // and only at a constructor; at a partial fixpoint's gate it
                // declines rather than refutes.
                | Some(&Computation::Fixpoint { body, evidence }) => {
                    let gate = match frames.last() {
                        | Some(&Frame::Apply(argument)) => match self.arena.value(argument) {
                            | Some(&Value::Constructor { .. }) => Gate::Constructor,
                            | Some(
                                &(Value::Variable(_)
                                | Value::Constant(_)
                                | Value::StaticApplication(..)),
                            ) => Gate::Shut,
                            | Some(_) => Gate::Canonical,
                            | None => return Err(unreadable()),
                        },
                        | Some(&(Frame::Bind(_) | Frame::Project(_))) => Gate::Observed,
                        | None => Gate::Shut,
                    };
                    match (evidence, gate) {
                        | (FixpointEvidence::StructuralDescent, Gate::Constructor) => {
                            let recursive = self.arena.value_thunk(focus);
                            focus = self.instantiate(body, recursive);
                            progress = Progress::Reduced;
                        },
                        | (
                            FixpointEvidence::Partial,
                            Gate::Constructor | Gate::Canonical | Gate::Observed,
                        ) => return Err(Stop::PartialFixpoint),
                        | (
                            FixpointEvidence::StructuralDescent,
                            Gate::Canonical | Gate::Observed | Gate::Shut,
                        )
                        | (FixpointEvidence::Partial, Gate::Shut) => break,
                    }
                },
                | Some(&Computation::Return(value)) => match frames.last() {
                    | Some(&Frame::Bind(body)) => {
                        frames.pop();
                        focus = self.instantiate(body, value);
                        progress = Progress::Reduced;
                    },
                    | Some(&(Frame::Apply(_) | Frame::Project(_))) | None => break,
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

    /// `elimination`, whose inspected value is a returned endpoint, as the
    /// bind running `returned` and eliminating what it returns.
    ///
    /// # Specification
    /// - requires: `elimination` is a force, a case, a data case, a dependent
    ///   split, a list fold or a projection, and `returned` the computation of
    ///   the returned endpoint it inspects.
    /// - ensures: `returned to x. E[x]`, where `E` is the elimination shifted
    ///   past the new binder and `x` stands where the endpoint stood.
    /// - provides: the elimination rule of a returned endpoint: a pure
    ///   returner's value is the one its computation binds.
    /// - fails: [`ReplayRefusal::Unreadable`] when `elimination` is no such
    ///   form.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Refused`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a force and a case over a returned endpoint reduce to
    ///   what forcing or casing its returned value gives, and a stuck one stays
    ///   the bind.
    /// - witness: `element_identity::tests::a_returned_endpoint_replays_as_its_computation`
    #[spec(ensures: |ret| match ret {
        Ok(bind) => matches!(self.arena.computation(bind), Some(&Computation::Bind(bound, _)) if bound == returned),
        Err(_) => true,
    })]
    fn bind_returned(
        &mut self,
        elimination: ComputationId,
        returned: ComputationId,
    ) -> Result<ComputationId, Stop>
    {
        let shifted = shift_computation(
            self.arena,
            &mut self.table,
            &mut self.memo,
            elimination,
            BinderDepth::NONE,
            BinderDepth::NONE.deeper(),
        );
        let bound = self.arena.value_variable(DeBruijnIndex::from(0_u32));
        let continuation = match self.arena.computation(shifted) {
            | Some(&Computation::Force(_)) => self.arena.computation_force(bound),
            | Some(&Computation::RecordProjection(_, ref label)) => {
                let label = label.clone();
                self.arena.computation_record_projection(bound, label)
            },
            | Some(&Computation::TupleProjection(_, component)) => {
                self.arena.computation_tuple_projection(bound, component)
            },
            | Some(&Computation::Case { ref branches, .. }) => {
                let branches = branches.clone();
                self.arena.computation_case(bound, &branches)
            },
            | Some(&Computation::DataCase {
                motive,
                ref branches,
                ..
            }) => {
                let branches = branches.clone();
                self.arena.computation_data_case(bound, motive, branches)
            },
            | Some(&Computation::SigmaSplit { motive, body, .. }) => {
                self.arena.computation_sigma_split(bound, motive, body)
            },
            | Some(&Computation::ListFold {
                element,
                result,
                on_nil,
                on_cons,
                ..
            }) => self
                .arena
                .computation_list_fold(element, result, bound, on_nil, on_cons),
            | _ => return Err(unreadable()),
        };
        Ok(self.arena.computation_bind(returned, continuation))
    }

    /// The normal form of `value` as an endpoint: a returned endpoint is what
    /// its computation returns, normalized again, and any other value itself.
    ///
    /// The computation reduces by [`Self::whnf`]'s search-free steps; at a
    /// stuck head naming a definition it takes the δ-step [`Self::unfold_term`]
    /// fires, the one step the head admits. This is the kernel's own
    /// evaluator, not a conversion: the normal form goes on to
    /// [`convert_values`]. A computation that reaches no `return` stays a
    /// returned endpoint, over what it reduced to.
    ///
    /// # Specification
    /// - requires: `value` lives in the arena.
    /// - ensures: the first value that is no returned endpoint along the chain
    ///   of returned values, or a returned endpoint whose computation is stuck
    ///   at no defined head; `value` itself when nothing reduced.
    /// - provides: the normal form [`read_endpoints`] converts.
    /// - fails: [`Stop::Budget`] past the budget; [`Stop::PartialFixpoint`] at
    ///   a partial fixpoint's gate; [`ReplayRefusal::Unreadable`] on a dangling
    ///   node or a definition that does not unfold.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails`.
    ///
    /// # Termination
    /// - reason: the outer `while let` over the chain of returned values and
    ///   the inner `loop` over one computation's reduction, not recursion.
    /// - measure: the budget left, which every inner iteration charges, and the
    ///   outer loop advances only after an inner one.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an endpoint returning through a definition reads as
    ///   its value, a stuck endpoint reads as itself, and a definition the
    ///   reading may not unfold leaves the endpoint apart from its value.
    /// - witness: `element_identity::tests::a_returned_endpoint_reads_at_a_mode_switch`
    /// - witness: `element_identity::tests::a_certificate_with_a_returned_endpoint_decodes_checks_and_replays`
    #[spec(ensures: |ret| match ret {
        Ok(read) => self.arena.value(read).is_some(),
        Err(Stop::Budget) => self.spent >= self.budget,
        Err(_) => true,
    })]
    fn normalize_returned(
        &mut self,
        value: ValueId,
    ) -> Result<ValueId, Stop>
    {
        let mut value = value;
        while let Some(&Value::Returned(computation)) = self.arena.value(value) {
            let mut term = Term::Computation(computation);
            loop {
                self.charge()?;
                term = self.whnf(term)?;
                let Term::Computation(reduced) = term
                else {
                    return Err(unreadable());
                };
                if let Some(&Computation::Return(returned)) = self.arena.computation(reduced) {
                    value = returned;
                    break;
                }
                if let Ok(Shape::Neutral(Head::Constant(constant, Status::Defined), _)) =
                    self.shape(term, &Frozen::default(), ConversionSide::Left)
                {
                    term = self.unfold_term(term, constant)?;
                    continue;
                }
                return Ok(if reduced == computation {
                    value
                }
                else {
                    self.arena.value_returned(reduced)
                });
            }
        }
        Ok(value)
    }

    /// `computation` under `frame`.
    ///
    /// # Specification
    /// - requires: the computation and the frame children live in the arena.
    /// - ensures: an application keeps the computation as its head and the
    ///   frame argument; a bind keeps it as the bound term and the frame body;
    ///   a projection keeps it as the projected pairing and the frame side.
    /// - provides: reconstruction of the unreduced outer elimination path.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3: a beta-reduced head under an application, a bind or a
    ///   projection remains convertible to the explicitly retained frame;
    ///   dropping or exchanging the frame changes that verdict.
    /// - witness: `replay::tests::reduced_heads_retain_application_and_bind_frames`
    /// - witness: `replay::tests::a_projection_runs_its_side_of_a_pairing`
    #[spec(ensures: |ret| self.arena.computation(ret) == Some(&match frame {
        Frame::Apply(argument) => Computation::Application(computation, argument),
        Frame::Bind(body) => Computation::Bind(computation, body),
        Frame::Project(side) => Computation::Project(side, computation),
    }))]
    fn wrap(
        &mut self,
        computation: ComputationId,
        frame: Frame,
    ) -> ComputationId
    {
        match frame {
            | Frame::Apply(argument) => self.arena.computation_application(computation, argument),
            | Frame::Bind(body) => self.arena.computation_bind(computation, body),
            | Frame::Project(side) => self.arena.computation_project(side, computation),
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
    ///
    /// # Adequacy
    /// - hypothesis: L3: the same equal and rigidly separated pairs are
    ///   replayed under both claims, distinguishing acceptance from a
    ///   contradiction at the consumed decision.
    /// - witness: `replay::tests::a_compared_pair_closes_on_alpha_equality_or_rigid_separation`
    #[spec(ensures: |ret| ret == if owed == verdict {
        Ok(())
    } else {
        Err(Stop::Refused(ReplayRefusal::Contradicted { at: self.at() }))
    })]
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
    /// - ensures: an available step is charged exactly once; an exhausted
    ///   budget is refused without changing the successful-step count.
    /// - provides: the replay's single bound.
    /// - fails: [`Stop::Budget`] when no step remains, including at the counter
    ///   ceiling.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Stop::Budget`].
    ///
    /// # Adequacy
    /// - hypothesis: L3: zero, one, and maximum budgets distinguish the last
    ///   admitted step from every subsequent refusal; this bounds the counter
    ///   transition, not the work within a replay step.
    /// - witness: `replay::tests::budget_exhaustion_survives_the_counter_ceiling`
    #[spec(
        captures: before = self.spent,
        ensures: |ret| if before < self.budget {
            ret == Ok(()) && self.spent == before.saturating_add(1)
        } else {
            ret == Err(Stop::Budget) && self.spent == before
        },
    )]
    fn charge(&mut self) -> Result<(), Stop>
    {
        if self.spent >= self.budget {
            return Err(Stop::Budget);
        }
        self.spent = self.spent.saturating_add(1);
        Ok(())
    }

    /// The next decision, unread.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the next decision is observed without advancing its position.
    /// - provides: lookahead shared by dispatch and refusal attribution.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3: repeated lookahead preserves both a pending decision
    ///   and the trace end; the reported position cannot wrap.
    /// - witness: `replay::tests::trace_consumption_preserves_the_end_and_position_ceiling`
    #[spec(
        captures: before = self.position,
        ensures: |ret| self.position == before && match ret {
            Next::End => self.trace.size_hint() == (0, Some(0)),
            Next::Decision(_) => self.trace.size_hint().0 > 0,
        },
    )]
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
    /// - requires: nothing.
    /// - ensures: a present decision advances the position with saturation; an
    ///   exhausted trace leaves the position unchanged.
    /// - provides: the consumed-prefix index carried by refusals.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3: consuming the last decision and then the end separates
    ///   advancement from exhaustion, including at the position ceiling.
    /// - witness: `replay::tests::trace_consumption_preserves_the_end_and_position_ceiling`
    #[spec(
        captures: before = self.position,
        ensures: self.position >= before && self.position <= before.saturating_add(1),
    )]
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
    /// - requires: nothing.
    /// - ensures: an available decision is inapplicable at this position; an
    ///   absent decision is exhausted rather than attributed to a slot.
    /// - provides: the distinction between a wrong decision and a missing one.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3: a missing eta decision and a wrong-side eta decision
    ///   produce different refusals after the same force prefix.
    /// - witness: `replay::tests::eta_and_force_open_the_suspended_sides`
    #[spec(ensures: |ret| match (next, ret) {
        (Next::Decision(_), Stop::Refused(ReplayRefusal::Inapplicable { at })) => at.0 == self.position,
        (Next::End, Stop::Refused(ReplayRefusal::Exhausted)) => true,
        _ => false,
    })]
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
///   for a lambda against a neutral; [`Rule::ProductEta`] for a lazy pairing
///   against a neutral; else [`Rule::Structural`].
/// - provides: the rule table's dispatch, in the engine's order.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3: the finite product of former, thunk, lambda, lazy pairing,
///   return, and variable or constant head statuses observes constant priority,
///   force priority, both eta sides, and structural fallback independently of
///   term depth.
/// - witness: `replay::tests::rule_dispatch_respects_constant_priority_and_eta_side`
#[spec(ensures: |ret| {
    let defined = [left, right].iter().any(|shape| matches!(shape, &&Shape::Neutral(Head::Constant(_, Status::Defined), _)));
    let force = matches!((left, right), (&Shape::Thunk(_), &(Shape::Thunk(_) | Shape::Neutral(..))) | (&Shape::Neutral(..), &Shape::Thunk(_)));
    let eta_left = matches!((left, right), (&Shape::Neutral(..), &Shape::Lambda(_)));
    let eta_right = matches!((left, right), (&Shape::Lambda(_), &Shape::Neutral(..)));
    let pairing_left = matches!((left, right), (&Shape::Neutral(..), &Shape::With(..)));
    let pairing_right = matches!((left, right), (&Shape::With(..), &Shape::Neutral(..)));
    match ret {
        Rule::Constants => defined,
        Rule::Force => !defined && force,
        Rule::Eta(ConversionSide::Left) => !defined && !force && eta_left,
        Rule::Eta(ConversionSide::Right) => !defined && !force && eta_right,
        Rule::ProductEta(ConversionSide::Left) => !defined && pairing_left,
        Rule::ProductEta(ConversionSide::Right) => !defined && pairing_right,
        Rule::Structural => !defined && !force && !eta_left && !eta_right && !pairing_left && !pairing_right,
    }
})]
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
        | (&Shape::With(..), &Shape::Neutral(..)) => Rule::ProductEta(ConversionSide::Right),
        | (&Shape::Neutral(..), &Shape::With(..)) => Rule::ProductEta(ConversionSide::Left),
        | (
            &(Shape::Former
            | Shape::Thunk(_)
            | Shape::Lambda(_)
            | Shape::With(..)
            | Shape::Fixpoint(_)
            | Shape::Return(_)
            | Shape::Neutral(..)),
            _,
        ) => Rule::Structural,
    }
}

/// The commuting conversion of `F` two shapes still owe.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`BindRule::Normal`] unless both shapes are neutral over one head
///   no δ-rule can unfold; otherwise [`BindRule::Reassociate`] naming the first
///   side whose spine stacks two binds in a row, the left before the right;
///   else [`BindRule::ReturnEta`] naming the side whose spine is one
///   elimination shorter than the other's when the other's ends in a bind; else
///   [`BindRule::Normal`].
/// - provides: the order both the engine and the replay normalize a pair's
///   binds in, so the trace names each rewrite where the replay meets it.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3: a stacked pair on either side, a spine one bind short on
///   either side, and a pair already normal each select a different rule;
///   reading the right side first or expanding a spine more than one bind short
///   changes the trace the engine's derivation must name.
/// - witness: `replay::tests::the_laws_of_bind_replay_by_name`
#[spec(ensures: |ret| {
    let stacked = |spine: &[Elimination]| spine.windows(2).any(|pair| matches!(pair, &[Elimination::Bind(_), Elimination::Bind(_)]));
    let ends = |spine: &[Elimination]| matches!(spine.last(), Some(&Elimination::Bind(_)));
    match (left, right) {
        (&Shape::Neutral(one, ref left_spine), &Shape::Neutral(other, ref right_spine))
            if one == other && !matches!(one, Head::Constant(_, Status::Defined)) =>
            ret == if stacked(left_spine) {
                BindRule::Reassociate(ConversionSide::Left)
            } else if stacked(right_spine) {
                BindRule::Reassociate(ConversionSide::Right)
            } else if left_spine.len().checked_add(1) == Some(right_spine.len()) && ends(right_spine) {
                BindRule::ReturnEta(ConversionSide::Left)
            } else if right_spine.len().checked_add(1) == Some(left_spine.len()) && ends(left_spine) {
                BindRule::ReturnEta(ConversionSide::Right)
            } else {
                BindRule::Normal
            },
        _ => ret == BindRule::Normal,
    }
})]
fn bind_rule(
    left: &Shape,
    right: &Shape,
) -> BindRule
{
    let (&Shape::Neutral(one, ref left_spine), &Shape::Neutral(other, ref right_spine)) =
        (left, right)
    else {
        return BindRule::Normal;
    };
    if one != other || matches!(one, Head::Constant(_, Status::Defined)) {
        return BindRule::Normal;
    }
    let stacked = |spine: &[Elimination]| {
        spine
            .windows(2)
            .any(|pair| matches!(pair, &[Elimination::Bind(_), Elimination::Bind(_)]))
    };
    let ends = |spine: &[Elimination]| matches!(spine.last(), Some(&Elimination::Bind(_)));
    if stacked(left_spine) {
        return BindRule::Reassociate(ConversionSide::Left);
    }
    if stacked(right_spine) {
        return BindRule::Reassociate(ConversionSide::Right);
    }
    if left_spine.len().checked_add(1) == Some(right_spine.len()) && ends(right_spine) {
        return BindRule::ReturnEta(ConversionSide::Left);
    }
    if right_spine.len().checked_add(1) == Some(left_spine.len()) && ends(left_spine) {
        return BindRule::ReturnEta(ConversionSide::Right);
    }
    BindRule::Normal
}

/// The premises two spines decompose into, innermost elimination first.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a refuting leaf when the spines differ in length or in any
///   elimination's kind; else an application's or a static application's
///   arguments, a bind's continuations, a sum case's two branches and a
///   dependent split's bodies, in spine order. A native data case first
///   compares its quoted motive, then its ordinary branch functions; a ride
///   compares its quoted motive, then its value; a force, a matching record
///   projection or a projection of one lazy-product side contributes none.
/// - provides: the decomposition of two neutrals over one head.
/// - fails: unreadable native metadata when a retained source is missing or
///   malformed.
/// - panics: none.
///
/// # Errors
/// Returns an unreadable replay refusal for missing or ill-shaped native
/// sources.
///
/// # Adequacy
/// - hypothesis: L3: case branches followed by an application distinguish
///   subgoal order; two rides along one flow refute at their values' subgoal,
///   not their motives'; unequal spine lengths and application-versus-bind
///   kinds refute without a decision; empty spines close positively. The
///   fixtures do not enumerate all mixed spines.
/// - witness: `replay::tests::neutral_spines_keep_subgoal_order_and_reject_kind_mismatches`
/// - witness: `replay::tests::a_refutation_follows_its_negative_subgoal`
/// - witness: `path_universe::tests::refl_collapses`
/// - witness: `replay::tests::a_lazy_pairing_meets_a_neutral_by_its_projections`
/// - witness: `replay::tests::a_ride_unfolds_its_flow_where_the_dialogue_names_it`
#[spec(ensures: |ret| {
    let compatible = left.len() == right.len() && left.iter().zip(right).all(|(one, other)| match (*one,*other) {
        (Elimination::RecordProjection(a),Elimination::RecordProjection(b)) => matches!((arena.computation(a),arena.computation(b)), (Some(Computation::RecordProjection(_,a)),Some(Computation::RecordProjection(_,b))) if a == b),
        (Elimination::TupleProjection(a),Elimination::TupleProjection(b)) => matches!((arena.computation(a),arena.computation(b)), (Some(Computation::TupleProjection(_,a)),Some(Computation::TupleProjection(_,b))) if a == b),
        (Elimination::DataCase(a),Elimination::DataCase(b)) => matches!((arena.computation(a),arena.computation(b)), (Some(Computation::DataCase{branches:a,..}),Some(Computation::DataCase{branches:b,..})) if a.len() == b.len()),
        (Elimination::Case(a),Elimination::Case(b)) => {
            let width = |case: ComputationId| match *arena.computation(case)? { Computation::Case { ref branches, .. } => Some(branches.len()), _ => None };
            width(a).is_some() && width(a) == width(b)
        },
        (Elimination::Project(a), Elimination::Project(b)) => a == b,
        _ => core::mem::discriminant(one) == core::mem::discriminant(other),
    });
    match ret {
Err(Stop::Refused(ReplayRefusal::Unreadable)) => true,
Err(_) => false,
Ok(Structure::Leaf(Expect::NotConvertible)) => !compatible,
Ok(Structure::Leaf(Expect::Convertible)) => compatible && left.iter().all(|one| matches!(*one, Elimination::Force | Elimination::RecordProjection(_) | Elimination::TupleProjection(_) | Elimination::Project(_)) || matches!(*one, Elimination::Case(case) if arena.computation(case).is_some_and(|node| matches!(*node, Computation::Case { ref branches, .. } if branches.is_empty())))),
Ok(Structure::Premises(ref premises)) => compatible && !premises.is_empty() && {
            let mut pending = premises.iter();
            let ordered = left.iter().zip(right).all(|(one, other)| match (*one, *other) {
                (Elimination::Force, Elimination::Force) | (Elimination::RecordProjection(_),Elimination::RecordProjection(_)) | (Elimination::TupleProjection(_),Elimination::TupleProjection(_)) | (Elimination::Project(_), Elimination::Project(_)) => true,
                (Elimination::Case(a),Elimination::Case(b)) => {
if let Some(left_node) = arena.computation(a) && let Computation::Case{branches:ref a,..} = *left_node && let Some(right_node) = arena.computation(b) && let Computation::Case{branches:ref b,..} = *right_node { a.iter().zip(b.iter()).all(|(a,b)| pending.next() == Some(&Premise::computations(*a,*b))) }
 else { false }
},
                (Elimination::DataCase(a),Elimination::DataCase(b)) => { let (matched_left_value, matched_right_value) = (arena.computation(a),arena.computation(b));
if let Some(matched_left_node) = matched_left_value && let Computation::DataCase{motive:ref a_motive,branches:ref a,..} = *matched_left_node && let Some(matched_right_node) = matched_right_value && let Computation::DataCase{motive:ref b_motive,branches:ref b,..} = *matched_right_node { pending.next().is_some_and(|premise| matches!((premise.left,premise.right),(Term::Value(left),Term::Value(right)) if arena.value(left) == Some(&Value::QuoteComputation(*a_motive)) && arena.value(right) == Some(&Value::QuoteComputation(*b_motive)))) && a.iter().zip(b).all(|(a,b)| pending.next() == Some(&Premise::computations(*a,*b))) }
 else { false }
},
                (Elimination::Ride(a), Elimination::Ride(b)) => if let (Some(&Computation::Ride { motive: a_motive, value: a_value, .. }), Some(&Computation::Ride { motive: b_motive, value: b_value, .. })) = (arena.computation(a), arena.computation(b)) {
                    pending.next().is_some_and(|premise| matches!((premise.left, premise.right), (Term::Value(left), Term::Value(right)) if arena.value(left) == Some(&Value::Quote(a_motive)) && arena.value(right) == Some(&Value::Quote(b_motive))))
                        && pending.next() == Some(&Premise::values(a_value, b_value))
                } else { false },
                (Elimination::Transport(one), Elimination::Transport(other)) | (Elimination::ProductTransport(one), Elimination::ProductTransport(other)) | (Elimination::Apply(one), Elimination::Apply(other)) | (Elimination::StaticApply(one), Elimination::StaticApply(other)) => pending.next() == Some(&Premise::values(one, other)),
                (Elimination::Bind(one), Elimination::Bind(other)) | (Elimination::Fixpoint(one), Elimination::Fixpoint(other)) => pending.next() == Some(&Premise::computations(one, other)),
                (Elimination::SigmaSplit(a), Elimination::SigmaSplit(b)) => matches!((arena.computation(a), arena.computation(b)), (Some(&Computation::SigmaSplit { body: one, .. }), Some(&Computation::SigmaSplit { body: other, .. })) if pending.next() == Some(&Premise::computations(one, other))),
                (Elimination::ListFold(one_left, one_right), Elimination::ListFold(other_left, other_right)) =>
                    pending.next() == Some(&Premise::computations(one_left, other_left)) && pending.next() == Some(&Premise::computations(one_right, other_right)),
                _ => false,
            });
            ordered && pending.next().is_none()
        },
}
})]
fn spines(
    arena: &mut TermArena,
    left: &[Elimination],
    right: &[Elimination],
) -> Result<Structure, Stop>
{
    if left.len() != right.len() {
        return Ok(Structure::Leaf(Expect::NotConvertible));
    }
    let mut premises = Vec::new();
    for (&one, &other) in left.iter().zip(right) {
        match (one, other) {
            | (Elimination::DataCase(a_case), Elimination::DataCase(b_case)) => {
                let (Some(left_node), Some(right_node)) =
                    (arena.computation(a_case), arena.computation(b_case))
                else {
                    return Err(unreadable());
                };
                let Computation::DataCase {
                    motive: ref a_motive,
                    branches: ref a,
                    ..
                } = *left_node
                else {
                    return Err(unreadable());
                };
                let Computation::DataCase {
                    motive: ref b_motive,
                    branches: ref b,
                    ..
                } = *right_node
                else {
                    return Err(unreadable());
                };
                if a.len() != b.len() {
                    return Ok(Structure::Leaf(Expect::NotConvertible));
                }
                let (a_motive, b_motive) = (*a_motive, *b_motive);
                let a_quote = arena.value_quote_computation(a_motive);
                let b_quote = arena.value_quote_computation(b_motive);
                premises.push(Premise::values(a_quote, b_quote));
                let (Some(left_node), Some(right_node)) =
                    (arena.computation(a_case), arena.computation(b_case))
                else {
                    return Err(unreadable());
                };
                let Computation::DataCase {
                    branches: ref a, ..
                } = *left_node
                else {
                    return Err(unreadable());
                };
                let Computation::DataCase {
                    branches: ref b, ..
                } = *right_node
                else {
                    return Err(unreadable());
                };
                premises.extend(a.iter().zip(b).map(|(a, b)| Premise::computations(*a, *b)));
            },
            | (Elimination::RecordProjection(a), Elimination::RecordProjection(b)) => {
                let (Some(left_node), Some(right_node)) =
                    (arena.computation(a), arena.computation(b))
                else {
                    return Err(unreadable());
                };
                let Computation::RecordProjection(_, ref a) = *left_node
                else {
                    return Err(unreadable());
                };
                let Computation::RecordProjection(_, ref b) = *right_node
                else {
                    return Err(unreadable());
                };
                if a != b {
                    return Ok(Structure::Leaf(Expect::NotConvertible));
                }
            },
            | (Elimination::TupleProjection(a), Elimination::TupleProjection(b)) => {
                let (Some(left_node), Some(right_node)) =
                    (arena.computation(a), arena.computation(b))
                else {
                    return Err(unreadable());
                };
                let Computation::TupleProjection(_, a) = *left_node
                else {
                    return Err(unreadable());
                };
                let Computation::TupleProjection(_, b) = *right_node
                else {
                    return Err(unreadable());
                };
                if a != b {
                    return Ok(Structure::Leaf(Expect::NotConvertible));
                }
            },
            // Two sum cases of one arity compare branch by branch; the empty
            // sum's elimination contributes nothing.
            | (Elimination::Case(a_case), Elimination::Case(b_case)) => {
                let (Some(left_node), Some(right_node)) =
                    (arena.computation(a_case), arena.computation(b_case))
                else {
                    return Err(unreadable());
                };
                let Computation::Case {
                    branches: ref a, ..
                } = *left_node
                else {
                    return Err(unreadable());
                };
                let Computation::Case {
                    branches: ref b, ..
                } = *right_node
                else {
                    return Err(unreadable());
                };
                if a.len() != b.len() {
                    return Ok(Structure::Leaf(Expect::NotConvertible));
                }
                premises.extend(a.iter().zip(b).map(|(a, b)| Premise::computations(*a, *b)));
            },
            | (Elimination::Force, Elimination::Force) => {},
            | (Elimination::Transport(a), Elimination::Transport(b))
            | (Elimination::ProductTransport(a), Elimination::ProductTransport(b))
            | (Elimination::Apply(a), Elimination::Apply(b))
            | (Elimination::StaticApply(a), Elimination::StaticApply(b)) => {
                premises.push(Premise::values(a, b));
            },
            // Two rides along one neutral flow compare their motives as
            // codes, as the engine's spines compare them, then their values.
            | (Elimination::Ride(a), Elimination::Ride(b)) => {
                let (
                    Some(&Computation::Ride {
                        motive: a_motive,
                        value: a_value,
                        ..
                    }),
                    Some(&Computation::Ride {
                        motive: b_motive,
                        value: b_value,
                        ..
                    }),
                ) = (arena.computation(a), arena.computation(b))
                else {
                    return Err(unreadable());
                };
                let a_quote = arena.value_quote(a_motive);
                let b_quote = arena.value_quote(b_motive);
                premises.extend([
                    Premise::values(a_quote, b_quote),
                    Premise::values(a_value, b_value),
                ]);
            },
            | (Elimination::Bind(a), Elimination::Bind(b))
            | (Elimination::Fixpoint(a), Elimination::Fixpoint(b)) => {
                premises.push(Premise::computations(a, b));
            },
            | (Elimination::ListFold(a, b), Elimination::ListFold(c, d)) => {
                premises.extend([Premise::computations(a, c), Premise::computations(b, d)]);
            },
            // Two dependent splits compare by their bodies under the two
            // component binders; the motives are annotations no reduction
            // reads.
            | (Elimination::SigmaSplit(a), Elimination::SigmaSplit(b)) => {
                let (
                    Some(&Computation::SigmaSplit { body: one, .. }),
                    Some(&Computation::SigmaSplit { body: other, .. }),
                ) = (arena.computation(a), arena.computation(b))
                else {
                    return Err(unreadable());
                };
                premises.push(Premise::computations(one, other));
            },
            // Two projections of one side add no premise; the two sides of
            // the lazy product are apart.
            | (Elimination::Project(a), Elimination::Project(b)) => {
                if a != b {
                    return Ok(Structure::Leaf(Expect::NotConvertible));
                }
            },
            | (
                Elimination::DataCase(_)
                | Elimination::SigmaSplit(_)
                | Elimination::RecordProjection(_)
                | Elimination::TupleProjection(_)
                | Elimination::Project(_)
                | Elimination::Transport(_)
                | Elimination::ProductTransport(_)
                | Elimination::Ride(_)
                | Elimination::Force
                | Elimination::Apply(_)
                | Elimination::Bind(_)
                | Elimination::Case(..)
                | Elimination::ListFold(..)
                | Elimination::StaticApply(_)
                | Elimination::Fixpoint(_),
                _,
            ) => return Ok(Structure::Leaf(Expect::NotConvertible)),
        }
    }
    Ok(Structure::of(premises))
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
    use gandr_kernel_term::FixpointEvidence;
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
    use super::convert;
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
            ReplayBudget::default(),
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
    fn native_list_fold_reduces_without_capturing_outer_variables()
    {
        let mut arena = TermArena::new();
        let unit_type = arena.value_type_unit();
        let list_type = arena.value_type_list(unit_type);
        let nil = arena.value_list_nil();
        let outer = arena.value_variable(DeBruijnIndex::from(0_u32));
        let second = arena.value_variable(DeBruijnIndex::from(1_u32));
        let tail = arena.value_list_cons(second, nil);
        let list = arena.value_list_cons(outer, tail);
        let head = arena.value_variable(DeBruijnIndex::from(1_u32));
        let folded = arena.value_variable(DeBruijnIndex::from(0_u32));
        let cell = arena.value_list_cons(head, folded);
        let on_cons = arena.computation_return(cell);
        let on_nil = arena.computation_return(nil);
        for input in [nil, list] {
            let fold = arena.computation_list_fold(unit_type, list_type, input, on_nil, on_cons);
            let expected = arena.computation_return(input);
            assert_eq!(
                run(
                    &mut arena,
                    &Unfoldings::default(),
                    ReplaySides::Computations(fold, expected),
                    EngineClaim::Convertible,
                    &[]
                ),
                KernelVerdict::Convertible
            );
        }
        let unit = arena.value_unit();
        let on_nil = arena.computation_return(unit);
        let on_cons = arena.computation_return(head);
        let fold = arena.computation_list_fold(unit_type, unit_type, list, on_nil, on_cons);
        let expected = arena.computation_return(outer);
        assert_eq!(
            run(
                &mut arena,
                &Unfoldings::default(),
                ReplaySides::Computations(fold, expected),
                EngineClaim::Convertible,
                &[]
            ),
            KernelVerdict::Convertible
        );
    }

    #[test]
    fn a_compared_pair_closes_on_alpha_equality_or_rigid_separation()
    {
        let mut arena = TermArena::new();
        let none = Unfoldings::default();
        let unit = arena.value_unit();
        let near = arena.value_variable(DeBruijnIndex::from(0));
        let far = arena.value_variable(DeBruijnIndex::from(1));
        let left = arena.value_tuple(&[unit, near]);
        let same = arena.value_tuple(&[unit, near]);
        let apart = arena.value_tuple(&[unit, far]);
        let pairs = |right| ReplaySides::Values(left, right);
        let mark = arena.watermark();

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

        assert_eq!(arena.watermark(), mark);

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
        let pair = arena.value_tuple(&[unit, unit]);
        let returned_pair = arena.computation_return(pair);
        let injected = arena.value_injection(Side::Right.into(), unit);
        let cased = arena.computation_case(injected, &[returned_pair, returned_bound]);
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
    fn two_reflexivities_decompose_to_their_points()
    {
        let mut arena = TermArena::new();
        let unit = arena.value_unit();
        let first = ConstantIndex::from(0_usize);
        let defined = arena.value_constant(first);
        let declared = arena.value_here(defined);
        let written = arena.value_here(unit);
        let unfoldings = Unfoldings::new(Vec::from([Unfoldable::Body(unit)]));
        let sides = ReplaySides::Values(declared, written);
        let unfolded = |reduce: ConversionDecision<ReplayNode>| {
            [
                ConversionDecision::Decompose,
                ConversionDecision::Unfold {
                    constant: ReplayNode::Constant(first),
                },
                reduce,
            ]
        };
        let redex = ReplayNode::Constant(first);

        assert_eq!(
            run(
                &mut arena,
                &unfoldings,
                sides,
                EngineClaim::Convertible,
                &unfolded(ConversionDecision::ReduceLeft { redex })
            ),
            KernelVerdict::Convertible,
            "the reflexivities convert by their points, one unfolding apart"
        );
        assert_eq!(
            run(
                &mut arena,
                &unfoldings,
                sides,
                EngineClaim::Convertible,
                &unfolded(ConversionDecision::ReduceRight { redex })
            ),
            refused(ReplayRefusal::Inapplicable {
                at: TracePosition::from(2),
            }),
            "the unfolding read on the other point does not apply"
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
        let parameters = arena.value_type_product(&[outer_type, inner_type]);
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
        let in_order_type = arena.value_type_product(&[integer, string]);
        let in_order = arena.value_quote(in_order_type);
        let swapped_type = arena.value_type_product(&[string, integer]);
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
        let open_type = arena.value_type_product(&[integer, ambient_type]);
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
        let left = arena.value_tuple(&[unit, unit]);
        let right = arena.value_tuple(&[unit, bound]);
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
        let pair = arena.value_tuple(&[unit, unit]);
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
    fn anchor_free_constant_decisions_read_their_constant_off_the_shapes()
    {
        let mut arena = TermArena::new();
        let unit = arena.value_unit();
        let pair = arena.value_tuple(&[unit, unit]);
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
        let other = ReplayNode::Other;
        let unfold_left = [
            ConversionDecision::Unfold { constant: other },
            ConversionDecision::ReduceLeft { redex: other },
        ];
        let shortcut = ConversionDecision::ConstShortcut { constant: other };
        let postpone = ConversionDecision::Postpone { constant: other };
        let freeze = |side| ConversionDecision::Freeze {
            constant: other,
            side,
        };
        let at = |position| {
            refused(ReplayRefusal::Inapplicable {
                at: TracePosition::from(position),
            })
        };
        let chain = ReplaySides::Values(named_second, named_first);

        // Both branches of the anchored chain replay with no constant named:
        // the freeze takes the right's head, the postponement the head
        // opposite the unfolding, the shortcut the head both sides share.
        for branch in [freeze(ConversionSide::Right), postpone] {
            let trace = [branch, unfold_left[0], unfold_left[1], shortcut];
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

        // Freezing the left leaves its head no unfolding: the reduction that
        // names it refuses.
        let wrong_freeze = [freeze(ConversionSide::Left), unfold_left[0], unfold_left[1]];
        assert_eq!(
            run(
                &mut arena,
                &unfoldings,
                chain,
                EngineClaim::Convertible,
                &wrong_freeze
            ),
            at(2)
        );

        // A side with no defined head offers no constant to freeze, to
        // postpone against, or to share.
        let bare = ReplaySides::Values(named_first, unit);
        assert_eq!(
            run(&mut arena, &unfoldings, bare, EngineClaim::Convertible, &[
                freeze(ConversionSide::Right)
            ]),
            at(0)
        );
        assert_eq!(
            run(&mut arena, &unfoldings, bare, EngineClaim::Convertible, &[
                postpone,
                unfold_left[0],
                unfold_left[1]
            ]),
            at(2)
        );

        // Two different defined heads share no constant to shortcut.
        assert_eq!(
            run(
                &mut arena,
                &unfoldings,
                ReplaySides::Values(named_second, named_third),
                EngineClaim::Convertible,
                &[shortcut]
            ),
            at(0)
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
    fn the_laws_of_bind_replay_by_name()
    {
        let mut arena = TermArena::new();
        let none = Unfoldings::default();
        let return_eta = |side| ConversionDecision::ReturnEta { side };
        let reassociate = |side| ConversionDecision::Reassociate { side };
        let negative = |position: u32| ConversionDecision::NegativeSubgoal {
            position: SubgoalPosition::from(position),
        };
        let variable =
            |arena: &mut TermArena, index: u32| arena.value_variable(DeBruijnIndex::from(index));

        // F-η: `force f` against `force f to x. return x`, `f` free.
        let function = variable(&mut arena, 0);
        let held = arena.computation_force(function);
        let bound = variable(&mut arena, 0);
        let returned = arena.computation_return(bound);
        let expanded = arena.computation_bind(held, returned);
        let eta = ReplaySides::Computations(held, expanded);
        let flipped = ReplaySides::Computations(expanded, held);
        assert_eq!(
            run(&mut arena, &none, eta, EngineClaim::Convertible, &[
                return_eta(ConversionSide::Left)
            ]),
            KernelVerdict::Convertible
        );
        assert_eq!(
            run(&mut arena, &none, flipped, EngineClaim::Convertible, &[
                return_eta(ConversionSide::Right)
            ]),
            KernelVerdict::Convertible
        );
        assert_eq!(
            run(&mut arena, &none, eta, EngineClaim::Convertible, &[]),
            refused(ReplayRefusal::Exhausted)
        );
        for wrong in [
            return_eta(ConversionSide::Right),
            reassociate(ConversionSide::Left),
            ConversionDecision::Decompose,
        ] {
            assert_eq!(
                run(&mut arena, &none, eta, EngineClaim::Convertible, &[wrong]),
                refused(ReplayRefusal::Inapplicable {
                    at: TracePosition::from(0),
                })
            );
        }

        // Not pointwise: `force f` against `force f to x. return g`, `g`
        // free. The refutation runs through the law, never past it.
        let other = variable(&mut arena, 2);
        let constant = arena.computation_return(other);
        let apart = arena.computation_bind(held, constant);
        let apart = ReplaySides::Computations(held, apart);
        assert_eq!(
            run(&mut arena, &none, apart, EngineClaim::NotConvertible, &[
                return_eta(ConversionSide::Left),
                negative(0),
                negative(0)
            ]),
            KernelVerdict::NotConvertible
        );
        assert_eq!(
            run(&mut arena, &none, apart, EngineClaim::NotConvertible, &[
                negative(0),
                negative(0)
            ]),
            refused(ReplayRefusal::Inapplicable {
                at: TracePosition::from(0),
            })
        );

        // Associativity: `(force f to x. g x) to y. g y` against
        // `force f to x. (g x to y. g y)`, `f` and `g` free; the outer
        // continuation's `g` moves past the new binder.
        let applied = |arena: &mut TermArena, function: u32| {
            let function = variable(arena, function);
            let forced = arena.computation_force(function);
            let argument = variable(arena, 0);
            arena.computation_application(forced, argument)
        };
        let function = variable(&mut arena, 1);
        let head = arena.computation_force(function);
        let first = applied(&mut arena, 1);
        let inner = arena.computation_bind(head, first);
        let nested = arena.computation_bind(inner, first);
        let shifted = applied(&mut arena, 2);
        let fused = arena.computation_bind(first, shifted);
        let reassociated = arena.computation_bind(head, fused);
        let associativity = ReplaySides::Computations(nested, reassociated);
        assert_eq!(
            run(
                &mut arena,
                &none,
                associativity,
                EngineClaim::Convertible,
                &[reassociate(ConversionSide::Left)]
            ),
            KernelVerdict::Convertible
        );
        assert_eq!(
            run(
                &mut arena,
                &none,
                ReplaySides::Computations(reassociated, nested),
                EngineClaim::Convertible,
                &[reassociate(ConversionSide::Right)]
            ),
            KernelVerdict::Convertible
        );
        assert_eq!(
            run(
                &mut arena,
                &none,
                associativity,
                EngineClaim::Convertible,
                &[reassociate(ConversionSide::Right)]
            ),
            refused(ReplayRefusal::Inapplicable {
                at: TracePosition::from(0),
            })
        );

        // Without the shift the outer continuation would read `x` for `g`:
        // that twin is apart, and its refutation names the continuation.
        let unshifted = arena.computation_bind(first, first);
        let unshifted = arena.computation_bind(head, unshifted);
        assert_eq!(
            run(
                &mut arena,
                &none,
                ReplaySides::Computations(nested, unshifted),
                EngineClaim::NotConvertible,
                &[reassociate(ConversionSide::Left), negative(0), negative(1)]
            ),
            KernelVerdict::NotConvertible
        );
    }

    #[test]
    fn the_kernel_converts_by_the_forced_rules_alone()
    {
        let mut arena = TermArena::new();
        let variable =
            |arena: &mut TermArena, index: u32| arena.value_variable(DeBruijnIndex::from(index));
        let function = variable(&mut arena, 0);
        let held = arena.computation_force(function);
        let bound = variable(&mut arena, 0);
        let returned = arena.computation_return(bound);
        let expanded = arena.computation_bind(held, returned);
        let other = variable(&mut arena, 2);
        let constant = arena.computation_return(other);
        let apart = arena.computation_bind(held, constant);
        // The thunks of both, so the forces fire unread too.
        let suspended = arena.value_thunk(held);
        let suspended_expanded = arena.value_thunk(expanded);
        let watermark = arena.watermark();

        for sides in [
            ReplaySides::Computations(held, expanded),
            ReplaySides::Computations(expanded, held),
            ReplaySides::Values(suspended, suspended_expanded),
        ] {
            assert_eq!(
                convert(
                    &mut arena,
                    &crate::presented::FREE,
                    sides,
                    ReplayBudget::default()
                ),
                KernelVerdict::Convertible
            );
        }
        // A pair apart declines: the kernel's own conversion certifies no
        // refutation, so an engine-free judgement never reads one.
        assert!(matches!(
            convert(
                &mut arena,
                &crate::presented::FREE,
                ReplaySides::Computations(held, apart),
                ReplayBudget::default()
            ),
            KernelVerdict::Declined(_)
        ));
        assert_eq!(arena.watermark(), watermark);
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
        for sides in [
            ReplaySides::Computations(omega, returned_unit),
            ReplaySides::Computations(returned_unit, omega),
            ReplaySides::Computations(omega, omega),
        ] {
            for claim in [EngineClaim::Convertible, EngineClaim::NotConvertible] {
                let verdict = replay(
                    &mut arena,
                    &none,
                    sides,
                    claim,
                    [SHARED],
                    ReplayBudget::from(64_u64),
                );
                assert_eq!(verdict, KernelVerdict::Declined(ReplayDecline::Budget));
                assert_eq!(arena.watermark(), mark, "every reduct is truncated away");
            }
        }
    }

    #[test]
    fn budget_exhaustion_survives_the_counter_ceiling()
    {
        let mut arena = TermArena::new();
        let unfoldings = Unfoldings::default();
        for (spent, budget, expected, after) in [
            (u64::MAX, u64::MAX, Err(super::Stop::Budget), u64::MAX),
            (0, 0, Err(super::Stop::Budget), 0),
            (0, 1, Ok(()), 1),
            (u64::MAX.saturating_sub(1), u64::MAX, Ok(()), u64::MAX),
        ] {
            let mut run = super::Replay {
                arena: &mut arena,
                unfoldings: &unfoldings,
                trace: core::iter::empty().peekable(),
                reading: super::Reading::Recorded,
                position: 0,
                spent,
                budget: u64::from(ReplayBudget::from(budget)),
                table: crate::ContentTable::new(),
                memo: gandr_kernel_check_memo::NullMemo,
            };
            assert_eq!(run.charge(), expected);
            assert_eq!(run.spent, after);
            assert_eq!(run.charge(), Err(super::Stop::Budget));
            assert_eq!(run.spent, after);
        }
    }

    #[test]
    fn trace_consumption_preserves_the_end_and_position_ceiling()
    {
        let mut arena = TermArena::new();
        let unfoldings = Unfoldings::default();
        for position in [0, usize::MAX] {
            let mut replay = super::Replay {
                arena: &mut arena,
                unfoldings: &unfoldings,
                trace: core::iter::once(SHARED).peekable(),
                reading: super::Reading::Recorded,
                position,
                spent: 0,
                budget: 1,
                table: crate::ContentTable::new(),
                memo: gandr_kernel_check_memo::NullMemo,
            };
            assert_eq!(replay.peek(), super::Next::Decision(SHARED));
            assert_eq!(replay.peek(), super::Next::Decision(SHARED));
            assert_eq!(usize::from(replay.at()), position);
            replay.take();
            assert_eq!(usize::from(replay.at()), position.saturating_add(1));
            assert_eq!(replay.peek(), super::Next::End);
            replay.take();
            assert_eq!(usize::from(replay.at()), position.saturating_add(1));
            assert_eq!(replay.peek(), super::Next::End);
        }
    }

    #[test]
    fn frozen_heads_are_side_local_and_opacity_takes_precedence()
    {
        let mut arena = TermArena::new();
        let unit = arena.value_unit();
        let unfoldings = Unfoldings::new(Vec::from([
            Unfoldable::Body(unit),
            Unfoldable::Operator {
                parameters: ParameterCount::from(0),
                body: unit,
            },
            Unfoldable::Opaque,
        ]));
        let replay = super::Replay {
            arena: &mut arena,
            unfoldings: &unfoldings,
            trace: core::iter::empty().peekable(),
            reading: super::Reading::Recorded,
            position: 0,
            spent: 0,
            budget: 1,
            table: crate::ContentTable::new(),
            memo: gandr_kernel_check_memo::NullMemo,
        };
        for (index, initial) in [
            (0, super::Status::Defined),
            (1, super::Status::Defined),
            (2, super::Status::Opaque),
            (3, super::Status::Opaque),
            (usize::MAX, super::Status::Opaque),
        ] {
            let constant = ConstantIndex::from(index);
            for side in [ConversionSide::Left, ConversionSide::Right] {
                let mut frozen = super::Frozen::default();
                assert_eq!(
                    replay.head(constant, &frozen, side),
                    super::Head::Constant(constant, initial)
                );
                frozen.freeze(side, constant);
                let expected = if initial == super::Status::Opaque {
                    initial
                }
                else {
                    super::Status::Frozen
                };
                assert_eq!(
                    replay.head(constant, &frozen, side),
                    super::Head::Constant(constant, expected)
                );
                assert_eq!(
                    replay.head(constant, &frozen, super::opposite(side)),
                    super::Head::Constant(constant, initial)
                );
            }
        }
    }

    #[test]
    fn rule_dispatch_respects_constant_priority_and_eta_side()
    {
        let mut arena = TermArena::new();
        let unit = arena.value_unit();
        let body = arena.computation_return(unit);
        let name = ConstantIndex::from(0);
        let shapes = [
            super::Shape::Former,
            super::Shape::Thunk(body),
            super::Shape::Lambda(body),
            super::Shape::Return(unit),
            super::Shape::Neutral(super::Head::Variable(DeBruijnIndex::from(0)), Vec::new()),
            super::Shape::Neutral(
                super::Head::Constant(name, super::Status::Opaque),
                Vec::new(),
            ),
            super::Shape::Neutral(
                super::Head::Constant(name, super::Status::Frozen),
                Vec::new(),
            ),
            super::Shape::Neutral(
                super::Head::Constant(name, super::Status::Defined),
                Vec::new(),
            ),
            super::Shape::With(body, body),
        ];
        for (left_kind, left) in shapes.iter().enumerate() {
            for (right_kind, right) in shapes.iter().enumerate() {
                let expected = match (left_kind, right_kind) {
                    | (7, _) | (_, 7) => super::Rule::Constants,
                    | (1, 1 | 4 ..= 6) | (4 ..= 6, 1) => super::Rule::Force,
                    | (2, 4 ..= 6) => super::Rule::Eta(ConversionSide::Right),
                    | (4 ..= 6, 2) => super::Rule::Eta(ConversionSide::Left),
                    | (8, 4 ..= 6) => super::Rule::ProductEta(ConversionSide::Right),
                    | (4 ..= 6, 8) => super::Rule::ProductEta(ConversionSide::Left),
                    | _ => super::Rule::Structural,
                };
                assert_eq!(
                    super::rule(left, right),
                    expected,
                    "shape classes {left_kind}, {right_kind}"
                );
            }
        }
    }

    #[test]
    fn a_projection_runs_its_side_of_a_pairing()
    {
        let mut arena = TermArena::new();
        let none = Unfoldings::default();
        let unit = arena.value_unit();
        let free = arena.value_variable(DeBruijnIndex::from(0));
        let left = arena.computation_return(unit);
        let right = arena.computation_return(free);
        let pairing = arena.computation_with(left, right);
        let first = arena.computation_project(Side::Left, pairing);
        let second = arena.computation_project(Side::Right, pairing);
        let negative = ConversionDecision::NegativeSubgoal {
            position: SubgoalPosition::from(0_u32),
        };

        // Each projection runs its own side and no decision is read.
        assert_eq!(
            run(
                &mut arena,
                &none,
                ReplaySides::Computations(first, left),
                EngineClaim::Convertible,
                &[]
            ),
            KernelVerdict::Convertible
        );
        assert_eq!(
            run(
                &mut arena,
                &none,
                ReplaySides::Computations(second, right),
                EngineClaim::Convertible,
                &[]
            ),
            KernelVerdict::Convertible
        );
        assert_eq!(
            run(
                &mut arena,
                &none,
                ReplaySides::Computations(second, left),
                EngineClaim::NotConvertible,
                &[negative]
            ),
            KernelVerdict::NotConvertible
        );

        // A projection stuck on a neutral keeps its frame over the reduct of
        // what it projects, and observes a fixpoint at its gate.
        let neutral = arena.computation_force(free);
        let suspended = arena.value_thunk(neutral);
        let forced = arena.computation_force(suspended);
        let reducible = arena.computation_project(Side::Left, forced);
        let stuck = arena.computation_project(Side::Left, neutral);
        let other_side = arena.computation_project(Side::Right, neutral);
        assert_eq!(
            run(
                &mut arena,
                &none,
                ReplaySides::Computations(reducible, stuck),
                EngineClaim::Convertible,
                &[]
            ),
            KernelVerdict::Convertible
        );
        assert_eq!(
            run(
                &mut arena,
                &none,
                ReplaySides::Computations(reducible, other_side),
                EngineClaim::NotConvertible,
                &[]
            ),
            KernelVerdict::NotConvertible
        );
        let partial = arena.computation_fixpoint(pairing, FixpointEvidence::Partial);
        let observed = arena.computation_project(Side::Left, partial);
        assert_eq!(
            run(
                &mut arena,
                &none,
                ReplaySides::Computations(observed, left),
                EngineClaim::Convertible,
                &[]
            ),
            KernelVerdict::Declined(ReplayDecline::PartialFixpoint)
        );
    }

    #[test]
    fn a_lazy_pairing_meets_a_neutral_by_its_projections()
    {
        let mut arena = TermArena::new();
        let none = Unfoldings::default();
        let head = arena.value_variable(DeBruijnIndex::from(0));
        let neutral = arena.computation_force(head);
        let first = arena.computation_project(Side::Left, neutral);
        let second = arena.computation_project(Side::Right, neutral);
        let expanded = arena.computation_with(first, second);
        let crossed = arena.computation_with(first, first);
        let first_again = arena.computation_project(Side::Left, neutral);
        let second_again = arena.computation_project(Side::Right, neutral);
        let rebuilt = arena.computation_with(first_again, second_again);
        let negative = |position| ConversionDecision::NegativeSubgoal {
            position: SubgoalPosition::from(position),
        };

        // The pairing of a neutral's projections is that neutral, on either
        // side, with no decision for the η step; two pairings compare
        // componentwise.
        for sides in [
            ReplaySides::Computations(expanded, neutral),
            ReplaySides::Computations(neutral, expanded),
            ReplaySides::Computations(expanded, rebuilt),
        ] {
            assert_eq!(
                run(&mut arena, &none, sides, EngineClaim::Convertible, &[]),
                KernelVerdict::Convertible
            );
        }

        // The arrow's decision is never read at the step, so it is left over;
        // a structural marker there is refused where it stands.
        let sides = ReplaySides::Computations(expanded, neutral);
        assert_eq!(
            run(&mut arena, &none, sides, EngineClaim::Convertible, &[
                ConversionDecision::EtaExpand {
                    side: ConversionSide::Right,
                    variable: ReplayNode::Other,
                }
            ]),
            refused(ReplayRefusal::Leftover {
                at: TracePosition::from(0),
            })
        );
        assert_eq!(
            run(&mut arena, &none, sides, EngineClaim::Convertible, &[
                ConversionDecision::Decompose
            ]),
            refused(ReplayRefusal::Inapplicable {
                at: TracePosition::from(0),
            })
        );

        // A pairing projecting the left side twice is refuted by its second
        // premise only, and only through the decision naming it.
        for sides in [
            ReplaySides::Computations(crossed, neutral),
            ReplaySides::Computations(neutral, crossed),
            ReplaySides::Computations(rebuilt, crossed),
        ] {
            assert_eq!(
                run(&mut arena, &none, sides, EngineClaim::NotConvertible, &[
                    negative(1_u32)
                ]),
                KernelVerdict::NotConvertible
            );
            assert_eq!(
                run(&mut arena, &none, sides, EngineClaim::NotConvertible, &[
                    negative(0_u32)
                ]),
                refused(ReplayRefusal::Contradicted {
                    at: TracePosition::from(1),
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
    }

    #[test]
    fn neutral_spines_keep_subgoal_order_and_reject_kind_mismatches()
    {
        let mut arena = TermArena::new();
        let none = Unfoldings::default();
        let head = arena.value_variable(DeBruijnIndex::from(0));
        let different = arena.value_variable(DeBruijnIndex::from(1));
        let unit = arena.value_unit();
        let same_branch = arena.computation_return(unit);
        let differing_branch = arena.computation_return(different);
        let left_case = arena.computation_case(head, &[same_branch, same_branch]);
        let right_case = arena.computation_case(head, &[same_branch, differing_branch]);
        let left = arena.computation_application(left_case, unit);
        let right = arena.computation_application(right_case, unit);
        let negative = |position| ConversionDecision::NegativeSubgoal {
            position: SubgoalPosition::from(position),
        };
        let sides = ReplaySides::Computations(left, right);
        assert_eq!(
            run(&mut arena, &none, sides, EngineClaim::NotConvertible, &[
                negative(1_u32),
                negative(0_u32)
            ]),
            KernelVerdict::NotConvertible
        );
        assert_eq!(
            run(&mut arena, &none, sides, EngineClaim::NotConvertible, &[
                negative(0_u32),
                negative(0_u32)
            ]),
            refused(ReplayRefusal::Contradicted {
                at: TracePosition::from(2)
            })
        );
        assert_eq!(
            run(&mut arena, &none, sides, EngineClaim::NotConvertible, &[
                negative(2_u32)
            ]),
            refused(ReplayRefusal::Contradicted {
                at: TracePosition::from(1)
            })
        );
        assert_eq!(
            run(&mut arena, &none, sides, EngineClaim::NotConvertible, &[
                negative(3_u32)
            ]),
            refused(ReplayRefusal::Inapplicable {
                at: TracePosition::from(0)
            })
        );
        let forced = arena.computation_force(head);
        let applied = arena.computation_application(forced, unit);
        let bound = arena.computation_bind(forced, same_branch);
        for other in [forced, bound] {
            assert_eq!(
                run(
                    &mut arena,
                    &none,
                    ReplaySides::Computations(applied, other),
                    EngineClaim::NotConvertible,
                    &[]
                ),
                KernelVerdict::NotConvertible
            );
        }
        assert_eq!(
            run(
                &mut arena,
                &none,
                ReplaySides::Values(head, head),
                EngineClaim::Convertible,
                &[]
            ),
            KernelVerdict::Convertible
        );
    }

    #[test]
    fn reduced_heads_retain_application_and_bind_frames()
    {
        let mut arena = TermArena::new();
        let none = Unfoldings::default();
        let unit = arena.value_unit();
        let ambient = arena.value_variable(DeBruijnIndex::from(0));
        let beneath_binder = arena.value_variable(DeBruijnIndex::from(1));
        let opened_head = arena.computation_force(ambient);
        let body = arena.computation_force(beneath_binder);
        let lambda = arena.computation_lambda(body);
        let redex = arena.computation_application(lambda, unit);
        let continuation = arena.computation_return(ambient);
        let applied_redex = arena.computation_application(redex, unit);
        let applied_normal = arena.computation_application(opened_head, unit);
        let bound_redex = arena.computation_bind(redex, continuation);
        let bound_normal = arena.computation_bind(opened_head, continuation);
        let mark = arena.watermark();
        for (left, right) in [(applied_redex, applied_normal), (bound_redex, bound_normal)] {
            assert_eq!(
                run(
                    &mut arena,
                    &none,
                    ReplaySides::Computations(left, right),
                    EngineClaim::Convertible,
                    &[]
                ),
                KernelVerdict::Convertible
            );
            assert_eq!(arena.watermark(), mark);
        }
    }

    #[test]
    fn engine_decline_and_zero_budget_do_not_read_the_trace()
    {
        let mut arena = TermArena::new();
        let none = Unfoldings::default();
        let unit = arena.value_unit();
        for (claim, budget, expected, consumed) in [
            (
                EngineClaim::Declined,
                0_u64,
                KernelVerdict::Declined(ReplayDecline::EngineDeclined),
                0,
            ),
            (
                EngineClaim::Convertible,
                0,
                KernelVerdict::Declined(ReplayDecline::Budget),
                0,
            ),
            (EngineClaim::Convertible, 1, KernelVerdict::Convertible, 1),
            (
                EngineClaim::NotConvertible,
                1,
                refused(ReplayRefusal::Contradicted {
                    at: TracePosition::from(1),
                }),
                1,
            ),
        ] {
            let observed = core::cell::Cell::new(0_u32);
            let trace = core::iter::once(SHARED)
                .inspect(|_| observed.set(observed.get().saturating_add(1)));
            assert_eq!(
                replay(
                    &mut arena,
                    &none,
                    ReplaySides::Values(unit, unit),
                    claim,
                    trace,
                    ReplayBudget::from(budget)
                ),
                expected
            );
            assert_eq!(observed.get(), consumed);
        }
    }

    #[test]
    fn a_ride_unfolds_its_flow_where_the_dialogue_names_it()
    {
        let mut arena = TermArena::new();
        let unit_type = arena.value_type_unit();
        let code = arena.value_quote(unit_type);
        let stay = arena.value_stay(code);
        let unfoldings = Unfoldings::new(Vec::from([Unfoldable::Body(stay)]));
        let named = arena.value_constant(ConstantIndex::from(0_usize));
        let decoded = arena.value_variable(DeBruijnIndex::from(0_u32));
        let motive = arena.value_type_element(decoded, Level::zero());
        let unit = arena.value_unit();
        let rode = arena.computation_ride(motive, named, unit);
        let returned = arena.computation_return(unit);
        let sides = ReplaySides::Computations(rode, returned);
        let unfold = |reduce: fn(ReplayNode) -> ConversionDecision<ReplayNode>| {
            [
                ConversionDecision::Unfold {
                    constant: ReplayNode::Other,
                },
                reduce(ReplayNode::Other),
            ]
        };
        let left = |redex| ConversionDecision::ReduceLeft { redex };
        let right = |redex| ConversionDecision::ReduceRight { redex };

        // The flow heads the ride: its side's unfolding reaches `stay`, and
        // the ride returns its value.
        assert_eq!(
            run(
                &mut arena,
                &unfoldings,
                sides,
                EngineClaim::Convertible,
                &unfold(left)
            ),
            KernelVerdict::Convertible
        );
        // Read on the other side, or not at all, the unfolding is refused.
        assert_eq!(
            run(
                &mut arena,
                &unfoldings,
                sides,
                EngineClaim::Convertible,
                &unfold(right)
            ),
            refused(ReplayRefusal::Inapplicable {
                at: TracePosition::from(1)
            })
        );
        assert_eq!(
            run(&mut arena, &unfoldings, sides, EngineClaim::Convertible, &[
            ]),
            refused(ReplayRefusal::Exhausted)
        );

        // Two rides along one neutral flow compare their motives, then their
        // values.
        let flow = arena.value_variable(DeBruijnIndex::from(0_u32));
        let injected = arena.value_injection(Side::Left.into(), unit);
        let one = arena.computation_ride(motive, flow, unit);
        let same = arena.computation_ride(motive, flow, unit);
        let apart = arena.computation_ride(motive, flow, injected);
        let negative = |position: u32| ConversionDecision::NegativeSubgoal {
            position: SubgoalPosition::from(position),
        };
        assert_eq!(
            run(
                &mut arena,
                &unfoldings,
                ReplaySides::Computations(one, same),
                EngineClaim::Convertible,
                &[]
            ),
            KernelVerdict::Convertible
        );
        let rides = ReplaySides::Computations(one, apart);
        assert_eq!(
            run(
                &mut arena,
                &unfoldings,
                rides,
                EngineClaim::NotConvertible,
                &[negative(1)]
            ),
            KernelVerdict::NotConvertible
        );
        assert_eq!(
            run(
                &mut arena,
                &unfoldings,
                rides,
                EngineClaim::NotConvertible,
                &[negative(0)]
            ),
            refused(ReplayRefusal::Contradicted {
                at: TracePosition::from(1)
            })
        );
    }
}
