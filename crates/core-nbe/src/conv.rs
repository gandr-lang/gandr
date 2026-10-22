//! Conversion over the domain, steps 1 through 3: the answers that need no
//! search.
//!
//! # The three steps
//!
//! Each step falls through to the next only when it does not answer:
//!
//! 1. **Identity.** Two ids naming one node are one value. So are two nodes
//!    whose term faces name one source term: both denote what that term
//!    denotes, which catches sharing the source had and evaluation expanded.
//! 2. **The guard.** Two [`Guard::Rigid`] words with different hashes settle
//!    the pair distinct in constant time, without reading either node.
//! 3. **Structural comparison**, over a heap worklist with head-mismatch
//!    fast-fail before any argument is compared. Steps 1 and 2 run again at
//!    every pair the walk reaches.
//!
//! # Three answers, not two
//!
//! Steps 1 through 3 never unfold and never open a binder, so a pair whose
//! answer depends on either is [`Settlement::Deferred`], naming which: a
//! neutral whose head has a body to unfold, or a closure — compared only once
//! a binder is opened, and the side of every η-equation. Deferral is never
//! distinct. A mismatch found beneath an unfoldable head or inside a closure's
//! environment defers rather than separates, because unfolding the head or
//! running the body may never read what differed. Under a rigid head the
//! mismatch separates: a stuck variable applied to two different arguments is
//! two different values.
//!
//! # Sharing-aware, and total
//!
//! The walk keeps the pairs it has met, per call, and skips a repeat, so two
//! graphs that share structure are compared in the number of distinct pairs
//! rather than in their expansion. Nothing is evaluated and nothing recurses,
//! so the walk is total on any depth; it reads core nodes only for literal
//! payloads.
//!
//! # Conversion steps 1 through 3
//!
//! Conversion's first three steps answer without searching, and each falls
//! through to the next only when it does not answer. **Step 1, identity**: one
//! id is one value, and so are two nodes whose term faces name one source term,
//! which catches sharing the source had and evaluation expanded — the
//! early-success rule `conv? β β′ → T if β = β′` read on the term face as well
//! as on the id. **Step 2, the guard**: two rigid cached words with different
//! hashes settle the pair distinct in constant time. **Step 3, structural
//! comparison**, over a heap worklist with head-mismatch fast-fail:
//! Courant–Leroy's `var-1`, `var-2`, `var-3` and `const` rules over neutrals,
//! with steps 1 and 2 run again at every pair the walk reaches.
//!
//! Domain validation precedes identity: an id removed by arena truncation is
//! `ConversionFault::Domain(DomainFault::Dangling)` even when both sides carry
//! it. A live self-comparison remains `Identical`. The structural walk applies
//! the same boundary to neutral and closure ids. Witnesses:
//! `conv::tests::identical_truncated_values_are_refused`,
//! `conv::tests::identical_truncated_computations_are_refused`,
//! `conv::tests::identical_truncated_neutrals_and_closures_are_refused`.
//!
//! The answer has three values because the steps never unfold and never open a
//! binder. A pair whose answer depends on either is `Settlement::Deferred`:
//! `Deferral::Unfolding` when a neutral's head has a body that may unfold into
//! the other side, `Deferral::Binder` when two closures suspend different
//! bodies or a closure meets a neutral an η-equation may relate it to, and
//! `Deferral::Indeterminate` when either side stands on a hole or a mark, which
//! a fill may make anything. A mismatch beneath an unfoldable head, or in a
//! closure's environment, defers rather than separates, because the unfolded
//! body or the opened closure may never read what differed; beneath a rigid
//! head it separates. A distinct answer is therefore sound relative to β, δ and
//! the η-equations a later step adds.
//!
//! The walk keeps the pairs it has met, per call, and skips a repeat, so two
//! graphs that share structure cost their distinct pairs rather than their
//! expansion. The set holds pairs only and dies with the call; it decides
//! nothing about which part of a value is copied, which is what keeps it clear
//! of the duplication parameter. Nothing is evaluated and nothing recurses, so
//! the walk is total on any depth and takes no fuel. Step 4, unfolding, is the
//! conversion machine's, with heights as scheduling shares; steps 5 and 6,
//! case-progress gating and speculation, are not built.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::Zone;
use gandr_kernel_check_memo::MemoError;
use gandr_kernel_term::Literal;

use crate::arena::CompClosureId;
use crate::arena::DomainArena;
use crate::arena::DomainCompId;
use crate::arena::DomainFault;
use crate::arena::DomainValueId;
use crate::arena::NeutralId;
use crate::code::CodeComparison;
use crate::code::ConstantReading;
use crate::code::compare_codes;
use crate::domain::CompTermFace;
use crate::domain::DomainComp;
use crate::domain::DomainValue;
use crate::domain::Elimination;
use crate::domain::NeutralHead;
use crate::domain::TermFace;
use crate::domain::Unfolding;
use crate::eval::EvalFault;
use crate::guard::Guard;
use crate::guard::GuardAnswer;

/// What a pair is, as far as steps 1 through 3 can tell.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Convertibility
{
    /// The two sides are one value.
    Convertible,
    /// The two sides are different values.
    Distinct,
    /// The answer needs a step past the third.
    Undecided,
}

/// Why steps 1 through 3 left a pair undecided.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Deferral
{
    /// A neutral whose head has a body to unfold met a side it might equal
    /// once unfolded.
    Unfolding,
    /// A closure met a closure over another body, or a neutral it might equal
    /// by an η-equation; either compares only once a binder is opened.
    Binder,
    /// A neutral standing on a hole or a mark met a side a fill might make it
    /// equal.
    Indeterminate,
}

/// Which step answered a pair, and how.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Settlement
{
    /// Step 1: the sides are one node, or two nodes of one source term.
    Identical,
    /// Step 2: both guards are rigid and their hashes differ.
    GuardedApart,
    /// Step 3: every pair the walk reached agreed.
    StructurallyEqual,
    /// Step 3: the walk reached a mismatch no unfolding or binder can repair.
    StructurallyApart,
    /// None of steps 1 through 3 answers; the first reason the walk met.
    Deferred(Deferral),
}

impl Settlement
{
    /// The answer, without the step that gave it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Convertibility::Convertible`] for step 1 and for a
    ///   structural agreement, [`Convertibility::Distinct`] for step 2 and for
    ///   a structural mismatch, and [`Convertibility::Undecided`] for a
    ///   deferral.
    /// - provides: the projection a consumer that does not care which step
    ///   answered reads.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a deferred comparison remains undecided, a later
    ///   rigid mismatch becomes distinct, and comparing a live node with itself
    ///   is convertible; conflating deferral with either settled answer changes
    ///   the consumer verdict.
    /// - witness: `conv::tests::the_first_deferral_is_retained_until_a_rigid_refutation`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| matches!((self, ret),
        (Self::Identical | Self::StructurallyEqual, Convertibility::Convertible)
        | (Self::GuardedApart | Self::StructurallyApart, Convertibility::Distinct)
        | (Self::Deferred(_), Convertibility::Undecided)))]
    pub fn verdict(self) -> Convertibility
    {
        match self {
            Self::Identical | Self::StructurallyEqual => Convertibility::Convertible,
            Self::GuardedApart | Self::StructurallyApart => Convertibility::Distinct,
            Self::Deferred(_) => Convertibility::Undecided,
        }
    }
}

/// Why a comparison was refused.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ConversionFault
{
    /// The domain arena refused, in its own vocabulary.
    Domain(DomainFault),
    /// A domain literal named a core node that is not a literal.
    LiteralPayload
    {
        /// The core id the domain literal carried.
        literal: ValueId,
    },
    /// A goal paired a value with a computation: an ill-typed input, which
    /// this crate does not re-derive types to exclude.
    Polarity,
    /// An evaluation the conversion machine drove was refused, in the
    /// evaluator's own vocabulary.
    Evaluation(EvalFault),
    /// The conversion machine's re-sharing memo refused to record a goal, in
    /// the memo's own vocabulary.
    Memo(MemoError),
    /// The conversion machine's own bookkeeping disagreed with itself: a
    /// process named another the machine does not hold. Unreachable while
    /// the machine's own pushes are the only source of ids; reported rather
    /// than asserted, so a miscount surfaces as a refusal.
    MachineInvariant,
}

/// What a mismatch at a pair means where the pair stands.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Context
{
    /// Nothing above the pair can repair a mismatch, so it separates.
    Rigid,
    /// The pair stands beneath an unfoldable head or in a closure's
    /// environment, so a mismatch defers for this reason.
    Flexible(Deferral),
}

/// One pair the walk still has to compare.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Goal
{
    /// Two values.
    Values(DomainValueId, DomainValueId, Context),
    /// Two weak-head computations.
    Comps(DomainCompId, DomainCompId, Context),
    /// Two neutrals.
    Neutrals(NeutralId, NeutralId, Context),
    /// Two computation closures; a mismatch inside always defers.
    Closures(CompClosureId, CompClosureId),
}

/// What steps 1 and 2 say about a pair.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Early
{
    /// Step 1 answered: one node, or one source term.
    Identical,
    /// Step 2 answered: rigid words that differ.
    Apart,
    /// Neither answered; structure decides.
    Open,
}

/// What comparing one pair's own structure found.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Local
{
    /// The pair's heads agree; its children, if any, are queued.
    Agree,
    /// The pair's heads differ, and the pair's context says what that means.
    Disagree,
    /// The pair needs a later step, whatever its context.
    Defer(Deferral),
}

/// Whether a walk ended on a separating mismatch.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Walked
{
    /// A mismatch in a rigid context: the pair is distinct.
    Apart,
    /// Every pair was met; the outstanding deferral, if any, decides.
    Exhausted,
}

/// The first deferral a walk met.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Outstanding
{
    /// No pair has deferred.
    Nothing,
    /// A pair deferred, for this reason.
    Deferred(Deferral),
}

/// The state of one structural walk.
struct Walk<'run>
{
    /// The core arena literal payloads are read from.
    core: &'run CoreArena,
    /// The domain arena both sides live in.
    domain: &'run DomainArena,
    /// Pairs still to compare, most recent last.
    goals: Vec<Goal>,
    /// Pairs already met in this call.
    met: BTreeSet<Goal>,
    /// The first deferral met.
    outstanding: Outstanding,
}

/// Steps 1 and 2 for two values.
///
/// # Specification
/// - requires: nothing — dangling ids are admissible input and refused.
/// - ensures: validation precedes identity: for resolving ids,
///   [`Early::Identical`] when the ids are equal or both term faces name one
///   source term; otherwise [`Early::Apart`] when the guards settle the pair
///   apart; otherwise [`Early::Open`].
/// - provides: the two constant-time steps, shared by the root and every pair
///   the walk reaches.
/// - fails: [`ConversionFault::Domain`] when either id does not resolve,
///   including an identical pair of dangling ids.
/// - panics: none.
///
/// # Errors
/// - [`ConversionFault::Domain`] — a side does not resolve.
///
/// # Adequacy
/// - hypothesis: L2 — live identity and equal source faces answer before guard
///   comparison, but truncating that same id makes even self-comparison fail;
///   rigid unequal words separate and flexible words remain open. Moving
///   identity before validation or treating equal hashes as equality changes a
///   boundary result.
/// - witness: `conv::tests::identical_truncated_values_are_refused`
/// - witness: `conv::tests::identity_answers_one_node_and_one_source_term`
/// - witness: `conv::tests::the_guard_answers_a_rigid_pair_identity_does_not`
/// - witness: `conv::tests::structure_answers_what_the_guard_cannot`
#[spec(ensures: |ret| match (domain.value(left), domain.value(right)) {
    (Some(one), Some(other)) => {
        let identical = left == right || matches!((one.face(), other.face()),
            (TermFace::Source(first), TermFace::Source(second)) if first == second);
        if identical { ret == Ok(Early::Identical) } else {
            match (domain.value_guard(left), domain.value_guard(right)) {
                (Ok(first), Ok(second)) => ret == Ok(early_by_guard(first, second)),
                _ => ret == Err(ConversionFault::Domain(DomainFault::Dangling)),
            }
        }
    },
    _ => ret == Err(ConversionFault::Domain(DomainFault::Dangling)),
})]
pub fn early_values(
    domain: &DomainArena,
    left: DomainValueId,
    right: DomainValueId,
) -> Result<Early, ConversionFault>
{
    let Some(one) = domain.value(left)
    else {
        return Err(ConversionFault::Domain(DomainFault::Dangling));
    };
    if left == right {
        return Ok(Early::Identical);
    }
    let Some(other) = domain.value(right)
    else {
        return Err(ConversionFault::Domain(DomainFault::Dangling));
    };
    if let (TermFace::Source(first), TermFace::Source(second)) = (one.face(), other.face())
        && first == second
    {
        return Ok(Early::Identical);
    }
    let guards = (domain.value_guard(left), domain.value_guard(right));
    let (Ok(first), Ok(second)) = guards
    else {
        return Err(ConversionFault::Domain(DomainFault::Dangling));
    };
    Ok(early_by_guard(first, second))
}

/// Steps 1 and 2 for two weak-head computations.
///
/// # Specification
/// - requires: nothing — dangling ids are admissible input and refused.
/// - ensures: validation precedes identity: for resolving ids,
///   [`Early::Identical`] when the ids are equal or both term faces name one
///   source term; otherwise [`Early::Apart`] when the guards settle the pair
///   apart; otherwise [`Early::Open`].
/// - provides: the computation half of the two constant-time steps.
/// - fails: [`ConversionFault::Domain`] when either id does not resolve,
///   including an identical pair of dangling ids.
/// - panics: none.
///
/// # Errors
/// - [`ConversionFault::Domain`] — a side does not resolve.
///
/// # Adequacy
/// - hypothesis: L2 — live identity and equal source faces answer before guard
///   comparison, but truncating that same id makes even self-comparison fail;
///   rigid unequal words separate and flexible words remain open. Moving
///   identity before validation or treating equal hashes as equality changes a
///   boundary result.
/// - witness: `conv::tests::identical_truncated_computations_are_refused`
/// - witness: `conv::tests::identity_answers_one_node_and_one_source_term`
/// - witness: `conv::tests::the_guard_answers_a_rigid_pair_identity_does_not`
/// - witness: `conv::tests::structure_answers_what_the_guard_cannot`
#[spec(ensures: |ret| match (domain.computation(left), domain.computation(right)) {
    (Some(one), Some(other)) => {
        let identical = left == right || matches!((one.face(), other.face()),
            (CompTermFace::Source(first), CompTermFace::Source(second)) if first == second);
        if identical { ret == Ok(Early::Identical) } else {
            match (domain.comp_guard(left), domain.comp_guard(right)) {
                (Ok(first), Ok(second)) => ret == Ok(early_by_guard(first, second)),
                _ => ret == Err(ConversionFault::Domain(DomainFault::Dangling)),
            }
        }
    },
    _ => ret == Err(ConversionFault::Domain(DomainFault::Dangling)),
})]
pub fn early_comps(
    domain: &DomainArena,
    left: DomainCompId,
    right: DomainCompId,
) -> Result<Early, ConversionFault>
{
    let Some(one) = domain.computation(left)
    else {
        return Err(ConversionFault::Domain(DomainFault::Dangling));
    };
    if left == right {
        return Ok(Early::Identical);
    }
    let Some(other) = domain.computation(right)
    else {
        return Err(ConversionFault::Domain(DomainFault::Dangling));
    };
    if let (CompTermFace::Source(first), CompTermFace::Source(second)) = (one.face(), other.face())
        && first == second
    {
        return Ok(Early::Identical);
    }
    let guards = (domain.comp_guard(left), domain.comp_guard(right));
    let (Ok(first), Ok(second)) = guards
    else {
        return Err(ConversionFault::Domain(DomainFault::Dangling));
    };
    Ok(early_by_guard(first, second))
}

/// Step 2 read as an early answer.
///
/// # Specification
/// trivial.
fn early_by_guard(
    left: Guard,
    right: Guard,
) -> Early
{
    match left.settles(right) {
        GuardAnswer::Apart => Early::Apart,
        GuardAnswer::Inconclusive => Early::Open,
    }
}

/// Run steps 1 through 3 on two domain values.
///
/// # Specification
/// - requires: `core` is the arena the values' literal payloads live in, and
///   both values live in `domain`.
/// - ensures: [`Settlement::Identical`] exactly when step 1 answers at the
///   root; otherwise [`Settlement::GuardedApart`] exactly when step 2 answers
///   at the root; otherwise the walk's answer — apart on a mismatch in a rigid
///   context, deferred with the first reason met when any pair deferred, equal
///   when every pair agreed.
/// - provides: the value half of the pipeline's three search-free steps. A
///   distinct answer is sound relative to β, δ and the η-equations, because
///   every pair an η-equation or an unfolding could relate is deferred rather
///   than separated.
/// - fails: [`ConversionFault::Domain`] when a node the walk reaches does not
///   resolve, and [`ConversionFault::LiteralPayload`] when a domain literal
///   names a core node that is not a literal.
/// - panics: none.
/// - intension: each distinct pair reached is compared once per call, so a
///   comparison costs the number of distinct pairs rather than the expansion of
///   the two graphs.
///
/// # Errors
/// - [`ConversionFault::Domain`] — a reached node does not resolve.
/// - [`ConversionFault::LiteralPayload`] — a literal names no core literal.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surfaces are the three steps and the walk's
///   context rule, separated by a pair each step answers that the previous one
///   does not, pairs deferred for each reason, a mismatch under an unfoldable
///   head deferring where the same mismatch under a rigid head separates, and a
///   shared graph whose expansion is exponential in its depth compared in
///   linear steps. A dangling identity is refused before step 1; accepting it
///   or changing the step precedence changes a boundary observation.
/// - witness: `conv::tests::identical_truncated_values_are_refused`
/// - witness: `conv::tests::identity_answers_one_node_and_one_source_term`
/// - witness: `conv::tests::the_guard_answers_a_rigid_pair_identity_does_not`
/// - witness: `conv::tests::structure_answers_what_the_guard_cannot`
/// - witness: `conv::tests::a_pair_needing_an_unfolding_or_a_binder_is_deferred`
/// - witness: `conv::tests::a_mismatch_separates_only_beneath_a_rigid_head`
/// - witness: `conv::tests::a_shared_graph_is_compared_once_per_pair`
#[inline]
#[spec(ensures: |ret| match early_values(domain, left, right) {
    Ok(Early::Identical) => ret == Ok(Settlement::Identical),
    Ok(Early::Apart) => ret == Ok(Settlement::GuardedApart),
    Ok(Early::Open) => !matches!(ret, Ok(Settlement::Identical | Settlement::GuardedApart)),
    Err(fault) => ret == Err(fault),
})]
pub fn convert_values(
    core: &CoreArena,
    domain: &DomainArena,
    left: DomainValueId,
    right: DomainValueId,
) -> Result<Settlement, ConversionFault>
{
    let early = early_values(domain, left, right)?;
    match early {
        Early::Identical => Ok(Settlement::Identical),
        Early::Apart => Ok(Settlement::GuardedApart),
        Early::Open => Walk::new(core, domain).settle(Goal::Values(left, right, Context::Rigid)),
    }
}

/// Run steps 1 through 3 on two weak-head domain computations.
///
/// # Specification
/// - requires: `core` is the arena the computations' literal payloads live in,
///   and both computations live in `domain`.
/// - ensures: [`Settlement::Identical`] exactly when step 1 answers at the
///   root; otherwise [`Settlement::GuardedApart`] exactly when step 2 answers
///   at the root; otherwise the walk's answer, read as for values.
/// - provides: the computation half of the pipeline's three search-free steps,
///   sound in the same sense as the value half.
/// - fails: [`ConversionFault::Domain`] and [`ConversionFault::LiteralPayload`]
///   as for values.
/// - panics: none.
/// - intension: each distinct pair reached is compared once per call.
///
/// # Errors
/// - [`ConversionFault::Domain`] — a reached node does not resolve.
/// - [`ConversionFault::LiteralPayload`] — a literal names no core literal.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surfaces are the three computation arms and
///   their mixtures, separated by two returners apart on their values, a lambda
///   against a neutral deferred to a binder, a returner against a rigid neutral
///   separated, and a lambda against a returner separated. A dangling identity
///   is refused before step 1; accepting it or changing the step precedence
///   changes a boundary observation.
/// - witness: `conv::tests::identical_truncated_computations_are_refused`
/// - witness: `conv::tests::computations_settle_by_their_weak_heads`
/// - witness: `conv::tests::a_pair_needing_an_unfolding_or_a_binder_is_deferred`
#[inline]
#[spec(ensures: |ret| match early_comps(domain, left, right) {
    Ok(Early::Identical) => ret == Ok(Settlement::Identical),
    Ok(Early::Apart) => ret == Ok(Settlement::GuardedApart),
    Ok(Early::Open) => !matches!(ret, Ok(Settlement::Identical | Settlement::GuardedApart)),
    Err(fault) => ret == Err(fault),
})]
pub fn convert_computations(
    core: &CoreArena,
    domain: &DomainArena,
    left: DomainCompId,
    right: DomainCompId,
) -> Result<Settlement, ConversionFault>
{
    let early = early_comps(domain, left, right)?;
    match early {
        Early::Identical => Ok(Settlement::Identical),
        Early::Apart => Ok(Settlement::GuardedApart),
        Early::Open => Walk::new(core, domain).settle(Goal::Comps(left, right, Context::Rigid)),
    }
}

impl<'run> Walk<'run>
{
    /// A walk over `domain` with no pair met.
    ///
    /// # Specification
    /// trivial.
    fn new(
        core: &'run CoreArena,
        domain: &'run DomainArena,
    ) -> Self
    {
        Self {
            core,
            domain,
            goals: Vec::new(),
            met: BTreeSet::new(),
            outstanding: Outstanding::Nothing,
        }
    }

    /// Walk from `root` and read the walk's end as a step-3 settlement.
    ///
    /// # Specification
    /// - requires: steps 1 and 2 left `root` open.
    /// - ensures: [`Settlement::StructurallyApart`] when the walk met a
    ///   separating mismatch; otherwise [`Settlement::Deferred`] with the first
    ///   reason met, or [`Settlement::StructurallyEqual`] when nothing
    ///   deferred.
    /// - provides: the one reading of a finished walk.
    /// - fails: whatever a pair's comparison refuses.
    /// - panics: none.
    ///
    /// # Errors
    /// Whatever [`Walk::run`] refuses.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — structural equality, binder deferral, unfolding
    ///   deferral and a later rigid refutation produce distinct settlements;
    ///   overwriting the first reason or allowing it to mask a rigid refutation
    ///   changes the observed answer.
    /// - witness: `conv::tests::structure_answers_what_the_guard_cannot`
    /// - witness: `conv::tests::the_first_deferral_is_retained_until_a_rigid_refutation`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |settlement| match *settlement {
        Settlement::StructurallyEqual => self.goals.is_empty() && self.outstanding == Outstanding::Nothing,
        Settlement::Deferred(reason) => self.goals.is_empty() && self.outstanding == Outstanding::Deferred(reason),
        Settlement::StructurallyApart => true,
        Settlement::Identical | Settlement::GuardedApart => false,
    }))]
    fn settle(
        mut self,
        root: Goal,
    ) -> Result<Settlement, ConversionFault>
    {
        self.goals.push(root);
        let walked = self.run()?;
        Ok(match (walked, self.outstanding) {
            (Walked::Apart, _) => Settlement::StructurallyApart,
            (Walked::Exhausted, Outstanding::Deferred(reason)) => Settlement::Deferred(reason),
            (Walked::Exhausted, Outstanding::Nothing) => Settlement::StructurallyEqual,
        })
    }

    /// Compare pairs until a separating mismatch or until none is left.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Walked::Apart`] at the first pair whose heads differ in a
    ///   rigid context; otherwise [`Walked::Exhausted`] once every queued pair
    ///   has been met, with the first deferral recorded.
    /// - provides: the one loop; every comparison is an arm of it, so there is
    ///   no call cycle. A pair met before is skipped.
    /// - fails: whatever a pair's comparison refuses.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ConversionFault`] as the pair comparisons raise it.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the first of two different deferrals is retained, a
    ///   rigid mismatch overrides the deferred settlement, and a shared graph
    ///   settles without expanding its repeated subgraphs; leaving queued work
    ///   or replacing the first reason changes a result.
    /// - witness: `conv::tests::the_first_deferral_is_retained_until_a_rigid_refutation`
    /// - witness: `conv::tests::a_shared_graph_is_compared_once_per_pair`
    #[spec(
        captures: entry_outstanding = self.outstanding,
        ensures: |ret| (ret != Ok(Walked::Exhausted) || self.goals.is_empty())
            && (entry_outstanding == Outstanding::Nothing || self.outstanding == entry_outstanding),
    )]
    fn run(&mut self) -> Result<Walked, ConversionFault>
    {
        while let Some(goal) = self.goals.pop() {
            if !self.met.insert(goal) {
                continue;
            }
            let (local, context) = match goal {
                Goal::Values(left, right, context) => {
                    let local = self.values(left, right, context)?;
                    (local, context)
                },
                Goal::Comps(left, right, context) => {
                    let local = self.comps(left, right, context)?;
                    (local, context)
                },
                Goal::Neutrals(left, right, context) => {
                    let local = self.neutrals(left, right, context)?;
                    (local, context)
                },
                Goal::Closures(left, right) => {
                    let local = self.closures(left, right)?;
                    (local, Context::Flexible(Deferral::Binder))
                },
            };
            match (local, context) {
                (Local::Agree, _) => {},
                (Local::Disagree, Context::Rigid) => return Ok(Walked::Apart),
                (Local::Disagree, Context::Flexible(reason)) | (Local::Defer(reason), _) => {
                    self.defer(reason);
                },
            }
        }
        Ok(Walked::Exhausted)
    }

    /// Record `reason` unless a deferral is already recorded.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the first deferral is recorded; a later reason preserves it.
    /// - provides: stable precedence among unresolved structural comparisons.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an empty slot accepts either reason and an occupied
    ///   slot retains its first reason. Pairs presenting binder and unfolding
    ///   deferrals in both orders observe the chosen reason; a later rigid
    ///   refutation still wins. Overwriting or ignoring the first reason
    ///   changes those public settlements.
    /// - witness: `conv::tests::the_first_deferral_is_retained_until_a_rigid_refutation`
    #[spec(
        captures: [prior = self.outstanding],
        ensures: self.outstanding == match prior {
            Outstanding::Nothing => Outstanding::Deferred(reason),
            Outstanding::Deferred(_) => prior,
        }
    )]
    fn defer(
        &mut self,
        reason: Deferral,
    )
    {
        if self.outstanding == Outstanding::Nothing {
            self.outstanding = Outstanding::Deferred(reason);
        }
    }

    /// Whether a mismatch at a neutral is final: its head is rigid, or it may
    /// unfold, or it stands on a hole or a mark a fill may make anything.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Context::Flexible`] for a hole or a mark head whatever its
    ///   face, for unfolding when another head's face is unforced or forced,
    ///   and [`Context::Rigid`] when that face is rigid.
    /// - provides: the one reading of "could unfolding or a fill repair a
    ///   mismatch here".
    /// - fails: [`ConversionFault::Domain`] when the neutral does not resolve.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ConversionFault::Domain`] — the neutral does not resolve.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the same argument mismatch separates under a rigid
    ///   head and defers under a loaded head, and a hole against a literal
    ///   defers where a rigid variable against it separates; classifying a
    ///   loaded face or a hole as rigid makes conversion unsound.
    /// - witness: `conv::tests::a_mismatch_separates_only_beneath_a_rigid_head`
    /// - witness: `live::tests::a_comparison_that_meets_a_hole_declines`
    #[spec(ensures: |ret| self.domain.neutral(neutral).map_or_else(
        || ret == Err(ConversionFault::Domain(DomainFault::Dangling)),
        |node| ret == Ok(match (node.head(), node.unfolding()) {
            (NeutralHead::Hole { .. } | NeutralHead::Mark { .. } | NeutralHead::Returned(_), _) => Context::Flexible(Deferral::Indeterminate),
            (_, Unfolding::Rigid) => Context::Rigid,
            (_, Unfolding::Unforced(_) | Unfolding::Forced(_)) => Context::Flexible(Deferral::Unfolding),
        }),
    ))]
    fn unfoldable(
        &self,
        neutral: NeutralId,
    ) -> Result<Context, ConversionFault>
    {
        let Some(held) = self.domain.neutral(neutral)
        else {
            return Err(ConversionFault::Domain(DomainFault::Dangling));
        };
        Ok(match (held.head(), held.unfolding()) {
            (NeutralHead::Hole { .. } | NeutralHead::Mark { .. } | NeutralHead::Returned(_), _) => {
                Context::Flexible(Deferral::Indeterminate)
            },
            (
                NeutralHead::Variable { .. } | NeutralHead::Constant(_) | NeutralHead::Module(_),
                Unfolding::Rigid,
            ) => Context::Rigid,
            (
                NeutralHead::Variable { .. } | NeutralHead::Constant(_) | NeutralHead::Module(_),
                Unfolding::Unforced(_) | Unfolding::Forced(_),
            ) => Context::Flexible(Deferral::Unfolding),
        })
    }

    /// What a neutral standing against a non-neutral former means: a
    /// mismatch, or a deferral when its head could unfold into that former.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Local::Defer`] for unfolding when the head has a body,
    ///   [`Local::Disagree`] when it is rigid.
    /// - provides: the rule for a stuck side against a constructor that no
    ///   η-equation relates it to.
    /// - fails: [`ConversionFault::Domain`] when the neutral does not resolve.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ConversionFault::Domain`] — the neutral does not resolve.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a returner separates from a rigid neutral but defers
    ///   against a defined one, and a defined value may meet unit after
    ///   unfolding; refusing the unfolding opportunity changes the verdict.
    /// - witness: `conv::tests::computations_settle_by_their_weak_heads`
    /// - witness: `conv::tests::a_pair_needing_an_unfolding_or_a_binder_is_deferred`
    #[spec(ensures: |ret| ret == self.unfoldable(neutral).map(|context| match context {
        Context::Rigid => Local::Disagree,
        Context::Flexible(reason) => Local::Defer(reason),
    }))]
    fn neutral_against_former(
        &self,
        neutral: NeutralId,
    ) -> Result<Local, ConversionFault>
    {
        let context = self.unfoldable(neutral)?;
        Ok(match context {
            Context::Rigid => Local::Disagree,
            Context::Flexible(reason) => Local::Defer(reason),
        })
    }

    /// The literal a domain literal's core id names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the payload the core node holds.
    /// - provides: the one core read the walk makes.
    /// - fails: [`ConversionFault::LiteralPayload`] when the node is missing or
    ///   is not a literal.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ConversionFault::LiteralPayload`] — no core literal at `literal`.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — equal literal contents at different core ids compare
    ///   structurally, while a unit id and an absent id are refused as
    ///   payloads; confusing a nonliteral node with a literal changes the named
    ///   refusal.
    /// - witness: `conv::tests::structure_answers_what_the_guard_cannot`
    /// - witness: `conv::tests::a_payload_read_refuses_nonliteral_and_missing_nodes`
    #[spec(ensures: |ret| ret.is_ok() == matches!(self.core.value(literal), Some(Value::Literal(_)))
        && ret.as_ref().err().is_none_or(|fault| *fault == ConversionFault::LiteralPayload { literal }))]
    fn payload(
        &self,
        literal: ValueId,
    ) -> Result<&'run Literal, ConversionFault>
    {
        match self.core.value(literal) {
            Some(&Value::Literal(ref payload)) => Ok(payload),
            Some(_) | None => Err(ConversionFault::LiteralPayload { literal }),
        }
    }

    /// Compare two values' own structure, queueing their children.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Local::Agree`] when steps 1 or 2 found the pair identical,
    ///   or when both sides have one former over agreeing payloads — their
    ///   children then queued at `context`, a thunk's closure as a closure
    ///   pair, a neutral as a neutral pair; [`Local::Disagree`] when step 2
    ///   separated them, when two formers or two payloads differ, or when a
    ///   rigid neutral meets a former; [`Local::Defer`] when a neutral meets a
    ///   thunk or a static lambda, or an unfoldable neutral meets a former. Two
    ///   static lambdas agree or disagree as their α-walk finds, and defer when
    ///   it cannot tell.
    /// - provides: the value arms of step 3, head-mismatch first.
    /// - fails: [`ConversionFault`] for a side, a level or a payload that does
    ///   not resolve.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ConversionFault`] for an unresolved node.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — structural children distinguish agreement from a
    ///   rigid mismatch, while a binder or an unfoldable head forces deferral;
    ///   suppressing a child, turning deferral into disagreement or proceeding
    ///   after an early answer changes the settlement.
    /// - witness: `conv::tests::structure_answers_what_the_guard_cannot`
    /// - witness: `conv::tests::a_pair_needing_an_unfolding_or_a_binder_is_deferred`
    /// - witness: `eval::tests::native_certificate_conversion_retains_map_syntax`
    /// - witness: `conv::tests::family_spines_are_separated_by_head_index_and_arity`
    /// - witness: `conv::tests::each_former_agrees_with_its_twin_at_another_id`
    /// - witness: `conv::tests::two_flows_of_different_formers_are_apart_over_the_same_parts`
    /// - witness: `conv::tests::a_record_with_more_labels_than_fields_is_refused_on_either_side`
    #[spec(
        captures: entry_goals = self.goals.len(),
        ensures: |ret| self.goals.len() >= entry_goals
            && (ret == Ok(Local::Agree) || self.goals.len() == entry_goals)
            && match early_values(self.domain, left, right) {
                Ok(Early::Identical) => ret == Ok(Local::Agree),
                Ok(Early::Apart) => ret == Ok(Local::Disagree),
                Ok(Early::Open) => true,
                Err(fault) => ret == Err(fault),
            } && match (self.domain.value(left), self.domain.value(right)) {
                (Some(&DomainValue::PathCertificate { .. }), Some(&DomainValue::PathProduct { .. })) | (Some(&DomainValue::PathProduct { .. }), Some(&DomainValue::PathCertificate { .. })) => ret == Ok(Local::Disagree),
                (Some(&DomainValue::PathCertificate { certificate: a, .. }), Some(&DomainValue::PathCertificate { certificate: b, .. })) if a == b => ret == Ok(Local::Agree) && self.goals.len() == entry_goals,
                _ => true,
            },
    )]
    fn values(
        &mut self,
        left: DomainValueId,
        right: DomainValueId,
        context: Context,
    ) -> Result<Local, ConversionFault>
    {
        let early = early_values(self.domain, left, right)?;
        match early {
            Early::Identical => return Ok(Local::Agree),
            Early::Apart => return Ok(Local::Disagree),
            Early::Open => {},
        }
        let (Some(&one), Some(&other)) = (self.domain.value(left), self.domain.value(right))
        else {
            return Err(ConversionFault::Domain(DomainFault::Dangling));
        };
        match (one, other) {
            (
                DomainValue::Constructor {
                    datatype: left_code,
                    tag: left_tag,
                    fields: left_fields,
                    ..
                },
                DomainValue::Constructor {
                    datatype: right_code,
                    tag: right_tag,
                    fields: right_fields,
                    ..
                },
            ) => {
                let left_fields = self
                    .domain
                    .fields(left_fields)
                    .map_err(ConversionFault::Domain)?;
                let right_fields = self
                    .domain
                    .fields(right_fields)
                    .map_err(ConversionFault::Domain)?;
                if left_tag != right_tag || left_fields.len() != right_fields.len() {
                    return Ok(Local::Disagree);
                }
                match compare_codes(
                    self.core,
                    self.domain,
                    ConstantReading::Unread,
                    left_code,
                    right_code,
                )? {
                    CodeComparison::Apart => return Ok(Local::Disagree),
                    CodeComparison::Undecided => return Ok(Local::Defer(Deferral::Unfolding)),
                    CodeComparison::Equal => {},
                }
                self.goals.extend(
                    left_fields
                        .iter()
                        .zip(right_fields)
                        .rev()
                        .map(|(a, b)| Goal::Values(*a, *b, context)),
                );
                Ok(Local::Agree)
            },
            (
                DomainValue::Record {
                    source: left_source,
                    fields: left_fields,
                    ..
                },
                DomainValue::Record {
                    source: right_source,
                    fields: right_fields,
                    ..
                },
            ) => {
                let (Some(left_node), Some(right_node)) =
                    (self.core.value(left_source), self.core.value(right_source))
                else {
                    return Err(ConversionFault::MachineInvariant);
                };
                let gandr_core_term::Value::Record(ref left_labels) = *left_node
                else {
                    return Err(ConversionFault::MachineInvariant);
                };
                let gandr_core_term::Value::Record(ref right_labels) = *right_node
                else {
                    return Err(ConversionFault::MachineInvariant);
                };
                let left_fields = self
                    .domain
                    .fields(left_fields)
                    .map_err(ConversionFault::Domain)?;
                let right_fields = self
                    .domain
                    .fields(right_fields)
                    .map_err(ConversionFault::Domain)?;
                if left_labels.len() != left_fields.len()
                    || right_labels.len() != right_fields.len()
                {
                    return Err(ConversionFault::MachineInvariant);
                }
                if !left_labels.keys().eq(right_labels.keys()) {
                    return Ok(Local::Disagree);
                }
                self.goals.extend(
                    left_fields
                        .iter()
                        .zip(right_fields)
                        .rev()
                        .map(|(a, b)| Goal::Values(*a, *b, context)),
                );
                Ok(Local::Agree)
            },
            (
                DomainValue::PathCertificate { .. } | DomainValue::PathProduct { .. },
                DomainValue::PathCertificate { .. } | DomainValue::PathProduct { .. },
            ) => Ok(
                if equal_paths(self.core, self.domain, left, right)?
                    == gandr_core_term::CertificateEquality::Equal
                {
                    Local::Agree
                }
                else {
                    Local::Disagree
                },
            ),
            (DomainValue::ListNil { .. }, DomainValue::ListNil { .. }) => Ok(Local::Agree),
            (
                DomainValue::Tuple {
                    fields: left_fields,
                    ..
                },
                DomainValue::Tuple {
                    fields: right_fields,
                    ..
                },
            ) => {
                let left_fields = self
                    .domain
                    .fields(left_fields)
                    .map_err(ConversionFault::Domain)?;
                let right_fields = self
                    .domain
                    .fields(right_fields)
                    .map_err(ConversionFault::Domain)?;
                if left_fields.len() != right_fields.len() {
                    return Ok(Local::Disagree);
                }
                self.goals.extend(
                    left_fields
                        .iter()
                        .zip(right_fields)
                        .rev()
                        .map(|(a, b)| Goal::Values(*a, *b, context)),
                );
                Ok(Local::Agree)
            },
            (
                DomainValue::Flow {
                    former: left_former,
                    parts: left_parts,
                    ..
                },
                DomainValue::Flow {
                    former: right_former,
                    parts: right_parts,
                    ..
                },
            ) => {
                let left_parts = self
                    .domain
                    .fields(left_parts)
                    .map_err(ConversionFault::Domain)?;
                let right_parts = self
                    .domain
                    .fields(right_parts)
                    .map_err(ConversionFault::Domain)?;
                if left_former != right_former || left_parts.len() != right_parts.len() {
                    return Ok(Local::Disagree);
                }
                self.goals.extend(
                    left_parts
                        .iter()
                        .zip(right_parts)
                        .rev()
                        .map(|(a, b)| Goal::Values(*a, *b, context)),
                );
                Ok(Local::Agree)
            },
            (
                DomainValue::Literal { literal: first, .. },
                DomainValue::Literal {
                    literal: second, ..
                },
            ) => {
                if first == second {
                    return Ok(Local::Agree);
                }
                let left_payload = self.payload(first)?;
                let right_payload = self.payload(second)?;
                Ok(if left_payload == right_payload {
                    Local::Agree
                }
                else {
                    Local::Disagree
                })
            },
            (
                DomainValue::ListCons {
                    first: left_first,
                    second: left_second,
                    ..
                },
                DomainValue::ListCons {
                    first: right_first,
                    second: right_second,
                    ..
                },
            ) => {
                self.goals
                    .push(Goal::Values(left_second, right_second, context));
                self.goals
                    .push(Goal::Values(left_first, right_first, context));
                Ok(Local::Agree)
            },
            (
                DomainValue::Injection {
                    summand: left_summand,
                    body: left_body,
                    ..
                },
                DomainValue::Injection {
                    summand: right_summand,
                    body: right_body,
                    ..
                },
            ) => {
                if left_summand != right_summand {
                    return Ok(Local::Disagree);
                }
                self.goals
                    .push(Goal::Values(left_body, right_body, context));
                Ok(Local::Agree)
            },
            (
                DomainValue::Here {
                    point: left_point, ..
                },
                DomainValue::Here {
                    point: right_point, ..
                },
            ) => {
                self.goals
                    .push(Goal::Values(left_point, right_point, context));
                Ok(Local::Agree)
            },
            (
                DomainValue::Univalence {
                    record: left_record,
                    ..
                },
                DomainValue::Univalence {
                    record: right_record,
                    ..
                },
            ) => {
                self.goals
                    .push(Goal::Values(left_record, right_record, context));
                Ok(Local::Agree)
            },
            // A held transport compares its family under a binder, which the
            // machine reads.
            (DomainValue::HeldTransport { .. }, DomainValue::HeldTransport { .. }) => {
                Ok(Local::Defer(Deferral::Binder))
            },
            (
                DomainValue::Thunk {
                    body: left_body, ..
                },
                DomainValue::Thunk {
                    body: right_body, ..
                },
            ) => {
                self.goals.push(Goal::Closures(left_body, right_body));
                Ok(Local::Agree)
            },
            (
                DomainValue::Lift {
                    target: left_target,
                    body: left_body,
                    ..
                },
                DomainValue::Lift {
                    target: right_target,
                    body: right_body,
                    ..
                },
            ) => {
                let (Some(left_level), Some(right_level)) = (
                    self.domain.level(left_target),
                    self.domain.level(right_target),
                )
                else {
                    return Err(ConversionFault::Domain(DomainFault::Dangling));
                };
                if left_level.level() != right_level.level() {
                    return Ok(Local::Disagree);
                }
                self.goals
                    .push(Goal::Values(left_body, right_body, context));
                Ok(Local::Agree)
            },
            (
                DomainValue::Code {
                    code: left_code, ..
                },
                DomainValue::Code {
                    code: right_code, ..
                },
            ) => Ok(
                match compare_codes(
                    self.core,
                    self.domain,
                    ConstantReading::Unread,
                    left_code,
                    right_code,
                )? {
                    CodeComparison::Equal => Local::Agree,
                    CodeComparison::Apart => Local::Disagree,
                    CodeComparison::Undecided => Local::Defer(Deferral::Unfolding),
                },
            ),
            (
                DomainValue::StaticLambda {
                    lambda: left_lambda,
                    ..
                },
                DomainValue::StaticLambda {
                    lambda: right_lambda,
                    ..
                },
            ) => Ok(
                match compare_codes(
                    self.core,
                    self.domain,
                    ConstantReading::Unread,
                    left_lambda,
                    right_lambda,
                )? {
                    CodeComparison::Equal => Local::Agree,
                    CodeComparison::Apart => Local::Disagree,
                    CodeComparison::Undecided => Local::Defer(Deferral::Unfolding),
                },
            ),
            (
                DomainValue::Neutral {
                    neutral: left_neutral,
                    ..
                },
                DomainValue::Neutral {
                    neutral: right_neutral,
                    ..
                },
            ) => {
                self.goals
                    .push(Goal::Neutrals(left_neutral, right_neutral, context));
                Ok(Local::Agree)
            },
            (
                DomainValue::Neutral { .. },
                DomainValue::Thunk { .. } | DomainValue::StaticLambda { .. },
            )
            | (
                DomainValue::Thunk { .. } | DomainValue::StaticLambda { .. },
                DomainValue::Neutral { .. },
            ) => Ok(Local::Defer(Deferral::Binder)),
            (DomainValue::Neutral { neutral, .. }, _)
            | (_, DomainValue::Neutral { neutral, .. }) => self.neutral_against_former(neutral),
            (
                DomainValue::PathCertificate { .. }
                | DomainValue::Constructor { .. }
                | DomainValue::Record { .. }
                | DomainValue::PathProduct { .. }
                | DomainValue::Here { .. }
                | DomainValue::Univalence { .. }
                | DomainValue::HeldTransport { .. }
                | DomainValue::Flow { .. }
                | DomainValue::Tuple { .. }
                | DomainValue::Literal { .. }
                | DomainValue::ListNil { .. }
                | DomainValue::ListCons { .. }
                | DomainValue::Injection { .. }
                | DomainValue::Thunk { .. }
                | DomainValue::Lift { .. }
                | DomainValue::Code { .. }
                | DomainValue::StaticLambda { .. },
                _,
            ) => Ok(Local::Disagree),
        }
    }

    /// Compare two weak-head computations' own structure, queueing their
    /// children.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Local::Agree`] when steps 1 or 2 found the pair identical,
    ///   or when both sides have one former — their children then queued;
    ///   [`Local::Disagree`] when step 2 separated them, when a lambda meets a
    ///   returner, or when a rigid neutral meets a returner; [`Local::Defer`]
    ///   when a neutral meets a lambda, or an unfoldable neutral meets a
    ///   returner.
    /// - provides: the computation arms of step 3, head-mismatch first.
    /// - fails: [`ConversionFault::Domain`] for a side that does not resolve.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ConversionFault::Domain`] — a side does not resolve.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — structural children distinguish agreement from a
    ///   rigid mismatch, while a binder or an unfoldable head forces deferral;
    ///   suppressing a child, turning deferral into disagreement or proceeding
    ///   after an early answer changes the settlement.
    /// - witness: `conv::tests::computations_settle_by_their_weak_heads`
    /// - witness: `conv::tests::a_pair_needing_an_unfolding_or_a_binder_is_deferred`
    #[spec(
        captures: entry_goals = self.goals.len(),
        ensures: |ret| self.goals.len() >= entry_goals
            && (ret == Ok(Local::Agree) || self.goals.len() == entry_goals)
            && match early_comps(self.domain, left, right) {
                Ok(Early::Identical) => ret == Ok(Local::Agree),
                Ok(Early::Apart) => ret == Ok(Local::Disagree),
                Ok(Early::Open) => true,
                Err(fault) => ret == Err(fault),
            },
    )]
    fn comps(
        &mut self,
        left: DomainCompId,
        right: DomainCompId,
        context: Context,
    ) -> Result<Local, ConversionFault>
    {
        let early = early_comps(self.domain, left, right)?;
        match early {
            Early::Identical => return Ok(Local::Agree),
            Early::Apart => return Ok(Local::Disagree),
            Early::Open => {},
        }
        let (Some(&one), Some(&other)) = (
            self.domain.computation(left),
            self.domain.computation(right),
        )
        else {
            return Err(ConversionFault::Domain(DomainFault::Dangling));
        };
        match (one, other) {
            (
                DomainComp::Lambda {
                    body: left_body, ..
                },
                DomainComp::Lambda {
                    body: right_body, ..
                },
            ) => {
                self.goals.push(Goal::Closures(left_body, right_body));
                Ok(Local::Agree)
            },
            (
                DomainComp::Return {
                    value: left_value, ..
                },
                DomainComp::Return {
                    value: right_value, ..
                },
            ) => {
                self.goals
                    .push(Goal::Values(left_value, right_value, context));
                Ok(Local::Agree)
            },
            (
                DomainComp::Neutral {
                    neutral: left_neutral,
                    ..
                },
                DomainComp::Neutral {
                    neutral: right_neutral,
                    ..
                },
            ) => {
                self.goals
                    .push(Goal::Neutrals(left_neutral, right_neutral, context));
                Ok(Local::Agree)
            },
            // Two fixpoints compare by congruence: their own closed source
            // nodes, then the leading arguments each has taken, pairwise. A
            // fixpoint never unfolds to meet anything else.
            (
                DomainComp::Fixpoint {
                    recursive: left_recursive,
                    leading: left_leading,
                    ..
                },
                DomainComp::Fixpoint {
                    recursive: right_recursive,
                    leading: right_leading,
                    ..
                },
            ) => {
                let left_leading = self
                    .domain
                    .fields(left_leading)
                    .map_err(ConversionFault::Domain)?;
                let right_leading = self
                    .domain
                    .fields(right_leading)
                    .map_err(ConversionFault::Domain)?;
                if left_leading.len() != right_leading.len() {
                    return Ok(Local::Disagree);
                }
                self.goals
                    .push(Goal::Closures(left_recursive, right_recursive));
                self.goals.extend(
                    left_leading
                        .iter()
                        .zip(right_leading)
                        .map(|(&one, &other)| Goal::Values(one, other, context)),
                );
                Ok(Local::Agree)
            },
            (DomainComp::Neutral { .. }, DomainComp::Lambda { .. })
            | (DomainComp::Lambda { .. }, DomainComp::Neutral { .. }) => {
                Ok(Local::Defer(Deferral::Binder))
            },
            (
                DomainComp::Neutral { neutral, .. },
                DomainComp::Return { .. } | DomainComp::Fixpoint { .. },
            )
            | (
                DomainComp::Return { .. } | DomainComp::Fixpoint { .. },
                DomainComp::Neutral { neutral, .. },
            ) => self.neutral_against_former(neutral),
            (
                DomainComp::Lambda { .. },
                DomainComp::Return { .. } | DomainComp::Fixpoint { .. },
            )
            | (
                DomainComp::Return { .. },
                DomainComp::Lambda { .. } | DomainComp::Fixpoint { .. },
            )
            | (
                DomainComp::Fixpoint { .. },
                DomainComp::Lambda { .. } | DomainComp::Return { .. },
            ) => Ok(Local::Disagree),
        }
    }

    /// Compare two neutrals: heads first, then spines elimination by
    /// elimination.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: validation precedes identity: [`Local::Agree`] when resolving
    ///   ids are equal, or when the heads agree and the spines have one length
    ///   and one elimination kind at every position — each operand pair then
    ///   queued beneath the head, flexible for unfolding when the head has a
    ///   body; two returned heads agree as heads with their stuck computations
    ///   queued beneath; two transports or rides queue their operands alone
    ///   when their motives read alike through their captures
    ///   ([`crate::code::motives_alike`]); [`Local::Defer`] for a binder when
    ///   the heads agree and the spines owe a commuting conversion of `F` first
    ///   ([`crate::rules::bind_step`]); [`Local::Disagree`] when the guards
    ///   separate the neutrals, or when rigid heads differ or a rigid head's
    ///   spines disagree in shape; [`Local::Defer`] for unfolding when either
    ///   head has a body and the heads or the spine shapes differ.
    /// - provides: Courant–Leroy's `var-1`, `var-2`, `var-3` and `const` rules,
    ///   with `var-2` the head-mismatch fast-fail.
    /// - fails: [`ConversionFault::Domain`] for a neutral that does not
    ///   resolve.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ConversionFault::Domain`] — a neutral does not resolve.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — rigid and loaded heads give different answers to the
    ///   same spine mismatch, head and arity differences separate rigid
    ///   families, and identity is refused after truncation; skipping
    ///   validation or losing the flexible context changes the result.
    /// - witness: `conv::tests::a_mismatch_separates_only_beneath_a_rigid_head`
    /// - witness: `machine::tests::the_laws_of_bind_convert_by_their_decisions`
    /// - witness: `conv::tests::family_spines_are_separated_by_head_index_and_arity`
    /// - witness: `conv::tests::identical_truncated_neutrals_and_closures_are_refused`
    /// - witness: `eval::tests::native_transport_sequences_product_components`
    /// - witness: `conv::tests::a_neutral_one_bind_short_of_its_twin_waits_for_return_eta`
    /// - witness: `conv::tests::two_cases_over_as_many_branches_compare_their_branches`
    /// - witness: `identity::tests::stuck_transports_under_one_motive_over_captures_it_does_not_read_settle_alike`
    #[spec(ensures: |ret| if self.domain.neutral(left).is_some() && self.domain.neutral(right).is_some() {
        ret.is_ok() && (left != right || ret == Ok(Local::Agree))
            && (ret != Ok(Local::Agree) || self.domain.neutral(left).zip(self.domain.neutral(right)).is_some_and(|(one, other)|
                (one.head() == other.head() || matches!((one.head(), other.head()), (NeutralHead::Returned(_), NeutralHead::Returned(_))))
                    && one.spine().len() == other.spine().len()
                    && one.spine().iter().zip(other.spine()).all(|(a, b)| core::mem::discriminant(a) == core::mem::discriminant(b))))
    } else { ret == Err(ConversionFault::Domain(DomainFault::Dangling)) })]
    fn neutrals(
        &mut self,
        left: NeutralId,
        right: NeutralId,
        context: Context,
    ) -> Result<Local, ConversionFault>
    {
        let Ok(left_guard) = self.domain.neutral_guard(left)
        else {
            return Err(ConversionFault::Domain(DomainFault::Dangling));
        };
        if left == right {
            return Ok(Local::Agree);
        }
        let Ok(right_guard) = self.domain.neutral_guard(right)
        else {
            return Err(ConversionFault::Domain(DomainFault::Dangling));
        };
        if left_guard.settles(right_guard) == GuardAnswer::Apart {
            return Ok(Local::Disagree);
        }
        let left_context = self.unfoldable(left)?;
        let right_context = self.unfoldable(right)?;
        let beneath = match (left_context, right_context) {
            (Context::Rigid, Context::Rigid) => context,
            (Context::Flexible(reason), _) | (_, Context::Flexible(reason)) => {
                Context::Flexible(reason)
            },
        };
        let mismatch = match beneath {
            Context::Rigid => Local::Disagree,
            Context::Flexible(reason) => Local::Defer(reason),
        };
        let (Some(one), Some(other)) = (self.domain.neutral(left), self.domain.neutral(right))
        else {
            return Err(ConversionFault::Domain(DomainFault::Dangling));
        };
        let one_head = matches!(
            (one.head(), other.head()),
            (NeutralHead::Returned(_), NeutralHead::Returned(_))
        ) || one.head() == other.head();
        if one_head
            && crate::rules::bind_step(one.spine(), other.spine()) != crate::rules::BindStep::Normal
        {
            return Ok(Local::Defer(Deferral::Binder));
        }
        if one.spine().len() != other.spine().len() {
            return Ok(mismatch);
        }
        let mut queued = Vec::new();
        match (one.head(), other.head()) {
            (NeutralHead::Returned(left_head), NeutralHead::Returned(right_head)) => {
                queued.push(Goal::Comps(left_head, right_head, beneath));
            },
            (left_head, right_head) if left_head != right_head => return Ok(mismatch),
            _ => {},
        }
        for (&left_elimination, &right_elimination) in one.spine().iter().zip(other.spine()) {
            match (left_elimination, right_elimination) {
                (Elimination::DataCase(left), Elimination::DataCase(right)) => {
                    let (_, left_branches) =
                        crate::rules::case_source(self.core, self.domain, left)?;
                    let (_, right_branches) =
                        crate::rules::case_source(self.core, self.domain, right)?;
                    if left_branches.len() != right_branches.len() {
                        return Ok(mismatch);
                    }
                    queued.push(Goal::Closures(left, right));
                },
                // A split's closure holds the split itself, so one source
                // body already fixes the arity.
                (Elimination::Split(left), Elimination::Split(right)) => {
                    queued.push(Goal::Closures(left, right));
                },
                (Elimination::Projection(left), Elimination::Projection(right)) => {
                    if crate::rules::projection_key(self.core, left)?
                        != crate::rules::projection_key(self.core, right)?
                    {
                        return Ok(mismatch);
                    }
                },
                (
                    Elimination::PathTransport {
                        motive: left_motive,
                        value: left_value,
                    },
                    Elimination::PathTransport {
                        motive: right_motive,
                        value: right_value,
                    },
                )
                | (
                    Elimination::Ride {
                        motive: left_motive,
                        value: left_value,
                    },
                    Elimination::Ride {
                        motive: right_motive,
                        value: right_value,
                    },
                )
                | (
                    Elimination::OperandTransport {
                        motive: left_motive,
                        path: left_value,
                    },
                    Elimination::OperandTransport {
                        motive: right_motive,
                        path: right_value,
                    },
                ) => match crate::identity::motives(self.domain, left_motive, right_motive)
                    .map_err(ConversionFault::Domain)?
                {
                    // One body over captures the body does not read apart —
                    // a definition's family at two of its calls — is one
                    // family, as the kernel's shared motive term is.
                    crate::identity::Motives::Alike(_)
                        if crate::code::motives_alike(
                            self.core,
                            self.domain,
                            left_motive,
                            right_motive,
                        )? == crate::code::Alike::Same =>
                    {
                        queued.push(Goal::Values(left_value, right_value, beneath));
                    },
                    crate::identity::Motives::Alike(bindings) => {
                        let flexible = Context::Flexible(Deferral::Binder);
                        queued.extend(
                            bindings
                                .into_iter()
                                .map(|(one, other)| Goal::Values(one, other, flexible)),
                        );
                        queued.push(Goal::Values(left_value, right_value, beneath));
                    },
                    // Motives written apart, or over captures of different
                    // depths, are one family when they read alike (#650).
                    crate::identity::Motives::Unlike => {
                        if crate::code::motives_alike(
                            self.core,
                            self.domain,
                            left_motive,
                            right_motive,
                        )? == crate::code::Alike::Different
                        {
                            return Ok(Local::Defer(Deferral::Binder));
                        }
                        queued.push(Goal::Values(left_value, right_value, beneath));
                    },
                },
                (
                    Elimination::TelescopeTransport {
                        motive: left_motive,
                        start: left_start,
                        over: left_over,
                        value: left_value,
                    },
                    Elimination::TelescopeTransport {
                        motive: right_motive,
                        start: right_start,
                        over: right_over,
                        value: right_value,
                    },
                ) => match crate::identity::motives(self.domain, left_motive, right_motive)
                    .map_err(ConversionFault::Domain)?
                {
                    crate::identity::Motives::Alike(bindings) => {
                        let flexible = Context::Flexible(Deferral::Binder);
                        queued.extend(
                            bindings
                                .into_iter()
                                .map(|(one, other)| Goal::Values(one, other, flexible)),
                        );
                        queued.extend([
                            Goal::Values(left_start, right_start, beneath),
                            Goal::Values(left_over, right_over, beneath),
                            Goal::Values(left_value, right_value, beneath),
                        ]);
                    },
                    crate::identity::Motives::Unlike => {
                        return Ok(Local::Defer(Deferral::Binder));
                    },
                },
                (Elimination::Transport(left_argument), Elimination::Transport(right_argument))
                | (
                    Elimination::ProductTransport(left_argument),
                    Elimination::ProductTransport(right_argument),
                )
                | (Elimination::Apply(left_argument), Elimination::Apply(right_argument))
                | (
                    Elimination::StaticApply(left_argument),
                    Elimination::StaticApply(right_argument),
                ) => {
                    queued.push(Goal::Values(left_argument, right_argument, beneath));
                },
                (Elimination::Force, Elimination::Force) => {},
                (Elimination::Bind(left_body), Elimination::Bind(right_body)) => {
                    queued.push(Goal::Closures(left_body, right_body));
                },
                // Two stuck fixpoints convert when their fixpoints do and
                // their leading arguments do, pairwise.
                (
                    Elimination::Fixpoint {
                        recursive: left_body,
                        leading: left_leading,
                    },
                    Elimination::Fixpoint {
                        recursive: right_body,
                        leading: right_leading,
                    },
                ) => {
                    let left_leading = self
                        .domain
                        .fields(left_leading)
                        .map_err(ConversionFault::Domain)?;
                    let right_leading = self
                        .domain
                        .fields(right_leading)
                        .map_err(ConversionFault::Domain)?;
                    if left_leading.len() != right_leading.len() {
                        return Ok(mismatch);
                    }
                    queued.push(Goal::Closures(left_body, right_body));
                    queued.extend(
                        left_leading
                            .iter()
                            .zip(right_leading)
                            .map(|(&one, &other)| Goal::Values(one, other, beneath)),
                    );
                },
                (
                    Elimination::ListFold {
                        on_nil: ln,
                        on_cons: lc,
                        ..
                    },
                    Elimination::ListFold {
                        on_nil: rn,
                        on_cons: rc,
                        ..
                    },
                )
                | (
                    Elimination::ListCase {
                        on_nil: ln,
                        on_cons: lc,
                        ..
                    },
                    Elimination::ListCase {
                        on_nil: rn,
                        on_cons: rc,
                        ..
                    },
                ) => {
                    queued.push(Goal::Closures(ln, rn));
                    queued.push(Goal::Closures(lc, rc));
                },
                (Elimination::Case(left_branches), Elimination::Case(right_branches)) => {
                    let left_branches = self
                        .domain
                        .branches(left_branches)
                        .map_err(ConversionFault::Domain)?;
                    let right_branches = self
                        .domain
                        .branches(right_branches)
                        .map_err(ConversionFault::Domain)?;
                    if left_branches.len() != right_branches.len() {
                        return Ok(mismatch);
                    }
                    queued.extend(left_branches.iter().zip(right_branches).map(
                        |(&left_branch, &right_branch)| Goal::Closures(left_branch, right_branch),
                    ));
                },
                (
                    Elimination::Transport(_)
                    | Elimination::DataCase(_)
                    | Elimination::Split(_)
                    | Elimination::Projection(_)
                    | Elimination::ProductTransport(_)
                    | Elimination::PathTransport { .. }
                    | Elimination::OperandTransport { .. }
                    | Elimination::Ride { .. }
                    | Elimination::TelescopeTransport { .. }
                    | Elimination::Apply(_)
                    | Elimination::Force
                    | Elimination::Bind(_)
                    | Elimination::Case(_)
                    | Elimination::ListFold { .. }
                    | Elimination::ListCase { .. }
                    | Elimination::StaticApply(_)
                    | Elimination::Fixpoint { .. },
                    _,
                ) => return Ok(mismatch),
            }
        }
        self.goals.extend(queued);
        Ok(Local::Agree)
    }

    /// Compare two closures without opening their binders.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: validation precedes identity: [`Local::Agree`] when resolving
    ///   ids are equal, or when both suspend one core body over environments of
    ///   one depth per zone — each binding pair then queued flexible for a
    ///   binder, because the body may never read the binding that differs;
    ///   [`Local::Defer`] for a binder otherwise.
    /// - provides: the congruence that settles two closures without evaluating
    ///   either; two different bodies wait for the rule that opens a binder.
    /// - fails: [`ConversionFault::Domain`] for a closure that does not
    ///   resolve.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ConversionFault::Domain`] — a closure does not resolve.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — different suspended bodies defer to binder opening,
    ///   whereas comparing a live closure with itself agrees; after truncation
    ///   the same id refuses. Treating different bodies as equal or accepting a
    ///   dangling identity changes the boundary answer.
    /// - witness: `conv::tests::a_pair_needing_an_unfolding_or_a_binder_is_deferred`
    /// - witness: `conv::tests::identical_truncated_neutrals_and_closures_are_refused`
    #[spec(ensures: |ret| match (self.domain.comp_closure(left), self.domain.comp_closure(right)) {
        (Some(one), Some(other)) => ret == Ok(if one.body() == other.body()
            && [Zone::Intuitionistic, Zone::Linear].iter().all(|&zone|
                one.environment().depth(zone) == other.environment().depth(zone)) {
            Local::Agree
        } else { Local::Defer(Deferral::Binder) }),
        _ => ret == Err(ConversionFault::Domain(DomainFault::Dangling)),
    })]
    fn closures(
        &mut self,
        left: CompClosureId,
        right: CompClosureId,
    ) -> Result<Local, ConversionFault>
    {
        let Some(one) = self.domain.comp_closure(left)
        else {
            return Err(ConversionFault::Domain(DomainFault::Dangling));
        };
        if left == right {
            return Ok(Local::Agree);
        }
        let Some(other) = self.domain.comp_closure(right)
        else {
            return Err(ConversionFault::Domain(DomainFault::Dangling));
        };
        let (left_environment, right_environment) = (one.environment(), other.environment());
        let zones = [Zone::Intuitionistic, Zone::Linear];
        let shaped = zones
            .iter()
            .all(|&zone| left_environment.depth(zone) == right_environment.depth(zone));
        if one.body() != other.body() || !shaped {
            return Ok(Local::Defer(Deferral::Binder));
        }
        let beneath = Context::Flexible(Deferral::Binder);
        for zone in zones {
            let pairs = left_environment
                .bindings(zone)
                .iter()
                .zip(right_environment.bindings(zone));
            for (&left_binding, &right_binding) in pairs {
                self.goals
                    .push(Goal::Values(left_binding, right_binding, beneath));
            }
        }
        Ok(Local::Agree)
    }
}

/// Compare path constructors without reducing their certificate programs.
///
/// # Specification
/// - requires: nothing; unreadable domain nodes produce a domain fault.
/// - ensures: evidence is erased but every translator constructor is retained;
///   product components are compared after ambient value substitution only.
/// - provides: certificate-syntax equality, not extensional map equality.
/// - fails: a domain fault on a dangling value or neutral.
/// - panics: none.
///
/// # Errors
/// `ConversionFault::Domain`.
///
/// # Adequacy
/// - hypothesis: L3 — normalization never equates different translator syntax.
/// - witness: `eval::tests::native_certificate_conversion_retains_map_syntax`
/// - witness: `conv::tests::two_path_products_agree_component_by_component`
/// - witness: `conv::tests::a_neutral_path_agrees_only_at_its_own_head_with_no_spine`
#[spec(ensures: |ret| match (domain.value(left), domain.value(right)) {
    (Some(&DomainValue::PathCertificate { certificate: a, .. }), Some(&DomainValue::PathCertificate { certificate: b, .. })) => matches!(ret, Ok(answer) if answer == gandr_core_term::equal_certificate_syntax(core, a, b)),
    (None, _) | (_, None) => matches!(ret, Err(ConversionFault::Domain(DomainFault::Dangling))),
    (Some(a), Some(b)) if core::mem::discriminant(a) != core::mem::discriminant(b) => matches!(ret, Ok(gandr_core_term::CertificateEquality::Different)),
    _ => true,
})]
pub fn equal_paths(
    core: &CoreArena,
    domain: &DomainArena,
    left: DomainValueId,
    right: DomainValueId,
) -> Result<gandr_core_term::CertificateEquality, ConversionFault>
{
    let mut pending = Vec::from([(left, right)]);
    let mut visited = alloc::collections::BTreeSet::new();
    while let Some((left, right)) = pending.pop() {
        if !visited.insert((left, right)) {
            continue;
        }
        let (Some(one), Some(other)) = (domain.value(left), domain.value(right))
        else {
            return Err(ConversionFault::Domain(DomainFault::Dangling));
        };
        match (*one, *other) {
            (
                DomainValue::PathCertificate { certificate: a, .. },
                DomainValue::PathCertificate { certificate: b, .. },
            ) => {
                if gandr_core_term::equal_certificate_syntax(core, a, b)
                    == gandr_core_term::CertificateEquality::Different
                {
                    return Ok(gandr_core_term::CertificateEquality::Different);
                }
            },
            (
                DomainValue::PathProduct {
                    first: a,
                    second: b,
                    ..
                },
                DomainValue::PathProduct {
                    first: c,
                    second: d,
                    ..
                },
            ) => pending.extend([(a, c), (b, d)]),
            (DomainValue::Neutral { neutral: a, .. }, DomainValue::Neutral { neutral: b, .. }) => {
                let (Some(a), Some(b)) = (domain.neutral(a), domain.neutral(b))
                else {
                    return Err(ConversionFault::Domain(DomainFault::Dangling));
                };
                if a.head() != b.head() || !a.spine().is_empty() || !b.spine().is_empty() {
                    return Ok(gandr_core_term::CertificateEquality::Different);
                }
            },
            _ => return Ok(gandr_core_term::CertificateEquality::Different),
        }
    }
    Ok(gandr_core_term::CertificateEquality::Equal)
}

#[cfg(test)]
mod tests;
