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
            | Self::Identical | Self::StructurallyEqual => Convertibility::Convertible,
            | Self::GuardedApart | Self::StructurallyApart => Convertibility::Distinct,
            | Self::Deferred(_) => Convertibility::Undecided,
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
        | GuardAnswer::Apart => Early::Apart,
        | GuardAnswer::Inconclusive => Early::Open,
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
        | Early::Identical => Ok(Settlement::Identical),
        | Early::Apart => Ok(Settlement::GuardedApart),
        | Early::Open => Walk::new(core, domain).settle(Goal::Values(left, right, Context::Rigid)),
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
        | Early::Identical => Ok(Settlement::Identical),
        | Early::Apart => Ok(Settlement::GuardedApart),
        | Early::Open => Walk::new(core, domain).settle(Goal::Comps(left, right, Context::Rigid)),
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
            | (Walked::Apart, _) => Settlement::StructurallyApart,
            | (Walked::Exhausted, Outstanding::Deferred(reason)) => Settlement::Deferred(reason),
            | (Walked::Exhausted, Outstanding::Nothing) => Settlement::StructurallyEqual,
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
                | Goal::Values(left, right, context) => {
                    let local = self.values(left, right, context)?;
                    (local, context)
                },
                | Goal::Comps(left, right, context) => {
                    let local = self.comps(left, right, context)?;
                    (local, context)
                },
                | Goal::Neutrals(left, right, context) => {
                    let local = self.neutrals(left, right, context)?;
                    (local, context)
                },
                | Goal::Closures(left, right) => {
                    let local = self.closures(left, right)?;
                    (local, Context::Flexible(Deferral::Binder))
                },
            };
            match (local, context) {
                | (Local::Agree, _) => {},
                | (Local::Disagree, Context::Rigid) => return Ok(Walked::Apart),
                | (Local::Disagree, Context::Flexible(reason)) | (Local::Defer(reason), _) => {
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

    /// Whether a neutral's head has a body to unfold.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Context::Flexible`] for unfolding when the neutral's face
    ///   is unforced or forced, [`Context::Rigid`] when it is rigid.
    /// - provides: the one reading of "could unfolding repair a mismatch here".
    /// - fails: [`ConversionFault::Domain`] when the neutral does not resolve.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ConversionFault::Domain`] — the neutral does not resolve.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the same argument mismatch separates under a rigid
    ///   head and defers under a loaded head; classifying a loaded face as
    ///   rigid makes conversion unsound.
    /// - witness: `conv::tests::a_mismatch_separates_only_beneath_a_rigid_head`
    #[spec(ensures: |ret| self.domain.neutral(neutral).map_or_else(
        || ret == Err(ConversionFault::Domain(DomainFault::Dangling)),
        |node| ret == Ok(if matches!(node.unfolding(), Unfolding::Rigid) {
            Context::Rigid
        } else { Context::Flexible(Deferral::Unfolding) }),
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
        Ok(match held.unfolding() {
            | Unfolding::Rigid => Context::Rigid,
            | Unfolding::Unforced(_) | Unfolding::Forced(_) => {
                Context::Flexible(Deferral::Unfolding)
            },
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
            | Context::Rigid => Local::Disagree,
            | Context::Flexible(reason) => Local::Defer(reason),
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
            | Some(&Value::Literal(ref payload)) => Ok(payload),
            | Some(_) | None => Err(ConversionFault::LiteralPayload { literal }),
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
            | Early::Identical => return Ok(Local::Agree),
            | Early::Apart => return Ok(Local::Disagree),
            | Early::Open => {},
        }
        let (Some(&one), Some(&other)) = (self.domain.value(left), self.domain.value(right))
        else {
            return Err(ConversionFault::Domain(DomainFault::Dangling));
        };
        match (one, other) {
            | (
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
            | (DomainValue::Unit { .. }, DomainValue::Unit { .. }) => Ok(Local::Agree),
            | (
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
            | (
                DomainValue::Pair {
                    first: left_first,
                    second: left_second,
                    ..
                },
                DomainValue::Pair {
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
            | (
                DomainValue::Injection {
                    side: left_side,
                    body: left_body,
                    ..
                },
                DomainValue::Injection {
                    side: right_side,
                    body: right_body,
                    ..
                },
            ) => {
                if left_side != right_side {
                    return Ok(Local::Disagree);
                }
                self.goals
                    .push(Goal::Values(left_body, right_body, context));
                Ok(Local::Agree)
            },
            | (
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
            | (
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
            | (
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
                    | CodeComparison::Equal => Local::Agree,
                    | CodeComparison::Apart => Local::Disagree,
                    | CodeComparison::Undecided => Local::Defer(Deferral::Unfolding),
                },
            ),
            | (
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
                    | CodeComparison::Equal => Local::Agree,
                    | CodeComparison::Apart => Local::Disagree,
                    | CodeComparison::Undecided => Local::Defer(Deferral::Unfolding),
                },
            ),
            | (
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
            | (
                DomainValue::Neutral { .. },
                DomainValue::Thunk { .. } | DomainValue::StaticLambda { .. },
            )
            | (
                DomainValue::Thunk { .. } | DomainValue::StaticLambda { .. },
                DomainValue::Neutral { .. },
            ) => Ok(Local::Defer(Deferral::Binder)),
            | (DomainValue::Neutral { neutral, .. }, _)
            | (_, DomainValue::Neutral { neutral, .. }) => self.neutral_against_former(neutral),
            | (
                DomainValue::PathCertificate { .. }
                | DomainValue::PathProduct { .. }
                | DomainValue::Unit { .. }
                | DomainValue::Literal { .. }
                | DomainValue::Pair { .. }
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
            | Early::Identical => return Ok(Local::Agree),
            | Early::Apart => return Ok(Local::Disagree),
            | Early::Open => {},
        }
        let (Some(&one), Some(&other)) = (
            self.domain.computation(left),
            self.domain.computation(right),
        )
        else {
            return Err(ConversionFault::Domain(DomainFault::Dangling));
        };
        match (one, other) {
            | (
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
            | (
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
            | (
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
            | (DomainComp::Neutral { .. }, DomainComp::Lambda { .. })
            | (DomainComp::Lambda { .. }, DomainComp::Neutral { .. }) => {
                Ok(Local::Defer(Deferral::Binder))
            },
            | (DomainComp::Neutral { neutral, .. }, DomainComp::Return { .. })
            | (DomainComp::Return { .. }, DomainComp::Neutral { neutral, .. }) => {
                self.neutral_against_former(neutral)
            },
            | (DomainComp::Lambda { .. }, DomainComp::Return { .. })
            | (DomainComp::Return { .. }, DomainComp::Lambda { .. }) => Ok(Local::Disagree),
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
    ///   body; [`Local::Disagree`] when the guards separate the neutrals, or
    ///   when rigid heads differ or a rigid head's spines disagree in shape;
    ///   [`Local::Defer`] for unfolding when either head has a body and the
    ///   heads or the spine shapes differ.
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
    /// - witness: `conv::tests::family_spines_are_separated_by_head_index_and_arity`
    /// - witness: `conv::tests::identical_truncated_neutrals_and_closures_are_refused`
    /// - witness: `eval::tests::native_transport_sequences_product_components`
    #[spec(ensures: |ret| if self.domain.neutral(left).is_some() && self.domain.neutral(right).is_some() {
        ret.is_ok() && (left != right || ret == Ok(Local::Agree))
            && (ret != Ok(Local::Agree) || self.domain.neutral(left).zip(self.domain.neutral(right)).is_some_and(|(one, other)|
                one.head() == other.head() && one.spine().len() == other.spine().len()
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
            | (Context::Rigid, Context::Rigid) => context,
            | (Context::Flexible(reason), _) | (_, Context::Flexible(reason)) => {
                Context::Flexible(reason)
            },
        };
        let mismatch = match beneath {
            | Context::Rigid => Local::Disagree,
            | Context::Flexible(reason) => Local::Defer(reason),
        };
        let (Some(one), Some(other)) = (self.domain.neutral(left), self.domain.neutral(right))
        else {
            return Err(ConversionFault::Domain(DomainFault::Dangling));
        };
        if one.head() != other.head() || one.spine().len() != other.spine().len() {
            return Ok(mismatch);
        }
        let mut queued = Vec::new();
        for (&left_elimination, &right_elimination) in one.spine().iter().zip(other.spine()) {
            match (left_elimination, right_elimination) {
                | (
                    Elimination::Transport(left_argument),
                    Elimination::Transport(right_argument),
                )
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
                | (Elimination::Force, Elimination::Force) => {},
                | (Elimination::Bind(left_body), Elimination::Bind(right_body)) => {
                    queued.push(Goal::Closures(left_body, right_body));
                },
                | (
                    Elimination::Case {
                        on_left: left_on_left,
                        on_right: left_on_right,
                    },
                    Elimination::Case {
                        on_left: right_on_left,
                        on_right: right_on_right,
                    },
                ) => {
                    queued.push(Goal::Closures(left_on_left, right_on_left));
                    queued.push(Goal::Closures(left_on_right, right_on_right));
                },
                | (
                    Elimination::Transport(_)
                    | Elimination::ProductTransport(_)
                    | Elimination::Apply(_)
                    | Elimination::Force
                    | Elimination::Bind(_)
                    | Elimination::Case { .. }
                    | Elimination::StaticApply(_),
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
            | (
                DomainValue::PathCertificate { certificate: a, .. },
                DomainValue::PathCertificate { certificate: b, .. },
            ) => {
                if gandr_core_term::equal_certificate_syntax(core, a, b)
                    == gandr_core_term::CertificateEquality::Different
                {
                    return Ok(gandr_core_term::CertificateEquality::Different);
                }
            },
            | (
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
            | (
                DomainValue::Neutral { neutral: a, .. },
                DomainValue::Neutral { neutral: b, .. },
            ) => {
                let (Some(a), Some(b)) = (domain.neutral(a), domain.neutral(b))
                else {
                    return Err(ConversionFault::Domain(DomainFault::Dangling));
                };
                if a.head() != b.head() || !a.spine().is_empty() || !b.spine().is_empty() {
                    return Ok(gandr_core_term::CertificateEquality::Different);
                }
            },
            | _ => return Ok(gandr_core_term::CertificateEquality::Different),
        }
    }
    Ok(gandr_core_term::CertificateEquality::Equal)
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;
    use alloc::vec::Vec;

    use anodized::spec;
    use gandr_core_term::CoreArena;
    use gandr_core_term::Zone;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::GlobalIndex;
    use gandr_kernel_term::IntegerLiteral;
    use gandr_kernel_term::Literal;
    use gandr_kernel_term::Magnitude;
    use gandr_kernel_term::Sign;

    use super::Convertibility;
    use super::Deferral;
    use super::Settlement;
    use super::convert_computations;
    use super::convert_values;
    use crate::arena::CompClosureId;
    use crate::arena::DomainArena;
    use crate::arena::DomainCompId;
    use crate::arena::DomainValueId;
    use crate::closure::Environment;
    use crate::domain::BinderLevel;
    use crate::domain::CompTermFace;
    use crate::domain::Elimination;
    use crate::domain::NeutralHead;
    use crate::domain::TermFace;
    use crate::domain::Unfolding;

    /// A domain literal over the non-negative integer `digits` spell, with
    /// its payload minted in `core`.
    ///
    /// # Specification
    /// - requires: `digits` is a non-empty run of decimal digits.
    /// - ensures: a reduced-face domain literal whose core payload is that
    ///   integer.
    /// - provides: the rigid leaves the step witnesses compare.
    /// - panics: when `digits` is not decimal, which no fixture passes.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — distinct decimal payloads separate through rigid
    ///   guards, while repeated equal payloads at distinct ids agree
    ///   structurally; replacing the requested integer or retaining a source
    ///   face changes which step answers.
    /// - witness: `conv::tests::the_guard_answers_a_rigid_pair_identity_does_not`
    /// - witness: `conv::tests::structure_answers_what_the_guard_cannot`
    #[spec(
        requires: !digits.is_empty() && digits.bytes().all(|byte| byte.is_ascii_digit()),
        ensures: |ret| matches!(domain.value(ret), Some(crate::DomainValue::Literal { face: TermFace::Reduced, .. })),
    )]
    fn literal(
        core: &mut CoreArena,
        domain: &mut DomainArena,
        digits: String,
    ) -> DomainValueId
    {
        let magnitude = Magnitude::from_decimal_text(digits).expect("the digits are decimal");
        let payload = Literal::Integer(IntegerLiteral::new(Sign::NonNegative, magnitude));
        let held = core.value_literal(payload.clone());
        domain.value_literal(held, &payload, TermFace::Reduced)
    }

    /// A closure over `return ⟨⟩` in the empty environment.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a fresh closure id over a fresh core body.
    /// - provides: the flexible part a thunk or a lambda fixture carries.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — independently suspended returners supply the two
    ///   thunks whose bodies require binder opening; reusing a body or adding a
    ///   captured binding changes the comparison path.
    /// - witness: `conv::tests::a_pair_needing_an_unfolding_or_a_binder_is_deferred`
    #[spec(ensures: |ret| domain.comp_closure(ret).is_some_and(|closure|
        [Zone::Intuitionistic, Zone::Linear].iter().all(|&zone|
            closure.environment().bindings(zone).is_empty())
        && matches!(closure.body(), crate::closure::CompBody::Source(body)
            if matches!(core.computation(body), Some(gandr_core_term::Computation::Return(value))
                if matches!(core.value(*value), Some(gandr_core_term::Value::Unit))))))]
    fn closure(
        core: &mut CoreArena,
        domain: &mut DomainArena,
    ) -> CompClosureId
    {
        let produced = core.value_unit();
        let body = core.computation_return(produced);
        domain.comp_closure_node(body, Environment::new())
    }

    /// A value-position neutral over `head` with `unfolding`.
    ///
    /// # Specification
    /// - requires: `unfolding` is rigid unless `head` is a declaration.
    /// - ensures: a reduced-face value standing for a spineless neutral.
    /// - provides: the stuck values the deferral witnesses compare.
    /// - panics: when the arena refuses the neutral, which no fixture provokes.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — rigid and defined value heads distinguish a
    ///   separating mismatch from unfolding deferral, while a rigid value
    ///   against a thunk waits for a binder; changing the head or face changes
    ///   the settlement.
    /// - witness: `conv::tests::a_pair_needing_an_unfolding_or_a_binder_is_deferred`
    #[spec(ensures: |ret| match domain.value(ret) {
        Some(&crate::DomainValue::Neutral { neutral, face: TermFace::Reduced }) =>
            domain.neutral(neutral).is_some_and(|node| node.head() == head
                && node.unfolding() == unfolding && node.spine().is_empty()),
        _ => false,
    })]
    fn stuck(
        domain: &mut DomainArena,
        head: NeutralHead,
        unfolding: Unfolding,
    ) -> DomainValueId
    {
        let neutral = domain
            .neutral_node(head, Vec::new(), unfolding)
            .expect("the head may carry the face");
        domain
            .value_neutral(neutral, TermFace::Reduced)
            .expect("a spineless neutral stands in a value position")
    }

    /// A computation-position neutral over `head` with `spine` and
    /// `unfolding`.
    ///
    /// # Specification
    /// - requires: `unfolding` is rigid unless `head` is a declaration.
    /// - ensures: a reduced-face computation standing for that neutral.
    /// - provides: the stuck computations the spine witnesses compare.
    /// - panics: when the arena refuses the neutral, which no fixture provokes.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — equal-shaped spines under rigid and loaded heads
    ///   distinguish refutation from unfolding deferral, and different head
    ///   indices and arities separate rigid families; changing the neutral
    ///   represented changes those results.
    /// - witness: `conv::tests::a_mismatch_separates_only_beneath_a_rigid_head`
    /// - witness: `conv::tests::family_spines_are_separated_by_head_index_and_arity`
    #[spec(ensures: |ret| match domain.computation(ret) {
        Some(&crate::DomainComp::Neutral { neutral, face: CompTermFace::Reduced }) =>
            domain.neutral(neutral).is_some_and(|node| node.head() == head && node.unfolding() == unfolding),
        _ => false,
    })]
    fn stuck_comp(
        domain: &mut DomainArena,
        head: NeutralHead,
        spine: Vec<Elimination>,
        unfolding: Unfolding,
    ) -> DomainCompId
    {
        let neutral = domain
            .neutral_node(head, spine, unfolding)
            .expect("the head may carry the face");
        domain.comp_neutral(neutral, CompTermFace::Reduced)
    }

    /// The innermost intuitionistic variable as a neutral head.
    ///
    /// # Specification
    /// trivial.
    fn variable() -> NeutralHead
    {
        NeutralHead::Variable {
            zone: Zone::Intuitionistic,
            level: BinderLevel::from(0_u32),
        }
    }

    #[test]
    fn identity_answers_one_node_and_one_source_term()
    {
        let mut core = CoreArena::new();
        let mut domain = DomainArena::new();
        let unit = domain.value_unit(TermFace::Reduced);
        assert_eq!(
            Ok(Settlement::Identical),
            convert_values(&core, &domain, unit, unit),
            "one id is one value"
        );

        let produced = core.value_unit();
        let suspended = core.computation_return(produced);
        let source = core.value_thunk(suspended);
        let first = closure(&mut core, &mut domain);
        let second = closure(&mut core, &mut domain);
        let one = domain.value_thunk(first, TermFace::Source(source));
        let other = domain.value_thunk(second, TermFace::Source(source));
        assert_eq!(
            Ok(Settlement::Identical),
            convert_values(&core, &domain, one, other),
            "two thunks evaluated from one source term are one value, which no guard could \
             say: a thunk's word is flexible"
        );
    }

    #[test]
    fn the_guard_answers_a_rigid_pair_identity_does_not()
    {
        let mut core = CoreArena::new();
        let mut domain = DomainArena::new();
        let unit = domain.value_unit(TermFace::Reduced);
        let one = literal(&mut core, &mut domain, String::from("1"));
        let two = literal(&mut core, &mut domain, String::from("2"));
        let left = domain.value_pair(unit, one, TermFace::Reduced);
        let right = domain.value_pair(unit, two, TermFace::Reduced);
        let settled = convert_values(&core, &domain, left, right);
        assert_eq!(
            Ok(Settlement::GuardedApart),
            settled,
            "two ids with reduced faces pass step 1, and two rigid words that differ settle \
             the pair at step 2"
        );
        assert_eq!(
            Ok(Convertibility::Distinct),
            settled.map(Settlement::verdict),
            "which is a distinct answer"
        );
    }

    #[test]
    fn structure_answers_what_the_guard_cannot()
    {
        let mut core = CoreArena::new();
        let mut domain = DomainArena::new();

        let left_unit = domain.value_unit(TermFace::Reduced);
        let left_one = literal(&mut core, &mut domain, String::from("1"));
        let right_unit = domain.value_unit(TermFace::Reduced);
        let right_one = literal(&mut core, &mut domain, String::from("1"));
        let left = domain.value_pair(left_unit, left_one, TermFace::Reduced);
        let right = domain.value_pair(right_unit, right_one, TermFace::Reduced);
        assert_eq!(
            Ok(Settlement::StructurallyEqual),
            convert_values(&core, &domain, left, right),
            "equal content at distinct ids folds to one word, which step 2 may not read as \
             convertible; step 3 does"
        );

        let left_closure = closure(&mut core, &mut domain);
        let right_closure = closure(&mut core, &mut domain);
        let left_thunk = domain.value_thunk(left_closure, TermFace::Reduced);
        let right_thunk = domain.value_thunk(right_closure, TermFace::Reduced);
        let two = literal(&mut core, &mut domain, String::from("2"));
        let left = domain.value_pair(left_thunk, left_unit, TermFace::Reduced);
        let right = domain.value_pair(right_thunk, two, TermFace::Reduced);
        assert_eq!(
            Ok(Settlement::StructurallyApart),
            convert_values(&core, &domain, left, right),
            "a thunk makes both words flexible, so step 2 is silent, and step 3 finds the \
             unit against the literal"
        );
    }

    #[test]
    fn a_pair_needing_an_unfolding_or_a_binder_is_deferred()
    {
        let mut core = CoreArena::new();
        let mut domain = DomainArena::new();

        let defined = stuck(
            &mut domain,
            NeutralHead::Constant(ConstantIndex::from(0_usize)),
            Unfolding::Unforced(GlobalIndex::from(3_u32)),
        );
        let axiom = stuck(
            &mut domain,
            NeutralHead::Constant(ConstantIndex::from(1_usize)),
            Unfolding::Rigid,
        );
        assert_eq!(
            Ok(Settlement::Deferred(Deferral::Unfolding)),
            convert_values(&core, &domain, defined, axiom),
            "two heads differ, but one has a body that may unfold into the other"
        );
        let unit = domain.value_unit(TermFace::Reduced);
        assert_eq!(
            Ok(Settlement::Deferred(Deferral::Unfolding)),
            convert_values(&core, &domain, defined, unit),
            "and a definition may unfold into a constructor"
        );

        let rigid = stuck(&mut domain, variable(), Unfolding::Rigid);
        let suspended = closure(&mut core, &mut domain);
        let thunk = domain.value_thunk(suspended, TermFace::Reduced);
        assert_eq!(
            Ok(Settlement::Deferred(Deferral::Binder)),
            convert_values(&core, &domain, thunk, rigid),
            "a thunk against a stuck variable waits for the η-rule that opens a binder"
        );

        let elsewhere = closure(&mut core, &mut domain);
        let other_thunk = domain.value_thunk(elsewhere, TermFace::Reduced);
        assert_eq!(
            Ok(Settlement::Deferred(Deferral::Binder)),
            convert_values(&core, &domain, thunk, other_thunk),
            "and two closures over different bodies compare only once their binders open"
        );

        let lambda = domain.comp_lambda(suspended, CompTermFace::Reduced);
        let applied = stuck_comp(
            &mut domain,
            variable(),
            Vec::from([Elimination::Force]),
            Unfolding::Rigid,
        );
        assert_eq!(
            Ok(Settlement::Deferred(Deferral::Binder)),
            convert_computations(&core, &domain, lambda, applied),
            "a lambda against a stuck computation waits for function η"
        );
    }

    #[test]
    fn a_mismatch_separates_only_beneath_a_rigid_head()
    {
        let mut core = CoreArena::new();
        let mut domain = DomainArena::new();
        let one = literal(&mut core, &mut domain, String::from("1"));
        let two = literal(&mut core, &mut domain, String::from("2"));
        let continuation = closure(&mut core, &mut domain);
        let spine = |argument| {
            Vec::from([
                Elimination::Force,
                Elimination::Apply(argument),
                Elimination::Bind(continuation),
            ])
        };

        let rigid_left = stuck_comp(&mut domain, variable(), spine(one), Unfolding::Rigid);
        let rigid_right = stuck_comp(&mut domain, variable(), spine(two), Unfolding::Rigid);
        assert_eq!(
            Ok(Settlement::StructurallyApart),
            convert_computations(&core, &domain, rigid_left, rigid_right),
            "a bind makes both words flexible; beneath a rigid head the differing arguments \
             separate the two stuck computations"
        );

        let defined = NeutralHead::Constant(ConstantIndex::from(0_usize));
        let body = Unfolding::Unforced(GlobalIndex::from(3_u32));
        let unfolding_left = stuck_comp(&mut domain, defined, spine(one), body);
        let unfolding_right = stuck_comp(&mut domain, defined, spine(two), body);
        assert_eq!(
            Ok(Settlement::Deferred(Deferral::Unfolding)),
            convert_computations(&core, &domain, unfolding_left, unfolding_right),
            "beneath a head with a body the same mismatch defers, because the unfolded body \
             may never read its argument"
        );
    }

    #[test]
    fn computations_settle_by_their_weak_heads()
    {
        let mut core = CoreArena::new();
        let mut domain = DomainArena::new();
        let suspended = closure(&mut core, &mut domain);
        let thunk = domain.value_thunk(suspended, TermFace::Reduced);
        let one = literal(&mut core, &mut domain, String::from("1"));
        let two = literal(&mut core, &mut domain, String::from("2"));
        let left_pair = domain.value_pair(thunk, one, TermFace::Reduced);
        let right_pair = domain.value_pair(thunk, two, TermFace::Reduced);
        let left = domain.comp_return(left_pair, CompTermFace::Reduced);
        let right = domain.comp_return(right_pair, CompTermFace::Reduced);
        assert_eq!(
            Ok(Settlement::StructurallyApart),
            convert_computations(&core, &domain, left, right),
            "two returners compare by the values they carry"
        );

        let lambda = domain.comp_lambda(suspended, CompTermFace::Reduced);
        assert_eq!(
            Ok(Settlement::StructurallyApart),
            convert_computations(&core, &domain, lambda, left),
            "a lambda and a returner are different weak heads"
        );

        let forced = stuck_comp(
            &mut domain,
            variable(),
            Vec::from([Elimination::Force]),
            Unfolding::Rigid,
        );
        assert_eq!(
            Ok(Settlement::StructurallyApart),
            convert_computations(&core, &domain, left, forced),
            "a returner against a rigid stuck computation separates"
        );
        let defined = stuck_comp(
            &mut domain,
            NeutralHead::Constant(ConstantIndex::from(0_usize)),
            Vec::from([Elimination::Force]),
            Unfolding::Unforced(GlobalIndex::from(3_u32)),
        );
        assert_eq!(
            Ok(Settlement::Deferred(Deferral::Unfolding)),
            convert_computations(&core, &domain, left, defined),
            "and against one whose head may unfold into a returner it defers"
        );
    }

    #[test]
    fn a_shared_graph_is_compared_once_per_pair()
    {
        let core = CoreArena::new();
        let mut domain = DomainArena::new();
        let mut left = domain.value_unit(TermFace::Reduced);
        let mut right = domain.value_unit(TermFace::Reduced);
        let mut remaining = 64_u32;
        while remaining > 0_u32 {
            left = domain.value_pair(left, left, TermFace::Reduced);
            right = domain.value_pair(right, right, TermFace::Reduced);
            remaining = remaining.saturating_sub(1_u32);
        }
        assert_eq!(
            Ok(Settlement::StructurallyEqual),
            convert_values(&core, &domain, left, right),
            "each graph expands to 2⁶⁴ leaves, and the walk meets 65 distinct pairs"
        );
    }

    #[test]
    fn family_spines_are_separated_by_head_index_and_arity()
    {
        /// The rigid family at `family` applied statically to `arguments`.
        ///
        /// # Specification
        /// trivial.
        fn applied(
            domain: &mut DomainArena,
            family: ConstantIndex,
            arguments: &[DomainValueId],
        ) -> DomainValueId
        {
            let spine = arguments
                .iter()
                .map(|&argument| Elimination::StaticApply(argument))
                .collect();
            let neutral = domain
                .neutral_node(NeutralHead::Constant(family), spine, Unfolding::Rigid)
                .expect("a rigid family mints");
            domain
                .value_neutral(neutral, TermFace::Reduced)
                .expect("a static spine stands as a value")
        }

        let mut core = CoreArena::new();
        let mut domain = DomainArena::new();
        let one = literal(&mut core, &mut domain, String::from("1"));
        let two = literal(&mut core, &mut domain, String::from("2"));
        let f_one = applied(&mut domain, ConstantIndex::from(0_usize), &[one]);
        let f_one_again = applied(&mut domain, ConstantIndex::from(0_usize), &[one]);
        let g_one = applied(&mut domain, ConstantIndex::from(1_usize), &[one]);
        let f_one_two = applied(&mut domain, ConstantIndex::from(0_usize), &[one, two]);
        let f_two = applied(&mut domain, ConstantIndex::from(0_usize), &[two]);
        assert_eq!(
            Ok(Settlement::StructurallyEqual),
            convert_values(&core, &domain, f_one, f_one_again),
            "one head at one arity over one argument is one family instance"
        );
        assert_eq!(
            Ok(Settlement::GuardedApart),
            convert_values(&core, &domain, f_one, g_one),
            "two head indices fold to two words"
        );
        assert_eq!(
            Ok(Settlement::GuardedApart),
            convert_values(&core, &domain, f_one, f_one_two),
            "two arities over one head fold to two words"
        );
        assert_eq!(
            Ok(Settlement::GuardedApart),
            convert_values(&core, &domain, f_one, f_two),
            "and two arguments at one head and arity fold apart too"
        );
    }

    #[test]
    fn identical_truncated_values_are_refused()
    {
        let mut domain = DomainArena::new();
        let floor = domain.watermark();
        let value = domain.value_unit(TermFace::Reduced);
        assert_eq!(
            Ok(super::Early::Identical),
            super::early_values(&domain, value, value)
        );
        domain.truncate_to(floor);
        assert!(domain.value(value).is_none());
        assert_eq!(
            Err(super::ConversionFault::Domain(crate::DomainFault::Dangling)),
            super::early_values(&domain, value, value)
        );
    }

    #[test]
    fn identical_truncated_computations_are_refused()
    {
        let mut domain = DomainArena::new();
        let floor = domain.watermark();
        let value = domain.value_unit(TermFace::Reduced);
        let computation = domain.comp_return(value, CompTermFace::Reduced);
        assert_eq!(
            Ok(super::Early::Identical),
            super::early_comps(&domain, computation, computation)
        );
        domain.truncate_to(floor);
        assert!(domain.computation(computation).is_none());
        assert_eq!(
            Err(super::ConversionFault::Domain(crate::DomainFault::Dangling)),
            super::early_comps(&domain, computation, computation)
        );
    }

    #[test]
    fn identical_truncated_neutrals_and_closures_are_refused()
    {
        let mut core = CoreArena::new();
        let mut domain = DomainArena::new();
        let floor = domain.watermark();
        let suspended = closure(&mut core, &mut domain);
        let neutral = domain
            .neutral_node(variable(), Vec::new(), Unfolding::Rigid)
            .expect("a variable is rigid");
        {
            let mut walk = super::Walk::new(&core, &domain);
            assert_eq!(
                Ok(super::Local::Agree),
                walk.neutrals(neutral, neutral, super::Context::Rigid)
            );
            assert_eq!(Ok(super::Local::Agree), walk.closures(suspended, suspended));
        }
        domain.truncate_to(floor);
        let mut walk = super::Walk::new(&core, &domain);
        let neutral_result = walk.neutrals(neutral, neutral, super::Context::Rigid);
        let closure_result = walk.closures(suspended, suspended);
        let refused = Err(super::ConversionFault::Domain(crate::DomainFault::Dangling));
        assert_eq!((refused, refused), (neutral_result, closure_result));
    }

    #[test]
    fn the_first_deferral_is_retained_until_a_rigid_refutation()
    {
        let mut core = CoreArena::new();
        let mut domain = DomainArena::new();
        let first = closure(&mut core, &mut domain);
        let second = closure(&mut core, &mut domain);
        let first_thunk = domain.value_thunk(first, TermFace::Reduced);
        let second_thunk = domain.value_thunk(second, TermFace::Reduced);
        let defined = stuck(
            &mut domain,
            NeutralHead::Constant(ConstantIndex::from(0_usize)),
            Unfolding::Unforced(GlobalIndex::from(0_u32)),
        );
        let unit = domain.value_unit(TermFace::Reduced);
        for (left_first, left_second, right_first, right_second, reason) in [
            (first_thunk, defined, second_thunk, unit, Deferral::Binder),
            (
                defined,
                first_thunk,
                unit,
                second_thunk,
                Deferral::Unfolding,
            ),
        ] {
            let left = domain.value_pair(left_first, left_second, TermFace::Reduced);
            let right = domain.value_pair(right_first, right_second, TermFace::Reduced);
            let answer =
                convert_values(&core, &domain, left, right).expect("the pair is well formed");
            assert_eq!(Settlement::Deferred(reason), answer);
            assert_eq!(Convertibility::Undecided, answer.verdict());
            assert_eq!(
                Convertibility::Convertible,
                convert_values(&core, &domain, left, left)
                    .expect("live identity agrees")
                    .verdict()
            );
            let one = literal(&mut core, &mut domain, String::from("1"));
            let left = domain.value_pair(left, unit, TermFace::Reduced);
            let right = domain.value_pair(right, one, TermFace::Reduced);
            let answer =
                convert_values(&core, &domain, left, right).expect("the mismatch resolves");
            assert_eq!(Settlement::StructurallyApart, answer);
            assert_eq!(Convertibility::Distinct, answer.verdict());
        }
    }

    #[test]
    fn a_payload_read_refuses_nonliteral_and_missing_nodes()
    {
        let mut core = CoreArena::new();
        let floor = core.watermark();
        let nonliteral = core.value_unit();
        let domain = DomainArena::new();
        assert_eq!(
            Err(super::ConversionFault::LiteralPayload {
                literal: nonliteral
            }),
            super::Walk::new(&core, &domain).payload(nonliteral)
        );
        core.truncate_to(floor);
        assert_eq!(
            Err(super::ConversionFault::LiteralPayload {
                literal: nonliteral
            }),
            super::Walk::new(&core, &domain).payload(nonliteral)
        );
    }
}
