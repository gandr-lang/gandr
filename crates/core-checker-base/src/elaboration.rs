//! Suspension on owed holes, and the term-producing path that resumes it.
//!
//! # A judgement blocked on an owed hole waits; it is not refused
//!
//! A declaration whose body is a hole under a formed signature is owed, and
//! crosses to the kernel as an axiom: a rigid constant. A later value
//! declaration that needs `El(h) ≡ Integer` against an owed code `h` cannot be
//! decided today — filling `h` with `⌜Integer⌝` settles it, filling it with
//! `⌜String⌝` refutes it — so the checker gives it neither acceptance nor
//! refusal but the third verdict, [`Verdict::Suspended`]: the declaration
//! waits on `h`, its blockers. This is the suspension case of Slattery and
//! Sterling's elaboration calculus (*Bidirectional Elaborators à la Carte*,
//! arXiv:2607.09564v2, Exegesis 6.6): the problem's sieve is inhabited but
//! does not contain the identity, so it resumes under a more specific
//! context — here, after a fill.
//!
//! The checker realizes the calculus natively, with the calculus as its
//! specification and the kernel as its certifier; kernel readmission certifies
//! only that an output is well typed, so the calculus's other guarantees —
//! invariance under judgemental equality, stability under substitution,
//! independence of order — are tested as relational witnesses, below.
//!
//! # The fragment: bare flex–rigid equations on owed code constants
//!
//! Only a decode of a bare owed code constant opposite a constructor-headed
//! type becomes a residual [`Equation`], in either orientation, at the root
//! of a comparison or beneath matching type constructors. A hole applied to a
//! spine (`El(h(x))`) and two decodes of holes (`El(h) ≡ El(k)`) keep the
//! ordinary checker's answer: telling a clash from a postponement there is
//! unification — certified emptiness of the sieve — and belongs to the
//! unifier (Abel and Pientka's pattern fragment), not to this collector. A
//! residual records what a fill must settle; it neither solves a hole nor
//! certifies a clash.
//!
//! A value declaration's judgement collects; a nominal declaration's
//! formation (data, abstract, world) decides every comparison rigidly. A
//! context that has judged no owed hole has nothing to collect, so ordinary
//! checking of a module without holes is unchanged, and the collector costs a
//! set lookup per comparison only where holes exist.
//!
//! # One rule machine
//!
//! The judgement is [`check_declaration`]'s, not a second elaborator: the
//! value bridge and the computation bridge are the calculus's `conv`
//! awaiting type equality, and the collector sits inside the conversion they
//! share. A declaration whose accepted judgement left a residual, or read the
//! type of a declaration that waits, is suspended: its type enters the
//! signature table, so later declarations judge against it, but nothing is
//! defined for it, so no conditional body unfolds or crosses to the kernel. A
//! refusal wins over every residual, so a declaration with a deferred
//! comparison and a refused premise is refused (multistrictness, Corollary
//! 5.2), and a waiting read propagates (Theorem 5.1: a composite's support is
//! the conjunction of its parts'). [`check_module`] reports each suspension
//! with its blockers — the holes still owed among its equations' heads, its
//! waiting prerequisites' included — and the declarations it waits on.
//!
//! Recorded design: a private residual collector beside an unchanged ordinary
//! checker, with a separate elaboration judge. Change: the collector is the
//! checker's own, so the report every face reads says what waits and on
//! which holes, and the one declaration judgement [`check_declaration`]
//! carries every former the checker admits. Reason: the separate judge
//! re-implemented the declaration rule and fell behind it, and a suspension
//! the faces cannot see is a refusal to them.
//!
//! A refused prerequisite does not refuse its readers: a signed declaration
//! refused at its body still supplies its type, as the checker has always
//! held, and the kernel bridge withholds a reader of a constant it was not
//! offered. A waiting prerequisite does propagate, because its reader's
//! output would name a body that does not yet exist.
//!
//! [`Verdict::Suspended`]: crate::Verdict::Suspended
//! [`check_declaration`]: crate::check_declaration
//! [`check_module`]: crate::check_module

mod constraints;
mod output;
#[cfg(test)]
mod tests;

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::ValueId;
use gandr_kernel_term::ConstantIndex;
use quenchant_shape::shape::Maybe;

pub(crate) use self::constraints::Collecting;
pub(crate) use self::constraints::Deferrals;
pub(crate) use self::constraints::Deferred;
pub use self::constraints::Equation;
pub(crate) use self::constraints::Residue;
pub(crate) use self::constraints::Signing;
pub(crate) use self::constraints::Unified;
pub(crate) use self::output::CodeUse;
pub(crate) use self::output::CodeUses;
pub(crate) use self::output::Emission;
use self::output::Transports;
use crate::CheckBudget;
use crate::CheckRefusal;
use crate::CheckingContext;
use crate::Declaration;
use crate::FormedValueType;
use crate::Lift;
use crate::ObligationEntry;
use crate::OriginToken;
use crate::Verdict;
use crate::signature_table;
use crate::unfolding;

/// A checked, emitted core term and its original judgement evidence.
///
/// # Specification
/// - requires: constructed only after all declaration premises succeed.
/// - ensures: the body contains explicit conversion lifts and has `declared`;
///   no residual equation is represented by an `Output`.
/// - provides: a term for independent kernel readmission.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 — the kernel independently checks emitted definitions;
///   exact nested-lift observations distinguish emission from input copying.
/// - witness: `gandr-core-checker::tests::elaboration::every_fixture_the_checker_accepts_is_readmitted`
/// - witness: `gandr-core-checker::tests::elaboration::outputs_materialize_nested_lifts`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Output
{
    /// The formed result type.
    declared: FormedValueType,
    /// The core output, with lifts materialized.
    body: ValueId,
    /// The verdict over the emitted body, for the kernel bridge.
    verdict: Verdict,
}

impl Output
{
    /// The emitted core body.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn body(&self) -> ValueId
    {
        self.body
    }

    /// The output's formed type.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn declared(&self) -> FormedValueType
    {
        self.declared
    }
}

/// What a suspended declaration waits on.
///
/// # Specification
/// - requires: created only from a suspended judgement's residue.
/// - ensures: equations are sorted and unique, the declaration's own and its
///   waiting prerequisites'; blockers are their distinct flex heads still owed
///   when this record is created; dependencies are the waiting declarations it
///   read. A record over a prerequisite can retain an equation whose hole was
///   filled since.
/// - provides: declaration-granular continuation, without a unification claim.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — exact blockers and equations detect refusal-as-suspension
///   and lost obligations; two residuals witness conjunction.
/// - witness: `gandr-core-checker::tests::elaboration::owed_conversion_suspends`
/// - witness: `gandr-core-checker::tests::elaboration::residual_conjunction_does_not_hide_refusal`
/// - witness: `gandr-core-checker::tests::elaboration::filling_through_a_suspended_dependency_reports_only_still_owed_blockers`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Suspension
{
    /// The type the waiting declaration supplies.
    declared: FormedValueType,
    /// Canonical residual equations, including waiting prerequisites'.
    equations: Vec<Equation>,
    /// Canonical owed-hole identities at creation.
    blockers: BTreeSet<ConstantIndex>,
    /// Earlier waiting declarations whose types this declaration read.
    dependencies: BTreeSet<ConstantIndex>,
}

impl Suspension
{
    /// The record of a judgement that left `residue`, supplying `declared`,
    /// with `owed` the holes owed and `prior` the suspensions kept when it was
    /// judged.
    ///
    /// # Specification
    /// - requires: `residue` is pending.
    /// - ensures: the equations are `residue`'s with each dependency's own
    ///   appended, sorted and deduplicated; the blockers are their holes that
    ///   `owed` holds; the dependencies are `residue`'s.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fill of the hole before a dependent's record is
    ///   made leaves its blockers empty with the prerequisite still named.
    /// - witness: `gandr-core-checker::tests::elaboration::filling_through_a_suspended_dependency_reports_only_still_owed_blockers`
    /// - witness: `gandr-core-checker::tests::elaboration::dependent_resumption_closes_its_prerequisites`
    #[spec(
        captures: residue_dependencies = residue.dependencies.clone(),
        ensures: |ret| ret.dependencies == residue_dependencies
            && ret.equations.windows(2).all(|pair| pair.first() < pair.get(1))
            && ret.blockers.iter().all(|hole| owed.contains(hole)),
    )]
    pub fn new(
        declared: FormedValueType,
        residue: Residue,
        owed: &BTreeSet<ConstantIndex>,
        prior: &BTreeMap<ConstantIndex, Self>,
    ) -> Self
    {
        let Residue {
            mut equations,
            dependencies,
        } = residue;
        for dependency in &dependencies {
            if let Some(waiting) = prior.get(dependency) {
                equations.extend_from_slice(&waiting.equations);
            }
        }
        equations.sort_unstable();
        equations.dedup();
        let blockers = equations
            .iter()
            .map(Equation::hole)
            .filter(|hole| owed.contains(hole))
            .collect();
        Self {
            declared,
            equations,
            blockers,
            dependencies,
        }
    }

    /// The suspension that these parts give, as a seat builds it again in
    /// another arena.
    ///
    /// # Specification
    /// - requires: `declared` is minted from the content of the formed type
    ///   that a suspension kept, so it is a rewrite of a formed type; the
    ///   equations are sorted and unique.
    /// - ensures: the suspension of these parts.
    /// - panics: none.
    /// - executable: none — the requirement names where the type came from,
    ///   which no predicate reads.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the parts of a suspension that a supported judgement
    ///   keeps seat that suspension again.
    /// - witness: `elaboration::tests::a_supported_judgement_keeps_the_suspension_that_the_module_run_reports`
    #[inline]
    #[must_use]
    pub fn seated(
        (declared, equations): (gandr_core_term::ValueTypeId, Vec<Equation>),
        (blockers, dependencies): (BTreeSet<ConstantIndex>, BTreeSet<ConstantIndex>),
    ) -> Self
    {
        Self {
            declared: FormedValueType::derived(declared),
            equations,
            blockers,
            dependencies,
        }
    }

    /// The type the waiting declaration supplies.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn declared(&self) -> FormedValueType
    {
        self.declared
    }

    /// The pending conversion equations.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn equations(&self) -> &[Equation]
    {
        &self.equations
    }

    /// The holes owed when this suspension was recorded.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn blockers(&self) -> &BTreeSet<ConstantIndex>
    {
        &self.blockers
    }

    /// Waiting declarations to resume before this one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn dependencies(&self) -> &BTreeSet<ConstantIndex>
    {
        &self.dependencies
    }
}

/// A term-producing run's answer for one declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Outcome
{
    /// Every premise is settled and a core term is available.
    Checked(Output),
    /// A nominal declaration formed.
    Formed,
    /// The declaration itself lacks its body.
    Owed(ObligationEntry),
    /// The declaration waits on owed code constants.
    Suspended(Suspension),
    /// A premise was refused; this is not certified sieve emptiness.
    Refused(CheckRefusal),
}

/// Number of declaration judgements actually executed.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
pub struct Judgements(usize);

impl From<Judgements> for usize
{
    /// Expose the declared work count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: Judgements) -> Self
    {
        count.0
    }
}

/// One declaration's current answer and cumulative judgement count.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Entry
{
    /// The current declaration, changed only by filling an owed body.
    source: Declaration,
    /// Its settled or residual answer.
    outcome: Outcome,
    /// The type it supplies, retained even when a signed body refuses.
    supplied: Maybe<FormedValueType, signature_table::Absent>,
    /// The body its constant unfolds to, as the judging run defined it.
    unfolds: Maybe<ValueId, unfolding::Absent>,
    /// The lifts its output left beneath a former read as a leaf, by node.
    lifts: BTreeMap<ValueId, Lift>,
    /// Actual judgement invocations, excluding adoption and kernel replay.
    judgements: Judgements,
}

impl Entry
{
    /// The declaration's admission identity.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn constant(&self) -> ConstantIndex
    {
        self.source.constant()
    }

    /// The declaration's origin.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn origin(&self) -> OriginToken
    {
        self.source.origin()
    }

    /// The declaration as currently filled.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn source(&self) -> &Declaration
    {
        &self.source
    }

    /// The current answer.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn outcome(&self) -> &Outcome
    {
        &self.outcome
    }

    /// Declaration judgements executed for this entry.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn judgements(&self) -> Judgements
    {
        self.judgements
    }

    /// The lifts the output left in a side table, by node.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn lifts(&self) -> &BTreeMap<ValueId, Lift>
    {
        &self.lifts
    }

    /// The type the declaration supplies, as the judging run's signature
    /// table held it.
    ///
    /// # Specification
    /// trivial.
    pub const fn supplied(&self) -> Maybe<FormedValueType, signature_table::Absent>
    {
        self.supplied
    }

    /// The body the declaration's constant unfolds to, as the judging run
    /// defined it, or why it has none.
    ///
    /// # Specification
    /// trivial.
    pub const fn unfolds(&self) -> Maybe<ValueId, unfolding::Absent>
    {
        self.unfolds
    }

    /// The entry of `source` after one judgement in `context` answered it:
    /// its outcome, with the lifts its output left.
    ///
    /// # Specification
    /// - requires: `context` is the context the judgement of `source` ran in,
    ///   and the outcome is its answer.
    /// - ensures: one judgement counted; the type the declaration supplies and
    ///   the body its constant unfolds to, read from `context`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — a resumed dependent of a filled hole unfolds it,
    ///   and per-entry counts distinguish adoption from judging again.
    /// - witness: `gandr-core-checker::tests::elaboration::incremental_equals_from_scratch`
    /// - witness: `gandr-core-checker::tests::elaboration::checked_success_is_stable_without_rejudgement`
    #[spec(ensures: |ret| ret.judgements == Judgements(1))]
    pub fn judged(
        context: &CheckingContext<'_>,
        source: Declaration,
        (outcome, lifts): (Outcome, BTreeMap<ValueId, Lift>),
    ) -> Self
    {
        let constant = source.constant();
        Self {
            supplied: context.signature(constant),
            unfolds: unfolds(context, constant, &outcome),
            source,
            outcome,
            lifts,
            judgements: Judgements(1),
        }
    }

    /// This entry, counted as judged once more than `earlier`.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub const fn after(
        mut self,
        earlier: Judgements,
    ) -> Self
    {
        self.judgements = Judgements(earlier.0.saturating_add(1));
        self
    }

    /// The verdict the checker's report carries for this entry: an accepted
    /// one over the emitted body.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Outcome::Checked`] gives its output's verdict,
    ///   [`Outcome::Formed`] [`Verdict::Data`], [`Outcome::Owed`] and
    ///   [`Outcome::Refused`] their payloads, and [`Outcome::Suspended`]
    ///   [`Verdict::Suspended`] at the type it supplies.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — readmission matches each outcome with its kernel
    ///   answer.
    /// - witness: `gandr-core-checker::tests::elaboration::every_fixture_the_checker_accepts_is_readmitted`
    #[spec(ensures: |ret| match self.outcome {
        Outcome::Checked(output) => ret == output.verdict,
        Outcome::Formed => ret == Verdict::Data,
        Outcome::Owed(owed) => ret == Verdict::Owed(owed),
        Outcome::Suspended(ref suspension) => ret == Verdict::Suspended(suspension.declared),
        Outcome::Refused(refusal) => ret == Verdict::Refused(refusal),
    })]
    pub(crate) fn verdict(&self) -> Verdict
    {
        match self.outcome {
            Outcome::Checked(output) => output.verdict,
            Outcome::Formed => Verdict::Data,
            Outcome::Owed(owed) => Verdict::Owed(owed),
            Outcome::Suspended(ref suspension) => Verdict::Suspended(suspension.declared),
            Outcome::Refused(refusal) => Verdict::Refused(refusal),
        }
    }
}

/// The body the run in `context` defined `constant` as, or why it has none:
/// owed for a hole, waiting for a suspended declaration.
///
/// # Specification
/// - requires: `outcome` is the run's answer for `constant`.
/// - ensures: [`unfolding::Absent::Owed`] for an owed outcome,
///   [`unfolding::Absent::Waiting`] for a suspended one, and otherwise the body
///   the context defines `constant` as, or [`unfolding::Absent::Rigid`].
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2/L3 — a resumed dependent of a filled hole unfolds it, and a
///   fill reading a waiting declaration waits on it.
/// - witness: `gandr-core-checker::tests::elaboration::incremental_equals_from_scratch`
/// - witness: `gandr-core-checker::tests::elaboration::filling_through_a_suspended_dependency_reports_only_still_owed_blockers`
#[spec(ensures: |ret| match *outcome {
    Outcome::Owed(_) => ret == Maybe::Absent(unfolding::Absent::Owed),
    Outcome::Suspended(_) => ret == Maybe::Absent(unfolding::Absent::Waiting),
    Outcome::Checked(_) | Outcome::Formed | Outcome::Refused(_) => ret != Maybe::Absent(unfolding::Absent::Owed)
        && ret != Maybe::Absent(unfolding::Absent::Waiting),
})]
fn unfolds(
    context: &CheckingContext<'_>,
    constant: ConstantIndex,
    outcome: &Outcome,
) -> Maybe<ValueId, unfolding::Absent>
{
    match *outcome {
        Outcome::Owed(_) => Maybe::Absent(unfolding::Absent::Owed),
        Outcome::Suspended(_) => Maybe::Absent(unfolding::Absent::Waiting),
        Outcome::Checked(_) | Outcome::Formed | Outcome::Refused(_) => {
            match context.definitions().body(constant) {
                Maybe::Present(body) => Maybe::Present(body),
                Maybe::Absent(_) => Maybe::Absent(unfolding::Absent::Rigid),
            }
        },
    }
}

/// Emit `body` with the transports the judgement just recorded, restarting
/// the recording for the next.
///
/// # Specification
/// - requires: `context` records transports.
/// - ensures: [`output::emit`]'s answer over the recorded transports; the
///   context records afresh.
/// - fails: [`CheckRefusal::MachineInvariant`] when the context records none;
///   the output pass's refusal.
/// - panics: none.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L1/L3 — a lifted argument is emitted explicitly, and two
///   declarations' transports stay their own, a refused one's included.
/// - witness: `gandr-core-checker::tests::elaboration::outputs_materialize_nested_lifts`
/// - witness: `gandr-core-checker::tests::elaboration::shared_code_occurrences_keep_distinct_transports`
/// - witness: `gandr-core-checker::tests::elaboration::a_refused_declaration_leaves_no_transport_behind`
#[spec(ensures: |ret| matches!(context.deferrals().emission, Emission::Recording(_)) || ret.is_err())]
pub fn emit_recorded(
    context: &mut CheckingContext<'_>,
    body: ValueId,
    budget: CheckBudget,
) -> Result<output::Emitted, CheckRefusal>
{
    let recorded = core::mem::replace(
        &mut context.deferrals_mut().emission,
        Emission::Recording(Transports::default()),
    );
    let Emission::Recording(transports) = recorded
    else {
        context.deferrals_mut().emission = recorded;
        return Err(CheckRefusal::MachineInvariant);
    };
    output::emit(context.arena_mut(), body, transports, budget)
}

/// Start recording, in `context`, the transports each judgement's output
/// emits.
///
/// # Specification
/// trivial.
pub fn record_transports(context: &mut CheckingContext<'_>)
{
    context.deferrals_mut().emission = Emission::Recording(Transports::default());
}

/// The outcome of the accepted `verdict` whose body emitted as `emitted`.
///
/// # Specification
/// - requires: `emitted` is the emission of `verdict`'s body.
/// - ensures: an accepted verdict whose emission succeeded is
///   [`Outcome::Checked`] over the emitted body, with the lifts the emission
///   left in a side table; one whose emission refused is [`Outcome::Refused`]
///   with that refusal, with no lifts.
/// - fails: never; a verdict that is not accepted is
///   [`CheckRefusal::MachineInvariant`] as the outcome.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 — readmission observes the emitted body under the verdict's
///   own evidence.
/// - witness: `gandr-core-checker::tests::elaboration::every_fixture_the_checker_accepts_is_readmitted`
/// - witness: `gandr-core-checker::tests::elaboration::outputs_materialize_nested_lifts`
#[spec(
    captures: emitted_before = emitted.as_ref().map(|emitted| emitted.body).map_err(|refusal| *refusal),
    ensures: |ret| match (&emitted_before, &ret.0) {
        (&Ok(body), &Outcome::Checked(output)) => output.body == body,
        (&Err(refusal), &Outcome::Refused(answer)) => refusal == answer,
        (_, &Outcome::Refused(CheckRefusal::MachineInvariant)) => true,
        _ => false,
    },
)]
pub fn accepted(
    verdict: Verdict,
    emitted: Result<output::Emitted, CheckRefusal>,
) -> (Outcome, BTreeMap<ValueId, Lift>)
{
    let emitted = match emitted {
        Ok(emitted) => emitted,
        Err(refusal) => return (Outcome::Refused(refusal), BTreeMap::new()),
    };
    let (declared, verdict) = match verdict {
        Verdict::Checked {
            declared, evidence, ..
        } => (declared, Verdict::Checked {
            declared,
            body: emitted.body,
            evidence,
        }),
        Verdict::Synthesised { synthesised, .. } => {
            (synthesised.produced(), Verdict::Synthesised {
                body: emitted.body,
                synthesised,
            })
        },
        Verdict::Data | Verdict::Owed(_) | Verdict::Suspended(_) | Verdict::Refused(_) => {
            return (
                Outcome::Refused(CheckRefusal::MachineInvariant),
                BTreeMap::new(),
            );
        },
    };
    (
        Outcome::Checked(Output {
            declared,
            body: emitted.body,
            verdict,
        }),
        emitted.lifts,
    )
}
