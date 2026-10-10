//! Term-producing elaboration with residual conversion and fill-only
//! resumption.
//!
//! The specification is Slattery and Sterling, *Bidirectional Elaborators à la
//! Carte*, arXiv:2607.09564v2: Construction 4.3, Theorem 5.1, Corollary 5.2,
//! Lemma 3.19 and Exegesis 6.6. Kernel readmission checks typing; the route-law
//! witnesses separately observe equality invariance, substitution and order.

mod constraints;
mod output;
#[cfg(test)]
mod tests;

use alloc::collections::BTreeSet;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_kernel_term::ConstantIndex;
use quenchant_shape::shape::Maybe;

pub(crate) use self::constraints::Deferrals;
pub(crate) use self::constraints::Deferred;
pub use self::constraints::Equation;
pub(crate) use self::output::CodeUse;
pub(crate) use self::output::Emission;
use crate::CheckBudget;
use crate::CheckRefusal;
use crate::CheckingContext;
use crate::CheckingForm;
use crate::Declaration;
use crate::FormedValueType;
use crate::ObligationEntry;
use crate::Verdict;
use crate::body;
use crate::bridge;
use crate::check_value;
use crate::form_value_type;
use crate::signature;
use crate::signature_table;
use crate::synthesise_value;
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
/// - witness: `elaboration::tests::every_fixture_the_checker_accepts_is_readmitted`
/// - witness: `elaboration::tests::outputs_materialize_nested_lifts`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Output
{
    /// The formed result type.
    declared: FormedValueType,
    /// The core output, with lifts materialized.
    body: ValueId,
    /// Evidence retained for the existing kernel bridge.
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

/// A declaration waiting for substitution at named module holes.
///
/// # Specification
/// - requires: created only by elaboration's residual collector.
/// - ensures: equations are sorted and unique; blockers are their distinct flex
///   heads still owed when this record is created. A suspended prerequisite can
///   retain an earlier equation after its hole is filled. The source
///   declaration is retained for resumption; there is no exported acceptance.
/// - provides: declaration-granular continuation, without a unification claim.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — exact blockers and equations detect refusal-as-suspension
///   and lost obligations; two residuals witness conjunction.
/// - witness: `elaboration::tests::owed_conversion_suspends`
/// - witness: `elaboration::tests::residual_conjunction_does_not_hide_refusal`
/// - witness: `elaboration::tests::filling_through_a_suspended_dependency_reports_only_still_owed_blockers`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Suspension
{
    /// The original judgement to resume.
    source: Declaration,
    /// Canonical residual equations, including suspended dependencies.
    equations: Vec<Equation>,
    /// Canonical owed-hole identities at creation.
    blockers: BTreeSet<ConstantIndex>,
    /// Earlier suspended declarations whose outputs this declaration uses.
    dependencies: BTreeSet<ConstantIndex>,
}

impl Suspension
{
    /// The declaration whose elaboration remains conditional.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn source(&self) -> Declaration
    {
        self.source
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

    /// Suspended declarations resumed before this continuation.
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

/// Elaboration's result, keeping an owed declaration apart from a suspension.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Outcome
{
    /// Every premise is settled and a core term is available.
    Checked(Output),
    /// The declaration itself lacks its body.
    Owed(ObligationEntry),
    /// The declaration's body waits on owed code constants.
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
    /// Its supplied type, retained even if a signed body refuses.
    supplied: Maybe<FormedValueType, signature_table::Absent>,
    /// Actual body-judgement invocations, excluding adoption and kernel replay.
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
}

/// An invalid request to fill or resume a module declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ResumeError
{
    /// The module has no declaration at this position.
    Unknown(ConstantIndex),
    /// Only a genuinely owed body may be filled.
    NotOwed(ConstantIndex),
    /// The proposed filling did not check; the session remains unchanged.
    Refused(CheckRefusal),
    /// The proposed filling itself needs a substitution; it is not installed.
    Suspended(Suspension),
}

impl fmt::Display for ResumeError
{
    /// Render the precise rejected transition.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            | Self::Unknown(constant) => write!(f, "unknown declaration {}", usize::from(constant)),
            | Self::NotOwed(constant) => {
                write!(f, "declaration {} has no owed body", usize::from(constant))
            },
            | Self::Refused(_) => f.write_str("filling fails checking"),
            | Self::Suspended(ref suspension) => write!(
                f,
                "filling of {} has residual equations",
                usize::from(suspension.source.constant())
            ),
        }
    }
}

impl core::error::Error for ResumeError
{
}

/// A module elaboration, admitting only checked hole fillings as mutations.
///
/// # Specification
/// - requires: input ids belong to the borrowed arena.
/// - ensures: checked outputs are retained under every admitted filling; only
///   explicitly resumed suspensions and proposed fillings are judged.
/// - provides: the fill-only substitution boundary behind stable success.
/// - panics: none.
/// - intension: each entry reports actual declaration judgements; rebuilding an
///   admission prefix adopts results and never increments those counts.
///
/// # Adequacy
/// - hypothesis: L2/L3 — filled batch equality, opposite resumption orders, and
///   unchanged checked work counts distinguish the three substitution laws.
/// - witness: `elaboration::tests::incremental_equals_from_scratch`
/// - witness: `elaboration::tests::resumptions_commute`
/// - witness: `elaboration::tests::checked_success_is_stable_without_rejudgement`
pub struct Session<'arena>
{
    /// Exclusive ownership of the arena borrow prevents external truncation.
    arena: &'arena mut CoreArena,
    /// One entry per input declaration, in admission order.
    entries: Vec<Entry>,
    /// The per-judgement and output-pass allowance.
    budget: CheckBudget,
}

impl<'arena> Session<'arena>
{
    /// Elaborate a module in admission order.
    ///
    /// # Specification
    /// - requires: ids resolve in `arena`; malformed inputs are refused.
    /// - ensures: one entry per declaration; checked outputs have explicit
    ///   lifts, and only bare owed flex–rigid comparisons become residuals.
    /// - fails: never; each refusal is an entry's outcome.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1/L3 — kernel replay checks output typing; exact residual
    ///   and refused-subterm observations separate all four outcomes.
    /// - witness: `elaboration::tests::every_fixture_the_checker_accepts_is_readmitted`
    /// - witness: `elaboration::tests::owed_conversion_suspends`
    /// - witness: `elaboration::tests::refused_subterms_refuse_the_declaration`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.entries.len() == declarations.len())]
    pub fn new(
        arena: &'arena mut CoreArena,
        declarations: &[Declaration],
        budget: CheckBudget,
    ) -> Self
    {
        let mut context = CheckingContext::new(arena, budget);
        let mut entries = Vec::with_capacity(declarations.len());
        for declaration in declarations {
            let entry = judge(&mut context, declaration, &entries);
            entries.push(entry);
        }
        Self {
            arena,
            entries,
            budget,
        }
    }

    /// Current answers in admission order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn entries(&self) -> &[Entry]
    {
        &self.entries
    }

    /// Read the emitted terms while the session owns the arena.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn arena(&self) -> &CoreArena
    {
        self.arena
    }

    /// Fill one owed body, without judging any dependent declaration.
    ///
    /// # Specification
    /// - requires: `body` belongs to the session's arena.
    /// - ensures: a successful fill checks against the original signature in
    ///   its original admission prefix, then replaces only that owed entry. A
    ///   failed fill changes no entry. Checked dependents are never judged.
    /// - fails: unknown position, a non-owed target, a refused or suspended
    ///   fill.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the corresponding `ResumeError` without installing the filling.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — batch equality and work counts witness
    ///   substitution; invalid fills distinguish substitution from arbitrary
    ///   body editing.
    /// - witness: `elaboration::tests::incremental_equals_from_scratch`
    /// - witness: `elaboration::tests::checked_success_is_stable_without_rejudgement`
    /// - witness: `elaboration::tests::invalid_fills_leave_entries_unchanged`
    /// - witness: `elaboration::tests::filling_through_a_suspended_dependency_reports_only_still_owed_blockers`
    #[inline]
    #[spec(
        captures: before = self.entries.clone(),
        ensures: |ret| match ret {
            | Err(_) => self.entries == before,
            | Ok(()) => self.entries.len() == before.len()
                && self.entries.iter().zip(&before).all(|(after, earlier)| {
                    if earlier.constant() == constant {
                        matches!(earlier.outcome, Outcome::Owed(_))
                            && matches!(after.outcome, Outcome::Checked(_))
                            && after.source.signature() == earlier.source.signature()
                            && after.source.body() == Maybe::Present(body)
                    } else {
                        after == earlier
                    }
                }),
        },
    )]
    pub fn fill(
        &mut self,
        constant: ConstantIndex,
        body: ValueId,
    ) -> Result<(), ResumeError>
    {
        let position = self
            .entries
            .iter()
            .position(|entry| entry.constant() == constant)
            .ok_or(ResumeError::Unknown(constant))?;
        let entry = self
            .entries
            .get(position)
            .ok_or(ResumeError::Unknown(constant))?;
        if !matches!(entry.outcome, Outcome::Owed(_)) {
            return Err(ResumeError::NotOwed(constant));
        }
        let source = Declaration::new(
            constant,
            entry.source.signature(),
            Maybe::Present(body),
            entry.source.origin(),
        );
        let count = entry.judgements;
        let mut replacement = in_prefix(self.arena, &self.entries, &source, self.budget)?;
        match replacement.outcome {
            | Outcome::Checked(_) => {},
            | Outcome::Refused(refusal) => return Err(ResumeError::Refused(refusal)),
            | Outcome::Suspended(suspension) => return Err(ResumeError::Suspended(suspension)),
            | Outcome::Owed(_) => return Err(ResumeError::Refused(CheckRefusal::MachineInvariant)),
        }
        replacement.judgements = Judgements(count.0.saturating_add(1));
        let entry = self
            .entries
            .get_mut(position)
            .ok_or(ResumeError::Unknown(constant))?;
        *entry = replacement;
        Ok(())
    }

    /// Resume a suspended declaration, or preserve a settled answer unchanged.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: judges only the suspended target and its suspended
    ///   prerequisites, in admission order. Every checked entry remains
    ///   unchanged; cached prefix bodies are adopted rather than rejudged.
    /// - fails: unknown target or inconsistent admission order in the prefix.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `ResumeError::Unknown` or the refused prefix admission.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — batch comparison and opposite orders observe the
    ///   calculus laws independently of typing; work counts detect rechecking.
    /// - witness: `elaboration::tests::incremental_equals_from_scratch`
    /// - witness: `elaboration::tests::resumptions_commute`
    /// - witness: `elaboration::tests::checked_success_is_stable_without_rejudgement`
    /// - witness: `elaboration::tests::dependent_resumption_closes_its_prerequisites`
    #[inline]
    #[spec(
        captures: before = self.entries.clone(),
        ensures: self.entries.len() == before.len()
            && self.entries.iter().zip(&before).all(|(after, earlier)| {
                after.source == earlier.source
                    && (matches!(earlier.outcome, Outcome::Suspended(_)) || after == earlier)
            }),
    )]
    pub fn resume(
        &mut self,
        constant: ConstantIndex,
    ) -> Result<(), ResumeError>
    {
        let mut pending = Vec::from([constant]);
        let mut scheduled = BTreeSet::new();
        while let Some(target) = pending.pop() {
            let entry = self
                .entries
                .iter()
                .find(|entry| entry.constant() == target)
                .ok_or(ResumeError::Unknown(target))?;
            if let Outcome::Suspended(ref suspension) = entry.outcome
                && scheduled.insert(target)
            {
                pending.extend(suspension.dependencies.iter().copied());
            }
        }
        for target in scheduled {
            let position = self
                .entries
                .iter()
                .position(|entry| entry.constant() == target)
                .ok_or(ResumeError::Unknown(target))?;
            let entry = self
                .entries
                .get(position)
                .ok_or(ResumeError::Unknown(target))?;
            let source = entry.source;
            let count = entry.judgements;
            let mut replacement = in_prefix(self.arena, &self.entries, &source, self.budget)?;
            replacement.judgements = Judgements(count.0.saturating_add(1));
            let entry = self
                .entries
                .get_mut(position)
                .ok_or(ResumeError::Unknown(target))?;
            *entry = replacement;
        }
        Ok(())
    }

    /// Independently readmit all settled outputs and owed holes.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the kernel sees emitted bodies, no implicit-lift side table,
    ///   and no suspended declaration. Refused entries cross as marks.
    /// - fails: never; kernel and bridge failures are readmission outcomes.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — the existing kernel independently checks every
    ///   output; no conditional success is smuggled into its environment as an
    ///   axiom.
    /// - witness: `elaboration::tests::every_fixture_the_checker_accepts_is_readmitted`
    /// - witness: `elaboration::tests::owed_conversion_suspends`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.readmitted().iter().map(bridge::Readmitted::constant).eq(
        self.entries.iter().filter(|entry| !matches!(entry.outcome, Outcome::Suspended(_)))
            .map(Entry::constant)
    ))]
    pub fn readmit(&mut self) -> bridge::Readmission
    {
        let report = crate::module::elaborated_report(&self.entries);
        bridge::readmit(self.arena, &report)
    }
}

/// Recover settled bridge input without exposing conditional evidence.
///
/// # Specification
/// trivial.
pub(crate) fn settled(entry: &Entry) -> Maybe<(Declaration, Verdict), unsettled::Absent>
{
    let verdict = match entry.outcome {
        | Outcome::Checked(output) => output.verdict,
        | Outcome::Owed(owed) => Verdict::Owed(owed),
        | Outcome::Refused(refusal) => Verdict::Refused(refusal),
        | Outcome::Suspended(_) => return Maybe::Absent(unsettled::Absent::Suspended),
    };
    Maybe::Present((entry.source, verdict))
}

quenchant_shape::reason_enum! {
    /// Why no settled bridge input exists.
    pub(crate) mod unsettled {
        /// The declaration still has residual premises.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub enum Absent {
            /// No accepted term or owed axiom may be exported.
            Suspended,
        }
    }
}

/// Adopt a cached prefix and judge just the requested declaration.
///
/// # Specification
/// - requires: `source` names an entry in `entries`.
/// - ensures: only `source` is judged; the prefix supplies cached signatures,
///   accepted definitions and owed-hole identities in admission order.
/// - fails: refused admission order in the prefix.
/// - panics: none.
///
/// # Errors
/// Returns the prefix's `ResumeError::Refused`.
///
/// # Adequacy
/// - hypothesis: L2/L3 — batch equality checks prefix reconstruction, and
///   per-entry counts distinguish adoption from rejudgement.
/// - witness: `elaboration::tests::incremental_equals_from_scratch`
/// - witness: `elaboration::tests::checked_success_is_stable_without_rejudgement`
#[spec(
    requires: entries.iter().any(|entry| entry.constant() == source.constant()),
    ensures: |ret| match ret {
        | Ok(ref entry) => entry.source == *source && entry.judgements == Judgements(1),
        | Err(_) => true,
    },
)]
fn in_prefix(
    arena: &mut CoreArena,
    entries: &[Entry],
    source: &Declaration,
    budget: CheckBudget,
) -> Result<Entry, ResumeError>
{
    let mut context = CheckingContext::new(arena, budget);
    for entry in entries
        .iter()
        .take_while(|entry| entry.constant() != source.constant())
    {
        let body = match entry.outcome {
            | Outcome::Checked(output) => Maybe::Present(output.body),
            | Outcome::Owed(_) | Outcome::Suspended(_) | Outcome::Refused(_) => {
                Maybe::Absent(unfolding::Absent::Rigid)
            },
        };
        context
            .adopt(entry.constant(), entry.supplied, body)
            .map_err(ResumeError::Refused)?;
        if matches!(entry.outcome, Outcome::Owed(_)) {
            context.deferrals().owed.insert(entry.constant());
        }
    }
    Ok(judge(&mut context, source, entries))
}

/// Run one declaration's conjunctive premises, then publish only settled
/// output.
///
/// # Specification
/// - requires: `prior` contains the earlier declaration outcomes.
/// - ensures: a refused premise wins over collected residuals; otherwise any
///   residual or suspended dependency withholds output. Only a fully checked
///   body becomes a definition. Owed declarations enter the flex-head set.
/// - fails: never; source and machine failures become `Outcome::Refused`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1/L3 — emitted terms, exact blockers and a bad premise after
///   a deferred comparison separate success, suspension and multistrict
///   refusal.
/// - witness: `elaboration::tests::every_fixture_the_checker_accepts_is_readmitted`
/// - witness: `elaboration::tests::residual_conjunction_does_not_hide_refusal`
#[spec(ensures: |ret| ret.source == *source)]
fn judge(
    context: &mut CheckingContext<'_>,
    source: &Declaration,
    prior: &[Entry],
) -> Entry
{
    context.deferrals().emission = Emission::Recording(output::Transports::default());
    context.start_support();
    let verdict = judge_body(context, source);
    let support = context.finish_support();
    let mut equations = core::mem::take(&mut context.deferrals().equations);
    let mut dependencies = BTreeSet::new();
    let mut refusal = match verdict {
        | Verdict::Refused(refusal) => Maybe::Present(refusal),
        | _ => Maybe::Absent(unsettled::Absent::Suspended),
    };
    for consulted in support.consulted() {
        if let Some(entry) = prior
            .iter()
            .find(|entry| entry.constant() == consulted.constant())
        {
            match entry.outcome {
                | Outcome::Suspended(ref suspension) => {
                    equations.extend_from_slice(&suspension.equations);
                    dependencies.insert(entry.constant());
                },
                | Outcome::Refused(reason) => refusal = Maybe::Present(reason),
                | Outcome::Checked(_) | Outcome::Owed(_) => {},
            }
        }
    }
    let outcome = if let Maybe::Present(refusal) = refusal {
        Outcome::Refused(refusal)
    }
    else if !equations.is_empty() {
        equations.sort_unstable();
        equations.dedup();
        let owed = &context.deferrals().owed;
        let blockers = equations
            .iter()
            .map(Equation::hole)
            .filter(|hole| owed.contains(hole))
            .collect();
        Outcome::Suspended(Suspension {
            source: *source,
            equations,
            blockers,
            dependencies,
        })
    }
    else {
        match finish(context, verdict) {
            | Ok(outcome) => outcome,
            | Err(refusal) => Outcome::Refused(refusal),
        }
    };
    match outcome {
        | Outcome::Checked(output) => {
            context.define(source.constant(), output.declared, output.body);
        },
        | Outcome::Owed(_) => {
            context.deferrals().owed.insert(source.constant());
        },
        | Outcome::Suspended(_) | Outcome::Refused(_) => {},
    }
    Entry {
        source: *source,
        supplied: context.signature(source.constant()),
        outcome,
        judgements: Judgements(1),
    }
}

/// Apply the existing four faces without defining a conditional body.
///
/// # Specification
/// - requires: the context belongs exclusively to this elaboration run.
/// - ensures: preserves ordinary declaration direction and signature admission;
///   conversion may accumulate residuals which `judge` must discharge before
///   exporting evidence. No body is installed as a definition here.
/// - fails: never; every failure is a provisional refused verdict.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1/L3 — readmission and all four declaration outcomes observe
///   the direction and admission boundary.
/// - witness: `elaboration::tests::every_fixture_the_checker_accepts_is_readmitted`
/// - witness: `elaboration::tests::owed_conversion_suspends`
#[spec(ensures: |ret| match ret {
    | Verdict::Checked { body, .. } => source.body() == Maybe::Present(body)
        && matches!(source.signature(), Maybe::Present(_)),
    | Verdict::Synthesised { body, .. } => source.body() == Maybe::Present(body)
        && matches!(source.signature(), Maybe::Absent(_)),
    | Verdict::Owed(owed) => matches!(source.body(), Maybe::Absent(_))
        && owed.absence().constant() == source.constant(),
    | Verdict::Refused(_) => true,
})]
fn judge_body(
    context: &mut CheckingContext<'_>,
    source: &Declaration,
) -> Verdict
{
    if let Err(refusal) = context.admit(source.constant()) {
        return Verdict::Refused(refusal);
    }
    match source.signature() {
        | Maybe::Present(signature) => {
            let declared = match form_value_type(context, signature) {
                | Ok(declared) => declared,
                | Err(refusal) => return Verdict::Refused(refusal),
            };
            let verdict = match source.body() {
                | Maybe::Present(body) => match check_value(context, body, declared) {
                    | Ok(evidence) => Verdict::Checked {
                        declared,
                        body,
                        evidence,
                    },
                    | Err(refusal) => Verdict::Refused(refusal),
                },
                | Maybe::Absent(body::Absent::Hole) => Verdict::Owed(ObligationEntry::from(
                    crate::ledger::Absence::new(source.constant(), declared, source.origin()),
                )),
            };
            context.record(source.constant(), declared);
            verdict
        },
        | Maybe::Absent(signature::Absent::Unsigned) => match source.body() {
            | Maybe::Present(body) => match synthesise_value(context, body) {
                | Ok(synthesised) => {
                    context.record(source.constant(), synthesised.produced());
                    Verdict::Synthesised { body, synthesised }
                },
                | Err(refusal) => Verdict::Refused(refusal),
            },
            | Maybe::Absent(body::Absent::Hole) => {
                Verdict::Refused(CheckRefusal::NotSynthesisable {
                    form: CheckingForm::Hole(source.constant()),
                })
            },
        },
    }
}

/// Materialize a settled body's output without an implicit conversion table.
///
/// # Specification
/// - requires: `verdict` has no residual premises.
/// - ensures: accepted bodies have every recorded lift written into their core
///   term; owed and refused verdicts retain their distinction.
/// - fails: output traversal faults or an exhausted output budget.
/// - panics: none.
///
/// # Errors
/// Returns the output pass's `CheckRefusal`.
///
/// # Adequacy
/// - hypothesis: L1/L3 — a nested lifted argument and independent readmission
///   distinguish explicit emission from a retained side table.
/// - witness: `elaboration::tests::outputs_materialize_nested_lifts`
#[spec(ensures: |ret| match (&ret, verdict) {
    | (&Ok(Outcome::Checked(output)), Verdict::Checked { declared, .. }) => output.declared == declared,
    | (&Ok(Outcome::Checked(output)), Verdict::Synthesised { synthesised, .. }) =>
        output.declared == synthesised.produced(),
    | (&Ok(Outcome::Owed(actual)), Verdict::Owed(expected)) => actual == expected,
    | (&Ok(Outcome::Refused(actual)), Verdict::Refused(expected)) => actual == expected,
    | (&Err(_), _) => true,
    | _ => false,
})]
fn finish(
    context: &mut CheckingContext<'_>,
    verdict: Verdict,
) -> Result<Outcome, CheckRefusal>
{
    let (declared, body) = match verdict {
        | Verdict::Checked { declared, body, .. } => (declared, body),
        | Verdict::Synthesised { body, synthesised } => (synthesised.produced(), body),
        | Verdict::Owed(owed) => return Ok(Outcome::Owed(owed)),
        | Verdict::Refused(refusal) => return Ok(Outcome::Refused(refusal)),
    };
    let Emission::Recording(transports) = core::mem::take(&mut context.deferrals().emission)
    else {
        return Err(CheckRefusal::MachineInvariant);
    };
    let budget = context.budget();
    let body = output::emit(context.arena_mut(), body, transports, budget)?;
    let verdict = match verdict {
        | Verdict::Checked {
            declared, evidence, ..
        } => Verdict::Checked {
            declared,
            body,
            evidence,
        },
        | Verdict::Synthesised { synthesised, .. } => Verdict::Synthesised { body, synthesised },
        | Verdict::Owed(_) | Verdict::Refused(_) => return Err(CheckRefusal::MachineInvariant),
    };
    Ok(Outcome::Checked(Output {
        declared,
        body,
        verdict,
    }))
}
