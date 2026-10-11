//! Live match observations over an evaluated scrutinee.
//!
//! The checkpoint retains the semantic value, including hole closures. Filling
//! it resumes that value through the live evaluator. Coverage is a report from
//! the checker, independent of the per-arm answers; it grants no admission.

use anodized::spec;
use gandr_core_checker::CheckingContext;
use gandr_core_checker::Coverage;
use gandr_core_checker::CoverageFault;
use gandr_core_checker::FormedValueType;
use gandr_core_checker::cover;
use gandr_core_nbe::ArmIndex;
use gandr_core_nbe::Definitions;
use gandr_core_nbe::DomainArena;
use gandr_core_nbe::DomainValueId;
use gandr_core_nbe::Environment;
use gandr_core_nbe::EvalFault;
use gandr_core_nbe::Fuel;
use gandr_core_nbe::Glued;
use gandr_core_nbe::LiveFault;
use gandr_core_nbe::MatchFault;
use gandr_core_nbe::Matched;
use gandr_core_nbe::Selection;
use gandr_core_nbe::eval_value_within;
use gandr_core_nbe::fill_and_resume;
use gandr_core_nbe::match_pattern;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::hole::HoleId;
use gandr_core_term::hole::TermId;
use gandr_core_term::pattern::BranchStatus;
use gandr_core_term::pattern::PatternId;
use gandr_core_term::pattern::Patterns;

/// An evaluated scrutinee, retained independently of its source expression.
///
/// # Specification
/// - requires: subsequent operations use the arena and definitions the
///   checkpoint was evaluated against, extended without changing existing ids.
/// - ensures: a fill reads the retained value, not the original expression.
/// - provides: hole closures and already-reduced work across observations.
/// - fails: evaluation and filling retain their core failure vocabulary.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: filling a root hole refines only the constructor tests that
///   depended on it, without changing the arm order.
/// - witness: `tests::live_match::filling_a_hole_refines_a_possible_verdict`
#[derive(Debug)]
pub struct MatchCheckpoint
{
    /// Semantic nodes retained by the checkpoint.
    domain: DomainArena,
    /// The current scrutinee in that domain.
    scrutinee: DomainValueId,
}

/// Per-arm liveness, first-match selection, and an independent coverage report.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MatchAnalysis
{
    /// Each arm's answer against the retained scrutinee, in source order.
    branches: Vec<BranchStatus>,
    /// The first arm not refuted; a possible arm blocks later arms.
    selection: Selection,
    /// Coverage may fail independently of evaluating the scrutinee.
    coverage: Result<Coverage, CoverageFault>,
}

/// Execution of the selected arm; a possible arm executes no body.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MatchRun
{
    /// The selected arm evaluated in the checkpoint's semantic domain.
    Evaluated
    {
        /// The selected source-order arm.
        arm: ArmIndex,
        /// The resulting computation in the retained domain.
        result: gandr_core_nbe::DomainCompId,
    },
    /// An unfinished test prevented selection.
    Held(ArmIndex),
    /// Every written test refuted the scrutinee.
    Uncovered,
}

/// Why a selected arm could not be executed.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MatchRunFault
{
    /// The body table omitted the selected arm.
    MissingArm(ArmIndex),
    /// The core evaluator refused the selected body.
    Eval(EvalFault),
}

impl MatchAnalysis
{
    /// Each arm's three-valued answer, without erasing shadowed arms.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn branches(&self) -> &[BranchStatus]
    {
        &self.branches
    }

    /// Ordered selection; bindings address the checkpoint's domain.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn selection(&self) -> &Selection
    {
        &self.selection
    }

    /// The checker's report, including a refusal to analyze.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn coverage(&self) -> &Result<Coverage, CoverageFault>
    {
        &self.coverage
    }
}

impl MatchCheckpoint
{
    /// Evaluate a closed scrutinee once, keeping holes as semantic values.
    ///
    /// # Specification
    /// - requires: `scrutinee` is closed and resolves in `core`; definitions
    ///   belong to that arena.
    /// - ensures: on success the checkpoint retains its weak-head value.
    /// - provides: the evaluator's remaining allowance beside the checkpoint.
    /// - fails: the evaluator's typed refusal, including exhausted fuel.
    /// - panics: none.
    ///
    /// # Errors
    /// [`EvalFault`] if the scrutinee cannot be evaluated under the allowance.
    ///
    /// # Adequacy
    /// - hypothesis: concrete constructor heads survive a hole in a field,
    ///   whereas a hole at the root decides no constructor test.
    /// - witness: `tests::live_match::a_hole_scrutinee_leaves_every_branch_possible`
    /// - witness: `tests::live_match::a_constructor_scrutinee_refutes_the_head_and_suspends_the_payload`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&(ref checkpoint, remaining)|
        checkpoint.domain.value(checkpoint.scrutinee).is_some()
            && u32::from(remaining) <= u32::from(fuel)))]
    #[inline]
    pub fn evaluate(
        core: &CoreArena,
        definitions: Definitions<'_>,
        fuel: Fuel,
        scrutinee: ValueId,
    ) -> Result<(Self, Fuel), EvalFault>
    {
        let mut domain = DomainArena::new();
        let (scrutinee, remaining) = eval_value_within(
            core,
            &mut domain,
            definitions,
            fuel,
            scrutinee,
            Environment::new(),
        )?;
        Ok((Self { domain, scrutinee }, remaining))
    }

    /// Observe every arm and report coverage without enforcing it.
    ///
    /// # Specification
    /// - requires: `context` reads this checkpoint's arena; `scrutinee_type`
    ///   describes its scrutinee, and every arm names a pattern in `patterns`.
    /// - ensures: one core live answer per arm; selection is the first answer
    ///   not refuted and is indeterminate if that answer is possible. Coverage
    ///   is the checker's independent report, including analysis failures.
    /// - provides: coverage never blocks selection or changes arm verdicts.
    /// - fails: [`MatchFault`] when a pattern or semantic node cannot be read.
    /// - panics: none.
    ///
    /// # Errors
    /// [`MatchFault`] preserves the core matcher's refusal.
    ///
    /// # Adequacy
    /// - hypothesis: a hole before a matching arm suspends selection without
    ///   hiding that later arm's satisfied verdict or asserting redundancy.
    /// - witness: `tests::live_match::a_hole_in_the_prefix_leaves_redundancy_unproved`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |analysis|
        analysis.branches.len() == arms.len()))]
    #[inline]
    pub fn analyze(
        &self,
        context: &mut CheckingContext<'_>,
        scrutinee_type: FormedValueType,
        patterns: &Patterns,
        arms: &[PatternId],
    ) -> Result<MatchAnalysis, MatchFault>
    {
        let mut branches = Vec::with_capacity(arms.len());
        let mut selection = Selection::Exhausted;
        for (index, &pattern) in arms.iter().enumerate() {
            let answer = match_pattern(
                context.arena(),
                &self.domain,
                patterns,
                pattern,
                self.scrutinee,
            )?;
            branches.push(answer.status());
            if selection == Selection::Exhausted {
                selection = match answer {
                    | Matched::Satisfied(bindings) => Selection::Taken {
                        arm: ArmIndex::from(index),
                        bindings,
                    },
                    | Matched::Possibly => Selection::Indeterminate {
                        arm: ArmIndex::from(index),
                    },
                    | Matched::Refuted => Selection::Exhausted,
                };
            }
        }
        let coverage = cover(context, scrutinee_type, patterns, arms);
        Ok(MatchAnalysis {
            branches,
            selection,
            coverage,
        })
    }

    /// Fill a hole in the retained scrutinee and resume suspended eliminations.
    ///
    /// # Specification
    /// - requires: `core` and `definitions` are this checkpoint's; `filling`
    ///   resolves in `core` at the context of the named hole.
    /// - ensures: success replaces the retained scrutinee with its resumed
    ///   value; failure leaves the previously observable scrutinee in place.
    /// - provides: other holes remain; no original expression is re-evaluated.
    /// - fails: [`LiveFault`] preserves readback and evaluation refusals.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LiveFault`] when the fill cannot read or resume the retained value.
    ///
    /// # Adequacy
    /// - hypothesis: a filling of the root hole changes possible injection
    ///   tests into the correct satisfied and refuted pair.
    /// - witness: `tests::live_match::filling_a_hole_refines_a_possible_verdict`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |remaining|
        self.domain.value(self.scrutinee).is_some()
            && u32::from(*remaining) <= u32::from(fuel)))]
    #[inline]
    pub fn fill(
        &mut self,
        core: &mut CoreArena,
        definitions: Definitions<'_>,
        fuel: Fuel,
        hole: HoleId,
        filling: TermId,
    ) -> Result<Fuel, LiveFault>
    {
        let (filled, remaining) = fill_and_resume(
            core,
            &mut self.domain,
            definitions,
            fuel,
            Glued::Value(self.scrutinee),
            hole,
            filling,
        )?;
        let Glued::Value(scrutinee) = filled
        else {
            return Err(LiveFault::Eval(EvalFault::MachineInvariant));
        };
        self.scrutinee = scrutinee;
        Ok(remaining)
    }

    /// Run the selected arm under the bindings produced by its live answer.
    ///
    /// # Specification
    /// - requires: `analysis` was produced by this checkpoint without an
    ///   intervening fill. Each body is closed apart from its pattern binders
    ///   and the global definitions. Binders are in pattern traversal order.
    /// - ensures: a possible arm executes no body, an exhausted match remains
    ///   uncovered, and a selected arm executes exactly its own body.
    /// - provides: execution without re-evaluating the scrutinee or matching
    ///   the patterns again.
    /// - fails: the selected body is absent or the evaluator refuses it.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the missing arm or the core evaluation fault.
    ///
    /// # Adequacy
    /// - hypothesis: a pattern hole holds both its own and later bodies,
    ///   whereas an earlier settled arm still executes.
    /// - witness: `tests::pattern_holes::an_unfilled_hole_never_runs_its_own_arm`
    /// - witness: `tests::pattern_holes::an_arm_before_the_hole_still_wins`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |&(run, remaining)|
        u32::from(remaining) <= u32::from(fuel) && match run {
            MatchRun::Evaluated { result, .. } => self.domain.computation(result).is_some(),
            MatchRun::Held(_) | MatchRun::Uncovered => remaining == fuel,
        }))]
    #[inline]
    pub fn run(
        &mut self,
        core: &CoreArena,
        definitions: Definitions<'_>,
        fuel: Fuel,
        analysis: &MatchAnalysis,
        bodies: &[gandr_core_term::ComputationId],
    ) -> Result<(MatchRun, Fuel), MatchRunFault>
    {
        match *analysis.selection() {
            | Selection::Indeterminate { arm } => Ok((MatchRun::Held(arm), fuel)),
            | Selection::Exhausted => Ok((MatchRun::Uncovered, fuel)),
            | Selection::Taken { arm, ref bindings } => {
                let &body = bodies
                    .get(usize::from(arm))
                    .ok_or(MatchRunFault::MissingArm(arm))?;
                let mut environment = Environment::new();
                for &bound in bindings {
                    environment.extend(gandr_core_term::Zone::Intuitionistic, bound);
                }
                let (result, remaining) = gandr_core_nbe::eval_comp_within(
                    core,
                    &mut self.domain,
                    definitions,
                    fuel,
                    body,
                    environment,
                )
                .map_err(MatchRunFault::Eval)?;
                Ok((MatchRun::Evaluated { arm, result }, remaining))
            },
        }
    }

    /// The retained semantic domain, including selected pattern bindings.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn domain(&self) -> &DomainArena
    {
        &self.domain
    }
}
