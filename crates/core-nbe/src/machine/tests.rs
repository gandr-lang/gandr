mod trace_pairing;

// The test harness links `std`; the canonicalizer keys its tables by hash.
extern crate std;

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::CompType;
use gandr_core_term::CompTypeId;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::DefinitionChain;
use gandr_core_term::DefinitionalEnvironment;
use gandr_core_term::Sort;
use gandr_core_term::Transparency;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_check_memo::CheckMemo;
use gandr_kernel_check_memo::NullMemo;
use gandr_kernel_conversion_trace::ConversionDecision;
use gandr_kernel_conversion_trace::ConversionSide;
use gandr_kernel_conversion_trace::NullSink;
use gandr_kernel_conversion_trace::SubgoalPosition;
use gandr_kernel_conversion_trace::TraceLog;
use gandr_kernel_conversion_trace::TraceSink;
use gandr_kernel_core::EngineClaim;
use gandr_kernel_core::KernelVerdict;
use gandr_kernel_core::ReplayBudget;
use gandr_kernel_core::ReplayDecline;
use gandr_kernel_core::ReplayNode;
use gandr_kernel_core::ReplayRefusal;
use gandr_kernel_core::ReplaySides;
use gandr_kernel_core::TracePosition;
use gandr_kernel_core::Unfoldable;
use gandr_kernel_core::Unfoldings;
use gandr_kernel_core::replay;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GlobalIndex;
use gandr_kernel_term::TermArena;

use super::DeclineReason;
use super::MachineReport;
use super::MachineSettings;
use super::MachineVerdict;
use super::Problem;
use super::ProcessId;
use super::StepBudget;
use super::TraceNode;
use super::decide;
use crate::arena::DomainArena;
use crate::domain::BinderLevel;
use crate::eval::Definitions;
use crate::eval::Endpoints;
use crate::eval::Fuel;
use crate::eval::LoweredChain;
use crate::eval::eval_computation;
use crate::eval::eval_value;
use crate::free::CoreTerm;
use crate::measure::ShareCount;
use crate::measure::SharingMeasure;
use crate::overlay::Bound;
use crate::overlay::CompGraft;
use crate::overlay::CompNode;
use crate::overlay::Overlay;
use crate::overlay::OverlayId;
use crate::overlay::ShareArity;
use crate::overlay::ShareDistance;
use crate::overlay::SharePosition;
use crate::overlay::Sharing;
use crate::overlay::ValueGraft;
use crate::overlay::ValueNode;
use crate::policy::DuplicationStance;
use crate::policy::GranularityPolicy;
use crate::policy::SchedulingPolicy;
use crate::policy::SchedulingStance;
use crate::resharing::GoalSupport;
use crate::resharing::ResharingMemo;
use crate::traced::TracedDuplication;

/// A pair of core terms of one polarity, to be evaluated and compared.
#[derive(Clone, Copy, Debug)]
enum Sides
{
    /// Two values.
    Values(ValueId, ValueId),
    /// Two computations.
    Computations(ComputationId, ComputationId),
}

/// A core arena and the definitions lowered into it.
struct World
{
    /// The terms.
    core: CoreArena,
    /// The definitions, constant `n` the `n`th admitted.
    chain: LoweredChain,
    /// The definitional environment, which seals nothing.
    environment: DefinitionalEnvironment,
    /// Every constant's body, at its admission position.
    bodies: Vec<ValueId>,
    /// How the world's runs read a compound endpoint.
    endpoints: Endpoints,
}

/// Which earlier definitions a fixture's definition declares it mentions.
#[derive(Clone, Copy, Debug)]
enum Mentions
{
    /// None: every definition sits at height one.
    Nothing,
    /// The one admitted just before it: constant `n` sits at height `n +
    /// 1`.
    Previous,
}

impl World
{
    /// Admit one manifest definition per `(entry, body)`, in order: the
    /// `n`th is the constant [`Name`] `n` names, its body stored under the
    /// table entry `entry` names.
    ///
    /// # Specification
    /// - requires: two definitions naming one entry name one body.
    /// - ensures: as [`World::admit`] over the entries the names give.
    /// - provides: the fixture every machine test over named constants runs in.
    /// - panics: as [`World::admit`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — for coherent named entry/body fixtures, admission
    ///   order assigns constants while names choose shared table entries.
    ///   Observable unfolding traces and the one-body/two-definition process
    ///   count distinguish confusing a name with an admission position, losing
    ///   a body or duplicating a shared lowering.
    /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
    /// - witness: `machine::tests::one_body_is_evaluated_once_for_two_definitions`
    #[spec(
            captures: [mark = core.watermark()],
            ensures: |ret| ret.core.watermark() == mark && ret.bodies.len() == bodies.len()
                && bodies.iter().enumerate().all(|(position, &(name, body))|
                    ret.bodies.get(position) == Some(&body)
                        && ret.chain.chain().entry(ConstantIndex::from(position)).is_some_and(|entry| entry.body() == name.entry())
                        && Definitions::new(&ret.chain, &ret.environment, ret.environment.root()).bodies().get(&name.entry()) == Some(&body))
        )]
    fn new(
        core: CoreArena,
        bodies: &[(Name, ValueId)],
    ) -> Self
    {
        let entries: Vec<(GlobalIndex, ValueId)> = bodies
            .iter()
            .map(|&(name, body)| (name.entry(), body))
            .collect();
        Self::admit(core, &entries)
    }

    /// Admit one manifest definition per `(entry, body)`, in order: the
    /// `n`th is constant `n`, its body stored under table entry `entry`.
    ///
    /// # Specification
    /// - requires: two definitions naming one entry name one body.
    /// - ensures: every constant admitted unfolds to its body; every other
    ///   constant is rigid.
    /// - provides: the fixture every machine test runs in.
    /// - panics: when the chain refuses a definition, which no fixture
    ///   provokes.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — coherent table entries are admitted without mentions,
    ///   including repeated entries and recursive bodies. The observer is the
    ///   resulting comparison trace and exact shared-body count; wrong ordinal
    ///   assignment, accidental dependency heights or per-definition lowering
    ///   change those observations.
    /// - witness: `machine::tests::one_body_is_evaluated_once_for_two_definitions`
    /// - witness: `machine::tests::a_definition_cycle_declines_rather_than_unfolding_forever`
    /// - witness: `machine::tests::re_sharing_runs_one_goal_per_distinct_pair`
    #[spec(
            captures: [mark = core.watermark()],
            ensures: |ret| ret.core.watermark() == mark && ret.bodies.len() == bodies.len()
                && bodies.iter().enumerate().all(|(position, &(entry, body))|
                    ret.bodies.get(position) == Some(&body)
                        && ret.chain.chain().entry(ConstantIndex::from(position)).is_some_and(|definition| definition.body() == entry)
                        && Definitions::new(&ret.chain, &ret.environment, ret.environment.root()).bodies().get(&entry) == Some(&body)
                        && u32::from(Definitions::new(&ret.chain, &ret.environment, ret.environment.root()).height(ConstantIndex::from(position))) == 1)
        )]
    fn admit(
        core: CoreArena,
        bodies: &[(GlobalIndex, ValueId)],
    ) -> Self
    {
        Self::chained(core, bodies, Mentions::Nothing)
    }

    /// Admit one manifest definition per `(entry, body)` as
    /// [`World::admit`] does, but with each definition declaring a
    /// mention of the one before it, so constant `n` sits at height
    /// `n + 1`.
    ///
    /// # Specification
    /// - requires: as [`World::admit`].
    /// - ensures: as [`World::admit`], with the heights rising by one per
    ///   position.
    /// - provides: the fixture whose heights a weighted schedule reads.
    /// - panics: as [`World::admit`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a positional chain mentions its immediate
    ///   predecessor, so unequal heights remain observable on either side of a
    ///   comparison. The height probe and fair/weighted divergence fixture
    ///   distinguish flat heights, wrong predecessor references and a shifted
    ///   admission order.
    /// - witness: `machine::tests::head_height_is_symmetric_and_nonconstants_stay_at_the_floor`
    /// - witness: `machine::tests::an_unlucky_schedule_declines_and_the_kernel_with_it`
    #[spec(
            captures: [mark = core.watermark()],
            ensures: |ret| ret.core.watermark() == mark && ret.bodies.len() == bodies.len()
                && bodies.iter().enumerate().all(|(position, &(entry, body))|
                    ret.bodies.get(position) == Some(&body)
                        && Definitions::new(&ret.chain, &ret.environment, ret.environment.root()).bodies().get(&entry) == Some(&body)
                        && usize::try_from(u32::from(Definitions::new(&ret.chain, &ret.environment, ret.environment.root()).height(ConstantIndex::from(position)))).ok() == position.checked_add(1))
        )]
    fn stacked(
        core: CoreArena,
        bodies: &[(GlobalIndex, ValueId)],
    ) -> Self
    {
        Self::chained(core, bodies, Mentions::Previous)
    }

    /// Admit one manifest definition per `(entry, body)`, each declaring
    /// the mentions `mentions` names.
    ///
    /// # Specification
    /// - requires: as [`World::admit`].
    /// - ensures: as [`World::admit`], at the heights the mentions give.
    /// - provides: the one admission both fixtures share.
    /// - panics: as [`World::admit`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the input is a coherent ordered list of table
    ///   entries, with either no mentions or only the immediate predecessor.
    ///   The observer is exact body sharing and unequal head heights; swapped
    ///   bodies, ordinal/entry confusion and the wrong mention policy alter
    ///   counts, traces or weighted scheduling.
    /// - witness: `machine::tests::one_body_is_evaluated_once_for_two_definitions`
    /// - witness: `machine::tests::head_height_is_symmetric_and_nonconstants_stay_at_the_floor`
    /// - witness: `machine::tests::an_unlucky_schedule_declines_and_the_kernel_with_it`
    #[spec(
            captures: [mark = core.watermark()],
            ensures: |ret| ret.core.watermark() == mark && ret.bodies.len() == bodies.len()
                && ret.chain.chain().entries().len() == bodies.len()
                && bodies.iter().enumerate().all(|(position, &(entry, body))| {
                    let definitions = Definitions::new(&ret.chain, &ret.environment, ret.environment.root());
                    ret.bodies.get(position) == Some(&body) && definitions.bodies().get(&entry) == Some(&body)
                        && ret.chain.chain().entry(ConstantIndex::from(position)).is_some_and(|definition| definition.body() == entry)
                        && usize::try_from(u32::from(definitions.height(ConstantIndex::from(position)))).ok()
                            == match mentions { Mentions::Nothing => Some(1), Mentions::Previous => position.checked_add(1) }
                })
        )]
    fn chained(
        core: CoreArena,
        bodies: &[(GlobalIndex, ValueId)],
        mentions: Mentions,
    ) -> Self
    {
        let mut chain = DefinitionChain::new();
        for (position, &(entry, _)) in bodies.iter().enumerate() {
            let previous = match (mentions, position.checked_sub(1)) {
                (Mentions::Previous, Some(previous)) => Vec::from([ConstantIndex::from(previous)]),
                (Mentions::Nothing, _) | (Mentions::Previous, None) => Vec::new(),
            };
            let defined = chain.define(
                ConstantIndex::from(position),
                entry,
                Transparency::Manifest,
                &previous,
            );
            assert!(defined.is_ok(), "fixtures admit constants in order");
        }
        let Ok(chain) = LoweredChain::lower(chain, |entry| {
            bodies
                .get(usize::from(entry.constant()))
                .map(|&(_, body)| body)
                .ok_or_else(|| entry.constant())
        })
        else {
            panic!("every admitted constant has a body");
        };
        Self {
            core,
            chain,
            environment: DefinitionalEnvironment::new(),
            bodies: bodies.iter().map(|&(_, body)| body).collect(),
            endpoints: Endpoints::Run,
        }
    }

    /// The same world, its runs holding compound endpoints.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the same terms and definitions, read under
    ///   [`Endpoints::Hold`].
    /// - provides: the stance a traced endpoint comparison runs in.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one nested endpoint traced in both stances records
    ///   its unfoldings only when held; a world that ignored the stance would
    ///   record the same trace twice.
    /// - witness: `machine::tests::a_held_endpoint_unfolds_by_a_recorded_step`
    #[spec(ensures: |ret| ret.endpoints == Endpoints::Hold)]
    fn holding(self) -> Self
    {
        Self {
            endpoints: Endpoints::Hold,
            ..self
        }
    }

    /// Evaluate `sides` into a fresh domain and decide them under the
    /// default settings.
    ///
    /// # Specification
    /// - requires: both sides are closed.
    /// - ensures: as [`World::run_under`] with the default settings.
    /// - provides: the entry every machine test with no settings of its own
    ///   goes through.
    /// - panics: as [`World::run_under`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — closed catalogue and ladder sides that evaluate
    ///   within the fixture fuel are run from fresh domains. Verdict, process
    ///   and derivation counts separate stale run state, a lost definitive
    ///   answer and recording that changes the comparison; the same inputs are
    ///   checked with recording off and on.
    /// - witness: `machine::tests::recording_does_not_move_the_verdict`
    /// - witness: `machine::tests::the_sink_off_run_keeps_no_derivation`
    /// - witness: `machine::tests::re_sharing_runs_one_goal_per_distinct_pair`
    #[spec(
            ensures: |ret| usize::from(ret.derivations()) == if matches!(S::ACTIVITY, super::SinkActivity::Active) {
                usize::from(ret.processes())
            } else { 0 }
                && (usize::from(ret.processes()) != 0
                    || (u64::from(ret.steps()) == 0 && !matches!(ret.verdict(), MachineVerdict::Declined(_))))
        )]
    fn run<S>(
        &self,
        sides: Sides,
        sink: &mut S,
    ) -> MachineReport
    where
        S: TraceSink<TraceNode>,
    {
        self.run_under(MachineSettings::default(), sides, sink)
    }

    /// Evaluate `sides` into a fresh domain and decide them under
    /// `settings`, re-sharing through the engine path's memo.
    ///
    /// # Specification
    /// - requires: both sides are closed.
    /// - ensures: as [`World::run_with`] at [`ResharingMemo`].
    /// - provides: the entry every machine test with settings of its own goes
    ///   through.
    /// - panics: as [`World::run_with`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — closed sides with bounded weak-head evaluation are
    ///   compared under caller-supplied scheduling and step budgets. The
    ///   observed verdict and trace distinguish ignoring the budget, ignoring
    ///   the stance and mistaking a decline for a refutation.
    /// - witness: `machine::tests::a_diverging_evaluation_declines_on_the_budget`
    /// - witness: `machine::tests::an_unlucky_schedule_declines_and_the_kernel_with_it`
    /// - witness: `machine::tests::recording_does_not_move_the_verdict`
    #[spec(
            ensures: |ret| usize::from(ret.derivations()) == if matches!(S::ACTIVITY, super::SinkActivity::Active) {
                usize::from(ret.processes())
            } else { 0 }
                && (usize::from(ret.processes()) != 0
                    || (u64::from(ret.steps()) == 0 && !matches!(ret.verdict(), MachineVerdict::Declined(_))))
        )]
    fn run_under<S>(
        &self,
        settings: MachineSettings,
        sides: Sides,
        sink: &mut S,
    ) -> MachineReport
    where
        S: TraceSink<TraceNode>,
    {
        self.run_with::<S, ResharingMemo>(settings, sides, sink)
    }

    /// Evaluate `sides` into a fresh domain and decide them under
    /// `settings`, re-sharing through a memo of type `M`.
    ///
    /// # Specification
    /// - requires: both sides are closed.
    /// - ensures: the machine's report.
    /// - provides: the one entry every machine test goes through, and the one
    ///   the memo differential instantiates twice.
    /// - panics: when evaluation or the machine refuses, which no fixture
    ///   provokes.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the domain is closed fixture sides with weak heads
    ///   obtainable within the fixed fuel, under either a run-local sharing
    ///   memo or the null memo. Verdict, process and support-edge counts
    ///   distinguish stale domains, lost sharing and accounting retained in a
    ///   memoless run; a genuine shared wait cycle may decline differently from
    ///   its unrolled reference.
    /// - witness: `machine::tests::the_memo_never_moves_a_verdict`
    /// - witness: `machine::tests::re_sharing_runs_one_goal_per_distinct_pair`
    /// - witness: `machine::tests::a_goal_resting_on_itself_declines_on_the_cycle`
    /// - witness: `machine::tests::edges_per_revision_grow_with_the_distinct_goals`
    #[spec(
            ensures: |ret| (usize::from(ret.derivations()) == if matches!(S::ACTIVITY, super::SinkActivity::Active) {
                usize::from(ret.processes())
            } else { 0 }
                && (usize::from(ret.processes()) != 0
                    || (u64::from(ret.steps()) == 0 && !matches!(ret.verdict(), MachineVerdict::Declined(_)))))
                && (matches!(M::ACTIVITY, super::MemoActivity::Active) || ret.edges() == super::SupportEdges::default())
        )]
    fn run_with<S, M>(
        &self,
        settings: MachineSettings,
        sides: Sides,
        sink: &mut S,
    ) -> MachineReport
    where
        S: TraceSink<TraceNode>,
        M: CheckMemo<GoalSupport, ProcessId> + Default,
    {
        let definitions = Definitions::new(&self.chain, &self.environment, self.environment.root())
            .reading_endpoints(self.endpoints);
        let mut domain = DomainArena::new();
        let fuel = Fuel::from(4_096_u32);
        let problem = match sides {
            Sides::Values(left, right) => {
                let left = eval_value(&self.core, &mut domain, definitions, fuel, left)
                    .expect("the left side evaluates");
                let right = eval_value(&self.core, &mut domain, definitions, fuel, right)
                    .expect("the right side evaluates");
                Problem::values(left, right)
            },
            Sides::Computations(left, right) => {
                let left = eval_computation(&self.core, &mut domain, definitions, fuel, left)
                    .expect("the left side evaluates");
                let right = eval_computation(&self.core, &mut domain, definitions, fuel, right)
                    .expect("the right side evaluates");
                Problem::computations(left, right)
            },
        };
        decide::<S, M>(
            &self.core,
            &mut domain,
            definitions,
            settings,
            problem,
            sink,
        )
        .expect("the machine answers every fixture")
    }

    /// Decide `sides` and keep the trace.
    ///
    /// # Specification
    /// - requires: as [`World::run`].
    /// - ensures: the verdict and the decisions recorded, in order.
    /// - provides: the trace every decision-level assertion reads.
    /// - panics: as [`World::run`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — closed fixtures may produce either verdict or decline
    ///   on a cycle or unresolved code. The observer is the exact ordered trace
    ///   and the empty conversion derivation on decline; eager emission of
    ///   speculative branches, wrong-side decisions and a decline emitted as
    ///   evidence change these witnesses.
    /// - witness: `machine::tests::a_refutation_outranks_a_decline`
    /// - witness: `machine::tests::codes_that_could_unfold_inside_are_declined`
    /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
    #[spec(
            ensures: |ret| !matches!(ret.0, MachineVerdict::Declined(_)) || ret.1.is_empty()
        )]
    fn traced(
        &self,
        sides: Sides,
    ) -> (MachineVerdict, Vec<ConversionDecision<TraceNode>>)
    {
        let mut log = TraceLog::new();
        let report = self.run(sides, &mut log);
        (report.verdict(), log.decisions().copied().collect())
    }

    /// Replay `decisions` for `sides` in the kernel, against the claim
    /// `verdict` makes.
    ///
    /// # Specification
    /// - requires: `sides` lie in this world's arena.
    /// - ensures: the kernel's verdict over a translation of the world's terms
    ///   and bodies, every admitted constant unfoldable and every other one
    ///   opaque.
    /// - provides: the end-to-end check every replay test runs.
    /// - panics: as [`Kernel::translate`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — supported intuitionistic fixtures are translated
    ///   independently, and the supplied trace may be genuine or have a changed
    ///   branch decision. The observer is kernel agreement, a named refusal for
    ///   the tampering, or an engine-decline result; trusting the claim or
    ///   treating a decline/refusal as the opposite verdict changes these
    ///   outcomes.
    /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
    /// - witness: `machine::tests::a_trace_naming_the_wrong_branch_is_refused`
    /// - witness: `machine::tests::an_unlucky_schedule_declines_and_the_kernel_with_it`
    #[spec(
            ensures: |ret| (!matches!(verdict, MachineVerdict::Declined(_))
                || ret == KernelVerdict::Declined(ReplayDecline::EngineDeclined))
                && (ret != KernelVerdict::Convertible || verdict == MachineVerdict::Convertible)
                && (ret != KernelVerdict::NotConvertible || verdict == MachineVerdict::NotConvertible)
        )]
    fn replayed(
        &self,
        sides: Sides,
        verdict: MachineVerdict,
        decisions: &[ConversionDecision<TraceNode>],
    ) -> KernelVerdict
    {
        let mut kernel = Kernel::default();
        let mut bodies = Vec::new();
        for &body in &self.bodies {
            bodies.push(Unfoldable::Body(kernel.value(&self.core, body)));
        }
        let sides = match sides {
            Sides::Values(left, right) => ReplaySides::Values(
                kernel.value(&self.core, left),
                kernel.value(&self.core, right),
            ),
            Sides::Computations(left, right) => ReplaySides::Computations(
                kernel.computation(&self.core, left),
                kernel.computation(&self.core, right),
            ),
        };
        let claim = match verdict {
            MachineVerdict::Convertible => EngineClaim::Convertible,
            MachineVerdict::NotConvertible => EngineClaim::NotConvertible,
            MachineVerdict::Declined(_) => EngineClaim::Declined,
        };
        replay(
            &mut kernel.arena,
            &Unfoldings::new(bodies),
            sides,
            claim,
            decisions.iter().map(|&decision| kernel_decision(decision)),
            ReplayBudget::DEFAULT,
        )
    }

    /// Lift each side into an overlay sharing every node it reaches along
    /// two edges, evaluate both under the spinal stance into a fresh
    /// domain over a copy of the world's arena, and decide them under
    /// `settings` through the installation's recording sink.
    ///
    /// # Specification
    /// - requires: both sides are closed.
    /// - ensures: the machine's report and the decisions the bound sink
    ///   recorded, in order.
    /// - provides: the spinal run every certification test replays.
    /// - panics: when installation, evaluation or the machine refuses, which no
    ///   fixture provokes.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — supported closed value and computation fixtures are
    ///   lifted and evaluated with recorded spinal duplication before
    ///   conversion. Kernel agreement on both verdicts and on a
    ///   schedule-induced decline distinguishes changed denotation, misplaced
    ///   shares and partial duplication evidence mistaken for a conversion
    ///   verdict.
    /// - witness: `machine::tests::the_kernel_certifies_every_spinal_catalogue_and_ladder_trace`
    /// - witness: `machine::tests::an_unlucky_spinal_schedule_declines_and_the_kernel_with_it`
    #[spec(
            ensures: |ret| usize::from(ret.0.derivations()) == usize::from(ret.0.processes())
                && (usize::from(ret.0.processes()) != 0
                    || (u64::from(ret.0.steps()) == 0 && !matches!(ret.0.verdict(), MachineVerdict::Declined(_))))
        )]
    fn spinal(
        &self,
        settings: MachineSettings,
        sides: Sides,
    ) -> (MachineReport, Vec<ConversionDecision<TraceNode>>)
    {
        let definitions = Definitions::new(&self.chain, &self.environment, self.environment.root());
        let mut core = self.core.clone();
        let mut domain = DomainArena::new();
        let fuel = Fuel::from(4_096_u32);
        let mut log = TraceLog::new();
        let report = {
            let mut spinal = TracedDuplication::install(DuplicationStance::Spinal, &mut log)
                .expect("a recording sink carries the spinal stance");
            let problem = match sides {
                Sides::Values(left, right) => {
                    let [left, right] = [left, right].map(|side| {
                        let (mut overlay, root) = lifted(&self.core, CoreTerm::Value(side));
                        let OverlayId::Value(root) = root
                        else {
                            panic!("a value lifts to a value");
                        };
                        spinal
                            .eval_overlay_value(
                                &mut overlay,
                                &mut core,
                                &mut domain,
                                definitions,
                                fuel,
                                root,
                            )
                            .expect("the side evaluates under the spinal stance")
                            .0
                    });
                    Problem::values(left, right)
                },
                Sides::Computations(left, right) => {
                    let [left, right] = [left, right].map(|side| {
                        let (mut overlay, root) = lifted(&self.core, CoreTerm::Computation(side));
                        let OverlayId::Computation(root) = root
                        else {
                            panic!("a computation lifts to a computation");
                        };
                        spinal
                            .eval_overlay_computation(
                                &mut overlay,
                                &mut core,
                                &mut domain,
                                definitions,
                                fuel,
                                root,
                            )
                            .expect("the side evaluates under the spinal stance")
                            .0
                    });
                    Problem::computations(left, right)
                },
            };
            spinal
                .decide::<ResharingMemo>(&core, &mut domain, definitions, settings, problem)
                .expect("the machine answers every fixture")
        };
        (report, log.decisions().copied().collect())
    }

    /// The shares each side's lifted overlay holds.
    ///
    /// # Specification
    /// - requires: both sides lie in this world's arena.
    /// - ensures: the share count of the left side's lifted overlay, then the
    ///   right side's.
    /// - provides: the check that a certification test exercised sharing.
    /// - panics: when a lifted overlay does not measure, which a fixture this
    ///   small never provokes.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — supported acyclic term fixtures include a leaf and
    ///   distinct arena nodes for equal nested pairs. Exact counts of zero and
    ///   two shared legs, plus erasure to the original tree, distinguish
    ///   pointer-only sharing, missing inner shares and a non-share node
    ///   counted as a share.
    /// - witness: `machine::tests::lifting_shares_equal_trees_without_reusing_occurrence_nodes`
    /// - witness: `machine::tests::the_kernel_certifies_every_spinal_catalogue_and_ladder_trace`
    #[spec(
            ensures: |ret| {
             let roots = match sides { Sides::Values(a,b) => [CoreTerm::Value(a),CoreTerm::Value(b)], Sides::Computations(a,b) => [CoreTerm::Computation(a),CoreTerm::Computation(b)] };
             (roots[0] != roots[1] || ret[0] == ret[1]) && roots.into_iter().zip(ret).all(|(root,count)|
                !matches!(root, CoreTerm::Value(id) if matches!(self.core.value(id), Some(Value::Variable{..} | Value::Constant(_) | Value::Literal(_)))) || u64::from(count) == 0)
            }
        )]
    fn shares(
        &self,
        sides: Sides,
    ) -> [ShareCount; 2]
    {
        let roots = match sides {
            Sides::Values(left, right) => [CoreTerm::Value(left), CoreTerm::Value(right)],
            Sides::Computations(left, right) => {
                [CoreTerm::Computation(left), CoreTerm::Computation(right)]
            },
        };
        roots.map(|side| {
            let (overlay, root) = lifted(&self.core, side);
            SharingMeasure::of(&overlay, root)
                .expect("a lifted side measures")
                .shares()
        })
    }
}

/// A share's place in a lifted overlay's nest, outermost first; read as a
/// count, the shares around a lifted leg or body.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Nest(usize);

/// One step of a walk over a core term.
#[derive(Clone, Copy, Debug)]
enum Lifting
{
    /// Visit a node, or queue its children.
    Enter(CoreTerm),
    /// Finish a node once its children are done.
    Exit(CoreTerm),
}

/// The children of the core node `node`, left to right.
///
/// # Specification
/// - requires: `node` resolves in the pure fixture language of `core`.
/// - ensures: each child the former names, in the order erasure mints them.
/// - provides: the one reading of a core former the lifting walks share.
/// - panics: when the node is unresolved or outside the pure fixture language.
///
/// # Adequacy
/// - hypothesis: L3 — resolved term formers are observed through lifted erasure
///   and independent kernel replay. Ordered mixed-family application, bind and
///   case children distinguish omitted, swapped or wrong-family edges; the leaf
///   and nested-pair witness also exercises zero, one and repeated children.
/// - witness: `machine::tests::lifting_shares_equal_trees_without_reusing_occurrence_nodes`
/// - witness: `machine::tests::the_kernel_certifies_every_spinal_catalogue_and_ladder_trace`
/// - witness: `machine::tests::trace_pairing::every_pair_of_generated_ladder_traces_replays`
#[spec(
        ensures: |ret| match node {
         CoreTerm::Value(id) => core.value(id).is_some_and(|value| match *value {
          Value::Constructor {ref fields,..} => ret.iter().copied().eq(fields.iter().copied().map(CoreTerm::Value)),
          Value::Record(ref fields) => ret.iter().copied().eq(fields.values().copied().map(CoreTerm::Value)),
          Value::Univalence(..) |
          Value::Reify(_) | Value::Here(_) | Value::Funext(..) | Value::Equiv(..) | Value::Ua { .. } | Value::Returned(_) | Value::Nested(_) | Value::Run(_) | Value::SessionRelated { .. } | Value::Stay(_) | Value::Then(..) | Value::FlowProduct(..) | Value::Forward(_) | Value::FunctionFlow(..) | Value::Recorded(_) => false,
          Value::PathRefl(code) => ret.as_slice() == [CoreTerm::Value(code)],
          Value::PathProduct(first, second) => ret.as_slice() == [CoreTerm::Value(first), CoreTerm::Value(second)],
          Value::PathEquiv { forward, backward, .. } => ret.as_slice() == [CoreTerm::Value(forward), CoreTerm::Value(backward)],
          Value::ListCons(a,b) | Value::StaticApplication(a,b) => ret.as_slice() == [CoreTerm::Value(a),CoreTerm::Value(b)],
          Value::Tuple(ref components) => ret.iter().copied().eq(components.iter().copied().map(CoreTerm::Value)),
          Value::ListNil | Value::Primitive { .. } | Value::Variable{..} | Value::Constant(_) | Value::Literal(_) | Value::Quote(_) | Value::QuoteComputation(_) | Value::Hole(_) => ret.is_empty(),
          Value::StaticLambda(body) | Value::Injection(_,body) | Value::Lift{body,..} | Value::Mark{body,..} => ret.as_slice() == [CoreTerm::Value(body)],
          Value::Thunk(body) => ret.as_slice() == [CoreTerm::Computation(body)],
          }),
         CoreTerm::Computation(id) => core.computation(id).is_some_and(|computation| match *computation {
          Computation::DataCase {scrutinee,ref branches,..} => ret.iter().copied().eq(core::iter::once(CoreTerm::Value(scrutinee)).chain(branches.iter().copied().map(CoreTerm::Computation))),
          Computation::RecordProjection(record,_) | Computation::TupleProjection(record,_) => ret.as_slice() == [CoreTerm::Value(record)],
          Computation::Perform { .. } | Computation::Handle { .. } | Computation::Exercise { .. } | Computation::Scope { .. } | Computation::Resume(..) | Computation::Abandon(_) | Computation::Split { .. } | Computation::Reset(_) | Computation::Shift(_) | Computation::With(..) | Computation::Project(..) | Computation::PathTransport { .. } | Computation::Ride { .. } | Computation::TelescopeTransport { .. } | Computation::Session(_) | Computation::Memory(_) | Computation::World(_) => false,
          Computation::ListFold { list,on_nil,on_cons,.. } | Computation::ListCase { list,on_nil,on_cons,.. } => ret.as_slice() == [CoreTerm::Value(list),CoreTerm::Computation(on_nil),CoreTerm::Computation(on_cons)],
          Computation::Primitive { arguments, .. } => ret.iter().copied().eq(arguments.iter().copied().map(CoreTerm::Value)),
          Computation::Transport(path, value) => ret.as_slice() == [CoreTerm::Value(path), CoreTerm::Value(value)],
          Computation::Lambda(body) | Computation::Mark{body,..} | Computation::Ascribe { body, .. } | Computation::Fixpoint { body, .. } => ret.as_slice() == [CoreTerm::Computation(body)],
          Computation::Application(head,arg) => ret.as_slice() == [CoreTerm::Computation(head),CoreTerm::Value(arg)],
          Computation::Return(value) | Computation::Force(value) => ret.as_slice() == [CoreTerm::Value(value)],
          Computation::Bind(bound,body) => ret.as_slice() == [CoreTerm::Computation(bound),CoreTerm::Computation(body)],
          Computation::Case{scrutinee,ref branches} => ret.iter().copied().eq(core::iter::once(CoreTerm::Value(scrutinee)).chain(branches.iter().copied().map(CoreTerm::Computation))),
          Computation::Hole(_) => ret.is_empty(),
         }),
        }
    )]
fn core_children(
    core: &CoreArena,
    node: CoreTerm,
) -> Vec<CoreTerm>
{
    match node {
        CoreTerm::Value(id) => match *core.value(id).expect("a reached value resolves") {
            Value::Constructor { ref fields, .. } => {
                fields.iter().copied().map(CoreTerm::Value).collect()
            },
            Value::Record(ref fields) => fields.values().copied().map(CoreTerm::Value).collect(),
            Value::Here(_)
            | Value::Funext(..)
            | Value::Equiv(..)
            | Value::Univalence(..)
            | Value::SessionRelated { .. }
            | Value::Stay(_)
            | Value::Then(..)
            | Value::FlowProduct(..)
            | Value::Forward(_)
            | Value::FunctionFlow(..)
            | Value::Recorded(_)
            | Value::Ua { .. }
            | Value::Returned(_)
            | Value::Nested(_)
            | Value::Run(_)
            | Value::Reify(_) => {
                panic!("the pure fixture language has no reified stacks")
            },
            Value::Primitive { .. }
            | Value::Variable { .. }
            | Value::Constant(_)
            | Value::ListNil
            | Value::Literal(_)
            | Value::Quote(_)
            | Value::QuoteComputation(_)
            | Value::Hole(_) => Vec::new(),
            Value::Tuple(ref components) => {
                components.iter().copied().map(CoreTerm::Value).collect()
            },
            Value::PathRefl(code) => Vec::from([CoreTerm::Value(code)]),
            Value::PathEquiv {
                forward, backward, ..
            } => Vec::from([CoreTerm::Value(forward), CoreTerm::Value(backward)]),
            Value::PathProduct(first, second)
            | Value::ListCons(first, second)
            | Value::StaticApplication(first, second) => {
                Vec::from([CoreTerm::Value(first), CoreTerm::Value(second)])
            },
            Value::StaticLambda(body)
            | Value::Injection(_, body)
            | Value::Lift { body, .. }
            | Value::Mark { body, .. } => Vec::from([CoreTerm::Value(body)]),
            Value::Thunk(body) => Vec::from([CoreTerm::Computation(body)]),
        },
        CoreTerm::Computation(id) => {
            match *core
                .computation(id)
                .expect("a reached computation resolves")
            {
                Computation::DataCase {
                    scrutinee,
                    ref branches,
                    ..
                } => core::iter::once(CoreTerm::Value(scrutinee))
                    .chain(branches.iter().copied().map(CoreTerm::Computation))
                    .collect(),
                Computation::RecordProjection(record, _)
                | Computation::TupleProjection(record, _) => Vec::from([CoreTerm::Value(record)]),
                Computation::PathTransport { .. }
                | Computation::Ride { .. }
                | Computation::TelescopeTransport { .. }
                | Computation::Perform { .. }
                | Computation::Handle { .. }
                | Computation::Exercise { .. }
                | Computation::Scope { .. }
                | Computation::Resume(..)
                | Computation::Abandon(_)
                | Computation::Split { .. }
                | Computation::Reset(_)
                | Computation::Shift(_)
                | Computation::With(..)
                | Computation::Project(..)
                | Computation::Session(_)
                | Computation::Memory(_)
                | Computation::World(_) => {
                    panic!("the pure fixture language has no runtime control formers")
                },
                Computation::ListFold {
                    list,
                    on_nil,
                    on_cons,
                    ..
                }
                | Computation::ListCase {
                    list,
                    on_nil,
                    on_cons,
                    ..
                } => Vec::from([
                    CoreTerm::Value(list),
                    CoreTerm::Computation(on_nil),
                    CoreTerm::Computation(on_cons),
                ]),
                Computation::Primitive { arguments, .. } => {
                    arguments.iter().copied().map(CoreTerm::Value).collect()
                },
                Computation::Transport(path, value) => {
                    Vec::from([CoreTerm::Value(path), CoreTerm::Value(value)])
                },
                Computation::Lambda(body)
                | Computation::Mark { body, .. }
                | Computation::Ascribe { body, .. }
                | Computation::Fixpoint { body, .. } => Vec::from([CoreTerm::Computation(body)]),
                Computation::Hole(_) => Vec::new(),
                Computation::Application(head, argument) => {
                    Vec::from([CoreTerm::Computation(head), CoreTerm::Value(argument)])
                },
                Computation::Return(value) | Computation::Force(value) => {
                    Vec::from([CoreTerm::Value(value)])
                },
                Computation::Bind(bound, body) => {
                    Vec::from([CoreTerm::Computation(bound), CoreTerm::Computation(body)])
                },
                Computation::Case {
                    scrutinee,
                    ref branches,
                } => core::iter::once(CoreTerm::Value(scrutinee))
                    .chain(branches.iter().copied().map(CoreTerm::Computation))
                    .collect(),
            }
        },
    }
}

/// Each node `root` reaches in `core`, mapped to the first node of equal
/// structure the walk completed.
///
/// # Specification
/// - requires: `root` resolves in `core`.
/// - ensures: a representative per reached term node, equal as a tree with
///   quoted type ids opaque; equal trees share a representative.
/// - provides: the hash-consing the lifter shares repeated subterms by.
/// - panics: when a reached node does not resolve.
///
/// # Adequacy
/// - hypothesis: L3 — finite resolved term DAGs are compared structurally, with
///   quoted type ids kept opaque. The observer is exact shared-leg count and
///   the erased tree; retaining nominally distinct equal pairs, merging unlike
///   formers or returning non-idempotent representatives changes these
///   observations.
/// - witness: `machine::tests::lifting_shares_equal_trees_without_reusing_occurrence_nodes`
/// - witness: `machine::tests::the_kernel_certifies_every_spinal_catalogue_and_ladder_trace`
/// - witness: `machine::tests::trace_pairing::every_pair_of_generated_ladder_traces_replays`
#[spec(
        ensures: |ret| ret.contains_key(&root) && ret.iter().all(|(node,representative)| {
         ret.get(representative) == Some(representative) && match (*node,*representative) {
         (CoreTerm::Value(node),CoreTerm::Value(representative)) => core.value(node).is_some() && core.value(representative).is_some(),
         (CoreTerm::Computation(node),CoreTerm::Computation(representative)) => core.computation(node).is_some() && core.computation(representative).is_some(),
         _ => false,
         }
        })
    )]
fn canonical(
    core: &CoreArena,
    root: CoreTerm,
) -> BTreeMap<CoreTerm, CoreTerm>
{
    let mut canon: BTreeMap<CoreTerm, CoreTerm> = BTreeMap::new();
    let mut values: std::collections::HashMap<Value, CoreTerm> = std::collections::HashMap::new();
    let mut computations: std::collections::HashMap<Computation, CoreTerm> =
        std::collections::HashMap::new();
    let mut walk = Vec::from([Lifting::Enter(root)]);
    while let Some(step) = walk.pop() {
        match step {
            Lifting::Enter(node) => {
                if canon.contains_key(&node) {
                    continue;
                }
                walk.push(Lifting::Exit(node));
                for child in core_children(core, node).into_iter().rev() {
                    walk.push(Lifting::Enter(child));
                }
            },
            Lifting::Exit(node) => {
                if canon.contains_key(&node) {
                    continue;
                }
                let value = |id: ValueId| match canon[&CoreTerm::Value(id)] {
                    CoreTerm::Value(id) => id,
                    CoreTerm::Computation(_) => panic!("a value is represented by a value"),
                };
                let computation = |id: ComputationId| match canon[&CoreTerm::Computation(id)] {
                    CoreTerm::Computation(id) => id,
                    CoreTerm::Value(_) => {
                        panic!("a computation is represented by a computation")
                    },
                };
                let representative = match node {
                    CoreTerm::Value(id) => {
                        let key = match core.value(id).expect("a reached value resolves").clone() {
                            Value::Constructor {
                                datatype,
                                tag,
                                mut fields,
                            } => {
                                for field in &mut fields {
                                    *field = value(*field);
                                }
                                Value::Constructor {
                                    datatype,
                                    tag,
                                    fields,
                                }
                            },
                            Value::Record(mut fields) => {
                                for field in fields.values_mut() {
                                    *field = value(*field);
                                }
                                Value::Record(fields)
                            },
                            Value::Here(_)
                            | Value::Funext(..)
                            | Value::Equiv(..)
                            | Value::Univalence(..)
                            | Value::SessionRelated { .. }
                            | Value::Stay(_)
                            | Value::Then(..)
                            | Value::FlowProduct(..)
                            | Value::Forward(_)
                            | Value::FunctionFlow(..)
                            | Value::Recorded(_)
                            | Value::Ua { .. }
                            | Value::Returned(_)
                            | Value::Nested(_)
                            | Value::Run(_)
                            | Value::Reify(_) => {
                                panic!("the pure fixture language has no reified stacks")
                            },
                            value @ Value::Primitive { .. } => value,
                            Value::ListNil => Value::ListNil,
                            Value::ListCons(first, second) => {
                                Value::ListCons(value(first), value(second))
                            },
                            Value::PathRefl(code) => Value::PathRefl(value(code)),
                            Value::PathProduct(first, second) => {
                                Value::PathProduct(value(first), value(second))
                            },
                            Value::PathEquiv {
                                path_type,
                                forward,
                                backward,
                                evidence,
                            } => Value::PathEquiv {
                                path_type,
                                forward: value(forward),
                                backward: value(backward),
                                evidence,
                            },
                            Value::Tuple(mut components) => {
                                for component in &mut components {
                                    *component = value(*component);
                                }
                                Value::Tuple(components)
                            },
                            Value::Injection(summand, body) => {
                                Value::Injection(summand, value(body))
                            },
                            Value::Thunk(body) => Value::Thunk(computation(body)),
                            Value::StaticLambda(body) => Value::StaticLambda(value(body)),
                            Value::StaticApplication(head, argument) => {
                                Value::StaticApplication(value(head), value(argument))
                            },
                            Value::Lift { target, body } => Value::Lift {
                                target,
                                body: value(body),
                            },
                            Value::Mark { mark, body } => Value::Mark {
                                mark,
                                body: value(body),
                            },
                            leaf @ (Value::Variable { .. }
                            | Value::Constant(_)
                            | Value::Literal(_)
                            | Value::Quote(_)
                            | Value::QuoteComputation(_)
                            | Value::Hole(_)) => leaf,
                        };
                        *values.entry(key).or_insert(node)
                    },
                    CoreTerm::Computation(id) => {
                        let key = match *core
                            .computation(id)
                            .expect("a reached computation resolves")
                        {
                            Computation::DataCase {
                                scrutinee,
                                motive,
                                ref branches,
                            } => Computation::DataCase {
                                scrutinee: value(scrutinee),
                                motive,
                                branches: branches
                                    .iter()
                                    .map(|branch| computation(*branch))
                                    .collect(),
                            },
                            Computation::RecordProjection(record, ref label) => {
                                Computation::RecordProjection(value(record), label.clone())
                            },
                            Computation::TupleProjection(tuple, component) => {
                                Computation::TupleProjection(value(tuple), component)
                            },
                            Computation::PathTransport { .. }
                            | Computation::Ride { .. }
                            | Computation::TelescopeTransport { .. }
                            | Computation::Perform { .. }
                            | Computation::Handle { .. }
                            | Computation::Exercise { .. }
                            | Computation::Scope { .. }
                            | Computation::Resume(..)
                            | Computation::Abandon(_)
                            | Computation::Split { .. }
                            | Computation::Reset(_)
                            | Computation::Shift(_)
                            | Computation::With(..)
                            | Computation::Project(..)
                            | Computation::Session(_)
                            | Computation::Memory(_)
                            | Computation::World(_) => {
                                panic!("the pure fixture language has no runtime control formers")
                            },
                            Computation::ListFold {
                                element,
                                result,
                                list,
                                on_nil,
                                on_cons,
                            } => Computation::ListFold {
                                element,
                                result,
                                list: value(list),
                                on_nil: computation(on_nil),
                                on_cons: computation(on_cons),
                            },
                            Computation::ListCase {
                                list,
                                on_nil,
                                on_cons,
                            } => Computation::ListCase {
                                list: value(list),
                                on_nil: computation(on_nil),
                                on_cons: computation(on_cons),
                            },
                            Computation::Primitive {
                                primitive,
                                mut arguments,
                            } => {
                                for argument in arguments.iter_mut() {
                                    *argument = value(*argument);
                                }
                                Computation::Primitive {
                                    primitive,
                                    arguments,
                                }
                            },
                            Computation::Transport(path, argument) => {
                                Computation::Transport(value(path), value(argument))
                            },
                            Computation::Lambda(body) => Computation::Lambda(computation(body)),
                            Computation::Fixpoint { body, evidence } => Computation::Fixpoint {
                                body: computation(body),
                                evidence,
                            },
                            Computation::Application(head, argument) => {
                                Computation::Application(computation(head), value(argument))
                            },
                            Computation::Return(returned) => Computation::Return(value(returned)),
                            Computation::Force(forced) => Computation::Force(value(forced)),
                            Computation::Bind(bound, body) => {
                                Computation::Bind(computation(bound), computation(body))
                            },
                            Computation::Ascribe { body, ty } => Computation::Ascribe {
                                body: computation(body),
                                ty,
                            },
                            Computation::Case {
                                scrutinee,
                                ref branches,
                            } => Computation::Case {
                                scrutinee: value(scrutinee),
                                branches: branches
                                    .iter()
                                    .map(|branch| computation(*branch))
                                    .collect(),
                            },
                            Computation::Mark { mark, body } => Computation::Mark {
                                mark,
                                body: computation(body),
                            },
                            Computation::Hole(hole) => Computation::Hole(hole),
                        };
                        *computations.entry(key).or_insert(node)
                    },
                };
                canon.insert(node, representative);
            },
        }
    }
    canon
}

/// The children of `node`, each read through `canon`.
///
/// # Specification
/// - requires: `canon` maps every child of `node`.
/// - ensures: the representatives of `node`'s children, left to right.
/// - provides: the children the lifting walks descend into.
/// - panics: when a child is unmapped, which the requirement excludes.
///
/// # Adequacy
/// - hypothesis: L3 — every child has a canonical representative. The lifted
///   output is checked for two nested shared legs and exact erased shape, then
///   replayed independently; ignoring canonical representatives, reordering
///   operands or collapsing duplicate edges alters those observations.
/// - witness: `machine::tests::lifting_shares_equal_trees_without_reusing_occurrence_nodes`
/// - witness: `machine::tests::the_kernel_certifies_every_spinal_catalogue_and_ladder_trace`
#[spec(
        ensures: |ret| match node {
         CoreTerm::Value(id) => core.value(id).is_some_and(|value| match *value {
          Value::Constructor {ref fields,..} => ret.iter().copied().eq(fields.iter().map(|field| canon[&CoreTerm::Value(*field)])),
          Value::Record(ref fields) => ret.iter().copied().eq(fields.values().map(|field| canon[&CoreTerm::Value(*field)])),
          Value::Univalence(..) |
          Value::Reify(_) | Value::Here(_) | Value::Funext(..) | Value::Equiv(..) | Value::Ua { .. } | Value::Returned(_) | Value::Nested(_) | Value::Run(_) | Value::SessionRelated { .. } | Value::Stay(_) | Value::Then(..) | Value::FlowProduct(..) | Value::Forward(_) | Value::FunctionFlow(..) | Value::Recorded(_) => false,
          Value::PathRefl(code) => ret.as_slice() == [canon[&CoreTerm::Value(code)]],
          Value::PathProduct(first, second) => ret.as_slice() == [canon[&CoreTerm::Value(first)], canon[&CoreTerm::Value(second)]],
          Value::PathEquiv { forward, backward, .. } => ret.as_slice() == [canon[&CoreTerm::Value(forward)], canon[&CoreTerm::Value(backward)]],
          Value::ListCons(a,b) | Value::StaticApplication(a,b) => ret.as_slice() == [canon[&CoreTerm::Value(a)],canon[&CoreTerm::Value(b)]],
          Value::Tuple(ref components) => ret.iter().copied().eq(components.iter().map(|&component| canon[&CoreTerm::Value(component)])),
          Value::ListNil | Value::Primitive { .. } | Value::Variable{..} | Value::Constant(_) | Value::Literal(_) | Value::Quote(_) | Value::QuoteComputation(_) | Value::Hole(_) => ret.is_empty(),
          Value::StaticLambda(body) | Value::Injection(_,body) | Value::Lift{body,..} | Value::Mark{body,..} => ret.as_slice() == [canon[&CoreTerm::Value(body)]],
          Value::Thunk(body) => ret.as_slice() == [canon[&CoreTerm::Computation(body)]],
          }),
         CoreTerm::Computation(id) => core.computation(id).is_some_and(|computation| match *computation {
          Computation::DataCase {scrutinee,ref branches,..} => ret.iter().copied().eq(core::iter::once(canon[&CoreTerm::Value(scrutinee)]).chain(branches.iter().map(|branch| canon[&CoreTerm::Computation(*branch)]))),
          Computation::RecordProjection(record,_) | Computation::TupleProjection(record,_) => ret.as_slice() == [canon[&CoreTerm::Value(record)]],
          Computation::Perform { .. } | Computation::Handle { .. } | Computation::Exercise { .. } | Computation::Scope { .. } | Computation::Resume(..) | Computation::Abandon(_) | Computation::Split { .. } | Computation::Reset(_) | Computation::Shift(_) | Computation::With(..) | Computation::Project(..) | Computation::PathTransport { .. } | Computation::Ride { .. } | Computation::TelescopeTransport { .. } | Computation::Session(_) | Computation::Memory(_) | Computation::World(_) => false,
          Computation::ListFold { list,on_nil,on_cons,.. } | Computation::ListCase { list,on_nil,on_cons,.. } => ret.as_slice() == [canon[&CoreTerm::Value(list)],canon[&CoreTerm::Computation(on_nil)],canon[&CoreTerm::Computation(on_cons)]],
          Computation::Primitive { arguments, .. } => ret.iter().copied().eq(arguments.iter().map(|argument| canon[&CoreTerm::Value(*argument)])),
          Computation::Transport(path, value) => ret.as_slice() == [canon[&CoreTerm::Value(path)], canon[&CoreTerm::Value(value)]],
          Computation::Lambda(body) | Computation::Mark{body,..} | Computation::Ascribe { body, .. } | Computation::Fixpoint { body, .. } => ret.as_slice() == [canon[&CoreTerm::Computation(body)]],
          Computation::Application(head,arg) => ret.as_slice() == [canon[&CoreTerm::Computation(head)],canon[&CoreTerm::Value(arg)]],
          Computation::Return(value) | Computation::Force(value) => ret.as_slice() == [canon[&CoreTerm::Value(value)]],
          Computation::Bind(bound,body) => ret.as_slice() == [canon[&CoreTerm::Computation(bound)],canon[&CoreTerm::Computation(body)]],
          Computation::Case{scrutinee,ref branches} => ret.iter().copied().eq(core::iter::once(canon[&CoreTerm::Value(scrutinee)]).chain(branches.iter().map(|&branch| canon[&CoreTerm::Computation(branch)]))),
          Computation::Hole(_) => ret.is_empty(),
         }),
        }
    )]
fn canonical_children(
    core: &CoreArena,
    canon: &BTreeMap<CoreTerm, CoreTerm>,
    node: CoreTerm,
) -> Vec<CoreTerm>
{
    core_children(core, node)
        .into_iter()
        .map(|child| canon[&child])
        .collect()
}

/// The core term `root` of `core` as an overlay: every former grafted,
/// subterms of equal tree read as one node, and each node the term
/// reaches along two or more edges shared, the shares nested at the root
/// in the order their nodes complete, the first outermost.
///
/// # Specification
/// - requires: all nodes beneath `root` resolve in `core`; the fixture contains
///   no quoted types or static operators.
/// - ensures: an overlay that validates from the returned root and erases to a
///   term equal to `root` as a tree; a node reached once is grafted where it
///   stands.
/// - provides: the spinal side of every certification test.
/// - panics: when a mint is refused, which no fixture provokes.
///
/// # Adequacy
/// - hypothesis: L3 — resolved quote-free, static-operator-free term DAGs are
///   lifted. Validation, exact sharing counts, erased constructors and kernel
///   replay distinguish reused occurrence nodes, wrong share distance or
///   position, missed structural sharing and a changed term family.
/// - witness: `machine::tests::lifting_shares_equal_trees_without_reusing_occurrence_nodes`
/// - witness: `machine::tests::the_kernel_certifies_every_spinal_catalogue_and_ladder_trace`
#[spec(
        ensures: |ret| ret.0.validate(ret.1).is_ok() && matches!((root,ret.1),
         (CoreTerm::Value(_),OverlayId::Value(_)) | (CoreTerm::Computation(_),OverlayId::Computation(_)))
    )]
fn lifted(
    core: &CoreArena,
    root: CoreTerm,
) -> (Overlay, OverlayId)
{
    let canon = canonical(core, root);
    let root = canon[&root];
    let mut edges: BTreeMap<CoreTerm, u32> = BTreeMap::new();
    let mut seen = BTreeSet::new();
    let mut completed = Vec::new();
    let mut walk = Vec::from([Lifting::Enter(root)]);
    while let Some(step) = walk.pop() {
        match step {
            Lifting::Enter(node) => {
                if !seen.insert(node) {
                    continue;
                }
                walk.push(Lifting::Exit(node));
                for child in canonical_children(core, &canon, node).into_iter().rev() {
                    let reached = edges.entry(child).or_default();
                    *reached = reached.saturating_add(1);
                    walk.push(Lifting::Enter(child));
                }
            },
            Lifting::Exit(node) => completed.push(node),
        }
    }
    let shared: Vec<CoreTerm> = completed
        .into_iter()
        .filter(|node| edges.get(node).copied().unwrap_or(0) >= 2)
        .collect();
    let index: BTreeMap<CoreTerm, Nest> = shared
        .iter()
        .enumerate()
        .map(|(share, &node)| (node, Nest(share)))
        .collect();
    let mut overlay = Overlay::new();
    let mut taken = Vec::from_iter(shared.iter().map(|_| SharePosition::from(0_u32)));
    let mut legs = Vec::new();
    for (depth, &leg) in shared.iter().enumerate() {
        legs.push(lifted_under(
            &mut overlay,
            core,
            &canon,
            leg,
            Nest(depth),
            &index,
            &mut taken,
        ));
    }
    let mut built = lifted_under(
        &mut overlay,
        core,
        &canon,
        root,
        Nest(shared.len()),
        &index,
        &mut taken,
    );
    for (share, &leg) in legs.iter().enumerate().rev() {
        let arity = ShareArity::from(u32::from(taken[share]));
        built = match built {
            OverlayId::Value(body) => OverlayId::Value(
                overlay
                    .mint_value(ValueNode::Shared(Sharing { arity, leg, body }))
                    .expect("the leg and the body resolve"),
            ),
            OverlayId::Computation(body) => OverlayId::Computation(
                overlay
                    .mint_computation(CompNode::Shared(Sharing { arity, leg, body }))
                    .expect("the leg and the body resolve"),
            ),
            OverlayId::ValueType(_) | OverlayId::CompType(_) => {
                panic!("a core term lifts to an evaluation node")
            },
        };
    }
    (overlay, built)
}

/// Graft `top` under `depth` shares, each shared node below it an
/// occurrence of its share numbered in the order occurrences are minted.
///
/// # Specification
/// - requires: every shared node `top` reaches has a share index below `depth`;
///   the resolved fixture contains no quotes or static operators.
/// - ensures: the grafted node; `taken` counts each share's occurrences minted
///   so far, left to right, which is preorder.
/// - provides: the one minting walk [`lifted`] runs per leg and for the body.
/// - panics: when a mint is refused, which no fixture provokes.
///
/// # Adequacy
/// - hypothesis: L3 — a canonical quote-free, static-operator-free term is
///   grafted beneath already indexed shares. The complete overlay must validate
///   and erase to the fixture tree; wrong distance, occurrence numbering, child
///   order or family changes validation, exact sharing or kernel certification.
/// - witness: `machine::tests::lifting_shares_equal_trees_without_reusing_occurrence_nodes`
/// - witness: `machine::tests::the_kernel_certifies_every_spinal_catalogue_and_ladder_trace`
/// - witness: `machine::tests::trace_pairing::every_pair_of_generated_ladder_traces_replays`
#[spec(
        captures: [taken_len = taken.len()],
        ensures: |ret| taken.len() == taken_len && match (top,ret) {
         (CoreTerm::Value(_),OverlayId::Value(id)) => overlay.value(id).is_some(),
         (CoreTerm::Computation(_),OverlayId::Computation(id)) => overlay.computation(id).is_some(),
         _ => false,
        }
    )]
fn lifted_under(
    overlay: &mut Overlay,
    core: &CoreArena,
    canon: &BTreeMap<CoreTerm, CoreTerm>,
    top: CoreTerm,
    depth: Nest,
    index: &BTreeMap<CoreTerm, Nest>,
    taken: &mut [SharePosition],
) -> OverlayId
{
    let mut results: Vec<OverlayId> = Vec::new();
    let mut walk = Vec::from([Lifting::Enter(top)]);
    while let Some(step) = walk.pop() {
        match step {
            Lifting::Enter(node) => {
                if node != top
                    && let Some(&Nest(share)) = index.get(&node)
                {
                    let distance = depth
                        .0
                        .checked_sub(1)
                        .and_then(|innermost| innermost.checked_sub(share))
                        .and_then(|distance| u32::try_from(distance).ok())
                        .expect("a shared node below lies in an outer share");
                    let bound = Bound {
                        distance: ShareDistance::from(distance),
                        position: taken[share],
                    };
                    taken[share] = SharePosition::from(u32::from(taken[share]).saturating_add(1));
                    results.push(match node {
                        CoreTerm::Value(_) => OverlayId::Value(
                            overlay
                                .mint_value(ValueNode::Bound(bound))
                                .expect("an occurrence names no child"),
                        ),
                        CoreTerm::Computation(_) => OverlayId::Computation(
                            overlay
                                .mint_computation(CompNode::Bound(bound))
                                .expect("an occurrence names no child"),
                        ),
                    });
                    continue;
                }
                walk.push(Lifting::Exit(node));
                for child in canonical_children(core, canon, node).into_iter().rev() {
                    walk.push(Lifting::Enter(child));
                }
            },
            Lifting::Exit(node) => {
                let count = core_children(core, node).len();
                let split = results
                    .len()
                    .checked_sub(count)
                    .expect("a node's children are on the stack");
                let children = results.split_off(split);
                let value = |at: usize| match children[at] {
                    OverlayId::Value(id) => id,
                    other @ (OverlayId::Computation(_)
                    | OverlayId::ValueType(_)
                    | OverlayId::CompType(_)) => panic!("a value child: {other:?}"),
                };
                let computation = |at: usize| match children[at] {
                    OverlayId::Computation(id) => id,
                    other @ (OverlayId::Value(_)
                    | OverlayId::ValueType(_)
                    | OverlayId::CompType(_)) => {
                        panic!("a computation child: {other:?}")
                    },
                };
                let made = match node {
                    CoreTerm::Value(id) => {
                        let graft = match *core.value(id).expect("a reached value resolves") {
                            Value::Here(_)
                            | Value::Funext(..)
                            | Value::Equiv(..)
                            | Value::Univalence(..)
                            | Value::SessionRelated { .. }
                            | Value::Stay(_)
                            | Value::Then(..)
                            | Value::FlowProduct(..)
                            | Value::Forward(_)
                            | Value::FunctionFlow(..)
                            | Value::Recorded(_)
                            | Value::Ua { .. }
                            | Value::Returned(_)
                            | Value::Nested(_)
                            | Value::Run(_)
                            | Value::Reify(_) => {
                                panic!("the pure fixture language has no reified stacks")
                            },
                            Value::Primitive { .. } => {
                                panic!("the duplication fixtures carry no native operation")
                            },
                            Value::Variable { zone, index } => ValueGraft::Variable { zone, index },
                            Value::Constant(constant) => ValueGraft::Constant(constant),
                            Value::Literal(ref literal) => ValueGraft::Literal(literal.clone()),
                            Value::Tuple(ref components) => match components.len() {
                                0 => ValueGraft::Unit,
                                2 => ValueGraft::Pair(value(0), value(1)),
                                _ => panic!("the fixture language's tuples are binary"),
                            },
                            Value::Injection(summand, _) => ValueGraft::Injection(
                                gandr_kernel_term::Side::try_from(summand)
                                    .expect("the fixture language's sums are binary"),
                                value(0),
                            ),
                            Value::Thunk(_) => ValueGraft::Thunk(computation(0)),
                            Value::Lift { ref target, .. } => ValueGraft::Lift {
                                target: target.clone(),
                                body: value(0),
                            },
                            Value::PathRefl(_)
                            | Value::Constructor { .. }
                            | Value::Record(_)
                            | Value::ListNil
                            | Value::ListCons(..)
                            | Value::PathProduct(..)
                            | Value::PathEquiv { .. }
                            | Value::Quote(_)
                            | Value::QuoteComputation(_)
                            | Value::StaticLambda(_)
                            | Value::StaticApplication(..) => {
                                panic!("the duplication fixture uses only the CBPV fragment")
                            },
                            Value::Hole(_) | Value::Mark { .. } => {
                                panic!("the duplication fixtures carry no hole or mark")
                            },
                        };
                        OverlayId::Value(
                            overlay
                                .mint_value(ValueNode::Grafted(graft))
                                .expect("the children resolve"),
                        )
                    },
                    CoreTerm::Computation(id) => {
                        let graft = match *core
                            .computation(id)
                            .expect("a reached computation resolves")
                        {
                            Computation::DataCase { .. }
                            | Computation::RecordProjection(..)
                            | Computation::TupleProjection(..) => {
                                panic!("native eliminators are outside the duplication fixture")
                            },
                            Computation::PathTransport { .. }
                            | Computation::Ride { .. }
                            | Computation::TelescopeTransport { .. }
                            | Computation::Perform { .. }
                            | Computation::Handle { .. }
                            | Computation::Exercise { .. }
                            | Computation::Scope { .. }
                            | Computation::Resume(..)
                            | Computation::Abandon(_)
                            | Computation::Split { .. }
                            | Computation::Reset(_)
                            | Computation::Shift(_)
                            | Computation::With(..)
                            | Computation::Project(..)
                            | Computation::Session(_)
                            | Computation::Memory(_)
                            | Computation::World(_) => {
                                panic!("the pure fixture language has no runtime control formers")
                            },
                            Computation::Primitive { .. } => {
                                panic!("the duplication fixtures carry no native operation")
                            },
                            Computation::Transport(..)
                            | Computation::ListFold { .. }
                            | Computation::ListCase { .. } => {
                                panic!("the duplication fixture uses only the CBPV fragment")
                            },
                            Computation::Fixpoint { .. } => {
                                panic!("the duplication fixtures carry no fixpoint")
                            },
                            Computation::Hole(_)
                            | Computation::Mark { .. }
                            | Computation::Ascribe { .. } => {
                                panic!("the duplication fixtures carry no hole, mark or ascription")
                            },
                            Computation::Lambda(_) => CompGraft::Lambda(computation(0)),
                            Computation::Application(..) => {
                                CompGraft::Application(computation(0), value(1))
                            },
                            Computation::Return(_) => CompGraft::Return(value(0)),
                            Computation::Force(_) => CompGraft::Force(value(0)),
                            Computation::Bind(..) => {
                                CompGraft::Bind(computation(0), computation(1))
                            },
                            Computation::Case { .. } => CompGraft::Case {
                                scrutinee: value(0),
                                on_left: computation(1),
                                on_right: computation(2),
                            },
                        };
                        OverlayId::Computation(
                            overlay
                                .mint_computation(CompNode::Grafted(graft))
                                .expect("the children resolve"),
                        )
                    },
                };
                results.push(made);
            },
        }
    }
    results.pop().expect("the walk leaves the top")
}

/// The kernel's copy of a world's terms and the types their codes quote,
/// each core node translated once.
#[derive(Default)]
struct Kernel
{
    /// The kernel's terms.
    arena: TermArena,
    /// The kernel node of every core value translated.
    values: BTreeMap<ValueId, gandr_kernel_term::ValueId>,
    /// The kernel node of every core computation translated.
    computations: BTreeMap<ComputationId, gandr_kernel_term::ComputationId>,
    /// The kernel node of every core value type translated.
    value_types: BTreeMap<ValueTypeId, gandr_kernel_term::ValueTypeId>,
    /// The kernel node of every core computation type translated.
    comp_types: BTreeMap<CompTypeId, gandr_kernel_term::CompTypeId>,
}

/// A core node awaiting translation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Node
{
    /// A value.
    Value(ValueId),
    /// A computation.
    Computation(ComputationId),
    /// A value type.
    ValueType(ValueTypeId),
    /// A computation type.
    CompType(CompTypeId),
}

/// Whether a core node has its kernel copy yet.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Translated
{
    /// The copy exists.
    Made,
    /// The copy is still to be minted.
    Missing,
}

impl Kernel
{
    /// The kernel copy of the core value `value`.
    ///
    /// # Specification
    /// - requires: as [`Kernel::translate`].
    /// - ensures: the kernel node `value` translates to.
    /// - provides: a side's or a body's translation.
    /// - panics: as [`Kernel::translate`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a resolved supported value belongs to the run’s
    ///   source arena. Independent replay of positive and negative comparisons,
    ///   including quoted codes, observes preserved constructors and constants;
    ///   a wrong cache entry, wrong node family or swapped operand changes
    ///   certification.
    /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
    /// - witness: `machine::tests::the_kernel_certifies_every_spinal_catalogue_and_ladder_trace`
    /// - witness: `machine::tests::a_trace_naming_the_wrong_branch_is_refused`
    /// - witness: `machine::tests::closed_codes_are_certified_in_both_type_families`
    #[spec(
            ensures: |ret| self.values.get(&value) == Some(&ret) && self.arena.value(ret).is_some()
        )]
    fn value(
        &mut self,
        core: &CoreArena,
        value: ValueId,
    ) -> gandr_kernel_term::ValueId
    {
        self.translate(core, Node::Value(value));
        *self.values.get(&value).expect("the value was translated")
    }

    /// The kernel copy of the core computation `computation`.
    ///
    /// # Specification
    /// - requires: as [`Kernel::translate`].
    /// - ensures: the kernel node `computation` translates to.
    /// - provides: a side's translation.
    /// - panics: as [`Kernel::translate`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a resolved supported computation belongs to the run’s
    ///   source arena. Kernel replay of lambdas, applications and forcing
    ///   distinguishes a wrong copy, changed binder structure or misplaced
    ///   value/computation child.
    /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
    /// - witness: `machine::tests::the_kernel_certifies_every_spinal_catalogue_and_ladder_trace`
    /// - witness: `machine::tests::a_trace_naming_the_wrong_branch_is_refused`
    /// - witness: `machine::tests::closed_codes_are_certified_in_both_type_families`
    #[spec(
            ensures: |ret| self.computations.get(&computation) == Some(&ret) && self.arena.computation(ret).is_some()
        )]
    fn computation(
        &mut self,
        core: &CoreArena,
        computation: ComputationId,
    ) -> gandr_kernel_term::ComputationId
    {
        self.translate(core, Node::Computation(computation));
        *self
            .computations
            .get(&computation)
            .expect("the computation was translated")
    }

    /// Translate `root` and everything beneath it, children first.
    ///
    /// # Specification
    /// - requires: `core` is this translator's source arena; every reached node
    ///   resolves, variables are intuitionistic, and no static lambda or
    ///   parameterized universe sort occurs.
    /// - ensures: `root` and every node beneath it have a kernel copy of the
    ///   same shape, constants at the same positions.
    /// - provides: the one translation the replay tests share.
    /// - panics: on a dangling or unsupported node or a linear variable,
    ///   excluded by the requirements.
    ///
    /// # Termination
    /// - reason: the `while let Some(&node) = stack.last()` loop over an
    ///   explicit stack, not recursion.
    /// - measure: the reachable nodes without a copy, then the stack's length:
    ///   a node is pushed only while it has no copy, beneath a parent minted
    ///   after it, and popped once it has one.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one source arena supplies finite intuitionistic
    ///   term/type DAGs without static lambdas or parameterized universe sorts.
    ///   Kernel agreement on ordinary terms and quoted codes observes
    ///   children-first translation, retained sharing and constant positions;
    ///   wrong-family caches or dropped descendants alter replay.
    /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
    /// - witness: `machine::tests::the_kernel_certifies_every_spinal_catalogue_and_ladder_trace`
    /// - witness: `machine::tests::a_trace_naming_the_wrong_branch_is_refused`
    /// - witness: `machine::tests::closed_codes_are_certified_in_both_type_families`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "test fixture: the replay tests translate catalogue terms of a few dozen nodes, and the check re-reads every cached copy once per translation"
        )
    )]
    #[spec(
            captures: [counts = [self.values.len(),self.computations.len(),self.value_types.len(),self.comp_types.len()]],
            ensures: |ret| self.translated(root) == Translated::Made
             && [self.values.len(),self.computations.len(),self.value_types.len(),self.comp_types.len()].into_iter().zip(counts).all(|(after,before)| after >= before)
             && self.values.values().all(|&id| self.arena.value(id).is_some())
             && self.computations.values().all(|&id| self.arena.computation(id).is_some())
             && self.value_types.values().all(|&id| self.arena.value_type(id).is_some())
             && self.comp_types.values().all(|&id| self.arena.comp_type(id).is_some())
        )]
    fn translate(
        &mut self,
        core: &CoreArena,
        root: Node,
    )
    {
        let mut stack = Vec::from([root]);
        while let Some(&node) = stack.last() {
            let pending: Vec<Node> = self
                .children(core, node)
                .into_iter()
                .filter(|&child| self.translated(child) == Translated::Missing)
                .collect();
            if pending.is_empty() {
                stack.pop();
                self.build(core, node);
            }
            else {
                stack.extend(pending);
            }
        }
    }

    /// Whether `node` has a kernel copy.
    ///
    /// # Specification
    /// - requires: nothing; a node need not have a copy yet.
    /// - ensures: Made exactly when the node's own family map contains its id.
    /// - provides: the completed-node boundary of the postorder translation.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — translation may encounter a new node, a completed
    ///   node or an already translated shared child in each supported family.
    ///   Kernel certification and shared-ladder comparisons observe premature
    ///   completion, wrong-family membership and discarded cached copies.
    /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
    /// - witness: `machine::tests::the_kernel_certifies_every_spinal_catalogue_and_ladder_trace`
    /// - witness: `machine::tests::a_trace_naming_the_wrong_branch_is_refused`
    /// - witness: `machine::tests::closed_codes_are_certified_in_both_type_families`
    #[spec(
            ensures: |ret| (ret == Translated::Made) == match node {
             Node::Value(id) => self.values.contains_key(&id), Node::Computation(id) => self.computations.contains_key(&id),
             Node::ValueType(id) => self.value_types.contains_key(&id), Node::CompType(id) => self.comp_types.contains_key(&id),
            }
        )]
    fn translated(
        &self,
        node: Node,
    ) -> Translated
    {
        let made = match node {
            Node::Value(value) => self.values.contains_key(&value),
            Node::Computation(computation) => self.computations.contains_key(&computation),
            Node::ValueType(value_type) => self.value_types.contains_key(&value_type),
            Node::CompType(comp_type) => self.comp_types.contains_key(&comp_type),
        };
        if made {
            Translated::Made
        }
        else {
            Translated::Missing
        }
    }

    /// The nodes `node` is built from.
    ///
    /// # Specification
    /// - requires: an untranslated node resolves in the pure fixture language.
    /// - ensures: no children for a completed copy; otherwise the source node's
    ///   immediate children in constructor order, including quoted types.
    /// - provides: the edges followed by the postorder translator.
    /// - panics: when a source node is unresolved or outside that language.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an untranslated resolved node contributes its ordered
    ///   children, while a cached node contributes none. Kernel replay spans
    ///   value, computation and quoted-type edges; wrong arity, operand order
    ///   or family changes certification, and repeated ladder subterms exercise
    ///   the completed-node boundary.
    /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
    /// - witness: `machine::tests::the_kernel_certifies_every_spinal_catalogue_and_ladder_trace`
    /// - witness: `machine::tests::a_trace_naming_the_wrong_branch_is_refused`
    /// - witness: `machine::tests::closed_codes_are_certified_in_both_type_families`
    #[spec(
            ensures: |ret| if self.translated(node) == Translated::Made { ret.is_empty() } else { match node {
             Node::Value(id) => core.value(id).is_some_and(|value| match *value {
              Value::Constructor {datatype,ref fields,..} => ret.iter().copied().eq(core::iter::once(Node::ValueType(datatype)).chain(fields.iter().copied().map(Node::Value))),
              Value::Record(ref fields) => ret.iter().copied().eq(fields.values().copied().map(Node::Value)),
          Value::Univalence(..) |
          Value::Reify(_) | Value::Here(_) | Value::Funext(..) | Value::Equiv(..) | Value::Ua { .. } | Value::SessionRelated { .. } | Value::Stay(_) | Value::Then(..) | Value::FlowProduct(..) | Value::Forward(_) | Value::FunctionFlow(..) | Value::Recorded(_) => false,
              Value::PathRefl(code) => ret.as_slice() == [Node::Value(code)],
              Value::PathProduct(first, second) => ret.as_slice() == [Node::Value(first), Node::Value(second)],
              Value::PathEquiv { path_type, forward, backward, .. } => ret.as_slice() == [Node::ValueType(path_type), Node::Value(forward), Node::Value(backward)],
              Value::ListCons(a,b) | Value::StaticApplication(a,b) => ret.as_slice() == [Node::Value(a),Node::Value(b)],
              Value::Tuple(ref components) => ret.iter().copied().eq(components.iter().copied().map(Node::Value)),
              Value::ListNil | Value::Primitive { .. } | Value::Variable{..} | Value::Constant(_) | Value::Literal(_) | Value::Hole(_) => ret.is_empty(),
              Value::StaticLambda(body) | Value::Injection(_,body) | Value::Lift{body,..} | Value::Mark{body,..} => ret.as_slice() == [Node::Value(body)],
              Value::Thunk(body) | Value::Returned(body) | Value::Nested(body) | Value::Run(body) => ret.as_slice() == [Node::Computation(body)],
             Value::Quote(id) => ret.as_slice() == [Node::ValueType(id)],
             Value::QuoteComputation(id) => ret.as_slice() == [Node::CompType(id)],
              }),
             Node::Computation(id) => core.computation(id).is_some_and(|computation| match *computation {
              Computation::DataCase {scrutinee,motive,ref branches} => ret.iter().copied().eq([Node::Value(scrutinee),Node::CompType(motive)].into_iter().chain(branches.iter().copied().map(Node::Computation))),
              Computation::RecordProjection(record,_) | Computation::TupleProjection(record,_) => ret.as_slice() == [Node::Value(record)],
          Computation::Perform { .. } | Computation::Handle { .. } | Computation::Exercise { .. } | Computation::Scope { .. } | Computation::Resume(..) | Computation::Abandon(_) | Computation::Split { .. } | Computation::Reset(_) | Computation::Shift(_) | Computation::With(..) | Computation::Project(..) | Computation::Ride { .. } | Computation::TelescopeTransport { .. } | Computation::Session(_) | Computation::Memory(_) | Computation::World(_) => false,
              Computation::PathTransport { motive, path, value } => ret.as_slice() == [Node::ValueType(motive), Node::Value(path), Node::Value(value)],
              Computation::ListFold { element,result,list,on_nil,on_cons } => ret.as_slice() == [Node::ValueType(element),Node::ValueType(result),Node::Value(list),Node::Computation(on_nil),Node::Computation(on_cons)],
              Computation::ListCase { list,on_nil,on_cons } => ret.as_slice() == [Node::Value(list),Node::Computation(on_nil),Node::Computation(on_cons)],
              Computation::Primitive { arguments, .. } => ret.iter().copied().eq(arguments.iter().copied().map(Node::Value)),
              Computation::Transport(path, value) => ret.as_slice() == [Node::Value(path), Node::Value(value)],
              Computation::Lambda(body) | Computation::Mark{body,..} | Computation::Fixpoint { body, .. } => ret.as_slice() == [Node::Computation(body)],
              Computation::Ascribe { body, ty } => ret.as_slice() == [Node::Computation(body), Node::CompType(ty)],
              Computation::Application(head,arg) => ret.as_slice() == [Node::Computation(head),Node::Value(arg)],
              Computation::Return(value) | Computation::Force(value) => ret.as_slice() == [Node::Value(value)],
              Computation::Bind(bound,body) => ret.as_slice() == [Node::Computation(bound),Node::Computation(body)],
              Computation::Case{scrutinee,ref branches} => ret.iter().copied().eq(core::iter::once(Node::Value(scrutinee)).chain(branches.iter().copied().map(Node::Computation))),
              Computation::Hole(_) => ret.is_empty(),
             }),
             Node::ValueType(id) => core.value_type(id).is_some_and(|value_type| match *value_type {
              ValueType::Data {ref arguments,..} => ret.iter().copied().eq(arguments.iter().copied().map(Node::Value)),
              ValueType::Record(ref fields) => ret.iter().copied().eq(fields.values().copied().map(Node::ValueType)),
              ValueType::Stack { .. } | ValueType::Capability { .. } | ValueType::Buffer | ValueType::Session(_) | ValueType::Flow { .. } | ValueType::Run(_) | ValueType::Staged { .. } | ValueType::Kept { .. } | ValueType::World(_) => false,
              ValueType::Path { carrier, left, right } => ret.as_slice() == [Node::ValueType(carrier), Node::Value(left), Node::Value(right)],
              ValueType::PathUniverse(source, target) => ret.as_slice() == [Node::Value(source), Node::Value(target)],
              ValueType::Product(ref parts) | ValueType::Sum(ref parts) => ret.iter().copied().eq(parts.iter().copied().map(Node::ValueType)),
              ValueType::StaticPi{domain:a,codomain:b} | ValueType::Sigma{first:a,second:b} => ret.as_slice() == [Node::ValueType(a),Node::ValueType(b)],
              ValueType::Thunk(body) => ret.as_slice() == [Node::CompType(body)],
              ValueType::List(inner) | ValueType::Lift{inner,..} => ret.as_slice() == [Node::ValueType(inner)],
              ValueType::Element{code,..} => ret.as_slice() == [Node::Value(code)],
              ValueType::Base(_) | ValueType::Universe{..} | ValueType::Abstract(_) | ValueType::Unknown => ret.is_empty(),
             }),
             Node::CompType(id) => core.comp_type(id).is_some_and(|comp_type| match *comp_type {
              CompType::With(..) | CompType::Codata { .. } => false,
              CompType::Returner { result, ref effects } => effects.purity() == gandr_core_term::effect::Purity::Pure && ret.as_slice() == [Node::ValueType(result)],
              CompType::Arrow{domain,codomain} | CompType::Pi{domain,codomain} => ret.as_slice() == [Node::ValueType(domain),Node::CompType(codomain)],
              CompType::Element{code,..} => ret.as_slice() == [Node::Value(code)],
              CompType::Unknown => ret.is_empty(),
             }),
            } }
        )]
    fn children(
        &self,
        core: &CoreArena,
        node: Node,
    ) -> Vec<Node>
    {
        if self.translated(node) == Translated::Made {
            return Vec::new();
        }
        match node {
            Node::Value(value) => match *(core.value(value).expect("a fixture value resolves")) {
                Value::Constructor {
                    ref datatype,
                    ref fields,
                    ..
                } => core::iter::once(Node::ValueType(*datatype))
                    .chain(fields.iter().copied().map(Node::Value))
                    .collect(),
                Value::Record(ref fields) => fields.values().copied().map(Node::Value).collect(),
                Value::Here(_)
                | Value::Funext(..)
                | Value::Equiv(..)
                | Value::Univalence(..)
                | Value::SessionRelated { .. }
                | Value::Stay(_)
                | Value::Then(..)
                | Value::FlowProduct(..)
                | Value::Forward(_)
                | Value::FunctionFlow(..)
                | Value::Recorded(_)
                | Value::Ua { .. }
                | Value::Reify(_) => {
                    panic!("the pure fixture language has no reified stacks")
                },
                Value::PathRefl(code) => Vec::from([Node::Value(code)]),
                Value::PathEquiv {
                    path_type,
                    forward,
                    backward,
                    ..
                } => Vec::from([
                    Node::ValueType(path_type),
                    Node::Value(forward),
                    Node::Value(backward),
                ]),
                Value::PathProduct(first, second)
                | Value::ListCons(first, second)
                | Value::StaticApplication(first, second) => {
                    Vec::from([Node::Value(first), Node::Value(second)])
                },
                Value::Tuple(ref components) => {
                    components.iter().copied().map(Node::Value).collect()
                },
                Value::StaticLambda(body)
                | Value::Injection(_, body)
                | Value::Lift { body, .. }
                | Value::Mark { body, .. } => Vec::from([Node::Value(body)]),
                Value::Thunk(body)
                | Value::Returned(body)
                | Value::Nested(body)
                | Value::Run(body) => Vec::from([Node::Computation(body)]),
                Value::Quote(quoted) => Vec::from([Node::ValueType(quoted)]),
                Value::QuoteComputation(quoted) => Vec::from([Node::CompType(quoted)]),
                Value::Primitive { .. }
                | Value::Variable { .. }
                | Value::Constant(_)
                | Value::ListNil
                | Value::Literal(_)
                | Value::Hole(_) => Vec::new(),
            },
            Node::Computation(computation) => {
                match *(core
                    .computation(computation)
                    .expect("a fixture computation resolves"))
                {
                    Computation::DataCase {
                        ref scrutinee,
                        ref motive,
                        ref branches,
                    } => [Node::Value(*scrutinee), Node::CompType(*motive)]
                        .into_iter()
                        .chain(branches.iter().copied().map(Node::Computation))
                        .collect(),
                    Computation::RecordProjection(ref record, _)
                    | Computation::TupleProjection(ref record, _) => {
                        Vec::from([Node::Value(*record)])
                    },
                    Computation::PathTransport {
                        motive,
                        path,
                        value,
                    } => Vec::from([
                        Node::ValueType(motive),
                        Node::Value(path),
                        Node::Value(value),
                    ]),
                    Computation::Ride { .. }
                    | Computation::TelescopeTransport { .. }
                    | Computation::Perform { .. }
                    | Computation::Handle { .. }
                    | Computation::Exercise { .. }
                    | Computation::Scope { .. }
                    | Computation::Resume(..)
                    | Computation::Abandon(_)
                    | Computation::Split { .. }
                    | Computation::Reset(_)
                    | Computation::Shift(_)
                    | Computation::With(..)
                    | Computation::Project(..)
                    | Computation::Session(_)
                    | Computation::Memory(_)
                    | Computation::World(_) => {
                        panic!("the pure fixture language has no runtime control formers")
                    },
                    Computation::ListFold {
                        element,
                        result,
                        list,
                        on_nil,
                        on_cons,
                    } => Vec::from([
                        Node::ValueType(element),
                        Node::ValueType(result),
                        Node::Value(list),
                        Node::Computation(on_nil),
                        Node::Computation(on_cons),
                    ]),
                    Computation::ListCase {
                        list,
                        on_nil,
                        on_cons,
                    } => Vec::from([
                        Node::Value(list),
                        Node::Computation(on_nil),
                        Node::Computation(on_cons),
                    ]),
                    Computation::Primitive { ref arguments, .. } => {
                        arguments.iter().copied().map(Node::Value).collect()
                    },
                    Computation::Transport(path, value) => {
                        Vec::from([Node::Value(path), Node::Value(value)])
                    },
                    Computation::Lambda(body)
                    | Computation::Mark { body, .. }
                    | Computation::Fixpoint { body, .. } => Vec::from([Node::Computation(body)]),
                    Computation::Hole(_) => Vec::new(),
                    Computation::Application(head, argument) => {
                        Vec::from([Node::Computation(head), Node::Value(argument)])
                    },
                    Computation::Return(value) | Computation::Force(value) => {
                        Vec::from([Node::Value(value)])
                    },
                    Computation::Bind(bound, body) => {
                        Vec::from([Node::Computation(bound), Node::Computation(body)])
                    },
                    Computation::Ascribe { body, ty } => {
                        Vec::from([Node::Computation(body), Node::CompType(ty)])
                    },
                    Computation::Case {
                        scrutinee,
                        ref branches,
                    } => core::iter::once(Node::Value(scrutinee))
                        .chain(branches.iter().copied().map(Node::Computation))
                        .collect(),
                }
            },
            Node::ValueType(value_type) => {
                match *core
                    .value_type(value_type)
                    .expect("a fixture type resolves")
                {
                    ValueType::Data { ref arguments, .. } => {
                        arguments.iter().copied().map(Node::Value).collect()
                    },
                    ValueType::Record(ref fields) => {
                        fields.values().copied().map(Node::ValueType).collect()
                    },
                    ValueType::Stack { .. } => panic!("the kernel has no stack type"),
                    ValueType::Session(_) => panic!("the kernel has no session type"),
                    ValueType::World(_) => panic!("the kernel has no world type"),
                    ValueType::Capability { .. } => {
                        panic!("the kernel has no capability type")
                    },
                    ValueType::Buffer => panic!("the kernel has no buffer type"),
                    ValueType::Flow { .. } | ValueType::Run(_) => {
                        panic!("the pure fixture language has no directed identity")
                    },
                    ValueType::Staged { .. } => panic!("a fixture term names no stage"),
                    ValueType::Kept { .. } => panic!("the kernel has no kept type"),
                    ValueType::Path {
                        carrier,
                        left,
                        right,
                    } => Vec::from([
                        Node::ValueType(carrier),
                        Node::Value(left),
                        Node::Value(right),
                    ]),
                    ValueType::PathUniverse(source, target) => {
                        Vec::from([Node::Value(source), Node::Value(target)])
                    },
                    ValueType::Product(ref parts) | ValueType::Sum(ref parts) => {
                        parts.iter().copied().map(Node::ValueType).collect()
                    },
                    ValueType::StaticPi {
                        domain: first,
                        codomain: second,
                    }
                    | ValueType::Sigma { first, second } => {
                        Vec::from([Node::ValueType(first), Node::ValueType(second)])
                    },
                    ValueType::Thunk(body) => Vec::from([Node::CompType(body)]),
                    ValueType::List(inner) | ValueType::Lift { inner, .. } => {
                        Vec::from([Node::ValueType(inner)])
                    },
                    ValueType::Element { code, .. } => Vec::from([Node::Value(code)]),
                    ValueType::Base(_)
                    | ValueType::Universe { .. }
                    | ValueType::Abstract(_)
                    | ValueType::Unknown => Vec::new(),
                }
            },
            Node::CompType(comp_type) => {
                match *core.comp_type(comp_type).expect("a fixture type resolves") {
                    CompType::With(..) => panic!("the kernel has no lazy computation pair"),
                    CompType::Codata { .. } => panic!("kernel replay fixtures hold no codata"),
                    CompType::Returner {
                        result,
                        ref effects,
                    } => {
                        assert_eq!(
                            effects.purity(),
                            gandr_core_term::effect::Purity::Pure,
                            "kernel replay fixtures are pure"
                        );
                        Vec::from([Node::ValueType(result)])
                    },
                    CompType::Arrow { domain, codomain } | CompType::Pi { domain, codomain } => {
                        Vec::from([Node::ValueType(domain), Node::CompType(codomain)])
                    },
                    CompType::Element { code, .. } => Vec::from([Node::Value(code)]),
                    CompType::Unknown => Vec::new(),
                }
            },
        }
    }

    /// Mint the kernel copy of `node`, whose children have theirs.
    ///
    /// # Specification
    /// - requires: the source and all descendants satisfy `Kernel::translate`'s
    ///   requirements; every immediate child already has its kernel copy.
    /// - ensures: the node has a same-shape kernel copy; an existing copy
    ///   remains unchanged, otherwise only this node's family gains an entry.
    /// - provides: the constructor-preserving step of the translation.
    /// - panics: on an unresolved or unsupported node, or an untranslated
    ///   child.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — supported source nodes have translated children, or
    ///   already have their own copy. Independent kernel certification checks
    ///   preserved constructor, constants, binders and quoted types;
    ///   overwriting another family, changing a child or rebuilding shared
    ///   copies changes the checked translation.
    /// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
    /// - witness: `machine::tests::the_kernel_certifies_every_spinal_catalogue_and_ladder_trace`
    /// - witness: `machine::tests::a_trace_naming_the_wrong_branch_is_refused`
    /// - witness: `machine::tests::closed_codes_are_certified_in_both_type_families`
    #[spec(
            captures: [counts = [self.values.len(),self.computations.len(),self.value_types.len(),self.comp_types.len()]],
            ensures: |ret| self.translated(node) == Translated::Made && {
             let after = [self.values.len(),self.computations.len(),self.value_types.len(),self.comp_types.len()];
             let family = match node { Node::Value(_) => 0, Node::Computation(_) => 1, Node::ValueType(_) => 2, Node::CompType(_) => 3 };
             after.into_iter().zip(counts).enumerate().all(|(at,(after,before))| if at == family { after == before || before.checked_add(1) == Some(after) } else { after == before })
            }
        )]
    fn build(
        &mut self,
        core: &CoreArena,
        node: Node,
    )
    {
        if self.translated(node) == Translated::Made {
            return;
        }
        let value =
            |kernel: &Self, value: ValueId| *kernel.values.get(&value).expect("children first");
        let computation = |kernel: &Self, computation: ComputationId| {
            *kernel
                .computations
                .get(&computation)
                .expect("children first")
        };
        match node {
            Node::Value(id) => {
                let copy = match *(core.value(id).expect("a fixture value resolves")) {
                    Value::Constructor {
                        ref datatype,
                        ref tag,
                        ref fields,
                    } => {
                        let datatype = self.value_types[datatype];
                        let fields = fields.iter().map(|field| value(self, *field)).collect();
                        self.arena.value_constructor(datatype, *tag, fields)
                    },
                    Value::Record(ref fields) => {
                        let fields = fields
                            .iter()
                            .map(|(label, field)| (label.clone(), value(self, *field)))
                            .collect();
                        self.arena.value_record(fields)
                    },
                    Value::Here(_)
                    | Value::Funext(..)
                    | Value::Equiv(..)
                    | Value::Univalence(..)
                    | Value::SessionRelated { .. }
                    | Value::Stay(_)
                    | Value::Then(..)
                    | Value::FlowProduct(..)
                    | Value::Forward(_)
                    | Value::FunctionFlow(..)
                    | Value::Recorded(_)
                    | Value::Ua { .. }
                    | Value::Nested(_)
                    | Value::Run(_)
                    | Value::Reify(_) => {
                        panic!("the pure fixture language has no reified stacks")
                    },
                    Value::Returned(body) => {
                        let body = computation(self, body);
                        self.arena.value_returned(body)
                    },
                    Value::Primitive { .. } => panic!("the kernel has no native operation"),
                    Value::Variable {
                        zone: Zone::Intuitionistic,
                        index,
                    } => self.arena.value_variable(index),
                    Value::Variable {
                        zone: Zone::Linear, ..
                    } => {
                        panic!("the kernel's terms have no linear zone")
                    },
                    Value::Constant(constant) => self.arena.value_constant(constant),
                    Value::ListNil => self.arena.value_list_nil(),
                    Value::ListCons(first, second) => {
                        let (first, second) = (value(self, first), value(self, second));
                        self.arena.value_list_cons(first, second)
                    },
                    Value::Literal(ref literal) => self.arena.value_literal(literal.clone()),
                    Value::PathRefl(code) => {
                        let code = value(self, code);
                        self.arena.value_path_refl(code)
                    },
                    Value::PathProduct(first, second) => {
                        let (first, second) = (value(self, first), value(self, second));
                        self.arena.value_path_product(first, second)
                    },
                    Value::PathEquiv {
                        path_type,
                        forward,
                        backward,
                        ref evidence,
                    } => {
                        let path_type = *self.value_types.get(&path_type).expect("children first");
                        let (forward, backward) = (value(self, forward), value(self, backward));
                        self.arena.value_path_equiv(
                            path_type,
                            forward,
                            backward,
                            alloc::sync::Arc::clone(evidence),
                        )
                    },
                    Value::Tuple(ref components) => {
                        let components: Vec<_> = components
                            .iter()
                            .map(|&component| value(self, component))
                            .collect();
                        self.arena.value_tuple(&components)
                    },
                    Value::Injection(summand, body) => {
                        let body = value(self, body);
                        self.arena.value_injection(summand, body)
                    },
                    Value::Thunk(body) => {
                        let body = computation(self, body);
                        self.arena.value_thunk(body)
                    },
                    Value::Quote(quoted) => {
                        let quoted = *self.value_types.get(&quoted).expect("children first");
                        self.arena.value_quote(quoted)
                    },
                    Value::QuoteComputation(quoted) => {
                        let quoted = *self.comp_types.get(&quoted).expect("children first");
                        self.arena.value_quote_computation(quoted)
                    },
                    Value::Lift { ref target, body } => {
                        let body = value(self, body);
                        self.arena.value_lift(target.clone(), body)
                    },
                    Value::StaticApplication(head, argument) => {
                        let (head, argument) = (value(self, head), value(self, argument));
                        self.arena.value_static_application(head, argument)
                    },
                    Value::StaticLambda(_) => {
                        panic!("the kernel has no static lambda: a replay fixture lifts it")
                    },
                    Value::Hole(_) | Value::Mark { .. } => {
                        panic!("the kernel admits no hole or mark: a replay fixture has none")
                    },
                };
                self.values.insert(id, copy);
            },
            Node::Computation(id) => {
                let copy = match *core
                    .computation(id)
                    .expect("a fixture computation resolves")
                {
                    Computation::DataCase {
                        scrutinee,
                        motive,
                        ref branches,
                    } => {
                        let scrutinee = value(self, scrutinee);
                        let motive = self.comp_types[&motive];
                        let branches = branches
                            .iter()
                            .map(|branch| computation(self, *branch))
                            .collect();
                        self.arena
                            .computation_data_case(scrutinee, motive, branches)
                    },
                    Computation::RecordProjection(record, ref label) => {
                        let record = value(self, record);
                        self.arena
                            .computation_record_projection(record, label.clone())
                    },
                    Computation::TupleProjection(tuple, component) => {
                        let tuple = value(self, tuple);
                        self.arena.computation_tuple_projection(tuple, component)
                    },
                    Computation::PathTransport {
                        motive,
                        path,
                        value: transported,
                    } => {
                        let motive = *self.value_types.get(&motive).expect("children first");
                        let (path, transported) = (value(self, path), value(self, transported));
                        self.arena
                            .computation_path_transport(motive, path, transported)
                    },
                    Computation::Ride { .. }
                    | Computation::TelescopeTransport { .. }
                    | Computation::Perform { .. }
                    | Computation::Handle { .. }
                    | Computation::Exercise { .. }
                    | Computation::Scope { .. }
                    | Computation::Resume(..)
                    | Computation::Abandon(_)
                    | Computation::Split { .. }
                    | Computation::Reset(_)
                    | Computation::Shift(_)
                    | Computation::With(..)
                    | Computation::Project(..) => {
                        panic!("the pure fixture language has no runtime control formers")
                    },
                    Computation::ListFold {
                        element,
                        result,
                        list,
                        on_nil,
                        on_cons,
                    } => {
                        let element = *self.value_types.get(&element).expect("children first");
                        let result = *self.value_types.get(&result).expect("children first");
                        let (list, on_nil, on_cons) = (
                            value(self, list),
                            computation(self, on_nil),
                            computation(self, on_cons),
                        );
                        self.arena
                            .computation_list_fold(element, result, list, on_nil, on_cons)
                    },
                    Computation::ListCase {
                        list,
                        on_nil,
                        on_cons,
                    } => {
                        let (list, on_nil, on_cons) = (
                            value(self, list),
                            computation(self, on_nil),
                            computation(self, on_cons),
                        );
                        self.arena.computation_list_case(list, on_nil, on_cons)
                    },
                    Computation::Primitive { .. } => {
                        panic!("the kernel has no native operation")
                    },
                    Computation::Transport(path, argument) => {
                        let (path, argument) = (value(self, path), value(self, argument));
                        self.arena.computation_transport(path, argument)
                    },
                    Computation::Lambda(body) => {
                        let body = computation(self, body);
                        self.arena.computation_lambda(body)
                    },
                    Computation::Fixpoint { body, evidence } => {
                        let body = computation(self, body);
                        self.arena.computation_fixpoint(body, evidence)
                    },
                    Computation::Application(head, argument) => {
                        let (head, argument) = (computation(self, head), value(self, argument));
                        self.arena.computation_application(head, argument)
                    },
                    Computation::Return(returned) => {
                        let returned = value(self, returned);
                        self.arena.computation_return(returned)
                    },
                    Computation::Bind(bound, body) => {
                        let (bound, body) = (computation(self, bound), computation(self, body));
                        self.arena.computation_bind(bound, body)
                    },
                    Computation::Force(forced) => {
                        let forced = value(self, forced);
                        self.arena.computation_force(forced)
                    },
                    Computation::Case {
                        scrutinee,
                        ref branches,
                    } => {
                        let scrutinee = value(self, scrutinee);
                        let branches: Vec<_> = branches
                            .iter()
                            .map(|&branch| computation(self, branch))
                            .collect();
                        self.arena.computation_case(scrutinee, &branches)
                    },
                    Computation::Hole(_) | Computation::Mark { .. } => {
                        panic!("the kernel admits no hole or mark: a replay fixture has none")
                    },
                    Computation::Ascribe { .. } => {
                        panic!("an ascription crosses the bridge, never a replay fixture")
                    },
                    Computation::Session(_) => {
                        panic!("the kernel has no session action: a replay fixture has none")
                    },
                    Computation::Memory(_) => {
                        panic!("the kernel has no memory form: a replay fixture has none")
                    },
                    Computation::World(_) => {
                        panic!("the kernel has no world form: a replay fixture has none")
                    },
                };
                self.computations.insert(id, copy);
            },
            Node::ValueType(id) => {
                let value_type = |kernel: &Self, id: ValueTypeId| {
                    *kernel.value_types.get(&id).expect("children first")
                };
                let comp_type = |kernel: &Self, id: CompTypeId| {
                    *kernel.comp_types.get(&id).expect("children first")
                };
                let copy = match *core.value_type(id).expect("a fixture type resolves") {
                    ValueType::Data {
                        declaration,
                        ref arguments,
                    } => {
                        let arguments = arguments
                            .iter()
                            .map(|argument| value(self, *argument))
                            .collect();
                        self.arena.value_type_data(declaration, arguments)
                    },
                    ValueType::Record(ref fields) => {
                        let fields = fields
                            .iter()
                            .map(|(label, field)| (label.clone(), value_type(self, *field)))
                            .collect();
                        self.arena.value_type_record(fields)
                    },
                    ValueType::Stack { .. } => panic!("the kernel has no stack type"),
                    ValueType::Session(_) => panic!("the kernel has no session type"),
                    ValueType::World(_) => panic!("the kernel has no world type"),
                    ValueType::Capability { .. } => {
                        panic!("the kernel has no capability type")
                    },
                    ValueType::Buffer => panic!("the kernel has no buffer type"),
                    ValueType::Flow { .. } | ValueType::Run(_) => {
                        panic!("the pure fixture language has no directed identity")
                    },
                    ValueType::Staged { .. } => panic!("a fixture term names no stage"),
                    ValueType::Kept { .. } => panic!("the kernel has no kept type"),
                    ValueType::Path {
                        carrier,
                        left,
                        right,
                    } => {
                        let carrier = value_type(self, carrier);
                        let (left, right) = (value(self, left), value(self, right));
                        self.arena.value_type_path(carrier, left, right)
                    },
                    ValueType::PathUniverse(source, target) => {
                        let (source, target) = (value(self, source), value(self, target));
                        self.arena.value_type_path_universe(source, target)
                    },
                    ValueType::Base(base) => self.arena.value_type_base(base),
                    ValueType::List(inner) => {
                        let inner = value_type(self, inner);
                        self.arena.value_type_list(inner)
                    },
                    ValueType::Product(ref components) => {
                        let components: Vec<_> = components
                            .iter()
                            .map(|&component| value_type(self, component))
                            .collect();
                        self.arena.value_type_product(&components)
                    },
                    ValueType::Sigma { first, second } => {
                        let (first, second) = (value_type(self, first), value_type(self, second));
                        self.arena.value_type_sigma(first, second)
                    },
                    ValueType::Sum(ref summands) => {
                        let summands: Vec<_> = summands
                            .iter()
                            .map(|&summand| value_type(self, summand))
                            .collect();
                        self.arena.value_type_sum(&summands)
                    },
                    ValueType::Thunk(body) => {
                        let body = comp_type(self, body);
                        self.arena.value_type_thunk(body)
                    },
                    ValueType::Universe {
                        sort: Sort::Ground(sort),
                        ref level,
                    } => self.arena.value_type_universe(sort, level.clone()),
                    ValueType::Universe {
                        sort: Sort::Parameter(_),
                        ..
                    } => panic!("no fixture quotes a sort-polymorphic universe"),
                    ValueType::Lift { inner, ref target } => {
                        let inner = value_type(self, inner);
                        self.arena.value_type_lift(inner, target.clone())
                    },
                    ValueType::Element { code, ref target } => {
                        let code = value(self, code);
                        self.arena.value_type_element(code, target.clone())
                    },
                    ValueType::Abstract(atom) => self.arena.value_type_abstract(atom),
                    ValueType::StaticPi { domain, codomain } => {
                        let (domain, codomain) =
                            (value_type(self, domain), value_type(self, codomain));
                        self.arena.value_type_static_pi(domain, codomain)
                    },
                    ValueType::Unknown => {
                        panic!("the kernel has no unknown type: a replay fixture has none")
                    },
                };
                self.value_types.insert(id, copy);
            },
            Node::CompType(id) => {
                let value_type = |kernel: &Self, id: ValueTypeId| {
                    *kernel.value_types.get(&id).expect("children first")
                };
                let comp_type = |kernel: &Self, id: CompTypeId| {
                    *kernel.comp_types.get(&id).expect("children first")
                };
                let copy = match *core.comp_type(id).expect("a fixture type resolves") {
                    CompType::With(..) => panic!("the kernel has no lazy computation pair"),
                    CompType::Codata { .. } => panic!("kernel replay fixtures hold no codata"),
                    CompType::Returner {
                        result,
                        ref effects,
                    } => {
                        assert_eq!(
                            effects.purity(),
                            gandr_core_term::effect::Purity::Pure,
                            "kernel replay fixtures are pure"
                        );
                        let result = value_type(self, result);
                        self.arena.comp_type_returner(result)
                    },
                    CompType::Arrow { domain, codomain } => {
                        let (domain, codomain) =
                            (value_type(self, domain), comp_type(self, codomain));
                        self.arena.comp_type_arrow(domain, codomain)
                    },
                    CompType::Pi { domain, codomain } => {
                        let (domain, codomain) =
                            (value_type(self, domain), comp_type(self, codomain));
                        self.arena.comp_type_pi(domain, codomain)
                    },
                    CompType::Element { code, ref target } => {
                        let code = value(self, code);
                        self.arena.comp_type_element(code, target.clone())
                    },
                    CompType::Unknown => {
                        panic!("the kernel has no unknown type: a replay fixture has none")
                    },
                };
                self.comp_types.insert(id, copy);
            },
        }
    }
}

/// The decision the kernel reads for the machine's `decision`: a constant
/// keeps its position, and every other node is opaque to the replay.
///
/// # Specification
/// - requires: nothing; every machine decision is representable in replay.
/// - ensures: the decision kind, side and subgoal position remain unchanged;
///   constant nodes retain their index and run-local nodes become Other.
/// - provides: the trust-boundary projection into kernel replay decisions.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — machine decisions carry constant identities or run-local
///   value/computation ids. Exact constructor and side preservation is observed
///   by independent certification and the wrong-branch refusal; erasing a
///   constant identity, retaining a run-local id or swapping a side changes
///   replay.
/// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
/// - witness: `machine::tests::the_kernel_certifies_every_spinal_catalogue_and_ladder_trace`
/// - witness: `machine::tests::a_trace_naming_the_wrong_branch_is_refused`
/// - witness: `machine::tests::closed_codes_are_certified_in_both_type_families`
#[spec(
        ensures: |ret| {
         let node = |node| match node { TraceNode::Constant(constant) => ReplayNode::Constant(constant), TraceNode::Value(_) | TraceNode::Computation(_) => ReplayNode::Other };
         ret == match decision {
         ConversionDecision::Decompose => ConversionDecision::Decompose,
         ConversionDecision::ReduceLeft{redex} => ConversionDecision::ReduceLeft{redex:node(redex)},
         ConversionDecision::ReduceRight{redex} => ConversionDecision::ReduceRight{redex:node(redex)},
         ConversionDecision::ConstShortcut{constant} => ConversionDecision::ConstShortcut{constant:node(constant)},
         ConversionDecision::Unfold{constant} => ConversionDecision::Unfold{constant:node(constant)},
         ConversionDecision::Postpone{constant} => ConversionDecision::Postpone{constant:node(constant)},
         ConversionDecision::Freeze{constant,side} => ConversionDecision::Freeze{constant:node(constant),side},
         ConversionDecision::EtaExpand{side,variable} => ConversionDecision::EtaExpand{side,variable:node(variable)},
         ConversionDecision::ReturnEta{side} => ConversionDecision::ReturnEta{side},
         ConversionDecision::Reassociate{side} => ConversionDecision::Reassociate{side},
         ConversionDecision::Discard{side} => ConversionDecision::Discard{side},
         ConversionDecision::Force{thunk} => ConversionDecision::Force{thunk:node(thunk)},
         ConversionDecision::ComparedShared{left,right} => ConversionDecision::ComparedShared{left:node(left),right:node(right)},
         ConversionDecision::NegativeSubgoal{position} => ConversionDecision::NegativeSubgoal{position},
         }
        }
    )]
fn kernel_decision(decision: ConversionDecision<TraceNode>) -> ConversionDecision<ReplayNode>
{
    decision.map(|node: TraceNode| match node {
        TraceNode::Constant(constant) => ReplayNode::Constant(constant),
        TraceNode::Value(_) | TraceNode::Computation(_) => ReplayNode::Other,
    })
}

/// The certified kernel verdict a machine verdict corresponds to.
///
/// # Specification
/// - requires: nothing.
/// - ensures: definitive verdicts keep their truth value; every machine decline
///   maps to the kernel's `EngineDeclined` result.
/// - provides: the expected independent replay verdict, not a certification.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the domain is both definitive verdicts and every engine
///   decline. Kernel comparisons check positive, negative and schedule-induced
///   declined results, distinguishing negation, treating decline as refutation
///   and inventing a kernel failure.
/// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
/// - witness: `machine::tests::an_unlucky_schedule_declines_and_the_kernel_with_it`
#[spec(
        ensures: |ret| match verdict {
         MachineVerdict::Convertible => ret == KernelVerdict::Convertible,
         MachineVerdict::NotConvertible => ret == KernelVerdict::NotConvertible,
         MachineVerdict::Declined(_) => ret == KernelVerdict::Declined(ReplayDecline::EngineDeclined),
        }
    )]
fn certified(verdict: MachineVerdict) -> KernelVerdict
{
    match verdict {
        MachineVerdict::Convertible => KernelVerdict::Convertible,
        MachineVerdict::NotConvertible => KernelVerdict::NotConvertible,
        MachineVerdict::Declined(_) => KernelVerdict::Declined(ReplayDecline::EngineDeclined),
    }
}

/// The constants a fixture names: the first four admitted, in order, and
/// one never admitted.
#[derive(Clone, Copy, Debug)]
enum Name
{
    /// The constant admitted first.
    Zero,
    /// The constant admitted second.
    One,
    /// The constant admitted third.
    Two,
    /// The constant admitted fourth.
    Three,
    /// A constant no fixture admits, so it never unfolds.
    Rigid,
}

impl Name
{
    /// The admission position this name stands for.
    ///
    /// # Specification
    /// trivial.
    fn constant(self) -> ConstantIndex
    {
        ConstantIndex::from(match self {
            Self::Zero => 0_usize,
            Self::One => 1_usize,
            Self::Two => 2_usize,
            Self::Three => 3_usize,
            Self::Rigid => 9_usize,
        })
    }

    /// The table entry a body stored under this name takes.
    ///
    /// # Specification
    /// trivial.
    fn entry(self) -> GlobalIndex
    {
        GlobalIndex::from(match self {
            Self::Zero => 0_u32,
            Self::One => 1_u32,
            Self::Two => 2_u32,
            Self::Three => 3_u32,
            Self::Rigid => 9_u32,
        })
    }
}

/// The trace node naming the constant `name` stands for.
///
/// # Specification
/// trivial.
fn named(name: Name) -> TraceNode
{
    TraceNode::Constant(name.constant())
}

/// The innermost bound variable.
///
/// # Specification
/// trivial.
fn innermost(core: &mut CoreArena) -> ValueId
{
    core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32))
}

/// `thunk (λx. return x)`: the identity function as a value.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a thunk of a lambda returning its innermost intuitionistic
///   variable.
/// - provides: a closed identity function for forcing and eta comparisons.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a fresh intuitionistic identity fixture is observed
///   through application, eta comparison and independent replay. Wrong binder
///   zone or index, missing suspension or missing return changes its reduction
///   and certification.
/// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
/// - witness: `machine::tests::the_kernel_certifies_every_spinal_catalogue_and_ladder_trace`
/// - witness: `machine::tests::a_trace_naming_the_wrong_branch_is_refused`
/// - witness: `machine::tests::closed_codes_are_certified_in_both_type_families`
#[spec(
        ensures: |ret| core.value(ret).is_some_and(|value| match *value {
         Value::Thunk(body) => core.computation(body).is_some_and(|comp| match *comp {
         Computation::Lambda(body) => core.computation(body).is_some_and(|comp| match *comp {
         Computation::Return(value) => matches!(core.value(value), Some(Value::Variable{zone:Zone::Intuitionistic,index}) if u32::from(*index) == 0), Computation::Primitive { .. } | Computation::Transport(..) | Computation::PathTransport { .. } | Computation::Ride { .. } | Computation::TelescopeTransport { .. } | Computation::Lambda(_) | Computation::Fixpoint { .. } | Computation::Application(..) | Computation::Bind(..) | Computation::Ascribe { .. } | Computation::Force(_) | Computation::Case { .. } | Computation::Split { .. } | Computation::DataCase { .. } | Computation::RecordProjection(..) | Computation::TupleProjection(..) | Computation::Hole(_) | Computation::Mark { .. } | Computation::ListFold { .. } | Computation::ListCase { .. } | Computation::Perform { .. } | Computation::Handle { .. } | Computation::Exercise { .. } | Computation::Scope { .. } | Computation::Resume(..) | Computation::Abandon(_) | Computation::Reset(_) | Computation::Shift(_) | Computation::With(..) | Computation::Project(..) | Computation::Session(_) | Computation::Memory(_) | Computation::World(_) => false,
         }), Computation::Primitive { .. } | Computation::Transport(..) | Computation::PathTransport { .. } | Computation::Ride { .. } | Computation::TelescopeTransport { .. } | Computation::Fixpoint { .. } | Computation::Application(..) | Computation::Return(_) | Computation::Bind(..) | Computation::Ascribe { .. } | Computation::Force(_) | Computation::Case { .. } | Computation::Split { .. } | Computation::DataCase { .. } | Computation::RecordProjection(..) | Computation::TupleProjection(..) | Computation::Hole(_) | Computation::Mark { .. } | Computation::ListFold { .. } | Computation::ListCase { .. } | Computation::Perform { .. } | Computation::Handle { .. } | Computation::Exercise { .. } | Computation::Scope { .. } | Computation::Resume(..) | Computation::Abandon(_) | Computation::Reset(_) | Computation::Shift(_) | Computation::With(..) | Computation::Project(..) | Computation::Session(_) | Computation::Memory(_) | Computation::World(_) => false,
         }), Value::Primitive { .. } | Value::PathRefl(_) | Value::PathProduct(..) | Value::PathEquiv { .. } | Value::Here(_) | Value::Funext(..) | Value::Equiv(..) | Value::Univalence(..) | Value::Ua { .. } | Value::SessionRelated { .. } | Value::Stay(_) | Value::Then(..) | Value::FlowProduct(..) | Value::Forward(_) | Value::FunctionFlow(..) | Value::Recorded(_) | Value::Returned(_) | Value::Nested(_) | Value::Run(_) | Value::Variable { .. } | Value::Constant(_) | Value::Literal(_) | Value::Tuple(_) | Value::Injection(..) | Value::ListNil | Value::ListCons(..) | Value::Lift { .. } | Value::Quote(_) | Value::QuoteComputation(_) | Value::StaticLambda(_) | Value::StaticApplication(..) | Value::Constructor { .. } | Value::Record(_) | Value::Hole(_) | Value::Mark { .. } | Value::Reify(_) => false,
        })
    )]
fn identity(core: &mut CoreArena) -> ValueId
{
    let occurrence = innermost(core);
    let returned = core.computation_return(occurrence);
    let lambda = core.computation_lambda(returned);
    core.value_thunk(lambda)
}

/// `force head` applied to each argument in turn.
///
/// # Specification
/// - requires: the head and arguments resolve in core.
/// - ensures: force head applied left-associatively to every argument in order;
///   an empty argument list is just force head.
/// - provides: the fixture constructor for rigid and reducible application
///   spines.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a live value head and ordered live arguments form a
///   left-associated application spine. Rigid-spine comparisons and independent
///   replay distinguish reversing arguments, dropping an application or failing
///   to force the head.
/// - witness: `machine::tests::a_rigid_spine_refutes_at_its_differing_argument`
/// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
#[spec(
        ensures: |ret| {
         let mut cursor = ret;
         let mut valid = true;
         for &expected in arguments.iter().rev() {
          match core.computation(cursor) {
           Some(&Computation::Application(head,argument)) if argument == expected => cursor = head,
           _ => { valid = false; break; },
          }
         }
         valid && matches!(core.computation(cursor),Some(&Computation::Force(value)) if value == head)
        }
    )]
fn call(
    core: &mut CoreArena,
    head: ValueId,
    arguments: &[ValueId],
) -> ComputationId
{
    let mut applied = core.computation_force(head);
    for &argument in arguments {
        applied = core.computation_application(applied, argument);
    }
    applied
}

/// A world of four definitions and a rigid constant, and one pair per
/// rule arm, each with the verdict it must reach.
///
/// Constants zero and one are `unit` over two table entries, two is the
/// identity function, three is a pair of units, and the rigid one has no
/// body.
///
/// # Specification
/// - requires: nothing.
/// - ensures: pairs covering the forced unfolding, both §6.1 choices, the §6.2
///   choice, forcing, η against a rigid head, a rigid spine and two lambdas,
///   with both verdicts represented.
/// - provides: the catalogue the sink comparisons run over.
/// - panics: as [`World::new`].
///
/// # Adequacy
/// - hypothesis: L3 — the fixed catalogue contains both verdicts over live
///   value and computation roots. Each expected verdict is compared with the
///   actual machine and independently certified, distinguishing mislabeled
///   examples, dangling fixture roots and rule cases lost from the sink
///   differential.
/// - witness: `machine::tests::recording_does_not_move_the_verdict`
/// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
#[spec(
        ensures: |ret| ret.1.iter().any(|&(_,verdict)| verdict == MachineVerdict::Convertible)
         && ret.1.iter().any(|&(_,verdict)| verdict == MachineVerdict::NotConvertible)
         && ret.1.iter().all(|&(sides,verdict)| !matches!(verdict,MachineVerdict::Declined(_)) && match sides {
         Sides::Values(left,right) => ret.0.core.value(left).is_some() && ret.0.core.value(right).is_some(),
         Sides::Computations(left,right) => ret.0.core.computation(left).is_some() && ret.0.core.computation(right).is_some(),
         })
    )]
fn catalogue() -> (World, Vec<(Sides, MachineVerdict)>)
{
    let mut core = CoreArena::new();
    let first_unit = core.value_unit();
    let second_unit = core.value_unit();
    let function = identity(&mut core);
    let units = core.value_tuple(&[first_unit, second_unit]);
    let zero = core.value_constant(Name::Zero.constant());
    let one = core.value_constant(Name::One.constant());
    let two = core.value_constant(Name::Two.constant());
    let three = core.value_constant(Name::Three.constant());
    let rigid = core.value_constant(Name::Rigid.constant());
    let unit = core.value_unit();

    let mut cases = Vec::from([
        (Sides::Values(zero, unit), MachineVerdict::Convertible),
        (Sides::Values(zero, units), MachineVerdict::NotConvertible),
        (Sides::Values(zero, one), MachineVerdict::Convertible),
        (Sides::Values(zero, three), MachineVerdict::NotConvertible),
    ]);
    let left = call(&mut core, two, &[zero]);
    let right = call(&mut core, two, &[unit]);
    cases.push((
        Sides::Computations(left, right),
        MachineVerdict::Convertible,
    ));
    let left = call(&mut core, rigid, &[unit, zero]);
    let right = call(&mut core, rigid, &[unit, units]);
    cases.push((
        Sides::Computations(left, right),
        MachineVerdict::NotConvertible,
    ));
    let occurrence = innermost(&mut core);
    let body = call(&mut core, two, &[occurrence]);
    let left = core.computation_lambda(body);
    let right = core.computation_force(two);
    cases.push((
        Sides::Computations(left, right),
        MachineVerdict::Convertible,
    ));
    let body = call(&mut core, rigid, &[occurrence]);
    let left = core.computation_lambda(body);
    let right = core.computation_force(rigid);
    cases.push((
        Sides::Computations(left, right),
        MachineVerdict::Convertible,
    ));
    let returned = core.computation_return(zero);
    let left = core.value_thunk(returned);
    let returned = core.computation_return(unit);
    let right = core.value_thunk(returned);
    cases.push((Sides::Values(left, right), MachineVerdict::Convertible));
    let returned = core.computation_return(zero);
    let left = core.computation_lambda(returned);
    let returned = core.computation_return(units);
    let right = core.computation_lambda(returned);
    cases.push((
        Sides::Computations(left, right),
        MachineVerdict::NotConvertible,
    ));

    let world = World::new(core, &[
        (Name::Zero, first_unit),
        (Name::One, second_unit),
        (Name::Two, function),
        (Name::Three, units),
    ]);
    (world, cases)
}

#[test]
fn the_search_free_steps_answer_before_any_process()
{
    let mut core = CoreArena::new();
    let left = core.value_unit();
    let right = core.value_unit();
    let paired = core.value_tuple(&[left, right]);
    let world = World::new(core, &[]);

    let mut log = TraceLog::new();
    let agreed = world.run(Sides::Values(left, right), &mut log);
    assert_eq!(MachineVerdict::Convertible, agreed.verdict());
    assert_eq!(
        0_usize,
        usize::from(agreed.processes()),
        "two units are structurally equal, so no goal is started"
    );
    let decisions: Vec<_> = log.decisions().copied().collect();
    assert!(
        matches!(decisions.as_slice(), [
            ConversionDecision::ComparedShared { .. }
        ]),
        "and the trace closes the pair in one decision: {decisions:?}"
    );

    let apart = world.run(Sides::Values(left, paired), &mut NullSink);
    assert_eq!(MachineVerdict::NotConvertible, apart.verdict());
    assert_eq!(
        0_usize,
        usize::from(apart.processes()),
        "a unit and a pair are separated by their guards, so no goal is started"
    );
}

#[test]
fn neutral_list_fold_conversion_replays_both_branch_scopes()
{
    let mut core = CoreArena::new();
    let unit_type = core.value_type_unit();
    let boolean = core.value_type_sum(&[unit_type, unit_type]);
    let unit = core.value_unit();
    let yes = core.value_injection(gandr_kernel_term::Side::Left.into(), unit);
    let no = core.value_injection(gandr_kernel_term::Side::Right.into(), unit);
    let named_yes = core.value_constant(Name::Zero.constant());
    let list = innermost(&mut core);
    let head = core.value_variable(
        gandr_core_term::Zone::Intuitionistic,
        gandr_kernel_term::DeBruijnIndex::from(1_u32),
    );
    let result = innermost(&mut core);
    let on_nil = core.computation_return(named_yes);
    let same_nil = core.computation_return(yes);
    let other_nil = core.computation_return(no);
    let on_cons = core.computation_return(head);
    let other_cons = core.computation_return(result);
    let under_bind = core.value_variable(
        gandr_core_term::Zone::Intuitionistic,
        gandr_kernel_term::DeBruijnIndex::from(2_u32),
    );
    let bound = core.computation_return(unit);
    let body = core.computation_return(under_bind);
    let same_cons = core.computation_bind(bound, body);
    let fold = core.computation_list_fold(boolean, boolean, list, on_nil, on_cons);
    let left = core.computation_lambda(fold);
    let cases = [
        (same_nil, same_cons, MachineVerdict::Convertible),
        (other_nil, same_cons, MachineVerdict::NotConvertible),
        (same_nil, other_cons, MachineVerdict::NotConvertible),
    ]
    .map(|(nil, cons, expected)| {
        let fold = core.computation_list_fold(boolean, boolean, list, nil, cons);
        (core.computation_lambda(fold), expected)
    });
    let world = World::new(core, &[(Name::Zero, yes)]);
    for (right, expected) in cases {
        let sides = Sides::Computations(left, right);
        let (verdict, decisions) = world.traced(sides);
        assert_eq!(expected, verdict);
        assert_eq!(
            certified(expected),
            world.replayed(sides, verdict, &decisions)
        );
    }
}

#[test]

fn a_code_constant_unfolds_to_its_quote()
{
    let mut core = CoreArena::new();
    let unit = core.value_type_unit();
    let body = core.value_quote(unit);
    let reference = core.value_constant(Name::Zero.constant());
    let same = core.value_type_unit();
    let written = core.value_quote(same);
    let integer = core.value_type_base(BaseType::Integer);
    let other = core.value_quote(integer);
    let world = World::new(core, &[(Name::Zero, body)]);

    let alike = Sides::Values(reference, written);
    let (verdict, decisions) = world.traced(alike);
    assert_eq!(MachineVerdict::Convertible, verdict);
    assert!(
        matches!(decisions.as_slice(), &[
                ConversionDecision::Unfold { constant },
                ConversionDecision::ReduceLeft { redex },
                ConversionDecision::ComparedShared { .. },
            ] if constant == named(Name::Zero) && redex == named(Name::Zero)),
        "the constant unfolds to a code, and two codes of one type close as shared: \
             {decisions:?}"
    );
    assert_eq!(
        KernelVerdict::Convertible,
        world.replayed(alike, verdict, &decisions),
        "and the kernel replays the unfolding and the closing over its own quotes"
    );

    let apart = Sides::Values(reference, other);
    let (verdict, decisions) = world.traced(apart);
    assert_eq!(
        MachineVerdict::NotConvertible,
        verdict,
        "and two codes of rigidly different types are apart"
    );
    assert!(
        matches!(
            decisions.last(),
            Some(&ConversionDecision::ComparedShared { .. })
        ),
        "by a shared comparison the kernel separates on its own terms: {decisions:?}"
    );
    assert_eq!(
        KernelVerdict::NotConvertible,
        world.replayed(apart, verdict, &decisions),
        "which the kernel's replay confirms"
    );
}

#[test]
fn codes_that_could_unfold_inside_are_declined()
{
    let mut core = CoreArena::new();
    let unit = core.value_type_unit();
    let body = core.value_quote(unit);
    let defined = core.value_constant(Name::Zero.constant());
    let decodes_defined = core.value_type_element(defined, Level::zero());
    let flexible = core.value_quote(decodes_defined);
    let opaque = core.value_constant(Name::Rigid.constant());
    let decodes_opaque = core.value_type_element(opaque, Level::zero());
    let rigid = core.value_quote(decodes_opaque);
    let plain = core.value_type_unit();
    let written = core.value_quote(plain);
    let world = World::new(core, &[(Name::Zero, body)]);

    let undecided = Sides::Values(flexible, written);
    let (verdict, decisions) = world.traced(undecided);
    assert_eq!(
        MachineVerdict::Declined(DeclineReason::UndecidedCodes),
        verdict,
        "the decode names a constant with a body, which could unfold to the very code \
             it is compared against, and nothing reduces inside a type at this rung"
    );
    assert_eq!(
        certified(verdict),
        world.replayed(undecided, verdict, &decisions),
        "and the kernel declines with it: {decisions:?}"
    );
    let apart = Sides::Values(rigid, written);
    let (verdict, decisions) = world.traced(apart);
    assert_eq!(
        MachineVerdict::NotConvertible,
        verdict,
        "while a decode of a constant with no body cannot, so the codes are apart"
    );
    assert_eq!(
        KernelVerdict::NotConvertible,
        world.replayed(apart, verdict, &decisions),
        "and the kernel separates them on its own reading of rigidity: {decisions:?}"
    );
}

#[test]
fn one_body_is_evaluated_once_for_two_definitions()
{
    let processes = |entries: [Name; 2]| {
        let mut core = CoreArena::new();
        let body = core.value_unit();
        let zero = core.value_constant(Name::Zero.constant());
        let one = core.value_constant(Name::One.constant());
        let [first, second] = entries;
        let world = World::new(core, &[(first, body), (second, body)]);
        let report = world.run(Sides::Values(zero, one), &mut NullSink);
        assert_eq!(MachineVerdict::Convertible, report.verdict());
        usize::from(report.processes())
    };
    assert_eq!(
        5_usize,
        processes([Name::Zero, Name::One]),
        "the root, its two alternatives, and one channel per body"
    );
    assert_eq!(
        4_usize,
        processes([Name::Zero, Name::Zero]),
        "two definitions the table gave one body unfold through one channel"
    );
}

#[test]
fn a_lambda_meets_a_defined_function_by_eta()
{
    let mut core = CoreArena::new();
    let function = identity(&mut core);
    let head = core.value_constant(Name::Zero.constant());
    let occurrence = innermost(&mut core);
    let body = call(&mut core, head, &[occurrence]);
    let left = core.computation_lambda(body);
    let right = core.computation_force(head);
    let world = World::new(core, &[(Name::Zero, function)]);

    let (verdict, decisions) = world.traced(Sides::Computations(left, right));
    assert_eq!(MachineVerdict::Convertible, verdict);
    let &[
        ConversionDecision::Freeze {
            constant: frozen,
            side: ConversionSide::Right,
        },
        ConversionDecision::EtaExpand {
            side: ConversionSide::Right,
            variable,
        },
        ConversionDecision::ConstShortcut { constant: compared },
        ConversionDecision::ComparedShared { left, right },
    ] = decisions.as_slice()
    else {
        panic!("the frozen η-expansion answers before the unfolding does: {decisions:?}");
    };
    assert_eq!((named(Name::Zero), named(Name::Zero)), (frozen, compared));
    assert_eq!(
        (variable, variable),
        (left, right),
        "both sides apply the head to the one variable the expansion minted"
    );
}

#[test]
fn a_lambda_meets_a_stuck_function_by_eta()
{
    let mut core = CoreArena::new();
    let rigid = core.value_constant(Name::Rigid.constant());
    let occurrence = innermost(&mut core);
    let body = call(&mut core, rigid, &[occurrence]);
    let left = core.computation_lambda(body);
    let right = core.computation_force(rigid);
    let world = World::new(core, &[]);

    let (verdict, decisions) = world.traced(Sides::Computations(left, right));
    assert_eq!(MachineVerdict::Convertible, verdict);
    assert!(
        matches!(decisions.as_slice(), [
            ConversionDecision::EtaExpand {
                side: ConversionSide::Right,
                variable: TraceNode::Value(_),
            },
            ConversionDecision::ComparedShared { .. },
        ]),
        "a rigid head cannot unfold, so η is the one rule, and the expanded pair closes \
             structurally: {decisions:?}"
    );
}

#[test]
fn the_laws_of_bind_convert_by_their_decisions()
{
    // A rigid `R`: `force R` against its bind into `return`, and under
    // `λ a` the two nestings of `force R a to x. force R x to y. force R
    // a`, whose outer continuation reads `a` past the binder it moves
    // under.
    let mut core = CoreArena::new();
    let rigid = core.value_constant(Name::Rigid.constant());
    let unit = core.value_unit();
    let bound = innermost(&mut core);
    let outer = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let outermost = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(2_u32));
    let held = core.computation_force(rigid);
    let returned = core.computation_return(bound);
    let expanded = core.computation_bind(held, returned);
    let constant = core.computation_return(unit);
    let apart = core.computation_bind(held, constant);
    let applied = call(&mut core, rigid, &[bound]);
    let reading = call(&mut core, rigid, &[outer]);
    let shifted = call(&mut core, rigid, &[outermost]);
    let inner = core.computation_bind(applied, applied);
    let nested = core.computation_bind(inner, reading);
    let nested = core.computation_lambda(nested);
    let fused = core.computation_bind(applied, shifted);
    let reassociated = core.computation_bind(applied, fused);
    let reassociated = core.computation_lambda(reassociated);
    let misread = core.computation_bind(applied, reading);
    let misread = core.computation_bind(applied, misread);
    let misread = core.computation_lambda(misread);
    let world = World::new(core, &[]);
    let return_eta = |side| ConversionDecision::ReturnEta { side };
    let reassociate = |side| ConversionDecision::Reassociate { side };

    for (sides, expected, law) in [
        (
            Sides::Computations(held, expanded),
            MachineVerdict::Convertible,
            return_eta(ConversionSide::Left),
        ),
        (
            Sides::Computations(expanded, held),
            MachineVerdict::Convertible,
            return_eta(ConversionSide::Right),
        ),
        (
            Sides::Computations(nested, reassociated),
            MachineVerdict::Convertible,
            reassociate(ConversionSide::Left),
        ),
        (
            Sides::Computations(reassociated, nested),
            MachineVerdict::Convertible,
            reassociate(ConversionSide::Right),
        ),
        (
            Sides::Computations(held, apart),
            MachineVerdict::NotConvertible,
            return_eta(ConversionSide::Left),
        ),
        (
            Sides::Computations(nested, misread),
            MachineVerdict::NotConvertible,
            reassociate(ConversionSide::Left),
        ),
    ] {
        let (verdict, decisions) = world.traced(sides);
        assert_eq!(
            expected, verdict,
            "a pair related by a law of bind converts, and one apart in a continuation \
                 does not: {decisions:?}"
        );
        assert!(
            decisions.contains(&law),
            "the law is a recorded decision on the side that owes it: {decisions:?}"
        );
        assert_eq!(
            certified(verdict),
            world.replayed(sides, verdict, &decisions),
            "and the kernel replays it by name: {decisions:?}"
        );
    }
}

#[test]
fn an_unread_call_is_discarded_only_where_it_returns()
{
    // Under rigid `g` at level 0 and `f` at level 1: `force g () to v. force
    // f ()` against `force f ()`, and `force g () to v. force f v`, whose
    // continuation reads what the call returned.
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let call = |core: &mut CoreArena, index: u32, argument: ValueId| {
        let head = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index));
        let forced = core.computation_force(head);
        core.computation_application(forced, argument)
    };
    let called = call(&mut core, 1, unit);
    let followed = call(&mut core, 0, unit);
    let under = call(&mut core, 1, unit);
    let unread = core.computation_bind(called, under);
    let bound = innermost(&mut core);
    let reading = call(&mut core, 1, bound);
    let read = core.computation_bind(called, reading);
    let world = World::new(core, &[]);
    let both = [BinderLevel::from(0_u32), BinderLevel::from(1_u32)];
    let only_f = [BinderLevel::from(1_u32)];
    let discard = |side| ConversionDecision::Discard { side };

    // The last column is the kernel's verdict on the engine's trace, `None`
    // for a refusal: every variable of the kernel's fragment returns, so a
    // refutation that leaves a call it could drop standing does not replay.
    for (sides, returning, expected, decided, kernel_owes) in [
        (
            (unread, followed),
            &both[..],
            MachineVerdict::Convertible,
            Some(discard(ConversionSide::Left)),
            Some(KernelVerdict::Convertible),
        ),
        (
            (followed, unread),
            &both[..],
            MachineVerdict::Convertible,
            Some(discard(ConversionSide::Right)),
            Some(KernelVerdict::Convertible),
        ),
        (
            (unread, followed),
            &only_f[..],
            MachineVerdict::NotConvertible,
            None,
            None,
        ),
        (
            (read, followed),
            &both[..],
            MachineVerdict::NotConvertible,
            None,
            Some(KernelVerdict::NotConvertible),
        ),
    ] {
        let definitions =
            Definitions::new(&world.chain, &world.environment, world.environment.root())
                .returning(returning);
        let mut domain = DomainArena::new();
        let mut environment = crate::closure::Environment::new();
        for level in 0_u32 .. 2 {
            let neutral = domain
                .neutral_node(
                    crate::domain::NeutralHead::Variable {
                        zone: Zone::Intuitionistic,
                        level: BinderLevel::from(level),
                    },
                    Vec::new(),
                    crate::domain::Unfolding::Rigid,
                )
                .expect("a variable is a neutral");
            let variable = domain
                .value_neutral(neutral, crate::domain::TermFace::Reduced)
                .expect("a neutral is a value");
            environment.extend(Zone::Intuitionistic, variable);
        }
        let fuel = Fuel::from(4_096_u32);
        let (left, right) = sides;
        let evaluate = |domain: &mut DomainArena, term| {
            crate::eval::eval_comp_within(
                &world.core,
                domain,
                definitions,
                fuel,
                term,
                environment.clone(),
            )
            .map(|(evaluated, _remaining)| evaluated)
            .expect("each side evaluates")
        };
        let one = evaluate(&mut domain, left);
        let other = evaluate(&mut domain, right);
        let problem = Problem::computations(one, other).under(BinderLevel::from(2_u32));
        let mut log = TraceLog::new();
        let report = decide::<TraceLog<TraceNode>, ResharingMemo>(
            &world.core,
            &mut domain,
            definitions,
            MachineSettings::default(),
            problem,
            &mut log,
        )
        .expect("the machine answers");
        let decisions: Vec<ConversionDecision<TraceNode>> = log.decisions().copied().collect();
        assert_eq!(
            expected,
            report.verdict(),
            "an unread call of a variable that returns is the computation after it, and a \
                 call of one not known to return, or one whose value is read, stays: \
                 {decisions:?}"
        );
        assert_eq!(
            decided,
            decisions
                .iter()
                .copied()
                .find(|decision| matches!(decision, ConversionDecision::Discard { .. })),
            "the discard is a recorded decision on the side that held the call: {decisions:?}"
        );
        let mut kernel = Kernel::default();
        let sides = ReplaySides::Computations(
            kernel.computation(&world.core, left),
            kernel.computation(&world.core, right),
        );
        let claim = match report.verdict() {
            MachineVerdict::Convertible => EngineClaim::Convertible,
            MachineVerdict::NotConvertible => EngineClaim::NotConvertible,
            MachineVerdict::Declined(_) => EngineClaim::Declined,
        };
        let replayed = replay(
            &mut kernel.arena,
            &Unfoldings::new(Vec::new()),
            sides,
            claim,
            decisions.iter().map(|&decision| kernel_decision(decision)),
            ReplayBudget::DEFAULT,
        );
        let owed = kernel_owes.map_or_else(
            || matches!(replayed, KernelVerdict::Declined(ReplayDecline::Refused(_))),
            |owed| replayed == owed,
        );
        assert!(
            owed,
            "the kernel replays the discard by name, and refuses a refutation past one: \
             {replayed:?} {decisions:?}"
        );
    }
}

#[test]
fn a_returned_call_is_read_as_the_call_it_holds()
{
    // Under rigid `g` at level 0 and `f` at level 1: `return (returned (force
    // f ()))` against `force f ()` and against `force g ()`.
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let call = |core: &mut CoreArena, index: u32| {
        let head = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index));
        let forced = core.computation_force(head);
        core.computation_application(forced, unit)
    };
    let own = call(&mut core, 0);
    let other = call(&mut core, 1);
    let held = core.value_returned(own);
    let returned = core.computation_return(held);
    let world = World::new(core, &[]);

    for (sides, expected) in [
        ((returned, own), MachineVerdict::Convertible),
        ((own, returned), MachineVerdict::Convertible),
        ((returned, other), MachineVerdict::NotConvertible),
    ] {
        let definitions =
            Definitions::new(&world.chain, &world.environment, world.environment.root());
        let mut domain = DomainArena::new();
        let mut environment = crate::closure::Environment::new();
        for level in 0_u32 .. 2 {
            let neutral = domain
                .neutral_node(
                    crate::domain::NeutralHead::Variable {
                        zone: Zone::Intuitionistic,
                        level: BinderLevel::from(level),
                    },
                    Vec::new(),
                    crate::domain::Unfolding::Rigid,
                )
                .expect("a variable is a neutral");
            let variable = domain
                .value_neutral(neutral, crate::domain::TermFace::Reduced)
                .expect("a neutral is a value");
            environment.extend(Zone::Intuitionistic, variable);
        }
        let fuel = Fuel::from(4_096_u32);
        let (left, right) = sides;
        let evaluate = |domain: &mut DomainArena, term| {
            crate::eval::eval_comp_within(
                &world.core,
                domain,
                definitions,
                fuel,
                term,
                environment.clone(),
            )
            .map(|(evaluated, _remaining)| evaluated)
            .expect("each side evaluates")
        };
        let one = evaluate(&mut domain, left);
        let two = evaluate(&mut domain, right);
        let problem = Problem::computations(one, two).under(BinderLevel::from(2_u32));
        let mut log = TraceLog::new();
        let report = decide::<TraceLog<TraceNode>, ResharingMemo>(
            &world.core,
            &mut domain,
            definitions,
            MachineSettings::default(),
            problem,
            &mut log,
        )
        .expect("the machine answers");
        let decisions: Vec<ConversionDecision<TraceNode>> = log.decisions().copied().collect();
        assert_eq!(
            expected,
            report.verdict(),
            "the return of a call's result is the call, and no other: {decisions:?}"
        );
        let mut kernel = Kernel::default();
        let sides = ReplaySides::Computations(
            kernel.computation(&world.core, left),
            kernel.computation(&world.core, right),
        );
        let replayed = replay(
            &mut kernel.arena,
            &Unfoldings::new(Vec::new()),
            sides,
            match report.verdict() {
                MachineVerdict::Convertible => EngineClaim::Convertible,
                MachineVerdict::NotConvertible => EngineClaim::NotConvertible,
                MachineVerdict::Declined(_) => EngineClaim::Declined,
            },
            decisions.iter().map(|&decision| kernel_decision(decision)),
            ReplayBudget::DEFAULT,
        );
        assert_eq!(
            certified(report.verdict()),
            replayed,
            "the kernel reads the same return as its call, with no decision for it: \
             {decisions:?}"
        );
    }
}

#[test]
fn stuck_fixpoints_compare_by_their_bodies()
{
    // `(fix rec. λx. return x) R` for a rigid `R`, written twice, once
    // with each evidence, and `(fix rec. λx. return ()) R`.
    let mut core = CoreArena::new();
    let rigid = core.value_constant(Name::Rigid.constant());
    let stuck = |core: &mut CoreArena, returned, evidence| {
        let produced = core.computation_return(returned);
        let body = core.computation_lambda(produced);
        let fixpoint = core.computation_fixpoint(body, evidence);
        core.computation_application(fixpoint, rigid)
    };
    let occurrence = innermost(&mut core);
    let unit = core.value_unit();
    let descending = stuck(
        &mut core,
        occurrence,
        gandr_kernel_term::FixpointEvidence::StructuralDescent,
    );
    let partial = stuck(
        &mut core,
        occurrence,
        gandr_kernel_term::FixpointEvidence::Partial,
    );
    let constant = stuck(
        &mut core,
        unit,
        gandr_kernel_term::FixpointEvidence::StructuralDescent,
    );
    let world = World::new(core, &[]);

    for (sides, expected) in [
        (
            Sides::Computations(descending, partial),
            MachineVerdict::Convertible,
        ),
        (
            Sides::Computations(descending, constant),
            MachineVerdict::NotConvertible,
        ),
    ] {
        let (verdict, decisions) = world.traced(sides);
        assert_eq!(
            expected, verdict,
            "a fixpoint at a neutral argument stands, and two compare by their bodies \
                 opened under one self variable, whatever their evidence: {decisions:?}"
        );
        assert_eq!(
            certified(verdict),
            world.replayed(sides, verdict, &decisions),
            "and the kernel replays the comparison: {decisions:?}"
        );
    }
}

#[test]
fn a_rigid_spine_refutes_at_its_differing_argument()
{
    let mut core = CoreArena::new();
    let body = core.value_unit();
    let rigid = core.value_constant(Name::Rigid.constant());
    let reference = core.value_constant(Name::Zero.constant());
    let unit = core.value_unit();
    let paired = core.value_tuple(&[unit, unit]);
    let left = call(&mut core, rigid, &[unit, reference]);
    let right = call(&mut core, rigid, &[unit, paired]);
    let world = World::new(core, &[(Name::Zero, body)]);

    let (verdict, decisions) = world.traced(Sides::Computations(left, right));
    assert_eq!(MachineVerdict::NotConvertible, verdict);
    assert!(
        matches!(decisions.as_slice(), &[
                ConversionDecision::NegativeSubgoal { position },
                ConversionDecision::Unfold { constant },
                ConversionDecision::ReduceLeft { redex },
                ConversionDecision::ComparedShared { .. },
            ] if position == SubgoalPosition::from(1_u32)
                && constant == named(Name::Zero)
                && redex == named(Name::Zero)),
        "the refutation names the second argument, then refutes it on its own; the \
             first argument's agreement is not part of it: {decisions:?}"
    );
}

#[test]
fn a_definition_cycle_declines_rather_than_unfolding_forever()
{
    let mut core = CoreArena::new();
    let zero = core.value_constant(Name::Zero.constant());
    let one = core.value_constant(Name::One.constant());
    let unit = core.value_unit();
    // Each body is the other constant, and neither definition declares the
    // other among its mentions, so the chain admits the cycle and nothing
    // ahead of conversion refuses it.
    let world = World::new(core, &[(Name::Zero, one), (Name::One, zero)]);

    let mut log = TraceLog::new();
    let report = world.run(Sides::Values(zero, unit), &mut log);
    assert_eq!(
        MachineVerdict::Declined(DeclineReason::Cycle),
        report.verdict(),
        "the left side unfolds to the other constant and back, so its third \
             unfolding repeats its first"
    );
    assert!(
        u64::from(report.steps()) < 64_u64,
        "the chain caught the cycle at its first repeat, long before any budget"
    );
    assert!(
        log.decisions().next().is_none(),
        "and a decline emits no derivation"
    );

    let (verdict, _) = world.traced(Sides::Values(zero, one));
    assert_eq!(
        MachineVerdict::Convertible,
        verdict,
        "the cycle does not hide that the two constants unfold to each other"
    );
}

#[test]
fn a_held_endpoint_unfolds_by_a_recorded_step()
{
    // `ident(ident(unit))` as a compound endpoint, the inner endpoint an
    // argument of the outer, against `unit`. Run, both unfold inside
    // evaluation and the trace names neither, so the kernel, which unfolds
    // only what a trace names, refuses it. Held, each waits on `ident`
    // until the conversion unfolds it by a step the trace records.
    let mut core = CoreArena::new();
    let function = identity(&mut core);
    let head = core.value_constant(Name::Zero.constant());
    let unit = core.value_unit();
    let inner = call(&mut core, head, &[unit]);
    let inner = core.value_returned(inner);
    let outer = call(&mut core, head, &[inner]);
    let endpoint = core.value_returned(outer);
    let sides = Sides::Values(unit, endpoint);
    let run = World::new(core, &[(Name::Zero, function)]);

    let (verdict, decisions) = run.traced(sides);
    assert_eq!(MachineVerdict::Convertible, verdict);
    assert!(
        !decisions
            .iter()
            .any(|decision| matches!(decision, ConversionDecision::Unfold { .. })),
        "a running endpoint unfolds inside evaluation: {decisions:?}"
    );
    assert!(
        matches!(
            run.replayed(sides, verdict, &decisions),
            KernelVerdict::Declined(ReplayDecline::Refused(_))
        ),
        "the kernel takes no unfolding the trace does not name"
    );

    let held = run.holding();
    let (verdict, decisions) = held.traced(sides);
    assert_eq!(MachineVerdict::Convertible, verdict);
    let named = TraceNode::Constant(Name::Zero.constant());
    let steps = decisions
            .windows(2)
            .filter(|pair| {
                matches!(*pair, [ConversionDecision::Unfold { constant }, ConversionDecision::ReduceRight { redex }]
                    if *constant == named && *redex == named)
            })
            .count();
    assert_eq!(
        2_usize, steps,
        "each endpoint unfolds `ident` on its own side by a recorded step: {decisions:?}"
    );
    assert_eq!(
        KernelVerdict::Convertible,
        held.replayed(sides, verdict, &decisions),
        "the kernel replays both unfoldings where the endpoints hold them"
    );
}

#[test]
fn a_held_endpoint_under_an_elimination_unfolds_the_call_it_waits_on_361()
{
    // `run(ident(thunk(return unit)))`, `run` forcing its argument, as a
    // compound endpoint against `unit`. Held, `run` unfolds first and
    // forces the inner endpoint, so the outer endpoint waits on `ident`
    // through that force: the conversion unfolds `ident` next, and the
    // kernel replays both steps.
    let mut core = CoreArena::new();
    let function = identity(&mut core);
    let occurrence = innermost(&mut core);
    let forced = core.computation_force(occurrence);
    let forcing = core.computation_lambda(forced);
    let forcing = core.value_thunk(forcing);
    let ident = core.value_constant(Name::Zero.constant());
    let run = core.value_constant(Name::One.constant());
    let unit = core.value_unit();
    let returned = core.computation_return(unit);
    let suspended = core.value_thunk(returned);
    let inner = call(&mut core, ident, &[suspended]);
    let inner = core.value_returned(inner);
    let outer = call(&mut core, run, &[inner]);
    let endpoint = core.value_returned(outer);
    let sides = Sides::Values(unit, endpoint);
    let held = World::new(core, &[(Name::Zero, function), (Name::One, forcing)]).holding();

    let (verdict, decisions) = held.traced(sides);
    assert_eq!(MachineVerdict::Convertible, verdict, "{decisions:?}");
    let unfolded: Vec<TraceNode> = decisions
        .iter()
        .filter_map(|decision| match *decision {
            ConversionDecision::Unfold { constant } => Some(constant),
            ConversionDecision::ReduceLeft { .. }
            | ConversionDecision::ReduceRight { .. }
            | ConversionDecision::ConstShortcut { .. }
            | ConversionDecision::Postpone { .. }
            | ConversionDecision::Freeze { .. }
            | ConversionDecision::EtaExpand { .. }
            | ConversionDecision::ReturnEta { .. }
            | ConversionDecision::Reassociate { .. }
            | ConversionDecision::Discard { .. }
            | ConversionDecision::Force { .. }
            | ConversionDecision::ComparedShared { .. }
            | ConversionDecision::Decompose
            | ConversionDecision::NegativeSubgoal { .. } => None,
        })
        .collect();
    assert_eq!(
        unfolded,
        [
            TraceNode::Constant(Name::One.constant()),
            TraceNode::Constant(Name::Zero.constant())
        ],
        "the outer call unfolds, then the call its force waits on: {decisions:?}"
    );
    assert_eq!(
        KernelVerdict::Convertible,
        held.replayed(sides, verdict, &decisions),
        "the kernel replays both unfoldings"
    );
}

/// `(fix rec. λx. return x) R` for a rigid `R`: a fixpoint call stuck at
/// a head nothing unfolds, as `wind(x)` is stuck at its variable.
///
/// # Specification
/// trivial.
fn stuck_call(core: &mut CoreArena) -> ComputationId
{
    let rigid = core.value_constant(Name::Rigid.constant());
    let occurrence = innermost(core);
    let produced = core.computation_return(occurrence);
    let body = core.computation_lambda(produced);
    let fixpoint =
        core.computation_fixpoint(body, gandr_kernel_term::FixpointEvidence::StructuralDescent);
    core.computation_application(fixpoint, rigid)
}

#[test]
fn a_bind_over_a_stuck_call_reads_through_its_continuation_369()
{
    // `⟨S to n. return (n, ())⟩` for the stuck call `S`, against
    // `(⟨S⟩, ())`: `wind(Loop(x))` against `S(wind(x))` in miniature. The
    // endpoint's computation is pure, so it reads as its continuation's
    // pair over the held call, under either stance, and that call compares
    // whole with the other side's. Two binds, as `wind(Loop(Loop(x)))`
    // leaves, read the inner first, so the outer reads over a pair rather
    // than over a held bind. No decision names the reading, and the kernel
    // replays it by forcing it.
    let mut core = CoreArena::new();
    let stuck = stuck_call(&mut core);
    let occurrence = innermost(&mut core);
    let unit = core.value_unit();
    let paired = core.value_tuple(&[occurrence, unit]);
    let continuation = core.computation_return(paired);
    let bound = core.computation_bind(stuck, continuation);
    let endpoint = core.value_returned(bound);
    let call = core.value_returned(stuck);
    let expected = core.value_tuple(&[call, unit]);
    let twice = core.computation_bind(bound, continuation);
    let twice = core.value_returned(twice);
    let nested = core.value_tuple(&[expected, unit]);
    let pairs = [
        Sides::Values(endpoint, expected),
        Sides::Values(twice, nested),
    ];
    let run = World::new(core, &[]);

    for sides in pairs {
        let (verdict, decisions) = run.traced(sides);
        assert_eq!(
            MachineVerdict::Convertible,
            verdict,
            "the endpoint reads as the pairs over its call: {decisions:?}"
        );
        assert_eq!(
            KernelVerdict::Convertible,
            run.replayed(sides, verdict, &decisions),
            "the kernel forces the same reading: {decisions:?}"
        );
    }
    let held = run.holding();
    for sides in pairs {
        let (verdict, decisions) = held.traced(sides);
        assert_eq!(
            MachineVerdict::Convertible,
            verdict,
            "a held endpoint reads through a call no definition heads: {decisions:?}"
        );
        assert_eq!(
            KernelVerdict::Convertible,
            held.replayed(sides, verdict, &decisions),
            "and the kernel replays it held: {decisions:?}"
        );
    }
}

#[test]
fn a_continuation_casing_on_a_stuck_call_stays_whole()
{
    // `⟨S to n. n.0 to m. return (m, ())⟩` against `(⟨S⟩, ())`: the
    // continuation eliminates the held call and sticks there, so it never
    // returns and the endpoint stays its bind, apart from a pair.
    let mut core = CoreArena::new();
    let stuck = stuck_call(&mut core);
    let occurrence = innermost(&mut core);
    let unit = core.value_unit();
    let projected =
        core.computation_tuple_projection(occurrence, gandr_kernel_term::Component::from(0_usize));
    let paired = core.value_tuple(&[occurrence, unit]);
    let returned = core.computation_return(paired);
    let continuation = core.computation_bind(projected, returned);
    let bound = core.computation_bind(stuck, continuation);
    let endpoint = core.value_returned(bound);
    let call = core.value_returned(stuck);
    let expected = core.value_tuple(&[call, unit]);
    let sides = Sides::Values(endpoint, expected);
    let world = World::new(core, &[]);

    let (verdict, decisions) = world.traced(sides);
    assert_eq!(
        MachineVerdict::Declined(DeclineReason::Indeterminate),
        verdict,
        "the endpoint stays the bind over its call: {decisions:?}"
    );
}

#[test]
fn a_continuation_handing_its_stuck_call_to_a_definition_reads_as_that_call_761()
{
    // `⟨S to n. pair n⟩` for the stuck call `S` and the definition
    // `pair = λx. return (x, ())`: `double(S(m))`'s arm `twice(double(m))`
    // in miniature. Held, the continuation stops at `pair`'s call, so the
    // endpoint reads as that call over the held call: against the pair
    // over the call it unfolds `pair` by a recorded step, against `pair`
    // applied to the call as written it meets the same call, and the kernel
    // replays both. Before, the reading kept the bind whole and the first
    // pair declined.
    let mut core = CoreArena::new();
    let stuck = stuck_call(&mut core);
    let occurrence = innermost(&mut core);
    let unit = core.value_unit();
    let paired = core.value_tuple(&[occurrence, unit]);
    let returned = core.computation_return(paired);
    let pairing = core.computation_lambda(returned);
    let pairing = core.value_thunk(pairing);
    let pair = core.value_constant(Name::Zero.constant());
    let continuation = call(&mut core, pair, &[occurrence]);
    let bound = core.computation_bind(stuck, continuation);
    let endpoint = core.value_returned(bound);
    let held_call = core.value_returned(stuck);
    let expected = core.value_tuple(&[held_call, unit]);
    let written = call(&mut core, pair, &[held_call]);
    let written = core.value_returned(written);
    let held = World::new(core, &[(Name::Zero, pairing)]).holding();

    let unfolding = Sides::Values(endpoint, expected);
    let (verdict, decisions) = held.traced(unfolding);
    assert_eq!(
        MachineVerdict::Convertible,
        verdict,
        "the endpoint reads as `pair`'s call over the held call: {decisions:?}"
    );
    assert!(
        decisions.contains(&ConversionDecision::Unfold {
            constant: TraceNode::Constant(Name::Zero.constant()),
        }),
        "the conversion unfolds `pair` by a recorded step: {decisions:?}"
    );
    assert_eq!(
        KernelVerdict::Convertible,
        held.replayed(unfolding, verdict, &decisions),
        "the kernel reads the endpoint as the same call: {decisions:?}"
    );
    let as_written = Sides::Values(endpoint, written);
    let (verdict, decisions) = held.traced(as_written);
    assert_eq!(
        MachineVerdict::Convertible,
        verdict,
        "the endpoint meets `pair` applied to the call: {decisions:?}"
    );
    assert_eq!(
        KernelVerdict::Convertible,
        held.replayed(as_written, verdict, &decisions),
        "and the kernel replays it: {decisions:?}"
    );
}

#[test]
fn two_held_eliminations_of_one_call_compare_by_their_parts_879()
{
    // `⟨g ⟨S⟩ ⟨unit⟩⟩` against `⟨g ⟨S⟩ ()⟩` for the stuck call `S`, the
    // fixpoint `g = fix rec. λt. λc. return c` and the definition `unit =
    // return ()`: `walk(walk(b, c1), succ(c2))` against `walk(S(walk(b,
    // c1)), c2)` unfolded, in miniature. Both sides are `g` at its gate over
    // the held call, apart only in the argument one side unfolded, so the
    // walk finds them apart; they decompose as the kernel reads each, a bind
    // over the call, and `unit` unfolds to meet `()`. A second argument
    // apart from `()` refutes at that argument. Before, both pairs declined.
    let mut core = CoreArena::new();
    let stuck = stuck_call(&mut core);
    let held = core.value_returned(stuck);
    let occurrence = innermost(&mut core);
    let unit = core.value_unit();
    let returned_unit = core.computation_return(unit);
    let unit_body = core.value_thunk(returned_unit);
    let unit_name = core.value_constant(Name::Zero.constant());
    let unforced = call(&mut core, unit_name, &[]);
    let unforced = core.value_returned(unforced);
    let produced = core.computation_return(occurrence);
    let inner = core.computation_lambda(produced);
    let outer = core.computation_lambda(inner);
    let walk = core.computation_fixpoint(
        outer,
        gandr_kernel_term::FixpointEvidence::StructuralDescent,
    );
    let walked = |core: &mut CoreArena, argument| {
        let gated = core.computation_application(walk, held);
        let applied = core.computation_application(gated, argument);
        core.value_returned(applied)
    };
    let left = walked(&mut core, unforced);
    let right = walked(&mut core, unit);
    let pair = core.value_tuple(&[unit, unit]);
    let apart = walked(&mut core, pair);
    let world = World::new(core, &[(Name::Zero, unit_body)]).holding();

    let converts = Sides::Values(left, right);
    let (verdict, decisions) = world.traced(converts);
    assert_eq!(
        MachineVerdict::Convertible,
        verdict,
        "the two applications compare by their parts: {decisions:?}"
    );
    assert!(
        decisions.contains(&ConversionDecision::Unfold {
            constant: TraceNode::Constant(Name::Zero.constant()),
        }),
        "the argument meets `()` by unfolding `unit`: {decisions:?}"
    );
    assert_eq!(
        KernelVerdict::Convertible,
        world.replayed(converts, verdict, &decisions),
        "the kernel decomposes the same binds: {decisions:?}"
    );
    let refutes = Sides::Values(left, apart);
    let (verdict, decisions) = world.traced(refutes);
    assert_eq!(
        MachineVerdict::NotConvertible,
        verdict,
        "a second argument apart refutes: {decisions:?}"
    );
    assert_eq!(
        KernelVerdict::NotConvertible,
        world.replayed(refutes, verdict, &decisions),
        "and the kernel refutes at the same argument: {decisions:?}"
    );
}

#[test]
fn two_held_transports_convert_by_their_computations()
{
    // `⟨comp(R)⟩` against `⟨other((), R)⟩` for the rigid path `R`, where
    // `comp = λq. tr(y. Path(Unit, (), y), q, ())` and `other` binds one
    // more parameter before the same transport: `p then q` written in two
    // definitions. Both unfold to a transport stuck on `R` whose motive
    // closes over its own definition's frame, so the walk leaves the two
    // apart beneath the motive's binder; read as their computations, the
    // two compare by their motives under one fresh variable and their
    // values, and the kernel replays the reading.
    let mut core = CoreArena::new();
    let unit_type = core.value_type_unit();
    let unit = core.value_unit();
    let endpoint = innermost(&mut core);
    let motive = core.value_type_path(unit_type, unit, endpoint);
    let path = innermost(&mut core);
    let transport = core.computation_path_transport(motive, path, unit);
    let comp = core.computation_lambda(transport);
    let comp = core.value_thunk(comp);
    let other = core.computation_lambda(transport);
    let other = core.computation_lambda(other);
    let other = core.value_thunk(other);
    let rigid = core.value_constant(Name::Rigid.constant());
    let named = core.value_constant(Name::Zero.constant());
    let left = call(&mut core, named, &[rigid]);
    let left = core.value_returned(left);
    let renamed = core.value_constant(Name::One.constant());
    let right = call(&mut core, renamed, &[unit, rigid]);
    let right = core.value_returned(right);
    let moved = core.computation_path_transport(motive, rigid, rigid);
    let moved = core.value_returned(moved);
    let held = World::new(core, &[(Name::Zero, comp), (Name::One, other)]).holding();

    let sides = Sides::Values(left, right);
    let (verdict, decisions) = held.traced(sides);
    assert_eq!(
        MachineVerdict::Convertible,
        verdict,
        "two held transports along one path are one: {decisions:?}"
    );
    assert_eq!(
        KernelVerdict::Convertible,
        held.replayed(sides, verdict, &decisions),
        "and the kernel replays them as their computations: {decisions:?}"
    );
    let (verdict, decisions) = held.traced(Sides::Values(left, moved));
    assert_ne!(
        MachineVerdict::Convertible,
        verdict,
        "a transport of another value is another endpoint: {decisions:?}"
    );
}

#[test]
fn a_continuation_stuck_at_its_own_bind_reads_through_both()
{
    // `⟨force R to n. force R to m. return (n, m)⟩` for the rigid
    // constant `R`, against `(⟨force R⟩, ⟨force R⟩)`: a decoder's arm
    // `el(a) to x. el(b) to y. return ⌜x ⇒ y⌝` in miniature. The
    // continuation sticks at its own bind; the reading nests into it and
    // reads through both, under either stance, and the kernel replays it by
    // the same nesting. The calls are forced constants rather than stuck
    // fixpoints, whose closures inside the continuation carry its binding
    // and so only meet a fixpoint from outside it under a binder.
    let mut core = CoreArena::new();
    let rigid = core.value_constant(Name::Rigid.constant());
    let held = core.computation_force(rigid);
    let occurrence = innermost(&mut core);
    let first = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let paired = core.value_tuple(&[first, occurrence]);
    let returned = core.computation_return(paired);
    let continuation = core.computation_bind(held, returned);
    let bound = core.computation_bind(held, continuation);
    let endpoint = core.value_returned(bound);
    let call = core.value_returned(held);
    let expected = core.value_tuple(&[call, call]);
    let sides = Sides::Values(endpoint, expected);
    let read = |world: &World| {
        let (verdict, decisions) = world.traced(sides);
        assert_eq!(
            MachineVerdict::Convertible,
            verdict,
            "the endpoint reads as the pair over both calls: {decisions:?}"
        );
        assert_eq!(
            KernelVerdict::Convertible,
            world.replayed(sides, verdict, &decisions),
            "the kernel nests the same reading: {decisions:?}"
        );
    };
    let run = World::new(core, &[]);
    read(&run);
    read(&run.holding());
}

#[test]
fn unfolding_one_function_twice_is_not_a_cycle()
{
    let mut core = CoreArena::new();
    let function = identity(&mut core);
    let head = Name::Zero.constant();
    let head = core.value_constant(head);
    let unit = core.value_unit();
    let applied = call(&mut core, head, &[unit]);
    let occurrence = innermost(&mut core);
    let again = call(&mut core, head, &[occurrence]);
    let twice = core.computation_bind(applied, again);
    let returned = core.computation_return(unit);
    let world = World::new(core, &[(Name::Zero, function)]);

    let (verdict, decisions) = world.traced(Sides::Computations(twice, returned));
    assert_eq!(
        MachineVerdict::Convertible,
        verdict,
        "the identity unfolds twice on one chain, under two spines, which is no cycle"
    );
    let unfoldings = decisions
        .iter()
        .filter(|decision| matches!(decision, ConversionDecision::Unfold { .. }))
        .count();
    assert_eq!(2_usize, unfoldings, "{decisions:?}");
}

#[test]
fn a_diverging_evaluation_declines_on_the_budget()
{
    let mut core = CoreArena::new();
    let occurrence = innermost(&mut core);
    let self_applied = call(&mut core, occurrence, &[occurrence]);
    let lambda = core.computation_lambda(self_applied);
    let omega = core.value_thunk(lambda);
    let looping = call(&mut core, omega, &[omega]);
    let body = core.value_thunk(looping);
    let head = core.value_constant(Name::Zero.constant());
    let forced = core.computation_force(head);
    let unit = core.value_unit();
    let returned = core.computation_return(unit);
    let world = World::new(core, &[(Name::Zero, body)]);

    let budget = StepBudget::from(10_000_u64);
    let settings = MachineSettings::new(
        SchedulingPolicy::default(),
        GranularityPolicy::default(),
        budget,
    );
    let report = world.run_under(
        settings,
        Sides::Computations(forced, returned),
        &mut NullSink,
    );
    assert_eq!(
        MachineVerdict::Declined(DeclineReason::Budget),
        report.verdict(),
        "forcing the definition runs Ω, which unfolds nothing the chain could catch"
    );
    assert!(
        u64::from(report.steps()) > u64::from(budget),
        "the evaluation slices were charged until they passed the budget"
    );
}

#[test]
fn a_refutation_outranks_a_decline()
{
    let mut core = CoreArena::new();
    let zero = core.value_constant(Name::Zero.constant());
    let one = core.value_constant(Name::One.constant());
    let unit = core.value_unit();
    let units = core.value_tuple(&[unit, unit]);
    let cyclic = core.value_tuple(&[zero, unit]);
    let refuted = core.value_tuple(&[unit, units]);
    let world = World::new(core, &[(Name::Zero, one), (Name::One, zero)]);

    let (verdict, decisions) = world.traced(Sides::Values(cyclic, refuted));
    assert_eq!(
        MachineVerdict::NotConvertible,
        verdict,
        "the second components refute the pair whatever the first declines"
    );
    assert!(
        matches!(decisions.as_slice(), &[
                ConversionDecision::NegativeSubgoal { position },
                ConversionDecision::ComparedShared { .. },
            ] if position == SubgoalPosition::from(1_u32)),
        "{decisions:?}"
    );

    let (verdict, decisions) = world.traced(Sides::Values(cyclic, units));
    assert_eq!(
        MachineVerdict::Declined(DeclineReason::Cycle),
        verdict,
        "with the second components agreeing, the first one's decline is the answer"
    );
    assert!(decisions.is_empty(), "{decisions:?}");
}

#[test]
fn recording_does_not_move_the_verdict()
{
    let (world, cases) = catalogue();
    for (sides, expected) in cases {
        let unrecorded = world.run(sides, &mut NullSink);
        let mut log = TraceLog::new();
        let recorded = world.run(sides, &mut log);
        assert_eq!(expected, unrecorded.verdict(), "{sides:?}");
        assert_eq!(
            (unrecorded.verdict(), unrecorded.processes()),
            (recorded.verdict(), recorded.processes()),
            "recording changes what is kept, never what is run: {sides:?}"
        );
    }
}

#[test]
fn the_sink_off_run_keeps_no_derivation()
{
    let (world, cases) = catalogue();
    for (sides, _) in cases {
        let unrecorded = world.run(sides, &mut NullSink);
        let recorded = world.run(sides, &mut TraceLog::new());
        assert_eq!(
            0_usize,
            usize::from(unrecorded.derivations()),
            "the null sink keeps nothing, so the run allocates no derivation: {sides:?}"
        );
        assert_eq!(
            usize::from(recorded.processes()),
            usize::from(recorded.derivations()),
            "a recording run keeps one derivation per process: {sides:?}"
        );
    }
}

/// `thunk (return below to x. return (x, x))`: one evaluation of the
/// constant `below`, paired with itself.
///
/// # Specification
/// - requires: nothing; below may denote a body or stand rigid.
/// - ensures: a thunk binding return below once, then returning a pair of the
///   same innermost intuitionistic variable.
/// - provides: one doubling rung whose repeated premise can be shared.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a constant reference is evaluated once beneath a bind and
///   its result is paired with itself. Exact memoized versus unrolled process
///   counts across successive ladder rungs, plus kernel replay, distinguish
///   duplicating evaluation, a wrong binder and naming the wrong predecessor.
/// - witness: `machine::tests::re_sharing_runs_one_goal_per_distinct_pair`
/// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
#[spec(
        ensures: |ret| core.value(ret).is_some_and(|value| match *value {
         Value::Thunk(body) => core.computation(body).is_some_and(|comp| match *comp {
         Computation::Bind(bound,body) => matches!(core.computation(bound),Some(&Computation::Return(value)) if core.value(value) == Some(&Value::Constant(below)))
          && core.computation(body).is_some_and(|comp| match *comp {
           Computation::Return(value) => core.value(value).is_some_and(|value| match *value {
            Value::Tuple(ref components) => matches!(**components, [left, right] if left == right) && matches!(components.first().and_then(|&left| core.value(left)),Some(Value::Variable{zone:Zone::Intuitionistic,index}) if u32::from(*index) == 0), Value::Primitive { .. } | Value::PathRefl(_) | Value::PathProduct(..) | Value::PathEquiv { .. } | Value::Here(_) | Value::Funext(..) | Value::Equiv(..) | Value::Univalence(..) | Value::Ua { .. } | Value::SessionRelated { .. } | Value::Stay(_) | Value::Then(..) | Value::FlowProduct(..) | Value::Forward(_) | Value::FunctionFlow(..) | Value::Recorded(_) | Value::Returned(_) | Value::Nested(_) | Value::Run(_) | Value::Variable { .. } | Value::Constant(_) | Value::Literal(_) | Value::Injection(..) | Value::ListNil | Value::ListCons(..) | Value::Thunk(_) | Value::Lift { .. } | Value::Quote(_) | Value::QuoteComputation(_) | Value::StaticLambda(_) | Value::StaticApplication(..) | Value::Constructor { .. } | Value::Record(_) | Value::Hole(_) | Value::Mark { .. } | Value::Reify(_) => false,
           }), Computation::Primitive { .. } | Computation::Transport(..) | Computation::PathTransport { .. } | Computation::Ride { .. } | Computation::TelescopeTransport { .. } | Computation::Lambda(_) | Computation::Fixpoint { .. } | Computation::Application(..) | Computation::Bind(..) | Computation::Ascribe { .. } | Computation::Force(_) | Computation::Case { .. } | Computation::Split { .. } | Computation::DataCase { .. } | Computation::RecordProjection(..) | Computation::TupleProjection(..) | Computation::Hole(_) | Computation::Mark { .. } | Computation::ListFold { .. } | Computation::ListCase { .. } | Computation::Perform { .. } | Computation::Handle { .. } | Computation::Exercise { .. } | Computation::Scope { .. } | Computation::Resume(..) | Computation::Abandon(_) | Computation::Reset(_) | Computation::Shift(_) | Computation::With(..) | Computation::Project(..) | Computation::Session(_) | Computation::Memory(_) | Computation::World(_) => false,
          }), Computation::Primitive { .. } | Computation::Transport(..) | Computation::PathTransport { .. } | Computation::Ride { .. } | Computation::TelescopeTransport { .. } | Computation::Lambda(_) | Computation::Fixpoint { .. } | Computation::Application(..) | Computation::Return(_) | Computation::Ascribe { .. } | Computation::Force(_) | Computation::Case { .. } | Computation::Split { .. } | Computation::DataCase { .. } | Computation::RecordProjection(..) | Computation::TupleProjection(..) | Computation::Hole(_) | Computation::Mark { .. } | Computation::ListFold { .. } | Computation::ListCase { .. } | Computation::Perform { .. } | Computation::Handle { .. } | Computation::Exercise { .. } | Computation::Scope { .. } | Computation::Resume(..) | Computation::Abandon(_) | Computation::Reset(_) | Computation::Shift(_) | Computation::With(..) | Computation::Project(..) | Computation::Session(_) | Computation::Memory(_) | Computation::World(_) => false,
         }), Value::Primitive { .. } | Value::PathRefl(_) | Value::PathProduct(..) | Value::PathEquiv { .. } | Value::Here(_) | Value::Funext(..) | Value::Equiv(..) | Value::Univalence(..) | Value::Ua { .. } | Value::SessionRelated { .. } | Value::Stay(_) | Value::Then(..) | Value::FlowProduct(..) | Value::Forward(_) | Value::FunctionFlow(..) | Value::Recorded(_) | Value::Returned(_) | Value::Nested(_) | Value::Run(_) | Value::Variable { .. } | Value::Constant(_) | Value::Literal(_) | Value::Tuple(_) | Value::Injection(..) | Value::ListNil | Value::ListCons(..) | Value::Lift { .. } | Value::Quote(_) | Value::QuoteComputation(_) | Value::StaticLambda(_) | Value::StaticApplication(..) | Value::Constructor { .. } | Value::Record(_) | Value::Hole(_) | Value::Mark { .. } | Value::Reify(_) => false,
        })
    )]
fn doubled(
    core: &mut CoreArena,
    below: ConstantIndex,
) -> ValueId
{
    let reference = core.value_constant(below);
    let produced = core.computation_return(reference);
    let occurrence = innermost(core);
    let paired = core.value_tuple(&[occurrence, occurrence]);
    let returned = core.computation_return(paired);
    let bound = core.computation_bind(produced, returned);
    core.value_thunk(bound)
}

/// Admit `body` as the next constant, under a table entry of its own.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the constant `body` is admitted as, at the next position.
/// - provides: the admission order the ladder fixture builds in.
/// - panics: past `u32::MAX` entries, which no fixture reaches.
///
/// # Adequacy
/// - hypothesis: L3 — a finite body table below the index ceiling gains a
///   distinct entry at its next ordinal. Successive ladder comparisons observe
///   correct predecessor bodies and sharing growth, distinguishing an
///   off-by-one constant, reused table entry or wrong admitted body.
/// - witness: `machine::tests::re_sharing_runs_one_goal_per_distinct_pair`
/// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
#[spec(
        captures: [position = bodies.len()],
        ensures: |ret| usize::from(ret) == position && position.checked_add(1) == Some(bodies.len())
         && bodies.last().is_some_and(|&(entry,stored)| usize::try_from(u32::from(entry)).ok() == Some(position) && stored == body)
    )]
fn next_constant(
    bodies: &mut Vec<(GlobalIndex, ValueId)>,
    body: ValueId,
) -> ConstantIndex
{
    let position = bodies.len();
    let entry = u32::try_from(position).expect("a fixture admits few constants");
    bodies.push((GlobalIndex::from(entry), body));
    ConstantIndex::from(position)
}

/// Two ladders of five rungs: rung zero of each is `unit`, and every rung
/// above is [`doubled`] over the rung below it on its own ladder.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the comparisons of rungs one through four across the two ladders,
///   in order, each convertible; a rung's comparison decomposes into two
///   premises naming one pair of the rung below.
/// - provides: the family whose memoless run starts goals exponentially in the
///   rung and whose re-shared run starts them linearly.
/// - panics: as [`World::admit`].
///
/// # Adequacy
/// - hypothesis: L3 — two five-rung ladders share only their structural
///   pattern, not admission identities. Exact linear memoized counts,
///   exponential null-memo counts and kernel certification distinguish a
///   skipped predecessor, same-side comparison, missing repeated premise or
///   wrong rung order.
/// - witness: `machine::tests::re_sharing_runs_one_goal_per_distinct_pair`
/// - witness: `machine::tests::edges_per_revision_grow_with_the_distinct_goals`
/// - witness: `machine::tests::the_kernel_certifies_every_catalogue_and_ladder_trace`
#[spec(
        ensures: |ret| ret.0.bodies.len() == 10 && ret.1.len() == 4
         && ret.0.bodies.iter().take(2).all(|&body| ret.0.core.value(body) == Some(&Value::unit()))
         && ret.1.iter().enumerate().all(|(rung,&sides)| match sides {
         Sides::Values(left,right) => rung.checked_add(1).and_then(|rung| rung.checked_mul(2)).is_some_and(|position|
             ret.0.core.value(left) == Some(&Value::Constant(ConstantIndex::from(position)))
                 && position.checked_add(1).is_some_and(|position| ret.0.core.value(right) == Some(&Value::Constant(ConstantIndex::from(position))))),
         Sides::Computations(_,_) => false,
         })
    )]
fn ladders() -> (World, Vec<Sides>)
{
    let mut core = CoreArena::new();
    let mut bodies = Vec::new();
    let mut rungs = Vec::new();
    let mut below = None;
    for _rung in 0_u32 .. 5_u32 {
        let (left, right) = match below {
            None => (core.value_unit(), core.value_unit()),
            Some((left, right)) => (doubled(&mut core, left), doubled(&mut core, right)),
        };
        let left = next_constant(&mut bodies, left);
        let right = next_constant(&mut bodies, right);
        if below.is_some() {
            let left_rung = core.value_constant(left);
            let right_rung = core.value_constant(right);
            rungs.push(Sides::Values(left_rung, right_rung));
        }
        below = Some((left, right));
    }
    (World::admit(core, &bodies), rungs)
}

#[test]
fn re_sharing_runs_one_goal_per_distinct_pair()
{
    let (world, rungs) = ladders();
    let mut reshared = Vec::new();
    let mut memoless = Vec::new();
    for &sides in &rungs {
        let live = world.run(sides, &mut NullSink);
        let null = world.run_with::<_, NullMemo>(MachineSettings::default(), sides, &mut NullSink);
        assert_eq!(
            (MachineVerdict::Convertible, MachineVerdict::Convertible),
            (live.verdict(), null.verdict()),
            "{sides:?}"
        );
        reshared.push(usize::from(live.processes()));
        memoless.push(usize::from(null.processes()));
    }
    assert_eq!(
        Vec::from([13_usize, 21_usize, 29_usize, 37_usize]),
        reshared,
        "eight processes per rung over five at the bottom: the rung's goal, its two \
             alternatives, its pair's goal, two body channels and two entering channels, \
             with the pair's two premises meeting in one goal"
    );
    assert_eq!(
        Vec::from([16_usize, 34_usize, 66_usize, 126_usize]),
        memoless,
        "without re-sharing each rung's goals double beneath it, while its channels \
             are still shared"
    );
}

#[test]
fn edges_per_revision_grow_with_the_distinct_goals()
{
    let (world, rungs) = ladders();
    let edges: Vec<(usize, usize)> = rungs
        .iter()
        .map(|&sides| {
            let report = world.run(sides, &mut NullSink);
            (
                usize::from(report.edges().acceptance()),
                usize::from(report.edges().refusal()),
            )
        })
        .collect();
    assert_eq!(
        Vec::from([
            (6_usize, 0_usize),
            (10_usize, 0_usize),
            (14_usize, 0_usize),
            (18_usize, 0_usize),
        ]),
        edges,
        "four edges per rung over two at the bottom: a rung's goal holds its two \
             unfoldings and its pair's entry, the pair holds one edge to the shared rung \
             below, and the bottom holds its two unfoldings"
    );
}

#[test]
fn an_acceptance_is_keyed_on_its_winning_derivation()
{
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let returned = core.computation_return(unit);
    let lambda = core.computation_lambda(returned);
    let constant = core.value_thunk(lambda);
    let head = core.value_constant(Name::Zero.constant());
    let units = core.value_tuple(&[unit, unit]);
    let left = call(&mut core, head, &[unit]);
    let right = call(&mut core, head, &[units]);
    let world = World::new(core, &[(Name::Zero, constant)]);

    let report = world.run(Sides::Computations(left, right), &mut NullSink);
    assert_eq!(
        MachineVerdict::Convertible,
        report.verdict(),
        "a constant function meets itself at any two arguments"
    );
    assert_eq!(
        (1_usize, 0_usize),
        (
            usize::from(report.edges().acceptance()),
            usize::from(report.edges().refusal()),
        ),
        "the root rests on its unfolding branch alone, which closes the two results by \
             their one source term and holds one edge, to the definition; the shortcut's \
             edge to its refuted entry on the arguments is not the root's, and that entry \
             holds none"
    );
}

#[test]
fn a_refusal_is_keyed_on_the_union_over_its_branches()
{
    let mut core = CoreArena::new();
    let occurrence = innermost(&mut core);
    let unit = core.value_unit();
    let paired = core.value_tuple(&[occurrence, unit]);
    let returned = core.computation_return(paired);
    let lambda = core.computation_lambda(returned);
    let function = core.value_thunk(lambda);
    let head = core.value_constant(Name::Zero.constant());
    let units = core.value_tuple(&[unit, unit]);
    let left = call(&mut core, head, &[unit]);
    let right = call(&mut core, head, &[units]);
    let world = World::new(core, &[(Name::Zero, function)]);

    let report = world.run(Sides::Computations(left, right), &mut NullSink);
    assert_eq!(
        MachineVerdict::NotConvertible,
        report.verdict(),
        "the function keeps its argument, and the arguments differ"
    );
    assert_eq!(
        (0_usize, 2_usize),
        (
            usize::from(report.edges().acceptance()),
            usize::from(report.edges().refusal()),
        ),
        "the root holds the union over its three branches: the shortcut's edge to its \
             entry on the arguments, and the definition the other two unfolded before \
             refuting; the arguments' guard-separated entry holds none"
    );
}

#[test]
fn a_goal_resting_on_itself_declines_on_the_cycle()
{
    let mut core = CoreArena::new();
    let zero = core.value_constant(Name::Zero.constant());
    let one = core.value_constant(Name::One.constant());
    let unit = core.value_unit();
    let left = core.value_tuple(&[zero, unit]);
    let right = core.value_tuple(&[one, unit]);
    let world = World::new(core, &[(Name::Zero, left), (Name::One, right)]);
    let sides = Sides::Values(zero, one);

    let reshared = world.run(sides, &mut NullSink);
    assert_eq!(
        MachineVerdict::Declined(DeclineReason::Cycle),
        reshared.verdict(),
        "each constant unfolds to a pair holding itself, so the goal on the first \
             components decomposes into itself and waits on itself"
    );
    let settings = MachineSettings::new(
        SchedulingPolicy::default(),
        GranularityPolicy::default(),
        StepBudget::from(10_000_u64),
    );
    let memoless = world.run_with::<_, NullMemo>(settings, sides, &mut NullSink);
    assert_eq!(
        MachineVerdict::Declined(DeclineReason::Budget),
        memoless.verdict(),
        "without re-sharing every lap starts a fresh goal, and only the budget ends them"
    );
}

#[test]
fn the_memo_never_moves_a_verdict()
{
    let (world, cases) = catalogue();
    for (sides, expected) in cases {
        let reshared = world.run(sides, &mut NullSink);
        let memoless =
            world.run_with::<_, NullMemo>(MachineSettings::default(), sides, &mut NullSink);
        assert_eq!(
            (expected, expected),
            (reshared.verdict(), memoless.verdict()),
            "{sides:?}"
        );
    }
}

#[test]
fn the_kernel_certifies_every_catalogue_and_ladder_trace()
{
    let (world, cases) = catalogue();
    for (sides, expected) in cases {
        let (verdict, decisions) = world.traced(sides);
        assert_eq!(expected, verdict, "{sides:?}");
        assert_eq!(
            certified(verdict),
            world.replayed(sides, verdict, &decisions),
            "{sides:?}: {decisions:?}"
        );
    }
    let (world, rungs) = ladders();
    for sides in rungs {
        let (verdict, decisions) = world.traced(sides);
        assert_eq!(MachineVerdict::Convertible, verdict, "{sides:?}");
        assert_eq!(
            KernelVerdict::Convertible,
            world.replayed(sides, verdict, &decisions),
            "{sides:?}: {decisions:?}"
        );
    }
}

#[test]
fn the_kernel_certifies_every_spinal_catalogue_and_ladder_trace()
{
    let (world, cases) = catalogue();
    for (sides, expected) in cases {
        let (report, decisions) = world.spinal(MachineSettings::default(), sides);
        assert_eq!(expected, report.verdict(), "{sides:?}");
        assert_eq!(
            certified(report.verdict()),
            world.replayed(sides, report.verdict(), &decisions),
            "{sides:?}: {decisions:?}"
        );
    }
    let (world, rungs) = ladders();
    for sides in rungs {
        let (report, decisions) = world.spinal(MachineSettings::default(), sides);
        assert_eq!(MachineVerdict::Convertible, report.verdict(), "{sides:?}");
        assert_eq!(
            KernelVerdict::Convertible,
            world.replayed(sides, report.verdict(), &decisions),
            "{sides:?}: {decisions:?}"
        );
    }
}

#[test]
fn a_trace_naming_the_wrong_branch_is_refused()
{
    let (world, cases) = catalogue();
    for (sides, _) in cases {
        let (verdict, decisions) = world.traced(sides);
        let opposite = match verdict {
            MachineVerdict::Convertible => MachineVerdict::NotConvertible,
            MachineVerdict::NotConvertible => MachineVerdict::Convertible,
            MachineVerdict::Declined(reason) => MachineVerdict::Declined(reason),
        };
        assert!(
            matches!(
                world.replayed(sides, opposite, &decisions),
                KernelVerdict::Declined(ReplayDecline::Refused(_))
            ),
            "a derivation of one verdict never replays as the other: {sides:?}"
        );
    }

    let mut core = CoreArena::new();
    let first = core.value_unit();
    let second = core.value_unit();
    let zero = core.value_constant(Name::Zero.constant());
    let one = core.value_constant(Name::One.constant());
    let world = World::new(core, &[(Name::Zero, first), (Name::One, second)]);
    let sides = Sides::Values(zero, one);
    let (verdict, mut decisions) = world.traced(sides);
    let position = decisions
        .iter()
        .position(|decision| {
            matches!(*decision,
            ConversionDecision::ReduceRight { redex } if redex == named(Name::One))
        })
        .expect("the right definition unfolds before the heads meet");
    decisions[position] = ConversionDecision::ReduceLeft {
        redex: named(Name::One),
    };
    assert_eq!(
        KernelVerdict::Declined(ReplayDecline::Refused(ReplayRefusal::Inapplicable {
            at: TracePosition::from(position),
        })),
        world.replayed(sides, verdict, &decisions),
        "the right side's unfolding read on the left, where the head is already unit"
    );
}

/// The pair's first components diverge — the left one forces a
/// definition that runs Ω, at height one — and its second components
/// refute after sixteen forced unfoldings down a chain whose head starts
/// at height seventeen. A fair schedule gives the refutation every other
/// turn and answers well inside the budget; the height-weighted schedule
/// gives the shallow divergence the turns, so the same budget runs out
/// first. The machine's decline is the kernel's: it has no search of its
/// own, so it replays nothing and certifies nothing, while the fair run's
/// trace replays without ever entering the divergence.
#[test]
fn an_unlucky_schedule_declines_and_the_kernel_with_it()
{
    let mut core = CoreArena::new();
    let occurrence = innermost(&mut core);
    let self_applied = call(&mut core, occurrence, &[occurrence]);
    let lambda = core.computation_lambda(self_applied);
    let omega = core.value_thunk(lambda);
    let looping = call(&mut core, omega, &[omega]);
    let diverging = core.value_thunk(looping);
    let mut bodies = Vec::new();
    let runaway = next_constant(&mut bodies, diverging);
    let unit = core.value_unit();
    let mut deep = next_constant(&mut bodies, unit);
    for _height in 0_u32 .. 15_u32 {
        let below = core.value_constant(deep);
        deep = next_constant(&mut bodies, below);
    }
    let runaway = core.value_constant(runaway);
    let forced = core.computation_force(runaway);
    let started = core.value_thunk(forced);
    let returned = core.computation_return(unit);
    let settled = core.value_thunk(returned);
    let deep = core.value_constant(deep);
    let units = core.value_tuple(&[unit, unit]);
    let left = core.value_tuple(&[started, deep]);
    let right = core.value_tuple(&[settled, units]);
    let world = World::stacked(core, &bodies);
    let sides = Sides::Values(left, right);

    let budget = StepBudget::from(2_000_u64);
    let under = |stance| {
        MachineSettings::new(
            SchedulingPolicy::new(stance),
            GranularityPolicy::default(),
            budget,
        )
    };
    let mut log = TraceLog::new();
    let fair = world.run_under(under(SchedulingStance::UniformFair), sides, &mut log);
    assert_eq!(
        MachineVerdict::NotConvertible,
        fair.verdict(),
        "the fair schedule reaches the refutation in {} steps",
        u64::from(fair.steps())
    );
    let decisions: Vec<_> = log.decisions().copied().collect();
    assert_eq!(
        KernelVerdict::NotConvertible,
        world.replayed(sides, fair.verdict(), &decisions),
        "{decisions:?}"
    );

    let mut log = TraceLog::new();
    let starved = world.run_under(under(SchedulingStance::HeightWeighted), sides, &mut log);
    assert_eq!(
        MachineVerdict::Declined(DeclineReason::Budget),
        starved.verdict(),
        "the weighted schedule spends the budget on the divergence"
    );
    let decisions: Vec<_> = log.decisions().copied().collect();
    assert!(
        decisions.is_empty(),
        "a decline emits no derivation: {decisions:?}"
    );
    assert_eq!(
        KernelVerdict::Declined(ReplayDecline::EngineDeclined),
        world.replayed(sides, starved.verdict(), &decisions),
        "and the kernel declines with it, never reading the decline as a refutation"
    );
}

/// The unlucky schedule of
/// [`an_unlucky_schedule_declines_and_the_kernel_with_it`],
/// its sides evaluated under the spinal stance: the right side's unit is
/// reached three times and shared.
#[test]
fn an_unlucky_spinal_schedule_declines_and_the_kernel_with_it()
{
    let mut core = CoreArena::new();
    let occurrence = innermost(&mut core);
    let self_applied = call(&mut core, occurrence, &[occurrence]);
    let lambda = core.computation_lambda(self_applied);
    let omega = core.value_thunk(lambda);
    let looping = call(&mut core, omega, &[omega]);
    let diverging = core.value_thunk(looping);
    let mut bodies = Vec::new();
    let runaway = next_constant(&mut bodies, diverging);
    let unit = core.value_unit();
    let mut deep = next_constant(&mut bodies, unit);
    for _height in 0_u32 .. 15_u32 {
        let below = core.value_constant(deep);
        deep = next_constant(&mut bodies, below);
    }
    let runaway = core.value_constant(runaway);
    let forced = core.computation_force(runaway);
    let started = core.value_thunk(forced);
    let returned = core.computation_return(unit);
    let settled = core.value_thunk(returned);
    let deep = core.value_constant(deep);
    let units = core.value_tuple(&[unit, unit]);
    let left = core.value_tuple(&[started, deep]);
    let right = core.value_tuple(&[settled, units]);
    let world = World::stacked(core, &bodies);
    let sides = Sides::Values(left, right);
    assert!(
        world
            .shares(sides)
            .iter()
            .any(|&count| u64::from(count) > 0),
        "the right side reaches its unit three times"
    );

    let budget = StepBudget::from(2_000_u64);
    let under = |stance| {
        MachineSettings::new(
            SchedulingPolicy::new(stance),
            GranularityPolicy::default(),
            budget,
        )
    };
    let (fair, decisions) = world.spinal(under(SchedulingStance::UniformFair), sides);
    assert_eq!(
        MachineVerdict::NotConvertible,
        fair.verdict(),
        "the fair schedule reaches the refutation in {} steps",
        u64::from(fair.steps())
    );
    assert_eq!(
        KernelVerdict::NotConvertible,
        world.replayed(sides, fair.verdict(), &decisions),
        "{decisions:?}"
    );

    let (starved, decisions) = world.spinal(under(SchedulingStance::HeightWeighted), sides);
    assert_eq!(
        MachineVerdict::Declined(DeclineReason::Budget),
        starved.verdict(),
        "the weighted schedule spends the budget on the divergence"
    );
    assert!(
        decisions.is_empty(),
        "a decline emits no derivation: {decisions:?}"
    );
    assert_eq!(
        KernelVerdict::Declined(ReplayDecline::EngineDeclined),
        world.replayed(sides, starved.verdict(), &decisions),
        "and the kernel declines with it, never reading the decline as a refutation"
    );
}

#[test]
fn support_store_refusals_preserve_state_and_inactive_operations_do_nothing()
{
    let missing = ProcessId(usize::MAX);
    let mut inactive =
        crate::resharing::Supports::new(gandr_kernel_check_memo::MemoActivity::Inactive);
    let untouched = inactive.clone();
    inactive
        .open(missing)
        .expect("inactive support stores no process");
    inactive
        .enter(missing)
        .expect("inactive support records no entry");
    inactive
        .unfolded(missing, ConstantIndex::from(0_usize))
        .expect("inactive support records no unfolding");
    inactive
        .settle(missing, crate::rules::Settled::Convertible, &[missing])
        .expect("inactive support records no basis");
    assert_eq!(untouched, inactive);
    assert_eq!(0, usize::from(inactive.totals().acceptance()));
    assert_eq!(0, usize::from(inactive.totals().refusal()));

    let mut active = crate::resharing::Supports::new(gandr_kernel_check_memo::MemoActivity::Active);
    let fault = Err(crate::ConversionFault::MachineInvariant);
    let empty = active.clone();
    assert_eq!(fault, active.open(ProcessId(1)));
    assert_eq!(empty, active);
    active.open(ProcessId(0)).expect("zero is the next id");
    let opened = active.clone();
    assert_eq!(fault, active.open(ProcessId(0)));
    assert_eq!(fault, active.open(ProcessId(2)));
    assert_eq!(fault, active.enter(ProcessId(1)));
    assert_eq!(
        fault,
        active.unfolded(ProcessId(1), ConstantIndex::from(0_usize))
    );
    assert_eq!(
        fault,
        active.settle(ProcessId(0), crate::rules::Settled::Convertible, &[
            ProcessId(1)
        ])
    );
    assert_eq!(
        fault,
        active.settle(ProcessId(1), crate::rules::Settled::Convertible, &[])
    );
    assert_eq!(opened, active, "every refusal preserves existing support");
    active.enter(ProcessId(0)).expect("the process is open");
    active
        .unfolded(ProcessId(0), ConstantIndex::from(0_usize))
        .expect("the process is open");
    active
        .unfolded(ProcessId(0), ConstantIndex::from(0_usize))
        .expect("an edge can be consulted again");
    active
        .settle(ProcessId(0), crate::rules::Settled::Convertible, &[])
        .expect("the process is open");
    assert_eq!(1, usize::from(active.totals().acceptance()));
    assert_eq!(0, usize::from(active.totals().refusal()));
}

#[test]
fn support_entries_reference_entries_and_inherit_inner_edges()
{
    let mut supports =
        crate::resharing::Supports::new(gandr_kernel_check_memo::MemoActivity::Active);
    let [root, inner, child, next] = [ProcessId(0), ProcessId(1), ProcessId(2), ProcessId(3)];
    for process in [root, inner, child, next] {
        supports.open(process).expect("process ids are consecutive");
    }
    for process in [root, child, next] {
        supports.enter(process).expect("each process is open");
    }
    supports
        .unfolded(root, ConstantIndex::from(0_usize))
        .expect("the root lives");
    for _ in 0_u32 .. 2_u32 {
        supports
            .unfolded(inner, ConstantIndex::from(0_usize))
            .expect("the inner process lives");
    }
    supports
        .unfolded(child, ConstantIndex::from(1_usize))
        .expect("the child lives");
    supports
        .settle(inner, crate::rules::Settled::Convertible, &[])
        .expect("the inner process lives");
    assert_eq!(
        0,
        usize::from(supports.totals().acceptance()),
        "inner support is not an entry total"
    );
    supports
        .settle(child, crate::rules::Settled::Convertible, &[])
        .expect("the child lives");
    assert_eq!(1, usize::from(supports.totals().acceptance()));
    supports
        .settle(root, crate::rules::Settled::NotConvertible, &[
            inner, child, inner, child,
        ])
        .expect("every basis process lives");
    assert_eq!(1, usize::from(supports.totals().acceptance()));
    assert_eq!(
        2,
        usize::from(supports.totals().refusal()),
        "one inherited unfolding and one referenced entry, without duplicates"
    );
    supports
        .settle(next, crate::rules::Settled::Convertible, &[root])
        .expect("the root entry lives");
    assert_eq!(
        2,
        usize::from(supports.totals().acceptance()),
        "the root contributes one reference, not its two edges"
    );
    assert_eq!(2, usize::from(supports.totals().refusal()));
}

#[test]
fn derivation_refusals_preserve_state_and_inactive_recording_is_empty()
{
    let core = CoreArena::new();
    let mut domain = DomainArena::new();
    let value = domain.value_unit(crate::TermFace::Reduced);
    let pair = (crate::Glued::Value(value), crate::Glued::Value(value));
    let marker = ConversionDecision::ComparedShared {
        left: TraceNode::Value(value),
        right: TraceNode::Value(value),
    };
    let missing = ProcessId(usize::MAX);
    let mut inactive =
        crate::derivation::Derivations::new(gandr_kernel_conversion_trace::SinkActivity::Inactive);
    let original = inactive.clone();
    inactive
        .open(missing)
        .expect("inactive recording stores no process");
    inactive
        .decide(missing, marker)
        .expect("inactive recording stores no decision");
    inactive
        .rest_on(missing, Vec::from([missing]))
        .expect("inactive recording stores no children");
    inactive
        .agree_on(missing, pair, Vec::from([missing]))
        .expect("inactive recording stores no pair");
    let mut log = TraceLog::new();
    log.record(marker);
    inactive
        .emit(&core, &domain, missing, &mut log)
        .expect("inactive recording traverses nothing");
    assert_eq!(original, inactive);
    assert_eq!(0, usize::from(inactive.count()));
    assert_eq!(
        Vec::from([marker]),
        log.decisions().copied().collect::<Vec<_>>()
    );

    let mut active =
        crate::derivation::Derivations::new(gandr_kernel_conversion_trace::SinkActivity::Active);
    let empty = active.clone();
    let fault = Err(crate::ConversionFault::MachineInvariant);
    assert_eq!(fault, active.open(ProcessId(1)));
    assert_eq!(empty, active);
    active.open(ProcessId(0)).expect("zero is the next id");
    let opened = active.clone();
    assert_eq!(fault, active.open(ProcessId(0)));
    assert_eq!(fault, active.open(ProcessId(2)));
    assert_eq!(fault, active.decide(ProcessId(1), marker));
    assert_eq!(fault, active.rest_on(ProcessId(1), Vec::new()));
    assert_eq!(fault, active.agree_on(ProcessId(1), pair, Vec::new()));
    assert_eq!(fault, active.emit(&core, &domain, ProcessId(1), &mut log));
    assert_eq!(opened, active);
    assert_eq!(1, usize::from(active.count()));
    assert_eq!(
        Vec::from([marker]),
        log.decisions().copied().collect::<Vec<_>>()
    );
}

#[test]
fn derivations_emit_preorder_and_repeat_shared_children()
{
    let core = CoreArena::new();
    let mut domain = DomainArena::new();
    let [zero, one, two, three, four] =
        [0_u32, 1, 2, 3, 4].map(|_| domain.value_unit(crate::TermFace::Reduced));
    let [start, later, first, second, shared] =
        [zero, one, two, three, four].map(|value| ConversionDecision::ComparedShared {
            left: TraceNode::Value(value),
            right: TraceNode::Value(value),
        });
    let [root, left, right, leaf] = [ProcessId(0), ProcessId(1), ProcessId(2), ProcessId(3)];
    let mut derivations =
        crate::derivation::Derivations::new(gandr_kernel_conversion_trace::SinkActivity::Active);
    for process in [root, left, right, leaf] {
        derivations.open(process).expect("ids are consecutive");
    }
    for (process, decision) in [
        (root, start),
        (root, later),
        (left, first),
        (right, second),
        (leaf, shared),
    ] {
        derivations
            .decide(process, decision)
            .expect("the process is open");
    }
    derivations
        .rest_on(left, Vec::from([leaf]))
        .expect("the left process is open");
    derivations
        .rest_on(right, Vec::from([leaf]))
        .expect("the right process is open");
    derivations
        .rest_on(root, Vec::from([left, right]))
        .expect("the root is open");
    let mut log = TraceLog::new();
    derivations
        .emit(&core, &domain, root, &mut log)
        .expect("the derivation graph is closed");
    assert_eq!(
        Vec::from([start, later, first, shared, second, shared]),
        log.decisions().copied().collect::<Vec<_>>()
    );
    assert_eq!(4, usize::from(derivations.count()));
    derivations
        .rest_on(right, Vec::from([ProcessId(4)]))
        .expect("the parent process is open");
    let mut broken = TraceLog::new();
    assert_eq!(
        Err(crate::ConversionFault::MachineInvariant),
        derivations.emit(&core, &domain, root, &mut broken)
    );
    assert_eq!(
        Vec::from([start, later, first, shared, second]),
        broken.decisions().copied().collect::<Vec<_>>(),
        "a missing child refuses after the preceding preorder prefix"
    );
}

#[test]
fn empty_choices_refuse_instead_of_producing_a_refutation()
{
    let core = CoreArena::new();
    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut domain = DomainArena::new();
    let unit = domain.value_unit(crate::TermFace::Reduced);
    let mut scheduler = super::Scheduler::<NullMemo>::new(
        &core,
        &mut domain,
        definitions,
        MachineSettings::default(),
        gandr_kernel_conversion_trace::SinkActivity::Inactive,
        NullMemo,
    );
    for combination in [
        super::Combine::Biased(Vec::new()),
        super::Combine::Either(Vec::new()),
    ] {
        let mut goal = super::Goal {
            left: super::Slot::Ready(crate::Glued::Value(unit)),
            right: super::Slot::Ready(crate::Glued::Value(unit)),
            depth: crate::BinderLevel::from(0_u32),
            frozen: super::Frozen::default(),
            chain: super::Chain::default(),
            next: super::Next::Classify,
        };
        let root = scheduler
            .start_goal(goal.clone())
            .expect("the pending goal is admitted");
        assert_eq!(
            Err(crate::ConversionFault::MachineInvariant),
            scheduler.combine(root, &mut goal, combination)
        );
        assert_eq!(Ok(super::Outcome::Pending), scheduler.outcome(root));
    }
    let mut goal = super::Goal {
        left: super::Slot::Ready(crate::Glued::Value(unit)),
        right: super::Slot::Ready(crate::Glued::Value(unit)),
        depth: crate::BinderLevel::from(0_u32),
        frozen: super::Frozen::default(),
        chain: super::Chain::default(),
        next: super::Next::Classify,
    };
    let root = scheduler
        .start_goal(goal.clone())
        .expect("the zero-premise goal is admitted");
    assert_eq!(
        Ok(super::Turn::Done),
        scheduler.combine(root, &mut goal, super::Combine::All {
            pair: (crate::Glued::Value(unit), crate::Glued::Value(unit)),
            children: Vec::new(),
            collapse: super::Collapse::Allowed,
        })
    );
    assert_eq!(
        Ok(super::Outcome::Settled(super::Settled::Convertible)),
        scheduler.outcome(root)
    );
}

#[test]
fn step_counter_overflow_cannot_disable_the_budget_backstop()
{
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let first_body = core.computation_return(unit);
    let second_body = core.computation_return(unit);
    let first = core.value_thunk(first_body);
    let second = core.value_thunk(second_body);
    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut domain = DomainArena::new();
    let left = eval_value(&core, &mut domain, definitions, Fuel::from(8_u32), first)
        .expect("the first thunk evaluates");
    let right = eval_value(&core, &mut domain, definitions, Fuel::from(8_u32), second)
        .expect("the second thunk evaluates");
    let settings = MachineSettings::new(
        SchedulingPolicy::default(),
        GranularityPolicy::default(),
        StepBudget::from(u64::MAX),
    );
    for (other, expected) in [
        (right, MachineVerdict::Declined(DeclineReason::Budget)),
        (left, MachineVerdict::Convertible),
    ] {
        let mut scheduler = super::Scheduler::<NullMemo>::new(
            &core,
            &mut domain,
            definitions,
            settings,
            gandr_kernel_conversion_trace::SinkActivity::Inactive,
            NullMemo,
        );
        let root = scheduler
            .start_fresh(
                crate::resharing::SupportSides::Heads(
                    crate::Glued::Value(left),
                    crate::Glued::Value(other),
                ),
                crate::BinderLevel::from(0_u32),
            )
            .expect("the root goal is admitted");
        scheduler.spent = super::StepCount(u64::MAX);
        assert_eq!(
            Ok(expected),
            scheduler.run(root),
            "a pending root must not run past an overflow; an answer on the same turn still wins"
        );
    }
}

#[test]
fn binder_ceiling_is_refused_before_opening_or_eta_allocation()
{
    for eta in [false, true] {
        for memo in [false, true] {
            let mut core = CoreArena::new();
            let unit = core.value_unit();
            let returned = core.computation_return(unit);
            let left = core.computation_lambda(returned);
            let right = if eta {
                let rigid = core.value_constant(Name::Rigid.constant());
                core.computation_force(rigid)
            }
            else {
                let pair = core.value_tuple(&[unit, unit]);
                let returned = core.computation_return(pair);
                core.computation_lambda(returned)
            };
            let chain = LoweredChain::new();
            let environment = DefinitionalEnvironment::new();
            let definitions = Definitions::new(&chain, &environment, environment.root());
            let mut domain = DomainArena::new();
            let left = eval_computation(&core, &mut domain, definitions, Fuel::from(32_u32), left)
                .expect("the lambda evaluates without entering its binder");
            let right =
                eval_computation(&core, &mut domain, definitions, Fuel::from(32_u32), right)
                    .expect("the other head evaluates without entering its binder");
            let problem =
                Problem::computations(left, right).under(crate::BinderLevel::from(u32::MAX));
            let mark = domain.watermark();
            let result = if memo {
                decide::<_, ResharingMemo>(
                    &core,
                    &mut domain,
                    definitions,
                    MachineSettings::default(),
                    problem,
                    &mut NullSink,
                )
            }
            else {
                decide::<_, NullMemo>(
                    &core,
                    &mut domain,
                    definitions,
                    MachineSettings::default(),
                    problem,
                    &mut NullSink,
                )
            };
            assert_eq!(
                Err(crate::ConversionFault::MachineInvariant),
                result,
                "eta={eta}, memo={memo}"
            );
            assert_eq!(
                mark,
                domain.watermark(),
                "an impossible deeper level mints no fresh variable"
            );
        }
    }
}

#[test]
fn completed_premises_wake_a_later_decomposition()
{
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let body = core.computation_return(unit);
    let first = core.value_thunk(body);
    let other_unit = core.value_unit();
    let other_body = core.computation_return(other_unit);
    let second = core.value_thunk(other_body);
    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut domain = DomainArena::new();
    let left = eval_value(&core, &mut domain, definitions, Fuel::from(32_u32), first)
        .expect("the first thunk evaluates");
    let right = eval_value(&core, &mut domain, definitions, Fuel::from(32_u32), second)
        .expect("the second thunk evaluates");
    let mut left_tail = domain.value_tuple([left, left], crate::TermFace::Reduced);
    let mut right_tail = domain.value_tuple([right, right], crate::TermFace::Reduced);
    let padding = domain.value_unit(crate::TermFace::Reduced);
    for _depth in 0_u32 .. 8_u32 {
        left_tail = domain.value_tuple([padding, left_tail], crate::TermFace::Reduced);
        right_tail = domain.value_tuple([padding, right_tail], crate::TermFace::Reduced);
    }
    let left_root = domain.value_tuple([left, left_tail], crate::TermFace::Reduced);
    let right_root = domain.value_tuple([right, right_tail], crate::TermFace::Reduced);
    let problem = Problem::values(left_root, right_root);
    let mut independent = domain.clone();
    let reshared = decide::<_, ResharingMemo>(
        &core,
        &mut domain,
        definitions,
        MachineSettings::default(),
        problem,
        &mut NullSink,
    )
    .expect("the shared run remains well formed");
    let memoless = decide::<_, NullMemo>(
        &core,
        &mut independent,
        definitions,
        MachineSettings::default(),
        problem,
        &mut NullSink,
    )
    .expect("the independent run remains well formed");
    assert_eq!(MachineVerdict::Convertible, memoless.verdict());
    assert_eq!(
        MachineVerdict::Convertible,
        reshared.verdict(),
        "completed premises cannot send another wakeup and must not become a cycle"
    );
}

#[test]
fn invalid_roots_refuse_before_identity_or_search()
{
    let mut core = CoreArena::new();
    let source = core.value_unit();
    let returned = core.computation_return(source);
    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut domain = DomainArena::new();
    let mark = domain.watermark();
    let value = eval_value(&core, &mut domain, definitions, Fuel::from(8_u32), source)
        .expect("the value evaluates before truncation");
    let computation =
        eval_computation(&core, &mut domain, definitions, Fuel::from(8_u32), returned)
            .expect("the computation evaluates before truncation");
    domain.truncate_to(mark);
    for (problem, expected) in [
        (
            Problem::values(value, value),
            crate::ConversionFault::Domain(crate::DomainFault::Dangling),
        ),
        (
            Problem::computations(computation, computation),
            crate::ConversionFault::Domain(crate::DomainFault::Dangling),
        ),
        (
            Problem {
                left: crate::Glued::Value(value),
                right: crate::Glued::Computation(computation),
                depth: crate::BinderLevel::FLOOR,
            },
            crate::ConversionFault::Polarity,
        ),
    ] {
        assert_eq!(
            Err(expected),
            decide::<_, ResharingMemo>(
                &core,
                &mut domain,
                definitions,
                MachineSettings::default(),
                problem,
                &mut NullSink
            )
        );
    }
}

#[test]
fn missing_processes_refuse_without_creating_waits()
{
    let core = CoreArena::new();
    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut domain = DomainArena::new();
    let unit = domain.value_unit(crate::TermFace::Reduced);
    let mut scheduler = super::Scheduler::<NullMemo>::new(
        &core,
        &mut domain,
        definitions,
        MachineSettings::default(),
        gandr_kernel_conversion_trace::SinkActivity::Inactive,
        NullMemo,
    );
    let missing = ProcessId(0);
    assert_eq!(
        Err(crate::ConversionFault::MachineInvariant),
        scheduler.resolve(super::Slot::Waiting(missing))
    );
    assert_eq!(
        Err(crate::ConversionFault::MachineInvariant),
        scheduler.need(missing)
    );
    assert_eq!(
        Err(crate::ConversionFault::MachineInvariant),
        scheduler.enqueue(missing)
    );
    assert!(
        scheduler.queue.is_empty(),
        "refused processes cannot acquire a queued wakeup"
    );
    let share = scheduler.share_at(super::DefinitionHeight::default());
    let answered = scheduler
        .start(
            super::Work::Spent,
            super::Outcome::Settled(super::Settled::Convertible),
            share,
        )
        .expect("a completed process is admitted");
    let missing = ProcessId(usize::MAX);
    assert_eq!(
        Ok(super::Outcome::Settled(super::Settled::Convertible)),
        scheduler.depend(missing, answered),
        "an answered dependency needs no waiter lookup or edge"
    );
    assert_eq!(
        Err(crate::ConversionFault::MachineInvariant),
        scheduler.resolve(super::Slot::Waiting(answered)),
        "a goal verdict cannot be received as an evaluated head"
    );
    let pending = scheduler
        .start_goal(super::Goal {
            left: super::Slot::Ready(crate::Glued::Value(unit)),
            right: super::Slot::Ready(crate::Glued::Value(unit)),
            depth: crate::BinderLevel::FLOOR,
            frozen: super::Frozen::default(),
            chain: super::Chain::default(),
            next: super::Next::Classify,
        })
        .expect("a pending goal is admitted");
    assert_eq!(
        Err(crate::ConversionFault::MachineInvariant),
        scheduler.depend(missing, pending)
    );
    assert!(
        scheduler
            .process(pending)
            .expect("the dependency remains live")
            .waiters
            .is_empty(),
        "a missing waiter cannot leave a reciprocal edge"
    );
    scheduler
        .enqueue(pending)
        .expect("the first wakeup is queued");
    scheduler
        .enqueue(pending)
        .expect("a repeated wakeup coalesces");
    assert_eq!(
        alloc::collections::VecDeque::from([pending]),
        scheduler.queue
    );
}

#[test]
fn combinators_preserve_answer_and_decline_precedence()
{
    #[derive(Clone, Copy, Debug)]
    enum Combinator
    {
        All,
        Biased,
        Either,
    }
    let accepted = super::Outcome::Settled(super::Settled::Convertible);
    let refuted = super::Outcome::Settled(super::Settled::NotConvertible);
    let pending = super::Outcome::Pending;
    let cycle = super::Outcome::Declined(DeclineReason::Cycle);
    let budget = super::Outcome::Declined(DeclineReason::Budget);
    let cases: &[(Combinator, &[super::Outcome], super::Outcome)] = &[
        (Combinator::All, &[pending, refuted], refuted),
        (Combinator::All, &[cycle, refuted], refuted),
        (Combinator::All, &[accepted, pending], pending),
        (Combinator::All, &[cycle, pending], pending),
        (Combinator::All, &[accepted, accepted], accepted),
        (Combinator::All, &[cycle, budget], cycle),
        (Combinator::All, &[pending, refuted, pending], refuted),
        (Combinator::All, &[accepted, cycle, budget], cycle),
        (Combinator::Biased, &[accepted, pending], accepted),
        (Combinator::Biased, &[refuted, pending], pending),
        (Combinator::Biased, &[pending, refuted], refuted),
        (Combinator::Biased, &[pending, cycle], pending),
        (Combinator::Biased, &[cycle, budget], budget),
        (Combinator::Biased, &[pending, accepted, pending], accepted),
        (Combinator::Either, &[pending, accepted], accepted),
        (Combinator::Either, &[refuted, pending], pending),
        (Combinator::Either, &[cycle, pending], pending),
        (Combinator::Either, &[refuted, refuted], refuted),
        (Combinator::Either, &[cycle, budget], cycle),
        (Combinator::Either, &[pending, accepted, pending], accepted),
        (Combinator::Either, &[refuted, cycle, budget], cycle),
    ];
    for &(kind, inputs, expected) in cases {
        let core = CoreArena::new();
        let chain = LoweredChain::new();
        let environment = DefinitionalEnvironment::new();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let mut domain = DomainArena::new();
        let unit = domain.value_unit(crate::TermFace::Reduced);
        let pair = (crate::Glued::Value(unit), crate::Glued::Value(unit));
        let mut goal = super::Goal {
            left: super::Slot::Ready(pair.0),
            right: super::Slot::Ready(pair.1),
            depth: crate::BinderLevel::FLOOR,
            frozen: super::Frozen::default(),
            chain: super::Chain::default(),
            next: super::Next::Classify,
        };
        let mut scheduler = super::Scheduler::<NullMemo>::new(
            &core,
            &mut domain,
            definitions,
            MachineSettings::default(),
            gandr_kernel_conversion_trace::SinkActivity::Inactive,
            NullMemo,
        );
        let root = scheduler
            .start_goal(goal.clone())
            .expect("the parent is admitted");
        let mut children = Vec::new();
        for &outcome in inputs {
            let work = if outcome == pending {
                super::Work::Goal(goal.clone())
            }
            else {
                super::Work::Spent
            };
            let share = scheduler.share_at(super::DefinitionHeight::default());
            children.push(
                scheduler
                    .start(work, outcome, share)
                    .expect("the child state is admitted"),
            );
        }
        let combine = match kind {
            Combinator::All => super::Combine::All {
                pair,
                children,
                collapse: super::Collapse::Never,
            },
            Combinator::Biased => super::Combine::Biased(children),
            Combinator::Either => super::Combine::Either(children),
        };
        let expected_turn = if expected == pending {
            super::Turn::Wait
        }
        else {
            super::Turn::Done
        };
        assert_eq!(
            Ok(expected_turn),
            scheduler.combine(root, &mut goal, combine),
            "{kind:?}: {inputs:?}"
        );
        assert_eq!(
            Ok(expected),
            scheduler.outcome(root),
            "{kind:?}: {inputs:?}"
        );
    }
}

#[test]
fn malformed_heads_and_channel_entries_are_refused()
{
    let core = CoreArena::new();
    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut domain = DomainArena::new();
    let unit = domain.value_unit(crate::TermFace::Reduced);
    let returned = domain.comp_return(unit, crate::CompTermFace::Reduced);
    let variable = domain
        .neutral_node(
            crate::NeutralHead::Variable {
                zone: Zone::Intuitionistic,
                level: crate::BinderLevel::FLOOR,
            },
            Vec::new(),
            crate::Unfolding::Rigid,
        )
        .expect("a variable is rigid");
    let module = domain
        .neutral_node(
            crate::NeutralHead::Module(Name::Zero.constant()),
            Vec::new(),
            crate::Unfolding::Rigid,
        )
        .expect("a module is rigid");
    let rigid = domain
        .neutral_node(
            crate::NeutralHead::Constant(Name::Rigid.constant()),
            Vec::new(),
            crate::Unfolding::Rigid,
        )
        .expect("an opaque constant is rigid");
    let wrong_body = domain
        .neutral_node(
            crate::NeutralHead::Constant(Name::Zero.constant()),
            Vec::new(),
            crate::Unfolding::Forced(crate::Glued::Computation(returned)),
        )
        .expect("the domain can hold a computation unfolding");
    let mark = domain.watermark();
    let stale_value = domain.value_unit(crate::TermFace::Reduced);
    let stale_computation = domain.comp_return(unit, crate::CompTermFace::Reduced);
    let stale_neutral = domain
        .neutral_node(
            crate::NeutralHead::Constant(Name::One.constant()),
            Vec::new(),
            crate::Unfolding::Rigid,
        )
        .expect("the later neutral initially resolves");
    domain.truncate_to(mark);
    let mut scheduler = super::Scheduler::<NullMemo>::new(
        &core,
        &mut domain,
        definitions,
        MachineSettings::default(),
        gandr_kernel_conversion_trace::SinkActivity::Inactive,
        NullMemo,
    );
    for head in [
        crate::Glued::Value(unit),
        crate::Glued::Computation(returned),
    ] {
        assert_eq!(
            Err(crate::ConversionFault::MachineInvariant),
            scheduler.neutral_of(head)
        );
    }
    for head in [
        crate::Glued::Value(stale_value),
        crate::Glued::Computation(stale_computation),
    ] {
        assert_eq!(
            Err(crate::ConversionFault::Domain(crate::DomainFault::Dangling)),
            scheduler.neutral_of(head)
        );
    }
    for head in [variable, module] {
        assert_eq!(
            Err(crate::ConversionFault::MachineInvariant),
            scheduler.head_constant(head)
        );
        assert_eq!(
            Err(crate::ConversionFault::MachineInvariant),
            scheduler.unfold_channel(head)
        );
    }
    assert_eq!(
        Err(crate::ConversionFault::Domain(crate::DomainFault::Dangling)),
        scheduler.head_constant(stale_neutral)
    );
    assert_eq!(
        Err(crate::ConversionFault::Domain(crate::DomainFault::Dangling)),
        scheduler.unfold_channel(stale_neutral)
    );
    for head in [rigid, wrong_body] {
        assert_eq!(
            Err(crate::ConversionFault::MachineInvariant),
            scheduler.unfold_channel(head)
        );
    }
    assert_eq!(
        Err(crate::ConversionFault::Evaluation(
            crate::EvalFault::DanglingTerm
        )),
        scheduler.body_channel(GlobalIndex::from(0_u32), super::DefinitionHeight::default())
    );
}

#[test]
fn opened_channels_preserve_distinct_binder_levels()
{
    let mut core = CoreArena::new();
    let variable = innermost(&mut core);
    let returned = core.computation_return(variable);
    let lambda = core.computation_lambda(returned);
    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut domain = DomainArena::new();
    let lambda = eval_computation(&core, &mut domain, definitions, Fuel::from(16_u32), lambda)
        .expect("the lambda suspends its binder body");
    let Some(&crate::DomainComp::Lambda { body, .. }) = domain.computation(lambda)
    else {
        panic!("the evaluated head is a lambda");
    };
    let mut scheduler = super::Scheduler::<NullMemo>::new(
        &core,
        &mut domain,
        definitions,
        MachineSettings::default(),
        gandr_kernel_conversion_trace::SinkActivity::Inactive,
        NullMemo,
    );
    for level in [0_u32, 1_u32, 0_u32] {
        let level = crate::BinderLevel::from(level);
        let channel = scheduler
            .open_channel(body, level, super::Opening::One)
            .expect("the closure opens at this level");
        if scheduler.outcome(channel) == Ok(super::Outcome::Pending) {
            assert_eq!(Ok(super::Turn::Done), scheduler.turn(channel));
        }
        let Ok(super::Outcome::Evaluated(crate::Glued::Computation(result))) =
            scheduler.outcome(channel)
        else {
            panic!("the opening channel returns a computation");
        };
        let Some(&crate::DomainComp::Return { value, .. }) = scheduler.domain.computation(result)
        else {
            panic!("the body returns its fresh variable");
        };
        let Some(&crate::DomainValue::Neutral { neutral, .. }) = scheduler.domain.value(value)
        else {
            panic!("the returned variable remains neutral");
        };
        assert_eq!(
            crate::NeutralHead::Variable {
                zone: Zone::Intuitionistic,
                level
            },
            scheduler
                .domain
                .neutral(neutral)
                .expect("the fresh neutral resolves")
                .head()
        );
    }
    assert_eq!(
        2_usize,
        scheduler.processes.len(),
        "a completed opening at the same level is reused"
    );
}

#[test]
fn head_height_is_symmetric_and_nonconstants_stay_at_the_floor()
{
    let mut core = CoreArena::new();
    let body = core.value_unit();
    let first = core.value_constant(Name::Zero.constant());
    let second = core.value_constant(Name::One.constant());
    let first_force = core.computation_force(first);
    let second_force = core.computation_force(second);
    let world = World::stacked(core, &[
        (GlobalIndex::from(0_u32), body),
        (GlobalIndex::from(1_u32), body),
    ]);
    let definitions = Definitions::new(&world.chain, &world.environment, world.environment.root());
    let mut domain = DomainArena::new();
    let first = eval_value(
        &world.core,
        &mut domain,
        definitions,
        Fuel::from(16_u32),
        first,
    )
    .expect("the first head evaluates");
    let second = eval_value(
        &world.core,
        &mut domain,
        definitions,
        Fuel::from(16_u32),
        second,
    )
    .expect("the second head evaluates");
    let first_force = eval_computation(
        &world.core,
        &mut domain,
        definitions,
        Fuel::from(16_u32),
        first_force,
    )
    .expect("the first force is neutral");
    let second_force = eval_computation(
        &world.core,
        &mut domain,
        definitions,
        Fuel::from(16_u32),
        second_force,
    )
    .expect("the second force is neutral");
    let unit = domain.value_unit(crate::TermFace::Reduced);
    let scheduler = super::Scheduler::<NullMemo>::new(
        &world.core,
        &mut domain,
        definitions,
        MachineSettings::default(),
        gandr_kernel_conversion_trace::SinkActivity::Inactive,
        NullMemo,
    );
    for (left, right) in [
        (crate::Glued::Value(first), crate::Glued::Value(second)),
        (
            crate::Glued::Computation(first_force),
            crate::Glued::Computation(second_force),
        ),
    ] {
        for pair in [(left, right), (right, left)] {
            assert_eq!(
                2_u32,
                u32::from(scheduler.pair_height(pair).expect("both heads resolve"))
            );
        }
    }
    assert_eq!(
        0_u32,
        u32::from(
            scheduler
                .pair_height((crate::Glued::Value(unit), crate::Glued::Value(unit)))
                .expect("formers have floor height")
        )
    );
}

#[test]
fn lifting_shares_equal_trees_without_reusing_occurrence_nodes()
{
    let mut core = CoreArena::new();
    let first = core.value_unit();
    let second = core.value_unit();
    let left = core.value_tuple(&[first, second]);
    let third = core.value_unit();
    let fourth = core.value_unit();
    let right = core.value_tuple(&[third, fourth]);
    let root = core.value_tuple(&[left, right]);
    let mut world = World::new(core, &[]);
    assert_eq!(
        [0_u64, 0_u64],
        world.shares(Sides::Values(first, second)).map(u64::from)
    );
    assert_eq!(
        [2_u64, 2_u64],
        world.shares(Sides::Values(root, root)).map(u64::from),
        "the repeated unit and repeated pair each have one shared leg"
    );
    let (overlay, lifted_root) = lifted(&world.core, CoreTerm::Value(root));
    assert_eq!(
        Ok(()),
        overlay.validate(lifted_root),
        "each occurrence is a distinct overlay node"
    );
    let OverlayId::Value(lifted_root) = lifted_root
    else {
        panic!("a value lifts to a value");
    };
    let erased = crate::overlay::erase_value(&overlay, lifted_root, &mut world.core)
        .expect("the lifted tree erases");
    let Some(&[first, second]) = world.core.value(erased).and_then(Value::components)
    else {
        panic!("the root is still a pair");
    };
    assert_eq!(first, second, "erasure reuses the shared pair leg");
    let Some(&[first, second]) = world.core.value(first).and_then(Value::components)
    else {
        panic!("each component is still a pair");
    };
    assert_eq!(first, second, "erasure reuses the shared unit leg");
    assert_eq!(Some(&Value::unit()), world.core.value(first));
}

#[test]
fn closed_codes_are_certified_in_both_type_families()
{
    let mut core = CoreArena::new();
    let first_unit = core.value_type_unit();
    let second_unit = core.value_type_unit();
    let first_returner = core.comp_type_returner(first_unit);
    let second_returner = core.comp_type_returner(second_unit);
    let first_arrow = core.comp_type_arrow(first_unit, first_returner);
    let second_arrow = core.comp_type_arrow(second_unit, second_returner);
    let first_thunk = core.value_type_thunk(first_returner);
    let second_thunk = core.value_type_thunk(second_returner);
    let first_value_code = core.value_quote(first_thunk);
    let second_value_code = core.value_quote(second_thunk);
    let first_comp_code = core.value_quote_computation(first_arrow);
    let second_comp_code = core.value_quote_computation(second_arrow);
    let different_comp_code = core.value_quote_computation(first_returner);
    let first = core.computation_return(first_comp_code);
    let second = core.computation_return(second_comp_code);
    let world = World::new(core, &[]);
    for (sides, expected) in [
        (
            Sides::Values(first_value_code, second_value_code),
            MachineVerdict::Convertible,
        ),
        (
            Sides::Values(first_comp_code, second_comp_code),
            MachineVerdict::Convertible,
        ),
        (
            Sides::Values(first_comp_code, different_comp_code),
            MachineVerdict::NotConvertible,
        ),
        (
            Sides::Computations(first, second),
            MachineVerdict::Convertible,
        ),
    ] {
        let (verdict, decisions) = world.traced(sides);
        assert_eq!(expected, verdict, "{sides:?}");
        assert_eq!(
            certified(expected),
            world.replayed(sides, verdict, &decisions),
            "{sides:?}: {decisions:?}"
        );
    }
}

#[test]
fn native_records_cases_and_traces_agree()
{
    use alloc::string::String;

    use gandr_core_term::ConstructorTag;
    use gandr_core_term::FieldLabel;
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let other_unit = core.value_unit();
    let x = FieldLabel::from(String::from("x"));
    let y = FieldLabel::from(String::from("y"));
    let record = core.value_record(BTreeMap::from([(x.clone(), unit), (y.clone(), unit)]));
    let repeated_record = core.value_record(BTreeMap::from([
        (x.clone(), other_unit),
        (y.clone(), other_unit),
    ]));
    let narrow = core.value_record(BTreeMap::from([(x.clone(), unit)]));
    let data = core.value_type_data(ConstantIndex::from(2_usize), Vec::from([unit]));
    let repeated_type = core.value_type_data(ConstantIndex::from(2_usize), Vec::from([other_unit]));
    let other_type = core.value_type_data(ConstantIndex::from(3_usize), Vec::from([unit]));
    let constructor =
        core.value_constructor(data, ConstructorTag::from(0_usize), Vec::from([record]));
    let repeated_constructor = core.value_constructor(
        repeated_type,
        ConstructorTag::from(0_usize),
        Vec::from([repeated_record]),
    );
    let other_tag =
        core.value_constructor(data, ConstructorTag::from(1_usize), Vec::from([record]));
    let other_constructor = core.value_constructor(
        other_type,
        ConstructorTag::from(0_usize),
        Vec::from([record]),
    );
    let bound = innermost(&mut core);
    let identity = core.computation_return(bound);
    let branch = core.computation_lambda(identity);
    let unit_type = core.value_type_unit();
    let record_type = core.value_type_record(BTreeMap::from([
        (x.clone(), unit_type),
        (y.clone(), unit_type),
    ]));
    let motive = core.comp_type_returner(record_type);
    let named_data = core.value_constant(Name::Zero.constant());
    let named_record = core.value_constant(Name::One.constant());
    let fired = core.computation_data_case(named_data, motive, Vec::from([branch]));
    let expected_record = core.computation_return(record);
    let projection = core.computation_record_projection(named_record, x.clone());
    let expected_unit = core.computation_return(unit);
    let rigid = core.value_constant(Name::Rigid.constant());
    let motive_type = core.value_type_data(ConstantIndex::from(3_usize), Vec::from([bound]));
    let dependent_motive = core.comp_type_returner(motive_type);
    let reconstructed =
        core.value_constructor(data, ConstructorTag::from(0_usize), Vec::from([bound]));
    let result_type =
        core.value_type_data(ConstantIndex::from(3_usize), Vec::from([reconstructed]));
    let result = core.value_constructor(
        result_type,
        ConstructorTag::from(0_usize),
        Vec::from([unit]),
    );
    let different_result = core.value_constructor(
        result_type,
        ConstructorTag::from(1_usize),
        Vec::from([unit]),
    );
    let result = core.computation_return(result);
    let different_result = core.computation_return(different_result);
    let result = core.computation_lambda(result);
    let different_result = core.computation_lambda(different_result);
    let first_case = core.computation_data_case(rigid, dependent_motive, Vec::from([result]));
    let repeated_case = core.computation_data_case(rigid, dependent_motive, Vec::from([result]));
    let changed_case =
        core.computation_data_case(rigid, dependent_motive, Vec::from([different_result]));
    let empty_case = core.computation_data_case(rigid, dependent_motive, Vec::new());
    let outer = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let outer_type = core.value_type_data(ConstantIndex::from(3_usize), Vec::from([outer]));
    let outer_motive = core.comp_type_returner(outer_type);
    let outer_case = core.computation_data_case(rigid, outer_motive, Vec::from([result]));
    let under_binder = core.computation_lambda(first_case);
    let capturing_motive = core.computation_lambda(outer_case);
    let rigid_projection = core.computation_record_projection(rigid, x.clone());
    let repeated_projection = core.computation_record_projection(rigid, x);
    let other_projection = core.computation_record_projection(rigid, y);
    let world = World::new(core, &[(Name::Zero, constructor), (Name::One, record)]);
    for (sides, expected) in [
        (
            Sides::Values(record, repeated_record),
            MachineVerdict::Convertible,
        ),
        (
            Sides::Values(record, narrow),
            MachineVerdict::NotConvertible,
        ),
        (
            Sides::Values(constructor, repeated_constructor),
            MachineVerdict::Convertible,
        ),
        (
            Sides::Values(constructor, other_tag),
            MachineVerdict::NotConvertible,
        ),
        (
            Sides::Values(constructor, other_constructor),
            MachineVerdict::NotConvertible,
        ),
        (
            Sides::Computations(fired, expected_record),
            MachineVerdict::Convertible,
        ),
        (
            Sides::Computations(projection, expected_unit),
            MachineVerdict::Convertible,
        ),
        (
            Sides::Computations(first_case, repeated_case),
            MachineVerdict::Convertible,
        ),
        (
            Sides::Computations(first_case, changed_case),
            MachineVerdict::NotConvertible,
        ),
        (
            Sides::Computations(first_case, empty_case),
            MachineVerdict::NotConvertible,
        ),
        (
            Sides::Computations(under_binder, capturing_motive),
            MachineVerdict::NotConvertible,
        ),
        (
            Sides::Computations(rigid_projection, repeated_projection),
            MachineVerdict::Convertible,
        ),
        (
            Sides::Computations(rigid_projection, other_projection),
            MachineVerdict::NotConvertible,
        ),
    ] {
        let (verdict, decisions) = world.traced(sides);
        assert_eq!(verdict, expected, "{sides:?}");
        assert_eq!(
            world.replayed(sides, verdict, &decisions),
            certified(expected),
            "{sides:?}: {decisions:?}"
        );
    }
}

/// Tuple projections compute to the component at their position, and two
/// projections stuck on one neutral compare by component, never as a
/// record projection of the same operand; the kernel replays each verdict.
#[test]
fn tuple_projections_of_one_neutral_compare_by_component()
{
    use alloc::string::String;

    use gandr_core_term::Component;
    use gandr_core_term::FieldLabel;
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let left = core.value_injection(gandr_core_term::Summand::from(0_usize), unit);
    let pair = core.value_tuple(&[unit, unit]);
    let components = [unit, left, pair];
    let tuple = core.value_tuple(&components);
    let named_tuple = core.value_constant(Name::Zero.constant());
    let mut sides = Vec::new();
    for (position, component) in components.into_iter().enumerate() {
        let projection = core.computation_tuple_projection(named_tuple, Component::from(position));
        let returned = core.computation_return(component);
        sides.push((
            Sides::Computations(projection, returned),
            MachineVerdict::Convertible,
        ));
    }
    let first = core.computation_tuple_projection(named_tuple, Component::from(0_usize));
    let returned_left = core.computation_return(left);
    sides.push((
        Sides::Computations(first, returned_left),
        MachineVerdict::NotConvertible,
    ));
    let rigid = core.value_constant(Name::Rigid.constant());
    let rigid_first = core.computation_tuple_projection(rigid, Component::from(0_usize));
    let repeated_first = core.computation_tuple_projection(rigid, Component::from(0_usize));
    let rigid_second = core.computation_tuple_projection(rigid, Component::from(1_usize));
    let labelled = core.computation_record_projection(rigid, FieldLabel::from(String::from("0")));
    sides.extend([
        (
            Sides::Computations(rigid_first, repeated_first),
            MachineVerdict::Convertible,
        ),
        (
            Sides::Computations(rigid_first, rigid_second),
            MachineVerdict::NotConvertible,
        ),
        (
            Sides::Computations(rigid_first, labelled),
            MachineVerdict::NotConvertible,
        ),
    ]);
    let world = World::new(core, &[(Name::Zero, tuple)]);
    for (sides, expected) in sides {
        let (verdict, decisions) = world.traced(sides);
        assert_eq!(verdict, expected, "{sides:?}");
        assert_eq!(
            world.replayed(sides, verdict, &decisions),
            certified(expected),
            "{sides:?}: {decisions:?}"
        );
    }
}

/// A tuple of a neutral's own projections converts to the neutral, on either
/// side, and a record of its own fields likewise; swapped projections, a
/// different neutral and a record missing a field stay apart. The kernel
/// replays each verdict (#715).
#[test]
fn a_tuple_of_a_neutrals_projections_is_the_neutral_715()
{
    use alloc::collections::BTreeMap;
    use alloc::string::String;

    use gandr_core_term::Component;
    use gandr_core_term::FieldLabel;
    let mut core = CoreArena::new();
    let rigid = core.value_constant(Name::Rigid.constant());
    let other = core.value_constant(Name::Zero.constant());
    let projected = |core: &mut CoreArena, position: usize| {
        let projection = core.computation_tuple_projection(rigid, Component::from(position));
        core.value_returned(projection)
    };
    let first = projected(&mut core, 0_usize);
    let second = projected(&mut core, 1_usize);
    let expanded = core.value_tuple(&[first, second]);
    let swapped = core.value_tuple(&[second, first]);
    let field = |core: &mut CoreArena, label: &str| {
        let projection =
            core.computation_record_projection(rigid, FieldLabel::from(String::from(label)));
        core.value_returned(projection)
    };
    let left = field(&mut core, "l");
    let right = field(&mut core, "r");
    let record = core.value_record(BTreeMap::from([
        (FieldLabel::from(String::from("l")), left),
        (FieldLabel::from(String::from("r")), right),
    ]));
    let crossed = core.value_record(BTreeMap::from([
        (FieldLabel::from(String::from("l")), right),
        (FieldLabel::from(String::from("r")), left),
    ]));
    let world = World::new(core, &[]);
    for (sides, expected) in [
        (Sides::Values(expanded, rigid), MachineVerdict::Convertible),
        (Sides::Values(rigid, expanded), MachineVerdict::Convertible),
        (Sides::Values(record, rigid), MachineVerdict::Convertible),
        (Sides::Values(rigid, record), MachineVerdict::Convertible),
        (
            Sides::Values(swapped, rigid),
            MachineVerdict::NotConvertible,
        ),
        (
            Sides::Values(crossed, rigid),
            MachineVerdict::NotConvertible,
        ),
        (
            Sides::Values(expanded, other),
            MachineVerdict::NotConvertible,
        ),
    ] {
        let (verdict, decisions) = world.traced(sides);
        assert_eq!(verdict, expected, "{sides:?}");
        assert_eq!(
            world.replayed(sides, verdict, &decisions),
            certified(expected),
            "{sides:?}: {decisions:?}"
        );
    }
}

/// A split computes on the tuple a definition unfolds to, and two splits
/// stuck on one neutral compare by arity and by their bodies opened under
/// one variable per component. The kernel has no split, so the verdicts
/// are not replayed: checked splits reach it as the projection binds it
/// judges itself.
#[test]
fn stuck_splits_compare_by_arity_and_body()
{
    use gandr_core_term::ComponentCount;
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let left = core.value_injection(gandr_core_term::Summand::from(0_usize), unit);
    let pair = core.value_tuple(&[unit, unit]);
    let tuple = core.value_tuple(&[unit, left, pair]);
    let named_tuple = core.value_constant(Name::Zero.constant());
    let rigid = core.value_constant(Name::Rigid.constant());
    let innermost = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let outer = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let middle = core.computation_return(outer);
    let last = core.computation_return(innermost);
    let three = ComponentCount::from(3_usize);
    let two = ComponentCount::from(2_usize);
    let computed = core.computation_split(named_tuple, three, middle);
    let returned_left = core.computation_return(left);
    let returned_pair = core.computation_return(pair);
    let stuck = core.computation_split(rigid, two, last);
    let repeated = core.computation_split(rigid, two, last);
    let other_component = core.computation_split(rigid, two, middle);
    let other_arity = core.computation_split(rigid, three, last);
    let world = World::new(core, &[(Name::Zero, tuple)]);
    for (sides, expected) in [
        (
            Sides::Computations(computed, returned_left),
            MachineVerdict::Convertible,
        ),
        (
            Sides::Computations(computed, returned_pair),
            MachineVerdict::NotConvertible,
        ),
        (
            Sides::Computations(stuck, repeated),
            MachineVerdict::Convertible,
        ),
        (
            Sides::Computations(stuck, other_component),
            MachineVerdict::NotConvertible,
        ),
        (
            Sides::Computations(stuck, other_arity),
            MachineVerdict::NotConvertible,
        ),
    ] {
        assert_eq!(world.traced(sides).0, expected, "{sides:?}");
    }
}

/// A goal comparing `unit` with itself at the floor, nothing frozen, still to
/// classify.
///
/// # Specification
/// trivial.
fn bare_goal(unit: crate::DomainValueId) -> super::Goal
{
    super::Goal {
        left: super::Slot::Ready(crate::Glued::Value(unit)),
        right: super::Slot::Ready(crate::Glued::Value(unit)),
        depth: crate::BinderLevel::FLOOR,
        frozen: super::Frozen::default(),
        chain: super::Chain::default(),
        next: super::Next::Classify,
    }
}

#[test]
fn a_dependency_is_needed_exactly_while_a_needed_waiter_holds_it()
{
    let core = CoreArena::new();
    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut domain = DomainArena::new();
    let unit = domain.value_unit(crate::TermFace::Reduced);
    let mut scheduler = super::Scheduler::<NullMemo>::new(
        &core,
        &mut domain,
        definitions,
        MachineSettings::default(),
        gandr_kernel_conversion_trace::SinkActivity::Inactive,
        NullMemo,
    );
    let waiter = scheduler
        .start_goal(bare_goal(unit))
        .expect("a goal is admitted");
    let dependency = scheduler
        .start_goal(bare_goal(unit))
        .expect("a goal is admitted");
    let demand = |scheduler: &super::Scheduler<'_, NullMemo>| {
        scheduler
            .process(dependency)
            .expect("the dependency is live")
            .demand
    };
    assert_eq!(
        Ok(super::Outcome::Pending),
        scheduler.depend(waiter, dependency)
    );
    assert_eq!(
        super::Demand(0_u32),
        demand(&scheduler),
        "a dormant waiter passes on no need"
    );
    scheduler.need(waiter).expect("the waiter is live");
    assert_eq!(
        super::Demand(1_u32),
        demand(&scheduler),
        "its first need wakes what it waits on"
    );
    scheduler.need(waiter).expect("the waiter is live");
    assert_eq!(
        super::Demand(1_u32),
        demand(&scheduler),
        "a second need passes nothing on"
    );
    scheduler.unneed(waiter).expect("the waiter is live");
    assert_eq!(
        super::Demand(1_u32),
        demand(&scheduler),
        "returning one of two needs keeps the dependency needed"
    );
    scheduler.unneed(waiter).expect("the waiter is live");
    assert_eq!(
        super::Demand(0_u32),
        demand(&scheduler),
        "returning the last releases it"
    );
}

#[test]
fn a_finished_process_releases_only_the_needs_it_passed_and_wakes_only_needed_waiters()
{
    let core = CoreArena::new();
    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut domain = DomainArena::new();
    let unit = domain.value_unit(crate::TermFace::Reduced);
    let mut scheduler = super::Scheduler::<NullMemo>::new(
        &core,
        &mut domain,
        definitions,
        MachineSettings::default(),
        gandr_kernel_conversion_trace::SinkActivity::Inactive,
        NullMemo,
    );
    let mut started = || {
        scheduler
            .start_goal(bare_goal(unit))
            .expect("a goal is admitted")
    };
    let [needed, dormant, dependency] = [started(), started(), started()];
    for waiter in [needed, dormant] {
        assert_eq!(
            Ok(super::Outcome::Pending),
            scheduler.depend(waiter, dependency)
        );
    }
    scheduler.need(needed).expect("the waiter is live");
    let settled = super::Outcome::Settled(super::Settled::Convertible);
    let demand = |scheduler: &super::Scheduler<'_, NullMemo>| {
        scheduler
            .process(dependency)
            .expect("the dependency is live")
            .demand
    };

    let other = scheduler
        .start_goal(bare_goal(unit))
        .expect("a goal is admitted");
    assert_eq!(
        Ok(super::Outcome::Pending),
        scheduler.depend(other, dependency)
    );
    scheduler
        .finish(other, settled)
        .expect("the process is live");
    assert_eq!(
        super::Demand(1_u32),
        demand(&scheduler),
        "a process that passed on no need returns none"
    );
    scheduler
        .finish(dependency, settled)
        .expect("the process is live");
    assert_eq!(
        Some(&super::Queued::Absent),
        scheduler.queued.get(dormant.0),
        "a dormant waiter stays asleep when what it waits on answers"
    );
    assert_eq!(
        Some(&super::Queued::Present),
        scheduler.queued.get(needed.0),
        "a needed one is queued"
    );

    let holder = scheduler
        .start_goal(bare_goal(unit))
        .expect("a goal is admitted");
    let held = scheduler
        .start_goal(bare_goal(unit))
        .expect("a goal is admitted");
    assert_eq!(Ok(super::Outcome::Pending), scheduler.depend(holder, held));
    scheduler.need(holder).expect("the holder is live");
    scheduler
        .finish(holder, settled)
        .expect("the process is live");
    assert_eq!(
        super::Demand(0_u32),
        scheduler
            .process(held)
            .expect("the dependency is live")
            .demand,
        "a needed process returns the need it passed when it answers"
    );
}

#[test]
fn the_run_passes_over_unneeded_work_and_takes_a_unit_share_at_once()
{
    let core = CoreArena::new();
    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut domain = DomainArena::new();
    let unit = domain.value_unit(crate::TermFace::Reduced);
    let mut scheduler = super::Scheduler::<NullMemo>::new(
        &core,
        &mut domain,
        definitions,
        MachineSettings::default(),
        gandr_kernel_conversion_trace::SinkActivity::Inactive,
        NullMemo,
    );
    let dormant = scheduler
        .start_goal(bare_goal(unit))
        .expect("a goal is admitted");
    let root = scheduler
        .start_goal(bare_goal(unit))
        .expect("a goal is admitted");
    let behind = scheduler
        .start_goal(bare_goal(unit))
        .expect("a goal is admitted");
    scheduler.enqueue(dormant).expect("the process is live");
    scheduler.enqueue(root).expect("the process is live");
    scheduler.need(behind).expect("the process is live");
    assert_eq!(Ok(MachineVerdict::Convertible), scheduler.run(root));
    let process = |id| scheduler.process(id).expect("the process is live");
    assert_eq!(
        super::Outcome::Pending,
        process(dormant).outcome,
        "a queued process nothing needs takes no turn"
    );
    assert_eq!(
        super::Credit(0_u32),
        process(behind).credit,
        "a root of share one takes its turn at its first pop, before the process queued \
         behind it is reached"
    );
}

#[test]
fn a_run_under_a_budget_equal_to_its_steps_answers()
{
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let returned = core.computation_return(unit);
    let body = core.value_thunk(returned);
    let head = core.value_constant(Name::Zero.constant());
    let forced = core.computation_force(head);
    let expected = core.computation_return(unit);
    let world = World::new(core, &[(Name::Zero, body)]);
    let sides = Sides::Computations(forced, expected);
    let under = |budget| {
        MachineSettings::new(
            SchedulingPolicy::default(),
            GranularityPolicy::default(),
            StepBudget::from(budget),
        )
    };
    let ample = world.run_under(under(1_000_u64), sides, &mut NullSink);
    assert_eq!(MachineVerdict::Convertible, ample.verdict());
    assert!(
        u64::from(ample.steps()) > 0_u64,
        "forcing the definition is charged"
    );
    let exact = world.run_under(under(u64::from(ample.steps())), sides, &mut NullSink);
    assert_eq!(
        MachineVerdict::Convertible,
        exact.verdict(),
        "spending exactly the budget is not exceeding it"
    );
}

#[test]
fn a_decomposition_waits_only_while_no_premise_refutes_and_one_is_pending()
{
    use crate::resharing::SupportSides;
    use crate::rules::Subgoal;

    let core = CoreArena::new();
    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut domain = DomainArena::new();
    let [
        unit,
        refuted_left,
        refuted_right,
        open_left,
        open_right,
        alone_left,
        alone_right,
    ] = [(); 7].map(|()| domain.value_unit(crate::TermFace::Reduced));
    let mut scheduler = super::Scheduler::<ResharingMemo>::new(
        &core,
        &mut domain,
        definitions,
        MachineSettings::default(),
        gandr_kernel_conversion_trace::SinkActivity::Inactive,
        ResharingMemo::new(),
    );
    let refuted = scheduler
        .start_fresh(
            SupportSides::Heads(
                crate::Glued::Value(refuted_left),
                crate::Glued::Value(refuted_right),
            ),
            crate::BinderLevel::FLOOR,
        )
        .expect("a goal is admitted");
    scheduler
        .finish(
            refuted,
            super::Outcome::Settled(super::Settled::NotConvertible),
        )
        .expect("the premise is live");
    let pair = (crate::Glued::Value(unit), crate::Glued::Value(unit));
    let mut decomposed = |subgoals| {
        let mut goal = bare_goal(unit);
        let parent = scheduler
            .start_goal(bare_goal(unit))
            .expect("a goal is admitted");
        scheduler
            .decompose(parent, &mut goal, pair, subgoals, super::Collapse::Allowed)
            .expect("the premises start")
    };
    assert_eq!(
        super::Turn::Again,
        decomposed(Vec::from([
            Subgoal::Values(refuted_left, refuted_right),
            Subgoal::Values(open_left, open_right),
        ])),
        "a recalled refutation is polled at once, though a sibling is pending"
    );
    assert_eq!(
        super::Turn::Wait,
        decomposed(Vec::from([Subgoal::Values(alone_left, alone_right)])),
        "a pending premise alone is waited on"
    );
}
