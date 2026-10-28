use gandr_kernel_conversion_trace::ConversionDecision;
use gandr_kernel_conversion_trace::NullSink;
use gandr_kernel_conversion_trace::TraceLog;
use gandr_kernel_conversion_trace::TraceSink as _;

use super::DuplicationStance;
use super::PolicyRefusal;
use super::TraceNode;
use super::TracedDuplication;

#[test]
fn the_spinal_stance_installs_only_bound_to_a_recording_sink()
{
    let mut discarding = NullSink;
    assert_eq!(
        Some(PolicyRefusal::Untraced {
            stance: DuplicationStance::Spinal,
        }),
        TracedDuplication::<NullSink>::install(DuplicationStance::Spinal, &mut discarding).err(),
        "a sink that keeps nothing cannot carry the spinal stance's derivations"
    );
    assert_eq!(
        Ok(DuplicationStance::EraseAndClone),
        TracedDuplication::install(DuplicationStance::EraseAndClone, &mut discarding)
            .map(|installed| installed.stance()),
        "the reference stance needs no trace, so any sink carries it"
    );
    let mut log = TraceLog::<TraceNode>::new();
    assert_eq!(
        Ok(DuplicationStance::Spinal),
        TracedDuplication::install(DuplicationStance::Spinal, &mut log)
            .map(|installed| installed.stance()),
        "a recording sink carries the spinal stance"
    );
    assert_eq!(
        Ok(DuplicationStance::EraseAndClone),
        TracedDuplication::install(DuplicationStance::EraseAndClone, &mut log)
            .map(|installed| installed.stance()),
        "and the reference stance with it"
    );
}

#[test]
fn trace_bound_operations_preserve_the_overlay_when_they_refuse()
{
    for stance in [DuplicationStance::EraseAndClone, DuplicationStance::Spinal] {
        let mut core = gandr_core_term::CoreArena::new();
        let chain = crate::LoweredChain::new();
        let environment = gandr_core_term::DefinitionalEnvironment::new();
        let definitions = crate::Definitions::new(&chain, &environment, environment.root());
        let mut overlay = crate::Overlay::new();
        let floor = overlay.watermark();
        let value = overlay
            .mint_value(crate::ValueNode::Grafted(crate::ValueGraft::Unit))
            .expect("the unit is closed");
        let comp = overlay
            .mint_computation(crate::CompNode::Grafted(crate::CompGraft::Return(value)))
            .expect("the value child lives");
        let before = overlay.clone();
        let mut domain = crate::DomainArena::new();
        let marker_value = domain.value_unit(crate::TermFace::Reduced);
        let marker = ConversionDecision::ComparedShared {
            left: TraceNode::Value(marker_value),
            right: TraceNode::Value(marker_value),
        };
        let mut log = TraceLog::new();
        log.record(marker);
        {
            let installed = TracedDuplication::install(stance, &mut log)
                .expect("a recording sink carries both stances");
            assert_eq!(
                Err(crate::OverlayEvalFault::Evaluation(
                    crate::EvalFault::OutOfFuel
                )),
                installed.eval_overlay_value(
                    &mut overlay,
                    &mut core,
                    &mut domain,
                    definitions,
                    crate::Fuel::from(0_u32),
                    value
                )
            );
            assert_eq!(before, overlay);
            assert_eq!(
                Err(crate::OverlayEvalFault::Evaluation(
                    crate::EvalFault::OutOfFuel
                )),
                installed.eval_overlay_computation(
                    &mut overlay,
                    &mut core,
                    &mut domain,
                    definitions,
                    crate::Fuel::from(0_u32),
                    comp
                )
            );
            assert_eq!(before, overlay);
            overlay.truncate_to(floor);
            let missing = overlay.clone();
            assert!(matches!(
                installed.duplicate_value(&mut overlay, &core, value),
                Err(crate::DuplicationFault::Refused(_))
            ));
            assert_eq!(missing, overlay);
            assert!(matches!(
                installed.duplicate_computation(&mut overlay, &core, comp),
                Err(crate::DuplicationFault::Refused(_))
            ));
            assert_eq!(missing, overlay);
        }
        assert_eq!(
            alloc::vec::Vec::from([marker]),
            log.decisions().copied().collect::<alloc::vec::Vec<_>>(),
            "evaluation and refused duplication preserve the bound trace"
        );
    }
}

#[test]
fn a_bound_trace_records_verdicts_but_not_declines()
{
    for stance in [DuplicationStance::EraseAndClone, DuplicationStance::Spinal] {
        let mut core = gandr_core_term::CoreArena::new();
        let source = core.value_unit();
        let returned = core.computation_return(source);
        let thunk = core.value_thunk(returned);
        let forced = core.computation_force(thunk);
        let mut domain = crate::DomainArena::new();
        let left_closure = domain.comp_closure_node(returned, crate::Environment::new());
        let right_closure = domain.comp_closure_node(forced, crate::Environment::new());
        let left = domain.comp_lambda(left_closure, crate::CompTermFace::Reduced);
        let right = domain.comp_lambda(right_closure, crate::CompTermFace::Reduced);
        let first = domain.value_unit(crate::TermFace::Reduced);
        let second = domain.value_unit(crate::TermFace::Reduced);
        let pair = domain.value_tuple([first, first], crate::TermFace::Reduced);
        let chain = crate::LoweredChain::new();
        let environment = gandr_core_term::DefinitionalEnvironment::new();
        let definitions = crate::Definitions::new(&chain, &environment, environment.root());
        let settings = crate::MachineSettings::default();
        let no_steps = crate::MachineSettings::new(
            crate::SchedulingPolicy::default(),
            crate::GranularityPolicy::default(),
            crate::StepBudget::from(0_u64),
        );
        let marker = ConversionDecision::ComparedShared {
            left: TraceNode::Value(second),
            right: TraceNode::Value(second),
        };
        let mut log = TraceLog::new();
        log.record(marker);
        {
            let mut installed = TracedDuplication::install(stance, &mut log)
                .expect("the recording sink carries the stance");
            let equal = installed
                .decide::<crate::ResharingMemo>(
                    &core,
                    &mut domain,
                    definitions,
                    settings,
                    crate::Problem::values(first, second),
                )
                .expect("the equal pair lives");
            assert_eq!(crate::MachineVerdict::Convertible, equal.verdict());
            let apart = installed
                .decide::<crate::ResharingMemo>(
                    &core,
                    &mut domain,
                    definitions,
                    settings,
                    crate::Problem::values(first, pair),
                )
                .expect("the apart pair lives");
            assert_eq!(crate::MachineVerdict::NotConvertible, apart.verdict());
            let declined = installed
                .decide::<crate::ResharingMemo>(
                    &core,
                    &mut domain,
                    definitions,
                    no_steps,
                    crate::Problem::computations(left, right),
                )
                .expect("exhaustion declines rather than refusing the input");
            assert_eq!(
                crate::MachineVerdict::Declined(crate::DeclineReason::Budget),
                declined.verdict()
            );
        }
        assert_eq!(
            alloc::vec::Vec::from([
                marker,
                ConversionDecision::ComparedShared {
                    left: TraceNode::Value(first),
                    right: TraceNode::Value(second)
                },
                ConversionDecision::ComparedShared {
                    left: TraceNode::Value(first),
                    right: TraceNode::Value(pair)
                },
            ]),
            log.decisions().copied().collect::<alloc::vec::Vec<_>>()
        );
    }
}
