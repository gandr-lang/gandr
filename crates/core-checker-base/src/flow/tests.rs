//! Session statements, runs and rides, judged and readmitted.

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec::Vec;

use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::session::RecordedMove;
use gandr_core_term::session::SessionRelation;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldLabel;

use super::Moving;
use super::computed;
use super::covariant;
use super::ride;
use super::universe;
use crate::context::CheckBudget;
use crate::context::CheckingContext;
use crate::fixture::flow::At;
use crate::fixture::flow::Branch;
use crate::fixture::flow::Seat;
use crate::fixture::flow::Word;
use crate::fixture::flow::declaration;
use crate::fixture::flow::judged;
use crate::fixture::flow::retiring;
use crate::fixture::flow::ridden;
use crate::fixture::flow::ridden_at;
use crate::fixture::flow::run;
use crate::fixture::flow::seat;
use crate::fixture::flow::statement;
use crate::fixture::flow::verdict;
use crate::refusal::CheckRefusal;
use crate::refusal::RunFault;
use crate::refusal::RunStep;
use crate::report::Verdict;

#[test]
fn each_refusal_is_named()
{
    let mut arena = CoreArena::new();
    let end = seat(&mut arena, Seat::End);
    let wide = seat(&mut arena, Seat::Wide);
    let kept = seat(&mut arena, Seat::Kept);
    let integer = arena.value_type_base(BaseType::Integer);
    let number = arena.value_quote(integer);
    let (apart, unequal) = statement(&mut arena, At(0), SessionRelation::Equivalence, (end, wide));
    let (reversed, narrower) =
        statement(&mut arena, At(1), SessionRelation::Subtyping, (wide, end));
    let (sub, _) = statement(&mut arena, At(2), SessionRelation::Subtyping, (end, wide));
    // ride(fun (X) { Flow[.A = Type](X, ⌜End⌝) }, sub, stay(⌜End⌝)) would
    // reverse `sub`.
    let sub_constant = arena.value_constant(ConstantIndex::from(2_usize));
    let code = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let type_universe = universe(&mut arena);
    let motive = arena.value_type_flow(type_universe, code, end);
    let stay = arena.value_stay(end);
    let symmetric = arena.computation_ride(motive, sub_constant, stay);
    let reverse = arena.value_type_flow(type_universe, wide, end);
    let returns = arena.comp_type_returner(reverse);
    let declared = arena.value_type_thunk(returns);
    let body = arena.value_thunk(symmetric);
    let flipped = declaration(At(3), declared, body);
    // A run that retires, ridden to a protocol that dropped the offer.
    let (keep, _) = statement(&mut arena, At(4), SessionRelation::Subtyping, (end, kept));
    let keep_constant = arena.value_constant(ConstantIndex::from(4_usize));
    let served = retiring(&mut arena);
    let (dropped, dropped_run) = ridden(&mut arena, At(5), keep_constant, served, kept);
    // A widened run that pauses, checked at the protocol without `pause`.
    let paused = run(&mut arena, &[
        RecordedMove::Received(Word::Task),
        RecordedMove::Selected(Branch::Pause.label()),
        RecordedMove::Sent(Word::Progress),
        RecordedMove::Selected(Branch::Handoff.label()),
        RecordedMove::Sent(Word::Notes),
        RecordedMove::Closed,
    ]);
    let narrow_run = arena.value_type_run(end);
    let backward = declaration(At(6), narrow_run, paused);
    let truncated = run(&mut arena, &[RecordedMove::Received(Word::Task)]);
    let short = declaration(At(7), narrow_run, truncated);
    let (unsession, _) = statement(&mut arena, At(8), SessionRelation::Subtyping, (number, end));
    // A run that sends where the protocol receives, and one that moves on
    // after its close.
    let crossed = run(&mut arena, &[RecordedMove::Sent(Word::Task)]);
    let wrong_way = declaration(At(9), narrow_run, crossed);
    let overrun = run(&mut arena, &[
        RecordedMove::Received(Word::Task),
        RecordedMove::Selected(Branch::Report.label()),
        RecordedMove::Sent(Word::Progress),
        RecordedMove::Offered(Branch::Retire.label()),
        RecordedMove::Closed,
        RecordedMove::Received(Word::Task),
    ]);
    let past_end = declaration(At(10), narrow_run, overrun);
    let report = judged(&mut arena, &[
        apart, reversed, sub, flipped, keep, dropped, backward, short, unsession, wrong_way,
        past_end,
    ]);
    let symmetric_at = symmetric;
    assert_eq!(
        [0, 1, 3, 5, 6, 7, 8, 9, 10].map(|position| verdict(&report, At(position))),
        [
            Some(Verdict::Refused(CheckRefusal::SessionNotEquivalent {
                at: unequal
            })),
            Some(Verdict::Refused(CheckRefusal::SessionNotSubtype {
                at: narrower
            })),
            Some(Verdict::Refused(CheckRefusal::NonCovariantMotive {
                at: symmetric_at
            })),
            Some(Verdict::Refused(CheckRefusal::RunNotAdmitted {
                at: dropped_run,
                fault: RunFault::WrongLabel(RunStep::from(3_u32)),
            })),
            Some(Verdict::Refused(CheckRefusal::RunNotAdmitted {
                at: paused,
                fault: RunFault::WrongLabel(RunStep::from(1_u32)),
            })),
            Some(Verdict::Refused(CheckRefusal::RunNotAdmitted {
                at: truncated,
                fault: RunFault::Incomplete(RunStep::from(1_u32)),
            })),
            Some(Verdict::Refused(CheckRefusal::SessionCodeExpected {
                at: number
            })),
            Some(Verdict::Refused(CheckRefusal::RunNotAdmitted {
                at: crossed,
                fault: RunFault::WrongDirection(RunStep::from(0_u32)),
            })),
            Some(Verdict::Refused(CheckRefusal::RunNotAdmitted {
                at: overrun,
                fault: RunFault::ResumeAfterEnd(RunStep::from(5_u32)),
            })),
        ],
        "each refusal names the engine's relation, the variance or the move: {report:?}"
    );
    assert!(
        [2, 4].iter().all(|&position| matches!(
            verdict(&report, At(position)),
            Some(Verdict::Checked { .. })
        )),
        "the two simulations the refusals ride along check"
    );
}

#[test]
fn a_prefix_rides_forward_and_refuses_by_move()
{
    let mut arena = CoreArena::new();
    let end = seat(&mut arena, Seat::End);
    let wide = seat(&mut arena, Seat::Wide);
    let kept = seat(&mut arena, Seat::Kept);
    let prefix = CoreArena::value_type_prefix;
    let (sub, _) = statement(&mut arena, At(0), SessionRelation::Subtyping, (end, wide));
    let sub_constant = arena.value_constant(ConstantIndex::from(0_usize));
    let (keep, _) = statement(&mut arena, At(1), SessionRelation::Subtyping, (end, kept));
    let keep_constant = arena.value_constant(ConstantIndex::from(1_usize));
    // A seat that reported, its offer still owed: it moves forward open, and
    // along the flow that drops `retire` too, the offer not yet taken.
    let reporting = |arena: &mut CoreArena| {
        run(arena, &[
            RecordedMove::Received(Word::Task),
            RecordedMove::Selected(Branch::Report.label()),
            RecordedMove::Sent(Word::Progress),
        ])
    };
    let open = reporting(&mut arena);
    let (forward, _) = ridden_at(&mut arena, prefix, (At(2), sub_constant, open, wide));
    let open = reporting(&mut arena);
    let (kept_open, _) = ridden_at(&mut arena, prefix, (At(3), keep_constant, open, kept));
    // The same seat after it took `retire`: the narrowed protocol refuses it
    // at that move.
    let retired = run(&mut arena, &[
        RecordedMove::Received(Word::Task),
        RecordedMove::Selected(Branch::Report.label()),
        RecordedMove::Sent(Word::Progress),
        RecordedMove::Offered(Branch::Retire.label()),
    ]);
    let (dropped, dropped_at) =
        ridden_at(&mut arena, prefix, (At(4), keep_constant, retired, kept));
    // A run motive does not move the open record.
    let open = reporting(&mut arena);
    let (unfinished, unfinished_at) = ridden(&mut arena, At(5), sub_constant, open, wide);
    let report = judged(&mut arena, &[
        sub, keep, forward, kept_open, dropped, unfinished,
    ]);
    for position in [0, 1, 2, 3] {
        assert!(
            matches!(
                verdict(&report, At(position)),
                Some(Verdict::Checked { .. })
            ),
            "declaration {position} checks: {report:?}"
        );
    }
    assert_eq!(
        [4, 5].map(|position| verdict(&report, At(position))),
        [
            Some(Verdict::Refused(CheckRefusal::RunNotAdmitted {
                at: dropped_at,
                fault: RunFault::WrongLabel(RunStep::from(3_u32)),
            })),
            Some(Verdict::Refused(CheckRefusal::RunNotAdmitted {
                at: unfinished_at,
                fault: RunFault::Incomplete(RunStep::from(3_u32)),
            })),
        ],
        "a prefix that took a dropped offer is refused at it, and an open record is no run: {report:?}"
    );
}

#[test]
fn motives_ride_only_covariantly()
{
    let mut arena = CoreArena::new();
    let end = seat(&mut arena, Seat::End);
    let type_universe = universe(&mut arena);
    let unit = arena.value_unit();
    let at = arena.computation_return(unit);
    let code = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let outer = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let runs = arena.value_type_run(code);
    let unit_type = arena.value_type_unit();
    let returns_run = arena.comp_type_returner(runs);
    let after = arena.comp_type_arrow(unit_type, returns_run);
    let codomain = arena.value_type_thunk(after);
    let returns_unit = arena.comp_type_returner(unit_type);
    let before = arena.comp_type_arrow(runs, returns_unit);
    let domain = arena.value_type_thunk(before);
    let source = arena.value_type_flow(type_universe, code, end);
    let target = arena.value_type_flow(type_universe, end, code);
    let path = arena.value_type_path(type_universe, code, code);
    let foreign = arena.value_type_run(outer);
    let pair = arena.value_type_product(&[runs, foreign]);
    let verdicts: Vec<_> = [
        runs, codomain, target, unit_type, domain, source, path, pair,
    ]
    .iter()
    .map(|&motive| covariant(&arena, at, motive))
    .collect();
    let refused = Err(CheckRefusal::NonCovariantMotive { at });
    assert_eq!(
        verdicts,
        [
            Ok(()),
            Ok(()),
            Ok(()),
            Ok(()),
            refused,
            refused,
            refused,
            Err(CheckRefusal::RideUnsupported { at }),
        ],
        "a run, an arrow's codomain, a flow's target and a motive ignoring the code ride; a domain, a flow's source and a path do not; an outer binder is unsupported"
    );
    let decoded = arena.value_type_element(code, Level::zero());
    let decoded_pair = arena.value_type_product(&[decoded, unit_type]);
    let mut fields = BTreeMap::new();
    fields.insert(FieldLabel::from(String::from("seat")), decoded);
    let record = arena.value_type_record(fields);
    let returns_decoded = arena.comp_type_returner(decoded);
    let reader = arena.comp_type_arrow(unit_type, returns_decoded);
    let suspended = arena.value_type_thunk(reader);
    let lifted = arena.value_type_element(code, Level::zero().succ().unwrap());
    let carried = arena.value_type_flow(decoded, end, code);
    let wrapped = arena.value_tuple(&[code]);
    let beside = arena.value_type_flow(type_universe, end, wrapped);
    let moved: Vec<_> = [
        decoded,
        decoded_pair,
        target,
        record,
        suspended,
        lifted,
        carried,
        beside,
    ]
    .iter()
    .map(|&motive| computed(&arena, at, motive, &Level::zero()))
    .collect();
    let unsupported = Err(CheckRefusal::RideUnsupported { at });
    assert_eq!(
        moved,
        [
            Ok(()),
            Ok(()),
            Ok(()),
            unsupported,
            unsupported,
            unsupported,
            unsupported,
            unsupported,
        ],
        "a decode of the code, a pair of it and a flow singleton compute; a record of it, a thunk returning it, a decode above level zero, a flow whose carrier reads it and one whose target only contains it do not"
    );
    let one = Level::zero().succ().unwrap();
    assert_eq!(
        [lifted, decoded].map(|motive| computed(&arena, at, motive, &one)),
        [Ok(()), unsupported],
        "along a flow one universe up, the decode at that level computes and the decode at level zero does not"
    );
}

/// The code rides beneath every covariant former — a sum, a list, a lift, a
/// staged or kept type, a lazy pair, a static Pi's or a dependent arrow's
/// codomain, a decode of a computation type — and is refused under a
/// domain, a dependent pair, a family's argument, a stack, a codata type
/// and any compound value.
#[test]
fn a_code_rides_beneath_exactly_the_covariant_formers()
{
    use gandr_core_term::effect::capability::Region;
    use gandr_core_term::effect::capability::RegionDepth;
    use gandr_kernel_term::Stage;
    use gandr_kernel_term::StageId;

    let mut arena = CoreArena::new();
    let unit = arena.value_unit();
    let at = arena.computation_return(unit);
    let unit_type = arena.value_type_unit();
    let returns_unit = arena.comp_type_returner(unit_type);
    let code = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let decoded = arena.value_type_element(code, Level::zero());
    let returns_decoded = arena.comp_type_returner(decoded);
    let lazy = arena.comp_type_with(&[returns_unit, returns_decoded]);
    let pi_codomain = arena.comp_type_pi(unit_type, returns_decoded);
    let pi_domain = arena.comp_type_pi(decoded, returns_unit);
    let decoded_computation = arena.comp_type_element(code, Level::zero());
    let wrapped = arena.value_tuple(&[code]);
    let codata = arena.comp_type_codata(ConstantIndex::from(0_usize), Vec::from([code]));
    let riding = [
        (arena.value_type_sum(&[unit_type, decoded]), "a summand"),
        (arena.value_type_list(decoded), "a list"),
        (arena.value_type_lift(decoded, Level::zero()), "a lift"),
        (
            arena.value_type_staged(decoded, Stage::At(StageId::from(0_usize))),
            "a staged type",
        ),
        (
            arena.value_type_kept(decoded, Region::Scoped(RegionDepth::from(1_u32))),
            "a kept type",
        ),
        (
            arena.value_type_static_pi(unit_type, decoded),
            "a static Pi's codomain",
        ),
        (arena.value_type_thunk(lazy), "a lazy pair"),
        (
            arena.value_type_thunk(pi_codomain),
            "a dependent arrow's codomain",
        ),
        (
            arena.value_type_thunk(decoded_computation),
            "a decoded computation type",
        ),
    ];
    let refused = [
        (
            arena.value_type_static_pi(decoded, unit_type),
            "a static Pi's domain",
        ),
        (
            arena.value_type_thunk(pi_domain),
            "a dependent arrow's domain",
        ),
        (
            arena.value_type_sigma(decoded, unit_type),
            "a dependent pair",
        ),
        (
            arena.value_type_data(ConstantIndex::from(0_usize), Vec::from([code])),
            "a family's argument",
        ),
        (
            arena.value_type_stack(returns_decoded, returns_unit),
            "a stack",
        ),
        (arena.value_type_thunk(codata), "a codata type"),
        (arena.value_type_run(wrapped), "a compound value"),
    ];
    for (motive, former) in riding {
        assert_eq!(covariant(&arena, at, motive), Ok(()), "{former}");
    }
    for (motive, former) in refused {
        assert_eq!(
            covariant(&arena, at, motive),
            Err(CheckRefusal::NonCovariantMotive { at }),
            "{former}"
        );
    }
}

/// Along a flow between two distinct session codes, a motive ignoring its
/// code rides fixed, while a decode of the code, which no run carries, is
/// unsupported.
#[test]
fn a_ride_between_session_codes_is_fixed_only_for_a_constant_motive()
{
    let mut arena = CoreArena::new();
    let end = seat(&mut arena, Seat::End);
    let wide = seat(&mut arena, Seat::Wide);
    let type_universe = universe(&mut arena);
    let flow = arena.value_type_flow(type_universe, end, wide);
    let code = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let constant = arena.value_type_unit();
    let decoded = arena.value_type_element(code, Level::zero());
    let along = arena.value_unit();
    let value = arena.value_unit();
    let [fixed, moving] =
        [constant, decoded].map(|motive| arena.computation_ride(motive, along, value));
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    assert!(
        matches!(ride(&mut context, fixed, flow), Ok(ref ridden) if ridden.moving == Moving::Fixed),
        "a motive ignoring its code rides fixed"
    );
    assert_eq!(
        ride(&mut context, moving, flow).map(|ridden| ridden.moving),
        Err(CheckRefusal::RideUnsupported { at: moving }),
        "a decode between session codes is unsupported"
    );
}

/// The type a bisimilarity's paths check against: the unit type when it owes
/// none, the one owed pair's universe path alone, and the tuple of both paths
/// in the pairs' order for two.
#[test]
fn payload_paths_check_as_unit_one_path_or_a_tuple_in_order()
{
    use gandr_core_term::Value;
    use gandr_core_term::ValueType;
    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let pair = arena.value_type_product(&[unit, unit]);
    let relates = |arena: &CoreArena,
                   path: ValueTypeId,
                   (source, target): (ValueTypeId, ValueTypeId)| {
        let quotes = |at: ValueId, ty: ValueTypeId| matches!(arena.value(at), Some(&Value::Quote(quoted)) if quoted == ty);
        matches!(
            arena.value_type(path),
            Some(&ValueType::Path { carrier, left, right })
                if matches!(arena.value_type(carrier), Some(&ValueType::Universe { .. }))
                    && quotes(left, source)
                    && quotes(right, target)
        )
    };
    let none = super::payload_paths(&mut arena, &[]);
    assert!(
        matches!(arena.value_type(none), Some(&ValueType::Product(ref components)) if components.is_empty()),
        "no owed pair checks against the unit type: {:?}",
        arena.value_type(none)
    );
    let one = super::payload_paths(&mut arena, &[(pair, unit)]);
    assert!(
        relates(&arena, one, (pair, unit)),
        "one owed pair checks against its path alone: {:?}",
        arena.value_type(one)
    );
    let two = super::payload_paths(&mut arena, &[(pair, unit), (unit, pair)]);
    let Some(&ValueType::Product(ref components)) = arena.value_type(two)
    else {
        panic!(
            "two owed pairs check against a tuple: {:?}",
            arena.value_type(two)
        );
    };
    assert!(
        matches!(**components, [first, second]
            if relates(&arena, first, (pair, unit)) && relates(&arena, second, (unit, pair))),
        "the tuple holds each pair's path in the pairs' order: {components:?}"
    );
}
