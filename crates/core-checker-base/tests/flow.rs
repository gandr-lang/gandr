//! Session statements, runs and rides, judged and readmitted through the
//! bridge.

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;

use gandr_core_checker_base::context::CheckBudget;
use gandr_core_checker_base::context::CheckingContext;
use gandr_core_checker_base::fixture::flow::At;
use gandr_core_checker_base::fixture::flow::Branch;
use gandr_core_checker_base::fixture::flow::Seat;
use gandr_core_checker_base::fixture::flow::Word;
use gandr_core_checker_base::fixture::flow::declaration;
use gandr_core_checker_base::fixture::flow::judged;
use gandr_core_checker_base::fixture::flow::retiring;
use gandr_core_checker_base::fixture::flow::ridden;
use gandr_core_checker_base::fixture::flow::run;
use gandr_core_checker_base::fixture::flow::seat;
use gandr_core_checker_base::fixture::flow::session_code;
use gandr_core_checker_base::fixture::flow::statement;
use gandr_core_checker_base::fixture::flow::texted;
use gandr_core_checker_base::fixture::flow::verdict;
use gandr_core_checker_base::flow::universe;
use gandr_core_checker_base::refusal::CheckRefusal;
use gandr_core_checker_base::refusal::RunFault;
use gandr_core_checker_base::refusal::RunStep;
use gandr_core_checker_base::refusal::UnadmittedFormer;
use gandr_core_checker_base::report::Verdict;
use gandr_core_checker_bridge::bridge;
use gandr_core_checker_bridge::bridge::Outcome;
use gandr_core_term::CoreArena;
use gandr_core_term::Sort;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::session::DialogueMove;
use gandr_core_term::session::Endpoint;
use gandr_core_term::session::PayloadCount;
use gandr_core_term::session::PayloadSlot;
use gandr_core_term::session::Protocol;
use gandr_core_term::session::ProtocolState;
use gandr_core_term::session::ProtocolSyntax;
use gandr_core_term::session::RecordedMove;
use gandr_core_term::session::SessionRelation;
use gandr_core_term::session::SessionType;
use gandr_kernel_strata::Level;
use gandr_kernel_strata::LevelConstant;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::DeclarationContent;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::Literal;
use gandr_kernel_term::StringLiteral;
use gandr_kernel_term::Value as KernelValue;
use quenchant_shape::shape::Maybe;

/// A dialogue of `turns`, in log order, each payload a string.
///
/// # Specification
/// trivial.
fn dialogue(
    arena: &mut CoreArena,
    turns: &[(Endpoint, RecordedMove<Word>)],
) -> ValueId
{
    let moves: Vec<DialogueMove> = turns
        .iter()
        .map(|&(endpoint, ref movement)| DialogueMove {
            endpoint,
            movement: texted(arena, movement),
        })
        .collect();
    arena.value_dialogue(Arc::from(moves))
}

#[test]
fn statements_decide_by_the_engine_and_replay()
{
    let mut arena = CoreArena::new();
    let end = seat(&mut arena, Seat::End);
    let twice = seat(&mut arena, Seat::Twice);
    let wide = seat(&mut arena, Seat::Wide);
    let (eq, bisimilar) = statement(
        &mut arena,
        At(0),
        SessionRelation::Equivalence,
        (end, twice),
    );
    let (sub, similar) = statement(&mut arena, At(1), SessionRelation::Subtyping, (end, wide));
    let module = [eq, sub];
    let report = judged(&mut arena, &module);
    assert!(
        report
            .judged()
            .iter()
            .all(|judged| matches!(judged.verdict(), Verdict::Checked { .. })),
        "a protocol and its renamed unfolding are bisimilar, and a widened selection simulates: {report:?}"
    );
    let relations: Vec<_> = [bisimilar, similar]
        .iter()
        .map(|at| {
            report
                .flows()
                .get(at)
                .map(gandr_core_checker_base::flow::Statement::relation)
        })
        .collect();
    assert_eq!(relations, [
        Some(SessionRelation::Equivalence),
        Some(SessionRelation::Subtyping)
    ]);
    let readmission = bridge::readmit(&mut arena, &report);
    assert!(
        readmission
            .readmitted()
            .iter()
            .all(|entry| matches!(entry.outcome(), Outcome::Defined { .. })),
        "the kernel replays the engine's pairs against the erased graphs: {:?}",
        readmission.readmitted()
    );
    let artifact = gandr_kernel_term::decode(readmission.export(BTreeMap::new()).as_image())
        .expect("the certificates persist");
    let bodies: Vec<_> = artifact
        .declarations()
        .iter()
        .filter_map(|marked| match *marked.declaration().content() {
            DeclarationContent::Def { body, .. } => artifact.arena().value(body).cloned(),
            DeclarationContent::Data { .. }
            | DeclarationContent::Codata { .. }
            | DeclarationContent::Axiom { .. }
            | DeclarationContent::LiteralIdentity { .. }
            | DeclarationContent::AbstractType { .. } => None,
        })
        .collect();
    let recorded = |at: ValueId| {
        report
            .flows()
            .get(&at)
            .map(|statement| Arc::clone(statement.evidence()))
    };
    assert!(
        matches!(
            bodies.as_slice(),
            [KernelValue::SessionPath { evidence: path, .. }, KernelValue::SessionFlow { evidence: flow, .. }]
                if Some(Arc::clone(path)) == recorded(bisimilar) && Some(Arc::clone(flow)) == recorded(similar)
        ),
        "each statement persists as the kernel's certificate over the engine's pairs: {bodies:?}"
    );
    let mut environment = gandr_kernel_core::Environment::new();
    for (position, marked) in artifact.declarations().iter().enumerate() {
        let mut staging = environment.stage();
        if position == 0 {
            *staging.arena() = artifact.arena().clone();
        }
        let DeclarationContent::Def { declared, body } = *marked.declaration().content()
        else {
            panic!("each statement persists as a definition");
        };
        let staged = staging.def(marked.declaration().levels().clone(), declared, body);
        environment
            .add_decl(staged)
            .expect("a fresh kernel replays each persisted certificate");
    }
    assert_eq!(environment.entries().len(), 2);
}

#[test]
fn a_run_rides_forward_and_refuses_by_move()
{
    let mut arena = CoreArena::new();
    let end = seat(&mut arena, Seat::End);
    let wide = seat(&mut arena, Seat::Wide);
    let kept = seat(&mut arena, Seat::Kept);
    let (sub, _) = statement(&mut arena, At(0), SessionRelation::Subtyping, (end, wide));
    let served = retiring(&mut arena);
    let narrow_run = arena.value_type_run(end);
    let recorded = declaration(At(1), narrow_run, served);
    let sub_constant = arena.value_constant(ConstantIndex::from(0_usize));
    let served_constant = arena.value_constant(ConstantIndex::from(1_usize));
    let (moved, _) = ridden(&mut arena, At(2), sub_constant, served_constant, wide);
    // An open run rides a flow that narrows no offer, but not one that does.
    let open = |arena: &mut CoreArena, position: At, flow: usize, target: ValueId| {
        let flow = arena.value_constant(ConstantIndex::from(flow));
        let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let code = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let motive = arena.value_type_run(code);
        let ride = arena.computation_ride(motive, flow, bound);
        let lambda = arena.computation_lambda(ride);
        let body = arena.value_thunk(lambda);
        let source = arena.value_type_run(end);
        let result = arena.value_type_run(target);
        let returner = arena.comp_type_returner(result);
        let arrow = arena.comp_type_arrow(source, returner);
        let declared = arena.value_type_thunk(arrow);
        (declaration(position, declared, body), bound)
    };
    let (forward, _) = open(&mut arena, At(3), 0, wide);
    let (keep, _) = statement(&mut arena, At(4), SessionRelation::Subtyping, (end, kept));
    let (narrowing, bound) = open(&mut arena, At(5), 4, kept);
    // A stay rides as the identity at any covariant motive.
    let stay = arena.value_stay(end);
    let (fixed, _) = ridden(&mut arena, At(6), stay, served_constant, end);
    let report = judged(&mut arena, &[
        sub, recorded, moved, forward, keep, narrowing, fixed,
    ]);
    for position in [0, 1, 2, 3, 4, 6] {
        assert!(
            matches!(
                verdict(&report, At(position)),
                Some(Verdict::Checked { .. })
            ),
            "declaration {position} checks: {report:?}"
        );
    }
    assert_eq!(
        verdict(&report, At(5)),
        Some(Verdict::Refused(CheckRefusal::RunNotAdmitted {
            at: bound,
            fault: RunFault::OfferNarrowed,
        })),
        "an open run may retire, which the narrowed protocol does not offer"
    );
    let readmission = bridge::readmit(&mut arena, &report);
    let outcomes: Vec<_> = readmission
        .readmitted()
        .iter()
        .map(|entry| entry.outcome().clone())
        .collect();
    assert!(
        matches!(outcomes.first(), Some(Outcome::Defined { .. })),
        "the simulation crosses: {outcomes:?}"
    );
    assert!(
        [1, 2, 3].iter().all(|&position| matches!(
            outcomes.get(position),
            Some(Outcome::Refused(bridge::Refusal::OutOfFragment {
                former: UnadmittedFormer::Run,
                ..
            }))
        )),
        "runs and rides stay on the checker's side, moved by the recorded-run consumer: {outcomes:?}"
    );
}

#[test]
fn a_dialogue_checks_by_its_web_and_refuses_by_move()
{
    use Endpoint::Left;
    use Endpoint::Right;
    let mut arena = CoreArena::new();
    let end = seat(&mut arena, Seat::End);
    let played = arena.value_type_dialogue(end);
    let report = || RecordedMove::Selected(Branch::Report.label());
    let offered = |branch: Branch| RecordedMove::Offered(branch.label());
    let retire = || RecordedMove::Selected(Branch::Retire.label());
    // The seat reports once and retires, its report logged before the
    // operator takes the choice, then after it: one dialogue.
    let first = dialogue(&mut arena, &[
        (Right, RecordedMove::Sent(Word::Task)),
        (Left, RecordedMove::Received(Word::Task)),
        (Left, report()),
        (Left, RecordedMove::Sent(Word::Progress)),
        (Right, offered(Branch::Report)),
        (Right, RecordedMove::Received(Word::Progress)),
        (Right, retire()),
        (Left, offered(Branch::Retire)),
        (Left, RecordedMove::Closed),
        (Right, RecordedMove::Closed),
    ]);
    let second = dialogue(&mut arena, &[
        (Right, RecordedMove::Sent(Word::Task)),
        (Left, RecordedMove::Received(Word::Task)),
        (Left, report()),
        (Right, offered(Branch::Report)),
        (Left, RecordedMove::Sent(Word::Progress)),
        (Right, RecordedMove::Received(Word::Progress)),
        (Right, retire()),
        (Left, offered(Branch::Retire)),
        (Right, RecordedMove::Closed),
        (Left, RecordedMove::Closed),
    ]);
    let (first_constant, second_constant) = (
        arena.value_constant(ConstantIndex::from(0_usize)),
        arena.value_constant(ConstantIndex::from(1_usize)),
    );
    let commuted = arena.value_type_path(played, first_constant, second_constant);
    let reflexivity = arena.value_here(first_constant);
    // The seat's receipt logged before the operator's send.
    let inverted = dialogue(&mut arena, &[
        (Left, RecordedMove::Received(Word::Task)),
        (Right, RecordedMove::Sent(Word::Task)),
        (Left, report()),
        (Left, RecordedMove::Sent(Word::Progress)),
        (Right, offered(Branch::Report)),
        (Right, RecordedMove::Received(Word::Progress)),
        (Right, retire()),
        (Left, offered(Branch::Retire)),
        (Left, RecordedMove::Closed),
        (Right, RecordedMove::Closed),
    ]);
    // The seat hears other than the task sent.
    let misheard = dialogue(&mut arena, &[
        (Right, RecordedMove::Sent(Word::Task)),
        (Left, RecordedMove::Received(Word::Progress)),
        (Left, report()),
        (Left, RecordedMove::Sent(Word::Progress)),
        (Right, offered(Branch::Report)),
        (Right, RecordedMove::Received(Word::Progress)),
        (Right, retire()),
        (Left, offered(Branch::Retire)),
        (Left, RecordedMove::Closed),
        (Right, RecordedMove::Closed),
    ]);
    // The seat selects the report, the operator offers the hand-off: each
    // endpoint follows its protocol, and the two do not agree.
    let misoffered = dialogue(&mut arena, &[
        (Right, RecordedMove::Sent(Word::Task)),
        (Left, RecordedMove::Received(Word::Task)),
        (Left, report()),
        (Left, RecordedMove::Sent(Word::Progress)),
        (Right, offered(Branch::Handoff)),
        (Right, RecordedMove::Received(Word::Notes)),
        (Left, offered(Branch::Retire)),
        (Left, RecordedMove::Closed),
        (Right, RecordedMove::Closed),
    ]);
    // The seat sends where its protocol receives.
    let crossed = dialogue(&mut arena, &[
        (Left, RecordedMove::Sent(Word::Task)),
        (Right, RecordedMove::Received(Word::Task)),
        (Left, RecordedMove::Closed),
        (Right, RecordedMove::Closed),
    ]);
    // The dialogue logged up to the retirement, neither endpoint closed.
    let short = dialogue(&mut arena, &[
        (Right, RecordedMove::Sent(Word::Task)),
        (Left, RecordedMove::Received(Word::Task)),
        (Left, report()),
        (Left, RecordedMove::Sent(Word::Progress)),
        (Right, offered(Branch::Report)),
        (Right, RecordedMove::Received(Word::Progress)),
        (Right, retire()),
        (Left, offered(Branch::Retire)),
    ]);
    let report = judged(&mut arena, &[
        declaration(At(0), played, first),
        declaration(At(1), played, second),
        declaration(At(2), commuted, reflexivity),
        declaration(At(3), played, inverted),
        declaration(At(4), played, misheard),
        declaration(At(5), played, misoffered),
        declaration(At(6), played, crossed),
        declaration(At(7), played, short),
    ]);
    for position in [0, 1, 2] {
        assert!(
            matches!(
                verdict(&report, At(position)),
                Some(Verdict::Checked { .. })
            ),
            "declaration {position} checks: {report:?}"
        );
    }
    assert_eq!(
        [3, 4, 5, 6, 7].map(|position| verdict(&report, At(position))),
        [
            Some(Verdict::Refused(CheckRefusal::DialogueInverted {
                at: inverted,
                earlier: RunStep::from(1_u32),
                later: RunStep::from(0_u32),
            })),
            Some(Verdict::Refused(CheckRefusal::DialogueUnmatched {
                at: misheard,
                step: RunStep::from(1_u32),
            })),
            Some(Verdict::Refused(CheckRefusal::DialogueUnmatched {
                at: misoffered,
                step: RunStep::from(2_u32),
            })),
            Some(Verdict::Refused(CheckRefusal::RunNotAdmitted {
                at: crossed,
                fault: RunFault::WrongDirection(RunStep::from(0_u32)),
            })),
            Some(Verdict::Refused(CheckRefusal::RunNotAdmitted {
                at: short,
                fault: RunFault::Incomplete(RunStep::from(8_u32)),
            })),
        ],
        "each refusal names its move by its position in the log"
    );
    let readmission = bridge::readmit(&mut arena, &report);
    let outcomes: Vec<_> = readmission
        .readmitted()
        .iter()
        .map(|entry| entry.outcome().clone())
        .collect();
    assert!(
        [0, 1].iter().all(|&position| matches!(
            outcomes.get(position),
            Some(Outcome::Refused(bridge::Refusal::OutOfFragment {
                former: UnadmittedFormer::Run,
                ..
            }))
        )),
        "dialogues stay on the checker's side, as runs do: {outcomes:?}"
    );
}

#[test]
fn a_prefix_admits_an_open_run_and_refuses_by_move()
{
    let mut arena = CoreArena::new();
    let end = seat(&mut arena, Seat::End);
    let prefix = arena.value_type_prefix(end);
    let complete = arena.value_type_run(end);
    // A run stopped after its first receive: a prefix, never a run.
    let open = run(&mut arena, &[RecordedMove::Received(Word::Task)]);
    let opened = declaration(At(0), prefix, open);
    let unfinished = declaration(At(1), complete, open);
    // A complete run and the empty one are prefixes too.
    let served = retiring(&mut arena);
    let closed = declaration(At(2), prefix, served);
    let empty = run(&mut arena, &[]);
    let unstarted = declaration(At(3), prefix, empty);
    // A move the monitor refuses is refused by name at either extent.
    let crossed = run(&mut arena, &[RecordedMove::Sent(Word::Task)]);
    let wrong_way = declaration(At(4), prefix, crossed);
    let overrun = run(&mut arena, &[
        RecordedMove::Received(Word::Task),
        RecordedMove::Selected(Branch::Report.label()),
        RecordedMove::Sent(Word::Progress),
        RecordedMove::Offered(Branch::Retire.label()),
        RecordedMove::Closed,
        RecordedMove::Received(Word::Task),
    ]);
    let past_end = declaration(At(5), prefix, overrun);
    // A prefix does not stand where a run is declared.
    let held = arena.value_constant(ConstantIndex::from(0_usize));
    let promoted = declaration(At(6), complete, held);
    let report = judged(&mut arena, &[
        opened, unfinished, closed, unstarted, wrong_way, past_end, promoted,
    ]);
    for position in [0, 2, 3] {
        assert!(
            matches!(
                verdict(&report, At(position)),
                Some(Verdict::Checked { .. })
            ),
            "declaration {position} is a prefix: {report:?}"
        );
    }
    assert_eq!(
        [1, 4, 5].map(|position| verdict(&report, At(position))),
        [
            Some(Verdict::Refused(CheckRefusal::RunNotAdmitted {
                at: open,
                fault: RunFault::Incomplete(RunStep::from(1_u32)),
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
        "the open run is no run, and a refused move is named at a prefix: {report:?}"
    );
    assert!(
        matches!(
            verdict(&report, At(6)),
            Some(Verdict::Refused(CheckRefusal::TypeMismatch(_)))
        ),
        "a prefix is not a run: {report:?}"
    );
    let readmission = bridge::readmit(&mut arena, &report);
    assert!(
        matches!(
            readmission
                .readmitted()
                .first()
                .map(bridge::Readmitted::outcome),
            Some(Outcome::Refused(bridge::Refusal::OutOfFragment {
                former: UnadmittedFormer::Run,
                ..
            }))
        ),
        "a prefix stays on the checker's side: {readmission:?}"
    );
}

#[test]
fn stays_and_composites_record_their_simulation()
{
    let mut arena = CoreArena::new();
    let end = seat(&mut arena, Seat::End);
    let wide = seat(&mut arena, Seat::Wide);
    let type_universe = universe(&mut arena);
    let (sub, _) = statement(&mut arena, At(0), SessionRelation::Subtyping, (end, wide));
    let sub_constant = arena.value_constant(ConstantIndex::from(0_usize));
    let stay = arena.value_stay(wide);
    let then = arena.value_then(sub_constant, stay);
    let composite = arena.value_type_flow(type_universe, end, wide);
    let composed = declaration(At(1), composite, then);
    let truth = arena.value_literal(Literal::Text(StringLiteral::new(String::from("x"))));
    let string = arena.value_type_base(BaseType::String);
    let element = arena.value_stay(truth);
    let element_flow = arena.value_type_flow(string, truth, truth);
    let elementary = declaration(At(2), element_flow, element);
    let report = judged(&mut arena, &[sub, composed, elementary]);
    assert!(
        report
            .judged()
            .iter()
            .all(|judged| matches!(judged.verdict(), Verdict::Checked { .. })),
        "a composite of simulations and a stay at a string check: {report:?}"
    );
    assert!(
        report.flows().contains_key(&then) && report.flows().contains_key(&stay),
        "the composite and the stay over session codes record their simulation"
    );
    assert!(
        !report.flows().contains_key(&element),
        "a stay at a string records none"
    );
    let readmission = bridge::readmit(&mut arena, &report);
    let outcomes: Vec<_> = readmission
        .readmitted()
        .iter()
        .map(|entry| entry.outcome().clone())
        .collect();
    assert!(
        matches!(outcomes.as_slice(), [
            Outcome::Defined { .. },
            Outcome::Defined { .. },
            Outcome::Defined { .. },
        ]),
        "the composite crosses as one replayed simulation, and a stay at a string as the kernel's stay: {outcomes:?}"
    );
}

#[test]
fn a_flow_above_level_zero_crosses_as_the_kernels_flow_at_its_universe_1628()
{
    // def kept : Flow[.A = Type[+, 1]](Type, Type) = stay(Type) ;
    // def twice : Flow[.A = Type[+, 1]](Type, Type) = kept then kept ;
    let mut arena = CoreArena::new();
    let small = universe(&mut arena);
    let large = arena.value_type_universe(
        Sort::Ground(GroundSort::Value),
        Level::constant(LevelConstant::from(1_u64)),
    );
    let code = arena.value_quote(small);
    let stay = arena.value_stay(code);
    let flow = arena.value_type_flow(large, code, code);
    let kept = arena.value_constant(ConstantIndex::from(0_usize));
    let then = arena.value_then(kept, kept);
    let report = judged(&mut arena, &[
        declaration(At(0), flow, stay),
        declaration(At(1), flow, then),
    ]);
    assert!(
        report
            .judged()
            .iter()
            .all(|judged| matches!(judged.verdict(), Verdict::Checked { .. })),
        "a stay at the code of a universe and its composite check at the universe above: {report:?}"
    );
    let readmission = bridge::readmit(&mut arena, &report);
    let outcomes: Vec<_> = readmission
        .readmitted()
        .iter()
        .map(|entry| entry.outcome().clone())
        .collect();
    assert!(
        matches!(outcomes.as_slice(), [
            Outcome::Defined { .. },
            Outcome::Defined { .. },
        ]),
        "the kernel replays both at its flow over the level-one universe: {outcomes:?}"
    );
}

#[test]
fn a_motive_above_level_zero_reads_its_binder_at_the_carriers_level_1837()
{
    // def kept : Flow[.A = Type[+, 1]](Type, Type) = stay(Type) ;
    // def same : Path[.A = Type[+, 1]](Type, Type) = here(Type) ;
    // def rode : () => Type = thunk { ride(fun (X) { X }, kept, Integer) } ;
    // def moved : () => Type = thunk { transport(fun (X) { X }, same, Integer) } ;
    // def small : () => Integer = thunk { ride(fun (X) { X }, stay(Integer), 0) } ;
    let mut arena = CoreArena::new();
    let small = universe(&mut arena);
    let one = Level::constant(LevelConstant::from(1_u64));
    let large = arena.value_type_universe(Sort::Ground(GroundSort::Value), one.clone());
    let code = arena.value_quote(small);
    let stay = arena.value_stay(code);
    let flow = arena.value_type_flow(large, code, code);
    let here = arena.value_here(code);
    let path = arena.value_type_path(large, code, code);
    let binder = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let motive = arena.value_type_element(binder, Level::zero());
    let integer = arena.value_type_base(BaseType::Integer);
    let quoted = arena.value_quote(integer);
    let kept = arena.value_constant(ConstantIndex::from(0_usize));
    let same = arena.value_constant(ConstantIndex::from(1_usize));
    let ride = arena.computation_ride(motive, kept, quoted);
    let transport = arena.computation_path_transport(motive, same, quoted);
    let returns_type = arena.comp_type_returner(small);
    let suspended_type = arena.value_type_thunk(returns_type);
    let rode = arena.value_thunk(ride);
    let moved = arena.value_thunk(transport);
    let integer_stay = arena.value_stay(quoted);
    let zero = arena.value_literal(gandr_core_checker_base::fixture::integer_literal());
    let small_ride = arena.computation_ride(motive, integer_stay, zero);
    let returns_integer = arena.comp_type_returner(integer);
    let suspended_integer = arena.value_type_thunk(returns_integer);
    let level_zero = arena.value_thunk(small_ride);
    let report = judged(&mut arena, &[
        declaration(At(0), flow, stay),
        declaration(At(1), path, here),
        declaration(At(2), suspended_type, rode),
        declaration(At(3), suspended_type, moved),
        declaration(At(4), suspended_integer, level_zero),
    ]);
    assert!(
        report
            .judged()
            .iter()
            .all(|judged| matches!(judged.verdict(), Verdict::Checked { .. })),
        "a ride and a transport along the level-one universe check, and so does a ride at level zero: {report:?}"
    );
    for at in [ride, transport] {
        let family = report.motives().get(&at).copied();
        assert!(
            family.is_some_and(|family| matches!(
                arena.value_type(family),
                Some(&gandr_core_term::ValueType::Element { code: read, ref target })
                    if read == binder && *target == one
            )),
            "the motive reads its binder at the carrier's level: {family:?}"
        );
    }
    assert!(
        !report.motives().contains_key(&small_ride),
        "a ride at level zero forms its written motive and records none"
    );
    let readmission = bridge::readmit(&mut arena, &report);
    let outcomes: Vec<_> = readmission
        .readmitted()
        .iter()
        .map(|entry| entry.outcome().clone())
        .collect();
    assert!(
        outcomes
            .iter()
            .all(|outcome| matches!(outcome, Outcome::Defined { .. })),
        "the kernel replays the ride and the transport at their recorded motives: {outcomes:?}"
    );
}

/// A quoted session type is a session code only at its protocol's root; the
/// same session past its root is read as some other code.
#[test]
fn a_session_is_a_code_only_at_its_root()
{
    let mut arena = CoreArena::new();
    let root = seat(&mut arena, Seat::End);
    let Some(&gandr_core_term::Value::Quote(quoted)) = arena.value(root)
    else {
        panic!("the seat is quoted");
    };
    let Some(gandr_core_term::ValueType::Session(session)) = arena.value_type(quoted).cloned()
    else {
        panic!("the seat quotes a session");
    };
    let later = session.at(ProtocolState::from(2_usize)).unwrap();
    let later = arena.value_type_session(later);
    let later = arena.value_quote(later);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    assert!(matches!(
        session_code(&mut context, root),
        Ok(Maybe::Present(ref read)) if *read == session
    ));
    assert_eq!(
        session_code(&mut context, later),
        Ok(Maybe::Absent(
            gandr_core_checker_base::flow::session_code::Absent::Elsewhere
        ))
    );
}

/// The quote of `?P. end` at its root, for the payload type `payload`.
///
/// # Specification
/// trivial.
fn asking(
    arena: &mut CoreArena,
    payload: ValueTypeId,
) -> ValueId
{
    let protocol = Protocol::new(
        alloc::vec![
            ProtocolSyntax::Receive {
                payload: PayloadSlot::from(0_usize),
                next: ProtocolState::from(1_usize),
            },
            ProtocolSyntax::End,
        ],
        ProtocolState::from(0_usize),
        PayloadCount::from(1_usize),
    )
    .unwrap();
    let session = SessionType::new(Arc::new(protocol), Arc::from([payload].as_slice())).unwrap();
    let ty = arena.value_type_session(session);
    arena.value_quote(ty)
}

/// Two protocols that receive `Unit * Unit` and `Unit` are bisimilar owing one
/// path between the payload types: written as an equivalence, it elaborates
/// to the native certificate the kernel checks against the owed pair; left
/// out, the protocols are not equivalent; bound by a parameter, it names no
/// certificate.
#[test]
fn a_bisimulation_owes_a_path_per_differing_payload_pair()
{
    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let pair = arena.value_type_product(&[unit, unit]);
    let (paired, single) = (asking(&mut arena, pair), asking(&mut arena, unit));
    let one = arena.value_unit();
    let ones = arena.value_tuple(&[one, one]);
    let [forget, double] = [one, ones].map(|result| {
        let body = arena.computation_return(result);
        let lambda = arena.computation_lambda(body);
        arena.value_thunk(lambda)
    });
    let [forgetting, doubling] = [(pair, unit), (unit, pair)].map(|(domain, codomain)| {
        let returns = arena.comp_type_returner(codomain);
        let arrow = arena.comp_type_arrow(domain, returns);
        arena.value_type_thunk(arrow)
    });
    let translators = [0_usize, 1_usize].map(|at| arena.value_constant(ConstantIndex::from(at)));
    let paths = arena.value_equiv(translators[0], translators[1]);
    let identity = gandr_core_checker_base::flow::identity(
        &mut arena,
        SessionRelation::Equivalence,
        (paired, single),
    );
    let paid = arena.value_session_related(SessionRelation::Equivalence, paired, single, paths);
    let report = judged(&mut arena, &[
        declaration(At(0), forgetting, forget),
        declaration(At(1), doubling, double),
        declaration(At(2), identity, paid),
    ]);
    assert!(
        matches!(verdict(&report, At(2)), Some(Verdict::Checked { .. })),
        "the equivalence pays the one differing pair: {report:?}"
    );
    let slot = gandr_kernel_term::session::PayloadSlot;
    assert_eq!(
        report
            .flows()
            .get(&paid)
            .map(|statement| statement.evidence().payloads.clone()),
        Some(alloc::vec![(slot(0), slot(0))]),
        "the evidence names the owed slot pair once"
    );
    assert_eq!(
        report
            .flows()
            .get(&paid)
            .map(|statement| statement.owed().to_vec()),
        Some(alloc::vec![(pair, unit)]),
        "the statement owes the pair's payload types, source first"
    );
    assert!(
        matches!(
            report.natives().get(&paths).and_then(|&native| arena.value(native)),
            Some(gandr_core_term::Value::Tuple(natives))
                if matches!(**natives, [native] if matches!(arena.value(native), Some(gandr_core_term::Value::PathEquiv { .. })))
        ),
        "the path elaborates to a tuple of one native certificate"
    );
    let readmission = bridge::readmit(&mut arena, &report);
    assert!(
        matches!(
            readmission.readmitted(),
            [.., entry] if matches!(entry.outcome(), Outcome::Defined { .. })
        ),
        "the kernel checks the certificate against the pair it covers: {:?}",
        readmission.readmitted()
    );
    let unpaid = arena.value_session_related(SessionRelation::Equivalence, paired, single, one);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let opened = arena.value_session_related(SessionRelation::Equivalence, paired, single, bound);
    let returned = arena.computation_return(opened);
    let lambda = arena.computation_lambda(returned);
    let parameter = arena.value_thunk(lambda);
    let universe = universe(&mut arena);
    let (pair_code, unit_code) = (arena.value_quote(pair), arena.value_quote(unit));
    let domain = arena.value_type_path(universe, pair_code, unit_code);
    let codomain = arena.comp_type_returner(identity);
    let arrow = arena.comp_type_arrow(domain, codomain);
    let declared = arena.value_type_thunk(arrow);
    let report = judged(&mut arena, &[
        declaration(At(0), identity, unpaid),
        declaration(At(1), declared, parameter),
    ]);
    assert_eq!(
        verdict(&report, At(0)),
        Some(Verdict::Refused(CheckRefusal::SessionNotEquivalent {
            at: unpaid
        })),
        "without the path the protocols are not equivalent"
    );
    assert!(
        matches!(
            verdict(&report, At(1)),
            Some(Verdict::Refused(CheckRefusal::ShapeMismatch {
                at: gandr_core_checker_base::refusal::TermNode::Value(at),
                wanted: gandr_core_checker_base::refusal::ExpectedShape::PathUniverse,
                ..
            })) if at == bound
        ),
        "a path a parameter binds names no certificate: {report:?}"
    );
}

/// `thunk(λx. a ← x.0; b ← x.1; return (b, a))`: a pair's components swapped.
///
/// # Specification
/// trivial.
fn swap(arena: &mut CoreArena) -> ValueId
{
    let point = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let first = arena.computation_tuple_projection(point, 0_usize.into());
    let under = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let second = arena.computation_tuple_projection(under, 1_usize.into());
    let [b, a] = [0_u32, 1_u32]
        .map(|index| arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index)));
    let swapped = arena.value_tuple(&[b, a]);
    let returned = arena.computation_return(swapped);
    let inner = arena.computation_bind(second, returned);
    let outer = arena.computation_bind(first, inner);
    let lambda = arena.computation_lambda(outer);
    arena.value_thunk(lambda)
}

/// Protocols that receive `Unit * Bool` and `Bool * Unit` are bisimilar owing
/// one path between the payload types: a univalence over the swap, whose laws
/// hold by η, pays it as itself and the kernel checks its record at the native
/// identity the pair owes; the same univalence over a record a parameter
/// binds names no certificate, for the kernel checks payload paths closed.
#[test]
fn a_univalence_pays_a_payload_pair_when_closed()
{
    use gandr_core_term::identity::bi_invertible;
    use gandr_core_term::identity::univalence_forward;
    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let boolean = arena.value_type_sum(&[unit, unit]);
    let (left, right) = (
        arena.value_type_product(&[unit, boolean]),
        arena.value_type_product(&[boolean, unit]),
    );
    let (heard, swapped) = (asking(&mut arena, left), asking(&mut arena, right));
    let record_type = bi_invertible(&mut arena, left, right);
    let record = {
        let map = swap(&mut arena);
        let point = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let reflexivity = arena.value_here(point);
        let returned = arena.computation_return(reflexivity);
        let lambda = arena.computation_lambda(returned);
        let law = arena.value_thunk(lambda);
        let section = arena.value_tuple(&[map, law]);
        let retraction = arena.value_tuple(&[map, law]);
        let inverses = arena.value_tuple(&[section, retraction]);
        arena.value_tuple(&[map, inverses])
    };
    let univalence = |arena: &mut CoreArena, record| {
        let forward = univalence_forward(arena, record);
        arena.value_univalence(record, forward)
    };
    let named = arena.value_constant(ConstantIndex::from(0_usize));
    let closed = univalence(&mut arena, named);
    let identity = gandr_core_checker_base::flow::identity(
        &mut arena,
        SessionRelation::Equivalence,
        (heard, swapped),
    );
    let paid = arena.value_session_related(SessionRelation::Equivalence, heard, swapped, closed);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let open = univalence(&mut arena, bound);
    let opened = arena.value_session_related(SessionRelation::Equivalence, heard, swapped, open);
    let parameter = {
        let returned = arena.computation_return(opened);
        let lambda = arena.computation_lambda(returned);
        arena.value_thunk(lambda)
    };
    let declared = {
        let codomain = arena.comp_type_returner(identity);
        let arrow = arena.comp_type_arrow(record_type, codomain);
        arena.value_type_thunk(arrow)
    };
    let report = judged(&mut arena, &[
        declaration(At(0), record_type, record),
        declaration(At(1), identity, paid),
        declaration(At(2), declared, parameter),
    ]);
    assert!(
        matches!(verdict(&report, At(1)), Some(Verdict::Checked { .. })),
        "the univalence pays the one differing pair: {report:?}"
    );
    assert!(
        matches!(
            report.natives().get(&closed).and_then(|&native| arena.value(native)),
            Some(gandr_core_term::Value::Tuple(natives))
                if matches!(**natives, [native] if native == closed)
        ),
        "the univalence stands for itself among the payload certificates: {report:?}"
    );
    let readmission = bridge::readmit(&mut arena, &report);
    assert!(
        matches!(
            readmission.readmitted(),
            [.., paid, _] if matches!(paid.outcome(), Outcome::Defined { .. })
        ),
        "the kernel checks the record at the native identity the pair owes: {:?}",
        readmission.readmitted()
    );
    assert!(
        matches!(
            verdict(&report, At(2)),
            Some(Verdict::Refused(CheckRefusal::ShapeMismatch {
                at: gandr_core_checker_base::refusal::TermNode::Value(at),
                wanted: gandr_core_checker_base::refusal::ExpectedShape::PathUniverse,
                ..
            })) if at == open
        ),
        "a univalence over a bound record names no certificate: {report:?}"
    );
}
