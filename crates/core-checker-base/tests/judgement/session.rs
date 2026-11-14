//! Session programs judged, then readmitted through the bridge.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use gandr_core_checker_base::CheckBudget;
use gandr_core_checker_base::CheckRefusal;
use gandr_core_checker_base::CheckingContext;
use gandr_core_checker_base::CoreNode;
use gandr_core_checker_base::Declaration;
use gandr_core_checker_base::OriginToken;
use gandr_core_checker_base::TermNode;
use gandr_core_checker_base::TypeNode;
use gandr_core_checker_base::Verdict;
use gandr_core_checker_base::answer::Direction;
use gandr_core_checker_base::check_module;
use gandr_core_checker_base::fixture::session::AfterSend;
use gandr_core_checker_base::fixture::session::Program;
use gandr_core_checker_base::fixture::session::Spelled;
use gandr_core_checker_base::fixture::session::check_unit;
use gandr_core_checker_base::fixture::session::delegating;
use gandr_core_checker_base::fixture::session::delegator;
use gandr_core_checker_base::fixture::session::end;
use gandr_core_checker_base::fixture::session::fork;
use gandr_core_checker_base::fixture::session::operator;
use gandr_core_checker_base::fixture::session::seat;
use gandr_core_checker_base::fixture::session::seat_end;
use gandr_core_checker_base::fixture::session::session;
use gandr_core_checker_base::fixture::session::session_at;
use gandr_core_checker_base::form_value_type;
use gandr_core_checker_base::judgement::type_value;
use gandr_core_checker_base::session::Endpoint;
use gandr_core_checker_base::session::ForkSide;
use gandr_core_checker_base::session::LinearityDefect;
use gandr_core_checker_bridge::bridge;
use gandr_core_term::Computation;
use gandr_core_term::CoreArena;
use gandr_core_term::Sort;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::session::ActionKind;
use gandr_core_term::session::PayloadSlot;
use gandr_core_term::session::ProtocolState;
use gandr_core_term::session::ProtocolSyntax;
use gandr_core_term::session::SessionAction;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GroundSort;
use quenchant_shape::shape::Maybe;

#[test]
fn a_typed_run_keeps_each_endpoint_s_state()
{
    let mut arena = CoreArena::new();
    let protocol = seat_end(&mut arena);
    let seat = seat(&mut arena);
    let operator = operator(&mut arena);
    let exchange = fork(&mut arena, protocol, seat, operator);
    let suspended = arena.value_thunk(exchange);
    let unit = arena.value_type_unit();
    let returner = arena.comp_type_returner(unit);
    let thunk = arena.value_type_thunk(returner);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let expected = form_value_type(&mut context, thunk).unwrap();
    let typed = type_value(&mut context, suspended, Direction::Check(expected));
    assert!(typed.marks().is_empty(), "the exchange checks: {typed:?}");
    let standings: Vec<(ActionKind, ActionKind, ValueTypeId)> = typed
        .endpoints()
        .iter()
        .map(|standing| {
            let (TermNode::Computation(at), TypeNode::Value(state)) = (standing.term, standing.ty)
            else {
                panic!("an endpoint is kept at an action, at a value type: {standing:?}");
            };
            let Some(Computation::Session(action)) = context.arena().computation(at).cloned()
            else {
                panic!("an endpoint is kept at an action");
            };
            let Maybe::Present(written) = action.kind()
            else {
                panic!("a fork names no endpoint of its own");
            };
            let session = session_at(&context, state).unwrap();
            let admitted = session.step().unwrap().action();
            (written, admitted, state)
        })
        .collect();
    assert_eq!(
        standings.len(),
        20,
        "each of the seat's 8 actions and the operator's 12 keeps its endpoint once"
    );
    assert!(
        standings
            .iter()
            .all(|&(written, admitted, _)| written == admitted),
        "each endpoint is kept at the state that admits its action: {standings:?}"
    );
    let states: BTreeSet<ValueTypeId> = standings.iter().map(|&(.., state)| state).collect();
    assert!(
        states.len() > 2,
        "an endpoint's state advances along the protocol: {standings:?}"
    );
}

/// A session code crosses to the kernel at the state it stands at: its
/// protocol's root, or the protocol re-rooted at a state past it.
#[test]
fn a_session_code_crosses_re_rooted_at_its_state_1319()
{
    let mut arena = CoreArena::new();
    let root = seat_end(&mut arena);
    let Some(gandr_core_term::ValueType::Session(session)) = arena.value_type(root).cloned()
    else {
        panic!("the seat is a session type");
    };
    let past = session.at(ProtocolState::from(2_usize)).unwrap();
    let past = arena.value_type_session(past);
    let universe = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let declarations: Vec<_> = [root, past]
        .into_iter()
        .enumerate()
        .map(|(position, code)| {
            let quoted = arena.value_quote(code);
            Declaration::new(
                ConstantIndex::from(position),
                Maybe::Present(universe),
                Maybe::Present(quoted),
                OriginToken::from(position),
            )
        })
        .collect();
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let report = check_module(&mut context, &declarations);
    assert!(
        report
            .judged()
            .iter()
            .all(|judged| matches!(judged.verdict(), Verdict::Checked { .. })),
        "a session type is a code the checker forms, at any state"
    );
    let readmission = bridge::readmit(&mut arena, &report);
    let outcomes: Vec<_> = readmission
        .readmitted()
        .iter()
        .map(bridge::Readmitted::outcome)
        .collect();
    assert!(
        matches!(outcomes.as_slice(), [
            bridge::Outcome::Defined { .. },
            bridge::Outcome::Defined { .. }
        ]),
        "the kernel defines the protocol at its root and re-rooted past it: {outcomes:?}"
    );
}

/// A fork crosses as its child, then its parent under the bind that sequences
/// them, so a parent reading a variable bound outside the fork still reads it.
#[test]
fn a_fork_crosses_as_its_child_then_its_parent_1319()
{
    let mut arena = CoreArena::new();
    let ended = end(&mut arena);
    let string = arena.value_type_base(BaseType::String);
    let returns_string = arena.comp_type_returner(string);
    let reads_a_string = arena.comp_type_arrow(string, returns_string);
    let declared = arena.value_type_thunk(reads_a_string);
    // \n. let d = fork (c : end) { close(c) }; close(d) ; return n
    let child = Program::new(&mut arena).close();
    let outer = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let returned = arena.computation_return(outer);
    let parent = Program::new(&mut arena).then(
        SessionAction::Close {
            endpoint: DeBruijnIndex::from(0_u32),
        },
        returned,
    );
    let forked = fork(&mut arena, ended, child, parent);
    let lambda = arena.computation_lambda(forked);
    let defined = arena.value_thunk(lambda);
    let declarations = alloc::vec![Declaration::new(
        ConstantIndex::from(0_usize),
        Maybe::Present(declared),
        Maybe::Present(defined),
        OriginToken::from(0_usize),
    )];
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let report = check_module(&mut context, &declarations);
    assert!(
        report
            .judged()
            .iter()
            .all(|judged| matches!(judged.verdict(), Verdict::Checked { .. })),
        "the exchange checks: {:?}",
        report
            .judged()
            .iter()
            .map(gandr_core_checker_base::Judged::verdict)
            .collect::<Vec<_>>()
    );
    let readmission = bridge::readmit(&mut arena, &report);
    let outcomes: Vec<_> = readmission
        .readmitted()
        .iter()
        .map(bridge::Readmitted::outcome)
        .collect();
    assert!(
        matches!(outcomes.as_slice(), [bridge::Outcome::Defined { .. }]),
        "the kernel defines the fork: {outcomes:?}"
    );
}

/// A fork at a row of operations stands for a program of the row's model.
/// Its reduct copies the parent without the judgement's records, so the
/// bridge refuses the fork as a session, and the kernel rejects nothing.
#[test]
fn a_fork_at_a_row_is_refused_as_a_session_6736()
{
    use gandr_core_term::effect::EffectName;
    use gandr_core_term::effect::EffectOp;
    use gandr_core_term::effect::EffectRow;
    use gandr_core_term::effect::EffectSig;
    use gandr_core_term::effect::OperationName;
    let mut arena = CoreArena::new();
    let ended = end(&mut arena);
    let unit = arena.value_type_unit();
    let string = arena.value_type_base(BaseType::String);
    let ask = EffectSig::new(EffectName::from("Ask"), [EffectOp {
        name: OperationName::from("ask"),
        payload: unit,
        reply: string,
    }])
    .expect("one operation");
    let returns_string = arena.comp_type_returner_with_effects(string, EffectRow::singleton(ask));
    let reads_a_string = arena.comp_type_arrow(string, returns_string);
    let declared = arena.value_type_thunk(reads_a_string);
    // \n. let d = fork (c : end) { close(c) }; close(d) ; return n, at `[Ask]`
    let child = Program::new(&mut arena).close();
    let outer = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let returned = arena.computation_return(outer);
    let parent = Program::new(&mut arena).then(
        SessionAction::Close {
            endpoint: DeBruijnIndex::from(0_u32),
        },
        returned,
    );
    let forked = fork(&mut arena, ended, child, parent);
    let lambda = arena.computation_lambda(forked);
    let defined = arena.value_thunk(lambda);
    let declarations = alloc::vec![Declaration::new(
        ConstantIndex::from(0_usize),
        Maybe::Present(declared),
        Maybe::Present(defined),
        OriginToken::from(0_usize),
    )];
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let report = check_module(&mut context, &declarations);
    assert!(
        report
            .judged()
            .iter()
            .all(|judged| matches!(judged.verdict(), Verdict::Checked { .. })),
        "the fork checks at the row: {:?}",
        report
            .judged()
            .iter()
            .map(gandr_core_checker_base::Judged::verdict)
            .collect::<Vec<_>>()
    );
    let readmission = bridge::readmit(&mut arena, &report);
    let outcomes: Vec<_> = readmission
        .readmitted()
        .iter()
        .map(bridge::Readmitted::outcome)
        .collect();
    let at = CoreNode::Term(TermNode::Computation(forked));
    assert!(
        matches!(
            outcomes.as_slice(),
            [bridge::Outcome::Refused(bridge::Refusal::Session { at: site })] if *site == at
        ),
        "the bridge refuses the fork at the row as a session: {outcomes:?}"
    );
}

/// A function's parameter at `end`, placed at its body's entry: closed, it
/// checks and the kernel defines it; left open, the placement is refused
/// with the endpoint as its residue; closed twice, the second close is
/// refused as a use after close.
#[test]
fn a_placed_endpoint_is_spent_by_its_body_1862()
{
    let mut arena = CoreArena::new();
    let ended = end(&mut arena);
    let unit = arena.value_type_unit();
    let returns_unit = arena.comp_type_returner(unit);
    let takes_an_end = arena.comp_type_arrow(ended, returns_unit);
    let declared = arena.value_type_thunk(takes_an_end);
    let parameter = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    // \seat. place seat { close(seat) }
    let closed = Program::new(&mut arena).close();
    let placed = arena.computation_session(SessionAction::Place {
        payload: parameter,
        body: closed,
    });
    // \seat. place seat { return () }
    let nothing = arena.value_unit();
    let kept = arena.computation_return(nothing);
    let leaked = arena.computation_session(SessionAction::Place {
        payload: parameter,
        body: kept,
    });
    // \seat. place seat { close(seat); close(seat) }
    let again = Program::new(&mut arena).close();
    let twice = Program::new(&mut arena).then(
        SessionAction::Close {
            endpoint: DeBruijnIndex::from(0_u32),
        },
        again,
    );
    let closed_twice = arena.computation_session(SessionAction::Place {
        payload: parameter,
        body: twice,
    });
    let declarations: Vec<_> = [placed, leaked, closed_twice]
        .into_iter()
        .enumerate()
        .map(|(position, body)| {
            let lambda = arena.computation_lambda(body);
            let defined = arena.value_thunk(lambda);
            Declaration::new(
                ConstantIndex::from(position),
                Maybe::Present(declared),
                Maybe::Present(defined),
                OriginToken::from(position),
            )
        })
        .collect();
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let report = check_module(&mut context, &declarations);
    let verdicts: Vec<_> = report
        .judged()
        .iter()
        .map(gandr_core_checker_base::Judged::verdict)
        .collect();
    assert!(
        matches!(verdicts.first(), Some(Verdict::Checked { .. })),
        "a placed endpoint the body closes checks: {verdicts:?}"
    );
    assert!(
        matches!(
            verdicts.get(1),
            Some(Verdict::Refused(CheckRefusal::Linearity {
                at: CoreNode::Term(TermNode::Computation(at)),
                defect: LinearityDefect::Residue {
                    endpoint: Endpoint {
                        fork,
                        side: ForkSide::Placed,
                    },
                    ..
                },
            })) if *at == leaked && *fork == leaked
        ),
        "a placed endpoint the body leaves open is the placement's residue: {verdicts:?}"
    );
    assert!(
        matches!(
            verdicts.get(2),
            Some(Verdict::Refused(CheckRefusal::Linearity {
                defect: LinearityDefect::Closed { .. },
                ..
            }))
        ),
        "a placed endpoint closed twice is refused at the second close: {verdicts:?}"
    );
    let readmission = bridge::readmit(&mut arena, &report);
    let outcomes: Vec<_> = readmission
        .readmitted()
        .iter()
        .map(bridge::Readmitted::outcome)
        .collect();
    assert!(
        matches!(outcomes.first(), Some(bridge::Outcome::Defined { .. })),
        "the kernel defines the closed placement as its body: {outcomes:?}"
    );
}

/// A received value crosses read from an assumption of its type, and an
/// offer as a case on an assumed choice among its arms: the kernel defines an
/// exchange returning the string it received and the whole seat exchange,
/// each resting only on the assumptions named for the actions it takes, the
/// seat's two two-armed offers on one. A delegation, whose receive binds an
/// endpoint that names no value, rests on none. A sent injection, which only
/// checks, crosses ascribed the payload type it was checked at.
#[test]
fn a_received_value_crosses_as_an_assumption_1319()
{
    let mut arena = CoreArena::new();
    let string = arena.value_type_base(BaseType::String);
    let returns_string = arena.comp_type_returner(string);
    let returning = arena.value_type_thunk(returns_string);
    let unit = arena.value_type_unit();
    let returns_unit = arena.comp_type_returner(unit);
    let running = arena.value_type_thunk(returns_unit);
    // let d = fork (c : !String. end) { send(c, "task") ; close(c) };
    //     let task = recv(d); close(d) ; return task
    let sending = session(
        &mut arena,
        alloc::vec![
            ProtocolSyntax::Send {
                payload: PayloadSlot::from(0_usize),
                next: ProtocolState::from(1_usize),
            },
            ProtocolSyntax::End,
        ],
        &[string],
    );
    let mut program = Program::new(&mut arena);
    let closed = program.close();
    let child = program.send(Spelled("task"), closed);
    let parent = Program::new(&mut arena).receive(|program| {
        let task = program
            .arena
            .value_variable(Zone::Linear, DeBruijnIndex::from(0_u32));
        let returned = program.arena.computation_return(task);
        program.then(
            SessionAction::Close {
                endpoint: program.endpoint(),
            },
            returned,
        )
    });
    let forked = fork(&mut arena, sending, child, parent);
    let received = arena.value_thunk(forked);
    let protocol = seat_end(&mut arena);
    let seat = seat(&mut arena);
    let operator = operator(&mut arena);
    let exchange = fork(&mut arena, protocol, seat, operator);
    let exchanged = arena.value_thunk(exchange);
    // the delegation of `a_delegated_endpoint_leaves_its_sender`
    let delegating = delegating(&mut arena);
    let (inner, _) = delegator(&mut arena, AfterSend::Leaves);
    let parent = Program::new(&mut arena).receive(|program| {
        let outer = program.close();
        program.then(
            SessionAction::Close {
                endpoint: DeBruijnIndex::from(0_u32),
            },
            outer,
        )
    });
    let delegation = fork(&mut arena, delegating, inner, parent);
    let delegated = arena.value_thunk(delegation);
    // let d = fork (c : ?(Integer + Unit). end) { let order = recv(c); close(c)
    // };     send(d, inj₀ 1) ; close(d)
    let integer = arena.value_type_base(BaseType::Integer);
    let order = arena.value_type_sum(&[integer, unit]);
    let ordering = session(
        &mut arena,
        alloc::vec![
            ProtocolSyntax::Receive {
                payload: PayloadSlot::from(0_usize),
                next: ProtocolState::from(1_usize),
            },
            ProtocolSyntax::End,
        ],
        &[order],
    );
    let child = Program::new(&mut arena).receive(Program::close);
    let one = arena.value_literal(gandr_core_checker_base::fixture::integer_literal());
    let injected = arena.value_injection(gandr_core_term::Summand::from(0_usize), one);
    let mut program = Program::new(&mut arena);
    let closed = program.close();
    let parent = program.then(
        SessionAction::Send {
            endpoint: DeBruijnIndex::from(0_u32),
            payload: injected,
        },
        closed,
    );
    let ordered = fork(&mut arena, ordering, child, parent);
    let ordered = arena.value_thunk(ordered);
    let declarations: Vec<_> = [
        (returning, received),
        (running, exchanged),
        (running, delegated),
        (running, ordered),
    ]
    .into_iter()
    .enumerate()
    .map(|(position, (declared, body))| {
        Declaration::new(
            ConstantIndex::from(position),
            Maybe::Present(declared),
            Maybe::Present(body),
            OriginToken::from(position),
        )
    })
    .collect();
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let report = check_module(&mut context, &declarations);
    let verdicts: Vec<_> = report
        .judged()
        .iter()
        .map(gandr_core_checker_base::Judged::verdict)
        .collect();
    assert!(
        verdicts
            .iter()
            .all(|verdict| matches!(verdict, Verdict::Checked { .. })),
        "the four exchanges check: {verdicts:?}"
    );
    let readmission = bridge::readmit(&mut arena, &report);
    let outcomes: Vec<_> = readmission
        .readmitted()
        .iter()
        .map(bridge::Readmitted::outcome)
        .collect();
    let &[
        &bridge::Outcome::Defined {
            audit: ref returned,
            ..
        },
        &bridge::Outcome::Defined {
            audit: ref exchanged,
            ..
        },
        &bridge::Outcome::Defined {
            audit: ref delegated,
            ..
        },
        &bridge::Outcome::Defined {
            audit: ref sent, ..
        },
    ] = outcomes.as_slice()
    else {
        panic!("the kernel defines the four exchanges: {outcomes:?}");
    };
    let artifact = gandr_kernel_term::decode(
        readmission
            .export(alloc::collections::BTreeMap::new())
            .as_image(),
    )
    .expect("the readmission's artifact decodes");
    // The action each axiom a declaration rests on assumes: `receive` or
    // `offer` for a session assumption, none for any other axiom.
    let actions = |axioms: &[ConstantIndex]| {
        axioms
            .iter()
            .map(|&position| {
                artifact
                    .declarations()
                    .get(usize::from(position))
                    .and_then(|entry| match *entry.declaration().name().segments() {
                        [ref session, ref action, _] if session.as_ref() == "session" => {
                            Some(action.as_ref())
                        },
                        _ => None,
                    })
            })
            .collect::<Vec<Option<&str>>>()
    };
    let returned = actions(returned.axioms());
    assert_eq!(
        returned,
        [Some("receive")],
        "the returned string rests on the one assumption of what was received"
    );
    let exchanged = actions(exchanged.axioms());
    assert!(
        exchanged.contains(&Some("receive"))
            && exchanged
                .iter()
                .filter(|&&action| action == Some("offer"))
                .take(2)
                .count()
                == 1
            && exchanged
                .iter()
                .all(|&action| matches!(action, Some("receive" | "offer"))),
        "the seat exchange rests on its receives' assumptions and one choice between two arms: {exchanged:?}"
    );
    assert!(
        delegated.axioms().is_empty(),
        "a received endpoint names no value to assume: {:?}",
        actions(delegated.axioms())
    );
    let sent = actions(sent.axioms());
    assert_eq!(
        sent,
        [Some("receive")],
        "the injection sent crosses ascribed, resting only on its receipt"
    );
}

/// A forked child, which no region bounds, receives nothing kept in a region
/// nor a capability living in one; and a fork's protocol is a session type.
#[test]
fn a_fork_carries_nothing_kept_in_a_region()
{
    let mut arena = CoreArena::new();
    let string = arena.value_type_base(BaseType::String);
    let kept = arena.value_type_kept(
        string,
        gandr_core_term::effect::capability::Region::Scoped(
            gandr_core_term::effect::capability::RegionDepth::from(1_u32),
        ),
    );
    // `?A. end`: the child receives one payload, then closes.
    let receiving = |arena: &mut CoreArena, payload| {
        session(
            arena,
            alloc::vec![
                ProtocolSyntax::Receive {
                    payload: PayloadSlot::from(0_usize),
                    next: ProtocolState::from(1_usize),
                },
                ProtocolSyntax::End,
            ],
            &[payload],
        )
    };
    let plain = receiving(&mut arena, string);
    let carrying = receiving(&mut arena, kept);
    let mut program = Program::new(&mut arena);
    let received = program.receive(Program::close);
    let closed = program.close();
    let sent = program.send(Spelled("buffer"), closed);
    let plain_fork = fork(&mut arena, plain, received, sent);
    assert_eq!(
        check_unit(&mut arena, plain_fork),
        Ok(()),
        "a child receives a plain payload"
    );
    let carrying_fork = fork(&mut arena, carrying, received, sent);
    assert_eq!(
        check_unit(&mut arena, carrying_fork),
        Err(CheckRefusal::Access {
            at: gandr_core_checker_base::refusal::CoreNode::Term(
                gandr_core_checker_base::refusal::TermNode::Computation(carrying_fork)
            ),
            defect: gandr_core_checker_base::access::AccessDefect::KeptEscaped,
        }),
        "a child no region bounds receives nothing kept in one"
    );
    let capability = arena.value_type_capability(
        gandr_core_term::effect::EffectRow::default(),
        gandr_core_term::effect::capability::CapabilityGrade::Durable,
        gandr_core_term::effect::capability::Region::Scoped(
            gandr_core_term::effect::capability::RegionDepth::from(1_u32),
        ),
    );
    let authorised = receiving(&mut arena, capability);
    let authorised_fork = fork(&mut arena, authorised, received, sent);
    assert!(
        matches!(
            check_unit(&mut arena, authorised_fork),
            Err(CheckRefusal::CapabilityEscaped { at: TermNode::Computation(at), .. })
                if at == authorised_fork
        ),
        "a child no region bounds receives no capability living in one"
    );
    let unprotocolled = fork(&mut arena, string, received, sent);
    assert!(
        matches!(
            check_unit(&mut arena, unprotocolled),
            Err(CheckRefusal::ShapeMismatch {
                at: TermNode::Computation(at),
                wanted: gandr_core_checker_base::refusal::ExpectedShape::Session,
                ..
            }) if at == unprotocolled
        ),
        "a fork's protocol is a session type"
    );
}
