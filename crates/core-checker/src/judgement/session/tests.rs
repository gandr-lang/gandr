use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;

use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::LinearUse;
use gandr_core_term::Sort;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::session::ActionKind;
use gandr_core_term::session::PayloadCount;
use gandr_core_term::session::PayloadSlot;
use gandr_core_term::session::Protocol;
use gandr_core_term::session::ProtocolState;
use gandr_core_term::session::ProtocolSyntax;
use gandr_core_term::session::RecursionIndex;
use gandr_core_term::session::SessionAction;
use gandr_core_term::session::SessionType;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldLabel;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::Literal;
use gandr_kernel_term::StringLiteral;
use quenchant_shape::shape::Maybe;

use crate::CheckBudget;
use crate::CheckRefusal;
use crate::CheckingContext;
use crate::CoreNode;
use crate::Declaration;
use crate::OriginToken;
use crate::TermNode;
use crate::TypeNode;
use crate::Verdict;
use crate::body;
use crate::bridge;
use crate::check_comp;
use crate::check_module;
use crate::form_comp_type;
use crate::form_value_type;
use crate::judgement::Direction;
use crate::judgement::check_value_with_failure;
use crate::judgement::type_value;
use crate::session::Capture;
use crate::session::Endpoint;
use crate::session::ForkSide;
use crate::session::LinearityDefect;
use crate::session::ProtocolDefect;
use crate::session::session_at;

/// A label or a string as a test spells it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Spelled(&'static str);

/// The label `spelled` names.
///
/// # Specification
/// trivial.
fn label(Spelled(text): Spelled) -> FieldLabel
{
    FieldLabel::from(String::from(text))
}

/// The session type over `syntax` rooted at its first node, its payloads
/// `payloads`.
///
/// # Specification
/// trivial.
fn session(
    arena: &mut CoreArena,
    syntax: Vec<ProtocolSyntax>,
    payloads: &[ValueTypeId],
) -> ValueTypeId
{
    let protocol = Protocol::new(
        syntax,
        ProtocolState::from(0_usize),
        PayloadCount::from(payloads.len()),
    )
    .unwrap();
    let session = SessionType::new(Arc::new(protocol), Arc::from(payloads)).unwrap();
    arena.value_type_session(session)
}

/// The seat's end: `?Dispatch. mu turn. +{ report : !Report. &{ next :
/// turn, retire : end }, handoff : !Handoff. end }`, every payload a
/// string.
///
/// # Specification
/// trivial.
fn seat_end(arena: &mut CoreArena) -> ValueTypeId
{
    let string = arena.value_type_base(BaseType::String);
    let state = ProtocolState::from;
    session(
        arena,
        alloc::vec![
            ProtocolSyntax::Receive {
                payload: PayloadSlot::from(0_usize),
                next: state(1),
            },
            ProtocolSyntax::Mu(state(2)),
            ProtocolSyntax::Select(BTreeMap::from([
                (label(Spelled("handoff")), state(6)),
                (label(Spelled("report")), state(3)),
            ])),
            ProtocolSyntax::Send {
                payload: PayloadSlot::from(1_usize),
                next: state(4),
            },
            ProtocolSyntax::Offer(BTreeMap::from([
                (label(Spelled("next")), state(5)),
                (label(Spelled("retire")), state(7)),
            ])),
            ProtocolSyntax::Recur(RecursionIndex::from(0_usize)),
            ProtocolSyntax::Send {
                payload: PayloadSlot::from(2_usize),
                next: state(8),
            },
            ProtocolSyntax::End,
            ProtocolSyntax::End,
        ],
        &[string, string, string],
    )
}

/// The pure `end` protocol.
///
/// # Specification
/// trivial.
fn end(arena: &mut CoreArena) -> ValueTypeId
{
    session(arena, alloc::vec![ProtocolSyntax::End], &[])
}

/// The terms one endpoint's program is built of, the endpoint the
/// innermost linear binder.
#[repr(transparent)]
struct Program<'arena>
{
    /// The arena.
    arena: &'arena mut CoreArena,
}

impl Program<'_>
{
    /// The endpoint, the innermost linear binder.
    ///
    /// # Specification
    /// trivial.
    fn endpoint() -> DeBruijnIndex
    {
        DeBruijnIndex::from(0_u32)
    }

    /// `x <- action ; rest`.
    ///
    /// # Specification
    /// trivial.
    fn then(
        &mut self,
        action: SessionAction,
        rest: ComputationId,
    ) -> ComputationId
    {
        let action = self.arena.computation_session(action);
        self.arena.computation_bind(action, rest)
    }

    /// The action alone.
    ///
    /// # Specification
    /// trivial.
    fn act(
        &mut self,
        action: SessionAction,
    ) -> ComputationId
    {
        self.arena.computation_session(action)
    }

    /// The string literal `text`.
    ///
    /// # Specification
    /// trivial.
    fn text(
        &mut self,
        Spelled(text): Spelled,
    ) -> ValueId
    {
        self.arena
            .value_literal(Literal::Text(StringLiteral::new(String::from(text))))
    }

    /// `close(c)`.
    ///
    /// # Specification
    /// trivial.
    fn close(&mut self) -> ComputationId
    {
        self.act(SessionAction::Close {
            endpoint: Self::endpoint(),
        })
    }

    /// `select(c, l) ; rest`.
    ///
    /// # Specification
    /// trivial.
    fn select(
        &mut self,
        choice: Spelled,
        rest: ComputationId,
    ) -> ComputationId
    {
        self.then(
            SessionAction::Select {
                endpoint: Self::endpoint(),
                label: label(choice),
            },
            rest,
        )
    }

    /// `send(c, text) ; rest`.
    ///
    /// # Specification
    /// trivial.
    fn send(
        &mut self,
        text: Spelled,
        rest: ComputationId,
    ) -> ComputationId
    {
        let payload = self.text(text);
        self.then(
            SessionAction::Send {
                endpoint: Self::endpoint(),
                payload,
            },
            rest,
        )
    }

    /// `recv(c) as x ; rest`.
    ///
    /// # Specification
    /// trivial.
    fn receive(
        &mut self,
        rest: ComputationId,
    ) -> ComputationId
    {
        self.then(
            SessionAction::Receive {
                endpoint: Self::endpoint(),
            },
            rest,
        )
    }

    /// `offer(c) { l => arm, … }`.
    ///
    /// # Specification
    /// trivial.
    fn offer(
        &mut self,
        arms: &[(Spelled, ComputationId)],
    ) -> ComputationId
    {
        self.act(SessionAction::Offer {
            endpoint: Self::endpoint(),
            arms: arms
                .iter()
                .map(|&(choice, arm)| (label(choice), arm))
                .collect(),
        })
    }
}

/// The seat's half: receive the dispatch, report, then on `next` hand
/// off and on `retire` close.
///
/// # Specification
/// trivial.
fn seat(arena: &mut CoreArena) -> ComputationId
{
    let mut program = Program { arena };
    let closed = program.close();
    let notes = program.send(Spelled("notes"), closed);
    let handed = program.select(Spelled("handoff"), notes);
    let retired = program.close();
    let answered = program.offer(&[(Spelled("next"), handed), (Spelled("retire"), retired)]);
    let reported = program.send(Spelled("progress"), answered);
    let chose = program.select(Spelled("report"), reported);
    program.receive(chose)
}

/// The operator's half: dispatch, then take each choice the seat makes,
/// asking for the next report once and retiring the seat the second
/// time.
///
/// # Specification
/// trivial.
fn operator(arena: &mut CoreArena) -> ComputationId
{
    let mut program = Program { arena };
    let closed = program.close();
    let second_notes = program.receive(closed);
    let closed = program.close();
    let retired = program.select(Spelled("retire"), closed);
    let second_report = program.receive(retired);
    let second = program.offer(&[
        (Spelled("handoff"), second_notes),
        (Spelled("report"), second_report),
    ]);
    let again = program.select(Spelled("next"), second);
    let first_report = program.receive(again);
    let closed = program.close();
    let first_notes = program.receive(closed);
    let first = program.offer(&[
        (Spelled("handoff"), first_notes),
        (Spelled("report"), first_report),
    ]);
    program.send(Spelled("task"), first)
}

/// `fork (c : protocol) { child } as d ; parent`.
///
/// # Specification
/// trivial.
fn fork(
    arena: &mut CoreArena,
    protocol: ValueTypeId,
    child: ComputationId,
    parent: ComputationId,
) -> ComputationId
{
    arena.computation_session(SessionAction::Fork {
        protocol,
        child,
        parent,
    })
}

/// Check `term` against the pure returner of the unit.
///
/// # Specification
/// trivial.
fn check_unit(
    arena: &mut CoreArena,
    term: ComputationId,
) -> Result<(), CheckRefusal>
{
    let unit = arena.value_type_unit();
    let returner = arena.comp_type_returner(unit);
    let mut context = CheckingContext::new(arena, CheckBudget::DEFAULT);
    let returner = form_comp_type(&mut context, returner)?;
    let checked = check_comp(&mut context, term, returner).map(|_| ());
    assert_eq!(
        context.depth(Zone::Linear),
        gandr_core_term::BinderDepth::default(),
        "a run leaves the linear zone as it found it"
    );
    checked
}

/// The child end of `fork`.
///
/// # Specification
/// trivial.
const fn child(fork: ComputationId) -> Endpoint
{
    Endpoint {
        fork,
        side: ForkSide::Child,
    }
}

#[test]
fn the_seat_exchange_checks_at_both_ends()
{
    let mut arena = CoreArena::new();
    let protocol = seat_end(&mut arena);
    let seat = seat(&mut arena);
    let operator = operator(&mut arena);
    let exchange = fork(&mut arena, protocol, seat, operator);
    assert_eq!(
        check_unit(&mut arena, exchange),
        Ok(()),
        "the seat follows its end and the operator the dual, through both choices"
    );
}

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

#[test]
fn an_operator_holding_the_seat_view_is_refused()
{
    let mut arena = CoreArena::new();
    let protocol = seat_end(&mut arena);
    let seat = seat(&mut arena);
    let wrong = Program { arena: &mut arena }.act(SessionAction::Receive {
        endpoint: DeBruijnIndex::from(0_u32),
    });
    let exchange = fork(&mut arena, protocol, seat, wrong);
    let refused = check_unit(&mut arena, exchange);
    assert!(
        matches!(
            refused,
            Err(CheckRefusal::SessionMismatch {
                at,
                endpoint: Endpoint { fork, side: ForkSide::Parent },
                defect: ProtocolDefect::Action { expected: ActionKind::Send, observed: ActionKind::Receive },
                ..
            }) if at == wrong && fork == exchange
        ),
        "the operator's end sends first, so a receive on it is refused: {refused:?}"
    );
}

#[test]
fn a_leftover_endpoint_is_reported_by_name()
{
    let mut arena = CoreArena::new();
    let protocol = end(&mut arena);
    let unit = arena.value_unit();
    let idle = arena.computation_return(unit);
    let closed = Program { arena: &mut arena }.close();
    let exchange = fork(&mut arena, protocol, idle, closed);
    let thunk = arena.value_thunk(exchange);
    let unit_type = arena.value_type_unit();
    let returner = arena.comp_type_returner(unit_type);
    let suspended = arena.value_type_thunk(returner);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let suspended = form_value_type(&mut context, suspended).unwrap();
    let failure = check_value_with_failure(&mut context, thunk, suspended).unwrap_err();
    assert_eq!(
        failure.refusal(),
        CheckRefusal::Linearity {
            at: CoreNode::Term(TermNode::Computation(exchange)),
            defect: LinearityDefect::Residue {
                endpoint: child(exchange),
                state: protocol,
            },
        },
        "the child finished with its end unclosed, named with its state"
    );
    assert_eq!(
        failure
            .endpoints()
            .iter()
            .map(|live| (live.endpoint, live.state, live.use_state))
            .collect::<Vec<_>>(),
        [(child(exchange), protocol, LinearUse::Available)],
        "the failure lists every endpoint the run held"
    );
    assert_eq!(
        context.depth(Zone::Linear),
        gandr_core_term::BinderDepth::default(),
        "the refused run leaves no endpoint behind"
    );
}

#[test]
fn an_endpoint_used_after_close_is_refused()
{
    let mut arena = CoreArena::new();
    let protocol = end(&mut arena);
    let mut program = Program { arena: &mut arena };
    let again = program.close();
    let twice = program.then(
        SessionAction::Close {
            endpoint: DeBruijnIndex::from(0_u32),
        },
        again,
    );
    let closed = program.close();
    let exchange = fork(&mut arena, protocol, twice, closed);
    assert_eq!(
        check_unit(&mut arena, exchange),
        Err(CheckRefusal::Linearity {
            at: CoreNode::Term(TermNode::Computation(again)),
            defect: LinearityDefect::Closed {
                endpoint: child(exchange),
            },
        }),
        "the second close acts on a consumed endpoint"
    );
}

#[test]
fn an_endpoint_used_twice_in_one_action_is_refused()
{
    let mut arena = CoreArena::new();
    let string = arena.value_type_base(BaseType::String);
    // !String. end
    let protocol = session(
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
    let itself = arena.value_variable(Zone::Linear, DeBruijnIndex::from(0_u32));
    let mut program = Program { arena: &mut arena };
    let closed = program.close();
    let send = program.then(
        SessionAction::Send {
            endpoint: DeBruijnIndex::from(0_u32),
            payload: itself,
        },
        closed,
    );
    let received = program.close();
    let parent = program.receive(received);
    let exchange = fork(&mut arena, protocol, send, parent);
    assert_eq!(
        check_unit(&mut arena, exchange),
        Err(CheckRefusal::Linearity {
            at: CoreNode::Term(TermNode::Value(itself)),
            defect: LinearityDefect::UsedTwice {
                endpoint: child(exchange),
            },
        }),
        "an endpoint sent over itself is used twice in the send"
    );
}

#[test]
fn an_endpoint_captured_by_a_thunk_is_refused()
{
    let mut arena = CoreArena::new();
    let protocol = end(&mut arena);
    let closed = Program { arena: &mut arena }.close();
    let suspended = arena.value_thunk(closed);
    let forced = arena.computation_force(suspended);
    let parent = Program { arena: &mut arena }.close();
    let exchange = fork(&mut arena, protocol, forced, parent);
    assert_eq!(
        check_unit(&mut arena, exchange),
        Err(CheckRefusal::Linearity {
            at: CoreNode::Term(TermNode::Value(suspended)),
            defect: LinearityDefect::Captured {
                endpoint: child(exchange),
                by: Capture::Thunk,
            },
        }),
        "a thunk may be forced any number of times"
    );
    let direct = Program { arena: &mut arena }.close();
    let parent = Program { arena: &mut arena }.close();
    let exchange = fork(&mut arena, protocol, direct, parent);
    assert_eq!(
        check_unit(&mut arena, exchange),
        Ok(()),
        "the same close outside the thunk checks"
    );
}

#[test]
fn offer_arms_leaving_different_endpoints_are_refused()
{
    let mut arena = CoreArena::new();
    // &{ a : end, b : end }
    let protocol = session(
        &mut arena,
        alloc::vec![
            ProtocolSyntax::Offer(BTreeMap::from([
                (label(Spelled("a")), ProtocolState::from(1_usize)),
                (label(Spelled("b")), ProtocolState::from(2_usize)),
            ])),
            ProtocolSyntax::End,
            ProtocolSyntax::End,
        ],
        &[],
    );
    let unit = arena.value_unit();
    let left_open = arena.computation_return(unit);
    let mut program = Program { arena: &mut arena };
    let closed = program.close();
    let offer = program.offer(&[(Spelled("a"), closed), (Spelled("b"), left_open)]);
    let parent_closed = program.close();
    let parent = program.select(Spelled("a"), parent_closed);
    let exchange = fork(&mut arena, protocol, offer, parent);
    assert_eq!(
        check_unit(&mut arena, exchange),
        Err(CheckRefusal::Linearity {
            at: CoreNode::Term(TermNode::Computation(left_open)),
            defect: LinearityDefect::ArmsDisagree {
                endpoint: child(exchange),
                first: closed,
                other: left_open,
            },
        }),
        "one arm closes the endpoint and the other leaves it open"
    );
}

#[test]
fn an_endpoint_at_a_top_level_declaration_is_refused()
{
    let mut arena = CoreArena::new();
    let protocol = end(&mut arena);
    let unit = arena.value_type_unit();
    let returner = arena.comp_type_returner(unit);
    let suspended = arena.value_type_thunk(returner);
    let declarations = [
        Declaration::new(
            ConstantIndex::from(0_usize),
            Maybe::Present(protocol),
            Maybe::Absent(body::Absent::Hole),
            OriginToken::from(0_usize),
        ),
        Declaration::new(
            ConstantIndex::from(1_usize),
            Maybe::Present(suspended),
            Maybe::Absent(body::Absent::Hole),
            OriginToken::from(1_usize),
        ),
    ];
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let report = check_module(&mut context, &declarations);
    let verdicts: Vec<_> = report.judged().iter().map(crate::Judged::verdict).collect();
    assert_eq!(
        verdicts.first(),
        Some(&Verdict::Refused(CheckRefusal::Linearity {
            at: CoreNode::Type(TypeNode::Value(protocol)),
            defect: LinearityDefect::Unrestricted,
        })),
        "an endpoint exists only in the linear zone a fork opens"
    );
    assert!(
        matches!(verdicts.get(1), Some(Verdict::Owed(_))),
        "a declaration at a thunk type is owed as before"
    );
}

#[test]
fn delegation_and_sharing_are_refused_by_name()
{
    let mut arena = CoreArena::new();
    let ended = end(&mut arena);
    // !end. end
    let delegating = session(
        &mut arena,
        alloc::vec![
            ProtocolSyntax::Send {
                payload: PayloadSlot::from(0_usize),
                next: ProtocolState::from(1_usize),
            },
            ProtocolSyntax::End,
        ],
        &[ended],
    );
    let child_closed = Program { arena: &mut arena }.close();
    let parent_closed = Program { arena: &mut arena }.close();
    let exchange = fork(&mut arena, delegating, child_closed, parent_closed);
    assert_eq!(
        check_unit(&mut arena, exchange),
        Err(CheckRefusal::Linearity {
            at: CoreNode::Type(TypeNode::Value(ended)),
            defect: LinearityDefect::Delegated,
        }),
        "a protocol that sends a session type delegates"
    );

    let string = arena.value_type_base(BaseType::String);
    // !String. end, whose child sends the parent's end of an inner fork
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
    // The payload is the inner fork's parent end, index 0; the send acts
    // on the outer child's end, index 1.
    let outer = arena.value_variable(Zone::Linear, DeBruijnIndex::from(0_u32));
    let inner_closed = Program { arena: &mut arena }.close();
    let mut program = Program { arena: &mut arena };
    let after_send = program.act(SessionAction::Close {
        endpoint: DeBruijnIndex::from(1_u32),
    });
    let inner_parent = program.then(
        SessionAction::Send {
            endpoint: DeBruijnIndex::from(1_u32),
            payload: outer,
        },
        after_send,
    );
    let inner = fork(&mut arena, ended, inner_closed, inner_parent);
    let received = Program { arena: &mut arena }.close();
    let parent = Program { arena: &mut arena }.receive(received);
    let exchange = fork(&mut arena, sending, inner, parent);
    let refused = check_unit(&mut arena, exchange);
    assert!(
        matches!(
            refused,
            Err(CheckRefusal::Linearity { at: CoreNode::Term(TermNode::Value(at)), defect: LinearityDefect::Delegated })
                if at == outer
        ),
        "a send whose payload is another endpoint delegates: {refused:?}"
    );

    let itself = arena.value_variable(Zone::Linear, DeBruijnIndex::from(0_u32));
    let escaped = arena.computation_return(itself);
    let parent = Program { arena: &mut arena }.close();
    let exchange = fork(&mut arena, ended, escaped, parent);
    assert_eq!(
        check_unit(&mut arena, exchange),
        Err(CheckRefusal::Linearity {
            at: CoreNode::Term(TermNode::Value(itself)),
            defect: LinearityDefect::AsValue {
                endpoint: child(exchange),
            },
        }),
        "an endpoint read as a value would be shared"
    );
}

#[test]
fn a_session_code_crosses_only_at_its_root()
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
        matches!(
            outcomes.as_slice(),
            [
                bridge::Outcome::Defined { .. },
                bridge::Outcome::Refused(bridge::Refusal::Session { at })
            ] if *at == CoreNode::Type(TypeNode::Value(past))
        ),
        "a protocol's root crosses as the kernel's session code; a state past it names an endpoint mid-protocol, which the kernel has no channel for: {outcomes:?}"
    );
    assert_eq!(
        bridge::Refusal::Session {
            at: CoreNode::Type(TypeNode::Value(past)),
        }
        .classify(),
        gandr_core_term::FailureClass::Unrepresentable,
        "a session is unrepresentable, not a fault"
    );
}
