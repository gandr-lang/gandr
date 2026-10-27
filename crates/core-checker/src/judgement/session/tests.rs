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
use gandr_core_term::control::EffectClause;
use gandr_core_term::effect::host::HostSignatures;
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

use super::super::Goal;
use super::super::Machine;
use super::super::Marking;
use super::Resident;
use super::Sessions;
use super::captured;
use crate::CheckBudget;
use crate::CheckRefusal;
use crate::CheckingContext;
use crate::CoreNode;
use crate::Declaration;
use crate::OriginToken;
use crate::TermNode;
use crate::TypeNode;
use crate::Verdict;
use crate::access::AccessDefect;
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

/// The terms one endpoint's program is built of, the endpoint the linear
/// binder under the received values the program is inside.
struct Program<'arena>
{
    /// The arena.
    arena: &'arena mut CoreArena,
    /// How many receives' binders stand inside the endpoint's.
    received: u32,
}

impl<'arena> Program<'arena>
{
    /// A program on the innermost linear binder.
    ///
    /// # Specification
    /// trivial.
    const fn new(arena: &'arena mut CoreArena) -> Self
    {
        Self { arena, received: 0 }
    }

    /// The endpoint, under the receives the program is inside.
    ///
    /// # Specification
    /// trivial.
    fn endpoint(&self) -> DeBruijnIndex
    {
        DeBruijnIndex::from(self.received)
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
            endpoint: self.endpoint(),
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
                endpoint: self.endpoint(),
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
                endpoint: self.endpoint(),
                payload,
            },
            rest,
        )
    }

    /// `recv(c) as x ; rest`, `rest` built under the receive's binder.
    ///
    /// # Specification
    /// trivial.
    fn receive(
        &mut self,
        rest: impl FnOnce(&mut Self) -> ComputationId,
    ) -> ComputationId
    {
        let endpoint = self.endpoint();
        self.received = self.received.saturating_add(1);
        let body = rest(self);
        self.received = self.received.saturating_sub(1);
        self.act(SessionAction::Receive { endpoint, body })
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
            endpoint: self.endpoint(),
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
    let mut program = Program::new(arena);
    program.receive(|program| {
        let closed = program.close();
        let notes = program.send(Spelled("notes"), closed);
        let handed = program.select(Spelled("handoff"), notes);
        let retired = program.close();
        let answered = program.offer(&[(Spelled("next"), handed), (Spelled("retire"), retired)]);
        let reported = program.send(Spelled("progress"), answered);
        program.select(Spelled("report"), reported)
    })
}

/// The operator's half: dispatch, then take each choice the seat makes,
/// asking for the next report once and retiring the seat the second
/// time.
///
/// # Specification
/// trivial.
fn operator(arena: &mut CoreArena) -> ComputationId
{
    let mut program = Program::new(arena);
    let first_report = program.receive(|program| {
        let second_notes = program.receive(Program::close);
        let second_report = program.receive(|program| {
            let closed = program.close();
            program.select(Spelled("retire"), closed)
        });
        let second = program.offer(&[
            (Spelled("handoff"), second_notes),
            (Spelled("report"), second_report),
        ]);
        program.select(Spelled("next"), second)
    });
    let first_notes = program.receive(Program::close);
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
    let wrong = Program::new(&mut arena).receive(Program::close);
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
    let closed = Program::new(&mut arena).close();
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
    let mut program = Program::new(&mut arena);
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
    let mut program = Program::new(&mut arena);
    let closed = program.close();
    let send = program.then(
        SessionAction::Send {
            endpoint: DeBruijnIndex::from(0_u32),
            payload: itself,
        },
        closed,
    );
    let parent = program.receive(Program::close);
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
    let closed = Program::new(&mut arena).close();
    let suspended = arena.value_thunk(closed);
    let forced = arena.computation_force(suspended);
    let parent = Program::new(&mut arena).close();
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
    let direct = Program::new(&mut arena).close();
    let parent = Program::new(&mut arena).close();
    let exchange = fork(&mut arena, protocol, direct, parent);
    assert_eq!(
        check_unit(&mut arena, exchange),
        Ok(()),
        "the same close outside the thunk checks"
    );
}

/// A capability scope's clause receives the rest of the scope's body as a
/// continuation it may drop or resume twice, so the body closes no endpoint
/// the run holds (#1336).
#[test]
fn a_scope_names_only_residents_that_owe_nothing_1336()
{
    let mut arena = CoreArena::new();
    let host = HostSignatures::new(&mut arena).unwrap();
    let protocol = end(&mut arena);
    let unit = arena.value_unit();
    let returned = arena.computation_return(unit);
    let answered = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let passes = arena.computation_return(answered);
    let clauses: Arc<[EffectClause]> = [EffectClause {
        operation: "exit".into(),
        body: returned,
    }]
    .into();
    let closed_inside = Program::new(&mut arena).close();
    let scoped = arena.computation_scope(host.proc, closed_inside, passes, clauses);
    let child_closed = Program::new(&mut arena).close();
    let exchange = fork(&mut arena, protocol, child_closed, scoped);
    assert_eq!(
        check_unit(&mut arena, exchange),
        Err(CheckRefusal::Linearity {
            at: CoreNode::Term(TermNode::Computation(scoped)),
            defect: LinearityDefect::Captured {
                endpoint: Endpoint {
                    fork: exchange,
                    side: ForkSide::Parent,
                },
                by: Capture::Continuation,
            },
        }),
        "the scope's clause may drop the close"
    );
    let closed_outside = Program::new(&mut arena).close();
    let child_closed = Program::new(&mut arena).close();
    let exchange = fork(&mut arena, protocol, child_closed, closed_outside);
    assert_eq!(
        check_unit(&mut arena, exchange),
        Ok(()),
        "the same close outside the scope checks"
    );
}

/// `exit(1)` through `capability`, a variable of the run.
///
/// # Specification
/// trivial.
fn exit(
    arena: &mut CoreArena,
    host: &HostSignatures,
    capability: DeBruijnIndex,
) -> ComputationId
{
    let code = arena.value_literal(crate::fixture::integer_literal());
    let capability = arena.value_variable(Zone::Intuitionistic, capability);
    arena.computation_exercise(capability, host.proc.clone(), "exit".into(), code)
}

/// `handle c : Proc { subject } with { pure(x) => pure x, exit(code, k) =>
/// body }`.
///
/// # Specification
/// trivial.
fn answering(
    arena: &mut CoreArena,
    host: &HostSignatures,
    subject: ComputationId,
    body: ComputationId,
) -> ComputationId
{
    let answered = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let passes = arena.computation_return(answered);
    let clauses: Arc<[EffectClause]> = [EffectClause {
        operation: "exit".into(),
        body,
    }]
    .into();
    arena.computation_scope(host.proc.clone(), subject, passes, clauses)
}

/// `handle c : Proc { subject } with { pure(x) => pure x, exit(code, k) =>
/// pure unit }`, its clause dropping the continuation, and the clause's body.
///
/// # Specification
/// trivial.
fn dropping(
    arena: &mut CoreArena,
    host: &HostSignatures,
    subject: ComputationId,
) -> (ComputationId, ComputationId)
{
    let unit = arena.value_unit();
    let returned = arena.computation_return(unit);
    (answering(arena, host, subject, returned), returned)
}

/// `Cap {exit}`, held by the host for the run.
///
/// # Specification
/// trivial.
fn held_exit(
    arena: &mut CoreArena,
    host: &HostSignatures,
) -> ValueTypeId
{
    let authority = gandr_core_term::effect::EffectRow::authority(&[host
        .proc
        .restrict(&["exit".into()])
        .expect("`Proc` performs `exit`")])
    .expect("one interface");
    arena.value_type_capability(
        authority,
        gandr_core_term::effect::capability::CapabilityGrade::Durable,
        gandr_core_term::effect::capability::Region::Held,
    )
}

/// Check `term` against the returner of the unit at the row `Proc`, under a
/// `Cap {exit}` the host holds for the run.
///
/// # Specification
/// trivial.
fn check_held_exit(
    arena: &mut CoreArena,
    host: &HostSignatures,
    term: ComputationId,
) -> Result<(), CheckRefusal>
{
    let cap = held_exit(arena, host);
    let unit = arena.value_type_unit();
    let returner = arena.comp_type_returner_with_effects(
        unit,
        gandr_core_term::effect::EffectRow::singleton(host.proc.clone()),
    );
    let mut context = CheckingContext::new(arena, CheckBudget::DEFAULT);
    context.binders().open(Zone::Intuitionistic, cap);
    let returner = form_comp_type(&mut context, returner)?;
    check_comp(&mut context, term, returner).map(|_| ())
}

/// An operation a capability scope answers hands the rest of the scope to
/// the scope's clause, so a clause whose operation's continuation holds an
/// endpoint the scope opened owes that continuation, and dropping it is
/// refused; an operation the host answers runs the rest once, and the
/// endpoint stays open across it (#1334).
#[test]
fn an_operation_a_scope_answers_captures_what_the_scope_opened_1334()
{
    let mut arena = CoreArena::new();
    let host = HostSignatures::new(&mut arena).unwrap();
    let protocol = end(&mut arena);
    // handle c : Proc { fork (s : end) { close(s) } as d; c.exit(1); close(d) }
    let exited = exit(&mut arena, &host, DeBruijnIndex::from(0_u32));
    let closed = Program::new(&mut arena).close();
    let parent = arena.computation_bind(exited, closed);
    let child_closed = Program::new(&mut arena).close();
    let exchange = fork(&mut arena, protocol, child_closed, parent);
    let (scoped, dropped) = dropping(&mut arena, &host, exchange);
    assert_eq!(
        check_unit(&mut arena, scoped),
        Err(CheckRefusal::Linearity {
            at: CoreNode::Term(TermNode::Computation(dropped)),
            defect: LinearityDefect::ContinuationUnspent { clause: dropped },
        }),
        "the scope's clause drops the close"
    );
    // handle c : Proc { fork (s : end) { close(s) } as d; close(d); c.exit(1) }
    let closed = Program::new(&mut arena).close();
    let exited_after = exit(&mut arena, &host, DeBruijnIndex::from(1_u32));
    let parent = arena.computation_bind(closed, exited_after);
    let child_closed = Program::new(&mut arena).close();
    let exchange = fork(&mut arena, protocol, child_closed, parent);
    let (scoped, _) = dropping(&mut arena, &host, exchange);
    assert_eq!(
        check_unit(&mut arena, scoped),
        Ok(()),
        "the same exit after the close leaves the clause nothing owed"
    );
    // c : Cap {exit}; fork (s : end) { close(s) } as d; c.exit(1); close(d)
    let child_closed = Program::new(&mut arena).close();
    let parent = parent_open(&mut arena, exited);
    let exchange = fork(&mut arena, protocol, child_closed, parent);
    assert_eq!(
        check_held_exit(&mut arena, &host, exchange),
        Ok(()),
        "the host answers the exit once, so the close runs once"
    );
}

/// A clause whose operation's continuation holds an endpoint owes that
/// continuation exactly one end: abandoning it or resuming it once checks,
/// and resuming it twice, reading it as a value, capturing it in a thunk and
/// handing it to a forked child are each refused by name (#1334).
#[test]
fn a_clause_ends_a_continuation_holding_an_obligation_once_1334()
{
    let mut arena = CoreArena::new();
    let host = HostSignatures::new(&mut arena).unwrap();
    let protocol = end(&mut arena);
    // fork (s : end) { close(s) } as d; c.exit(1); close(d)
    let exited = exit(&mut arena, &host, DeBruijnIndex::from(0_u32));
    let parent = parent_open(&mut arena, exited);
    let child_closed = Program::new(&mut arena).close();
    let subject = fork(&mut arena, protocol, child_closed, parent);
    let stack = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let unit = arena.value_unit();
    let replied = arena.computation_return(unit);
    // exit(code, k) => abandon(k)
    let abandoned = arena.computation_abandon(stack);
    let scoped = answering(&mut arena, &host, subject, abandoned);
    assert_eq!(
        check_unit(&mut arena, scoped),
        Ok(()),
        "abandoning the continuation ends it once"
    );
    // exit(code, k) => resume(k, pure ())
    let resumed = arena.computation_resume(stack, replied);
    let scoped = answering(&mut arena, &host, subject, resumed);
    assert_eq!(
        check_unit(&mut arena, scoped),
        Ok(()),
        "resuming it once runs the close once"
    );
    // exit(code, k) => resume(k, pure ()); resume(k, pure ())
    let outer = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let again = arena.computation_resume(outer, replied);
    let twice = arena.computation_bind(resumed, again);
    let scoped = answering(&mut arena, &host, subject, twice);
    assert_eq!(
        check_unit(&mut arena, scoped),
        Err(CheckRefusal::Linearity {
            at: CoreNode::Term(TermNode::Computation(again)),
            defect: LinearityDefect::ContinuationUsedTwice { clause: twice },
        }),
        "the second resumption would run the close twice"
    );
    // exit(code, k) => pure k
    let leaked = arena.computation_return(stack);
    let scoped = answering(&mut arena, &host, subject, leaked);
    assert_eq!(
        check_unit(&mut arena, scoped),
        Err(CheckRefusal::Linearity {
            at: CoreNode::Term(TermNode::Value(stack)),
            defect: LinearityDefect::ContinuationAsValue { clause: leaked },
        }),
        "a continuation read as a value may be ended anywhere, or never"
    );
    // exit(code, k) => force(thunk { abandon(k) })
    let suspended = arena.value_thunk(abandoned);
    let forced = arena.computation_force(suspended);
    let scoped = answering(&mut arena, &host, subject, forced);
    assert_eq!(
        check_unit(&mut arena, scoped),
        Err(CheckRefusal::Linearity {
            at: CoreNode::Term(TermNode::Value(suspended)),
            defect: LinearityDefect::ContinuationCaptured {
                clause: forced,
                by: Capture::Thunk,
            },
        }),
        "a thunk may be forced twice, or never"
    );
    // exit(code, k) => fork (s : end) { abandon(k); close(s) } as d; close(d)
    let closed = Program::new(&mut arena).close();
    let child = arena.computation_bind(abandoned, closed);
    let parent_closed = Program::new(&mut arena).close();
    let forked = fork(&mut arena, protocol, child, parent_closed);
    let scoped = answering(&mut arena, &host, subject, forked);
    assert_eq!(
        check_unit(&mut arena, scoped),
        Err(CheckRefusal::Linearity {
            at: CoreNode::Term(TermNode::Computation(forked)),
            defect: LinearityDefect::ContinuationCaptured {
                clause: forked,
                by: Capture::Task,
            },
        }),
        "a child may end the continuation after the clause returned"
    );
}

/// `operation; close(d)`.
///
/// # Specification
/// trivial.
fn parent_open(
    arena: &mut CoreArena,
    operation: ComputationId,
) -> ComputationId
{
    let closed = Program::new(arena).close();
    arena.computation_bind(operation, closed)
}

/// A forked child runs as its parent's peer, which no region bounds: it may
/// exercise a capability the host holds for the run, and one its scope
/// introduced is refused at the fork, since the scope could end while the
/// child runs (#1334).
#[test]
fn a_child_exercises_only_what_outlives_every_region_1334()
{
    let mut arena = CoreArena::new();
    let host = HostSignatures::new(&mut arena).unwrap();
    let protocol = end(&mut arena);
    // c : Cap {exit}; fork (s : end) { c.exit(1); close(s) } as d; close(d)
    let exited = exit(&mut arena, &host, DeBruijnIndex::from(0_u32));
    let child = parent_open(&mut arena, exited);
    let closed = Program::new(&mut arena).close();
    let exchange = fork(&mut arena, protocol, child, closed);
    assert_eq!(
        check_held_exit(&mut arena, &host, exchange),
        Ok(()),
        "the child exits through the run's capability"
    );
    // handle c : Proc { fork (s : end) { c.exit(1); close(s) } as d; close(d) }
    let (scoped, _) = dropping(&mut arena, &host, exchange);
    assert!(
        matches!(
            check_unit(&mut arena, scoped),
            Err(CheckRefusal::CapabilityEscaped { at, .. }) if at == TermNode::Computation(exchange)
        ),
        "the scope's capability would outlive the scope in the child"
    );
}

/// `Cap {operations}` over the host's file system, held by the host for the
/// run.
///
/// # Specification
/// trivial.
fn held_files(
    arena: &mut CoreArena,
    host: &HostSignatures,
    operations: &[gandr_core_term::effect::OperationName],
) -> ValueTypeId
{
    let authority = gandr_core_term::effect::EffectRow::authority(&[host
        .fs
        .restrict(operations)
        .expect("`Fs` performs these")])
    .expect("one interface");
    arena.value_type_capability(
        authority,
        gandr_core_term::effect::capability::CapabilityGrade::Durable,
        gandr_core_term::effect::capability::Region::Held,
    )
}

/// A file operation the fork witnesses perform on `"notes"`.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
enum Notes
{
    /// `read("notes")`, which changes nothing.
    Read,
    /// `write(("notes", "notes"))`, which changes the file system.
    Write,
}

/// The file operation `operation` on `"notes"`: exercised through the
/// variable `capability` of the run, or performed by name without one.
///
/// # Specification
/// trivial.
fn on_notes(
    arena: &mut CoreArena,
    host: &HostSignatures,
    capability: Option<DeBruijnIndex>,
    operation: Notes,
) -> ComputationId
{
    let path = arena.value_literal(Literal::Text(StringLiteral::new(String::from("notes"))));
    let (operation, payload) = match operation {
        Notes::Read => ("read", path),
        Notes::Write => ("write", arena.value_tuple(&[path, path])),
    };
    match capability {
        Some(index) => {
            let capability = arena.value_variable(Zone::Intuitionistic, index);
            arena.computation_exercise(capability, host.fs.clone(), operation.into(), payload)
        },
        None => arena.computation_perform(host.fs.clone(), operation.into(), payload),
    }
}

/// Check `term` against the returner of the unit at the row `Fs`, under a
/// `Cap {read}` and then a `Cap {write}` the host holds for the run.
///
/// # Specification
/// trivial.
fn check_holding_files(
    arena: &mut CoreArena,
    host: &HostSignatures,
    term: ComputationId,
) -> Result<(), CheckRefusal>
{
    let reader = held_files(arena, host, &["read".into()]);
    let writer = held_files(arena, host, &["write".into()]);
    let unit = arena.value_type_unit();
    let returner = arena.comp_type_returner_with_effects(
        unit,
        gandr_core_term::effect::EffectRow::singleton(host.fs.clone()),
    );
    let mut context = CheckingContext::new(arena, CheckBudget::DEFAULT);
    context.binders().open(Zone::Intuitionistic, reader);
    context.binders().open(Zone::Intuitionistic, writer);
    let returner = form_comp_type(&mut context, returner)?;
    check_comp(&mut context, term, returner).map(|_| ())
}

/// The operations the held capability type `capability` grants, each as
/// `Interface.operation`.
///
/// # Specification
/// trivial.
fn granted(
    arena: &CoreArena,
    capability: ValueTypeId,
) -> Vec<String>
{
    let Some(&gandr_core_term::ValueType::Capability {
        ref authority,
        region: gandr_core_term::effect::capability::Region::Held,
        ..
    }) = arena.value_type(capability)
    else {
        panic!("a footprint is named as a held capability");
    };
    authority
        .signatures()
        .flat_map(|signature| {
            signature.operations().map(|operation| {
                alloc::format!("{}.{}", signature.name().as_ref(), operation.name.as_ref())
            })
        })
        .collect()
}

/// The two halves of a fork run as peers, so they may share a host interface
/// only to read through it: a reader beside a writer is refused naming each
/// half's footprint and what they share; two readers check; a writer beside a
/// half that uses no capability checks; two halves writing by name, through
/// no capability, once each has closed its end, are refused; a task the child
/// forks counts toward the child (#2789).
#[test]
fn two_halves_share_a_capability_only_to_read_through_it_2789()
{
    let mut arena = CoreArena::new();
    let host = HostSignatures::new(&mut arena).unwrap();
    let protocol = end(&mut arena);
    let (reader, writer) = (DeBruijnIndex::from(1_u32), DeBruijnIndex::from(0_u32));
    // r : Cap {read}, w : Cap {write};
    // fork (s : end) { r.read("notes"); close(s) } as d; w.write(("notes",
    // "notes")); close(d)
    let read = on_notes(&mut arena, &host, Some(reader), Notes::Read);
    let child = parent_open(&mut arena, read);
    let write = on_notes(&mut arena, &host, Some(writer), Notes::Write);
    let parent = parent_open(&mut arena, write);
    let racing = fork(&mut arena, protocol, child, parent);
    let refused = check_holding_files(&mut arena, &host, racing);
    let Err(CheckRefusal::FootprintsOverlap {
        at,
        child,
        parent,
        shared,
    }) = refused
    else {
        panic!("a reader beside a writer on one interface is refused: {refused:?}");
    };
    assert_eq!(at, racing, "the fork is refused");
    assert_eq!(
        [
            granted(&arena, child),
            granted(&arena, parent),
            granted(&arena, shared)
        ],
        [
            alloc::vec![String::from("Fs.read")],
            alloc::vec![String::from("Fs.write")],
            alloc::vec![String::from("Fs.read"), String::from("Fs.write")],
        ],
        "each half's footprint is what it may do, and the shared one both"
    );
    // fork (s : end) { r.read("notes"); close(s) } as d; r.read("notes"); close(d)
    let read = on_notes(&mut arena, &host, Some(reader), Notes::Read);
    let child = parent_open(&mut arena, read);
    let read = on_notes(&mut arena, &host, Some(reader), Notes::Read);
    let parent = parent_open(&mut arena, read);
    let reading = fork(&mut arena, protocol, child, parent);
    assert_eq!(
        check_holding_files(&mut arena, &host, reading),
        Ok(()),
        "two readers share the file system"
    );
    // fork (s : end) { w.write(("notes", "notes")); close(s) } as d; close(d)
    let write = on_notes(&mut arena, &host, Some(writer), Notes::Write);
    let child = parent_open(&mut arena, write);
    let closed = Program::new(&mut arena).close();
    let alone = fork(&mut arena, protocol, child, closed);
    assert_eq!(
        check_holding_files(&mut arena, &host, alone),
        Ok(()),
        "a writer beside a half that touches no file is separate from it"
    );
    // fork (s : end) { close(s); write(("notes", "notes")) } as d; close(d);
    // write(("notes", "notes"))
    let closed = Program::new(&mut arena).close();
    let write = on_notes(&mut arena, &host, None, Notes::Write);
    let child = arena.computation_bind(closed, write);
    let closed = Program::new(&mut arena).close();
    let write = on_notes(&mut arena, &host, None, Notes::Write);
    let parent = arena.computation_bind(closed, write);
    let by_name = fork(&mut arena, protocol, child, parent);
    let refused = check_holding_files(&mut arena, &host, by_name);
    assert!(
        matches!(refused, Err(CheckRefusal::FootprintsOverlap { at, .. }) if at == by_name),
        "two halves writing by name share the file system to change it: {refused:?}"
    );
    // fork (s : end) {
    //   fork (t : end) { w.write(("notes", "notes")); close(t) } as e; close(e);
    // close(s) } as d; w.write(("notes", "notes")); close(d)
    let write = on_notes(&mut arena, &host, Some(writer), Notes::Write);
    let inner_child = parent_open(&mut arena, write);
    let inner_end = Program::new(&mut arena).close();
    let outer_end = arena.computation_session(SessionAction::Close {
        endpoint: DeBruijnIndex::from(1_u32),
    });
    let inner_parent = arena.computation_bind(inner_end, outer_end);
    let inner = fork(&mut arena, protocol, inner_child, inner_parent);
    let write = on_notes(&mut arena, &host, Some(writer), Notes::Write);
    let parent = parent_open(&mut arena, write);
    let nested = fork(&mut arena, protocol, inner, parent);
    let refused = check_holding_files(&mut arena, &host, nested);
    assert!(
        matches!(refused, Err(CheckRefusal::FootprintsOverlap { at, .. }) if at == nested),
        "a task the child forks writes for the child, beside the writing parent: {refused:?}"
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
    let mut program = Program::new(&mut arena);
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

/// A selection names a label the protocol offers, and an offer answers
/// exactly the labels the protocol offers: a label it lacks and arms that
/// miss one are each refused by that defect on the acting end.
#[test]
fn a_selection_or_offer_off_the_protocol_s_labels_is_refused()
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
    let mut program = Program::new(&mut arena);
    let first = program.close();
    let second = program.close();
    let both = program.offer(&[(Spelled("a"), first), (Spelled("b"), second)]);
    let only_a = program.close();
    let one = program.offer(&[(Spelled("a"), only_a)]);
    let parent_closed = program.close();
    let stray = program.select(Spelled("z"), parent_closed);
    let parent_closed = program.close();
    let parent = program.select(Spelled("a"), parent_closed);
    let labelled = fork(&mut arena, protocol, both, stray);
    let armed = fork(&mut arena, protocol, one, parent);
    for (exchange, side, defect) in [
        (labelled, ForkSide::Parent, ProtocolDefect::Label),
        (armed, ForkSide::Child, ProtocolDefect::Arms),
    ] {
        let refused = check_unit(&mut arena, exchange);
        assert!(
            matches!(
                refused,
                Err(CheckRefusal::SessionMismatch { endpoint, defect: named, .. })
                    if endpoint == Endpoint { fork: exchange, side } && named == defect
            ),
            "{defect:?} on the {side:?} end: {refused:?}"
        );
    }
}

/// Offer arms that leave the endpoint open agree when they leave it at
/// convertible states, so the child's leftover endpoint is what is refused,
/// and disagree when they leave it at different states.
#[test]
fn offer_arms_leaving_an_endpoint_open_agree_on_its_state()
{
    let offered = |arena: &mut CoreArena, syntax: Vec<ProtocolSyntax>| {
        let protocol = session(arena, syntax, &[]);
        let unit = arena.value_unit();
        let first = arena.computation_return(unit);
        let other = arena.computation_return(unit);
        let mut program = Program::new(arena);
        let offer = program.offer(&[(Spelled("a"), first), (Spelled("b"), other)]);
        let parent_closed = program.close();
        let parent = program.select(Spelled("a"), parent_closed);
        let exchange = fork(arena, protocol, offer, parent);
        (check_unit(arena, exchange), exchange, first, other)
    };
    let offer = |branches: [usize; 2]| {
        ProtocolSyntax::Offer(BTreeMap::from([
            (label(Spelled("a")), ProtocolState::from(branches[0])),
            (label(Spelled("b")), ProtocolState::from(branches[1])),
        ]))
    };
    let mut arena = CoreArena::new();
    // &{ a : end, b : end }: the arms leave the endpoint at two `end` states,
    // one type each, which convert.
    let (checked, ..) = offered(&mut arena, alloc::vec![
        offer([1, 2]),
        ProtocolSyntax::End,
        ProtocolSyntax::End
    ]);
    assert!(
        matches!(
            checked,
            Err(CheckRefusal::Linearity {
                defect: LinearityDefect::Residue { .. },
                ..
            })
        ),
        "both arms leave the endpoint at `end`, which the child leaves open: {checked:?}"
    );
    // &{ a : end, b : &{ z : end } }: the arms leave it at different states.
    let later = ProtocolSyntax::Offer(BTreeMap::from([(
        label(Spelled("z")),
        ProtocolState::from(3_usize),
    )]));
    let (checked, exchange, first, other) = offered(&mut arena, alloc::vec![
        offer([1, 2]),
        ProtocolSyntax::End,
        later,
        ProtocolSyntax::End
    ]);
    assert_eq!(
        checked,
        Err(CheckRefusal::Linearity {
            at: CoreNode::Term(TermNode::Computation(other)),
            defect: LinearityDefect::ArmsDisagree {
                endpoint: child(exchange),
                first,
                other,
            },
        }),
        "the arms leave the endpoint at different states"
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

/// `!end. end`: one endpoint at `end` sent, then the end.
///
/// # Specification
/// trivial.
fn delegating(arena: &mut CoreArena) -> ValueTypeId
{
    let ended = end(arena);
    session(
        arena,
        alloc::vec![
            ProtocolSyntax::Send {
                payload: PayloadSlot::from(0_usize),
                next: ProtocolState::from(1_usize),
            },
            ProtocolSyntax::End,
        ],
        &[ended],
    )
}

/// What the sender does with an end it has sent.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum AfterSend
{
    /// Leaves it to the receiver.
    Leaves,
    /// Closes it again.
    Closes,
}

/// The sending half of an exchange over [`delegating`]: `fork (e : end) {
/// close(e) } as d ; send(c, d) ; close(c)`, with `close(d)` after the send
/// when `after` closes it. Answers the inner fork and the `close(d)`.
///
/// # Specification
/// trivial.
fn delegator(
    arena: &mut CoreArena,
    after: AfterSend,
) -> (ComputationId, ComputationId)
{
    let ended = end(arena);
    let inner_child = Program::new(arena).close();
    // Under the inner fork, `d` is index 0 and the outer `c` index 1.
    let sent = arena.value_variable(Zone::Linear, DeBruijnIndex::from(0_u32));
    let mut program = Program::new(arena);
    let close_outer = program.act(SessionAction::Close {
        endpoint: DeBruijnIndex::from(1_u32),
    });
    let reused = program.act(SessionAction::Close {
        endpoint: DeBruijnIndex::from(0_u32),
    });
    let after_send = if after == AfterSend::Closes {
        program.arena.computation_bind(reused, close_outer)
    }
    else {
        close_outer
    };
    let inner_parent = program.then(
        SessionAction::Send {
            endpoint: DeBruijnIndex::from(1_u32),
            payload: sent,
        },
        after_send,
    );
    (fork(arena, ended, inner_child, inner_parent), reused)
}

#[test]
fn a_delegated_endpoint_leaves_its_sender()
{
    let mut arena = CoreArena::new();
    let protocol = delegating(&mut arena);
    let (inner, _) = delegator(&mut arena, AfterSend::Leaves);
    // `recv(c) as x ; close(x) ; close(c)`
    let parent = Program::new(&mut arena).receive(|program| {
        let outer = program.close();
        program.then(
            SessionAction::Close {
                endpoint: DeBruijnIndex::from(0_u32),
            },
            outer,
        )
    });
    let exchange = fork(&mut arena, protocol, inner, parent);
    assert_eq!(
        check_unit(&mut arena, exchange),
        Ok(()),
        "the sent end is consumed at the send and closed by the receiver"
    );

    let (inner, reused) = delegator(&mut arena, AfterSend::Closes);
    let exchange = fork(&mut arena, protocol, inner, parent);
    assert_eq!(
        check_unit(&mut arena, exchange),
        Err(CheckRefusal::Linearity {
            at: CoreNode::Term(TermNode::Computation(reused)),
            defect: LinearityDefect::Closed {
                endpoint: Endpoint {
                    fork: inner,
                    side: ForkSide::Parent,
                },
            },
        }),
        "an end sent away is no longer the sender's to close"
    );
}

/// An end its sender has already closed is no end to delegate: the send
/// naming it is refused, at the payload, as acting on a closed end.
#[test]
fn a_closed_endpoint_is_not_delegated()
{
    let mut arena = CoreArena::new();
    let protocol = delegating(&mut arena);
    let ended = end(&mut arena);
    let inner_child = Program::new(&mut arena).close();
    // `fork (e : end) { close(e) } as d ; close(d) ; send(c, d) ; close(c)`
    let sent = arena.value_variable(Zone::Linear, DeBruijnIndex::from(0_u32));
    let mut program = Program::new(&mut arena);
    let close_outer = program.act(SessionAction::Close {
        endpoint: DeBruijnIndex::from(1_u32),
    });
    let closed_first = program.act(SessionAction::Close {
        endpoint: DeBruijnIndex::from(0_u32),
    });
    let send = program.then(
        SessionAction::Send {
            endpoint: DeBruijnIndex::from(1_u32),
            payload: sent,
        },
        close_outer,
    );
    let inner_parent = program.arena.computation_bind(closed_first, send);
    let inner = fork(&mut arena, ended, inner_child, inner_parent);
    let parent = Program::new(&mut arena).receive(|program| {
        let outer = program.close();
        program.then(
            SessionAction::Close {
                endpoint: DeBruijnIndex::from(0_u32),
            },
            outer,
        )
    });
    let exchange = fork(&mut arena, protocol, inner, parent);
    assert_eq!(
        check_unit(&mut arena, exchange),
        Err(CheckRefusal::Linearity {
            at: CoreNode::Term(TermNode::Value(sent)),
            defect: LinearityDefect::Closed {
                endpoint: Endpoint {
                    fork: inner,
                    side: ForkSide::Parent,
                },
            },
        }),
        "a closed end is not the sender's to send"
    );
}

#[test]
fn a_received_endpoint_is_acted_on_and_must_be_closed()
{
    let mut arena = CoreArena::new();
    let protocol = delegating(&mut arena);
    let (inner, _) = delegator(&mut arena, AfterSend::Leaves);
    // `recv(c) as x ; close(c)`, `x` left open
    let parent = Program::new(&mut arena).receive(Program::close);
    let exchange = fork(&mut arena, protocol, inner, parent);
    let refused = check_unit(&mut arena, exchange);
    assert!(
        matches!(
            refused,
            Err(CheckRefusal::Linearity {
                at: CoreNode::Term(TermNode::Computation(at)),
                defect: LinearityDefect::Residue {
                    endpoint: Endpoint { fork, side: ForkSide::Received },
                    ..
                },
            }) if at == parent && fork == parent
        ),
        "a received end is the receiver's to close: {refused:?}"
    );
}

/// A linear variable nothing binds is unbound in the linear zone, and a
/// buffer read as a value, rather than returned, is refused by its
/// placement.
#[test]
fn a_linear_read_of_nothing_or_of_a_buffer_is_refused()
{
    let mut arena = CoreArena::new();
    let stray = arena.value_variable(Zone::Linear, DeBruijnIndex::from(3_u32));
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    assert_eq!(
        crate::judgement::synthesise_value(&mut context, stray).map(|_| ()),
        Err(CheckRefusal::UnboundIndex {
            at: stray,
            zone: Zone::Linear,
            index: DeBruijnIndex::from(3_u32),
            depth: gandr_core_term::BinderDepth::default(),
        }),
        "no linear binder is open"
    );
    let ring = ring(&mut arena);
    let mut read = None;
    let (copied, placed) = allocated(&mut arena, &ring, |arena, live| {
        read = Some(live);
        let single = arena.value_tuple(&[live]);
        let projected =
            arena.computation_tuple_projection(single, gandr_kernel_term::Component::from(0_usize));
        let empty = arena.value_unit();
        let finished = arena.computation_return(empty);
        arena.computation_bind(projected, finished)
    });
    let read = read.expect("the read was minted");
    assert_eq!(
        check_ring(&mut arena, ring, copied),
        Err(CheckRefusal::Linearity {
            at: CoreNode::Term(TermNode::Value(read)),
            defect: LinearityDefect::BufferRead { site: placed },
        }),
        "a buffer is returned, never read"
    );
}

#[test]
fn an_endpoint_read_as_a_value_is_refused()
{
    let mut arena = CoreArena::new();
    let ended = end(&mut arena);
    let itself = arena.value_variable(Zone::Linear, DeBruijnIndex::from(0_u32));
    let escaped = arena.computation_return(itself);
    let parent = Program::new(&mut arena).close();
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

/// An inner fork's child may take an outer endpoint its parent leaves alone;
/// when both halves name it, it is used twice.
#[test]
fn an_inner_child_takes_an_outer_endpoint_only_when_its_parent_leaves_it()
{
    let exchange = |arena: &mut CoreArena, parent_closes_outer| {
        let ended = end(arena);
        let closes = |arena: &mut CoreArena, outer| {
            let mut program = Program::new(arena);
            let own = program.close();
            if outer {
                program.then(
                    SessionAction::Close {
                        endpoint: DeBruijnIndex::from(1_u32),
                    },
                    own,
                )
            }
            else {
                own
            }
        };
        let inner_child = closes(arena, true);
        let inner_parent = closes(arena, parent_closes_outer);
        let inner = fork(arena, ended, inner_child, inner_parent);
        let outer_parent = Program::new(arena).close();
        let outer = fork(arena, ended, inner, outer_parent);
        (check_unit(arena, outer), outer, inner)
    };
    let mut arena = CoreArena::new();
    let (checked, ..) = exchange(&mut arena, false);
    assert_eq!(checked, Ok(()), "the inner child takes the outer endpoint");
    let (checked, outer, inner) = exchange(&mut arena, true);
    assert_eq!(
        checked,
        Err(CheckRefusal::Linearity {
            at: CoreNode::Term(TermNode::Computation(inner)),
            defect: LinearityDefect::UsedTwice {
                endpoint: child(outer),
            },
        }),
        "both halves of the inner fork name the outer endpoint"
    );
}

/// An inner child that takes an outer endpoint must finish it: one it leaves
/// open is a residue of the inner fork, not of the outer one.
#[test]
fn an_outer_endpoint_an_inner_child_leaves_open_is_its_residue()
{
    let mut arena = CoreArena::new();
    let ended = end(&mut arena);
    // ⊕{ a : end }
    let choosing = session(
        &mut arena,
        alloc::vec![
            ProtocolSyntax::Select(BTreeMap::from([(
                label(Spelled("a")),
                ProtocolState::from(1_usize),
            )])),
            ProtocolSyntax::End,
        ],
        &[],
    );
    let mut program = Program::new(&mut arena);
    let own = program.close();
    let inner_child = program.then(
        SessionAction::Select {
            endpoint: DeBruijnIndex::from(1_u32),
            label: label(Spelled("a")),
        },
        own,
    );
    let inner_parent = program.close();
    let inner = fork(&mut arena, ended, inner_child, inner_parent);
    let closed = Program::new(&mut arena).close();
    let outer_parent = Program::new(&mut arena).offer(&[(Spelled("a"), closed)]);
    let outer = fork(&mut arena, choosing, inner, outer_parent);
    let refused = check_unit(&mut arena, outer);
    assert!(
        matches!(
            refused,
            Err(CheckRefusal::Linearity {
                at: CoreNode::Term(TermNode::Computation(at)),
                defect: LinearityDefect::Residue { .. },
            }) if at == inner
        ),
        "the inner fork leaves the outer endpoint open: {refused:?}"
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
    // \n. fork (c : end) { close(c) } as d ; close(d) ; return n
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
            .map(crate::Judged::verdict)
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
    // fork (c : !String. end) { send(c, "task") ; close(c) } as d ;
    //     recv(d) as task ; close(d) ; return task
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
    // fork (c : ?(Integer + Unit). end) { recv(c) as order ; close(c) } as d ;
    //     send(d, inj₀ 1) ; close(d)
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
    let one = arena.value_literal(crate::fixture::integer_literal());
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
    let verdicts: Vec<_> = report.judged().iter().map(crate::Judged::verdict).collect();
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

/// A held value may be read by a branch, which runs once; any other capture
/// is refused by its capturer.
#[test]
fn a_held_value_is_captured_by_a_branch_only()
{
    let mut arena = CoreArena::new();
    let at = seat(&mut arena);
    let node = CoreNode::Term(TermNode::Computation(at));
    let held = Resident::Held { at };
    assert_eq!(captured(node, held, Capture::Branch), Ok(()));
    for by in [
        Capture::Thunk,
        Capture::Recursion,
        Capture::Stack,
        Capture::Continuation,
    ] {
        assert_eq!(
            captured(node, held, by),
            Err(CheckRefusal::Access {
                at: node,
                defect: AccessDefect::HeldCaptured { by },
            })
        );
    }
}

/// A buffer is read by a branch only, whose arms each return it; a world's
/// capability and a clause's continuation are captured by nothing, each
/// refused by its own name with its capturer.
#[test]
fn a_buffer_capability_or_continuation_capture_is_refused_by_its_name()
{
    use gandr_core_term::world::World;

    let mut arena = CoreArena::new();
    let at = seat(&mut arena);
    let node = CoreNode::Term(TermNode::Computation(at));
    let buffer = Resident::Buffer { at };
    assert_eq!(
        captured(node, buffer, Capture::Branch),
        Ok(()),
        "a branch returns the buffer in each arm"
    );
    for by in [
        Capture::Branch,
        Capture::Thunk,
        Capture::Recursion,
        Capture::Stack,
        Capture::Continuation,
    ] {
        if by != Capture::Branch {
            assert_eq!(
                captured(node, buffer, by),
                Err(CheckRefusal::Linearity {
                    at: node,
                    defect: LinearityDefect::BufferRead { site: at },
                }),
                "{by:?} reads a buffer it cannot return"
            );
        }
        assert_eq!(
            captured(node, Resident::Capability { world: World::Host }, by),
            Err(CheckRefusal::Located {
                at: node,
                defect: crate::worlds::LocatedDefect::CapabilityCaptured {
                    world: World::Host,
                    by,
                },
            }),
            "{by:?} captures a world's capability"
        );
        assert_eq!(
            captured(node, Resident::Continuation { clause: at }, by),
            Err(CheckRefusal::Linearity {
                at: node,
                defect: LinearityDefect::ContinuationCaptured { clause: at, by },
            }),
            "{by:?} captures a continuation"
        );
    }
}

/// A type formed at an intuitionistic depth reads unchanged at that depth and
/// shifted past every binder opened since.
#[test]
fn a_type_is_read_shifted_past_the_binders_opened_since_it_was_formed()
{
    let mut arena = CoreArena::new();
    let unit_type = arena.value_type_unit();
    let variable = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let open = arena.value_type_element(variable, Level::zero());
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let mut machine = Machine {
        context: &mut context,
        frames: Vec::new(),
        owner: Goal::Form(TypeNode::Value(unit_type)),
        native_types: Vec::new(),
        conversions: crate::conversion::ConversionCount::default(),
        remaining: 1_usize,
        marking: Marking::Strict,
        anchors: Vec::new(),
        marks: Vec::new(),
        sessions: Sessions::new(
            gandr_core_term::BinderDepth::default(),
            crate::capability::Reach::Clear,
        ),
        root: Maybe::Absent(crate::respect::root::Absent::Unmarked),
        staged_motives: Vec::new(),
    };
    let formed = gandr_core_term::BinderDepth::default();
    assert_eq!(
        machine.here(open, formed),
        Ok(open),
        "read where it was formed"
    );
    machine
        .context
        .binders()
        .open(Zone::Intuitionistic, unit_type);
    let read = machine.here(open, formed).unwrap();
    let Some(&gandr_core_term::ValueType::Element { code, .. }) =
        machine.context.arena_mut().value_type(read)
    else {
        panic!("an element reads as an element");
    };
    assert_eq!(
        machine.context.arena_mut().value(code),
        Some(&gandr_core_term::Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(1_u32),
        }),
        "read one binder later, its variable names the same binder"
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
            at: crate::refusal::CoreNode::Term(crate::refusal::TermNode::Computation(
                carrying_fork
            )),
            defect: crate::access::AccessDefect::KeptEscaped,
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
                wanted: crate::refusal::ExpectedShape::Session,
                ..
            }) if at == unprotocolled
        ),
        "a fork's protocol is a session type"
    );
}

/// The host's buffer interface.
///
/// # Specification
/// trivial.
fn ring(arena: &mut CoreArena) -> gandr_core_term::effect::EffectSig
{
    gandr_core_term::effect::host::HostSignatures::new(arena)
        .expect("the host signatures are consistent")
        .ring
}

/// The program `run b <- alloc(0) ; body` over `ring`, with `b` placed live
/// over `body`, which `rest` mints from the placement's linear variable; and
/// the placement.
///
/// # Specification
/// trivial.
fn allocated(
    arena: &mut CoreArena,
    ring: &gandr_core_term::effect::EffectSig,
    rest: impl FnOnce(&mut CoreArena, ValueId) -> ComputationId,
) -> (ComputationId, ComputationId)
{
    let size = arena.value_literal(crate::fixture::integer_literal());
    let alloc = arena.computation_perform(ring.clone(), "alloc".into(), size);
    let live = arena.value_variable(Zone::Linear, DeBruijnIndex::from(0_u32));
    let body = rest(arena, live);
    let reply = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let place = arena.computation_session(SessionAction::Place {
        payload: reply,
        body,
    });
    (arena.computation_bind(alloc, place), place)
}

/// Check `term` against the returner of the unit performing `ring`.
///
/// # Specification
/// trivial.
fn check_ring(
    arena: &mut CoreArena,
    ring: gandr_core_term::effect::EffectSig,
    term: ComputationId,
) -> Result<(), CheckRefusal>
{
    let unit = arena.value_type_unit();
    let returner = arena
        .comp_type_returner_with_effects(unit, gandr_core_term::effect::EffectRow::singleton(ring));
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

#[test]
fn an_allocated_buffer_is_returned_once()
{
    let mut arena = CoreArena::new();
    let ring = ring(&mut arena);
    let (freed, _) = allocated(&mut arena, &ring, |arena, live| {
        arena.computation_perform(ring.clone(), "free".into(), live)
    });
    assert_eq!(
        check_ring(&mut arena, ring.clone(), freed),
        Ok(()),
        "the free returns the buffer the allocation placed"
    );
    let mut second = None;
    let (twice, twice_placed) = allocated(&mut arena, &ring, |arena, live| {
        let first = arena.computation_perform(ring.clone(), "free".into(), live);
        let again = arena.value_variable(Zone::Linear, DeBruijnIndex::from(0_u32));
        second = Some(again);
        let then = arena.computation_perform(ring.clone(), "free".into(), again);
        arena.computation_bind(first, then)
    });
    let again = second.expect("the second free was minted");
    assert_eq!(
        check_ring(&mut arena, ring.clone(), twice),
        Err(CheckRefusal::Linearity {
            at: CoreNode::Term(TermNode::Value(again)),
            defect: LinearityDefect::BufferReturnedTwice { site: twice_placed },
        }),
        "the second free returns a buffer already returned"
    );
    let (kept, kept_placed) = allocated(&mut arena, &ring, |arena, _live| {
        let unit = arena.value_unit();
        arena.computation_return(unit)
    });
    assert_eq!(
        check_ring(&mut arena, ring, kept),
        Err(CheckRefusal::Linearity {
            at: CoreNode::Term(TermNode::Computation(kept_placed)),
            defect: LinearityDefect::BufferUnreturned { site: kept_placed },
        }),
        "a body that never frees its buffer is refused at the placement"
    );
}

/// The program `x <- (return inl(()) : F (1 + 1)) ; case x { _ => on_left,
/// _ => on_right }` placed live over `alloc(0)` as `allocated` builds it, each
/// arm minted from the placement's linear variable; the program, the
/// placement and the right arm.
///
/// # Specification
/// trivial.
fn branched(
    arena: &mut CoreArena,
    ring: &gandr_core_term::effect::EffectSig,
    on_left: impl FnOnce(&mut CoreArena) -> ComputationId,
    on_right: impl FnOnce(&mut CoreArena) -> ComputationId,
) -> (ComputationId, ComputationId, ComputationId)
{
    let mut right = None;
    let (program, placed) = allocated(arena, ring, |arena, _live| {
        let unit_type = arena.value_type_unit();
        let two = arena.value_type_sum(&[unit_type, unit_type]);
        let twos = arena.comp_type_returner(two);
        let unit = arena.value_unit();
        let left = arena.value_injection(gandr_core_term::Summand::from(0_usize), unit);
        let returned = arena.computation_return(left);
        let ascribed = arena.computation_ascribe(returned, twos);
        let left_arm = on_left(arena);
        let right_arm = on_right(arena);
        right = Some(right_arm);
        let x = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let case = arena.computation_case(x, &[left_arm, right_arm]);
        arena.computation_bind(ascribed, case)
    });
    (program, placed, right.expect("the right arm was minted"))
}

#[test]
fn a_case_s_arms_each_return_the_placed_buffer_1792()
{
    let mut arena = CoreArena::new();
    let ring = ring(&mut arena);
    let free = |arena: &mut CoreArena| {
        let live = arena.value_variable(Zone::Linear, DeBruijnIndex::from(0_u32));
        arena.computation_perform(ring.clone(), "free".into(), live)
    };
    let kept = |arena: &mut CoreArena| {
        let unit = arena.value_unit();
        arena.computation_return(unit)
    };
    let (both, ..) = branched(&mut arena, &ring, free, free);
    assert_eq!(
        check_ring(&mut arena, ring.clone(), both),
        Ok(()),
        "each arm returns the buffer the case found live"
    );
    let (one, placed, right) = branched(&mut arena, &ring, free, kept);
    assert_eq!(
        check_ring(&mut arena, ring.clone(), one),
        Err(CheckRefusal::Linearity {
            at: CoreNode::Term(TermNode::Computation(right)),
            defect: LinearityDefect::BufferUnreturned { site: placed },
        }),
        "the right arm keeps the buffer the left arm returned"
    );
    let (other, placed, right) = branched(&mut arena, &ring, kept, free);
    assert_eq!(
        check_ring(&mut arena, ring, other),
        Err(CheckRefusal::Linearity {
            at: CoreNode::Term(TermNode::Computation(right)),
            defect: LinearityDefect::BufferUnreturned { site: placed },
        }),
        "the right arm returns the buffer the left arm kept"
    );
}

#[test]
fn a_buffer_no_slot_holds_is_never_returned()
{
    let mut arena = CoreArena::new();
    let ring = ring(&mut arena);
    let size = arena.value_literal(crate::fixture::integer_literal());
    let alloc = arena.computation_perform(ring.clone(), "alloc".into(), size);
    let reply = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let free = arena.computation_perform(ring.clone(), "free".into(), reply);
    let unplaced = arena.computation_bind(alloc, free);
    assert_eq!(
        check_ring(&mut arena, ring, unplaced),
        Err(CheckRefusal::Linearity {
            at: CoreNode::Term(TermNode::Value(reply)),
            defect: LinearityDefect::BufferRead { site: free },
        }),
        "a reply no placement holds live is no buffer to return: returning it would forge one"
    );
}
