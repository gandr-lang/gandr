//! The protocols, programs, endpoints and forks that the session judgement's
//! witnesses build. Its unit tests and the tests that readmit through the
//! bridge read them both.

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;

use gandr_core_term::CompTypeId;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::session::PayloadCount;
use gandr_core_term::session::PayloadSlot;
use gandr_core_term::session::Protocol;
use gandr_core_term::session::ProtocolState;
use gandr_core_term::session::ProtocolSyntax;
use gandr_core_term::session::RecursionIndex;
use gandr_core_term::session::SessionAction;
use gandr_core_term::session::SessionType;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldLabel;
use gandr_kernel_term::Literal;
use gandr_kernel_term::StringLiteral;

use crate::CheckBudget;
use crate::CheckRefusal;
use crate::CheckingContext;
use crate::check_comp;
use crate::form_comp_type;
use crate::session::Endpoint;
use crate::session::ForkSide;

/// A label or a string as a test spells it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Spelled(pub &'static str);

/// The label `spelled` names.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub fn label(Spelled(text): Spelled) -> FieldLabel
{
    FieldLabel::from(String::from(text))
}

/// The session type over `syntax` rooted at its first node, its payloads
/// `payloads`.
///
/// # Specification
/// trivial.
#[inline]
pub fn session(
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
#[inline]
pub fn seat_end(arena: &mut CoreArena) -> ValueTypeId
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
#[inline]
pub fn end(arena: &mut CoreArena) -> ValueTypeId
{
    session(arena, alloc::vec![ProtocolSyntax::End], &[])
}

/// The terms one endpoint's program is built of, the endpoint the linear
/// binder under the received values the program is inside.
pub struct Program<'arena>
{
    /// The arena.
    pub arena: &'arena mut CoreArena,
    /// How many receives' binders stand inside the endpoint's.
    pub received: u32,
}

impl<'arena> Program<'arena>
{
    /// A program on the innermost linear binder.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn new(arena: &'arena mut CoreArena) -> Self
    {
        Self { arena, received: 0 }
    }

    /// The endpoint, under the receives the program is inside.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn endpoint(&self) -> DeBruijnIndex
    {
        DeBruijnIndex::from(self.received)
    }

    /// `x <- action ; rest`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn then(
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
    #[inline]
    pub fn act(
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
    #[inline]
    pub fn text(
        &mut self,
        Spelled(text): Spelled,
    ) -> ValueId
    {
        self.arena
            .value_literal(Literal::Text(StringLiteral::new(String::from(text))))
    }

    /// `close c`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn close(&mut self) -> ComputationId
    {
        self.act(SessionAction::Close {
            endpoint: self.endpoint(),
        })
    }

    /// `select c l ; rest`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn select(
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

    /// `send c text ; rest`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn send(
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

    /// `let x = recv c; rest`, `rest` built under the receive's binder.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn receive<R>(
        &mut self,
        rest: R,
    ) -> ComputationId
    where
        R: FnOnce(&mut Self) -> ComputationId,
    {
        let endpoint = self.endpoint();
        self.received = self.received.saturating_add(1);
        let body = rest(self);
        self.received = self.received.saturating_sub(1);
        self.act(SessionAction::Receive { endpoint, body })
    }

    /// `offer c { l => arm, … }`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn offer(
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
#[inline]
pub fn seat(arena: &mut CoreArena) -> ComputationId
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
#[inline]
pub fn operator(arena: &mut CoreArena) -> ComputationId
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

/// `let d = fork (c : protocol) { child }; parent`.
///
/// # Specification
/// trivial.
#[inline]
pub fn fork(
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
/// # Errors
/// The judgement's refusal of `term`.
///
/// # Specification
/// trivial.
#[inline]
pub fn check_unit(
    arena: &mut CoreArena,
    term: ComputationId,
) -> Result<(), CheckRefusal>
{
    let unit = arena.value_type_unit();
    let returner = arena.comp_type_returner(unit);
    check_at(arena, term, returner)
}

/// Check `term` against `expected`, formed first.
///
/// # Errors
/// The refusal of `expected`'s formation, or the judgement's refusal of
/// `term`.
///
/// # Specification
/// trivial.
#[inline]
pub fn check_at(
    arena: &mut CoreArena,
    term: ComputationId,
    expected: CompTypeId,
) -> Result<(), CheckRefusal>
{
    let mut context = CheckingContext::new(arena, CheckBudget::DEFAULT);
    let expected = form_comp_type(&mut context, expected)?;
    let checked = check_comp(&mut context, term, expected).map(|_| ());
    assert_eq!(
        context.depth(Zone::Linear),
        gandr_core_term::BinderDepth::default(),
        "a run leaves the linear zone as it found it"
    );
    checked
}

/// The integer literal `digits` spells.
///
/// # Specification
/// trivial.
#[inline]
pub fn integer(
    arena: &mut CoreArena,
    Spelled(digits): Spelled,
) -> ValueId
{
    crate::fixture::integer(arena, String::from(digits))
}

/// The child end of `fork`.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub const fn child(fork: ComputationId) -> Endpoint
{
    Endpoint {
        fork,
        side: ForkSide::Child,
    }
}

/// `!end. end`: one endpoint at `end` sent, then the end.
///
/// # Specification
/// trivial.
#[inline]
pub fn delegating(arena: &mut CoreArena) -> ValueTypeId
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
pub enum AfterSend
{
    /// Leaves it to the receiver.
    Leaves,
    /// Closes it again.
    Closes,
}

/// The sending half of an exchange over [`delegating`].
///
/// The half is `let d = fork (e : end) { close(e) }; send(c, d) ; close(c)`,
/// with `close(d)` after the send when `after` closes it. Answers the inner
/// fork and the `close d`.
///
/// # Specification
/// trivial.
#[inline]
pub fn delegator(
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

/// The session type at `ty`, as the session judgement reads it.
///
/// # Specification
/// trivial.
///
/// # Errors
/// As the judgement's reading: the refusal when `ty` is no session type.
#[inline]
pub fn session_at(
    context: &CheckingContext<'_>,
    ty: ValueTypeId,
) -> Result<SessionType, CheckRefusal>
{
    crate::session::session_at(context, ty)
}
