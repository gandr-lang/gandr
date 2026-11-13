//! The seat protocols, statements, runs and rides that the flow's witnesses
//! build. The flow's unit tests and the tests that readmit through the bridge
//! read them both.

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;

use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::session::PayloadCount;
use gandr_core_term::session::PayloadSlot;
use gandr_core_term::session::Protocol;
use gandr_core_term::session::ProtocolState;
use gandr_core_term::session::ProtocolSyntax;
use gandr_core_term::session::RecordedMove;
use gandr_core_term::session::RecursionIndex;
use gandr_core_term::session::SessionRelation;
use gandr_core_term::session::SessionType;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldLabel;
use gandr_kernel_term::Literal;
use gandr_kernel_term::StringLiteral;
use quenchant_shape::shape::Maybe;

use crate::context::CheckBudget;
use crate::context::CheckingContext;
use crate::declaration::Declaration;
use crate::declaration::OriginToken;
use crate::module::check_module;
use crate::report::Judged;
use crate::report::ModuleReport;
use crate::report::Verdict;

/// The seat protocols the witnesses relate.
#[derive(Clone, Copy, Debug)]
pub enum Seat
{
    /// `?D. mu turn. +{ report : !R. &{ next : turn, retire : end }, handoff :
    /// !H. end }`.
    End,
    /// `End` with `pause : !R. turn` added to the selection.
    Wide,
    /// `End` unfolded once under a renamed binder.
    Twice,
    /// `End` without the `retire` offer.
    Kept,
}

/// A declaration position in a fixture module.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct At(pub usize);

/// The labels the seat protocols choose among.
#[derive(Clone, Copy, Debug)]
pub enum Branch
{
    /// Report progress.
    Report,
    /// Hand the seat off.
    Handoff,
    /// Pause: the selection `Wide` adds.
    Pause,
    /// Take the next turn.
    Next,
    /// Retire: the offer `Kept` drops.
    Retire,
}

impl Branch
{
    /// The label the protocol spells.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn label(self) -> FieldLabel
    {
        FieldLabel::from(String::from(match self {
            Self::Report => "report",
            Self::Handoff => "handoff",
            Self::Pause => "pause",
            Self::Next => "next",
            Self::Retire => "retire",
        }))
    }
}

/// The payloads the witness runs carry.
#[derive(Clone, Copy, Debug)]
pub enum Word
{
    /// The task the seat receives.
    Task,
    /// The progress it reports.
    Progress,
    /// The notes it hands off.
    Notes,
}

impl Word
{
    /// The payload's string literal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn text(
        self,
        arena: &mut CoreArena,
    ) -> ValueId
    {
        let body = match self {
            Self::Task => "task",
            Self::Progress => "progress",
            Self::Notes => "notes",
        };
        arena.value_literal(Literal::Text(StringLiteral::new(String::from(body))))
    }
}

/// The quote of `seat`'s session type at its root, every payload a string.
///
/// # Specification
/// trivial.
#[inline]
pub fn seat(
    arena: &mut CoreArena,
    seat: Seat,
) -> ValueId
{
    let choice = |branches: &[(Branch, usize)]| -> BTreeMap<FieldLabel, ProtocolState> {
        branches
            .iter()
            .map(|&(branch, state)| (branch.label(), ProtocolState::from(state)))
            .collect()
    };
    let send = |slot: usize, next: usize| ProtocolSyntax::Send {
        payload: PayloadSlot::from(slot),
        next: ProtocolState::from(next),
    };
    let recur = ProtocolSyntax::Recur(RecursionIndex::from(0_usize));
    let receive = ProtocolSyntax::Receive {
        payload: PayloadSlot::from(0_usize),
        next: ProtocolState::from(1_usize),
    };
    let syntax = match seat {
        Seat::End => alloc::vec![
            receive,
            ProtocolSyntax::Mu(ProtocolState::from(2_usize)),
            ProtocolSyntax::Select(choice(&[(Branch::Report, 3), (Branch::Handoff, 7)])),
            send(1, 4),
            ProtocolSyntax::Offer(choice(&[(Branch::Next, 5), (Branch::Retire, 6)])),
            recur,
            ProtocolSyntax::End,
            send(2, 8),
            ProtocolSyntax::End,
        ],
        Seat::Wide => alloc::vec![
            receive,
            ProtocolSyntax::Mu(ProtocolState::from(2_usize)),
            ProtocolSyntax::Select(choice(&[
                (Branch::Report, 3),
                (Branch::Handoff, 7),
                (Branch::Pause, 9),
            ])),
            send(1, 4),
            ProtocolSyntax::Offer(choice(&[(Branch::Next, 5), (Branch::Retire, 6)])),
            recur.clone(),
            ProtocolSyntax::End,
            send(2, 8),
            ProtocolSyntax::End,
            send(1, 10),
            recur,
        ],
        Seat::Twice => alloc::vec![
            receive,
            ProtocolSyntax::Select(choice(&[(Branch::Report, 2), (Branch::Handoff, 13)])),
            send(1, 3),
            ProtocolSyntax::Offer(choice(&[(Branch::Next, 4), (Branch::Retire, 12)])),
            ProtocolSyntax::Mu(ProtocolState::from(5_usize)),
            ProtocolSyntax::Select(choice(&[(Branch::Report, 6), (Branch::Handoff, 10)])),
            send(1, 7),
            ProtocolSyntax::Offer(choice(&[(Branch::Next, 8), (Branch::Retire, 9)])),
            recur,
            ProtocolSyntax::End,
            send(2, 11),
            ProtocolSyntax::End,
            ProtocolSyntax::End,
            send(2, 14),
            ProtocolSyntax::End,
        ],
        Seat::Kept => alloc::vec![
            receive,
            ProtocolSyntax::Mu(ProtocolState::from(2_usize)),
            ProtocolSyntax::Select(choice(&[(Branch::Report, 3), (Branch::Handoff, 6)])),
            send(1, 4),
            ProtocolSyntax::Offer(choice(&[(Branch::Next, 5)])),
            recur,
            send(2, 7),
            ProtocolSyntax::End,
        ],
    };
    let string = arena.value_type_base(BaseType::String);
    let payloads = [string, string, string];
    let protocol = Protocol::new(
        syntax,
        ProtocolState::from(0_usize),
        PayloadCount::from(payloads.len()),
    )
    .unwrap();
    let session = SessionType::new(Arc::new(protocol), Arc::from(payloads.as_slice())).unwrap();
    let ty = arena.value_type_session(session);
    arena.value_quote(ty)
}

/// `movement` with its payload, if any, the word's string literal.
///
/// # Specification
/// trivial.
#[inline]
pub fn texted(
    arena: &mut CoreArena,
    movement: &RecordedMove<Word>,
) -> RecordedMove
{
    match *movement {
        RecordedMove::Sent(word) => RecordedMove::Sent(word.text(arena)),
        RecordedMove::Received(word) => RecordedMove::Received(word.text(arena)),
        RecordedMove::Selected(ref label) => RecordedMove::Selected(label.clone()),
        RecordedMove::Offered(ref label) => RecordedMove::Offered(label.clone()),
        RecordedMove::Closed => RecordedMove::Closed,
    }
}

/// A recorded run of `moves`, each payload a string.
///
/// # Specification
/// trivial.
#[inline]
pub fn run(
    arena: &mut CoreArena,
    moves: &[RecordedMove<Word>],
) -> ValueId
{
    let moves: Vec<RecordedMove> = moves
        .iter()
        .map(|movement| texted(arena, movement))
        .collect();
    arena.value_recorded(Arc::from(moves))
}

/// The seat run that reports once and retires.
///
/// # Specification
/// trivial.
#[inline]
pub fn retiring(arena: &mut CoreArena) -> ValueId
{
    run(arena, &[
        RecordedMove::Received(Word::Task),
        RecordedMove::Selected(Branch::Report.label()),
        RecordedMove::Sent(Word::Progress),
        RecordedMove::Offered(Branch::Retire.label()),
        RecordedMove::Closed,
    ])
}

/// The declaration at `position`.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub fn declaration(
    At(position): At,
    declared: ValueTypeId,
    body: ValueId,
) -> Declaration
{
    Declaration::new(
        ConstantIndex::from(position),
        Maybe::Present(declared),
        Maybe::Present(body),
        OriginToken::from(position),
    )
}

/// The module judged.
///
/// # Specification
/// trivial.
#[inline]
pub fn judged(
    arena: &mut CoreArena,
    module: &[Declaration],
) -> ModuleReport
{
    let mut context = CheckingContext::new(arena, CheckBudget::DEFAULT);
    check_module(&mut context, module)
}

/// The statement `relation(source, target)` at the identity it inhabits.
///
/// # Specification
/// trivial.
#[inline]
pub fn statement(
    arena: &mut CoreArena,
    position: At,
    relation: SessionRelation,
    (source, target): (ValueId, ValueId),
) -> (Declaration, ValueId)
{
    let unit = arena.value_tuple(&[]);
    let at = arena.value_session_related(relation, source, target, unit);
    let identity = crate::flow::identity(arena, relation, (source, target));
    (declaration(position, identity, at), at)
}

/// The thunk of a ride of `value` along the constant at `flow`, at motive
/// `Run(X)`, declared at `U (F Run(target))`.
///
/// # Specification
/// trivial.
#[inline]
pub fn ridden(
    arena: &mut CoreArena,
    position: At,
    flow: ValueId,
    value: ValueId,
    target: ValueId,
) -> (Declaration, ValueId)
{
    ridden_at(
        arena,
        CoreArena::value_type_run,
        (position, flow, value, target),
    )
}

/// The thunk of a ride of `value` along the constant at `flow`, at motive
/// `former(X)`, declared at `U (F former(target))`.
///
/// # Specification
/// trivial.
#[inline]
pub fn ridden_at(
    arena: &mut CoreArena,
    former: fn(&mut CoreArena, ValueId) -> ValueTypeId,
    (position, flow, value, target): (At, ValueId, ValueId, ValueId),
) -> (Declaration, ValueId)
{
    let code = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let motive = former(arena, code);
    let ride = arena.computation_ride(motive, flow, value);
    let body = arena.value_thunk(ride);
    let result = former(arena, target);
    let returner = arena.comp_type_returner(result);
    let declared = arena.value_type_thunk(returner);
    (declaration(position, declared, body), value)
}

/// The verdict of the declaration at `position`.
///
/// # Specification
/// trivial.
#[inline]
pub fn verdict(
    report: &ModuleReport,
    At(position): At,
) -> Option<Verdict>
{
    report.judged().get(position).map(Judged::verdict)
}

/// The session that `code` denotes at its root, as the flow reads it.
///
/// # Specification
/// trivial.
///
/// # Errors
/// As the flow's reading: the refusal that the code's normal form meets.
#[inline]
pub fn session_code(
    context: &mut CheckingContext<'_>,
    code: ValueId,
) -> Result<Maybe<SessionType, crate::flow::session_code::Absent>, crate::CheckRefusal>
{
    crate::flow::session_code(context, code)
}
