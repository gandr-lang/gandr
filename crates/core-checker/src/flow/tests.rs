//! Session statements, runs and rides, judged and readmitted.

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;

use gandr_core_term::CoreArena;
use gandr_core_term::Sort;
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
use gandr_kernel_strata::Level;
use gandr_kernel_strata::LevelConstant;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::DeclarationContent;
use gandr_kernel_term::FieldLabel;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::Literal;
use gandr_kernel_term::StringLiteral;
use gandr_kernel_term::Value as KernelValue;
use quenchant_shape::shape::Maybe;

use super::Moving;
use super::computed;
use super::covariant;
use super::ride;
use super::session_code;
use super::universe;
use crate::bridge;
use crate::bridge::Outcome;
use crate::context::CheckBudget;
use crate::context::CheckingContext;
use crate::declaration::Declaration;
use crate::declaration::OriginToken;
use crate::module::Judged;
use crate::module::ModuleReport;
use crate::module::Verdict;
use crate::module::check_module;
use crate::refusal::CheckRefusal;
use crate::refusal::RunFault;
use crate::refusal::RunStep;
use crate::refusal::UnadmittedFormer;

/// The seat protocols the witnesses relate.
#[derive(Clone, Copy, Debug)]
enum Seat
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
struct At(usize);

/// The labels the seat protocols choose among.
#[derive(Clone, Copy, Debug)]
enum Branch
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
    fn label(self) -> FieldLabel
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
enum Word
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
    fn text(
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
fn seat(
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

/// A recorded run of `moves`, each payload a string.
///
/// # Specification
/// trivial.
fn run(
    arena: &mut CoreArena,
    moves: &[RecordedMove<Word>],
) -> ValueId
{
    let moves: Vec<RecordedMove> = moves
        .iter()
        .map(|movement| match *movement {
            RecordedMove::Sent(word) => RecordedMove::Sent(word.text(arena)),
            RecordedMove::Received(word) => RecordedMove::Received(word.text(arena)),
            RecordedMove::Selected(ref label) => RecordedMove::Selected(label.clone()),
            RecordedMove::Offered(ref label) => RecordedMove::Offered(label.clone()),
            RecordedMove::Closed => RecordedMove::Closed,
        })
        .collect();
    arena.value_recorded(Arc::from(moves))
}

/// The seat run that reports once and retires.
///
/// # Specification
/// trivial.
fn retiring(arena: &mut CoreArena) -> ValueId
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
fn declaration(
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
fn judged(
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
fn statement(
    arena: &mut CoreArena,
    position: At,
    relation: SessionRelation,
    (source, target): (ValueId, ValueId),
) -> (Declaration, ValueId)
{
    let unit = arena.value_tuple(&[]);
    let at = arena.value_session_related(relation, source, target, unit);
    let identity = super::identity(arena, relation, (source, target));
    (declaration(position, identity, at), at)
}

/// The thunk of a ride of `value` along the constant at `flow`, at motive
/// `Run(X)`, declared at `U (F Run(target))`.
///
/// # Specification
/// trivial.
fn ridden(
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
fn ridden_at(
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
fn verdict(
    report: &ModuleReport,
    At(position): At,
) -> Option<Verdict>
{
    report.judged().get(position).map(Judged::verdict)
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
        .map(|at| report.flows().get(at).map(super::Statement::relation))
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
    // ride(\X. Flow(Type, X, ⌜End⌝), sub, stay(⌜End⌝)) would reverse `sub`.
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
    // def kept : Flow(Type[+, 1], Type, Type) = stay(Type) ;
    // def twice : Flow(Type[+, 1], Type, Type) = kept then kept ;
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
    // def kept : Flow(Type[+, 1], Type, Type) = stay(Type) ;
    // def same : Path(Type[+, 1], Type, Type) = here(Type) ;
    // def rode : () => Type = thunk { ride(\X. X, kept, Integer) } ;
    // def moved : () => Type = thunk { transport(\X. X, same, Integer) } ;
    // def small : () => Integer = thunk { ride(\X. X, stay(Integer), 0) } ;
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
    let zero = arena.value_literal(crate::fixture::integer_literal());
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
        Ok(Maybe::Absent(session_code::Absent::Elsewhere))
    );
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
    let identity = super::identity(&mut arena, SessionRelation::Equivalence, (paired, single));
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
                at: crate::refusal::TermNode::Value(at),
                wanted: crate::refusal::ExpectedShape::PathUniverse,
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
    let identity = super::identity(&mut arena, SessionRelation::Equivalence, (heard, swapped));
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
                at: crate::refusal::TermNode::Value(at),
                wanted: crate::refusal::ExpectedShape::PathUniverse,
                ..
            })) if at == open
        ),
        "a univalence over a bound record names no certificate: {report:?}"
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
