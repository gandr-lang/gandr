//! Session statements, runs and rides, judged and readmitted.

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
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::DeclarationContent;
use gandr_kernel_term::FieldLabel;
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
    let at = arena.value_session_related(relation, source, target);
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
    let code = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let motive = arena.value_type_run(code);
    let ride = arena.computation_ride(motive, flow, value);
    let body = arena.value_thunk(ride);
    let result = arena.value_type_run(target);
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
    let report = judged(&mut arena, &[
        apart, reversed, sub, flipped, keep, dropped, backward, short, unsession,
    ]);
    let symmetric_at = symmetric;
    assert_eq!(
        [0, 1, 3, 5, 6, 7, 8].map(|position| verdict(&report, At(position))),
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
    .map(|&motive| computed(&arena, at, motive))
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
