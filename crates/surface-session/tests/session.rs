//! The session's submissions: what each revision reports, and what the
//! session keeps between them.
//!
//! Each submission is a whole revision. Appending a line means resubmitting
//! the previous source with that line added; the session carries the resume
//! it adopts from and the import scope it resolves in.

use anodized::spec;
use gandr_core_checker::Verdict;
use gandr_core_incremental::Adoption;
use gandr_core_incremental::ContentNode;
use gandr_core_incremental::ItemCount;
use gandr_core_incremental::SynthesisEvent;
use gandr_core_incremental::Typing;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_surface_corpus::DeclarationReport;
use gandr_surface_corpus::Outcome;
use gandr_surface_corpus::Produced;
use gandr_surface_corpus::RefusalName;
use gandr_surface_corpus::Settlement;
use gandr_surface_dispatcher::Composed;
use gandr_surface_dispatcher::Evaluation;
use gandr_surface_dispatcher::SourceRoot;
use gandr_surface_dispatcher::Standing;
use gandr_surface_lowering::LoweringRefusal;
use gandr_surface_lowering::SurfaceName;
use gandr_surface_lowering::namespace::DottedName;
use gandr_surface_lowering::namespace::NamePath;
use gandr_surface_session::admission;
use gandr_surface_session::admitted;
use gandr_surface_session::evaluation;
use gandr_surface_session::import;
use gandr_surface_session::resumed;
use quenchant_shape::shape::Maybe;

use crate::common::names;
use crate::common::resumed;
use crate::common::session;
use crate::common::submit;

/// The rows a settled composition reports: each declaration's name, outcome
/// and settlement, in admission order.
///
/// # Specification
/// - requires: the composition is settled.
/// - ensures: one row per declaration, in admission order, with that
///   declaration's name, outcome, and settlement.
/// - panics: if the composition was refused as a whole.
///
/// # Adequacy
/// - hypothesis: L3 — literal two-declaration successes, a surviving
///   declaration after a malformed one, and a named type refusal. Exact ordered
///   tuples expose dropped, reordered, renamed, or mismatched report fields;
///   this is a bounded report projection, not an independent typing oracle.
/// - witness: `tests::session::whole_file_submit_carries_definitions_forward`
/// - witness: `tests::session::a_malformed_declaration_is_declined_and_the_later_definition_binds`
/// - witness: `tests::session::an_unbound_variable_is_a_type_error`
#[spec(
    requires: matches!(* composed, Composed::Settled { .. }),
    ensures: |ret| match *composed {
    Composed::Settled { ref report, .. } => {
        ret.len() == report.declarations().len()
            && ret
                .iter()
                .zip(report.declarations())
                .all(|(row, declaration)| {
                    row.0.as_str() == declaration.name().as_ref()
                        && row.1 == declaration.outcome()
                        && row.2 == declaration.settlement()
                })
    }
    Composed::Refused(_) => false,
},
)]
fn rows(composed: &Composed<'_>) -> Vec<(String, Outcome, Settlement)>
{
    match *composed {
        | Composed::Settled { ref report, .. } => report
            .declarations()
            .iter()
            .map(|declaration| {
                (
                    declaration.name().to_string(),
                    declaration.outcome(),
                    declaration.settlement(),
                )
            })
            .collect(),
        | Composed::Refused(ref refusal) => panic!("refused as a whole: {refusal}"),
    }
}

/// The outcome of a declaration that checks owing nothing.
///
/// # Specification
/// trivial.
fn checks() -> Outcome
{
    Outcome::Checks(gandr_core_checker::ObligationCount::from(0_usize))
}

/// The nodes of the type an unsigned body synthesised; none for any other
/// typing.
///
/// # Specification
/// - requires: nothing.
/// - ensures: returns the original produced node slice for synthesized typing,
///   and an empty slice for checked, native, owed, or refused typing.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — integer and string literal typings and a later reference
///   compare exact base-type nodes. The predicate preserves the borrowed slice
///   and excludes nodes from nonsynthesizing variants; the concrete witnesses
///   cover synthesized outputs, not every typing variant.
/// - witness: `tests::session::scalar_literals_carry_their_types`
/// - witness: `tests::session::definitions_carry_across_lines`
/// - witness: `tests::session::integer_literal_types_and_evaluates`
#[spec(
    ensures: |ret| match *typing {
    Typing::Synthesised { ref produced, .. } => {
        core::ptr::eq(core::ptr::from_ref(ret), core::ptr::from_ref(produced.nodes()))
    }
    Typing::Data | Typing::Checked { .. } | Typing::Owed | Typing::Refused(_) => ret.is_empty(),
},
)]
fn produced(typing: &Typing) -> &[ContentNode]
{
    match *typing {
        | Typing::Synthesised { ref produced, .. } => produced.nodes(),
        | Typing::Data | Typing::Checked { .. } | Typing::Owed | Typing::Refused(_) => &[],
    }
}

/// The census a submission's resume carries.
///
/// # Specification
/// - requires: the submission carries a resume.
/// - ensures: returns that resume's complete census unchanged.
/// - panics: if the submission carries no resume.
///
/// # Adequacy
/// - hypothesis: L3 — exact admitted item counts after a malformed declaration
///   and exact adopted counts on an append. These observations distinguish
///   report size from resume size and adoption from judging; they do not
///   establish checker correctness.
/// - witness: `tests::session::a_malformed_declaration_is_declined_and_the_later_definition_binds`
/// - witness: `tests::session::checkpointed_session_matches_from_scratch`
/// - witness: `tests::session::definitions_carry_across_lines`
#[spec(
    requires: matches!(submission.resumed(), Maybe::Present(_)),
    ensures: |ret| match submission.resumed() {
    Maybe::Present(resumed) => ret == resumed.census(),
    Maybe::Absent(_) => false,
},
)]
fn census(
    submission: &gandr_surface_session::Submission<'_>
) -> gandr_core_incremental::ResumeCensus
{
    match submission.resumed() {
        | Maybe::Present(resumed) => resumed.census(),
        | Maybe::Absent(reason) => panic!("the submission carries no resume: {reason:?}"),
    }
}

#[test]
fn whole_file_submit_carries_definitions_forward()
{
    let mut session = session(SourceRoot::Strict);
    let submission = submit(
        &mut session,
        "def greeting = \"the value zone\" ;\ndef shown : String ;\ndef shown = greeting ;",
    );
    assert_eq!(
        rows(submission.composed()),
        vec![
            ("greeting".to_owned(), checks(), Settlement::Settled),
            ("shown".to_owned(), checks(), Settlement::Settled),
        ],
        "the later declaration checks against the earlier one in the same submission"
    );
    assert_eq!(
        submission.standing(),
        Standing::Settled,
        "the source settles"
    );
    let typings = resumed(&session);
    assert!(
        matches!(typings.as_slice(), [greeting, Typing::Checked { .. }] if produced(greeting) == [ContentNode::Base(BaseType::String)]),
        "`greeting : String` synthesised, `shown` checked: {typings:?}"
    );
}

#[test]
fn a_malformed_declaration_is_declined_and_the_later_definition_binds()
{
    let mut session = session(SourceRoot::Strict);
    let first = submit(&mut session, "def bad = 1 ~ 2 ;\ndef good = 2 ;");
    let Composed::Settled { ref report, .. } = *first.composed()
    else {
        panic!("the damaged declaration does not collapse the submission");
    };
    let [ref bad, ref good] = *report.declarations()
    else {
        panic!("both declarations are reported: {report:?}");
    };
    assert_eq!(
        bad.outcome(),
        Outcome::Refuses(RefusalName::MalformedForm),
        "the damaged declaration is refused for its missing operand"
    );
    assert!(
        matches!(bad.produced(), Produced::Unlowered(refusal) if matches!(refusal.span(), Maybe::Present(span) if usize::from(span.start()) == 12_usize)),
        "the refusal points at the stray token, so the report points at the damage"
    );
    assert_eq!(good.outcome(), checks(), "the later definition checks");
    assert_eq!(
        census(&first).items,
        ItemCount::from(1_usize),
        "the refused declaration offers no item; the later one does"
    );

    let later = submit(
        &mut session,
        "def bad = 1 ~ 2 ;\ndef good = 2 ;\ndef later : Integer ;\ndef later = good ;",
    );
    assert_eq!(
        rows(later.composed()).get(2_usize),
        Some(&("later".to_owned(), checks(), Settlement::Settled)),
        "`good` is usable on a later line exactly as an undamaged definition is"
    );
}

#[test]
fn checkpointed_session_matches_from_scratch()
{
    let mut checkpointed = session(SourceRoot::Strict);
    let _definitions = submit(&mut checkpointed, "def x = 40 ;");
    let appended = submit(
        &mut checkpointed,
        "def x = 40 ;\ndef y : Integer ;\ndef y = x ;",
    );
    let mut scratch = session(SourceRoot::Strict);
    let whole = submit(&mut scratch, "def x = 40 ;\ndef y : Integer ;\ndef y = x ;");
    assert_eq!(
        appended.composed(),
        whole.composed(),
        "the appended revision reports exactly what the whole text reports from scratch"
    );
    assert_eq!(
        resumed(&checkpointed),
        resumed(&scratch),
        "the resumed typings are the from-scratch typings"
    );
    assert_eq!(
        census(&appended).adopted,
        ItemCount::from(1_usize),
        "the unchanged definition is adopted, not judged again"
    );
}

#[test]
fn successful_submissions_publish_whole_program_synthesis()
{
    let mut session = session(SourceRoot::Strict);
    assert!(
        matches!(session.stream(), Maybe::Absent(_)),
        "a fresh session has no synthesis"
    );
    let _first = submit(&mut session, "def retained = 40 ;");
    let Maybe::Present(first_stream) = session.stream()
    else {
        panic!("an accepted submission publishes a stream");
    };
    let _second = submit(
        &mut session,
        "def retained = 40 ;\ndef appended = retained ;",
    );
    let first_events: Vec<SynthesisEvent> = first_stream.collect();
    let [
        SynthesisEvent::Started { item_count },
        SynthesisEvent::Item {
            ref typing,
            adoption,
            ..
        },
        SynthesisEvent::Completed,
    ] = *first_events.as_slice()
    else {
        panic!("Started, one Item, Completed: {first_events:?}");
    };
    assert_eq!(item_count, ItemCount::from(1_usize), "the one-item program");
    assert_eq!(
        adoption,
        Adoption::Judged,
        "the first submission judges its item"
    );

    let Maybe::Present(second_stream) = session.stream()
    else {
        panic!("the second submission replaces the stream");
    };
    let second_events: Vec<SynthesisEvent> = second_stream.collect();
    let [
        SynthesisEvent::Started {
            item_count: second_count,
        },
        SynthesisEvent::Item {
            typing: ref retained_typing,
            adoption: retained,
            ..
        },
        SynthesisEvent::Item {
            adoption: appended, ..
        },
        SynthesisEvent::Completed,
    ] = *second_events.as_slice()
    else {
        panic!("Started, two Items in order, Completed: {second_events:?}");
    };
    assert_eq!(second_count, ItemCount::from(2_usize), "both items");
    assert_eq!(
        retained_typing, typing,
        "adoption preserves the retained definition's typing"
    );
    assert_eq!(
        retained,
        Adoption::Adopted,
        "the unchanged definition is adopted"
    );
    assert_eq!(
        appended,
        Adoption::Judged,
        "the appended definition is judged"
    );
}

#[test]
fn submission_owns_outcomes_after_session_advances()
{
    let mut session = session(SourceRoot::Strict);
    let first = submit(&mut session, "def retained = 40 ;");
    let second = submit(&mut session, "def retained = 40 ;\ndef later = retained ;");
    assert_eq!(
        names(first.composed()),
        vec!["retained".to_owned()],
        "the first submission keeps its own report after the session advances"
    );
    assert_eq!(
        census(&first).items,
        ItemCount::from(1_usize),
        "and its own census"
    );
    assert_eq!(
        names(second.composed()),
        vec!["retained".to_owned(), "later".to_owned()],
        "the second is independent of it"
    );
}

#[test]
fn scalar_literals_carry_their_types()
{
    let mut session = session(SourceRoot::Strict);
    let _submission = submit(&mut session, "def number = 42 ;\ndef text = \"hi\" ;");
    let typings = resumed(&session);
    assert!(
        matches!(typings.as_slice(), [number, text] if produced(number) == [ContentNode::Base(BaseType::Integer)] && produced(text) == [ContentNode::Base(BaseType::String)]),
        "an integer literal synthesises `Integer`, a string literal `String`: {typings:?}"
    );
}

#[test]
fn definitions_carry_across_lines()
{
    let mut session = session(SourceRoot::Strict);
    let _first = submit(&mut session, "def y = 5 ;");
    let later = submit(
        &mut session,
        "def y = 5 ;\ndef z = y ;\ndef w : Integer ;\ndef w = y ;",
    );
    let typings = resumed(&session);
    assert!(
        matches!(typings.as_slice(), [y, z, Typing::Checked { .. }] if produced(y) == [ContentNode::Base(BaseType::Integer)] && produced(z) == [ContentNode::Base(BaseType::Integer)]),
        "`y` carries to later lines, where it both synthesises and checks: {typings:?}"
    );
    assert_eq!(
        census(&later).adopted,
        ItemCount::from(1_usize),
        "the carried definition is adopted"
    );
}

#[test]
fn an_unbound_variable_is_a_type_error()
{
    let mut session = session(SourceRoot::Strict);
    let submission = submit(&mut session, "def user = foo ;");
    assert_eq!(
        rows(submission.composed()),
        vec![(
            "user".to_owned(),
            Outcome::Refuses(RefusalName::UnresolvedName),
            Settlement::Unsettled
        )],
        "`foo` is unbound"
    );
    assert_eq!(
        submission.standing(),
        Standing::Unsettled,
        "the source does not settle"
    );
}

#[test]
fn an_undeclared_type_name_in_a_signature_is_refused_by_name()
{
    let mut session = session(SourceRoot::Strict);
    let refused = submit(
        &mut session,
        "def f(x: NoSuchType) -> -F Integer { return 1 }",
    );
    let Composed::Settled { ref report, .. } = *refused.composed()
    else {
        panic!("the definition lowers");
    };
    assert!(
        matches!(
            report.declarations().first().map(gandr_surface_corpus::DeclarationReport::produced),
            Some(Produced::Unlowered(LoweringRefusal::UnresolvedTypeHead { name, .. })) if name.as_ref() == "NoSuchType"
        ),
        "an undeclared type name in a signature is refused by its name: {report:?}"
    );
    let accepted = submit(&mut session, "def f(x: Integer) -> -F Integer { return 1 }");
    assert_eq!(
        rows(accepted.composed()),
        vec![("f".to_owned(), checks(), Settlement::Settled)],
        "the same signature over a declared name checks"
    );
}

#[test]
fn verdicts_keep_an_outcome_only_type_error_visible()
{
    let mut session = session(SourceRoot::Strict);
    let submission = submit(
        &mut session,
        "def wrong : Integer ;\ndef wrong = \"text\" ;",
    );
    let Composed::Settled { ref report, .. } = *submission.composed()
    else {
        panic!("the module lowers");
    };
    assert!(
        matches!(
            report
                .declarations()
                .first()
                .map(gandr_surface_corpus::DeclarationReport::produced),
            Some(Produced::Judged(Verdict::Refused(_)))
        ),
        "the report carries the checker's refusal: {report:?}"
    );
    assert!(
        matches!(resumed(&session).as_slice(), [Typing::Refused(_)]),
        "and so does the resume the faces read"
    );
}

#[test]
fn failed_submission_retains_latest_synthesis()
{
    let mut session = session(SourceRoot::Strict);
    let _submission = submit(&mut session, "def retained = 40 ;");
    let Maybe::Present(before) = session.stream()
    else {
        panic!("an accepted submission publishes a stream");
    };
    let before: Vec<SynthesisEvent> = before.collect();
    let before_snapshot = session.snapshot().items().to_vec();
    let before_lowerings = usize::from(session.lowerings());
    let refused = submit(&mut session, "def retained = 40 ;\npure retained");
    assert!(
        matches!(refused.composed(), Composed::Refused(_)),
        "a top-level expression refuses the revision as a whole"
    );
    assert_eq!(
        refused.resumed(),
        Maybe::Absent(resumed::Absent::RefusedWhole),
        "a refused revision is not resumed"
    );
    assert_eq!(refused.standing(), Standing::Refused, "and stands refused");
    assert_eq!(session.snapshot().items(), before_snapshot.as_slice());
    assert_eq!(
        usize::from(session.lowerings()),
        before_lowerings.saturating_add(1_usize)
    );
    let Maybe::Present(after) = session.stream()
    else {
        panic!("the refused revision leaves the stream");
    };
    assert_eq!(
        after.collect::<Vec<SynthesisEvent>>(),
        before,
        "every prior event and adoption is kept"
    );
}

#[test]
fn a_judged_revision_reports_before_its_admission()
{
    let text = gandr_surface_syntax::SourceText::from("def a : Integer ; def a = 1 ; def b = a ;");
    let mut submitted = session(SourceRoot::Strict);
    let whole = submitted.submit(text).expect("submits");
    let mut judging = session(SourceRoot::Strict);
    let judged = judging.judge(text).expect("judges");
    assert_eq!(
        judged.kernel(),
        Maybe::Absent(admitted::Absent::Pending),
        "a judged revision has committed no kernel checkpoint"
    );
    let Composed::Settled {
        kernel: Maybe::Absent(_),
        ..
    } = *judged.composed()
    else {
        panic!("a judged revision settles before the kernel exports anything");
    };
    assert_eq!(
        (rows(judged.composed()), judged.standing()),
        (rows(whole.composed()), whole.standing()),
        "the judgement reports what the submission reports"
    );
    let Ok(Maybe::Present(admission)) = judging.admit()
    else {
        panic!("the judgement left its admission");
    };
    let Composed::Settled {
        kernel: Maybe::Present(ref kernel),
        ..
    } = *whole.composed()
    else {
        panic!("the submission carries its kernel artifact");
    };
    assert_eq!(
        (admission.kernel(), Maybe::Present(admission.checkpoint())),
        (kernel, whole.kernel()),
        "the admission exports and commits what the submission did"
    );
    assert!(
        matches!(judging.admit(), Ok(Maybe::Absent(admission::Absent::Idle))),
        "an admission runs once"
    );
    let _superseded = judging.judge(text).expect("judges again");
    let refused = judging
        .judge(gandr_surface_syntax::SourceText::from("pure 3"))
        .expect("judges");
    assert_eq!(
        refused.kernel(),
        Maybe::Absent(admitted::Absent::RefusedWhole)
    );
    assert!(
        matches!(judging.admit(), Ok(Maybe::Absent(admission::Absent::Idle))),
        "a later judgement drops the admission an earlier one left, and a refused revision \
         leaves none"
    );
}

#[test]
fn a_judged_revision_hands_its_tree_to_a_reader()
{
    let text = gandr_surface_syntax::SourceText::from("def a = 1 ;\ndef b = a ;\ndef c = ");
    let mut reading = session(SourceRoot::Strict);
    let mut read = Vec::new();
    let judged = reading
        .judge_reading(text, |tree| read.push((tree.source(), tree.forms().len())))
        .expect("judges");
    assert_eq!(
        read,
        [(text, 3)],
        "the reader reads the revision's own tree once, every form of it"
    );
    let plain = session(SourceRoot::Strict).judge(text).expect("judges");
    assert_eq!(
        (rows(judged.composed()), judged.standing()),
        (rows(plain.composed()), plain.standing()),
        "reading the tree changes nothing the judgement reports"
    );
}

#[test]
fn import_namespace_carries_across_lines_and_resolves_source_declarations()
{
    let mut session = session(SourceRoot::Strict);
    let parse = NamePath::from(DottedName::from("parse"));
    let list = NamePath::from(DottedName::from("list_ext"));
    let missing = NamePath::from(DottedName::from("missing"));
    assert_eq!(
        session.resolve_import(&parse),
        Maybe::Absent(import::Absent::Unbound),
        "a fresh session binds nothing"
    );

    let first = submit(
        &mut session,
        "import \"file:///lib/parse.gandr\" as parse ;",
    );
    assert_eq!(
        first.standing(),
        Standing::Settled,
        "an import alone settles"
    );
    let second = submit(
        &mut session,
        "import \"file:///lib/parse.gandr\" as parse ;\nimport \"file:///lib/list.gandr\" as list_ext ;",
    );
    assert_eq!(
        second.standing(),
        Standing::Settled,
        "a distinct later alias extends the scope cleanly"
    );
    let uri = |path: &NamePath| {
        session
            .resolve_import(path)
            .map(|row| row.uri().to_string())
    };
    assert_eq!(
        uri(&parse),
        Maybe::Present("file:///lib/parse.gandr".to_owned()),
        "the first line's alias resolves"
    );
    assert_eq!(
        uri(&list),
        Maybe::Present("file:///lib/list.gandr".to_owned()),
        "the second line's alias resolves"
    );
    assert_eq!(
        uri(&missing),
        Maybe::Absent(import::Absent::Unbound),
        "an unbound path resolves to nothing"
    );

    let duplicate = submit(
        &mut session,
        "import \"file:///lib/parse.gandr\" as parse ;\nimport \"file:///lib/list.gandr\" as list_ext ;\nimport \"file:///lib/other.gandr\" as parse ;",
    );
    assert!(
        matches!(
            duplicate.composed(),
            Composed::Refused(LoweringRefusal::DuplicateImportAlias { .. })
        ),
        "a later line cannot silently replace an import alias: {:?}",
        duplicate.composed()
    );
    let uri = |path: &NamePath| {
        session
            .resolve_import(path)
            .map(|row| row.uri().to_string())
    };
    assert_eq!(
        uri(&parse),
        Maybe::Present("file:///lib/parse.gandr".to_owned()),
        "the refused collision leaves the original alias reachable"
    );
    assert_eq!(
        uri(&list),
        Maybe::Present("file:///lib/list.gandr".to_owned()),
        "and every other alias of the accepted revision"
    );
}

/// The position the settled composition admitted `name` at.
///
/// # Specification
/// - requires: the composition is settled and contains a declaration named
///   `name`.
/// - ensures: returns the constant of the first declaration with that name.
/// - panics: if the composition was refused as a whole or no such declaration
///   exists.
///
/// # Adequacy
/// - hypothesis: L3 — named integer, thunk, refused, and goal declarations feed
///   actual evaluation. Distinct eligibility and value observations expose the
///   wrong constant; the predicate checks first-match selection directly
///   without evaluating a second time.
/// - witness: `tests::session::integer_literal_types_and_evaluates`
/// - witness: `tests::session::nullary_function_call_evaluates`
/// - witness: `tests::session::evaluation_declines_missing_and_refused_items`
/// - witness: `tests::session::holes_decline_evaluation`
#[spec(
    requires: match *composed {
    Composed::Settled { ref report, .. } => {
        report.declarations().iter().any(|declaration| declaration.name() == name)
    }
    Composed::Refused(_) => false,
},
    ensures: |ret| match *composed {
    Composed::Settled { ref report, .. } => {
        report
            .declarations()
            .iter()
            .find(|declaration| declaration.name() == name)
            .is_some_and(|declaration| ret == declaration.constant())
    }
    Composed::Refused(_) => false,
},
)]
fn constant_of(
    composed: &Composed<'_>,
    name: SurfaceName<'_>,
) -> ConstantIndex
{
    let Composed::Settled { ref report, .. } = *composed
    else {
        panic!("refused as a whole: {composed:?}");
    };
    report
        .declarations()
        .iter()
        .find(|declaration| declaration.name() == name)
        .map_or_else(
            || panic!("`{name}` is declared: {report:?}"),
            DeclarationReport::constant,
        )
}

/// An integer literal types to `Integer` and evaluates to itself.
#[test]
fn integer_literal_types_and_evaluates()
{
    let mut session = session(SourceRoot::Strict);
    let mut submission = submit(&mut session, "def answer = 42 ;");
    let typings = resumed(&session);
    assert!(
        matches!(typings.as_slice(), [answer] if produced(answer) == [ContentNode::Base(BaseType::Integer)]),
        "`answer : Integer`: {typings:?}"
    );
    let answer = constant_of(submission.composed(), SurfaceName::from("answer"));
    assert!(
        matches!(submission.evaluate(answer), Maybe::Present(Evaluation::Value(ref value)) if value.as_ref() == "42"),
        "`answer` evaluates to itself"
    );
}

/// A nullary function binds a thunk, and a call of it runs its body.
#[test]
fn nullary_function_call_evaluates()
{
    let mut session = session(SourceRoot::Strict);
    let mut submission = submit(
        &mut session,
        "def step() -> -F Integer { return 1 }\ndef called : +U (-F Integer) ;\ndef called = thunk { become step() } ;",
    );
    assert_eq!(
        rows(submission.composed()),
        vec![
            ("step".to_owned(), checks(), Settlement::Settled),
            ("called".to_owned(), checks(), Settlement::Settled),
        ],
        "both declarations check"
    );
    for name in ["step", "called"] {
        let constant = constant_of(submission.composed(), SurfaceName::from(name));
        assert!(
            matches!(submission.evaluate(constant), Maybe::Present(Evaluation::Value(ref value)) if value.as_ref() == "1"),
            "`{name}` runs the nullary body"
        );
    }
}

/// Missing constants, refused declarations, and refused revisions are not
/// eligible for evaluation.
#[test]
fn evaluation_declines_missing_and_refused_items()
{
    let mut held = session(SourceRoot::Strict);
    let mut accepted = submit(&mut held, r#"def answer = 42 ;"#);
    assert!(matches!(
        accepted.evaluate(ConstantIndex::from(999_usize)),
        Maybe::Absent(evaluation::Absent::Unaccepted)
    ));
    let mut rejected = submit(
        &mut held,
        r#"def broken : String ;
def broken = 1 ;"#,
    );
    let broken = constant_of(rejected.composed(), SurfaceName::from("broken"));
    assert!(matches!(
        rejected.evaluate(broken),
        Maybe::Absent(evaluation::Absent::Unaccepted)
    ));
    let mut whole = submit(
        &mut held,
        r#"def answer = 42 ;
pure answer"#,
    );
    assert!(matches!(
        whole.evaluate(ConstantIndex::from(0_usize)),
        Maybe::Absent(evaluation::Absent::Unaccepted)
    ));
}

#[test]
#[expect(
    clippy::use_debug,
    reason = "the Debug implementations’ sink-refusal contract is under test"
)]
fn formatters_propagate_sink_refusals()
{
    use core::fmt::Write as _;

    use gandr_core_incremental::CheckpointStoreError;
    use gandr_core_incremental::MemoryCheckpointStore;
    use gandr_storage_records::InMemoryBlockStore;
    use gandr_surface_session::Session;
    use gandr_surface_session::SessionFault;
    use gandr_surface_syntax::SourceText;

    use crate::common::RefusingWriter;
    let fault = SessionFault::Store(CheckpointStoreError::Io);
    assert!(write!(&mut RefusingWriter, "{fault}").is_err());
    let held = session(SourceRoot::Strict);
    assert!(write!(&mut RefusingWriter, "{held:?}").is_err());
    let reopened = Session::reopen(
        crate::common::grammar(),
        SourceRoot::Strict,
        MemoryCheckpointStore::default(),
        InMemoryBlockStore::default(),
        crate::common::backend(),
        SourceText::from(r#"def value = 1 ;"#),
    )
    .expect("an empty store reopens fresh");
    assert!(write!(&mut RefusingWriter, "{reopened:?}").is_err());
}

/// A declaration owed its body is a goal and is not evaluated; one that runs
/// into it is, and is blamed on it.
#[test]
fn holes_decline_evaluation()
{
    let mut session = session(SourceRoot::Strict);
    let mut submission = submit(
        &mut session,
        "def later : +U (-F Integer) ;\ndef main : +U (-F Integer) ;\ndef main = thunk { become force later } ;",
    );
    let later = constant_of(submission.composed(), SurfaceName::from("later"));
    assert_eq!(
        submission.evaluate(later),
        Maybe::Absent(evaluation::Absent::Holed),
        "the goal is not evaluated"
    );
    let main = constant_of(submission.composed(), SurfaceName::from("main"));
    assert!(
        matches!(submission.evaluate(main), Maybe::Present(Evaluation::Blamed(name)) if name.to_string() == "later"),
        "the run that reaches the goal is blamed on it"
    );
}

/// Arithmetic is checked at Integer and evaluated through the native prelude.
#[test]
fn arithmetic_operators_type_check_and_evaluate()
{
    let mut session = session(SourceRoot::Strict);
    let mut submission = submit(
        &mut session,
        "def answer : +U (-F Integer) ; def answer = thunk { become 1 + 2 } ;",
    );
    assert_eq!(rows(submission.composed()), vec![(
        "answer".to_owned(),
        checks(),
        Settlement::Settled
    )]);
    let answer = constant_of(submission.composed(), SurfaceName::from("answer"));
    assert!(
        matches!(submission.evaluate(answer), Maybe::Present(Evaluation::Value(ref value)) if value.as_ref() == "3")
    );
}

/// An operator-backed definition remains usable by the next revision.
#[test]
fn operator_definition_carries_across_lines()
{
    let mut session = session(SourceRoot::Strict);
    let first = "def z : +U (-F Integer) ; def z = thunk { become 1 + 2 } ;";
    let initial = submit(&mut session, first);
    assert_eq!(rows(initial.composed()), vec![(
        "z".to_owned(),
        checks(),
        Settlement::Settled
    )]);
    let revision =
        format!("{first} def answer : +U (-F Integer) ; def answer = thunk {{ become z() }} ;");
    let mut submission = submit(&mut session, &revision);
    assert_eq!(rows(submission.composed()), vec![
        ("z".to_owned(), checks(), Settlement::Settled),
        ("answer".to_owned(), checks(), Settlement::Settled)
    ]);
    let answer = constant_of(submission.composed(), SurfaceName::from("answer"));
    assert!(
        matches!(submission.evaluate(answer), Maybe::Present(Evaluation::Value(ref value)) if value.as_ref() == "3")
    );
}

/// Qualified prelude calls preserve identity and first-argument selection.
#[test]
fn module_builtins_type_and_evaluate()
{
    let mut session = session(SourceRoot::Strict);
    let mut submission = submit(
        &mut session,
        "def identity : +U (-F Integer) ; def identity = thunk { become prim.id(5) } ; def first : +U (-F Integer) ; def first = thunk { become prim.const(7, 9) } ;",
    );
    assert_eq!(rows(submission.composed()), vec![
        ("identity".to_owned(), checks(), Settlement::Settled),
        ("first".to_owned(), checks(), Settlement::Settled)
    ]);
    for (name, expected) in [("identity", "5"), ("first", "7")] {
        let constant = constant_of(submission.composed(), SurfaceName::from(name));
        assert!(
            matches!(submission.evaluate(constant), Maybe::Present(Evaluation::Value(ref value)) if value.as_ref() == expected)
        );
    }
}

/// Comparison has Boolean result type and evaluates to the true injection.
#[test]
fn comparison_operators_type_check_and_evaluate()
{
    let mut session = session(SourceRoot::Strict);
    let mut submission = submit(
        &mut session,
        "def answer : +U (-F Bool) ; def answer = thunk { become 1 < 2 } ;",
    );
    assert_eq!(rows(submission.composed()), vec![(
        "answer".to_owned(),
        checks(),
        Settlement::Settled
    )]);
    let answer = constant_of(submission.composed(), SurfaceName::from("answer"));
    assert!(
        matches!(submission.evaluate(answer), Maybe::Present(Evaluation::Value(ref value)) if value.as_ref() == "inl(unit)")
    );
}

/// Dependent parameter types remain scoped through checking and readmission.
#[test]
fn a_dependent_signature_is_an_abstention_not_a_refusal()
{
    let mut session = session(SourceRoot::Strict);
    let submission = submit(&mut session, "def id(a : Type, x : a) -> -F a { return x }");
    assert_eq!(rows(submission.composed()), vec![(
        "id".to_owned(),
        checks(),
        Settlement::Settled
    )]);
}

/// The cross-tree key of the first declaration form of `text`.
///
/// # Specification
/// trivial.
fn first_declaration(text: gandr_surface_syntax::SourceText<'_>) -> gandr_surface_syntax::NodeKey
{
    let grammar = crate::common::grammar();
    let tree = gandr_surface_parser::parse(&grammar, text)
        .expect("the text parses")
        .into_tree();
    tree.children(tree.root())
        .find(|&child| {
            tree.node(child).is_some_and(|node| {
                matches!(node.label(), gandr_surface_syntax::NodeLabel::Meld(_))
            })
        })
        .and_then(|child| tree.key(child))
        .expect("the text declares a form")
}

/// The session keeps the accepted revision's documentation under the
/// documented form's identity, which an edit to the documentation alone
/// leaves unchanged, and an undocumented form answers the absence.
#[test]
fn documentation_is_kept_by_declaration_identity()
{
    let mut session = session(SourceRoot::Strict);
    let first = "/// The answer.\ndef answer = 42 ;\ndef other = 1 ;";
    let _submitted = submit(&mut session, first);
    let answer = first_declaration(first.into());
    assert!(
        matches!(session.documentation(answer), Maybe::Present(text) if text.as_ref() == "The answer.")
    );
    let other = first_declaration("def other = 1 ;".into());
    assert!(matches!(
        session.documentation(other),
        Maybe::Absent(gandr_surface_lowering::documentation::Absent::Undocumented)
    ));
    let second = "/// The answer,\n/// twice over.\ndef answer = 42 ;\ndef other = 1 ;";
    let _submitted = submit(&mut session, second);
    assert_eq!(first_declaration(second.into()), answer);
    assert!(
        matches!(session.documentation(answer), Maybe::Present(text) if text.as_ref() == "The answer,\ntwice over.")
    );
}
