//! The session's submissions: what each revision reports, and what the
//! session keeps between them.
//!
//! The proto session appended each submission to a running transcript; this
//! one takes each revision whole, so a later "line" is the earlier revision
//! with the line appended, and what carries across lines is what the session
//! keeps: the resume it adopts from and the import scope it resolves in.

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
/// trivial.
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
/// trivial.
fn produced(typing: &Typing) -> &[ContentNode]
{
    match *typing {
        | Typing::Synthesised { ref produced, .. } => produced.nodes(),
        | Typing::Checked { .. } | Typing::Owed | Typing::Refused(_) => &[],
    }
}

/// The census a submission's resume carries.
///
/// # Specification
/// trivial.
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
    let refused = submit(&mut session, "def f(x: NoSuchType) -> -F Integer { ret 1 }");
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
    let accepted = submit(&mut session, "def f(x: Integer) -> -F Integer { ret 1 }");
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
    let refused = submit(&mut session, "def retained = 40 ;\nret retained");
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
/// trivial.
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
        "def step() -> -F Integer { ret 1 }\ndef called : +U (-F Integer) ;\ndef called = thunk { step() } ;",
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

/// A declaration owed its body is a goal and is not evaluated; one that runs
/// into it is, and is blamed on it.
#[test]
fn holes_decline_evaluation()
{
    let mut session = session(SourceRoot::Strict);
    let mut submission = submit(
        &mut session,
        "def later : +U (-F Integer) ;\ndef main : +U (-F Integer) ;\ndef main = thunk { force later } ;",
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
