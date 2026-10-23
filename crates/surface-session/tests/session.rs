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
use gandr_surface_session::Tables;
use gandr_surface_session::admission;
use gandr_surface_session::admitted;
use gandr_surface_session::evaluation;
use gandr_surface_session::import;
use gandr_surface_session::resumed;
use gandr_surface_syntax::ByteOffset;
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
        Composed::Settled { ref report, .. } => report
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
        Composed::Refused(ref refusal) => panic!("refused as a whole: {refusal}"),
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

/// The de Bruijn table of the type an unsigned body synthesised; none for
/// any other typing.
///
/// # Specification
/// - requires: nothing.
/// - ensures: returns the produced type's projection for synthesised typing,
///   and no node for checked, native, owed or refused typing, or for a
///   projection the type cannot make.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — integer and string literal typings and a later reference
///   compare exact base-type nodes. The predicate excludes nodes from
///   nonsynthesizing variants; the concrete witnesses cover synthesized
///   outputs, not every typing variant.
/// - witness: `tests::session::scalar_literals_carry_their_types`
/// - witness: `tests::session::definitions_carry_across_lines`
/// - witness: `tests::session::integer_literal_types_and_evaluates`
#[spec(
    ensures: |ret| match *typing {
    Typing::Synthesised { ref produced, .. } => produced.debruijn().map_or(ret.is_empty(), |table| *ret == table),
    Typing::Data | Typing::Checked { .. } | Typing::Owed | Typing::Suspended | Typing::Refused(_) => ret.is_empty(),
},
)]
fn produced(typing: &Typing) -> Vec<ContentNode>
{
    match *typing {
        Typing::Synthesised { ref produced, .. } => produced.debruijn().unwrap_or_default(),
        Typing::Data
        | Typing::Checked { .. }
        | Typing::Owed
        | Typing::Suspended
        | Typing::Refused(_) => Vec::new(),
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
        Maybe::Present(resumed) => resumed.census(),
        Maybe::Absent(reason) => panic!("the submission carries no resume: {reason:?}"),
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
    let refused = submit(&mut session, "@[ checks ]");
    assert!(
        matches!(refused.composed(), Composed::Refused(_)),
        "a revision that declares nothing is refused as a whole"
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
        .judge(gandr_surface_syntax::SourceText::from("@[ checks ]"))
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
    let Maybe::Present(row) = session.resolve_import(&list)
    else {
        panic!("the second line's alias resolves");
    };
    assert_eq!(
        second
            .text()
            .fragment(row.span())
            .map(|covered| String::from(covered.as_ref())),
        Ok(String::from(
            "import \"file:///lib/list.gandr\" as list_ext ;"
        )),
        "the row covers its own declaration in the revision's text"
    );
    assert_eq!(
        second.base(),
        ByteOffset::default(),
        "a revision that imports no sibling starts its own text at zero"
    );

    let duplicate = submit(
        &mut session,
        "import \"file:///lib/parse.gandr\" as parse ;\nimport \"file:///lib/list.gandr\" as list_ext ;\nimport \"file:///lib/other.gandr\" as parse ;",
    );
    assert!(
        rows(duplicate.composed())
            .iter()
            .any(|row| row.0 == "import"
                && row.1 == Outcome::Refuses(RefusalName::DuplicateImportAlias)),
        "a later line cannot silently replace an import alias: the import is refused: {:?}",
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

/// A session keeps no type tables until asked. Asked, it hands each judged
/// revision's table on once, and a second take reads apart from a table never
/// kept.
#[test]
fn a_kept_table_is_handed_on_once()
{
    let mut session = session(SourceRoot::Strict);
    let mut unkept = submit(&mut session, "def a = 1 ;");
    let Maybe::Absent(untabled) = unkept.take_table()
    else {
        panic!("a session keeps no table unless asked");
    };
    session.keep(Tables::Kept);
    let mut kept = submit(&mut session, "def a = 1 ;\ndef b = a ;");
    assert!(
        matches!(kept.take_table(), Maybe::Present(_)),
        "a session asked to keep tables keeps the judged revision's"
    );
    let Maybe::Absent(taken) = kept.take_table()
    else {
        panic!("the table is handed on once");
    };
    assert_ne!(
        taken, untabled,
        "a taken table reads apart from one never kept"
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
    let mut whole = submit(&mut held, r#"@[ checks ]"#);
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
        matches!(submission.evaluate(answer), Maybe::Present(Evaluation::Value(ref value)) if value.as_ref() == "+{.0 = unit}")
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

/// The session keeps what each accepted declaration's `deprecated`
/// attribute states under the form's identity: a record's texts, nothing
/// for a bare mark, and no answer for an unmarked form.
#[test]
fn a_deprecation_is_kept_by_declaration_identity()
{
    let mut session = session(SourceRoot::Strict);
    let text = "@[ deprecated(#{ since = \"0.2\", note = \"use `other`\" }) ]\ndef answer = 42 \
                ;\n@[ deprecated ]\ndef bare = 2 ;\ndef other = 1 ;";
    let _submitted = submit(&mut session, text);
    let key = |form: &str| first_declaration(form.into());
    assert_eq!(
        session.deprecation(key("def answer = 42 ;")),
        Some(&gandr_surface_lowering::Deprecation {
            since: Some(String::from("0.2")),
            note: Some(String::from("use `other`")),
        }),
        "a record states both texts"
    );
    assert_eq!(
        session.deprecation(key("def bare = 2 ;")),
        Some(&gandr_surface_lowering::Deprecation::default()),
        "a bare mark states neither"
    );
    assert_eq!(
        session.deprecation(key("def other = 1 ;")),
        None,
        "an unmarked form answers nothing"
    );
}

/// #776: a document laid out after its import closure offers the kernel its
/// own declarations alone once the closure was admitted, exporting and
/// committing what a whole admission of the revision exports and commits, and
/// offers the whole closure again once a source of it changed.
#[test]
fn an_edit_to_its_own_text_readmits_the_document_alone_776()
{
    use gandr_core_checker::HostGrant;
    use gandr_storage_artifact::ArtifactRecordSet;
    use gandr_storage_artifact::build;
    use gandr_storage_records::InMemoryBlockStore;
    use gandr_storage_records::TreeParams;
    use gandr_surface_corpus::CorpusRoot;
    use gandr_surface_dispatcher::Lowered;
    use gandr_surface_dispatcher::LoweringCount;
    use gandr_surface_dispatcher::judge_member;
    use gandr_surface_dispatcher::lay_out;
    use gandr_surface_dispatcher::lower_unit_source;
    use gandr_surface_session::KernelCheckpoint;
    use gandr_surface_syntax::SourceText;

    let directory =
        std::env::temp_dir().join(format!("gandr-session-closure-776-{}", std::process::id()));
    let _cleared = std::fs::remove_dir_all(&directory);
    std::fs::create_dir_all(&directory).expect("the scratch directory is created");
    let directory =
        std::fs::canonicalize(&directory).expect("the scratch directory has a canonical path");
    let sibling = directory.join("base.gandr");
    let document = directory.join("document.gandr");
    std::fs::write(
        &sibling,
        "/// #776: the closure.\ndef one : Integer ;\ndef one = 1 ;\ndef two : Integer ;\ndef two \
         = one ;\n",
    )
    .expect("the sibling is written");
    // The editor's buffer is what is judged; the file only has to exist.
    std::fs::write(&document, "").expect("the document is written");
    let grammar = &*crate::common::GRAMMAR;
    let mut session = session(SourceRoot::Strict);
    // Each revision of the document, judged and admitted laid out after the
    // sibling: what the admission counted, and whether its artifact and its
    // commit are what a whole admission of the same text exports and commits.
    let mut admit = |own: &str| {
        let laid = lay_out(grammar, &document, SourceRoot::Strict, own.into());
        let Maybe::Present(laid) = laid
        else {
            panic!("the document is laid out after its sibling: {laid:?}");
        };
        let text = SourceText::from(laid.text.as_str());
        let slot = gandr_surface_session::ClosureSlot::new();
        let _judged = session
            .judge_unit_reading(text, &laid.unit, laid.base, &slot, |_| ())
            .expect("the revision is judged");
        let Ok(Maybe::Present(admitted)) = session.admit()
        else {
            panic!("the judgement left its admission");
        };
        let Lowered::Module { module, arena } =
            lower_unit_source(grammar, text, &laid.unit, &mut LoweringCount::default())
                .expect("the revision lowers")
                .into_lowered()
        else {
            panic!("the revision is not refused whole");
        };
        let whole = judge_member(
            CorpusRoot::Strict,
            (module, text),
            arena,
            &HostGrant::UNBOUNDED,
            laid.base,
        )
        .into_parts()
        .1
        .admit()
        .expect("the kernel re-derives the revision");
        let cut = ArtifactRecordSet::from_artifact(whole.as_image()).expect("the export cuts");
        let committed = build(
            &cut,
            TreeParams::current(),
            &mut InMemoryBlockStore::default(),
        )
        .expect("the records commit");
        (
            usize::from(admitted.crossed()),
            usize::from(admitted.judged()),
            *admitted.kernel() == whole,
            *admitted.checkpoint() == KernelCheckpoint::Stored(committed),
        )
    };
    let first = "import \"./base.gandr\" ;\ndef three : Integer ;\ndef three = two ;\n";
    let second = format!("{first}def four : Integer ;\ndef four = three ;\n");
    assert_eq!(
        admit(first),
        (3_usize, 3_usize, true, true),
        "the closure's first admission offers the kernel every declaration"
    );
    assert_eq!(
        admit(&second),
        (2_usize, 4_usize, true, true),
        "an edit to the document's own text offers its own declarations alone"
    );
    std::fs::write(
        &sibling,
        "/// #776: the closure, changed.\ndef one : Integer ;\ndef one = 2 ;\ndef two : Integer \
         ;\ndef two = one ;\n",
    )
    .expect("the sibling is rewritten");
    assert_eq!(
        admit(&second),
        (4_usize, 4_usize, true, true),
        "a changed sibling offers the whole closure again"
    );
    assert_eq!(
        admit(first),
        (1_usize, 3_usize, true, true),
        "and the changed closure is resumed thereafter"
    );
    let _removed = std::fs::remove_dir_all(&directory);
}

/// A poll that answers wanted a number of times, then retired.
#[repr(transparent)]
struct After(core::cell::Cell<usize>);

impl gandr_core_checker::Retirement for After
{
    type Retired = ();

    /// Wanted while polls are left, then retired.
    ///
    /// # Specification
    /// trivial.
    fn demand(&self) -> gandr_core_checker::Demand<()>
    {
        self.0
            .get()
            .checked_sub(1_usize)
            .map_or(gandr_core_checker::Demand::Retired(()), |left| {
                self.0.set(left);
                gandr_core_checker::Demand::Wanted
            })
    }
}

/// #1547: an admission retired part way leaves the record of the declarations
/// it crossed, inside the import closure or past it, and the next admission of
/// the same revision offers the kernel only those after it, exporting what a
/// whole admission exports.
#[test]
fn a_retired_admission_leaves_what_it_crossed_to_the_next_1547()
{
    use gandr_core_checker::HostGrant;
    use gandr_core_checker::Polled;
    use gandr_surface_corpus::CorpusRoot;
    use gandr_surface_dispatcher::Lowered;
    use gandr_surface_dispatcher::LoweringCount;
    use gandr_surface_dispatcher::judge_member;
    use gandr_surface_dispatcher::lay_out;
    use gandr_surface_dispatcher::lower_unit_source;
    use gandr_surface_syntax::SourceText;

    let directory =
        std::env::temp_dir().join(format!("gandr-session-retired-1547-{}", std::process::id()));
    let _cleared = std::fs::remove_dir_all(&directory);
    std::fs::create_dir_all(&directory).expect("the scratch directory is created");
    let directory =
        std::fs::canonicalize(&directory).expect("the scratch directory has a canonical path");
    let sibling = directory.join("base.gandr");
    let document = directory.join("document.gandr");
    std::fs::write(
        &sibling,
        "/// #1547: the closure.\ndef one : Integer ;\ndef one = 1 ;\ndef two : Integer ;\ndef \
         two = one ;\n",
    )
    .expect("the sibling is written");
    std::fs::write(&document, "").expect("the document is written");
    let grammar = &*crate::common::GRAMMAR;
    let mut session = session(SourceRoot::Strict);
    let own = "import \"./base.gandr\" ;\ndef three : Integer ;\ndef three = two ;\ndef four : \
               Integer ;\ndef four = three ;\n";
    let laid = lay_out(grammar, &document, SourceRoot::Strict, own.into());
    let Maybe::Present(laid) = laid
    else {
        panic!("the document is laid out after its sibling: {laid:?}");
    };
    let text = SourceText::from(laid.text.as_str());
    let judge = |session: &mut gandr_surface_session::Session<
        gandr_core_incremental::MemoryCheckpointStore,
        gandr_storage_records::InMemoryBlockStore,
    >| {
        let slot = gandr_surface_session::ClosureSlot::new();
        let _judged = session
            .judge_unit_reading(text, &laid.unit, laid.base, &slot, |_| ())
            .expect("the revision is judged");
        let Maybe::Present(detached) = session.admission()
        else {
            panic!("the judgement left its admission");
        };
        detached
    };
    // Each retirement, then the whole admission after it: what it counted and
    // the artifact it exported.
    let mut retire_then_admit = |wanted: usize| {
        let retired = judge(&mut session).run(&After(core::cell::Cell::new(wanted)));
        assert!(
            matches!(retired, Polled::Retired((), ())),
            "the admission is retired after {wanted} crossings"
        );
        let ran = judge(&mut session)
            .run(&gandr_core_checker::Unretired)
            .whole();
        let Ok(Maybe::Present(admitted)) = session.settle(ran)
        else {
            panic!("the admission settles");
        };
        (
            usize::from(admitted.crossed()),
            usize::from(admitted.judged()),
            admitted,
        )
    };
    let (crossed, judged, inside) = retire_then_admit(1_usize);
    assert_eq!(
        (crossed, judged),
        (3_usize, 4_usize),
        "retired inside the closure, the next admission crosses the rest"
    );
    let Lowered::Module { module, arena } =
        lower_unit_source(grammar, text, &laid.unit, &mut LoweringCount::default())
            .expect("the revision lowers")
            .into_lowered()
    else {
        panic!("the revision is not refused whole");
    };
    let whole = judge_member(
        CorpusRoot::Strict,
        (module, text),
        arena,
        &HostGrant::UNBOUNDED,
        laid.base,
    )
    .into_parts()
    .1
    .admit()
    .expect("the kernel re-derives the revision");
    assert!(*inside.kernel() == whole, "and exports the whole artifact");
    let (crossed, judged, past) = retire_then_admit(1_usize);
    assert_eq!(
        (crossed, judged),
        (1_usize, 4_usize),
        "retired past the closure, the next admission crosses the last declaration alone"
    );
    assert!(*past.kernel() == whole, "and exports the whole artifact");
    let _removed = std::fs::remove_dir_all(&directory);
}

/// #1547: a judgement retired before its first item leaves the session the
/// resume it held, so the next judgement of the same revision judges and
/// adopts what it would have with no retired one before it.
#[test]
fn a_retired_judgement_leaves_the_next_its_resume_1547()
{
    use gandr_core_checker::Polled;
    let first = "def kept = 40 ;\ndef edited = 1 ;\ndef after = kept ;";
    let second = "def kept = 40 ;\ndef edited = 2 ;\ndef after = kept ;";
    let mut retiring = session(SourceRoot::Strict);
    let _first = submit(&mut retiring, first);
    assert!(
        matches!(
            retiring.judge_reading_retiring(
                gandr_surface_syntax::SourceText::from(second),
                |_| (),
                &After(core::cell::Cell::new(0_usize)),
            ),
            Ok(Polled::Retired((), ()))
        ),
        "a judgement polled retired before its first item answers retired"
    );
    let after_retired = census(&submit(&mut retiring, second));
    let mut plain = session(SourceRoot::Strict);
    let _first = submit(&mut plain, first);
    let unretired = census(&submit(&mut plain, second));
    assert_eq!(
        (after_retired.adopted, after_retired.judged),
        (unretired.adopted, unretired.judged),
        "the next judgement adopts and judges what it would with no retired one before it"
    );
    assert!(
        usize::from(after_retired.adopted) > 0_usize,
        "and resumes from the first revision's items: {after_retired:?}"
    );
}

/// #1663: a judgement polls its retirement before each declaration of the
/// revision it checks and once before their settle, then before each item the
/// incremental pass adopts or judges, so a change made while the revision's
/// declarations are checked retires the judgement there.
#[test]
fn a_judgement_polls_before_each_declaration_it_checks_1663()
{
    use gandr_core_checker::Polled;
    let first = "def kept = 40 ;\ndef edited = 1 ;\ndef after = kept ;";
    let second = "def kept = 40 ;\ndef edited = 2 ;\ndef after = kept ;";
    let mut session = session(SourceRoot::Strict);
    let _first = submit(&mut session, first);
    let poll = After(core::cell::Cell::new(usize::MAX));
    let Ok(Polled::Whole(judged)) = session.judge_reading_retiring(
        gandr_surface_syntax::SourceText::from(second),
        |_| (),
        &poll,
    )
    else {
        panic!("a judgement never polled retired is judged whole");
    };
    let polled = usize::MAX.saturating_sub(poll.0.get());
    let items = census(&judged);
    let declarations = 3_usize;
    assert_eq!(
        polled,
        declarations
            .saturating_add(1_usize)
            .saturating_add(usize::from(items.adopted))
            .saturating_add(usize::from(items.judged)),
        "one poll before each declaration, one before the settle, one before each item: {items:?}"
    );
}

/// #776: each revision of a document laid out after its import closure shares
/// the closure's items' images with the revision before it, and its edits are
/// the document's own.
#[test]
fn a_document_after_its_closure_shares_the_closure_s_images_776()
{
    use alloc::sync::Arc;

    use gandr_surface_dispatcher::lay_out;
    use gandr_surface_session::Action;
    use gandr_surface_session::ItemTree;
    use gandr_surface_syntax::SourceText;

    let directory =
        std::env::temp_dir().join(format!("gandr-session-images-776-{}", std::process::id()));
    let _cleared = std::fs::remove_dir_all(&directory);
    std::fs::create_dir_all(&directory).expect("the scratch directory is created");
    let directory =
        std::fs::canonicalize(&directory).expect("the scratch directory has a canonical path");
    let sibling = directory.join("base.gandr");
    let document = directory.join("document.gandr");
    std::fs::write(
        &sibling,
        "def one : Integer ;\ndef one = 1 ;\ndef two : Integer ;\ndef two = one ;\n",
    )
    .expect("the sibling is written");
    std::fs::write(&document, "").expect("the document is written");
    let grammar = &*crate::common::GRAMMAR;
    let mut session = session(SourceRoot::Strict);
    // Each revision judged laid out after the sibling: the snapshot's items
    // and the item ordinals its edits are anchored at.
    let mut judge = |own: &str| {
        let laid = lay_out(grammar, &document, SourceRoot::Strict, own.into());
        let Maybe::Present(laid) = laid
        else {
            panic!("the document is laid out after its sibling: {laid:?}");
        };
        let text = SourceText::from(laid.text.as_str());
        let slot = gandr_surface_session::ClosureSlot::new();
        let judged = session
            .judge_unit_reading(text, &laid.unit, laid.base, &slot, |_| ())
            .expect("the revision is judged");
        let Maybe::Present(edits) = judged.edits()
        else {
            panic!("an accepted revision carries its edits");
        };
        let anchors: Vec<usize> = edits
            .actions()
            .iter()
            .map(|action| match *action {
                Action::InsertItem { at, .. }
                | Action::DeleteItem { at }
                | Action::SetSignature { at, .. }
                | Action::FillHole { at, .. }
                | Action::EraseToHole { at } => usize::from(at),
                Action::Replace { ref path, .. }
                | Action::SetLiteral { ref path, .. }
                | Action::SetVariable { ref path, .. }
                | Action::SetConstant { ref path, .. } => usize::from(path.item()),
            })
            .collect();
        let items: Vec<Arc<ItemTree>> = session.snapshot().items().to_vec();
        (items, anchors)
    };
    let first = "import \"./base.gandr\" ;\ndef three : Integer ;\ndef three = two ;\n";
    let (before, _) = judge(first);
    let (after, anchors) = judge(&format!(
        "{first}def four : Integer ;\ndef four = three ;\n"
    ));
    assert_eq!((before.len(), after.len()), (3_usize, 4_usize));
    assert!(
        before
            .iter()
            .zip(&after)
            .take(2)
            .all(|(before, after)| Arc::ptr_eq(before, after)),
        "the closure's two items keep their images"
    );
    assert_eq!(
        anchors,
        [3_usize],
        "the one edit inserts the document's new item"
    );
    let _removed = std::fs::remove_dir_all(&directory);
}

/// #1033: an importer judged twice lowers its closure once and its own source
/// each time; a second session judges it over the closure the first lowered,
/// to the same composition; every judgement reports what the dispatcher
/// composes of the laid-out text, its closure lowered and judged fresh and the
/// document judged after it; and the session's held parse of each revision is
/// the tree its judgement read, read beside the key of its closure's lowering
/// when it is typed and when it is only read. #776: the second session's first
/// submission adopts the closure's items the first session judged, judging the
/// document's own, to the first session's typings.
#[test]
fn an_importer_lowers_its_closure_once_1033()
{
    use alloc::sync::Arc;

    use gandr_core_checker::HostGrant;
    use gandr_core_incremental::MemoryCheckpointStore;
    use gandr_core_incremental::ResumeCensus;
    use gandr_storage_records::InMemoryBlockStore;
    use gandr_surface_corpus::CorpusRoot;
    use gandr_surface_dispatcher::JudgedClosure;
    use gandr_surface_dispatcher::Laid;
    use gandr_surface_dispatcher::Lowered;
    use gandr_surface_dispatcher::LoweringCount;
    use gandr_surface_dispatcher::judge_member_after;
    use gandr_surface_dispatcher::lay_out;
    use gandr_surface_dispatcher::lower_closure;
    use gandr_surface_dispatcher::lower_onto_closure;
    use gandr_surface_lowering::OriginTable;
    use gandr_surface_lowering::Unit;
    use gandr_surface_session::ClosureSlot;
    use gandr_surface_session::Led;
    use gandr_surface_session::Session;
    use gandr_surface_syntax::SourceText;

    /// The sources a judgement of `laid` lowered, its composition with the
    /// origin table, which indexes the syntax tree it was read off, cleared,
    /// and its resume's census; the session's held parse of `laid` is the
    /// tree the judgement read.
    fn judged<'text>(
        session: &mut Session<MemoryCheckpointStore, InMemoryBlockStore>,
        laid: &'text Laid,
        slot: &'text ClosureSlot,
    ) -> (LoweringCount, Composed<'text>, ResumeCensus)
    {
        let text = SourceText::from(laid.text.as_str());
        let before = usize::from(session.lowerings());
        let mut read = None;
        let submission = session
            .judge_unit_reading(text, &laid.unit, laid.base, slot, |tree| {
                read = Some(tree.clone());
            })
            .expect("the revision is judged");
        let lowered = usize::from(session.lowerings()).saturating_sub(before);
        let held = session
            .parse_held_unit(text, &laid.unit, laid.base)
            .expect("the revision parses held");
        assert_eq!(
            Some(held.tree()),
            read.as_ref(),
            "the held parse is the tree the judgement read"
        );
        let mut reread = None;
        session
            .read_held_unit(text, (&laid.unit, laid.base), |tree, key| {
                reread = Some((tree.clone(), key));
            })
            .expect("the revision parses held");
        let mut typed = None;
        let _table = session.type_held_unit(text, (&laid.unit, laid.base), |_, key| {
            typed = Some(key);
        });
        let (tree, key) = reread.expect("the reader is handed the held parse");
        assert_eq!(
            Some(&tree),
            read.as_ref(),
            "a read of the held parse reads the tree the judgement read"
        );
        assert!(
            key.is_some() && typed == Some(key),
            "beside the key of the closure's lowering a typing is handed"
        );
        (
            LoweringCount::from(lowered),
            unrooted(submission.composed().clone()),
            census(&submission),
        )
    }

    /// `composed` is what the dispatcher composes of `laid`'s text, its
    /// closure lowered and judged fresh and the document lowered and judged
    /// after it, the origin table cleared.
    fn assert_fresh(
        laid: &Laid,
        composed: &Composed<'_>,
    )
    {
        let text = SourceText::from(laid.text.as_str());
        let base = usize::from(laid.base);
        let sources = laid.unit.sources();
        let closure = Arc::new(
            lower_closure(
                Arc::new(crate::common::grammar()),
                String::from(laid.text.get(.. base).unwrap_or_default()),
                Unit::new(
                    sources
                        .get(.. sources.len().saturating_sub(1))
                        .unwrap_or_default()
                        .to_vec(),
                )
                .expect("the closure's sources make a unit"),
                &mut LoweringCount::default(),
            )
            .expect("the closure is held"),
        );
        let judged = JudgedClosure::new(
            Arc::clone(&closure),
            &HostGrant::UNBOUNDED,
            CorpusRoot::Strict,
        )
        .expect("the closure lowers to its end");
        let parsed = gandr_surface_parser::parse(
            closure.grammar(),
            SourceText::from(laid.text.get(base ..).unwrap_or_default()),
        )
        .expect("the document parses")
        .after(closure.tree(), text)
        .expect("the document lays after its closure");
        // The session lowers a document after its closure onto the arena the
        // incremental pass over the closure's items left; a fresh one here.
        let led = Led::of(&judged).expect("the closure's items are ordered");
        let (lowering, checking) = lower_onto_closure(
            &judged,
            led.arena(),
            parsed,
            &laid.unit,
            &mut LoweringCount::default(),
            &mut gandr_surface_lowering::coincide::Decisions::none(),
        )
        .expect("the document lowers");
        let Lowered::Module { module, arena } = lowering.into_lowered()
        else {
            panic!("the revision is not refused whole");
        };
        let (settled, _admission) = judge_member_after(
            CorpusRoot::Strict,
            (module, text),
            arena,
            (&HostGrant::UNBOUNDED, checking),
            laid.base,
        )
        .into_parts();
        assert_eq!(
            composed,
            &unrooted(settled.expect("the revision settles")),
            "the judgement reports what a fresh judgement of the closure composes"
        );
    }

    /// `composed` with its origin table cleared: the one table that differs
    /// between the document laid after its closure's tree and the whole
    /// text's tree, the nodes being numbered in each.
    fn unrooted(composed: Composed<'_>) -> Composed<'_>
    {
        match composed {
            Composed::Settled {
                report,
                exercised,
                unstatable,
                spellings,
                failures,
                shadowed,
                inferred,
                runs,
                deprecated,
                unused,
                unreached,
                kernel,
                program,
                ..
            } => Composed::Settled {
                report,
                exercised,
                unstatable,
                origins: OriginTable::default(),
                spellings,
                failures,
                shadowed,
                inferred,
                runs,
                deprecated,
                unused,
                unreached,
                kernel,
                program,
            },
            refused @ Composed::Refused(_) => refused,
        }
    }

    let directory =
        std::env::temp_dir().join(format!("gandr-session-closure-1033-{}", std::process::id()));
    let _cleared = std::fs::remove_dir_all(&directory);
    std::fs::create_dir_all(&directory).expect("the scratch directory is created");
    let directory =
        std::fs::canonicalize(&directory).expect("the scratch directory has a canonical path");
    let sibling = directory.join("base.gandr");
    let document = directory.join("document.gandr");
    std::fs::write(
        &sibling,
        "/// #1033: the closure.\ndef one : Integer ;\ndef one = 1 ;\ndef two : Integer ;\ndef \
         two = one ;\n",
    )
    .expect("the sibling is written");
    // The editor's buffer is what is judged; the file only has to exist.
    std::fs::write(&document, "").expect("the document is written");
    let laid = |own: &str| {
        let laid = lay_out(
            &crate::common::GRAMMAR,
            &document,
            SourceRoot::Strict,
            own.into(),
        );
        let Maybe::Present(laid) = laid
        else {
            panic!("the document is laid out after its sibling: {laid:?}");
        };
        laid
    };
    let first = laid("import \"./base.gandr\" ;\ndef three : Integer ;\ndef three = two ;\n");
    let second = laid(
        "import \"./base.gandr\" ;\ndef three : Integer ;\ndef three = two ;\ndef four : \
         Integer ;\ndef four = three ;\n",
    );
    let (cold_slot, again_slot, warm_slot) =
        (ClosureSlot::new(), ClosureSlot::new(), ClosureSlot::new());
    let mut cold = session(SourceRoot::Strict);
    let (lowered, composed, cold_census) = judged(&mut cold, &first, &cold_slot);
    assert_eq!(
        lowered,
        LoweringCount::from(2_usize),
        "the first judgement lowers the closure and the document"
    );
    assert_eq!(
        (cold_census.adopted, cold_census.judged),
        (ItemCount::from(2_usize), ItemCount::from(1_usize)),
        "and judges the document's item after the closure's, which are judged once per closure"
    );
    let cold_typings = resumed(&cold);
    assert_fresh(&first, &composed);
    let (lowered, again, again_census) = judged(&mut cold, &second, &again_slot);
    assert_eq!(
        (
            again_census.recalled,
            again_census.adopted,
            again_census.judged
        ),
        (
            ItemCount::from(2_usize),
            ItemCount::from(3_usize),
            ItemCount::from(1_usize)
        ),
        "#776: an edit to the document's own text recalls only the document's items, adopting \
         the unchanged one and judging the new"
    );
    assert_eq!(
        lowered,
        LoweringCount::from(1_usize),
        "an edit to the document's own text lowers the document alone"
    );
    assert_fresh(&second, &again);
    let mut warm = session(SourceRoot::Strict);
    let (lowered, warmed, warm_census) = judged(&mut warm, &first, &warm_slot);
    assert_eq!(
        lowered,
        LoweringCount::from(1_usize),
        "a second session lowers the document over the closure the first lowered"
    );
    assert_eq!(warmed, composed, "to the composition the cold store gave");
    assert_eq!(
        (warm_census.adopted, warm_census.judged),
        (ItemCount::from(2_usize), ItemCount::from(1_usize)),
        "its first submission adopts the closure's items and judges the document's"
    );
    assert_eq!(
        resumed(&warm),
        cold_typings,
        "to the typings the cold session's judged"
    );
    let _removed = std::fs::remove_dir_all(&directory);
}

/// A revision read through the session's form store parses as the session's
/// grammar parses it afresh: before any submission, and after one that molded
/// a form the revision shares.
#[test]
fn a_held_parse_is_the_grammar_s_own_parse()
{
    let text = gandr_surface_syntax::SourceText::from("def a = 1 ;\ndef b = a ;");
    let mut session = session(SourceRoot::Strict);
    let afresh = gandr_surface_parser::parse(session.grammar(), text)
        .expect("the revision parses")
        .tree()
        .digest();
    let held = |session: &gandr_surface_session::Session<_, _>| {
        session
            .parse_held(text)
            .expect("the revision parses")
            .tree()
            .digest()
    };
    assert_eq!(held(&session), afresh, "with nothing held");
    let _first = submit(&mut session, "def a = 1 ;");
    assert_eq!(held(&session), afresh, "with the first form held");
}
