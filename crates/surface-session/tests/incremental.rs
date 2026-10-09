//! The differential over real surface text: a session resumed onto an edited
//! revision reports and types it exactly as a from-scratch run does.
//!
//! The incremental checker gates its engine against its own toy front end;
//! this is the same theorem driven through the dispatcher's parse and
//! lowering. For every edit the resumed typings equal the checker's module
//! entry over the edited program, and the submission's composition equals the
//! dispatcher's for the edited text. Adoption skips work; these suites prove
//! the skips never change the answer, and pin where the fragment lets them
//! happen.

use gandr_core_incremental::Adoption;
use gandr_core_incremental::ItemCount;
use gandr_core_incremental::ItemSource as _;
use gandr_core_incremental::MemoryCheckpointStore;
use gandr_core_incremental::Typing;
use gandr_surface_dispatcher::LoweringCount;
use gandr_surface_dispatcher::SourceRoot;
use gandr_surface_dispatcher::compose;
use gandr_surface_session::Revision;
use gandr_surface_session::Session;
use gandr_surface_session::SurfaceItems;
use gandr_surface_syntax::SourceText;
use proptest::prelude::ProptestConfig;
use proptest::prop_assert_eq;
use proptest::proptest;
use quenchant_shape::shape::Maybe;

use crate::common::Text;
use crate::common::batch;
use crate::common::grammar;
use crate::common::resumed;
use crate::common::session;
use crate::common::submit;
use crate::generate::CASES;
use crate::generate::apply;
use crate::generate::program_and_edits;
use crate::generate::render;

/// The edit fixture's base revision: a function and a thunk applying it.
const INCREMENTAL_BASE: &str = include_str!("fixtures/incremental-base.gandr");
/// The same revision with the function's returned literal changed.
const INCREMENTAL_EDITED: &str = include_str!("fixtures/incremental-edited.gandr");

/// What `edited` resumed onto `base` adopted, once the gate held: the resumed
/// typings equal the checker's module entry over the edited program, and the
/// submission's composition equals the dispatcher's.
///
/// # Specification
/// trivial.
fn gate<'text>(
    base: impl Into<Text<'text>>,
    edited: impl Into<Text<'text>>,
) -> Vec<Adoption>
{
    let Text(base) = base.into();
    let Text(edited) = edited.into();
    let mut session = session(SourceRoot::Strict);
    let _base = submit(&mut session, base);
    let submission = submit(&mut session, edited);
    let grammar = grammar();
    let mut lowerings = LoweringCount::default();
    let composed = compose(
        &grammar,
        SourceRoot::Strict.corpus_root(),
        SourceText::from(edited),
        &mut lowerings,
    )
    .expect("the edited revision composes");
    assert_eq!(
        *submission.composed(),
        composed,
        "the resumed submission reports what the batch pipeline reports\n base:   {base:?}\n edited: {edited:?}"
    );
    let program = SurfaceItems::new(grammar)
        .items(&Revision::from(edited))
        .expect("the edited revision is offered");
    assert_eq!(
        resumed(&session),
        batch(&program),
        "incremental resume equals from-scratch typing\n base:   {base:?}\n edited: {edited:?}"
    );
    match session.last() {
        | Maybe::Present(resume) => resume.adoptions().to_vec(),
        | Maybe::Absent(reason) => panic!("the session holds no resume: {reason:?}"),
    }
}

#[test]
fn body_edit_adopts_the_type_stable_dependent()
{
    assert_eq!(
        gate(INCREMENTAL_BASE, INCREMENTAL_EDITED),
        vec![Adoption::Judged, Adoption::Adopted],
        "the edited function is judged; the thunk applying it reads only its unchanged type, \
         and is adopted"
    );
}

#[test]
fn insertion_adopts_untouched_neighbours()
{
    assert_eq!(
        gate(
            "def a = 1 ;\ndef c = 3 ;",
            "def a = 1 ;\ndef b = 2 ;\ndef c = 3 ;"
        ),
        vec![Adoption::Adopted, Adoption::Judged, Adoption::Adopted],
        "only the inserted definition is judged"
    );
}

#[test]
fn noop_edit_adopts_everything()
{
    let source = "def a = 1 ;\ndef b = a ;\ndef c = b ;";
    assert_eq!(
        gate(source, source),
        vec![Adoption::Adopted; 3],
        "an identity edit reuses everything"
    );
}

#[test]
fn append_sequence_counts_reused_prefixes()
{
    let mut session = session(SourceRoot::Strict);
    let _first = submit(&mut session, "def x = 1 ;");
    for (source, adopted) in [
        ("def x = 1 ;\ndef y = x ;", 1_usize),
        ("def x = 1 ;\ndef y = x ;\ndef z = y ;", 2_usize),
    ] {
        let submission = submit(&mut session, source);
        assert!(
            matches!(submission.resumed(), Maybe::Present(resumed) if resumed.census().adopted == ItemCount::from(adopted)),
            "an append reuses its complete preceding prefix: {source:?}"
        );
    }
}

#[test]
fn type_change_retypes_the_dependent()
{
    let adoptions = gate("def x = 1 ;\ndef y = x ;", "def x = \"hi\" ;\ndef y = x ;");
    assert_eq!(
        adoptions,
        vec![Adoption::Judged, Adoption::Judged],
        "the dependent reads the retyped definition, so both are judged"
    );
}

#[test]
fn downstream_error_surfaces()
{
    let edited = "def x = \"hi\" ;\ndef y : Integer ;\ndef y = x ;";
    let adoptions = gate("def x = 1 ;\ndef y : Integer ;\ndef y = x ;", edited);
    assert_eq!(
        adoptions.get(1_usize),
        Some(&Adoption::Judged),
        "the dependent is judged against the retyped definition"
    );
    let mut session = session(SourceRoot::Strict);
    let _submission = submit(&mut session, edited);
    assert!(
        matches!(resumed(&session).get(1_usize), Some(Typing::Refused(_))),
        "the downstream mismatch surfaces rather than a stale success"
    );
}

#[test]
fn deletion_matches_from_scratch()
{
    assert_eq!(
        gate(
            "def a = 1 ;\ndef b = 2 ;\ndef c = 3 ;",
            "def a = 1 ;\ndef c = 3 ;"
        ),
        vec![Adoption::Adopted, Adoption::Adopted],
        "both survivors are reused"
    );
}

#[test]
fn rename_matches_from_scratch()
{
    let adoptions = gate(
        "def foo = 1 ;\ndef keep = 9 ;",
        "def bar = 1 ;\ndef keep = 9 ;",
    );
    assert_eq!(
        adoptions.get(1_usize),
        Some(&Adoption::Adopted),
        "a definition the renamed one does not read is adopted across the rename"
    );
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(CASES))]

    /// Over a generated revision and a chain of edits, each submitted to one
    /// session, every resumed submission reports what the batch pipeline
    /// reports and types what the checker's module entry types.
    #[test]
    fn incremental_equals_from_scratch((statements, edits) in program_and_edits()) {
        let grammar = grammar();
        let items = SurfaceItems::new(grammar.clone());
        let mut session = Session::new(
            grammar.clone(),
            SourceRoot::Fixture,
            MemoryCheckpointStore::default(),
            crate::common::backend(),
        );
        let mut current = statements;
        let base = render(&current);
        let _base = submit(&mut session, &base);
        for edit in &edits {
            current = apply(&current, edit);
            let text = render(&current);
            let submission = submit(&mut session, &text);
            let mut lowerings = LoweringCount::default();
            let composed = compose(
                &grammar,
                SourceRoot::Fixture.corpus_root(),
                SourceText::from(text.as_str()),
                &mut lowerings,
            )
            .expect("a generated revision composes");
            prop_assert_eq!(submission.composed(), &composed, "the report, for {:?}", text);
            let program = items
                .items(&Revision::from(text.as_str()))
                .expect("a generated revision is offered");
            prop_assert_eq!(resumed(&session), batch(&program), "the typings, for {:?}", text);
        }
    }
}
