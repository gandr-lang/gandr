//! The edit loop's differential: every revision a session parses through its
//! form store reports what the walk's composition of the same text reports,
//! and what a fresh session's whole-revision submission holds — the
//! composition, the standing, the parse's repairs, the kernel checkpoint and
//! the resume's typings — over generated modules of both roots, edited by
//! every class of edit, at one thread and at several.

use core::num::NonZeroUsize;

use anodized::spec;
use gandr_core_incremental::MemoryCheckpointStore;
use gandr_storage_records::InMemoryBlockStore;
use gandr_surface_corpus::CorpusRoot;
use gandr_surface_dispatcher::Composed;
use gandr_surface_dispatcher::LoweringCount;
use gandr_surface_dispatcher::SourceRoot;
use gandr_surface_dispatcher::Step;
use gandr_surface_dispatcher::Threads;
use gandr_surface_dispatcher::Walk;
use gandr_surface_dispatcher::Width;
use gandr_surface_dispatcher::compose;
use gandr_surface_parser::FormSplit;
use gandr_surface_parser::Molder;
use gandr_surface_parser::label;
use gandr_surface_session::FormCensus;
use gandr_surface_session::FormCount;
use gandr_surface_session::Session;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SourceText;
use proptest::prelude::ProptestConfig;
use proptest::prelude::any;
use proptest::proptest;
use quenchant_shape::shape::Maybe;

use crate::common::GRAMMAR;
use crate::common::Text;
use crate::common::backend;
use crate::common::corpus;
use crate::common::grammar;
use crate::common::resumed;
use crate::common::session;
use crate::large::FormEdit;
use crate::large::Position;
use crate::large::edits;
use crate::large::module;
use crate::large::script;

/// The cases the generated property runs: fewer where specifications are
/// enforced, whose checks multiply a submission's cost about fortyfold.
const CASES: u32 = if cfg!(anodized_panic) { 6 } else { 24 };

/// The large script's module: two thousand forms, or thirty-two where
/// specifications are enforced, so that lane runs every edit class through
/// every checked clause within its time limit on the smallest runner.
const LARGE: usize = if cfg!(anodized_panic) { 32 } else { 2_000 };

/// Every how many corpus sources the edit scripts take: each, or every sixth
/// where specifications are enforced.
const STRIDE: usize = if cfg!(anodized_panic) { 6 } else { 1 };

/// Submit `text` to `incremental` and assert it reports what the walk's
/// composition and a fresh session's submission of the same text report.
///
/// # Specification
/// - requires: `incremental` sits under `root`.
/// - ensures: the incremental submission faults exactly when the composition
///   does, with the same fault; otherwise its composition is the walk's, and
///   its standing, completion obligations, kernel checkpoint and resume typings
///   are a fresh session's. Answers the incremental submission's form census.
/// - panics: when any of those differ, naming `context`.
///
/// # Adequacy
/// - hypothesis: L2 — every generated and scripted revision is compared through
///   it; a field it skipped would let a store bug through.
/// - witness: `tests::forms::every_generated_edit_submits_as_the_walk_composes_it`
/// - witness: `tests::forms::a_large_module_edit_script_submits_as_the_walk_composes_it`
#[spec(ensures: |ret| ret.molded() <= ret.forms())]
fn agree(
    incremental: &mut Session<MemoryCheckpointStore, InMemoryBlockStore>,
    root: SourceRoot,
    text: Text<'_>,
    context: &dyn core::fmt::Display,
) -> FormCensus
{
    let source = SourceText::from(text.0);
    let walked = compose(
        &GRAMMAR,
        root.corpus_root(),
        source,
        &mut LoweringCount::default(),
    );
    let submitted = incremental.submit(source);
    let (submission, walked) = match (submitted, walked) {
        (Ok(submission), Ok(walked)) => (submission, walked),
        (Err(fault), Err(walked)) => {
            assert_eq!(
                fault.to_string(),
                walked.to_string(),
                "{context}: the fault"
            );
            return FormCensus::default();
        },
        (submitted, walked) => panic!(
            "{context}: the session {} where the walk {}",
            if submitted.is_ok() {
                "submitted"
            }
            else {
                "faulted"
            },
            if walked.is_ok() {
                "composed"
            }
            else {
                "faulted"
            }
        ),
    };
    assert_eq!(
        *submission.composed(),
        walked,
        "{context}: the composition is the walk's"
    );
    let mut whole = session(root).with_width(Width::SERIAL);
    let fresh = whole
        .submit(source)
        .expect("the whole revision submits as before");
    assert_eq!(
        submission.standing(),
        fresh.standing(),
        "{context}: the standing"
    );
    assert_eq!(
        submission.obligations(),
        fresh.obligations(),
        "{context}: the parse's repairs"
    );
    assert_eq!(
        submission.kernel(),
        fresh.kernel(),
        "{context}: the kernel checkpoint"
    );
    let census = submission.forms();
    assert_eq!(
        census.forms(),
        fresh.forms().forms(),
        "{context}: the forms"
    );
    if matches!(walked, Composed::Settled { .. }) {
        assert_eq!(
            resumed(incremental),
            resumed(&whole),
            "{context}: the typings"
        );
    }
    census
}

/// Three threads: wider than one, narrower than the host.
///
/// # Specification
/// trivial.
fn three() -> Width
{
    Width::Threads(Threads::from(NonZeroUsize::MIN.saturating_add(2)))
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(CASES))]

    #[test]
    fn every_generated_edit_submits_as_the_walk_composes_it(
        forms in 8_usize .. 48,
        fixture in any::<bool>(),
        wide in any::<bool>(),
        chain in edits(FormCount::from(6_usize)),
    ) {
        let root = if fixture { SourceRoot::Fixture } else { SourceRoot::Strict };
        let width = if wide { three() } else { Width::SERIAL };
        let mut module = module(FormCount::from(forms), root);
        let mut incremental = session(root).with_width(width);
        let _first = agree(&mut incremental, root, Text::from(&module.text()), &"the generated module");
        for edit in &chain {
            module.edit(edit);
            let _census = agree(&mut incremental, root, Text::from(&module.text()), &format_args!("{edit:?}"));
        }
    }
}

#[test]
fn a_large_module_edit_script_submits_as_the_walk_composes_it()
{
    // Two thousand forms, each root, every class of edit at the host's
    // width: each revision agrees, the first molds every form, and each edit
    // after it molds a handful.
    let forms = FormCount::from(LARGE);
    for root in [SourceRoot::Strict, SourceRoot::Fixture] {
        let mut module = module(forms, root);
        let mut incremental = session(root);
        let first = agree(
            &mut incremental,
            root,
            Text::from(&module.text()),
            &format_args!("{root:?}"),
        );
        assert_eq!(first.forms(), forms, "{root:?}: one run per generated form");
        assert_eq!(
            first.molded(),
            forms,
            "{root:?}: the first revision molds every form"
        );
        for edit in script(forms) {
            module.edit(&edit);
            let census = agree(
                &mut incremental,
                root,
                Text::from(&module.text()),
                &format_args!("{root:?} {edit}"),
            );
            assert!(
                usize::from(census.molded()) <= 8,
                "{root:?} {edit}: molds {} of {} forms",
                usize::from(census.molded()),
                usize::from(census.forms())
            );
        }
    }
}

#[test]
fn a_one_form_edit_molds_only_the_forms_that_read_it()
{
    // Twelve forms of twenty-one significant tokens each. Unchanged, none is
    // molded; a change past a form's eighth significant token molds that form
    // alone; a change within its first eight molds it and the form before,
    // whose lookahead reads them.
    let form = |i: usize, name: &str, returned: &str| {
        format!("def {name}{i} = thunk {{ fn (x) {{ fn (y) {{ pure {returned} }} }} }} ;\n")
    };
    let text = |renamed: &str, returned: &str| -> String {
        (0 .. 12)
            .map(|i| match i {
                6 => form(i, renamed, returned),
                _ => form(i, "p", "x"),
            })
            .collect()
    };
    let root = SourceRoot::Strict;
    let mut incremental = session(root);
    for (revision, molded) in [
        (text("p", "x"), 12_usize),
        (text("p", "x"), 0),
        (text("p", "y"), 1),
        (text("q", "y"), 2),
        (text("q", "y"), 0),
    ] {
        let census = agree(&mut incremental, root, Text::from(&revision), &revision);
        assert_eq!(usize::from(census.forms()), 12);
        assert_eq!(usize::from(census.molded()), molded, "{revision}");
    }
}

#[test]
fn a_reopened_session_keeps_the_forms_it_parsed()
{
    // A session reopened over a revision holds that revision's forms: the
    // same text submitted next molds none of them, and an edit molds only
    // what it touches.
    let root = SourceRoot::Fixture;
    let mut module = module(FormCount::from(40_usize), root);
    let text = module.text();
    let mut reopened = Session::reopen(
        grammar(),
        root,
        MemoryCheckpointStore::default(),
        InMemoryBlockStore::default(),
        backend(),
        SourceText::from(text.as_str()),
    )
    .expect("the module reopens")
    .into_session();
    let census = agree(
        &mut reopened,
        root,
        Text::from(&text),
        &"the reopened revision",
    );
    assert_eq!(usize::from(census.molded()), 0);
    module.edit(&FormEdit::Change(Position(20)));
    let census = agree(
        &mut reopened,
        root,
        Text::from(&module.text()),
        &"one change",
    );
    assert!(usize::from(census.molded()) <= 3, "{census:?}");
}

/// A byte offset into a source.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Byte(usize);

/// The byte at which each form of `text` starts, in source order, as the
/// parser's split predicts them, and the text's length after the last.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one start per predicted form, ascending, then the length.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — every corpus source's script cuts at these bytes and
///   submits to the walk's compositions.
/// - witness: `tests::forms::every_corpus_edit_script_submits_as_the_walk_composes_it`
#[spec(ensures: |ret| ret.windows(2).all(|pair| matches!(pair, [left, right] if left <= right))
    && ret.last().copied() == Some(Byte(text.0.len())))]
fn form_starts(text: Text<'_>) -> Vec<Byte>
{
    let molder = Molder::new(&GRAMMAR);
    let split = FormSplit::new(&molder, SourceText::from(text.0));
    let tokens = label(SourceFragment::from(text.0));
    let mut starts: Vec<Byte> = split
        .runs()
        .iter()
        .filter_map(|run| tokens.get(usize::from(run.start())))
        .filter_map(|token| usize::try_from(token.start).ok())
        .map(Byte)
        .collect();
    starts.push(Byte(text.0.len()));
    starts
}

#[test]
fn every_corpus_edit_script_submits_as_the_walk_composes_it()
{
    // Every source of both corpus roots (every sixth where specifications are
    // enforced), then a declaration inserted at its middle form, its first
    // form deleted, its last form moved first, and the source again: each
    // revision agrees with the walk's composition and a fresh session's.
    let mut walk = Walk::new(vec![
        corpus(CorpusRoot::Strict),
        corpus(CorpusRoot::Fixture),
    ]);
    let mut walked = 0_usize;
    let mut sources = 0_usize;
    while let Maybe::Present(step) = walk.step() {
        let Step::Source {
            path, root, text, ..
        } = step
        else {
            panic!("the corpus walks without a fault: {step:?}");
        };
        walked = walked.saturating_add(1);
        if walked.rem_euclid(STRIDE) != 0 {
            continue;
        }
        let original = String::from(<&str>::from(text));
        let starts = form_starts(Text::from(&original));
        let cut = |at: usize| {
            original
                .split_at_checked(at)
                .unwrap_or((original.as_str(), ""))
        };
        let middle = starts
            .get(starts.len().div_euclid(2))
            .map_or(0, |&Byte(at)| at);
        let first_end = starts.get(1).map_or(original.len(), |&Byte(at)| at);
        let last_start = starts.iter().rev().nth(1).map_or(0, |&Byte(at)| at);
        let (head, tail) = cut(middle);
        let inserted = format!("{head}def inserted = 1;\n{tail}");
        let deleted = String::from(cut(first_end).1);
        let (front, last) = cut(last_start);
        let moved = format!("{last}\n{front}");
        let mut incremental = session(root);
        for (revision, name) in [
            (&original, "the source"),
            (&inserted, "an insertion"),
            (&deleted, "a deletion"),
            (&moved, "a move"),
            (&original, "the source again"),
        ] {
            let _census = agree(
                &mut incremental,
                root,
                Text::from(revision),
                &format_args!("{}: {name}", path.display()),
            );
        }
        sources = sources.saturating_add(1);
    }
    assert!(sources > 0, "the corpus roots are populated");
}
