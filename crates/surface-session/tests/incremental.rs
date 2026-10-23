//! Bounded differentials over real surface text: resumed typings are compared
//! with a fresh checker, and compositions with the batch pipeline.
//!
//! Literal fixtures distinguish adoption, retyping, and downstream refusals.
//! Generated edit chains extend that domain; they do not prove agreement for
//! every source. The composition comparison shares the dispatcher's parse
//! and judgement, unlike the independent fresh-checker comparison.

use std::collections::HashMap;

use gandr_core_incremental::Adoption;
use gandr_core_incremental::Answered;
use gandr_core_incremental::ItemCheckpoint;
use gandr_core_incremental::ItemContent;
use gandr_core_incremental::ItemCount;
use gandr_core_incremental::ItemSource as _;
use gandr_core_incremental::MemoryCheckpointStore;
use gandr_core_incremental::Typing;
use gandr_storage_records::InMemoryBlockStore;
use gandr_surface_dispatcher::LoweringCount;
use gandr_surface_dispatcher::SourceRoot;
use gandr_surface_dispatcher::compose;
use gandr_surface_session::Revision;
use gandr_surface_session::Session;
use gandr_surface_session::SurfaceItems;
use gandr_surface_syntax::SourceText;
use proptest::prelude::ProptestConfig;
use proptest::prop_assert_eq;
use proptest::prop_oneof;
use proptest::proptest;
use proptest::strategy::Just;
use proptest::strategy::Strategy;
use proptest::strategy::ValueTree as _;
use proptest::test_runner::TestRunner;
use quenchant_shape::shape::Maybe;

use crate::common::GRAMMAR;
use crate::common::Text;
use crate::common::batch;
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
/// - requires: both inputs lower as modules, and the edited revision can be
///   submitted and leaves a resume.
/// - ensures: returns the edited revision's ordered adoption tags after
///   checking its full resumed typings against a fresh checker and its
///   composition against the batch pipeline.
/// - panics: if either input cannot be submitted, the edited revision has no
///   resume, or either comparison disagrees.
/// - executable: none — the independently checked program, composition, and
///   typings are local observations consumed before return. The opaque input
///   conversions are consumed once; a postcondition would repeat parsing and
///   checking or merely enumerate the closed adoption variants. The full
///   comparisons already execute in the body.
///
/// # Adequacy
/// - hypothesis: L2 for reuse — literal body, insertion, identity, retyping,
///   deletion, and rename fixtures compare complete typings against a fresh
///   checker. The separate property adds 200 generated edit chains. Composition
///   agreement is L3 because both paths share the dispatcher. Exact adoption
///   rows distinguish needless rechecking from unsound reuse; the sampled
///   domain is not universal.
/// - witness: `tests::incremental::body_edit_adopts_the_type_stable_dependent`
/// - witness: `tests::incremental::insertion_adopts_untouched_neighbours`
/// - witness: `tests::incremental::noop_edit_adopts_everything`
/// - witness: `tests::incremental::type_change_retypes_the_dependent`
/// - witness: `tests::incremental::downstream_error_surfaces`
/// - witness: `tests::incremental::deletion_matches_from_scratch`
/// - witness: `tests::incremental::rename_matches_from_scratch`
/// - witness: `tests::incremental::incremental_equals_from_scratch`
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
    let grammar = &*GRAMMAR;
    let mut lowerings = LoweringCount::default();
    let composed = compose(
        grammar,
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
    let program = SurfaceItems::new(grammar.clone())
        .items(&Revision::from(edited))
        .expect("the edited revision is offered");
    assert_eq!(
        resumed(&session),
        batch(&program),
        "incremental resume equals from-scratch typing\n base:   {base:?}\n edited: {edited:?}"
    );
    match session.last() {
        Maybe::Present(resume) => resume.adoptions().to_vec(),
        Maybe::Absent(reason) => panic!("the session holds no resume: {reason:?}"),
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

/// The over-adoption twin of a handed-on signature (#2102): `three`'s
/// signature decodes `code`, whose value changes while its type does not, so
/// `three`'s content and every answer it consulted stand. Only the value it
/// read changed, and a seat handed on from the base would check `3` at
/// `Integer`; the gate requires the fresh checker's refusal at `String`.
#[test]
fn a_signature_decoding_a_changed_code_is_judged_again_2102()
{
    let adoptions = gate(
        "def code : Type ;\ndef code = Integer ;\ndef three : code ;\ndef three = 3 ;",
        "def code : Type ;\ndef code = String ;\ndef three : code ;\ndef three = 3 ;",
    );
    assert_eq!(
        adoptions,
        vec![Adoption::Judged, Adoption::Judged],
        "the reader of the changed code's value is judged, not adopted"
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
        let grammar = &*GRAMMAR;
        let items = SurfaceItems::new(grammar.clone());
        let mut session = Session::new(
            grammar.clone(),
            SourceRoot::Fixture,
            MemoryCheckpointStore::default(),
            InMemoryBlockStore::default(),
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
                grammar,
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

/// The checkpoints the session's latest resume holds, in source order; none
/// before a revision was accepted.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a copy of every checkpoint of the latest resume, in its order, or
///   none when the session holds no resume.
/// - panics: none.
/// - executable: none — the copy is the observation; a clause would compare it
///   with the borrow it was cloned from.
///
/// # Adequacy
/// - hypothesis: L3 — the dirty-set witness reads the base it resumes from and
///   the from-scratch checkpoints through this, and an absent base judges every
///   item.
/// - witness: `tests::incremental::an_edit_judges_exactly_the_items_its_support_logs_separate`
fn latest(session: &Session<MemoryCheckpointStore, InMemoryBlockStore>) -> Vec<ItemCheckpoint>
{
    match session.last() {
        Maybe::Present(resume) => resume.checkpoints().items().to_vec(),
        Maybe::Absent(_) => Vec::new(),
    }
}

/// The support log `base` records, by content: each checkpoint's consulted
/// answers under the content it holds.
///
/// # Specification
/// - requires: no two checkpoints of `base` hold the same content, which each
///   item's own reference in its content ensures.
/// - ensures: one entry per checkpoint, its support under its content.
/// - panics: none.
/// - executable: none — the map is the clause.
///
/// # Adequacy
/// - hypothesis: L2 — as [`separated`].
/// - witness: `tests::incremental::an_edit_judges_exactly_the_items_its_support_logs_separate`
fn logged(base: &[ItemCheckpoint]) -> HashMap<&ItemContent, &[Answered]>
{
    base.iter()
        .map(|recorded| (recorded.content(), recorded.support()))
        .collect()
}

/// The adoption of each `fresh` item read off the two support logs: adopted
/// exactly when `base` holds a checkpoint of the same content whose recorded
/// support is the support the item's from-scratch judgement records.
///
/// # Specification
/// - requires: `base` is a [`logged`] support log; `fresh` are the checkpoints
///   a from-scratch judgement of the edited revision records, and no type
///   position of it reads a definition.
/// - ensures: one tag per `fresh` item, in order: adopted when `base` holds its
///   content with equal support, judged otherwise.
/// - panics: none.
/// - executable: none — the body is the clause, one lookup per item.
///
/// # Adequacy
/// - hypothesis: L2 — generated edit chains compare this prediction with what
///   the resume did; the census of the same run asserts that new, touched and
///   untouched items each occur.
/// - witness: `tests::incremental::an_edit_judges_exactly_the_items_its_support_logs_separate`
fn separated(
    base: &HashMap<&ItemContent, &[Answered]>,
    fresh: &[ItemCheckpoint],
) -> Vec<Adoption>
{
    fresh
        .iter()
        .map(|item| match base.get(item.content()) {
            Some(&support) if support == item.support() => Adoption::Adopted,
            Some(_) | None => Adoption::Judged,
        })
        .collect()
}

/// How often a generated edit reached each way an item is decided: adopted,
/// judged for new content, judged for a recorded answer the edit changed.
#[derive(Clone, Copy, Debug, Default)]
struct Reached
{
    /// Items adopted.
    adopted: usize,
    /// Items judged because the base holds no checkpoint of their content.
    new: usize,
    /// Items of unchanged content judged because a recorded answer moved.
    touched: usize,
}

/// One body of a chain: an integer, a text, or a read of an earlier
/// definition.
#[derive(Clone, Copy, Debug)]
enum Link
{
    /// An integer literal.
    Integer(u8),
    /// A text literal.
    Text,
    /// A read of the definition this index names among those before it.
    Read(u8),
}

/// A link: integers and reads drawn more often than texts, so a retyping
/// edit usually has readers.
///
/// # Specification
/// - requires: nothing.
/// - ensures: draws each link variant.
/// - panics: none.
/// - executable: none — the result is a dormant strategy, not a drawn value.
///
/// # Adequacy
/// - hypothesis: L2 — the dirty-set witness asserts that the drawn chains reach
///   a reader judged for a retyped definition.
/// - witness: `tests::incremental::an_edit_judges_exactly_the_items_its_support_logs_separate`
fn link() -> impl Strategy<Value = Link>
{
    prop_oneof![
        2 => (0_u8 .. 4_u8).prop_map(Link::Integer),
        1 => Just(Link::Text),
        3 => (0_u8 .. 8_u8).prop_map(Link::Read),
    ]
}

/// The text of the chain `links`: `def d<i> = <link> ;` in order, a read
/// naming an earlier definition, and the first definition's read an integer.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one line per link, each defining `d<i>` and reading only
///   definitions before it.
/// - panics: none.
/// - executable: none — the clause would render the text again.
///
/// # Adequacy
/// - hypothesis: L2 — every drawn chain is submitted and accepted by the
///   dirty-set witness.
/// - witness: `tests::incremental::an_edit_judges_exactly_the_items_its_support_logs_separate`
fn chained(links: &[Link]) -> String
{
    use core::fmt::Write as _;

    let mut text = String::new();
    for (index, link) in links.iter().enumerate() {
        let body = match *link {
            Link::Integer(literal) => format!("{literal}"),
            Link::Text => String::from("\"t\""),
            Link::Read(read) => usize::from(read)
                .checked_rem(index)
                .map_or_else(|| String::from("0"), |read| format!("d{read}")),
        };
        writeln!(text, "def d{index} = {body} ;").expect("a string takes every write");
    }
    text
}

/// The revisions of a chain under edits that each replace one body.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the chain's text, then one text per edit, each the previous with
///   one link replaced.
/// - panics: none.
/// - executable: none — the result is a dormant strategy, not a drawn value.
///
/// # Adequacy
/// - hypothesis: L2 — as [`link`].
/// - witness: `tests::incremental::an_edit_judges_exactly_the_items_its_support_logs_separate`
fn chain_revisions() -> impl Strategy<Value = Vec<String>>
{
    (
        proptest::collection::vec(link(), 1_usize .. 8_usize),
        proptest::collection::vec((0_u8 .. 8_u8, link()), 1_usize .. 5_usize),
    )
        .prop_map(|(mut links, edits)| {
            let mut revisions = vec![chained(&links)];
            for (at, link) in edits {
                let at = usize::from(at).checked_rem(links.len());
                if let Some(slot) = at.and_then(|at| links.get_mut(at)) {
                    *slot = link;
                }
                revisions.push(chained(&links));
            }
            revisions
        })
}

/// The revisions of a generated program under its generated edits.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the program's text, then one text per edit applied in order.
/// - panics: none.
/// - executable: none — the result is a dormant strategy, not a drawn value.
///
/// # Adequacy
/// - hypothesis: L2 — as `program_and_edits`, every revision submitted.
/// - witness: `tests::incremental::an_edit_judges_exactly_the_items_its_support_logs_separate`
fn program_revisions() -> impl Strategy<Value = Vec<String>>
{
    program_and_edits().prop_map(|(statements, edits)| {
        let mut current = statements;
        let mut revisions = vec![render(&current)];
        for edit in &edits {
            current = apply(&current, edit);
            revisions.push(render(&current));
        }
        revisions
    })
}

/// Submit `revisions` in order to one session and check each accepted edit
/// against a from-scratch judgement of its text: the resumed checkpoints are
/// the from-scratch ones, the items judged are exactly those the support logs
/// separate, and the same text submitted again judges nothing, molds nothing,
/// and composes the same report and kernel manifest. Counts each item's way
/// into `reached`.
///
/// # Specification
/// - requires: no type position of a revision reads a definition.
/// - ensures: returns once every revision after the first was checked.
/// - panics: when a check disagrees, naming the revision.
/// - executable: none — the checks are the body's assertions.
///
/// # Adequacy
/// - hypothesis: L2 — both generators' deterministic draws, with the reach of
///   every way an item is decided asserted.
/// - witness: `tests::incremental::an_edit_judges_exactly_the_items_its_support_logs_separate`
fn drift(
    revisions: &[String],
    reached: &mut Reached,
)
{
    let Some((first, edits)) = revisions.split_first()
    else {
        return;
    };
    let mut editor = session(SourceRoot::Fixture);
    let _base = submit(&mut editor, first);
    for text in edits {
        let base = latest(&editor);
        let submission = submit(&mut editor, text);
        let Maybe::Present(resumed) = submission.resumed()
        else {
            continue;
        };
        let mut scratch = session(SourceRoot::Fixture);
        let _fresh = submit(&mut scratch, text);
        let fresh = latest(&scratch);
        let Maybe::Present(resume) = editor.last()
        else {
            panic!("an accepted revision leaves a resume");
        };
        assert_eq!(
            resume.checkpoints().items(),
            fresh.as_slice(),
            "the resumed checkpoints are the from-scratch ones, for {text:?}"
        );
        let log = logged(&base);
        let predicted = separated(&log, &fresh);
        assert_eq!(
            resume.adoptions(),
            predicted.as_slice(),
            "the judged items are the ones the support logs separate, for {text:?}"
        );
        for (item, adoption) in fresh.iter().zip(&predicted) {
            let known = log.contains_key(item.content());
            let count = match (*adoption, known) {
                (Adoption::Adopted, _) => &mut reached.adopted,
                (Adoption::Judged, false) => &mut reached.new,
                (Adoption::Judged, true) => &mut reached.touched,
            };
            *count = count.saturating_add(1);
        }
        let again = submit(&mut editor, text);
        assert_eq!(
            (again.composed(), again.kernel()),
            (submission.composed(), submission.kernel()),
            "the same text composes the same report and kernel manifest, for {text:?}"
        );
        assert!(
            matches!(again.resumed(), Maybe::Present(unchanged)
                if unchanged.census().judged == ItemCount::from(0_usize)
                    && unchanged.census().items == resumed.census().items),
            "the same text judges nothing, for {text:?}"
        );
        assert_eq!(
            usize::from(again.forms().molded()),
            0_usize,
            "the same text molds no form, for {text:?}"
        );
    }
}

#[test]
fn an_edit_judges_exactly_the_items_its_support_logs_separate()
{
    let mut runner = TestRunner::deterministic();
    let mut reached = Reached::default();
    let programs = program_revisions();
    let chains = chain_revisions();
    for _ in 0_u32 .. CASES {
        let revisions = programs
            .new_tree(&mut runner)
            .expect("the strategy generates")
            .current();
        drift(&revisions, &mut reached);
        let revisions = chains
            .new_tree(&mut runner)
            .expect("the strategy generates")
            .current();
        drift(&revisions, &mut reached);
    }
    // The deterministic runner gives 2006 adopted items, 471 judged for new
    // content and 46 judged for a recorded answer an edit moved; the floors
    // sit at about half, so a generator change that loses a class fails here
    // rather than passing the property vacuously.
    assert!(
        reached.adopted >= 1_000_usize && reached.new >= 230_usize && reached.touched >= 23_usize,
        "every way an item is decided is reached: {reached:?}"
    );
}

#[test]
fn a_retyped_definition_dirties_its_reader_and_nothing_else()
{
    let mut editor = session(SourceRoot::Fixture);
    let _base = submit(&mut editor, "def x = 1 ;\ndef y = x ;\ndef z = 2 ;");
    let base = latest(&editor);
    let edited = "def x = \"hi\" ;\ndef y = x ;\ndef z = 2 ;";
    let _edited = submit(&mut editor, edited);
    let mut scratch = session(SourceRoot::Fixture);
    let _fresh = submit(&mut scratch, edited);
    let fresh = latest(&scratch);
    let log = logged(&base);
    let known: Vec<bool> = fresh
        .iter()
        .map(|item| log.contains_key(item.content()))
        .collect();
    assert_eq!(known, vec![false, true, true], "only x's content changed");
    assert_eq!(separated(&log, &fresh), vec![
        Adoption::Judged,
        Adoption::Judged,
        Adoption::Adopted
    ]);
}
