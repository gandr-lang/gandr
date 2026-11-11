//! The trace layer: a recheck at the trace sink keeps, for each declaration
//! that the judgement judged, the tree of the goals that its check visited.

use std::path::Path;
use std::path::PathBuf;

use gandr_core_checker::Polled;
use gandr_core_checker::Unretired;
use gandr_core_incremental::MemoryCheckpointStore;
use gandr_kernel_term::ConstantIndex;
use gandr_storage_records::InMemoryBlockStore;
use gandr_surface_dispatcher::SourceRoot;
use gandr_surface_dispatcher::lay_out;
use gandr_surface_pretty::PageWidth;
use gandr_surface_session::ClosureSlot;
use gandr_surface_session::Counts;
use gandr_surface_session::DerivationNode;
use gandr_surface_session::Instrument;
use gandr_surface_session::MemoMark;
use gandr_surface_session::Session;
use gandr_surface_session::Trace;
use gandr_surface_session::Warrant;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::common::GRAMMAR;
use crate::common::Text;
use crate::common::session;

/// The corpus source the witness rechecks.
///
/// # Specification
/// trivial.
fn source() -> PathBuf
{
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../surface-corpus/strict/functions.gandr")
}

/// Judge `text`, the source at `path`, in `session` as the hub judges it:
/// laid out after its closure, the prelude first. The judgement and the
/// admission each run at a fresh sink that `sink` makes; then the settle.
///
/// # Specification
/// trivial.
fn recheck<Sink>(
    session: &mut Session<MemoryCheckpointStore, InMemoryBlockStore>,
    (path, Text(text)): (&Path, Text<'_>),
    sink: fn() -> Sink,
) where
    Sink: Instrument,
{
    let laid = lay_out(&GRAMMAR, path, SourceRoot::Strict, SourceText::from(text));
    let slot = ClosureSlot::new();
    let Ok(Polled::Whole(_)) = session.judge_unit_reading_retiring(
        SourceText::from(laid.text.as_str()),
        (&laid.unit, laid.base),
        &slot,
        |_| (),
        (&Unretired, &mut sink()),
    )
    else {
        panic!("the revision is judged whole");
    };
    let Maybe::Present(detached) = session.admission()
    else {
        panic!("the judgement left its admission");
    };
    let ran = detached.run(&Unretired, &mut sink()).whole();
    let Ok(Maybe::Present(_)) = session.settle(ran)
    else {
        panic!("the admission settles");
    };
}

/// Assert that `nodes`, the tree at `constant`, is a tree in pre-order: the
/// first node is a root, each node is at most one deeper than the one before
/// it, and each node's count of visited nodes spans exactly the nodes deeper
/// than it that follow it.
///
/// # Specification
/// trivial.
fn assert_nests(
    constant: ConstantIndex,
    nodes: &[DerivationNode],
)
{
    let depth = |node: &DerivationNode| u32::from(node.depth());
    let first_is_a_root = nodes.first().is_some_and(|node| depth(node) == 0);
    let steps_down_one = nodes.windows(2).all(
        |pair| matches!(pair, [before, after] if depth(after) <= depth(before).saturating_add(1)),
    );
    let spans = nodes.iter().enumerate().all(|(at, node)| {
        let end =
            at.saturating_add(usize::try_from(u32::from(node.visited())).unwrap_or(usize::MAX));
        nodes
            .get(at.saturating_add(1) .. end)
            .is_some_and(|under| under.iter().all(|below| depth(below) > depth(node)))
            && nodes.get(end).is_none_or(|next| depth(next) <= depth(node))
    });
    assert!(
        first_is_a_root && steps_down_one && spans,
        "the tree at {constant:?} nests: {nodes:?}"
    );
}

/// A corpus source, laid out after the prelude as the hub lays it, rechecked
/// at the trace sink in one session and at the counts sink in another. Each
/// declaration holds a tree that nests in the order the machine met its
/// goals; the tree marks a hit for each goal that the memo answered and a
/// miss for each goal it keyed first, as many as the counts layer counts; and
/// each node reads replayed, since the admission replays the declaration. The
/// printer spells each root's goal at a page of 80 columns, and the root's
/// rule has a name. A second recheck of the same text adopts each item, so
/// each declaration keeps its tree. A fold that nested a goal under the wrong
/// parent, a mark taken from the wrong consult, a warrant that did not read
/// the kernel's tier, or a tree dropped on adoption changes what a row holds.
#[test]
fn each_judged_declaration_keeps_the_tree_its_judgement_visited()
{
    let path = source();
    let text = std::fs::read_to_string(&path).expect("the corpus source is read");
    let mut traced = session(SourceRoot::Strict);
    recheck(&mut traced, (&path, Text(&text)), Trace::default);
    let mut counted = session(SourceRoot::Strict);
    recheck(&mut counted, (&path, Text(&text)), Counts::default);
    let page = PageWidth::from(80_u32);
    let mut kept = Vec::new();
    for ((constant, ..), (_, _, row)) in traced.account().rows().zip(counted.account().rows()) {
        let Maybe::Present(derivation) = traced.account().derivation_at(constant)
        else {
            panic!("the declaration at {constant:?} holds a tree");
        };
        let nodes = derivation.nodes();
        assert_nests(constant, nodes);
        let Maybe::Present(counts) = row.counts()
        else {
            panic!("the row at {constant:?} is counted");
        };
        let marked = |mark: MemoMark| {
            u64::try_from(nodes.iter().filter(|node| node.memo() == mark).count())
                .unwrap_or(u64::MAX)
        };
        assert_eq!(
            (marked(MemoMark::Hit), marked(MemoMark::Miss)),
            (u64::from(counts.hits()), u64::from(counts.misses())),
            "the tree at {constant:?} marks the consults the counts layer counts"
        );
        assert!(
            nodes
                .iter()
                .all(|node| derivation.warrant(node) == Warrant::Replayed),
            "each node at {constant:?} is replayed"
        );
        let root = nodes.first().expect("a tree has a root");
        assert!(
            matches!(derivation.goal(root, page), Maybe::Present(ref goal) if !goal.as_ref().is_empty())
                && !derivation.rule(root).as_ref().is_empty(),
            "the root at {constant:?} prints its goal and names its rule"
        );
        kept.push(nodes.to_vec());
    }
    assert!(!kept.is_empty(), "the source declares something of its own");
    recheck(&mut traced, (&path, Text(&text)), Trace::default);
    let again: Vec<Vec<DerivationNode>> = traced
        .account()
        .rows()
        .map(
            |(constant, ..)| match traced.account().derivation_at(constant) {
                Maybe::Present(derivation) => derivation.nodes().to_vec(),
                Maybe::Absent(reason) => {
                    panic!("the declaration at {constant:?} keeps its tree: {reason:?}")
                },
            },
        )
        .collect();
    assert_eq!(
        again, kept,
        "a second recheck adopts each item and keeps each tree"
    );
}
