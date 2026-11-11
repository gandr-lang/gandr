//! The trace layer: a recheck at the trace sink keeps, for each declaration
//! that the judgement judged, the tree of the goals that its check visited.

use std::path::Path;
use std::path::PathBuf;

use gandr_core_checker::Polled;
use gandr_core_checker::Unretired;
use gandr_core_incremental::MemoryCheckpointStore;
use gandr_core_incremental::Refusal;
use gandr_core_incremental::Typing;
use gandr_kernel_term::ConstantIndex;
use gandr_storage_records::InMemoryBlockStore;
use gandr_surface_dispatcher::SourceRoot;
use gandr_surface_dispatcher::lay_out;
use gandr_surface_pretty::PageWidth;
use gandr_surface_session::ClosureSlot;
use gandr_surface_session::Counts;
use gandr_surface_session::DerivationNode;
use gandr_surface_session::Instrument;
use gandr_surface_session::Lay;
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
            matches!(derivation.goals().goal(root, Lay::Page(page)), Maybe::Present(ref goal) if !goal.as_ref().is_empty())
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

/// A body that sums 50 variables holds goals that nest `let` blocks up to 49
/// deep: the checker's second run over the body's elaboration. The layout of
/// such a goal resolves forced contexts, which the resolver memoizes under
/// their mode (#6747). Without that memo, 19 of the goals pass the resolver's
/// ceiling of 4,000,000 frontier entries and print nothing. The expected text
/// is the print of the shallowest of the 19 before the memo, with every
/// ceiling lifted: the layout that the cost order chooses when no ceiling
/// refuses it.
#[test]
fn a_deep_goal_prints_as_it_does_with_no_ceiling_6747()
{
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/trace/unformatted/a-deep-goal-prints-as-it-does-with-no-ceiling-6747.gandr");
    let text =
        include_str!("trace/unformatted/a-deep-goal-prints-as-it-does-with-no-ceiling-6747.gandr");
    let mut traced = session(SourceRoot::Strict);
    recheck(&mut traced, (&path, Text(text)), Trace::default);
    let page = PageWidth::from(80_u32);
    let (constant, ..) = traced
        .account()
        .rows()
        .next()
        .expect("the source declares `big`");
    let Maybe::Present(derivation) = traced.account().derivation_at(constant)
    else {
        panic!("`big` holds a tree");
    };
    let goals = derivation.goals();
    let printed: Vec<String> = derivation
        .nodes()
        .iter()
        .filter_map(|node| match goals.goal(node, Lay::Page(page)) {
            Maybe::Present(goal) => Some(format!("{goal}")),
            Maybe::Absent(_) => None,
        })
        .collect();
    assert_eq!(
        printed.len(),
        derivation.nodes().len(),
        "every goal of the tree prints"
    );
    let unbounded =
        include_str!("trace/expected/a-deep-goal-prints-as-it-does-with-no-ceiling-6747.txt");
    assert!(
        printed.iter().any(|goal| goal == unbounded),
        "a deep goal prints as it does with no ceiling"
    );
}

/// The goals of a corpus source's trees, printed at a page of 80 columns,
/// spell each binder as the source writes it and each variable by the name of
/// its binder. `identity(x)` and `first(x, y)` lower to lambdas, whose goals
/// and whose bodies' goals the source names `x` and `y`. A printer that named
/// a lambda's binder by its own scheme, or a variable bound above the printed
/// node by no name at all, prints `a`, `b` or `?` where the source writes `x`
/// and `y`.
#[test]
fn a_goal_prints_its_binders_as_the_source_names_them_6717()
{
    let path = source();
    let text = std::fs::read_to_string(&path).expect("the corpus source is read");
    let mut traced = session(SourceRoot::Strict);
    recheck(&mut traced, (&path, Text(&text)), Trace::default);
    let page = PageWidth::from(80_u32);
    let goals: Vec<Vec<String>> = traced
        .account()
        .rows()
        .map(|(constant, ..)| {
            let Maybe::Present(derivation) = traced.account().derivation_at(constant)
            else {
                panic!("the declaration at {constant:?} holds a tree");
            };
            let goals = derivation.goals();
            derivation
                .nodes()
                .iter()
                .filter_map(|node| match goals.goal(node, Lay::Page(page)) {
                    Maybe::Present(goal) => Some(format!("{goal}")),
                    Maybe::Absent(_) => None,
                })
                .collect()
        })
        .collect();
    // The goals from each body's lambda on: the declared types before them
    // bind no name.
    let bodies: Vec<Vec<&str>> = goals
        .iter()
        .take(2)
        .map(|goals| {
            goals
                .iter()
                .skip_while(|goal| !goal.starts_with("fun"))
                .map(String::as_str)
                .collect()
        })
        .collect();
    assert_eq!(
        bodies,
        [
            Vec::from(["fun (x) { x }", "x", "x", "x"]),
            Vec::from(["fun (x) { fun (y) { x } }", "fun (y) { x }", "x", "x", "x"]),
        ],
        "each lambda's goal spells its binder as written, and each goal under it the variable"
    );
    assert!(
        goals.iter().flatten().all(|goal| !goal.contains('?')),
        "no goal prints a variable with no name: {goals:?}"
    );
}

/// At the trace layer the pass takes no verdict of the judgement and decides
/// each item itself, in a context opened as the judgement's is (#6707). So
/// `rank` and `weigh`, whose matches leave an arm to a pattern hole, keep the
/// judgement's `UndecidedCoverage` in their checkpoints.
#[test]
fn a_traced_pass_keeps_the_judgement_s_refusal_of_a_pattern_hole_6707()
{
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(
        "tests/incremental/fixtures/a-deciding-pass-refuses-a-pattern-hole-as-its-judgement-does-6707.gandr",
    );
    let text = std::fs::read_to_string(&path).expect("the fixture is read");
    let mut traced = session(SourceRoot::Strict);
    recheck(&mut traced, (&path, Text(&text)), Trace::default);
    let Maybe::Present(resume) = traced.last()
    else {
        panic!("the recheck leaves a resume");
    };
    let undecided = resume
        .checkpoints()
        .items()
        .iter()
        .filter(|checkpoint| {
            matches!(
                checkpoint.typing(),
                Typing::Refused(Refusal::UndecidedCoverage(_))
            )
        })
        .count();
    assert_eq!(
        undecided, 2,
        "`rank` and `weigh` keep `UndecidedCoverage` at the trace layer"
    );
}
