//! The walk over scratch trees: its order, its standings, its faults and its
//! judgement of each component. Each visit judges with the run stage's
//! engine, so these tests stand in the `tests` target (#7048).

use core::convert::Infallible;
use core::fmt::Write as _;
use core::num::NonZeroUsize;
use core::ops::ControlFlow;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use gandr_core_checker::HostGrant;
use gandr_core_term::effect::OperationName;
use gandr_surface_dispatcher::Pool;
use gandr_surface_dispatcher::RunReport;
use gandr_surface_dispatcher::SourceCount;
use gandr_surface_dispatcher::SourceFault;
use gandr_surface_dispatcher::SourceRoot;
use gandr_surface_dispatcher::Standing;
use gandr_surface_dispatcher::Step;
use gandr_surface_dispatcher::Threads;
use gandr_surface_dispatcher::Walk;
use gandr_surface_dispatcher::Width;
use gandr_surface_dispatcher::classify;
use gandr_surface_dispatcher::fixture::Scratch;
use gandr_surface_evaluate::Evaluator;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

/// What a test row records of one step.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Seen
{
    /// A source, and how it stands.
    Source(Standing),
    /// A path that could not be listed or read.
    Unreadable,
    /// A path that yielded no source.
    NoSource,
    /// The grammar did not build.
    Grammar,
    /// The pipeline faulted on a source.
    Compose,
}

impl From<&Step<'_>> for Seen
{
    /// What a test row records of `step`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: preserves a source's standing, or records the exact
    ///   source-fault category without retaining its borrowed payload.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exact rows separate source standings, unreadable
    ///   paths and empty directories. Grammar and composition engine faults are
    ///   outside these filesystem fixtures.
    /// - witness: `tests::walk::a_tree_is_walked_in_order`
    /// - witness: `tests::walk::every_path_answers_in_order`
    /// - witness: `tests::walk::each_root_stands_its_sources`
    #[spec(ensures: |ret| match (step, ret) {
            (&Step::Source { standing, .. }, Self::Source(observed)) => observed == standing,
            (&Step::Fault { fault: SourceFault::Unreadable(_), .. }, Self::Unreadable)
                | (&Step::Fault { fault: SourceFault::NoSource, .. }, Self::NoSource)
                | (&Step::Fault { fault: SourceFault::Grammar(_), .. }, Self::Grammar)
                | (&Step::Fault { fault: SourceFault::Compose(_), .. }, Self::Compose) => true,
            _ => false,
        })]
    fn from(step: &Step<'_>) -> Self
    {
        match *step {
            Step::Source { standing, .. } => Self::Source(standing),
            Step::Fault { ref fault, .. } => match *fault {
                SourceFault::Unreadable(_) => Self::Unreadable,
                SourceFault::NoSource => Self::NoSource,
                SourceFault::Grammar(_) => Self::Grammar,
                SourceFault::Compose(_) => Self::Compose,
            },
        }
    }
}

/// The serial visit and three threads: the widths a visit is compared at,
/// the serial one first, as the reference.
///
/// # Specification
/// trivial.
fn widths() -> [Width; 2]
{
    [
        Width::SERIAL,
        Width::Threads(Threads::from(NonZeroUsize::MIN.saturating_add(2))),
    ]
}

/// Every step a visit over `paths` at `width` hands over, as
/// `(path relative to base, seen)`, and the visit's report.
///
/// # Specification
/// - requires: nothing.
/// - ensures: records each step in the order handed over, strips `base` only
///   when it is a prefix, and returns the report the visit answers, whose
///   source and fault counts agree with the recorded rows.
/// - fails: never; source faults are recorded as rows.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the rows and report are compared whole across widths over
///   nested, empty, missing and rooted inputs, which detects a lost, doubled,
///   reordered or differently counted step.
/// - witness: `tests::walk::a_tree_is_walked_in_order`
/// - witness: `tests::walk::every_path_answers_in_order`
/// - witness: `tests::walk::each_root_stands_its_sources`
#[spec(ensures: |ref ret| {
        let sources = ret.0.iter().filter(|row| matches!(row.1, Seen::Source(_))).count();
        sources == usize::from(ret.1.sources().read())
            && ret.0.len().checked_sub(sources) == Some(usize::from(ret.1.sources().faulted()))
    })]
fn visited(
    base: &Path,
    paths: Vec<PathBuf>,
    width: Width,
) -> (Vec<(PathBuf, Seen)>, RunReport)
{
    let mut seen = Vec::new();
    let ControlFlow::Continue(report) = Walk::new(paths).visit::<Evaluator, _, _>(
        &Pool::new(width),
        |step| -> ControlFlow<Infallible> {
            let kind = Seen::from(&step);
            let path = match step {
                Step::Source { path, .. } | Step::Fault { path, .. } => path,
            };
            seen.push((path.strip_prefix(base).unwrap_or(path).to_path_buf(), kind));
            ControlFlow::Continue(())
        },
    );
    (seen, report)
}

/// `(path, seen)` rows with owned paths.
///
/// # Specification
///
/// trivial.
fn rows(pairs: &[(&Path, Seen)]) -> Vec<(PathBuf, Seen)>
{
    pairs
        .iter()
        .map(|&(path, seen)| (path.to_path_buf(), seen))
        .collect()
}

#[test]
fn a_sketch_set_is_walked_only_when_named_4560()
{
    let scratch = Scratch::new(Path::new("corpus"));
    scratch.file(
        Path::new("corpus/model/a.gandr"),
        SourceText::from("def a = 1 ;"),
    );
    scratch.file(
        Path::new("corpus/sketch/cells/b.gandr"),
        SourceText::from("def b = #fuse{ f g } ;"),
    );
    scratch.file(
        Path::new("corpus/model/sketch/c.gandr"),
        SourceText::from("def c = 3 ;"),
    );
    let (seen, _report) = visited(&scratch.0, vec![scratch.0.join("corpus")], Width::SERIAL);
    assert_eq!(
        seen,
        rows(&[
            (
                Path::new("corpus/model/a.gandr"),
                Seen::Source(Standing::Settled)
            ),
            (
                Path::new("corpus/model/sketch/c.gandr"),
                Seen::Source(Standing::Settled)
            ),
        ]),
        "a walk of the corpus leaves the sketch set out, and only the one directly inside it"
    );
    let (seen, _report) = visited(
        &scratch.0,
        vec![scratch.0.join("corpus/sketch")],
        Width::SERIAL,
    );
    assert_eq!(
        seen,
        rows(&[(
            Path::new("corpus/sketch/cells/b.gandr"),
            Seen::Source(Standing::Unsettled)
        )]),
        "the sketch set named as a path is walked"
    );
}

#[test]
fn a_tree_is_walked_in_order()
{
    let scratch = Scratch::new(Path::new("tree"));
    scratch.file(Path::new("tree/b.gandr"), SourceText::from("def b = 2 ;"));
    scratch.file(
        Path::new("tree/a/z.gandr"),
        SourceText::from("def z = missing ;"),
    );
    scratch.file(Path::new("tree/a/y.gandr"), SourceText::from("def y = 1 ;"));
    scratch.file(
        Path::new("tree/a/notes.txt"),
        SourceText::from("not a source"),
    );
    scratch.file(Path::new("tree/c.gandr"), SourceText::from("@[ checks ]"));
    scratch.file(Path::new("named.source"), SourceText::from("def n = 4 ;"));
    scratch.file(
        Path::new("elsewhere/linked.gandr"),
        SourceText::from("def l = 5 ;"),
    );
    #[cfg(unix)]
    std::os::unix::fs::symlink(
        scratch.0.join("elsewhere/linked.gandr"),
        scratch.0.join("tree/linked.gandr"),
    )
    .expect("the link is made");

    let paths = vec![scratch.0.join("tree"), scratch.0.join("named.source")];
    assert_eq!(
        Walk::new(paths.clone()).sources_up_to(SourceCount::from(8_usize)),
        SourceCount::from(5_usize),
        "a count under a larger bound reaches each source the visit reaches"
    );
    assert_eq!(
        Walk::new(paths.clone()).sources_up_to(SourceCount::from(2_usize)),
        SourceCount::from(2_usize),
        "a count stops at its bound"
    );
    let (seen, report) = visited(&scratch.0, paths.clone(), Width::SERIAL);
    assert_eq!(
        seen,
        rows(&[
            (Path::new("tree/a/y.gandr"), Seen::Source(Standing::Settled)),
            (
                Path::new("tree/a/z.gandr"),
                Seen::Source(Standing::Unsettled)
            ),
            (Path::new("tree/b.gandr"), Seen::Source(Standing::Settled)),
            (Path::new("tree/c.gandr"), Seen::Source(Standing::Refused)),
            (Path::new("named.source"), Seen::Source(Standing::Settled)),
        ]),
        "depth-first in name order, sources only, no link followed, an explicit file of any name"
    );
    assert_eq!(
        report.sources().faulted(),
        SourceCount::from(0_usize),
        "no path faults"
    );
    assert_eq!(
        report.sources().strict(),
        SourceCount::from(5_usize),
        "five strict sources"
    );
    assert_eq!(
        report.sources().refused(),
        SourceCount::from(1_usize),
        "one refused whole"
    );
    assert_eq!(
        usize::from(report.lowerings()),
        5_usize,
        "one lowering per source read"
    );
    assert_eq!(
        usize::from(report.tally().declarations().unsettled()),
        1_usize,
        "the undefined name is the one unsettled declaration"
    );
    for width in widths() {
        assert_eq!(
            visited(&scratch.0, paths.clone(), width),
            (seen.clone(), report),
            "a visit at {width:?} hands over the serial visit's steps and counts"
        );
    }
}

#[cfg(feature = "instrument")]
#[test]
fn a_recorded_walk_marks_each_lowering_and_hands_over_the_same_steps()
{
    use gandr_core_fork::activity::Declared;
    use gandr_core_fork::activity::Edge;
    use gandr_core_fork::activity::Fold;
    use gandr_core_fork::activity::Slots;
    use gandr_core_fork::activity::Task;
    use gandr_core_fork::activity::World;

    let scratch = Scratch::new(Path::new("recorded"));
    for name in ["a", "b", "c", "d"] {
        scratch.file(
            &Path::new("tree").join(format!("{name}.gandr")),
            SourceText::from("def x = 1 ;"),
        );
    }
    let paths = vec![scratch.0.join("tree")];
    let width = Width::Threads(Threads::from(NonZeroUsize::MIN.saturating_add(2)));
    let (unrecorded, unrecorded_report) = visited(&scratch.0, paths.clone(), width);
    let pool = Pool::new(width);
    let activity = pool.activity(Slots::from(NonZeroUsize::new(256_usize).unwrap()));
    let recording = pool.recording(&activity, (Task::Fork, World::from(0)), |_| Declared::NONE);
    let mut seen = Vec::new();
    let ControlFlow::Continue(report) = Walk::new(paths).visit_recording::<Evaluator, _, _, _>(
        &recording,
        |step| -> ControlFlow<Infallible> {
            let kind = Seen::from(&step);
            let path = match step {
                Step::Source { path, .. } | Step::Fault { path, .. } => path,
            };
            seen.push((
                path.strip_prefix(&scratch.0).unwrap_or(path).to_path_buf(),
                kind,
            ));
            ControlFlow::Continue(())
        },
    );
    assert_eq!(
        (seen, report),
        (unrecorded, unrecorded_report),
        "a recorded walk hands over the steps and the counts of an unrecorded one"
    );
    let mut fold = Fold::new(&activity);
    let card = fold.tick(&activity, gandr_surface_dispatcher::activity_clock());
    let marked = |edge| {
        card.events
            .iter()
            .filter(|event| event.edge == edge)
            .count()
    };
    assert_eq!(
        (marked(Edge::Start), marked(Edge::End)),
        (4, 4),
        "each component's lowering is marked once at its start and once at its end"
    );
}

#[test]
fn every_path_answers_in_order()
{
    let scratch = Scratch::new(Path::new("answers"));
    scratch.file(
        Path::new("empty/notes.txt"),
        SourceText::from("not a source"),
    );
    scratch.file(Path::new("one.gandr"), SourceText::from("def one = 1 ;"));
    let paths = vec![
        scratch.0.join("absent.gandr"),
        scratch.0.join("empty"),
        scratch.0.join("one.gandr"),
        scratch.0.join("absent"),
    ];
    let (seen, report) = visited(&scratch.0, paths.clone(), Width::SERIAL);
    assert_eq!(
        seen,
        rows(&[
            (Path::new("absent.gandr"), Seen::Unreadable),
            (Path::new("empty"), Seen::NoSource),
            (Path::new("one.gandr"), Seen::Source(Standing::Settled)),
            (Path::new("absent"), Seen::Unreadable),
        ]),
        "each path answers once, in the order given"
    );
    assert_eq!(
        report.sources().faulted(),
        SourceCount::from(3_usize),
        "three faults"
    );
    assert_eq!(
        report.sources().read(),
        SourceCount::from(1_usize),
        "one source read"
    );
    for width in widths() {
        assert_eq!(
            visited(&scratch.0, paths.clone(), width),
            (seen.clone(), report),
            "a visit at {width:?} answers every path in the serial visit's order"
        );
    }
}

/// #3889: an entry another path given names is reached once, by that
/// path: a directory given after its subdirectory and one of its sources
/// reaches neither again, answers through them, and reaches the rest.
#[test]
fn a_path_another_path_names_is_walked_once_3889()
{
    let scratch = Scratch::new(Path::new("named-elsewhere"));
    scratch.file(
        Path::new("outer/inner/a.gandr"),
        SourceText::from("def a = 1 ;"),
    );
    scratch.file(Path::new("outer/b.gandr"), SourceText::from("def b = 2 ;"));
    scratch.file(Path::new("outer/c.gandr"), SourceText::from("def c = 3 ;"));
    scratch.file(
        Path::new("covered/inner/d.gandr"),
        SourceText::from("def d = 4 ;"),
    );
    let paths = vec![
        scratch.0.join("outer/inner"),
        scratch.0.join("outer"),
        scratch.0.join("outer/b.gandr"),
        scratch.0.join("covered/inner"),
        scratch.0.join("covered"),
    ];
    let (seen, report) = visited(&scratch.0, paths.clone(), Width::SERIAL);
    assert_eq!(
        seen,
        rows(&[
            (
                Path::new("outer/inner/a.gandr"),
                Seen::Source(Standing::Settled)
            ),
            (Path::new("outer/c.gandr"), Seen::Source(Standing::Settled)),
            (Path::new("outer/b.gandr"), Seen::Source(Standing::Settled)),
            (
                Path::new("covered/inner/d.gandr"),
                Seen::Source(Standing::Settled)
            ),
        ]),
        "each source once, by the path naming it; a directory whose sources another path \
             walks answers through it"
    );
    assert_eq!(
        report.sources().faulted(),
        SourceCount::from(0_usize),
        "no path faults"
    );
    for width in widths() {
        assert_eq!(
            visited(&scratch.0, paths.clone(), width),
            (seen.clone(), report),
            "a visit at {width:?} reaches the serial visit's sources"
        );
    }
}

/// A source given twice answers twice, each time as judged once: its
/// component is lowered no more often than when each source is given
/// once, and every answer of each is handed over.
#[test]
fn a_source_given_twice_answers_twice_from_one_judgement()
{
    let scratch = Scratch::new(Path::new("given-twice"));
    scratch.file(
        Path::new("fixture/base.gandr"),
        SourceText::from("pub def one = 1 ;"),
    );
    scratch.file(
        Path::new("fixture/importer.gandr"),
        SourceText::from(include_str!(
            "walk/fixtures/a-source-given-twice-answers-twice-from-one-judgement.gandr"
        )),
    );
    let [base, importer] =
        ["base.gandr", "importer.gandr"].map(|file| scratch.0.join("fixture").join(file));
    let paths = vec![
        importer.clone(),
        base.clone(),
        importer.clone(),
        base.clone(),
    ];
    for width in core::iter::once(Width::SERIAL).chain(widths()) {
        let (_, once) = visited(&scratch.0, vec![importer.clone(), base.clone()], width);
        let (seen, report) = visited(&scratch.0, paths.clone(), width);
        assert_eq!(
            seen,
            rows(&[
                (
                    Path::new("fixture/importer.gandr"),
                    Seen::Source(Standing::Settled)
                ),
                (
                    Path::new("fixture/base.gandr"),
                    Seen::Source(Standing::Settled)
                ),
                (
                    Path::new("fixture/importer.gandr"),
                    Seen::Source(Standing::Settled)
                ),
                (
                    Path::new("fixture/base.gandr"),
                    Seen::Source(Standing::Settled)
                ),
            ]),
            "at {width:?}, each giving answers, in the order given"
        );
        assert_eq!(
            report.lowerings(),
            once.lowerings(),
            "at {width:?}, giving the sources again lowers nothing again"
        );
    }
}

#[test]
fn each_root_stands_its_sources()
{
    let scratch = Scratch::new(Path::new("roots"));
    let owes = SourceText::from("@[ owes(1) ] def a : Integer ;");
    scratch.file(Path::new("corpus/strict/owes.gandr"), owes);
    scratch.file(Path::new("corpus/fixture/owes.gandr"), owes);
    scratch.file(
        Path::new("corpus/fixture/whole.gandr"),
        SourceText::from("@[ checks ]"),
    );
    scratch.file(
        Path::new("corpus/fixture/pending/outside.gandr"),
        SourceText::from("@[ checks ]"),
    );
    scratch.file(
        Path::new("corpus/fixture/pending/lowered.gandr"),
        SourceText::from("def a = 1 ;"),
    );
    scratch.file(
        Path::new("corpus/fixture/pending/form.gandr"),
        SourceText::from(include_str!(
            "walk/fixtures/each-root-stands-its-sources.gandr"
        )),
    );
    scratch.file(
        Path::new("corpus/fixture/pending/coded.gandr"),
        SourceText::from("def small : Type ; def small = Integer ;"),
    );
    let (seen, report) = visited(&scratch.0, vec![scratch.0.join("corpus")], Width::SERIAL);
    assert_eq!(
        seen,
        rows(&[
            (
                Path::new("corpus/fixture/owes.gandr"),
                Seen::Source(Standing::Settled)
            ),
            (
                Path::new("corpus/fixture/pending/coded.gandr"),
                Seen::Source(Standing::Lowered)
            ),
            (
                Path::new("corpus/fixture/pending/form.gandr"),
                Seen::Source(Standing::Pending)
            ),
            (
                Path::new("corpus/fixture/pending/lowered.gandr"),
                Seen::Source(Standing::Lowered)
            ),
            (
                Path::new("corpus/fixture/pending/outside.gandr"),
                Seen::Source(Standing::Pending)
            ),
            (
                Path::new("corpus/fixture/whole.gandr"),
                Seen::Source(Standing::Refused)
            ),
            (
                Path::new("corpus/strict/owes.gandr"),
                Seen::Source(Standing::Unsettled)
            ),
        ]),
        "the root each source sits under decides its standing; a code the command IL \
             never carries leaves a pending source lowered"
    );
    let sources = report.sources();
    assert_eq!(
        (sources.strict(), sources.fixture(), sources.pending()),
        (
            SourceCount::from(1_usize),
            SourceCount::from(2_usize),
            SourceCount::from(4_usize)
        ),
        "each source counted under its root"
    );
    assert_eq!(
        (sources.refused(), sources.lowered_pending()),
        (SourceCount::from(1_usize), SourceCount::from(2_usize)),
        "the fixture source refused whole, and the pending sources lowered"
    );
    assert_eq!(
        (
            usize::from(report.tally().declarations().settled()),
            usize::from(report.tally().declarations().unsettled())
        ),
        (3_usize, 1_usize),
        "a pending source's declarations are not counted; a lowered one's are"
    );
    assert_eq!(
        classify(&scratch.0.join("corpus/fixture/pending/outside.gandr")),
        SourceRoot::Pending,
        "the pending set is classified by location"
    );
    for width in widths() {
        assert_eq!(
            visited(&scratch.0, vec![scratch.0.join("corpus")], width),
            (seen.clone(), report),
            "a visit at {width:?} stands each source under its root"
        );
    }
}

#[test]
fn a_grant_bounds_every_source_the_walk_judges()
{
    let scratch = Scratch::new(Path::new("granted"));
    scratch.file(
        Path::new("corpus/fixture/both.gandr"),
        SourceText::from("@[ owes(1) ] def fs : Cap {read, write} ;"),
    );
    scratch.file(
        Path::new("corpus/fixture/read.gandr"),
        SourceText::from("@[ owes(1) ] def reads : Cap {read} ;"),
    );
    let reading =
        HostGrant::within([&OperationName::from("read")]).expect("the host offers `read`");
    for width in widths() {
        for (grant, both) in [
            (HostGrant::UNBOUNDED, Standing::Settled),
            (reading.clone(), Standing::Unsettled),
        ] {
            let mut seen = Vec::new();
            let ControlFlow::Continue(_report) = Walk::new(vec![scratch.0.join("corpus")])
                .granting(grant.clone())
                .visit::<Evaluator, _, _>(&Pool::new(width), |step| -> ControlFlow<Infallible> {
                    let kind = Seen::from(&step);
                    let path = match step {
                        Step::Source { path, .. } | Step::Fault { path, .. } => path,
                    };
                    seen.push((
                        path.strip_prefix(&scratch.0).unwrap_or(path).to_path_buf(),
                        kind,
                    ));
                    ControlFlow::Continue(())
                });
            assert_eq!(
                seen,
                rows(&[
                    (Path::new("corpus/fixture/both.gandr"), Seen::Source(both)),
                    (
                        Path::new("corpus/fixture/read.gandr"),
                        Seen::Source(Standing::Settled)
                    ),
                ]),
                "at {width:?} under {grant:?}, a capability claiming `write` is owed \
                     only where no grant bounds it, and one within the grant stays owed"
            );
        }
    }
}

#[test]
fn a_stopped_visit_hands_over_nothing_more()
{
    let scratch = Scratch::new(Path::new("stopped"));
    scratch.file(Path::new("a.gandr"), SourceText::from("def a = 1 ;"));
    scratch.file(Path::new("b.gandr"), SourceText::from("def b = 2 ;"));
    scratch.file(Path::new("c.gandr"), SourceText::from("def c = 3 ;"));
    for width in widths() {
        let mut handed = Vec::new();
        let stopped = Walk::new(vec![scratch.0.clone()]).visit::<Evaluator, _, _>(
            &Pool::new(width),
            |step| {
                let path = match step {
                    Step::Source { path, .. } | Step::Fault { path, .. } => path,
                };
                handed.push(path.strip_prefix(&scratch.0).unwrap_or(path).to_path_buf());
                if handed.len() == 2 {
                    ControlFlow::Break(path.to_path_buf())
                }
                else {
                    ControlFlow::Continue(())
                }
            },
        );
        assert_eq!(
            stopped,
            ControlFlow::Break(scratch.0.join("b.gandr")),
            "the visit answers the visitor's stop at {width:?}"
        );
        assert_eq!(
            handed,
            vec![PathBuf::from("a.gandr"), PathBuf::from("b.gandr")],
            "no step follows the stop at {width:?}"
        );
    }
}

#[test]
fn a_tree_is_read_when_visited()
{
    let scratch = Scratch::new(Path::new("late-changes"));
    let root = scratch.0.join("strict/tree");
    let walk = Walk::new(vec![root.clone()]);
    let first = "def first = 1 ;";
    let last = "def last = 2 ;";
    scratch.file(Path::new("strict/tree/0.gandr"), SourceText::from(first));
    std::fs::create_dir_all(root.join("a")).expect("an empty directory is created");
    scratch.file(Path::new("strict/tree/b.gandr"), SourceText::from(last));

    let mut read = Vec::new();
    let ControlFlow::Continue(report) = walk.visit::<Evaluator, _, _>(
        &Pool::new(Width::SERIAL),
        |step| -> ControlFlow<Infallible> {
            if let Step::Source {
                path, text, base, ..
            } = step
            {
                read.push((
                    path.strip_prefix(&root)
                        .expect("inside the tree")
                        .to_path_buf(),
                    <&str>::from(text)
                        .get(usize::from(base) ..)
                        .unwrap_or_default()
                        .to_owned(),
                ));
            }
            ControlFlow::Continue(())
        },
    );
    assert_eq!(
        read,
        [
            (PathBuf::from("0.gandr"), first.to_owned()),
            (PathBuf::from("b.gandr"), last.to_owned())
        ],
        "the tree written after the walk was built is read when it is visited"
    );
    assert_eq!(usize::from(report.sources().read()), 2);
    assert_eq!(usize::from(report.sources().faulted()), 0);
    assert_eq!(usize::from(report.lowerings()), 2);

    let removed = root
        .parent()
        .expect("the strict directory")
        .parent()
        .expect("the fixture root")
        .to_path_buf();
    drop(scratch);
    assert!(removed.try_exists().is_ok_and(|exists| !exists));
}

#[cfg(unix)]
#[test]
fn an_explicit_link_uses_its_target_root_and_keeps_its_path()
{
    let scratch = Scratch::new(Path::new("explicit-link"));
    let source = SourceText::from("def greeting = \"λ\" ;\r\n");
    scratch.file(Path::new("fixture/pending/target.gandr"), source);
    let target = scratch.0.join("fixture/pending/target.gandr");
    std::fs::create_dir_all(scratch.0.join("strict")).expect("the alias directory is created");
    let alias = scratch.0.join("strict/alias.gandr");
    std::os::unix::fs::symlink(&target, &alias).expect("the explicit link is created");
    assert_eq!(classify(&alias), SourceRoot::Strict);
    let mut read = Vec::new();
    let ControlFlow::Continue(_report) = Walk::new(vec![alias.clone()]).visit::<Evaluator, _, _>(
        &Pool::new(Width::SERIAL),
        |step| -> ControlFlow<Infallible> {
            if let Step::Source {
                path,
                root,
                text,
                base,
                standing,
                ..
            } = step
            {
                read.push((
                    path.to_path_buf(),
                    root,
                    standing,
                    <&str>::from(text)
                        .get(usize::from(base) ..)
                        .unwrap_or_default()
                        .to_owned(),
                ));
            }
            ControlFlow::Continue(())
        },
    );
    assert_eq!(
        read,
        [(
            alias,
            SourceRoot::Pending,
            Standing::Lowered,
            <&str>::from(source).to_owned()
        )],
        "an explicit symbolic link is read as its target, under its target's root"
    );
}

#[test]
fn an_importer_is_judged_over_its_sibling()
{
    let scratch = Scratch::new(Path::new("importers"));
    // The bytes of each declaration segment of a kernel artifact, in
    // admission order.
    let segments = |image: &[u8]| -> Vec<Vec<u8>> {
        let decoded = gandr_kernel_term::decode(image.into()).expect("the kernel's export decodes");
        decoded
            .segments()
            .declaration_segments()
            .map(|span| {
                image
                    .get(usize::from(span.start) .. usize::from(span.end))
                    .unwrap_or_default()
                    .to_vec()
            })
            .collect()
    };
    let base = include_str!("walk/fixtures/an-importer-is-judged-over-its-sibling-base.gandr");
    scratch.file(Path::new("fixture/base.gandr"), SourceText::from(base));
    for side in ["left", "right"] {
        scratch.file(
            Path::new(&format!("fixture/{side}.gandr")),
            SourceText::from(
                format!(
                    include_str!("walk/unformatted/an-importer-is-judged-over-its-sibling-1.gandr"),
                    side = side
                )
                .as_str(),
            ),
        );
    }
    // A diamond: the top reaches the base through both sides, and names
    // it too, since an import brings in its source's own declarations and
    // not what that source imports.
    scratch.file(
        Path::new("fixture/top.gandr"),
        SourceText::from(include_str!(
            "walk/fixtures/an-importer-is-judged-over-its-sibling-2.gandr"
        )),
    );
    // A source no import joins to the diamond: a component of its own.
    scratch.file(
        Path::new("fixture/apart.gandr"),
        SourceText::from(include_str!(
            "walk/fixtures/an-importer-is-judged-over-its-sibling-3.gandr"
        )),
    );
    for width in widths() {
        let mut judged = Vec::new();
        let ControlFlow::Continue(report) = Walk::new(vec![scratch.0.join("fixture")])
            .visit::<Evaluator, _, _>(&Pool::new(width), |step| -> ControlFlow<Infallible> {
                let Step::Source {
                    path,
                    text,
                    base: own,
                    composed:
                        gandr_surface_dispatcher::Composed::Settled {
                            ref report,
                            kernel: Maybe::Present(ref kernel),
                            ..
                        },
                    standing,
                    ..
                } = step
                else {
                    panic!("each source is judged and admitted: {step:?}");
                };
                let name = path
                    .file_stem()
                    .map(|stem| stem.to_string_lossy().into_owned());
                assert_eq!(standing, Standing::Settled, "{name:?} settles");
                let declared: Vec<String> = report
                    .declarations()
                    .iter()
                    .map(|declaration| declaration.name().to_string())
                    .collect();
                judged.push((
                    name.unwrap_or_default(),
                    (<&str>::from(text).to_owned(), own),
                    declared,
                    segments(kernel.as_ref()),
                ));
                ControlFlow::Continue(())
            });
        assert_eq!(
            usize::from(report.lowerings()),
            5_usize,
            "at {width:?}, each of the five sources is lowered once, the base \
                 among them, however many import it"
        );
        let find = |wanted: &str| {
            judged
                .iter()
                .find(|&&(ref name, ..)| name == wanted)
                .unwrap_or_else(|| panic!("{wanted} is walked"))
        };
        let &(_, (ref base_text, _), ref base_declared, ref base_segments) = find("base");
        assert_eq!(
            base_declared,
            &["Point", "here"],
            "the base reports its own declarations"
        );
        for side in ["left", "right", "top"] {
            let &(_, (ref text, own), ref declared, ref segments) = find(side);
            assert!(
                text.get(.. usize::from(own))
                    .is_some_and(|before| before.starts_with(base_text.as_str())),
                "{side} is judged after the base it imports"
            );
            assert_eq!(
                declared,
                &[side],
                "{side} reports its own declaration alone"
            );
            assert_eq!(
                segments, base_segments,
                "{side} carries the one certificate its component was admitted with"
            );
        }
        let &(_, (ref top, _), ..) = find("top");
        assert_eq!(
            top.matches("data Point").count(),
            1_usize,
            "a base reached by two paths is laid out once"
        );
        let &(_, (ref apart, own), ref declared, ref apart_segments) = find("apart");
        assert_eq!(
            (own, declared.as_slice()),
            (
                gandr_surface_lowering::prelude::base(),
                ["apart".to_owned()].as_slice()
            ),
            "a source joined to no other is laid after the prelude alone"
        );
        let (apart_own, prelude_segments) = apart_segments
            .split_last()
            .expect("the apart source's certificate holds its declaration");
        assert!(
            !prelude_segments.is_empty()
                && base_segments.starts_with(prelude_segments)
                && !base_segments.contains(apart_own),
            "a source joined to no other is judged after the prelude alone: its \
                 certificate is the prelude's segments, which the base's begins with, \
                 and its own"
        );
        assert!(!apart.contains("data Point"));
    }
}

/// Two fixtures importing a standard library module the walk is given
/// are judged apart, each after its own copy of the module, which is
/// also judged once on its own.
#[test]
fn importers_of_a_given_std_module_are_judged_apart_4856()
{
    let scratch = Scratch::new(Path::new("std-importers"));
    for side in ["left", "right"] {
        scratch.file(
                Path::new(&format!("fixture/{side}.gandr")),
                SourceText::from(
                    format!(
                        include_str!("walk/unformatted/importers-of-a-given-std-module-are-judged-apart-4856.gandr"), side = side
                    )
                    .as_str(),
                ),
            );
    }
    let module = std::fs::canonicalize(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../library/std/src/string.gandr"),
    )
    .expect("the standard library is checked out");
    let written = std::fs::read_to_string(&module).expect("the module reads");
    for width in widths() {
        let mut judged = Vec::new();
        let ControlFlow::Continue(report) =
            Walk::new(vec![scratch.0.join("fixture"), module.clone()]).visit::<Evaluator, _, _>(
                &Pool::new(width),
                |step| -> ControlFlow<Infallible> {
                    let Step::Source {
                        path,
                        text,
                        base: own,
                        standing,
                        ..
                    } = step
                    else {
                        panic!("each source is read: {step:?}");
                    };
                    let name = path
                        .file_stem()
                        .map(|stem| stem.to_string_lossy().into_owned())
                        .unwrap_or_default();
                    assert_eq!(standing, Standing::Settled, "{name} settles");
                    judged.push((name, <&str>::from(text).to_owned(), own));
                    ControlFlow::Continue(())
                },
            );
        assert_eq!(
            usize::from(report.lowerings()),
            usize::from(report.sources().read()).saturating_add(2_usize),
            "at {width:?}, each source is lowered once, and the module once more in each \
                 importer's component"
        );
        for (side, other) in [("left", "right"), ("right", "left")] {
            let &(_, ref text, own) = judged
                .iter()
                .find(|&&(ref name, ..)| name == side)
                .unwrap_or_else(|| panic!("{side} is walked"));
            let before = text.get(.. usize::from(own)).unwrap_or_default();
            assert!(
                before.contains(written.as_str()),
                "at {width:?}, {side} is judged after the module it imports"
            );
            assert!(
                !text.contains(&format!("def {other}")),
                "at {width:?}, {side} is judged apart from {other}"
            );
        }
    }
}

#[test]
fn each_source_of_a_component_settles_under_its_own_root_3100()
{
    let scratch = Scratch::new(Path::new("roots-3100"));
    // Under the strict root a `refuses` is itself the refusal; under the
    // fixture root it is read, and settles when the checker refuses.
    scratch.file(
        Path::new("strict/s.gandr"),
        SourceText::from(include_str!(
            "walk/fixtures/each-source-of-a-component-settles-under-its-own-root-3100-1.gandr"
        )),
    );
    let strict = scratch.0.join("strict/s.gandr");
    scratch.file(
            Path::new("fixture/f.gandr"),
            SourceText::from(
                format!(
                    include_str!("walk/unformatted/each-source-of-a-component-settles-under-its-own-root-3100-2.gandr"),
                    strict.display()
                )
                .as_str(),
            ),
        );
    let fixture = scratch.0.join("fixture/f.gandr");
    for given in [vec![fixture.clone(), strict.clone()], vec![
        strict.clone(),
        fixture.clone(),
    ]] {
        let mut standings = Vec::new();
        let ControlFlow::Continue(_report) = Walk::new(given.clone()).visit::<Evaluator, _, _>(
            &Pool::new(Width::SERIAL),
            |step| -> ControlFlow<Infallible> {
                if let Step::Source { path, standing, .. } = step {
                    standings.push((path.to_path_buf(), standing));
                }
                ControlFlow::Continue(())
            },
        );
        standings.sort();
        let mut expected = vec![
            (fixture.clone(), Standing::Settled),
            (strict.clone(), Standing::Unsettled),
        ];
        expected.sort();
        assert_eq!(
            standings, expected,
            "given {given:?}, the fixture's `refuses` settles and the strict source's is \
                 refused"
        );
    }
}

/// A source reads a module through the source it imports, though another
/// source of its component declares a module of the same name: `user`
/// imports `base`, `other` declares its own `Seat`, and `mid` joins the
/// three into one component by importing `base` beside `other`'s import.
#[test]
fn a_module_resolves_through_the_importer_s_own_import()
{
    let scratch = Scratch::new(Path::new("rival-module"));
    let files = [
        (
            "fixture/base.gandr",
            include_str!(
                "walk/fixtures/a-module-resolves-through-the-importer-s-own-import-files.gandr"
            ),
        ),
        ("fixture/shared.gandr", "def shared : Integer = 0;\n"),
        (
            "fixture/mid.gandr",
            include_str!(
                "walk/fixtures/a-module-resolves-through-the-importer-s-own-import-1.gandr"
            ),
        ),
        (
            "fixture/other.gandr",
            include_str!(
                "walk/fixtures/a-module-resolves-through-the-importer-s-own-import-2.gandr"
            ),
        ),
        (
            "fixture/user.gandr",
            include_str!(
                "walk/fixtures/a-module-resolves-through-the-importer-s-own-import-3.gandr"
            ),
        ),
    ];
    for (relative, text) in files {
        scratch.file(Path::new(relative), SourceText::from(text));
    }
    let mut standings = Vec::new();
    let ControlFlow::Continue(_report) = Walk::new(vec![scratch.0.join("fixture")])
        .visit::<Evaluator, _, _>(
            &Pool::new(Width::SERIAL),
            |step| -> ControlFlow<Infallible> {
                if let Step::Source { path, standing, .. } = step {
                    standings.push((path.file_name().map(std::ffi::OsStr::to_owned), standing));
                }
                ControlFlow::Continue(())
            },
        );
    assert!(
        standings
            .iter()
            .all(|&(_, standing)| standing == Standing::Settled),
        "each source settles, `user`'s `Seat` the one `base` declares: {standings:?}"
    );
}

/// #617: an import made its importer dearer to judge by a second parse of
/// the importer — once alone to read its imports, again inside its
/// component — which cost 23 M of a 7 KB importer's 152 M instructions
/// while every later phase stayed within 1 %. Two rows: a source of that
/// size with a one-declaration sibling's text laid in front of it, and the
/// same source importing that sibling. The importing walk parses within
/// 2 % of the flat one's bytes; read whole, it parsed twice as many.
#[test]
fn an_import_parses_its_importer_once_617()
{
    let scratch = Scratch::new(Path::new("parsed-once"));
    let floor = include_str!("walk/fixtures/an-import-parses-its-importer-once-617-floor.gandr");
    let body = (0_usize .. 150_usize).fold(String::new(), |mut body, n| {
        let _written = write!(
            body,
            "\n@[ checks ]\ndef n{n} : Integer ;\ndef n{n} = {n} ;\n"
        );
        body
    });
    scratch.file(
        Path::new("fixture/flat/flat.gandr"),
        SourceText::from(
            format!(
                include_str!("walk/unformatted/an-import-parses-its-importer-once-617-1.gandr"),
                body = body,
                floor = floor
            )
            .as_str(),
        ),
    );
    scratch.file(
        Path::new("fixture/import/floor.gandr"),
        SourceText::from(floor),
    );
    scratch.file(
        Path::new("fixture/import/importer.gandr"),
        SourceText::from(
            format!(
                include_str!("walk/unformatted/an-import-parses-its-importer-once-617-2.gandr"),
                body = body
            )
            .as_str(),
        ),
    );
    let parsed = |directory: &str| {
        let ControlFlow::Continue(report) =
            Walk::new(vec![scratch.0.join("fixture").join(directory)]).visit::<Evaluator, _, _>(
                &Pool::new(Width::SERIAL),
                |_| -> ControlFlow<Infallible> { ControlFlow::Continue(()) },
            );
        usize::from(report.parsed())
    };
    let (flat, importing) = (parsed("flat"), parsed("import"));
    assert!(
        flat > 7000_usize,
        "the source is the size of the issue's: {flat} bytes"
    );
    assert!(
        importing.saturating_mul(100) <= flat.saturating_mul(102),
        "the importing walk parses {importing} bytes against the flat walk's {flat}"
    );
}

/// #2331: every component lays the prelude first, and a walk that parsed
/// and lowered it again for each one paid the prelude per component —
/// with `Ord` in it, 2.5 ms of each component's time. Two rows: one source,
/// and eight such sources apart. The seven more cost their own bytes, read
/// at most once more to group them, and never the prelude again; every one
/// settles, each lowered once.
#[test]
fn a_walk_parses_the_prelude_once_for_every_component_2331()
{
    let scratch = Scratch::new(Path::new("prelude-once"));
    let source = |n: usize| format!("@[ checks ]\ndef n{n} : Integer ;\ndef n{n} = {n} ;\n");
    scratch.file(
        Path::new("fixture/one/s0.gandr"),
        SourceText::from(source(0).as_str()),
    );
    for n in 0_usize .. 8_usize {
        scratch.file(
            Path::new(&format!("fixture/eight/s{n}.gandr")),
            SourceText::from(source(n).as_str()),
        );
    }
    let own = source(7).len();
    let prelude = usize::from(gandr_surface_lowering::prelude::base());
    assert!(
        prelude > own.saturating_mul(2),
        "the prelude, {prelude} bytes, outweighs a source read twice"
    );
    for width in widths() {
        let (one_seen, one) = visited(&scratch.0, vec![scratch.0.join("fixture/one")], width);
        let (eight_seen, eight) = visited(&scratch.0, vec![scratch.0.join("fixture/eight")], width);
        assert!(
            one_seen
                .iter()
                .chain(&eight_seen)
                .all(|row| row.1 == Seen::Source(Standing::Settled)),
            "at {width:?}, every source settles: {one_seen:?} {eight_seen:?}"
        );
        assert_eq!(
            (usize::from(one.lowerings()), usize::from(eight.lowerings())),
            (1_usize, 8_usize),
            "at {width:?}, each source is lowered once"
        );
        let more = usize::from(eight.parsed()).saturating_sub(usize::from(one.parsed()));
        assert!(
            more <= own.saturating_mul(2).saturating_mul(7),
            "at {width:?}, seven more components parse {more} bytes: their own, never \
                 the {prelude}-byte prelude again"
        );
    }
}

/// #1027: a source the lowering refuses as a whole is refused alone. The
/// source it imports and a sibling importing that source too settle as
/// they do alone, and a source importing the refused one refuses its
/// import, at every width.
#[test]
fn a_source_refused_whole_refuses_only_itself_and_its_importers_1027()
{
    let scratch = Scratch::new(Path::new("refused-whole"));
    let sources = [
        (
            "base",
            include_str!(
                "walk/unformatted/a-source-refused-whole-refuses-only-itself-and-its-importers-1027-sources.gandr"
            ),
        ),
        // A source that declares nothing, an attribute block decorating
        // nothing after its import, is refused as a whole.
        (
            "bad",
            include_str!(
                "walk/unformatted/a-source-refused-whole-refuses-only-itself-and-its-importers-1027-1.gandr"
            ),
        ),
        (
            "sibling",
            include_str!(
                "walk/unformatted/a-source-refused-whole-refuses-only-itself-and-its-importers-1027-2.gandr"
            ),
        ),
        (
            "top",
            include_str!(
                "walk/unformatted/a-source-refused-whole-refuses-only-itself-and-its-importers-1027-3.gandr"
            ),
        ),
    ];
    for (name, text) in sources {
        scratch.file(
            Path::new(&format!("fixture/{name}.gandr")),
            SourceText::from(text),
        );
    }
    for width in widths() {
        let mut standings = Vec::new();
        let ControlFlow::Continue(_report) = Walk::new(vec![scratch.0.join("fixture")])
            .visit::<Evaluator, _, _>(&Pool::new(width), |step| -> ControlFlow<Infallible> {
                if let Step::Source { path, standing, .. } = step {
                    standings.push((
                        path.file_stem()
                            .map(|stem| stem.to_string_lossy().into_owned())
                            .unwrap_or_default(),
                        standing,
                    ));
                }
                ControlFlow::Continue(())
            });
        standings.sort_by(|left, right| left.0.cmp(&right.0));
        assert_eq!(
            standings,
            [
                (String::from("bad"), Standing::Refused),
                (String::from("base"), Standing::Settled),
                (String::from("sibling"), Standing::Settled),
                (String::from("top"), Standing::Settled),
            ],
            "at {width:?}, only the refused source is refused whole, and its \
                 importer refuses its import"
        );
    }
}

/// A component of two sources refused whole within one of them is parted
/// too: the base the refused source imports settles as it does alone.
#[test]
fn a_pair_refused_whole_in_its_importer_settles_its_base()
{
    let scratch = Scratch::new(Path::new("refused-pair"));
    scratch.file(
        Path::new("fixture/base.gandr"),
        SourceText::from(include_str!(
            "walk/unformatted/a-pair-refused-whole-in-its-importer-settles-its-base.gandr"
        )),
    );
    scratch.file(
            Path::new("fixture/bad.gandr"),
            SourceText::from(include_str!("walk/unformatted/a-source-refused-whole-refuses-only-itself-and-its-importers-1027-1.gandr")),
        );
    for width in core::iter::once(Width::SERIAL).chain(widths()) {
        let (seen, _report) = visited(&scratch.0, vec![scratch.0.join("fixture")], width);
        assert_eq!(
            seen,
            rows(&[
                (
                    Path::new("fixture/bad.gandr"),
                    Seen::Source(Standing::Refused)
                ),
                (
                    Path::new("fixture/base.gandr"),
                    Seen::Source(Standing::Settled)
                ),
            ]),
            "at {width:?}, only the source refused whole is refused"
        );
    }
}

/// Two sources of one component refused whole are each set apart, one a
/// round: the lowering of the whole names the first, a part of more than
/// one source the second, and the base and sibling they import settle. A
/// lowering counts each source it lowers, so the walk lowers 13: the four
/// sources whole, the three left once the first is apart, the two left
/// once the second is, and each of the four again as regrouped. A part of
/// one source is never lowered to find a refusal.
#[test]
fn two_sources_refused_whole_are_each_set_apart()
{
    let scratch = Scratch::new(Path::new("refused-twice"));
    let checks = include_str!(
        "walk/unformatted/a-source-refused-whole-refuses-only-itself-and-its-importers-1027-sources.gandr"
    );
    let bad = include_str!(
        "walk/unformatted/a-source-refused-whole-refuses-only-itself-and-its-importers-1027-1.gandr"
    );
    for (name, text) in [
        ("base", checks),
        ("bad1", bad),
        ("bad2", bad),
        (
            "sibling",
            include_str!(
                "walk/unformatted/a-source-refused-whole-refuses-only-itself-and-its-importers-1027-2.gandr"
            ),
        ),
    ] {
        scratch.file(
            Path::new(&format!("fixture/{name}.gandr")),
            SourceText::from(text),
        );
    }
    for width in core::iter::once(Width::SERIAL).chain(widths()) {
        let (seen, report) = visited(&scratch.0, vec![scratch.0.join("fixture")], width);
        assert_eq!(
            seen,
            rows(&[
                (
                    Path::new("fixture/bad1.gandr"),
                    Seen::Source(Standing::Refused)
                ),
                (
                    Path::new("fixture/bad2.gandr"),
                    Seen::Source(Standing::Refused)
                ),
                (
                    Path::new("fixture/base.gandr"),
                    Seen::Source(Standing::Settled)
                ),
                (
                    Path::new("fixture/sibling.gandr"),
                    Seen::Source(Standing::Settled)
                ),
            ]),
            "at {width:?}, only the two sources refused whole are refused"
        );
        assert_eq!(
            usize::from(report.lowerings()),
            13_usize,
            "at {width:?}, the whole, each round's parts of more than one source, then \
                 each regrouped source"
        );
    }
}

/// #617: a walk reads an importer's imports from its import forms and
/// confirms them on its component's parse. An import inside a module is
/// read from the forms but written by no root: the component's parse does
/// not confirm it, and the walk lays the sources out again as each one's
/// own parse reads it — the nested source after the prelude alone, judged
/// over its own bytes.
#[test]
fn an_import_its_parse_does_not_read_is_grouped_again()
{
    let scratch = Scratch::new(Path::new("regrouped"));
    let base = include_str!(
        "walk/unformatted/a-pair-refused-whole-in-its-importer-settles-its-base.gandr"
    );
    let nested = include_str!(
        "walk/fixtures/an-import-its-parse-does-not-read-is-grouped-again-nested.gandr"
    );
    scratch.file(Path::new("fixture/base.gandr"), SourceText::from(base));
    scratch.file(Path::new("fixture/nested.gandr"), SourceText::from(nested));
    for width in widths() {
        let mut walked = Vec::new();
        let ControlFlow::Continue(report) = Walk::new(vec![scratch.0.join("fixture")])
            .visit::<Evaluator, _, _>(&Pool::new(width), |step| -> ControlFlow<Infallible> {
                let Step::Source {
                    path, text, base, ..
                } = step
                else {
                    panic!("each source is judged: {step:?}");
                };
                walked.push((
                    path.file_name()
                        .map(|name| name.to_string_lossy().into_owned())
                        .unwrap_or_default(),
                    <&str>::from(text)
                        .get(usize::from(base) ..)
                        .unwrap_or_default()
                        .to_owned(),
                    base,
                ));
                ControlFlow::Continue(())
            });
        let after = gandr_surface_lowering::prelude::base();
        assert_eq!(
            walked,
            [
                (String::from("base.gandr"), String::from(base), after),
                (String::from("nested.gandr"), String::from(nested), after),
            ],
            "at {width:?}, each source is judged over its own bytes after the prelude alone"
        );
        assert_eq!(
            usize::from(report.lowerings()),
            2_usize,
            "at {width:?}, each source is lowered once, in the grouping its own \
                 parse reads"
        );
    }
}

/// #596: two members of one component that write one attributed form
/// byte for byte — their documentation apart, which no key reads — each
/// settle under their own expectation. Keyed by content alone, the two
/// forms shared a key, each declaration read both `checks`, and both
/// stated no verdict.
#[test]
fn one_form_in_two_members_keeps_its_own_expectation_596()
{
    let scratch = Scratch::new(Path::new("one-form-two-members"));
    scratch.file(
        Path::new("fixture/base.gandr"),
        SourceText::from(include_str!(
            "walk/fixtures/one-form-in-two-members-keeps-its-own-expectation-596-1.gandr"
        )),
    );
    for (side, documentation) in [("left", "The left two."), ("right", "The right two.")] {
        scratch.file(
                Path::new(&format!("fixture/{side}.gandr")),
                SourceText::from(
                    format!(
                        include_str!("walk/unformatted/one-form-in-two-members-keeps-its-own-expectation-596-2.gandr"), documentation = documentation
                    )
                    .as_str(),
                ),
            );
    }
    for width in widths() {
        let mut judged = Vec::new();
        let ControlFlow::Continue(report) = Walk::new(vec![scratch.0.join("fixture")])
            .visit::<Evaluator, _, _>(&Pool::new(width), |step| -> ControlFlow<Infallible> {
                let Step::Source {
                    path,
                    composed: gandr_surface_dispatcher::Composed::Settled { ref report, .. },
                    standing,
                    ..
                } = step
                else {
                    panic!("each source is judged: {step:?}");
                };
                let name = path
                    .file_stem()
                    .map(|stem| stem.to_string_lossy().into_owned())
                    .unwrap_or_default();
                let settlements: Vec<(String, gandr_surface_corpus::Settlement)> = report
                    .declarations()
                    .iter()
                    .map(|declaration| (declaration.name().to_string(), declaration.settlement()))
                    .collect();
                judged.push((name, standing, settlements));
                ControlFlow::Continue(())
            });
        judged.sort();
        let settled =
            |name: &str| vec![(name.to_owned(), gandr_surface_corpus::Settlement::Settled)];
        assert_eq!(
            judged,
            [
                ("base".to_owned(), Standing::Settled, settled("One")),
                ("left".to_owned(), Standing::Settled, settled("Two")),
                ("right".to_owned(), Standing::Settled, settled("Two")),
            ],
            "at {width:?}, each member's `Two` settles under its own `checks`"
        );
        assert_eq!(usize::from(report.lowerings()), 3_usize);
    }
}
