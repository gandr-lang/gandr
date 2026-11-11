//! The corpus's two roots, run through the walk, read from the runner's
//! report.
//!
//! Nothing here pins a count: a gate over an unpopulated root would pass
//! vacuously, so each root is asserted non-empty and every row of the
//! fragment's exercised table carried, and adding a source changes a count
//! without reddening anything.
//!
//! The corpus cases, in a `cfg(test)` module so the crate's lint wall reads
//! them as test code rather than as shipping code.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use core::convert::Infallible;
use core::num::NonZeroUsize;
use core::ops::ControlFlow;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use gandr_core_sequent::FocusRefusal;
use gandr_kernel_check_memo::MemoActivity;
use gandr_surface_corpus::CorpusRoot;
use gandr_surface_corpus::Outcome;
use gandr_surface_corpus::RunSpelling;
use gandr_surface_corpus::Seal;
use gandr_surface_corpus::Settlement;
use gandr_surface_corpus::Stated;
use gandr_surface_dispatcher::Composed;
use gandr_surface_dispatcher::Descent;
use gandr_surface_dispatcher::Goals;
use gandr_surface_dispatcher::HostGrant;
use gandr_surface_dispatcher::Lowered;
use gandr_surface_dispatcher::LoweringCount;
use gandr_surface_dispatcher::Pool;
use gandr_surface_dispatcher::Row;
use gandr_surface_dispatcher::RunReport;
use gandr_surface_dispatcher::RunVerdict;
use gandr_surface_dispatcher::SourceRoot;
use gandr_surface_dispatcher::Step;
use gandr_surface_dispatcher::Threads;
use gandr_surface_dispatcher::Verb;
use gandr_surface_dispatcher::Walk;
use gandr_surface_dispatcher::Width;
use gandr_surface_dispatcher::descent;
use gandr_surface_dispatcher::judge_module;
use gandr_surface_dispatcher::lower_source;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::built_in;
use gandr_surface_lowering::ENTRY;
use gandr_surface_lowering::Role;
use gandr_surface_syntax::SourceText;
use gandr_theory_cellular_sheaves::Integer;
use gandr_theory_cellular_sheaves::Rational;
use gandr_theory_probability::Distribution;
use gandr_theory_probability::Independence;
use quenchant_shape::shape::Maybe;

use crate::digest;

/// The corpus's strict root, under the corpus crate.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the absolute path of the strict root.
/// - fails: never; this only constructs the path, without reading it.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the strict root is the one the gate runs.
/// - witness: `tests::corpus::the_strict_root_checks_owing_nothing`
#[spec(ensures: |ref ret| ret.is_absolute() && ret.ends_with("strict"))]
fn strict_root() -> PathBuf
{
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../surface-corpus/strict")
}

/// The corpus's fixture root, at the repository's top.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the absolute path of the fixture root.
/// - fails: never; this only constructs the path, without reading it.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the fixture root is the one the gate runs.
/// - witness: `tests::corpus::the_fixture_root_settles_every_fixture`
#[spec(ensures: |ref ret| ret.is_absolute() && ret.ends_with("corpus"))]
fn fixture_root() -> PathBuf
{
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../corpus")
}

/// The standard library, at its package root, which the gate checks beside
/// the strict root and the corpus's fixtures import (#2767, #3711, #4529).
///
/// # Specification
/// - requires: nothing.
/// - ensures: the absolute path of the standard library's package, under
///   `library`.
/// - fails: never; this only constructs the path, without reading it.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the library is the one the gate runs.
/// - witness: `tests::corpus::the_std_root_adds_one_lowering_per_module`
#[spec(ensures: |ref ret| ret.is_absolute()
        && ret.parent().is_some_and(|library| library.ends_with("library")))]
fn std_root() -> PathBuf
{
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../library/std")
}

/// The report of a visit over `path`, every step a source.
///
/// # Specification
/// - requires: `path` names a finite corpus walk with no source or engine
///   fault; fixtures may still be unsettled or pending.
/// - ensures: the visit's report has no faulted paths and records at least one
///   lowering per source read, preserving unsettled results for callers.
/// - fails: does not convert a fault into an empty or settled report.
/// - panics: if a step faults.
///
/// # Adequacy
/// - hypothesis: L3 — both real corpus roots have exact verdict, ledger,
///   settlement and row expectations; the shared source sweep checks the
///   lowering/read relation rather than pinning a corpus size.
/// - witness: `tests::corpus::the_strict_root_checks_owing_nothing`
/// - witness: `tests::corpus::the_fixture_root_settles_every_fixture`
/// - witness: `tests::corpus::the_std_root_adds_one_lowering_per_module`
#[spec(ensures: |ref ret| usize::from(ret.sources().faulted()) == 0_usize
        && usize::from(ret.lowerings()) >= usize::from(ret.sources().read()))]
fn run(paths: Vec<PathBuf>) -> RunReport
{
    let ControlFlow::Continue(report) = Walk::new(paths).visit(
        &Pool::new(Width::SERIAL),
        |step| -> ControlFlow<Infallible> {
            if let Step::Fault { path, fault } = step {
                panic!("{}: {fault}", path.display());
            }
            ControlFlow::Continue(())
        },
    );
    report
}

/// What a corpus test reads of a walk's report, kept in a digest so the
/// tests of one nextest run share the walk (#5256).
#[derive(serde::Deserialize, serde::Serialize)]
struct Counted
{
    /// The report as the runner prints it.
    shown: String,
    /// Whether `check` settles under the gated goals.
    checked: bool,
    /// Whether `test` settles.
    tested: bool,
    /// The declarations settled.
    settled: usize,
    /// The declarations unsettled.
    unsettled: usize,
    /// The ledger's entries.
    ledger: usize,
    /// Whether the tally is sealed.
    sealed: bool,
    /// The sources read.
    read: usize,
    /// The sources read under the strict root.
    strict: usize,
    /// The sources read as pending.
    pending: usize,
    /// The fixtures settled.
    fixtures: usize,
    /// The lowerings performed.
    lowerings: usize,
    /// Each row's count, in [`Row::ALL`] order.
    rows: [usize; 12],
}

impl Counted
{
    /// What the corpus tests read of `report`.
    ///
    /// # Specification
    /// trivial.
    fn of(report: &RunReport) -> Self
    {
        let tally = report.tally();
        Self {
            shown: report.to_string(),
            checked: report.verdict(Verb::Check(Goals::Gated)) == RunVerdict::Settled,
            tested: report.verdict(Verb::Test) == RunVerdict::Settled,
            settled: usize::from(tally.declarations().settled()),
            unsettled: usize::from(tally.declarations().unsettled()),
            ledger: usize::from(tally.ledger()),
            sealed: tally.seal() == Seal::Sealed,
            read: usize::from(report.sources().read()),
            strict: usize::from(report.sources().strict()),
            pending: usize::from(report.sources().pending()),
            fixtures: usize::from(tally.fixtures().settled()),
            lowerings: usize::from(report.lowerings()),
            rows: Row::ALL.map(|row| usize::from(report.exercised().count(row))),
        }
    }

    /// The count of `row`.
    ///
    /// # Specification
    /// trivial.
    fn count(
        &self,
        row: Row,
    ) -> gandr_surface_lowering::DeclarationCount
    {
        gandr_surface_lowering::DeclarationCount::from(
            Row::ALL
                .iter()
                .position(|&candidate| candidate == row)
                .and_then(|at| self.rows.get(at).copied())
                .unwrap_or_default(),
        )
    }
}

/// The report of the walk over `paths`, as [`run`] gives it, shared under
/// `name` by the tests of one nextest run.
///
/// # Specification
/// trivial.
fn counted(
    name: &Path,
    paths: Vec<PathBuf>,
) -> Counted
{
    digest::shared(name, || Counted::of(&run(paths)))
}

#[test]
fn the_strict_root_checks_owing_nothing()
{
    let report = counted(Path::new("strict"), vec![strict_root()]);
    assert!(
        report.checked,
        "check settles the strict root:\n{}",
        report.shown
    );
    assert!(
        report.settled > 0_usize,
        "the strict root holds declarations"
    );
    assert_eq!(report.unsettled, 0_usize, "{}", report.shown);
    assert_eq!(report.ledger, 0_usize, "the ledger is empty");
    assert!(report.sealed, "the strict root is sealed");
    assert_eq!(
        report.read, report.strict,
        "every source sits under the strict root"
    );
    for row in [
        Row::LambdaChecks,
        Row::ReturnChecks,
        Row::ForceSynthesises,
        Row::ApplicationSynthesises,
        Row::SubsumptionBridge,
    ] {
        assert!(
            usize::from(report.count(row)) > 0_usize,
            "the strict root exercises {row}"
        );
    }
}

#[test]
fn the_fixture_root_settles_every_fixture()
{
    let report = counted(Path::new("fixture-std"), vec![fixture_root(), std_root()]);
    assert!(
        report.tested,
        "test settles the fixture root:\n{}",
        report.shown
    );
    assert!(report.fixtures > 0_usize, "the fixture root holds fixtures");
    assert!(
        report.pending > 0_usize,
        "the fixture root holds its pending set"
    );
    for row in [
        Row::UndefinedTermName,
        Row::UndefinedTypeHead,
        Row::ShapeRefusal,
        Row::NonSynthesisableHead,
        Row::NonSynthesisableDefinition,
        Row::ReservedForm,
        Row::AddressableObligation,
    ] {
        assert!(
            usize::from(report.count(row)) > 0_usize,
            "the fixture root exercises {row}"
        );
    }
}

#[test]
fn the_two_roots_exercise_every_row()
{
    let strict = counted(Path::new("strict"), vec![strict_root()]);
    let fixture = counted(Path::new("fixture-std"), vec![fixture_root(), std_root()]);
    let missing = Row::ALL
        .into_iter()
        .filter(|&row| {
            usize::from(strict.count(row)).saturating_add(usize::from(fixture.count(row)))
                == 0_usize
        })
        .collect::<Vec<_>>();
    assert_eq!(missing, Vec::new(), "every row is carried");
}

/// The `std` root given beside the corpus's two roots adds one lowering per
/// module it holds: each module is lowered once for itself, and each importer
/// lowers the modules it reaches, whichever roots the walk is given.
#[test]
fn the_std_root_adds_one_lowering_per_module()
{
    let corpus = corpus();
    assert_eq!(
        corpus.faults,
        Vec::<String>::new(),
        "the corpus walks with no fault"
    );
    let without = corpus.counted;
    let library = run(vec![std_root()]);
    let with = run(vec![strict_root(), fixture_root(), std_root()]);
    assert_eq!(
        usize::from(library.lowerings()),
        usize::from(library.sources().read()),
        "the library alone lowers each of its modules once"
    );
    assert_eq!(
        usize::from(with.sources().read()),
        without
            .read
            .saturating_add(usize::from(library.sources().read())),
        "the library's modules are read beside the corpus's sources"
    );
    assert_eq!(
        usize::from(with.lowerings()),
        without
            .lowerings
            .saturating_add(usize::from(library.lowerings())),
        "each module adds its own lowering, and no importer joins another through it"
    );
}

/// The identity subject's base source is lowered once, in the one
/// component every source importing it is judged in, and `std.list`, which
/// the walk reaches and is not given, once in each component that imports it.
#[test]
fn the_identity_base_is_lowered_once_for_its_importers()
{
    let subject = fixture_root().join("model/identity");
    let base = subject.join("circle-base.gandr");
    let mut certificates = Vec::new();
    let mut list_importers = 0_usize;
    let ControlFlow::Continue(report) = Walk::new(vec![subject]).visit(
        &Pool::new(Width::SERIAL),
        |step| -> ControlFlow<Infallible> {
            let Step::Source {
                path,
                text,
                base: own,
                composed:
                    Composed::Settled {
                        kernel: Maybe::Present(ref kernel),
                        ..
                    },
                ..
            } = step
            else {
                panic!("each identity source is judged and admitted: {step:?}");
            };
            let written = <&str>::from(text)
                .get(usize::from(own) ..)
                .unwrap_or_default();
            let imports_base = written.contains("import \"./circle-base.gandr\"");
            if written.contains("import std.list") {
                list_importers = list_importers.saturating_add(1);
            }
            if path == base || imports_base {
                certificates.push((path.to_path_buf(), kernel.as_ref().to_vec()));
            }
            ControlFlow::Continue(())
        },
    );
    assert_eq!(
        usize::from(report.lowerings()),
        usize::from(report.sources().read()).saturating_add(list_importers),
        "each source of the subject is lowered once, the base among them, and `std.list` once in \
         each component that imports it: once per importer, none of which imports another"
    );
    let Some((first, rest)) = certificates.split_first()
    else {
        panic!("the base is walked");
    };
    assert!(
        !rest.is_empty(),
        "the subject holds a source importing its base"
    );
    for &(ref path, ref certificate) in rest {
        assert!(
            certificate == &first.1,
            "{} carries the certificate its base's component was admitted with",
            path.display()
        );
    }
}

/// #595: the identity subject is spelled once per component — its base
/// and every source importing it once between them — not once per source
/// the component is projected onto.
#[test]
fn the_identity_base_is_spelled_once_for_its_importers_595()
{
    let subject = fixture_root().join("model/identity");
    let mut components = BTreeSet::new();
    let ControlFlow::Continue(report) = Walk::new(vec![subject]).visit(
        &Pool::new(Width::SERIAL),
        |step| -> ControlFlow<Infallible> {
            let Step::Source {
                composed:
                    Composed::Settled {
                        kernel: Maybe::Present(ref kernel),
                        ..
                    },
                ..
            } = step
            else {
                panic!("each identity source is judged and admitted: {step:?}");
            };
            // A component's sources share its one certificate.
            let _new = components.insert(kernel.as_ref().to_vec());
            ControlFlow::Continue(())
        },
    );
    assert!(
        components.len() < usize::from(report.sources().read()),
        "the subject holds a component of more than one source"
    );
    assert_eq!(
        usize::from(report.spellings()),
        components.len(),
        "one spelling pass per component"
    );
}

/// Every non-directory `.gandr` entry under one of `roots`, with directory
/// links followed and each canonical directory listed once.
///
/// # Specification
/// - requires: a finite, quiescent directory graph whose directories resolve
///   and list successfully.
/// - ensures: selected entries retain their paths under one of `roots` and
///   exact `.gandr` extension; a directory with that extension is traversed
///   rather than returned, and the sketch set, registered by its location as no
///   gate's source, is not. Revisited directory identities do not create a
///   cycle.
/// - fails: does not silently omit a directory that fails to resolve or list.
/// - panics: on a directory-resolution, listing or entry-read failure.
///
/// # Adequacy
/// - hypothesis: L3 — planted sources distinguish registered roots, outside
///   roots, nested source-suffixed directories and, on Unix, a directory link
///   the production walk skips. Cyclic links and special files are not
///   separately generated.
/// - witness: `tests::corpus::a_planted_orphan_is_not_registered`
/// - witness: `tests::corpus::every_corpus_source_is_registered`
#[spec(ensures: |ref ret| ret.iter().all(|path| roots.iter().any(|root| path.starts_with(root))
        && path.extension().is_some_and(|extension| extension == "gandr")))]
fn sources_under(roots: &[PathBuf]) -> BTreeSet<PathBuf>
{
    let mut found = BTreeSet::new();
    let mut listed = BTreeSet::new();
    let mut directories = roots.to_vec();
    while let Some(directory) = directories.pop() {
        let canonical = directory.canonicalize().expect("the directory resolves");
        if !listed.insert(canonical) {
            continue;
        }
        for entry in std::fs::read_dir(&directory).expect("the directory lists") {
            let path = entry.expect("the entry reads").path();
            if path.is_dir() {
                if descent(&path) == Descent::Walked {
                    directories.push(path);
                }
            }
            else if path
                .extension()
                .is_some_and(|extension| extension == "gandr")
            {
                found.insert(path);
            }
        }
    }
    found
}

/// The `.gandr` files under one of `roots` that a walk did not reach, given
/// as `reached`: every path the walk's steps name.
///
/// # Specification
/// - requires: `roots` meet the stable, readable directory-graph premise of
///   `sources_under`.
/// - ensures: the independently listed source entries not in `reached`, in
///   strictly increasing path order. A fault at a source still establishes that
///   the walk reached that path.
/// - fails: directory-inventory errors are not mistaken for registration.
/// - panics: when the independent directory inventory cannot be read.
///
/// # Adequacy
/// - hypothesis: L3 — an exact planted orphan set separates root membership
///   from reachability through links, while the real corpus has no orphan.
///   Transient filesystem failures are outside the quiescent domain.
/// - witness: `tests::corpus::a_planted_orphan_is_not_registered`
/// - witness: `tests::corpus::every_corpus_source_is_registered`
#[spec(ensures: |ref ret| ret.iter().all(|path| roots.iter().any(|root| path.starts_with(root))
        && path.extension().is_some_and(|extension| extension == "gandr"))
        && ret.windows(2_usize).all(|pair| match *pair {
            [ref first, ref second] => first < second,
            _ => false,
        }))]
fn unreached(
    roots: &[PathBuf],
    reached: &BTreeSet<PathBuf>,
) -> Vec<PathBuf>
{
    sources_under(roots)
        .into_iter()
        .filter(|source| !reached.contains(source))
        .collect()
}

#[test]
fn every_corpus_source_is_registered()
{
    let roots = vec![strict_root(), fixture_root()];
    assert!(
        !sources_under(&roots).is_empty(),
        "the corpus holds sources"
    );
    let reached = corpus()
        .reached
        .into_iter()
        .map(PathBuf::from)
        .collect::<BTreeSet<_>>();
    assert_eq!(
        unreached(&roots, &reached),
        Vec::<PathBuf>::new(),
        "every source sits where the walk reaches it"
    );
}

#[test]
fn a_planted_orphan_is_not_registered()
{
    let scratch =
        std::env::temp_dir().join(format!("gandr-dispatcher-orphans-{}", std::process::id()));
    if scratch.exists() {
        std::fs::remove_dir_all(&scratch).expect("a stale scratch directory is removed");
    }
    let corpus = scratch.join("corpus");
    let mut planted = Vec::new();
    for (relative, orphan) in [
        ("strict/answer.gandr", false),
        ("strict/tree.gandr/inside.gandr", false),
        ("fixture/model/unit.gandr", false),
        ("fixture/pending/later.gandr", false),
        ("fixture/sketch/cells/fused.gandr", false),
        ("examples/orphan.gandr", true),
        ("examples/tree.gandr/inner.gandr", true),
        ("orphan.gandr", true),
    ] {
        let path = corpus.join(relative);
        std::fs::create_dir_all(path.parent().expect("a file has a parent"))
            .expect("the directories are created");
        std::fs::write(&path, "def answer = 42 ;\n").expect("the source is written");
        if orphan {
            planted.push(path);
        }
    }
    #[cfg(unix)]
    {
        let shelf = scratch.join("shelf");
        std::fs::create_dir_all(&shelf).expect("the shelf is created");
        std::fs::write(shelf.join("stray.gandr"), "def stray = 1 ;\n")
            .expect("the shelved source is written");
        std::os::unix::fs::symlink(&shelf, corpus.join("strict/shelved"))
            .expect("the directory is linked");
        planted.push(corpus.join("strict/shelved/stray.gandr"));
    }
    planted.sort();
    let mut reached = BTreeSet::new();
    let ControlFlow::Continue(_report) =
        Walk::new(vec![corpus.join("strict"), corpus.join("fixture")]).visit(
            &Pool::new(Width::SERIAL),
            |step| -> ControlFlow<Infallible> {
                match step {
                    Step::Source { path, .. } | Step::Fault { path, .. } => {
                        reached.insert(path.to_path_buf());
                    },
                }
                ControlFlow::Continue(())
            },
        );
    let found = unreached(core::slice::from_ref(&corpus), &reached);
    std::fs::remove_dir_all(&scratch).expect("the scratch directory is removed");
    assert_eq!(
        found, planted,
        "each source outside the roots, or behind a link the walk does not follow, is an orphan"
    );
}

/// What the corpus tests read of the one walk over the strict and fixture
/// roots, shared by the tests of one nextest run (#5256).
#[derive(serde::Deserialize, serde::Serialize)]
struct Corpus
{
    /// The walk's report.
    counted: Counted,
    /// Each fault, as `<path>: <fault>`.
    faults: Vec<String>,
    /// Every path a step names, a source's or a fault's.
    reached: Vec<String>,
    /// The model sources: those under neither root's `pathological`
    /// directory.
    model: Swept,
    /// The sources under a root's `pathological` directory.
    pathological: Swept,
}

/// What the tests read of one half of the corpus: each source under a root
/// other than the pending one whose composition settles.
#[derive(Default, serde::Deserialize, serde::Serialize)]
struct Swept
{
    /// Each such source's path.
    composed: Vec<String>,
    /// Each accepted declaration that did not focus for a reason other than
    /// a code, element identity or a hole, described.
    refusals: Vec<String>,
    /// Each declaration that states a run outcome, and whether it settled.
    /// Each row begins with the source's location in this workspace, then
    /// names the declaration, the stated outcome and the observed one.
    runs: Vec<(String, bool)>,
}

/// The one walk over the strict and fixture roots that the corpus tests
/// read, shared by the tests of one nextest run.
///
/// # Specification
/// - requires: the committed corpus remains quiescent during the walk.
/// - ensures: every path a step names is reached; each source under a root
///   other than the pending one whose composition settles is recorded in its
///   half, with its focusing refusals other than a code, element identity or a
///   hole, and each run outcome a declaration states with its settlement.
///   Pending sources, whole-source refusals and faults record no half; a fault
///   is recorded with its path.
/// - fails: never converts a fault or an unsettled run into a settled one.
/// - panics: when the digest cannot be written or read.
/// - executable: none — a later test reads the walk from a file that another
///   process wrote, which no predicate over the value reads.
///
/// # Adequacy
/// - hypothesis: L3 — both real halves compose sources, state run outcomes that
///   settle and focus but for codes, element identity and holes; the
///   registration test reads the reached set beside an independent listing.
/// - witness: `tests::corpus::l_machine_matches_the_outcome_snapshots_on_the_model_corpus`
/// - witness: `tests::corpus::l_machine_matches_the_outcome_snapshots_on_the_pathological_corpus`
/// - witness: `tests::corpus::focusing_is_total_on_the_model_corpus`
/// - witness: `tests::corpus::focusing_is_total_on_the_pathological_corpus`
/// - witness: `tests::corpus::every_corpus_source_is_registered`
fn corpus() -> Corpus
{
    digest::shared(Path::new("strict-fixture"), || {
        let mut faults = Vec::new();
        let mut reached = Vec::new();
        let mut model = Swept::default();
        let mut pathological = Swept::default();
        let ControlFlow::Continue(report) = Walk::new(vec![strict_root(), fixture_root()]).visit(
            &Pool::new(Width::SERIAL),
            |step| -> ControlFlow<Infallible> {
                let (path, root, composed) = match step {
                    Step::Fault { path, fault } => {
                        reached.push(path.display().to_string());
                        faults.push(format!("{}: {fault}", path.display()));
                        return ControlFlow::Continue(());
                    },
                    Step::Source {
                        path,
                        root,
                        ref composed,
                        ..
                    } => (path, root, composed),
                };
                reached.push(path.display().to_string());
                let Composed::Settled {
                    ref program,
                    ref report,
                    ..
                } = *composed
                else {
                    return ControlFlow::Continue(());
                };
                if root == SourceRoot::Pending {
                    return ControlFlow::Continue(());
                }
                let swept = if path
                    .components()
                    .any(|component| component.as_os_str() == "pathological")
                {
                    &mut pathological
                }
                else {
                    &mut model
                };
                swept.composed.push(path.display().to_string());
                swept.refusals.extend(
                    program
                        .focus_refusals()
                        .filter(|&(_, refusal)| {
                            !matches!(
                                refusal,
                                FocusRefusal::Code(_)
                                    | FocusRefusal::ElementPath(_)
                                    | FocusRefusal::ElementTransport(..)
                                    | FocusRefusal::IncompleteValue(_)
                                    | FocusRefusal::IncompleteComputation(_)
                            )
                        })
                        .map(|(name, refusal)| format!("{}: `{name}`: {refusal}", path.display())),
                );
                for declaration in report.declarations() {
                    if let Stated::Verdict(
                        Outcome::Runs(ref spelled) | Outcome::RunsTracing(ref spelled, _),
                    ) = *declaration.stated()
                    {
                        swept.runs.push((
                            format!(
                                "{}: `{}` states runs to {spelled}, {}",
                                path.display(),
                                declaration.name(),
                                declaration.outcome(),
                            ),
                            declaration.settlement() == Settlement::Settled,
                        ));
                    }
                }
                ControlFlow::Continue(())
            },
        );
        Corpus {
            counted: Counted::of(&report),
            faults,
            reached,
            model,
            pathological,
        }
    })
}

/// The model corpus runs to the outcome each source states.
#[test]
fn l_machine_matches_the_outcome_snapshots_on_the_model_corpus()
{
    let runs = corpus().model.runs;
    assert!(!runs.is_empty(), "the model corpus states run outcomes");
    for (run, settled) in runs {
        assert!(settled, "{run}");
    }
}

/// The pathological corpus runs to the outcome each source states.
#[test]
fn l_machine_matches_the_outcome_snapshots_on_the_pathological_corpus()
{
    let runs = corpus().pathological.runs;
    assert!(
        !runs.is_empty(),
        "the pathological corpus states run outcomes"
    );
    for (run, settled) in runs {
        assert!(settled, "{run}");
    }
}

/// Every accepted declaration of the model corpus focuses, but for a code,
/// element identity or a hole, which the machine carries no image of.
#[test]
fn focusing_is_total_on_the_model_corpus()
{
    let Swept {
        composed, refusals, ..
    } = corpus().model;
    assert!(!composed.is_empty(), "the model corpus composes");
    assert_eq!(
        refusals,
        Vec::<String>::new(),
        "focusing refuses only codes, element identity and holes"
    );
}

/// Every accepted declaration of the pathological corpus focuses, but for
/// a code, element identity or a hole.
#[test]
fn focusing_is_total_on_the_pathological_corpus()
{
    let Swept {
        composed, refusals, ..
    } = corpus().pathological;
    assert!(!composed.is_empty(), "the pathological corpus composes");
    assert_eq!(
        refusals,
        Vec::<String>::new(),
        "focusing refuses only codes, element identity, holes, session actions and world forms"
    );
}

/// The names a source exports, lowered on its own text: each top-level
/// declaration's name and each top-level module's, as the source spells
/// them. A constructor belongs to its type and an operation to its family,
/// so neither is counted; a module member is reached through its module's
/// name; a name the lowering mints for a form — the `Theory` code type a
/// signature block declares — is spelled by no source, so it is not
/// counted. Each program declares its entry under [`ENTRY`], so the entry
/// belongs to its program and is not counted.
///
/// # Specification
/// trivial.
fn exported(
    grammar: &Pbg,
    own: SourceText<'_>,
    lowerings: &mut LoweringCount,
) -> BTreeSet<String>
{
    let lowering = lower_source(grammar, own, lowerings)
        .unwrap_or_else(|fault| panic!("a model source lowers: {fault}"));
    let Lowered::Module { ref module, .. } = lowering.into_lowered()
    else {
        return BTreeSet::new();
    };
    module
        .declarations()
        .iter()
        .filter(|declaration| declaration.role() == Role::Declared)
        .filter_map(|declaration| {
            let name = module.path_of(declaration).first()?.to_string();
            let span = declaration.span();
            let form = own
                .as_ref()
                .get(usize::from(span.start()) .. usize::from(span.end()))?;
            form.split(|character: char| !(character.is_alphanumeric() || character == '_'))
                .any(|word| word == name)
                .then_some(name)
        })
        .filter(|name| name != ENTRY)
        .collect()
}

/// No name is exported by two sources of one model subject — the
/// directory directly under `model` that holds them. A lemma two sources
/// need is written in the one that owns it and imported by the other, so
/// a second declaration of a name a sibling exports is refused here by
/// name (#436). A program's entry `main` is not a lemma: `gandr run` enters
/// each source at its own `main`, and no sibling imports it, so it is not
/// counted.
#[test]
fn no_subject_declares_a_name_twice()
{
    let grammar = built_in().expect("the built-in grammar builds");
    let mut lowerings = LoweringCount::default();
    let model = fixture_root().join("model");
    let mut declared: BTreeMap<(PathBuf, String), BTreeSet<PathBuf>> = BTreeMap::new();
    let ControlFlow::Continue(_report) = Walk::new(vec![model.clone()]).visit(
        &Pool::new(Width::SERIAL),
        |step| -> ControlFlow<Infallible> {
            let Step::Source {
                path, text, base, ..
            } = step
            else {
                panic!("each model source is read: {step:?}");
            };
            let relative = path.strip_prefix(&model).expect("under the model root");
            let mut parts = relative.components();
            let (Some(subject), Some(_)) = (parts.next(), parts.next())
            else {
                return ControlFlow::Continue(());
            };
            let own = <&str>::from(text)
                .get(usize::from(base) ..)
                .expect("a source's own text follows its base");
            let named = exported(&grammar, SourceText::from(own), &mut lowerings);
            for name in named.into_iter().filter(|name| name != "main") {
                declared
                    .entry((PathBuf::from(subject.as_os_str()), name))
                    .or_default()
                    .insert(relative.to_path_buf());
            }
            ControlFlow::Continue(())
        },
    );
    assert!(!declared.is_empty(), "the model corpus declares names");
    let twice: Vec<String> = declared
        .iter()
        .filter(|&(_, sources)| sources.len() > 1)
        .map(|(&(ref subject, ref name), sources)| {
            let mut message = format!("{}: `{name}` is declared by ", subject.display());
            for (index, source) in sources.iter().enumerate() {
                if index > 0 {
                    message.push_str(" and ");
                }
                core::fmt::Write::write_fmt(&mut message, format_args!("{}", source.display()))
                    .expect("a string accepts every write");
            }
            message
        })
        .collect();
    assert_eq!(
        twice,
        Vec::<String>::new(),
        "each name a subject exports is declared once, in the source that owns it"
    );
}

/// #2520: a `reads` claim settles against the footprint the content table
/// carries for its declaration, the items named in any order: a data type's
/// fields, a case reading its scrutinee's type through its constructors, a
/// call reading its callee in a value position, and a body reading nothing.
/// A claim naming other items is unsettled, the carried footprint produced.
#[test]
fn a_reads_claim_settles_against_the_carried_footprint_2520()
{
    let text = include_str!(
        "corpus/fixtures/a-reads-claim-settles-against-the-carried-footprint-2520.gandr"
    );
    let grammar = built_in().expect("the built-in grammar builds");
    let mut lowerings = LoweringCount::default();
    let Lowered::Module { module, arena } =
        lower_source(&grammar, SourceText::from(text), &mut lowerings)
            .expect("the source lowers")
            .into_lowered()
    else {
        panic!("the module is read");
    };
    let Composed::Settled { report, .. } = judge_module(
        CorpusRoot::Fixture,
        (module, SourceText::from(text)),
        arena,
        &HostGrant::UNBOUNDED,
    )
    .expect("the source composes")
    else {
        panic!("the source settles");
    };
    let read = |spelled: &str| Outcome::Reads(RunSpelling::from(String::from(spelled)));
    let claims: Vec<(String, Outcome, Settlement)> = report
        .declarations()
        .iter()
        .filter(|declaration| matches!(declaration.stated(), &Stated::Verdict(Outcome::Reads(_))))
        .map(|declaration| {
            (
                declaration.name().to_string(),
                declaration.outcome(),
                declaration.settlement(),
            )
        })
        .collect();
    assert_eq!(
        claims,
        vec![
            (
                String::from("Either"),
                read("*{Flag, Nat}"),
                Settlement::Settled
            ),
            (
                String::from("side"),
                read("*{Either, Nat}"),
                Settlement::Settled
            ),
            (
                String::from("marked"),
                read("*{side, Nat, Flag, Either}"),
                Settlement::Settled
            ),
            (String::from("answer"), read("()"), Settlement::Settled),
            (String::from("short"), read("Nat"), Settlement::Unsettled),
        ],
        "each claim settles against the footprint its declaration carries"
    );
}

/// The `distributes` claims of the declarations `text` holds, each with the
/// distribution its runs produce and its settlement. The source is walked
/// from a fixture root under a scratch directory that `tag` names, since a
/// source that imports `std.rand` is walked from one.
///
/// # Specification
/// trivial.
fn distribution_claims(
    tag: &Path,
    text: SourceText<'_>,
) -> Vec<(String, Outcome, Settlement)>
{
    let scratch = std::env::temp_dir().join(format!(
        "gandr-dispatcher-{}-{}",
        tag.display(),
        std::process::id()
    ));
    if scratch.exists() {
        std::fs::remove_dir_all(&scratch).expect("a stale scratch directory is removed");
    }
    let fixture = scratch.join("corpus/fixture");
    let source = fixture.join("model/distributes.gandr");
    std::fs::create_dir_all(source.parent().expect("a file has a parent"))
        .expect("the directories are created");
    std::fs::write(&source, <&str>::from(text)).expect("the source is written");
    let mut claims: Vec<(String, Outcome, Settlement)> = Vec::new();
    let ControlFlow::Continue(_report) = Walk::new(vec![fixture]).visit(
        &Pool::new(Width::SERIAL),
        |step| -> ControlFlow<Infallible> {
            let Step::Source {
                composed: Composed::Settled { ref report, .. },
                ..
            } = step
            else {
                panic!("the source settles: {step:?}");
            };
            claims.extend(
                report
                    .declarations()
                    .iter()
                    .filter(|declaration| {
                        matches!(
                            declaration.stated(),
                            &Stated::Verdict(Outcome::Distributes(_))
                        )
                    })
                    .map(|declaration| {
                        (
                            declaration.name().to_string(),
                            declaration.outcome(),
                            declaration.settlement(),
                        )
                    }),
            );
            ControlFlow::Continue(())
        },
    );
    std::fs::remove_dir_all(&scratch).expect("the scratch directory is removed");
    claims
}

/// #5710: a `distributes` claim settles against the runs of its declaration,
/// one for each sequence of answers to its draws, each path of weight `2^-n`
/// for its `n` bits. Two draws of one bit settle their exact weights; the same
/// runs stated with other weights are unsettled, the runs' distribution
/// produced; and a draw of 17 bits passes the quota of 16, refused by name.
#[test]
fn a_distribution_settles_over_every_answer_of_its_draws_5710()
{
    let claims = distribution_claims(
        Path::new("distributes"),
        SourceText::from(include_str!(
            "corpus/fixtures/a-distribution-settles-over-every-answer-of-its-draws-5710.gandr"
        )),
    );
    let distributed =
        |spelled: &str| Outcome::Distributes(RunSpelling::from(String::from(spelled)));
    let runs = r#""1/4 0", "1/2 1", "1/4 2""#;
    assert_eq!(
        claims,
        vec![
            (String::from("pair"), distributed(runs), Settlement::Settled),
            (
                String::from("coin"),
                distributed(runs),
                Settlement::Unsettled
            ),
            (
                String::from("wide"),
                distributed("PastQuota: a path draws 17 bits, past the quota of 16"),
                Settlement::Unsettled
            ),
        ],
        "each claim settles against the distribution of its runs"
    );
}

/// #5712: a draw that the exact model declines gives no distribution. The
/// corpus refuses it by name, with what performs the draw: the run itself,
/// the task a fork starts, or the world a `migrate` runs its body at.
#[test]
fn a_declined_draw_names_its_task_or_world_5712()
{
    let claims = distribution_claims(
        Path::new("declined"),
        SourceText::from(include_str!(
            "corpus/fixtures/a-declined-draw-names-its-task-or-world-5712.gandr"
        )),
    );
    let unanswered = |performer: &str, width: u32| {
        Outcome::Distributes(RunSpelling::from(format!(
            "Unanswered: the exact model answers no draw of {performer}: a width of {width} \
             bits lies outside 1 to 64"
        )))
    };
    assert_eq!(
        claims,
        vec![
            (
                String::from("rooted"),
                unanswered("the run", 0),
                Settlement::Unsettled
            ),
            (
                String::from("forked"),
                unanswered("the task `seat`", 99),
                Settlement::Unsettled
            ),
            (
                String::from("migrated"),
                unanswered("the world `far`", 99),
                Settlement::Unsettled
            ),
        ],
        "each declined draw is refused with what performs it"
    );
}

/// #5713: a width enters the randomness of std at a draw. `std.rand.lcg`
/// sends each draw it cannot answer to the model outside it, so the exact
/// model refuses a width outside 1 to 64 by name: a draw under the generator,
/// the width of the generator, a key and a multiplier. A draw wider than the
/// generator but within 64 bits gets the answers of the exact model.
#[test]
fn a_width_outside_one_to_sixty_four_is_refused_by_name_5713()
{
    let claims = distribution_claims(
        Path::new("widths"),
        SourceText::from(include_str!(
            "corpus/fixtures/a-width-outside-one-to-sixty-four-is-refused-by-name-5713.gandr"
        )),
    );
    let refused = |name: &str, width: u32| {
        (
            String::from(name),
            Outcome::Distributes(RunSpelling::from(format!(
                "Unanswered: the exact model answers no draw of the run: a width of {width} bits \
                 lies outside 1 to 64"
            ))),
            Settlement::Unsettled,
        )
    };
    assert_eq!(
        claims,
        vec![
            refused("empty", 0),
            refused("wide", 65),
            refused("wideGenerator", 70),
            refused("wideKey", 65),
            refused("emptyMultiplier", 0),
            (
                String::from("passedOn"),
                Outcome::Distributes(RunSpelling::from(String::from(
                    r#""1/4 0", "1/4 1", "1/4 2", "1/4 3""#
                ))),
                Settlement::Settled
            ),
        ],
        "each width outside 1 to 64 is refused with the width the draw names"
    );
}

/// One component of a pair that a run spells, such as the message or the
/// ciphertext of the one-time pad.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Component(i64);

/// The distribution over pairs of integers that `outcome` spells: each quoted
/// text a weight `p/q`, a space and a pair `*{a, b}`.
///
/// # Specification
/// trivial.
fn pairs(outcome: &Outcome) -> Distribution<(Component, Component)>
{
    let Outcome::Distributes(ref spelled) = *outcome
    else {
        panic!("the runs give a distribution: {outcome:?}");
    };
    let integer = |digits: &str| Integer::from(digits.parse::<i128>().expect("an integer"));
    let points = spelled
        .as_ref()
        .trim_matches('"')
        .split(r#"", ""#)
        .map(|point| {
            let (weight, pair) = point
                .split_once(' ')
                .expect("a point writes a weight and an outcome");
            let (numerator, denominator) = weight.split_once('/').expect("a weight is a fraction");
            let (first, second) = pair
                .strip_prefix("*{")
                .and_then(|inner| inner.strip_suffix('}'))
                .and_then(|inner| inner.split_once(", "))
                .expect("an outcome is a pair");
            (
                (
                    Component(first.parse::<i64>().expect("an integer")),
                    Component(second.parse::<i64>().expect("an integer")),
                ),
                Rational::new(integer(numerator), integer(denominator)).expect("a weight"),
            )
        });
    Distribution::new(points).expect("the weights sum to one")
}

/// #5713: under a fresh key, the ciphertext of the one-time pad is
/// independent of its message, which is perfect secrecy. A key used twice
/// reveals the message. The exemplar's runs give each joint, and
/// `independent` decides it: the pair `*{1, 0}` of the reused key weighs one
/// half, and its marginals one quarter.
#[test]
fn the_pad_s_ciphertext_is_independent_of_its_message_5713()
{
    let claims = distribution_claims(
        Path::new("pad"),
        SourceText::from(include_str!(
            "../../../corpus/model/probability/one-time-pad.gandr"
        )),
    );
    let joint = |name: &str| {
        let &(_, ref outcome, ref settlement) = claims
            .iter()
            .find(|&&(ref declared, ..)| declared == name)
            .unwrap_or_else(|| panic!("the exemplar declares `{name}`"));
        assert_eq!(*settlement, Settlement::Settled, "`{name}` settles");
        pairs(outcome)
    };
    let fraction = |numerator: i128, denominator: i128| {
        Rational::new(Integer::from(numerator), Integer::from(denominator)).expect("a weight")
    };
    assert_eq!(
        joint("joint").independent(),
        Ok(Independence::Independent),
        "a fresh key hides the message"
    );
    assert_eq!(
        joint("reused").independent(),
        Ok(Independence::Dependent {
            at: (Component(1), Component(0)),
            joint: fraction(1, 2),
            product: fraction(1, 4),
        }),
        "a key used twice reveals the message"
    );
}

/// The corpus sweeps: a wider visit over corpus sources hands over, step by
/// step, exactly what the serial visit over them yields, and answers the
/// serial visit's report; and a judgement's type table answers as the table
/// typed alone.
mod sweeps
{
    use gandr_workflow_sweep::Nights;
    use gandr_workflow_sweep::Portion;
    use gandr_workflow_sweep::Rotation;
    use gandr_workflow_sweep::Sample;
    use gandr_workflow_sweep::SampleName;
    use gandr_workflow_sweep::SampleSize;
    use gandr_workflow_sweep::Sweep;

    use super::*;

    /// The sample: sixty-four sources, ranked by their BLAKE3 digest under
    /// this name, at least one of each corpus class — `strict` and each
    /// directory below `fixture` — and, in the companion, every source the
    /// change adds or modifies beside them (`gandr-workflow-sweep`), each
    /// walked as its own path. The nightly profile walks the night's slice
    /// the same way, and the `sweeps` profile walks the two roots whole.
    const SAMPLE: Sample = Sample {
        name: SampleName("every_width_composes_the_corpus_alike"),
        size: SampleSize(64),
    };

    /// The nights the nightly profile takes to walk every source at every
    /// width: a seventh a night, the count the nightly's sweeps share
    /// (#3013). The two roots walked whole for 56 s on the nightly runner
    /// (run 40602657172).
    const NIGHTS: Nights = Nights(7);

    #[test]
    fn every_width_composes_the_corpus_alike()
    {
        composes_alike(&Sweep::asked().expect("the run's sweep resolves"));
    }

    /// The change's sources beside the fixed set (#4654).
    #[test]
    fn every_width_composes_the_corpus_alike_changed()
    {
        composes_alike(&Sweep::asked().expect("the run's sweep resolves").changed());
    }

    /// Every width composes the sources `sweep` visits as the serial visit
    /// does.
    ///
    /// # Specification
    /// trivial.
    fn composes_alike(sweep: &Sweep)
    {
        let paths: Vec<PathBuf> = match (sweep.portion(), sweep.coverage(), sweep.rotation()) {
            (Portion::Fixed, gandr_workflow_sweep::Coverage::Full, Rotation::Whole) => {
                vec![strict_root(), fixture_root()]
            },
            (Portion::Fixed, gandr_workflow_sweep::Coverage::Full, Rotation::Night(_))
            | (Portion::Fixed, gandr_workflow_sweep::Coverage::Sampled, _)
            | (Portion::Changed, ..) => {
                eprintln!("{}", sweep.rotation());
                let visited = sweep.visit_rotating(
                    SAMPLE,
                    NIGHTS,
                    &gandr_workflow_sweep::corpus::sources().expect("the corpus reads"),
                );
                assert!(
                    visited.len() >= sweep.drawn(SAMPLE).0,
                    "the sample is drawn: {}",
                    visited.len()
                );
                visited.into_iter().map(|source| source.path).collect()
            },
        };
        if paths.is_empty() {
            return;
        }
        let serial = digests(&paths, Width::SERIAL);
        for width in [
            Width::Threads(Threads::from(NonZeroUsize::MIN.saturating_add(1))),
            Width::Threads(Threads::from(NonZeroUsize::MIN.saturating_add(6))),
            Width::PerformanceCores,
        ] {
            assert!(
                digests(&paths, width) == serial,
                "the visit at {width:?} hands over the serial visit's steps, each composed \
                     alike, and counts its report"
            );
        }
    }

    /// The table parity's sample: two hundred and fifty-six sources, ranked
    /// by their BLAKE3 digest under this name, at least one of each corpus
    /// class, and, in the companion, every source the change adds or modifies
    /// beside them (`gandr-workflow-sweep`); more than half of them lower
    /// to a module and are compared. The `sweeps` and nightly profiles
    /// visit the two roots whole.
    const TABLED: Sample = Sample {
        name: SampleName("a_judgement_s_table_answers_as_the_table_typed_alone_1521"),
        size: SampleSize(256),
    };

    /// #1521: every corpus source, judged keeping its type table, answers
    /// every entry, every declaration, every declaration's refusal and every
    /// declared name as its table typed alone does, so a document's table can
    /// come from the judgement that checks it. Held to the 30 s bound by its
    /// sample (#2037).
    #[test]
    fn a_judgement_s_table_answers_as_the_table_typed_alone_1521()
    {
        tables_alike(&Sweep::asked().expect("the run's sweep resolves"));
    }

    /// The change's sources beside the fixed set (#4654).
    #[test]
    fn a_judgement_s_table_answers_as_the_table_typed_alone_1521_changed()
    {
        tables_alike(&Sweep::asked().expect("the run's sweep resolves").changed());
    }

    /// Every source `sweep` visits, judged keeping its type table, answers as
    /// its table typed alone.
    ///
    /// # Specification
    /// trivial.
    fn tables_alike(sweep: &Sweep)
    {
        use gandr_surface_dispatcher::Checking;
        use gandr_surface_dispatcher::HostGrant;
        use gandr_surface_dispatcher::TypeTable;
        use gandr_surface_dispatcher::judge_member_tabled;
        use gandr_surface_lowering::Unit;
        use gandr_surface_pretty::Form;
        use gandr_surface_pretty::PageWidth;
        use gandr_surface_syntax::ByteOffset;

        let (paths, least) = match (sweep.portion(), sweep.coverage()) {
            (Portion::Fixed, gandr_workflow_sweep::Coverage::Full) => (
                sources_under(&[strict_root(), fixture_root()]),
                Some(100_usize),
            ),
            (Portion::Fixed, gandr_workflow_sweep::Coverage::Sampled) | (Portion::Changed, _) => {
                let visited = sweep.visit(
                    TABLED,
                    &gandr_workflow_sweep::corpus::sources().expect("the corpus reads"),
                );
                assert!(
                    visited.len() >= sweep.drawn(TABLED).0,
                    "the sample is drawn: {}",
                    visited.len()
                );
                (
                    visited.into_iter().map(|source| source.path).collect(),
                    (sweep.portion() == Portion::Fixed).then_some(128_usize),
                )
            },
        };
        let grammar = built_in().expect("the built-in grammar builds");
        let page = PageWidth::from(80_u32);
        let style = Form::Explicit.into();
        let answers = |table: &TypeTable| {
            let declarations = table.declarations(page, style).collect::<Vec<_>>();
            let refusals = declarations
                .iter()
                .map(|&(key, _)| {
                    table
                        .refusal(key)
                        .map(|refusal| String::from(<&str>::from(refusal)))
                })
                .collect::<Vec<_>>();
            (
                table.entries(page, style).collect::<Vec<_>>(),
                declarations,
                refusals,
                table.declared_names().to_vec(),
            )
        };
        let mut tabled = 0_usize;
        let mut differing = Vec::new();
        for path in paths {
            let own = std::fs::read_to_string(&path).expect("a corpus source reads");
            let text = SourceText::from(own.as_str());
            let Ok(alone) = TypeTable::of(&grammar, text)
            else {
                continue;
            };
            let Ok(Lowered::Module { module, arena }) =
                lower_source(&grammar, text, &mut LoweringCount::default())
                    .map(gandr_surface_dispatcher::Lowering::into_lowered)
            else {
                continue;
            };
            let (_judged, table) = judge_member_tabled(
                gandr_surface_corpus::CorpusRoot::Fixture,
                (module, text),
                arena,
                (&HostGrant::UNBOUNDED, Checking::Whole),
                (&Unit::single(), ByteOffset::from(0_usize)),
            );
            let Maybe::Present(table) = table
            else {
                panic!("{} is judged keeping its table", path.display());
            };
            tabled = tabled.saturating_add(1);
            if answers(&table) != answers(&alone) {
                differing.push(path);
            }
        }
        assert!(
            least.is_none_or(|least| tabled > least) && differing.is_empty(),
            "over {tabled} sources, a judgement's table answers as the table typed alone; \
             differing: {differing:?}"
        );
    }

    /// The concurrent schedule's sample: sixty-four sources, ranked by their
    /// BLAKE3 digest under this name, at least one of each corpus class, and,
    /// in the companion, every source the change adds or modifies beside them
    /// (`gandr-workflow-sweep`). The `sweeps` and nightly profiles visit
    /// the two roots whole.
    const SCHEDULED: Sample = Sample {
        name: SampleName("the_concurrent_schedule_settles_the_corpus_alike_2954"),
        size: SampleSize(64),
    };

    /// #2954: every corpus source composed on the concurrent schedule, at
    /// four threads, settles each declaration as its sequential composition
    /// settles it. Each `runs` item then spells its run as the sequential
    /// schedule spells it, though its independent writers ran as jobs of the
    /// pool.
    #[test]
    fn the_concurrent_schedule_settles_the_corpus_alike_2954()
    {
        schedules_alike(&Sweep::asked().expect("the run's sweep resolves"));
    }

    /// The change's sources beside the fixed set (#4654).
    #[test]
    fn the_concurrent_schedule_settles_the_corpus_alike_2954_changed()
    {
        schedules_alike(&Sweep::asked().expect("the run's sweep resolves").changed());
    }

    /// Every source `sweep` visits settles on the concurrent schedule as on
    /// the sequential one.
    ///
    /// # Specification
    /// trivial.
    fn schedules_alike(sweep: &Sweep)
    {
        use gandr_surface_dispatcher::Scheduling;
        use gandr_surface_dispatcher::compose_on;

        let (paths, least) = match (sweep.portion(), sweep.coverage()) {
            (Portion::Fixed, gandr_workflow_sweep::Coverage::Full) => (
                sources_under(&[strict_root(), fixture_root()]),
                Some(100_usize),
            ),
            (Portion::Fixed, gandr_workflow_sweep::Coverage::Sampled) | (Portion::Changed, _) => {
                let visited = sweep.visit(
                    SCHEDULED,
                    &gandr_workflow_sweep::corpus::sources().expect("the corpus reads"),
                );
                assert!(
                    visited.len() >= sweep.drawn(SCHEDULED).0,
                    "the sample is drawn: {}",
                    visited.len()
                );
                (
                    visited.into_iter().map(|source| source.path).collect(),
                    (sweep.portion() == Portion::Fixed).then_some(32_usize),
                )
            },
        };
        let grammar = built_in().expect("the built-in grammar builds");
        let pool = Pool::new(Width::Threads(Threads::from(
            NonZeroUsize::MIN.saturating_add(3),
        )));
        let settled = |text: SourceText<'_>, scheduling| match compose_on(
            &grammar,
            CorpusRoot::Fixture,
            text,
            &mut LoweringCount::default(),
            scheduling,
            MemoActivity::Active,
        ) {
            Ok(Composed::Settled { report, .. }) => Some(
                report
                    .declarations()
                    .iter()
                    .map(|declaration| {
                        (
                            declaration.name().to_string(),
                            declaration.outcome(),
                            declaration.settlement(),
                        )
                    })
                    .collect::<Vec<_>>(),
            ),
            Ok(Composed::Refused(_)) | Err(_) => None,
        };
        let mut compared = 0_usize;
        let mut differing = Vec::new();
        for path in paths {
            let own = std::fs::read_to_string(&path).expect("a corpus source reads");
            let text = SourceText::from(own.as_str());
            let sequential = settled(text, Scheduling::Sequential);
            if sequential.is_some() {
                compared = compared.saturating_add(1);
            }
            if settled(text, Scheduling::Concurrent(&pool)) != sequential {
                differing.push(path);
            }
        }
        assert!(
            least.is_none_or(|least| compared > least) && differing.is_empty(),
            "over {compared} sources, the concurrent schedule settles as the sequential one; \
             differing: {differing:?}"
        );
    }

    /// The goal memo's sample: sixty-four sources, ranked by their BLAKE3
    /// digest under this name, at least one of each corpus class, and, in the
    /// companion, every source the change adds or modifies beside them
    /// (`gandr-workflow-sweep`). The `sweeps` and nightly profiles visit the
    /// two roots whole.
    const MEMOISED: Sample = Sample {
        name: SampleName("the_goal_memo_settles_the_corpus_alike_5719"),
        size: SampleSize(64),
    };

    /// #5719: every corpus source composed without the core checker's goal
    /// memo settles each declaration as its composition with the memo settles
    /// it. A memo answer is then the answer a fresh judgement gives. A
    /// declaration that spends its allowance without the memo gives no answer,
    /// and the memo may settle it: `model/records/iterated-pair.gandr` from
    /// `t18`.
    #[test]
    fn the_goal_memo_settles_the_corpus_alike_5719()
    {
        memoised_alike(&Sweep::asked().expect("the run's sweep resolves"));
    }

    /// The change's sources beside the fixed set (#4654).
    #[test]
    fn the_goal_memo_settles_the_corpus_alike_5719_changed()
    {
        memoised_alike(&Sweep::asked().expect("the run's sweep resolves").changed());
    }

    /// Every source `sweep` visits settles with the goal memo as without it,
    /// past each declaration that spends its allowance without the memo.
    ///
    /// # Specification
    /// trivial.
    fn memoised_alike(sweep: &Sweep)
    {
        use gandr_surface_dispatcher::Scheduling;
        use gandr_surface_dispatcher::compose_on;

        let (paths, least) = match (sweep.portion(), sweep.coverage()) {
            (Portion::Fixed, gandr_workflow_sweep::Coverage::Full) => (
                sources_under(&[strict_root(), fixture_root()]),
                Some(100_usize),
            ),
            (Portion::Fixed, gandr_workflow_sweep::Coverage::Sampled) | (Portion::Changed, _) => {
                let visited = sweep.visit(
                    MEMOISED,
                    &gandr_workflow_sweep::corpus::sources().expect("the corpus reads"),
                );
                assert!(
                    visited.len() >= sweep.drawn(MEMOISED).0,
                    "the sample is drawn: {}",
                    visited.len()
                );
                (
                    visited.into_iter().map(|source| source.path).collect(),
                    (sweep.portion() == Portion::Fixed).then_some(32_usize),
                )
            },
        };
        let grammar = built_in().expect("the built-in grammar builds");
        let settled = |text: SourceText<'_>, memo| match compose_on(
            &grammar,
            CorpusRoot::Fixture,
            text,
            &mut LoweringCount::default(),
            Scheduling::Sequential,
            memo,
        ) {
            Ok(Composed::Settled { report, .. }) => Some(
                report
                    .declarations()
                    .iter()
                    .map(|declaration| {
                        (
                            declaration.name().to_string(),
                            declaration.outcome(),
                            declaration.settlement(),
                        )
                    })
                    .collect::<Vec<_>>(),
            ),
            Ok(Composed::Refused(_)) | Err(_) => None,
        };
        let mut compared = 0_usize;
        let mut differing = Vec::new();
        for path in paths {
            let own = std::fs::read_to_string(&path).expect("a corpus source reads");
            let text = SourceText::from(own.as_str());
            let memoised = settled(text, MemoActivity::Active);
            let unmemoised = settled(text, MemoActivity::Inactive);
            if memoised.is_some() {
                compared = compared.saturating_add(1);
            }
            // A run that spends its allowance gives no answer, so a declaration
            // that only the memo brings within it has nothing to compare.
            let agree = match (memoised.as_ref(), unmemoised.as_ref()) {
                (Some(with), Some(without)) => {
                    with.len() == without.len()
                        && with.iter().zip(without).all(|(with, without)| {
                            with == without
                                || (with.0 == without.0
                                    && without.1
                                        == Outcome::Refuses(
                                            gandr_surface_corpus::RefusalName::BudgetExceeded,
                                        ))
                        })
                },
                (None, None) => true,
                (Some(_), None) | (None, Some(_)) => false,
            };
            if !agree {
                differing.push((path, memoised, unmemoised));
            }
        }
        assert!(
            least.is_none_or(|least| compared > least) && differing.is_empty(),
            "over {compared} sources, each declaration settles without the goal memo as it \
             settles with it; differing, with the memo and without it: {differing:#?}"
        );
    }

    /// The resume parity's sample: sixty-four sources, ranked by their BLAKE3
    /// digest under this name, at least one of each corpus class, and, in the
    /// companion, every source the change adds or modifies beside them
    /// (`gandr-workflow-sweep`). The nightly profile resumes the night's
    /// slice, and the `sweeps` profile every source.
    const RESUMED: Sample = Sample {
        name: SampleName("a_resume_onto_the_unchanged_program_gives_the_fresh_set_6549"),
        size: SampleSize(64),
    };

    /// The nights the nightly profile takes to resume every source: a seventh
    /// a night, the count the nightly's sweeps share (#3013). Every source,
    /// checked fresh and resumed once, took 32 s in one local debug run.
    const RESUMED_NIGHTS: Nights = Nights(7);

    /// #6549: every corpus source, checked fresh and then resumed onto its
    /// unchanged program, gives the fresh set: each item's typing, support
    /// and entered form. An adoption that seats the written form of a
    /// declaration its judgement entered elaborated changes the verdict or
    /// the support of an item that reads it.
    #[test]
    fn a_resume_onto_the_unchanged_program_gives_the_fresh_set_6549()
    {
        resumes_alike(&Sweep::asked().expect("the run's sweep resolves"));
    }

    /// The change's sources beside the fixed set (#4654).
    #[test]
    fn a_resume_onto_the_unchanged_program_gives_the_fresh_set_6549_changed()
    {
        resumes_alike(&Sweep::asked().expect("the run's sweep resolves").changed());
    }

    /// Every source `sweep` visits, laid out after its import closure, checked
    /// fresh and resumed onto its unchanged program, gives the fresh set.
    ///
    /// # Specification
    /// trivial.
    fn resumes_alike(sweep: &Sweep)
    {
        use gandr_core_checker::CheckBudget;
        use gandr_core_incremental::check_program;
        use gandr_core_incremental::resume_from;

        let grammar = built_in().expect("the built-in grammar builds");
        eprintln!("{}", sweep.rotation());
        let visited = sweep.visit_rotating(
            RESUMED,
            RESUMED_NIGHTS,
            &gandr_workflow_sweep::corpus::sources().expect("the corpus reads"),
        );
        assert!(
            visited.len() >= sweep.drawn(RESUMED).0,
            "the sample is drawn: {}",
            visited.len()
        );
        let program_of = |path: &Path| lowered_program(&grammar, path);
        let mut resumed = 0_usize;
        let mut differing = Vec::new();
        for source in visited {
            let (Some(mut checked), Some(mut again)) =
                (program_of(&source.path), program_of(&source.path))
            else {
                continue;
            };
            let fresh = check_program(&mut checked, CheckBudget::DEFAULT)
                .expect("a lowered program checks");
            let again = resume_from(fresh.checkpoints(), &mut again)
                .expect("a set resumes onto the program it was checked from");
            resumed = resumed.saturating_add(1);
            if again.checkpoints() != fresh.checkpoints() {
                differing.push(source.path);
            }
        }
        eprintln!("resumed {resumed} of the sources visited");
        assert!(
            differing.is_empty(),
            "over {resumed} sources, a resume onto the unchanged program gives the fresh set; \
             differing: {differing:?}"
        );
    }

    /// The item program the source at `path` lowers to, laid out after its
    /// import closure; none for a source that lowers to no module.
    ///
    /// # Specification
    /// trivial.
    fn lowered_program(
        grammar: &Pbg,
        path: &Path,
    ) -> Option<gandr_core_incremental::Program>
    {
        let own = std::fs::read_to_string(path).expect("a corpus source reads");
        lowered_text(grammar, path, SourceText::from(own.as_str()))
    }

    /// The item program that `own`, read as the source at `path`, lowers
    /// to, laid out after its import closure; none for a text that lowers to
    /// no module.
    ///
    /// # Specification
    /// trivial.
    fn lowered_text(
        grammar: &Pbg,
        path: &Path,
        own: SourceText<'_>,
    ) -> Option<gandr_core_incremental::Program>
    {
        use gandr_surface_dispatcher::Unshadowed;
        use gandr_surface_dispatcher::classify;
        use gandr_surface_dispatcher::item_program;
        use gandr_surface_dispatcher::lay_out_shadowed;
        use gandr_surface_dispatcher::lower_unit_source;

        let laid = lay_out_shadowed(grammar, path, classify(path), own, &Unshadowed);
        let lowering = lower_unit_source(
            grammar,
            SourceText::from(laid.text.as_str()),
            &laid.unit,
            &mut LoweringCount::default(),
        )
        .ok()?;
        let Lowered::Module { module, arena } = lowering.into_lowered()
        else {
            return None;
        };
        item_program(&module, arena).ok()
    }

    /// The item tables' sample: sixty-four sources, ranked by their BLAKE3
    /// digest under this name, at least one of each corpus class, and, in the
    /// companion, every source the change adds or modifies beside them
    /// (`gandr-workflow-sweep`). The nightly profile mints the night's slice,
    /// and the `sweeps` profile every source.
    const MINTED: Sample = Sample {
        name: SampleName("every_item_table_mints_back_to_itself"),
        size: SampleSize(64),
    };

    /// The nights the nightly profile takes to mint every source: a seventh
    /// a night, the count the nightly's sweeps share.
    const MINTED_NIGHTS: Nights = Nights(7);

    /// Each root of each item table a corpus source checks to, minted into a
    /// fresh arena and encoded again, gives the table under that root: the
    /// mint inverts the encoding of each former the corpus holds. The mint
    /// refuses a root by name only when its table holds a node that content
    /// keeps unresolved (a stage type, a codata application)
    /// or names a declaration the program holds no item for.
    #[test]
    fn every_item_table_mints_back_to_itself()
    {
        mints_alike(&Sweep::asked().expect("the run's sweep resolves"));
    }

    /// The change's sources beside the fixed set.
    #[test]
    fn every_item_table_mints_back_to_itself_changed()
    {
        mints_alike(&Sweep::asked().expect("the run's sweep resolves").changed());
    }

    /// Every source `sweep` visits, checked, has each root of each item table
    /// mint back to the table under it.
    ///
    /// # Specification
    /// trivial.
    fn mints_alike(sweep: &Sweep)
    {
        use gandr_core_checker::CheckBudget;
        use gandr_core_incremental::Program;
        use gandr_core_incremental::Sort;
        use gandr_core_incremental::TypeContent;
        use gandr_core_incremental::check_program;
        use gandr_core_incremental::seating;

        let grammar = built_in().expect("the built-in grammar builds");
        eprintln!("{}", sweep.rotation());
        let visited = sweep.visit_rotating(
            MINTED,
            MINTED_NIGHTS,
            &gandr_workflow_sweep::corpus::sources().expect("the corpus reads"),
        );
        assert!(
            visited.len() >= sweep.drawn(MINTED).0,
            "the sample is drawn: {}",
            visited.len()
        );
        let mut items = 0_usize;
        let mut minted: BTreeMap<Sort, usize> = BTreeMap::new();
        let mut refused: BTreeMap<seating::Absent, usize> = BTreeMap::new();
        let mut differing = Vec::new();
        for source in visited {
            let Some(mut checked) = lowered_program(&grammar, &source.path)
            else {
                continue;
            };
            let mut fresh =
                Program::new(gandr_core_term::CoreArena::new(), checked.items().to_vec())
                    .expect("the items keep their order");
            let resume = check_program(&mut checked, CheckBudget::DEFAULT)
                .expect("a lowered program checks");
            for item in resume.checkpoints().items() {
                items = items.saturating_add(1);
                let content = item.content();
                for (root, sort) in content.declaration().iter() {
                    let table = content.rooted(root);
                    match table.mint_in(&mut fresh) {
                        Maybe::Present(node) => {
                            let count = minted.entry(sort).or_default();
                            *count = count.saturating_add(1);
                            if TypeContent::of_node(&fresh, node) != table {
                                differing.push((
                                    source.path.clone(),
                                    content.reference().clone(),
                                    root,
                                ));
                            }
                        },
                        Maybe::Absent(reason) => {
                            let count = refused.entry(reason).or_default();
                            *count = count.saturating_add(1);
                        },
                    }
                }
            }
        }
        eprintln!(
            "{items} items; roots minted back, by sort: {minted:?}; refused, by reason: {refused:?}"
        );
        assert!(
            differing.is_empty(),
            "over {items} items, each minted root reads back as the table under it; differing: \
             {differing:?}"
        );
        assert!(
            refused.keys().all(|&reason| matches!(
                reason,
                seating::Absent::Unresolved | seating::Absent::Unplaced
            )),
            "a root is refused only for an unresolved node or an unplaced reference: {refused:?}"
        );
    }

    /// The deciding pass's sample: sixty-four sources, ranked by their BLAKE3
    /// digest under this name, at least one of each corpus class, and, in the
    /// companion, every source the change adds or modifies beside them
    /// (`gandr-workflow-sweep`). The nightly profile decides the night's
    /// slice, and the `sweeps` profile every source.
    const DECIDED: Sample = Sample {
        name: SampleName("a_deciding_pass_admits_what_its_judgement_admits"),
        size: SampleSize(64),
    };

    /// The nights the nightly profile takes to decide every source: a seventh
    /// a night, the count the nightly's sweeps share.
    const DECIDED_NIGHTS: Nights = Nights(7);

    /// A pass that decides each item opens its context through the
    /// judgement's own constructor, and steps the module run's own schedule
    /// of mutual blocks. So over each corpus source it admits each item that
    /// the whole judgement admits, and refuses each item that it refuses. A
    /// pattern hole, a reduct or a literal reader that the pass's context
    /// lacked would admit an item the judgement refuses; a member of a block
    /// decided alone would refuse one it admits.
    #[test]
    fn a_deciding_pass_admits_what_its_judgement_admits()
    {
        decides_within(&Sweep::asked().expect("the run's sweep resolves"));
    }

    /// The change's sources beside the fixed set.
    #[test]
    fn a_deciding_pass_admits_what_its_judgement_admits_changed()
    {
        decides_within(&Sweep::asked().expect("the run's sweep resolves").changed());
    }

    /// Every source `sweep` visits, judged whole and decided item by item by
    /// a fresh pass, has no item that one of the two admits and the other
    /// refuses.
    ///
    /// # Specification
    /// trivial.
    fn decides_within(sweep: &Sweep)
    {
        use gandr_core_checker::CheckBudget;
        use gandr_core_checker::Unretired;
        use gandr_core_incremental::Typing;
        use gandr_core_incremental::check_program;
        use gandr_surface_corpus::Refusal;
        use gandr_surface_dispatcher::Checking;
        use gandr_surface_dispatcher::Recording;
        use gandr_surface_dispatcher::Supporting;
        use gandr_surface_dispatcher::Unshadowed;
        use gandr_surface_dispatcher::classify;
        use gandr_surface_dispatcher::item_program;
        use gandr_surface_dispatcher::judge_member_after_retiring;
        use gandr_surface_dispatcher::lay_out_shadowed;
        use gandr_surface_dispatcher::lower_unit_source;
        use gandr_surface_syntax::ByteOffset;

        let grammar = built_in().expect("the built-in grammar builds");
        eprintln!("{}", sweep.rotation());
        let visited = sweep.visit_rotating(
            DECIDED,
            DECIDED_NIGHTS,
            &gandr_workflow_sweep::corpus::sources().expect("the corpus reads"),
        );
        assert!(
            visited.len() >= sweep.drawn(DECIDED).0,
            "the sample is drawn: {}",
            visited.len()
        );
        let mut compared = 0_usize;
        let mut refused_by_the_pass = Vec::new();
        let mut admitted_by_the_pass = Vec::new();
        for source in visited {
            let path = source.path.as_path();
            let own = std::fs::read_to_string(path).expect("a corpus source reads");
            let root = classify(path);
            let laid = lay_out_shadowed(
                &grammar,
                path,
                root,
                SourceText::from(own.as_str()),
                &Unshadowed,
            );
            let text = SourceText::from(laid.text.as_str());
            let lower = || {
                let lowering =
                    lower_unit_source(&grammar, text, &laid.unit, &mut LoweringCount::default())
                        .ok()?;
                match lowering.into_lowered() {
                    Lowered::Module { module, arena } => Some((module, arena)),
                    Lowered::Refused(_) => None,
                }
            };
            let (Some((judged, judged_arena)), Some((decided, decided_arena))) = (lower(), lower())
            else {
                continue;
            };
            let (settled, _admission) = judge_member_after_retiring(
                root.corpus_root(),
                (judged, text),
                judged_arena,
                (&HostGrant::UNBOUNDED, Checking::Whole),
                ByteOffset::from(0_usize),
                (&Unretired, Recording::Unrecorded, Supporting::Unkept),
            )
            .whole()
            .into_parts();
            let Ok(Composed::Settled { ref report, .. }) = settled
            else {
                continue;
            };
            let mut refused = BTreeSet::new();
            let mut admitted = BTreeSet::new();
            for declaration in report.declarations() {
                let refusal = declaration.produced().refusal();
                if let Maybe::Present(Refusal::Checking(_)) = refusal {
                    let _new = refused.insert(declaration.constant());
                }
                else if let Maybe::Absent(_) = refusal {
                    let _new = admitted.insert(declaration.constant());
                }
            }
            let Ok(mut program) = item_program(&decided, decided_arena)
            else {
                continue;
            };
            let resume = check_program(&mut program, CheckBudget::DEFAULT)
                .expect("a lowered program checks");
            for (item, checkpoint) in program.items().iter().zip(resume.checkpoints().items()) {
                let constant = item.declaration().constant();
                let pass_refuses = matches!(checkpoint.typing(), Typing::Refused(_));
                if refused.contains(&constant) {
                    compared = compared.saturating_add(1);
                    if !pass_refuses {
                        admitted_by_the_pass.push((source.path.clone(), constant));
                    }
                }
                else if admitted.contains(&constant) {
                    compared = compared.saturating_add(1);
                    if pass_refuses {
                        refused_by_the_pass.push((source.path.clone(), constant));
                    }
                }
            }
        }
        eprintln!(
            "{compared} items compared; the pass refuses {} that the judgement admits, and \
             admits {} that it refuses",
            refused_by_the_pass.len(),
            admitted_by_the_pass.len()
        );
        assert!(
            admitted_by_the_pass.is_empty() && refused_by_the_pass.is_empty(),
            "over {compared} items, a deciding pass admits and refuses each item as the whole \
             judgement does; admitted: {admitted_by_the_pass:?}; refused: \
             {refused_by_the_pass:?}"
        );
    }

    /// #3381: `corpus/model/worlds/two-processes.gandr` persists its 53
    /// items. Its set is stored at the address of its program, and the model
    /// lowered again restores it. A resume from the restored set adopts each
    /// item that no judgement elaborated. A change of the entry's capabilities
    /// judges again `main` and the elaborated items, and no other item.
    ///
    /// The model then resumes under two grants in turn: `near` with a
    /// capability for `far` twice, then thrice. Each resume judges again each
    /// value declaration whose resolved entry moves, and each elaborated item.
    /// It adopts each data, world, abstract and codata item. Each verdict is
    /// the one a fresh pass under the grant gives.
    #[test]
    fn two_processes_persists_and_a_grant_judges_again_what_it_moves_3381()
    {
        use gandr_core_checker::CheckBudget;
        use gandr_core_checker::DeclarationContent;
        use gandr_core_checker::Entered;
        use gandr_core_checker::worlds::Entry;
        use gandr_core_checker::worlds::HostEntry;
        use gandr_core_incremental::Adoption;
        use gandr_core_incremental::BackendArtifact;
        use gandr_core_incremental::CheckpointObserver;
        use gandr_core_incremental::MemoryCheckpointStore;
        use gandr_core_incremental::Typing;
        use gandr_core_incremental::address_of;
        use gandr_core_incremental::check_program;
        use gandr_core_incremental::persist;
        use gandr_core_incremental::restore;
        use gandr_core_incremental::resume;
        use gandr_core_incremental::resume_from;
        use gandr_core_term::world::World;
        use quenchant_shape::shape::Maybe;

        /// An observer that keeps nothing.
        struct Quiet;

        impl CheckpointObserver for Quiet
        {
        }

        let grammar = built_in().expect("the built-in grammar builds");
        let path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../corpus/model/worlds/two-processes.gandr");
        let source = std::fs::read_to_string(&path).expect("the model reads");
        let lowered = |text: &str| {
            lowered_text(&grammar, &path, SourceText::from(text))
                .expect("the model lowers to a module")
        };
        let judged = |adoptions: &[Adoption]| {
            adoptions
                .iter()
                .map(|&adoption| adoption != Adoption::Adopted)
                .collect::<Vec<bool>>()
        };
        let mut base = lowered(&source);
        assert_eq!(base.items().len(), 53, "the model's closure holds 53 items");
        let checked = check_program(&mut base, CheckBudget::DEFAULT).expect("the pass runs");
        let elaborated: Vec<bool> = checked
            .checkpoints()
            .items()
            .iter()
            .map(|checkpoint| checkpoint.entered() == Entered::Elaborated)
            .collect();
        let backend = BackendArtifact::from(b"core-checker".as_slice());
        let mut store = MemoryCheckpointStore::default();
        let address = persist(
            &mut store,
            &base,
            backend,
            checked.checkpoints(),
            &mut Quiet,
        )
        .expect("each item persists");
        let mut again = lowered(&source);
        assert_eq!(
            address_of(&again).expect("the model has an address"),
            address,
            "the model lowered again has the address its set is stored at"
        );
        let Maybe::Present(restored) =
            restore(&mut store, &again, address, backend, &mut Quiet).expect("the store reads")
        else {
            panic!("the store holds the model's set");
        };
        assert_eq!(
            restored,
            *checked.checkpoints(),
            "the restored set is the stored one"
        );
        let adopted = resume_from(&restored, &mut again).expect("the model resumes");
        assert_eq!(
            adopted.typings().collect::<Vec<&Typing>>(),
            checked.typings().collect::<Vec<&Typing>>(),
            "each verdict is the one the source check gives"
        );
        assert_eq!(
            judged(adopted.adoptions()),
            elaborated,
            "the resume adopts each item that no judgement elaborated"
        );

        let edited = source.replace(
            "@[entry(*{near, far, far})",
            "@[entry(*{near, far, far, far})",
        );
        assert_ne!(
            edited, source,
            "the model states the entry the edit changes"
        );
        let mut capable = lowered(&edited);
        let resumed = resume_from(&restored, &mut capable).expect("the edited model resumes");
        let fresh =
            check_program(&mut lowered(&edited), CheckBudget::DEFAULT).expect("the pass runs");
        assert_eq!(
            resumed.typings().collect::<Vec<&Typing>>(),
            fresh.typings().collect::<Vec<&Typing>>(),
            "each verdict after the edit is the one a fresh pass gives"
        );
        let expected: Vec<bool> = capable
            .items()
            .iter()
            .zip(&elaborated)
            .map(|(item, &elaborated)| elaborated || <&[u8]>::from(item.key().name()) == b"main")
            .collect();
        assert_eq!(
            judged(resumed.adoptions()),
            expected,
            "the edit judges again `main` and the elaborated items, and no other item"
        );

        let world = |name: &str| {
            base.items()
                .iter()
                .find(|item| {
                    <&[u8]>::from(item.key().name()) == name.as_bytes()
                        && matches!(item.declaration().content(), DeclarationContent::World(_))
                })
                .map(|item| World::Declared(item.declaration().constant()))
                .expect("the model declares the world")
        };
        let (near, far) = (world("near"), world("far"));
        let mut previous = checked;
        for grant in [
            HostEntry::Within(Entry::new(near, vec![far, far])),
            HostEntry::Within(Entry::new(near, vec![far, far, far])),
        ] {
            let granted = || {
                let mut granted = lowered(&source);
                granted.enter_at(grant.clone());
                granted
            };
            let mut moved = granted();
            let resumed = resume(previous, &mut moved).expect("the granted model resumes");
            let fresh = check_program(&mut granted(), CheckBudget::DEFAULT).expect("the pass runs");
            assert_eq!(
                resumed.typings().collect::<Vec<&Typing>>(),
                fresh.typings().collect::<Vec<&Typing>>(),
                "each verdict under {grant:?} is the one a fresh pass under it gives"
            );
            let expected: Vec<bool> = moved
                .items()
                .iter()
                .zip(&elaborated)
                .map(|(item, &elaborated)| {
                    let declaration = item.declaration();
                    match *declaration.content() {
                        // One that states no entry takes the grant's, which moves.
                        DeclarationContent::Value { .. } => {
                            elaborated || matches!(declaration.entry(), Maybe::Absent(_))
                        },
                        DeclarationContent::Data(_)
                        | DeclarationContent::Codata(_)
                        | DeclarationContent::Abstract(_)
                        | DeclarationContent::World(_) => false,
                    }
                })
                .collect();
            assert_eq!(
                judged(resumed.adoptions()),
                expected,
                "{grant:?} judges again each value declaration whose entry it moves and each \
                 elaborated item, and no other item"
            );
            previous = resumed;
        }
    }

    /// The bytes of a step's `Debug` spelling, folded into one hash.
    #[repr(transparent)]
    #[derive(Default)]
    struct Digest(std::hash::DefaultHasher);

    /// A step's folded hash, compared row for row across widths.
    #[repr(transparent)]
    #[derive(Debug, PartialEq)]
    struct Hashed(u64);

    impl core::fmt::Write for Digest
    {
        /// Fold `text` into the hash.
        ///
        /// # Specification
        /// trivial.
        fn write_str(
            &mut self,
            s: &str,
        ) -> core::fmt::Result
        {
            core::hash::Hasher::write(&mut self.0, s.as_bytes());
            Ok(())
        }
    }

    /// Each step a visit over `paths` at `width` hands over, as its path
    /// and the hash of its whole `Debug` spelling, and the visit's report:
    /// one row per step, in the order handed over, so two visits' rows
    /// differ when a step's path, root, text, start, composition or
    /// standing does, up to a hash collision. A step that faults panics.
    ///
    /// # Specification
    /// trivial.
    fn digests(
        paths: &[PathBuf],
        width: Width,
    ) -> (Vec<(PathBuf, Hashed)>, ControlFlow<Infallible, RunReport>)
    {
        let mut rows = Vec::new();
        let visited =
            Walk::new(paths.to_vec()).visit(&Pool::new(width), |step| -> ControlFlow<Infallible> {
                if let Step::Fault { path, ref fault } = step {
                    panic!("{}: {fault}", path.display());
                }
                let mut digest = Digest::default();
                core::fmt::Write::write_fmt(&mut digest, format_args!("{step:?}"))
                    .expect("a hash takes every byte");
                let path = match step {
                    Step::Source { path, .. } | Step::Fault { path, .. } => path.to_path_buf(),
                };
                rows.push((path, Hashed(core::hash::Hasher::finish(&digest.0))));
                ControlFlow::Continue(())
            });
        (rows, visited)
    }
}
