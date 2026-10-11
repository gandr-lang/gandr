//! The corpus's two roots, run through the walk, read from the runner's
//! report.
//!
//! Nothing here pins a count: a gate over an unpopulated root would pass
//! vacuously, so each root is asserted non-empty and every row of the
//! fragment's exercised table carried, and adding a source changes a count
//! without reddening anything.

extern crate alloc;

/// The corpus cases, in a `cfg(test)` module so the crate's lint wall reads
/// them as test code rather than as shipping code.
#[cfg(test)]
mod corpus
{
    use alloc::collections::BTreeSet;
    use core::convert::Infallible;
    use core::num::NonZeroUsize;
    use core::ops::ControlFlow;
    use std::path::Path;
    use std::path::PathBuf;

    use anodized::spec;
    use gandr_core_sequent::FocusRefusal;
    use gandr_surface_corpus::Outcome;
    use gandr_surface_corpus::Seal;
    use gandr_surface_corpus::Settlement;
    use gandr_surface_corpus::Stated;
    use gandr_surface_dispatcher::Composed;
    use gandr_surface_dispatcher::Goals;
    use gandr_surface_dispatcher::Row;
    use gandr_surface_dispatcher::RunReport;
    use gandr_surface_dispatcher::RunVerdict;
    use gandr_surface_dispatcher::Step;
    use gandr_surface_dispatcher::Threads;
    use gandr_surface_dispatcher::Verb;
    use gandr_surface_dispatcher::Walk;
    use gandr_surface_dispatcher::Width;
    use quenchant_shape::shape::Maybe;

    /// The corpus directory `name`, under the corpus crate.
    ///
    /// # Specification
    /// - requires: `name` is empty or consists only of normal relative path
    ///   components, so it cannot replace or escape the corpus directory.
    /// - ensures: an absolute corpus path retaining the offered suffix.
    /// - fails: never; this only constructs the path, without reading it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty, strict and fixture suffixes locate the actual
    ///   corpus sweeps; absolute and parent components are outside this domain.
    /// - witness: `corpus::corpus::the_strict_root_checks_owing_nothing`
    /// - witness: `corpus::corpus::the_fixture_root_settles_every_fixture`
    /// - witness: `corpus::corpus::every_corpus_source_is_registered`
    #[spec(
        requires: name.components().all(|component| matches!(component, std::path::Component::Normal(_))),
        ensures: |ref ret| ret.is_absolute() && ret.ends_with(name)
    )]
    fn root(name: &Path) -> PathBuf
    {
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../surface-corpus")
            .join(name)
    }

    /// The report of a walk over `path`, every step a source.
    ///
    /// # Specification
    /// - requires: `path` names a finite corpus walk with no source or engine
    ///   fault; fixtures may still be unsettled or pending.
    /// - ensures: the exhausted walk's report has no faulted paths and records
    ///   one lowering per source read, preserving unsettled results for
    ///   callers.
    /// - fails: does not convert a fault into an empty or settled report.
    /// - panics: if a step faults.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — both real corpus roots have exact verdict, ledger,
    ///   settlement and row expectations; the shared source sweep checks the
    ///   lowering/read relation rather than pinning a corpus size.
    /// - witness: `corpus::corpus::the_strict_root_checks_owing_nothing`
    /// - witness: `corpus::corpus::the_fixture_root_settles_every_fixture`
    /// - witness: `corpus::corpus::a_run_lowers_each_source_once`
    #[spec(ensures: |ref ret| usize::from(ret.sources().faulted()) == 0_usize
        && usize::from(ret.lowerings()) == usize::from(ret.sources().read()))]
    fn run(path: PathBuf) -> RunReport
    {
        let mut walk = Walk::new(vec![path]);
        while let Maybe::Present(step) = walk.step() {
            if let Step::Fault { path, fault } = step {
                panic!("{}: {fault}", path.display());
            }
        }
        walk.report()
    }

    #[test]
    fn the_strict_root_checks_owing_nothing()
    {
        let report = run(root(Path::new("strict")));
        assert_eq!(
            report.verdict(Verb::Check(Goals::Gated)),
            RunVerdict::Settled,
            "check settles the strict root:\n{report}"
        );
        let declarations = report.tally().declarations();
        assert!(
            usize::from(declarations.settled()) > 0_usize,
            "the strict root holds declarations"
        );
        assert_eq!(usize::from(declarations.unsettled()), 0_usize, "{report}");
        assert_eq!(
            usize::from(report.tally().ledger()),
            0_usize,
            "the ledger is empty"
        );
        assert_eq!(
            report.tally().seal(),
            Seal::Sealed,
            "the strict root is sealed"
        );
        assert_eq!(
            usize::from(report.sources().read()),
            usize::from(report.sources().strict()),
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
                usize::from(report.exercised().count(row)) > 0_usize,
                "the strict root exercises {row}"
            );
        }
    }

    #[test]
    fn the_fixture_root_settles_every_fixture()
    {
        let report = run(root(Path::new("fixture")));
        assert_eq!(
            report.verdict(Verb::Test),
            RunVerdict::Settled,
            "test settles the fixture root:\n{report}"
        );
        assert!(
            usize::from(report.tally().fixtures().settled()) > 0_usize,
            "the fixture root holds fixtures"
        );
        assert!(
            usize::from(report.sources().pending()) > 0_usize,
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
                usize::from(report.exercised().count(row)) > 0_usize,
                "the fixture root exercises {row}"
            );
        }
    }

    #[test]
    fn the_two_roots_exercise_every_row()
    {
        let mut exercised = run(root(Path::new("strict"))).exercised();
        exercised.absorb(&run(root(Path::new("fixture"))).exercised());
        assert_eq!(exercised.missing(), Vec::new(), "every row is carried");
    }

    #[test]
    fn a_run_lowers_each_source_once()
    {
        let report = run(root(Path::new("")));
        assert_eq!(
            usize::from(report.lowerings()),
            usize::from(report.sources().read()),
            "one lowering per source read"
        );
    }

    /// A wider visit over both roots hands over, step by step, exactly what
    /// the serial walk yields, and answers the serial walk's report.
    #[test]
    fn every_width_composes_the_corpus_alike()
    {
        let paths = vec![root(Path::new("strict")), root(Path::new("fixture"))];
        for width in [
            Width::Threads(Threads::from(NonZeroUsize::MIN.saturating_add(1))),
            Width::Threads(Threads::from(NonZeroUsize::MIN.saturating_add(6))),
            Width::PerformanceCores,
        ] {
            let mut serial = Walk::new(paths.clone());
            let visited =
                Walk::new(paths.clone()).visit(width, |step| -> ControlFlow<Infallible> {
                    let Maybe::Present(expected) = serial.step()
                    else {
                        panic!("the serial walk ended first at {width:?}");
                    };
                    match (step, expected) {
                        | (
                            Step::Source {
                                path,
                                root,
                                text,
                                composed,
                                standing,
                            },
                            Step::Source {
                                path: serial_path,
                                root: serial_root,
                                text: serial_text,
                                composed: serial_composed,
                                standing: serial_standing,
                            },
                        ) => {
                            assert_eq!(
                                (path, root, text, standing),
                                (serial_path, serial_root, serial_text, serial_standing),
                                "the visit at {width:?} reaches the serial walk's source"
                            );
                            assert!(
                                composed == serial_composed,
                                "{} composes alike at {width:?}",
                                path.display()
                            );
                        },
                        | (Step::Fault { path, fault }, _) | (_, Step::Fault { path, fault }) => {
                            panic!("{}: {fault}", path.display());
                        },
                    }
                    ControlFlow::Continue(())
                });
            assert!(
                matches!(serial.step(), Maybe::Absent(_)),
                "the visit at {width:?} hands over every source"
            );
            assert_eq!(
                visited,
                ControlFlow::Continue(serial.report()),
                "the visit at {width:?} counts the serial walk's report"
            );
        }
    }

    /// Every non-directory `.gandr` entry under `corpus`, with directory
    /// links followed and each canonical directory listed once.
    ///
    /// # Specification
    /// - requires: a finite, quiescent directory graph whose directories
    ///   resolve and list successfully.
    /// - ensures: selected entries retain their paths under `corpus` and exact
    ///   `.gandr` extension; a directory with that extension is traversed
    ///   rather than returned. Revisited directory identities do not create a
    ///   cycle.
    /// - fails: does not silently omit a directory that fails to resolve or
    ///   list.
    /// - panics: on a directory-resolution, listing or entry-read failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — planted sources distinguish registered roots, outside
    ///   roots, nested source-suffixed directories and, on Unix, a directory
    ///   link the production walk skips. Cyclic links and special files are not
    ///   separately generated.
    /// - witness: `corpus::corpus::a_planted_orphan_is_not_registered`
    /// - witness: `corpus::corpus::every_corpus_source_is_registered`
    #[spec(ensures: |ref ret| ret.iter().all(|path| path.starts_with(corpus)
        && path.extension().is_some_and(|extension| extension == "gandr")))]
    fn sources_under(corpus: &Path) -> BTreeSet<PathBuf>
    {
        let mut found = BTreeSet::new();
        let mut listed = BTreeSet::new();
        let mut directories = vec![corpus.to_path_buf()];
        while let Some(directory) = directories.pop() {
            let canonical = directory.canonicalize().expect("the directory resolves");
            if !listed.insert(canonical) {
                continue;
            }
            for entry in std::fs::read_dir(&directory).expect("the directory lists") {
                let path = entry.expect("the entry reads").path();
                if path.is_dir() {
                    directories.push(path);
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

    /// The `.gandr` files under `corpus` that the one walk over its two roots
    /// does not reach.
    ///
    /// # Specification
    /// - requires: `corpus` meets the stable, readable directory-graph premise
    ///   of `sources_under`.
    /// - ensures: the independently listed source entries not reached by the
    ///   two-root walk, in strictly increasing path order. A fault at a source
    ///   still establishes that the walk reached that path.
    /// - fails: directory-inventory errors are not mistaken for registration.
    /// - panics: when the independent directory inventory cannot be read.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an exact planted orphan set separates root membership
    ///   from reachability through links, while the real corpus has no orphan.
    ///   Transient filesystem failures are outside the quiescent domain.
    /// - witness: `corpus::corpus::a_planted_orphan_is_not_registered`
    /// - witness: `corpus::corpus::every_corpus_source_is_registered`
    #[spec(ensures: |ref ret| ret.iter().all(|path| path.starts_with(corpus)
        && path.extension().is_some_and(|extension| extension == "gandr"))
        && ret.windows(2_usize).all(|pair| match *pair {
            [ref first, ref second] => first < second,
            _ => false,
        }))]
    fn orphans(corpus: &Path) -> Vec<PathBuf>
    {
        let mut reached = BTreeSet::new();
        let mut walk = Walk::new(vec![corpus.join("strict"), corpus.join("fixture")]);
        while let Maybe::Present(step) = walk.step() {
            match step {
                | Step::Source { path, .. } | Step::Fault { path, .. } => {
                    reached.insert(path.to_path_buf());
                },
            }
        }
        sources_under(corpus)
            .into_iter()
            .filter(|source| !reached.contains(source))
            .collect()
    }

    #[test]
    fn every_corpus_source_is_registered()
    {
        let corpus = root(Path::new(""));
        assert!(
            !sources_under(&corpus).is_empty(),
            "the corpus holds sources"
        );
        assert_eq!(
            orphans(&corpus),
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
        let found = orphans(&corpus);
        std::fs::remove_dir_all(&scratch).expect("the scratch directory is removed");
        assert_eq!(
            found, planted,
            "each source outside the roots, or behind a link the walk does not follow, is an orphan"
        );
    }

    /// Which half of the corpus a sweep reads: the sources under a
    /// `pathological` directory, or the model sources beside them.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum Tree
    {
        /// Every source under neither root's `pathological` directory.
        Model,
        /// Every source under a root's `pathological` directory.
        Pathological,
    }

    /// Visit each source of `tree` that the walk over both roots composes
    /// settled.
    ///
    /// # Specification
    /// - requires: the committed corpus remains quiescent during the sweep.
    /// - ensures: visits each source in the selected tree whose composition
    ///   yields a declaration report, including reports with unsettled
    ///   declarations; whole-source refusals and faulted steps are not visited.
    /// - fails: preserves the walk's exclusion of faulted sources from
    ///   callbacks.
    /// - panics: propagates a callback panic.
    /// - executable: none — the only result is calls into an opaque `FnMut`;
    ///   neither its observations nor a visit journal are returned, and
    ///   invoking it again from a predicate would change the caller's effects.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — both selected trees expose run-outcome and focusing
    ///   checks, with non-vacuity guards; this does not exhaust filesystem
    ///   faults or observe arbitrary callback side effects independently.
    /// - witness: `corpus::corpus::l_machine_matches_the_outcome_snapshots_on_the_model_corpus`
    /// - witness: `corpus::corpus::l_machine_matches_the_outcome_snapshots_on_the_pathological_corpus`
    /// - witness: `corpus::corpus::focusing_is_total_on_the_model_corpus`
    /// - witness: `corpus::corpus::focusing_is_total_on_the_pathological_corpus`
    fn each_settled(
        tree: Tree,
        mut visit: impl FnMut(&Path, &Composed<'_>),
    )
    {
        let mut walk = Walk::new(vec![root(Path::new("strict")), root(Path::new("fixture"))]);
        while let Maybe::Present(step) = walk.step() {
            let Step::Source {
                path, ref composed, ..
            } = step
            else {
                continue;
            };
            let pathological = path
                .components()
                .any(|component| component.as_os_str() == "pathological");
            let sweeps = match tree {
                | Tree::Model => !pathological,
                | Tree::Pathological => pathological,
            };
            if sweeps && matches!(*composed, Composed::Settled { .. }) {
                visit(path, composed);
            }
        }
    }

    /// Each declaration of `tree` that states a run outcome, described, and
    /// whether it settled.
    ///
    /// # Specification
    /// - requires: the committed corpus remains quiescent during the sweep.
    /// - ensures: each row retains a run expectation's observed settlement,
    ///   including failure, and begins its diagnostic with the source location
    ///   in this workspace before naming the declaration and expected outcome.
    /// - fails: does not filter out unsettled run expectations.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — real model and pathological run expectations retain
    ///   their locations and settle; location/name substitution and a wrong run
    ///   result are observable, but arbitrary diagnostic prose is not pinned.
    /// - witness: `corpus::corpus::l_machine_matches_the_outcome_snapshots_on_the_model_corpus`
    /// - witness: `corpus::corpus::l_machine_matches_the_outcome_snapshots_on_the_pathological_corpus`
    #[spec(ensures: |ref ret| ret.iter().all(|row|
        row.0.starts_with(env!("CARGO_MANIFEST_DIR"))))]
    fn stated_runs(tree: Tree) -> Vec<(String, Settlement)>
    {
        let mut runs = Vec::new();
        each_settled(tree, |path, composed| {
            let Composed::Settled { ref report, .. } = *composed
            else {
                return;
            };
            for declaration in report.declarations() {
                if let Stated::Verdict(Outcome::Runs(ref spelled)) = *declaration.stated() {
                    runs.push((
                        format!(
                            "{}: `{}` states runs to {spelled}, {}",
                            path.display(),
                            declaration.name(),
                            declaration.outcome(),
                        ),
                        declaration.settlement(),
                    ));
                }
            }
        });
        runs
    }

    /// The model corpus runs to the outcome each source states.
    #[test]
    fn l_machine_matches_the_outcome_snapshots_on_the_model_corpus()
    {
        let runs = stated_runs(Tree::Model);
        assert!(!runs.is_empty(), "the model corpus states run outcomes");
        for (run, settlement) in runs {
            assert_eq!(settlement, Settlement::Settled, "{run}");
        }
    }

    /// The pathological corpus runs to the outcome each source states.
    #[test]
    fn l_machine_matches_the_outcome_snapshots_on_the_pathological_corpus()
    {
        let runs = stated_runs(Tree::Pathological);
        assert!(
            !runs.is_empty(),
            "the pathological corpus states run outcomes"
        );
        for (run, settlement) in runs {
            assert_eq!(settlement, Settlement::Settled, "{run}");
        }
    }

    /// Every accepted declaration of `tree` that did not focus for a reason
    /// other than being a code, and the sources that composed.
    ///
    /// # Specification
    /// - requires: the committed corpus remains quiescent during the sweep.
    /// - ensures: records every composed source in the selected tree and its
    ///   non-code focusing refusals. Pending, wholly refused and faulted
    ///   sources contribute no composed path; code-only refusals are not
    ///   failures here.
    /// - fails: retains unexpected focusing refusals for the calling gate.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — both real trees compose sources and have no non-code
    ///   focusing refusal; the selected path domain is observed independently
    ///   of the diagnostic wording. Unexpected future refusal kinds are not
    ///   generated by these fixtures.
    /// - witness: `corpus::corpus::focusing_is_total_on_the_model_corpus`
    /// - witness: `corpus::corpus::focusing_is_total_on_the_pathological_corpus`
    #[spec(ensures: |ref ret| ret.1.iter().all(|path|
        path.extension().is_some_and(|extension| extension == "gandr")
            && path.components().any(|component| component.as_os_str() == "pathological")
                == matches!(tree, Tree::Pathological)))]
    fn unfocused(tree: Tree) -> (Vec<String>, Vec<PathBuf>)
    {
        let mut refusals = Vec::new();
        let mut composed_sources = Vec::new();
        each_settled(tree, |path, composed| {
            let Composed::Settled { ref program, .. } = *composed
            else {
                return;
            };
            composed_sources.push(path.to_path_buf());
            refusals.extend(
                program
                    .focus_refusals()
                    .filter(|&(_, refusal)| !matches!(refusal, FocusRefusal::Code(_)))
                    .map(|(name, refusal)| format!("{}: `{name}`: {refusal}", path.display())),
            );
        });
        (refusals, composed_sources)
    }

    /// Every accepted declaration of the model corpus focuses, but for a code,
    /// which the machine carries no image of.
    #[test]
    fn focusing_is_total_on_the_model_corpus()
    {
        let (refusals, composed) = unfocused(Tree::Model);
        assert!(!composed.is_empty(), "the model corpus composes");
        assert_eq!(
            refusals,
            Vec::<String>::new(),
            "focusing refuses only codes"
        );
    }

    /// Every accepted declaration of the pathological corpus focuses, but for
    /// a code.
    #[test]
    fn focusing_is_total_on_the_pathological_corpus()
    {
        let (refusals, composed) = unfocused(Tree::Pathological);
        assert!(!composed.is_empty(), "the pathological corpus composes");
        assert_eq!(
            refusals,
            Vec::<String>::new(),
            "focusing refuses only codes"
        );
    }
}
