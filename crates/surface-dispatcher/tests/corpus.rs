//! The corpus's two roots, run through the walk, read from the runner's
//! report.
//!
//! Nothing here pins a count: a gate over an unpopulated root would pass
//! vacuously, so each root is asserted non-empty and every row of the
//! fragment's exercised table carried, and adding a source changes a count
//! without reddening anything.

/// The corpus cases, in a `cfg(test)` module so the crate's lint wall reads
/// them as test code rather than as shipping code.
#[cfg(test)]
mod corpus
{
    use std::path::Path;
    use std::path::PathBuf;

    use gandr_surface_corpus::Seal;
    use gandr_surface_dispatcher::Goals;
    use gandr_surface_dispatcher::Row;
    use gandr_surface_dispatcher::RunReport;
    use gandr_surface_dispatcher::RunVerdict;
    use gandr_surface_dispatcher::Step;
    use gandr_surface_dispatcher::Verb;
    use gandr_surface_dispatcher::Walk;
    use quenchant_shape::shape::Maybe;

    /// The corpus directory `name`, under the corpus crate.
    ///
    /// # Specification
    ///
    /// trivial.
    fn root(name: &Path) -> PathBuf
    {
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../surface-corpus")
            .join(name)
    }

    /// The report of a walk over `path`, every step a source.
    ///
    /// # Specification
    ///
    /// trivial.
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
        assert!(
            usize::from(report.sources().read()) > 0_usize,
            "the corpus holds sources"
        );
        assert_eq!(
            usize::from(report.lowerings()),
            usize::from(report.sources().read()),
            "one lowering per source read"
        );
    }
}
