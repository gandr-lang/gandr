//! The declarations of features of the corpus and of the library: the head of
//! each source states each feature that the source uses, as
//! `gandr features --check` judges it.

use std::path::PathBuf;

use gandr_surface_dispatcher::FeatureCensus;
use gandr_surface_dispatcher::FeatureStep;
use gandr_surface_dispatcher::Head;
use gandr_surface_dispatcher::Rewrite;
use quenchant_shape::shape::Maybe;

/// The library, from this crate.
const LIBRARY: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../../library");

/// One line for each source below `paths` whose head states a declaration
/// that differs from the features that the source uses, and one for each path
/// that the census cannot read.
///
/// # Specification
/// trivial.
fn misses(paths: Vec<PathBuf>) -> Vec<String>
{
    let mut census = FeatureCensus::new(paths, Rewrite::Check);
    let mut misses = Vec::new();
    while let Maybe::Present(step) = census.step() {
        match step {
            FeatureStep::Source {
                path,
                declaration,
                head: Head::Differs,
            } => misses.push(format!(
                "{}: the head does not state {declaration}; `gandr features --write` writes it",
                path.display()
            )),
            FeatureStep::Source { .. } => {},
            FeatureStep::Fault { path, fault } => {
                misses.push(format!("{}: {fault}", path.display()));
            },
        }
    }
    misses
}

#[test]
fn each_source_of_the_library_declares_the_features_that_it_uses()
{
    let misses = misses(Vec::from([PathBuf::from(LIBRARY)]));
    assert!(
        misses.is_empty(),
        "{} misses:\n{}",
        misses.len(),
        misses.join("\n")
    );
}

/// The sweep of the corpus: a sample on every pull request, every source
/// under the `sweeps` profile.
mod sweeps
{
    use gandr_workflow_sweep::Nights;
    use gandr_workflow_sweep::Sample;
    use gandr_workflow_sweep::SampleName;
    use gandr_workflow_sweep::SampleSize;
    use gandr_workflow_sweep::Sweep;
    use gandr_workflow_sweep::corpus::Roots;

    use super::misses;

    /// The sample: sixteen sources, ranked by their BLAKE3 digest under this
    /// name, at least one of each corpus class, and, in the companion, every
    /// source the change adds or modifies beside them
    /// (`gandr-workflow-sweep`). Sixteen hold the sweep within the suite's
    /// bound of a second a test.
    const SAMPLE: Sample = Sample {
        name: SampleName("each_source_of_the_corpus_declares_the_features_that_it_uses"),
        size: SampleSize(16),
    };

    /// The nights the nightly profile takes to judge every source: a seventh
    /// a night, the count the nightly's sweeps share.
    const NIGHTS: Nights = Nights(7);

    #[test]
    fn each_source_of_the_corpus_declares_the_features_that_it_uses()
    {
        declares(|sweep| sweep);
    }

    /// The change's sources beside the fixed set.
    #[test]
    fn each_source_of_the_corpus_declares_the_features_that_it_uses_changed()
    {
        declares(Sweep::changed);
    }

    /// The head of every source that the sweep visits states the features
    /// that the source uses. The sweep reads each directory of the corpus,
    /// the ones that the other sweeps hold out too: a source of the features
    /// ledger declares its features as each other source does.
    ///
    /// # Specification
    /// trivial.
    fn declares(portion: fn(Sweep) -> Sweep)
    {
        let mut roots = Roots::asked().expect("the roots of the corpus resolve");
        roots.fixture.held_out = &[];
        let sweep = portion(Sweep::under(&roots).expect("the run's sweep resolves"));
        eprintln!("{}", sweep.rotation());
        let visited =
            sweep.visit_rotating(SAMPLE, NIGHTS, &roots.sources().expect("the corpus reads"));
        assert!(
            visited.len() >= sweep.drawn(SAMPLE).0,
            "the sample is drawn: {}",
            visited.len()
        );
        let misses = misses(visited.into_iter().map(|source| source.path).collect());
        assert!(
            misses.is_empty(),
            "{} misses:\n{}",
            misses.len(),
            misses.join("\n")
        );
    }
}
