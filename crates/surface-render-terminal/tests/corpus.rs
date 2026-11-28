//! The rendered refusals of the corpus's refusing sources, as the writer of
//! the outputs crate gives them. The store of outputs holds each text, and a
//! landing compares it with the text of its base.
//!
//! The cases, in a `cfg(test)` module so the crate's lint wall reads them as
//! test code rather than as shipping code.

use std::path::Path;
use std::path::PathBuf;

use gandr_workflow_outputs::refusals::rendered;

/// The checkout's root, as the walk reaches it.
///
/// # Specification
/// trivial.
fn repository() -> PathBuf
{
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("the checkout's root resolves")
}

/// The cyclic circuit's refusal names its port. The walk reads that source
/// alone, as a refusal of one source reads nothing beside it.
#[test]
fn cyclic_circuit_wiring_names_its_port_5805()
{
    let source = "pathological/circuit/circuit-cyclic-wiring.gandr";
    let repository = repository();
    let refusals = rendered(&repository, vec![repository.join("corpus").join(source)])
        .expect("the cyclic circuit fixture reads");
    let rendered = refusals
        .get(Path::new(source))
        .expect("the cyclic circuit fixture is refused");
    assert!(
        rendered.contains("port `z`"),
        "the cyclic circuit refusal names its port: {rendered}"
    );
}

// The refusing sources render their refusals in a sweep: a pull request
// renders a sample of them and the sources its change touches, and the
// nightly profile renders each of them.
mod sweeps
{
    use gandr_workflow_outputs::refusals::REFUSING;
    use gandr_workflow_sweep::Portion;
    use gandr_workflow_sweep::Sample;
    use gandr_workflow_sweep::SampleName;
    use gandr_workflow_sweep::SampleSize;
    use gandr_workflow_sweep::Source;
    use gandr_workflow_sweep::Sweep;

    use super::PathBuf;
    use super::rendered;
    use super::repository;

    /// The sample: eight refusing sources, ranked by their BLAKE3 digest under
    /// this name, at least one of the pathological twins and one of the
    /// diagnostics exemplars of the ledger; and, in the companion, each
    /// refusing source the change adds or modifies beside them
    /// (`gandr-workflow-sweep`).
    const SAMPLE: Sample = Sample {
        name: SampleName("every_refusing_source_renders_a_text_that_names_no_checkout"),
        size: SampleSize(8),
    };

    /// Every refusing source's rendered refusals are a text that two checkouts
    /// share: it names no path of the checkout, and its last line ends. A text
    /// that named the checkout would differ between two hosts, and the store
    /// would hold a change that no source made.
    #[test]
    fn every_refusing_source_renders_a_text_that_names_no_checkout()
    {
        renders(&Sweep::asked().expect("the run's sweep resolves"));
    }

    /// The change's sources beside the fixed set.
    #[test]
    fn every_refusing_source_renders_a_text_that_names_no_checkout_changed()
    {
        renders(&Sweep::asked().expect("the run's sweep resolves").changed());
    }

    /// Whether `source` sits in a directory of [`REFUSING`]: its path below
    /// `corpus/` is its name below the fixture root, or its whole name in the
    /// ledger.
    ///
    /// # Specification
    /// trivial.
    fn refusing(source: &Source) -> bool
    {
        let name = source.name.as_ref();
        let below = name.strip_prefix("fixture/").unwrap_or(name);
        REFUSING.iter().any(|directory| {
            below
                .strip_prefix(directory)
                .is_some_and(|rest| rest.starts_with('/'))
        })
    }

    /// The refusing sources `sweep` visits render texts that name no checkout
    /// and whose last line ends.
    ///
    /// # Specification
    /// trivial.
    fn renders(sweep: &Sweep)
    {
        let mut candidates = gandr_workflow_sweep::corpus::sources().expect("the corpus reads");
        candidates.extend(gandr_workflow_sweep::corpus::ledger().expect("the ledger reads"));
        candidates.retain(refusing);
        let visited = sweep.visit(SAMPLE, &candidates);
        assert!(
            visited.len() >= sweep.drawn(SAMPLE).0,
            "the sample is drawn: {}",
            visited.len()
        );
        if visited.is_empty() {
            return;
        }
        let repository = repository();
        let refusals = rendered(
            &repository,
            visited.into_iter().map(|source| source.path).collect(),
        )
        .expect("every refusing source reads");
        assert!(
            sweep.portion() == Portion::Changed || !refusals.is_empty(),
            "the refusing sources print their refusals"
        );
        let checkout = repository.display().to_string();
        let named: Vec<&PathBuf> = refusals
            .iter()
            .filter(|&(_, text)| text.contains(&checkout))
            .map(|(source, _)| source)
            .collect();
        assert!(
            named.is_empty(),
            "refusals that name the checkout: {named:?}"
        );
        let open: Vec<&PathBuf> = refusals
            .iter()
            .filter(|&(_, text)| !text.ends_with('\n'))
            .map(|(source, _)| source)
            .collect();
        assert!(
            open.is_empty(),
            "refusals whose last line does not end: {open:?}"
        );
    }
}
