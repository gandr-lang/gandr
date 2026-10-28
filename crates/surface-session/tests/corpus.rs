//! The corpus agreement suite: each corpus source, submitted whole to a fresh
//! session, reports what `gandr check`'s walk reports of it, and its kernel
//! checkpoint reads back as the decoding of the kernel artifact the submission
//! carries. Every pull-request profile submits a stated sample of the two
//! roots; the `sweeps` and nightly profiles submit both roots whole.
//!
//! The walk is the batch pipeline the driver runs; it judges each source in
//! the import-connected component it belongs to. The session judges a source
//! over its import closure, through the dispatcher's two halves with the
//! incremental checker beside them. The two agree on everything a source shows
//! of itself — its own text, its standing and every entry each verb prints —
//! while the tables a component shares (its certificate, its origins, its
//! program) are the closure's in the session. Nothing here pins a count: each
//! root is asserted non-empty, so a source added to either changes the count
//! without reddening anything.

use core::convert::Infallible;
use core::ops::ControlFlow;
use std::path::PathBuf;

use gandr_core_incremental::MemoryCheckpointStore;
use gandr_kernel_term::decode;
use gandr_storage_records::InMemoryBlockStore;
use gandr_surface_corpus::CorpusRoot;
use gandr_surface_dispatcher::Composed;
use gandr_surface_dispatcher::Goals;
use gandr_surface_dispatcher::Pool;
use gandr_surface_dispatcher::SourceRoot;
use gandr_surface_dispatcher::Step;
use gandr_surface_dispatcher::Verb;
use gandr_surface_dispatcher::Walk;
use gandr_surface_dispatcher::Width;
use gandr_surface_dispatcher::entries;
use gandr_surface_dispatcher::lay_out;
use gandr_surface_session::ClosureSlot;
use gandr_surface_session::KernelCheckpoint;
use gandr_surface_session::Session;
use gandr_surface_session::admitted;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::common::GRAMMAR;
use crate::common::backend;
use crate::common::corpus;
use crate::common::three;

/// How many sources the walk read under each root.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct Sources
{
    /// The strict sources read.
    strict: usize,
    /// The fixture sources read, the pending set among them.
    fixture: usize,
}

/// The corpus submission sweep: each visited source submitted to a fresh
/// session molding at `three` threads, against the walk's step for it.
mod sweeps
{
    use gandr_workflow_sweep::Coverage;
    use gandr_workflow_sweep::Nights;
    use gandr_workflow_sweep::Rotation;
    use gandr_workflow_sweep::Sample;
    use gandr_workflow_sweep::SampleName;
    use gandr_workflow_sweep::SampleSize;
    use gandr_workflow_sweep::Sweep;

    use super::*;

    /// The sample: thirty-two corpus sources ranked by their BLAKE3 digest
    /// under this name, the first of every class — `strict` and each directory
    /// below `fixture` — and every one the change adds or modifies
    /// (`gandr-workflow-sweep`), each walked as its own path. The nightly
    /// profile walks the night's slice the same way, and the `sweeps` profile
    /// walks the two roots whole.
    const SAMPLE: Sample = Sample {
        name: SampleName("every_source_submits_as_the_walk_composes_it"),
        size: SampleSize(32),
    };

    /// The nights the nightly profile takes to submit every source: a
    /// seventh a night, the count the nightly's sweeps share (#3013). The two
    /// roots submitted whole with specifications enforced for 87 s on the
    /// nightly runner (run 40602657172).
    const NIGHTS: Nights = Nights(7);

    #[test]
    fn every_source_submits_as_the_walk_composes_it()
    {
        let sweep = Sweep::asked().expect("the run's sweep resolves");
        // A night's slice is drawn by digest alone, so it may hold no source
        // of a small class; a sample and the whole hold one of each.
        let (paths, classed): (Vec<PathBuf>, bool) = match (sweep.coverage(), sweep.rotation()) {
            (Coverage::Full, Rotation::Whole) => (
                vec![corpus(CorpusRoot::Strict), corpus(CorpusRoot::Fixture)],
                true,
            ),
            (Coverage::Full, Rotation::Night(_)) | (Coverage::Sampled, _) => {
                eprintln!("{}", sweep.rotation());
                let visited = sweep.visit_rotating(
                    SAMPLE,
                    NIGHTS,
                    &gandr_workflow_sweep::corpus::sources().expect("the corpus reads"),
                );
                assert!(
                    visited.len() >= SAMPLE.size.0,
                    "the sample is drawn: {}",
                    visited.len()
                );
                (
                    visited.into_iter().map(|source| source.path).collect(),
                    sweep.coverage() == Coverage::Sampled,
                )
            },
        };
        let mut sources = Sources::default();
        let ControlFlow::Continue(_report) = Walk::new(paths).visit(
            &Pool::new(Width::SERIAL),
            |step| -> ControlFlow<Infallible> {
                submits_as_composed(&step, &mut sources);
                ControlFlow::Continue(())
            },
        );
        if classed {
            assert!(
                sources.strict > 0_usize,
                "the strict root is populated: {sources:?}"
            );
            assert!(
                sources.fixture > 0_usize,
                "the fixture root is populated: {sources:?}"
            );
        }
        else {
            assert!(
                sources.strict.saturating_add(sources.fixture) > 0_usize,
                "the night's slice submits a source: {sources:?}"
            );
        }
    }
}

/// `step`, a corpus source the walk composed, submitted whole to a fresh
/// session molding at `three` threads, counted into `sources` by its root.
///
/// # Specification
/// - requires: `step` is a source step, the walk reaching it without a fault.
/// - ensures: the submission's kernel checkpoint reads back as the decoding of
///   the kernel artifact it carries, or the source is refused whole and stores
///   none; the submission's step stands at the walk's path and root with the
///   source's own text and standing, and prints the walk's entries under
///   `check` and `test`; `sources` counts the step under its root.
/// - panics: when `step` is a fault, the session faults, or the submission
///   disagrees with the walk.
/// - executable: none — the outcome is the panic or the return; the function
///   returns nothing a predicate could read.
///
/// # Adequacy
/// - hypothesis: L3 — the sample under every pull-request profile, both roots
///   whole under `sweeps` and nightly.
/// - witness: `tests::corpus::sweeps::every_source_submits_as_the_walk_composes_it`
fn submits_as_composed(
    step: &Step<'_>,
    sources: &mut Sources,
)
{
    let grammar = &*GRAMMAR;
    let &Step::Source {
        path,
        root,
        text,
        base,
        standing,
        ..
    } = step
    else {
        panic!("the corpus walks without a fault: {step:?}");
    };
    match root {
        SourceRoot::Strict => sources.strict = sources.strict.saturating_add(1_usize),
        SourceRoot::Fixture | SourceRoot::Pending => {
            sources.fixture = sources.fixture.saturating_add(1_usize);
        },
    }
    let mut session = Session::new(
        grammar.clone(),
        root,
        MemoryCheckpointStore::default(),
        InMemoryBlockStore::default(),
        backend(),
    )
    .with_pool(three());
    // A source is submitted over the prelude and the siblings it imports.
    let own = <&str>::from(text)
        .get(usize::from(base) ..)
        .unwrap_or_default();
    let laid = lay_out(grammar, path, root, SourceText::from(own));
    let slot = ClosureSlot::new();
    let submitted = session.submit_unit(
        SourceText::from(laid.text.as_str()),
        &laid.unit,
        laid.base,
        &slot,
    );
    let submission = match submitted {
        Ok(submission) => submission,
        Err(fault) => panic!("{}: the session faulted: {fault}", path.display()),
    };
    match (submission.composed(), submission.kernel()) {
        (
            &Composed::Settled {
                kernel: Maybe::Present(ref kernel),
                ..
            },
            Maybe::Present(&KernelCheckpoint::Stored(ref manifest)),
        ) => assert_eq!(
            Ok(decode(kernel.as_image()).expect("the kernel's own export decodes")),
            session.read_kernel(manifest),
            "{}: the kernel checkpoint reads back as the export",
            path.display()
        ),
        (&Composed::Refused(_), Maybe::Absent(admitted::Absent::RefusedWhole)) => {},
        (_, checkpoint) => panic!(
            "{}: the kernel checkpoint does not match the composition: {checkpoint:?}",
            path.display()
        ),
    }
    let submitted = submission.into_step(path);
    let Step::Source {
        path: submitted_path,
        root: submitted_root,
        text: submitted_text,
        base: submitted_base,
        standing: submitted_standing,
        ..
    } = submitted
    else {
        panic!("a submission is a source step");
    };
    assert_eq!(submitted_path, path, "the step is at the walked path");
    assert_eq!(submitted_root, root, "{}: the root", path.display());
    assert_eq!(
        <&str>::from(submitted_text).get(usize::from(submitted_base) ..),
        Some(own),
        "{}: the source's own text",
        path.display()
    );
    assert_eq!(
        submitted_standing,
        standing,
        "{}: the standing",
        path.display()
    );
    for verb in [Verb::Check(Goals::Reported), Verb::Test] {
        assert_eq!(
            entries(&submitted, verb).collect::<Vec<_>>(),
            entries(step, verb).collect::<Vec<_>>(),
            "{}: the session prints the walk's entries under {verb:?}",
            path.display()
        );
    }
}
