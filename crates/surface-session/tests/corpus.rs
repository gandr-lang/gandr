//! The corpus agreement suite: every source of both corpus roots, submitted
//! whole to a fresh session, reports exactly the step `gandr check`'s walk
//! yields for it, and its kernel checkpoint reads back as the decoding of the
//! kernel artifact that step carries.
//!
//! The walk is the batch pipeline the driver runs; the session reaches the
//! same composition through the dispatcher's two halves with the incremental
//! checker beside them. Nothing here pins a count: each root is asserted
//! non-empty, so a source added to either changes the count without
//! reddening anything.

use gandr_core_incremental::MemoryCheckpointStore;
use gandr_kernel_term::decode;
use gandr_storage_records::InMemoryBlockStore;
use gandr_surface_corpus::CorpusRoot;
use gandr_surface_dispatcher::Composed;
use gandr_surface_dispatcher::SourceRoot;
use gandr_surface_dispatcher::Step;
use gandr_surface_dispatcher::Walk;
use gandr_surface_session::KernelCheckpoint;
use gandr_surface_session::Session;
use gandr_surface_session::resumed;
use quenchant_shape::shape::Maybe;

use crate::common::GRAMMAR;
use crate::common::backend;
use crate::common::corpus;

/// How many sources the walk read under each root.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct Sources
{
    /// The strict sources read.
    strict: usize,
    /// The fixture sources read, the pending set among them.
    fixture: usize,
}

#[test]
fn every_source_submits_as_the_walk_composes_it()
{
    let grammar = &*GRAMMAR;
    let mut walk = Walk::new(vec![
        corpus(CorpusRoot::Strict),
        corpus(CorpusRoot::Fixture),
    ]);
    let mut sources = Sources::default();
    while let Maybe::Present(step) = walk.step() {
        let Step::Source {
            path,
            root,
            text,
            composed,
            standing,
        } = step
        else {
            panic!("the corpus walks without a fault: {step:?}");
        };
        match root {
            | SourceRoot::Strict => sources.strict = sources.strict.saturating_add(1_usize),
            | SourceRoot::Fixture | SourceRoot::Pending => {
                sources.fixture = sources.fixture.saturating_add(1_usize);
            },
        }
        let mut session = Session::new(
            grammar.clone(),
            root,
            MemoryCheckpointStore::default(),
            InMemoryBlockStore::default(),
            backend(),
        );
        let submission = match session.submit(text) {
            | Ok(submission) => submission,
            | Err(fault) => panic!("{}: the session faulted: {fault}", path.display()),
        };
        match (submission.composed(), submission.kernel()) {
            | (
                &Composed::Settled { ref kernel, .. },
                Maybe::Present(&KernelCheckpoint::Stored(ref manifest)),
            ) => assert_eq!(
                Ok(decode(kernel.as_image()).expect("the kernel's own export decodes")),
                session.read_kernel(manifest),
                "{}: the kernel checkpoint reads back as the export",
                path.display()
            ),
            | (&Composed::Refused(_), Maybe::Absent(resumed::Absent::RefusedWhole)) => {},
            | (_, checkpoint) => panic!(
                "{}: the kernel checkpoint does not match the composition: {checkpoint:?}",
                path.display()
            ),
        }
        let Step::Source {
            path: submitted_path,
            root: submitted_root,
            text: submitted_text,
            composed: submitted_composed,
            standing: submitted_standing,
        } = submission.into_step(path)
        else {
            panic!("a submission is a source step");
        };
        assert_eq!(submitted_path, path, "the step is at the walked path");
        assert_eq!(submitted_root, root, "{}: the root", path.display());
        assert_eq!(submitted_text, text, "{}: the text", path.display());
        assert_eq!(
            submitted_composed,
            composed,
            "{}: the session's composition is the walk's",
            path.display()
        );
        assert_eq!(
            submitted_standing,
            standing,
            "{}: the standing",
            path.display()
        );
    }
    assert!(
        sources.strict > 0_usize,
        "the strict root is populated: {sources:?}"
    );
    assert!(
        sources.fixture > 0_usize,
        "the fixture root is populated: {sources:?}"
    );
}
