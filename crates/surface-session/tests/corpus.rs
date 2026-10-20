//! The corpus agreement suite: every source of both corpus roots, submitted
//! whole to a fresh session, reports what `gandr check`'s walk reports of it,
//! and its kernel checkpoint reads back as the decoding of the kernel artifact
//! the submission carries.
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

use gandr_core_incremental::MemoryCheckpointStore;
use gandr_kernel_term::decode;
use gandr_storage_records::InMemoryBlockStore;
use gandr_surface_corpus::CorpusRoot;
use gandr_surface_dispatcher::Composed;
use gandr_surface_dispatcher::Goals;
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
    let walk = Walk::new(vec![
        corpus(CorpusRoot::Strict),
        corpus(CorpusRoot::Fixture),
    ]);
    let mut sources = Sources::default();
    let ControlFlow::Continue(_report) =
        walk.visit(Width::SERIAL, |step| -> ControlFlow<Infallible> {
            let Step::Source {
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
            );
            // An importer is submitted over the siblings it imports.
            let own = <&str>::from(text)
                .get(usize::from(base) ..)
                .unwrap_or_default();
            let laid = lay_out(grammar, path, root, SourceText::from(own));
            let slot = ClosureSlot::new();
            let submitted = match laid {
                Maybe::Present(ref laid) => session.submit_unit(
                    SourceText::from(laid.text.as_str()),
                    &laid.unit,
                    laid.base,
                    &slot,
                ),
                Maybe::Absent(_) => session.submit(SourceText::from(own)),
            };
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
                    entries(&step, verb).collect::<Vec<_>>(),
                    "{}: the session prints the walk's entries under {verb:?}",
                    path.display()
                );
            }
            ControlFlow::Continue(())
        });
    assert!(
        sources.strict > 0_usize,
        "the strict root is populated: {sources:?}"
    );
    assert!(
        sources.fixture > 0_usize,
        "the fixture root is populated: {sources:?}"
    );
}
