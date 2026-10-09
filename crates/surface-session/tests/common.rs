//! What the suites share: the grammar, a backend identity, fresh sessions,
//! the corpus roots, and the batch judgement a resume is compared with.

use std::path::Path;
use std::path::PathBuf;

use gandr_core_checker::CheckBudget;
use gandr_core_checker::CheckingContext;
use gandr_core_checker::check_module;
use gandr_core_incremental::BackendArtifact;
use gandr_core_incremental::HoleMark;
use gandr_core_incremental::ItemKey;
use gandr_core_incremental::ItemOrdinal;
use gandr_core_incremental::MemoryCheckpointStore;
use gandr_core_incremental::Program;
use gandr_core_incremental::Reference;
use gandr_core_incremental::Typing;
use gandr_core_incremental::project;
use gandr_storage_records::InMemoryBlockStore;
use gandr_surface_corpus::CorpusRoot;
use gandr_surface_dispatcher::Composed;
use gandr_surface_dispatcher::SourceRoot;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::built_in;
use gandr_surface_session::Session;
use gandr_surface_session::Submission;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

/// The built-in grammar.
///
/// # Specification
/// trivial.
pub fn grammar() -> Pbg
{
    built_in().expect("the built-in grammar builds")
}

/// The backend identity every suite persists under.
///
/// # Specification
/// trivial.
pub fn backend() -> BackendArtifact
{
    BackendArtifact::from(b"gandr-surface-session tests".as_slice())
}

/// A fresh session over memory stores, for a source under `root`.
///
/// # Specification
/// trivial.
pub fn session(root: SourceRoot) -> Session<MemoryCheckpointStore, InMemoryBlockStore>
{
    Session::new(
        grammar(),
        root,
        MemoryCheckpointStore::default(),
        InMemoryBlockStore::default(),
        backend(),
    )
}

/// A source text a test submits.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Text<'text>(pub &'text str);

impl<'text> From<&'text str> for Text<'text>
{
    /// The text `text`.
    ///
    /// # Specification
    /// trivial.
    fn from(text: &'text str) -> Self
    {
        Self(text)
    }
}

impl<'text> From<&'text String> for Text<'text>
{
    /// The text `text` holds.
    ///
    /// # Specification
    /// trivial.
    fn from(text: &'text String) -> Self
    {
        Self(text.as_str())
    }
}

/// `text` submitted to `session`, which must not fault.
///
/// # Specification
/// trivial.
pub fn submit<'text>(
    session: &mut Session<MemoryCheckpointStore, InMemoryBlockStore>,
    text: impl Into<Text<'text>>,
) -> Submission<'text>
{
    let Text(text) = text.into();
    match session.submit(SourceText::from(text)) {
        | Ok(submission) => submission,
        | Err(fault) => panic!("{text:?} faulted: {fault}"),
    }
}

/// The directory of the corpus root `root`, under the corpus crate.
///
/// # Specification
/// trivial.
pub fn corpus(root: CorpusRoot) -> PathBuf
{
    let name = match root {
        | CorpusRoot::Strict => "strict",
        | CorpusRoot::Fixture => "fixture",
    };
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("surface-corpus")
        .join(name)
}

/// The typings the session's latest resume holds, in item order.
///
/// # Specification
/// trivial.
pub fn resumed<Store, Blocks>(session: &Session<Store, Blocks>) -> Vec<Typing>
{
    match session.last() {
        | Maybe::Present(resume) => resume.typings().cloned().collect(),
        | Maybe::Absent(reason) => panic!("the session holds no resume: {reason:?}"),
    }
}

/// Each item of the session's latest resume, in source order: its key and
/// whether its checkpoint's footprint marks the body a hole.
///
/// # Specification
/// trivial.
pub fn footprints<Store, Blocks>(session: &Session<Store, Blocks>) -> Vec<(ItemKey, HoleMark)>
{
    let Maybe::Present(resume) = session.last()
    else {
        panic!("the session holds no resume");
    };
    resume
        .handles()
        .iter()
        .zip(resume.checkpoints().items())
        .map(|(&handle, checkpoint)| match resume.reference(handle) {
            | Maybe::Present(&Reference::Item { ref key, .. }) => {
                (key.clone(), checkpoint.footprint().hole())
            },
            | Maybe::Present(&Reference::Unoccupied) => {
                panic!("a resume's handle names an occupied position")
            },
            | Maybe::Absent(reason) => panic!("the resume's own handle is live: {reason:?}"),
        })
        .collect()
}

/// The typings the checker's own module entry gives `program` in a fresh
/// context over a copy of its arena, projected.
///
/// # Specification
/// trivial.
pub fn batch(program: &Program) -> Vec<Typing>
{
    let mut arena = program.arena().clone();
    let declarations = program.declarations();
    let report = check_module(
        &mut CheckingContext::new(&mut arena, CheckBudget::DEFAULT),
        &declarations,
    );
    report
        .judged()
        .iter()
        .enumerate()
        .map(|(index, judged)| {
            project(program, &arena, ItemOrdinal::from(index), &judged.verdict())
        })
        .collect()
}

/// The declared names a settled composition reports, in admission order.
///
/// # Specification
/// trivial.
pub fn names(composed: &Composed<'_>) -> Vec<String>
{
    match *composed {
        | Composed::Settled { ref report, .. } => report
            .declarations()
            .iter()
            .map(|declaration| declaration.name().to_string())
            .collect(),
        | Composed::Refused(ref refusal) => panic!("refused as a whole: {refusal}"),
    }
}
