//! What the suites share: the grammar, a backend identity, fresh sessions,
//! the corpus roots, and the batch judgement a resume is compared with.

use core::fmt;
use std::path::Path;
use std::path::PathBuf;
use std::sync::LazyLock;

use anodized::spec;
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

/// The built-in grammar, assembled once per test process for borrowed fixtures.
pub static GRAMMAR: LazyLock<Pbg> =
    LazyLock::new(|| built_in().expect("the built-in grammar builds"));

/// An owned grammar for sessions and lowering adapters.
///
/// # Specification
/// trivial.
pub fn grammar() -> Pbg
{
    GRAMMAR.clone()
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
/// - requires: the built-in grammar builds.
/// - ensures: returns a fresh session under the requested root, with separate
///   empty in-memory checkpoint and block stores.
/// - panics: if the built-in grammar is invalid.
///
/// # Adequacy
/// - hypothesis: L3 — first submissions under strict and fixture roots, with
///   exact standings and census values. Initial absence and root preservation
///   distinguish a stale or misconfigured fixture.
/// - witness: `tests::session::whole_file_submit_carries_definitions_forward`
/// - witness: `tests::corpus::every_source_submits_as_the_walk_composes_it`
#[spec(
    ensures: |ret| {
    ret.root() == root && usize::from(ret.lowerings()) == 0_usize
        && ret.snapshot().items().is_empty() && matches!(ret.last(), Maybe::Absent(_))
},
)]
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
/// - requires: the source may be accepted or refused but must not cause an
///   engine fault.
/// - ensures: returns that revision’s submission and records exactly one
///   lowering attempt under the session’s root.
/// - panics: if the session reports an engine fault.
///
/// # Adequacy
/// - hypothesis: L3 — accepted and wholly refused revisions, exact source
///   reports and retained prior state. The opaque conversion input is consumed
///   once; its source correspondence is observed by the callers rather than
///   converted twice in a predicate.
/// - witness: `tests::session::whole_file_submit_carries_definitions_forward`
/// - witness: `tests::session::failed_submission_retains_latest_synthesis`
#[spec(
    captures: before = usize::from(session.lowerings()),
    ensures: |ret| {
    ret.root() == session.root()
        && usize::from(session.lowerings()) == before.saturating_add(1_usize)
},
)]
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
/// - requires: the workspace keeps its corpus crate beside the session crate.
/// - ensures: names the selected corpus root, never the other root, relative to
///   this crate’s manifest directory.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — every checked-in strict and fixture source is submitted
///   with its own root and compared with the batch walk. Wrong root selection
///   changes the source set and standings.
/// - witness: `tests::corpus::every_source_submits_as_the_walk_composes_it`
#[spec(
    ensures: |ret| {
    ret
        .ends_with(
            match root {
                CorpusRoot::Strict => Path::new("surface-corpus/strict"),
                CorpusRoot::Fixture => Path::new("surface-corpus/fixture"),
            },
        )
},
)]
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
/// - requires: the session has an accepted resume.
/// - ensures: returns its typings in item order, preserving every typing
///   payload.
/// - panics: if no resume is retained.
///
/// # Adequacy
/// - hypothesis: L2 — generated revisions and edits compared against the
///   independent fresh checker. Exact ordered typings distinguish dropped
///   items, reordering and stale results.
/// - witness: `tests::incremental::incremental_equals_from_scratch`
/// - witness: `tests::session::checkpointed_session_matches_from_scratch`
#[spec(
    ensures: |ret| {
    matches!(session.last(), Maybe::Present(resume) if ret.iter().eq(resume.typings()))
},
)]
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
/// - requires: the session has a resume whose ordered handles name occupied
///   checkpoints.
/// - ensures: preserves each item key and checkpoint hole mark in source order.
/// - panics: if the resume is absent, a handle is stale, or a position is
///   unoccupied.
///
/// # Adequacy
/// - hypothesis: L3 — parser-recovery and incomplete-input sources, comparing
///   each declaration’s owed-body status with the incremental checkpoint
///   footprint. Exact keyed pairs distinguish misalignment or false hole marks.
/// - witness: `tests::goals::goal_flags_match_checkpoint_footprints_for_recovery_fixtures`
/// - witness: `tests::diag_attr::a_bare_marker_missing_its_payload_is_a_diagnostic`
#[spec(
    ensures: |ret| {
    matches!(
        session.last(), Maybe::Present(resume) if ret.len() == resume.handles().len() &&
        ret.iter().zip(resume.handles().iter().zip(resume.checkpoints().items())).all(|
        (row, (& handle, checkpoint)) | row.1 == checkpoint.footprint().hole() && match
        resume.reference(handle) { Maybe::Present(reference) => matches!(* reference,
        Reference::Item { ref key, .. } if row.0 == * key), Maybe::Absent(_) => false })
    )
},
)]
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
/// - requires: the program’s declarations and arena belong to one revision.
/// - ensures: returns one projected fresh-checker typing per item in admission
///   order, independently of any incremental resume.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — generated revisions and edit chains compare the full
///   result with incremental typings. The predicate checks cardinality;
///   semantic equality uses the independent checker path, not a second checker
///   invocation inside the postcondition.
/// - witness: `tests::incremental::incremental_equals_from_scratch`
/// - witness: `tests::session::checkpointed_session_matches_from_scratch`
#[spec(
    ensures: |ret| ret.len() == program.items().len(),
)]
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
/// - requires: the composition is settled rather than refused as a whole.
/// - ensures: returns every declaration name in admission order.
/// - panics: if the composition was refused as a whole.
///
/// # Adequacy
/// - hypothesis: L3 — successive submissions keep their own exact declaration
///   names after the session advances. Wrong order or borrowing mutable session
///   state changes those observations.
/// - witness: `tests::session::submission_owns_outcomes_after_session_advances`
/// - witness: `tests::session::whole_file_submit_carries_definitions_forward`
#[spec(
    ensures: |ret| {
    matches!(
        * composed, Composed::Settled { ref report, .. } if ret.len() == report
        .declarations().len() && ret.iter().zip(report.declarations()).all(| (name,
        declaration) | name == declaration.name().as_ref())
    )
},
)]
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
/// A sink that refuses the first attempted write.
#[derive(Debug)]
pub struct RefusingWriter;

impl fmt::Write for RefusingWriter
{
    /// Refuses the offered text without accepting output.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the sink refusal.
    /// - fails: always returns `fmt::Error`.
    /// - panics: none.
    ///
    /// # Errors
    /// Always returns `fmt::Error`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — revision faults with spans, no span and admission
    ///   positions are formatted through this sink; exact errors distinguish
    ///   swallowed sink failures.
    /// - witness: `tests::items::revision_faults_retain_fields_and_sink_refusals`
    #[spec(
        ensures: |ret| matches!(ret, Err(fmt::Error)),
    )]
    fn write_str(
        &mut self,
        _text: &str,
    ) -> fmt::Result
    {
        Err(fmt::Error)
    }
}
