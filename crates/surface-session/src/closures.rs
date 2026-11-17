//! The readmissions sessions made of a revision, held so that a later
//! admission leading with the same declarations keeps or resumes them rather
//! than offering the kernel each again.
//!
//! An editor rechecks a document by laying it out after its import closure and
//! judging the whole text. A store of [`Runs`] holds the record of a
//! readmission of such a text — the kernel environment, the positions its
//! declarations took and their outcomes, as [`Crossed`] records them — under
//! the closure's text and checkpoints. A record with the content key of each
//! declaration stands under the checkpoints of the closure's declarations, and
//! a later readmission keeps each entry of it that the edit leaves, matched by
//! its key. A record without keys, which an admission retired part way
//! leaves, stands under the checkpoints of its whole run. An admission whose
//! closure text is held, byte for byte, and whose leading declarations'
//! checkpoints — content, the answers each consulted and its typing — are
//! pointwise the run's resumes the run. The text selects the candidate, and
//! the keys or the comparison of what the judgement recorded admit it, so
//! nothing below the elaborator is keyed by a name, a position or a session.
//!
//! The process holds these records in one store every session reads
//! ([`find`], [`keep`]): a second connection opening the document, or a
//! session over another document importing the same closure, keeps or resumes
//! too. The store lets the record asked for longest ago go. A session holds
//! the record of the whole revision it admitted last as its own as well, so
//! the records of other documents never push it out.

use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;
use std::sync::Mutex;
use std::sync::OnceLock;
use std::sync::PoisonError;

use anodized::spec;
use gandr_core_checker::bridge::Crossed;
use gandr_core_incremental::ItemCheckpoint;
use gandr_kernel_term::DecodedPrefix;
use gandr_surface_dispatcher::Memo;
use gandr_surface_syntax::SourceText;

/// The most closure runs the process's store holds before it lets the one
/// asked for longest ago go: those of the few documents an editor has open.
const CLOSURES_HELD: usize = 8;

/// A readmission's record — of a leading run, or of a whole revision with the
/// content key of each declaration — and once a commit of an export kept it,
/// the decode of the kernel declarations the readmission admitted.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the readmission it was kept with; the decoded prefix at most one
///   commit kept.
/// - panics: none.
/// - executable: none — a carrier; [`ClosureAdmission::new`] and
///   [`ClosureAdmission::keep_decoded`] set it.
///
/// # Adequacy
/// - hypothesis: L3 — as [`find`].
/// - witness: `tests::session::an_edit_to_its_own_text_readmits_the_document_alone_776`
#[derive(Debug)]
pub struct ClosureAdmission
{
    /// What readmitting the run's declarations built.
    crossed: Crossed,
    /// The decode of the kernel declarations they admitted, once kept.
    decoded: OnceLock<DecodedPrefix>,
}

impl ClosureAdmission
{
    /// The record `crossed`, with no decode kept.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(crossed: Crossed) -> Self
    {
        Self {
            crossed,
            decoded: OnceLock::new(),
        }
    }

    /// What readmitting the run's declarations built.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn crossed(&self) -> &Crossed
    {
        &self.crossed
    }

    /// The decode of the kernel declarations the run admitted, once a commit
    /// kept it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn decoded(&self) -> Option<&DecodedPrefix>
    {
        self.decoded.get()
    }

    /// Keep `decoded`, the decode of the kernel declarations the run admitted,
    /// unless one is kept.
    ///
    /// # Specification
    /// - requires: `decoded` was kept by a decode of an artifact leading with
    ///   the run's kernel declarations.
    /// - ensures: a decoded prefix is kept.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`find`].
    /// - witness: `tests::session::an_edit_to_its_own_text_readmits_the_document_alone_776`
    #[spec(ensures: self.decoded.get().is_some())]
    #[inline]
    pub fn keep_decoded(
        &self,
        decoded: DecodedPrefix,
    )
    {
        let _kept = self.decoded.set(decoded);
    }
}

/// One leading run's readmission, under the run's checkpoints that admit it.
#[derive(Debug)]
struct Held
{
    /// The checkpoints of the run's declarations, in order.
    checkpoints: Vec<ItemCheckpoint>,
    /// What readmitting them built.
    admission: Arc<ClosureAdmission>,
}

/// Readmissions of leading runs under the closure's text and each run's
/// checkpoints, at most `HELD` of them: the process's store of the runs a
/// closure's declarations make.
///
/// # Specification
/// - requires: nothing.
/// - ensures: never holds more than `HELD` once a [`Runs::keep`] returns.
/// - panics: none.
/// - executable: none — a store; [`Runs::find`] and [`Runs::keep`] carry the
///   executable clauses.
///
/// # Adequacy
/// - hypothesis: L3 — as [`find`].
/// - witness: `tests::session::an_admission_resumes_the_declarations_a_revision_left_alone_2102`
#[repr(transparent)]
#[derive(Debug)]
pub struct Runs<const HELD: usize>
{
    /// The runs, by the closure's text: the laid-out revision before the
    /// document's own.
    held: Memo<String, Held, HELD>,
}

impl<const HELD: usize> Runs<HELD>
{
    /// A store holding nothing.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new() -> Self
    {
        Self { held: Memo::new() }
    }

    /// The readmission held for a revision laid out after the closure `text`,
    /// covering the longest run of leading items whose checkpoints are those
    /// of `checkpoints`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: of the readmissions [`Runs::keep`] holds under a text equal
    ///   to `text` byte for byte and checkpoints equal pointwise to a leading
    ///   run of `checkpoints`, the one under the longest run, now the one asked
    ///   for last; `None` when none is held. A record that covers more
    ///   declarations than `checkpoints` holds the key of each one, which a
    ///   readmission matches by key.
    /// - provides: the candidate a session's admission resumes from.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`find`].
    /// - witness: `tests::session::an_admission_resumes_the_declarations_a_revision_left_alone_2102`
    #[spec(ensures: |ret| ret.as_ref().is_none_or(|found| usize::from(found.crossed().boundary()) <= checkpoints.len()
        || matches!(found.crossed().keys(), quenchant_shape::shape::Maybe::Present(_))))]
    pub fn find(
        &mut self,
        text: SourceText<'_>,
        checkpoints: &[ItemCheckpoint],
    ) -> Option<Arc<ClosureAdmission>>
    {
        self.held
            .find(<&str>::from(text), |held| {
                checkpoints
                    .starts_with(&held.checkpoints)
                    .then_some(held.checkpoints.len())
            })
            .map(|held| Arc::clone(&held.admission))
    }

    /// Hold `admission`, a readmission's record of a revision laid out after
    /// the closure `text`, under `checkpoints`, in place of any held under
    /// both, letting the one asked for longest ago go past `HELD`.
    ///
    /// # Specification
    /// - requires: `admission` records the readmission of declarations judged
    ///   to `checkpoints`, laid out after `text`; it records more declarations
    ///   after them only when it holds the key of each one it records, since a
    ///   readmission matches those by their keys.
    /// - ensures: [`Runs::find`] of `text` and `checkpoints` answers
    ///   `admission` until a later [`Runs::keep`] replaces it or lets it go; no
    ///   more than `HELD` is held, and the record just kept stays while `HELD`
    ///   is one or more.
    /// - provides: the record a later admission leading with the same
    ///   declarations resumes or keeps from.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`find`].
    /// - witness: `tests::session::an_edit_to_its_own_text_readmits_the_document_alone_776`
    /// - witness: `tests::session::an_admission_resumes_the_declarations_a_revision_left_alone_2102`
    #[spec(requires: usize::from(admission.crossed().boundary()) == checkpoints.len()
        || matches!(admission.crossed().keys(), quenchant_shape::shape::Maybe::Present(_)) && checkpoints.len() <= usize::from(admission.crossed().boundary()))]
    pub fn keep(
        &mut self,
        text: String,
        checkpoints: Vec<ItemCheckpoint>,
        admission: Arc<ClosureAdmission>,
    )
    {
        self.held.keep(
            text,
            Held {
                checkpoints,
                admission,
            },
            |held, kept| held.checkpoints == kept.checkpoints,
        );
    }
}

/// The process's runs of closure declarations, shared by every session.
// economy: no byte form, the codec is #4084. A run's core bodies name nodes
// of the closure lowering's arena, so the run crosses the store beside the
// lowering; the kernel's verdicts already cross through the verdict cache.
static CLOSURES: Mutex<Runs<CLOSURES_HELD>> = Mutex::new(Runs::new());

/// The readmission the process holds for a revision laid out after the closure
/// `text`, covering the longest run of leading items whose checkpoints are
/// those of `checkpoints`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`Runs::find`] of the process's store.
/// - provides: the candidate a session's admission resumes the closure from,
///   whether a whole admission or a retired one left it.
/// - fails: never.
/// - panics: none.
/// - executable: none — the clause reads the store the call locks; the witness
///   admits a closure, then resumes it.
///
/// # Adequacy
/// - hypothesis: L3 — an edit to a document's own text resumes its closure, and
///   an edit to a source of the closure does not; an admission retired part way
///   is resumed from where it stopped.
/// - witness: `tests::session::an_edit_to_its_own_text_readmits_the_document_alone_776`
/// - witness: `tests::session::a_retired_admission_leaves_what_it_crossed_to_the_next_1547`
pub fn find(
    text: SourceText<'_>,
    checkpoints: &[ItemCheckpoint],
) -> Option<Arc<ClosureAdmission>>
{
    let mut closures = CLOSURES.lock().unwrap_or_else(PoisonError::into_inner);
    let found = closures.find(text, checkpoints);
    drop(closures);
    found
}

/// Hold `admission` in the process's store, as [`Runs::keep`] holds it.
///
/// # Specification
/// - requires: as [`Runs::keep`].
/// - ensures: as [`Runs::keep`], the store holding at most [`CLOSURES_HELD`].
/// - provides: the record a later admission of the same closure resumes or
///   keeps from.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`find`].
/// - witness: `tests::session::an_edit_to_its_own_text_readmits_the_document_alone_776`
#[spec(requires: usize::from(admission.crossed().boundary()) == checkpoints.len()
    || matches!(admission.crossed().keys(), quenchant_shape::shape::Maybe::Present(_)) && checkpoints.len() <= usize::from(admission.crossed().boundary()))]
pub fn keep(
    text: String,
    checkpoints: Vec<ItemCheckpoint>,
    admission: Arc<ClosureAdmission>,
)
{
    let mut closures = CLOSURES.lock().unwrap_or_else(PoisonError::into_inner);
    closures.keep(text, checkpoints, admission);
    drop(closures);
}
