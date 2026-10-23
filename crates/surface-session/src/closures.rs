//! The readmissions sessions made of a revision's leading declarations, held
//! so that a later admission leading with the same declarations resumes them
//! rather than offering the kernel each again.
//!
//! An editor rechecks a document by laying it out after its import closure and
//! judging the whole text. A store of [`Runs`] holds what readmitting a leading
//! run of such a text built — the kernel environment, the positions its
//! declarations took and their outcomes, as [`Crossed`] records them — under
//! the closure's text and the run's checkpoints. An admission whose closure
//! text is held, byte for byte, and whose leading declarations' checkpoints —
//! content, the answers each consulted and its typing — are pointwise a held
//! run's resumes from the longest such run, and the kernel is offered the
//! declarations past it alone: the text selects the candidate, the comparison
//! of what the judgement recorded admits it, so nothing below the elaborator is
//! keyed by a name, a position or a session.
//!
//! The process holds the runs of closure declarations in one store every
//! session reads ([`find`], [`keep`]): a second connection opening the
//! document, or a session over another document importing the same closure,
//! resumes too. A session holds the runs reaching past its closure into its
//! own declarations in a store of its own, [`SESSION_RUNS_HELD`] of them, so
//! the runs one document's edits make never push a closure's out. Each store
//! lets the run asked for longest ago go.

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
use gandr_surface_syntax::SourceText;

/// The most closure runs the process's store holds before it lets the one
/// asked for longest ago go: those of the few documents an editor has open.
const CLOSURES_HELD: usize = 8;

/// The most runs past its closure a session holds: one through the
/// declaration its revisions keep changing, and one through every declaration
/// for a revision that changes none.
pub const SESSION_RUNS_HELD: usize = 2;

/// A leading run's readmission, and once a commit of an export kept it, the
/// decode of the kernel declarations the readmission admitted.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the readmission it was kept with; the decoded prefix at most one
///   commit kept.
/// - panics: none.
/// - executable: none — a carrier; [`Runs::keep`] and
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

/// One leading run's readmission, under the closure's text and the run's
/// checkpoints that select and admit it.
#[derive(Debug)]
struct Held
{
    /// The closure's text: the laid-out revision before the document's own.
    text: String,
    /// The checkpoints of the run's declarations, in order.
    checkpoints: Vec<ItemCheckpoint>,
    /// What readmitting them built.
    admission: Arc<ClosureAdmission>,
    /// The tick of the store's clock it was last asked for at.
    used: u64,
}

/// Readmissions of leading runs under the closure's text and each run's
/// checkpoints, at most `HELD` of them: the process's store of the runs a
/// closure's declarations make, or a session's of the runs past its closure.
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
#[derive(Debug)]
pub struct Runs<const HELD: usize>
{
    /// The runs, in no order.
    held: Vec<Held>,
    /// Ticks once per question.
    clock: u64,
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
        Self {
            held: Vec::new(),
            clock: 0_u64,
        }
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
    ///   for last; `None` when none is held.
    /// - provides: the candidate a session's admission resumes from.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`find`].
    /// - witness: `tests::session::an_admission_resumes_the_declarations_a_revision_left_alone_2102`
    #[spec(ensures: |ret| ret.as_ref().is_none_or(|found| usize::from(found.crossed().boundary()) <= checkpoints.len()))]
    pub fn find(
        &mut self,
        text: SourceText<'_>,
        checkpoints: &[ItemCheckpoint],
    ) -> Option<Arc<ClosureAdmission>>
    {
        self.clock = self.clock.saturating_add(1);
        let now = self.clock;
        self.held
            .iter_mut()
            .filter(|held| {
                held.text == <&str>::from(text) && checkpoints.starts_with(&held.checkpoints)
            })
            .max_by_key(|held| held.checkpoints.len())
            .map(|held| {
                held.used = now;
                Arc::clone(&held.admission)
            })
    }

    /// Hold `crossed`, the readmission of the leading declarations of a
    /// revision laid out after the closure `text`, whose checkpoints are
    /// `checkpoints`, in place of any held under both, letting the one asked
    /// for longest ago go past `HELD`.
    ///
    /// # Specification
    /// - requires: `crossed` records the readmission of declarations judged to
    ///   `checkpoints`, laid out after `text`.
    /// - ensures: [`Runs::find`] of `text` and `checkpoints` answers what is
    ///   returned, holding `crossed` and no decode, until a later
    ///   [`Runs::keep`] replaces it or lets it go; no more than `HELD` is held,
    ///   and the run just kept stays while `HELD` is one or more.
    /// - provides: the record a later admission leading with the same
    ///   declarations resumes from.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`find`].
    /// - witness: `tests::session::an_edit_to_its_own_text_readmits_the_document_alone_776`
    /// - witness: `tests::session::an_admission_resumes_the_declarations_a_revision_left_alone_2102`
    #[spec(
        requires: usize::from(crossed.boundary()) == checkpoints.len(),
        ensures: self.held.len() <= HELD,
    )]
    pub fn keep(
        &mut self,
        text: String,
        checkpoints: Vec<ItemCheckpoint>,
        crossed: Crossed,
    ) -> Arc<ClosureAdmission>
    {
        let admission = Arc::new(ClosureAdmission {
            crossed,
            decoded: OnceLock::new(),
        });
        self.clock = self.clock.saturating_add(1);
        let now = self.clock;
        self.held
            .retain(|held| held.text != text || held.checkpoints != checkpoints);
        self.held.push(Held {
            text,
            checkpoints,
            admission: Arc::clone(&admission),
            used: now,
        });
        while self.held.len() > HELD {
            let oldest = self
                .held
                .iter()
                .enumerate()
                .min_by_key(|&(_, held)| held.used)
                .map(|(index, _)| index);
            let Some(oldest) = oldest
            else {
                break;
            };
            let _gone = self.held.swap_remove(oldest);
        }
        admission
    }
}

/// The process's runs of closure declarations, shared by every session.
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

/// Hold `crossed` in the process's store, as [`Runs::keep`] holds it.
///
/// # Specification
/// - requires: as [`Runs::keep`].
/// - ensures: as [`Runs::keep`], the store holding at most [`CLOSURES_HELD`].
/// - provides: the record a later admission of the same closure resumes from.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`find`].
/// - witness: `tests::session::an_edit_to_its_own_text_readmits_the_document_alone_776`
#[spec(requires: usize::from(crossed.boundary()) == checkpoints.len())]
pub fn keep(
    text: String,
    checkpoints: Vec<ItemCheckpoint>,
    crossed: Crossed,
) -> Arc<ClosureAdmission>
{
    let mut closures = CLOSURES.lock().unwrap_or_else(PoisonError::into_inner);
    let admission = closures.keep(text, checkpoints, crossed);
    drop(closures);
    admission
}
