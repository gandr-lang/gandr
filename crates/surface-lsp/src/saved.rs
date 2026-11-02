//! Saves: what `textDocument/didSave` keeps, and what an open reads back.
//!
//! # Checkpoints kept at a save
//!
//! Every change is judged as it arrives, so a save owes no check. What it is
//! the natural point for is work too heavy to repeat per keystroke: keeping
//! what the judgement built for a later one to start from. A save persists
//! the checkpoints of the copy's latest judgement into a [`Saved`] store, a
//! [`FileCheckpointStore`] directory the driver names under the user's cache
//! (`$XDG_CACHE_HOME/gandr/checkpoints`), one directory every connection of a
//! hub shares. A copy opened later in another server process, or in one whose
//! workspace hands it no set an earlier copy of its document recorded, has
//! its first judgement restore from that store: when the store holds the set
//! of the program that judgement lowers — the saved text, laid after the same
//! closure — the judgement resumes from it, adopting what the save judged
//! rather than judging the text whole. A save that lands while the
//! copy's judgement runs persists once that judgement is published; a change
//! read before then withdraws it, since the judgement is then of another text.
//!
//! The set is keyed by the identity of the checker build that judged it,
//! read off the running executable's digest, so a set another build judged is
//! never restored; and each save prunes by it: every record another build
//! judged is deleted, the running build the one the server can name. The
//! store is a cache of judgements the server makes anyway: a set it fails to
//! hold or read leaves the judgement whole, and a save it fails to keep is
//! said in a warning and changes nothing else.
//!
//! Within one workspace a set needs no store: a copy let go hands what its
//! last judgement recorded to the next copy opened at its URI, whatever its
//! text, and a connection opening a copy another holds starts from that
//! one's, as the `server` module's `Workspace` states. The store is what
//! outlasts the server.

use alloc::boxed::Box;
use core::fmt;
use std::path::Path;

use anodized::spec;
use gandr_core_incremental::BackendArtifact;
use gandr_core_incremental::CheckpointStoreError;
use gandr_core_incremental::FileCheckpointStore;
use gandr_core_incremental::RestoreFrom;
use gandr_core_incremental::Restorer;
use quenchant_shape::shape::Maybe;

use crate::build::unidentified;
use crate::recheck::DocumentSession;

/// Where saves keep their copies' checkpoints and opens restore from.
///
/// # Specification
/// - executable: none — the store is a directory path; [`Saved::keep`] and
///   [`Saved::restorer`] carry the clauses.
///
/// # Adequacy
/// - hypothesis: L3 — a copy saved, closed and opened again adopts what the
///   save judged; a save prunes what another build judged.
/// - witness: `server::tests::a_saved_copy_reopens_adopting_what_the_save_judged_1816`
/// - witness: `server::tests::a_save_prunes_what_another_build_judged_1816`
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Saved
{
    /// The checkpoint store.
    store: FileCheckpointStore,
}

/// Why a save kept nothing.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Unsaved
{
    /// The running build has no identity to key the checkpoints by.
    Unidentified(unidentified::Absent),
    /// The store refused or failed.
    Store(CheckpointStoreError),
}

impl fmt::Display for Unsaved
{
    /// Writes why the save kept nothing.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Unidentified(reason) => write!(f, "{reason}"),
            Self::Store(error) => write!(f, "{error}"),
        }
    }
}

impl Saved
{
    /// Saves kept in the directory at `path`, created if it is missing.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the directory exists.
    /// - fails: [`CheckpointStoreError::Io`] when it cannot be created.
    /// - panics: none.
    /// - executable: none — the directory's existence is
    ///   [`FileCheckpointStore::open`]'s clause, checked there.
    ///
    /// # Errors
    /// [`CheckpointStoreError::Io`], as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`FileCheckpointStore::open`].
    /// - witness: `server::tests::a_saved_copy_reopens_adopting_what_the_save_judged_1816`
    #[inline]
    pub fn at<Location>(path: Location) -> Result<Self, CheckpointStoreError>
    where
        Location: AsRef<Path>,
    {
        FileCheckpointStore::open(path).map(|store| Self { store })
    }

    /// What a copy's first judgement restores from: this store, read for the
    /// sets the running build judged.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a restorer over the store, keyed by the running build's
    ///   identity.
    /// - provides: `unidentified::Absent` when the build has none.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Saved`].
    /// - witness: `server::tests::a_saved_copy_reopens_adopting_what_the_save_judged_1816`
    #[spec(ensures: |ret| matches!(
        (&ret, crate::build::running()),
        (&Maybe::Present(_), Maybe::Present(_)) | (&Maybe::Absent(_), Maybe::Absent(_))
    ))]
    pub(crate) fn restorer(&self) -> Maybe<Box<dyn Restorer>, unidentified::Absent>
    {
        crate::build::running().map(|build| -> Box<dyn Restorer> {
            Box::new(RestoreFrom::new(
                self.store.clone(),
                BackendArtifact::from(build),
            ))
        })
    }

    /// Keep the checkpoints of `session`'s latest judgement, then prune every
    /// record another build judged.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the store holds the latest judgement's set under
    ///   the running build's identity, when the session judged one, and no
    ///   record another build judged.
    /// - fails: [`Unsaved::Unidentified`] when the build has no identity, and
    ///   [`Unsaved::Store`] when storing or pruning fails.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Unsaved`], as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Saved`].
    /// - witness: `server::tests::a_saved_copy_reopens_adopting_what_the_save_judged_1816`
    /// - witness: `server::tests::a_save_prunes_what_another_build_judged_1816`
    #[spec(ensures: |ret| !matches!(ret, Err(Unsaved::Unidentified(_))) || matches!(crate::build::running(), Maybe::Absent(_)))]
    pub(crate) fn keep(
        &self,
        session: &DocumentSession,
    ) -> Result<(), Unsaved>
    {
        let backend = match crate::build::running() {
            Maybe::Present(build) => BackendArtifact::from(build),
            Maybe::Absent(reason) => return Err(Unsaved::Unidentified(reason)),
        };
        if let Ok(ref judging) = *session {
            let mut store = self.store.clone();
            let _kept = judging
                .persist_to(&mut store, backend)
                .map_err(Unsaved::Store)?;
        }
        self.store
            .prune(backend)
            .map(|_pruned| ())
            .map_err(Unsaved::Store)
    }
}
