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
//! hub shares. A copy opened later, by any connection or any server process,
//! has its first judgement restore from that store: when the store holds the
//! set of the program that judgement lowers — the saved text, laid after the
//! same closure — the judgement resumes from it, adopting what the save
//! judged rather than judging the text whole. A save that lands while the
//! copy's judgement runs persists once that judgement is published; a change
//! read before then withdraws it, since the judgement is then of another text.
//!
//! The set is keyed by the identity of the checker build that judged it, the
//! BLAKE3 digest of the running executable, so a set another build judged is
//! never restored; and each save prunes by it: every record another build
//! judged is deleted, the running build the one the server can name. The
//! store is a cache of judgements the server makes anyway: a set it fails to
//! hold or read leaves the judgement whole, and a save it fails to keep is
//! said in a warning and changes nothing else.
//!
//! The alternatives were a sweep at each save over the importers of the saved
//! file under the opened folders, which moves earlier the work a workspace
//! pull already does when it is made, and persisting the kernel artifact,
//! which waits on a durable block store and a reader of what it holds. A
//! session that hands its records on across revisions by content, beside the
//! closure's own, is the durable form; this is the save-shaped cheap one, and
//! gives way to it once that exists.

use alloc::boxed::Box;
use core::fmt;
use std::path::Path;
use std::sync::OnceLock;

use anodized::spec;
use gandr_core_incremental::BackendArtifact;
use gandr_core_incremental::CheckpointStoreError;
use gandr_core_incremental::FileCheckpointStore;
use gandr_core_incremental::RestoreFrom;
use gandr_core_incremental::Restorer;
use quenchant_shape::shape::Maybe;

use crate::recheck::DocumentSession;

quenchant_shape::reason_enum! {
    /// Why the running build has no identity to key checkpoints by.
    pub mod unidentified {
        /// The reason none is known.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The platform does not say where the executable is.
            Unlocated,
            /// The executable could not be read.
            Unread,
        }
    }
}

/// The identity of the running build, read once per process.
static BUILD: OnceLock<Maybe<BackendArtifact, unidentified::Absent>> = OnceLock::new();

/// The identity of the running build: the BLAKE3 digest of its executable,
/// read the first time a save or an open asks.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the same answer on every call in a process; the digest of the
///   bytes of the executable the process runs when it can be read.
/// - provides: `unidentified::Absent` naming why it cannot.
/// - panics: none.
/// - executable: none — restating the digest rereads the whole executable.
///
/// # Adequacy
/// - hypothesis: L3 — a set a save keyed by it restores in the same build, and
///   a record keyed by another identity is pruned.
/// - witness: `server::tests::a_saved_copy_reopens_adopting_what_the_save_judged_1816`
/// - witness: `server::tests::a_save_prunes_what_another_build_judged_1816`
#[expect(
    clippy::std_instead_of_core,
    reason = "`core::io::ErrorKind` is not stable yet"
)]
fn build() -> Maybe<BackendArtifact, unidentified::Absent>
{
    *BUILD.get_or_init(|| {
        let Ok(path) = std::env::current_exe()
        else {
            return Maybe::Absent(unidentified::Absent::Unlocated);
        };
        let Ok(mut file) = std::fs::File::open(path)
        else {
            return Maybe::Absent(unidentified::Absent::Unread);
        };
        let mut hasher = blake3::Hasher::new();
        let mut buffer = alloc::vec![0_u8; 1 << 16];
        loop {
            match std::io::Read::read(&mut file, &mut buffer) {
                Ok(0) => break,
                Ok(read) => {
                    let _hashed = hasher.update(buffer.get(.. read).unwrap_or_default());
                },
                Err(ref error) if error.kind() == std::io::ErrorKind::Interrupted => {},
                Err(_error) => return Maybe::Absent(unidentified::Absent::Unread),
            }
        }
        Maybe::Present(BackendArtifact::from(
            hasher.finalize().as_bytes().as_slice(),
        ))
    })
}

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
            Self::Unidentified(unidentified::Absent::Unlocated) => {
                f.write_str("the running executable cannot be located")
            },
            Self::Unidentified(unidentified::Absent::Unread) => {
                f.write_str("the running executable cannot be read")
            },
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
    /// - ensures: a restorer over the store, keyed by [`build`]'s identity.
    /// - provides: `unidentified::Absent` when the build has none.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Saved`].
    /// - witness: `server::tests::a_saved_copy_reopens_adopting_what_the_save_judged_1816`
    #[spec(ensures: |ret| matches!(
        (&ret, build()),
        (&Maybe::Present(_), Maybe::Present(_)) | (&Maybe::Absent(_), Maybe::Absent(_))
    ))]
    pub(crate) fn restorer(&self) -> Maybe<Box<dyn Restorer>, unidentified::Absent>
    {
        build().map(|backend| -> Box<dyn Restorer> {
            Box::new(RestoreFrom::new(self.store.clone(), backend))
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
    #[spec(ensures: |ret| !matches!(ret, Err(Unsaved::Unidentified(_))) || matches!(build(), Maybe::Absent(_)))]
    pub(crate) fn keep(
        &self,
        session: &DocumentSession,
    ) -> Result<(), Unsaved>
    {
        let backend = match build() {
            Maybe::Present(backend) => backend,
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
