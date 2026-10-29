//! The one writer that publishes a file whole.
//!
//! [`publish`] writes a file's contents into a private temporary beside it,
//! then renames the temporary onto the file's name. A reader of the directory
//! meets the file's old bytes or its new ones, never half of either. The
//! temporary's name is the file's, then `.tmp-`, the process and a nonce, and
//! the write opens it only by creating it. So a name that another writer or a
//! squatter holds is never written through: the write draws another nonce. A
//! guard owns the temporary from its creation, and on every exit but the
//! rename it attempts to remove the file.
//!
//! The writer lives in a crate of its own. So a consumer at any layer from
//! the core upward publishes a file without a dependency on another
//! consumer's store: the record stores of `core-incremental` and the planes
//! and roots of `storage-store` both write through it.
//!
//! # Boundaries
//!
//! A publication is atomic, not durable: no sync precedes or follows the
//! rename, so a crash may lose a file just published. A removal that the file
//! system refuses leaves the temporary behind, and the fault names the step
//! that failed, never the cleanup.
//!
//! # References
//!
//! - `vault:01a178aa-4bbc-7842-9a60-d11551c41e06` — lineage: the rollback audit
//!   (§ The real leak was in the filesystem): the guard owns the temporary, and
//!   the staging name is safe by exclusive creation, not by being hard to
//!   guess.

extern crate alloc;

#[cfg(test)]
mod tests;

use alloc::format;
use alloc::string::ToString as _;
use std::ffi::OsStr;
use std::io;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;

/// How many temporary names a publication tries before it gives up.
///
/// Each candidate draws a fresh 64-bit nonce, so a collision is already
/// improbable; the bound turns a pathological run of them into a fault rather
/// than a loop or a silent overwrite.
const MAX_TEMPORARY_ATTEMPTS: u8 = 8_u8;

/// The bytes a file is published with.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Contents<'bytes>(pub &'bytes [u8]);

/// The step of a publication that the file system refused.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Step
{
    /// Creating the temporary beside the file, or finding a free name for it.
    Create,
    /// Writing the contents into the temporary.
    Write,
    /// Renaming the temporary onto the file.
    Rename,
}

/// Why a file was not published: the file, the step refused and what the
/// file system said.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Unpublished
{
    /// The file the publication was to write.
    pub path: PathBuf,
    /// The step the file system refused.
    pub step: Step,
    /// What the file system said; `AlreadyExists` when every candidate name
    /// for a temporary was taken.
    pub kind: io::ErrorKind,
}

impl Unpublished
{
    /// The fault of `step` at `file`, the file system saying `kind`.
    ///
    /// # Specification
    /// trivial.
    fn at(
        file: &Path,
        step: Step,
        kind: io::ErrorKind,
    ) -> Self
    {
        Self {
            path: file.to_path_buf(),
            step,
            kind,
        }
    }
}

/// Publish `contents` as the file `name` of `directory`: a private temporary,
/// then one rename.
///
/// # Specification
/// - requires: `name` spells one file name, with no separator.
/// - ensures: on success the file `name` holds `contents`, and no temporary of
///   this publication remains; on failure the file `name` is as it was, and the
///   guard has attempted to remove the temporary.
/// - fails: [`Unpublished`] naming the file and the step refused:
///   [`Step::Create`] when no temporary can be created, or when each of
///   [`MAX_TEMPORARY_ATTEMPTS`] candidate names exists; [`Step::Write`] when
///   the contents cannot be written whole; [`Step::Rename`] when the rename
///   fails.
/// - panics: none.
/// - executable: none — the outcome is the file system's.
///
/// # Errors
/// [`Unpublished`], as above.
///
/// # Adequacy
/// - hypothesis: L3 — a publication reads back with only the file in the
///   directory, and a second one replaces it; a missing directory refuses the
///   creation; a directory at the file's name refuses the rename and is all the
///   directory holds after; squatters at the names a predictable scheme would
///   pick keep their bytes; four threads publishing one name leave one whole
///   file. A forced nonce collision, a write refused partway and a refused
///   removal are not witnessed.
/// - witness: `tests::a_published_file_holds_its_contents_and_nothing_else`
/// - witness: `tests::a_missing_directory_refuses_the_creation`
/// - witness: `tests::a_refused_rename_leaves_the_directory_as_it_was`
/// - witness: `tests::a_squatted_name_is_never_written_through`
/// - witness: `tests::concurrent_publications_leave_one_whole_file`
#[inline]
pub fn publish<Name>(
    directory: &Path,
    name: Name,
    contents: Contents<'_>,
) -> Result<(), Unpublished>
where
    Name: core::fmt::Display,
{
    let file = directory.join(name.to_string());
    let temporary = Temporary::written(directory, &name, contents, &file)?;
    temporary.rename(&file)
}

/// A temporary created exclusively beside the file it publishes, owned until
/// the rename publishes it. Its drop attempts to remove it unless the rename
/// disarmed the guard.
///
/// # Specification
/// - executable: none — publication and cleanup are the file system's; the
///   guard holds only a path and whether the rename happened.
///
/// # Adequacy
/// - hypothesis: L3 — a refused rename leaves no temporary in a writable
///   directory, and a publication leaves only the file. A refused removal is
///   not injected.
/// - witness: `tests::a_refused_rename_leaves_the_directory_as_it_was`
/// - witness: `tests::a_published_file_holds_its_contents_and_nothing_else`
/// - witness: `tests::concurrent_publications_leave_one_whole_file`
#[derive(Debug)]
struct Temporary
{
    /// The temporary's path.
    path: PathBuf,
    /// Whether the rename published it, which disarms the removal.
    published: Publication,
}

/// Whether a temporary reached the file's name.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Publication
{
    /// Still private: the guard attempts to remove it.
    Private,
    /// Renamed onto the file: nothing to remove.
    Published,
}

impl Temporary
{
    /// `contents`, written whole into a file created exclusively in
    /// `directory`, under a private name leading with `name`.
    ///
    /// # Specification
    /// - requires: `file` is `name` in `directory`.
    /// - ensures: on success the contents are whole in a file this call created
    ///   in `directory`, named `name`, then `.tmp-` and more, and the guard is
    ///   armed. A candidate name that exists is never opened: exclusive
    ///   creation turns a collision into a retry under a fresh nonce.
    /// - fails: [`Unpublished`] at `file`: [`Step::Create`] when a candidate
    ///   cannot be created for any reason but existing, or when
    ///   [`MAX_TEMPORARY_ATTEMPTS`] candidates in a row exist; [`Step::Write`]
    ///   when the write fails, the handle then closed before the guard attempts
    ///   to remove the partial file.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a publication, a missing directory, a squatter at
    ///   each predictable name and four concurrent publishers exercise the
    ///   exclusive creation. The predicate checks the temporary's directory,
    ///   its name and an armed guard; it does not reread the contents or force
    ///   the collision retry.
    /// - witness: `tests::a_published_file_holds_its_contents_and_nothing_else`
    /// - witness: `tests::a_missing_directory_refuses_the_creation`
    /// - witness: `tests::a_squatted_name_is_never_written_through`
    /// - witness: `tests::concurrent_publications_leave_one_whole_file`
    #[spec(
        ensures: |ret| match ret {
            Ok(ref temporary) => {
                temporary.published == Publication::Private
                    && temporary.path.parent() == Some(directory)
                    && temporary.path.file_name().and_then(OsStr::to_str).is_some_and(|spelled| {
                        spelled
                            .strip_prefix(name.to_string().as_str())
                            .is_some_and(|rest| rest.starts_with(".tmp-"))
                    })
            },
            Err(ref fault) => {
                fault.path == file && matches!(fault.step, Step::Create | Step::Write)
            },
        },
    )]
    fn written<Name>(
        directory: &Path,
        name: &Name,
        contents: Contents<'_>,
        file: &Path,
    ) -> Result<Self, Unpublished>
    where
        Name: core::fmt::Display,
    {
        let process = std::process::id();
        for _ in 0 .. MAX_TEMPORARY_ATTEMPTS {
            // A fresh nonce per attempt, so a retry resolves the collision it
            // met instead of meeting it again.
            let nonce = core::hash::BuildHasher::hash_one(&std::hash::RandomState::new(), process);
            let candidate = directory.join(format!("{name}.tmp-{process}-{nonce:016x}"));
            let created = std::fs::OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(&candidate);
            let mut handle = match created {
                Ok(handle) => handle,
                Err(ref error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
                Err(ref error) => return Err(Unpublished::at(file, Step::Create, error.kind())),
            };
            // Armed before the first byte, so the cleanup also covers a
            // partial write.
            let temporary = Self {
                path: candidate,
                published: Publication::Private,
            };
            let written = io::Write::write_all(&mut handle, contents.0)
                .and_then(|()| io::Write::flush(&mut handle));
            // The handle closes here, before either exit: left to the scope's
            // end, locals drop in reverse order and the guard would remove a
            // file still open, which some platforms refuse.
            drop(handle);
            return match written {
                Ok(()) => Ok(temporary),
                Err(ref error) => Err(Unpublished::at(file, Step::Write, error.kind())),
            };
        }
        Err(Unpublished::at(
            file,
            Step::Create,
            io::ErrorKind::AlreadyExists,
        ))
    }

    /// Rename the temporary onto `file`, publishing it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Ok` exactly when the rename succeeded, and the guard is then
    ///   disarmed; on failure the guard attempts to remove the temporary as it
    ///   drops.
    /// - fails: [`Unpublished`] at `file` with [`Step::Rename`] when the rename
    ///   fails.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a rename succeeds in a writable directory and fails
    ///   onto a directory at the file's name. The predicate checks the guard
    ///   and the fault; the witnesses observe the directory after, without
    ///   claiming that a refused removal could not leave a temporary.
    /// - witness: `tests::a_published_file_holds_its_contents_and_nothing_else`
    /// - witness: `tests::a_refused_rename_leaves_the_directory_as_it_was`
    #[spec(
        captures: [before = self.published],
        ensures: |ret| match ret {
            Ok(()) => self.published == Publication::Published,
            Err(ref fault) => {
                fault.path == file && fault.step == Step::Rename && self.published == before
            },
        },
    )]
    fn rename(
        mut self,
        file: &Path,
    ) -> Result<(), Unpublished>
    {
        std::fs::rename(&self.path, file)
            .map_err(|error| Unpublished::at(file, Step::Rename, error.kind()))?;
        self.published = Publication::Published;
        Ok(())
    }
}

impl Drop for Temporary
{
    /// Attempt to remove the temporary unless the rename published it.
    ///
    /// # Specification
    /// - ensures: an unpublished temporary receives one best-effort removal
    ///   attempt; a published one is not removed.
    /// - executable: none — removal is external I/O whose failure is discarded;
    ///   probing the path afterward would neither prove the attempt nor be
    ///   race-free.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a refused rename leaves no temporary in the writable
    ///   test directory, while a publication stays readable. A refused removal
    ///   or a concurrent deletion is not injected.
    /// - witness: `tests::a_refused_rename_leaves_the_directory_as_it_was`
    /// - witness: `tests::a_published_file_holds_its_contents_and_nothing_else`
    #[inline]
    fn drop(&mut self)
    {
        if self.published == Publication::Private {
            drop(std::fs::remove_file(&self.path));
        }
    }
}
