//! The one writer that publishes a file whole.
//!
//! [`publish_as`] writes a file's contents into a private temporary beside
//! it, then gives the temporary the file's name by its [`Placement`]. A
//! rename replaces the file, so a reader of the directory meets its old bytes
//! or its new ones, never half of either. A link keeps a file that already
//! holds the name, so the first publication stays. The temporary's name is
//! the file's, then `.tmp-`, the process and a nonce, and the write opens it
//! only by creating it. So a name that another writer or a squatter holds is
//! never written through: the write draws another nonce. Its [`Access`]
//! states who may read it from before it takes the name. A guard owns the
//! temporary from its creation, and on every exit but the rename it attempts
//! to remove the temporary's own name. [`publish`] is the rename at the
//! process's default access.
//!
//! The writer lives in a crate of its own. So a consumer at any layer from
//! the core upward publishes a file without a dependency on another
//! consumer's store. The record stores of `core-incremental`, the planes and
//! roots of `storage-store`, the dispatcher's rewrite of a mapped source and
//! the driver's kernel key all write through it.
//!
//! # Boundaries
//!
//! A replacement is atomic, not durable: no sync precedes or follows the
//! rename, so a crash may lose a file just published. A kept file is synced
//! before its link, since no later publication replaces it. A removal that
//! the file system refuses leaves the temporary behind, and the fault names
//! the step that failed, never the cleanup.
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

/// How a publication's temporary takes the file's name.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Placement
{
    /// Renamed onto the name, replacing any file there.
    Replace,
    /// Synced, then linked to the name, which a file already there refuses:
    /// the first publication stays. The temporary's own name goes after.
    Keep,
}

/// Who may read a published file, from its temporary's creation on.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Access
{
    /// The mode the process gives a file it creates.
    Default,
    /// Its owner alone, from the temporary's creation: mode `0o600` on Unix.
    Owner,
    /// These permissions, set on the temporary before it takes the name.
    Exactly(std::fs::Permissions),
}

/// The step of a publication that the file system refused.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Step
{
    /// Creating the temporary beside the file, or finding a free name for it.
    Create,
    /// Writing the contents into the temporary, with its permissions and, for
    /// a kept file, its sync.
    Write,
    /// Renaming the temporary onto the file.
    Rename,
    /// Linking the temporary to the file's name.
    Link,
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
/// then one rename, at the process's default access.
///
/// # Specification
/// - requires: `name` spells one file name, with no separator.
/// - ensures: as [`publish_as`] at `directory`'s `name` with
///   [`Placement::Replace`] and [`Access::Default`].
/// - fails: as [`publish_as`].
/// - panics: none.
/// - executable: none — the outcome is the file system's.
///
/// # Errors
/// [`Unpublished`], as [`publish_as`].
///
/// # Adequacy
/// - hypothesis: L3 — as [`publish_as`]'s replacement.
/// - witness: `tests::a_published_file_holds_its_contents_and_nothing_else`
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
    publish_as(
        &directory.join(name.to_string()),
        contents,
        Placement::Replace,
        &Access::Default,
    )
}

/// Publish `contents` as `file`: a private temporary beside it, readable as
/// `access` states, then `placement`'s one rename or one link.
///
/// # Specification
/// - requires: nothing; a `file` that ends in no file name is refused.
/// - ensures: on success `file` holds `contents`, and no temporary of this
///   publication remains. On failure the guard has attempted to remove the
///   temporary, and `file` is as it was: with [`Placement::Keep`], a file that
///   already held the name keeps its bytes.
/// - fails: [`Unpublished`] naming the file and the step refused:
///   [`Step::Create`] when no temporary can be created, when each of
///   [`MAX_TEMPORARY_ATTEMPTS`] candidate names exists, or with `InvalidInput`
///   when `file` ends in no file name; [`Step::Write`] when the contents, the
///   permissions or a kept file's sync cannot be written; [`Step::Rename`] when
///   the rename fails; [`Step::Link`] when the link fails, with `AlreadyExists`
///   when a file holds the name.
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
///   file. A kept publication refuses a held name and leaves the first bytes
///   alone in the directory; an owner's file and one given its permissions read
///   back with that mode. A forced nonce collision, a write refused partway and
///   a refused removal are not witnessed.
/// - witness: `tests::a_published_file_holds_its_contents_and_nothing_else`
/// - witness: `tests::a_missing_directory_refuses_the_creation`
/// - witness: `tests::a_refused_rename_leaves_the_directory_as_it_was`
/// - witness: `tests::a_squatted_name_is_never_written_through`
/// - witness: `tests::concurrent_publications_leave_one_whole_file`
/// - witness: `tests::a_kept_file_refuses_a_second_publication`
/// - witness: `tests::each_access_reaches_the_published_file`
#[inline]
pub fn publish_as(
    file: &Path,
    contents: Contents<'_>,
    placement: Placement,
    access: &Access,
) -> Result<(), Unpublished>
{
    let temporary = Temporary::written(file, contents, placement, access)?;
    match placement {
        Placement::Replace => temporary.rename(file),
        Placement::Keep => temporary.link(file),
    }
}

/// A temporary created exclusively beside the file it publishes, owned until
/// the rename moves it onto the file. Its drop attempts to remove its own
/// name unless the rename disarmed the guard; after a link the file keeps the
/// contents under its own name.
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
/// - witness: `tests::a_kept_file_refuses_a_second_publication`
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
    /// Still under its private name: the guard attempts to remove it.
    Private,
    /// Renamed onto the file: nothing to remove.
    Published,
}

impl Temporary
{
    /// `contents`, written whole into a file created exclusively beside
    /// `file`, under a private name leading with `file`'s, readable as
    /// `access` states and synced when `placement` keeps it.
    ///
    /// # Specification
    /// - requires: nothing; a `file` with no file name is refused.
    /// - ensures: on success the contents are whole in a file this call created
    ///   beside `file`, named `file`'s name, then `.tmp-` and more, and the
    ///   guard is armed. A candidate name that exists is never opened:
    ///   exclusive creation turns a collision into a retry under a fresh nonce.
    /// - fails: [`Unpublished`] at `file`: [`Step::Create`] when `file` ends in
    ///   no file name, when a candidate cannot be created for any reason but
    ///   existing, or when [`MAX_TEMPORARY_ATTEMPTS`] candidates in a row
    ///   exist; [`Step::Write`] when the write, the permissions or the sync
    ///   fail, the handle then closed before the guard attempts to remove the
    ///   partial file.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a publication, a missing directory, a squatter at
    ///   each predictable name and four concurrent publishers exercise the
    ///   exclusive creation, and an owner's file and one given permissions read
    ///   back with their mode. The predicate checks the temporary's directory,
    ///   its name and an armed guard; it does not reread the contents, the mode
    ///   or force the collision retry.
    /// - witness: `tests::a_published_file_holds_its_contents_and_nothing_else`
    /// - witness: `tests::a_missing_directory_refuses_the_creation`
    /// - witness: `tests::a_squatted_name_is_never_written_through`
    /// - witness: `tests::concurrent_publications_leave_one_whole_file`
    /// - witness: `tests::each_access_reaches_the_published_file`
    #[spec(
        ensures: |ret| match ret {
            Ok(ref temporary) => {
                temporary.published == Publication::Private
                    && temporary.path.parent() == file.parent()
                    && temporary.path.file_name().zip(file.file_name()).is_some_and(|(spelled, name)| {
                        spelled
                            .as_encoded_bytes()
                            .strip_prefix(name.as_encoded_bytes())
                            .is_some_and(|rest| rest.starts_with(b".tmp-"))
                    })
            },
            Err(ref fault) => {
                fault.path == file && matches!(fault.step, Step::Create | Step::Write)
            },
        },
    )]
    fn written(
        file: &Path,
        contents: Contents<'_>,
        placement: Placement,
        access: &Access,
    ) -> Result<Self, Unpublished>
    {
        let Some(name) = file.file_name()
        else {
            return Err(Unpublished::at(
                file,
                Step::Create,
                io::ErrorKind::InvalidInput,
            ));
        };
        let mut options = std::fs::OpenOptions::new();
        let _creating = options.write(true).create_new(true);
        #[cfg(unix)]
        {
            if *access == Access::Owner {
                let _private = std::os::unix::fs::OpenOptionsExt::mode(&mut options, 0o600);
            }
        }
        let process = std::process::id();
        for _ in 0 .. MAX_TEMPORARY_ATTEMPTS {
            // A fresh nonce per attempt, so a retry resolves the collision it
            // met instead of meeting it again.
            let nonce = core::hash::BuildHasher::hash_one(&std::hash::RandomState::new(), process);
            let mut spelled = name.to_os_string();
            spelled.push(format!(".tmp-{process}-{nonce:016x}"));
            let candidate = file.with_file_name(spelled);
            let mut handle = match options.open(&candidate) {
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
                .and_then(|()| io::Write::flush(&mut handle))
                .and_then(|()| match *access {
                    Access::Exactly(ref permissions) => handle.set_permissions(permissions.clone()),
                    Access::Default | Access::Owner => Ok(()),
                })
                .and_then(|()| match placement {
                    Placement::Keep => handle.sync_all(),
                    Placement::Replace => Ok(()),
                });
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

    /// Link the temporary to `file`, publishing it unless a file already
    /// holds the name. The guard stays armed, so the temporary's own name goes
    /// as it drops and the file keeps the contents.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Ok` exactly when the link succeeded; the guard stays armed
    ///   either way.
    /// - fails: [`Unpublished`] at `file` with [`Step::Link`] when the link
    ///   fails, with `AlreadyExists` when a file holds the name.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a link succeeds at a free name and leaves only the
    ///   file, and a second one meets the first and leaves its bytes alone in
    ///   the directory.
    /// - witness: `tests::a_kept_file_refuses_a_second_publication`
    #[spec(
        ensures: |ret| self.published == Publication::Private
            && ret.as_ref().err().is_none_or(|fault| fault.path == file && fault.step == Step::Link),
    )]
    fn link(
        self,
        file: &Path,
    ) -> Result<(), Unpublished>
    {
        std::fs::hard_link(&self.path, file)
            .map_err(|error| Unpublished::at(file, Step::Link, error.kind()))
    }
}

impl Drop for Temporary
{
    /// Attempt to remove the temporary's own name unless the rename moved it.
    ///
    /// # Specification
    /// - ensures: a temporary still under its private name receives one
    ///   best-effort removal attempt; a renamed one is not removed.
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
    /// - witness: `tests::a_kept_file_refuses_a_second_publication`
    #[inline]
    fn drop(&mut self)
    {
        if self.published == Publication::Private {
            drop(std::fs::remove_file(&self.path));
        }
    }
}
