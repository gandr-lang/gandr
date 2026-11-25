//! The subscription table of the toolset: one row for each subscription, kept
//! in one file under the hub's state directory.
//!
//! The file holds the rows as one JSON array. The toolset writes the whole
//! array to a staged file, flushes it to the disk, and renames it over the
//! table. A reader thus never reads half a table, and a crash leaves the
//! earlier table or the new one. A table with no row has no file, so a hub
//! with no subscription writes nothing.
//!
//! The rows are encoded as a [`Snapshot`] under the lock of the subscriptions,
//! and the file is written outside that lock, because a flush to the disk
//! takes milliseconds. Each snapshot carries the generation of the change that
//! made it. The table writes a snapshot only when it is newer than the one the
//! file holds, so two writers that finish out of order leave the newer rows.

use alloc::string::String;
use alloc::vec::Vec;
use std::fs::DirBuilder;
use std::fs::OpenOptions;
use std::io;
use std::io::Write as _;
use std::os::unix::fs::DirBuilderExt as _;
use std::os::unix::fs::OpenOptionsExt as _;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Mutex;

use serde::Deserialize;
use serde::Serialize;

use crate::face::lock;
use crate::tools::Scope;

/// One row of the table: a subscription as a restart of the hub resumes it.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct Kept
{
    /// The conversation that the subscription belongs to.
    pub group_id: String,
    /// The identifier of the call that opened the subscription, which each
    /// event carries.
    pub tool_call_id: String,
    /// Where its events go.
    pub callback_url: String,
    /// The bearer that the runtime sent, sent back on each event.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub token: Option<String>,
    /// What the subscription follows.
    pub scope: Scope,
    /// The version of the last state that the runtime took. A resumed
    /// subscription receives a state of a later version alone.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub last_version: Option<i32>,
}

/// The count of the changes to the subscriptions, which orders their
/// snapshots.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
pub struct Generation(u64);

impl Generation
{
    /// The generation of the change after this one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn next(self) -> Self
    {
        Self(self.0.saturating_add(1))
    }
}

/// The rows of the subscriptions at one generation, encoded for the file.
pub struct Snapshot
{
    /// The generation of the change that made it.
    generation: Generation,
    /// The rows as one JSON array, or none when there is no row.
    rows: Option<Vec<u8>>,
}

impl Snapshot
{
    /// The snapshot of `rows` at `generation`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// The error encoding a row.
    #[inline]
    pub fn of(
        generation: Generation,
        rows: &[&Kept],
    ) -> io::Result<Self>
    {
        let rows = if rows.is_empty() {
            None
        }
        else {
            Some(serde_json::to_vec(rows).map_err(io::Error::other)?)
        };
        Ok(Self { generation, rows })
    }
}

/// The file of the table, and the generation of the snapshot that it holds.
pub struct Table
{
    /// The file.
    path: PathBuf,
    /// The generation of the snapshot that the file holds. Its lock is held
    /// for each write, so the writes of the file are one at a time.
    written: Mutex<Generation>,
}

impl Table
{
    /// The table in the file `path`, and the rows that the file holds.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the directory of `path` exists, made readable by its owner
    ///   alone when this call made it. The rows are those of the file, and none
    ///   when no file is there.
    /// - provides: the rows that a restart of the hub resumes.
    /// - fails: when the directory cannot be made, or the file cannot be read
    ///   or does not hold a table.
    /// - panics: none.
    /// - executable: none — the effects are a directory and a file.
    ///
    /// # Errors
    /// The error making the directory or reading the file, or
    /// [`io::ErrorKind::InvalidData`] for a file that holds no table.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a toolset that opens the table of an earlier one
    ///   sends a later state to the subscription that the earlier one kept.
    /// - witness: `rap::tests::an_account_subscription_outlives_a_restart_of_the_hub`
    #[inline]
    pub fn open(path: &Path) -> io::Result<(Self, Vec<Kept>)>
    {
        if let Some(directory) = path.parent() {
            DirBuilder::new()
                .recursive(true)
                .mode(0o700)
                .create(directory)?;
        }
        let rows = match std::fs::read(path) {
            Ok(written) => serde_json::from_slice(&written)
                .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))?,
            Err(error) if error.kind() == io::ErrorKind::NotFound => Vec::new(),
            Err(error) => return Err(error),
        };
        Ok((
            Self {
                path: path.to_path_buf(),
                written: Mutex::new(Generation::default()),
            },
            rows,
        ))
    }

    /// Write the rows of `snapshot` as the whole table, readable by its owner
    /// alone, or remove the file when the snapshot has no row. A snapshot that
    /// is not newer than the one the file holds writes nothing.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: when `snapshot` is newer than each snapshot written before,
    ///   the file holds its rows and nothing else, or is absent when it has no
    ///   row, and the file replaces the earlier one whole. Otherwise the file
    ///   is unchanged.
    /// - provides: the table as the toolset holds it, after each change.
    /// - fails: when the staged file cannot be written, flushed or put in
    ///   place, or the file cannot be removed. The file then holds the earlier
    ///   snapshot, and a later one writes the rows again.
    /// - panics: none.
    /// - executable: none — the effect is a file.
    ///
    /// # Errors
    /// The error of the write, the flush, the rename or the removal.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a table that loses its last row has no file, and a
    ///   restart reads the version that the runtime last took.
    /// - witness: `rap::tests::a_cancel_and_a_closed_thread_drop_their_rows`
    /// - witness: `rap::tests::an_account_subscription_outlives_a_restart_of_the_hub`
    #[inline]
    pub fn write(
        &self,
        snapshot: &Snapshot,
    ) -> io::Result<()>
    {
        let mut written = lock(&self.written);
        if snapshot.generation <= *written {
            return Ok(());
        }
        match snapshot.rows {
            None => match std::fs::remove_file(&self.path) {
                Err(error) if error.kind() != io::ErrorKind::NotFound => return Err(error),
                Ok(()) | Err(_) => {},
            },
            Some(ref rows) => {
                let mut staged = self.path.clone().into_os_string();
                staged.push(".new");
                let staged = PathBuf::from(staged);
                let mut file = OpenOptions::new()
                    .write(true)
                    .create(true)
                    .truncate(true)
                    .mode(0o600)
                    .open(&staged)?;
                file.write_all(rows)?;
                file.sync_all()?;
                drop(file);
                std::fs::rename(&staged, &self.path)?;
            },
        }
        *written = snapshot.generation;
        drop(written);
        Ok(())
    }
}
