//! A file that a reader reads: its path, which a refusal names, and its text.

use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use serde::de::DeserializeOwned;

use crate::error::HostToolsError;

/// A file that a reader reads.
///
/// # Specification
/// - provides: the file's path, which a refusal names, and its whole text.
/// - executable: none — a plain record; [`Input::read`] fills it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Input
{
    /// The file's path.
    pub path: PathBuf,
    /// The file's text.
    pub text: String,
}

impl Input
{
    /// The file at `path`, read whole.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the path and the whole text of the file.
    /// - provides: the one read of a file that a reader parses.
    /// - fails: [`HostToolsError::Io`] when the file cannot be read.
    /// - panics: none.
    /// - executable: none — the outcome is the file system's.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the tree's table reads whole, and the binary reads
    ///   its table and its lock through it.
    /// - witness: `recipe::tests::the_trees_table_reads_each_tool`
    /// - witness: `tests::cli::a_key_that_stands_is_kept_and_exits_zero`
    #[inline]
    pub fn read(path: &Path) -> Result<Self, HostToolsError>
    {
        let text = std::fs::read_to_string(path).map_err(|error| HostToolsError::Io {
            path: path.to_path_buf(),
            message: error.to_string(),
        })?;
        Ok(Self {
            path: path.to_path_buf(),
            text,
        })
    }

    /// The value of `T` that the text states as TOML.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the value of `T` that the text states.
    /// - provides: the one TOML reading of the table, the lock and the
    ///   configuration.
    /// - fails: [`HostToolsError::Toml`], with the file's path, when the text
    ///   is not the TOML of a `T`.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a table of an unknown way to build, a lock entry with
    ///   no version and a target with no linker are each refused with the
    ///   file's path.
    /// - witness: `recipe::tests::an_unknown_way_to_build_is_refused`
    /// - witness: `lock::tests::an_entry_with_no_version_is_refused`
    /// - witness: `host::tests::a_target_with_no_linker_is_refused`
    #[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(HostToolsError::Toml { .. })))]
    #[inline]
    pub fn parse<T>(&self) -> Result<T, HostToolsError>
    where
        T: DeserializeOwned,
    {
        toml::from_str(&self.text).map_err(|error| HostToolsError::Toml {
            path: self.path.clone(),
            message: error.message().to_owned(),
        })
    }
}
