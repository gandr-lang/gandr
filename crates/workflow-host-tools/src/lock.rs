//! The version that `mise.lock` locks for each tool.

extern crate alloc;

use alloc::collections::BTreeMap;

use anodized::spec;
use serde::Deserialize;

use crate::error::HostToolsError;
use crate::input::Input;
use crate::names::ToolKey;
use crate::names::Version;

/// The locked versions of `mise.lock`, by the tool's key.
///
/// # Specification
/// - provides: for each key of the lock's `tools`, the version of its first
///   entry. mise writes one entry for each version that a configuration asks,
///   and the tree asks one.
/// - executable: none — a plain record; [`Lock::read`] fills it.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Lock
{
    /// The version of each key.
    versions: BTreeMap<ToolKey, Version>,
}

/// The part of `mise.lock` that the lock reads.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Deserialize)]
struct LockFile
{
    /// The entries of each tool.
    #[serde(default)]
    tools: BTreeMap<ToolKey, Vec<Locked>>,
}

/// One entry of a tool in `mise.lock`.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Deserialize)]
struct Locked
{
    /// The locked version.
    version: Version,
}

impl Lock
{
    /// The versions that `input` locks.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the version of the first entry of each tool of `input`.
    /// - provides: the one reading of the lock.
    /// - fails: [`HostToolsError::Toml`] when `input` is not a lock whose
    ///   entries each state a version.
    /// - panics: none.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the tree's lock reads a version for each tool of the
    ///   table, and an entry with no version is refused.
    /// - witness: `lock::tests::the_trees_lock_locks_each_tool_of_the_table`
    /// - witness: `lock::tests::an_entry_with_no_version_is_refused`
    #[spec(ensures: |ret| ret.is_ok() || matches!(ret, Err(HostToolsError::Toml { .. })))]
    #[inline]
    pub fn read(input: &Input) -> Result<Self, HostToolsError>
    {
        let file: LockFile = input.parse()?;
        Ok(Self {
            versions: file
                .tools
                .into_iter()
                .filter_map(|(key, entries)| {
                    entries.into_iter().next().map(|entry| (key, entry.version))
                })
                .collect(),
        })
    }

    /// The version locked for `key`, if any.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn version(
        &self,
        key: &ToolKey,
    ) -> Option<&Version>
    {
        self.versions.get(key)
    }
}

#[cfg(test)]
mod tests
{
    use std::path::Path;

    use super::Lock;
    use crate::error::HostToolsError;
    use crate::input::Input;
    use crate::names::ToolKey;
    use crate::recipe::Builds;

    #[test]
    fn the_trees_lock_locks_each_tool_of_the_table()
    {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let lock = Lock::read(&Input::read(&root.join("mise.lock")).unwrap()).unwrap();
        let builds =
            Builds::read(&Input::read(&root.join(".config/host-tools/builds.toml")).unwrap())
                .unwrap();
        for tool in builds.tool.iter().filter(|tool| tool.key != *"mise") {
            assert!(
                lock.version(&tool.key).is_some(),
                "{} has no locked version",
                tool.key
            );
        }
        assert_eq!(
            lock.version(&ToolKey::from("github:crate-ci/typos"))
                .map(|version| AsRef::<str>::as_ref(version).split('.').count()),
            Some(3)
        );
    }

    #[test]
    fn an_entry_with_no_version_is_refused()
    {
        let refused = Lock::read(&Input {
            path: "mise.lock".into(),
            text: "[[tools.\"github:a/b\"]]\nbackend = \"github:a/b\"\n".to_owned(),
        });
        assert!(matches!(refused, Err(HostToolsError::Toml { .. })));
    }
}
