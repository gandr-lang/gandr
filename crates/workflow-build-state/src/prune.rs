//! Removing every unit's files that no recorded build used.

extern crate alloc;

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use std::fs;
use std::io;
use std::path::Path;
use std::path::PathBuf;

use crate::error::BuildStateError;
use crate::units::UnitHash;
use crate::units::Units;

/// The directories of a profile directory whose entries carry a unit hash.
pub const UNIT_DIRECTORIES: [&str; 4] = ["deps", "build", ".fingerprint", "examples"];

/// What a prune removed and kept.
///
/// # Specification
/// - provides: the counts the binary reports; `kept` and `removed` count
///   entries of [`UNIT_DIRECTORIES`], a directory as one entry.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Pruned
{
    /// Entries removed: a file, or a directory with everything under it.
    pub removed: usize,
    /// The bytes the removed entries held.
    pub bytes: u64,
    /// Entries kept because a recorded unit names them.
    pub kept: usize,
}

/// Removes from `profile` every entry of [`UNIT_DIRECTORIES`] whose unit
/// `units` does not hold.
///
/// An uplifted path names its unit by being the same file as the unit's
/// hashed copy: Cargo hard-links the copy. Where the two are not one file,
/// every unit whose hashed name has the uplifted name's stem is kept.
///
/// # Specification
/// - requires: `units` read from builds into `profile`.
/// - ensures: on success every entry of the unit directories carrying a unit
///   hash `units` holds, or the hash of a file an uplifted path is, is still
///   there; every other entry carrying a hash is gone; entries carrying no hash
///   are untouched.
/// - provides: a profile directory the size of the recorded builds.
/// - fails: [`BuildStateError::Io`] when `profile` cannot be read, an uplifted
///   path is missing, or an entry cannot be measured or removed; a failure
///   during removal leaves the entries not yet visited in place.
/// - panics: none.
/// - executable: none — the outcome is the directory on disk.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — a profile holding a kept and a superseded library, a kept
///   and a superseded build-script directory pair, fingerprints, an uplifted
///   binary hard-linked to its unit beside a stale binary of the same stem, an
///   example, and an unhashed lock file; keeping by name stem, removing
///   unhashed entries or ignoring the uplift changes what survives.
/// - witness: `prune::tests::a_prune_keeps_exactly_the_recorded_units`
/// - witness: `prune::tests::a_missing_profile_is_refused`
#[inline]
pub fn prune(
    profile: &Path,
    units: &Units,
) -> Result<Pruned, BuildStateError>
{
    let entries = unit_entries(profile)?;
    let lifted = uplifted_units(units, &entries)?;
    let mut pruned = Pruned::default();
    for (path, hash) in entries {
        if units.hashes().contains(&hash) || lifted.contains(&hash) {
            pruned.kept = pruned.kept.saturating_add(1);
            continue;
        }
        count_bytes(&path, &mut pruned)?;
        remove(&path)?;
        pruned.removed = pruned.removed.saturating_add(1);
    }
    Ok(pruned)
}

/// Every entry of the unit directories of `profile` that carries a unit
/// hash, with the hash.
///
/// # Specification
/// - requires: nothing.
/// - ensures: each entry of an existing unit directory whose name is UTF-8 and
///   carries a hash, once; a missing unit directory contributes none.
/// - provides: the candidates of a prune.
/// - fails: [`BuildStateError::Io`] when `profile` is not a readable directory
///   or a unit directory cannot be listed.
/// - panics: none.
/// - executable: none — the outcome is the directory listing.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — as [`prune`].
/// - witness: `prune::tests::a_prune_keeps_exactly_the_recorded_units`
/// - witness: `prune::tests::a_missing_profile_is_refused`
fn unit_entries(profile: &Path) -> Result<Vec<(PathBuf, UnitHash)>, BuildStateError>
{
    let profile_metadata = fs::metadata(profile).map_err(|error| io(profile, &error))?;
    if !profile_metadata.is_dir() {
        return Err(BuildStateError::Io {
            path: profile.to_owned(),
            message: "not a directory".to_owned(),
        });
    }
    let mut entries = Vec::new();
    for directory in UNIT_DIRECTORIES {
        let directory = profile.join(directory);
        let listing = match fs::read_dir(&directory) {
            Ok(listing) => listing,
            Err(error) if error.kind() == io::ErrorKind::NotFound => continue,
            Err(error) => return Err(io(&directory, &error)),
        };
        for entry in listing {
            let entry = entry.map_err(|error| io(&directory, &error))?;
            let name = entry.file_name();
            let Some(name) = name.to_str()
            else {
                continue;
            };
            if let Ok(hash) = name.parse::<UnitHash>() {
                entries.push((entry.path(), hash));
            }
        }
    }
    Ok(entries)
}

/// The units behind the uplifted paths of `units`.
///
/// # Specification
/// - requires: `entries` the hashed entries of the profile directory the
///   uplifted paths were copied out of.
/// - ensures: for each uplifted path, the hash of the entry that is the same
///   file, or, where none is, the hash of every entry whose stem is the path's
///   file name with `-` read as `_` or as written.
/// - provides: the units a prune keeps for the executables Cargo copied out.
/// - fails: [`BuildStateError::Io`] when an uplifted path or an entry cannot be
///   read.
/// - panics: none.
/// - executable: none — the outcome depends on the files on disk.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — as [`prune`].
/// - witness: `prune::tests::a_prune_keeps_exactly_the_recorded_units`
fn uplifted_units(
    units: &Units,
    entries: &[(PathBuf, UnitHash)],
) -> Result<BTreeSet<UnitHash>, BuildStateError>
{
    let mut identities: BTreeMap<FileIdentity, UnitHash> = BTreeMap::new();
    let mut kept = BTreeSet::new();
    let mut indexed = false;
    for uplifted in units.uplifted() {
        let metadata = fs::metadata(uplifted).map_err(|error| io(uplifted, &error))?;
        if !indexed {
            for &(ref path, hash) in entries {
                let entry = fs::symlink_metadata(path).map_err(|error| io(path, &error))?;
                if entry.is_file() {
                    identities.insert(FileIdentity::of(&entry), hash);
                }
            }
            indexed = true;
        }
        if let Some(&hash) = identities.get(&FileIdentity::of(&metadata)) {
            kept.insert(hash);
            continue;
        }
        let Some(name) = uplifted.file_name().and_then(|name| name.to_str())
        else {
            continue;
        };
        let underscored = name.replace('-', "_");
        for &(ref path, hash) in entries {
            let stem = path
                .file_name()
                .and_then(|entry| entry.to_str())
                .and_then(|entry| entry.rsplit_once('-'))
                .map(|(stem, _)| stem);
            if stem.is_some_and(|stem| stem == name || stem == underscored) {
                kept.insert(hash);
            }
        }
    }
    Ok(kept)
}

/// The identity of a file: the same for two hard links to one file.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct FileIdentity
{
    /// The device holding the file.
    device: u64,
    /// The file's number on that device; zero where the platform has none,
    /// so no identity matches and the stem decides.
    inode: u64,
}

impl FileIdentity
{
    /// The identity `metadata` describes.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on Unix the device and inode numbers; elsewhere an identity
    ///   unique to this call's file, so it matches no other.
    /// - provides: the hard-link test of [`uplifted_units`].
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the numbers are the platform's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`prune`].
    /// - witness: `prune::tests::a_prune_keeps_exactly_the_recorded_units`
    #[cfg(unix)]
    fn of(metadata: &fs::Metadata) -> Self
    {
        use std::os::unix::fs::MetadataExt as _;
        Self {
            device: metadata.dev(),
            inode: metadata.ino(),
        }
    }

    /// The identity `metadata` describes.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: an identity matching no other file's: the platform offers no
    ///   inode, so the stem decides.
    /// - provides: the hard-link test of [`uplifted_units`].
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — a constant.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — no hosted lane prunes off Unix.
    /// - witness: `prune::tests::a_prune_keeps_exactly_the_recorded_units`
    #[cfg(not(unix))]
    fn of(metadata: &fs::Metadata) -> Self
    {
        Self {
            device: u64::MAX,
            inode: metadata.len(),
        }
    }
}

/// Adds the bytes the files under `path` hold, `path` itself included, to
/// `pruned`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: on success `pruned.bytes` grew by the sum of the lengths of every
///   file and symbolic link at or below `path`, links not followed, saturating
///   at `u64::MAX`.
/// - provides: the bytes a prune reports.
/// - fails: [`BuildStateError::Io`] when an entry cannot be read.
/// - panics: none.
/// - executable: none — the outcome depends on the files on disk.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — the removed library and build directory are counted by
///   their contents; counting only the top entry changes the total.
/// - witness: `prune::tests::a_prune_keeps_exactly_the_recorded_units`
fn count_bytes(
    path: &Path,
    pruned: &mut Pruned,
) -> Result<(), BuildStateError>
{
    let mut pending = vec![path.to_owned()];
    while let Some(next) = pending.pop() {
        let metadata = fs::symlink_metadata(&next).map_err(|error| io(&next, &error))?;
        if metadata.is_dir() {
            for entry in fs::read_dir(&next).map_err(|error| io(&next, &error))? {
                let entry = entry.map_err(|error| io(&next, &error))?;
                pending.push(entry.path());
            }
        }
        else {
            pruned.bytes = pruned.bytes.saturating_add(metadata.len());
        }
    }
    Ok(())
}

/// Removes the file or the directory tree at `path`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: on success nothing exists at `path`.
/// - provides: the removal of a superseded unit's entry.
/// - fails: [`BuildStateError::Io`] when the entry cannot be read or removed.
/// - panics: none.
/// - executable: none — the outcome is the directory on disk.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — a superseded library file and a superseded build
///   directory are both gone after a prune.
/// - witness: `prune::tests::a_prune_keeps_exactly_the_recorded_units`
fn remove(path: &Path) -> Result<(), BuildStateError>
{
    let metadata = fs::symlink_metadata(path).map_err(|error| io(path, &error))?;
    let removed = if metadata.is_dir() {
        fs::remove_dir_all(path)
    }
    else {
        fs::remove_file(path)
    };
    removed.map_err(|error| io(path, &error))
}

/// The refusal for an operation on `path` that failed with `error`.
///
/// # Specification
/// trivial.
fn io(
    path: &Path,
    error: &std::io::Error,
) -> BuildStateError
{
    BuildStateError::Io {
        path: path.to_owned(),
        message: error.to_string(),
    }
}

#[cfg(test)]
mod tests
{
    use std::fs;
    use std::path::Path;

    use super::prune;
    use crate::error::BuildStateError;
    use crate::units::Messages;
    use crate::units::Units;

    #[test]
    fn a_prune_keeps_exactly_the_recorded_units()
    {
        let root = std::env::temp_dir().join(format!("build-state-{}-keeps", std::process::id()));
        if root.exists() {
            fs::remove_dir_all(&root).unwrap();
        }
        let profile = root.join("debug");
        let file = |path: &str, bytes: usize| {
            let path = profile.join(path);
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            fs::write(path, vec![0_u8; bytes]).unwrap();
        };
        let kept = [
            "deps/liba-00000000000000a1.rlib",
            "deps/liba-00000000000000a1.rmeta",
            "deps/a-00000000000000a1.d",
            "build/b-00000000000000b1/build-script-build",
            "build/b-00000000000000b2/out/generated.rs",
            ".fingerprint/a-00000000000000a1/lib-a",
            ".fingerprint/gandr-00000000000000c1/bin-gandr",
            "deps/gandr-00000000000000c1",
            ".cargo-lock",
            "examples/lifecycle",
        ];
        let stale = [
            ("deps/liba-00000000000000f1.rlib", 100),
            ("deps/liba-00000000000000f1.rmeta", 10),
            ("build/b-00000000000000f2/out/generated.rs", 7),
            (".fingerprint/a-00000000000000f1/lib-a", 1),
            ("deps/gandr-00000000000000f3", 1000),
        ];
        for path in kept {
            file(path, 3);
        }
        for (path, bytes) in stale {
            file(path, bytes);
        }
        fs::hard_link(
            profile.join("deps/gandr-00000000000000c1"),
            profile.join("gandr"),
        )
        .unwrap();
        let messages = format!(
            concat!(
                r#"{{"reason":"compiler-artifact","filenames":["{p}/deps/liba-00000000000000a1.rlib","{p}/deps/liba-00000000000000a1.rmeta"]}}"#,
                "\n",
                r#"{{"reason":"compiler-artifact","filenames":["{p}/build/b-00000000000000b1/build-script-build"]}}"#,
                "\n",
                r#"{{"reason":"build-script-executed","out_dir":"{p}/build/b-00000000000000b2/out"}}"#,
                "\n",
                r#"{{"reason":"compiler-artifact","filenames":["{p}/gandr"]}}"#,
                "\n",
                r#"{{"reason":"build-finished","success":true}}"#,
                "\n",
            ),
            p = profile.display()
        );
        let mut units = Units::default();
        units
            .read(Path::new("units.jsonl"), Messages::from(messages.as_str()))
            .unwrap();
        let pruned = prune(&profile, &units).unwrap();
        assert_eq!(pruned.removed, 5);
        assert_eq!(pruned.bytes, 1118);
        assert_eq!(pruned.kept, 8);
        for path in kept {
            assert!(profile.join(path).exists(), "{path} kept");
        }
        for (path, _) in stale {
            assert!(!profile.join(path).exists(), "{path} removed");
        }
        assert!(!profile.join("build/b-00000000000000f2").exists());
        assert!(!profile.join(".fingerprint/a-00000000000000f1").exists());
        fs::remove_dir_all(&root).unwrap();
    }

    #[test]
    fn a_missing_profile_is_refused()
    {
        let root = std::env::temp_dir().join(format!("build-state-{}-missing", std::process::id()));
        let profile = root.join("debug");
        assert!(matches!(
            prune(&profile, &Units::default()),
            Err(BuildStateError::Io { ref path, .. }) if *path == profile
        ));
    }
}
