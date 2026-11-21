//! Joining the builds of a lane's shards into one state, each unit from one
//! build.
//!
//! A shard restores the lane's state, builds its own packages and hands on
//! the files its build wrote. Two shards that build one unit write it under
//! one unit hash, and their two builds can differ. A build script that prints
//! its `rerun-if-changed` lines in the order a file system lists them gives
//! its run a different fingerprint on each host. A compiler can give
//! one crate two crate hashes from equal inputs. A join that copies the
//! shards' files over one another then holds a unit from one build beside a
//! dependent compiled against another. Cargo calls the dependent fresh, and
//! rustc refuses it.
//!
//! [`join`] keeps each unit whole from one build: the first shard that holds
//! it, else the restored state. It keeps a unit only when the unit holds its
//! fingerprint and its outputs, and when each dependency its fingerprint
//! names is the very build the join keeps. Every other unit leaves the state,
//! with each unit that depends on it, and the next build makes it again.

extern crate alloc;

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::collections::VecDeque;
use core::str::FromStr;
use std::fs;
use std::io;
use std::path::Path;
use std::path::PathBuf;

use serde::Deserialize;

use crate::error::BuildStateError;
use crate::prune::io;
use crate::prune::remove;
use crate::prune::unit_entries;
use crate::units::UnitHash;

/// The index of the restored state among the sources; the shards follow it
/// in the order the join names them.
const RESTORED: usize = 0;

/// The bytes of a fingerprint's value.
const VALUE_BYTES: usize = 8;

/// What a join kept, took from a shard and dropped.
///
/// # Specification
/// - provides: the counts the binary reports, each a count of units.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Joined
{
    /// Units of the restored state that stay as they were.
    pub restored: usize,
    /// Units taken whole from a shard.
    pub taken: usize,
    /// Units that leave the state.
    pub dropped: usize,
}

/// The value of a fingerprint: the number Cargo stores beside the
/// fingerprint's JSON, and the number a dependent's JSON records for it.
///
/// # Specification
/// - provides: the name by which a dependent's fingerprint names one build of
///   its dependency.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Value(u64);

impl FromStr for Value
{
    type Err = ();

    /// The value a fingerprint's value file holds: the hexadecimal digits of
    /// the value's little-endian bytes, as Cargo writes them.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Ok(value)` exactly when `text`, without surrounding white
    ///   space, is sixteen hexadecimal digits, read as the eight bytes of
    ///   `value` from the lowest.
    /// - provides: the value by which a dependent names this build.
    /// - fails: `()` for text of another shape.
    /// - panics: none.
    /// - executable: none — the outcome is the parse itself.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the value file of a real fingerprint against the
    ///   decimal its dependent's JSON records, a short text and a text with a
    ///   digit out of range; reading the digits as one number in the order they
    ///   stand names another value.
    /// - witness: `join::tests::a_value_reads_as_cargo_writes_it_7508`
    #[inline]
    fn from_str(text: &str) -> Result<Self, Self::Err>
    {
        let digits = text.trim().as_bytes();
        if digits.len() != VALUE_BYTES.saturating_mul(2) {
            return Err(());
        }
        let mut bytes = [0_u8; VALUE_BYTES];
        let (pairs, _) = digits.as_chunks::<2>();
        for (byte, pair) in bytes.iter_mut().zip(pairs) {
            let pair = core::str::from_utf8(pair).map_err(drop)?;
            *byte = u8::from_str_radix(pair, 16).map_err(drop)?;
        }
        Ok(Self(u64::from_le_bytes(bytes)))
    }
}

/// One build of a unit in one source.
///
/// # Specification
/// - provides: the entries that a join moves or removes, and the fingerprint
///   that decides whether the build stays.
struct Build
{
    /// The unit's entries in its source: its directory under the new layout,
    /// its files and directories under the old one.
    entries: Vec<PathBuf>,
    /// The fingerprint, when the build holds it and its outputs.
    whole: Option<Fingerprint>,
}

/// What a unit's fingerprint says of it.
///
/// # Specification
/// - provides: the value that names this build, and the values that name the
///   builds it was compiled against.
struct Fingerprint
{
    /// The value Cargo stores beside the fingerprint's JSON.
    value: Value,
    /// The value of each dependency's fingerprint.
    dependencies: Vec<Value>,
}

/// The fields of a fingerprint's JSON that a join reads.
///
/// # Specification
/// - provides: the dependencies' values and the files the local inputs name.
#[derive(Deserialize)]
struct Recorded
{
    /// Each dependency: its package, its name, whether it is public, and the
    /// value of its fingerprint.
    deps: Vec<(u64, String, bool, u64)>,
    /// The local inputs, each a one-key object.
    local: Vec<serde_json::Value>,
}

/// Joins the builds of `shards` into the restored state `profile`, each unit
/// from one build.
///
/// Each unit takes the build of the first shard that holds it, else the
/// restored build. A unit stays when its build holds its fingerprint and its
/// outputs, and when each dependency its fingerprint names resolves to the
/// build the join keeps: in the unit's own shard when that shard built the
/// dependency, else in the restored state. Every other unit leaves, with each
/// unit that depends on it.
///
/// # Specification
/// - requires: each of `shards` a profile directory that holds each entry at
///   its path in `profile`, on the file system of `profile`; a missing shard
///   holds no unit.
/// - ensures: on success each unit of `profile` is one build, whole, whose
///   dependencies are the builds `profile` holds; a kept shard build is moved
///   out of its shard; entries that carry no unit hash are untouched.
/// - provides: a state that never pairs a unit with a dependency from another
///   build.
/// - fails: [`BuildStateError::Io`] when `profile` is not a readable directory,
///   a fingerprint cannot be read, or an entry cannot be moved or removed; a
///   failure while moving leaves the units not yet visited in place.
/// - panics: none.
/// - executable: none — the outcome is the directories on disk.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — two shards that build one unit with different
///   fingerprints, a dependent compiled against the second shard's build, a
///   unit without its outputs and its dependent, a restored unit a shard
///   rebuilt with its restored dependent, and a restored unit no shard touched;
///   copying files over each other, keeping a mixed dependent or a partial
///   unit, or dropping an untouched unit changes what the state holds.
/// - witness: `join::tests::a_unit_two_shards_build_comes_whole_from_the_first_7508`
/// - witness: `join::tests::a_dependent_of_another_build_leaves_with_its_dependents_7508`
/// - witness: `join::tests::a_unit_without_its_outputs_leaves_with_its_dependents_7508`
/// - witness: `join::tests::a_missing_profile_is_refused_7508`
#[inline]
pub fn join(
    profile: &Path,
    shards: &[PathBuf],
) -> Result<Joined, BuildStateError>
{
    let mut sources = Vec::with_capacity(shards.len().saturating_add(1));
    sources.push(builds(profile)?);
    for shard in shards {
        let source = match fs::symlink_metadata(shard) {
            Ok(_) => builds(shard)?,
            Err(error) if error.kind() == io::ErrorKind::NotFound => BTreeMap::new(),
            Err(error) => return Err(io(shard, &error)),
        };
        sources.push(source);
    }
    let mut chosen: BTreeMap<UnitHash, usize> = BTreeMap::new();
    for (index, source) in sources.iter().enumerate() {
        for &hash in source.keys() {
            let choice = chosen.entry(hash).or_insert(index);
            if *choice == RESTORED {
                *choice = index;
            }
        }
    }
    let values: Vec<BTreeMap<Value, UnitHash>> = sources
        .iter()
        .map(|source| {
            source
                .iter()
                .filter_map(|(&hash, build)| {
                    build
                        .whole
                        .as_ref()
                        .map(|fingerprint| (fingerprint.value, hash))
                })
                .collect()
        })
        .collect();
    let mut dependents: BTreeMap<UnitHash, Vec<UnitHash>> = BTreeMap::new();
    let mut dropped: BTreeSet<UnitHash> = BTreeSet::new();
    let mut pending: VecDeque<UnitHash> = VecDeque::new();
    for (&hash, &index) in &chosen {
        let fingerprint = sources
            .get(index)
            .and_then(|source| source.get(&hash))
            .and_then(|build| build.whole.as_ref());
        let consistent = fingerprint.is_some_and(|fingerprint| {
            fingerprint.dependencies.iter().all(|value| {
                let own = values
                    .get(index)
                    .and_then(|own| own.get(value))
                    .map(|&found| (found, index));
                let found = own.or_else(|| {
                    if index == RESTORED {
                        return None;
                    }
                    values
                        .get(RESTORED)
                        .and_then(|restored| restored.get(value))
                        .map(|&found| (found, RESTORED))
                });
                match found {
                    Some((dependency, source)) if chosen.get(&dependency) == Some(&source) => {
                        dependents.entry(dependency).or_default().push(hash);
                        true
                    },
                    Some(_) | None => false,
                }
            })
        });
        if !consistent && dropped.insert(hash) {
            pending.push_back(hash);
        }
    }
    while let Some(hash) = pending.pop_front() {
        for &dependent in dependents.get(&hash).map_or(&[][..], Vec::as_slice) {
            if dropped.insert(dependent) {
                pending.push_back(dependent);
            }
        }
    }
    let mut joined = Joined::default();
    for (&hash, &index) in &chosen {
        let restored = sources.get(RESTORED).and_then(|source| source.get(&hash));
        if index == RESTORED && !dropped.contains(&hash) {
            joined.restored = joined.restored.saturating_add(1);
            continue;
        }
        if let Some(build) = restored {
            for entry in &build.entries {
                remove(entry)?;
            }
        }
        if dropped.contains(&hash) {
            joined.dropped = joined.dropped.saturating_add(1);
            continue;
        }
        let shard = index.checked_sub(1).and_then(|at| shards.get(at));
        let build = sources.get(index).and_then(|source| source.get(&hash));
        if let (Some(shard), Some(build)) = (shard, build) {
            for entry in &build.entries {
                take(entry, shard, profile)?;
            }
            joined.taken = joined.taken.saturating_add(1);
        }
    }
    Ok(joined)
}

/// The builds of every unit in the profile directory `directory`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one build per unit hash the directory's entries carry, each with
///   its entries and, when whole, its fingerprint.
/// - provides: one source of a join.
/// - fails: [`BuildStateError::Io`] as [`unit_entries`] fails, a missing
///   directory included, and as [`whole`] fails.
/// - panics: none.
/// - executable: none — the outcome is the directory listing.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — as [`join`].
/// - witness: `join::tests::a_unit_two_shards_build_comes_whole_from_the_first_7508`
/// - witness: `join::tests::a_missing_profile_is_refused_7508`
fn builds(directory: &Path) -> Result<BTreeMap<UnitHash, Build>, BuildStateError>
{
    let target = directory.parent().unwrap_or(directory);
    let mut grouped: BTreeMap<UnitHash, Vec<PathBuf>> = BTreeMap::new();
    for (path, hash) in unit_entries(directory)? {
        grouped.entry(hash).or_default().push(path);
    }
    let mut builds = BTreeMap::new();
    for (hash, entries) in grouped {
        let whole = whole(target, &entries)?;
        builds.insert(hash, Build { entries, whole });
    }
    Ok(builds)
}

/// The fingerprint of the unit whose entries are `entries`, when the unit
/// holds it and its outputs.
///
/// # Specification
/// - requires: `target` the directory that the fingerprint's paths are relative
///   to, the parent of the profile directory.
/// - ensures: `Some` exactly when the unit has one fingerprint directory
///   holding one JSON and its value, each file its local inputs name exists,
///   and a unit that compiles holds an output that is not its dependency file.
/// - provides: whether a build may cross the join, and what it names.
/// - fails: [`BuildStateError::Io`] when a fingerprint file exists and cannot
///   be read, or a directory cannot be listed.
/// - panics: none.
/// - executable: none — the outcome depends on the files on disk.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — as [`join`].
/// - witness: `join::tests::a_unit_without_its_outputs_leaves_with_its_dependents_7508`
fn whole(
    target: &Path,
    entries: &[PathBuf],
) -> Result<Option<Fingerprint>, BuildStateError>
{
    let mut directories = Vec::new();
    for entry in entries {
        let inside = entry.join("fingerprint");
        if inside.is_dir() {
            directories.push(inside);
        }
        else if entry.is_dir()
            && entry
                .parent()
                .and_then(Path::file_name)
                .is_some_and(|name| name == ".fingerprint")
        {
            directories.push(entry.clone());
        }
    }
    let &[ref directory] = directories.as_slice()
    else {
        return Ok(None);
    };
    let mut json = None;
    for file in fs::read_dir(directory).map_err(|error| io(directory, &error))? {
        let path = file.map_err(|error| io(directory, &error))?.path();
        if path
            .extension()
            .is_some_and(|extension| extension == "json")
        {
            if json.is_some() {
                return Ok(None);
            }
            json = Some(path);
        }
    }
    let Some(json) = json
    else {
        return Ok(None);
    };
    let Some(value) = read(&json.with_extension(""))?.and_then(|text| text.parse::<Value>().ok())
    else {
        return Ok(None);
    };
    let Some(recorded) = read(&json)?.and_then(|text| serde_json::from_str::<Recorded>(&text).ok())
    else {
        return Ok(None);
    };
    let mut compiles = false;
    for local in &recorded.local {
        let compile = local
            .get("CheckDepInfo")
            .map(|dep_info| dep_info.get("dep_info"));
        compiles |= compile.is_some();
        let named = compile.unwrap_or_else(|| {
            let rerun = local.get("RerunIfChanged")?;
            rerun.get("output")
        });
        if let Some(path) = named.and_then(serde_json::Value::as_str)
            && !target.join(path).exists()
        {
            return Ok(None);
        }
    }
    if compiles && output_in(entries)?.is_none() {
        return Ok(None);
    }
    Ok(Some(Fingerprint {
        value,
        dependencies: recorded
            .deps
            .into_iter()
            .map(|(_, _, _, value)| Value(value))
            .collect(),
    }))
}

/// The output that the entries of a unit that compiles hold: a file other
/// than a dependency file, in a unit directory's `out` or among the entries.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Some` exactly when one entry, or one file of an entry's `out`
///   directory, is a file whose name does not end in `.d`, holding the first
///   such file.
/// - provides: the outputs half of a whole unit.
/// - fails: [`BuildStateError::Io`] when an `out` directory exists and cannot
///   be listed.
/// - panics: none.
/// - executable: none — the outcome depends on the files on disk.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — as [`join`].
/// - witness: `join::tests::a_unit_without_its_outputs_leaves_with_its_dependents_7508`
fn output_in(entries: &[PathBuf]) -> Result<Option<PathBuf>, BuildStateError>
{
    let output =
        |path: &Path| path.is_file() && path.extension().is_none_or(|extension| extension != "d");
    for entry in entries {
        if output(entry) {
            return Ok(Some(entry.clone()));
        }
        let out = entry.join("out");
        let listing = match fs::read_dir(&out) {
            Ok(listing) => listing,
            Err(error)
                if matches!(
                    error.kind(),
                    io::ErrorKind::NotFound | io::ErrorKind::NotADirectory
                ) =>
            {
                continue;
            },
            Err(error) => return Err(io(&out, &error)),
        };
        for file in listing {
            let path = file.map_err(|error| io(&out, &error))?.path();
            if output(&path) {
                return Ok(Some(path));
            }
        }
    }
    Ok(None)
}

/// The text of the file at `path`, or `None` when no file is there.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Some` with the file's text when it reads as UTF-8; `None` when
///   nothing is at `path` or the text is not UTF-8.
/// - provides: a fingerprint file read, absent when the unit lacks it.
/// - fails: [`BuildStateError::Io`] for any other read failure.
/// - panics: none.
/// - executable: none — the outcome depends on the file on disk.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — as [`join`].
/// - witness: `join::tests::a_unit_without_its_outputs_leaves_with_its_dependents_7508`
fn read(path: &Path) -> Result<Option<String>, BuildStateError>
{
    match fs::read_to_string(path) {
        Ok(text) => Ok(Some(text)),
        Err(error)
            if matches!(
                error.kind(),
                io::ErrorKind::NotFound | io::ErrorKind::InvalidData
            ) =>
        {
            Ok(None)
        },
        Err(error) => Err(io(path, &error)),
    }
}

/// Moves `entry` out of the shard `shard` to its path in `profile`.
///
/// # Specification
/// - requires: `entry` below `shard`; `shard` and `profile` on one file system.
/// - ensures: on success `entry` is at its path relative to `shard` below
///   `profile`, with its parent directories made, and absent from `shard`.
/// - provides: the move of a kept shard build into the state, without a copy.
/// - fails: [`BuildStateError::Io`] when `entry` is not below `shard`, or a
///   directory cannot be made or the entry moved.
/// - panics: none.
/// - executable: none — the outcome is the directories on disk.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — as [`join`].
/// - witness: `join::tests::a_unit_two_shards_build_comes_whole_from_the_first_7508`
fn take(
    entry: &Path,
    shard: &Path,
    profile: &Path,
) -> Result<(), BuildStateError>
{
    let relative = entry
        .strip_prefix(shard)
        .map_err(|error| BuildStateError::Io {
            path: entry.to_owned(),
            message: format!("not below the shard {}: {error}", shard.display()),
        })?;
    let destination = profile.join(relative);
    if let Some(parent) = destination.parent() {
        fs::create_dir_all(parent).map_err(|error| io(parent, &error))?;
    }
    fs::rename(entry, &destination).map_err(|error| io(entry, &error))
}

#[cfg(test)]
mod tests
{
    use std::fs;
    use std::path::Path;
    use std::path::PathBuf;

    use super::Value;
    use super::join;
    use crate::error::BuildStateError;

    /// A fresh directory for one test, named after it.
    ///
    /// # Specification
    /// trivial.
    fn scratch(name: &Path) -> PathBuf
    {
        let root = std::env::temp_dir()
            .join(format!("build-state-{}", std::process::id()))
            .join(name);
        if root.exists() {
            fs::remove_dir_all(&root).unwrap();
        }
        fs::create_dir_all(&root).unwrap();
        root
    }

    /// A library unit of the new layout, as a test writes it into a profile.
    #[derive(Clone, Copy)]
    struct Library<'fixture>
    {
        /// The package, which names the unit's directory.
        package: &'fixture str,
        /// The unit hash.
        hash: &'fixture str,
        /// The value of the unit's fingerprint.
        value: u64,
        /// The values of the fingerprints the unit names as its dependencies.
        dependencies: &'fixture [u64],
        /// Whether the unit holds its library.
        outputs: bool,
        /// What the library holds, so a test tells two builds apart.
        marker: &'fixture str,
    }

    impl Library<'_>
    {
        /// Writes the unit under `profile`: its fingerprint and its value as
        /// Cargo writes them, its dependency file, and its library unless the
        /// unit has no outputs.
        ///
        /// # Specification
        /// trivial.
        fn write(
            &self,
            profile: &Path,
        )
        {
            let unit = profile.join("build").join(self.package).join(self.hash);
            let fingerprint = unit.join("fingerprint");
            fs::create_dir_all(&fingerprint).unwrap();
            let crate_name = self.package.replace('-', "_");
            let deps: Vec<String> = self
                .dependencies
                .iter()
                .map(|value| format!("[1,\"dependency\",false,{value}]"))
                .collect();
            let dep_info = format!(
                "debug/build/{}/{}/fingerprint/dep-lib-{crate_name}",
                self.package, self.hash
            );
            fs::write(
                fingerprint.join(format!("lib-{crate_name}.json")),
                format!(
                    "{{\"rustc\":1,\"deps\":[{}],\"local\":[{{\"CheckDepInfo\":{{\"dep_info\":\"{dep_info}\",\"checksum\":false}}}}]}}",
                    deps.join(",")
                ),
            )
            .unwrap();
            fs::write(
                fingerprint.join(format!("lib-{crate_name}")),
                format!("{:016x}", self.value.swap_bytes()),
            )
            .unwrap();
            fs::write(
                fingerprint.join(format!("dep-lib-{crate_name}")),
                "dependencies",
            )
            .unwrap();
            let out = unit.join("out");
            fs::create_dir_all(&out).unwrap();
            fs::write(out.join(format!("{crate_name}-{}.d", self.hash)), "sources").unwrap();
            if self.outputs {
                fs::write(
                    out.join(format!("lib{crate_name}-{}.rmeta", self.hash)),
                    self.marker,
                )
                .unwrap();
            }
        }

        /// The marker the unit's library holds in `profile`, or `None` when
        /// the unit is gone from it.
        ///
        /// # Specification
        /// trivial.
        fn marker_in(
            &self,
            profile: &Path,
        ) -> Option<String>
        {
            let unit = profile.join("build").join(self.package).join(self.hash);
            if !unit.exists() {
                return None;
            }
            let crate_name = self.package.replace('-', "_");
            Some(
                fs::read_to_string(
                    unit.join("out")
                        .join(format!("lib{crate_name}-{}.rmeta", self.hash)),
                )
                .unwrap(),
            )
        }
    }

    #[test]
    fn a_unit_two_shards_build_comes_whole_from_the_first_7508()
    {
        let root = scratch(Path::new("join-whole"));
        let (profile, first, second) = (
            root.join("debug"),
            root.join("a/debug"),
            root.join("b/debug"),
        );
        fs::create_dir_all(&profile).unwrap();
        let untouched = Library {
            package: "untouched",
            hash: "00000000000000c1",
            value: 7,
            dependencies: &[],
            outputs: true,
            marker: "restored",
        };
        let shared = Library {
            package: "shared",
            hash: "00000000000000a1",
            value: 11,
            marker: "first",
            ..untouched
        };
        let own = Library {
            package: "own",
            hash: "00000000000000b1",
            value: 13,
            marker: "second",
            ..untouched
        };
        untouched.write(&profile);
        shared.write(&first);
        Library {
            value: 12,
            marker: "second",
            ..shared
        }
        .write(&second);
        own.write(&second);
        let joined = join(&profile, &[first.clone(), second]).unwrap();
        assert_eq!(shared.marker_in(&profile).as_deref(), Some("first"));
        let fingerprint = profile.join("build/shared/00000000000000a1/fingerprint/lib-shared");
        assert_eq!(
            fs::read_to_string(fingerprint).unwrap(),
            format!("{:016x}", 11_u64.swap_bytes())
        );
        assert_eq!(own.marker_in(&profile).as_deref(), Some("second"));
        assert_eq!(untouched.marker_in(&profile).as_deref(), Some("restored"));
        assert!(
            !first.join("build/shared/00000000000000a1").exists(),
            "the kept build moves"
        );
        assert_eq!((joined.restored, joined.taken, joined.dropped), (1, 2, 0));
    }

    #[test]
    fn a_dependent_of_another_build_leaves_with_its_dependents_7508()
    {
        let root = scratch(Path::new("join-mixed"));
        let (profile, first, second) = (
            root.join("debug"),
            root.join("a/debug"),
            root.join("b/debug"),
        );
        fs::create_dir_all(&profile).unwrap();
        // The restored state: a base unit and a dependent compiled against
        // it, and a second pair that no shard touches.
        let base = Library {
            package: "base",
            hash: "00000000000000d1",
            value: 21,
            dependencies: &[],
            outputs: true,
            marker: "restored",
        };
        let above = Library {
            package: "above",
            hash: "00000000000000d2",
            value: 22,
            dependencies: &[21],
            ..base
        };
        let beside = Library {
            package: "beside",
            hash: "00000000000000d3",
            value: 23,
            ..base
        };
        let over_beside = Library {
            package: "over-beside",
            hash: "00000000000000d4",
            value: 24,
            dependencies: &[23],
            ..base
        };
        for unit in [base, above, beside, over_beside] {
            unit.write(&profile);
        }
        // The first shard rebuilds the base; the second builds it differently,
        // with a dependent on its own build and a dependent of that. The
        // second shard's unit on the untouched restored unit stays.
        let mixed = Library {
            package: "mixed",
            hash: "00000000000000e1",
            value: 33,
            dependencies: &[32],
            marker: "second",
            ..base
        };
        let over_mixed = Library {
            package: "over-mixed",
            hash: "00000000000000e2",
            value: 34,
            dependencies: &[33],
            ..mixed
        };
        let on_beside = Library {
            package: "on-beside",
            hash: "00000000000000e3",
            value: 35,
            dependencies: &[23],
            ..mixed
        };
        Library {
            value: 31,
            marker: "first",
            ..base
        }
        .write(&first);
        for unit in [
            Library {
                value: 32,
                marker: "second",
                ..base
            },
            mixed,
            over_mixed,
            on_beside,
        ] {
            unit.write(&second);
        }
        let joined = join(&profile, &[first, second]).unwrap();
        assert_eq!(base.marker_in(&profile).as_deref(), Some("first"));
        assert_eq!(
            mixed.marker_in(&profile),
            None,
            "compiled against another build"
        );
        assert_eq!(
            over_mixed.marker_in(&profile),
            None,
            "depends on a dropped unit"
        );
        assert_eq!(
            above.marker_in(&profile),
            None,
            "its restored dependency is replaced"
        );
        assert_eq!(beside.marker_in(&profile).as_deref(), Some("restored"));
        assert_eq!(over_beside.marker_in(&profile).as_deref(), Some("restored"));
        assert_eq!(on_beside.marker_in(&profile).as_deref(), Some("second"));
        assert_eq!((joined.restored, joined.taken, joined.dropped), (2, 2, 3));
    }

    #[test]
    fn a_unit_without_its_outputs_leaves_with_its_dependents_7508()
    {
        let root = scratch(Path::new("join-partial"));
        let (profile, shard) = (root.join("debug"), root.join("a/debug"));
        fs::create_dir_all(&profile).unwrap();
        let partial = Library {
            package: "partial",
            hash: "00000000000000f1",
            value: 41,
            dependencies: &[],
            outputs: false,
            marker: "shard",
        };
        let over_partial = Library {
            package: "over-partial",
            hash: "00000000000000f2",
            value: 42,
            dependencies: &[41],
            outputs: true,
            ..partial
        };
        let unprinted = Library {
            package: "unprinted",
            hash: "00000000000000f3",
            value: 43,
            dependencies: &[],
            ..over_partial
        };
        let undescribed = Library {
            package: "undescribed",
            hash: "00000000000000f4",
            value: 44,
            ..unprinted
        };
        for unit in [partial, over_partial, unprinted, undescribed] {
            unit.write(&shard);
        }
        fs::remove_file(shard.join("build/unprinted/00000000000000f3/fingerprint/lib-unprinted"))
            .unwrap();
        fs::remove_file(
            shard.join("build/undescribed/00000000000000f4/fingerprint/dep-lib-undescribed"),
        )
        .unwrap();
        fs::create_dir_all(shard.join("build/empty/00000000000000f5/out")).unwrap();
        let joined = join(&profile, &[shard]).unwrap();
        for unit in [partial, over_partial, unprinted, undescribed] {
            assert_eq!(unit.marker_in(&profile), None, "{} leaves", unit.package);
        }
        assert!(
            !profile.join("build/empty/00000000000000f5").exists(),
            "a unit without a fingerprint leaves"
        );
        assert_eq!((joined.restored, joined.taken, joined.dropped), (0, 0, 5));
    }

    #[test]
    fn a_missing_profile_is_refused_7508()
    {
        let root = scratch(Path::new("join-missing"));
        let refused = join(&root.join("debug"), &[root.join("a/debug")]);
        assert!(
            matches!(refused, Err(BuildStateError::Io { .. })),
            "{refused:?}"
        );
    }

    #[test]
    fn a_value_reads_as_cargo_writes_it_7508()
    {
        // A fingerprint's value file from a real build, and the decimal its
        // dependent's JSON records for it.
        assert_eq!(
            "82362a45a64875f8\n".parse::<Value>(),
            Ok(Value(17_903_295_772_643_440_258_u64))
        );
        assert_eq!("82362a45a64875".parse::<Value>(), Err(()));
        assert_eq!("82362a45a64875fz".parse::<Value>(), Err(()));
    }
}
