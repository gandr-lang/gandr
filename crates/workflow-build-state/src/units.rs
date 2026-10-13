//! The units a build used, read from Cargo's JSON messages.
//!
//! Cargo names every file and directory a unit writes with the unit's hash:
//! `libname-<hash>.rlib` and `name-<hash>` under `deps`, `name-<hash>` under
//! `.fingerprint`, `build` and `examples`. The hash covers the package, its
//! features, the profile and the hashes of its dependencies, never its
//! source, so an edit rebuilds a unit in place while a changed dependency or
//! feature set writes a unit under a new hash beside the old one. A build's
//! `compiler-artifact` messages name every unit it used, fresh ones
//! included, and its `build-script-executed` messages every build-script
//! output directory.

extern crate alloc;

use alloc::collections::BTreeSet;
use core::str::FromStr;
use std::path::Path;
use std::path::PathBuf;

use serde::Deserialize;

use crate::error::BuildStateError;

/// The hexadecimal digits of a unit hash.
const HASH_DIGITS: usize = 16;

/// The hash Cargo appends to the name of every file and directory a unit
/// writes.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct UnitHash(u64);

/// Why a name carries no unit hash.
///
/// # Specification
/// - provides: the one reason a name belongs to no single unit.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Unhashed
{
    /// No `-` in the name is followed by sixteen lowercase hexadecimal digits
    /// that end the name or precede a `.`: an output Cargo copied out under
    /// its plain name, a lock file, or a directory units share.
    Unnamed,
}

impl FromStr for UnitHash
{
    type Err = Unhashed;

    /// The unit hash `name` carries: the last `-` followed by sixteen
    /// lowercase hexadecimal digits that end the name or precede a `.`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Ok` exactly when such a `-` exists, holding the digits'
    ///   value; the extension after the digits does not matter, so a unit's
    ///   `.rlib`, `.rmeta`, `.d` and executable share one hash.
    /// - provides: the unit a file or directory of a profile directory belongs
    ///   to.
    /// - fails: [`Unhashed::Unnamed`] when no such `-` exists.
    /// - panics: none.
    /// - executable: none — the outcome is the parse itself.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — library, executable, dependency-information and
    ///   directory names, a name whose dash is followed by fifteen or seventeen
    ///   digits, uppercase digits, and a package name holding dashes; taking
    ///   the first dash, ignoring the length or accepting uppercase changes a
    ///   parsed hash.
    /// - witness: `units::tests::a_hash_is_read_from_every_unit_name`
    #[inline]
    fn from_str(name: &str) -> Result<Self, Self::Err>
    {
        for (dash, _) in name.rmatch_indices('-') {
            let start = dash.saturating_add(1);
            let end = start.saturating_add(HASH_DIGITS);
            let Some(digits) = name.get(start .. end)
            else {
                continue;
            };
            let ends_stem = name
                .get(end ..)
                .is_some_and(|after| after.is_empty() || after.starts_with('.'));
            let lower_hex = digits
                .bytes()
                .all(|byte| byte.is_ascii_digit() || (b'a' ..= b'f').contains(&byte));
            if !(ends_stem && lower_hex) {
                continue;
            }
            if let Ok(value) = u64::from_str_radix(digits, 16) {
                return Ok(Self(value));
            }
        }
        Err(Unhashed::Unnamed)
    }
}

/// The text of one build's JSON messages, one message per line.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Messages<'text>(&'text str);

impl<'text> From<&'text str> for Messages<'text>
{
    /// Reads `text` as a build's messages.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(text: &'text str) -> Self
    {
        Self(text)
    }
}

/// One Cargo JSON message, as far as a prune reads it.
#[derive(Debug, Deserialize)]
#[serde(tag = "reason")]
enum Message
{
    /// A unit compiled or found fresh, with the files it produced.
    #[serde(rename = "compiler-artifact")]
    Artifact
    {
        /// Every file the unit produced, or the plain-named copy Cargo made
        /// of an executable.
        filenames: Vec<String>,
    },
    /// A build script run, with the directory it wrote.
    #[serde(rename = "build-script-executed")]
    BuildScript
    {
        /// The run's output directory.
        out_dir: String,
    },
    /// The end of the build.
    #[serde(rename = "build-finished")]
    Finished
    {
        /// Whether every unit built.
        success: bool,
    },
    /// Any other message: diagnostics and timings name no unit.
    #[serde(other)]
    Other,
}

/// The units one or more builds used: the unit hashes their messages name,
/// and the plain-named copies Cargo made of executables, whose unit a prune
/// finds on disk.
///
/// # Specification
/// - provides: the set a prune keeps; reading a second build's messages adds
///   its units, so one prune serves every build a directory holds.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Units
{
    /// The hashes the messages name.
    hashes: BTreeSet<UnitHash>,
    /// The paths that name no hash: copies of a unit's executable.
    uplifted: BTreeSet<PathBuf>,
}

impl Units
{
    /// Adds the units of one build's messages, read from `path`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success every hash a `compiler-artifact` file name or a
    ///   `build-script-executed` output directory carries, in its own name or
    ///   its parent directory's, is in the set, and every such path carrying
    ///   none is an uplifted path; on failure the set may hold part of the
    ///   file's units.
    /// - provides: the keep set of one build.
    /// - fails: [`BuildStateError::Json`] at the first line that is not a JSON
    ///   message; [`BuildStateError::Unfinished`] when no line is
    ///   `build-finished`; [`BuildStateError::Failed`] when the build failed.
    /// - panics: none.
    /// - executable: none — the hashes a message names are the parse itself.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a library, a test executable, a build script, an
    ///   uplifted binary and a diagnostic, then a truncated file, a failed
    ///   build and a malformed line; dropping the parent directory, the uplift
    ///   or the end check changes the set or the verdict.
    /// - witness: `units::tests::a_build_names_its_units`
    /// - witness: `units::tests::an_incomplete_or_failed_build_is_refused`
    #[inline]
    pub fn read(
        &mut self,
        path: &Path,
        messages: Messages<'_>,
    ) -> Result<(), BuildStateError>
    {
        let mut finished = None;
        for (index, line) in messages.0.lines().enumerate() {
            if line.trim().is_empty() {
                continue;
            }
            let message: Message =
                serde_json::from_str(line).map_err(|error| BuildStateError::Json {
                    path: path.to_owned(),
                    line: index.saturating_add(1),
                    message: error.to_string(),
                })?;
            match message {
                | Message::Artifact { filenames } => {
                    for file in filenames {
                        self.insert(PathBuf::from(file));
                    }
                },
                | Message::BuildScript { out_dir } => self.insert(PathBuf::from(out_dir)),
                | Message::Finished { success } => finished = Some(success),
                | Message::Other => {},
            }
        }
        match finished {
            | Some(true) => Ok(()),
            | Some(false) => Err(BuildStateError::Failed {
                path: path.to_owned(),
            }),
            | None => Err(BuildStateError::Unfinished {
                path: path.to_owned(),
            }),
        }
    }

    /// Records the unit `path` belongs to.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the hash the file's name carries, else its parent
    ///   directory's, is in the set; a path carrying neither is uplifted.
    /// - provides: the one place a message's path becomes a unit.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the outcome is the set itself.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Units::read`].
    /// - witness: `units::tests::a_build_names_its_units`
    #[inline]
    fn insert(
        &mut self,
        path: PathBuf,
    )
    {
        let named = [path.file_name(), path.parent().and_then(Path::file_name)]
            .into_iter()
            .flatten()
            .filter_map(|name| name.to_str())
            .find_map(|name| name.parse::<UnitHash>().ok());
        match named {
            | Some(hash) => {
                self.hashes.insert(hash);
            },
            | None => {
                self.uplifted.insert(path);
            },
        }
    }

    /// The unit hashes the messages named.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: every hash read, in order.
    /// - provides: the keep set of a prune, before the uplifted copies' units
    ///   join it.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the set itself.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Units::read`].
    /// - witness: `units::tests::a_build_names_its_units`
    #[inline]
    #[must_use]
    pub const fn hashes(&self) -> &BTreeSet<UnitHash>
    {
        &self.hashes
    }

    /// The paths a build named without a hash: the plain-named copies Cargo
    /// made of executables and examples.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: every uplifted path read, in path order.
    /// - provides: the copies whose units a prune finds on disk.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the iterator is the set itself.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Units::read`].
    /// - witness: `units::tests::a_build_names_its_units`
    #[inline]
    pub fn uplifted(&self) -> impl Iterator<Item = &Path>
    {
        self.uplifted.iter().map(PathBuf::as_path)
    }
}

#[cfg(test)]
mod tests
{
    use std::path::Path;

    use super::Messages;
    use super::Unhashed;
    use super::UnitHash;
    use super::Units;
    use crate::error::BuildStateError;

    /// A build of a library, its test executable, a build script, the
    /// driver binary and a diagnostic, as Cargo writes its messages.
    const BUILD: &str = concat!(
        r#"{"reason":"compiler-artifact","package_id":"a","filenames":["/t/debug/deps/liba-00000000000000a1.rlib","/t/debug/deps/liba-00000000000000a1.rmeta"],"executable":null,"fresh":true}"#,
        "\n",
        r#"{"reason":"compiler-artifact","package_id":"a","filenames":["/t/debug/deps/a-00000000000000a2"],"executable":"/t/debug/deps/a-00000000000000a2","fresh":false}"#,
        "\n",
        r#"{"reason":"compiler-artifact","package_id":"b","filenames":["/t/debug/build/b-00000000000000b1/build-script-build"],"executable":null,"fresh":true}"#,
        "\n",
        r#"{"reason":"build-script-executed","package_id":"b","out_dir":"/t/debug/build/b-00000000000000b2/out"}"#,
        "\n",
        r#"{"reason":"compiler-artifact","package_id":"c","filenames":["/t/debug/gandr"],"executable":"/t/debug/gandr","fresh":true}"#,
        "\n",
        r#"{"reason":"compiler-message","package_id":"c","message":{}}"#,
        "\n\n",
        r#"{"reason":"build-finished","success":true}"#,
        "\n",
    );

    #[test]
    fn a_hash_is_read_from_every_unit_name()
    {
        let one = "x-0123456789abcdef".parse::<UnitHash>();
        assert!(one.is_ok());
        for name in [
            "libgandr_core_term-0123456789abcdef.rlib",
            "libgandr_core_term-0123456789abcdef.rmeta",
            "gandr_core_term-0123456789abcdef.d",
            "gandr_core_term-0123456789abcdef",
            "gandr-core-term-0123456789abcdef",
            "lib-ffffffffffffffff-0123456789abcdef.so",
        ] {
            assert_eq!(name.parse::<UnitHash>(), one, "{name}");
        }
        for name in [
            "gandr",
            "gandr.d",
            ".cargo-lock",
            "a-0123456789abcde",
            "a-0123456789abcdef0",
            "a-0123456789ABCDEF",
            "a-0123456789abcdefx",
            "a-0123456789abcdeg.rlib",
        ] {
            assert_eq!(name.parse::<UnitHash>(), Err(Unhashed::Unnamed), "{name}");
        }
    }

    #[test]
    fn a_build_names_its_units()
    {
        let mut units = Units::default();
        units
            .read(Path::new("units.jsonl"), Messages::from(BUILD))
            .unwrap();
        let named = |digits: &str| {
            let hash = format!("x-{digits}").parse::<UnitHash>().unwrap();
            units.hashes().contains(&hash)
        };
        for digits in [
            "00000000000000a1",
            "00000000000000a2",
            "00000000000000b1",
            "00000000000000b2",
        ] {
            assert!(named(digits), "{digits}");
        }
        assert!(!named("00000000000000c1"));
        assert_eq!(units.hashes().len(), 4);
        assert_eq!(units.uplifted().collect::<Vec<_>>(), [Path::new(
            "/t/debug/gandr"
        )]);
    }

    #[test]
    fn an_incomplete_or_failed_build_is_refused()
    {
        let path = Path::new("units.jsonl");
        let read = |text: &str| Units::default().read(path, Messages::from(text));
        let unfinished = BUILD.replace(r#"{"reason":"build-finished","success":true}"#, "");
        assert_eq!(
            read(&unfinished),
            Err(BuildStateError::Unfinished {
                path: path.to_owned()
            })
        );
        let failed = BUILD.replace(r#""success":true"#, r#""success":false"#);
        assert_eq!(
            read(&failed),
            Err(BuildStateError::Failed {
                path: path.to_owned()
            })
        );
        let malformed = format!("{BUILD}not json\n");
        assert!(matches!(
            read(&malformed),
            Err(BuildStateError::Json { line: 9, .. })
        ));
    }
}
