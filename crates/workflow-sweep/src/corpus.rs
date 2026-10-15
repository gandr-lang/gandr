//! The corpus a sweep draws from: every source under the strict and fixture
//! roots, each with its name and its class.

use core::fmt;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;

use crate::error::SweepError;

/// The corpus crate's directory, beside this one in the workspace.
const CORPUS: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../surface-corpus");

/// The two roots a source sits under, as the dispatcher's walk names them.
const ROOTS: [&str; 2] = ["strict", "fixture"];

/// A source's path below the corpus crate, `/`-separated:
/// `strict/values.gandr`, `fixture/model/identity/circle.gandr`. The name a
/// sample ranks, a change lists and a failure prints.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CorpusName(String);

impl CorpusName
{
    /// The name as text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn as_str(&self) -> &str
    {
        &self.0
    }
}

impl From<&str> for CorpusName
{
    /// The name spelled `name`, `/`-separated below the corpus crate.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(name: &str) -> Self
    {
        Self(name.to_owned())
    }
}

impl fmt::Display for CorpusName
{
    /// Writes the name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(&self.0)
    }
}

/// The class a source belongs to by where it sits.
///
/// The class is `strict`, or the directory below `fixture` —
/// `fixture/model`, `fixture/pending` — or `fixture` for a source directly
/// under that root. Membership is location, so the classes are the corpus's
/// own: the gating root, each family of settled fixtures, and the pending set
/// the lowering refuses.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Class(String);

impl Class
{
    /// The class of the source named `name`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `strict` for a name under the strict root; the root and the
    ///   first directory below it for a name under the fixture root that sits
    ///   in a directory; the first component alone otherwise.
    /// - provides: the stratum a sample keeps at least one source of.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a strict source in a subdirectory, a fixture source
    ///   two directories deep, and a fixture source directly under the root;
    ///   splitting strict by directory, keeping the whole directory path, or
    ///   dropping the root changes a class.
    /// - witness: `corpus::tests::a_class_is_the_directory_below_its_root`
    #[spec(ensures: |ret| name.as_str().starts_with(ret.0.as_str()))]
    #[inline]
    #[must_use]
    pub fn of(name: &CorpusName) -> Self
    {
        let mut parts = name.as_str().split('/');
        let root = parts.next().unwrap_or_default();
        let below: Vec<&str> = parts.collect();
        match (root, below.as_slice()) {
            ("fixture", &[directory, _, ..]) => Self(format!("{root}/{directory}")),
            _ => Self(root.to_owned()),
        }
    }
}

impl fmt::Display for Class
{
    /// Writes the class.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(&self.0)
    }
}

/// One corpus source: where it is on disk, its name and its class.
///
/// # Specification
/// - provides: a sweep's unit of work; `class` is [`Class::of`] the name and
///   `path` the canonical path the name stands for.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Source
{
    /// The canonical path of the source.
    pub path: PathBuf,
    /// Its name below the corpus crate.
    pub name: CorpusName,
    /// Its class.
    pub class: Class,
}

/// The corpus crate's directory, canonical.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the canonical path of `crates/surface-corpus` in the workspace
///   this crate was built in.
/// - provides: the directory the walk starts from and `git` runs in.
/// - fails: [`SweepError::Walk`] when the directory cannot be resolved.
/// - panics: none.
/// - executable: none — the outcome is the file system's.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — the walk below starts here; a wrong directory reaches no
///   strict source and fails its witness.
/// - witness: `corpus::tests::the_walk_reaches_every_class_in_name_order`
#[inline]
pub fn directory() -> Result<PathBuf, SweepError>
{
    Path::new(CORPUS)
        .canonicalize()
        .map_err(|error| SweepError::Walk {
            path: PathBuf::from(CORPUS),
            detail: error.to_string(),
        })
}

/// Every source under the corpus's strict and fixture roots, in name order.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one source per `.gandr` file under `strict/` and `fixture/`,
///   reached without following a symbolic link — the dispatcher walk's rule —
///   each named by its path below the corpus crate, sorted by name.
/// - provides: the candidates a sweep samples.
/// - fails: [`SweepError::Walk`] when the corpus directory, one of its
///   directories or one of their entries cannot be read.
/// - panics: none.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — the corpus holds strict sources, fixture sources two
///   directories deep and the pending set; a shallow walk, a walk of one root,
///   or an unsorted result fails the witness.
/// - witness: `corpus::tests::the_walk_reaches_every_class_in_name_order`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |sources| sources.is_sorted_by(|left, right| left.name < right.name) && sources.iter().all(|source| Class::of(&source.name) == source.class)))]
#[inline]
pub fn sources() -> Result<Vec<Source>, SweepError>
{
    let corpus = directory()?;
    let mut pending: Vec<PathBuf> = ROOTS.iter().map(|root| corpus.join(root)).collect();
    let mut found = Vec::new();
    while let Some(at) = pending.pop() {
        let unreadable = |error: std::io::Error| SweepError::Walk {
            path: at.clone(),
            detail: error.to_string(),
        };
        for entry in std::fs::read_dir(&at).map_err(unreadable)? {
            let entry = entry.map_err(unreadable)?;
            let kind = entry.file_type().map_err(unreadable)?;
            let path = entry.path();
            if kind.is_dir() {
                pending.push(path);
            }
            else if !kind.is_symlink()
                && path
                    .extension()
                    .is_some_and(|extension| extension == "gandr")
            {
                let below = path
                    .strip_prefix(&corpus)
                    .map_err(|error| SweepError::Walk {
                        path: path.clone(),
                        detail: error.to_string(),
                    })?;
                let parts: Vec<String> = below
                    .components()
                    .map(|part| part.as_os_str().to_string_lossy().into_owned())
                    .collect();
                let name = CorpusName(parts.join("/"));
                let class = Class::of(&name);
                found.push(Source { path, name, class });
            }
        }
    }
    found.sort_by(|left, right| left.name.cmp(&right.name));
    Ok(found)
}

#[cfg(test)]
mod tests
{
    use alloc::collections::BTreeSet;

    use super::Class;
    use super::CorpusName;
    use super::sources;

    #[test]
    fn a_class_is_the_directory_below_its_root()
    {
        for (name, class) in [
            ("strict/values.gandr", "strict"),
            ("strict/classifier/relative-monad.gandr", "strict"),
            ("fixture/model/identity/circle.gandr", "fixture/model"),
            ("fixture/pending/records.gandr", "fixture/pending"),
            ("fixture/loose.gandr", "fixture"),
        ] {
            assert_eq!(
                Class::of(&CorpusName::from(name)).to_string(),
                class,
                "{name}"
            );
        }
    }

    #[test]
    fn the_walk_reaches_every_class_in_name_order()
    {
        let found = sources().expect("the corpus reads");
        let classes: BTreeSet<String> = found
            .iter()
            .map(|source| source.class.to_string())
            .collect();
        for class in [
            "strict",
            "fixture/fragment",
            "fixture/model",
            "fixture/pathological",
            "fixture/pending",
        ] {
            assert!(classes.contains(class), "{class} in {classes:?}");
        }
        assert!(
            found
                .iter()
                .any(|source| source.name.as_str().matches('/').count() > 2),
            "a source two directories below its root is reached"
        );
        assert!(
            found
                .windows(2)
                .all(|pair| matches!(pair, [left, right] if left.name < right.name)),
            "the sources are in name order"
        );
        assert!(
            found
                .iter()
                .all(|source| source.path.ends_with(source.name.as_str())),
            "each path is the source its name stands for"
        );
    }
}
