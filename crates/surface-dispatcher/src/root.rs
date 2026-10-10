//! Which root a source sits under, decided by its path.
//!
//! # Membership is location
//!
//! A source is gated or asserted by the directory it sits in, never by what it
//! says about itself: a declaration under the strict root cannot describe its
//! way out of the gate, because moving it is a change to its path that a
//! reviewer sees. The innermost root directory a source sits under decides.

use std::ffi::OsStr;
use std::path::Path;

use gandr_surface_corpus::CorpusRoot;

/// The directory name of the strict root.
const STRICT: &str = "strict";

/// The directory name of the fixture root.
const FIXTURE: &str = "fixture";

/// The directory name of the pending set, directly inside a fixture root.
const PENDING: &str = "pending";

/// The root a source sits under.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum SourceRoot
{
    /// Under a `strict` directory, or under no root at all: every declaration
    /// is held to *checks, owing nothing*, and `owes` and `refuses` are
    /// refused.
    Strict,
    /// Under a `fixture` directory: the three expectation schemas are
    /// admitted.
    Fixture,
    /// Under the `pending` directory directly inside a fixture root: the
    /// lowering is expected to refuse the source as a whole, as outside the
    /// fragment, before any declaration exists to carry an expectation.
    Pending,
}

impl SourceRoot
{
    /// The corpus root the source's declarations are settled under.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the strict root settles under [`CorpusRoot::Strict`]; the
    ///   fixture root and its pending set under [`CorpusRoot::Fixture`].
    /// - provides: the root `settle` reads, so a pending source the lowering
    ///   does read is settled as a fixture source would be.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — three roots, enumerated against their corpus roots.
    /// - witness: `root::tests::each_root_settles_under_its_corpus_root`
    #[inline]
    #[must_use]
    #[anodized::spec(ensures: |ret| matches!((self, ret),
        (Self::Strict, CorpusRoot::Strict)
            | (Self::Fixture | Self::Pending, CorpusRoot::Fixture),
    ))]
    pub const fn corpus_root(self) -> CorpusRoot
    {
        match self {
            | Self::Strict => CorpusRoot::Strict,
            | Self::Fixture | Self::Pending => CorpusRoot::Fixture,
        }
    }
}

impl core::fmt::Display for SourceRoot
{
    /// Writes `strict`, `fixture` or `pending`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.write_str(match *self {
            | Self::Strict => STRICT,
            | Self::Fixture => FIXTURE,
            | Self::Pending => PENDING,
        })
    }
}

/// Classify the source at `path` by the innermost root directory it sits
/// under.
///
/// # Specification
/// - requires: `path` names the source itself; a relative path is read as
///   written, so a caller wanting the location a source really has passes its
///   canonical path.
/// - ensures: only the directories containing the source are read, never its
///   own file name. The innermost directory named `strict` or `fixture`
///   decides, and a directory named `pending` decides when its own parent
///   directory is named `fixture`; a path under none of them is
///   [`SourceRoot::Strict`].
/// - provides: the membership the walk settles each source under.
/// - fails: never; every path classifies.
/// - panics: none.
/// - intension: reads the path's components once, front to back, and touches no
///   file.
///
/// # Adequacy
/// - hypothesis: L3 — default membership, both root nestings, adjacent pending
///   membership and root-like filenames have exact expected roots.
///   Parent-directory components establish lexical rather than filesystem
///   resolution. These fixtures do not enumerate every native path spelling.
/// - witness: `root::tests::a_path_under_no_root_is_strict`
/// - witness: `root::tests::the_innermost_root_decides`
/// - witness: `root::tests::pending_counts_only_directly_inside_a_fixture_root`
/// - witness: `root::tests::the_file_name_never_classifies`
/// - witness: `root::tests::parent_components_are_classified_lexically`
#[inline]
#[must_use]
#[anodized::spec(ensures: |ret| ret == path.ancestors().skip(1).find_map(|directory| {
    let name = directory.file_name()?;
    if name == STRICT { Some(SourceRoot::Strict) }
    else if name == FIXTURE { Some(SourceRoot::Fixture) }
    else if name == PENDING
        && directory.parent().and_then(Path::file_name) == Some(OsStr::new(FIXTURE))
    { Some(SourceRoot::Pending) }
    else { None }
}).unwrap_or(SourceRoot::Strict))]
pub fn classify(path: &Path) -> SourceRoot
{
    let mut root = SourceRoot::Strict;
    let mut parent = OsStr::new("");
    for directory in path.parent().into_iter().flat_map(Path::iter) {
        if directory == STRICT {
            root = SourceRoot::Strict;
        }
        else if directory == FIXTURE {
            root = SourceRoot::Fixture;
        }
        else if directory == PENDING && parent == FIXTURE {
            root = SourceRoot::Pending;
        }
        parent = directory;
    }
    root
}

#[cfg(test)]
mod tests
{
    use std::path::Path;

    use gandr_surface_corpus::CorpusRoot;

    use super::SourceRoot;
    use super::classify;

    #[test]
    fn each_root_settles_under_its_corpus_root()
    {
        assert_eq!(
            SourceRoot::Strict.corpus_root(),
            CorpusRoot::Strict,
            "the strict root gates"
        );
        assert_eq!(
            SourceRoot::Fixture.corpus_root(),
            CorpusRoot::Fixture,
            "the fixture root asserts"
        );
        assert_eq!(
            SourceRoot::Pending.corpus_root(),
            CorpusRoot::Fixture,
            "the pending set is part of the fixture root"
        );
    }

    #[test]
    fn a_path_under_no_root_is_strict()
    {
        for path in [
            "a.gandr",
            "src/a.gandr",
            "/tmp/work/a.gandr",
            "pending/a.gandr",
        ] {
            assert_eq!(
                classify(Path::new(path)),
                SourceRoot::Strict,
                "{path} sits under no root"
            );
        }
    }

    #[test]
    fn the_innermost_root_decides()
    {
        let rows = [
            ("corpus/strict/a.gandr", SourceRoot::Strict),
            ("corpus/fixture/a.gandr", SourceRoot::Fixture),
            ("corpus/fixture/deep/er/a.gandr", SourceRoot::Fixture),
            ("corpus/strict/fixture/a.gandr", SourceRoot::Fixture),
            ("corpus/fixture/strict/a.gandr", SourceRoot::Strict),
            ("corpus/fixture/pending/model/a.gandr", SourceRoot::Pending),
            ("corpus/fixture/pending/strict/a.gandr", SourceRoot::Strict),
        ];
        for (path, root) in rows {
            assert_eq!(classify(Path::new(path)), root, "{path}");
        }
    }

    #[test]
    fn pending_counts_only_directly_inside_a_fixture_root()
    {
        let rows = [
            ("fixture/pending/a.gandr", SourceRoot::Pending),
            ("fixture/model/pending/a.gandr", SourceRoot::Fixture),
            ("strict/pending/a.gandr", SourceRoot::Strict),
            ("pending/fixture/a.gandr", SourceRoot::Fixture),
        ];
        for (path, root) in rows {
            assert_eq!(classify(Path::new(path)), root, "{path}");
        }
    }

    #[test]
    fn the_file_name_never_classifies()
    {
        assert_eq!(
            classify(Path::new("strict/fixture")),
            SourceRoot::Strict,
            "a file named `fixture` sits under the strict root"
        );
        assert_eq!(
            classify(Path::new("fixture/strict")),
            SourceRoot::Fixture,
            "a file named `strict` sits under the fixture root"
        );
        assert_eq!(
            classify(Path::new("fixture")),
            SourceRoot::Strict,
            "a bare file named `fixture` sits under no root"
        );
    }

    #[test]
    fn parent_components_are_classified_lexically()
    {
        assert_eq!(
            SourceRoot::Fixture,
            classify(Path::new("fixture/../a.gandr"))
        );
        assert_eq!(
            SourceRoot::Pending,
            classify(Path::new("fixture/pending/../a.gandr"))
        );
    }
}
