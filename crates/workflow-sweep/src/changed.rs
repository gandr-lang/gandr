//! The corpus sources a change touches, against the revision it is measured
//! from: the merge-base selection the obligations report applies to
//! witnesses, applied to a sweep's inputs.
//!
//! A source whose change is layout alone is no change: when the formatter
//! lays out the base's text and the working tree's text to one text, the two
//! hold the same tokens and comments in the same order — the invariant
//! `gandr-surface-format` checks on every text it returns — and every sweep
//! reads the source as it did before. Such a source leaves the change, so a
//! layout pass over the corpus keeps the sample at its stated size; the
//! nightly `sweeps` profile, which visits every source, is the backstop.
//! The alternative was listing every touched file, which puts a corpus-wide
//! layout into every sample at once and past the 30 s bound (#492).

use alloc::collections::BTreeSet;
use std::path::Path;
use std::process::Command;

use anodized::spec;
use gandr_surface_format::FormatOptions;
use gandr_surface_format::format;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::built_in;
use gandr_surface_parser::parse;
use gandr_surface_syntax::SourceText;

use crate::corpus::CorpusName;
use crate::error::SweepError;

/// The variable naming the revision a change is measured against.
pub const BASE: &str = "GANDR_SWEEP_BASE";

/// The corpus sources a change adds or modifies, by name.
///
/// # Specification
/// - provides: the names a sample takes whatever their rank.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Changed(BTreeSet<CorpusName>);

/// A revision Git resolves: a commit, a branch, or an expression such as
/// `HEAD^`.
///
/// # Specification
/// - provides: the base a change is measured against.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Revision<'text>(&'text str);

impl<'text> From<&'text str> for Revision<'text>
{
    /// The revision spelled `spelled`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(spelled: &'text str) -> Self
    {
        Self(spelled)
    }
}

/// The arguments of one Git invocation, after `git -C <directory>`.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct GitArgs<'args>(&'args [&'args str]);

impl Changed
{
    /// The changed sources the environment names: those differing from the
    /// revision [`BASE`] names, or, when it is unset or empty, from where the
    /// checkout's `HEAD` left `origin/main`.
    ///
    /// # Specification
    /// - requires: `git` on the path; `corpus` is the corpus crate's directory
    ///   inside a Git work tree holding the base revision.
    /// - ensures: every `.gandr` file below `corpus` that the working tree adds
    ///   or modifies against the base, and every untracked one Git does not
    ///   ignore, named below `corpus` — less every modified source the
    ///   formatter lays out to the text it lays the base's out to.
    /// - provides: a sample's changed-files rule; the working tree, not `HEAD`,
    ///   is compared, so an uncommitted edit counts.
    /// - fails: [`SweepError::Git`] when an invocation cannot run, exits
    ///   unsuccessfully, or prints what is not UTF-8; [`SweepError::Grammar`]
    ///   when the built-in grammar does not build.
    /// - panics: none.
    /// - executable: none — the outcome is the external process's.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the base's own resolution is Git's; against a
    ///   committed corpus, an uncommitted edit and an untracked source are
    ///   listed by their names below the corpus and an edited non-source is
    ///   not, and a base that does not exist is refused naming the command.
    ///   Reading `HEAD` instead of the working tree, dropping untracked files,
    ///   or treating a failed command as an empty change fails the witness.
    /// - witness: `changed::tests::a_change_lists_its_modified_and_untracked_sources_and_a_missing_base_is_refused`
    /// - witness: `changed::tests::a_layout_alone_is_no_change_492`
    #[inline]
    pub fn asked(corpus: &Path) -> Result<Self, SweepError>
    {
        let base = match std::env::var(BASE) {
            Ok(base) if !base.is_empty() => base,
            Ok(_) | Err(_) => git(corpus, GitArgs(&["merge-base", "origin/main", "HEAD"]))?
                .trim()
                .to_owned(),
        };
        Self::against(corpus, Revision::from(base.as_str()))
    }

    /// The changed sources against `base`.
    ///
    /// # Specification
    /// - requires: as [`Changed::asked`], with `base` a revision Git resolves.
    /// - ensures: as [`Changed::asked`], against `base`.
    /// - provides: the comparison once the base is known.
    /// - fails: as [`Changed::asked`].
    /// - panics: none.
    /// - executable: none — the outcome is the external process's.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Changed::asked`].
    /// - witness: `changed::tests::a_change_lists_its_modified_and_untracked_sources_and_a_missing_base_is_refused`
    /// - witness: `changed::tests::a_layout_alone_is_no_change_492`
    /// - witness: `changed::tests::an_added_source_is_a_change_683`
    #[inline]
    pub fn against(
        corpus: &Path,
        base: Revision<'_>,
    ) -> Result<Self, SweepError>
    {
        let added = git(
            corpus,
            GitArgs(&[
                "diff",
                "--name-only",
                "--no-renames",
                "--diff-filter=A",
                "--relative",
                base.0,
                "--",
                ".",
            ]),
        )?;
        let modified = git(
            corpus,
            GitArgs(&[
                "diff",
                "--name-only",
                "--no-renames",
                "--diff-filter=M",
                "--relative",
                base.0,
                "--",
                ".",
            ]),
        )?;
        let untracked = git(
            corpus,
            GitArgs(&["ls-files", "--others", "--exclude-standard"]),
        )?;
        let grammar = built_in().map_err(|error| SweepError::Grammar {
            detail: error.to_string(),
        })?;
        let source = |name: &&str| {
            Path::new(name)
                .extension()
                .is_some_and(|extension| extension == "gandr")
        };
        let mut names: BTreeSet<CorpusName> =
            added.lines().filter(source).map(CorpusName::from).collect();
        for name in modified.lines().filter(source) {
            let shown = format!("{}:./{name}", base.0);
            let before = git(corpus, GitArgs(&["show", &shown]))?;
            let after = std::fs::read_to_string(corpus.join(name)).ok();
            let before = laid_out(&grammar, SourceText::from(before.as_str()));
            let after =
                after.and_then(|after| laid_out(&grammar, SourceText::from(after.as_str())));
            if before.is_none() || before != after {
                names.insert(CorpusName::from(name));
            }
        }
        names.extend(untracked.lines().filter(source).map(CorpusName::from));
        Ok(Self(names))
    }

    /// The changed sources, by name, ascending.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn names(&self) -> impl Iterator<Item = &CorpusName>
    {
        self.0.iter()
    }
}

/// The layout the formatter gives `text`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the text [`format()`] returns at the default options when `text`
///   parses and formats; none otherwise, so a text that does not lay out is
///   alike to nothing and stays in the change.
/// - provides: the layout-only test of [`Changed::against`]: two texts laid out
///   to one text hold the same tokens and comments in the same order.
/// - fails: never — a refusal is no layout.
/// - panics: none.
/// - executable: none — the answer is the formatter's, which a predicate would
///   run again.
///
/// # Adequacy
/// - hypothesis: L3 — a respaced source lays out alike, an edited token does
///   not.
/// - witness: `changed::tests::a_layout_alone_is_no_change_492`
fn laid_out(
    grammar: &Pbg,
    text: SourceText<'_>,
) -> Option<String>
{
    let parsed = parse(grammar, text).ok()?;
    format(grammar, &parsed, FormatOptions::default())
        .ok()
        .map(gandr_surface_format::Formatted::into_text)
}

impl FromIterator<CorpusName> for Changed
{
    /// The change touching exactly `names`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from_iter<Names>(iter: Names) -> Self
    where
        Names: IntoIterator<Item = CorpusName>,
    {
        Self(iter.into_iter().collect())
    }
}

/// What `git` prints when run in `directory` with `args`.
///
/// # Specification
/// - requires: `git` on the path.
/// - ensures: the invocation's standard output when it exits successfully.
/// - provides: the one way this crate asks Git.
/// - fails: [`SweepError::Git`] naming the invocation when it cannot run, exits
///   unsuccessfully — with its standard error — or prints what is not UTF-8.
/// - panics: none.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Changed::asked`].
/// - witness: `changed::tests::a_change_lists_its_modified_and_untracked_sources_and_a_missing_base_is_refused`
#[spec(ensures: |ret| ret.as_ref().map_or_else(|error| matches!(*error, SweepError::Git { .. }), |_| true))]
fn git(
    directory: &Path,
    args: GitArgs<'_>,
) -> Result<String, SweepError>
{
    let refuse = |detail: String| SweepError::Git {
        command: format!("git {}", args.0.join(" ")),
        detail,
    };
    let output = Command::new("git")
        .arg("-C")
        .arg(directory)
        .args(args.0)
        .output()
        .map_err(|error| refuse(error.to_string()))?;
    if !output.status.success() {
        return Err(refuse(
            String::from_utf8_lossy(&output.stderr).trim().to_owned(),
        ));
    }
    String::from_utf8(output.stdout).map_err(|error| refuse(error.to_string()))
}

#[cfg(test)]
mod tests
{
    use std::path::Path;
    use std::process::Command;

    use super::Changed;
    use super::GitArgs;
    use super::Revision;
    use crate::corpus::CorpusName;
    use crate::error::SweepError;

    /// Run `git args` in `directory`, which must succeed.
    ///
    /// # Specification
    /// trivial.
    fn run(
        directory: &Path,
        args: GitArgs<'_>,
    )
    {
        let status = Command::new("git")
            .arg("-C")
            .arg(directory)
            .args(["-c", "user.name=sweep", "-c", "user.email=sweep@invalid"])
            .args(["-c", "commit.gpgsign=false"])
            .args(args.0)
            .status()
            .expect("git runs");
        assert!(status.success(), "git {args:?}");
    }

    #[test]
    fn a_change_lists_its_modified_and_untracked_sources_and_a_missing_base_is_refused()
    {
        let scratch =
            std::env::temp_dir().join(format!("gandr-sweep-changed-{}", std::process::id()));
        let corpus = scratch.join("crates").join("surface-corpus");
        std::fs::create_dir_all(corpus.join("fixture/model")).expect("the scratch corpus is made");
        run(&scratch, GitArgs(&["init", "--quiet"]));
        for name in [
            "fixture/model/kept.gandr",
            "fixture/model/edited.gandr",
            "notes.txt",
        ] {
            std::fs::write(corpus.join(name), "def a = 1 ;\n").expect("a file is written");
        }
        run(&scratch, GitArgs(&["add", "."]));
        run(&scratch, GitArgs(&["commit", "--quiet", "-m", "base"]));
        std::fs::write(corpus.join("fixture/model/edited.gandr"), "def a = 2 ;\n")
            .expect("an edit is written");
        std::fs::write(corpus.join("fixture/model/added.gandr"), "def b = 1 ;\n")
            .expect("a new source is written");
        std::fs::write(corpus.join("notes.txt"), "edited\n").expect("a non-source is edited");
        let changed = Changed::against(&corpus, Revision::from("HEAD"));
        let missing = Changed::against(
            &corpus,
            Revision::from("refs/heads/no-such-branch-for-a-sweep"),
        );
        std::fs::remove_dir_all(&scratch).expect("the scratch repository is removed");
        assert_eq!(
            changed.expect("HEAD resolves").names().collect::<Vec<_>>(),
            [
                &CorpusName::from("fixture/model/added.gandr"),
                &CorpusName::from("fixture/model/edited.gandr"),
            ],
            "the uncommitted edit and the untracked source, named below the corpus"
        );
        assert!(
            matches!(
                missing,
                Err(SweepError::Git { ref command, .. }) if command.contains("no-such-branch-for-a-sweep")
            ),
            "{missing:?}"
        );
    }

    /// #492: a source laid out anew, its tokens and comments the base's, is
    /// no change; an edited token in a source laid out the same is one.
    #[test]
    fn a_layout_alone_is_no_change_492()
    {
        let scratch =
            std::env::temp_dir().join(format!("gandr-sweep-layout-{}", std::process::id()));
        let corpus = scratch.join("crates").join("surface-corpus");
        std::fs::create_dir_all(corpus.join("fixture/model")).expect("the scratch corpus is made");
        run(&scratch, GitArgs(&["init", "--quiet"]));
        let base = "// One.\ndef  one =   1 ;\n";
        for name in ["fixture/model/laid.gandr", "fixture/model/edited.gandr"] {
            std::fs::write(corpus.join(name), base).expect("a source is written");
        }
        run(&scratch, GitArgs(&["add", "."]));
        run(&scratch, GitArgs(&["commit", "--quiet", "-m", "base"]));
        std::fs::write(
            corpus.join("fixture/model/laid.gandr"),
            "// One.\ndef one = 1 ;\n",
        )
        .expect("a layout is written");
        std::fs::write(
            corpus.join("fixture/model/edited.gandr"),
            "// One.\ndef  one =   2 ;\n",
        )
        .expect("an edit is written");
        let changed = Changed::against(&corpus, Revision::from("HEAD"));
        std::fs::remove_dir_all(&scratch).expect("the scratch repository is removed");
        assert_eq!(
            changed.expect("HEAD resolves").names().collect::<Vec<_>>(),
            [&CorpusName::from("fixture/model/edited.gandr")],
            "the layout leaves the change, the edit stays"
        );
    }

    /// #683: a source the change commits and the base lacks is in the change —
    /// there is no base text to lay out, and the sweep must not ask Git for
    /// one.
    #[test]
    fn an_added_source_is_a_change_683()
    {
        let scratch =
            std::env::temp_dir().join(format!("gandr-sweep-added-{}", std::process::id()));
        let corpus = scratch.join("crates").join("surface-corpus");
        std::fs::create_dir_all(corpus.join("fixture/model")).expect("the scratch corpus is made");
        run(&scratch, GitArgs(&["init", "--quiet"]));
        std::fs::write(corpus.join("fixture/model/kept.gandr"), "def a = 1 ;\n")
            .expect("a source is written");
        run(&scratch, GitArgs(&["add", "."]));
        run(&scratch, GitArgs(&["commit", "--quiet", "-m", "base"]));
        std::fs::write(corpus.join("fixture/model/added.gandr"), "def b = 1 ;\n")
            .expect("a new source is written");
        run(&scratch, GitArgs(&["add", "."]));
        run(
            &scratch,
            GitArgs(&["commit", "--quiet", "-m", "adds a source"]),
        );
        let changed = Changed::against(&corpus, Revision::from("HEAD^"));
        std::fs::remove_dir_all(&scratch).expect("the scratch repository is removed");
        assert_eq!(
            changed
                .expect("the base resolves")
                .names()
                .collect::<Vec<_>>(),
            [&CorpusName::from("fixture/model/added.gandr")],
            "the committed addition is the change"
        );
    }
}
