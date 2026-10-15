//! The corpus sources a change touches, against the revision it is measured
//! from: the merge-base selection the obligations report applies to
//! witnesses, applied to a sweep's inputs.

use alloc::collections::BTreeSet;
use std::path::Path;
use std::process::Command;

use anodized::spec;

use crate::corpus::CorpusName;
use crate::error::SweepError;

/// The variable naming the revision a change is measured against.
pub const BASE: &str = "GANDR_SWEEP_BASE";

/// The corpus sources a change adds or modifies, by name.
///
/// # Specification
/// - provides: the names a sample takes whatever their rank.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Changed(BTreeSet<CorpusName>);

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
    ///   ignore, named below `corpus`.
    /// - provides: a sample's changed-files rule; the working tree, not `HEAD`,
    ///   is compared, so an uncommitted edit counts.
    /// - fails: [`SweepError::Git`] when an invocation cannot run, exits
    ///   unsuccessfully, or prints what is not UTF-8.
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
    #[inline]
    pub fn asked(corpus: &Path) -> Result<Self, SweepError>
    {
        let base = match std::env::var(BASE) {
            Ok(base) if !base.is_empty() => base,
            Ok(_) | Err(_) => git(corpus, &["merge-base", "origin/main", "HEAD"])?
                .trim()
                .to_owned(),
        };
        Self::against(corpus, &base)
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
    #[inline]
    pub fn against(
        corpus: &Path,
        base: &str,
    ) -> Result<Self, SweepError>
    {
        let differing = git(corpus, &[
            "diff",
            "--name-only",
            "--no-renames",
            "--diff-filter=AM",
            "--relative",
            base,
            "--",
            ".",
        ])?;
        let untracked = git(corpus, &["ls-files", "--others", "--exclude-standard"])?;
        Ok(Self(
            differing
                .lines()
                .chain(untracked.lines())
                .filter(|name| {
                    Path::new(name)
                        .extension()
                        .is_some_and(|extension| extension == "gandr")
                })
                .map(CorpusName::from)
                .collect(),
        ))
    }

    /// Whether the change touches the source named `name`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn touches(
        &self,
        name: &CorpusName,
    ) -> bool
    {
        self.0.contains(name)
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

/// What `git args` prints, run in `directory`.
///
/// # Specification
/// - requires: `git` on the path.
/// - ensures: the invocation's standard output when it exits successfully.
/// - provides: the one way this crate asks Git.
/// - fails: [`SweepError::Git`] naming the invocation when it cannot run, exits
///   unsuccessfully — with its standard error — or prints what is not UTF-8.
/// - panics: none.
/// - executable: none — the outcome is the external process's.
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
    args: &[&str],
) -> Result<String, SweepError>
{
    let refuse = |detail: String| SweepError::Git {
        command: format!("git {}", args.join(" ")),
        detail,
    };
    let output = Command::new("git")
        .arg("-C")
        .arg(directory)
        .args(args)
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
    use crate::corpus::CorpusName;
    use crate::error::SweepError;

    /// Run `git args` in `directory`, which must succeed.
    ///
    /// # Specification
    /// trivial.
    fn run(
        directory: &Path,
        args: &[&str],
    )
    {
        let status = Command::new("git")
            .arg("-C")
            .arg(directory)
            .args(["-c", "user.name=sweep", "-c", "user.email=sweep@invalid"])
            .args(["-c", "commit.gpgsign=false"])
            .args(args)
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
        run(&scratch, &["init", "--quiet"]);
        for name in [
            "fixture/model/kept.gandr",
            "fixture/model/edited.gandr",
            "notes.txt",
        ] {
            std::fs::write(corpus.join(name), "def a = 1 ;\n").expect("a file is written");
        }
        run(&scratch, &["add", "."]);
        run(&scratch, &["commit", "--quiet", "-m", "base"]);
        std::fs::write(corpus.join("fixture/model/edited.gandr"), "def a = 2 ;\n")
            .expect("an edit is written");
        std::fs::write(corpus.join("fixture/model/added.gandr"), "def b = 1 ;\n")
            .expect("a new source is written");
        std::fs::write(corpus.join("notes.txt"), "edited\n").expect("a non-source is edited");
        let changed = Changed::against(&corpus, "HEAD");
        let missing = Changed::against(&corpus, "refs/heads/no-such-branch-for-a-sweep");
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
}
