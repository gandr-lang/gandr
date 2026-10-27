//! The corpus sources a change touches, against the revision it is measured
//! from: the merge-base selection the obligations report applies to
//! witnesses, applied to a sweep's inputs.
//!
//! The change carries the commit it was read at, which keys the rotation a
//! sample takes the touched sources by.
//!
//! A source whose change is layout alone is no change: when the formatter
//! lays out the base's text and the working tree's text to one text, the two
//! hold the same tokens and comments in the same order — the invariant
//! `gandr-surface-format` checks on every text it returns — and every sweep
//! reads the source as it did before. Such a source leaves the change, so a
//! layout pass over the corpus keeps the sample at its stated size; the
//! nightly profile, which visits every source over its rotation, is the
//! backstop.
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
use crate::corpus::Roots;
use crate::error::SweepError;

/// The variable naming the revision a change is measured against.
pub const BASE: &str = "GANDR_SWEEP_BASE";

/// The corpus sources a change adds or modifies, by name, and the commit the
/// change was read at.
///
/// # Specification
/// - provides: the names a sample takes before its ranked slice, and the key
///   that rotates which of them it takes when they outnumber its size.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Changed
{
    /// The touched sources.
    names: BTreeSet<CorpusName>,
    /// The commit the change was read at; empty when none was.
    head: Head,
}

/// The commit a change was read at, as Git spells its object name: the key
/// of the rotation a sample takes the touched sources by.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct Head(String);

impl Head
{
    /// Feeds the key to `hasher`; the empty key feeds nothing.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one wide change at two commits visits two parts, so a
    ///   key fed nothing visits one part at both.
    /// - witness: `sample::tests::a_wide_change_is_visited_at_the_size_a_part_per_commit`
    pub(crate) fn key(
        &self,
        hasher: &mut blake3::Hasher,
    )
    {
        let _keyed = hasher.update(self.0.as_bytes());
    }
}

#[cfg(test)]
impl From<&str> for Head
{
    /// The key spelled `spelled`.
    ///
    /// # Specification
    /// trivial.
    fn from(spelled: &str) -> Self
    {
        Self(spelled.to_owned())
    }
}

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
    /// - requires: `git` on the path; each of `roots` is a directory inside one
    ///   Git work tree holding the base revision.
    /// - ensures: every `.gandr` file below a root, outside its held-out
    ///   directory, that the working tree adds or modifies against the base,
    ///   and every untracked one Git does not ignore, named as
    ///   [`crate::corpus::Root::name`] names it — less every modified source
    ///   the formatter lays out to the text it lays the base's out to — keyed
    ///   by the commit `HEAD` names.
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
    ///   listed by their names and an edited non-source is not, a source under
    ///   either root is named by that root's prefix and one in the held-out
    ///   directory is not listed, the key is the commit `HEAD` names, and a
    ///   base that does not exist is refused naming the command. Reading `HEAD`
    ///   instead of the working tree, dropping untracked files, listing one
    ///   root, keying by the base, or treating a failed command as an empty
    ///   change fails a witness.
    /// - witness: `changed::tests::a_change_lists_its_modified_and_untracked_sources_and_a_missing_base_is_refused`
    /// - witness: `changed::tests::a_layout_alone_is_no_change_492`
    /// - witness: `changed::tests::an_added_source_is_a_change_683`
    /// - witness: `changed::tests::a_change_names_each_root_s_sources_by_its_prefix_2949`
    #[inline]
    pub fn asked(roots: &Roots) -> Result<Self, SweepError>
    {
        let base = match std::env::var(BASE) {
            Ok(base) if !base.is_empty() => base,
            Ok(_) | Err(_) => git(
                &roots.strict.directory,
                GitArgs(&["merge-base", "origin/main", "HEAD"]),
            )?
            .trim()
            .to_owned(),
        };
        Self::against(roots, Revision::from(base.as_str()))
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
    /// - witness: `changed::tests::a_change_names_each_root_s_sources_by_its_prefix_2949`
    #[inline]
    pub fn against(
        roots: &Roots,
        base: Revision<'_>,
    ) -> Result<Self, SweepError>
    {
        let grammar = built_in().map_err(|error| SweepError::Grammar {
            detail: error.to_string(),
        })?;
        let source = |name: &&str| {
            Path::new(name)
                .extension()
                .is_some_and(|extension| extension == "gandr")
        };
        let mut names = BTreeSet::new();
        let mut shown = String::new();
        let mut excluded = String::new();
        for root in roots.each() {
            let directory = root.directory.as_path();
            excluded.clear();
            if let Some(held) = root.held_out {
                excluded.push_str(":(exclude)");
                excluded.push_str(held);
            }
            let within: &[&str] = if excluded.is_empty() {
                &["."]
            }
            else {
                &[".", excluded.as_str()]
            };
            let listed = |filter: &str| {
                let mut args = vec![
                    "diff",
                    "--name-only",
                    "--no-renames",
                    filter,
                    "--relative",
                    base.0,
                    "--",
                ];
                args.extend_from_slice(within);
                git(directory, GitArgs(&args))
            };
            let added = listed("--diff-filter=A")?;
            let modified = listed("--diff-filter=M")?;
            let mut untracked_args = vec!["ls-files", "--others", "--exclude-standard", "--"];
            untracked_args.extend_from_slice(within);
            let untracked = git(directory, GitArgs(&untracked_args))?;
            names.extend(
                added
                    .lines()
                    .filter(source)
                    .map(|below| root.name(Path::new(below))),
            );
            for below in modified.lines().filter(source) {
                shown.clear();
                shown.push_str(base.0);
                shown.push_str(":./");
                shown.push_str(below);
                let before = git(directory, GitArgs(&["show", &shown]))?;
                let after = std::fs::read_to_string(directory.join(below)).ok();
                let before = laid_out(&grammar, SourceText::from(before.as_str()));
                let after =
                    after.and_then(|after| laid_out(&grammar, SourceText::from(after.as_str())));
                if before.is_none() || before != after {
                    names.insert(root.name(Path::new(below)));
                }
            }
            names.extend(
                untracked
                    .lines()
                    .filter(source)
                    .map(|below| root.name(Path::new(below))),
            );
        }
        let head = git(&roots.strict.directory, GitArgs(&["rev-parse", "HEAD"]))?;
        Ok(Self {
            names,
            head: Head(head.trim().to_owned()),
        })
    }

    /// The changed sources, by name, ascending.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a change's names are compared with the sources it
    ///   edits and adds, so an empty or an invented name shows.
    /// - witness: `changed::tests::a_change_lists_its_modified_and_untracked_sources_and_a_missing_base_is_refused`
    #[inline]
    pub fn names(&self) -> impl Iterator<Item = &CorpusName>
    {
        self.names.iter()
    }

    /// The commit the change was read at.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Head::key`]: a commit read as the empty key
    ///   visits one part at both commits.
    /// - witness: `sample::tests::a_wide_change_is_visited_at_the_size_a_part_per_commit`
    pub(crate) const fn head(&self) -> &Head
    {
        &self.head
    }

    /// This change, read at `head`.
    ///
    /// # Specification
    /// trivial.
    #[cfg(test)]
    pub(crate) fn at(
        self,
        head: Head,
    ) -> Self
    {
        Self { head, ..self }
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
    /// The change touching exactly `names`, read at no commit.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a change collected from one source outside a sample
    ///   puts it in, so a change collected empty leaves it out.
    /// - witness: `sample::tests::a_sample_keeps_every_class_and_every_change`
    #[inline]
    fn from_iter<Names>(iter: Names) -> Self
    where
        Names: IntoIterator<Item = CorpusName>,
    {
        Self {
            names: iter.into_iter().collect(),
            head: Head::default(),
        }
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
    use crate::corpus::Root;
    use crate::corpus::Roots;
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

    /// The corpus's two roots laid out under `scratch` as the workspace lays
    /// them out, each directory made.
    ///
    /// # Specification
    /// trivial.
    fn scratch_roots(scratch: &Path) -> Roots
    {
        let strict = scratch.join("crates").join("surface-corpus").join("strict");
        let fixture = scratch.join("corpus");
        std::fs::create_dir_all(&strict).expect("the scratch strict root is made");
        std::fs::create_dir_all(fixture.join("model")).expect("the scratch fixture root is made");
        std::fs::create_dir_all(fixture.join("ledger")).expect("the scratch ledger is made");
        Roots {
            strict: Root {
                prefix: "strict",
                directory: strict,
                held_out: None,
            },
            fixture: Root {
                prefix: "fixture",
                directory: fixture,
                held_out: Some("ledger"),
            },
        }
    }

    #[test]
    fn a_change_lists_its_modified_and_untracked_sources_and_a_missing_base_is_refused()
    {
        let scratch =
            std::env::temp_dir().join(format!("gandr-sweep-changed-{}", std::process::id()));
        let roots = scratch_roots(&scratch);
        let fixture = &roots.fixture.directory;
        run(&scratch, GitArgs(&["init", "--quiet"]));
        for name in ["model/kept.gandr", "model/edited.gandr", "notes.txt"] {
            std::fs::write(fixture.join(name), "def a = 1 ;\n").expect("a file is written");
        }
        run(&scratch, GitArgs(&["add", "."]));
        run(&scratch, GitArgs(&["commit", "--quiet", "-m", "base"]));
        std::fs::write(fixture.join("model/edited.gandr"), "def a = 2 ;\n")
            .expect("an edit is written");
        std::fs::write(fixture.join("model/added.gandr"), "def b = 1 ;\n")
            .expect("a new source is written");
        std::fs::write(fixture.join("notes.txt"), "edited\n").expect("a non-source is edited");
        let changed = Changed::against(&roots, Revision::from("HEAD"));
        let missing = Changed::against(
            &roots,
            Revision::from("refs/heads/no-such-branch-for-a-sweep"),
        );
        std::fs::remove_dir_all(&scratch).expect("the scratch repository is removed");
        assert_eq!(
            changed.expect("HEAD resolves").names().collect::<Vec<_>>(),
            [
                &CorpusName::from("fixture/model/added.gandr"),
                &CorpusName::from("fixture/model/edited.gandr"),
            ],
            "the uncommitted edit and the untracked source, named below their root"
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
        let roots = scratch_roots(&scratch);
        let fixture = &roots.fixture.directory;
        run(&scratch, GitArgs(&["init", "--quiet"]));
        let base = "// One.\ndef  one =   1 ;\n";
        for name in ["model/laid.gandr", "model/edited.gandr"] {
            std::fs::write(fixture.join(name), base).expect("a source is written");
        }
        run(&scratch, GitArgs(&["add", "."]));
        run(&scratch, GitArgs(&["commit", "--quiet", "-m", "base"]));
        std::fs::write(fixture.join("model/laid.gandr"), "// One.\ndef one = 1 ;\n")
            .expect("a layout is written");
        std::fs::write(
            fixture.join("model/edited.gandr"),
            "// One.\ndef  one =   2 ;\n",
        )
        .expect("an edit is written");
        let changed = Changed::against(&roots, Revision::from("HEAD"));
        std::fs::remove_dir_all(&scratch).expect("the scratch repository is removed");
        assert_eq!(
            changed.expect("HEAD resolves").names().collect::<Vec<_>>(),
            [&CorpusName::from("fixture/model/edited.gandr")],
            "the layout leaves the change, the edit stays"
        );
    }

    /// #683: a source the change commits and the base lacks is in the change —
    /// there is no base text to lay out, and the sweep must not ask Git for
    /// one. The change is keyed by the commit it was read at, not its base.
    #[test]
    fn an_added_source_is_a_change_683()
    {
        let scratch =
            std::env::temp_dir().join(format!("gandr-sweep-added-{}", std::process::id()));
        let roots = scratch_roots(&scratch);
        let fixture = &roots.fixture.directory;
        run(&scratch, GitArgs(&["init", "--quiet"]));
        std::fs::write(fixture.join("model/kept.gandr"), "def a = 1 ;\n")
            .expect("a source is written");
        run(&scratch, GitArgs(&["add", "."]));
        run(&scratch, GitArgs(&["commit", "--quiet", "-m", "base"]));
        std::fs::write(fixture.join("model/added.gandr"), "def b = 1 ;\n")
            .expect("a new source is written");
        run(&scratch, GitArgs(&["add", "."]));
        run(
            &scratch,
            GitArgs(&["commit", "--quiet", "-m", "adds a source"]),
        );
        let changed = Changed::against(&roots, Revision::from("HEAD^"));
        let head = super::git(&scratch, GitArgs(&["rev-parse", "HEAD"]));
        std::fs::remove_dir_all(&scratch).expect("the scratch repository is removed");
        let changed = changed.expect("the base resolves");
        assert_eq!(
            changed.names().collect::<Vec<_>>(),
            [&CorpusName::from("fixture/model/added.gandr")],
            "the committed addition is the change"
        );
        assert_eq!(
            changed.head.0,
            head.expect("HEAD resolves").trim(),
            "the change is keyed by HEAD"
        );
    }

    /// #2949: the change lists both roots, the strict root in the corpus crate
    /// and the fixture root at the repository's top, and names each source by
    /// its root's prefix; a source in the fixture root's ledger is none.
    #[test]
    fn a_change_names_each_root_s_sources_by_its_prefix_2949()
    {
        let scratch =
            std::env::temp_dir().join(format!("gandr-sweep-roots-{}", std::process::id()));
        let roots = scratch_roots(&scratch);
        let strict = &roots.strict.directory;
        let fixture = &roots.fixture.directory;
        run(&scratch, GitArgs(&["init", "--quiet"]));
        std::fs::write(strict.join("kept.gandr"), "def a = 1 ;\n").expect("a source is written");
        run(&scratch, GitArgs(&["add", "."]));
        run(&scratch, GitArgs(&["commit", "--quiet", "-m", "base"]));
        for (directory, name) in [
            (strict, "added.gandr"),
            (fixture, "model/staged.gandr"),
            (fixture, "ledger/entry.gandr"),
        ] {
            std::fs::write(directory.join(name), "def b = 1 ;\n").expect("a new source is written");
        }
        run(&scratch, GitArgs(&["add", "corpus/model/staged.gandr"]));
        std::fs::write(fixture.join("loose.gandr"), "def c = 1 ;\n")
            .expect("an untracked source is written");
        let changed = Changed::against(&roots, Revision::from("HEAD"));
        std::fs::remove_dir_all(&scratch).expect("the scratch repository is removed");
        assert_eq!(
            changed.expect("HEAD resolves").names().collect::<Vec<_>>(),
            [
                &CorpusName::from("fixture/loose.gandr"),
                &CorpusName::from("fixture/model/staged.gandr"),
                &CorpusName::from("strict/added.gandr"),
            ],
            "each root's sources by its prefix, the ledger held out"
        );
    }
}
