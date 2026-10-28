//! The cone a landing touches: deep when it reaches the kernel or core
//! stack, surface otherwise.

use core::fmt;
use std::process::Command;

use gandr_workflow_github::Feed;
use gandr_workflow_github::run;

use crate::error::BudgetError;
use crate::report::RunId;

/// The cone a landing's changed files touch.
///
/// # Specification
/// - provides: the class a run's samples are held to.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Cone
{
    /// A changed file is under `crates/kernel-*` or `crates/core-*`, or is
    /// `Cargo.lock`, `rust-toolchain.toml` or under `.cargo/`: the landing
    /// rebuilds the kernel and core stack and everything downstream.
    Deep,
    /// No such file changed: the landing rebuilds only what it touched.
    Surface,
}

impl fmt::Display for Cone
{
    /// Writes the class as the report's class column: `deep` or `surface`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the report's rows name both classes, so writing
    ///   nothing changes the asserted rows.
    /// - witness: `tests::cli::a_run_is_classified_by_the_cone_it_touched`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            Self::Deep => "deep",
            Self::Surface => "surface",
        })
    }
}

/// A changed file's path, as the comparison prints it.
///
/// # Specification
/// - provides: the nominal boundary a file's cone is read from.
#[repr(transparent)]
#[derive(Clone, Copy)]
struct Path<'path>(&'path str);

impl<'path> From<&'path str> for Path<'path>
{
    /// Names the file `path`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a compare naming a kernel file holds its run deep,
    ///   which an emptied path would hold surface.
    /// - witness: `tests::cli::a_run_is_classified_by_the_cone_it_touched`
    #[inline]
    fn from(path: &'path str) -> Self
    {
        Self(path)
    }
}

/// Whether one changed file puts the landing in the deep cone.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`Cone::Deep`] when the path is under a `crates/kernel-*` or
///   `crates/core-*` directory, is `Cargo.lock` or `rust-toolchain.toml`, or is
///   under `.cargo/`; [`Cone::Surface`] otherwise.
/// - provides: the file half of a landing's cone.
/// - fails: never.
/// - panics: none.
/// - executable: none — the prefixes are the clause.
///
/// # Adequacy
/// - hypothesis: L3 — a kernel path, a core path, a lockfile, a toolchain pin,
///   a `.cargo/` file, a surface path and a root file; a prefix that matches
///   `crates/core` without the dash, or a path that only contains `kernel`,
///   changes a classification.
/// - witness: `cone::tests::a_file_names_its_cone`
#[inline]
#[must_use]
fn file_cone(path: Path<'_>) -> Cone
{
    let deep = path.0 == "Cargo.lock"
        || path.0 == "rust-toolchain.toml"
        || path.0.starts_with(".cargo/")
        || path.0.starts_with("crates/kernel-")
        || path.0.starts_with("crates/core-");
    if deep { Cone::Deep } else { Cone::Surface }
}

/// The cone of the files `run` changed against its merge base.
///
/// # Specification
/// - requires: `gh` on the path, authenticated for the repository.
/// - ensures: [`Cone::Deep`] when any changed file is deep, when the run's base
///   cannot be read, or when the comparison fails; [`Cone::Surface`] when every
///   changed file is surface.
/// - provides: the class a run's samples are held to.
/// - fails: [`BudgetError::Gh`] when a `gh` invocation fails or prints what
///   this crate does not read.
/// - panics: none.
/// - executable: none — the outcome is the external process's.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — a merge-group run whose compare names a kernel file, one
///   whose compare names only surface files, a pull-request run, and a run
///   whose base is unreadable; classifying a failed compare surface changes the
///   budget a deep landing is held to.
/// - witness: `tests::cli::a_run_is_classified_by_the_cone_it_touched`
/// - witness: `tests::cli::a_run_without_a_base_is_held_deep`
#[inline]
pub fn classify(run_id: RunId) -> Result<Cone, BudgetError>
{
    let mut command = Command::new("gh");
    command.args([
        "api",
        "--method",
        "GET",
        &format!("repos/{{owner}}/{{repo}}/actions/runs/{run_id}"),
        "--jq",
        r#"(.event + "\t" + .head_sha + "\t" + (.pull_request.base.sha // "") + "\t" + (.head_branch // ""))"#,
    ]);
    let text = run(&mut command, Feed::Nothing)?;
    let mut fields = text.split('\t');
    let event = fields.next().unwrap_or_default();
    let head = fields.next().unwrap_or_default();
    let base = fields.next().unwrap_or_default();
    let branch = fields.next().unwrap_or_default();
    // The queue's branch names the entry's base: `pr-N-<base sha>`.
    let base = if event == "merge_group" {
        let sha = branch
            .rsplit_once('-')
            .map_or_else(String::new, |(_, sha)| sha.to_owned());
        sha.get(0 .. 40).unwrap_or_default().to_owned()
    }
    else {
        base.to_owned()
    };
    if base.len() != 40 || !base.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        return Ok(Cone::Deep);
    }
    let mut compare = Command::new("gh");
    compare.args([
        "api",
        "--method",
        "GET",
        &format!("repos/{{owner}}/{{repo}}/compare/{base}...{head}"),
        "--jq",
        r#".files[] | .filename"#,
    ]);
    let files = run(&mut compare, Feed::Nothing)?;
    let deep = files
        .lines()
        .any(|path| file_cone(Path::from(path)) == Cone::Deep);
    Ok(if deep { Cone::Deep } else { Cone::Surface })
}

#[cfg(test)]
mod tests
{
    use super::Cone;
    use super::Path;
    use super::file_cone;

    #[test]
    fn a_file_names_its_cone()
    {
        for path in [
            "crates/kernel-core/src/lib.rs",
            "crates/core-nbe/src/eval.rs",
            "Cargo.lock",
            "rust-toolchain.toml",
            ".cargo/config.toml",
        ] {
            assert_eq!(file_cone(Path::from(path)), Cone::Deep, "{path}");
        }
        for path in [
            "crates/surface-parser/src/lib.rs",
            "crates/core.rs",
            "kernel-notes.md",
            "README.md",
            "crates/workflow-lane-budget/src/cone.rs",
        ] {
            assert_eq!(file_cone(Path::from(path)), Cone::Surface, "{path}");
        }
    }
}
