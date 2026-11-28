//! The values of a commit whose tool is not the tool of this run.
//!
//! A value is a function of its tool, so the tool of the commit must compute
//! it. The run checks the commit out in a detached work tree below the
//! target directory, builds the `outputs` binary of the commit there, and
//! runs it on the same store. The work tree and its target directory stay
//! for the next run, so a second commit with the same packages builds no
//! more than cargo needs.

use std::path::Path;
use std::path::PathBuf;
use std::process::Command;
use std::process::Stdio;

use gandr_workflow_output_store::Kind;
use gandr_workflow_output_store::Store;

/// The detached work tree of the other commit, below the target directory of
/// the workspace `root`.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub fn place(root: &Path) -> PathBuf
{
    root.join("target/outputs-checkout")
}

/// The exit status of an `outputs` binary that refuses its command line: a
/// command or a kind that the binary does not have.
pub const COMMAND_LINE_REFUSED: u8 = 2;

/// Computes the values of the kind `kind` of the commit `revision` of the
/// repository `root` into `store`, by the `outputs` binary of that commit.
///
/// Gives `false` when that binary refuses the command line: the commit does
/// not have the kind, and thus has no value of it.
///
/// # Specification
/// trivial.
///
/// # Errors
/// One line that names the step that failed: the checkout of the commit, or
/// the build or the run of its binary, with the last line that the step
/// wrote. A commit with no `gandr-workflow-outputs` fails in its build.
#[inline]
pub fn compute(
    root: &Path,
    store: &Store,
    kind: Kind,
    revision: &str,
) -> Result<bool, String>
{
    let commit = run(Command::new("git").arg("-C").arg(root).args([
        "rev-parse",
        "--verify",
        &format!("{revision}^{{commit}}"),
    ]))
    .map_err(|error| format!("{revision} names no commit: {error}"))?;
    let commit = commit.trim();
    let work = place(root);
    // Two runs do not make the checkout or build in it at the same time: the
    // second one waits for the lock. The lock ends with its file handle.
    let target = root.join("target");
    std::fs::create_dir_all(&target).map_err(|error| format!("the target directory: {error}"))?;
    let lock = std::fs::File::create(target.join("outputs-checkout.lock"))
        .map_err(|error| format!("the lock of the checkout: {error}"))?;
    lock.lock()
        .map_err(|error| format!("the lock of the checkout: {error}"))?;
    let checked_out = if work.join(".git").exists() {
        run(Command::new("git")
            .arg("-C")
            .arg(&work)
            .args(["checkout", "--quiet", "--detach", "--force", commit]))
    }
    else {
        run(Command::new("git")
            .arg("-C")
            .arg(root)
            .args(["worktree", "add", "--quiet", "--detach", "--force"])
            .arg(&work)
            .arg(commit))
    };
    let _checked_out = checked_out.map_err(|error| format!("the checkout of {commit}: {error}"))?;
    let cargo = std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into());
    let output = Command::new(cargo)
        .current_dir(&work)
        .env("CARGO_TARGET_DIR", root.join("target/outputs-target"))
        .env("GANDR_OUTPUT_STORE", store.root())
        .args([
            "run",
            "--locked",
            "--quiet",
            "--package",
            "gandr-workflow-outputs",
            "--bin",
            "outputs",
            "--",
        ])
        .args(["compute", kind.0, "--revision", commit])
        .stdin(Stdio::null())
        .output()
        .map_err(|error| format!("the tool of {commit}: {error}"))?;
    drop(lock);
    if output.status.code() == Some(i32::from(COMMAND_LINE_REFUSED)) {
        return Ok(false);
    }
    if !output.status.success() {
        return Err(format!(
            "the tool of {commit}: {}",
            last_line(&output.stderr)
        ));
    }
    Ok(true)
}

/// The standard output of `command`, or the last line of its standard error
/// when it fails.
///
/// # Specification
/// trivial.
///
/// # Errors
/// The refusal to start, or the last line of standard error.
fn run(command: &mut Command) -> Result<String, String>
{
    let output = command
        .stdin(Stdio::null())
        .output()
        .map_err(|error| error.to_string())?;
    if output.status.success() {
        return Ok(String::from_utf8_lossy(&output.stdout).into_owned());
    }
    Err(last_line(&output.stderr))
}

/// The last line of `stderr` that is not blank.
///
/// # Specification
/// trivial.
fn last_line(stderr: &[u8]) -> String
{
    String::from_utf8_lossy(stderr)
        .lines()
        .rev()
        .find(|line| !line.trim().is_empty())
        .unwrap_or("no message")
        .to_owned()
}
