//! The markdown documents, read under the merge base's paragraph digests.
//!
//! A change answers for the paragraphs it wrote, and for no other. The check
//! reads each document that the change touched, at the head and at the base.
//! A head paragraph whose digest the base holds is one that the change did not
//! write, and the check leaves it alone. Each other paragraph parses and meets
//! every sentence rule, and a finding refuses. No ledger holds a document's
//! debt: a paragraph that no change writes keeps its debt until a change
//! writes it.
//!
//! The documents are the markdown files that the tree tracks, with three kinds
//! set aside. The issue templates and the pull request template are bodies, and
//! the body rules read them. The census and the syntax pages are written by
//! their generators, whose own sources hold the words. An untracked markdown
//! file is a document too, so a new page meets the rules before its commit.

use std::io::Read as _;
use std::io::Write as _;
use std::path::Path;
use std::process::Command;
use std::process::Stdio;

use crate::error::ProseError;
use crate::passage;
use crate::passage::Passage;
use crate::passage::Text;

/// The revision a change runs from: the merge base of the change and its
/// trunk.
///
/// # Specification
/// - provides: the side whose paragraphs the change did not write.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Base<'rev>(pub &'rev str);

/// The paths the rule sets aside: a directory ends in `/`, and a file is
/// named whole.
const SET_ASIDE: [&str; 4] = [
    ".config/issues/templates/",
    ".github/",
    "ledger/census.md",
    "ledger/syntax.md",
];

/// Which documents a listing names beside the untracked ones.
///
/// # Specification
/// - provides: the one difference between [`touched`] and [`every`].
#[derive(Clone, Copy, Debug)]
enum Listing<'rev>
{
    /// Each document the working tree adds or alters against the base.
    Changed(Base<'rev>),
    /// Each document the tree tracks.
    Tracked,
}

/// The documents the change touched since `base`, by path.
///
/// # Specification
/// - requires: `root` is a repository checkout that holds `base`.
/// - ensures: each markdown file that the working tree adds or alters against
///   `base`, and each untracked one that `.gitignore` admits, the paths of
///   [`SET_ASIDE`] left out, sorted, each once. A file the change deletes is
///   not listed.
/// - provides: the documents whose paragraphs the check reads.
/// - fails: [`ProseError::Io`] naming the root when git cannot list the change,
///   as for a base the clone does not hold.
/// - panics: none.
/// - executable: none — the outcome is git's.
///
/// # Errors
/// As `fails` lists.
///
/// # Cost
/// - allocation: the listed paths, growth within the change
///
/// # Adequacy
/// - hypothesis: L3 — a scratch repository whose change alters a README, adds
///   an untracked page, deletes a page and alters an issue template; a deleted
///   page listed, the new page missed or the template read changes the list.
/// - witness: `tests::cli::a_document_answers_for_the_paragraphs_its_change_wrote`
#[inline]
pub fn touched(
    root: &Path,
    base: Base<'_>,
) -> Result<Vec<String>, ProseError>
{
    listed(root, Listing::Changed(base))
}

/// Every document of the head, by path.
///
/// # Specification
/// - requires: `root` is a repository checkout.
/// - ensures: each markdown file that the tree tracks, and each untracked one
///   that `.gitignore` admits, the paths of [`SET_ASIDE`] left out, sorted,
///   each once.
/// - provides: the documents whose paragraphs a prune of the parse cache keeps.
/// - fails: [`ProseError::Io`] naming the root when git cannot list the tree.
/// - panics: none.
/// - executable: none — the outcome is git's.
///
/// # Errors
/// As `fails` lists.
///
/// # Cost
/// - allocation: the listed paths, growth within the tree
///
/// # Adequacy
/// - hypothesis: L3 — as [`touched`]; a document of the head left out removes
///   its parse in a prune, which the next run parses again.
/// - witness: `tests::cli::a_prune_keeps_the_head_s_parses_and_removes_the_rest`
#[inline]
pub fn every(root: &Path) -> Result<Vec<String>, ProseError>
{
    listed(root, Listing::Tracked)
}

/// The documents `listing` names under `root`, with the untracked ones.
///
/// # Specification
/// - requires: as [`touched`] and [`every`].
/// - ensures: as [`touched`] for [`Listing::Changed`], and as [`every`] for
///   [`Listing::Tracked`].
/// - fails: as [`touched`].
/// - panics: none.
/// - executable: none — the outcome is git's.
///
/// # Cost
/// - allocation: git's output and the listed paths, growth within the tree
///
/// # Adequacy
/// - hypothesis: L3 — as [`touched`].
/// - witness: `tests::cli::a_document_answers_for_the_paragraphs_its_change_wrote`
fn listed(
    root: &Path,
    listing: Listing<'_>,
) -> Result<Vec<String>, ProseError>
{
    let git = |arguments: &[&str]| {
        let refused = |message: String| ProseError::Io {
            path: root.to_owned(),
            message: format!(
                "git {}: {message}",
                arguments.first().copied().unwrap_or_default()
            ),
        };
        let output = Command::new("git")
            .arg("-C")
            .arg(root)
            .args(arguments)
            .output()
            .map_err(|error| refused(error.to_string()))?;
        if !output.status.success() {
            return Err(refused(
                String::from_utf8_lossy(&output.stderr).trim().to_owned(),
            ));
        }
        Ok(String::from_utf8_lossy(&output.stdout).into_owned())
    };
    let named = match listing {
        Listing::Changed(base) => git(&[
            "diff",
            "--name-only",
            "--no-renames",
            "--diff-filter=d",
            "-z",
            base.0,
            "--",
            "*.md",
        ])?,
        Listing::Tracked => git(&["ls-files", "-z", "--", "*.md"])?,
    };
    let untracked = git(&[
        "ls-files",
        "-z",
        "--others",
        "--exclude-standard",
        "--",
        "*.md",
    ])?;
    let mut paths: Vec<String> = named
        .split('\0')
        .chain(untracked.split('\0'))
        .filter(|path| {
            !path.is_empty()
                && !SET_ASIDE.iter().any(|aside| {
                    if aside.ends_with('/') {
                        path.starts_with(aside)
                    }
                    else {
                        path == aside
                    }
                })
        })
        .map(str::to_owned)
        .collect();
    paths.sort();
    paths.dedup();
    Ok(paths)
}

/// The paragraphs that `base` holds of each document in `paths`.
///
/// # Specification
/// - requires: `root` is a repository checkout that holds `base`.
/// - ensures: the passages [`passage::document`] reads from each path's blob at
///   `base`, in the order of `paths`; a path that `base` lacks gives none. One
///   `git cat-file --batch` reads every blob.
/// - provides: the paragraphs the change did not write, and the text each
///   override changes.
/// - fails: [`ProseError::Io`] naming the root when git cannot start, exits
///   unsuccessfully or prints what a batch read does not print.
/// - panics: none.
/// - executable: none — the outcome is git's.
///
/// # Errors
/// As `fails` lists.
///
/// # Cost
/// - allocation: the batch's input and every blob's text, growth within the
///   touched documents
///
/// # Adequacy
/// - hypothesis: L3 — as [`touched`]; a base paragraph left out refuses a
///   paragraph the change did not write, and a head paragraph read as the
///   base's admits a written one.
/// - witness: `tests::cli::a_document_answers_for_the_paragraphs_its_change_wrote`
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        pool_only_threads,
        reason = "a writer feeds git's stdin while this thread reads its stdout, so neither pipe fills; a pool job must not block on a child process"
    )
)]
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        linear_search_in_loop,
        reason = "the cursor moves past each header it finds, so the loop reads each byte of the batch once"
    )
)]
#[inline]
pub fn held(
    root: &Path,
    base: Base<'_>,
    paths: &[String],
) -> Result<Vec<Passage>, ProseError>
{
    let refused = |message: String| ProseError::Io {
        path: root.to_owned(),
        message: format!("git cat-file: {message}"),
    };
    if paths.is_empty() {
        return Ok(Vec::new());
    }
    let mut input = String::new();
    for path in paths {
        input.push_str(base.0);
        input.push(':');
        input.push_str(path);
        input.push('\n');
    }
    let mut child = Command::new("git")
        .arg("-C")
        .arg(root)
        .args(["cat-file", "--batch"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|error| refused(error.to_string()))?;
    let stdin = child.stdin.take();
    let mut stdout = child.stdout.take();
    let mut printed = Vec::new();
    let read = std::thread::scope(|scope| {
        let writer = scope
            .spawn(move || stdin.map_or(Ok(()), |mut stdin| stdin.write_all(input.as_bytes())));
        let read = stdout
            .as_mut()
            .map_or(Ok(0), |stdout| stdout.read_to_end(&mut printed));
        let written = writer.join().unwrap_or(Ok(()));
        read.and(written)
    });
    read.map_err(|error| refused(error.to_string()))?;
    let output = child
        .wait_with_output()
        .map_err(|error| refused(error.to_string()))?;
    if !output.status.success() {
        return Err(refused(format!(
            "{}: {}",
            output.status,
            String::from_utf8_lossy(&output.stderr).trim()
        )));
    }
    let mut passages = Vec::new();
    let mut rest = printed.as_slice();
    for path in paths {
        let end = rest
            .iter()
            .position(|&byte| byte == b'\n')
            .ok_or_else(|| refused(format!("no header for {path}")))?;
        let header = String::from_utf8_lossy(rest.get(.. end).unwrap_or_default());
        rest = rest.get(end.saturating_add(1) ..).unwrap_or_default();
        if header.ends_with(" missing") {
            continue;
        }
        let size: usize = header
            .rsplit(' ')
            .next()
            .and_then(|size| size.parse().ok())
            .ok_or_else(|| refused(format!("`{header}` names no size for {path}")))?;
        let blob = rest
            .get(.. size)
            .ok_or_else(|| refused(format!("the blob of {path} ends early")))?;
        passages.extend(passage::document(
            Text(path),
            Text(&String::from_utf8_lossy(blob)),
        ));
        rest = rest.get(size.saturating_add(1) ..).unwrap_or_default();
    }
    Ok(passages)
}
