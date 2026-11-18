//! The files whose prose the check reads under the merge base's paragraph
//! digests: the markdown documents, and the `#` comments of tasks, scripts,
//! workflows, manifests and the lists that tools read.
//!
//! A change answers for the paragraphs it wrote, and for no other. The check
//! reads each file that the change touched, at the head and at the base. A
//! head paragraph whose digest the base holds is one that the change did not
//! write, and the check leaves it alone. Each other paragraph parses and meets
//! every sentence rule, and a finding refuses. No ledger holds a file's debt:
//! a paragraph that no change writes keeps its debt until a change writes it.
//!
//! The documents are the markdown files that the tree tracks, with three kinds
//! set aside. The issue templates and the pull request template are bodies, and
//! the body rules read them. The census and the syntax pages are written by
//! their generators, whose own sources hold the words. A file of `#` comments
//! is one whose syntax [`Syntax::of`] names, by its name, its extension or its
//! shebang. The seeds that proptest writes are set aside, as the words of a
//! tool. An untracked file is read too, so a new page or script meets the
//! rules before its commit.

use std::io::Read as _;
use std::io::Write as _;
use std::path::Path;
use std::process::Command;
use std::process::Stdio;

use crate::error::ProseError;
use crate::passage;
use crate::passage::Passage;
use crate::passage::Text;
use crate::passage::hash;
use crate::passage::hash::Paragraphs;
use crate::passage::hash::Syntax;

/// The revision a change runs from: the merge base of the change and its
/// trunk.
///
/// # Specification
/// - provides: the side whose paragraphs the change did not write.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Base<'rev>(pub &'rev str);

/// The markdown paths the rule sets aside: a directory ends in `/`, and a
/// file is named whole.
const SET_ASIDE: [&str; 4] = [
    ".config/issues/templates/",
    ".github/",
    "ledger/census.md",
    "ledger/syntax.md",
];

/// The directories, named at any depth, whose `#` comments a tool writes.
const WRITTEN_BY_TOOLS: [&str; 1] = ["proptest-regressions"];

/// The reader that a listed file takes.
///
/// # Specification
/// - provides: the one choice between the markdown reader and
///   [`hash::comments`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Kind
{
    /// A markdown document: its prose paragraphs.
    Markdown,
    /// A file of `#` comments, in its syntax.
    Hash(Syntax),
}

impl Kind
{
    /// The paragraphs of `text`, the file at `path`, of this kind.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the passages of [`passage::document`] with no code lines for
    ///   a markdown document; [`hash::comments`] in its syntax for a file of
    ///   `#` comments.
    /// - provides: the one dispatch that the head and the base share.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the dispatch is the clause.
    ///
    /// # Cost
    /// - allocation: the paragraphs, growth within the file
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a change that touches a document and a task file; a
    ///   file read by the other kind's reader changes the paragraphs that the
    ///   change wrote.
    /// - witness: `tests::cli::a_hash_comment_answers_for_the_paragraphs_its_change_wrote`
    #[inline]
    #[must_use]
    pub fn read(
        self,
        path: Text<'_>,
        text: Text<'_>,
    ) -> Paragraphs
    {
        match self {
            Self::Markdown => Paragraphs {
                passages: passage::document(path, text),
                code: 0,
            },
            Self::Hash(syntax) => hash::comments(path, text, syntax),
        }
    }
}

/// A file that the check reads, with its reader.
///
/// # Specification
/// - provides: one row of [`touched`] and [`every`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Listed
{
    /// The path, relative to the checkout's root.
    pub path: String,
    /// The reader that the file takes.
    pub kind: Kind,
}

/// Which files a listing names beside the untracked ones.
///
/// # Specification
/// - provides: the one difference between [`touched`] and [`every`].
#[derive(Clone, Copy, Debug)]
enum Listing<'rev>
{
    /// Each file the working tree adds or alters against the base.
    Changed(Base<'rev>),
    /// Each file the tree tracks.
    Tracked,
}

/// The files the change touched since `base`, by path.
///
/// # Specification
/// - requires: `root` is a repository checkout that holds `base`.
/// - ensures: each file that the working tree adds or alters against `base`,
///   and each untracked one that `.gitignore` admits, whose kind [`kind`]
///   names, sorted by path, each once. A file the change deletes is not listed.
/// - provides: the files whose paragraphs the check reads.
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
///   page listed, the new page missed or the template read changes the list. A
///   second change alters a task file and adds an untracked script; either one
///   missed changes the paragraphs written.
/// - witness: `tests::cli::a_document_answers_for_the_paragraphs_its_change_wrote`
/// - witness: `tests::cli::a_hash_comment_answers_for_the_paragraphs_its_change_wrote`
#[inline]
pub fn touched(
    root: &Path,
    base: Base<'_>,
) -> Result<Vec<Listed>, ProseError>
{
    listed(root, Listing::Changed(base))
}

/// Every file of the head that the check reads, by path.
///
/// # Specification
/// - requires: `root` is a repository checkout.
/// - ensures: each file that the tree tracks, and each untracked one that
///   `.gitignore` admits, whose kind [`kind`] names, sorted by path, each once.
/// - provides: the files whose paragraphs a prune of the parse cache keeps.
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
/// - hypothesis: L3 — as [`touched`]; a file of the head left out removes its
///   parse in a prune, which the next run parses again.
/// - witness: `tests::cli::a_prune_keeps_the_head_s_parses_and_removes_the_rest`
#[inline]
pub fn every(root: &Path) -> Result<Vec<Listed>, ProseError>
{
    listed(root, Listing::Tracked)
}

/// The paragraphs of `file` at the head: its text in the checkout at `root`.
///
/// # Specification
/// - requires: `root` is a repository checkout.
/// - ensures: [`Kind::read`] of the file's text, each byte that is not UTF-8
///   replaced, as [`held`] reads the base.
/// - provides: the head side of a change, and the paragraphs a prune keeps.
/// - fails: [`ProseError::Io`] naming the file when it cannot be read.
/// - panics: none.
/// - executable: none — the outcome is the file system's.
///
/// # Errors
/// As `fails` lists.
///
/// # Cost
/// - allocation: the file's text and paragraphs, growth within the file
///
/// # Adequacy
/// - hypothesis: L3 — as [`touched`].
/// - witness: `tests::cli::a_hash_comment_answers_for_the_paragraphs_its_change_wrote`
#[inline]
pub fn at_head(
    root: &Path,
    file: &Listed,
) -> Result<Paragraphs, ProseError>
{
    let full = root.join(&file.path);
    let bytes = std::fs::read(&full).map_err(|error| ProseError::Io {
        path: full.clone(),
        message: error.to_string(),
    })?;
    Ok(file
        .kind
        .read(Text(&file.path), Text(&String::from_utf8_lossy(&bytes))))
}

/// The reader of the file at `path` under `root`, if the check reads it: a
/// markdown document outside [`SET_ASIDE`], or a file whose syntax
/// [`Syntax::of`] names outside [`WRITTEN_BY_TOOLS`].
///
/// # Specification
/// trivial.
///
/// # Cost
/// - allocation: the first line of a file with no extension, setup
fn kind(
    root: &Path,
    path: Text<'_>,
) -> Option<Kind>
{
    let path = path.0;
    let markdown = Path::new(path)
        .extension()
        .is_some_and(|extension| extension.eq_ignore_ascii_case("md"));
    if markdown {
        let aside = SET_ASIDE.iter().any(|aside| {
            if aside.ends_with('/') {
                path.starts_with(aside)
            }
            else {
                path == *aside
            }
        });
        return (!aside).then_some(Kind::Markdown);
    }
    if path
        .split('/')
        .any(|directory| WRITTEN_BY_TOOLS.contains(&directory))
    {
        return None;
    }
    Syntax::of(Text(path), || first_line(&root.join(path))).map(Kind::Hash)
}

/// The longest a shebang line can be that [`first_line`] reads, in bytes.
const SHEBANG: u64 = 256;

/// The first line of the file at `path`, read from at most its first
/// [`SHEBANG`] bytes; none for a file that cannot be read.
///
/// # Specification
/// trivial.
///
/// # Cost
/// - allocation: the first bytes of the file, setup
fn first_line(path: &Path) -> Option<String>
{
    let mut head = Vec::new();
    std::fs::File::open(path)
        .ok()?
        .take(SHEBANG)
        .read_to_end(&mut head)
        .ok()?;
    let line = head.split(|&byte| byte == b'\n').next()?;
    Some(String::from_utf8_lossy(line).into_owned())
}

/// The files `listing` names under `root`, with the untracked ones.
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
/// - allocation: git's output and the listed files, growth within the tree
///
/// # Adequacy
/// - hypothesis: L3 — as [`touched`].
/// - witness: `tests::cli::a_document_answers_for_the_paragraphs_its_change_wrote`
fn listed(
    root: &Path,
    listing: Listing<'_>,
) -> Result<Vec<Listed>, ProseError>
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
        ])?,
        Listing::Tracked => git(&["ls-files", "-z"])?,
    };
    let untracked = git(&["ls-files", "-z", "--others", "--exclude-standard"])?;
    let mut files: Vec<Listed> = named
        .split('\0')
        .chain(untracked.split('\0'))
        .filter(|path| !path.is_empty())
        .filter_map(|path| {
            kind(root, Text(path)).map(|kind| Listed {
                path: path.to_owned(),
                kind,
            })
        })
        .collect();
    files.sort_by(|left, right| left.path.cmp(&right.path));
    files.dedup_by(|left, right| left.path == right.path);
    Ok(files)
}

/// The paragraphs that `base` holds of each file in `files`.
///
/// # Specification
/// - requires: `root` is a repository checkout that holds `base`.
/// - ensures: the passages [`Kind::read`] reads from each file's blob at
///   `base`, in the order of `files`; a path that `base` lacks gives none. One
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
///   touched files
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
    files: &[Listed],
) -> Result<Vec<Passage>, ProseError>
{
    let refused = |message: String| ProseError::Io {
        path: root.to_owned(),
        message: format!("git cat-file: {message}"),
    };
    if files.is_empty() {
        return Ok(Vec::new());
    }
    let mut input = String::new();
    for file in files {
        input.push_str(base.0);
        input.push(':');
        input.push_str(&file.path);
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
    for file in files {
        let path = &file.path;
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
        passages.extend(
            file.kind
                .read(Text(path), Text(&String::from_utf8_lossy(blob)))
                .passages,
        );
        rest = rest.get(size.saturating_add(1) ..).unwrap_or_default();
    }
    Ok(passages)
}
