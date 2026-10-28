//! The passages the check reads: a corpus source's `///` paragraphs, a crate
//! README's prose paragraphs, a rendered diagnostic's message, label and
//! advice, and a pull request's or an issue's body.
//!
//! A passage is a paragraph joined onto one line, so a sentence wrapped over
//! several comment lines parses whole. A list item, a `- see:` reference, a
//! heading, a table, a fenced block and an indented continuation are not
//! paragraphs and are left out: their fragments are not sentences. A body is
//! the exception: each of its list items is a passage of its own.

use core::fmt;
use std::fs;
use std::path::Path;

use crate::error::ProseError;

/// Where a passage was read from.
///
/// # Specification
/// - provides: the four kinds of text the check reads.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Source
{
    /// A corpus source's `///` comment.
    Comment,
    /// A crate README's paragraph.
    Readme,
    /// A rendered diagnostic's advice.
    Diagnostic,
    /// A pull request's or an issue's body.
    Body,
}

/// A one-based line number in a file.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Line(usize);

impl fmt::Display for Line
{
    /// Writes the number in decimal.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a finding names its line, so writing nothing changes
    ///   the line printed.
    /// - witness: `passage::tests::a_comment_run_splits_at_its_blank_lines_and_lists`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "{}", self.0)
    }
}

/// Borrowed text a reader splits into passages.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Text<'text>(pub &'text str);

/// One paragraph to parse, and where it came from.
///
/// # Specification
/// - provides: the unit the parser reads and a finding names.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Passage
{
    /// The file, relative to the repository root, `/`-separated.
    pub path: String,
    /// The line the paragraph starts on.
    pub line: Line,
    /// What kind of text it is.
    pub source: Source,
    /// The paragraph, its lines joined by single spaces.
    pub text: String,
}

/// Collects one paragraph's lines into a passage once the paragraph ends.
///
/// # Specification
/// - provides: the paragraph state both readers share.
#[derive(Debug)]
struct Paragraph<'path>
{
    /// The file.
    path: Text<'path>,
    /// The kind of text.
    source: Source,
    /// The open paragraph's first line and text, empty when none is open.
    open: Vec<(Line, String)>,
    /// The passages closed so far.
    passages: Vec<Passage>,
}

impl<'path> Paragraph<'path>
{
    /// No paragraph open and none closed.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as the readers.
    /// - witness: `passage::tests::a_comment_run_splits_at_its_blank_lines_and_lists`
    fn new(
        path: Text<'path>,
        source: Source,
    ) -> Self
    {
        Self {
            path,
            source,
            open: Vec::new(),
            passages: Vec::new(),
        }
    }

    /// Adds `text`, on line `line`, to the open paragraph, opening one if none
    /// is.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a two-line paragraph joins on one space and keeps its
    ///   first line; another join or line changes the passage.
    /// - witness: `passage::tests::a_comment_run_splits_at_its_blank_lines_and_lists`
    fn push(
        &mut self,
        line: Line,
        text: Text<'_>,
    )
    {
        if let Some(&mut (_, ref mut joined)) = self.open.first_mut() {
            joined.push(' ');
            joined.push_str(text.0.trim());
        }
        else {
            self.open.push((line, text.0.trim().to_owned()));
        }
    }

    /// Closes the open paragraph, if any, into a passage.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a blank line ends a paragraph; a paragraph left open
    ///   or closed twice changes the passages.
    /// - witness: `passage::tests::a_comment_run_splits_at_its_blank_lines_and_lists`
    fn close(&mut self)
    {
        for (line, text) in self.open.drain(..) {
            self.passages.push(Passage {
                path: self.path.0.to_owned(),
                line,
                source: self.source,
                text,
            });
        }
    }
}

/// The `///` paragraphs of a corpus source.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one passage per paragraph of consecutive `///` lines, a paragraph
///   ending at a blank `///` line, a list item, a `- see:` line or a line that
///   is not a `///` comment; a list item and a `- see:` line are not part of
///   any passage; each passage starts on its first line.
/// - provides: the comments the sentence rules read.
/// - fails: never.
/// - panics: none.
/// - executable: none — the scan is the clause.
///
/// # Adequacy
/// - hypothesis: L3 — a run of two paragraphs, a list and a reference beside
///   code; a list item kept, a paragraph run across a blank line, or a code
///   line read as comment changes the passages.
/// - witness: `passage::tests::a_comment_run_splits_at_its_blank_lines_and_lists`
#[inline]
#[must_use]
pub fn comments(
    path: Text<'_>,
    text: Text<'_>,
) -> Vec<Passage>
{
    let mut paragraph = Paragraph::new(path, Source::Comment);
    for (index, raw) in text.0.lines().enumerate() {
        let Some(comment) = raw.trim_start().strip_prefix("///")
        else {
            paragraph.close();
            continue;
        };
        let comment = comment.trim();
        if comment.is_empty() || comment.starts_with("- ") || comment == "-" {
            paragraph.close();
            continue;
        }
        paragraph.push(Line(index.saturating_add(1)), Text(comment));
    }
    paragraph.close();
    paragraph.passages
}

/// The prose paragraphs of a Markdown file.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one passage per paragraph of consecutive plain lines, a paragraph
///   ending at a blank line; a heading, a table row, a list item, an indented
///   line, an HTML line and every line of a fenced block are not part of any
///   passage and end the open paragraph.
/// - provides: the README text the sentence rules read.
/// - fails: never.
/// - panics: none.
/// - executable: none — the scan is the clause.
///
/// # Adequacy
/// - hypothesis: L3 — a heading, a fenced block holding prose-like text, a
///   table, a list and two paragraphs; reading inside the fence, or joining
///   across the heading, changes the passages.
/// - witness: `passage::tests::a_readme_keeps_its_paragraphs_alone`
#[inline]
#[must_use]
pub fn readme(
    path: Text<'_>,
    text: Text<'_>,
) -> Vec<Passage>
{
    let mut paragraph = Paragraph::new(path, Source::Readme);
    let mut fenced = false;
    for (index, raw) in text.0.lines().enumerate() {
        if raw.trim_start().starts_with("```") {
            fenced = !fenced;
            paragraph.close();
            continue;
        }
        let structural = raw.trim().is_empty()
            || raw.starts_with([' ', '\t', '#', '|', '<', '-', '*', '>'])
            || raw.split_once(". ").is_some_and(|(number, _)| {
                !number.is_empty() && number.bytes().all(|byte| byte.is_ascii_digit())
            });
        if fenced || structural {
            paragraph.close();
            continue;
        }
        paragraph.push(Line(index.saturating_add(1)), Text(raw));
    }
    paragraph.close();
    paragraph.passages
}

/// The lines that open and close the block `pr:open` writes, which no rule
/// reads.
const OBLIGATIONS: [&str; 2] = [
    "<!-- quenchant-obligations:start -->",
    "<!-- quenchant-obligations:end -->",
];

/// The keywords of a line that only links issues.
const LINKS: [&str; 5] = ["Closes ", "Fixes ", "Resolves ", "Advances ", "Part of "];

/// Whether an HTML comment is open at a line's edge.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Comment
{
    /// No comment is open.
    Closed,
    /// A comment opened and has not closed.
    Open,
}

/// `line` with its HTML comments left out, given the comment state where it
/// starts, and the state where it ends.
///
/// # Specification
/// trivial.
///
/// # Adequacy
/// - hypothesis: L3 — a comment inside a line and one across lines are left
///   out; a comment kept, or text after its close dropped, changes the
///   passages.
/// - witness: `passage::tests::a_body_reads_its_paragraphs_and_items`
fn uncommented(
    line: Text<'_>,
    start: Comment,
) -> (String, Comment)
{
    let mut kept = String::new();
    let mut rest = line.0;
    let mut state = start;
    loop {
        let marker = match state {
            Comment::Open => "-->",
            Comment::Closed => "<!--",
        };
        let Some((before, after)) = rest.split_once(marker)
        else {
            if state == Comment::Closed {
                kept.push_str(rest);
            }
            return (kept, state);
        };
        state = match state {
            Comment::Open => Comment::Closed,
            Comment::Closed => {
                kept.push_str(before);
                Comment::Open
            },
        };
        rest = after;
    }
}

/// The text of a list item, its marker and any checkbox left out, or nothing
/// when `line` is not a list item.
///
/// # Specification
/// trivial.
///
/// # Adequacy
/// - hypothesis: L3 — a dash, a star and a numbered item are items and a
///   sentence is not; another reading joins an item to its neighbour.
/// - witness: `passage::tests::a_body_reads_its_paragraphs_and_items`
fn itemised(line: Text<'_>) -> Option<Text<'_>>
{
    let item = ["- ", "* ", "+ "]
        .into_iter()
        .find_map(|marker| line.0.strip_prefix(marker))
        .or_else(|| {
            let (number, rest) = line.0.split_once(". ")?;
            (!number.is_empty() && number.bytes().all(|byte| byte.is_ascii_digit())).then_some(rest)
        })?;
    Some(Text(
        ["[x] ", "[X] ", "[ ] "]
            .into_iter()
            .find_map(|checkbox| item.strip_prefix(checkbox))
            .unwrap_or(item),
    ))
}

/// The text after the label `text` opens with: a few lowercase words and a
/// colon, as `taken:` or `stays design:`. Nothing when it opens with none.
///
/// # Specification
/// trivial.
///
/// # Adequacy
/// - hypothesis: L3 — `taken: the binary` loses its label and `the cache is
///   stale` has none; a label read in prose changes the passages.
/// - witness: `passage::tests::a_body_reads_its_paragraphs_and_items`
fn unlabelled(text: Text<'_>) -> Option<Text<'_>>
{
    let (label, after) = text.0.split_once(": ")?;
    (!label.is_empty()
        && label.len() <= 24
        && label
            .bytes()
            .all(|byte| byte.is_ascii_lowercase() || b" /-".contains(&byte)))
    .then_some(Text(after))
}

/// The part of a list item a reader parses. An item of the form a mechanism
/// writes, a head, a dash and an answer, is read from its answer: a head
/// holding code or an issue, or an answer opening with a label, marks the
/// form. The answer's label and a leading `no —` or `yes —` are left out.
///
/// # Specification
/// trivial.
///
/// # Adequacy
/// - hypothesis: L3 — a `## Sources read` item, a `no —` reading and a plain
///   item with a dash; reading the head, or the plain item's answer alone,
///   changes the passages.
/// - witness: `passage::tests::a_body_reads_its_paragraphs_and_items`
fn answered(item: Text<'_>) -> Text<'_>
{
    let Some((head, answer)) = item.0.split_once(" — ")
    else {
        return item;
    };
    let label = unlabelled(Text(answer));
    if !(head.contains('`') || head.starts_with('#') || label.is_some()) {
        return item;
    }
    let answer = label.map_or(answer, |after| after.0);
    Text(
        ["no — ", "yes — "]
            .into_iter()
            .find_map(|verdict| answer.strip_prefix(verdict))
            .unwrap_or(answer),
    )
}

/// The prose of a pull request's or an issue's body.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one passage per paragraph of consecutive plain lines and one per
///   list item, an item's indented continuation lines joining it; an item of a
///   mechanism's form is read from its answer, as [`answered`] states. A blank
///   line, a heading, a table row, a quotation, an HTML line, a line that only
///   links issues and a `from:` line end the open passage and are not read.
///   Every line of a fenced block and of the block `pr:open` writes between its
///   obligations markers is not read, nor is the text of an HTML comment. Each
///   passage starts on its first line.
/// - provides: the body text the sentence rules read.
/// - fails: never.
/// - panics: none.
/// - executable: none — the scan is the clause.
///
/// # Adequacy
/// - hypothesis: L3 — a body with a paragraph, items, a form item, a fence, a
///   table, a comment, a link line and the obligations block; reading any
///   skipped line, or joining two items, changes the passages.
/// - witness: `passage::tests::a_body_reads_its_paragraphs_and_items`
#[inline]
#[must_use]
pub fn body(
    path: Text<'_>,
    text: Text<'_>,
) -> Vec<Passage>
{
    let mut paragraph = Paragraph::new(path, Source::Body);
    let mut fenced = false;
    let mut obliged = false;
    let mut commented = Comment::Closed;
    for (index, raw) in text.0.lines().enumerate() {
        let trimmed = raw.trim();
        if OBLIGATIONS.contains(&trimmed) {
            obliged = trimmed == OBLIGATIONS[0];
            paragraph.close();
            continue;
        }
        if trimmed.starts_with("```") || trimmed.starts_with("~~~") {
            fenced = !fenced;
            paragraph.close();
            continue;
        }
        if fenced || obliged {
            continue;
        }
        let (kept, state) = uncommented(Text(raw), commented);
        commented = state;
        let bare = kept.trim();
        let linking = bare.starts_with("from:")
            || LINKS.into_iter().any(|keyword| {
                bare.strip_prefix(keyword).is_some_and(|issues| {
                    issues
                        .bytes()
                        .all(|byte| byte.is_ascii_digit() || b"#, ".contains(&byte))
                })
            });
        let unhashed = bare.trim_start_matches('#');
        let heading =
            unhashed.len() != bare.len() && (unhashed.is_empty() || unhashed.starts_with(' '));
        if bare.is_empty() || heading || bare.starts_with(['|', '<', '>']) || linking {
            paragraph.close();
            continue;
        }
        let line = Line(index.saturating_add(1));
        if let Some(item) = itemised(Text(bare)) {
            paragraph.close();
            paragraph.push(line, answered(item));
            continue;
        }
        paragraph.push(line, Text(bare));
    }
    paragraph.close();
    paragraph.passages
}

/// Whether a rendered diagnostic labels its span.
///
/// # Specification
/// - provides: the where of the procedural form.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Placed
{
    /// A label under the source names the span.
    Labelled,
    /// No label names it.
    Unlabelled,
}

/// What a rendered diagnostic tells the reader to do.
///
/// # Specification
/// - provides: the what-to-do of the procedural form.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Advice
{
    /// A `help:` line, to be read as an imperative sentence.
    Help(Passage),
    /// A note naming the issue that tracks the refusal.
    Tracked,
    /// Neither.
    Missing,
}

/// A rendered diagnostic golden, read for the procedural form.
///
/// # Specification
/// - provides: the what, the where and the what-to-do of one diagnostic.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Golden
{
    /// The headline's message: what is wrong.
    pub what: Passage,
    /// Whether a label names the span.
    pub placed: Placed,
    /// What the reader is told to do.
    pub advice: Advice,
}

/// The rendered diagnostics of a golden file, when its first line is a
/// diagnostic's headline: one for each headline, read up to the next.
///
/// # Specification
/// - requires: nothing.
/// - ensures: for each line `error[NAME]: MESSAGE`, `warning[NAME]: MESSAGE` or
///   the same without `[NAME]`, in order, a golden whose what is `MESSAGE` at
///   that line; labelled when a line before the next headline holds `│` after a
///   blank gutter, where no source line is quoted, then the drawing of the
///   margin, the marks and their connectors (`│`, `┃`, corners, `─`, `━`, `┬`,
///   `┯`, spaces), a space last, then text; the first `help:` line's text
///   there, at the start of the line or after the group's rule (`╰ help:`), as
///   its advice, else tracked when a `note:` line there names an issue as `#`
///   and digits, else missing. A file whose first line is no headline, such as
///   a JSON rendering, gives an empty vector.
/// - provides: the diagnostics the procedural rule reads.
/// - fails: never.
/// - panics: none.
/// - executable: none — the scan is the clause.
///
/// # Adequacy
/// - hypothesis: L3 — a golden with a help line, one tracked by a note, one
///   with neither and no label, a JSON rendering, a file of two diagnostics,
///   the first labelled and helped inside its group and the second neither, one
///   labelled only under a span's nested margin (`│ └─┘ label`), one labelled
///   only from a mark's connector, and one whose quoted line holds text after
///   `│` with no label; a missed label, a quoted line read as one, a help
///   missed after the group's rule, a note read as help, a JSON line read as a
///   headline, or a second diagnostic missed or read into the first changes the
///   goldens.
/// - witness: `passage::tests::a_golden_reads_its_what_where_and_advice`
#[inline]
#[must_use]
pub fn golden(
    path: Text<'_>,
    text: Text<'_>,
) -> Vec<Golden>
{
    /// The message of a diagnostic's headline, when `line` is one.
    ///
    /// # Specification
    /// trivial.
    fn headline(line: Text<'_>) -> Option<Text<'_>>
    {
        ["error", "warning"].iter().find_map(|severity| {
            let rest = line.0.strip_prefix(severity)?;
            let rest = match rest.strip_prefix('[') {
                Some(named) => named.split_once(']')?.1,
                None => rest,
            };
            rest.strip_prefix(": ").map(Text)
        })
    }
    if text.0.lines().next().map(Text).and_then(headline).is_none() {
        return Vec::new();
    }
    let passage = |line: usize, text: &str, source: Source| Passage {
        path: path.0.to_owned(),
        line: Line(line),
        source,
        text: text.trim().to_owned(),
    };
    let lines: Vec<&str> = text.0.lines().collect();
    let starts: Vec<usize> = lines
        .iter()
        .enumerate()
        .filter_map(|(index, line)| headline(Text(line)).map(|_| index))
        .collect();
    let mut goldens = Vec::with_capacity(starts.len());
    for (at, &start) in starts.iter().enumerate() {
        let end = starts
            .get(at.saturating_add(1))
            .copied()
            .unwrap_or(lines.len());
        let Some(Text(message)) = lines.get(start).copied().map(Text).and_then(headline)
        else {
            continue;
        };
        let mut placed = Placed::Unlabelled;
        let mut help = None;
        let mut tracked = false;
        for (index, line) in lines
            .iter()
            .enumerate()
            .take(end)
            .skip(start.saturating_add(1))
        {
            if let Some((gutter, after)) = line.split_once('│')
                && gutter.trim().is_empty()
            {
                let text = after.trim_start_matches([
                    ' ', '│', '┃', '┌', '┏', '└', '┗', '┘', '┛', '─', '━', '┬', '┯',
                ]);
                let drawn = after
                    .get(.. after.len().saturating_sub(text.len()))
                    .unwrap_or("");
                if drawn.ends_with(' ') && !text.trim().is_empty() {
                    placed = Placed::Labelled;
                }
            }
            if help.is_none()
                && let Some(advice) = line
                    .trim_start_matches([' ', '╰', '├', '│', '='])
                    .strip_prefix("help: ")
            {
                help = Some(passage(index.saturating_add(1), advice, Source::Diagnostic));
            }
            if let Some((_, note)) = line.split_once("note: ") {
                tracked |= note.split('#').skip(1).any(|after| {
                    after
                        .bytes()
                        .next()
                        .is_some_and(|byte| byte.is_ascii_digit())
                });
            }
        }
        let advice = match help {
            Some(help) => Advice::Help(help),
            None if tracked => Advice::Tracked,
            None => Advice::Missing,
        };
        goldens.push(Golden {
            what: passage(start.saturating_add(1), message, Source::Diagnostic),
            placed,
            advice,
        });
    }
    goldens
}

/// Everything the check reads under a repository root.
///
/// # Specification
/// - provides: the passages the sentence rules read and the goldens the
///   procedural rule reads.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Gathered
{
    /// The comment and README passages, by path then line.
    pub passages: Vec<Passage>,
    /// The rendered diagnostics, by path.
    pub goldens: Vec<Golden>,
}

/// The directory of the rendered diagnostic goldens.
const GOLDENS: &str = "crates/surface-render-terminal/tests/golden";

/// Reads every corpus source under `root/corpus`, every crate README under
/// `root/crates`, and every rendered diagnostic golden.
///
/// # Specification
/// - requires: `root` is a repository checkout.
/// - ensures: the passages of every `.gandr` file under `corpus/`, walked in
///   path order, then of every `crates/*/README.md` in path order; the goldens
///   of every `.txt` file under the render goldens, walked in path order.
/// - provides: the check's whole input.
/// - fails: [`ProseError::Io`] naming the directory or file that could not be
///   read.
/// - panics: none.
/// - executable: none — the outcome is the file system's.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — a scratch root with a nested corpus source, a README, a
///   golden and a nested golden; a file skipped, read twice or out of order
///   changes the gathered input.
/// - witness: `passage::tests::a_root_gathers_its_sources_readmes_and_goldens`
#[inline]
pub fn gather(root: &Path) -> Result<Gathered, ProseError>
{
    let mut gathered = Gathered::default();
    let mut sources = Vec::new();
    walk(&root.join("corpus"), &mut sources)?;
    sources.retain(|path| {
        path.extension()
            .is_some_and(|extension| extension == "gandr")
    });
    for path in &sources {
        let key = relative(root, path);
        gathered
            .passages
            .extend(comments(Text(&key), Text(&read(path)?)));
    }
    let mut readmes: Vec<_> = listed(&root.join("crates"))?
        .into_iter()
        .map(|crate_dir| crate_dir.join("README.md"))
        .filter(|path| path.is_file())
        .collect();
    readmes.sort();
    for path in &readmes {
        let key = relative(root, path);
        gathered
            .passages
            .extend(readme(Text(&key), Text(&read(path)?)));
    }
    let mut goldens = Vec::new();
    walk(&root.join(GOLDENS), &mut goldens)?;
    goldens.retain(|path| path.extension().is_some_and(|extension| extension == "txt"));
    for path in &goldens {
        let key = relative(root, path);
        gathered
            .goldens
            .extend(golden(Text(&key), Text(&read(path)?)));
    }
    Ok(gathered)
}

/// `path` relative to `root`, `/`-separated.
///
/// # Specification
/// trivial.
///
/// # Adequacy
/// - hypothesis: L3 — as [`gather`].
/// - witness: `passage::tests::a_root_gathers_its_sources_readmes_and_goldens`
fn relative(
    root: &Path,
    path: &Path,
) -> String
{
    path.strip_prefix(root)
        .unwrap_or(path)
        .components()
        .map(|component| component.as_os_str().to_string_lossy())
        .collect::<Vec<_>>()
        .join("/")
}

/// The text of `path`.
///
/// # Specification
/// trivial.
///
/// # Adequacy
/// - hypothesis: L3 — as [`gather`].
/// - witness: `passage::tests::a_root_gathers_its_sources_readmes_and_goldens`
fn read(path: &Path) -> Result<String, ProseError>
{
    fs::read_to_string(path).map_err(|error| ProseError::Io {
        path: path.to_owned(),
        message: error.to_string(),
    })
}

/// The entries of `dir`, unsorted.
///
/// # Specification
/// trivial.
///
/// # Adequacy
/// - hypothesis: L3 — as [`gather`].
/// - witness: `passage::tests::a_root_gathers_its_sources_readmes_and_goldens`
fn listed(dir: &Path) -> Result<Vec<std::path::PathBuf>, ProseError>
{
    let io = |error: std::io::Error| ProseError::Io {
        path: dir.to_owned(),
        message: error.to_string(),
    };
    fs::read_dir(dir)
        .map_err(io)?
        .map(|entry| entry.map(|entry| entry.path()).map_err(io))
        .collect()
}

/// Every file under `dir`, in path order, followed by its subdirectories.
///
/// # Specification
/// trivial.
///
/// # Adequacy
/// - hypothesis: L3 — as [`gather`].
/// - witness: `passage::tests::a_root_gathers_its_sources_readmes_and_goldens`
fn walk(
    dir: &Path,
    files: &mut Vec<std::path::PathBuf>,
) -> Result<(), ProseError>
{
    let mut pending = vec![dir.to_owned()];
    while let Some(next) = pending.pop() {
        let mut entries = listed(&next)?;
        entries.sort();
        for entry in entries.into_iter().rev() {
            if entry.is_dir() {
                pending.push(entry);
            }
            else {
                files.push(entry);
            }
        }
    }
    files.sort();
    Ok(())
}

#[cfg(test)]
mod tests
{
    use super::Advice;
    use super::Line;
    use super::Placed;
    use super::Source;
    use super::Text;
    use super::body;
    use super::comments;
    use super::gather;
    use super::golden;
    use super::readme;

    #[test]
    fn a_comment_run_splits_at_its_blank_lines_and_lists()
    {
        let text = "/// The first paragraph\n/// wraps here.\n///\n/// The second.\n/// - a \
                    list item\n/// - see: #12\ndef x = 1 ;\n/// Last.\n";
        let passages = comments(Text("corpus/a.gandr"), Text(text));
        let read: Vec<(String, String)> = passages
            .iter()
            .map(|passage| (passage.line.to_string(), passage.text.clone()))
            .collect();
        assert_eq!(read, [
            ("1".to_owned(), "The first paragraph wraps here.".to_owned()),
            ("4".to_owned(), "The second.".to_owned()),
            ("8".to_owned(), "Last.".to_owned()),
        ]);
        assert!(
            passages.iter().all(
                |passage| passage.source == Source::Comment && passage.path == "corpus/a.gandr"
            )
        );
        assert_eq!(passages.first().map(|passage| passage.line), Some(Line(1)));
    }

    #[test]
    fn a_readme_keeps_its_paragraphs_alone()
    {
        let text = "# Title\n\nOne paragraph\nwrapped.\n\n```sh\nThis is code that reads like \
                    prose.\n```\n\n| a | b |\n\n- an item\n  continued\n1. numbered\n\nTwo.\n";
        let read: Vec<String> = readme(Text("crates/x/README.md"), Text(text))
            .into_iter()
            .map(|passage| format!("{}:{}", passage.line, passage.text))
            .collect();
        assert_eq!(read, ["3:One paragraph wrapped.", "16:Two."]);
    }

    #[test]
    fn a_body_reads_its_paragraphs_and_items()
    {
        let text = "## Observed\n\nThe gate reads\nthe body. <!-- hidden -->\n\n- one item\n  \
                    continued\n- [x] `main.rs` — taken: the binary reads it\n- `univalent` — no \
                    — nothing is transported\n- the cache is stale — it fails\n1. numbered\n\n```sh\n\
                    This was code.\n```\n\n| a | b |\n> quoted text\n<!--\nhidden too\n-->\nCloses \
                    #12, #13\nfrom: the owner\n<!-- quenchant-obligations:start -->\nIt was written \
                    by the tool.\n<!-- quenchant-obligations:end -->\n#12 holds it.\nLast.\n";
        let passages = body(Text("pr.md"), Text(text));
        let read: Vec<String> = passages
            .iter()
            .map(|passage| format!("{}:{}", passage.line, passage.text))
            .collect();
        assert_eq!(read, [
            "3:The gate reads the body.",
            "6:one item continued",
            "8:the binary reads it",
            "9:nothing is transported",
            "10:the cache is stale — it fails",
            "11:numbered",
            "27:#12 holds it. Last.",
        ]);
        assert!(
            passages
                .iter()
                .all(|passage| passage.source == Source::Body)
        );
    }

    #[test]
    fn a_golden_reads_its_what_where_and_advice()
    {
        let helped = "warning[explicit-exits]: this path ends without its exit\n  ╭▸ a.gandr:2:38\n  \
                      │\n2 │ def kept\n  │     ━━━━ this body\n  ╰╴\nhelp: apply this edit\n";
        let read = golden(Text("g/helped.txt"), Text(helped));
        let [ref one] = read[..]
        else {
            panic!("{read:?}");
        };
        assert_eq!(one.what.text, "this path ends without its exit");
        assert_eq!(one.placed, Placed::Labelled);
        assert!(
            matches!(one.advice, Advice::Help(ref help) if help.text == "apply this edit" && help.line == Line(7))
        );
        let tracked = "error[OutOfFragment.typed_number]: the typed number is not supported yet\n  \
                       │\n  ├ note: `half` is expected to check\n  ╰ note: tracked by #2563 <url>\n";
        let read = golden(Text("g/tracked.txt"), Text(tracked));
        assert!(
            matches!(read[..], [ref one] if one.advice == Advice::Tracked && one.placed == Placed::Unlabelled),
            "{read:?}"
        );
        let bare = "error: `answer` states refuses UnresolvedName\n  ╰ note: `a` is expected to \
                    check\n";
        let read = golden(Text("g/bare.txt"), Text(bare));
        assert!(
            matches!(read[..], [ref one] if one.advice == Advice::Missing && one.what.text.starts_with("`answer`")),
            "{read:?}"
        );
        assert!(golden(Text("g/json.txt"), Text("{\"severity\":\"error\"}\n")).is_empty());
        let two = "error[A]: first\n  │\n1 │ def a\n  │ ━━━━━ the first\n  ╰ help: write it\n\nerror[B]: \
                   second\n  ╰ note: `b` is expected to check\n";
        let read = golden(Text("g/two.txt"), Text(two));
        let [ref first, ref second] = read[..]
        else {
            panic!("two diagnostics: {read:?}");
        };
        assert_eq!(
            (first.what.text.as_str(), first.placed),
            ("first", Placed::Labelled)
        );
        assert!(
            matches!(first.advice, Advice::Help(ref help) if help.text == "write it" && help.line == Line(5)),
            "a help inside the group is read after its rule: {:?}",
            first.advice
        );
        assert_eq!(
            (
                second.what.text.as_str(),
                second.what.line,
                second.placed,
                &second.advice
            ),
            ("second", Line(7), Placed::Unlabelled, &Advice::Missing),
            "the second reads nothing of the first"
        );
        let nested = "error[C]: third\n  │\n7 │   def f() -> Integer {\n  │ ┌─┘\n8 │ │   pure \
                      unit;\n9 │ │ }\n  │ └─┘ checked against `() => Integer`\n";
        let hung = "error[D]: fourth\n   │\n17 │ def m = (f : g);\n   │         ┬───┯━\n   │      \
                    \x20  │   │\n   │         │   its type does not convert\n   │         the type \
                    it synthesises\n";
        let unlabelled = "error[E]: fifth\n  │\n3 │ │ def a = b;\n  │ ━━━━\n";
        for (path, text, placed) in [
            ("g/nested.txt", nested, Placed::Labelled),
            ("g/hung.txt", hung, Placed::Labelled),
            ("g/unlabelled.txt", unlabelled, Placed::Unlabelled),
        ] {
            let read = golden(Text(path), Text(text));
            assert!(
                matches!(read[..], [ref one] if one.placed == placed),
                "a label under a nested margin or hung from a connector places the span, and a \
                 quoted line does not: {path} {read:?}"
            );
        }
    }

    #[test]
    fn a_root_gathers_its_sources_readmes_and_goldens()
    {
        let root = std::env::temp_dir().join(format!("workflow-prose-{}", std::process::id()));
        drop(std::fs::remove_dir_all(&root));
        let write = |path: &str, text: &str| {
            let path = root.join(path);
            std::fs::create_dir_all(path.parent().unwrap()).unwrap();
            std::fs::write(path, text).unwrap();
        };
        write("corpus/model/b.gandr", "/// Bee.\n");
        write("corpus/a.gandr", "/// Ay.\n");
        write("corpus/notes.txt", "/// Not a source.\n");
        write("crates/x/README.md", "Ex.\n");
        write("crates/x/src/lib.rs", "/// Not read.\n");
        write(
            "crates/surface-render-terminal/tests/golden/g.txt",
            "error[E]: wrong\nhelp: fix it\n",
        );
        write(
            "crates/surface-render-terminal/tests/golden/corpus/p/h.txt",
            "error[H]: nested\n",
        );
        let gathered = gather(&root).unwrap();
        let read: Vec<String> = gathered
            .passages
            .iter()
            .map(|passage| format!("{}:{}", passage.path, passage.text))
            .collect();
        assert_eq!(read, [
            "corpus/a.gandr:Ay.",
            "corpus/model/b.gandr:Bee.",
            "crates/x/README.md:Ex."
        ]);
        let goldens: Vec<&str> = gathered
            .goldens
            .iter()
            .map(|golden| golden.what.path.as_str())
            .collect();
        assert_eq!(goldens, [
            "crates/surface-render-terminal/tests/golden/corpus/p/h.txt",
            "crates/surface-render-terminal/tests/golden/g.txt"
        ]);
        std::fs::remove_dir_all(&root).unwrap();
    }
}
