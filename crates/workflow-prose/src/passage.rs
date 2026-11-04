//! The passages the check reads: a gandr source's comment paragraphs, a
//! crate README's prose paragraphs, a rendered diagnostic's message, label and
//! advice, and a pull request's or an issue's body.
//!
//! A passage is a paragraph joined onto one line, so a sentence wrapped over
//! several comment lines parses whole. A list item, a `- see:` reference, a
//! footer line `[label]: target`, a heading, a table, a fenced block and an
//! indented continuation are not paragraphs and are left out: their fragments
//! are not sentences. A body is the exception: each of its list items is a
//! passage of its own.

extern crate alloc;

use alloc::collections::BTreeSet;
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
    /// A gandr source's comment: a `//!`, `///` or `//` paragraph.
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

/// Whether a corpus source opens on a comment run.
///
/// # Specification
/// - provides: the head the shape rules read, or its absence.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Opened
{
    /// The source opens on a comment run.
    Run(Head),
    /// The source does not open on a comment run.
    Absent,
}

/// The opening comment run of a corpus source.
///
/// # Specification
/// - provides: the paragraph count, the references paragraph and the line of
///   the first prose paragraph.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Head
{
    /// The line the run starts on.
    pub line: Line,
    /// The paragraphs of the run, a blank comment line splitting them.
    pub paragraphs: usize,
    /// Whether the references paragraph keeps its line form.
    pub references: References,
    /// The line of the first prose paragraph, when the run has one.
    pub what: WhatLine,
}

/// Whether the references paragraph keeps its line form.
///
/// # Specification
/// - provides: the verdict of the head's last paragraph and its footer.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum References
{
    /// Every line opens with `- see:`, `- owes:` or `- cites:`, or continues
    /// one, and the footer defines each label a `- cites:` line names, each
    /// with a quoted title.
    Shaped,
    /// A line opens with none of the three.
    Broken,
    /// The `- cites:` line at this line names a label that no footer line of
    /// the run defines.
    Unfooted(Line),
    /// The footer line at this line gives its target no quoted title.
    Untitled(Line),
}

/// The line of a head's first prose paragraph.
///
/// # Specification
/// - provides: where the first-sentence rule reads, or that the run has no
///   prose paragraph.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum WhatLine
{
    /// The paragraph starts on this line.
    At(Line),
    /// The run has no prose paragraph.
    None,
}

/// One item comment of a corpus source, after the head.
///
/// # Specification
/// - provides: the prose passages whose sentences the item rule counts.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Item
{
    /// The line the run starts on.
    pub line: Line,
    /// The lines of its prose passages, in order.
    pub prose: Vec<Line>,
}

/// The head and the item comments of one corpus source.
///
/// # Specification
/// - provides: what the head and item rules read of one source.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CommentShape
{
    /// The file, relative to the repository root, `/`-separated.
    pub path: String,
    /// The opening comment run, when the source opens on one.
    pub opened: Opened,
    /// The `///` runs after the head.
    pub items: Vec<Item>,
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

/// The comment markers a source line may open with, the longest first.
const MARKERS: [&str; 3] = ["//!", "///", "//"];

/// The comment paragraphs of a gandr source.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one passage per paragraph of consecutive comment lines of one
///   kind, `//!`, `///` or `//`, a paragraph ending at a blank comment line, a
///   list item, a `- see:` line, a footer line `[label]: target`, a line of
///   another kind or a line that is not a comment; a list item, a `- see:`
///   line, the indented lines continuing either and a footer line are not part
///   of any passage; each passage starts on its first line.
/// - provides: the comments the sentence rules read.
/// - fails: never.
/// - panics: none.
/// - executable: none — the scan is the clause.
///
/// # Adequacy
/// - hypothesis: L3 — a run of two paragraphs, a list with a continued item and
///   a reference beside code, then a `//!` and a `//` run touching; a list item
///   or its continuation kept, a paragraph run across a blank line or a change
///   of kind, or a code line read as comment changes the passages.
/// - witness: `passage::tests::a_comment_run_splits_at_its_blank_lines_and_lists`
#[inline]
#[must_use]
pub fn comments(
    path: Text<'_>,
    text: Text<'_>,
) -> Vec<Passage>
{
    let mut paragraph = Paragraph::new(path, Source::Comment);
    let mut kind = None;
    let mut listed = false;
    for (index, raw) in text.0.lines().enumerate() {
        let line = raw.trim_start();
        let Some((marker, comment)) = MARKERS
            .into_iter()
            .find_map(|marker| line.strip_prefix(marker).map(|rest| (marker, rest)))
        else {
            paragraph.close();
            kind = None;
            listed = false;
            continue;
        };
        if kind != Some(marker) {
            paragraph.close();
            kind = Some(marker);
            listed = false;
        }
        let comment = comment.strip_prefix(' ').unwrap_or(comment);
        let indented = comment.starts_with([' ', '\t']);
        let comment = comment.trim();
        if comment.is_empty() || comment.starts_with("- ") || comment == "-" {
            paragraph.close();
            listed = !comment.is_empty();
            continue;
        }
        if listed && indented {
            continue;
        }
        listed = false;
        if footer_label(Text(comment)).is_some() {
            paragraph.close();
            continue;
        }
        paragraph.push(Line(index.saturating_add(1)), Text(comment));
    }
    paragraph.close();
    paragraph.passages
}

/// The opening of a references line citing a source.
const SEE: &str = "- see:";

/// The opening of a references line naming an issue that owes the rest.
const OWES: &str = "- owes:";

/// The opening of a references line citing a paper through the footer.
const CITES: &str = "- cites:";

/// A label a footer line defines or a `- cites:` line names, its backticks
/// removed.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Label<'text>(&'text str);

/// Whether a footer line gives its target a quoted title.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Titled
{
    /// `[label]: <target> "<title>"`.
    Quoted,
    /// Any other form.
    Bare,
}

/// `label` with the backticks around it removed.
///
/// # Specification
/// trivial.
fn unquoted(label: Text<'_>) -> Label<'_>
{
    Label(
        label
            .0
            .strip_prefix('`')
            .and_then(|quoted| quoted.strip_suffix('`'))
            .unwrap_or(label.0),
    )
}

/// The label the footer line `text` defines, its backticks removed: `text`
/// opens `[label]:`. `None` for any other line.
///
/// # Specification
/// trivial.
fn footer_label(text: Text<'_>) -> Option<Label<'_>>
{
    let (label, _) = text.0.strip_prefix('[')?.split_once("]:")?;
    let label = unquoted(Text(label));
    (!label.0.is_empty()).then_some(label)
}

/// The kind of one comment line.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Kind
{
    /// A `///` line.
    Doc,
    /// A `//!` line.
    Inner,
    /// A `//` line.
    Line,
}

/// One run of comment lines of one kind.
struct Run<'text>
{
    /// The kind.
    kind: Kind,
    /// The zero-based index of its first line.
    first: usize,
    /// Each line's number and text, the marker left out.
    lines: Vec<(Line, &'text str)>,
}

/// The head and the item comments of `text`, read beside `passages`.
///
/// The head is the comment run that starts on the first non-empty line, a
/// shebang left out. An item is a later `///` run. A prose passage is one
/// `passages` already holds whose line falls in the run.
///
/// # Specification
/// - requires: `passages` are [`comments`] of `text`.
/// - ensures: the opening run's paragraph count, its references verdict and the
///   line of its first prose paragraph, and each later `///` run's prose
///   passage lines.
/// - provides: the shape the head and item rules read.
/// - fails: never.
/// - panics: none.
/// - executable: none — the scan is the clause.
///
/// # Adequacy
/// - hypothesis: L3 — a head of four paragraphs, one of three, a references
///   line that opens with neither marker, an item of two prose paragraphs and a
///   later `//` run; another paragraph count or a dropped item changes the
///   shape.
/// - witness: `passage::tests::a_head_counts_its_paragraphs_and_an_item_keeps_its_prose`
#[must_use]
pub(crate) fn comment_shape(
    path: Text<'_>,
    text: Text<'_>,
    passages: &[Passage],
) -> CommentShape
{
    let runs = runs(text);
    let opening = text
        .0
        .lines()
        .position(|line| !line.trim().is_empty() && !line.starts_with("#!"));
    let mut runs = runs.into_iter();
    let opened = match runs.next() {
        Some(run) if Some(run.first) == opening => Opened::Run(head_of(&run)),
        Some(run) => {
            return CommentShape {
                path: path.0.to_owned(),
                opened: Opened::Absent,
                items: items(core::iter::once(run).chain(runs), passages),
            };
        },
        None => Opened::Absent,
    };
    CommentShape {
        path: path.0.to_owned(),
        opened,
        items: items(runs, passages),
    }
}

/// The comment runs of `text`, in order.
///
/// # Specification
/// trivial.
fn runs(text: Text<'_>) -> Vec<Run<'_>>
{
    let mut found: Vec<Run<'_>> = Vec::new();
    let mut open = false;
    for (place, raw) in text.0.lines().enumerate() {
        let trimmed = raw.trim_start();
        let Some(rest) = trimmed.strip_prefix("//")
        else {
            open = false;
            continue;
        };
        let (kind, rest) = match rest.strip_prefix('/') {
            Some(doc) if !doc.starts_with('/') => (Kind::Doc, doc),
            Some(_) => (Kind::Line, rest),
            None => rest
                .strip_prefix('!')
                .map_or((Kind::Line, rest), |inner| (Kind::Inner, inner)),
        };
        let content = rest.strip_prefix(' ').unwrap_or(rest).trim_end();
        let line = (Line(place.saturating_add(1)), content);
        match found.last_mut() {
            Some(run) if open && run.kind == kind => run.lines.push(line),
            _ => found.push(Run {
                kind,
                first: place,
                lines: vec![line],
            }),
        }
        open = true;
    }
    found
}

/// The head facts of `run`. Its footer, the footer lines and the blank lines
/// that end it, belongs to the references paragraph and counts as no
/// paragraph of its own.
///
/// # Specification
/// trivial.
fn head_of(run: &Run<'_>) -> Head
{
    let body = run
        .lines
        .iter()
        .rposition(|&(_, text)| {
            !text.trim().is_empty() && footer_label(Text(text.trim())).is_none()
        })
        .map_or(0, |last| last.saturating_add(1));
    let (lines, footer) = run.lines.split_at(body);
    let mut paragraphs: Vec<Vec<(Line, &str)>> = Vec::new();
    let mut open = false;
    for line in lines {
        if line.1.trim().is_empty() {
            open = false;
            continue;
        }
        match paragraphs.last_mut() {
            Some(paragraph) if open => paragraph.push(*line),
            _ => paragraphs.push(vec![*line]),
        }
        open = true;
    }
    let opens =
        |text: &str| text.starts_with(SEE) || text.starts_with(OWES) || text.starts_with(CITES);
    let continues = |text: &str| opens(text) || text.starts_with(' ') || text.starts_with('\t');
    let listed = paragraphs.last().is_some_and(|lines| {
        lines.first().is_some_and(|&(_, text)| opens(text))
            && lines.iter().all(|&(_, text)| continues(text))
    });
    let split = if listed {
        paragraphs.len().saturating_sub(1)
    }
    else {
        paragraphs.len().min(3)
    };
    let (prose, references) = paragraphs.split_at(split);
    let broken = references
        .iter()
        .flatten()
        .any(|&(_, text)| !continues(text));
    let labels: BTreeSet<Label<'_>> = footer
        .iter()
        .filter_map(|&(_, text)| footer_label(Text(text.trim())))
        .collect();
    // A `- cites:` item reads its labels from its own line and from the
    // indented lines that continue it.
    let unfooted = references.iter().find_map(|paragraph| {
        paragraph
            .iter()
            .enumerate()
            .find(|&(at, &(_, text))| {
                text.strip_prefix(CITES).is_some_and(|cites| {
                    let continued = paragraph
                        .get(at.saturating_add(1) ..)
                        .unwrap_or_default()
                        .iter()
                        .map(|&(_, more)| more)
                        .take_while(|more| more.starts_with([' ', '\t']));
                    let mut named = core::iter::once(cites)
                        .chain(continued)
                        .flat_map(|item| cited(Text(item)))
                        .peekable();
                    named.peek().is_none() || named.any(|label| !labels.contains(&label))
                })
            })
            .map(|(_, &(line, _))| line)
    });
    let untitled = footer
        .iter()
        .find(|&&(_, text)| {
            footer_label(Text(text.trim())).is_some() && titled(Text(text.trim())) == Titled::Bare
        })
        .map(|&(line, _)| line);
    Head {
        line: run.lines.first().map_or(Line(1), |&(line, _)| line),
        paragraphs: paragraphs.len(),
        references: match (broken, unfooted, untitled) {
            (true, ..) => References::Broken,
            (false, Some(line), _) => References::Unfooted(line),
            (false, None, Some(line)) => References::Untitled(line),
            (false, None, None) => References::Shaped,
        },
        what: prose
            .first()
            .and_then(|lines| lines.first().map(|&(line, _)| WhatLine::At(line)))
            .unwrap_or(WhatLine::None),
    }
}

/// The labels a `- cites:` line names after its opening, `cites`: each
/// bracketed label, its backticks removed.
///
/// # Specification
/// trivial.
fn cited(cites: Text<'_>) -> impl Iterator<Item = Label<'_>>
{
    cites
        .0
        .split('[')
        .skip(1)
        .filter_map(|rest| rest.split_once(']').map(|(label, _)| unquoted(Text(label))))
}

/// Whether the footer line `text` gives its target a quoted title, the form
/// a reference definition of `CommonMark` admits: `[label]: <target>
/// "<title>"`.
///
/// # Specification
/// trivial.
fn titled(text: Text<'_>) -> Titled
{
    let quoted = text
        .0
        .split_once("]:")
        .and_then(|(_, rest)| rest.trim().strip_suffix('"'))
        .and_then(|quoted| quoted.split_once(" \""))
        .is_some_and(|(target, title)| !target.trim().is_empty() && !title.trim().is_empty());
    if quoted { Titled::Quoted } else { Titled::Bare }
}

/// The item comments among `runs`, each naming the prose passages it holds.
///
/// # Specification
/// trivial.
fn items<'text, Runs>(
    runs: Runs,
    passages: &[Passage],
) -> Vec<Item>
where
    Runs: IntoIterator<Item = Run<'text>>,
{
    let mut found = Vec::new();
    for run in runs {
        if run.kind != Kind::Doc {
            continue;
        }
        let end = run.first.saturating_add(run.lines.len());
        let prose = passages
            .iter()
            .filter(|passage| {
                let index = passage.line.0.saturating_sub(1);
                index >= run.first && index < end
            })
            .map(|passage| passage.line)
            .collect();
        found.push(Item {
            line: run.lines.first().map_or(Line(1), |&(line, _)| line),
            prose,
        });
    }
    found
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

/// The lines that open and close each block the workflow writes into a body,
/// which no rule reads: `pr:open`'s obligations and the `### Observed` box
/// `evidence:obligations` writes for a defect.
const GENERATED: [(&str, &str); 2] = [
    (
        "<!-- quenchant-obligations:start -->",
        "<!-- quenchant-obligations:end -->",
    ),
    (
        "<!-- gandr-observed:start -->",
        "<!-- gandr-observed:end -->",
    ),
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
///   Every line of a fenced block and of a block the workflow writes between
///   its markers is not read, nor is the text of an HTML comment. Each passage
///   starts on its first line.
/// - provides: the body text the sentence rules read.
/// - fails: never.
/// - panics: none.
/// - executable: none — the scan is the clause.
///
/// # Adequacy
/// - hypothesis: L3 — a body with a paragraph, items, a form item, a fence, a
///   table, a comment, a link line, the obligations block and the observed
///   block; reading any skipped line, or joining two items, changes the
///   passages.
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
        if let Some(&(start, _)) = GENERATED
            .iter()
            .find(|&&(start, end)| trimmed == start || trimmed == end)
        {
            obliged = trimmed == start;
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
    /// The head and item comments of each corpus source outside the features
    /// ledger, in path order.
    pub shapes: Vec<CommentShape>,
    /// The rendered diagnostics, by path.
    pub goldens: Vec<Golden>,
}

/// The directory of the rendered diagnostic goldens.
const GOLDENS: &str = "crates/surface-render-terminal/tests/golden";

/// Reads every tracked gandr source under `root`, every crate README under
/// `root/crates`, and every rendered diagnostic golden.
///
/// # Specification
/// - requires: `root` is a repository checkout.
/// - ensures: the passages of every `.gandr` file git tracks under `root`, in
///   path order, then of every `crates/*/README.md` in path order; the goldens
///   of every `.txt` file under the render goldens, walked in path order.
/// - provides: the check's whole input.
/// - fails: [`ProseError::Io`] naming the directory or file that could not be
///   read, or the root whose tracked files git could not list.
/// - panics: none.
/// - executable: none — the outcome is the file system's.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — a scratch repository with a tracked source outside
///   `corpus/`, a nested one, an untracked one, a README, a golden and a nested
///   golden; a file skipped, an untracked one read, or one read twice or out of
///   order changes the gathered input.
/// - witness: `passage::tests::a_root_gathers_its_sources_readmes_and_goldens`
#[inline]
pub fn gather(root: &Path) -> Result<Gathered, ProseError>
{
    let mut gathered = Gathered::default();
    for key in tracked(root)? {
        let text = read(&root.join(&key))?;
        let passages = comments(Text(&key), Text(&text));
        if key.starts_with("corpus/") && !key.starts_with("corpus/ledger/") {
            gathered
                .shapes
                .push(comment_shape(Text(&key), Text(&text), &passages));
        }
        gathered.passages.extend(passages);
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

/// The `.gandr` files git tracks under `root`, `/`-separated and relative to
/// it, in path order.
///
/// # Specification
/// trivial.
///
/// # Adequacy
/// - hypothesis: L3 — as [`gather`].
/// - witness: `passage::tests::a_root_gathers_its_sources_readmes_and_goldens`
fn tracked(root: &Path) -> Result<Vec<String>, ProseError>
{
    let refused = |message: String| ProseError::Io {
        path: root.to_owned(),
        message,
    };
    let listed = std::process::Command::new("git")
        .arg("-C")
        .arg(root)
        .args(["ls-files", "-z", "--", "*.gandr"])
        .output()
        .map_err(|error| refused(format!("git ls-files: {error}")))?;
    if !listed.status.success() {
        return Err(refused(format!(
            "git ls-files: {}",
            String::from_utf8_lossy(&listed.stderr).trim()
        )));
    }
    let mut keys: Vec<String> = String::from_utf8_lossy(&listed.stdout)
        .split('\0')
        .filter(|key| !key.is_empty())
        .map(str::to_owned)
        .collect();
    keys.sort();
    Ok(keys)
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
    use super::Head;
    use super::Line;
    use super::Opened;
    use super::Placed;
    use super::References;
    use super::Source;
    use super::Text;
    use super::WhatLine;
    use super::body;
    use super::comment_shape;
    use super::comments;
    use super::gather;
    use super::golden;
    use super::readme;

    #[test]
    fn a_comment_run_splits_at_its_blank_lines_and_lists()
    {
        let text = "/// The first paragraph\n/// wraps here.\n///\n/// The second.\n/// - a \
                    list item\n/// - see: #12 — a reference\n///   wrapped onto a second \
                    line\ndef x = 1 ;\n/// Last.\n//! Inner.\n// Line.\n";
        let passages = comments(Text("corpus/a.gandr"), Text(text));
        let read: Vec<(String, String)> = passages
            .iter()
            .map(|passage| (passage.line.to_string(), passage.text.clone()))
            .collect();
        assert_eq!(read, [
            ("1".to_owned(), "The first paragraph wraps here.".to_owned()),
            ("4".to_owned(), "The second.".to_owned()),
            ("9".to_owned(), "Last.".to_owned()),
            ("10".to_owned(), "Inner.".to_owned()),
            ("11".to_owned(), "Line.".to_owned()),
        ]);
        assert!(
            passages.iter().all(
                |passage| passage.source == Source::Comment && passage.path == "corpus/a.gandr"
            )
        );
        assert_eq!(passages.first().map(|passage| passage.line), Some(Line(1)));
    }

    #[test]
    fn a_head_counts_its_paragraphs_and_an_item_keeps_its_prose()
    {
        let shaped = "/// Pairs sum their halves.\n///\n/// The sum is the reading.\n///\n/// \
                      The checker reduces both sides.\n///\n/// - see: #1 — x\n\ndef x = 1;\n/// \
                      One item.\n///\n/// Two.\n// later\n";
        let passages = comments(Text("corpus/a.gandr"), Text(shaped));
        let shape = comment_shape(Text("corpus/a.gandr"), Text(shaped), &passages);
        let Opened::Run(head) = shape.opened
        else {
            panic!("the source opens on a head");
        };
        assert_eq!(head.paragraphs, 4);
        assert_eq!(head.references, References::Shaped);
        assert_eq!(head.what, WhatLine::At(Line(1)));
        assert_eq!(
            shape
                .items
                .iter()
                .map(|item| item
                    .prose
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>())
                .collect::<Vec<_>>(),
            [vec!["10".to_owned(), "12".to_owned()]]
        );
        let short = "/// Pairs sum.\n///\n/// Why.\n///\n/// How.\n";
        let passages = comments(Text("corpus/a.gandr"), Text(short));
        let shape = comment_shape(Text("corpus/a.gandr"), Text(short), &passages);
        let Opened::Run(head) = shape.opened
        else {
            panic!("the short source opens on a head");
        };
        assert_eq!(head.paragraphs, 3);
        let broken = "/// Pairs sum.\n///\n/// Why.\n///\n/// How.\n///\n/// Not implemented: #1\n";
        let passages = comments(Text("corpus/a.gandr"), Text(broken));
        let shape = comment_shape(Text("corpus/a.gandr"), Text(broken), &passages);
        let Opened::Run(head) = shape.opened
        else {
            panic!("the broken source opens on a head");
        };
        assert_eq!(head.references, References::Broken);
        let lines = "// Pairs sum.\n//\n// Why.\n//\n// How.\n//\n// - see: #1 — x\n\n// later\n";
        let passages = comments(Text("corpus/a.gandr"), Text(lines));
        let shape = comment_shape(Text("corpus/a.gandr"), Text(lines), &passages);
        assert!(
            matches!(shape.opened, Opened::Run(_)) && shape.items.is_empty(),
            "a `//` head is judged and a later `//` run is no item"
        );
    }

    #[test]
    fn a_head_cites_through_its_footer()
    {
        let head = |references: &str| {
            let text = format!(
                "//! Pairs sum.\n//!\n//! Why.\n//!\n//! How.\n//!\n{references}\n\ndef x = 1;\n"
            );
            let passages = comments(Text("corpus/a.gandr"), Text(&text));
            let shape = comment_shape(Text("corpus/a.gandr"), Text(&text), &passages);
            let Opened::Run(head) = shape.opened
            else {
                panic!("the source opens on a head");
            };
            (head, passages.len())
        };
        assert_eq!(
            head(
                "//! - see: #1 — x\n//! - cites: [Dybjer-1994-inductive_families]\n//!\n//! \
                 [Dybjer-1994-inductive_families]: https://doi.org/10.1007/BF01211308 \"Dybjer, \
                 Inductive families\""
            ),
            (
                Head {
                    line: Line(1),
                    paragraphs: 4,
                    references: References::Shaped,
                    what: WhatLine::At(Line(1)),
                },
                3
            ),
            "the footer belongs to the references paragraph and is no passage"
        );
        assert_eq!(
            head(
                "//! - cites: [Missing-2020]\n//!\n//! [Other-2020]: https://example.org \"Other\""
            )
            .0
            .references,
            References::Unfooted(Line(7)),
            "a label no footer line defines is refused at its `- cites:` line"
        );
        assert_eq!(
            head(
                "//! - cites: [Dybjer-1994]\n//!\n//! [Dybjer-1994]: https://doi.org/10.1007/BF01211308 — \
                 Dybjer, Inductive families"
            )
            .0
            .references,
            References::Untitled(Line(9)),
            "a footer line whose title is not quoted is refused at its line"
        );
        assert_eq!(
            head(
                "//! - cites:\n//!   [Dybjer-1994], § 3\n//!\n//! [Dybjer-1994]: https://doi.org/10.1007/BF01211308 \
                 \"Dybjer, Inductive families\""
            )
            .0
            .references,
            References::Shaped,
            "a `- cites:` item reads its label from the line that continues it"
        );
        assert_eq!(
            head(
                "//! - cites: [Dybjer-1994]\n//!   and [Missing-2020]\n//!\n//! [Dybjer-1994]: \
                 https://doi.org/10.1007/BF01211308 \"Dybjer, Inductive families\""
            )
            .0
            .references,
            References::Unfooted(Line(7)),
            "a label on a continuing line with no footer line is refused at its item"
        );
        assert_eq!(
            head("//! - cites:").0.references,
            References::Unfooted(Line(7)),
            "a `- cites:` line naming no label is refused"
        );
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
                    by the tool.\n<!-- quenchant-obligations:end -->\n<!-- gandr-observed:start \
                    -->\n- [ ] observed — it was seen by nobody.\n<!-- gandr-observed:end -->\n#12 \
                    holds it.\nLast.\n";
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
            "30:#12 holds it. Last.",
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
                      *{};\n9 │ │ }\n  │ └─┘ checked against `() => Integer`\n";
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
        write("library/std/src/c.gandr", "// Sea.\n");
        write("corpus/ledger/features/d.gandr", "/// Ledger.\n");
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
        let git = |arguments: &[&str]| {
            let status = std::process::Command::new("git")
                .arg("-C")
                .arg(&root)
                .args(arguments)
                .status()
                .unwrap();
            assert!(status.success(), "git {arguments:?}");
        };
        git(&["init", "--quiet"]);
        git(&["add", "."]);
        write("corpus/untracked.gandr", "/// Not tracked.\n");
        let gathered = gather(&root).unwrap();
        let read: Vec<String> = gathered
            .passages
            .iter()
            .map(|passage| format!("{}:{}", passage.path, passage.text))
            .collect();
        assert_eq!(
            read,
            [
                "corpus/a.gandr:Ay.",
                "corpus/ledger/features/d.gandr:Ledger.",
                "corpus/model/b.gandr:Bee.",
                "library/std/src/c.gandr:Sea.",
                "crates/x/README.md:Ex."
            ],
            "every tracked source is read, and an untracked one is not"
        );
        let shaped: Vec<&str> = gathered
            .shapes
            .iter()
            .map(|shape| shape.path.as_str())
            .collect();
        assert_eq!(
            shaped,
            ["corpus/a.gandr", "corpus/model/b.gandr"],
            "the features ledger and a library source keep no head rule"
        );
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
