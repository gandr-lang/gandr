//! The passages the check reads: a corpus source's `///` paragraphs, a crate
//! README's prose paragraphs, and a rendered diagnostic's message, label and
//! advice.
//!
//! A passage is a paragraph joined onto one line, so a sentence wrapped over
//! several comment lines parses whole. A list item, a `- see:` reference, a
//! heading, a table, a fenced block and an indented continuation are not
//! paragraphs and are left out: their fragments are not sentences.

use core::fmt;
use std::fs;
use std::path::Path;

use crate::error::ProseError;

/// Where a passage was read from.
///
/// # Specification
/// - provides: the three kinds of text the check reads.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Source
{
    /// A corpus source's `///` comment.
    Comment,
    /// A crate README's paragraph.
    Readme,
    /// A rendered diagnostic's advice.
    Diagnostic,
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

/// The rendered diagnostic of a golden file, when its first line is a
/// diagnostic's headline.
///
/// # Specification
/// - requires: nothing.
/// - ensures: for a first line `error[NAME]: MESSAGE`, `warning[NAME]: MESSAGE`
///   or the same without `[NAME]`, a golden whose what is `MESSAGE` on line 1;
///   labelled when a line holds `│`, then a run of `─` or `━`, a space and
///   text; the first `help:` line's text as its advice, else tracked when a
///   `note:` line names an issue as `#` and digits, else missing. Any other
///   first line, such as a JSON rendering, gives an empty vector.
/// - provides: the diagnostics the procedural rule reads.
/// - fails: never.
/// - panics: none.
/// - executable: none — the scan is the clause.
///
/// # Adequacy
/// - hypothesis: L3 — a golden with a help line, one tracked by a note, one
///   with neither and no label, and a JSON rendering; a missed label, a note
///   read as help or a JSON line read as a headline changes the golden.
/// - witness: `passage::tests::a_golden_reads_its_what_where_and_advice`
#[inline]
#[must_use]
pub fn golden(
    path: Text<'_>,
    text: Text<'_>,
) -> Vec<Golden>
{
    let mut lines = text.0.lines();
    let Some(headline) = lines.next()
    else {
        return Vec::new();
    };
    let Some(message) = ["error", "warning"].iter().find_map(|severity| {
        let rest = headline.strip_prefix(severity)?;
        let rest = match rest.strip_prefix('[') {
            Some(named) => named.split_once(']')?.1,
            None => rest,
        };
        rest.strip_prefix(": ")
    })
    else {
        return Vec::new();
    };
    let passage = |line: usize, text: &str, source: Source| Passage {
        path: path.0.to_owned(),
        line: Line(line),
        source,
        text: text.trim().to_owned(),
    };
    let mut placed = Placed::Unlabelled;
    let mut help = Vec::new();
    let mut tracked = false;
    for (index, line) in text.0.lines().enumerate().skip(1) {
        if let Some((_, after)) = line.split_once('│') {
            let after = after.trim_start();
            let marks = after.trim_start_matches(['─', '━', '┬', '┯']);
            if marks.len() < after.len() && marks.starts_with(' ') && !marks.trim().is_empty() {
                placed = Placed::Labelled;
            }
        }
        if let Some(advice) = line.trim_start().strip_prefix("help: ") {
            help.push(passage(index.saturating_add(1), advice, Source::Diagnostic));
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
    let advice = match help.into_iter().next() {
        Some(help) => Advice::Help(help),
        None if tracked => Advice::Tracked,
        None => Advice::Missing,
    };
    vec![Golden {
        what: passage(1, message, Source::Diagnostic),
        placed,
        advice,
    }]
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
///   of every `.txt` file of the render goldens, in path order.
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
/// - hypothesis: L3 — a scratch root with a nested corpus source, a README and
///   a golden; a file skipped, read twice or out of order changes the gathered
///   input.
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
    let mut goldens = listed(&root.join(GOLDENS))?;
    goldens.retain(|path| path.extension().is_some_and(|extension| extension == "txt"));
    goldens.sort();
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
            "crates/surface-render-terminal/tests/golden/g.txt"
        ]);
        std::fs::remove_dir_all(&root).unwrap();
    }
}
