//! The fence check: each fenced `gandr` block of the prose, read by the
//! reader.
//!
//! A doc page or a comment that shows gandr source can keep a spelling that
//! the grammar does not read. The reader refuses each retired spelling by
//! name, so [`check`] gives each fenced `gandr` block to the reader and keeps
//! each refusal named `RetiredSpelling.<surface>`. The check holds no list of
//! spellings: the retired forms are the refused rows of the syntax ledger, and
//! a new refused row reaches the check with no change of it.
//!
//! A Markdown file holds its fenced blocks in its lines. A `.rs` or a `.gandr`
//! file holds them in its `//`, `///` and `//!` comments: the reader reads the
//! text after the comment marker and one space. A fence is three or more
//! backticks or tildes. A block opens on a fence whose info string starts with
//! the word `gandr`, and closes on a fence of the same character, at least as
//! long, with no info string. A fence of another language opens a block that
//! the check does not read. A line that is not a comment ends the block of a
//! comment, and a block that the file ends inside is not read.
//!
//! Each block is parsed and lowered as one module. Each other refusal is left
//! alone: a block often holds a fragment, as `f : Integer` in a hover, and the
//! reader refuses a fragment as out of the fragment, never as a retired
//! spelling.

use alloc::collections::BTreeSet;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use gandr_core_term::CoreArena;
use gandr_surface_corpus::Refusal;
use gandr_surface_corpus::RefusalName;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::RetiredForm;
use gandr_surface_lowering::DeclarationOutcome;
use gandr_surface_lowering::LoweringBudget;
use gandr_surface_lowering::LoweringRefusal;
use gandr_surface_lowering::lower_module;
use gandr_surface_lowering::namespace::Recognition;
use gandr_surface_parser::parse;
use gandr_surface_syntax::SourceText;

use super::LedgerFault;

/// The word an info string starts with to mark a block of gandr source.
const GANDR: &str = "gandr";

/// The fewest fence characters that open or close a block.
const FENCE: usize = 3;

/// A line of a file, counted from one.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct LineNumber(usize);

/// A fenced `gandr` block that writes a retired spelling.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FenceFinding
{
    /// The file that holds the block.
    path: PathBuf,
    /// The line of the block's opening fence.
    line: LineNumber,
    /// The retired form that the reader refuses in the block.
    form: RetiredForm,
}

impl core::fmt::Display for FenceFinding
{
    /// Writes the file and the line of the block's fence, the old spelling,
    /// the name of its refusal and the spelling that replaces it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        write!(
            f,
            "{}:{}: the fenced `gandr` block writes `{}`, which the reader refuses as `RetiredSpelling.{}`; write `{}`",
            self.path.display(),
            self.line.0,
            self.form.written().0,
            self.form.surface().0,
            self.form.replaced_by().0,
        )
    }
}

/// What a fence check found.
#[derive(Clone, Debug, Default)]
pub struct FenceReport
{
    /// How many files the check read.
    files: usize,
    /// How many fenced `gandr` blocks the reader read.
    blocks: usize,
    /// Each block that writes a retired spelling, once for each form, in the
    /// order of the files and of their lines.
    findings: Vec<FenceFinding>,
}

impl FenceReport
{
    /// Each block that writes a retired spelling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn findings(&self) -> &[FenceFinding]
    {
        &self.findings
    }
}

impl core::fmt::Display for FenceReport
{
    /// Writes each finding, then the count of the files, of the blocks and of
    /// the findings.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        for finding in &self.findings {
            writeln!(f, "{finding}")?;
        }
        write!(
            f,
            "fences: {} fenced `gandr` blocks read in {} files, {} retired spellings found",
            self.blocks,
            self.files,
            self.findings.len()
        )
    }
}

/// How a file holds its prose.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Prose
{
    /// Each line of a Markdown file.
    Markdown,
    /// The text after the marker of each `//`, `///` and `//!` comment.
    Comments,
    /// A file of another kind, which the check does not read.
    Unread,
}

impl Prose
{
    /// How the file at `path` holds its prose, read off its extension.
    ///
    /// # Specification
    /// trivial.
    fn of(path: &Path) -> Self
    {
        match path.extension().and_then(std::ffi::OsStr::to_str) {
            Some("md") => Self::Markdown,
            Some("rs" | GANDR) => Self::Comments,
            Some(_) | None => Self::Unread,
        }
    }
}

/// An open fence: its character, its width, its indent and whether it opens
/// a block of gandr source.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Fence
{
    /// The fence character, a backtick or a tilde.
    mark: char,
    /// How many fence characters open the block.
    width: usize,
    /// How many spaces stand before the fence, which each line of the block
    /// loses.
    indent: usize,
    /// Whether the info string starts with the word `gandr`.
    gandr: bool,
}

impl Fence
{
    /// The fence that `line` opens, when it opens one.
    ///
    /// # Specification
    /// trivial.
    fn opened(Line(line): Line<'_>) -> Option<Self>
    {
        let rest = line.trim_start_matches(' ');
        let indent = line.len().saturating_sub(rest.len());
        let mark = rest
            .chars()
            .next()
            .filter(|&mark| mark == '`' || mark == '~')?;
        let info = rest.trim_start_matches(mark);
        let width = rest.len().saturating_sub(info.len());
        if width < FENCE || (mark == '`' && info.contains('`')) {
            return None;
        }
        let gandr = info
            .trim()
            .split(|character: char| character.is_whitespace() || character == ',')
            .next()
            == Some(GANDR);
        Some(Self {
            mark,
            width,
            indent,
            gandr,
        })
    }

    /// Whether `line` closes the block this fence opens.
    ///
    /// # Specification
    /// trivial.
    fn closed_by(
        self,
        Line(line): Line<'_>,
    ) -> Closing
    {
        let rest = line.trim_start_matches(' ');
        let after = rest.trim_start_matches(self.mark);
        if rest.len().saturating_sub(after.len()) >= self.width && after.trim().is_empty() {
            Closing::Closes
        }
        else {
            Closing::Holds
        }
    }

    /// `line` without the spaces of the fence's indent.
    ///
    /// # Specification
    /// trivial.
    fn unindented(
        self,
        Line(line): Line<'_>,
    ) -> Line<'_>
    {
        let spaces = line
            .bytes()
            .take(self.indent)
            .take_while(|&byte| byte == b' ')
            .count();
        Line(line.get(spaces ..).unwrap_or(line))
    }
}

/// Whether a line closes an open fence.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Closing
{
    /// The line is a closing fence of the open fence.
    Closes,
    /// The line stands inside the open fence.
    Holds,
}

/// One line of a file, with no line feed.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Line<'text>(&'text str);

/// The whole text of a file of the prose.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct FileText<'text>(&'text str);

/// One fenced `gandr` block: the line of its opening fence and its text.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Block
{
    /// The line of the opening fence.
    line: LineNumber,
    /// The lines between the fences, each ended by a line feed.
    text: String,
}

/// The text of `line` that a file of `prose` holds as prose, when it holds
/// any.
///
/// # Specification
/// trivial.
fn read_as(
    prose: Prose,
    Line(line): Line<'_>,
) -> Option<Line<'_>>
{
    match prose {
        Prose::Markdown => Some(Line(line)),
        Prose::Comments => {
            let rest = line.trim_start().strip_prefix("//")?;
            let rest = rest.strip_prefix(['/', '!']).unwrap_or(rest);
            Some(Line(rest.strip_prefix(' ').unwrap_or(rest)))
        },
        Prose::Unread => None,
    }
}

/// Each fenced `gandr` block of `text`, a file of `prose`, in the order of
/// its lines.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one block for each fence whose info string starts with `gandr`
///   and that a fence of the same character, at least as long and with no info
///   string, closes, with the line of its opening fence and the lines between
///   the fences, each without the opening fence's indent. A fence of another
///   language holds no block. A line that `prose` does not read ends an open
///   fence, and a fence that `text` ends inside holds no block.
/// - panics: none.
///
/// # Cost
/// - allocation: the text of each block, growth within the file
///
/// # Adequacy
/// - hypothesis: L3 — a block in a Markdown file and in a doc comment is read
///   at its fence's line, a fence of another language and a fence inside it are
///   not read, and a block that a line of code cuts is not read.
/// - witness: `ledger::fences::tests::a_retired_spelling_in_a_fenced_block_is_refused_by_name_5190`
/// - witness: `ledger::fences::tests::a_fragment_a_current_block_and_another_language_pass_5190`
/// - witness: `ledger::fences::tests::a_comment_holds_its_block_at_its_fence_s_line_5190`
#[spec(ensures: |ref ret| ret.windows(2).all(|pair| pair.first().map(|block| block.line) < pair.get(1).map(|block| block.line)))]
fn blocks(
    prose: Prose,
    FileText(text): FileText<'_>,
) -> Vec<Block>
{
    let mut blocks = Vec::new();
    let mut open: Option<(Fence, LineNumber, String)> = None;
    for (index, line) in text.lines().enumerate() {
        let Some(read) = read_as(prose, Line(line))
        else {
            open = None;
            continue;
        };
        match open.take() {
            None => {
                open = Fence::opened(read)
                    .map(|fence| (fence, LineNumber(index.saturating_add(1)), String::new()));
            },
            Some((fence, at, body)) if fence.closed_by(read) == Closing::Closes => {
                if fence.gandr {
                    blocks.push(Block {
                        line: at,
                        text: body,
                    });
                }
            },
            Some((fence, at, mut body)) => {
                if fence.gandr {
                    body.push_str(fence.unindented(read).0);
                    body.push('\n');
                }
                open = Some((fence, at, body));
            },
        }
    }
    blocks
}

/// The retired forms that the reader refuses in `block`, each once.
///
/// # Specification
/// - requires: nothing.
/// - ensures: each form `f` such that a refusal of the block's lowering, of the
///   module whole or of one of its declarations, is named `RetiredSpelling(f)`;
///   none when the block does not parse.
/// - panics: none.
/// - executable: none — the predicate would parse and lower the block again,
///   which is the function's own body.
///
/// # Cost
/// - allocation: the block's parse, its arena and its module, setup
///
/// # Adequacy
/// - hypothesis: L3 — a path type that writes its carrier first is refused as
///   its retired form, and a fragment and the current spelling are not.
/// - witness: `ledger::fences::tests::a_retired_spelling_in_a_fenced_block_is_refused_by_name_5190`
/// - witness: `ledger::fences::tests::a_fragment_a_current_block_and_another_language_pass_5190`
fn retired(
    pbg: &Pbg,
    block: &Block,
) -> BTreeSet<RetiredForm>
{
    let Ok(parsed) = parse(pbg, SourceText::from(block.text.as_str()))
    else {
        return BTreeSet::new();
    };
    let mut arena = CoreArena::new();
    let refusals: Vec<LoweringRefusal<'_>> = match lower_module(
        pbg,
        parsed.tree(),
        &mut arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
    ) {
        Ok(module) => module
            .declarations()
            .iter()
            .filter_map(|declared| {
                if let DeclarationOutcome::Refused(refusal) = declared.outcome() {
                    Some(refusal)
                }
                else {
                    None
                }
            })
            .collect(),
        Err(refusal) => vec![refusal],
    };
    refusals
        .into_iter()
        .filter_map(|refusal| {
            if let RefusalName::RetiredSpelling(form) = Refusal::Lowering(refusal).name() {
                Some(form)
            }
            else {
                None
            }
        })
        .collect()
}

/// Read each fenced `gandr` block of `text`, the file at `path`, into
/// `report`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the report counts the file and each block of [`blocks`], and
///   holds one finding for each block and each form that [`retired`] names in
///   it, in the order of the blocks.
/// - panics: none.
///
/// # Cost
/// - allocation: each finding's path, growth within the findings
///
/// # Adequacy
/// - hypothesis: L3 — as [`blocks`] and [`retired`].
/// - witness: `ledger::fences::tests::a_retired_spelling_in_a_fenced_block_is_refused_by_name_5190`
/// - witness: `ledger::fences::tests::a_comment_holds_its_block_at_its_fence_s_line_5190`
#[spec(ensures: |_| report.files >= 1)]
fn read_into(
    pbg: &Pbg,
    path: &Path,
    text: FileText<'_>,
    report: &mut FenceReport,
)
{
    report.files = report.files.saturating_add(1);
    for block in blocks(Prose::of(path), text) {
        report.blocks = report.blocks.saturating_add(1);
        for form in retired(pbg, &block) {
            report.findings.push(FenceFinding {
                path: path.to_owned(),
                line: block.line,
                form,
            });
        }
    }
}

/// Read each fenced `gandr` block of the files at `paths`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the report of [`read_into`] over each path whose extension is
///   `md`, `rs` or `gandr`, in the order given; a path of another extension is
///   not read.
/// - fails: a file cannot be read as UTF-8 text.
/// - panics: none.
///
/// # Errors
/// [`LedgerFault::Prose`] naming the file that cannot be read.
///
/// # Cost
/// - allocation: the text of each file, growth within the files
///
/// # Adequacy
/// - hypothesis: L3 — a file with a retired spelling in a fenced block is named
///   with its line, and a file with none passes.
/// - witness: `tests::cli::the_fences_name_a_retired_spelling_and_exit_one_5190`
#[spec(ensures: |ref ret| ret.as_ref().map_or(true, |report| report.files <= paths.len()))]
pub(super) fn check(
    pbg: &Pbg,
    paths: &[PathBuf],
) -> Result<FenceReport, LedgerFault>
{
    let mut report = FenceReport::default();
    for path in paths {
        if Prose::of(path) == Prose::Unread {
            continue;
        }
        let text = std::fs::read_to_string(path).map_err(|error| LedgerFault::Prose {
            path: path.clone(),
            error,
        })?;
        read_into(pbg, path, FileText(&text), &mut report);
    }
    Ok(report)
}

#[cfg(test)]
mod tests
{
    use std::path::Path;

    use gandr_surface_grammar::RetiredForm;
    use gandr_surface_grammar::built_in;

    use super::FenceFinding;
    use super::FenceReport;
    use super::FileText;
    use super::LineNumber;
    use super::read_into;

    /// The report of `text`, read as the file at `path`.
    ///
    /// # Specification
    /// trivial.
    fn read(
        path: &Path,
        text: FileText<'_>,
    ) -> FenceReport
    {
        let pbg = built_in().expect("the grammar builds");
        let mut report = FenceReport::default();
        read_into(&pbg, path, text, &mut report);
        report
    }

    #[test]
    fn a_retired_spelling_in_a_fenced_block_is_refused_by_name_5190()
    {
        let path = Path::new("notes.md");
        let report = read(
            path,
            FileText(include_str!(
                "fences/fixtures/a-retired-spelling-in-markdown.txt"
            )),
        );

        assert_eq!(report.blocks, 1);
        assert_eq!(report.findings, vec![FenceFinding {
            path: path.to_owned(),
            line: LineNumber(3),
            form: RetiredForm::PositionalPathCarrier,
        }]);
    }

    #[test]
    fn a_fragment_a_current_block_and_another_language_pass_5190()
    {
        let report = read(
            Path::new("notes.md"),
            FileText(include_str!(
                "fences/fixtures/a-fragment-a-current-block-and-another-language.txt"
            )),
        );

        assert_eq!(report.blocks, 2);
        assert_eq!(report.findings, vec![]);
    }

    #[test]
    fn a_comment_holds_its_block_at_its_fence_s_line_5190()
    {
        let path = Path::new("lib.rs");
        let report = read(
            path,
            FileText(include_str!(
                "fences/fixtures/a-comment-holds-its-block.txt"
            )),
        );

        assert_eq!(report.blocks, 1);
        assert_eq!(report.findings, vec![FenceFinding {
            path: path.to_owned(),
            line: LineNumber(3),
            form: RetiredForm::PositionalPathCarrier,
        }]);
    }
}
