//! The source formatter: a parsed gandr source laid out at a page width.
//!
//! [`format`] reads the concrete syntax tree, never the core, so every token
//! and comment the source wrote is kept, in order, and only the layout
//! between them changes. Each top-level form is laid out on its own: its
//! brackets nest as groups, a group stays on one line when it fits and
//! breaks one item per line when it does not. A form the parser repaired, a
//! string, a shell block and a hole are copied byte for byte.
//!
//! The formatted text is parsed again before it is returned: its content
//! digest must equal the source's and its tokens and comments must be the
//! source's, or [`format`] refuses with [`FormatError::Changed`] and returns
//! nothing.
//!
//! # The form a source is spelled in
//!
//! A source is spelled in the surface's sugared form or in the core's
//! explicit form, every thunk, force, run and exit written out. Since the
//! formatter keeps every token, it lays a source out in the spelling the
//! source was written in and never re-sugars an explicit source: that is the
//! invariant the corpus's formatting gate rests on. [`FormatOptions::form`]
//! asks for a [`Form`] — [`Form::Explicit`] or [`Form::Sugared`], or
//! [`Form::Source`], the source's own spelling, by default — and a source
//! states its own at its head, as an entry of an attribute block on its first
//! declaration, after its imports: `@[ form(explicit) ]` or
//! `@[ form(sugared) ]`, an attribute the lowering registers and files
//! without lowering its word. The declaration wins
//! over the option, so one command lays out sources of both spellings. An
//! option asking for a form a source does not declare is refused with
//! [`FormatError::Form`], naming the form: no layout here changes a source's
//! tokens, so a form the source does not state cannot be kept.
//!
//! - Choice: the form is the source's to state, and the formatter keeps it.
//! - Alternative: a sugaring layout, rewriting the explicit form into the
//!   sugared one; it would change tokens and digests, and the gate could no
//!   longer tell a layout from an edit.
//! - Reversal: a layout that sugars or desugars lands with its own digest
//!   check, and the option then selects it for a source declaring no form.
//!
//! | item              | what it is                                              |
//! | ----------------- | ------------------------------------------------------- |
//! | [`format`]        | a parsed source formatted at a page width               |
//! | [`Formatted`]     | the formatted text and where each top-level form landed |
//! | [`Piece`]         | one top-level form's source span and formatted span     |
//! | [`FormatOptions`] | the page width and the form                             |
//! | [`Form`]          | the spelling a source is laid out in                    |
//! | [`FormatError`]   | why a source was not formatted                          |

#![no_std]

extern crate alloc;

mod layout;
mod leaf;

use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_surface_grammar::Pbg;
use gandr_surface_layout::ComputationWidth;
use gandr_surface_layout::LayoutOptions;
pub use gandr_surface_layout::PageWidth;
use gandr_surface_layout::PhysicalLineEnding;
use gandr_surface_layout::RenderError;
use gandr_surface_layout::error::BuildError;
use gandr_surface_parser::MeldError;
use gandr_surface_parser::ParseResult;
use gandr_surface_parser::parse;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SourceText;

use crate::layout::Gap;
use crate::leaf::Integrity;
use crate::leaf::Leaf;
use crate::leaf::Material;
use crate::leaf::Owner;

/// How a source is formatted.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct FormatOptions
{
    /// The width a line is laid out to fit.
    pub page: PageWidth,
    /// The spelling the source is laid out in, unless its head declares one.
    pub form: Form,
}

impl Default for FormatOptions
{
    /// A page of 100 columns, in the source's own spelling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self {
            page: PageWidth::from(100_u32),
            form: Form::Source,
        }
    }
}

/// The spelling a source is laid out in.
///
/// The formatter keeps every token the source wrote, so the one spelling it
/// lays out is the source's own. A source states which spelling it keeps with
/// `@[ form(explicit) ]` or `@[ form(sugared) ]` in an attribute block of its
/// first form; the declaration wins over [`FormatOptions::form`]. A form asked
/// for by the options that the source does not declare is refused with
/// [`FormatError::Form`]: laying a source out in a spelling it was not written
/// in would change its tokens, and no layout here does.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum Form
{
    /// The source's own spelling, every token kept.
    #[default]
    Source,
    /// The core's explicit spelling: every binder, run and exit written out.
    Explicit,
    /// The surface's sugared spelling.
    Sugared,
}

impl fmt::Display for Form
{
    /// The form's name, as the option and the declaration spell it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            Self::Source => "source",
            Self::Explicit => "explicit",
            Self::Sugared => "sugared",
        })
    }
}

/// Why a source was not formatted.
#[derive(Debug, Eq, PartialEq)]
pub enum FormatError
{
    /// A form's brackets do not pair.
    Unbalanced,
    /// Building a form's layout document reached a ceiling.
    Build(BuildError),
    /// Laying a form's document out reached a ceiling.
    Render(RenderError),
    /// The formatted text did not parse.
    Reparse(MeldError),
    /// The formatted text would have changed the source.
    Changed(Change),
    /// The options asked for a spelling the source does not declare, which
    /// the formatter cannot lay out without changing its tokens.
    Form(Form),
}

/// What formatting would have changed.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Change
{
    /// The content digest: the formatted text means something else.
    Meaning,
    /// The tokens or comments, or their order.
    Material,
}

impl From<BuildError> for FormatError
{
    /// A build ceiling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(error: BuildError) -> Self
    {
        Self::Build(error)
    }
}

impl From<RenderError> for FormatError
{
    /// A render ceiling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(error: RenderError) -> Self
    {
        Self::Render(error)
    }
}

impl fmt::Display for FormatError
{
    /// One line naming the refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Unbalanced => write!(f, "a form's brackets do not pair"),
            Self::Build(ref error) => write!(f, "the layout could not be built: {error}"),
            Self::Render(ref error) => write!(f, "the layout could not be rendered: {error}"),
            Self::Reparse(ref error) => write!(f, "the formatted text does not parse: {error}"),
            Self::Form(form) => write!(
                f,
                "the source does not declare the {form} form, and the formatter keeps the \
                 source's own spelling"
            ),
            Self::Changed(Change::Meaning) => {
                write!(f, "formatting would change what the source means")
            },
            Self::Changed(Change::Material) => {
                write!(f, "formatting would change the source's tokens or comments")
            },
        }
    }
}

/// The formatted text of one source.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Formatted
{
    /// The text.
    text: String,
    /// Each top-level form, in source order.
    pieces: Vec<Piece>,
}

impl Formatted
{
    /// The formatted text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn text(&self) -> SourceText<'_>
    {
        SourceText::from(self.text.as_str())
    }

    /// Each top-level form's source span and formatted span, in source order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn pieces(&self) -> &[Piece]
    {
        &self.pieces
    }

    /// The formatted text, owned.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn into_text(self) -> String
    {
        self.text
    }
}

/// Where one top-level form was and where it landed.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Piece
{
    /// Its span in the source: its first token, comment or documentation to
    /// its last.
    pub source: ByteSpan,
    /// Its span in the formatted text.
    pub formatted: ByteSpan,
    /// Whether it was laid out or copied as written.
    pub layout: Layout,
}

/// Whether a top-level form was laid out.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Layout
{
    /// It was laid out.
    Formatted,
    /// The parser repaired it, so it was copied as written.
    Repaired,
}

/// Format the source `parsed` was parsed from.
///
/// # Errors
/// Returns [`FormatError::Changed`] when the formatted text would mean
/// something else or spell other tokens or comments, and
/// [`FormatError::Reparse`] when it does not parse; either is a defect in
/// the formatter, and no text is returned. A form whose brackets do not pair
/// is [`FormatError::Unbalanced`]; a layout ceiling is
/// [`FormatError::Build`] or [`FormatError::Render`]. Options asking for a
/// [`Form`] the source's head does not declare are [`FormatError::Form`].
///
/// # Specification
/// - requires: `parsed` was parsed under `grammar`.
/// - ensures: the text keeps every token and comment of the source, in order;
///   each top-level form starts on a line of its own, and the source's blank
///   lines between them are kept, one at most; a comment the source wrote on a
///   top-level form's last line stays there, as does a separator ending a
///   top-level statement; the text ends in one line break unless it is empty,
///   and uses the line ending most of the source's breaks use. A form the
///   parser repaired, or that an obligation touches, is copied as written. Each
///   other form is laid out at `options.page` as the crate root describes. The
///   text parses under `grammar` to the source's root digest, and formatting it
///   again returns it unchanged. One piece per top-level form, in order, spans
///   it in the source and in the text. The spelling is the source's own: a form
///   the source declares wins over `options.form`, and `options.form` other
///   than [`Form::Source`] with no declaration is refused.
/// - provides: the text `gandr fmt` writes and the language server's formatting
///   edits.
/// - fails: as `# Errors` states.
/// - panics: none.
/// - intension: one walk of the tree, one layout per top-level form, one parse
///   of the result.
///
/// # Adequacy
/// - hypothesis: L3 — every corpus source is formatted at three widths and
///   formatted again unchanged, the formatter checking each against the
///   source's digest and material; goldens fix each layout rule at a narrow and
///   a wide page, and exact texts fix the top-level joins, the verbatim forms,
///   a repaired form, the line ending and the pieces.
/// - witness: `format::tests::sweeps::every_source_keeps_its_meaning_and_formats_once`
/// - witness: `format::tests::a_block_breaks_one_item_per_line_when_it_does_not_fit`
/// - witness: `format::tests::top_level_forms_and_comments_keep_their_lines`
/// - witness: `format::tests::a_repaired_form_is_copied_as_written`
/// - witness: `format::tests::the_source_line_ending_is_kept`
/// - witness: `format::tests::pieces_place_each_top_level_form`
/// - witness: `format::tests::a_form_written_against_the_one_before_starts_its_own_line`
/// - witness: `format::tests::a_separator_written_on_the_next_line_joins_its_statement`
/// - witness: `format::tests::a_source_split_evenly_between_endings_keeps_line_feeds`
/// - witness: `format::tests::an_explicit_source_keeps_its_explicit_spelling`
/// - witness: `format::tests::a_form_the_source_does_not_declare_is_refused`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |formatted| formatted.pieces.windows(2).all(|pair| matches!(pair, [left, right] if left.source.end() <= right.source.start() && left.formatted.end() <= right.formatted.start()))))]
#[inline]
pub fn format(
    grammar: &Pbg,
    parsed: &ParseResult<'_>,
    options: FormatOptions,
) -> Result<Formatted, FormatError>
{
    let tree = parsed.tree();
    let source = tree.source();
    let flat = leaf::flatten(grammar, tree, parsed.obligations());
    if options.form != Form::Source && declared(&flat.leaves).is_none() {
        return Err(FormatError::Form(options.form));
    }
    let ending = Ending::of(source);
    let layout = LayoutOptions::try_new(
        options.page,
        ComputationWidth::from(u32::from(options.page).saturating_mul(2_u32)),
        ending.physical(),
    )?;
    let breaks = <&str>::from(ending.spelling());
    let mut text = String::with_capacity(<&str>::from(source).len());
    let mut pieces = Vec::new();
    for unit in units(&flat.leaves) {
        let Some(first) = unit.leaves.first()
        else {
            continue;
        };
        if !text.is_empty() {
            match (unit.joins, unit.gap) {
                (Joins::Touching, _) => {},
                (Joins::SameLine, _) => text.push(' '),
                (Joins::OwnLine, Gap::Blank) => {
                    text.push_str(breaks);
                    text.push_str(breaks);
                },
                (Joins::OwnLine, Gap::Adjacent | Gap::Space | Gap::Break) => {
                    text.push_str(breaks);
                },
            }
        }
        let start = text.len();
        let span = unit.span;
        let Owner::Form(form) = first.owner
        else {
            text.push_str(<&str>::from(first.text));
            continue;
        };
        let laid = match flat.integrity(form) {
            Integrity::Clean => {
                text.push_str(&layout::lay_out(unit.leaves, &layout, ending.spelling())?);
                Layout::Formatted
            },
            Integrity::Repaired => {
                if let Ok(written) = source.fragment(span) {
                    text.push_str(<&str>::from(written));
                }
                Layout::Repaired
            },
        };
        if let Ok(formatted) = ByteSpan::new(ByteOffset::from(start), ByteOffset::from(text.len()))
        {
            pieces.push(Piece {
                source: span,
                formatted,
                layout: laid,
            });
        }
    }
    if !text.is_empty() {
        text.push_str(breaks);
    }
    verify(
        grammar,
        parsed,
        &flat.leaves,
        SourceText::from(text.as_str()),
    )?;
    Ok(Formatted { text, pieces })
}

/// One top-level unit of the source: a form, or a comment or shebang at the
/// root, beside the layout before it.
#[derive(Clone, Copy, Debug)]
struct Unit<'leaves, 'source>
{
    /// The unit's leaves, from its first token or comment to its last.
    leaves: &'leaves [Leaf<'source>],
    /// The span from its first leaf to its last.
    span: ByteSpan,
    /// The layout the source wrote before it.
    gap: Gap,
    /// How it joins the unit before it.
    joins: Joins,
}

/// How a top-level unit joins the unit before it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Joins
{
    /// On its own line: a form, or a comment the source wrote on its own.
    OwnLine,
    /// After one space: a comment the source wrote on the line before it
    /// ended, or a separator the source spaced off.
    SameLine,
    /// Touching: a separator the source wrote against the form it ends.
    Touching,
}

/// The top-level units of `leaves`, in order.
///
/// # Specification
/// trivial.
fn units<'leaves, 'source>(leaves: &'leaves [Leaf<'source>]) -> Vec<Unit<'leaves, 'source>>
{
    let mut units = Vec::new();
    let mut gap = Gap::Adjacent;
    let mut rest = leaves;
    while let Some((first, after)) = rest.split_first() {
        if first.material == Material::Whitespace {
            gap = gap.widen(Gap::of(first.text));
            rest = after;
            continue;
        }
        let mut length = 1_usize;
        if first.owner != Owner::Root {
            for (offset, leaf) in after.iter().enumerate() {
                if leaf.material == Material::Whitespace {
                    continue;
                }
                if leaf.owner != first.owner {
                    break;
                }
                length = offset.saturating_add(2);
            }
        }
        let (unit, remaining) = rest.split_at(length.min(rest.len()));
        let separator = matches!(unit, [only] if only.material == Material::Token
            && layout::SEPARATORS.contains(&<&str>::from(only.text)));
        let comment = matches!(
            first.material,
            Material::LineComment | Material::BlockComment
        );
        let joins = match gap {
            Gap::Adjacent if separator => Joins::Touching,
            Gap::Adjacent | Gap::Space if comment || separator => Joins::SameLine,
            Gap::Break | Gap::Blank if separator => Joins::SameLine,
            Gap::Adjacent | Gap::Space | Gap::Break | Gap::Blank => Joins::OwnLine,
        };
        let last = unit.last().map_or(first.span, |last| last.span);
        units.push(Unit {
            leaves: unit,
            span: first.span.join(last),
            gap,
            joins,
        });
        gap = Gap::Adjacent;
        rest = remaining;
    }
    units
}

/// The line ending a source's line breaks mostly use.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Ending
{
    /// A line feed.
    Lf,
    /// A carriage return and a line feed.
    CrLf,
}

impl Ending
{
    /// The ending of `source`: a carriage return and line feed when more of
    /// its line breaks are spelled so than not, a line feed otherwise.
    ///
    /// # Specification
    /// trivial.
    fn of(source: SourceText<'_>) -> Self
    {
        let source = <&str>::from(source);
        let breaks = source.bytes().filter(|&byte| byte == b'\n').count();
        let crlf = source.matches("\r\n").count();
        if crlf.saturating_mul(2) > breaks {
            Self::CrLf
        }
        else {
            Self::Lf
        }
    }

    /// The ending's bytes.
    ///
    /// # Specification
    /// trivial.
    fn spelling(self) -> SourceFragment<'static>
    {
        SourceFragment::from(match self {
            Self::Lf => "\n",
            Self::CrLf => "\r\n",
        })
    }

    /// The ending as the layout engine names it.
    ///
    /// # Specification
    /// trivial.
    const fn physical(self) -> PhysicalLineEnding
    {
        match self {
            Self::Lf => PhysicalLineEnding::Lf,
            Self::CrLf => PhysicalLineEnding::CrLf,
        }
    }
}

/// Check that `text` parses to the root digest of `parsed` and spells the
/// tokens and comments of `leaves`, its leaves, in order.
///
/// # Specification
/// trivial.
fn verify(
    grammar: &Pbg,
    parsed: &ParseResult<'_>,
    leaves: &[Leaf<'_>],
    text: SourceText<'_>,
) -> Result<(), FormatError>
{
    let reparsed = parse(grammar, text).map_err(FormatError::Reparse)?;
    let digest = |result: &ParseResult<'_>| result.tree().digest();
    if digest(&reparsed) != digest(parsed) {
        return Err(FormatError::Changed(Change::Meaning));
    }
    let again = leaf::flatten(grammar, reparsed.tree(), reparsed.obligations());
    if material(leaves).ne(material(&again.leaves)) {
        return Err(FormatError::Changed(Change::Material));
    }
    Ok(())
}

/// The tokens and comments of `leaves`, in order.
///
/// # Specification
/// trivial.
fn material<'leaves, 'source>(
    leaves: &'leaves [Leaf<'source>]
) -> impl Iterator<Item = (Material, SourceFragment<'source>)> + 'leaves
{
    leaves
        .iter()
        .filter(|leaf| leaf.material != Material::Whitespace)
        .map(|leaf| (leaf.material, leaf.text))
}

/// The form the source's head declares: `form(explicit)` or `form(sugared)`
/// as an entry of an attribute block written before the source's first
/// declaration, after its imports — the one place a block before a
/// declaration stands, since a block before an import refuses the module.
///
/// # Specification
/// - requires: `leaves` are a source's, in offset order.
/// - ensures: the form named by the first `form` entry of the attribute blocks
///   before the first token, outside an import, that no block holds; none when
///   there is none, or it names neither form.
/// - fails: never.
/// - panics: none.
/// - executable: none — the declaration is read from the leaves' text, which a
///   predicate over the answer would read again.
///
/// # Adequacy
/// - hypothesis: L3 — a source declaring the explicit form keeps it under
///   either option, after an import as at its first line; the same source with
///   no declaration is refused a form.
/// - witness: `format::tests::an_explicit_source_keeps_its_explicit_spelling`
/// - witness: `format::tests::a_form_the_source_does_not_declare_is_refused`
fn declared(leaves: &[Leaf<'_>]) -> Option<Form>
{
    let tokens: Vec<&str> = leaves
        .iter()
        .filter(|leaf| matches!(leaf.owner, Owner::Form(_)) && leaf.material == Material::Token)
        .map(|leaf| <&str>::from(leaf.text))
        .collect();
    let mut depth = 0_usize;
    let mut importing = false;
    for (at, &token) in tokens.iter().enumerate() {
        match token {
            ";" if importing => importing = false,
            _ if importing => {},
            "import" if depth == 0 => importing = true,
            "@[" => depth = depth.saturating_add(1),
            "[" if depth > 0 => depth = depth.saturating_add(1),
            "]" if depth > 0 => depth = depth.saturating_sub(1),
            _ if depth == 0 => return None,
            "form" if depth == 1 => {
                if let (Some(&"("), Some(&word), Some(&")")) = (
                    tokens.get(at.saturating_add(1)),
                    tokens.get(at.saturating_add(2)),
                    tokens.get(at.saturating_add(3)),
                ) {
                    return match word {
                        "explicit" => Some(Form::Explicit),
                        "sugared" => Some(Form::Sugared),
                        _ => None,
                    };
                }
            },
            _ => {},
        }
    }
    None
}
