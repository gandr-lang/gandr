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
//! | item              | what it is                                              |
//! | ----------------- | ------------------------------------------------------- |
//! | [`format`]        | a parsed source formatted at a page width               |
//! | [`Formatted`]     | the formatted text and where each top-level form landed |
//! | [`Piece`]         | one top-level form's source span and formatted span     |
//! | [`FormatOptions`] | the page width                                          |
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
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct FormatOptions
{
    /// The width a line is laid out to fit.
    pub page: PageWidth,
}

impl Default for FormatOptions
{
    /// A page of 100 columns.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self {
            page: PageWidth::from(100_u32),
        }
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
/// [`FormatError::Build`] or [`FormatError::Render`].
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
///   it in the source and in the text.
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
/// - witness: `format::tests::every_source_keeps_its_meaning_and_formats_once`
/// - witness: `format::tests::a_block_breaks_one_item_per_line_when_it_does_not_fit`
/// - witness: `format::tests::top_level_forms_and_comments_keep_their_lines`
/// - witness: `format::tests::a_repaired_form_is_copied_as_written`
/// - witness: `format::tests::the_source_line_ending_is_kept`
/// - witness: `format::tests::pieces_place_each_top_level_form`
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
