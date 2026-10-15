//! One top-level form laid out: its brackets nested as groups, each group on
//! one line when it fits and broken one item per line when it does not.

use alloc::string::String;
use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_layout::LayoutOptions;
use gandr_surface_layout::RenderLimits;
use gandr_surface_layout::RenderMeter;
use gandr_surface_layout::arena::DocId;
use gandr_surface_layout::arena::TextSource;
use gandr_surface_layout::arena::VerbatimSource;
use gandr_surface_layout::build::DocBuilder;
use gandr_surface_layout::limits::BuildLimits;
use gandr_surface_layout::limits::BuildMeter;
use gandr_surface_layout::render::render;
use gandr_surface_layout::units::NestAmount;
use gandr_surface_syntax::SourceFragment;

use crate::FormatError;
use crate::leaf::Documentation;
use crate::leaf::Leaf;
use crate::leaf::Material;

/// The brackets that open a group, each beside the closer that ends it.
const BRACKETS: [(&str, &str); 5] = [("(", ")"), ("[", "]"), ("{", "}"), ("@[", "]"), ("#{", "}")];

/// The tokens that end an item of a group.
pub const SEPARATORS: [&str; 2] = [",", ";"];

/// How far a broken group indents its items.
const INDENT: u32 = 2;

/// The layout between two leaves of the source.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Gap
{
    /// Nothing: the leaves touch.
    Adjacent,
    /// Spaces or tabs, no line break.
    Space,
    /// One line break, with any spaces around it.
    Break,
    /// Two or more line breaks: a blank line.
    Blank,
}

impl Gap
{
    /// The gap the whitespace `text` spells.
    ///
    /// # Specification
    /// trivial.
    pub fn of(text: SourceFragment<'_>) -> Self
    {
        match <&str>::from(text)
            .bytes()
            .filter(|&byte| byte == b'\n')
            .count()
        {
            0 => Self::Space,
            1 => Self::Break,
            _ => Self::Blank,
        }
    }

    /// The wider of two gaps, so consecutive whitespace leaves read as one.
    ///
    /// # Specification
    /// trivial.
    pub fn widen(
        self,
        other: Self,
    ) -> Self
    {
        match (self, other) {
            (Self::Blank, _) | (_, Self::Blank) | (Self::Break, Self::Break) => Self::Blank,
            (Self::Break, _) | (_, Self::Break) => Self::Break,
            (Self::Space, _) | (_, Self::Space) => Self::Space,
            (Self::Adjacent, Self::Adjacent) => Self::Adjacent,
        }
    }

    /// Whether the gap holds a line break.
    ///
    /// # Specification
    /// trivial.
    const fn breaks(self) -> Breaks
    {
        match self {
            Self::Adjacent | Self::Space => Breaks::No,
            Self::Break | Self::Blank => Breaks::Yes,
        }
    }
}

/// Whether a gap holds a line break.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Breaks
{
    /// It does not.
    No,
    /// It does.
    Yes,
}

/// The position of a group among a form's groups.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct GroupId(usize);

/// One element of a group, in source order.
#[derive(Clone, Copy, Debug)]
enum Element<'source>
{
    /// A token, a block comment on one line, or a one-line verbatim form.
    Text(SourceFragment<'source>),
    /// Material laid down byte for byte: a form or a comment spanning lines
    /// or holding a tab.
    Verbatim(SourceFragment<'source>),
    /// A comment running to the end of its line.
    LineComment(SourceFragment<'source>),
    /// A delimited comment on one line.
    BlockComment(SourceFragment<'source>),
    /// A nested group.
    Group(GroupId),
}

impl Element<'_>
{
    /// What the element is, as layout decisions read it.
    ///
    /// # Specification
    /// trivial.
    const fn kind(self) -> Kind
    {
        match self {
            Self::LineComment(_) => Kind::LineComment,
            Self::BlockComment(_) => Kind::BlockComment,
            Self::Text(_) | Self::Verbatim(_) | Self::Group(_) => Kind::Code,
        }
    }
}

/// What an element is, as layout decisions read it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Kind
{
    /// A token, a verbatim form or a group.
    Code,
    /// A comment running to the end of its line.
    LineComment,
    /// A delimited comment.
    BlockComment,
}

/// An element beside the gap the source wrote before it.
#[derive(Clone, Copy, Debug)]
struct Placed<'source>
{
    /// The gap before the element.
    gap: Gap,
    /// The element's column in the source when the gap breaks the line.
    indent: Indent,
    /// Whether documentation starts or ends at the element.
    edge: Edge,
    /// The element.
    element: Element<'source>,
}

/// Whether documentation starts or ends between an element and the one
/// before it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Edge
{
    /// Both are documentation, or neither is.
    Within,
    /// One is documentation and the other is not, so a line break between
    /// them is kept.
    Documentation,
}

/// A column in the source, counted in characters from the line's start.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
struct Indent(usize);

/// What surrounds a group's elements.
#[derive(Clone, Copy, Debug)]
enum Frame<'source>
{
    /// The top-level form itself: no brackets, one item.
    Form,
    /// A bracketed group.
    Bracketed
    {
        /// The opening bracket.
        open: SourceFragment<'source>,
        /// The closer the opening bracket expects.
        expects: &'static str,
        /// The closing bracket, once read.
        close: SourceFragment<'source>,
        /// The gap before the closing bracket.
        closing: Gap,
    },
}

/// A group: a frame and the elements inside it.
#[derive(Debug)]
struct Group<'source>
{
    /// What surrounds the elements.
    frame: Frame<'source>,
    /// The elements, in source order.
    placed: Vec<Placed<'source>>,
}

/// The text one top-level form lays out to at `options`.
///
/// # Specification
/// - requires: `leaves` are the leaves of one clean top-level form, in offset
///   order, whitespace included, and `ending` spells `options`' physical line
///   ending.
/// - ensures: the text spells every token and comment of `leaves` once, in
///   order. A bracketed group is laid on one line, with the source's spacing
///   inside its brackets, when that fits the page and the source did not break
///   the line after its opening bracket and no line comment stands directly in
///   it; otherwise each of its items — the elements up to and including a `,`
///   or `;`, with a comment on the same line — stands on its own line indented
///   by two, and a blank line before an item is kept. Two tokens the source
///   wrote touching still touch, and two it separated are separated by one
///   space or a line break.
/// - provides: the layout of each top-level form [`crate::format`] joins.
/// - fails: [`FormatError::Unbalanced`] when a bracket closes a group it does
///   not open or a group is left open; a layout ceiling as
///   [`FormatError::Build`] or [`FormatError::Render`].
/// - panics: none.
/// - intension: one pass building groups with an explicit stack, then the
///   groups' documents innermost first.
///
/// # Adequacy
/// - hypothesis: L3 — goldens at a narrow and a wide page fix each layout rule,
///   and the corpus checks every form's tokens and meaning survive.
/// - witness: `format::tests::a_block_breaks_one_item_per_line_when_it_does_not_fit`
/// - witness: `format::tests::a_long_declaration_breaks_its_parameters_before_its_type`
/// - witness: `format::tests::a_continuation_line_indents_under_its_statement`
/// - witness: `format::tests::sweeps::every_source_keeps_its_meaning_and_formats_once`
#[spec(ensures: |ret| ret.as_ref().is_err() || !leaves.is_empty())]
pub fn lay_out(
    leaves: &[Leaf<'_>],
    options: &LayoutOptions,
    ending: SourceFragment<'static>,
) -> Result<String, FormatError>
{
    let groups = nest(leaves)?;
    let mut meter = BuildMeter::new(BuildLimits::default());
    let mut builder = DocBuilder::try_new(&mut meter)?;
    let blank = builder.verbatim(VerbatimSource::from(<&str>::from(ending)))?;
    let empty = builder.empty();
    let mut docs: Vec<Built> = Vec::with_capacity(groups.len());
    docs.resize(groups.len(), Built {
        flat: Flat::Fits(empty),
        best: empty,
    });
    for (index, group) in groups.iter().enumerate().rev() {
        let built = group_doc(&mut builder, group, &docs, blank)?;
        if let Some(slot) = docs.get_mut(index) {
            *slot = built;
        }
    }
    let root = docs.first().map_or(empty, |built| built.best);
    let arena = builder.finish()?;
    let mut render_meter = RenderMeter::new(RenderLimits::default());
    let rendered = render(&arena, root, options, &mut render_meter)?;
    Ok(String::from(&*rendered.text))
}

/// The groups of one form, the form itself first and each group before the
/// groups inside it.
///
/// # Specification
/// trivial.
fn nest<'source>(leaves: &[Leaf<'source>]) -> Result<Vec<Group<'source>>, FormatError>
{
    let mut groups: Vec<Group<'source>> = Vec::from([Group {
        frame: Frame::Form,
        placed: Vec::new(),
    }]);
    let mut open: Vec<GroupId> = Vec::from([GroupId(0)]);
    let mut gap = Gap::Adjacent;
    let mut indent = Indent::default();
    let mut documented = leaves
        .iter()
        .find(|leaf| leaf.material != Material::Whitespace)
        .map_or(Documentation::Outside, |leaf| leaf.documentation);
    for leaf in leaves {
        if leaf.material == Material::Whitespace {
            let text = <&str>::from(leaf.text);
            let column = match text.rsplit_once('\n') {
                Some((_, after)) => after.chars().count(),
                None => indent.0.saturating_add(text.chars().count()),
            };
            indent = Indent(column);
            gap = gap.widen(Gap::of(leaf.text));
            continue;
        }
        let edge = if leaf.documentation == documented {
            Edge::Within
        }
        else {
            Edge::Documentation
        };
        documented = leaf.documentation;
        let element = match leaf.material {
            Material::Token => {
                let text = <&str>::from(leaf.text);
                if let Some(&(_, expects)) = BRACKETS.iter().find(|&&(opener, _)| opener == text) {
                    let id = GroupId(groups.len());
                    groups.push(Group {
                        frame: Frame::Bracketed {
                            open: leaf.text,
                            expects,
                            close: leaf.text,
                            closing: Gap::Adjacent,
                        },
                        placed: Vec::new(),
                    });
                    place(&mut groups, &open, Placed {
                        gap,
                        indent,
                        edge,
                        element: Element::Group(id),
                    })?;
                    open.push(id);
                    gap = Gap::Adjacent;
                    indent = Indent::default();
                    continue;
                }
                if BRACKETS.iter().any(|&(_, closer)| closer == text) {
                    let Some(&GroupId(top)) = open.last()
                    else {
                        return Err(FormatError::Unbalanced);
                    };
                    match groups.get_mut(top).map(|group| &mut group.frame) {
                        Some(&mut Frame::Bracketed {
                            expects,
                            ref mut close,
                            ref mut closing,
                            ..
                        }) if expects == text => {
                            *close = leaf.text;
                            *closing = gap;
                        },
                        Some(&mut (Frame::Form | Frame::Bracketed { .. })) | None => {
                            return Err(FormatError::Unbalanced);
                        },
                    }
                    let _closed = open.pop();
                    gap = Gap::Adjacent;
                    indent = Indent::default();
                    continue;
                }
                Element::Text(leaf.text)
            },
            Material::Verbatim | Material::Shebang | Material::Whitespace => material(leaf.text),
            Material::LineComment => Element::LineComment(leaf.text),
            Material::BlockComment => Element::BlockComment(leaf.text),
        };
        place(&mut groups, &open, Placed {
            gap,
            indent,
            edge,
            element,
        })?;
        gap = Gap::Adjacent;
        indent = Indent::default();
    }
    if open.len() != 1 {
        return Err(FormatError::Unbalanced);
    }
    Ok(groups)
}

/// The element for material laid down as written: text when a text leaf can
/// hold it, verbatim otherwise.
///
/// # Specification
/// trivial.
fn material(text: SourceFragment<'_>) -> Element<'_>
{
    if <&str>::from(text).contains(['\n', '\r', '\t']) {
        Element::Verbatim(text)
    }
    else {
        Element::Text(text)
    }
}

/// Add `placed` to the innermost open group.
///
/// # Specification
/// trivial.
fn place<'source>(
    groups: &mut [Group<'source>],
    open: &[GroupId],
    placed: Placed<'source>,
) -> Result<(), FormatError>
{
    let Some(&GroupId(top)) = open.last()
    else {
        return Err(FormatError::Unbalanced);
    };
    let Some(group) = groups.get_mut(top)
    else {
        return Err(FormatError::Unbalanced);
    };
    group.placed.push(placed);
    Ok(())
}

/// A group's documents.
#[derive(Clone, Copy, Debug)]
struct Built
{
    /// The group on one line, every group inside it on one line too.
    flat: Flat,
    /// The group laid out as it best fits the page.
    best: DocId,
}

/// Whether a group can stand on one line.
#[derive(Clone, Copy, Debug)]
enum Flat
{
    /// It can, spelled by this document.
    Fits(DocId),
    /// It holds a line comment, or the source broke it, or a group inside it.
    Breaks,
}

/// How a run reads the groups inside it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Mode
{
    /// On one line where they can stand on one, as written otherwise.
    Flat,
    /// As each best fits the page.
    Best,
}

/// The documents of `group`, its nested groups' documents read from `docs`.
///
/// # Specification
/// trivial.
fn group_doc(
    builder: &mut DocBuilder<'_>,
    group: &Group<'_>,
    docs: &[Built],
    blank: DocId,
) -> Result<Built, FormatError>
{
    let Frame::Bracketed {
        open,
        close,
        closing,
        ..
    } = group.frame
    else {
        let best = run(builder, &group.placed, docs, Mode::Best)?;
        return Ok(Built {
            flat: Flat::Breaks,
            best,
        });
    };
    let open_text = open;
    let open = builder.text(TextSource::from(<&str>::from(open)))?;
    let close = builder.text(TextSource::from(<&str>::from(close)))?;
    let Some(first) = group.placed.first()
    else {
        let inside = spacing(builder, closing)?;
        let only = builder.concat_all([open, inside, close])?;
        return Ok(Built {
            flat: Flat::Fits(only),
            best: only,
        });
    };
    let forced = first.gap.breaks() == Breaks::Yes
        || group
            .placed
            .iter()
            .any(|placed| placed.element.kind() == Kind::LineComment);
    let listed = <&str>::from(open_text) == "{"
        || group.placed.iter().any(|placed| {
            matches!(placed.element, Element::Text(text)
                if SEPARATORS.contains(&<&str>::from(text)))
        });
    let mut lines: Vec<DocId> = Vec::new();
    for (index, item) in items(&group.placed).into_iter().enumerate() {
        let Some(&Placed { gap, .. }) = item.placed.first()
        else {
            continue;
        };
        if index > 0 && gap == Gap::Blank {
            lines.push(blank);
        }
        let line = builder.hard_line();
        let content = run(builder, item.placed, docs, Mode::Best)?;
        let both = builder.concat(line, content)?;
        lines.push(match item.continuation {
            Continuation::Statement => both,
            Continuation::Continued => builder.nest(NestAmount::from(INDENT), both)?,
        });
    }
    let body = builder.concat_all(lines)?;
    let indented = builder.nest(NestAmount::from(INDENT), body)?;
    let hard = builder.hard_line();
    let broken = builder.concat_all([open, indented, hard, close])?;
    if forced {
        return Ok(Built {
            flat: Flat::Breaks,
            best: broken,
        });
    }
    let pad = spacing(builder, first.gap)?;
    let content = run(builder, &group.placed, docs, Mode::Flat)?;
    let inline = builder.concat_all([open, pad, content, pad, close])?;
    let hugs = group.placed.iter().any(|placed| match placed.element {
        Element::Group(GroupId(inner)) => docs
            .get(inner)
            .is_some_and(|built| matches!(built.flat, Flat::Breaks)),
        Element::Text(_)
        | Element::Verbatim(_)
        | Element::LineComment(_)
        | Element::BlockComment(_) => false,
    });
    let flat = if hugs {
        Flat::Breaks
    }
    else {
        Flat::Fits(inline)
    };
    if !listed {
        let content = run(builder, &group.placed, docs, Mode::Best)?;
        let best = builder.concat_all([open, pad, content, pad, close])?;
        return Ok(Built { flat, best });
    }
    Ok(Built {
        flat,
        best: builder.choice(inline, broken)?,
    })
}

/// The space one line gives `gap` between a bracket and the element beside
/// it: none when the source touched, one space otherwise.
///
/// # Specification
/// trivial.
fn spacing(
    builder: &mut DocBuilder<'_>,
    gap: Gap,
) -> Result<DocId, FormatError>
{
    Ok(match gap {
        Gap::Adjacent => builder.empty(),
        Gap::Space | Gap::Break | Gap::Blank => builder.text(TextSource::from(" "))?,
    })
}

/// One line of a broken group.
#[derive(Clone, Copy, Debug)]
struct Item<'group, 'source>
{
    /// Its elements.
    placed: &'group [Placed<'source>],
    /// Whether it starts a statement or continues the one before.
    continuation: Continuation,
}

/// Whether a line of a broken group starts a statement.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Continuation
{
    /// It starts one: it follows a separator, or the source indented it no
    /// deeper than the statement before.
    Statement,
    /// It continues the statement before, which the source indented it
    /// deeper than.
    Continued,
}

/// The items of a group's elements: an item ends after a separator, unless
/// a comment follows on the separator's line, and before an element the
/// source wrote on a new line. An item the source started on a new line,
/// after no separator and indented deeper than the statement before it,
/// continues that statement.
///
/// # Specification
/// trivial.
fn items<'group, 'source>(placed: &'group [Placed<'source>]) -> Vec<Item<'group, 'source>>
{
    let mut items = Vec::new();
    let mut start = 0_usize;
    let mut ended = false;
    let mut continuation = Continuation::Statement;
    let mut base: Option<Indent> = placed
        .first()
        .filter(|first| first.gap.breaks() == Breaks::Yes)
        .map(|first| first.indent);
    for (index, current) in placed.iter().enumerate() {
        let breaks = current.gap.breaks() == Breaks::Yes;
        let starts = index > start && (breaks || (ended && current.element.kind() == Kind::Code));
        if starts {
            if let Some(item) = placed.get(start .. index) {
                items.push(Item {
                    placed: item,
                    continuation,
                });
            }
            start = index;
            continuation = Continuation::Statement;
            if current.element.kind() == Kind::Code {
                match base {
                    Some(statement) if !ended && breaks && current.indent > statement => {
                        continuation = Continuation::Continued;
                    },
                    Some(_) | None => base = Some(current.indent),
                }
            }
        }
        ended = match current.element {
            Element::Text(text) => SEPARATORS.contains(&<&str>::from(text)),
            Element::LineComment(_) | Element::BlockComment(_) => ended,
            Element::Verbatim(_) | Element::Group(_) => false,
        };
    }
    if let Some(item) = placed.get(start ..)
        && !item.is_empty()
    {
        items.push(Item {
            placed: item,
            continuation,
        });
    }
    items
}

/// The elements of `placed` on as few lines as their comments allow: two
/// elements the source wrote touching touch, any other two are one space
/// apart, and a line break follows a line comment and surrounds a comment
/// the source wrote on its own line.
///
/// # Specification
/// trivial.
fn run(
    builder: &mut DocBuilder<'_>,
    placed: &[Placed<'_>],
    docs: &[Built],
    mode: Mode,
) -> Result<DocId, FormatError>
{
    let mut parts: Vec<DocId> = Vec::with_capacity(placed.len().saturating_mul(2));
    let mut previous: Option<Kind> = None;
    for current in placed {
        let kind = current.element.kind();
        match previous {
            None => {},
            Some(Kind::LineComment) => parts.push(builder.hard_line()),
            Some(before) => {
                let comment = kind != Kind::Code
                    || before != Kind::Code
                    || current.edge == Edge::Documentation;
                match current.gap {
                    Gap::Adjacent => {},
                    Gap::Break | Gap::Blank if comment => parts.push(builder.hard_line()),
                    Gap::Space | Gap::Break | Gap::Blank => {
                        parts.push(builder.text(TextSource::from(" "))?);
                    },
                }
            },
        }
        parts.push(element_doc(builder, current.element, docs, mode)?);
        previous = Some(kind);
    }
    Ok(builder.concat_all(parts)?)
}

/// The document of one element.
///
/// # Specification
/// trivial.
fn element_doc(
    builder: &mut DocBuilder<'_>,
    element: Element<'_>,
    docs: &[Built],
    mode: Mode,
) -> Result<DocId, FormatError>
{
    Ok(match element {
        Element::Text(text)
        | Element::Verbatim(text)
        | Element::LineComment(text)
        | Element::BlockComment(text) => match material(text) {
            Element::Verbatim(text) => {
                builder.verbatim(VerbatimSource::from(<&str>::from(text)))?
            },
            Element::Text(text) | Element::LineComment(text) | Element::BlockComment(text) => {
                builder.text(TextSource::from(<&str>::from(text)))?
            },
            Element::Group(_) => return Err(FormatError::Unbalanced),
        },
        Element::Group(GroupId(group)) => {
            let built = docs.get(group).ok_or(FormatError::Unbalanced)?;
            match (mode, built.flat) {
                (Mode::Flat, Flat::Fits(flat)) => flat,
                (Mode::Flat, Flat::Breaks) | (Mode::Best, _) => built.best,
            }
        },
    })
}
