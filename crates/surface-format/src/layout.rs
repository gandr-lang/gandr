//! One top-level form laid out: its brackets nested as groups, each group on
//! one line when it fits and broken one item per line when it does not, and
//! each juxtaposed spine on one line or broken one operand per line.

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
use crate::leaf::Branch;
use crate::leaf::Direct;
use crate::leaf::Documentation;
use crate::leaf::Leaf;
use crate::leaf::Material;
use crate::leaf::Offside;
use crate::space;
use crate::space::Context;
use crate::space::Join;
use crate::space::Kind as Neighbour;
use crate::space::Padding;

/// The brackets that open a group, each beside the closer that ends it.
pub const BRACKETS: [(&str, &str); 12] = [
    ("(", ")"),
    ("type(", ")"),
    ("[", "]"),
    ("#[", "]"),
    (".#[", "]"),
    ("{", "}"),
    ("@[", "]"),
    ("@![", "]"),
    ("*{", "}"),
    (".*{", "}"),
    ("+{", "}"),
    ("&{", "}"),
];

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
    /// A layout block's separator: nothing written, the end of an item.
    Break,
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
            Self::Text(_) | Self::Verbatim(_) | Self::Group(_) | Self::Break => Kind::Code,
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

/// An element beside the gap the source wrote before it and the space the
/// spacing table decides there.
#[derive(Clone, Copy, Debug)]
struct Placed<'source>
{
    /// The gap the source wrote before the element.
    gap: Gap,
    /// The space before the element when it shares a line with the element
    /// before it.
    join: Join,
    /// The element's column in the source when the gap breaks the line.
    indent: Indent,
    /// Whether documentation starts or ends at the element.
    edge: Edge,
    /// Where the element's first leaf stands among its block's items; none
    /// for a separator and a comment.
    branch: Option<Branch>,
    /// The element.
    element: Element<'source>,
    /// The part the element's token plays, as the spacing table reads it:
    /// [`space::Context::Plain`] for a group, a break and a comment.
    context: space::Context,
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
        /// Whether the brackets hug what they hold.
        padding: Padding,
        /// The part the opening bracket plays, which its closer plays too.
        context: space::Context,
        /// The closing bracket, once read.
        close: SourceFragment<'source>,
        /// The space before the closing bracket.
        closing: Join,
    },
    /// A layout block: the column rule, not a bracket, ends it, so it breaks
    /// one item per line and writes no closer.
    Layout
    {
        /// The token that opens it: a line-final `=`, or nothing.
        open: SourceFragment<'source>,
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
///   order. A bracketed group is laid on one line, padded as its bracket
///   decides, when that fits the page and the source did not break the line
///   after its opening bracket and no line comment stands directly in it;
///   otherwise each of its items — the elements up to and including a `,` or
///   `;`, with a comment on the same line — stands on its own line indented by
///   two, and a blank line before an item is kept. A layout block, which the
///   column rule ends, always stands so under the token that opens it, its
///   empty separators and close writing nothing. A juxtaposed expression spine
///   that ends its run stands on one line when that fits. Otherwise its head
///   stands first and each operand on a line of its own, two columns deeper. A
///   spine the source broke before an operand stays so (#5202). A type's spine
///   never breaks between its operands (#5326). Two elements on one line are as
///   far apart as [`space::join`] decides, except inside a string the grammar
///   reads as tiles and beside a token a rewrite wrote, where the source's
///   spacing stands as one space or none.
/// - provides: the layout of each top-level form [`crate::format`] joins.
/// - fails: [`FormatError::Unbalanced`] when a bracket or a layout close ends a
///   group it does not open or a group is left open; a layout ceiling as
///   [`FormatError::Build`] or [`FormatError::Render`].
/// - panics: none.
/// - intension: one pass building groups with an explicit stack, then the
///   groups' documents innermost first.
///
/// # Adequacy
/// - hypothesis: L3 — goldens at a narrow and a wide page fix each layout rule,
///   and the corpus checks every form's tokens and meaning survive.
/// - witness: `tests::format::a_block_breaks_one_item_per_line_when_it_does_not_fit`
/// - witness: `tests::format::a_long_declaration_breaks_its_parameters_before_its_type`
/// - witness: `tests::format::a_continuation_line_indents_under_its_statement`
/// - witness: `tests::format::a_member_after_a_column_zero_comment_starts_a_statement_2950`
/// - witness: `tests::format::the_printer_decides_every_inner_space`
/// - witness: `tests::format::a_juxtaposed_spine_breaks_one_operand_a_line_5202`
/// - witness: `tests::format::a_type_s_spine_keeps_its_line_in_a_signature_5326`
/// - witness: `tests::format::sweeps::every_source_keeps_its_meaning_and_formats_once`
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
        opens: Opens::Other,
        ends: Ends::Closer,
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
/// groups inside it, each element beside the space the spacing table decides
/// before it.
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
    let mut before = Before::Start;
    let mut quoted = Quoted::No;
    let mut documented = leaves
        .iter()
        .find(|leaf| leaf.material != Material::Whitespace)
        .map_or(Documentation::Outside, |leaf| leaf.documentation);
    let mut rewrote = Rewrote::No;
    for leaf in leaves {
        if leaf.material == Material::Whitespace {
            let text = <&str>::from(leaf.text);
            let column = match text.rsplit_once('\n') {
                Some((_, after)) => after.chars().count(),
                None => indent.0.saturating_add(text.chars().count()),
            };
            indent = Indent(column);
            gap = gap.widen(Gap::of(leaf.text));
            if leaf.context == Context::Written {
                rewrote = Rewrote::Yes;
            }
            continue;
        }
        let edge = if leaf.documentation == documented {
            Edge::Within
        }
        else {
            Edge::Documentation
        };
        documented = leaf.documentation;
        let (inside, opened) = inside_of(&groups, &open);
        let (element, here) = match leaf.material {
            Material::Token => {
                let text = <&str>::from(leaf.text);
                // A layout block's parts: an empty part passes on the gap and
                // the column before it, as the source's lines are what the
                // column rule reads.
                let empty = text.is_empty();
                match leaf.offside {
                    Offside::Opens => {
                        let here = space::Token {
                            text: leaf.text,
                            context: leaf.context,
                            kind: Neighbour::Open,
                        };
                        let join = if empty {
                            Join::Touch
                        }
                        else {
                            between(before, here, (gap, rewrote), inside, quoted)
                        };
                        let id = GroupId(groups.len());
                        groups.push(Group {
                            frame: Frame::Layout { open: leaf.text },
                            placed: Vec::new(),
                        });
                        place(&mut groups, &open, Placed {
                            gap: if empty { Gap::Adjacent } else { gap },
                            join,
                            indent,
                            edge,
                            branch: leaf.branch,
                            element: Element::Group(id),
                            context: space::Context::Plain,
                        })?;
                        open.push(id);
                        before = Before::After(here);
                        if !empty {
                            gap = Gap::Adjacent;
                            rewrote = Rewrote::No;
                            indent = Indent::default();
                        }
                        continue;
                    },
                    Offside::Separates => {
                        place(&mut groups, &open, Placed {
                            gap: Gap::Adjacent,
                            join: Join::Touch,
                            indent,
                            edge,
                            branch: None,
                            element: Element::Break,
                            context: space::Context::Plain,
                        })?;
                        before = Before::After(space::Token {
                            text: leaf.text,
                            context: leaf.context,
                            kind: Neighbour::Token,
                        });
                        continue;
                    },
                    Offside::Closes => {
                        let Some(&GroupId(top)) = open.last()
                        else {
                            return Err(FormatError::Unbalanced);
                        };
                        match groups.get(top).map(|group| group.frame) {
                            Some(Frame::Layout { .. }) => {},
                            Some(Frame::Form | Frame::Bracketed { .. }) | None => {
                                return Err(FormatError::Unbalanced);
                            },
                        }
                        let _closed = open.pop();
                        before = Before::After(space::Token {
                            text: leaf.text,
                            context: opened,
                            kind: Neighbour::Close(inside),
                        });
                        continue;
                    },
                    Offside::Written => {},
                }
                if let Some(&(_, expects)) = BRACKETS.iter().find(|&&(opener, _)| opener == text) {
                    let here = space::Token {
                        text: leaf.text,
                        context: leaf.context,
                        kind: Neighbour::Open,
                    };
                    let join = between(before, here, (gap, rewrote), inside, quoted);
                    let id = GroupId(groups.len());
                    groups.push(Group {
                        frame: Frame::Bracketed {
                            open: leaf.text,
                            expects,
                            padding: space::padding(here),
                            context: leaf.context,
                            close: leaf.text,
                            closing: Join::Touch,
                        },
                        placed: Vec::new(),
                    });
                    place(&mut groups, &open, Placed {
                        gap,
                        join,
                        indent,
                        edge,
                        branch: leaf.branch,
                        element: Element::Group(id),
                        context: space::Context::Plain,
                    })?;
                    open.push(id);
                    before = Before::After(here);
                    gap = Gap::Adjacent;
                    rewrote = Rewrote::No;
                    indent = Indent::default();
                    continue;
                }
                if BRACKETS.iter().any(|&(_, closer)| closer == text) {
                    let Some(&GroupId(top)) = open.last()
                    else {
                        return Err(FormatError::Unbalanced);
                    };
                    let here = space::Token {
                        text: leaf.text,
                        context: opened,
                        kind: Neighbour::Close(inside),
                    };
                    let join = between(before, here, (gap, rewrote), inside, quoted);
                    match groups.get_mut(top).map(|group| &mut group.frame) {
                        Some(&mut Frame::Bracketed {
                            expects,
                            ref mut close,
                            ref mut closing,
                            ..
                        }) if expects == text => {
                            *close = leaf.text;
                            *closing = join;
                        },
                        Some(
                            &mut (Frame::Form | Frame::Bracketed { .. } | Frame::Layout { .. }),
                        )
                        | None => {
                            return Err(FormatError::Unbalanced);
                        },
                    }
                    let _closed = open.pop();
                    before = Before::After(here);
                    gap = Gap::Adjacent;
                    rewrote = Rewrote::No;
                    indent = Indent::default();
                    continue;
                }
                (Element::Text(leaf.text), Neighbour::Token)
            },
            Material::Verbatim | Material::Shebang | Material::Whitespace => {
                (material(leaf.text), Neighbour::Material)
            },
            Material::LineComment => (Element::LineComment(leaf.text), Neighbour::Comment),
            Material::BlockComment => (Element::BlockComment(leaf.text), Neighbour::Comment),
        };
        let here = space::Token {
            text: leaf.text,
            context: leaf.context,
            kind: here,
        };
        // A string the grammar reads as tiles between two `"` keeps the
        // spacing it holds: that spacing is its text.
        let quote = here.kind == Neighbour::Token && <&str>::from(leaf.text) == "\"";
        let join = match (quote, quoted) {
            (true, Quoted::Yes) => {
                quoted = Quoted::No;
                written(gap)
            },
            (true, Quoted::No) => {
                let join = between(before, here, (gap, rewrote), inside, quoted);
                quoted = Quoted::Yes;
                join
            },
            (false, _) => between(before, here, (gap, rewrote), inside, quoted),
        };
        place(&mut groups, &open, Placed {
            gap,
            join,
            indent,
            edge,
            branch: match leaf.material {
                Material::Token | Material::Verbatim => leaf.branch,
                Material::LineComment
                | Material::BlockComment
                | Material::Shebang
                | Material::Whitespace => None,
            },
            element,
            context: leaf.context,
        })?;
        before = Before::After(here);
        gap = Gap::Adjacent;
        rewrote = Rewrote::No;
        indent = Indent::default();
    }
    if open.len() != 1 {
        return Err(FormatError::Unbalanced);
    }
    Ok(groups)
}

/// The neighbour before the next element of a form.
#[derive(Clone, Copy, Debug)]
enum Before<'source>
{
    /// None: the next element starts the form.
    Start,
    /// This one.
    After(space::Token<'source>),
}

/// Whether the next element stands inside a string the grammar reads as
/// tiles.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Quoted
{
    /// It does not.
    No,
    /// It does: a `"` opened the string and none has closed it.
    Yes,
}

/// The padding of the innermost open group of `groups`, `open` naming the
/// open ones, and the part its opening bracket plays; a form hugs and plays
/// no part.
///
/// # Specification
/// trivial.
fn inside_of(
    groups: &[Group<'_>],
    open: &[GroupId],
) -> (Padding, space::Context)
{
    match open
        .last()
        .and_then(|&GroupId(top)| groups.get(top))
        .map(|group| group.frame)
    {
        Some(Frame::Bracketed {
            padding, context, ..
        }) => (padding, context),
        Some(Frame::Form | Frame::Layout { .. }) | None => (Padding::Hug, space::Context::Plain),
    }
}

/// Whether a rewrite wrote the gap before the next element.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Rewrote
{
    /// It did not: the source wrote it, or nothing stands there.
    No,
    /// It did.
    Yes,
}

/// The space the source wrote as `gap`, kept where the spacing is a
/// string's text or a rewrite wrote it.
///
/// # Specification
/// trivial.
const fn written(gap: Gap) -> Join
{
    match gap {
        Gap::Adjacent => Join::Touch,
        Gap::Space | Gap::Break | Gap::Blank => Join::Space,
    }
}

/// The space before `here` on a line, `before` the neighbour before it,
/// `gap` the layout written between them, `inside` the padding of the
/// innermost open group, `quoted` whether a string holds them and `rewrote`
/// whether a rewrite wrote the gap.
///
/// # Specification
/// trivial.
fn between(
    before: Before<'_>,
    here: space::Token<'_>,
    (gap, rewrote): (Gap, Rewrote),
    inside: Padding,
    quoted: Quoted,
) -> Join
{
    let Before::After(previous) = before
    else {
        return Join::Touch;
    };
    if quoted == Quoted::Yes
        || rewrote == Rewrote::Yes
        || (previous.context == Context::Written && here.context == Context::Written)
    {
        return written(gap);
    }
    match (previous.kind, here.kind) {
        (Neighbour::Open, Neighbour::Close(_)) => Join::Touch,
        (Neighbour::Open, _) | (_, Neighbour::Close(_)) => inside.join(),
        (
            Neighbour::Token | Neighbour::Close(_) | Neighbour::Material | Neighbour::Comment,
            Neighbour::Token | Neighbour::Open | Neighbour::Material | Neighbour::Comment,
        ) => space::join(previous, here),
    }
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
    /// What opened the group.
    opens: Opens,
    /// What ends the group.
    ends: Ends,
}

/// What ends a group: a closer, or the column rule.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Ends
{
    /// A closing bracket, or the end of the form.
    Closer,
    /// The column rule: a layout block, whose first line sets the column it
    /// reads, so a spine before it keeps its line (#5202).
    Column,
}

/// What opened a group: an attribute block, whose member the next line
/// starts at the attribute's own indent, or anything else.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Opens
{
    /// `@[` or `@![`.
    Attribute,
    /// Any other opener, or none.
    Other,
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
    let opens = match group.frame {
        Frame::Bracketed { open, .. } if matches!(<&str>::from(open), "@[" | "@![") => {
            Opens::Attribute
        },
        Frame::Bracketed { .. } | Frame::Form | Frame::Layout { .. } => Opens::Other,
    };
    let ends = match group.frame {
        Frame::Layout { .. } => Ends::Column,
        Frame::Bracketed { .. } | Frame::Form => Ends::Closer,
    };
    let (open, close, closing) = match group.frame {
        Frame::Bracketed {
            open,
            close,
            closing,
            ..
        } => (open, close, closing),
        Frame::Form => {
            let best = run(builder, &group.placed, docs, Mode::Best)?;
            return Ok(Built {
                flat: Flat::Breaks,
                best,
                opens,
                ends,
            });
        },
        // The column rule ends the block, so its items stand one per line
        // under its open and nothing closes it.
        Frame::Layout { open } => {
            let open = builder.text(TextSource::from(<&str>::from(open)))?;
            let indented = item_lines(builder, &group.placed, docs, blank, Columns::Read)?;
            let best = builder.concat(open, indented)?;
            return Ok(Built {
                flat: Flat::Breaks,
                best,
                opens,
                ends,
            });
        },
    };
    let open_text = open;
    let open = builder.text(TextSource::from(<&str>::from(open)))?;
    let close = builder.text(TextSource::from(<&str>::from(close)))?;
    let Some(first) = group.placed.first()
    else {
        let inside = join_doc(builder, closing)?;
        let only = builder.concat_all([open, inside, close])?;
        return Ok(Built {
            flat: Flat::Fits(only),
            best: only,
            opens,
            ends,
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
    let columns = if <&str>::from(open_text) == "{" {
        Columns::Read
    }
    else {
        Columns::Unread
    };
    let indented = item_lines(builder, &group.placed, docs, blank, columns)?;
    let hard = builder.hard_line();
    let broken = builder.concat_all([open, indented, hard, close])?;
    if forced {
        return Ok(Built {
            flat: Flat::Breaks,
            best: broken,
            opens,
            ends,
        });
    }
    let opening = join_doc(builder, first.join)?;
    let closing = join_doc(builder, closing)?;
    let content = run(builder, &group.placed, docs, Mode::Flat)?;
    let inline = builder.concat_all([open, opening, content, closing, close])?;
    let hugs = group.placed.iter().any(|placed| match placed.element {
        Element::Group(GroupId(inner)) => docs
            .get(inner)
            .is_some_and(|built| matches!(built.flat, Flat::Breaks)),
        Element::Text(_)
        | Element::Verbatim(_)
        | Element::LineComment(_)
        | Element::BlockComment(_)
        | Element::Break => false,
    });
    let flat = if hugs {
        Flat::Breaks
    }
    else {
        Flat::Fits(inline)
    };
    if !listed {
        let content = run(builder, &group.placed, docs, Mode::Best)?;
        let best = builder.concat_all([open, opening, content, closing, close])?;
        return Ok(Built {
            flat,
            best,
            opens,
            ends,
        });
    }
    Ok(Built {
        flat,
        best: builder.choice(inline, broken)?,
        opens,
        ends,
    })
}

/// The items of `placed`, each on a line of its own and indented under the
/// line that opens them, a continuation further still, a blank line the
/// source wrote before an item kept as `blank`.
///
/// # Specification
/// trivial.
fn item_lines(
    builder: &mut DocBuilder<'_>,
    placed: &[Placed<'_>],
    docs: &[Built],
    blank: DocId,
    columns: Columns,
) -> Result<DocId, FormatError>
{
    let mut lines: Vec<DocId> = Vec::new();
    for (index, item) in items(placed, docs, columns).into_iter().enumerate() {
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
    Ok(builder.nest(NestAmount::from(INDENT), body)?)
}

/// The document of `join`: nothing, or one space.
///
/// # Specification
/// trivial.
fn join_doc(
    builder: &mut DocBuilder<'_>,
    join: Join,
) -> Result<DocId, FormatError>
{
    Ok(match join {
        Join::Touch => builder.empty(),
        Join::Space => builder.text(TextSource::from(" "))?,
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

/// Whether the column rule reads a group's lines.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Columns
{
    /// It does: a block's braces or a layout block, where a separator, the
    /// source's or the layout pass's, starts each statement.
    Read,
    /// It does not: any other group.
    Unread,
}

/// Whether a line of a broken group starts a statement.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Continuation
{
    /// It starts one: it follows a separator, or a bar leads it, or, in a
    /// group whose lines the column rule does not read, the source indented
    /// it no deeper than the statement before.
    Statement,
    /// It continues the statement before: no separator stands before it,
    /// and the column rule reads its group's lines or the source indented it
    /// deeper than that statement.
    Continued,
}

/// The items of a group's elements: an item ends after a separator, unless a
/// comment follows on the separator's line, before an element the source
/// wrote on a new line, and before each `|` of the form whose group a bar
/// opens, whose arms each such bar starts, an or-pattern's left on its line.
/// A separator is a `;`, a layout block's empty one, or
/// a `,` in a group neither separates and no bar opens, so the commas inside
/// a statement, as in a row's `under [State, Console]` or a clause's
/// `| m, Zero => m`, stay on its line. An item the source started on a new
/// line, after no separator and indented deeper than the statement before it,
/// continues that statement, unless a bar leads it: a `|` at the head of a
/// line is an arm bar, which opens a member as a separator ends one. In a
/// group whose lines the column rule reads, a block's braces or a layout
/// block, such an item continues its
/// statement wherever the source indented it when a separator leads it, which
/// ends that statement, when the tree holds it in the same branch as the code
/// before it, or when that code is a tile of the block's own form, as a
/// line-final `=`; it starts a statement in another branch, as a module's
/// next member does, and the source's indentation decides where a rewrite
/// wrote the code. In a group a bar opens, an item no deeper than the arm
/// before it starts a statement, whatever branch holds it: an arm's own
/// lines stand deeper than its bar, so a data block's member after its
/// constructors, at the bars' column, is no part of the last one. A comment
/// is no statement, so code after a comment the group opens with starts one
/// wherever the comment stands. A line after an attribute block, `@[ … ]`,
/// starts the member the attribute decorates, at the attribute's indent.
///
/// # Specification
/// trivial.
fn items<'group, 'source>(
    placed: &'group [Placed<'source>],
    docs: &[Built],
    columns: Columns,
) -> Vec<Item<'group, 'source>>
{
    let mut items = Vec::new();
    let mut start = 0_usize;
    let mut ended = false;
    // A group a bar opens lists arms: each `|` of its own form opens one, as a
    // separator ends an item, so a broken arm list stands one arm a line. A
    // `|` inside a pattern, an or-pattern's, is no arm's.
    let armed = placed
        .iter()
        .find(|current| current.element.kind() == Kind::Code)
        .is_some_and(
            |first| matches!(first.element, Element::Text(text) if <&str>::from(text) == "|"),
        );
    let commas_end = !armed
        && !placed.iter().any(|current| match current.element {
            Element::Text(text) => <&str>::from(text) == ";",
            Element::Break => true,
            Element::Verbatim(_)
            | Element::LineComment(_)
            | Element::BlockComment(_)
            | Element::Group(_) => false,
        });
    let mut continuation = Continuation::Statement;
    // The branch of the last code before the current element: none before any
    // code, and an unknown one where a rewrite wrote that code.
    let mut last: Option<Option<Branch>> = None;
    // What opened the last code when it is a group: a line after an
    // attribute block starts the member it decorates, at its own indent.
    let mut after = Opens::Other;
    let mut base: Option<Indent> = placed
        .first()
        .filter(|first| first.gap.breaks() == Breaks::Yes && first.element.kind() == Kind::Code)
        .map(|first| first.indent);
    for (index, current) in placed.iter().enumerate() {
        let breaks = current.gap.breaks() == Breaks::Yes;
        let arm = armed
            && matches!(current.element, Element::Text(text) if <&str>::from(text) == "|")
            && current
                .branch
                .is_some_and(|branch| branch.direct == Direct::Yes);
        let starts =
            index > start && (breaks || arm || (ended && current.element.kind() == Kind::Code));
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
                let barred =
                    matches!(current.element, Element::Text(text) if <&str>::from(text) == "|");
                let unseparated = !ended && !barred && breaks;
                let deeper = base.is_some_and(|statement| current.indent > statement);
                // A separator on a line of its own ends the statement before
                // it.
                let separator = matches!(current.element, Element::Text(text)
                    if SEPARATORS.contains(&<&str>::from(text)));
                let continues = after == Opens::Other
                    && match (columns, last) {
                        (Columns::Read | Columns::Unread, None) => false,
                        (Columns::Read, Some(_)) if separator => true,
                        (Columns::Read, Some(Some(previous))) => {
                            current.branch.map_or(deeper, |here| {
                                here.node == previous.node || previous.direct == Direct::Yes
                            })
                        },
                        (Columns::Read, Some(None)) | (Columns::Unread, Some(_)) => deeper,
                    };
                if unseparated && continues && (!armed || deeper) {
                    continuation = Continuation::Continued;
                }
                else {
                    base = Some(current.indent);
                }
            }
        }
        match current.element {
            Element::Text(_) | Element::Verbatim(_) => {
                last = Some(current.branch);
                after = Opens::Other;
            },
            Element::Group(GroupId(group)) => {
                last = Some(current.branch);
                after = docs.get(group).map_or(Opens::Other, |built| built.opens);
            },
            Element::Break | Element::LineComment(_) | Element::BlockComment(_) => {},
        }
        ended = match current.element {
            Element::Text(text) => match <&str>::from(text) {
                ";" => true,
                "," => commas_end,
                _ => false,
            },
            Element::Break => true,
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
/// elements on one line are as far apart as the spacing table decides, and a
/// line break follows a line comment and surrounds a comment the source wrote
/// on its own line. In [`Mode::Best`] each juxtaposed spine is a choice
/// (#5202): on its line as written, or broken before each operand
/// ([`spine_doc`]).
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
    let spines = match mode {
        Mode::Best => spines(placed, docs),
        Mode::Flat => Vec::new(),
    };
    let mut spines = spines.iter().peekable();
    let mut parts: Vec<DocId> = Vec::with_capacity(placed.len().saturating_mul(2));
    let mut previous: Option<Kind> = None;
    let mut index = 0_usize;
    while let Some(current) = placed.get(index) {
        separate(builder, &mut parts, previous, current)?;
        if let Some(spine) = spines.next_if(|spine| spine.start == index) {
            parts.push(spine_doc(builder, placed, spine, docs)?);
            previous = Some(Kind::Code);
            index = spine.end;
            continue;
        }
        parts.push(element_doc(builder, current.element, docs, mode)?);
        previous = Some(current.element.kind());
        index = index.saturating_add(1);
    }
    Ok(builder.concat_all(parts)?)
}

/// The elements of `placed` on one line as [`run`] lays them, with no choice
/// at a spine, each group inside read in `mode`.
///
/// # Specification
/// trivial.
fn line_run(
    builder: &mut DocBuilder<'_>,
    placed: &[Placed<'_>],
    docs: &[Built],
    mode: Mode,
) -> Result<DocId, FormatError>
{
    let mut parts: Vec<DocId> = Vec::with_capacity(placed.len().saturating_mul(2));
    let mut previous: Option<Kind> = None;
    for current in placed {
        separate(builder, &mut parts, previous, current)?;
        parts.push(element_doc(builder, current.element, docs, mode)?);
        previous = Some(current.element.kind());
    }
    Ok(builder.concat_all(parts)?)
}

/// Push onto `parts` what stands between the element before `current`, of
/// kind `previous`, and `current`: nothing before the first element, a line
/// break after a line comment and around a comment the source wrote on its
/// own line, and the spacing table's join otherwise.
///
/// # Specification
/// trivial.
fn separate(
    builder: &mut DocBuilder<'_>,
    parts: &mut Vec<DocId>,
    previous: Option<Kind>,
    current: &Placed<'_>,
) -> Result<(), FormatError>
{
    match previous {
        None => {},
        Some(Kind::LineComment) => parts.push(builder.hard_line()),
        Some(before) => {
            let comment = current.element.kind() != Kind::Code
                || before != Kind::Code
                || current.edge == Edge::Documentation;
            if comment && current.gap.breaks() == Breaks::Yes {
                parts.push(builder.hard_line());
            }
            else {
                parts.push(join_doc(builder, current.join)?);
            }
        },
    }
    Ok(())
}

/// One juxtaposed spine of a run, `f x y`: the elements from `start` up to
/// `end`, and the empty tile before each operand.
#[derive(Debug)]
struct Spine
{
    /// The position of its head's first element.
    start: usize,
    /// The position of each tile, in order.
    tiles: Vec<usize>,
    /// The position after its last operand's last element.
    end: usize,
}

/// Whether an element is the empty tile an application writes between its
/// head and an operand, `f x`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Tile
{
    /// It is: the only empty text a run holds.
    Juxtaposition,
    /// It is not.
    Other,
}

/// Whether `placed` is the empty tile an expression's application writes
/// between its head and an operand. A type's juxtaposition, `Maybe A`, is no
/// such tile: its spine keeps its line, since a signature's spine broken
/// before its operands would stand at the column of the body after it
/// (#5326). Nor is a call's in call form that a postfix form takes as its
/// target, `f(x).l`: a break there would give the postfix form the group
/// alone (#5665).
///
/// # Specification
/// trivial.
fn tile(placed: &Placed<'_>) -> Tile
{
    if matches!(placed.element, Element::Text(text) if <&str>::from(text).is_empty())
        && !matches!(
            placed.context,
            space::Context::TypeGlue | space::Context::CallGlue
        )
    {
        Tile::Juxtaposition
    }
    else {
        Tile::Other
    }
}

/// The juxtaposed spines of `placed`, in order. A spine's head is the
/// elements before its first tile that touch one another, and each operand is
/// the elements after a tile that touch one another, up to the next tile. An
/// element the spacing table sets apart ends the spine, as the `+` of
/// `f x + g y` ends `f x`. A spine that holds a comment, a layout separator or
/// an edge of documentation is no spine: it keeps its line. A spine that
/// another element follows in the run keeps its line too, as `Left 5` in
/// `(Left 5 : Either(Integer, String))`: its broken lines would carry that
/// element on the last operand's line, and the brackets break first. A layout
/// block ends an operand, as the arms after `match holds[<] g a` do: the
/// block's first line sets the column it reads, so an operand line before it
/// would read as the block's first item.
///
/// # Specification
/// trivial.
fn spines(
    placed: &[Placed<'_>],
    docs: &[Built],
) -> Vec<Spine>
{
    let juxtaposes = |placed: &Placed<'_>| tile(placed) == Tile::Juxtaposition;
    let mut spines = Vec::new();
    let mut floor = 0_usize;
    let mut index = 0_usize;
    while let Some(current) = placed.get(index) {
        if !juxtaposes(current) || index <= floor {
            index = index.saturating_add(1);
            continue;
        }
        let mut start = index.saturating_sub(1);
        while start > floor
            && placed
                .get(start)
                .is_some_and(|head| head.join == Join::Touch && !juxtaposes(head))
        {
            start = start.saturating_sub(1);
        }
        let mut tiles = Vec::new();
        let mut end = index;
        while placed.get(end).is_some_and(juxtaposes) {
            tiles.push(end);
            end = end.saturating_add(1);
            let operand = end;
            while placed.get(end).is_some_and(|element| {
                !juxtaposes(element)
                    && !matches!(element.element, Element::Break)
                    && !matches!(element.element, Element::Group(GroupId(group))
                        if docs.get(group).is_some_and(|built| built.ends == Ends::Column))
                    && (end == operand || element.join == Join::Touch)
            }) {
                end = end.saturating_add(1);
            }
            if end == operand {
                break;
            }
        }
        let whole = placed.get(start .. end).unwrap_or_default();
        let plain = whole.iter().enumerate().all(|(at, element)| {
            element.element.kind() == Kind::Code
                && !matches!(element.element, Element::Break)
                && (at == 0 || element.edge == Edge::Within)
        });
        let operands = tiles.iter().all(|&tile| {
            placed
                .get(tile.saturating_add(1))
                .is_some_and(|after| !juxtaposes(after))
        });
        let last = placed
            .get(end ..)
            .unwrap_or_default()
            .iter()
            .all(|after| matches!(after.element, Element::Break));
        if plain && operands && !tiles.is_empty() && last {
            spines.push(Spine { start, tiles, end });
        }
        floor = end;
        index = end;
    }
    spines
}

/// The document of `spine`, a juxtaposed spine of `placed`: a choice between
/// the spine on one line, which wins a tie, and its head followed by each
/// operand on a line of its own, two columns deeper than the head. On its
/// line every group the spine holds stands on one line too, so the layout's
/// cost breaks the outermost spine that overflows the page first, and a
/// bracket inside an operand stays whole on the operand's line when it fits.
/// A group that cannot stand on one line, as a lambda's block, keeps its own
/// lines inside the spine's line: a lambda that ends the spine hugs its last
/// line. The broken spine's head lays its groups out as each best fits the
/// page, as an operand's line does: a bracket in the head that does not fit
/// breaks, as the next pass breaks it on the head's own line (#5528). A spine
/// the source broke before an operand stays broken, as a group the source
/// broke after its opening bracket does, so the layout formats once: the
/// broken spine's blocks break, and on the next pass its line would hug them.
///
/// # Specification
/// trivial.
fn spine_doc(
    builder: &mut DocBuilder<'_>,
    placed: &[Placed<'_>],
    spine: &Spine,
    docs: &[Built],
) -> Result<DocId, FormatError>
{
    let whole = placed
        .get(spine.start .. spine.end)
        .ok_or(FormatError::Unbalanced)?;
    let kept = line_run(builder, whole, docs, Mode::Flat)?;
    let first = spine
        .tiles
        .first()
        .copied()
        .ok_or(FormatError::Unbalanced)?;
    let head = placed
        .get(spine.start .. first)
        .ok_or(FormatError::Unbalanced)?;
    let head = line_run(builder, head, docs, Mode::Best)?;
    let mut lines: Vec<DocId> = Vec::with_capacity(spine.tiles.len().saturating_mul(2));
    for (at, &tile) in spine.tiles.iter().enumerate() {
        let until = spine
            .tiles
            .get(at.saturating_add(1))
            .copied()
            .unwrap_or(spine.end);
        let operand = placed
            .get(tile.saturating_add(1) .. until)
            .ok_or(FormatError::Unbalanced)?;
        lines.push(builder.hard_line());
        lines.push(line_run(builder, operand, docs, Mode::Best)?);
    }
    let operands = builder.concat_all(lines)?;
    let operands = builder.nest(NestAmount::from(INDENT), operands)?;
    let broken = builder.concat(head, operands)?;
    if spine.tiles.iter().any(|&tile| {
        placed
            .get(tile)
            .is_some_and(|tile| tile.gap.breaks() == Breaks::Yes)
    }) {
        return Ok(broken);
    }
    Ok(builder.choice(kept, broken)?)
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
            Element::Group(_) | Element::Break => return Err(FormatError::Unbalanced),
        },
        Element::Break => builder.empty(),
        Element::Group(GroupId(group)) => {
            let built = docs.get(group).ok_or(FormatError::Unbalanced)?;
            match (mode, built.flat) {
                (Mode::Flat, Flat::Fits(flat)) => flat,
                (Mode::Flat, Flat::Breaks) | (Mode::Best, _) => built.best,
            }
        },
    })
}
