//! Where a declaration's brackets first disagree with its layout.
//!
//! The parser pairs each closer with the nearest form still open, so a bracket
//! written once too often, or left out, pairs the wrong ones, and the repair
//! the parser makes stands where that pairing finally fails: often lines past
//! the bracket. In
//!
//! ```text
//! def same(n : Integer) -> -F Integer {
//!   case n {{
//!     0 as zero => return zero,
//!     _ => return n
//!   }
//! }
//! ```
//!
//! the doubled `{` is paired with the case's `}`, the case's `{` with the
//! definition's, and the definition is closed at the end of the source. The
//! layout says which bracket it was. A line that opens a bracket expects its
//! closer on that line when the next line is no deeper, and otherwise at the
//! start of a later line, at the opener's line's indentation. [`misplaced()`]
//! pairs the bracket tiles of one declaration family by family, and reports
//! the first point where the pairing and the layout disagree:
//!
//! - an opener waiting when a line comes back to its line's indentation, or a
//!   closer begins a line left of it, or the declaration ends, has lost its
//!   closer. Its line holds one opener too many when the opener is doubled —
//!   the tile after it is the same opener — and another opener of its line was
//!   answered ([`FormFault::ExtraOpen`], at the opener). Otherwise the closer
//!   is missing ([`Repair::GhostClose`]): on the opener's line, before its
//!   trailing `;` or `,`, when the next line is no deeper; at the end of the
//!   line before the one that comes back, when it is;
//! - a closer beginning a line indented past every opener still waiting, after
//!   a line at its indentation that opens nothing of its family and is followed
//!   by a deeper one, answers an opener left out at the end of that line
//!   ([`FormFault::MissingOpen`]).
//!
//! A line beginning with a closer of any family continues the bracket it
//! closes, so it brings no opener back. A closer that closes nothing and
//! answers no line is left to the module's reading of a closer written twice.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_grammar::Pbg;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::ClosingClass;
use gandr_surface_syntax::DelimSpelling;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SyntaxTree;
use quenchant_shape::shape::Maybe;

use crate::error::FormFault;
use crate::form::FormName;
use crate::form::Repair;
use crate::form::Shape;
use crate::form::TileName;
use crate::form::shape_of;
use crate::form::tile_label;

quenchant_shape::reason_enum! {
    /// Why a declaration's layout places none of its brackets elsewhere.
    pub mod misplaced {
        /// Every bracket stands where the layout expects it.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// Each opener is answered on its line or at the start of a later
            /// line at its indentation, and each closer beginning a line
            /// answers an opener waiting at its indentation.
            Agreed,
        }
    }
}

/// How a tile takes part in bracket nesting.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Nesting
{
    /// An opener of this family: `(`, `[`, `{`, or a compound opener ending in
    /// one, such as `type(`, `@[` or `#{`.
    Opens(ClosingClass),
    /// A closer of this family.
    Closes(ClosingClass),
    /// Any other tile.
    Neither,
}

/// How `label` nests: a closer of its family when it is `)`, `]` or `}`, and
/// otherwise an opener of the family its last character opens.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`Nesting::Closes`] exactly for `)`, `]` and `}`, with their
///   family; [`Nesting::Opens`] for any other label ending in `(`, `[` or `{`,
///   with the family of that character; [`Nesting::Neither`] otherwise.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`misplaced()`] and the module's reading of a closer
///   written twice: the doubled `{`, `}` and `(` of their witnesses are each
///   paired by family.
/// - witness: `lower::tests::a_bracket_the_layout_misplaces_is_refused_where_it_was_written_2242`
/// - witness: `module::tests::a_doubled_closer_is_refused_where_it_was_written_2047`
#[spec(ensures: |ret| ClosingClass::closing(DelimSpelling::from(label.as_ref())).map_or_else(
    || match ret {
        Nesting::Opens(ClosingClass::Paren) => label.as_ref().ends_with('('),
        Nesting::Opens(ClosingClass::Bracket) => label.as_ref().ends_with('['),
        Nesting::Opens(ClosingClass::Brace) => label.as_ref().ends_with('{'),
        Nesting::Neither => !label.as_ref().ends_with(['(', '[', '{']),
        Nesting::Closes(_) => false,
    },
    |close| ret == Nesting::Closes(close),
))]
pub fn nesting(label: TileName) -> Nesting
{
    let text = label.as_ref();
    if let Some(close) = ClosingClass::closing(DelimSpelling::from(text)) {
        return Nesting::Closes(close);
    }
    match text.as_bytes().last().copied() {
        Some(b'(') => Nesting::Opens(ClosingClass::Paren),
        Some(b'[') => Nesting::Opens(ClosingClass::Bracket),
        Some(b'{') => Nesting::Opens(ClosingClass::Brace),
        Some(_) | None => Nesting::Neither,
    }
}

/// The form a bracket tile of `tree` belongs to: the form holding the tile at
/// `bracket` among its children.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the name of the form whose child is a tile spanning `bracket`;
///   [`FormName::ROOT`] when no form holds one.
/// - fails: never.
/// - panics: none.
/// - executable: none — the clause restates the search of the tree.
///
/// # Adequacy
/// - hypothesis: L3 — as [`misplaced()`] and the module's reading of a closer
///   written twice: each names the form of the bracket it reports.
/// - witness: `lower::tests::a_bracket_the_layout_misplaces_is_refused_where_it_was_written_2242`
/// - witness: `module::tests::a_doubled_closer_is_refused_where_it_was_written_2047`
pub fn bracket_form(
    pbg: &Pbg,
    tree: &SyntaxTree<'_>,
    bracket: ByteSpan,
) -> FormName
{
    // economy: the search runs only for a declaration the lowering refused, so
    // an admitted tree never pays for it.
    tree.positions()
        .find(|&position| {
            tree.children(position).any(|child| {
                tree.node(child).is_some_and(|node| {
                    node.span() == bracket && matches!(node.label(), NodeLabel::Tile(_))
                })
            })
        })
        .and_then(|position| tree.node(position))
        .and_then(|node| match shape_of(pbg, node) {
            Ok(Shape::Form { name, .. }) => Some(name),
            Ok(Shape::Root | Shape::Repair(_) | Shape::Layout) | Err(_) => None,
        })
        .unwrap_or(FormName::ROOT)
}

/// A bracket the layout of a declaration places elsewhere than the parser
/// paired it.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Misplaced
{
    /// Where the fault is reported: the opener written once too often, or the
    /// empty point a closer or an opener left out belongs at.
    pub at: ByteSpan,
    /// The bracket whose form the fault names: the opener, or the closer whose
    /// opener was left out.
    pub bracket: ByteSpan,
    /// What the layout says of it.
    pub fault: FormFault,
}

/// A written tile of the declaration, as the layout reads it.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
struct Laid
{
    /// The tile's bytes.
    span: ByteSpan,
    /// How it nests.
    nesting: Nesting,
    /// The tile is a `;` or a `,`.
    separator: bool,
    /// Its label, when the grammar names one.
    label: Option<TileName>,
}

/// A line on which at least one written tile of the declaration begins.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
struct Line
{
    /// Where the line begins.
    start: usize,
    /// How far the line is indented.
    indent: usize,
    /// The line begins with a closer of any family.
    leads_closer: bool,
    /// The first of its tiles, as an index into the declaration's tiles.
    first: usize,
    /// The last of its tiles.
    last: usize,
    /// The end of its last tile.
    end: ByteOffset,
    /// Where a closer missing from the line belongs: before a trailing `;` or
    /// `,`, past the last tile otherwise.
    before_separator: ByteOffset,
}

/// A line, by its index into the declaration's lines.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct LineAt(usize);

/// An opener still waiting for its closer.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
struct Waiting
{
    /// The opener's bytes.
    span: ByteSpan,
    /// The line it stands on.
    line: LineAt,
    /// That line's indentation.
    indent: usize,
    /// The tile after it is the same opener.
    doubled: bool,
}

/// The written tiles of one declaration, laid out on their lines.
///
/// # Specification
/// trivial.
#[derive(Debug)]
struct Layout
{
    /// The tiles, in source order.
    tiles: Vec<Laid>,
    /// The lines they begin on, in source order.
    lines: Vec<Line>,
}

/// One family's pairing of a declaration's brackets, and the earliest fault it
/// has met.
///
/// # Specification
/// trivial.
#[derive(Debug)]
struct Pairing<'layout>
{
    /// The declaration's layout.
    layout: &'layout Layout,
    /// The family paired.
    family: ClosingClass,
    /// The openers still waiting, the innermost last.
    waiting: Vec<Waiting>,
    /// The lines one of whose openers a closer answered.
    answered: BTreeSet<LineAt>,
    /// The earliest fault met so far.
    found: Maybe<Misplaced, misplaced::Absent>,
}

/// The first bracket the layout of the declaration spanning `within` places
/// elsewhere than the parser paired it.
///
/// # Specification
/// - requires: `within` spans one declaration of `tree`.
/// - ensures: among the faults the module documentation lists, read over the
///   written tiles inside `within` family by family, the one reported first;
///   its point lies inside `within`, and its fault is an extra opener, a
///   missing opener or a minted close. Absent when the layout agrees with the
///   pairing.
/// - provides: where a declaration the parser repaired went wrong, when a
///   bracket did.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a doubled `{` of a case is refused at the case's `{`; a
///   `}` left out of a block on one line before the line's `;`; a `}` left out
///   before a line that comes back to the block's indentation at the end of the
///   line before it; a `{` left out of a case at the end of the case's line;
///   and a doubled `(` at the first of the pair.
/// - witness: `lower::tests::a_bracket_the_layout_misplaces_is_refused_where_it_was_written_2242`
#[spec(ensures: |ret| match ret {
    | Maybe::Present(found) => within.start() <= found.at.start()
        && found.at.end() <= within.end()
        && matches!(
            found.fault,
            FormFault::ExtraOpen(_)
                | FormFault::MissingOpen(_)
                | FormFault::Repaired(Repair::GhostClose(_))
        ),
    | Maybe::Absent(_) => true,
})]
pub fn misplaced(
    pbg: &Pbg,
    tree: &SyntaxTree<'_>,
    within: ByteSpan,
) -> Maybe<Misplaced, misplaced::Absent>
{
    let layout = Layout::of(pbg, tree, within);
    [
        ClosingClass::Paren,
        ClosingClass::Bracket,
        ClosingClass::Brace,
    ]
    .into_iter()
    .filter_map(|family| match layout.pair(family) {
        Maybe::Present(found) => Some(found),
        Maybe::Absent(_) => None,
    })
    .min_by_key(|found| found.at.start())
    .map_or(Maybe::Absent(misplaced::Absent::Agreed), Maybe::Present)
}

impl Layout
{
    /// The written tiles of `tree` inside `within`, with their lines.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: every tile and every grout over written bytes inside
    ///   `within`, in source order, each on the line its start is on, every
    ///   line holding at least one; a line's indentation is the blanks it
    ///   begins with.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clause restates the walk over the tree.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`misplaced()`].
    /// - witness: `lower::tests::a_bracket_the_layout_misplaces_is_refused_where_it_was_written_2242`
    fn of(
        pbg: &Pbg,
        tree: &SyntaxTree<'_>,
        within: ByteSpan,
    ) -> Self
    {
        let mut tiles: Vec<Laid> = tree
            .positions()
            .filter_map(|position| {
                let node = tree.node(position)?;
                let span = node.span();
                let inside = span.start() < span.end()
                    && within.start() <= span.start()
                    && span.end() <= within.end();
                if !inside {
                    return None;
                }
                let label = match node.label() {
                    NodeLabel::Tile(_) => match tile_label(pbg, node) {
                        Maybe::Present(label) => Some(label),
                        Maybe::Absent(_) => None,
                    },
                    NodeLabel::Grout { .. } => None,
                    NodeLabel::Wald
                    | NodeLabel::Meld(_)
                    | NodeLabel::GhostClose { .. }
                    | NodeLabel::Space
                    | NodeLabel::Doc => return None,
                };
                Some(Laid {
                    span,
                    label,
                    nesting: label.map_or(Nesting::Neither, nesting),
                    separator: label.is_some_and(|label| {
                        label == TileName::SEMICOLON || label == TileName::COMMA
                    }),
                })
            })
            .collect();
        tiles.sort_unstable_by_key(|laid| laid.span.start());
        let text = <&str>::from(tree.source());
        let mut start = text
            .get(.. usize::from(within.start()))
            .and_then(|before| before.rfind('\n'))
            .map_or(0_usize, |newline| newline.saturating_add(1));
        let mut previous = start;
        let mut lines: Vec<Line> = Vec::new();
        for (index, laid) in tiles.iter().enumerate() {
            let begins = usize::from(laid.span.start());
            if let Some(newline) = text.get(previous .. begins).and_then(|gap| gap.rfind('\n')) {
                start = previous.saturating_add(newline).saturating_add(1);
            }
            match lines.last_mut() {
                Some(line) if line.start == start => {
                    line.before_separator = if laid.separator {
                        line.end
                    }
                    else {
                        laid.span.end()
                    };
                    line.last = index;
                    line.end = laid.span.end();
                },
                Some(_) | None => {
                    let rest = text.get(start ..).unwrap_or_default();
                    let blank = rest
                        .len()
                        .saturating_sub(rest.trim_start_matches([' ', '\t']).len());
                    lines.push(Line {
                        start,
                        indent: blank,
                        leads_closer: rest
                            .get(blank ..)
                            .is_some_and(|lead| lead.starts_with(['}', ')', ']'])),
                        first: index,
                        last: index,
                        end: laid.span.end(),
                        before_separator: laid.span.end(),
                    });
                },
            }
            let ends = usize::from(laid.span.end());
            if let Some(newline) = text.get(begins .. ends).and_then(|inner| inner.rfind('\n')) {
                start = begins.saturating_add(newline).saturating_add(1);
            }
            previous = ends;
        }
        Self { tiles, lines }
    }

    /// The earliest fault in the pairing of `family`'s brackets.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`misplaced()`], over one family.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clause restates the walk over the lines.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`misplaced()`].
    /// - witness: `lower::tests::a_bracket_the_layout_misplaces_is_refused_where_it_was_written_2242`
    fn pair(
        &self,
        family: ClosingClass,
    ) -> Maybe<Misplaced, misplaced::Absent>
    {
        let mut pairing = Pairing {
            layout: self,
            family,
            waiting: Vec::new(),
            answered: BTreeSet::new(),
            found: Maybe::Absent(misplaced::Absent::Agreed),
        };
        for (index, line) in self.lines.iter().enumerate() {
            let here = LineAt(index);
            if !line.leads_closer {
                pairing.unwind(here, |waiting| {
                    waiting.line < here && waiting.indent >= line.indent
                });
            }
            for (index, laid) in self
                .tiles
                .iter()
                .enumerate()
                .take(line.last.saturating_add(1))
                .skip(line.first)
            {
                match laid.nesting {
                    Nesting::Opens(opened) if opened == family => pairing.waiting.push(Waiting {
                        span: laid.span,
                        line: here,
                        indent: line.indent,
                        doubled: self
                            .tiles
                            .get(index.saturating_add(1))
                            .is_some_and(|next| next.label == laid.label),
                    }),
                    Nesting::Closes(closed) if closed == family => pairing.close(*laid, here),
                    Nesting::Opens(_) | Nesting::Closes(_) | Nesting::Neither => {},
                }
            }
        }
        pairing.unwind(LineAt(self.lines.len()), |_| true);
        pairing.found
    }
}

impl Pairing<'_>
{
    /// Settle every innermost opener still waiting that `lost` says has lost
    /// its closer, before the line `before`.
    ///
    /// # Specification
    /// - requires: `before` is a line after every waiting opener's, or one past
    ///   the last.
    /// - ensures: the openers popped are the longest run from the innermost
    ///   that `lost` holds of, each settled by [`Self::unanswered`].
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clause restates the loop.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`misplaced()`].
    /// - witness: `lower::tests::a_bracket_the_layout_misplaces_is_refused_where_it_was_written_2242`
    fn unwind(
        &mut self,
        before: LineAt,
        lost: impl Fn(&Waiting) -> bool,
    )
    {
        while let Some(&waiting) = self.waiting.last()
            && lost(&waiting)
        {
            self.waiting.pop();
            self.unanswered(waiting, before);
        }
    }

    /// Pair the closer `laid`, of the family paired, on the line `here`.
    ///
    /// # Specification
    /// - requires: `here` is the line `laid` begins on.
    /// - ensures: a closer beginning its line first settles every opener
    ///   waiting indented past it; then, when no opener waits at or past its
    ///   indentation and the nearest line at its indentation before it opens
    ///   nothing of the family and is followed by a deeper line, it notes a
    ///   missing opener at that line's end and answers nothing; otherwise it
    ///   answers the innermost opener waiting, if any, and marks that opener's
    ///   line as answered.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clause restates the pairing.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`misplaced()`].
    /// - witness: `lower::tests::a_bracket_the_layout_misplaces_is_refused_where_it_was_written_2242`
    fn close(
        &mut self,
        laid: Laid,
        here: LineAt,
    )
    {
        let layout = self.layout;
        let Some(line) = layout.lines.get(here.0)
        else {
            return;
        };
        let leads = layout
            .tiles
            .get(line.first)
            .is_some_and(|first| first.span == laid.span);
        if leads {
            let column = usize::from(laid.span.start()).saturating_sub(line.start);
            self.unwind(here, |waiting| waiting.indent > column);
            if self
                .waiting
                .last()
                .is_none_or(|waiting| waiting.indent < column)
                && let Some(header) = self.header(here, laid)
            {
                self.note(Misplaced {
                    at: ByteSpan::new(header.end, header.end).unwrap_or(laid.span),
                    bracket: laid.span,
                    fault: FormFault::MissingOpen(self.family),
                });
                return;
            }
        }
        if let Some(waiting) = self.waiting.pop() {
            let _fresh = self.answered.insert(waiting.line);
        }
    }

    /// The line the closer `laid`, beginning the line `here`, answers an
    /// opener left out at the end of.
    ///
    /// # Specification
    /// - requires: `here` is a line of the layout.
    /// - ensures: with `column` the closer's column, the nearest line before
    ///   `here` indented at `column`, past lines indented further only, when it
    ///   holds no opener of the family and the line after it is indented past
    ///   `column`; nothing otherwise.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clause restates the search.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`misplaced()`].
    /// - witness: `lower::tests::a_bracket_the_layout_misplaces_is_refused_where_it_was_written_2242`
    fn header(
        &self,
        here: LineAt,
        laid: Laid,
    ) -> Option<Line>
    {
        let lines = &self.layout.lines;
        let column = usize::from(laid.span.start()).saturating_sub(lines.get(here.0)?.start);
        let found = lines
            .get(.. here.0)?
            .iter()
            .rposition(|line| line.indent <= column)?;
        let header = *lines.get(found)?;
        let deeper = lines.get(found.saturating_add(1))?;
        let opens = self
            .layout
            .tiles
            .get(header.first ..= header.last)
            .unwrap_or_default()
            .iter()
            .any(|laid| laid.nesting == Nesting::Opens(self.family));
        (header.indent == column && deeper.indent > column && !opens).then_some(header)
    }

    /// Settle `waiting`, an opener whose closer never came, lost before the
    /// line `before`.
    ///
    /// # Specification
    /// - requires: `before` is a line after `waiting`'s, or one past the last.
    /// - ensures: notes an extra opener at `waiting` when it is doubled and
    ///   another opener of its line was answered; otherwise a minted close at
    ///   the end of its line, before a trailing `;` or `,`, when no line
    ///   follows it or the next is indented no further than it, and at the end
    ///   of the line before `before` when it is.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clause restates the choice.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`misplaced()`].
    /// - witness: `lower::tests::a_bracket_the_layout_misplaces_is_refused_where_it_was_written_2242`
    fn unanswered(
        &mut self,
        waiting: Waiting,
        before: LineAt,
    )
    {
        if waiting.doubled && self.answered.contains(&waiting.line) {
            self.note(Misplaced {
                at: waiting.span,
                bracket: waiting.span,
                fault: FormFault::ExtraOpen(self.family),
            });
            return;
        }
        let lines = &self.layout.lines;
        let one_line = lines
            .get(waiting.line.0.saturating_add(1))
            .is_none_or(|next| next.indent <= waiting.indent);
        let point = if one_line {
            lines.get(waiting.line.0).map(|line| line.before_separator)
        }
        else {
            lines.get(before.0.saturating_sub(1)).map(|line| line.end)
        };
        let Some(point) = point
        else {
            return;
        };
        self.note(Misplaced {
            at: ByteSpan::new(point, point).unwrap_or(waiting.span),
            bracket: waiting.span,
            fault: FormFault::Repaired(Repair::GhostClose(self.family)),
        });
    }

    /// Keep `fault` when it is reported before every fault met so far.
    ///
    /// # Specification
    /// trivial.
    fn note(
        &mut self,
        fault: Misplaced,
    )
    {
        let earlier = match self.found {
            Maybe::Present(held) => fault.at.start() < held.at.start(),
            Maybe::Absent(_) => true,
        };
        if earlier {
            self.found = Maybe::Present(fault);
        }
    }
}
