//! A closer that closes nothing, read back as the closer before it that was
//! written once too often.
//!
//! The parser pairs each closer with the nearest form still open, so a closer
//! written twice balances the wrong opener. In
//!
//! ```text
//! def give_up() -> -F Unit {
//!   hold c = 0;
//!   access c as v { abort(v) }}
//! }
//! ```
//!
//! the second `}` of the access line closes the definition, and the `}` under
//! `def` stands at the root closing nothing. The tree is faithful to that
//! pairing; the mistake is the doubled `}`, and the layout says which closer it
//! is. [`Collector::closed_early`] reads the tiles of the stray's source up to
//! the stray, pairs each closer with the nearest opener before it, and keeps
//! the last closer that follows another tile on its line and closes an opener
//! on an earlier line indented less than its own. When the stray stands first
//! on its line, at that opener's indentation and of the kept closer's family,
//! the kept closer is the one written too often: the stray is refused there, as
//! the form it closed early. A closer of the family that begins a line at that
//! indentation and closes an opener indented less stands where the kept closer
//! belonged, so the displacement moves out to the opener it closes, as when the
//! doubled closer sits in a definition inside a module. Any other tile that
//! begins a line at or left of the indentation sought settles the opener as
//! closed where the parser closed it, and the stray keeps its own refusal.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::ClosingClass;
use gandr_surface_syntax::DelimSpelling;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::NodeLabel;
use quenchant_shape::shape::Maybe;

use super::Collector;
use crate::error::FormFault;
use crate::error::LoweringRefusal;
use crate::form::FormName;
use crate::form::Placed;
use crate::form::Shape;
use crate::form::TileName;
use crate::form::shape_of;
use crate::form::tile_label;

/// How a tile takes part in bracket nesting.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Nesting
{
    /// An opener: `(`, `[`, `{`, or a compound opener such as `@[` or `#{`.
    Opens,
    /// A closer of this family.
    Closes(ClosingClass),
    /// Any other tile.
    Neither,
}

/// A tile of the stray's source, with how it nests.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
struct Tiled
{
    /// The tile's bytes.
    span: ByteSpan,
    /// How it nests.
    nesting: Nesting,
}

/// An opener still waiting for its closer.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
struct Opener
{
    /// The opener's bytes.
    span: ByteSpan,
    /// Where the opener's line starts.
    line: usize,
    /// How far the opener's line is indented.
    indent: usize,
}

/// A closer that follows another tile on its line and closes an opener on an
/// earlier line indented less than its own.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
struct Suspect
{
    /// The closer's bytes.
    span: ByteSpan,
    /// Its family.
    close: ClosingClass,
    /// The bytes of the opener it closes.
    opener: ByteSpan,
    /// The indentation the stray is sought at: its opener's line's, moved out
    /// by each aligned closer after it.
    indent: usize,
}

/// What a closer written twice on a line makes of one root piece of that line:
/// the pieces it tore out of the form it closed early are one stray, led by
/// the line's first piece and refused at the closer.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug)]
pub(super) enum Tearing<'source>
{
    /// The line's first piece: the stray, refused at the closer, owning the
    /// later pieces of the line.
    Leads
    {
        /// The refusal at the closer.
        refusal: LoweringRefusal<'source>,
        /// The later pieces of the line.
        torn: Vec<Placed>,
    },
    /// A later piece of the line, owned by the stray its first piece leads.
    Follows
    {
        /// Whether it is the line's last piece, after which a `;` ends the
        /// stray.
        last: bool,
    },
}

/// How `label` nests: an opener when it ends in `(`, `[` or `{`, a closer of
/// its family when it is `)`, `]` or `}`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`Nesting::Closes`] exactly for `)`, `]` and `}`, with their
///   family; [`Nesting::Opens`] for any other label ending in `(`, `[` or `{`;
///   [`Nesting::Neither`] otherwise.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Collector::closed_early`].
/// - witness: `module::tests::a_doubled_closer_is_refused_where_it_was_written_2047`
#[spec(ensures: |ret| ClosingClass::closing(DelimSpelling::from(label.as_ref())).map_or_else(
    || (ret == Nesting::Opens) == label.as_ref().ends_with(['(', '[', '{']),
    |close| ret == Nesting::Closes(close),
))]
fn nesting(label: TileName) -> Nesting
{
    let text = label.as_ref();
    ClosingClass::closing(DelimSpelling::from(text)).map_or_else(
        || {
            if text.ends_with(['(', '[', '{']) {
                Nesting::Opens
            }
            else {
                Nesting::Neither
            }
        },
        Nesting::Closes,
    )
}

impl<'source> Collector<'_, 'source>
{
    /// The refusal of `stray`, a root child that begins with a closer, at the
    /// closer before it that was written once too often.
    ///
    /// # Specification
    /// - requires: `stray` is a root child of the tree.
    /// - ensures: when `stray` begins with a closer that the closer kept by
    ///   [`Self::repeated_closer`] explains, a malformed-form refusal at that
    ///   closer, of its family, naming the form whose opener it closes; nothing
    ///   otherwise.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a definition whose access closes its block twice is
    ///   refused at the second closer, and a stray after a definition closed at
    ///   the end of a line, then a declaration, keeps its own refusal.
    /// - witness: `module::tests::a_doubled_closer_is_refused_where_it_was_written_2047`
    #[spec(ensures: |ret| ret.as_ref().is_none_or(|refusal| matches!(*refusal,
        LoweringRefusal::MalformedForm { span, fault: FormFault::ExtraClose(_), .. }
            if span.end() <= stray.span.start())))]
    pub(super) fn closed_early(
        &self,
        stray: Placed,
    ) -> Option<LoweringRefusal<'source>>
    {
        let text = <&str>::from(self.tree.source());
        let begins = text
            .get(usize::from(stray.span.start()) ..)
            .is_some_and(|rest| rest.starts_with(['}', ')', ']']));
        if !begins {
            return None;
        }
        let held = self.repeated_closer(stray.span.start())?;
        let form = self
            .tree
            .positions()
            .find(|&position| {
                self.tree.children(position).any(|child| {
                    self.tree.node(child).is_some_and(|node| {
                        node.span() == held.opener && matches!(node.label(), NodeLabel::Tile(_))
                    })
                })
            })
            .and_then(|position| self.tree.node(position))
            .and_then(|node| match shape_of(self.pbg, node) {
                Ok(Shape::Form { name, .. }) => Some(name),
                Ok(Shape::Root | Shape::Repair(_) | Shape::Layout) | Err(_) => None,
            })
            .unwrap_or(FormName::ROOT);
        Some(LoweringRefusal::MalformedForm {
            span: held.span,
            form,
            fault: FormFault::ExtraClose(held.close),
        })
    }

    /// The closer before `stray` that was written once too often, with its
    /// family and the opener it closes, read from the layout of `stray`'s
    /// source.
    ///
    /// # Specification
    /// - requires: `stray` is the start of a tile of the tree.
    /// - ensures: present only when the tile at `stray` is a closer that no
    ///   opener before it in its source waits for, standing first on its line;
    ///   the closer returned is of its family, ends before it, follows another
    ///   tile on its line, and closes an opener on an earlier line indented
    ///   less than the closer's own. Between them, each tile beginning a line
    ///   at or left of that opener's indentation is a closer of the family
    ///   standing at it and closing an opener indented less, whose indentation
    ///   the next such closer, or `stray`, stands at.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::closed_early`].
    /// - witness: `module::tests::a_doubled_closer_is_refused_where_it_was_written_2047`
    #[spec(ensures: |ret| ret.is_none_or(|held| held.span.end() <= stray && held.opener.end() <= held.span.start()))]
    fn repeated_closer(
        &self,
        stray: ByteOffset,
    ) -> Option<Suspect>
    {
        let unit = &self.collected.unit;
        let source = unit.source_at(stray);
        let mut tiles: Vec<Tiled> = self
            .tree
            .positions()
            .filter_map(|position| {
                let node = self.tree.node(position)?;
                let nesting = match node.label() {
                    NodeLabel::Tile(_) => match tile_label(self.pbg, node) {
                        Maybe::Present(label) => nesting(label),
                        Maybe::Absent(_) => Nesting::Neither,
                    },
                    NodeLabel::Grout { .. } => Nesting::Neither,
                    NodeLabel::Wald
                    | NodeLabel::Meld(_)
                    | NodeLabel::GhostClose { .. }
                    | NodeLabel::Space
                    | NodeLabel::Doc => return None,
                };
                let span = node.span();
                (span.start() < span.end()
                    && span.start() <= stray
                    && unit.source_at(span.start()) == source)
                    .then_some(Tiled { span, nesting })
            })
            .collect();
        tiles.sort_unstable_by_key(|tiled| tiled.span.start());
        let text = <&str>::from(self.tree.source());
        let stray = usize::from(stray);
        let mut line = 0_usize;
        let mut lead: Option<usize> = None;
        let mut previous = 0_usize;
        let mut opened: Vec<Opener> = Vec::new();
        let mut suspect: Option<Suspect> = None;
        for tiled in tiles {
            let start = usize::from(tiled.span.start());
            let end = usize::from(tiled.span.end());
            if let Some(newline) = text.get(previous .. start).and_then(|gap| gap.rfind('\n')) {
                line = previous.saturating_add(newline).saturating_add(1);
                lead = None;
            }
            let first = lead.is_none();
            let indent = lead.get_or_insert(start).saturating_sub(line);
            let mut shifted = false;
            match tiled.nesting {
                Nesting::Opens => opened.push(Opener {
                    span: tiled.span,
                    line,
                    indent,
                }),
                Nesting::Closes(close) => match opened.pop() {
                    Some(opener) if first => {
                        if let Some(held) = suspect.as_mut()
                            && held.indent == indent
                            && held.close == close
                            && opener.indent < indent
                        {
                            held.indent = opener.indent;
                            shifted = true;
                        }
                    },
                    Some(opener) => {
                        if opener.line != line && opener.indent < indent {
                            suspect = Some(Suspect {
                                span: tiled.span,
                                close,
                                opener: opener.span,
                                indent: opener.indent,
                            });
                        }
                    },
                    None if start == stray => {
                        return suspect
                            .filter(|held| first && held.indent == indent && held.close == close);
                    },
                    None => {},
                },
                Nesting::Neither => {},
            }
            if first && !shifted && suspect.is_some_and(|held| indent <= held.indent) {
                suspect = None;
            }
            if let Some(newline) = text.get(start .. end).and_then(|inner| inner.rfind('\n')) {
                line = start.saturating_add(newline).saturating_add(1);
                lead = None;
            }
            previous = end;
        }
        None
    }

    /// The runs of root pieces a closer written twice on one line tore out of
    /// the form it closed early.
    ///
    /// The parser pairs the first closer with the form's opener, so the second
    /// closes nothing: the form's tiles before it stand at the root as pieces
    /// of their own, and so does the rest of the form after it. Each piece
    /// refuses as a form of the wrong sort at its own bytes, ahead of the
    /// closer that caused them. A closer is written twice when the one before
    /// it on its line, past any blank, is the same; a closer that follows
    /// anything else stands for an opener left out, not one written too often.
    /// A run is every piece that begins on the doubled closer's line after the
    /// attribute blocks leading it, when a bare tile stands before the closer
    /// or a piece begins after it; a line of whole forms ended by a closer with
    /// nothing after it keeps its refusals.
    ///
    /// # Specification
    /// - requires: `pieces` are the root pieces of one source, in order.
    /// - ensures: each run is led by its first piece and followed by the rest;
    ///   its last piece is at or after a piece beginning with a `)`, `]` or `}`
    ///   that follows the same closer and is not first on its line, every piece
    ///   of the run begins on that line, and the run's refusal is a malformed
    ///   form at that closer, of its family, naming the form of the run's first
    ///   piece; no piece belongs to two runs.
    /// - panics: none.
    /// - executable: none — the clause restates the walk over the pieces.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a codata declaration whose universe's `]` is doubled
    ///   and an operation whose parameter's `)` is doubled refuse at the second
    ///   closer; a closer after a word, an opener left out, keeps its own
    ///   refusal.
    /// - witness: `module::tests::a_closer_doubled_on_its_line_is_refused_where_it_was_written_2051`
    pub(super) fn torn_lines(
        &self,
        pieces: &[Placed],
    ) -> BTreeMap<NodeIndex, Tearing<'source>>
    {
        let text = <&str>::from(self.tree.source());
        let line_of = |at: usize| {
            text.get(.. at)
                .and_then(|before| before.rfind('\n'))
                .map_or(0, |newline| newline.saturating_add(1))
        };
        let line = |placed: &Placed| line_of(usize::from(placed.span.start()));
        let mut tearings = BTreeMap::new();
        let mut claimed: Option<usize> = None;
        for (index, stray) in pieces.iter().enumerate() {
            let start = usize::from(stray.span.start());
            let Some(written) = text.get(start .. start.saturating_add(1))
            else {
                continue;
            };
            // Doubled: the closer before it, past any blank, is the same, and
            // its line opens no more of the family before it than it closes.
            let opener = match written {
                ")" => '(',
                "]" => '[',
                _ => '{',
            };
            let doubled = text.get(line_of(start) .. start).is_some_and(|before| {
                before.trim_end_matches([' ', '\t']).ends_with(written)
                    && before.matches(opener).count() <= before.matches(written).count()
            });
            let Some(close) =
                ClosingClass::closing(DelimSpelling::from(written)).filter(|_| doubled)
            else {
                continue;
            };
            let own = line(stray);
            let Some(before) = pieces.get(.. index)
            else {
                continue;
            };
            let first = before
                .iter()
                .rposition(|placed| line(placed) != own)
                .map_or(0, |earlier| earlier.saturating_add(1));
            let first = (first .. index)
                .find(|&at| {
                    pieces.get(at).is_some_and(|placed| {
                        !text
                            .get(usize::from(placed.span.start()) ..)
                            .is_some_and(|rest| rest.starts_with("@["))
                    })
                })
                .unwrap_or(index);
            if first == index || claimed.is_some_and(|last| last >= first) {
                continue;
            }
            let last = pieces
                .get(index ..)
                .and_then(|after| after.iter().position(|placed| line(placed) != own))
                .map_or(pieces.len(), |later| index.saturating_add(later))
                .saturating_sub(1);
            let bare = pieces.get(first .. index).is_some_and(|torn| {
                torn.iter().any(|placed| {
                    self.tree
                        .node(placed.node)
                        .is_some_and(|node| matches!(node.label(), NodeLabel::Tile(_)))
                })
            });
            if !bare && last == index {
                continue;
            }
            let (Some(lead), Some(rest)) = (
                pieces.get(first),
                pieces.get(first.saturating_add(1) ..= last),
            )
            else {
                continue;
            };
            let form = self
                .tree
                .node(lead.node)
                .and_then(|node| match shape_of(self.pbg, node) {
                    Ok(Shape::Form { name, .. }) => Some(name),
                    Ok(Shape::Root | Shape::Repair(_) | Shape::Layout) | Err(_) => None,
                })
                .unwrap_or(FormName::ROOT);
            let Ok(span) = ByteSpan::new(
                ByteOffset::from(start),
                ByteOffset::from(start.saturating_add(1)),
            )
            else {
                continue;
            };
            claimed = Some(last);
            let _led = tearings.insert(lead.node, Tearing::Leads {
                refusal: LoweringRefusal::MalformedForm {
                    span,
                    form,
                    fault: FormFault::ExtraClose(close),
                },
                torn: rest.to_vec(),
            });
            for (at, placed) in rest.iter().enumerate() {
                let _followed = tearings.insert(placed.node, Tearing::Follows {
                    last: at.saturating_add(1) == rest.len(),
                });
            }
        }
        tearings
    }
}
