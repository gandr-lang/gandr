//! One reading of a held text: the parse every request about the text's
//! structure answers from, made once per text.
//!
//! # A held text is parsed once
//!
//! Semantic tokens, document symbols, folding ranges, selection ranges, a
//! hover and the render bus's report all read the molded tree of the same
//! text. A copy of a document holds that text beside a [`Reading`] of it,
//! made by the first such request after the text last changed: one parse,
//! from which the highlighter's spans, the declarations with their form keys,
//! the folds and the selection skeleton are read and kept. Every later request
//! until the next change answers from them. A change to the text drops the
//! reading, so no answer is read off a text the copy no longer holds.
//!
//! An editor sends the four structural requests after each keystroke, so a
//! parse per request parses each text four times or more and pays the molder's
//! cost on a malformed text, which a text being typed often is, at each. The
//! reading keeps owned answers, not the tree, because the tree borrows the
//! text it is held beside.
//!
//! - Alternatives: a parse per request, which keeps nothing between requests
//!   and pays the molder once per request; the tree itself beside the text,
//!   which borrows the text and would need a self-referential holder; a parse
//!   at each synchronisation, which reads texts no request asks about, since
//!   the session's composition consumes its own tree.
//! - Reversal: a measured memory cost of a reading per held copy, with many
//!   documents open, drops a reading once its requests are answered; a request
//!   that needs the tree's every node, not what is kept here, holds the tree
//!   beside an owned text instead.

use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_parser::parse;
use gandr_surface_render_remote::ByteOffset as RenderOffset;
use gandr_surface_render_remote::HlSpan;
use gandr_surface_render_remote::LineIndex;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::NodeKey;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SourceText;
use gandr_surface_syntax::SyntaxTree;
use quenchant_shape::shape::Maybe;

use crate::outline::Skeleton;
use crate::outline::declarations;
use crate::outline::folds;
use crate::position::Position;
use crate::position::Range;
use crate::protocol::DocumentSymbol;
use crate::protocol::DocumentSymbols;
use crate::protocol::FoldingRange;
use crate::protocol::SelectionRange;
use crate::recheck::grammar;
use crate::recheck::roles;

quenchant_shape::reason_enum! {
    /// Why a text has no reading.
    pub mod unread {
        /// The reason the text was not read.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub enum Absent {
            /// The process's grammar did not build.
            Unbuilt,
            /// The parser could not commit a tree over the text.
            Unparsed,
        }
    }
}

/// A declaration of a read text: its symbol, the key of the form that
/// declares it, and the extent of its head.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Declaration
{
    /// The key of the declaring form, when the tree keys it.
    pub key: Option<NodeKey>,
    /// The symbol it declares.
    pub symbol: DocumentSymbol,
    /// Its head: from the declaring form's own start — past any attribute
    /// block before it — to the brace opening the form's own body, or to the
    /// symbol's end for a form without one.
    pub head: Range,
}

/// The head of the form at `at` declaring `symbol`: from the form's own start
/// to the first brace among its own tiles, or to the symbol's end when the form
/// has none.
///
/// # Specification
/// trivial.
fn head(
    tree: &SyntaxTree<'_>,
    index: &LineIndex<'_>,
    at: NodeIndex,
    symbol: &DocumentSymbol,
) -> Range
{
    let brace = tree.children(at).find_map(|child| {
        let node = tree.node(child)?;
        let NodeLabel::Tile(_) = node.label()
        else {
            return None;
        };
        (tree.fragment(child).map(<&str>::from) == Some("{"))
            .then(|| {
                Position::of_byte(index, RenderOffset::from(usize::from(node.span().start()))).ok()
            })
            .flatten()
    });
    let start = tree
        .node(at)
        .and_then(|node| {
            Position::of_byte(index, RenderOffset::from(usize::from(node.span().start()))).ok()
        })
        .map_or(symbol.range.start, |start| start.max(symbol.range.start));
    Range {
        start,
        end: brace.unwrap_or(symbol.range.end),
    }
}

/// What one parse of a text answers: its highlighter spans, declarations,
/// folds and selection skeleton.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Readout
{
    /// The highlighter's spans, sorted and disjoint.
    spans: Vec<HlSpan>,
    /// The declarations, in source order, each after the one holding it.
    declarations: Vec<Declaration>,
    /// The folding ranges, ascending by first line.
    folds: Vec<FoldingRange>,
    /// The nodes a selection walks.
    skeleton: Skeleton,
}

/// The reading of one text, or why it has none.
#[derive(Clone, Debug, Eq, PartialEq)]
#[repr(transparent)]
pub struct Reading(Maybe<Readout, unread::Absent>);

impl Reading
{
    /// The reading of `text`, from one parse under the process's grammar.
    ///
    /// # Specification
    /// - requires: nothing; any text is admissible input.
    /// - ensures: [`unread::Absent::Unbuilt`] when the grammar did not build,
    ///   [`unread::Absent::Unparsed`] when the parser could not commit a tree;
    ///   otherwise the highlighter's spans over the tree, sorted, pairwise
    ///   disjoint and on character boundaries of `text`, its declarations each
    ///   beside its declaring form's key, its folds and its selection skeleton,
    ///   as [`crate::outline`] reads each off the tree.
    /// - provides: the one parse a held text's structural requests share.
    /// - fails: never; an unread text names its reason.
    /// - panics: none.
    /// - intension: one parse and one walk of the tree per answer kind.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a definition has a pinned semantic-token stream; over
    ///   every corpus source, encoded coverage agrees with the highlighter;
    ///   over every keystroke of the editor scenarios, each structural answer
    ///   read off a connection's held reading equals the one a fresh connection
    ///   reads off its own, so a reading kept past a change, or read off
    ///   another text, disagrees at the keystroke that changed it.
    /// - witness: `recheck::tests::a_definition_produces_semantic_tokens`
    /// - witness: `outline::tests::declarations_nest_as_symbols`
    /// - witness: `session::session::corpus_tokens_cover_the_highlighted_bytes`
    /// - witness: `editor::editor::scenarios::random_edits_keep_every_answer_faithful`
    #[spec(ensures: |ret| match ret.0 {
        Maybe::Present(ref readout) => readout.spans.iter().zip(readout.spans.iter().skip(1))
            .all(|(first, second)| first.range.end() <= second.range.start())
            && readout.spans.iter().all(|span| usize::from(span.range.end()) <= text.as_ref().len()
                && text.as_ref().is_char_boundary(usize::from(span.range.start()))
                && text.as_ref().is_char_boundary(usize::from(span.range.end()))),
        Maybe::Absent(_) => true,
    })]
    #[must_use]
    pub fn of(text: SourceText<'_>) -> Self
    {
        let (Ok(grammar), Ok(roles)) = (grammar(), roles())
        else {
            return Self(Maybe::Absent(unread::Absent::Unbuilt));
        };
        let Ok(parsed) = parse(grammar, text)
        else {
            return Self(Maybe::Absent(unread::Absent::Unparsed));
        };
        let tree = parsed.into_tree();
        let index = LineIndex::new(<&str>::from(text).into());
        Self(Maybe::Present(Readout {
            spans: roles.highlight(&tree).unwrap_or_default(),
            declarations: declarations(grammar, roles, &tree, &index)
                .into_iter()
                .map(|(at, symbol)| Declaration {
                    key: tree.key(at),
                    head: head(&tree, &index, at, &symbol),
                    symbol,
                })
                .collect(),
            folds: folds(&tree, &index),
            skeleton: Skeleton::of(&tree),
        }))
    }

    /// The highlighter's spans over the text, none when it was not read.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub fn spans(&self) -> &[HlSpan]
    {
        match self.0 {
            Maybe::Present(ref readout) => &readout.spans,
            Maybe::Absent(_) => &[],
        }
    }

    /// The declarations of the text, or why it was not read.
    ///
    /// # Specification
    /// trivial.
    pub fn declarations(&self) -> Maybe<&[Declaration], unread::Absent>
    {
        match self.0 {
            Maybe::Present(ref readout) => Maybe::Present(&readout.declarations),
            Maybe::Absent(reason) => Maybe::Absent(reason),
        }
    }

    /// The document symbols of the text: its declarations' symbols, in order;
    /// none when it was not read.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub fn symbols(&self) -> DocumentSymbols
    {
        DocumentSymbols(match self.0 {
            Maybe::Present(ref readout) => readout
                .declarations
                .iter()
                .map(|declaration| declaration.symbol.clone())
                .collect(),
            Maybe::Absent(_) => Vec::new(),
        })
    }

    /// The folding ranges of the text, none when it was not read.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub fn folds(&self) -> &[FoldingRange]
    {
        match self.0 {
            Maybe::Present(ref readout) => &readout.folds,
            Maybe::Absent(_) => &[],
        }
    }

    /// For each of `positions`, the nodes around it, innermost first, ranged
    /// through `index`, built over the text this reading read.
    ///
    /// # Specification
    /// - requires: `index` was built over the text this reading read.
    /// - ensures: one answer per position, in order: the chain
    ///   [`Skeleton::around`] walks, or, in a text that was not read or at a
    ///   position no node reaches, the empty range at the position.
    /// - provides: the answer to `textDocument/selectionRange`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a position inside a name, at a name's end and inside
    ///   an operand are asserted at their exact chains.
    /// - witness: `outline::tests::a_selection_grows_from_the_innermost_form`
    #[spec(ensures: |ret| ret.len() == positions.len())]
    #[must_use]
    pub fn selections(
        &self,
        index: &LineIndex<'_>,
        positions: &[Position],
    ) -> Vec<SelectionRange>
    {
        let unread = |position: Position| SelectionRange {
            ranges: Vec::from([crate::position::Range {
                start: position,
                end: position,
            }]),
        };
        positions
            .iter()
            .map(|&position| match self.0 {
                Maybe::Present(ref readout) => readout
                    .skeleton
                    .around(index, position)
                    .unwrap_or_else(|| unread(position)),
                Maybe::Absent(_) => unread(position),
            })
            .collect()
    }
}
