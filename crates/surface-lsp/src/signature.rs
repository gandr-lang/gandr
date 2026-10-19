//! Signature help: the declared head of the call a position stands in, and the
//! argument the position writes.
//!
//! A held text's reading keeps every call the parser molded, a value's call
//! and a family's application alike, ordered by where its arguments open
//! ([`Calls`]). A copy's hovering keeps the head of every declaration and
//! constructor its import closure writes ([`Signatures`]): the name through its
//! parameters and its result, each parameter's place in that label, and the
//! documentation written for it. Both are read once per text, off the parse
//! each already makes. A request takes the innermost call whose arguments hold
//! the position. The type table's referent index ([`TypeTable::referent`])
//! gives the declaration the call's head refers to, and the request answers
//! that declaration's head. It reads no text and resolves no name.
//!
//! A head is read off its declaring form:
//!
//! | Form | Label | Parameters |
//! | --- | --- | --- |
//! | `def plus(n : Nat, m : Nat) -> -F Nat` | `plus(n : Nat, m : Nat) -> -F Nat` | `n : Nat`, `m : Nat` |
//! | `def double : +U (Nat -> -F Nat)` | `double : +U (Nat -> -F Nat)` | each domain of the arrow: `Nat` |
//! | `Cons : (head : a, tail : List(a)) --> List(a)` | as written | `head : a`, `tail : List(a)` |
//! | `data List(a : Type) : Type` | `List(a : Type) : Type` | `a : Type` |
//!
//! The pieces of a head are joined with one space wherever the source leaves
//! layout between them, so a head written over several lines reads on one,
//! and its comments are dropped.
//!
//! [`TypeTable::referent`]: gandr_surface_dispatcher::TypeTable::referent

use alloc::string::String;
use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_dispatcher::Referent;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::RoleTable;
use gandr_surface_grammar::Sort;
use gandr_surface_lowering::Documentation;
use gandr_surface_lowering::SourceIndex;
use gandr_surface_lowering::Unit;
use gandr_surface_lowering::read_doc;
use gandr_surface_render_remote::HlRole;
use gandr_surface_render_remote::LineIndex;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::Node;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SourceText;
use gandr_surface_syntax::SyntaxTree;
use quenchant_shape::shape::Maybe;

use crate::hover::Hovering;
use crate::position::Position;
use crate::protocol::Answer;
use crate::protocol::LabelOffsets;
use crate::protocol::MarkupContent;
use crate::protocol::ParameterInformation;
use crate::protocol::ParameterLabel;
use crate::protocol::SignatureHelp;
use crate::protocol::SignatureInformation;
use crate::reading::Reading;

/// The rule of a value's call, `f(a, b)`.
const CALL: &str = "call_expression";

/// The rule of a family's application, `List(a)`.
const APPLICATION: &str = "type_application";

/// The rule of an attribute block standing before the declaration it
/// decorates, whose documentation documents that declaration.
const ATTRIBUTE_BLOCK: &str = "attribute_block";

/// The rules a function type's arrow is read through: the thunk around it, and
/// the parentheses around either.
const ENCLOSING: [&str; 2] = ["u_type", PARENTHESES];

/// The rule of a parenthesised type, a wrapper or a telescope.
const PARENTHESES: &str = "parenthesized_type";

/// The rule of a computation's function type, `A -> B`.
const ARROW: &str = "function_type";

/// The rule of a value's function type over a telescope, `(a : A) => B`.
const VALUE_ARROW: &str = "value_function_type";

/// One call the parser molded: its head, where its arguments open, the commas
/// between them and the parenthesis closing them.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Call
{
    /// The bytes of the head.
    head: ByteSpan,
    /// Just past the `(` opening the arguments.
    open: ByteOffset,
    /// The start of each `,` between the arguments, ascending.
    separators: Vec<ByteOffset>,
    /// The start of the written `)`, or, when the parser closed the call, the
    /// end of the form it molded.
    close: ByteOffset,
    /// The position of the innermost call holding this one, among the calls
    /// in order.
    holder: Option<usize>,
}

/// Every call of a text, ascending by where its arguments open.
///
/// # Specification
/// - requires: built by [`Calls::of`].
/// - ensures: ascending by `open`; every holder is the position of a call
///   holding the one naming it.
/// - panics: none.
/// - executable: none — a carrier; [`Calls::of`] and [`Calls::at`] carry the
///   predicates.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Calls::at`].
/// - witness: `signature::tests::the_innermost_call_answers_with_its_argument`
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Calls(Vec<Call>);

impl Calls
{
    /// The calls of `tree`, parsed under `grammar`.
    ///
    /// # Specification
    /// - requires: `tree` was parsed under `grammar`.
    /// - ensures: one call per molded call or family application that writes an
    ///   opening `(` among its own tiles: its first child as its head, its own
    ///   `,` tiles as separators, its own `)` as its close, or the form's end
    ///   when the parser closed it; ascending by opening, each naming the
    ///   innermost call holding it.
    /// - provides: the calls a reading keeps for signature help.
    /// - fails: never.
    /// - panics: none.
    /// - intension: one walk of the tree with an explicit stack and one sort.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a nested call, a call in a call's head, a family's
    ///   application and a call the parser closed are each found where they are
    ///   written.
    /// - witness: `signature::tests::the_innermost_call_answers_with_its_argument`
    #[spec(ensures: |ret| ret.0.windows(2).all(|pair| matches!(pair, [first, second] if first.open <= second.open)))]
    #[must_use]
    pub fn of(
        grammar: &Pbg,
        tree: &SyntaxTree<'_>,
    ) -> Self
    {
        let mut found: Vec<Call> = Vec::new();
        let mut pending: Vec<(NodeIndex, Option<usize>)> = Vec::from([(tree.root(), None)]);
        while let Some((at, holder)) = pending.pop() {
            let holder = call(grammar, tree, at).map_or(holder, |mut written| {
                written.holder = holder;
                found.push(written);
                Some(found.len().saturating_sub(1))
            });
            pending.extend(tree.children(at).map(|child| (child, holder)));
        }
        let mut order: Vec<usize> = (0 .. found.len()).collect();
        order.sort_by_key(|&position| found.get(position).map(|written| written.open));
        let mut placed = alloc::vec![0_usize; found.len()];
        for (rank, &position) in order.iter().enumerate() {
            if let Some(slot) = placed.get_mut(position) {
                *slot = rank;
            }
        }
        let mut calls: Vec<Call> = order
            .iter()
            .filter_map(|&position| found.get(position).cloned())
            .collect();
        for written in &mut calls {
            written.holder = written
                .holder
                .and_then(|holder| placed.get(holder).copied());
        }
        Self(calls)
    }

    /// The head of the innermost call whose arguments hold `offset`, and how
    /// many of its separators stand before `offset`.
    ///
    /// # Specification
    /// - requires: nothing; any offset is admitted.
    /// - ensures: among the calls whose `(` ends at or before `offset` and
    ///   whose close starts at or after it, the one opened last, with the count
    ///   of its separators starting before `offset`; none when no call holds
    ///   it.
    /// - provides: the call a signature-help request at `offset` answers.
    /// - fails: never.
    /// - panics: none.
    /// - intension: a binary search for the last call opened at or before
    ///   `offset`, then one step per call holding it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a position in a nested call answers it, one past its
    ///   close answers the call around it, one in a call's head answers the
    ///   call holding that call, and the separators before the position count
    ///   the argument.
    /// - witness: `signature::tests::the_innermost_call_answers_with_its_argument`
    #[spec(ensures: |ret| ret.is_none() || !self.0.is_empty())]
    #[must_use]
    pub fn at(
        &self,
        offset: ByteOffset,
    ) -> Option<(ByteSpan, Argument)>
    {
        let last = self.0.partition_point(|written| written.open <= offset);
        let mut at = last.checked_sub(1_usize);
        while let Some(written) = at.and_then(|position| self.0.get(position)) {
            if written.open <= offset && offset <= written.close {
                let argument = written
                    .separators
                    .partition_point(|&separator| separator < offset);
                return Some((written.head, Argument(argument)));
            }
            at = written.holder;
        }
        None
    }
}

/// The position of the argument a position writes among a call's arguments,
/// from zero.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Argument(pub usize);

/// The call the form at `at` is, when it is one that writes its opening `(`.
///
/// # Specification
/// trivial.
fn call(
    grammar: &Pbg,
    tree: &SyntaxTree<'_>,
    at: NodeIndex,
) -> Option<Call>
{
    let node = tree.node(at)?;
    let NodeLabel::Meld(mold) = node.label()
    else {
        return None;
    };
    let rule = grammar.rule_of(mold).ok()?.name().0;
    if rule != CALL && rule != APPLICATION {
        return None;
    }
    let mut head = None;
    let mut open = None;
    let mut separators = Vec::new();
    let mut close = node.span().end();
    for child in tree.children(at) {
        let Some(held) = tree.node(child)
        else {
            continue;
        };
        match held.label() {
            NodeLabel::Tile(tile)
                if grammar
                    .rule_of(tile)
                    .is_ok_and(|owner| owner.name().0 == rule) =>
            {
                match tree.fragment(child).map(<&str>::from) {
                    Some("(") if open.is_none() => open = Some(held.span().end()),
                    Some(",") if open.is_some() => separators.push(held.span().start()),
                    Some(")") if open.is_some() => close = held.span().start(),
                    Some(_) | None => {},
                }
                if head.is_none() {
                    head = Some(held.span());
                }
            },
            NodeLabel::Meld(_) | NodeLabel::Tile(_) => {
                if head.is_none() {
                    head = Some(held.span());
                }
            },
            NodeLabel::Wald
            | NodeLabel::Grout { .. }
            | NodeLabel::GhostClose { .. }
            | NodeLabel::Space
            | NodeLabel::Doc => {},
        }
    }
    Some(Call {
        head: head?,
        open: open?,
        separators,
        close,
        holder: None,
    })
}

/// A run of a label: where a piece or a parameter starts and ends in it, in
/// bytes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Place
{
    /// Its first byte.
    start: usize,
    /// One past its last byte.
    end: usize,
}

/// A head: its label, each parameter's place in the label, and the
/// documentation written for it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Signature
{
    /// The name through its parameters and its result, on one line.
    label: String,
    /// Each parameter's place in `label`, in written order.
    parameters: Vec<Place>,
    /// The documentation written for the declaration or constructor.
    documentation: Option<String>,
}

/// The heads an import closure writes, by the source and the name tile of
/// each declaration, constructor and binder typed by a function.
///
/// # Specification
/// - requires: built by [`Signatures::of`].
/// - ensures: ascending by source, then name tile; no tile twice.
/// - panics: none.
/// - executable: none — a carrier; [`Signatures::of`] and
///   [`Signatures::declared`] carry the predicates.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Signatures::of`].
/// - witness: `signature::tests::each_head_reads_its_parameters`
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Signatures(Vec<((SourceIndex, ByteSpan), Signature)>);

impl Signatures
{
    /// The heads `tree`, parsed under `grammar` over the text `unit` lays out
    /// and classified by `roles`, writes, each keyed by the source holding its
    /// name and the name's span in that source's own text.
    ///
    /// # Specification
    /// - requires: `tree` was parsed under `grammar` over the text `unit` lays
    ///   out.
    /// - ensures: one head per tile an item or module member owns that the
    ///   highlighter classifies as a function, a value, a type or a constructor
    ///   being declared, as the module documentation's table reads it, its
    ///   documentation that of the documentation nodes written before it in its
    ///   form since the last head, else of those written before the form or in
    ///   the attribute blocks before it; then one head per tile any form owns
    ///   or holds that the form's own `:` follows and a function type after it,
    ///   as the table reads it, undocumented; each for a tile `unit` places in
    ///   a source, the first head for a tile kept.
    /// - provides: the index a signature-help request answers from, built once
    ///   per text.
    /// - fails: never.
    /// - panics: none.
    /// - intension: one walk of the tree, one pass over each form's children,
    ///   and one sort.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a function with a parameter list, one with a
    ///   signature's arrow, a family with parameters, a constructor with fields
    ///   and one with none, a head over two lines, documented ones, a parameter
    ///   typed by an arrow and record fields typed by an arrow and over a
    ///   telescope each read at their exact label and parameters.
    /// - witness: `signature::tests::each_head_reads_its_parameters`
    #[spec(ensures: |ret| ret.0.windows(2).all(|pair| matches!(pair, [first, second] if first.0 < second.0)))]
    #[must_use]
    pub fn of(
        grammar: &Pbg,
        roles: &RoleTable,
        tree: &SyntaxTree<'_>,
        unit: &Unit,
    ) -> Self
    {
        let text = SourceText::from(
            tree.fragment(tree.root())
                .map(<&str>::from)
                .unwrap_or_default(),
        );
        let mut heads: Vec<((SourceIndex, ByteSpan), Signature)> = Vec::new();
        let mut pending: Vec<(NodeIndex, Option<String>)> = Vec::from([(tree.root(), None)]);
        while let Some((at, carried)) = pending.pop() {
            let read = Form::of(grammar, roles, tree, at);
            if let Some(ref form) = read {
                form.heads(grammar, tree, text, carried, &mut |named, signature| {
                    if let Some(key) = placed(unit, named) {
                        heads.push((key, signature));
                    }
                });
            }
            let first = pending.len();
            let mut documented: Option<String> = None;
            for child in tree.children(at) {
                let Some(node) = tree.node(child)
                else {
                    continue;
                };
                match node.label() {
                    NodeLabel::Doc => append(&mut documented, documentation(grammar, tree, child)),
                    NodeLabel::Meld(mold)
                        if grammar
                            .rule_of(mold)
                            .is_ok_and(|rule| rule.name().0 == ATTRIBUTE_BLOCK) =>
                    {
                        for inner in tree.children(child) {
                            if tree.node(inner).map(Node::label) == Some(NodeLabel::Doc) {
                                append(&mut documented, documentation(grammar, tree, inner));
                            }
                        }
                    },
                    NodeLabel::Meld(_) => pending.push((child, documented.take())),
                    NodeLabel::Tile(_) => documented = None,
                    NodeLabel::Wald
                    | NodeLabel::Grout { .. }
                    | NodeLabel::GhostClose { .. }
                    | NodeLabel::Space => {},
                }
            }
            if let Some(added) = pending.get_mut(first ..) {
                added.reverse();
            }
        }
        heads.sort_by_key(|held| held.0);
        heads.dedup_by(|second, first| first.0 == second.0);
        Self(heads)
    }

    /// The head written where `referent` is named.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub fn declared(
        &self,
        referent: &Referent,
    ) -> Option<&Signature>
    {
        let key = (referent.source(), referent.named());
        self.0
            .binary_search_by(|held| held.0.cmp(&key))
            .ok()
            .and_then(|at| self.0.get(at))
            .map(|held| &held.1)
    }
}

/// `span`, a span of `unit`'s text, as the source holding its start writes it,
/// with that source.
///
/// # Specification
/// trivial.
fn placed(
    unit: &Unit,
    span: ByteSpan,
) -> Option<(SourceIndex, ByteSpan)>
{
    let source = unit.source_at(span.start());
    let base = usize::from(unit.sources().get(usize::from(source))?.start());
    let start = usize::from(span.start()).checked_sub(base)?;
    let end = usize::from(span.end()).checked_sub(base)?;
    let moved = ByteSpan::new(ByteOffset::from(start), ByteOffset::from(end)).ok()?;
    Some((source, moved))
}

/// `more` appended to `documented` on a line of its own.
///
/// # Specification
/// trivial.
fn append(
    documented: &mut Option<String>,
    more: Option<String>,
)
{
    let Some(more) = more
    else {
        return;
    };
    match *documented {
        Some(ref mut held) => {
            held.push('\n');
            held.push_str(&more);
        },
        None => *documented = Some(more),
    }
}

/// The text of the documentation node at `at`, none when it does not read.
///
/// # Specification
/// trivial.
fn documentation(
    grammar: &Pbg,
    tree: &SyntaxTree<'_>,
    at: NodeIndex,
) -> Option<String>
{
    let mut read = Documentation::default();
    read_doc(grammar, tree, at, &mut read).ok()?;
    Some(String::from(read.text().as_ref()))
}

/// One child of a form, as a head reads it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Piece
{
    /// A tile the form owns, with its highlighter role.
    Own(ByteSpan, Option<HlRole>),
    /// An operand: a form or a tile of another rule.
    Operand(NodeIndex, ByteSpan),
    /// A documentation node.
    Doc(NodeIndex),
}

impl Piece
{
    /// The bytes it covers; none for documentation.
    ///
    /// # Specification
    /// trivial.
    const fn span(self) -> Option<ByteSpan>
    {
        match self {
            Self::Own(span, _) | Self::Operand(_, span) => Some(span),
            Self::Doc(_) => None,
        }
    }
}

/// A form's children, as its heads read them, and whether it declares what
/// its name tiles name.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Form
{
    /// Its own tiles, its operands and its documentation, in order.
    pieces: Vec<Piece>,
    /// Whether it is an item or a module member.
    declares: Declares,
}

/// Whether a form declares what its name tiles name.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Declares
{
    /// An item or a module member.
    Names,
    /// Any other form.
    Nothing,
}

impl Form
{
    /// The children of the form at `at`, when it is a form: its own tiles,
    /// its operands and its documentation, layout and repairs left out.
    ///
    /// # Specification
    /// trivial.
    fn of(
        grammar: &Pbg,
        roles: &RoleTable,
        tree: &SyntaxTree<'_>,
        at: NodeIndex,
    ) -> Option<Self>
    {
        let NodeLabel::Meld(mold) = tree.node(at)?.label()
        else {
            return None;
        };
        let declares = if matches!(
            grammar.mold(mold).ok()?.sort,
            Sort::Item | Sort::ModuleMember
        ) {
            Declares::Names
        }
        else {
            Declares::Nothing
        };
        let rule = grammar.rule_of(mold).ok()?.name().0;
        let mut pieces = Vec::new();
        for child in tree.children(at) {
            let Some(node) = tree.node(child)
            else {
                continue;
            };
            match node.label() {
                NodeLabel::Tile(tile)
                    if grammar
                        .rule_of(tile)
                        .is_ok_and(|owner| owner.name().0 == rule) =>
                {
                    pieces.push(Piece::Own(node.span(), roles.role_of(tile).ok()));
                },
                NodeLabel::Tile(_) | NodeLabel::Meld(_) => {
                    pieces.push(Piece::Operand(child, node.span()));
                },
                NodeLabel::Doc => pieces.push(Piece::Doc(child)),
                NodeLabel::Wald
                | NodeLabel::Grout { .. }
                | NodeLabel::GhostClose { .. }
                | NodeLabel::Space => {},
            }
        }
        Some(Self { pieces, declares })
    }

    /// Hand each head the form writes in `text` to `found`, by its name tile:
    /// each name a declaring form declares, the first documented by `carried`
    /// unless the form documents it, then each tile it types by a function.
    ///
    /// # Specification
    /// trivial.
    fn heads(
        &self,
        grammar: &Pbg,
        tree: &SyntaxTree<'_>,
        text: SourceText<'_>,
        carried: Option<String>,
        found: &mut impl FnMut(ByteSpan, Signature),
    )
    {
        if self.declares == Declares::Names {
            let mut documented = carried;
            for (at, &piece) in self.pieces.iter().enumerate() {
                match piece {
                    Piece::Doc(node) => {
                        append(&mut documented, documentation(grammar, tree, node));
                    },
                    Piece::Own(named, Some(role)) if NAMING.contains(&role) => {
                        let from = self.pieces.get(at ..).unwrap_or_default();
                        found(named, head(grammar, tree, text, from, documented.take()));
                    },
                    Piece::Own(..) | Piece::Operand(..) => {},
                }
            }
        }
        for window in self.pieces.windows(3) {
            let &[named, Piece::Own(colon, _), Piece::Operand(typed, span)] = window
            else {
                continue;
            };
            let tile = match named {
                Piece::Own(tile, _) => Some(tile),
                Piece::Operand(node, tile) => {
                    matches!(tree.node(node).map(Node::label), Some(NodeLabel::Tile(_)))
                        .then_some(tile)
                },
                Piece::Doc(_) => None,
            };
            if let Some(tile) = tile
                && <&str>::from(spelled(text, colon)) == ":"
                && let Some(domains) = domains(grammar, tree, typed)
            {
                let (label, placed) = labelled(text, window);
                let parameters = placed
                    .get(2)
                    .map(|&place| within(span, place, &domains))
                    .unwrap_or_default();
                found(tile, Signature {
                    label,
                    parameters,
                    documentation: None,
                });
            }
        }
    }
}

/// The roles of a tile naming what its form declares.
const NAMING: [HlRole; 4] = [
    HlRole::FunctionDef,
    HlRole::VariableDef,
    HlRole::Type,
    HlRole::Constructor,
];

/// The head of `text` whose pieces start with its name `from`, documented by
/// `documentation`: the pieces up to the next name, the start of a body or
/// documentation.
///
/// # Specification
/// trivial.
fn head(
    grammar: &Pbg,
    tree: &SyntaxTree<'_>,
    text: SourceText<'_>,
    from: &[Piece],
    documentation: Option<String>,
) -> Signature
{
    let tail = from.get(1 ..).unwrap_or_default();
    let length = tail
        .iter()
        .position(|&piece| match piece {
            Piece::Own(span, role) => {
                role.is_some_and(|role| NAMING.contains(&role))
                    || matches!(<&str>::from(spelled(text, span)), "{" | "=" | ";" | "}")
            },
            Piece::Doc(_) => true,
            Piece::Operand(..) => false,
        })
        .unwrap_or(tail.len());
    let pieces = from.get(..= length).unwrap_or_default();
    let (label, placed) = labelled(text, pieces);
    let parameters = parameters(grammar, tree, text, pieces, &placed);
    Signature {
        label,
        parameters,
        documentation,
    }
}

/// The label `pieces` spell in `text`, joined by one space wherever `text`
/// leaves layout between them, beside each piece's place in it.
///
/// # Specification
/// trivial.
fn labelled(
    text: SourceText<'_>,
    pieces: &[Piece],
) -> (String, Vec<Place>)
{
    let mut label = String::new();
    let mut placed: Vec<Place> = Vec::with_capacity(pieces.len());
    let mut previous: Option<ByteSpan> = None;
    for span in pieces.iter().filter_map(|piece| piece.span()) {
        if previous.is_some_and(|before| before.end() < span.start()) {
            label.push(' ');
        }
        let start = label.len();
        label.push_str(<&str>::from(spelled(text, span)));
        placed.push(Place {
            start,
            end: label.len(),
        });
        previous = Some(span);
    }
    (label, placed)
}

/// Each of `spans`, written inside the piece covering `base` that the label
/// writes at `place`, as its place in the label.
///
/// # Specification
/// trivial.
fn within(
    base: ByteSpan,
    place: Place,
    spans: &[ByteSpan],
) -> Vec<Place>
{
    let moved = |offset: ByteOffset| {
        place
            .start
            .saturating_add(usize::from(offset).saturating_sub(usize::from(base.start())))
    };
    spans
        .iter()
        .map(|span| Place {
            start: moved(span.start()),
            end: moved(span.end()),
        })
        .collect()
}

/// The bytes `span` covers in `text`.
///
/// # Specification
/// trivial.
fn spelled(
    text: SourceText<'_>,
    span: ByteSpan,
) -> SourceText<'_>
{
    SourceText::from(
        <&str>::from(text)
            .get(usize::from(span.start()) .. usize::from(span.end()))
            .unwrap_or_default(),
    )
}

/// The parameters of the head `pieces` of `text`, its name first, each piece
/// written at its place in `placed`: the entries of a parenthesised list after
/// the name, or after its `:`; else the domains of the function type its `:`
/// types it by.
///
/// # Specification
/// trivial.
fn parameters(
    grammar: &Pbg,
    tree: &SyntaxTree<'_>,
    text: SourceText<'_>,
    pieces: &[Piece],
    placed: &[Place],
) -> Vec<Place>
{
    let own = |at: usize, written: &str| matches!(pieces.get(at), Some(&Piece::Own(span, _)) if <&str>::from(spelled(text, span)) == written);
    let after = |at: usize| {
        entries(
            text,
            pieces.get(at ..).unwrap_or_default(),
            placed.get(at ..).unwrap_or_default(),
        )
    };
    if own(1, "(") {
        return after(2);
    }
    if own(1, ":") && own(2, "(") {
        return after(3);
    }
    if own(1, ":")
        && let (Some(&Piece::Operand(node, span)), Some(&place)) = (pieces.get(2), placed.get(2))
    {
        return domains(grammar, tree, node)
            .map(|domains| within(span, place, &domains))
            .unwrap_or_default();
    }
    Vec::new()
}

/// The entries of the parenthesised list of `text` whose pieces after its `(`
/// are `pieces`, written at `placed`, each from its first piece's start to its
/// last piece's end.
///
/// # Specification
/// trivial.
fn entries(
    text: SourceText<'_>,
    pieces: &[Piece],
    placed: &[Place],
) -> Vec<Place>
{
    let mut found = Vec::new();
    let mut entry: Option<Place> = None;
    let mut depth = 0_usize;
    for (&piece, &place) in pieces.iter().zip(placed) {
        let written = match piece {
            Piece::Own(span, _) => <&str>::from(spelled(text, span)),
            Piece::Operand(..) | Piece::Doc(_) => "",
        };
        match written {
            "," | ")" if depth == 0 => {
                found.extend(entry.take());
                if written == ")" {
                    break;
                }
                continue;
            },
            "(" => depth = depth.saturating_add(1),
            ")" => depth = depth.saturating_sub(1),
            _ => {},
        }
        entry = Some(entry.map_or(place, |first| Place {
            start: first.start,
            end: place.end,
        }));
    }
    found
}

/// The bytes of each parameter the function type at `at` takes, read through
/// the thunks and parentheses around it, outermost first: the domain of each
/// `->`, and each entry of the parenthesised telescope before each `=>`; none
/// when `at` is no function type.
///
/// # Specification
/// trivial.
fn domains(
    grammar: &Pbg,
    tree: &SyntaxTree<'_>,
    at: NodeIndex,
) -> Option<Vec<ByteSpan>>
{
    let mut found = Vec::new();
    let mut function = None;
    let mut at = at;
    while let Some(read) = Operands::of(grammar, tree, at) {
        match (read.rule, read.nodes.as_slice()) {
            (enclosing, &[inner]) if ENCLOSING.contains(&enclosing) && !read.listed => {
                at = inner;
            },
            (ARROW, &[domain, .., codomain]) => {
                found.extend(tree.node(domain).map(Node::span));
                function = Some(());
                at = codomain;
            },
            (VALUE_ARROW, &[domain, .., codomain]) => {
                found.extend(telescope(grammar, tree, domain));
                function = Some(());
                at = codomain;
            },
            _ => break,
        }
    }
    function.map(|()| found)
}

/// A form's rule, its operands, and whether it owns a `,` or a `:`, as a
/// telescope does.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Operands<'grammar>
{
    /// The form's rule.
    rule: &'grammar str,
    /// Its operands, in order.
    nodes: Vec<NodeIndex>,
    /// Whether it owns a `,` or a `:`.
    listed: bool,
}

impl<'grammar> Operands<'grammar>
{
    /// The operands of the form at `at`; none when `at` is no form.
    ///
    /// # Specification
    /// trivial.
    fn of(
        grammar: &'grammar Pbg,
        tree: &SyntaxTree<'_>,
        at: NodeIndex,
    ) -> Option<Self>
    {
        let NodeLabel::Meld(mold) = tree.node(at)?.label()
        else {
            return None;
        };
        let rule = grammar.rule_of(mold).ok()?.name().0;
        let mut nodes = Vec::new();
        let mut listed = false;
        for child in tree.children(at) {
            match tree.node(child).map(Node::label) {
                Some(NodeLabel::Meld(_)) => nodes.push(child),
                Some(NodeLabel::Tile(tile)) => {
                    if grammar
                        .rule_of(tile)
                        .is_ok_and(|owner| owner.name().0 == rule)
                    {
                        listed |= matches!(tree.fragment(child).map(<&str>::from), Some("," | ":"));
                    }
                    else {
                        nodes.push(child);
                    }
                },
                Some(
                    NodeLabel::Wald
                    | NodeLabel::Grout { .. }
                    | NodeLabel::GhostClose { .. }
                    | NodeLabel::Space
                    | NodeLabel::Doc,
                )
                | None => {},
            }
        }
        Some(Self {
            rule,
            nodes,
            listed,
        })
    }
}

/// The bytes of each entry of the telescope at `at`: each run between the
/// parentheses and commas a parenthesised type owns, or `at` whole when it is
/// no parenthesised type.
///
/// # Specification
/// trivial.
fn telescope(
    grammar: &Pbg,
    tree: &SyntaxTree<'_>,
    at: NodeIndex,
) -> Vec<ByteSpan>
{
    let Some(node) = tree.node(at)
    else {
        return Vec::new();
    };
    let rule = match node.label() {
        NodeLabel::Meld(mold) => grammar.rule_of(mold).ok().map(|rule| rule.name().0),
        NodeLabel::Wald
        | NodeLabel::Tile(_)
        | NodeLabel::Grout { .. }
        | NodeLabel::GhostClose { .. }
        | NodeLabel::Space
        | NodeLabel::Doc => None,
    };
    if rule != Some(PARENTHESES) {
        return Vec::from([node.span()]);
    }
    let mut found = Vec::new();
    let mut entry: Option<ByteSpan> = None;
    for child in tree.children(at) {
        let Some(held) = tree.node(child)
        else {
            continue;
        };
        let delimits = match held.label() {
            NodeLabel::Tile(tile) => {
                grammar
                    .rule_of(tile)
                    .is_ok_and(|owner| Some(owner.name().0) == rule)
                    && matches!(
                        tree.fragment(child).map(<&str>::from),
                        Some("(" | "," | ")")
                    )
            },
            NodeLabel::Meld(_) => false,
            NodeLabel::Wald
            | NodeLabel::Grout { .. }
            | NodeLabel::GhostClose { .. }
            | NodeLabel::Space
            | NodeLabel::Doc => continue,
        };
        if delimits {
            found.extend(entry.take());
        }
        else {
            entry = Some(entry.map_or_else(|| held.span(), |first| first.join(held.span())));
        }
    }
    found
}

/// What a signature-help request at `position` of `text`, whose reading is
/// `reading` and whose copy keeps `hovering`, answers to a client that takes
/// a parameter as its place in the label when `offsets` holds.
///
/// # Specification
/// - requires: `reading` and `hovering` were read off `text`.
/// - ensures: for the innermost call whose arguments hold the position
///   ([`Calls::at`]), when the type table refers its head's first byte to a
///   declaration or constructor whose head the hovering keeps: that head as the
///   one signature, active, with its documentation as markdown, each parameter
///   as its start and end in the label counted in UTF-16 code units when
///   `offsets` holds or as its text otherwise, and the argument the position
///   writes as the active parameter, `null` past the last parameter; Nothing
///   otherwise.
/// - provides: the answer to `textDocument/signatureHelp`.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a function's call at each argument, a constructor applied
///   to no field yet, a nested call, a position past the last parameter, a call
///   of a sibling's declaration and a position in no call are each asserted at
///   their exact answer.
/// - witness: `server::tests::signature_help_answers_the_declared_head_of_the_call`
/// - witness: `tests::session::signature_help_reads_a_sibling_s_head`
#[spec(ensures: |ret| matches!(ret, Answer::Nothing | Answer::Signatures(_)))]
#[must_use]
pub fn help(
    text: SourceText<'_>,
    reading: &Reading,
    hovering: &Hovering,
    position: Position,
    offsets: LabelOffsets,
) -> Answer
{
    let index = LineIndex::new(<&str>::from(text).into());
    let at = ByteOffset::from(usize::from(position.byte(&index)));
    let Some((head, argument)) = reading.call_at(at)
    else {
        return Answer::Nothing;
    };
    let Maybe::Present((_, referent)) = hovering.table().referent(head.start())
    else {
        return Answer::Nothing;
    };
    let Some(signature) = hovering.signatures().declared(&referent)
    else {
        return Answer::Nothing;
    };
    let units = |bytes: usize| {
        u32::try_from(
            signature
                .label
                .get(.. bytes)
                .unwrap_or_default()
                .encode_utf16()
                .count(),
        )
        .unwrap_or(u32::MAX)
    };
    let parameters: Vec<ParameterInformation> = signature
        .parameters
        .iter()
        .map(|&Place { start, end }| ParameterInformation {
            label: if offsets.0 {
                ParameterLabel::Offsets([units(start), units(end)])
            }
            else {
                ParameterLabel::Text(String::from(
                    signature.label.get(start .. end).unwrap_or_default(),
                ))
            },
        })
        .collect();
    let active = (argument.0 < parameters.len())
        .then(|| u32::try_from(argument.0).ok())
        .flatten();
    Answer::Signatures(SignatureHelp {
        signatures: Vec::from([SignatureInformation {
            label: signature.label.clone(),
            documentation: signature
                .documentation
                .as_ref()
                .map(|documented| MarkupContent {
                    kind: "markdown",
                    value: documented.clone(),
                }),
            parameters,
        }]),
        active_signature: 0,
        active_parameter: active,
    })
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;
    use alloc::vec::Vec;

    use gandr_surface_lowering::Unit;
    use gandr_surface_parser::parse;
    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::SourceText;

    use super::Calls;
    use super::Signatures;
    use crate::recheck::grammar;
    use crate::recheck::roles;

    /// A family, a function matching on it, a call nesting a constructor and
    /// a family applied in a type.
    const CALLED: &str = "data Nat : Type {\n  Zero : Nat;\n  Succ : (n : Nat) --> Nat;\n}\ndef rec \
                          plus(n : Nat, m : Nat) -> -F Nat {\n  case m {\n    Zero => n,\n    \
                          Succ(p) => Succ(plus[<](n, p))\n  }\n}\ndef f : +U (-F Nat) ;\ndef f = \
                          thunk { plus(Succ(Zero), Zero) } ;\ndata List(a : Type) : Type {\n  \
                          Nil : List(a);\n}\n";

    #[test]
    fn the_innermost_call_answers_with_its_argument()
    {
        let grammar = grammar().expect("the grammar builds");
        let called = |text: &str, marker: &str| {
            let parsed = parse(grammar, SourceText::from(text)).expect("the text parses");
            let at = text.find(marker).expect("the marker occurs");
            Calls::of(grammar, parsed.tree())
                .at(ByteOffset::from(at))
                .map(|(head, argument)| {
                    let head = text
                        .get(usize::from(head.start()) .. usize::from(head.end()))
                        .unwrap_or_default();
                    (String::from(head), argument.0)
                })
        };
        let answer = |head: &str, argument: usize| Some((String::from(head), argument));
        assert_eq!(
            called(CALLED, "Zero), Zero)"),
            answer("Succ", 0),
            "a call nested in an argument answers itself"
        );
        assert_eq!(
            called(CALLED, ", Zero) }"),
            answer("plus", 0),
            "just before a comma, the argument it ends"
        );
        assert_eq!(
            called(CALLED, "Zero) }"),
            answer("plus", 1),
            "past a comma, the argument after it"
        );
        assert_eq!(
            called(CALLED, ") }"),
            answer("plus", 1),
            "just before the closing parenthesis, the call it closes"
        );
        assert_eq!(
            called(CALLED, " } ;\ndata List"),
            None,
            "past the closing parenthesis, no call"
        );
        assert_eq!(
            called(CALLED, "plus(Succ"),
            None,
            "on the head, not the call it heads"
        );
        assert_eq!(
            called(CALLED, "p))"),
            answer("plus[<]", 1),
            "a recursive call, headed by its claim"
        );
        assert_eq!(
            called(CALLED, "a);"),
            answer("List", 0),
            "a family's application in a type"
        );
        assert_eq!(
            called("def g = thunk { plus(Zero, \n} ;\n", "\n} ;"),
            answer("plus", 1),
            "a call the parser closed holds the rest of its form"
        );
    }

    #[test]
    fn each_head_reads_its_parameters()
    {
        let text = "/// Natural numbers.\ndata Nat : Type {\n  Zero : Nat;\n  /// One more.\n  Succ \
                    : (n : Nat) --> Nat;\n}\n/// Addition.\n@[ checks ]\ndef rec plus(n : Nat,\n    \
                    m : Nat) -> -F Nat { n }\ndef double : +U (Nat -> Nat -> -F Nat) ;\ndata \
                    List(a : Type) : Type {\n  Nil : List(a);\n  Cons : (head : a, tail : List(a)) \
                    --> List(a);\n}\ndef ap(f : +U (Nat -> -F Nat), x : Nat) -> -F Nat { f(x) \
                    }\ndef r : #{ sub : +U (Nat -> Nat -> -F Type), subTm : (g : Nat, t : sub(g, \
                    g)) => Nat } ;\n";
        let grammar = grammar().expect("the grammar builds");
        let roles = roles().expect("the roles build");
        let parsed = parse(grammar, SourceText::from(text)).expect("the text parses");
        let heads = Signatures::of(grammar, roles, parsed.tree(), &Unit::single());
        let read: Vec<(String, String, Vec<String>, Option<String>)> = heads
            .0
            .iter()
            .map(|&((_, named), ref signature)| {
                let name = text
                    .get(usize::from(named.start()) .. usize::from(named.end()))
                    .unwrap_or_default();
                let parameters = signature
                    .parameters
                    .iter()
                    .map(|&super::Place { start, end }| {
                        String::from(signature.label.get(start .. end).unwrap_or_default())
                    })
                    .collect();
                (
                    String::from(name),
                    signature.label.clone(),
                    parameters,
                    signature.documentation.clone(),
                )
            })
            .collect();
        let head = |name: &str, label: &str, parameters: &[&str], documentation: Option<&str>| {
            (
                String::from(name),
                String::from(label),
                parameters
                    .iter()
                    .map(|&parameter| String::from(parameter))
                    .collect::<Vec<_>>(),
                documentation.map(String::from),
            )
        };
        assert_eq!(read, [
            head("Nat", "Nat : Type", &[], Some("Natural numbers.")),
            head("Zero", "Zero : Nat", &[], None),
            head(
                "Succ",
                "Succ : (n : Nat) --> Nat",
                &["n : Nat"],
                Some("One more.")
            ),
            head(
                "plus",
                "plus(n : Nat, m : Nat) -> -F Nat",
                &["n : Nat", "m : Nat"],
                Some("Addition.")
            ),
            head(
                "double",
                "double : +U (Nat -> Nat -> -F Nat)",
                &["Nat", "Nat"],
                None
            ),
            head("List", "List(a : Type) : Type", &["a : Type"], None),
            head("Nil", "Nil : List(a)", &[], None),
            head(
                "Cons",
                "Cons : (head : a, tail : List(a)) --> List(a)",
                &["head : a", "tail : List(a)"],
                None
            ),
            head(
                "ap",
                "ap(f : +U (Nat -> -F Nat), x : Nat) -> -F Nat",
                &["f : +U (Nat -> -F Nat)", "x : Nat"],
                None
            ),
            head("f", "f : +U (Nat -> -F Nat)", &["Nat"], None),
            head(
                "r",
                "r : #{ sub : +U (Nat -> Nat -> -F Type), subTm : (g : Nat, t : sub(g, g)) => Nat }",
                &[],
                None
            ),
            head(
                "sub",
                "sub : +U (Nat -> Nat -> -F Type)",
                &["Nat", "Nat"],
                None
            ),
            head(
                "subTm",
                "subTm : (g : Nat, t : sub(g, g)) => Nat",
                &["g : Nat", "t : sub(g, g)"],
                None
            ),
        ]);
    }
}
