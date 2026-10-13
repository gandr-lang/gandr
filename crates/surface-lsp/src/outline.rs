//! The document's outline, read off its parsed tree: its declarations as
//! symbols, the lines its forms and documentation span as folding ranges, and
//! the forms around a position as nested selection ranges.
//!
//! Each answer parses the document again under the process's grammar, as a
//! token request does, and reads nothing the checker decides: a declaration
//! is a form of the grammar's item or module-member sort, and its name is
//! the first tile the highlighter classifies as a definition or a type.
//!
//! # The outline is read off the tree
//!
//! The three outline requests parse the held text under the process's grammar,
//! as a token request does, and read the molded tree alone; nothing the checker
//! decides reaches them, so an outline is answered for a document that does not
//! check.
//!
//! - **Symbols.** A declaration is a form of the grammar's item or
//!   module-member sort, and its name is its first tile the highlighter
//!   classifies as a defined function, a defined value or a type. A declaration
//!   written inside another is among its children, so a module's members nest
//!   under it, a nested module's under that. A defined function is a `Function`
//!   symbol and a defined value a `Variable`; a declaration named by a type is
//!   a `Module`, an `Interface`, a `Struct` or an `Enum` by its keyword:
//!   `module`, `sign`, `codata`, and `data` or anything else. A symbol's range
//!   is its form's, widened over the attribute blocks standing directly before
//!   it, and its selection range is the name's tile. An attribute block is a
//!   form with no such tile, so it is no symbol.
//! - **Folding.** Every form, documentation node and block comment that ends on
//!   a later line than it starts folds from its first line to its last. Forms
//!   often share a first line, a function and its block say, and the client
//!   folds one range per line, so the outermost is answered. Documentation and
//!   block comments carry the `comment` kind, which a client's
//!   fold-all-comments reads.
//! - **Selection.** For each position the server walks down from the root, into
//!   the child holding the position, or, when none holds it, the child ending
//!   there, so a cursor just past a name selects the name. Layout is skipped,
//!   and a span its child repeats is given once. A document that does not parse
//!   answers the empty range at each position.
//!
//! The alternatives were the lowered module, whose declarations carry names and
//! spans but only for a document that lowers, and the highlighter's spans,
//! which classify a name but say nothing of what encloses it. The choice
//! reverses when a declaration's symbol must say what only lowering knows, its
//! type in the symbol's detail say: the symbol then reads the session's lowered
//! module, the tree still giving its ranges.

use alloc::string::String;
use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::RoleTable;
use gandr_surface_grammar::Sort;
use gandr_surface_parser::parse;
use gandr_surface_render_remote::ByteOffset;
use gandr_surface_render_remote::HlRole;
use gandr_surface_render_remote::LineIndex;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::Node;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SourceText;
use gandr_surface_syntax::SyntaxTree;

use crate::position::Position;
use crate::position::Range;
use crate::protocol::DocumentSymbol;
use crate::protocol::DocumentSymbols;
use crate::protocol::FoldingRange;
use crate::protocol::SelectionRange;
use crate::protocol::SymbolKind;
use crate::recheck::grammar;
use crate::recheck::roles;

/// The kind a folding range of documentation or a block comment carries.
const COMMENT: &str = "comment";

/// The rule of an attribute block standing before the declaration it
/// decorates.
const ATTRIBUTE_BLOCK: &str = "attribute_block";

/// The opening of a block comment.
const BLOCK_COMMENT: &str = "/*";

/// The declarations of `text`, each holding the declarations written inside
/// it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one symbol per form of the [`Sort::Item`] or
///   [`Sort::ModuleMember`] sort that has a name: its first direct tile the
///   highlighter classifies as [`HlRole::FunctionDef`], [`HlRole::VariableDef`]
///   or [`HlRole::Type`]. The symbol's range is the form's, widened to the
///   attribute blocks standing directly before it, its selection range the
///   name's, and its kind a function, a value, or by the form's first keyword a
///   module, a data declaration, a codata declaration or a signature. Symbols
///   are in source order, each after the declaration holding it, which it names
///   by position; a top-level one names none. Empty when the grammar does not
///   build or the text does not parse.
/// - provides: the answer to `textDocument/documentSymbol`.
/// - fails: never.
/// - panics: none.
/// - intension: one parse and one walk of the tree with an explicit stack.
///
/// # Adequacy
/// - hypothesis: L3 — a function, a value, a data declaration, a module with a
///   nested module, documentation and attribute blocks before a definition and
///   a data declaration are asserted at the exact symbol tree. Taking a
///   declaration's range from its name or its form alone, dropping a nested
///   member, reversing source order or reading an attribute name as the
///   declared one changes it.
/// - witness: `outline::tests::declarations_nest_as_symbols`
#[spec(ensures: |ret| ret.0.iter().enumerate().all(|(position, symbol)|
    !symbol.name.is_empty() && symbol.holder.is_none_or(|holder| holder < position)))]
pub fn symbols(text: SourceText<'_>) -> DocumentSymbols
{
    let (Ok(grammar), Ok(roles)) = (grammar(), roles())
    else {
        return DocumentSymbols::default();
    };
    let Ok(parsed) = parse(grammar, text)
    else {
        return DocumentSymbols::default();
    };
    let tree = parsed.into_tree();
    let index = LineIndex::new(<&str>::from(text).into());
    DocumentSymbols(
        declarations(grammar, roles, &tree, &index)
            .into_iter()
            .map(|(_, symbol)| symbol)
            .collect(),
    )
}

/// The declarations of `tree`, each beside the form declaring it.
///
/// # Specification
/// - requires: `tree` was parsed under `grammar`, and `index` built over its
///   text.
/// - ensures: the symbols [`symbols`] answers, in its order, each beside the
///   node of the form that declares it.
/// - provides: the declarations both the outline and a hover read.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`symbols`], and a hover finds each declaration's
///   documentation under its own form.
/// - witness: `outline::tests::declarations_nest_as_symbols`
/// - witness: `hover::tests::a_declaration_hovers_its_type_and_documentation`
#[spec(ensures: |ret| ret.iter().enumerate().all(|(position, found)|
    found.1.holder.is_none_or(|holder| holder < position)))]
pub fn declarations(
    grammar: &Pbg,
    roles: &RoleTable,
    tree: &SyntaxTree<'_>,
    index: &LineIndex<'_>,
) -> Vec<(NodeIndex, DocumentSymbol)>
{
    // A depth-first walk in source order meets each declaration after the
    // one holding it.
    let mut found: Vec<(NodeIndex, DocumentSymbol)> = Vec::new();
    let mut pending: Vec<(NodeIndex, Option<usize>, Option<ByteSpan>)> =
        Vec::from([(tree.root(), None, None)]);
    while let Some((at, holder, decorated)) = pending.pop() {
        let holder = match declared(grammar, roles, tree, index, at, decorated) {
            | Some(symbol) => {
                found.push((at, DocumentSymbol { holder, ..symbol }));
                Some(found.len().saturating_sub(1))
            },
            | None => holder,
        };
        let first = pending.len();
        // The attribute blocks standing before a form decorate it, layout
        // between them included.
        let mut blocks: Option<ByteSpan> = None;
        for child in tree.children(at) {
            let Some(node) = tree.node(child)
            else {
                continue;
            };
            match node.label() {
                | NodeLabel::Meld(mold)
                    if grammar
                        .rule_of(mold)
                        .is_ok_and(|rule| rule.name().0 == ATTRIBUTE_BLOCK) =>
                {
                    let span = node.span();
                    blocks = Some(blocks.map_or(span, |first| first.join(span)));
                    pending.push((child, holder, None));
                },
                | NodeLabel::Meld(_) | NodeLabel::Tile(_) => {
                    pending.push((child, holder, blocks.take()));
                },
                | _ => pending.push((child, holder, None)),
            }
        }
        if let Some(added) = pending.get_mut(first ..) {
            added.reverse();
        }
    }
    found
}

/// The symbol the form at `at` declares, when it is a named declaration,
/// its range widened over the attribute blocks `decorated` before it.
///
/// # Specification
/// trivial.
fn declared(
    grammar: &Pbg,
    roles: &RoleTable,
    tree: &SyntaxTree<'_>,
    index: &LineIndex<'_>,
    at: NodeIndex,
    decorated: Option<ByteSpan>,
) -> Option<DocumentSymbol>
{
    let node = tree.node(at)?;
    let NodeLabel::Meld(mold) = node.label()
    else {
        return None;
    };
    if !matches!(
        grammar.mold(mold).ok()?.sort,
        Sort::Item | Sort::ModuleMember
    ) {
        return None;
    }
    let mut keyword = None;
    for child in tree.children(at) {
        let Some(NodeLabel::Tile(tile)) = tree.node(child).map(Node::label)
        else {
            continue;
        };
        match roles.role_of(tile) {
            | Ok(HlRole::Keyword) if keyword.is_none() => keyword = tree.fragment(child),
            | Ok(role @ (HlRole::FunctionDef | HlRole::VariableDef | HlRole::Type)) => {
                let name = tree.fragment(child)?;
                return Some(DocumentSymbol {
                    name: String::from(<&str>::from(name)),
                    kind: kind_of(role, keyword),
                    range: range_of(
                        index,
                        decorated.map_or_else(|| node.span(), |blocks| blocks.join(node.span())),
                    )?,
                    selection_range: range_of(index, tree.node(child)?.span())?,
                    holder: None,
                });
            },
            | Ok(_) | Err(_) => {},
        }
    }
    None
}

/// What a declaration named by a tile of `role` declares, after its first
/// keyword `keyword`.
///
/// # Specification
/// trivial.
fn kind_of(
    role: HlRole,
    keyword: Option<SourceFragment<'_>>,
) -> SymbolKind
{
    match (role, keyword.map(<&str>::from)) {
        | (HlRole::FunctionDef, _) => SymbolKind::FUNCTION,
        | (HlRole::VariableDef, _) => SymbolKind::VARIABLE,
        | (_, Some("module")) => SymbolKind::MODULE,
        | (_, Some("sign")) => SymbolKind::INTERFACE,
        | (_, Some("codata")) => SymbolKind::STRUCT,
        | (_, Some(_) | None) => SymbolKind::ENUM,
    }
}

/// The runs of lines of `text` a client can fold.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one range per line at which a form, a documentation node or a
///   block comment starts that ends on a later line, from its first line to its
///   last; at a line where several start, the outermost. Documentation and
///   block comments carry the `comment` kind, forms none. Ascending by first
///   line. Empty when the grammar does not build or the text does not parse.
/// - provides: the answer to `textDocument/foldingRange`.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a multi-line function with a block inside it, a one-line
///   declaration, a documentation run and a block comment are asserted at the
///   exact ranges. Folding a one-line form, keeping the inner of two forms
///   starting on one line or losing the comment kind changes them.
/// - witness: `outline::tests::multi_line_forms_and_documentation_fold`
#[spec(ensures: |ret| ret.iter().all(|fold| fold.start_line < fold.end_line)
    && ret.windows(2).all(|pair| matches!(pair, [first, second] if first.start_line < second.start_line)))]
pub fn folds(text: SourceText<'_>) -> Vec<FoldingRange>
{
    let Ok(grammar) = grammar()
    else {
        return Vec::new();
    };
    let Ok(parsed) = parse(grammar, text)
    else {
        return Vec::new();
    };
    let tree = parsed.into_tree();
    let index = LineIndex::new(<&str>::from(text).into());
    let mut folds: Vec<FoldingRange> = Vec::new();
    // Level order visits a form before every form inside it.
    for position in tree.positions() {
        let Some(node) = tree.node(position)
        else {
            continue;
        };
        let kind = match node.label() {
            | NodeLabel::Meld(_) => None,
            | NodeLabel::Doc => Some(COMMENT),
            | NodeLabel::Space
                if tree
                    .fragment(position)
                    .is_some_and(|text| <&str>::from(text).starts_with(BLOCK_COMMENT)) =>
            {
                Some(COMMENT)
            },
            | NodeLabel::Wald
            | NodeLabel::Space
            | NodeLabel::Tile(_)
            | NodeLabel::Grout { .. }
            | NodeLabel::GhostClose { .. } => continue,
        };
        let Some(range) = range_of(&index, node.span())
        else {
            continue;
        };
        if range.start.line < range.end.line {
            folds.push(FoldingRange {
                start_line: range.start.line,
                end_line: range.end.line,
                kind,
            });
        }
    }
    folds.sort_by_key(|fold| fold.start_line);
    folds.dedup_by_key(|fold| fold.start_line);
    folds
}

/// For each of `positions`, the nodes of `text` around it, innermost first.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one answer per position, in order. Each is the chain of nodes
///   whose span holds the position — a child preferred when the position falls
///   inside it, else one that ends at the position — from the innermost out to
///   the whole document, whitespace and layout skipped, a span its child
///   repeats given once. A position in a document that does not parse answers
///   the empty range at itself.
/// - provides: the answer to `textDocument/selectionRange`.
/// - fails: never.
/// - panics: none.
/// - intension: one parse; each position walks down from the root, never back
///   up.
///
/// # Adequacy
/// - hypothesis: L3 — a position inside a name, at a name's end and inside an
///   operand are asserted at their exact chains. Preferring the node ending at
///   the position over the one holding it, repeating a span, or stopping short
///   of the document changes them.
/// - witness: `outline::tests::a_selection_grows_from_the_innermost_form`
#[spec(ensures: |ret| ret.len() == positions.len())]
pub fn selections(
    text: SourceText<'_>,
    positions: &[Position],
) -> Vec<SelectionRange>
{
    let index = LineIndex::new(<&str>::from(text).into());
    let unparsed = |position: Position| SelectionRange {
        ranges: Vec::from([Range {
            start: position,
            end: position,
        }]),
    };
    let tree = grammar()
        .ok()
        .and_then(|grammar| parse(grammar, text).ok())
        .map(gandr_surface_parser::ParseResult::into_tree);
    positions
        .iter()
        .map(|&position| match tree {
            | Some(ref tree) => {
                enclosing(tree, &index, position).unwrap_or_else(|| unparsed(position))
            },
            | None => unparsed(position),
        })
        .collect()
}

/// The chain of nodes of `tree` around `position`, innermost first.
///
/// # Specification
/// trivial.
fn enclosing(
    tree: &SyntaxTree<'_>,
    index: &LineIndex<'_>,
    position: Position,
) -> Option<SelectionRange>
{
    let at = gandr_surface_syntax::ByteOffset::from(usize::from(position.byte(index)));
    let mut chain: Vec<ByteSpan> = Vec::new();
    let mut current = Some(tree.root());
    while let Some(here) = current {
        let span = tree.node(here)?.span();
        if chain.last() != Some(&span) {
            chain.push(span);
        }
        let selectable = |child: &NodeIndex| {
            tree.node(*child).filter(|node| {
                !matches!(node.label(), NodeLabel::Space) && node.span().start() < node.span().end()
            })
        };
        let children: Vec<NodeIndex> = tree.children(here).collect();
        current = children
            .iter()
            .find(|child| {
                selectable(child)
                    .is_some_and(|node| node.span().start() <= at && at < node.span().end())
            })
            .or_else(|| {
                children
                    .iter()
                    .find(|child| selectable(child).is_some_and(|node| node.span().end() == at))
            })
            .copied();
    }
    let ranges: Vec<Range> = chain
        .into_iter()
        .rev()
        .filter_map(|span| range_of(index, span))
        .collect();
    (!ranges.is_empty()).then_some(SelectionRange { ranges })
}

/// The range `span` covers in the text `index` was built from.
///
/// # Specification
/// trivial.
fn range_of(
    index: &LineIndex<'_>,
    span: ByteSpan,
) -> Option<Range>
{
    Range::of_bytes(
        index,
        ByteOffset::from(usize::from(span.start())),
        ByteOffset::from(usize::from(span.end())),
    )
    .ok()
}

#[cfg(test)]
mod tests
{
    use gandr_surface_syntax::SourceText;
    use serde_json::Value;

    use super::folds;
    use super::selections;
    use super::symbols;
    use crate::position::Character;
    use crate::position::Line;
    use crate::position::Position;
    use crate::position::Range;
    use crate::protocol::DocumentSymbols;
    use crate::protocol::SelectionRange;

    /// `range` spelled `line:character-line:character`.
    ///
    /// # Specification
    /// trivial.
    fn spelled(range: Range) -> String
    {
        let at = |position: Position| {
            let value = serde_json::to_value(position).expect("a position encodes");
            let read = |field| value.get(field).and_then(Value::as_u64).unwrap_or(u64::MAX);
            format!("{}:{}", read("line"), read("character"))
        };
        format!("{}-{}", at(range.start), at(range.end))
    }

    /// The position at `line` and `character`.
    ///
    /// # Specification
    /// trivial.
    fn at(
        line: Line,
        character: Character,
    ) -> Position
    {
        Position { line, character }
    }

    /// Every symbol of `symbols` in order, one line each: its depth, name,
    /// kind, range and selection range.
    ///
    /// # Specification
    /// trivial.
    fn outline(symbols: &DocumentSymbols) -> Vec<String>
    {
        let mut depths: Vec<usize> = Vec::new();
        let mut lines = Vec::new();
        for symbol in &symbols.0 {
            let depth = symbol
                .holder
                .and_then(|holder| depths.get(holder))
                .map_or(0_usize, |depth| depth.saturating_add(1));
            depths.push(depth);
            let kind = serde_json::to_value(symbol.kind).expect("a kind encodes");
            lines.push(format!(
                "{}{} {kind} {} at {}",
                "  ".repeat(depth),
                symbol.name,
                spelled(symbol.range),
                spelled(symbol.selection_range),
            ));
        }
        lines
    }

    /// The ranges of `selection`, innermost first.
    ///
    /// # Specification
    /// trivial.
    fn chain(selection: &SelectionRange) -> Vec<String>
    {
        selection.ranges.iter().copied().map(spelled).collect()
    }

    #[test]
    fn declarations_nest_as_symbols()
    {
        let source = "/// Doubles nothing.\n@[ checks ]\ndef twice(x: Integer) -> -F Integer {\n  return x\n}\n\
                      def answer = 42 ;\n\
                      @[ checks ]\ndata Color : Type { Red : Color; }\n\
                      module Outer {\n  def inner = 1 ;\n  module Nested {\n    def deep = 2 ;\n  }\n}\n";
        let answered = symbols(SourceText::from(source));
        assert_eq!(outline(&answered), [
            "twice 12 1:0-4:1 at 2:4-2:9",
            "answer 12 5:0-5:17 at 5:4-5:10",
            "Color 10 6:0-7:34 at 7:5-7:10",
            "Outer 2 8:0-13:1 at 8:7-8:12",
            "  inner 12 9:2-9:17 at 9:6-9:11",
            "  Nested 2 10:2-12:3 at 10:9-10:15",
            "    deep 12 11:4-11:18 at 11:8-11:12",
        ]);
        // The wire tree: each held symbol under its holder's `children`.
        let wire = serde_json::to_value(&answered).expect("the symbols encode");
        let names = |value: &Value| -> Vec<String> {
            value
                .as_array()
                .map(|symbols| {
                    symbols
                        .iter()
                        .filter_map(|symbol| symbol.get("name").and_then(Value::as_str))
                        .map(str::to_owned)
                        .collect()
                })
                .unwrap_or_default()
        };
        let outer = wire.get(3_usize);
        let nested = outer
            .and_then(|outer| outer.get("children"))
            .and_then(|children| children.get(1_usize));
        assert_eq!(names(&wire), ["twice", "answer", "Color", "Outer"]);
        assert_eq!(
            outer.and_then(|outer| outer.get("children")).map(names),
            Some(vec!["inner".to_owned(), "Nested".to_owned()])
        );
        assert_eq!(
            nested.and_then(|nested| nested.get("children")).map(names),
            Some(vec!["deep".to_owned()])
        );
        assert!(
            wire.get(0_usize)
                .is_some_and(|twice| twice.get("children").is_none()),
            "a symbol holding none writes no children"
        );
    }

    #[test]
    fn multi_line_forms_and_documentation_fold()
    {
        let source = "/// One.\n/// Two.\ndef f(x: Integer) -> -F Integer {\n  return x\n}\n\
                      def g = 1 ;\n/* a\n   block */\ndef h = 2 ;\n";
        let answered: Vec<(u64, u64, Option<&str>)> = folds(SourceText::from(source))
            .into_iter()
            .map(|fold| {
                let value = serde_json::to_value(&fold).expect("a fold encodes");
                let line = |field| value.get(field).and_then(Value::as_u64).unwrap_or(u64::MAX);
                (line("startLine"), line("endLine"), fold.kind)
            })
            .collect();
        assert_eq!(
            answered,
            [
                (0, 1, Some("comment")),
                (2, 4, None),
                (6, 7, Some("comment"))
            ],
            "documentation, the function and the block comment fold; the one-line forms do not"
        );
    }

    #[test]
    fn a_selection_grows_from_the_innermost_form()
    {
        let source = SourceText::from("def f = g(10) ;\n");
        let answered = selections(source, &[
            at(Line::from(0), Character::from(11)),
            at(Line::from(0), Character::from(5)),
        ]);
        let chains: Vec<Vec<String>> = answered.iter().map(chain).collect();
        assert_eq!(
            chains.first().map(|first| first.first().cloned()),
            Some(Some("0:10-0:12".to_owned())),
            "inside the argument, the number is selected first: {chains:?}"
        );
        assert_eq!(
            chains.get(1).map(|second| second.first().cloned()),
            Some(Some("0:4-0:5".to_owned())),
            "at the end of a name, the name is selected first: {chains:?}"
        );
        for ranges in &chains {
            assert_eq!(
                ranges.last().map(String::as_str),
                Some("0:0-1:0"),
                "every chain ends at the whole document: {chains:?}"
            );
            assert!(
                ranges.windows(2).all(|pair| pair.first() != pair.get(1)),
                "no range is given twice: {chains:?}"
            );
        }
    }
}
