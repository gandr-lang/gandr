//! The document's outline, read off its parsed tree: its declarations as
//! symbols, the lines its forms and documentation span as folding ranges, and
//! the forms around a position as nested selection ranges.
//!
//! Each is read once per held text, off the tree of its one
//! [`Reading`](crate::reading::Reading), under the process's grammar, and reads
//! nothing the checker decides: a declaration is a form of the grammar's item
//! or module-member sort, and its name is the first tile the highlighter
//! classifies as a definition or a type.
//!
//! # The outline is read off the tree
//!
//! The three outline answers read the molded tree alone; nothing the checker
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
//!   `module`, `theory`, `codata`, and `data` or anything else. A symbol's
//!   range is its form's, widened over the attribute blocks standing directly
//!   before it, and its selection range is the name's tile. An attribute block
//!   is a form with no such tile, so it is no symbol.
//! - **Members.** A `theory` block, a `data` declaration and a `codata`
//!   declaration write their members among their own tiles, not as forms, so
//!   each `;`-ended run between the form's braces is read as a member nested
//!   under it: a theory's `sort`, `shape` and `ext` as `TypeParameter`, `oper`
//!   as `Method`, `obs` as `Field`, `rule` as `Property` and `data` as
//!   `Constructor`; a family's constructors as `Constructor`; a codata
//!   declaration's observations as `Field`. An `include` names a theory
//!   declared elsewhere and is no member.
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

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::RoleTable;
use gandr_surface_grammar::Sort;
use gandr_surface_render_remote::ByteOffset;
use gandr_surface_render_remote::HlRole;
use gandr_surface_render_remote::LineIndex;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::Node;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SourceFragment;
use gandr_surface_syntax::SyntaxTree;

use crate::position::Position;
use crate::position::Range;
use crate::protocol::DocumentSymbol;
use crate::protocol::FoldingRange;
use crate::protocol::SelectionRange;
use crate::protocol::SymbolKind;

/// The kind a folding range of documentation or a block comment carries.
const COMMENT: &str = "comment";

/// The rule of an attribute block standing before the declaration it
/// decorates.
const ATTRIBUTE_BLOCK: &str = "attribute_block";

/// The opening of a block comment.
const BLOCK_COMMENT: &str = "/*";

/// What declares a symbol: a form of its own, or a member written among the
/// tiles of the form holding it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Declarer
{
    /// The form at the node declares it.
    Form(NodeIndex),
    /// A member of the `theory` block, `data` declaration or `codata`
    /// declaration at the node declares it, written among that form's own
    /// tiles over the span.
    Member(NodeIndex, ByteSpan),
}

/// The declarations of `tree`, each beside what declares it and holding the
/// declarations written inside it.
///
/// # Specification
/// - requires: `tree` was parsed under `grammar`, and `index` built over its
///   text.
/// - ensures: one symbol per form of the [`Sort::Item`] or
///   [`Sort::ModuleMember`] sort that has a name: its first direct tile the
///   highlighter classifies as [`HlRole::FunctionDef`], [`HlRole::VariableDef`]
///   or [`HlRole::Type`], or as [`HlRole::Label`] after the keyword `world`.
///   The symbol's range is the form's, widened to the attribute blocks standing
///   directly before it, its selection range the name's, and its kind a
///   function, a value, or by the form's first keyword a world, a module, a
///   data declaration, a codata declaration or a signature. A signature, data
///   declaration or codata declaration holds one symbol per member written
///   between its own braces, as [`members`] reads them. Symbols are in source
///   order, each after the declaration holding it, which it names by position;
///   a top-level one names none. Each is beside the form that declares it, or
///   the form whose member it is.
/// - provides: the declarations the document symbols and a hover read.
/// - fails: never.
/// - panics: none.
/// - intension: one walk of the tree with an explicit stack, and one more of a
///   container's own children.
///
/// # Adequacy
/// - hypothesis: L3 — a function, a value, a data declaration with its
///   constructors, a codata declaration with its observations, a module with a
///   nested module, a theory with a member of every kind, documentation and
///   attribute blocks before a definition and a data declaration are asserted
///   at the exact symbol tree. Taking a declaration's range from its name or
///   its form alone, dropping a nested member, reversing source order or
///   reading an attribute name as the declared one changes it; a hover finds
///   each declaration's documentation under its own form.
/// - witness: `outline::tests::declarations_nest_as_symbols`
/// - witness: `outline::tests::a_theory_holds_its_members`
/// - witness: `hover::tests::a_declaration_hovers_its_type_and_documentation`
#[spec(ensures: |ret| ret.iter().enumerate().all(|(position, found)|
    !found.1.name.is_empty() && found.1.holder.is_none_or(|holder| holder < position)))]
pub fn declarations(
    grammar: &Pbg,
    roles: &RoleTable,
    tree: &SyntaxTree<'_>,
    index: &LineIndex<'_>,
) -> Vec<(Declarer, DocumentSymbol)>
{
    // A depth-first walk in source order meets each declaration after the
    // one holding it.
    let mut found: Vec<(Declarer, DocumentSymbol)> = Vec::new();
    let mut pending: Vec<(NodeIndex, Option<usize>, Option<ByteSpan>)> =
        Vec::from([(tree.root(), None, None)]);
    while let Some((at, holder, decorated)) = pending.pop() {
        let holder =
            declared(grammar, roles, tree, index, at, decorated).map_or(holder, |symbol| {
                let container = matches!(
                    symbol.kind,
                    SymbolKind::INTERFACE | SymbolKind::ENUM | SymbolKind::STRUCT
                );
                found.push((Declarer::Form(at), DocumentSymbol { holder, ..symbol }));
                let held = found.len().saturating_sub(1);
                if container {
                    members(roles, tree, index, at, &mut found);
                }
                Some(held)
            });
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
                NodeLabel::Meld(mold)
                    if grammar
                        .rule_of(mold)
                        .is_ok_and(|rule| rule.name().0 == ATTRIBUTE_BLOCK) =>
                {
                    let span = node.span();
                    blocks = Some(blocks.map_or(span, |first| first.join(span)));
                    pending.push((child, holder, None));
                },
                NodeLabel::Meld(_) | NodeLabel::Tile(_) => {
                    pending.push((child, holder, blocks.take()));
                },
                NodeLabel::Wald
                | NodeLabel::Grout { .. }
                | NodeLabel::GhostClose { .. }
                | NodeLabel::Space
                | NodeLabel::Doc => pending.push((child, holder, None)),
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
            Ok(HlRole::Keyword) if keyword.is_none() => keyword = tree.fragment(child),
            // A world's name is classified as a label, as its uses are.
            Ok(HlRole::Label) if keyword.map(<&str>::from) != Some("world") => {},
            Ok(
                role @ (HlRole::FunctionDef | HlRole::VariableDef | HlRole::Type | HlRole::Label),
            ) => {
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
            Ok(_) | Err(_) => {},
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
        (HlRole::FunctionDef, _) => SymbolKind::FUNCTION,
        (HlRole::VariableDef, _) => SymbolKind::VARIABLE,
        (_, Some("world")) => SymbolKind::CONSTANT,
        (_, Some("module")) => SymbolKind::MODULE,
        (_, Some("theory")) => SymbolKind::INTERFACE,
        (_, Some("codata")) => SymbolKind::STRUCT,
        (_, Some(_) | None) => SymbolKind::ENUM,
    }
}

/// One run of a form's own children between its outermost braces.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Run
{
    /// From its first child to the `;` ending it, or to its last child
    /// before the closing `}`.
    pub span: ByteSpan,
    /// Its own tiles at the braces' depth, in source order.
    tiles: Vec<NodeIndex>,
}

/// The runs of the form at `at`: its own children between the first `{`
/// among its own tiles and the `}` closing it, cut at each `;` the braces hold
/// directly.
///
/// # Specification
/// - requires: nothing; a form with no braces has no runs.
/// - ensures: one run per stretch of the form's own children, layout and
///   documentation aside, ended by a `;` at the braces' depth — which it
///   includes — or by the closing `}`, in source order; a brace a run writes
///   nests, so a `shape`'s faces stay in its run. An empty stretch is no run.
/// - provides: the members a theory, a family or a codata declaration writes,
///   for its symbols and its hover.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`declarations`], and a theory's hover lists its
///   members, an `include` among them.
/// - witness: `outline::tests::a_theory_holds_its_members`
/// - witness: `hover::tests::a_theory_and_a_module_hover_as_written_1122_1124`
#[spec(ensures: |ret| ret.windows(2).all(|pair| matches!(pair, [first, second] if first.span.end() <= second.span.start())))]
#[must_use]
pub fn runs(
    tree: &SyntaxTree<'_>,
    at: NodeIndex,
) -> Vec<Run>
{
    let mut runs = Vec::new();
    let mut depth = 0_usize;
    let mut written: Option<ByteSpan> = None;
    let mut tiles: Vec<NodeIndex> = Vec::new();
    for child in tree.children(at) {
        let Some(node) = tree.node(child)
        else {
            continue;
        };
        let tile = match node.label() {
            NodeLabel::Space | NodeLabel::Doc => continue,
            NodeLabel::Tile(_) => true,
            NodeLabel::Meld(_)
            | NodeLabel::Wald
            | NodeLabel::Grout { .. }
            | NodeLabel::GhostClose { .. } => false,
        };
        let text = tree.fragment(child).filter(|_| tile).map(<&str>::from);
        match (depth, text) {
            (0, Some("{")) => {
                depth = 1;
                continue;
            },
            (0, _) => continue,
            (1, Some(closer @ (";" | "}"))) => {
                let span = match closer {
                    ";" => written.map(|run| run.join(node.span())),
                    _ => written,
                };
                if let Some(span) = span {
                    runs.push(Run {
                        span,
                        tiles: core::mem::take(&mut tiles),
                    });
                }
                written = None;
                if closer == "}" {
                    break;
                }
                continue;
            },
            (_, Some("{")) => depth = depth.saturating_add(1),
            (_, Some("}")) => depth = depth.saturating_sub(1),
            _ => {},
        }
        let span = node.span();
        written = Some(written.map_or(span, |run| run.join(span)));
        if depth == 1 && tile {
            tiles.push(child);
        }
    }
    runs
}

/// Push onto `found` a symbol for each member the form at `at` writes among
/// its own tiles, held by the symbol last in `found`, the form's own.
///
/// # Specification
/// - requires: the form at `at` declares the symbol last in `found`.
/// - ensures: one symbol per run of [`runs`] that is named: its name is its
///   first own tile at the braces' depth that the highlighter classifies as a
///   definition, a type, a constructor or a member, and its keyword the first
///   keyword before that name. A run whose keyword is `include`, which names a
///   theory declared elsewhere, pushes none. A symbol's range is its run's, its
///   selection range the name's, its kind [`member_kind`]'s; it is held by the
///   form's symbol and beside [`Declarer::Member`] of `at`.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`declarations`].
/// - witness: `outline::tests::a_theory_holds_its_members`
/// - witness: `outline::tests::declarations_nest_as_symbols`
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        spec_clause_traversal,
        reason = "parity: the body pushes each member once; the check reads the pushed ones once more"
    )
)]
#[spec(
    captures: before = found.len(),
    ensures: |()| found.iter().skip(before).all(|pushed|
        pushed.1.holder == before.checked_sub(1) && matches!(pushed.0, Declarer::Member(form, _) if form == at)),
)]
fn members(
    roles: &RoleTable,
    tree: &SyntaxTree<'_>,
    index: &LineIndex<'_>,
    at: NodeIndex,
    found: &mut Vec<(Declarer, DocumentSymbol)>,
)
{
    let Some(holder) = found.len().checked_sub(1)
    else {
        return;
    };
    for run in runs(tree, at) {
        let mut keyword: Option<SourceFragment<'_>> = None;
        let mut name: Option<(NodeIndex, HlRole)> = None;
        for &child in &run.tiles {
            let Some(NodeLabel::Tile(tile)) = tree.node(child).map(Node::label)
            else {
                continue;
            };
            match roles.role_of(tile) {
                Ok(HlRole::Keyword) if keyword.is_none() => keyword = tree.fragment(child),
                Ok(
                    role @ (HlRole::FunctionDef
                    | HlRole::VariableDef
                    | HlRole::Type
                    | HlRole::Constructor
                    | HlRole::Member),
                ) => {
                    name = Some((child, role));
                    break;
                },
                Ok(_) | Err(_) => {},
            }
        }
        if let Some(symbol) = member(tree, index, run.span, keyword, name) {
            found.push((Declarer::Member(at, run.span), DocumentSymbol {
                holder: Some(holder),
                ..symbol
            }));
        }
    }
}

/// The symbol of a member written over `span` after its keyword `keyword`,
/// named by the tile at `name`, or none for an unnamed member or an
/// `include`.
///
/// # Specification
/// trivial.
fn member(
    tree: &SyntaxTree<'_>,
    index: &LineIndex<'_>,
    span: ByteSpan,
    keyword: Option<SourceFragment<'_>>,
    name: Option<(NodeIndex, HlRole)>,
) -> Option<DocumentSymbol>
{
    let (named, role) = name?;
    if keyword.map(<&str>::from) == Some("include") {
        return None;
    }
    Some(DocumentSymbol {
        name: String::from(<&str>::from(tree.fragment(named)?)),
        kind: member_kind(role, keyword),
        range: range_of(index, span)?,
        selection_range: range_of(index, tree.node(named)?.span())?,
        holder: None,
    })
}

/// What a member named by a tile of `role` declares, after its keyword
/// `keyword`: a law for `rule`, an observation for `obs` or a codata
/// declaration's member, a constructor for `data` or a family's constructor, a
/// type the theory is over for a sort, a shape or an extension, an operation
/// for any other definition.
///
/// # Specification
/// trivial.
fn member_kind(
    role: HlRole,
    keyword: Option<SourceFragment<'_>>,
) -> SymbolKind
{
    match (role, keyword.map(<&str>::from)) {
        (_, Some("rule")) => SymbolKind::PROPERTY,
        (_, Some("obs")) | (HlRole::Member, _) => SymbolKind::FIELD,
        (_, Some("data")) | (HlRole::Constructor, _) => SymbolKind::CONSTRUCTOR,
        (HlRole::Type, _) => SymbolKind::TYPE_PARAMETER,
        (HlRole::FunctionDef, _) => SymbolKind::METHOD,
        (_, Some(_) | None) => SymbolKind::VARIABLE,
    }
}

/// The runs of lines of `tree`'s text a client can fold, the members
/// `members` writes among their holders' tiles included.
///
/// # Specification
/// - requires: `index` was built over `tree`'s text, and each of `members` is
///   the span of a member of the form at its node.
/// - ensures: one range per line at which a form, a member, a documentation
///   node or a block comment starts that ends on a later line, from its first
///   line to its last; at a line where several start, the one reaching
///   furthest, the outermost of those nested there. Documentation and block
///   comments carry the `comment` kind, forms and members none. Ascending by
///   first line.
/// - provides: the answer to `textDocument/foldingRange`.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a multi-line function with a block inside it, a one-line
///   declaration, a documentation run, a block comment, and a theory with a
///   multi-line member and a one-line one are asserted at the exact ranges.
///   Folding a one-line form or member, keeping the inner of two ranges
///   starting on one line, dropping a member or losing the comment kind changes
///   them.
/// - witness: `outline::tests::multi_line_forms_and_documentation_fold`
#[spec(ensures: |ret| ret.iter().all(|fold| fold.start_line < fold.end_line)
    && ret.windows(2).all(|pair| matches!(pair, [first, second] if first.start_line < second.start_line)))]
pub fn folds(
    tree: &SyntaxTree<'_>,
    index: &LineIndex<'_>,
    members: &[(NodeIndex, ByteSpan)],
) -> Vec<FoldingRange>
{
    let mut folds: Vec<FoldingRange> = Vec::new();
    let mut fold = |span: ByteSpan, kind: Option<&'static str>| {
        if let Some(range) = range_of(index, span)
            && range.start.line < range.end.line
        {
            folds.push(FoldingRange {
                start_line: range.start.line,
                end_line: range.end.line,
                kind,
            });
        }
    };
    for position in tree.positions() {
        let Some(node) = tree.node(position)
        else {
            continue;
        };
        let kind = match node.label() {
            NodeLabel::Meld(_) => None,
            NodeLabel::Doc => Some(COMMENT),
            NodeLabel::Space
                if tree
                    .fragment(position)
                    .is_some_and(|text| <&str>::from(text).starts_with(BLOCK_COMMENT)) =>
            {
                Some(COMMENT)
            },
            NodeLabel::Wald
            | NodeLabel::Space
            | NodeLabel::Tile(_)
            | NodeLabel::Grout { .. }
            | NodeLabel::GhostClose { .. } => continue,
        };
        fold(node.span(), kind);
    }
    for &(_, span) in members {
        fold(span, None);
    }
    folds.sort_by_key(|fold| (fold.start_line, core::cmp::Reverse(fold.end_line)));
    folds.dedup_by_key(|fold| fold.start_line);
    folds
}

/// One node a selection can stop at: its span, and the positions of its
/// selectable children in source order.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Bone
{
    /// The node's span.
    span: ByteSpan,
    /// The positions in the skeleton of its children that are neither layout
    /// nor empty, in source order.
    children: Vec<usize>,
}

/// The nodes of a tree a selection walks, owned apart from the tree's text:
/// the root first, then every node that is neither layout nor empty.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
#[repr(transparent)]
pub struct Skeleton(Vec<Bone>);

impl Skeleton
{
    /// The skeleton of `tree`, each of `members` a bone between the form at
    /// its node and the children the member covers.
    ///
    /// # Specification
    /// - requires: each of `members` is the span of a member of the form at its
    ///   node, in source order.
    /// - ensures: a bone for the root, at position zero, and one for every node
    ///   below it that is neither layout nor empty, each beside the positions
    ///   of such children of its node, in source order; a member's bone stands
    ///   among its form's children where its first covered child would, and
    ///   holds every child of the form its span covers. Nothing for an empty
    ///   tree.
    /// - provides: what a selection walks once the tree is let go.
    /// - fails: never.
    /// - panics: none.
    /// - intension: one walk of the tree with an explicit stack, and one map of
    ///   `members` by form.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the selection witness walks a skeleton down to a
    ///   number inside a call, to a name, and to a theory member's name; a
    ///   skipped child, a layout bone, a reordered child or a member's bone
    ///   left out changes the chains it asserts.
    /// - witness: `outline::tests::a_selection_grows_from_the_innermost_form`
    #[spec(ensures: |ret| ret.0.iter().all(|bone| bone.children.iter().all(|&child| child < ret.0.len())))]
    #[must_use]
    pub fn of(
        tree: &SyntaxTree<'_>,
        members: &[(NodeIndex, ByteSpan)],
    ) -> Self
    {
        let Some(root) = tree.node(tree.root())
        else {
            return Self::default();
        };
        let mut bones = Vec::from([Bone {
            span: root.span(),
            children: Vec::new(),
        }]);
        // Each form's members, each with its bone once a covered child has
        // placed it.
        let mut held: BTreeMap<NodeIndex, Vec<(ByteSpan, Option<usize>)>> = BTreeMap::new();
        for &(form, span) in members {
            held.entry(form).or_default().push((span, None));
        }
        let mut pending: Vec<(NodeIndex, usize)> = Vec::from([(tree.root(), 0_usize)]);
        while let Some((at, holder)) = pending.pop() {
            let mut runs = held.remove(&at).unwrap_or_default();
            for child in tree.children(at) {
                let Some(node) = tree
                    .node(child)
                    .filter(|node| !matches!(node.label(), NodeLabel::Space))
                    .filter(|node| node.span().start() < node.span().end())
                else {
                    continue;
                };
                let span = node.span();
                let parent = match runs
                    .iter_mut()
                    .find(|run| run.0.start() <= span.start() && span.end() <= run.0.end())
                {
                    Some(&mut (_, Some(bone))) => bone,
                    Some(run) => {
                        let bone = bones.len();
                        bones.push(Bone {
                            span: run.0,
                            children: Vec::new(),
                        });
                        if let Some(form) = bones.get_mut(holder) {
                            form.children.push(bone);
                        }
                        run.1 = Some(bone);
                        bone
                    },
                    None => holder,
                };
                let position = bones.len();
                bones.push(Bone {
                    span,
                    children: Vec::new(),
                });
                if let Some(bone) = bones.get_mut(parent) {
                    bone.children.push(position);
                }
                pending.push((child, position));
            }
        }
        Self(bones)
    }

    /// The chain of nodes around `position`, innermost first, ranged through
    /// `index`.
    ///
    /// # Specification
    /// - requires: `index` was built over the text the skeleton's tree read.
    /// - ensures: the chain of nodes whose span holds the position — a child
    ///   preferred when the position falls inside it, else one that ends at the
    ///   position — from the innermost out to the whole document, a span its
    ///   child repeats given once; nothing when no node's range projects.
    /// - provides: one position's `textDocument/selectionRange` answer.
    /// - fails: never.
    /// - panics: none.
    /// - intension: one walk down from the root, never back up.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a position inside a name, at a name's end and inside
    ///   an operand are asserted at their exact chains. Preferring the node
    ///   ending at the position over the one holding it, repeating a span, or
    ///   stopping short of the document changes them.
    /// - witness: `outline::tests::a_selection_grows_from_the_innermost_form`
    #[spec(ensures: |ret| ret.as_ref().is_none_or(|selection| !selection.ranges.is_empty()))]
    #[must_use]
    pub fn around(
        &self,
        index: &LineIndex<'_>,
        position: Position,
    ) -> Option<SelectionRange>
    {
        let at = gandr_surface_syntax::ByteOffset::from(usize::from(position.byte(index)));
        let mut chain: Vec<ByteSpan> = Vec::new();
        let mut current = self.0.first();
        while let Some(bone) = current {
            if chain.last() != Some(&bone.span) {
                chain.push(bone.span);
            }
            let children = || bone.children.iter().filter_map(|&child| self.0.get(child));
            current = children()
                .find(|child| child.span.start() <= at && at < child.span.end())
                .or_else(|| children().find(|child| child.span.end() == at));
        }
        let ranges: Vec<Range> = chain
            .into_iter()
            .rev()
            .filter_map(|span| range_of(index, span))
            .collect();
        (!ranges.is_empty()).then_some(SelectionRange { ranges })
    }
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
    use gandr_surface_render_remote::LineIndex;
    use gandr_surface_syntax::SourceText;
    use serde_json::Value;

    use crate::position::Character;
    use crate::position::Line;
    use crate::position::Position;
    use crate::position::Range;
    use crate::protocol::DocumentSymbols;
    use crate::protocol::SelectionRange;
    use crate::reading::Reading;

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
                      module Outer {\n  def inner = 1 ;\n  module Nested {\n    def deep = 2 ;\n  }\n}\n\
                      world seat ;\n";
        let answered = Reading::of(SourceText::from(source)).symbols();
        assert_eq!(outline(&answered), [
            "twice 12 1:0-4:1 at 2:4-2:9",
            "answer 12 5:0-5:17 at 5:4-5:10",
            "Color 10 6:0-7:34 at 7:5-7:10",
            "  Red 9 7:20-7:32 at 7:20-7:23",
            "Outer 2 8:0-13:1 at 8:7-8:12",
            "  inner 12 9:2-9:17 at 9:6-9:11",
            "  Nested 2 10:2-12:3 at 10:9-10:15",
            "    deep 12 11:4-11:18 at 11:8-11:12",
            "seat 14 14:0-14:12 at 14:6-14:10",
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
        assert_eq!(names(&wire), ["twice", "answer", "Color", "Outer", "seat"]);
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

    /// A theory's members nest under it, one of each kind with its own kind;
    /// a face list's braces and `;` stay inside its shape; an `include` is no
    /// member; and a codata declaration's observations nest under it.
    #[test]
    fn a_theory_holds_its_members()
    {
        let source = "theory Shapes {\n  sort M : Type;\n  data Unit : M;\n  oper mul : (x : M, y \
                      : M) --> M;\n  obs size : (m : M) --> M;\n  rule assoc : mul(mul(x, y), z) \
                      ==> mul(x, mul(y, z));\n  shape Square : 4 {\n    left = {0, 2};\n  };\n  \
                      ext Cell = M on left is zero;\n}\ntheory Monoid {\n  include Shapes;\n  oper \
                      one : () --> M;\n}\ncodata Stream : Type {\n  head : M;\n  tail : \
                      Stream;\n}\n";
        assert_eq!(outline(&Reading::of(SourceText::from(source)).symbols()), [
            "Shapes 11 0:0-10:1 at 0:7-0:13",
            "  M 26 1:2-1:16 at 1:7-1:8",
            "  Unit 9 2:2-2:16 at 2:7-2:11",
            "  mul 6 3:2-3:34 at 3:7-3:10",
            "  size 8 4:2-4:27 at 4:6-4:10",
            "  assoc 7 5:2-5:55 at 5:7-5:12",
            "  Square 26 6:2-8:4 at 6:8-6:14",
            "  Cell 26 9:2-9:31 at 9:6-9:10",
            "Monoid 11 11:0-14:1 at 11:7-11:13",
            "  one 6 13:2-13:22 at 13:7-13:10",
            "Stream 23 15:0-18:1 at 15:7-15:13",
            "  head 8 16:2-16:11 at 16:2-16:6",
            "  tail 8 17:2-17:16 at 17:2-17:6",
        ]);
    }

    #[test]
    fn multi_line_forms_and_documentation_fold()
    {
        let source = "/// One.\n/// Two.\ndef f(x: Integer) -> -F Integer {\n  return x\n}\n\
                      def g = 1 ;\n/* a\n   block */\ndef h = 2 ;\n\
                      theory T {\n  sort M : Type;\n  shape Square : 4 {\n    left = {0, 2};\n  \
                      };\n}\n";
        let answered: Vec<(u64, u64, Option<&str>)> = Reading::of(SourceText::from(source))
            .folds()
            .iter()
            .map(|fold| {
                let value = serde_json::to_value(fold).expect("a fold encodes");
                let line = |field| value.get(field).and_then(Value::as_u64).unwrap_or(u64::MAX);
                (line("startLine"), line("endLine"), fold.kind)
            })
            .collect();
        assert_eq!(
            answered,
            [
                (0, 1, Some("comment")),
                (2, 4, None),
                (6, 7, Some("comment")),
                (9, 14, None),
                (11, 13, None)
            ],
            "documentation, the function, the block comment, the theory and its multi-line \
             member fold; the one-line forms and members do not"
        );
    }

    #[test]
    fn a_selection_grows_from_the_innermost_form()
    {
        let source = SourceText::from("def f = g(10) ;\n");
        let answered = Reading::of(source).selections(&LineIndex::new(source.as_ref().into()), &[
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
        let between =
            Reading::of(source).selections(&LineIndex::new(source.as_ref().into()), &[at(
                Line::from(0),
                Character::from(9),
            )]);
        assert_eq!(
            between
                .iter()
                .map(chain)
                .next()
                .and_then(|chain| chain.first().cloned()),
            Some("0:9-0:10".to_owned()),
            "where one token ends and the next starts, the one starting is selected"
        );
        let theory =
            SourceText::from("theory T {\n  sort M : Type;\n  oper mul : (x : M) --> M;\n}\n");
        let member =
            Reading::of(theory).selections(&LineIndex::new(theory.as_ref().into()), &[at(
                Line::from(2),
                Character::from(8),
            )]);
        assert_eq!(
            member.iter().map(chain).next(),
            Some(vec![
                "2:7-2:10".to_owned(),
                "2:2-2:27".to_owned(),
                "0:0-3:1".to_owned(),
                "0:0-4:0".to_owned()
            ]),
            "a theory member's name grows to its member before the theory"
        );
    }
}
