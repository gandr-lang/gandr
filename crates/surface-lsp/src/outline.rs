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
//!   before it — a block of `doc` entries alone too, which the parser files
//!   under the form as its documentation — and its selection range is the
//!   name's tile; it is tagged `Deprecated` when one of those blocks, or one an
//!   attributed module member writes before its keyword, names the `deprecated`
//!   attribute. An attribute block is a form with no such tile, so it is no
//!   symbol.
//! - **Root forms that declare nothing.** A form written at the root that names
//!   nothing and writes no declaration — a stray the lowering refuses — is an
//!   `Event` symbol, named by what it writes up to its first own `{` (then `{ …
//!   }`), or all of it without a final `;`, its layout collapsed. Its range is
//!   its form's, widened over the attribute blocks before it and the lone `;`
//!   after it, which the lowering files with it; its selection range is the
//!   form's own. A run of attribute blocks that no form follows is one such
//!   symbol. An import, which a hover answers as the import, is none. The
//!   engine keys each stray's slot by the form, so a hover reads its refusal as
//!   a declaration's.
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
use gandr_surface_lowering::Visibility;
use gandr_surface_render_remote::ByteOffset;
use gandr_surface_render_remote::HlRole;
use gandr_surface_render_remote::LineIndex;
use gandr_surface_syntax::ByteOffset as SyntaxOffset;
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

/// The rule of an import, which a hover answers as the import and which is
/// no symbol.
const IMPORT: &str = "import_declaration";

/// The rule of a `pub` mark, one tile before the declaration it exports: it
/// widens that declaration's symbol as an attribute block does.
const PUB_DECLARATION: &str = "pub_declaration";

/// What declares a symbol: a form of its own, a member written among the
/// tiles of the form holding it, or a root form that declares nothing.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Declarer
{
    /// The form at the node declares it.
    Form(NodeIndex),
    /// A member of the `theory` block, `data` declaration or `codata`
    /// declaration at the node declares it, written among that form's own
    /// tiles over the span.
    Member(NodeIndex, ByteSpan),
    /// The root form at the node declares nothing: a stray.
    Root(NodeIndex),
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
///   The symbol's range is the form's, widened to the attribute blocks and the
///   `pub` mark standing directly before it, and to a block of `doc` entries
///   alone the parser files under the form, and it is deprecated exactly when
///   one of those blocks, or one the form writes among its own tiles before its
///   keyword, names the `deprecated` attribute; it is exported exactly when the
///   mark stands there, or, held by another symbol, when that one is. Its
///   selection range is the name's, and its kind a function, a value, or by the
///   form's first keyword a world, a module, a data declaration, a codata
///   declaration or a signature. A signature, data declaration or codata
///   declaration holds one symbol per member written between its own braces, as
///   [`members`] reads them, none of them deprecated, each exported when its
///   holder is. Every other form or tile at the root that is no import, no
///   `pub` mark and writes no such form, as [`rooted`] reads them, is one
///   unexported symbol of the kind [`SymbolKind::EVENT`], named by
///   [`root_name`], its range the bytes [`rooted`] gives it, its selection
///   range the form's own, deprecated exactly when an attribute block before it
///   names the `deprecated` attribute, and beside [`Declarer::Root`] of it.
///   Symbols are in source order, each after the declaration holding it, which
///   it names by position; a top-level one names none. Each is beside the form
///   that declares it, or the form whose member it is.
/// - provides: the declarations the document symbols and a hover read.
/// - fails: never.
/// - panics: none.
/// - intension: one walk of the tree with an explicit stack, one more of a
///   container's own children, and one of each root form that declares nothing.
///
/// # Adequacy
/// - hypothesis: L3 — a function, a value, a data declaration with its
///   constructors, a codata declaration with its observations, a module with a
///   nested module, a theory with a member of every kind, documentation and
///   attribute blocks before a definition and a data declaration are asserted
///   at the exact symbol tree. Taking a declaration's range from its name or
///   its form alone, dropping a nested member, reversing source order or
///   reading an attribute name as the declared one changes it; a hover finds
///   each declaration's documentation under its own form. A stray with its
///   attribute block and its `;`, another stray and a trailing attribute block
///   are asserted at their exact symbols, and an import and a `rec` group
///   writing declarations at none.
/// - witness: `outline::tests::declarations_nest_as_symbols`
/// - witness: `outline::tests::a_deprecated_declaration_is_tagged`
/// - witness: `outline::tests::a_theory_holds_its_members`
/// - witness: `outline::tests::a_root_form_that_declares_nothing_is_a_symbol_2073`
/// - witness: `hover::tests::a_declaration_hovers_its_type_and_documentation`
/// - witness: `hover::tests::a_doc_attribute_hovers_its_declaration_3197`
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
    let roots = rooted(grammar, roles, tree, index);
    let mut found: Vec<(Declarer, DocumentSymbol)> = Vec::new();
    let mut pending: Vec<(NodeIndex, Option<usize>, Option<Decorated>)> =
        Vec::from([(tree.root(), None, None)]);
    while let Some((at, holder, decorated)) = pending.pop() {
        let holder = if let Some(symbol) = declared(grammar, roles, tree, index, at, decorated) {
            let container = matches!(
                symbol.kind,
                SymbolKind::INTERFACE | SymbolKind::ENUM | SymbolKind::STRUCT
            );
            let exported = holder
                .and_then(|held| found.get(held))
                .map_or(symbol.exported, |&(_, ref held)| held.exported);
            found.push((Declarer::Form(at), DocumentSymbol {
                holder,
                exported,
                ..symbol
            }));
            let held = found.len().saturating_sub(1);
            if container {
                members(roles, tree, index, at, &mut found);
            }
            Some(held)
        }
        else {
            if let Some(&covered) = roots.get(&at)
                && let Some(symbol) = root_symbol(tree, index, at, covered)
            {
                found.push((Declarer::Root(at), symbol));
            }
            holder
        };
        let first = pending.len();
        // The attribute blocks standing before a form decorate it, layout
        // between them included.
        let mut blocks: Option<Decorated> = None;
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
                    let span = documented(tree, child, node.span());
                    let Deprecated(deprecated) = names_deprecated(tree, child);
                    blocks = Some(Decorated::joined(blocks, Decorated {
                        span,
                        deprecated,
                        exported: Visibility::Private,
                    }));
                    pending.push((child, holder, None));
                },
                NodeLabel::Tile(mold)
                    if grammar
                        .rule_of(mold)
                        .is_ok_and(|rule| rule.name().0 == PUB_DECLARATION) =>
                {
                    blocks = Some(Decorated::joined(blocks, Decorated {
                        span: node.span(),
                        deprecated: false,
                        exported: Visibility::Public,
                    }));
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

/// What the symbol of a root form that declares nothing covers.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Rooted
{
    /// From the first attribute block before the form, or the form's start,
    /// to the lone `;` after it, or the form's end.
    span: ByteSpan,
    /// Whether an attribute block before the form names the `deprecated`
    /// attribute.
    deprecated: bool,
}

/// The root forms of `tree` that declare nothing, each by its node, with
/// what its symbol covers.
///
/// # Specification
/// - requires: `tree` was parsed under `grammar`, and `index` built over its
///   text.
/// - ensures: one entry per child of the root that is a form or a tile, is no
///   attribute block, no `pub` mark and no import, and holds no form
///   [`declared`] names, counted by [`declares`]; except a `;` written alone
///   right after such a child, layout between them, which widens that child's
///   entry instead, as the lowering files it with the child. An entry covers
///   the attribute blocks and `pub` mark written directly before its child, the
///   child and that `;`, and is deprecated when one of those blocks names the
///   `deprecated` attribute. A run of attribute blocks and marks that no form
///   follows is one entry, by its first, covering the run.
/// - provides: the root forms [`declarations`] gives an `Event` symbol.
/// - fails: never.
/// - panics: none.
/// - intension: one pass over the root's children and one walk of each child
///   that is a candidate.
/// - executable: none — the clause would walk the tree again.
///
/// # Adequacy
/// - hypothesis: L3 — as [`declarations`]'s root forms.
/// - witness: `outline::tests::a_root_form_that_declares_nothing_is_a_symbol_2073`
fn rooted(
    grammar: &Pbg,
    roles: &RoleTable,
    tree: &SyntaxTree<'_>,
    index: &LineIndex<'_>,
) -> BTreeMap<NodeIndex, Rooted>
{
    let mut rooted: BTreeMap<NodeIndex, Rooted> = BTreeMap::new();
    // The attribute blocks waiting for the form they decorate, by the first,
    // and the entry a lone `;` would end.
    let mut blocks: Option<(NodeIndex, Rooted)> = None;
    let mut ended: Option<NodeIndex> = None;
    for child in tree.children(tree.root()) {
        let Some(node) = tree.node(child)
        else {
            continue;
        };
        let span = node.span();
        let rule = match node.label() {
            NodeLabel::Space | NodeLabel::Doc => continue,
            NodeLabel::Meld(mold) | NodeLabel::Tile(mold) => {
                grammar.rule_of(mold).ok().map(|rule| rule.name().0)
            },
            NodeLabel::Wald | NodeLabel::Grout { .. } | NodeLabel::GhostClose { .. } => {
                blocks = None;
                ended = None;
                continue;
            },
        };
        let marks = matches!(node.label(), NodeLabel::Meld(_)) && rule == Some(ATTRIBUTE_BLOCK)
            || matches!(node.label(), NodeLabel::Tile(_)) && rule == Some(PUB_DECLARATION);
        if marks {
            let Deprecated(deprecated) = names_deprecated(tree, child);
            let block = Rooted { span, deprecated };
            blocks = Some(blocks.map_or((child, block), |(first, run)| {
                (first, Rooted {
                    span: run.span.join(span),
                    deprecated: run.deprecated || deprecated,
                })
            }));
            ended = None;
            continue;
        }
        if blocks.is_none()
            && matches!(node.label(), NodeLabel::Tile(_))
            && tree.fragment(child).map(<&str>::from) == Some(";")
            && let Some(entry) = ended.take().and_then(|at| rooted.get_mut(&at))
        {
            entry.span = entry.span.join(span);
            continue;
        }
        let decorated = blocks.take().map(|(_, run)| run);
        ended = None;
        if rule == Some(IMPORT) || declares(grammar, roles, tree, index, child).0 {
            continue;
        }
        rooted.insert(child, Rooted {
            span: decorated.map_or(span, |run| run.span.join(span)),
            deprecated: decorated.is_some_and(|run| run.deprecated),
        });
        ended = Some(child);
    }
    if let Some((first, run)) = blocks {
        rooted.insert(first, run);
    }
    rooted
}

/// Whether a subtree holds a form [`declared`] names.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Declares(bool);

/// Whether the subtree at `at` holds a form [`declared`] names, `at` itself
/// among them.
///
/// # Specification
/// trivial.
fn declares(
    grammar: &Pbg,
    roles: &RoleTable,
    tree: &SyntaxTree<'_>,
    index: &LineIndex<'_>,
    at: NodeIndex,
) -> Declares
{
    let mut pending = Vec::from([at]);
    while let Some(next) = pending.pop() {
        if declared(grammar, roles, tree, index, next, None).is_some() {
            return Declares(true);
        }
        pending.extend(tree.children(next));
    }
    Declares(false)
}

/// The symbol of the root form at `at` that declares nothing, covering what
/// `rooted` says; none when it writes nothing to name it by.
///
/// # Specification
/// trivial.
fn root_symbol(
    tree: &SyntaxTree<'_>,
    index: &LineIndex<'_>,
    at: NodeIndex,
    rooted: Rooted,
) -> Option<DocumentSymbol>
{
    Some(DocumentSymbol {
        name: root_name(tree, at)?,
        kind: SymbolKind::EVENT,
        range: range_of(index, rooted.span)?,
        selection_range: range_of(index, tree.node(at)?.span())?,
        detail: None,
        holder: None,
        deprecated: rooted.deprecated,
        exported: Visibility::Private,
    })
}

/// The name of the root form at `at`: what it writes up to its first own
/// `{`, then `{ … }`, or all it writes without a final `;` when it opens no
/// brace, its layout collapsed; none when that is empty.
///
/// # Specification
/// trivial.
fn root_name(
    tree: &SyntaxTree<'_>,
    at: NodeIndex,
) -> Option<String>
{
    let span = tree.node(at)?.span();
    let brace = tree.children(at).find_map(|child| {
        let node = tree.node(child)?;
        (matches!(node.label(), NodeLabel::Tile(_))
            && tree.fragment(child).map(<&str>::from) == Some("{"))
        .then(|| node.span().start())
    });
    let written = <&str>::from(
        tree.source()
            .fragment(ByteSpan::new(span.start(), brace.unwrap_or_else(|| span.end())).ok()?)
            .ok()?,
    );
    let written = written.trim_end();
    let mut name = String::new();
    laid_out(
        SourceFragment::from(written.strip_suffix(';').unwrap_or(written)),
        &mut name,
    );
    if brace.is_some() {
        if !name.is_empty() {
            name.push(' ');
        }
        name.push_str("{ … }");
    }
    (!name.is_empty()).then_some(name)
}

/// The attribute blocks and the `pub` mark standing before a form: the bytes
/// they cover, whether a block names the `deprecated` attribute, and whether
/// the mark exports the form.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Decorated
{
    /// From the first block's or the mark's start to the last one's end.
    span: ByteSpan,
    /// Whether a block names the `deprecated` attribute.
    deprecated: bool,
    /// Whether a `pub` mark stands among them.
    exported: Visibility,
}

impl Decorated
{
    /// `next` after the run `before`, when one stands before it: the run
    /// widened over it, deprecated or exported when either is.
    ///
    /// # Specification
    /// trivial.
    fn joined(
        before: Option<Self>,
        next: Self,
    ) -> Self
    {
        before.map_or(next, |first| Self {
            span: first.span.join(next.span),
            deprecated: first.deprecated || next.deprecated,
            exported: match (first.exported, next.exported) {
                (Visibility::Public, _) | (_, Visibility::Public) => Visibility::Public,
                (Visibility::Private, Visibility::Private) => Visibility::Private,
            },
        })
    }
}

/// Whether attribute blocks name the `deprecated` attribute.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Deprecated(bool);

/// Whether the attribute blocks the node at `at` starts with name the
/// `deprecated` attribute: a tile reading `deprecated` right after a block's
/// `@[` or a `,`, where an attribute's name stands, not inside a payload. The
/// node is an attribute block, or a form writing its blocks among its own
/// tiles before its keyword, as an attributed module member does; the reading
/// stops at the first tile or form outside a block.
///
/// # Specification
/// trivial.
fn names_deprecated(
    tree: &SyntaxTree<'_>,
    at: NodeIndex,
) -> Deprecated
{
    let mut inside = false;
    let mut opens_name = false;
    for child in tree.children(at) {
        let Some(node) = tree.node(child)
        else {
            continue;
        };
        match node.label() {
            NodeLabel::Space | NodeLabel::Doc => {},
            NodeLabel::Tile(_) => {
                let written = tree.fragment(child).map(<&str>::from);
                if !inside {
                    if written != Some("@[") {
                        return Deprecated(false);
                    }
                    inside = true;
                }
                else if written == Some("]") {
                    inside = false;
                }
                else if opens_name && written == Some("deprecated") {
                    return Deprecated(true);
                }
                opens_name = inside && matches!(written, Some("@[" | ","));
            },
            NodeLabel::Meld(_)
            | NodeLabel::Wald
            | NodeLabel::Grout { .. }
            | NodeLabel::GhostClose { .. } => {
                if !inside {
                    return Deprecated(false);
                }
                opens_name = false;
            },
        }
    }
    Deprecated(false)
}

/// `span`, the node at `at`'s own, widened over each block of `doc` entries
/// alone among its children: the parser files such a block as documentation of
/// the form or the attribute block after it, a documentation node whose first
/// tile opens a block, `@[`, which stands before that node all the same
/// (#3197).
///
/// # Specification
/// trivial.
fn documented(
    tree: &SyntaxTree<'_>,
    at: NodeIndex,
    span: ByteSpan,
) -> ByteSpan
{
    tree.children(at)
        .filter_map(|child| {
            let node = tree.node(child)?;
            if !matches!(node.label(), NodeLabel::Doc) {
                return None;
            }
            let opener = tree.children(child).find(|&written| {
                matches!(
                    tree.node(written).map(Node::label),
                    Some(NodeLabel::Tile(_))
                )
            })?;
            (tree.fragment(opener).map(<&str>::from) == Some("@[")).then_some(node.span())
        })
        .fold(span, ByteSpan::join)
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
    decorated: Option<Decorated>,
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
                let first = tree.fragment(child)?;
                let mut name = String::from(<&str>::from(first));
                let mut named = tree.node(child)?.span();
                // A dotted name, `theory Gandr.Package`, is the symbol's name
                // whole: the modules its prefix names are written by no form
                // of their own.
                let after: Vec<NodeIndex> = tree
                    .children(at)
                    .skip_while(|&later| later != child)
                    .skip(1)
                    .filter(|&later| {
                        matches!(tree.node(later).map(Node::label), Some(NodeLabel::Tile(_)))
                    })
                    .collect();
                for pair in after.chunks_exact(2) {
                    let &[dot, segment] = pair
                    else {
                        break;
                    };
                    let Some(written) = tree.fragment(segment)
                    else {
                        break;
                    };
                    if tree.fragment(dot).map(<&str>::from) != Some(".") {
                        break;
                    }
                    name.push('.');
                    name.push_str(<&str>::from(written));
                    named = named.join(tree.node(segment)?.span());
                }
                let body = tree
                    .children(at)
                    .skip_while(|&later| later != child)
                    .find_map(|later| body_start(tree, later))
                    .unwrap_or_else(|| node.span().end());
                // A block of `doc` entries alone filed under the form widens
                // its range as a block standing beside it does.
                let widened = documented(tree, at, node.span());
                return Some(DocumentSymbol {
                    name,
                    kind: kind_of(role, keyword),
                    range: range_of(
                        index,
                        decorated.map_or(widened, |blocks| blocks.span.join(widened)),
                    )?,
                    selection_range: range_of(index, named)?,
                    detail: detail(tree, named.end(), body),
                    holder: None,
                    deprecated: decorated.is_some_and(|blocks| blocks.deprecated)
                        || names_deprecated(tree, at).0,
                    exported: decorated.map_or(Visibility::Private, |blocks| blocks.exported),
                });
            },
            Ok(_) | Err(_) => {},
        }
    }
    None
}

/// Where the node at `at` starts, when it is a tile ending what a declaration
/// writes after its name: the `=` before its definition, the `{` opening its
/// body or the `;` ending it.
///
/// # Specification
/// trivial.
fn body_start(
    tree: &SyntaxTree<'_>,
    at: NodeIndex,
) -> Option<SyntaxOffset>
{
    let node = tree.node(at)?;
    let NodeLabel::Tile(_) = node.label()
    else {
        return None;
    };
    tree.fragment(at)
        .filter(|text| matches!(<&str>::from(*text), "=" | "{" | ";"))
        .map(|_| node.span().start())
}

/// What a declaration writes between `start`, where its name ends, and `end`,
/// where its definition or body starts: the source's text there, each run of
/// layout one space — none after an opening bracket or before a closing one —
/// a leading `:` and a trailing `;` dropped; none when nothing remains.
///
/// # Specification
/// trivial.
fn detail(
    tree: &SyntaxTree<'_>,
    start: SyntaxOffset,
    end: SyntaxOffset,
) -> Option<String>
{
    let written = <&str>::from(
        tree.source()
            .fragment(ByteSpan::new(start, end).ok()?)
            .ok()?,
    );
    let written = written.trim();
    let written = written.strip_prefix(':').unwrap_or(written);
    let written = written.strip_suffix(';').unwrap_or(written);
    let mut collapsed = String::new();
    laid_out(SourceFragment::from(written), &mut collapsed);
    (!collapsed.is_empty()).then_some(collapsed)
}

/// Appends `written` to `collapsed` with each run of layout one space, none
/// after an opening bracket or before a closing one.
///
/// # Specification
/// trivial.
fn laid_out(
    written: SourceFragment<'_>,
    collapsed: &mut String,
)
{
    let start = collapsed.len();
    for word in <&str>::from(written).split_whitespace() {
        let glued = collapsed.ends_with(['(', '[', '{']) || word.starts_with([')', ']', '}']);
        if collapsed.len() > start && !glued {
            collapsed.push(' ');
        }
        collapsed.push_str(word);
    }
}

/// What a client shows in place of the lines `span` folds, written by the
/// form at `holder` among its own tiles: the text before `span` on its first
/// line, then what the form writes up to its first own `{`, `=` or `;` inside
/// `span`, its layout collapsed, the body after a `{` elided as `{ … }` and
/// the definition after an `=` as `= …` with a final `;` kept; none when no
/// such tile is inside `span`.
///
/// # Specification
/// trivial.
fn folded(
    tree: &SyntaxTree<'_>,
    holder: NodeIndex,
    span: ByteSpan,
) -> Option<String>
{
    let (opener, spelled) = tree.children(holder).find_map(|child| {
        let start = body_start(tree, child)?;
        let inside = span.start() <= start && start < span.end();
        inside.then_some((start, tree.fragment(child)?))
    })?;
    let source = <&str>::from(tree.source());
    let before = source.get(.. usize::from(span.start()))?;
    let line = before
        .rfind('\n')
        .map_or(0_usize, |newline| newline.saturating_add(1));
    let mut shown = String::from(before.get(line ..)?);
    let lead = shown.len();
    laid_out(
        tree.source()
            .fragment(ByteSpan::new(span.start(), opener).ok()?)
            .ok()?,
        &mut shown,
    );
    let ended = source
        .get(usize::from(span.start()) .. usize::from(span.end()))
        .is_some_and(|written| written.trim_end().ends_with(';'));
    let elided = match <&str>::from(spelled) {
        "{" => "{ … }",
        "=" if ended => "= …;",
        "=" => "= …",
        _ => ";",
    };
    if shown.len() > lead && elided != ";" {
        shown.push(' ');
    }
    shown.push_str(elided);
    Some(shown)
}

/// What a declaration named by a tile of `role` declares, after its first
/// keyword `keyword`: a law for `law`, a model's admitted law.
///
/// # Specification
/// trivial.
fn kind_of(
    role: HlRole,
    keyword: Option<SourceFragment<'_>>,
) -> SymbolKind
{
    match (role, keyword.map(<&str>::from)) {
        (_, Some("law")) => SymbolKind::PROPERTY,
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
    /// Its own tiles written at the braces' depth, in source order: the `{`
    /// opening a nested group among them, the `}` closing it not.
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
        let written_at = depth;
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
        if written_at == 1 && tile {
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
        let body = name.and_then(|(named, _)| {
            run.tiles
                .iter()
                .copied()
                .skip_while(|&later| later != named)
                .find_map(|later| body_start(tree, later))
        });
        if let Some(symbol) = member(tree, index, &run, keyword, name, body) {
            let exported = found
                .get(holder)
                .map_or(Visibility::Private, |&(_, ref held)| held.exported);
            found.push((Declarer::Member(at, run.span), DocumentSymbol {
                holder: Some(holder),
                exported,
                ..symbol
            }));
        }
    }
}

/// The symbol of a member written as `run` after its keyword `keyword`, named
/// by the tile at `name`, its body or definition starting at `body`, or none
/// for an unnamed member or an `include`.
///
/// # Specification
/// trivial.
fn member(
    tree: &SyntaxTree<'_>,
    index: &LineIndex<'_>,
    run: &Run,
    keyword: Option<SourceFragment<'_>>,
    name: Option<(NodeIndex, HlRole)>,
    body: Option<SyntaxOffset>,
) -> Option<DocumentSymbol>
{
    let (named, role) = name?;
    if keyword.map(<&str>::from) == Some("include") {
        return None;
    }
    let named_span = tree.node(named)?.span();
    let end = body.unwrap_or_else(|| run.span.end());
    Some(DocumentSymbol {
        name: String::from(<&str>::from(tree.fragment(named)?)),
        kind: member_kind(role, keyword),
        range: range_of(index, run.span)?,
        selection_range: range_of(index, named_span)?,
        detail: detail(tree, named_span.end(), end),
        holder: None,
        deprecated: false,
        exported: Visibility::Private,
    })
}

/// What a member named by a tile of `role` declares, after its keyword
/// `keyword`: a law for `rule` and `law`, an observation for `obs` or a codata
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
        (_, Some("rule" | "law")) => SymbolKind::PROPERTY,
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
///   comments carry the `comment` kind and no collapsed text; forms and members
///   no kind and, when one of their own `{`, `=` or `;` tiles is inside them,
///   the text the first line holds before them followed by what they write up
///   to that tile, layout collapsed, the rest elided. Ascending by first line.
/// - provides: the answer to `textDocument/foldingRange`.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a multi-line function with a block inside it, a one-line
///   declaration, a documentation run, a block comment, a theory with a
///   multi-line member and a one-line one, a definition after `=` and a member
///   ending at `;` are asserted at the exact ranges and texts. Folding a
///   one-line form or member, keeping the inner of two ranges starting on one
///   line, dropping a member, losing the comment kind, giving a comment a text
///   or eliding at the wrong tile changes them.
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
    // A form or a member names the form whose tiles write it; a comment none.
    let mut fold = |span: ByteSpan, holder: Option<NodeIndex>| {
        if let Some(range) = range_of(index, span)
            && range.start.line < range.end.line
        {
            folds.push(FoldingRange {
                start_line: range.start.line,
                end_line: range.end.line,
                kind: holder.is_none().then_some(COMMENT),
                collapsed_text: holder.and_then(|holder| folded(tree, holder, span)),
            });
        }
    };
    for position in tree.positions() {
        let Some(node) = tree.node(position)
        else {
            continue;
        };
        let holder = match node.label() {
            NodeLabel::Meld(_) => Some(position),
            NodeLabel::Doc => None,
            NodeLabel::Space
                if tree
                    .fragment(position)
                    .is_some_and(|text| <&str>::from(text).starts_with(BLOCK_COMMENT)) =>
            {
                None
            },
            NodeLabel::Wald
            | NodeLabel::Space
            | NodeLabel::Tile(_)
            | NodeLabel::Grout { .. }
            | NodeLabel::GhostClose { .. } => continue,
        };
        fold(node.span(), holder);
    }
    for &(holder, span) in members {
        fold(span, Some(holder));
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

    /// A root form that declares nothing is an `Event` symbol named by what it
    /// writes: a final expression over its attribute block and its `;`, a
    /// stray, and a run of attribute blocks no form follows; an import and
    /// a `rec` group writing a declaration are none (#2073).
    #[test]
    fn a_root_form_that_declares_nothing_is_a_symbol_2073()
    {
        let targeted = "def a = 1 ;\n@[ deprecated ]\nthunk {\n  return a\n} ;\n";
        let answered = Reading::of(SourceText::from(targeted)).symbols();
        assert_eq!(outline(&answered), [
            "a 12 0:0-0:11 at 0:4-0:5",
            "thunk { … } 24 1:0-4:3 at 2:0-4:1",
        ]);
        assert_eq!(
            answered
                .0
                .iter()
                .map(|symbol| symbol.deprecated)
                .collect::<Vec<_>>(),
            [false, true],
            "the block before the final expression marks it"
        );
        let strays =
            "import \"./a.gandr\" ;\n1 ;\nrec {\n  def b = 2 ;\n}\nb ;\n@[ checks ]\n@[ checks ]\n";
        assert_eq!(outline(&Reading::of(SourceText::from(strays)).symbols()), [
            "1 24 1:0-1:3 at 1:0-1:1",
            "b 12 3:2-3:13 at 3:6-3:7",
            "b 24 5:0-5:3 at 5:0-5:1",
            "@[checks] 24 6:0-7:11 at 6:0-6:11",
        ]);
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

    /// A declaration an attribute block before it marks `deprecated` is
    /// tagged so on the wire, whichever block names it and whatever its
    /// payload; a `deprecated` word inside another attribute's payload marks
    /// nothing, and neither does a module member's block mark its holder.
    #[test]
    fn a_deprecated_declaration_is_tagged()
    {
        let source = "@[ deprecated ] def bare = 1 ;\n@[ checks ]\n@[ doc(\"x\"), deprecated(#{ \
                      since = \"0.2\" }) ] def recorded = 2 ;\n@[ respects(deprecated) ] def \
                      named = 3 ;\nmodule Holder {\n  @[ deprecated ] def member = 4 ;\n}\ndef \
                      plain = 5 ;\n";
        let answered = Reading::of(SourceText::from(source)).symbols();
        assert_eq!(
            answered
                .0
                .iter()
                .map(|symbol| (symbol.name.as_str(), symbol.deprecated))
                .collect::<Vec<_>>(),
            [
                ("bare", true),
                ("recorded", true),
                ("named", false),
                ("Holder", false),
                ("member", true),
                ("plain", false),
            ]
        );
        let wire = serde_json::to_value(&answered).expect("the symbols encode");
        assert_eq!(
            wire.pointer("/0/tags"),
            Some(&serde_json::json!([1_u8])),
            "a deprecated symbol carries the protocol's `Deprecated` tag"
        );
        assert_eq!(
            wire.pointer("/3/children/0/tags"),
            Some(&serde_json::json!([1_u8])),
            "a member is tagged where it nests"
        );
        assert!(
            wire.pointer("/2/tags").is_none(),
            "an unmarked symbol carries no tags"
        );
    }

    /// Each declaration carries what it writes between its name and its body
    /// or definition, its layout collapsed and a leading `:` dropped; one
    /// that writes nothing there, a member among them, carries none. A dotted
    /// name is the symbol's whole name (#2687).
    #[test]
    fn each_symbol_carries_what_it_writes_after_its_name()
    {
        let source = "def twice(\n  x : Integer\n) -> -F Integer {\n  return x\n}\ndef answer = 42 \
                      ;\ndef later : Integer ;\ndata Color : Type { Red : Color; }\ntheory Shapes {\n  \
                      sort M : Type;\n  oper mul : (x : M, y : M) --> M;\n  rule spin : (data s : \
                      M) ==> (out : M) {\n    node : mul(s, s) --> (out);\n  };\n}\nmodule Plain \
                      {\n  def one = 1 ;\n}\nworld seat ;\nmodule Kit.Tools : #{ two : Integer } \
                      {\n  def two = 2 ;\n}\n";
        let details: Vec<(String, Option<String>)> = Reading::of(SourceText::from(source))
            .symbols()
            .0
            .into_iter()
            .map(|symbol| (symbol.name, symbol.detail))
            .collect();
        let row = |name: &str, detail: Option<&str>| (name.to_owned(), detail.map(str::to_owned));
        assert_eq!(details, [
            row("twice", Some("(x : Integer) -> -F Integer")),
            row("answer", None),
            row("later", Some("Integer")),
            row("Color", Some("Type")),
            row("Red", Some("Color")),
            row("Shapes", None),
            row("M", Some("Type")),
            row("mul", Some("(x : M, y : M) --> M")),
            row("spin", Some("(data s : M) ==> (out : M)")),
            row("Plain", None),
            row("one", None),
            row("seat", None),
            row("Kit.Tools", Some("#{two : Integer}")),
            row("two", None),
        ]);
    }

    /// A theory's members nest under it, one of each kind with its own kind;
    /// a name list's braces and `;` stay inside its boundary or face; an
    /// `include` is no member; and a codata declaration's observations nest
    /// under it.
    #[test]
    fn a_theory_holds_its_members()
    {
        let source = "theory Shapes {\n  sort M : Type;\n  data Unit : M;\n  oper mul : (x : M, y \
                      : M) --> M;\n  obs size : (m : M) --> M;\n  rule assoc : mul(mul(x, y), z) \
                      ==> mul(x, mul(y, z));\n  boundary Square { tl, tr, bl, br };\n  face \
                      left = { tl, bl };\n  ext Cell = M on left is zero;\n}\ntheory Monoid {\n  \
                      include Shapes;\n  oper \
                      one : () --> M;\n}\ncodata Stream : Type {\n  head : M;\n  tail : \
                      Stream;\n}\n";
        assert_eq!(outline(&Reading::of(SourceText::from(source)).symbols()), [
            "Shapes 11 0:0-9:1 at 0:7-0:13",
            "  M 26 1:2-1:16 at 1:7-1:8",
            "  Unit 9 2:2-2:16 at 2:7-2:11",
            "  mul 6 3:2-3:34 at 3:7-3:10",
            "  size 8 4:2-4:27 at 4:6-4:10",
            "  assoc 7 5:2-5:55 at 5:7-5:12",
            "  Square 26 6:2-6:37 at 6:11-6:17",
            "  left 8 7:2-7:25 at 7:7-7:11",
            "  Cell 26 8:2-8:31 at 8:6-8:10",
            "Monoid 11 10:0-13:1 at 10:7-10:13",
            "  one 6 12:2-12:22 at 12:7-12:10",
            "Stream 23 14:0-17:1 at 14:7-14:13",
            "  head 8 15:2-15:11 at 15:2-15:6",
            "  tail 8 16:2-16:16 at 16:2-16:6",
        ]);
    }

    #[test]
    fn multi_line_forms_and_documentation_fold()
    {
        let source = "/// One.\n/// Two.\ndef f(x: Integer) -> -F Integer {\n  return x\n}\n\
                      def g = 1 ;\n/* a\n   block */\ndef h = 2 ;\n\
                      theory T {\n  sort M : Type;\n  boundary Square {\n    tl, tr, bl, br\n  \
                      };\n  oper mul :\n    (M, M) => M;\n}\ndef k =\n  1 ;\n";
        let answered: Vec<(u64, u64, Option<&str>, Option<String>)> =
            Reading::of(SourceText::from(source))
                .folds()
                .iter()
                .map(|fold| {
                    let value = serde_json::to_value(fold).expect("a fold encodes");
                    let line = |field| value.get(field).and_then(Value::as_u64).unwrap_or(u64::MAX);
                    let text = value
                        .get("collapsedText")
                        .and_then(Value::as_str)
                        .map(str::to_owned);
                    (line("startLine"), line("endLine"), fold.kind, text)
                })
                .collect();
        let shown = |text: &str| Some(text.to_owned());
        assert_eq!(
            answered,
            [
                (0, 1, Some("comment"), None),
                (2, 4, None, shown("def f(x: Integer) -> -F Integer { … }")),
                (6, 7, Some("comment"), None),
                (9, 16, None, shown("theory T { … }")),
                (11, 13, None, shown("  boundary Square { … }")),
                (14, 15, None, shown("  oper mul : (M, M) => M;")),
                (17, 18, None, shown("def k = …;")),
            ],
            "documentation, the function, the block comment, the theory, its multi-line \
             members and a definition after `=` fold, each form showing what it writes \
             before its body; the one-line forms and members do not"
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
