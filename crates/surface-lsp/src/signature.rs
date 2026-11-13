//! Signature help and the context stack: each spine a position stands in, the
//! declared head of each, and the slot the position fills.
//!
//! A held text's reading keeps the context stack of the text
//! ([`Stack`]): the spines of each form, a juxtaposed application and a
//! family's application alike, which the form store keeps with the form's
//! region. A copy's hovering keeps the head of every declaration and
//! constructor its import closure writes ([`Signatures`]): the name through its
//! parameters and its result on one line, each parameter's place in that label
//! with the `///` run written before it, and the documentation written for the
//! head. The heads are read once per text, off the parse it already makes; the
//! heads the closure writes are read once per closure lowering the process
//! holds and shared by every text laid after it, so a keystroke reads the
//! document's own forms alone. The type table's referent index
//! ([`TypeTable::referent`]) gives the declaration a spine's head refers to.
//! The faces read the spines a position stands in once, from the innermost
//! outward. A position past the last argument of a spine, after layout on its
//! line, opens the spine's next slot while its declared head takes one. A
//! position after a head that has no argument yet, and layout on its line,
//! opens that head's first slot in the same way. So a space typed after a head
//! whose type still takes arguments stands in the slot that it opens.
//! Signature help answers one signature per spine, the innermost active, each
//! with the parameter its slot fills. A `gandr/stack` request answers each
//! spine: its head, the type the judgement gives the head, the declared head
//! and its arity, the slot, and the type the judgement checked the slot's
//! argument against, or none where the judgement typed no term in the slot.
//! The stack card of the render bus holds the same rows, the type of each head
//! with the run its slot's parameter writes. None of them reads text past the
//! layout before the position, or resolves a name.
//!
//! A head is read off its declaring form:
//!
//! | Form | Label | Parameters |
//! | --- | --- | --- |
//! | `def plus(n : Nat, m : Nat) -> -F Nat` | `plus(n : Nat, m : Nat) -> -F Nat` | `n : Nat`, `m : Nat` |
//! | `def double : +U (Nat -> -F Nat)` | `double : +U (Nat -> -F Nat)` | each domain of the arrow: `Nat` |
//! | `\| Cons : (head : a, tail : List(a)) --> List(a)` | as written, past its bar | `head : a`, `tail : List(a)` |
//! | `data List(a : Type) : Type where` | `List(a : Type) : Type` | `a : Type` |
//!
//! The pieces of a head are joined with one space wherever the source leaves
//! layout between them, so a head written over several lines reads on one,
//! and its comments are dropped.
//!
//! [`Stack`]: gandr_surface_session::Stack
//! [`TypeTable::referent`]: gandr_surface_dispatcher::TypeTable::referent

use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::fmt::Write as _;
use std::sync::Mutex;
use std::sync::PoisonError;

use anodized::spec;
use gandr_surface_dispatcher::Referent;
use gandr_surface_dispatcher::TypedSpan;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::RoleTable;
use gandr_surface_grammar::Sort;
use gandr_surface_lowering::Documentation;
use gandr_surface_lowering::SourceIndex;
use gandr_surface_lowering::Unit;
use gandr_surface_lowering::read_doc;
use gandr_surface_pretty::Style;
use gandr_surface_render_remote::Count;
use gandr_surface_render_remote::HlRole;
use gandr_surface_render_remote::LineIndex;
use gandr_surface_render_remote::SpineRow;
use gandr_surface_render_remote::StackCard;
use gandr_surface_session::ClosureKey;
use gandr_surface_session::Frame;
use gandr_surface_session::Holding;
use gandr_surface_session::Slot;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::Node;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SourceText;
use gandr_surface_syntax::SyntaxTree;
use quenchant_shape::shape::Maybe;

use crate::hover::Hovering;
use crate::inline::escape_into;
use crate::position::Position;
use crate::position::ranged;
use crate::protocol::Answer;
use crate::protocol::LabelOffsets;
use crate::protocol::MarkupContent;
use crate::protocol::ParameterInformation;
use crate::protocol::ParameterLabel;
use crate::protocol::SignatureHelp;
use crate::protocol::SignatureInformation;
use crate::protocol::StackRow;
use crate::reading::Reading;

/// The rule of an attribute block standing before the declaration it
/// decorates, whose documentation documents that declaration.
const ATTRIBUTE_BLOCK: &str = "attribute_block";

/// The rule of a `pub` mark, one tile between a declaration's documentation
/// and the declaration it exports.
const PUB_DECLARATION: &str = "pub_declaration";

/// The rules a function type's arrow is read through: the thunk around it, and
/// the parentheses around either.
const ENCLOSING: [&str; 2] = ["u_type", PARENTHESES];

/// The rule of a parenthesised type, a wrapper or a telescope.
const PARENTHESES: &str = "parenthesized_type";

/// The rule of a function type, `A -> B` or `(a : A) -> B`.
const ARROW: &str = "function_type";

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

/// A parameter of a head: its place in the label, the name tile it binds,
/// and the documentation written before it.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Parameter
{
    /// Its place in the head's label.
    place: Place,
    /// The first tile it writes, in the text the head was read off.
    named: Option<ByteSpan>,
    /// The `///` run written before it.
    documentation: Option<String>,
}

/// A head: its label, each parameter's place in the label, and the
/// documentation written for it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Signature
{
    /// The name through its parameters and its result, on one line.
    label: String,
    /// Each parameter, in written order.
    parameters: Vec<Parameter>,
    /// The documentation written for the declaration or constructor.
    documentation: Option<String>,
    /// Where the type starts in the label: past the name, and past the `:`
    /// written after it.
    typed: usize,
}

impl Signature
{
    /// The head that `label` writes, with `parameters` and `documentation`, its
    /// name at `name` written first: its type starts past the name, the layout
    /// after it, and a `:` with the layout after that.
    ///
    /// # Specification
    /// trivial.
    fn written(
        label: Label,
        parameters: Vec<Parameter>,
        documentation: Option<String>,
        name: Option<ByteSpan>,
    ) -> Self
    {
        let named = name.map_or(0, |name| {
            usize::from(name.end()).saturating_sub(usize::from(name.start()))
        });
        let rest = label.text.get(named ..).unwrap_or_default().trim_start();
        let rest = rest.strip_prefix(':').map_or(rest, str::trim_start);
        Self {
            typed: label.text.len().saturating_sub(rest.len()),
            label: label.text,
            parameters,
            documentation,
        }
    }

    /// The name through its parameters and its result, on one line.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn label(&self) -> SourceText<'_>
    {
        SourceText::from(self.label.as_str())
    }

    /// The documentation written for the declaration or constructor.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn documentation(&self) -> Option<SourceText<'_>>
    {
        self.documentation.as_deref().map(SourceText::from)
    }

    /// A call of `name` with each parameter a tab stop, as a snippet, written
    /// as `calling` says: the stop holds the name the parameter declares, or
    /// what it writes when it declares none.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: none for a head with no parameters; otherwise `name`, then
    ///   one stop per parameter in written order, numbered from 1 — each after
    ///   a space when [`Calling::Juxtaposed`], or between `(` and `)` and
    ///   separated by `, ` when [`Calling::Applied`] — then the final stop
    ///   `$0`. A stop's text is the parameter's text before its first ` : `
    ///   when it has one and its whole text otherwise, escaped for the snippet
    ///   syntax, as `name` is.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — named parameters of a function, a family and a
    ///   constructor, the unnamed domains of a thunk, and a head with none.
    /// - witness: `complete::tests::a_call_fills_its_parameters_as_tab_stops`
    #[spec(ensures: |ret| ret.is_none() == self.parameters.is_empty()
        && ret.as_ref().is_none_or(|snippet| snippet.ends_with("$0")
            && snippet.matches("${").count() >= self.parameters.len()))]
    pub(crate) fn called(
        &self,
        name: SourceText<'_>,
        calling: Calling,
    ) -> Option<String>
    {
        if self.parameters.is_empty() {
            return None;
        }
        let mut snippet = String::new();
        escape_into(&mut snippet, name);
        if calling == Calling::Applied {
            snippet.push('(');
        }
        for (stop, parameter) in (1_usize ..).zip(&self.parameters) {
            match calling {
                Calling::Juxtaposed => snippet.push(' '),
                Calling::Applied if stop > 1 => snippet.push_str(", "),
                Calling::Applied => {},
            }
            let written = self
                .label
                .get(parameter.place.start .. parameter.place.end)
                .unwrap_or_default();
            let held = written
                .split_once(" : ")
                .map_or(written, |(named, _)| named);
            let _written = write!(snippet, "${{{stop}:");
            escape_into(&mut snippet, SourceText::from(held));
            snippet.push('}');
        }
        if calling == Calling::Applied {
            snippet.push(')');
        }
        snippet.push_str("$0");
        Some(snippet)
    }
}

/// How a call is written: a value's call as a juxtaposed spine, `f x y`, a
/// family's application in its parentheses, `List(a)`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Calling
{
    /// `f x y`.
    Juxtaposed,
    /// `List(a)`.
    Applied,
}

/// One head: the source holding its name and the name's span in that source's
/// own text, and the head written there.
type Head = ((SourceIndex, ByteSpan), Signature);

/// The heads each closure lowering's part of a tree writes, by the lowering's
/// key: read the first time a text is laid after the lowering, and let go
/// once nothing holds the lowering.
// economy: no byte form, the codec is #4084. The heads are keyed by the
// lowering they come from, so they cross the store under the lowering's
// content key once the lowering has an image.
static CLOSURE_HEADS: Mutex<Vec<(ClosureKey, Arc<[Head]>)>> = Mutex::new(Vec::new());

/// The heads an import closure writes, by the source and the name tile of
/// each declaration, constructor and binder typed by a function: those its
/// closure writes, shared with every text laid after the same closure
/// lowering, and those the document's own text writes.
///
/// # Specification
/// - requires: built by [`Signatures::of`] or [`Signatures::after`].
/// - ensures: each part ascending by source, then name tile, no tile twice;
///   every source of the closure's part before every source of the document's.
/// - panics: none.
/// - executable: none — a carrier; [`Signatures::of`], [`Signatures::after`]
///   and [`Signatures::declared`] carry the predicates.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Signatures::of`] and [`Signatures::after`].
/// - witness: `signature::tests::each_head_reads_its_parameters`
/// - witness: `signature::tests::a_closure_s_heads_are_read_once_per_lowering_1403`
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Signatures
{
    /// The heads the closure a text is laid after writes.
    closure: Arc<[Head]>,
    /// The heads the text's own forms write.
    own: Vec<Head>,
    /// The documentation of each parameter the text's own heads write that
    /// has any, by the source holding the parameter's first tile and that
    /// tile's span in the source's own text, ascending.
    documented: Vec<((SourceIndex, ByteSpan), String)>,
}

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
    ///   a source, the first head for a tile kept; all of them the text's own.
    ///   A head laid over lines labels as one line: each stretch of layout that
    ///   breaks a line or holds documentation is one space, none inside its
    ///   parentheses or before a comma. A parameter carries the documentation
    ///   nodes written before it inside its list or telescope, and none of them
    ///   documents the head.
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
    ///   telescope each read at their exact label and parameters; documented
    ///   parameters of a list laid over lines and of a telescope, a run of two
    ///   lines among them, at their exact documentation.
    /// - witness: `signature::tests::each_head_reads_its_parameters`
    /// - witness: `signature::tests::a_parameter_reads_the_documentation_written_before_it_1116`
    #[spec(ensures: |ret| ret.closure.is_empty()
        && ret.own.windows(2).all(|pair| matches!(pair, [first, second] if first.0 < second.0)))]
    #[must_use]
    pub fn of(
        grammar: &Pbg,
        roles: &RoleTable,
        tree: &SyntaxTree<'_>,
        unit: &Unit,
    ) -> Self
    {
        let own = heads_among(
            grammar,
            roles,
            tree,
            unit,
            tree.roots().iter().flat_map(|&root| tree.children(root)),
        );
        Self {
            closure: Arc::default(),
            documented: parameters_documented(unit, &own),
            own,
        }
    }

    /// The heads `tree`, the text `unit` lays out with the document's own text
    /// from `base` on, writes, as [`Signatures::of`] reads them: those of the
    /// forms before `base` under the closure's part, and those of the forms
    /// from `base` on under the text's own.
    ///
    /// # Specification
    /// - requires: as [`Signatures::of`]; `tree`'s forms before `base` are the
    ///   closure's, and `closure` names the lowering of them the process holds,
    ///   when it holds one.
    /// - ensures: [`Signatures::of`]'s heads, each top-level form read with the
    ///   documentation written before it on its own side of `base`. When
    ///   `closure` names a lowering, the closure's part is the one kept for it,
    ///   read now when nothing is kept, and kept until nothing holds the
    ///   lowering. Else the closure's part is read now and not kept. The split
    ///   does not depend on whether the process holds the lowering (#5198).
    /// - provides: a keystroke's heads read off the document's own forms alone.
    /// - fails: never.
    /// - panics: none.
    /// - intension: one walk of the forms from `base` on, one lock and a scan
    ///   of the kept closures; the closure's forms walked once per lowering, or
    ///   once per call when no lowering is named.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an importer read after its closure's lowering, read
    ///   whole, and read again after an edit of its own text answers the same
    ///   heads, and the second reading finds the closure's part kept; a hover
    ///   read before any lowering of the closure splits the heads as the
    ///   recheck after it does; a hover after a keystroke answers from the
    ///   heads its judgement read, without the copy parsing its text.
    /// - witness: `signature::tests::a_closure_s_heads_are_read_once_per_lowering_1403`
    /// - witness: `recheck::tests::a_hover_before_its_closure_is_lowered_splits_as_a_recheck_does_5198`
    /// - witness: `server::tests::a_hover_reads_the_parse_its_judgement_made_2440`
    #[spec(ensures: |ret| ret.own.windows(2).all(|pair| matches!(pair, [first, second] if first.0 < second.0)))]
    #[must_use]
    pub fn after(
        grammar: &Pbg,
        roles: &RoleTable,
        (tree, unit, base): (&SyntaxTree<'_>, &Unit, ByteOffset),
        closure: Option<&ClosureKey>,
    ) -> Self
    {
        let top = || tree.roots().iter().flat_map(|&root| tree.children(root));
        let before = |child: &NodeIndex| {
            tree.node(*child)
                .is_some_and(|node| node.span().start() < base)
        };
        let own = heads_among(
            grammar,
            roles,
            tree,
            unit,
            top().filter(|child| !before(child)),
        );
        let read = || heads_among(grammar, roles, tree, unit, top().filter(before));
        Self {
            closure: closure
                .map_or_else(|| Arc::from(read()), |closure| closure_heads(closure, read)),
            documented: parameters_documented(unit, &own),
            own,
        }
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
        [&*self.closure, self.own.as_slice()]
            .into_iter()
            .find_map(|heads| {
                let at = heads.binary_search_by(|held| held.0.cmp(&key)).ok()?;
                heads.get(at)
            })
            .map(|held| &held.1)
    }

    /// The documentation written before the parameter of one of the text's
    /// own heads whose first tile `source` writes at `named`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a documented parameter answers its run at its name
    ///   tile, and a tile no run documents answers nothing.
    /// - witness: `signature::tests::a_parameter_reads_the_documentation_written_before_it_1116`
    /// - witness: `hover::tests::a_documented_parameter_hovers_its_documentation_1116`
    #[must_use]
    pub fn parameter(
        &self,
        source: SourceIndex,
        named: ByteSpan,
    ) -> Option<SourceText<'_>>
    {
        let key = (source, named);
        let at = self
            .documented
            .binary_search_by(|held| held.0.cmp(&key))
            .ok()?;
        self.documented
            .get(at)
            .map(|held| SourceText::from(held.1.as_str()))
    }
}

/// The documentation of each parameter of `own` that has any, by the source
/// `unit` places its first tile in and that tile's span there, ascending, the
/// first for a tile kept.
///
/// # Specification
/// trivial.
///
/// # Adequacy
/// - hypothesis: L3 — documented and undocumented parameters of a list and a
///   telescope, each asserted at its exact documentation.
/// - witness: `signature::tests::a_parameter_reads_the_documentation_written_before_it_1116`
/// - witness: `hover::tests::a_documented_parameter_hovers_its_documentation_1116`
/// - witness: `signature::tests::a_run_documents_only_what_it_is_written_before_1800`
fn parameters_documented(
    unit: &Unit,
    own: &[Head],
) -> Vec<((SourceIndex, ByteSpan), String)>
{
    let mut found: Vec<((SourceIndex, ByteSpan), String)> = own
        .iter()
        .flat_map(|held| &held.1.parameters)
        .filter_map(|parameter| {
            Some((
                placed(unit, parameter.named?)?,
                parameter.documentation.clone()?,
            ))
        })
        .collect();
    found.sort_by_key(|held| held.0);
    found.dedup_by(|second, first| first.0 == second.0);
    found
}

/// The heads the forms among `children`, top-level forms of `tree` in order,
/// and every form inside them write, as [`Signatures::of`] reads them.
///
/// # Specification
/// - requires: as [`Signatures::of`]; `children` are top-level forms of `tree`,
///   in order.
/// - ensures: ascending by source, then name tile, the first head for a tile
///   kept.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Signatures::of`].
/// - witness: `signature::tests::each_head_reads_its_parameters`
#[spec(ensures: |ret| ret.windows(2).all(|pair| matches!(pair, [first, second] if first.0 < second.0)))]
fn heads_among(
    grammar: &Pbg,
    roles: &RoleTable,
    tree: &SyntaxTree<'_>,
    unit: &Unit,
    children: impl IntoIterator<Item = NodeIndex>,
) -> Vec<Head>
{
    let text = tree.source();
    let mut heads: Vec<Head> = Vec::new();
    // The roots of a forest read as the one root of the text they lay end to
    // end: their children are one level.
    let mut pending: Vec<(NodeIndex, Option<String>)> = Vec::new();
    level(grammar, tree, children, &mut pending);
    while let Some((at, carried)) = pending.pop() {
        let read = Form::of(grammar, roles, tree, at);
        if let Some(ref form) = read {
            form.heads(grammar, tree, text, carried, &mut |named, signature| {
                if let Some(key) = placed(unit, named) {
                    heads.push((key, signature));
                }
            });
        }
        level(grammar, tree, tree.children(at), &mut pending);
    }
    heads.sort_by_key(|held| held.0);
    heads.dedup_by(|second, first| first.0 == second.0);
    heads
}

/// The heads kept for the closure lowering `key` names, read by `read` and
/// kept when none are, every kept entry whose lowering nothing holds let go.
///
/// # Specification
/// - requires: `read` reads the heads of the closure's part of a tree laid
///   after the lowering `key` names.
/// - ensures: the heads kept for `key` when any are, else `read`'s, kept for
///   `key`.
/// - fails: never.
/// - panics: only by propagating a panic of `read`.
/// - executable: none — the clauses read the process's table, which the call
///   locks inside; the witness observes the second reading find the first's.
///
/// # Adequacy
/// - hypothesis: L3 — a second text laid after the same lowering takes the
///   first's heads without reading the closure's forms.
/// - witness: `signature::tests::a_closure_s_heads_are_read_once_per_lowering_1403`
fn closure_heads(
    key: &ClosureKey,
    read: impl FnOnce() -> Vec<Head>,
) -> Arc<[Head]>
{
    let kept = CLOSURE_HEADS
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .iter()
        .find(|entry| entry.0 == *key)
        .map(|entry| Arc::clone(&entry.1));
    if let Some(heads) = kept {
        return heads;
    }
    let heads: Arc<[Head]> = Arc::from(read());
    let mut kept = CLOSURE_HEADS.lock().unwrap_or_else(PoisonError::into_inner);
    kept.retain(|entry| entry.0.holding() == Holding::Held);
    kept.push((key.clone(), Arc::clone(&heads)));
    drop(kept);
    heads
}

/// Push the forms among `children`, one level of `tree`, onto `pending` so
/// that the first pops first, each with the documentation written before it
/// since the last form or tile other than a `pub` mark: in its attribute
/// blocks or as its own documentation nodes.
///
/// # Specification
/// - requires: `children` are siblings in `tree`, in order.
/// - ensures: one entry per form among them, in reverse order, each carrying
///   the documentation [`Signatures::of`] reads for it.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Signatures::of`].
/// - witness: `signature::tests::each_head_reads_its_parameters`
#[spec(captures: before = pending.len(), ensures: pending.len() >= before)]
fn level(
    grammar: &Pbg,
    tree: &SyntaxTree<'_>,
    children: impl IntoIterator<Item = NodeIndex>,
    pending: &mut Vec<(NodeIndex, Option<String>)>,
)
{
    let first = pending.len();
    let mut documented: Option<String> = None;
    for child in children {
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
            // A `pub` mark stands between a declaration's documentation and
            // the declaration it exports.
            NodeLabel::Tile(mold)
                if grammar
                    .rule_of(mold)
                    .is_ok_and(|rule| rule.name().0 == PUB_DECLARATION) => {},
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every head of the corpus sources, each asserted at
    ///   its exact label, parameters and documentation.
    /// - witness: `signature::tests::each_head_reads_its_parameters`
    /// - witness: `signature::tests::a_parameter_reads_the_documentation_written_before_it_1116`
    /// - witness: `signature::tests::a_run_documents_only_what_it_is_written_before_1800`
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
            let mut depth = Depth::default();
            for (at, &piece) in self.pieces.iter().enumerate() {
                match piece {
                    // A run inside the parentheses documents a parameter.
                    Piece::Doc(node) if depth == Depth::default() => {
                        append(&mut documented, documentation(grammar, tree, node));
                    },
                    Piece::Own(named, Some(role)) if NAMING.contains(&role) => {
                        let from = self.pieces.get(at ..).unwrap_or_default();
                        found(named, head(grammar, tree, text, from, documented.take()));
                    },
                    Piece::Own(span, _) => {
                        depth = depth.after(spelled(text, span));
                    },
                    Piece::Doc(_) | Piece::Operand(..) => {},
                }
            }
        }
        for window in self.pieces.windows(3) {
            let &[named, Piece::Own(colon, _), Piece::Operand(typed, _)] = window
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
                let label = labelled(tree, text, window);
                let parameters = label.parameters(domains);
                found(
                    tile,
                    Signature::written(label, parameters, None, Some(tile)),
                );
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

/// The parentheses open before a tile; `Depth::default()` when none is.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
#[repr(transparent)]
struct Depth(usize);

impl Depth
{
    /// The depth after the tile `written`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a run inside a parameter list and one before the
    ///   head, each asserted at the parameter or the head it documents.
    /// - witness: `signature::tests::a_parameter_reads_the_documentation_written_before_it_1116`
    /// - witness: `signature::tests::a_run_documents_only_what_it_is_written_before_1800`
    fn after(
        self,
        written: SourceText<'_>,
    ) -> Self
    {
        match <&str>::from(written) {
            "(" => Self(self.0.saturating_add(1)),
            ")" => Self(self.0.saturating_sub(1)),
            _ => self,
        }
    }
}

/// The head of `text` whose pieces start with its name `from`, documented by
/// `documentation`: the pieces up to the next name, the start of a body, the
/// `where` opening a declaration's members, the bar opening the next member,
/// or documentation outside its parentheses.
///
/// # Specification
/// trivial.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Form::heads`].
/// - witness: `signature::tests::each_head_reads_its_parameters`
/// - witness: `signature::tests::a_parameter_reads_the_documentation_written_before_it_1116`
fn head(
    grammar: &Pbg,
    tree: &SyntaxTree<'_>,
    text: SourceText<'_>,
    from: &[Piece],
    documentation: Option<String>,
) -> Signature
{
    let tail = from.get(1 ..).unwrap_or_default();
    let mut depth = Depth::default();
    let length = tail
        .iter()
        .position(|&piece| match piece {
            Piece::Own(span, role) => {
                let written = spelled(text, span);
                depth = depth.after(written);
                role.is_some_and(|role| NAMING.contains(&role))
                    || matches!(<&str>::from(written), "{" | "=" | ";" | "}" | "where" | "|")
            },
            Piece::Doc(_) => depth == Depth::default(),
            Piece::Operand(..) => false,
        })
        .unwrap_or(tail.len());
    let pieces = from.get(..= length).unwrap_or_default();
    let label = labelled(tree, text, pieces);
    let parameters = parameters(grammar, tree, text, pieces, &label);
    Signature::written(
        label,
        parameters,
        documentation,
        from.first().and_then(|piece| piece.span()),
    )
}

/// A label being written on one line from the bytes of a text, with where
/// each run it copies starts in both.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct Label
{
    /// What is written so far.
    text: String,
    /// Each run copied unchanged: its first byte in the source text and in
    /// `text`, ascending in both.
    runs: Vec<(ByteOffset, usize)>,
}

impl Label
{
    /// Copy `span` of `text` on, each stretch of layout that breaks a line or
    /// holds one of `docs` written as [`Label::space`] writes it.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — heads laid over one line and over several, each
    ///   asserted at its exact label.
    /// - witness: `signature::tests::each_head_reads_its_parameters`
    /// - witness: `signature::tests::a_parameter_reads_the_documentation_written_before_it_1116`
    /// - witness: `signature::tests::a_run_documents_only_what_it_is_written_before_1800`
    fn copy(
        &mut self,
        text: SourceText<'_>,
        span: ByteSpan,
        docs: &[ByteSpan],
    )
    {
        let text = <&str>::from(text);
        let end = usize::from(span.end());
        let mut at = usize::from(span.start());
        let doc_at = |offset| docs.iter().find(|doc| usize::from(doc.start()) == offset);
        while at < end {
            let mut layout = at;
            let mut documented = false;
            loop {
                // A documentation node is never empty; the guard keeps an empty
                // span from holding the layout where it is.
                if let Some(doc) = doc_at(layout)
                    && usize::from(doc.end()) > layout
                {
                    layout = usize::from(doc.end()).min(end);
                    documented = true;
                    continue;
                }
                match text.get(layout .. end).and_then(|rest| rest.chars().next()) {
                    Some(blank) if blank.is_whitespace() => {
                        layout = layout.saturating_add(blank.len_utf8());
                    },
                    _ => break,
                }
            }
            if layout > at {
                let blank = text.get(at .. layout).unwrap_or_default();
                if documented || blank.contains('\n') {
                    self.space(SourceText::from(text.get(layout ..).unwrap_or_default()));
                }
                else {
                    self.verbatim(ByteOffset::from(at), SourceText::from(blank));
                }
                at = layout;
                continue;
            }
            let next = text
                .get(at .. end)
                .and_then(|rest| {
                    rest.char_indices().skip(1).find(|&(offset, written)| {
                        written.is_whitespace() || doc_at(at.saturating_add(offset)).is_some()
                    })
                })
                .map_or(end, |(offset, _)| at.saturating_add(offset));
            self.verbatim(
                ByteOffset::from(at),
                SourceText::from(text.get(at .. next).unwrap_or_default()),
            );
            at = next;
        }
    }

    /// Write one space, unless the label is empty or ends one already or an
    /// opening parenthesis or bracket, or `rest`, what the text writes next,
    /// starts with a closing one or a comma.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Label::copy`].
    /// - witness: `signature::tests::each_head_reads_its_parameters`
    /// - witness: `signature::tests::a_parameter_reads_the_documentation_written_before_it_1116`
    fn space(
        &mut self,
        rest: SourceText<'_>,
    )
    {
        let rest = <&str>::from(rest);
        if !(self.text.is_empty()
            || self.text.ends_with([' ', '(', '['])
            || rest.starts_with([')', ']', ',']))
        {
            self.text.push(' ');
        }
    }

    /// Copy `written`, the bytes of the source text from `at`, on unchanged.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Label::copy`].
    /// - witness: `signature::tests::each_head_reads_its_parameters`
    /// - witness: `signature::tests::a_parameter_reads_the_documentation_written_before_it_1116`
    fn verbatim(
        &mut self,
        at: ByteOffset,
        written: SourceText<'_>,
    )
    {
        let continues = self.runs.last().is_some_and(|&(source, label)| {
            usize::from(source).saturating_add(self.text.len().saturating_sub(label))
                == usize::from(at)
        });
        if !continues {
            self.runs.push((at, self.text.len()));
        }
        self.text.push_str(<&str>::from(written));
    }

    /// Where `span` of the source text stands in the label: each end inside
    /// the run that copied it, else at the end of the last run before it.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every parameter's label range, asserted as the text
    ///   it covers in the head's label.
    /// - witness: `signature::tests::each_head_reads_its_parameters`
    /// - witness: `signature::tests::a_parameter_reads_the_documentation_written_before_it_1116`
    fn place(
        &self,
        span: ByteSpan,
    ) -> Place
    {
        let at = |offset| {
            let next = self.runs.partition_point(|&(source, _)| source <= offset);
            let Some(&(source, label)) = next.checked_sub(1).and_then(|run| self.runs.get(run))
            else {
                return 0;
            };
            let limit = self
                .runs
                .get(next)
                .map_or(self.text.len(), |&(_, start)| start);
            label
                .saturating_add(usize::from(offset).saturating_sub(usize::from(source)))
                .min(limit)
        };
        Place {
            start: at(span.start()),
            end: at(span.end()),
        }
    }

    /// Each of `entries`, bytes of the source text the label copied, as a
    /// parameter written at its place in the label.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Label::place`].
    /// - witness: `signature::tests::each_head_reads_its_parameters`
    /// - witness: `signature::tests::a_parameter_reads_the_documentation_written_before_it_1116`
    fn parameters(
        &self,
        entries: Vec<Entry>,
    ) -> Vec<Parameter>
    {
        entries
            .into_iter()
            .map(|entry| Parameter {
                place: self.place(entry.span),
                named: entry.named,
                documentation: entry.documentation,
            })
            .collect()
    }
}

/// A parameter as the source text writes it: its bytes, its first tile, and
/// the documentation written before it.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Entry
{
    /// Its bytes.
    span: ByteSpan,
    /// Its first tile.
    named: Option<ByteSpan>,
    /// The `///` run written before it.
    documentation: Option<String>,
}

/// The label `pieces` spell in `text`, on one line: each piece as
/// [`Label::copy`] writes it, joined by one space wherever `text` leaves
/// layout between them, or as [`Label::space`] writes a stretch that breaks a
/// line; documentation pieces left out.
///
/// # Specification
/// trivial.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Label::copy`].
/// - witness: `signature::tests::each_head_reads_its_parameters`
/// - witness: `signature::tests::a_parameter_reads_the_documentation_written_before_it_1116`
fn labelled(
    tree: &SyntaxTree<'_>,
    text: SourceText<'_>,
    pieces: &[Piece],
) -> Label
{
    let written = <&str>::from(text);
    let mut label = Label::default();
    let mut previous: Option<ByteSpan> = None;
    let mut docs = Vec::new();
    for &piece in pieces {
        let Some(span) = piece.span()
        else {
            continue;
        };
        if let Some(before) = previous
            && before.end() < span.start()
        {
            let rest = written
                .get(usize::from(span.start()) ..)
                .unwrap_or_default();
            let gap = written
                .get(usize::from(before.end()) .. usize::from(span.start()))
                .unwrap_or_default();
            if gap.contains('\n') {
                label.space(SourceText::from(rest));
            }
            else {
                label.text.push(' ');
            }
        }
        docs.clear();
        if let Piece::Operand(node, _) = piece
            && <&str>::from(spelled(text, span)).contains('\n')
        {
            docs_under(tree, node, &mut docs);
        }
        label.copy(text, span, &docs);
        previous = Some(span);
    }
    label
}

/// Push the span of each documentation node under `at` onto `found`, in
/// written order.
///
/// # Specification
/// trivial.
///
/// # Adequacy
/// - hypothesis: L3 — a run laid inside a parameter list is left out of the
///   label the head is answered with.
/// - witness: `signature::tests::a_parameter_reads_the_documentation_written_before_it_1116`
/// - witness: `signature::tests::a_run_documents_only_what_it_is_written_before_1800`
fn docs_under(
    tree: &SyntaxTree<'_>,
    at: NodeIndex,
    found: &mut Vec<ByteSpan>,
)
{
    // The nodes still to read, the next one last.
    let mut pending: Vec<NodeIndex> = tree.children(at).collect();
    pending.reverse();
    while let Some(child) = pending.pop() {
        match tree.node(child).map(Node::label) {
            Some(NodeLabel::Doc) => found.extend(tree.node(child).map(Node::span)),
            Some(NodeLabel::Meld(_)) => {
                let added = pending.len();
                pending.extend(tree.children(child));
                if let Some(children) = pending.get_mut(added ..) {
                    children.reverse();
                }
            },
            Some(
                NodeLabel::Tile(_)
                | NodeLabel::Wald
                | NodeLabel::Grout { .. }
                | NodeLabel::GhostClose { .. }
                | NodeLabel::Space,
            )
            | None => {},
        }
    }
}

/// The first tile under `at`, or `at` itself when it is a tile.
///
/// # Specification
/// trivial.
///
/// # Adequacy
/// - hypothesis: L3 — a documented parameter is keyed by its name tile, read
///   back at that tile.
/// - witness: `signature::tests::a_parameter_reads_the_documentation_written_before_it_1116`
/// - witness: `hover::tests::a_documented_parameter_hovers_its_documentation_1116`
/// - witness: `signature::tests::a_run_documents_only_what_it_is_written_before_1800`
fn first_tile(
    tree: &SyntaxTree<'_>,
    at: NodeIndex,
) -> Option<ByteSpan>
{
    // The nodes still to read, the next one last.
    let mut pending = vec![at];
    while let Some(next) = pending.pop() {
        let Some(node) = tree.node(next)
        else {
            continue;
        };
        match node.label() {
            NodeLabel::Tile(_) => return Some(node.span()),
            NodeLabel::Meld(_) => {
                let added = pending.len();
                pending.extend(tree.children(next));
                if let Some(children) = pending.get_mut(added ..) {
                    children.reverse();
                }
            },
            NodeLabel::Wald
            | NodeLabel::Grout { .. }
            | NodeLabel::GhostClose { .. }
            | NodeLabel::Space
            | NodeLabel::Doc => {},
        }
    }
    None
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

/// The parameters of the head `pieces` of `text`, its name first, as `label`
/// writes them: the entries of a parenthesised list after the name, or after
/// its `:`; else the domains of the function type its `:` types it by.
///
/// # Specification
/// trivial.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Form::heads`].
/// - witness: `signature::tests::each_head_reads_its_parameters`
/// - witness: `signature::tests::a_parameter_reads_the_documentation_written_before_it_1116`
fn parameters(
    grammar: &Pbg,
    tree: &SyntaxTree<'_>,
    text: SourceText<'_>,
    pieces: &[Piece],
    label: &Label,
) -> Vec<Parameter>
{
    let own = |at: usize, written: &str| matches!(pieces.get(at), Some(&Piece::Own(span, _)) if <&str>::from(spelled(text, span)) == written);
    let after = |at: usize| {
        label.parameters(entries(
            grammar,
            tree,
            text,
            pieces.get(at ..).unwrap_or_default(),
        ))
    };
    if own(1, "(") {
        return after(2);
    }
    if own(1, ":") && own(2, "(") {
        return after(3);
    }
    if own(1, ":")
        && let Some(&Piece::Operand(node, _)) = pieces.get(2)
    {
        return domains(grammar, tree, node)
            .map(|domains| label.parameters(domains))
            .unwrap_or_default();
    }
    Vec::new()
}

/// The entries of the parenthesised list of `text` whose pieces after its `(`
/// are `pieces`, each from its first piece's start to its last piece's end,
/// documented by the documentation pieces before its first.
///
/// # Specification
/// trivial.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Form::heads`].
/// - witness: `signature::tests::each_head_reads_its_parameters`
/// - witness: `signature::tests::a_parameter_reads_the_documentation_written_before_it_1116`
/// - witness: `signature::tests::a_run_documents_only_what_it_is_written_before_1800`
/// - witness: `signature::tests::only_a_function_type_and_a_list_s_own_separators_make_parameters_1810`
fn entries(
    grammar: &Pbg,
    tree: &SyntaxTree<'_>,
    text: SourceText<'_>,
    pieces: &[Piece],
) -> Vec<Entry>
{
    let mut found = Vec::new();
    let mut entry: Option<Entry> = None;
    let mut documented: Option<String> = None;
    let mut depth = Depth::default();
    for &piece in pieces {
        let (span, named) = match piece {
            Piece::Doc(node) => {
                if depth == Depth::default() {
                    append(&mut documented, documentation(grammar, tree, node));
                }
                continue;
            },
            Piece::Own(span, _) => {
                let written = <&str>::from(spelled(text, span));
                match written {
                    "," | ")" if depth == Depth::default() => {
                        found.extend(entry.take());
                        documented = None;
                        if written == ")" {
                            break;
                        }
                        continue;
                    },
                    _ => depth = depth.after(SourceText::from(written)),
                }
                (span, Some(span))
            },
            Piece::Operand(node, span) => (span, first_tile(tree, node)),
        };
        entry = Some(match entry {
            Some(first) => Entry {
                span: first.span.join(span),
                ..first
            },
            None => Entry {
                span,
                named,
                documentation: documented.take(),
            },
        });
    }
    found
}

/// Each parameter the function type at `at` takes, read through the thunks
/// and parentheses around it, outermost first: each entry of the
/// parenthesised telescope before each `->`, with its documentation, or the
/// domain whole when it is no telescope; none when `at` is no function type.
///
/// # Specification
/// trivial.
///
/// # Adequacy
/// - hypothesis: L3 — a binder typed by a function, a constructor's telescope
///   and a type returning a function, each asserted at its parameters.
/// - witness: `signature::tests::each_head_reads_its_parameters`
/// - witness: `signature::tests::only_a_function_type_and_a_list_s_own_separators_make_parameters_1810`
fn domains(
    grammar: &Pbg,
    tree: &SyntaxTree<'_>,
    at: NodeIndex,
) -> Option<Vec<Entry>>
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

/// Each entry of the telescope at `at`: each run between the parentheses and
/// commas a parenthesised type owns, documented by the documentation nodes
/// written before it, or `at` whole when it is no parenthesised type.
///
/// # Specification
/// trivial.
///
/// # Adequacy
/// - hypothesis: L3 — a constructor's telescope, documented and not, asserted
///   at each parameter.
/// - witness: `signature::tests::each_head_reads_its_parameters`
/// - witness: `signature::tests::a_parameter_reads_the_documentation_written_before_it_1116`
fn telescope(
    grammar: &Pbg,
    tree: &SyntaxTree<'_>,
    at: NodeIndex,
) -> Vec<Entry>
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
        return Vec::from([Entry {
            span: node.span(),
            named: None,
            documentation: None,
        }]);
    }
    let mut found = Vec::new();
    let mut entry: Option<Entry> = None;
    let mut documented: Option<String> = None;
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
            NodeLabel::Doc => {
                if entry.is_none() {
                    append(&mut documented, documentation(grammar, tree, child));
                }
                continue;
            },
            NodeLabel::Wald
            | NodeLabel::Grout { .. }
            | NodeLabel::GhostClose { .. }
            | NodeLabel::Space => continue,
        };
        if delimits {
            found.extend(entry.take());
            documented = None;
        }
        else {
            entry = Some(match entry {
                Some(first) => Entry {
                    span: first.span.join(held.span()),
                    ..first
                },
                None => Entry {
                    span: held.span(),
                    named: first_tile(tree, child),
                    documentation: documented.take(),
                },
            });
        }
    }
    found
}

/// What asked for signature help: the author or a character that opens or
/// separates arguments, or a space typed after a head.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Opened
{
    /// The author, or `(` or `,`: the help answers every spine.
    Asked,
    /// A space: the help answers only while the innermost spine's declared head
    /// takes a parameter at its slot.
    Spaced,
}

/// One spine a position stands in, as the faces read it: the frame, and the
/// declared head its head refers to when the hovering keeps one.
#[derive(Clone, Copy, Debug)]
struct Spine<'hovering>
{
    /// The head, the slot and the argument written in the slot.
    frame: Frame,
    /// The declared head that the head refers to.
    declared: Option<&'hovering Signature>,
}

impl Spine<'_>
{
    /// The parameter of the declared head that the slot fills; none past the
    /// last parameter and with no declared head.
    ///
    /// # Specification
    /// trivial.
    fn filled(&self) -> Option<&Parameter>
    {
        self.declared?.parameters.get(usize::from(self.frame.slot))
    }
}

/// The spines that `at`, a byte of `text`, stands in, from the innermost
/// outward, `text` read as `reading` reads it and kept as `hovering` keeps it.
///
/// # Specification
/// - requires: `reading` and `hovering` were read off `text`.
/// - ensures: the spines of [`Reading::frames`] at `at`, each with the declared
///   head the type table refers its head's first byte to, when the hovering
///   keeps one. When spaces or tabs come just before `at`, one spine more opens
///   before them, unless the frames hold its head already. That spine is the
///   innermost spine whose argument ends where those blanks start, at its next
///   slot. With no such spine, it is the use that ends there, at its first
///   slot. It opens only while its declared head takes a parameter at that
///   slot.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a space after a head, after an argument a head still
///   owes, after a saturated call, and inside a nested call, each asserted at
///   its exact signatures; every position of a closed and an open call agrees
///   with the context stack.
/// - witness: `server::tests::a_space_opens_the_help_while_the_spine_owes_an_argument_4697`
/// - witness: `server::tests::the_context_stack_agrees_with_the_hover_and_the_signature_help`
#[spec(ensures: |ret| ret.len() <= reading.frames(at).count().saturating_add(1))]
fn spines<'hovering>(
    text: SourceText<'_>,
    reading: &Reading,
    hovering: &'hovering Hovering,
    at: ByteOffset,
) -> Vec<Spine<'hovering>>
{
    let spine = |frame: Frame| Spine {
        declared: declared(hovering, frame.head),
        frame,
    };
    let mut found: Vec<Spine<'hovering>> = reading.frames(at).map(spine).collect();
    let start = usize::from(at);
    let before = <&str>::from(text)
        .get(.. start)
        .map_or(start, |written| written.trim_end_matches([' ', '\t']).len());
    if before == start {
        return found;
    }
    let blank = ByteOffset::from(before);
    let ended = reading.frames(blank).find(|frame| {
        frame
            .argument
            .is_some_and(|argument| argument.end() == blank)
    });
    let opened = if let Some(frame) = ended {
        Frame {
            slot: Slot::from(usize::from(frame.slot).saturating_add(1)),
            argument: None,
            ..frame
        }
    }
    else {
        let Some(last) = before.checked_sub(1)
        else {
            return found;
        };
        match hovering.table().referent(ByteOffset::from(last)) {
            Maybe::Present((head, _)) if head.end() == blank => Frame {
                head,
                slot: Slot::from(0_usize),
                argument: None,
            },
            Maybe::Present(_) | Maybe::Absent(_) => return found,
        }
    };
    let opened = spine(opened);
    if opened.filled().is_some()
        && found
            .iter()
            .all(|held| held.frame.head != opened.frame.head)
    {
        found.insert(0, opened);
    }
    found
}

/// The type the judgement gives the term at the first byte of `head`, when
/// that term lies inside `head`, on one line in `style` as the hover spells it
/// on a page wider than every line ([`TypeTable::at_line`]).
///
/// [`TypeTable::at_line`]: gandr_surface_dispatcher::TypeTable::at_line
///
/// # Specification
/// trivial.
fn head_type(
    hovering: &Hovering,
    head: ByteSpan,
    style: Style,
) -> Option<String>
{
    match hovering.table().at_line(head.start(), style) {
        Maybe::Present(ref typed) if inside(typed, head).is_some() => {
            Some(String::from(typed.ty().as_ref()))
        },
        Maybe::Present(_) | Maybe::Absent(_) => None,
    }
}

/// Some when `typed` lies inside `within`.
///
/// # Specification
/// trivial.
fn inside(
    typed: &TypedSpan,
    within: ByteSpan,
) -> Option<()>
{
    (within.start() <= typed.span().start() && typed.span().end() <= within.end()).then_some(())
}

/// The type the judgement checked the outermost term of `argument` against
/// ([`TypeTable::outermost`]), its own type when it was checked against no
/// other, on one line in `style`; none for no argument or one the table types
/// no term inside.
///
/// [`TypeTable::outermost`]: gandr_surface_dispatcher::TypeTable::outermost
///
/// # Specification
/// trivial.
fn expected(
    hovering: &Hovering,
    argument: Option<ByteSpan>,
    style: Style,
) -> Option<String>
{
    match hovering.table().outermost(argument?, style) {
        Maybe::Present(ref typed) => Some(String::from(match typed.expected() {
            Maybe::Present(checked) => checked.as_ref(),
            Maybe::Absent(_) => typed.ty().as_ref(),
        })),
        Maybe::Absent(_) => None,
    }
}

/// The bytes of `head` in `text`.
///
/// # Specification
/// trivial.
fn written(
    text: SourceText<'_>,
    head: ByteSpan,
) -> Option<SourceText<'_>>
{
    <&str>::from(text)
        .get(usize::from(head.start()) .. usize::from(head.end()))
        .map(SourceText::from)
}

/// The signature of `spine` of `text` to a client that takes a parameter as
/// its place in the label when `offsets` holds: its declared head, or the head
/// as written with the type `hovering` gives it in `style` when it has none.
///
/// # Specification
/// trivial.
fn informed(
    text: SourceText<'_>,
    hovering: &Hovering,
    spine: &Spine<'_>,
    offsets: LabelOffsets,
    style: Style,
) -> SignatureInformation
{
    let Some(signature) = spine.declared
    else {
        let head = written(text, spine.frame.head).map_or("", <&str>::from);
        return SignatureInformation {
            label: head_type(hovering, spine.frame.head, style)
                .map_or_else(|| String::from(head), |ty| format!("{head} : {ty}")),
            documentation: None,
            parameters: Vec::new(),
            active_parameter: None,
        };
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
        .map(|parameter| {
            let Place { start, end } = parameter.place;
            ParameterInformation {
                label: if offsets.0 {
                    ParameterLabel::Offsets([units(start), units(end)])
                }
                else {
                    ParameterLabel::Text(String::from(
                        signature.label.get(start .. end).unwrap_or_default(),
                    ))
                },
                documentation: parameter
                    .documentation
                    .as_ref()
                    .map(|documented| MarkupContent {
                        kind: "markdown",
                        value: documented.clone(),
                    }),
            }
        })
        .collect();
    SignatureInformation {
        label: signature.label.clone(),
        documentation: signature
            .documentation
            .as_ref()
            .map(|documented| MarkupContent {
                kind: "markdown",
                value: documented.clone(),
            }),
        parameters,
        active_parameter: spine
            .filled()
            .and_then(|_| u32::try_from(usize::from(spine.frame.slot)).ok()),
    }
}

/// What a signature-help request at `position` of `text`, whose reading is
/// `reading` and whose copy keeps `hovering`, answers to a client that takes
/// a parameter as its place in the label when `offsets` holds, each type
/// spelled in `style`, asked as `opened` says.
///
/// # Specification
/// - requires: `reading` and `hovering` were read off `text`.
/// - ensures: one signature for each spine the position stands in ([`spines`]),
///   from the innermost outward, the first active. A spine whose head the type
///   table refers to a declaration or constructor whose head the hovering keeps
///   answers that head, with its documentation as markdown and each parameter
///   as its start and end in the label counted in UTF-16 code units when
///   `offsets` holds or as its text otherwise, with the documentation written
///   before it as markdown when it has any. Its active parameter is the one its
///   slot fills, `null` past the last parameter. Another spine answers its head
///   as written, then ` : ` and the type the judgement gives the head when it
///   gives one, with no parameters. The help's active parameter is the first
///   signature's. Nothing when the position stands in no spine, and nothing for
///   [`Opened::Spaced`] unless the innermost spine's declared head takes a
///   parameter at its slot.
/// - provides: the answer to `textDocument/signatureHelp`.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a function's juxtaposed call at each argument, a
///   constructor applied to no field yet, a nested call, a position past the
///   last parameter, a call of a sibling's declaration and a position in no
///   call are each asserted at their exact answer; a space after a head that
///   owes an argument opens the help, and one after a saturated call does not.
/// - witness: `server::tests::signature_help_answers_the_declared_head_of_the_call`
/// - witness: `tests::session::signature_help_reads_a_sibling_s_head`
/// - witness: `server::tests::signature_help_sends_a_parameter_s_documentation_1116`
/// - witness: `server::tests::a_space_opens_the_help_while_the_spine_owes_an_argument_4697`
#[spec(ensures: |ret| matches!(ret, Answer::Nothing | Answer::Signatures(_)))]
#[must_use]
pub fn help(
    text: SourceText<'_>,
    reading: &Reading,
    hovering: &Hovering,
    position: Position,
    (offsets, style): (LabelOffsets, Style),
    opened: Opened,
) -> Answer
{
    let index = LineIndex::new(<&str>::from(text).into());
    let at = ByteOffset::from(usize::from(position.byte(&index)));
    let spines = spines(text, reading, hovering, at);
    let Some(innermost) = spines.first()
    else {
        return Answer::Nothing;
    };
    if opened == Opened::Spaced && innermost.filled().is_none() {
        return Answer::Nothing;
    }
    let signatures: Vec<SignatureInformation> = spines
        .iter()
        .map(|spine| informed(text, hovering, spine, offsets, style))
        .collect();
    Answer::Signatures(SignatureHelp {
        active_parameter: signatures.first().and_then(|first| first.active_parameter),
        signatures,
        active_signature: 0,
    })
}

/// The declared head of the declaration or constructor the head at `head`
/// refers to, when the hovering keeps one.
///
/// # Specification
/// trivial.
fn declared(
    hovering: &Hovering,
    head: ByteSpan,
) -> Option<&Signature>
{
    let Maybe::Present((_, referent)) = hovering.table().referent(head.start())
    else {
        return None;
    };
    hovering.signatures().declared(&referent)
}

/// What a `gandr/stack` request at `position` of `text`, whose reading is
/// `reading` and whose copy keeps `hovering`, answers: each spine the position
/// stands in, from the innermost outward, each type spelled in `style` on one
/// line.
///
/// # Specification
/// - requires: `reading` and `hovering` were read off `text`.
/// - ensures: one row for each spine the position stands in ([`spines`]), in
///   its order. A row holds the head as written and its range, and the type the
///   table gives the term at the head's first byte when that term lies inside
///   the head, as the hover spells it on a page wider than every line
///   ([`TypeTable::at_line`]). It holds the declared head and its count of
///   parameters when the table refers the head's first byte to a declaration or
///   constructor whose head the hovering keeps. It holds the slot, and the type
///   the judgement checked the outermost term of the slot's argument against
///   ([`TypeTable::outermost`]), its own type when it was checked against no
///   other. That type is none, which reads owed, when the slot writes no
///   argument or the table types no term inside it.
/// - provides: the answer to `gandr/stack`.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — at every position of a closed call and of an open one,
///   each row agrees with the hover at its head, and the rows with the
///   signatures of the signature help.
/// - witness: `server::tests::the_context_stack_agrees_with_the_hover_and_the_signature_help`
///
/// [`TypeTable::at_line`]: gandr_surface_dispatcher::TypeTable::at_line
/// [`TypeTable::outermost`]: gandr_surface_dispatcher::TypeTable::outermost
#[spec(ensures: |ret| matches!(ret, Answer::Stack(_)))]
#[must_use]
pub fn stack(
    text: SourceText<'_>,
    reading: &Reading,
    hovering: &Hovering,
    position: Position,
    style: Style,
) -> Answer
{
    let index = LineIndex::new(<&str>::from(text).into());
    let at = ByteOffset::from(usize::from(position.byte(&index)));
    Answer::Stack(
        spines(text, reading, hovering, at)
            .into_iter()
            .filter_map(|spine| {
                Some(StackRow {
                    range: ranged(&index, spine.frame.head)?,
                    head: String::from(<&str>::from(written(text, spine.frame.head)?)),
                    ty: head_type(hovering, spine.frame.head, style),
                    declared: spine.declared.map(|declared| declared.label.clone()),
                    arity: spine
                        .declared
                        .and_then(|declared| u32::try_from(declared.parameters.len()).ok()),
                    slot: u32::try_from(usize::from(spine.frame.slot)).unwrap_or(u32::MAX),
                    expected: expected(hovering, spine.frame.argument, style),
                })
            })
            .collect(),
    )
}

/// The stack card at `position` of `text`, whose reading is `reading` and
/// whose copy keeps `hovering`, each type spelled in `style` on one line.
///
/// # Specification
/// - requires: `reading` and `hovering` were read off `text`.
/// - ensures: the card at the position's byte offset, one row for each spine
///   the position stands in ([`spines`]), in its order. A row holds the head as
///   written, the slot, and the expected type as [`stack`] answers them. A
///   spine with a declared head holds its arity, and as its type the declared
///   head past its name and the `:` after it, with the run that the parameter
///   at its slot writes there. Another spine holds the type the judgement gives
///   its head, with no run.
/// - provides: the card the render bus sends for the cursor of a document.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an attached view hears the card of the cursor the
///   editor's signature help names, its innermost row's run the parameter its
///   slot fills, and a card again once an edit changes the stack there.
/// - witness: `hub::tests::an_attached_view_follows_the_stack_at_the_editors_cursor`
#[spec(ensures: |ret| ret.rows.iter().all(|row| row.filled.is_none() || row.ty.is_some()))]
#[must_use]
pub fn card(
    text: SourceText<'_>,
    reading: &Reading,
    hovering: &Hovering,
    position: Position,
    style: Style,
) -> StackCard
{
    let index = LineIndex::new(<&str>::from(text).into());
    let at = ByteOffset::from(usize::from(position.byte(&index)));
    let count = |value: usize| Count(u64::try_from(value).unwrap_or(u64::MAX));
    let rows = spines(text, reading, hovering, at)
        .into_iter()
        .filter_map(|spine| {
            let head = String::from(<&str>::from(written(text, spine.frame.head)?));
            let (ty, filled) = spine.declared.map_or_else(
                || (head_type(hovering, spine.frame.head, style), None),
                |signature| {
                    let filled = spine.filled().and_then(|parameter| {
                        let shifted = |offset: usize| {
                            offset
                                .checked_sub(signature.typed)
                                .map(gandr_surface_render_remote::ByteOffset::from)
                        };
                        gandr_surface_render_remote::ByteRange::new(
                            shifted(parameter.place.start)?,
                            shifted(parameter.place.end)?,
                        )
                        .ok()
                    });
                    (
                        signature.label.get(signature.typed ..).map(String::from),
                        filled,
                    )
                },
            );
            Some(SpineRow {
                head,
                ty,
                filled,
                slot: count(usize::from(spine.frame.slot)),
                arity: spine
                    .declared
                    .map(|declared| count(declared.parameters.len())),
                expected: expected(hovering, spine.frame.argument, style),
            })
        })
        .collect();
    StackCard {
        offset: gandr_surface_render_remote::ByteOffset::from(usize::from(at)),
        rows,
    }
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;
    use alloc::vec::Vec;

    use gandr_surface_lowering::Unit;
    use gandr_surface_parser::parse;
    use gandr_surface_syntax::SourceText;

    use super::Signatures;
    use crate::toolkit::grammar;
    use crate::toolkit::roles;

    /// #1403: an importer's heads, read after its closure's lowering, are the
    /// heads read off its whole tree, and a second reading after the same
    /// lowering takes the closure's part kept instead of walking its forms.
    #[test]
    fn a_closure_s_heads_are_read_once_per_lowering_1403()
    {
        use alloc::sync::Arc;

        use gandr_surface_diagnostics::Verbosity;
        use gandr_surface_lsp_base::quiet::formless;
        use gandr_surface_pretty::Spelling;
        use quenchant_shape::shape::Maybe;

        use crate::protocol::DocumentUri;
        use crate::recheck::open;
        use crate::recheck::recheck;

        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../corpus/model/identity/circle-elim.gandr");
        let written = std::fs::read_to_string(&path).expect("the corpus importer is read");
        let text = SourceText::from(written.as_str());
        let uri = DocumentUri::from(format!("file://{}", path.display()).as_str());
        let mut session = open(&uri, &Arc::default());
        let rechecked = recheck(
            &uri,
            &mut session,
            text,
            &gandr_surface_dispatcher::Unshadowed,
            Verbosity::User,
            Spelling::Unicode,
            Maybe::Absent(formless::Absent::Uncareted),
        );
        let Maybe::Present(laid) = rechecked.laid
        else {
            panic!("the importer is laid out after its closure");
        };
        let session = session.expect("the grammar builds");
        let grammar = grammar().expect("the grammar builds");
        let roles = roles().expect("the roles build");
        let mut read = None;
        let _table = session.type_held_unit(
            SourceText::from(laid.text.as_str()),
            (&laid.unit, laid.base),
            |tree, closure| {
                let key = closure.expect("the process holds the closure's lowering");
                let after =
                    Signatures::after(grammar, roles, (tree, &laid.unit, laid.base), Some(&key));
                let whole = Signatures::of(grammar, roles, tree, &laid.unit);
                let again = super::closure_heads(&key, || {
                    panic!("a closure whose heads are kept is not walked again")
                });
                read = Some((after, whole, again));
            },
        );
        let (after, whole, again) = read.expect("the laid revision parses");
        assert!(
            !after.closure.is_empty() && !after.own.is_empty(),
            "the closure and the importer each declare heads"
        );
        assert_eq!(
            after
                .closure
                .iter()
                .chain(&after.own)
                .cloned()
                .collect::<Vec<_>>(),
            whole.own,
            "the closure's heads then the importer's are the whole tree's"
        );
        assert!(
            Arc::ptr_eq(&after.closure, &again),
            "the second reading takes the heads the first kept"
        );
    }

    #[test]
    fn each_head_reads_its_parameters()
    {
        // `plus`'s head stays over two lines, so a label reads its layout
        // collapsed.
        let text = include_str!("signature/unformatted/heads.gandr");
        let grammar = grammar().expect("the grammar builds");
        let roles = roles().expect("the roles build");
        let parsed = parse(grammar, SourceText::from(text)).expect("the text parses");
        let heads = Signatures::of(grammar, roles, parsed.tree(), &Unit::single());
        let read: Vec<(String, String, Vec<String>, Option<String>)> = heads
            .own
            .iter()
            .map(|&((_, named), ref signature)| {
                let name = text
                    .get(usize::from(named.start()) .. usize::from(named.end()))
                    .unwrap_or_default();
                let parameters = signature
                    .parameters
                    .iter()
                    .map(|parameter| {
                        let super::Place { start, end } = parameter.place;
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
                "r : *{ sub : +U (Nat -> Nat -> -F Type), subTm : (g : Nat, t : sub(g, g)) -> Nat }",
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
                "subTm : (g : Nat, t : sub(g, g)) -> Nat",
                &["g : Nat", "t : sub(g, g)"],
                None
            ),
        ]);
    }

    /// #1116: a `///` run written before a parameter documents it, in a
    /// declaration's parameter list and in a constructor's telescope, and a
    /// list laid over lines labels as one line.
    #[test]
    fn a_parameter_reads_the_documentation_written_before_it_1116()
    {
        // A head as read: its name, its label, each parameter's text with
        // its documentation, and the head's documentation.
        type Read = (
            String,
            String,
            Vec<(String, Option<String>)>,
            Option<String>,
        );
        let text = include_str!("signature/fixtures/documented-parameters.gandr");
        let grammar = grammar().expect("the grammar builds");
        let roles = roles().expect("the roles build");
        let parsed = parse(grammar, SourceText::from(text)).expect("the text parses");
        let heads = Signatures::of(grammar, roles, parsed.tree(), &Unit::single());
        let read: Vec<Read> = heads
            .own
            .iter()
            .map(|&((_, named), ref signature)| {
                let name = text
                    .get(usize::from(named.start()) .. usize::from(named.end()))
                    .unwrap_or_default();
                let parameters = signature
                    .parameters
                    .iter()
                    .map(|parameter| {
                        (
                            String::from(
                                signature
                                    .label
                                    .get(parameter.place.start .. parameter.place.end)
                                    .unwrap_or_default(),
                            ),
                            parameter.documentation.clone(),
                        )
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
        let documented = |parameter: &str, documentation: Option<&str>| {
            (String::from(parameter), documentation.map(String::from))
        };
        assert_eq!(read, [
            (
                String::from("Nat"),
                String::from("Nat : Type"),
                Vec::new(),
                None
            ),
            (
                String::from("Zero"),
                String::from("Zero : Nat"),
                Vec::new(),
                None
            ),
            (
                String::from("Succ"),
                String::from("Succ : (n : Nat) --> Nat"),
                Vec::from([documented("n : Nat", Some("The predecessor."))]),
                Some(String::from("One more.")),
            ),
            (
                String::from("plus"),
                String::from("plus(n : Nat, m : Nat, k : Nat) -> -F Nat"),
                Vec::from([
                    documented("n : Nat", Some("The first summand.")),
                    documented("m : Nat", Some("The second\nsummand.")),
                    documented("k : Nat", None),
                ]),
                Some(String::from("Addition.")),
            ),
        ]);
    }

    /// A run documents the one parameter or member written after it: not the
    /// member after a documented telescope, not a function type's domain it
    /// sits inside, which the label leaves out; a parameter whose type holds a
    /// comma is one parameter; the documented parameters are keyed by their
    /// name tiles.
    #[test]
    fn a_run_documents_only_what_it_is_written_before_1800()
    {
        let text = include_str!("signature/fixtures/documented-runs.gandr");
        let grammar = grammar().expect("the grammar builds");
        let roles = roles().expect("the roles build");
        let parsed = parse(grammar, SourceText::from(text)).expect("the text parses");
        let heads = Signatures::of(grammar, roles, parsed.tree(), &Unit::single());
        let spelled = |span: super::ByteSpan| {
            text.get(usize::from(span.start()) .. usize::from(span.end()))
                .unwrap_or_default()
        };
        let read: Vec<_> = heads
            .own
            .iter()
            .map(|&((_, named), ref signature)| {
                let parameters: Vec<_> = signature
                    .parameters
                    .iter()
                    .map(|parameter| {
                        (
                            signature
                                .label
                                .get(parameter.place.start .. parameter.place.end)
                                .unwrap_or_default(),
                            parameter.documentation.as_deref(),
                        )
                    })
                    .collect();
                (
                    spelled(named),
                    signature.label.as_str(),
                    parameters,
                    signature.documentation.as_deref(),
                )
            })
            .collect();
        assert_eq!(read, [
            ("Nat", "Nat : Type", Vec::new(), None),
            ("Zero", "Zero : Nat", Vec::new(), None),
            (
                "Succ",
                "Succ : (n : Nat) --> Nat",
                Vec::from([("n : Nat", Some("The predecessor."))]),
                None
            ),
            ("Two", "Two : Nat", Vec::new(), None),
            ("Three", "Three : Nat", Vec::new(), Some("Three.")),
            (
                "apply",
                "apply(f : (x : Nat) -> -F Nat, p : (a : Nat, b : Nat), y : Nat) -> -F Nat",
                Vec::from([
                    ("f : (x : Nat) -> -F Nat", None),
                    ("p : (a : Nat, b : Nat)", Some("The pair.")),
                    ("y : Nat", None),
                ]),
                None
            ),
            (
                "f",
                "f : (x : Nat) -> -F Nat",
                Vec::from([("x : Nat", Some("The argument."))]),
                None
            ),
            (
                "use",
                "use(h : (i : Nat) -> Nat) -> -F Nat",
                Vec::from([("h : (i : Nat) -> Nat", None)]),
                None
            ),
            (
                "h",
                "h : (i : Nat) -> Nat",
                Vec::from([("i : Nat", Some("The index."))]),
                None
            ),
        ]);
        let documented: Vec<_> = heads
            .documented
            .iter()
            .map(|&((_, named), ref documentation)| (spelled(named), documentation.as_str()))
            .collect();
        assert_eq!(documented, [
            ("n", "The predecessor."),
            ("x", "The argument."),
            ("p", "The pair."),
            ("i", "The index.")
        ]);
    }

    /// #1810: a list's own parentheses nested inside a parameter, as a
    /// binder writes them, keep the parameter whole, and a type returning a
    /// function is no function type, so its head takes no parameter.
    #[test]
    fn only_a_function_type_and_a_list_s_own_separators_make_parameters_1810()
    {
        let text = include_str!(
            "signature/unformatted/only-a-function-type-and-a-list-s-own-separators-make-parameters-1810.gandr"
        );
        let grammar = grammar().expect("the grammar builds");
        let roles = roles().expect("the roles build");
        let parsed = parse(grammar, SourceText::from(text)).expect("the text parses");
        let heads = Signatures::of(grammar, roles, parsed.tree(), &Unit::single());
        let read: Vec<_> = heads
            .own
            .iter()
            .map(|&((_, named), ref signature)| {
                let parameters: Vec<_> = signature
                    .parameters
                    .iter()
                    .map(|parameter| {
                        signature
                            .label
                            .get(parameter.place.start .. parameter.place.end)
                            .unwrap_or_default()
                    })
                    .collect();
                (
                    text.get(usize::from(named.start()) .. usize::from(named.end()))
                        .unwrap_or_default(),
                    signature.label.as_str(),
                    parameters,
                )
            })
            .collect();
        assert_eq!(read, [
            ("Lambda", "Lambda", Vec::new()),
            ("Tm", "Tm : Type", Vec::new()),
            (
                "lam",
                "lam : (t : pi+ (x : Tm) . Tm) --> Tm",
                Vec::from(["t : pi+ (x : Tm) . Tm"])
            ),
            (
                "app",
                "app : (t : Tm, u : Tm) --> Tm",
                Vec::from(["t : Tm", "u : Tm"])
            ),
            ("g", "g : -F (Nat -> -F Nat)", Vec::new()),
        ]);
    }
}
