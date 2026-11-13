//! The heads of a text: the head of each declaration and constructor, read
//! off its declaring form, and the signature that a client is answered with.
//!
//! A head is the name through its parameters and its result, on one line. It
//! holds the place of each parameter in that label, with the `///` run
//! written before the parameter, and the documentation written for the head.
//! The heads are read off the parse that a text already makes. The `signature`
//! module of `gandr-surface-lsp` keeps them by the source and the name tile of
//! each. It reads the heads of a closure once per closure lowering, and it
//! answers signature help and the context stack from them. This module reads
//! neither the dispatcher nor the session.
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

use alloc::string::String;
use alloc::vec::Vec;
use core::fmt::Write as _;

use anodized::spec;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::RoleTable;
use gandr_surface_grammar::Sort;
use gandr_surface_lowering::Documentation;
use gandr_surface_lowering::SourceIndex;
use gandr_surface_lowering::Unit;
use gandr_surface_lowering::read_doc;
use gandr_surface_render_remote::ByteRange;
use gandr_surface_render_remote::HlRole;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::Node;
use gandr_surface_syntax::NodeIndex;
use gandr_surface_syntax::NodeLabel;
use gandr_surface_syntax::SourceText;
use gandr_surface_syntax::SyntaxTree;

use crate::inline::escape_into;
use crate::protocol::LabelOffsets;
use crate::protocol::MarkupContent;
use crate::protocol::ParameterInformation;
use crate::protocol::ParameterLabel;
use crate::protocol::SignatureInformation;

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
    #[must_use]
    #[inline]
    pub fn label(&self) -> SourceText<'_>
    {
        SourceText::from(self.label.as_str())
    }

    /// The documentation written for the declaration or constructor.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub fn documentation(&self) -> Option<SourceText<'_>>
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
    /// - witness: `gandr-surface-lsp::complete::tests::a_call_fills_its_parameters_as_tab_stops`
    #[spec(ensures: |ret| ret.is_none() == self.parameters.is_empty()
        && ret.as_ref().is_none_or(|snippet| snippet.ends_with("$0")
            && snippet.matches("${").count() >= self.parameters.len()))]
    #[must_use]
    #[inline]
    pub fn called(
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

    /// Each parameter, in written order: the run that it writes in the label,
    /// and the documentation written before it.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub fn parameters(
        &self
    ) -> impl ExactSizeIterator<Item = (SourceText<'_>, Option<SourceText<'_>>)>
    {
        self.parameters.iter().map(|parameter| {
            (
                SourceText::from(
                    self.label
                        .get(parameter.place.start .. parameter.place.end)
                        .unwrap_or_default(),
                ),
                parameter.documentation.as_deref().map(SourceText::from),
            )
        })
    }

    /// Its type: the label past the name, the layout after the name, and a
    /// `:` with the layout after it.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub fn ty(&self) -> Option<SourceText<'_>>
    {
        self.label.get(self.typed ..).map(SourceText::from)
    }

    /// The run that the parameter at `slot` writes in the type, counted from
    /// the start of the type. None past the last parameter, and none for a
    /// run that starts before the type.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub fn run(
        &self,
        ParameterSlot(slot): ParameterSlot,
    ) -> Option<ByteRange>
    {
        let parameter = self.parameters.get(slot)?;
        let shifted = |offset: usize| {
            offset
                .checked_sub(self.typed)
                .map(gandr_surface_render_remote::ByteOffset::from)
        };
        ByteRange::new(
            shifted(parameter.place.start)?,
            shifted(parameter.place.end)?,
        )
        .ok()
    }

    /// The signature that a client is answered with: the label, the
    /// documentation as markdown, and each parameter with the documentation
    /// written before it as markdown. A parameter is its start and its end in
    /// the label, in UTF-16 code units, when `offsets` holds, and its text
    /// otherwise. The active parameter is `active`, when the wire can count
    /// it.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub fn information(
        &self,
        offsets: LabelOffsets,
        active: Option<ParameterSlot>,
    ) -> SignatureInformation
    {
        let units = |bytes: usize| {
            u32::try_from(
                self.label
                    .get(.. bytes)
                    .unwrap_or_default()
                    .encode_utf16()
                    .count(),
            )
            .unwrap_or(u32::MAX)
        };
        let parameters: Vec<ParameterInformation> = self
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
                            self.label.get(start .. end).unwrap_or_default(),
                        ))
                    },
                    documentation: parameter.documentation.as_ref().map(|documented| {
                        MarkupContent {
                            kind: "markdown",
                            value: documented.clone(),
                        }
                    }),
                }
            })
            .collect();
        SignatureInformation {
            label: self.label.clone(),
            documentation: self.documentation.as_ref().map(|documented| MarkupContent {
                kind: "markdown",
                value: documented.clone(),
            }),
            parameters,
            active_parameter: active.and_then(|ParameterSlot(slot)| u32::try_from(slot).ok()),
        }
    }
}

/// The place of a parameter among the parameters of a head, counted from the
/// first.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ParameterSlot(pub usize);

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
pub type Head = ((SourceIndex, ByteSpan), Signature);

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
/// - witness: `gandr-surface-lsp::signature::tests::a_parameter_reads_the_documentation_written_before_it_1116`
/// - witness: `gandr-surface-lsp::hover::tests::a_documented_parameter_hovers_its_documentation_1116`
/// - witness: `gandr-surface-lsp::signature::tests::a_run_documents_only_what_it_is_written_before_1800`
#[must_use]
#[inline]
pub fn parameters_documented(
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

/// The heads that the forms among `children` write.
///
/// The forms are top-level forms of `tree` in order, with every form inside
/// them, read as the module documentation's table reads them. Each head is
/// keyed by the source holding its name and the name's span in that source's
/// own text.
///
/// # Specification
/// - requires: `tree` was parsed under `grammar` over the text `unit` lays out;
///   `children` are top-level forms of `tree`, in order.
/// - ensures: ascending by source, then name tile, the first head for a tile
///   kept.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Form::heads`].
/// - witness: `gandr-surface-lsp::signature::tests::each_head_reads_its_parameters`
#[spec(ensures: |ret| ret.windows(2).all(|pair| matches!(pair, [first, second] if first.0 < second.0)))]
#[must_use]
#[inline]
pub fn heads_among<Children>(
    grammar: &Pbg,
    roles: &RoleTable,
    tree: &SyntaxTree<'_>,
    unit: &Unit,
    children: Children,
) -> Vec<Head>
where
    Children: IntoIterator<Item = NodeIndex>,
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

/// Push the forms among `children`, one level of `tree`, onto `pending` so
/// that the first pops first, each with the documentation written before it
/// since the last form or tile other than a `pub` mark: in its attribute
/// blocks or as its own documentation nodes.
///
/// # Specification
/// - requires: `children` are siblings in `tree`, in order.
/// - ensures: one entry per form among them, in reverse order, each carrying
///   the documentation [`heads_among`] reads for it.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`heads_among`].
/// - witness: `gandr-surface-lsp::signature::tests::each_head_reads_its_parameters`
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
    /// - witness: `gandr-surface-lsp::signature::tests::each_head_reads_its_parameters`
    /// - witness: `gandr-surface-lsp::signature::tests::a_parameter_reads_the_documentation_written_before_it_1116`
    /// - witness: `gandr-surface-lsp::signature::tests::a_run_documents_only_what_it_is_written_before_1800`
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
    /// - witness: `gandr-surface-lsp::signature::tests::a_parameter_reads_the_documentation_written_before_it_1116`
    /// - witness: `gandr-surface-lsp::signature::tests::a_run_documents_only_what_it_is_written_before_1800`
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
/// - witness: `gandr-surface-lsp::signature::tests::each_head_reads_its_parameters`
/// - witness: `gandr-surface-lsp::signature::tests::a_parameter_reads_the_documentation_written_before_it_1116`
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
    /// - witness: `gandr-surface-lsp::signature::tests::each_head_reads_its_parameters`
    /// - witness: `gandr-surface-lsp::signature::tests::a_parameter_reads_the_documentation_written_before_it_1116`
    /// - witness: `gandr-surface-lsp::signature::tests::a_run_documents_only_what_it_is_written_before_1800`
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
    /// - witness: `gandr-surface-lsp::signature::tests::each_head_reads_its_parameters`
    /// - witness: `gandr-surface-lsp::signature::tests::a_parameter_reads_the_documentation_written_before_it_1116`
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
    /// - witness: `gandr-surface-lsp::signature::tests::each_head_reads_its_parameters`
    /// - witness: `gandr-surface-lsp::signature::tests::a_parameter_reads_the_documentation_written_before_it_1116`
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
    /// - witness: `gandr-surface-lsp::signature::tests::each_head_reads_its_parameters`
    /// - witness: `gandr-surface-lsp::signature::tests::a_parameter_reads_the_documentation_written_before_it_1116`
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
    /// - witness: `gandr-surface-lsp::signature::tests::each_head_reads_its_parameters`
    /// - witness: `gandr-surface-lsp::signature::tests::a_parameter_reads_the_documentation_written_before_it_1116`
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
/// - witness: `gandr-surface-lsp::signature::tests::each_head_reads_its_parameters`
/// - witness: `gandr-surface-lsp::signature::tests::a_parameter_reads_the_documentation_written_before_it_1116`
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
/// - witness: `gandr-surface-lsp::signature::tests::a_parameter_reads_the_documentation_written_before_it_1116`
/// - witness: `gandr-surface-lsp::signature::tests::a_run_documents_only_what_it_is_written_before_1800`
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
/// - witness: `gandr-surface-lsp::signature::tests::a_parameter_reads_the_documentation_written_before_it_1116`
/// - witness: `gandr-surface-lsp::hover::tests::a_documented_parameter_hovers_its_documentation_1116`
/// - witness: `gandr-surface-lsp::signature::tests::a_run_documents_only_what_it_is_written_before_1800`
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
/// - witness: `gandr-surface-lsp::signature::tests::each_head_reads_its_parameters`
/// - witness: `gandr-surface-lsp::signature::tests::a_parameter_reads_the_documentation_written_before_it_1116`
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
/// - witness: `gandr-surface-lsp::signature::tests::each_head_reads_its_parameters`
/// - witness: `gandr-surface-lsp::signature::tests::a_parameter_reads_the_documentation_written_before_it_1116`
/// - witness: `gandr-surface-lsp::signature::tests::a_run_documents_only_what_it_is_written_before_1800`
/// - witness: `gandr-surface-lsp::signature::tests::only_a_function_type_and_a_list_s_own_separators_make_parameters_1810`
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
/// - witness: `gandr-surface-lsp::signature::tests::each_head_reads_its_parameters`
/// - witness: `gandr-surface-lsp::signature::tests::only_a_function_type_and_a_list_s_own_separators_make_parameters_1810`
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
/// - witness: `gandr-surface-lsp::signature::tests::each_head_reads_its_parameters`
/// - witness: `gandr-surface-lsp::signature::tests::a_parameter_reads_the_documentation_written_before_it_1116`
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
