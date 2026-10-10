//! The checked grammar model: sorts, symbols, regular expressions over them,
//! rules, the named precedence table, the refusal vocabulary, and [`Pbg`],
//! the grammar that exists only once its three build-time gates have passed.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec;
use alloc::vec::Vec;
use core::borrow::Borrow;
use core::error::Error;
use core::fmt::Display;
use core::fmt::Formatter;
use core::fmt::Result as FmtResult;

use anodized::spec;
use gandr_surface_syntax::ClosingClass;
use gandr_surface_syntax::GrammarFingerprint;
use gandr_surface_syntax::GroutSort;
use gandr_surface_syntax::MoldId;
use gandr_theory_graphs::Bound;
use gandr_theory_graphs::Dir;
use gandr_theory_graphs::Prec;
use gandr_theory_graphs::PrecDag;
use gandr_theory_graphs::PrecDagError;
use gandr_theory_graphs::PrecSpecError;
use gandr_theory_graphs::WalkBuildError;

use crate::check::validate_assumption_3;
use crate::check::validate_operator_form;
use crate::mold::MoldDef;
use crate::mold::MoldHasPredecessor;
use crate::mold::MoldHasRequiredTail;
use crate::mold::MoldHasSuccessor;
use crate::mold::MoldIsFormFirst;
use crate::mold::MoldIsFormLast;
use crate::mold::MoldTable;
use crate::mold::MoldsAdjacent;
use crate::mold::RCtxId;
use crate::mold::RCtxStep;
use crate::parity::NamedKind;

/// Defines a transparent static-text identity with `AsRef<str>`,
/// `Borrow<str>` and `Display`, so a consumer compares, keys and prints it
/// without unpacking it.
macro_rules! static_text_wrapper {
    ($name:ident, $doc:literal) => {
        #[doc = $doc]
        #[repr(transparent)]
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct $name(pub &'static str);

        impl AsRef<str> for $name
        {
            /// Borrows the text.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn as_ref(&self) -> &str
            {
                self.0
            }
        }

        impl Borrow<str> for $name
        {
            /// Borrows the text, so a map keyed by this type is probed with a
            /// `&str`.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn borrow(&self) -> &str
            {
                self.0
            }
        }

        impl Display for $name
        {
            /// Writes the text.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn fmt(
                &self,
                f: &mut Formatter<'_>,
            ) -> FmtResult
            {
                f.write_str(self.0)
            }
        }
    };
}

static_text_wrapper!(RuleName, "The identity of one grammar rule.");
static_text_wrapper!(
    TileLabel,
    "The label of one tile: the token class a lexer emits for it."
);
static_text_wrapper!(
    Provenance,
    "The named node kind a rule realises: a tree-sitter named kind, or a kind only this grammar has."
);
static_text_wrapper!(PrecName, "The name of one precedence group.");
static_text_wrapper!(
    SurfaceForm,
    "The surface form an adaptation record documents."
);
static_text_wrapper!(
    AdaptationReason,
    "Why a rule's shape departs from the surface form it realises."
);
static_text_wrapper!(SortName, "The display name of one grammar sort.");

/// How many molds a grammar declares.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MoldCount(pub usize);

/// Whether a precedence table names a group.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct PrecPresence(pub bool);

/// How many molds one tile label can take.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CandidateCount(pub usize);

/// A grammar sort: the closed set of things a hole can stand for.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Sort
{
    /// A top-level item.
    Item,
    /// A pattern.
    Pattern,
    /// An expression.
    Expression,
    /// A type.
    Type,
    /// A resident of an instantiation slot.
    Instantiation,
    /// A member of a module body.
    ///
    /// Module members have a sort of their own so a nested module holds
    /// members of the same sort by reference, which is the only recursion a
    /// precedence-bounded grammar has: rules recur through sorts, never through
    /// rule names. Nesting is unbounded and costs one rule.
    ModuleMember,
}

impl Sort
{
    /// Names the sort's grout tag.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the tags are `0` to `5` in declaration order, and
    ///   [`try_from_tag`](Self::try_from_tag) reads each back to its sort.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: For all six sorts, L2 exhaustive tag observations catch
    ///   reordered, aliased or shifted discriminants; decoding rejection beyond
    ///   the closed set is checked separately.
    /// - witness: `tests::surface::sort_decode_contract`
    #[spec(ensures: |ret| u16::from(ret) == match self { Self::Item => 0, Self::Pattern => 1, Self::Expression => 2, Self::Type => 3, Self::Instantiation => 4, Self::ModuleMember => 5 })]
    #[inline]
    #[must_use]
    pub fn grout_sort(self) -> GroutSort
    {
        GroutSort::from(match self {
            | Self::Item => 0_u16,
            | Self::Pattern => 1,
            | Self::Expression => 2,
            | Self::Type => 3,
            | Self::Instantiation => 4,
            | Self::ModuleMember => 5,
        })
    }

    /// Names the sort for display.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn name(self) -> SortName
    {
        match self {
            | Self::Item => SortName("item"),
            | Self::Pattern => SortName("pattern"),
            | Self::Expression => SortName("expression"),
            | Self::Type => SortName("type"),
            | Self::Instantiation => SortName("instantiation"),
            | Self::ModuleMember => SortName("module_member"),
        }
    }

    /// Reads a grout tag back as its sort.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the sort whose [`grout_sort`](Self::grout_sort) is
    ///   `sort`.
    /// - provides: the checked boundary from a tree's grout back to the
    ///   grammar's sorts.
    /// - fails: a tag no sort carries.
    /// - panics: none.
    ///
    /// # Errors
    /// [`PbgError::InvalidSort`] for a tag past the closed set.
    ///
    /// # Adequacy
    /// - hypothesis: For the six legal tags and the first illegal tag, L3
    ///   boundary observations catch missing sorts, swapped tags and mistaken
    ///   acceptance; larger rejected tags are not individually enumerated.
    /// - witness: `tests::surface::sort_decode_contract`
    #[spec(ensures: |ret| ret.as_ref().map_or_else(|error| matches!(error, PbgError::InvalidSort { sort: rejected } if *rejected == sort) && u16::from(sort) > 5, |decoded| decoded.grout_sort() == sort))]
    #[inline]
    pub fn try_from_tag(sort: GroutSort) -> Result<Self, PbgError>
    {
        match u16::from(sort) {
            | 0 => Ok(Self::Item),
            | 1 => Ok(Self::Pattern),
            | 2 => Ok(Self::Expression),
            | 3 => Ok(Self::Type),
            | 4 => Ok(Self::Instantiation),
            | 5 => Ok(Self::ModuleMember),
            | _ => Err(PbgError::InvalidSort { sort }),
        }
    }
}

/// A terminal tile, declared by label alone: its mold — context,
/// precedence and sort — is assigned per occurrence when the grammar is built.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Tile
{
    /// The tile's label.
    pub label: &'static str,
}

impl Tile
{
    /// Declares a tile by its label.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(label: TileLabel) -> Self
    {
        Self { label: label.0 }
    }
}

/// One symbol of a regular grammar expression.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Sym
{
    /// A hole of a grammar sort.
    Sort(Sort),
    /// A terminal tile.
    Tile(Tile),
}

/// How many children a composite regular-expression node has.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct RegexArity(usize);

/// How many layout entries a regular-expression subtree spans, its root
/// included.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct RegexExtent(usize);

/// One node of a [`Regex`]'s pre-order layout.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum RegexNode
{
    /// The empty sequence.
    Empty,
    /// One symbol.
    Sym(Sym),
    /// A concatenation of the next `arity` subtrees.
    Seq(RegexArity),
    /// An alternation of the next `arity` subtrees.
    Alt(RegexArity),
    /// The next subtree, or nothing.
    Optional,
    /// Zero or more of the next subtree.
    Repeat,
}

/// One layout entry: a node and the extent of the subtree it roots.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct RegexEntry
{
    /// The node.
    node: RegexNode,
    /// The extent of the subtree the node roots.
    extent: RegexExtent,
}

/// Which composite a [`Regex::composite`] call builds.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Composite
{
    /// A concatenation.
    Seq,
    /// An alternation.
    Alt,
}

/// A regular expression over grammar symbols.
///
/// The expression is stored flat, in pre-order: each node records the extent
/// of its subtree, so a child is reached by offset and the type owns no path
/// back to itself. [`view`](Self::view) reads it back as a tree.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Regex
{
    /// The layout, root first.
    entries: Vec<RegexEntry>,
}

impl Regex
{
    /// Builds a one-node expression.
    ///
    /// # Specification
    /// - requires: the node is empty or a single symbol, not a composite.
    /// - ensures: the layout has exactly that node with extent one.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: For empty, tile and sort leaves inside a nested
    ///   expression, L3 shape observations catch the wrong leaf kind or extent;
    ///   malformed composite leaves are excluded by the precondition.
    /// - witness: `tests::regex::nested_shapes_read_back_as_built`
    #[spec(requires: matches!(node, RegexNode::Empty | RegexNode::Sym(_)), ensures: |ret| ret.entries.len() == 1 && ret.entries.first().is_some_and(|root| root.node == node && root.extent.0 == 1))]
    fn leaf(node: RegexNode) -> Self
    {
        Self {
            entries: vec![RegexEntry {
                node,
                extent: RegexExtent(1),
            }],
        }
    }

    /// Builds a concatenation or an alternation of `items`, in order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the root records the item count and the whole extent, and
    ///   each item's layout follows it unchanged, in order.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: For finite constructor-built children, L3 nested and
    ///   empty-composite shape observations catch wrong root kinds, extents and
    ///   child order; the predicate checks root kind and extent, not the
    ///   consumed input stream.
    /// - witness: `tests::regex::nested_shapes_read_back_as_built`
    /// - witness: `tests::regex::empty_alternation_stays_distinct_from_empty_sequence`
    #[spec(ensures: |ret| ret.entries.first().is_some_and(|root| root.extent.0 == ret.entries.len() && matches!((kind, root.node), (Composite::Seq, RegexNode::Seq(_)) | (Composite::Alt, RegexNode::Alt(_)))))]
    fn composite<I>(
        kind: Composite,
        items: I,
    ) -> Self
    where
        I: IntoIterator<Item = Self>,
    {
        let mut entries = vec![RegexEntry {
            node: RegexNode::Empty,
            extent: RegexExtent(1),
        }];
        let mut arity = 0_usize;
        for item in items {
            entries.extend(item.entries);
            arity = arity.saturating_add(1);
        }
        let extent = RegexExtent(entries.len());
        let node = match kind {
            | Composite::Seq => RegexNode::Seq(RegexArity(arity)),
            | Composite::Alt => RegexNode::Alt(RegexArity(arity)),
        };
        if let Some(root) = entries.first_mut() {
            *root = RegexEntry { node, extent };
        }
        Self { entries }
    }

    /// Wraps `inner` under a one-child node.
    ///
    /// # Specification
    /// - requires: `node` is [`RegexNode::Optional`] or [`RegexNode::Repeat`].
    /// - ensures: the root is `node` with the whole extent, and `inner`'s
    ///   layout follows it unchanged.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: For optional and repeated constructor-built subtrees, L3
    ///   nested shape observations catch the wrong wrapper or lost child; the
    ///   precondition rejects another node class, while the postcondition
    ///   checks extent without copying the consumed child.
    /// - witness: `tests::regex::nested_shapes_read_back_as_built`
    #[spec(requires: matches!(node, RegexNode::Optional | RegexNode::Repeat), captures: inner_len = inner.entries.len(), ensures: |ret| ret.entries.len() == inner_len.saturating_add(1) && ret.entries.first().is_some_and(|root| root.node == node && root.extent.0 == ret.entries.len()))]
    fn wrap(
        node: RegexNode,
        inner: Self,
    ) -> Self
    {
        let mut entries = Vec::with_capacity(inner.entries.len().saturating_add(1));
        entries.push(RegexEntry {
            node,
            extent: RegexExtent(inner.entries.len().saturating_add(1)),
        });
        entries.extend(inner.entries);
        Self { entries }
    }

    /// The empty sequence.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn empty() -> Self
    {
        Self::leaf(RegexNode::Empty)
    }

    /// A hole of `sort`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn sort(sort: Sort) -> Self
    {
        Self::leaf(RegexNode::Sym(Sym::Sort(sort)))
    }

    /// A tile labelled `label`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn tile(label: TileLabel) -> Self
    {
        Self::leaf(RegexNode::Sym(Sym::Tile(Tile::new(label))))
    }

    /// The concatenation of `items`, in order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`view`](Self::view) reads back a sequence of `items`, in
    ///   order.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: For finite nested and empty sequences, L3 shape
    ///   observations catch reordered or missing children and a wrong root
    ///   kind; they do not enumerate arbitrary consumed iterators.
    /// - witness: `tests::regex::nested_shapes_read_back_as_built`
    #[spec(ensures: |ret| ret.entries.first().is_some_and(|root| matches!(root.node, RegexNode::Seq(_)) && root.extent.0 == ret.entries.len()))]
    #[inline]
    #[must_use]
    pub fn seq<I>(items: I) -> Self
    where
        I: IntoIterator<Item = Self>,
    {
        Self::composite(Composite::Seq, items)
    }

    /// The alternation of `items`, in order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`view`](Self::view) reads back an alternation of `items`, in
    ///   order.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: For nested, empty and multi-branch alternatives, L3 shape
    ///   observations catch branch loss, reordering and confusion with an empty
    ///   sequence; arbitrary consumed iterators are outside this finite census.
    /// - witness: `tests::regex::nested_shapes_read_back_as_built`
    /// - witness: `tests::regex::empty_alternation_stays_distinct_from_empty_sequence`
    #[spec(ensures: |ret| ret.entries.first().is_some_and(|root| matches!(root.node, RegexNode::Alt(_)) && root.extent.0 == ret.entries.len()))]
    #[inline]
    #[must_use]
    pub fn alt<I>(items: I) -> Self
    where
        I: IntoIterator<Item = Self>,
    {
        Self::composite(Composite::Alt, items)
    }

    /// `inner`, or nothing.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn optional(inner: Self) -> Self
    {
        Self::wrap(RegexNode::Optional, inner)
    }

    /// Zero or more of `inner`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn repeat(inner: Self) -> Self
    {
        Self::wrap(RegexNode::Repeat, inner)
    }

    /// Reads the expression as a tree.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn view(&self) -> RegexView<'_>
    {
        RegexView {
            entries: &self.entries,
        }
    }

    /// The expression's top-level alternatives: the branches of a root
    /// alternation, or the whole expression otherwise.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a root alternation yields its branches in order; any other
    ///   root yields the expression alone.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: For root alternatives, other root kinds and empty
    ///   alternatives, L3 grouped-form observations catch flattening at the
    ///   wrong depth and reordered or dropped branches; no language-equivalence
    ///   claim is made.
    /// - witness: `tests::pbg::grouped_forms_preserve_branch_and_rule_order`
    #[spec(ensures: |ret| match self.entries.first().map(|root| root.node) { Some(RegexNode::Alt(arity)) => ret.len() == arity.0 && ret.iter().flat_map(|branch| branch.entries.iter()).eq(self.entries.iter().skip(1)), _ => ret.as_slice() == core::slice::from_ref(self) })]
    pub(crate) fn alternatives(&self) -> Vec<Self>
    {
        match self.view().shape() {
            | RegexShape::Alt(items) => items.into_iter().map(RegexView::to_regex).collect(),
            | RegexShape::Empty
            | RegexShape::Sym(_)
            | RegexShape::Seq(_)
            | RegexShape::Optional(_)
            | RegexShape::Repeat(_) => vec![self.clone()],
        }
    }
}

/// A borrowed subtree of a [`Regex`].
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RegexView<'regex>
{
    /// The subtree's layout, root first.
    entries: &'regex [RegexEntry],
}

/// The root of a [`RegexView`] with its children as views.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RegexShape<'regex>
{
    /// The empty sequence.
    Empty,
    /// One symbol.
    Sym(Sym),
    /// A concatenation, children in order.
    Seq(Vec<RegexView<'regex>>),
    /// An alternation, branches in order.
    Alt(Vec<RegexView<'regex>>),
    /// The child, or nothing.
    Optional(RegexView<'regex>),
    /// Zero or more of the child.
    Repeat(RegexView<'regex>),
}

impl<'regex> RegexView<'regex>
{
    /// Reads the subtree's root and its children.
    ///
    /// # Specification
    /// - requires: nothing; a view's layout is a [`Regex`] subtree by
    ///   construction.
    /// - ensures: returns the root node with one view per child, in order.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: For constructor-built nested expressions and zero-child
    ///   composites, L3 structural observations catch wrong root tags, child
    ///   order and subtree boundaries; malformed private layouts are outside
    ///   the public domain.
    /// - witness: `tests::regex::nested_shapes_read_back_as_built`
    #[spec(ensures: |ret| match (self.entries.split_first(), &ret) {
        (None, &RegexShape::Empty) => true,
        (Some((root, rest)), shape) => match (root.node, shape) {
            (RegexNode::Empty, &RegexShape::Empty) => true,
            (RegexNode::Sym(expected), &RegexShape::Sym(actual)) => expected == actual,
            (RegexNode::Seq(arity), &RegexShape::Seq(ref items)) | (RegexNode::Alt(arity), &RegexShape::Alt(ref items)) => items.len() == arity.0 && items.iter().flat_map(|child| child.entries.iter()).eq(rest.iter()),
            (RegexNode::Optional, &RegexShape::Optional(child)) | (RegexNode::Repeat, &RegexShape::Repeat(child)) => child.entries == rest,
            _ => false,
        },
        _ => false,
    })]
    #[inline]
    #[must_use]
    pub fn shape(self) -> RegexShape<'regex>
    {
        let Some((root, rest)) = self.entries.split_first()
        else {
            return RegexShape::Empty;
        };
        match root.node {
            | RegexNode::Empty => RegexShape::Empty,
            | RegexNode::Sym(sym) => RegexShape::Sym(sym),
            | RegexNode::Seq(arity) => RegexShape::Seq(children(rest, arity)),
            | RegexNode::Alt(arity) => RegexShape::Alt(children(rest, arity)),
            | RegexNode::Optional => RegexShape::Optional(first_child(rest)),
            | RegexNode::Repeat => RegexShape::Repeat(first_child(rest)),
        }
    }

    /// Copies the subtree out as an expression of its own.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn to_regex(self) -> Regex
    {
        Regex {
            entries: self.entries.to_vec(),
        }
    }
}

/// Splits the layout after a composite root into its first `arity`
/// subtrees.
///
/// # Specification
/// - requires: `rest` starts with `arity` consecutive subtrees.
/// - ensures: returns one view per subtree, in order.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For consecutive well-formed subtree layouts, L3 nested and
///   empty-composite observations catch skipped or merged child spans and
///   incorrect arity; invalid private layouts are not a supported input.
/// - witness: `tests::regex::nested_shapes_read_back_as_built`
/// - witness: `tests::regex::empty_alternation_stays_distinct_from_empty_sequence`
#[spec(ensures: |ret| ret.len() == arity.0 && ret.iter().all(|view| view.entries.first().is_some_and(|root| root.extent.0 == view.entries.len())))]
fn children(
    rest: &[RegexEntry],
    arity: RegexArity,
) -> Vec<RegexView<'_>>
{
    let mut views = Vec::with_capacity(arity.0);
    let mut remaining = rest;
    for _child in 0 .. arity.0 {
        let Some(first) = remaining.first()
        else {
            break;
        };
        let (child, tail) = remaining
            .split_at_checked(first.extent.0)
            .unwrap_or((remaining, &[]));
        views.push(RegexView { entries: child });
        remaining = tail;
    }
    views
}

/// The first subtree of the layout after a one-child root.
///
/// # Specification
/// - requires: `rest` starts with one subtree.
/// - ensures: returns a view of exactly that subtree.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For a valid leading subtree, L3 nested wrapper observations
///   catch inclusion of siblings or truncation; the predicate bounds and
///   measures the first extent, not arbitrary malformed private layouts.
/// - witness: `tests::regex::nested_shapes_read_back_as_built`
#[spec(requires: rest.first().is_some_and(|root| root.extent.0 > 0 && root.extent.0 <= rest.len()), ensures: |ret| rest.first().is_some_and(|root| ret.entries.len() == root.extent.0) && core::ptr::eq(ret.entries.as_ptr(), rest.as_ptr()))]
fn first_child(rest: &[RegexEntry]) -> RegexView<'_>
{
    let extent = rest.first().map_or(0, |entry| entry.extent.0);
    RegexView {
        entries: rest.get(.. extent).unwrap_or(rest),
    }
}

/// An adaptation record: where a rule's shape departs from the surface form
/// it realises, and why. Audit data only; the gates never read it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Adaptation
{
    /// The rule the record belongs to.
    pub rule: &'static str,
    /// The surface form the record documents.
    pub surface: &'static str,
    /// Why the shape departs.
    pub reason: &'static str,
}

impl Adaptation
{
    /// Records an adaptation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        rule: RuleName,
        surface: SurfaceForm,
        reason: AdaptationReason,
    ) -> Self
    {
        Self {
            rule: rule.0,
            surface: surface.0,
            reason: reason.0,
        }
    }
}

/// One grammar rule: a named form of one sort at one precedence.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Rule
{
    /// The rule's identity, unique in its grammar.
    pub name: &'static str,
    /// The sort the rule's form produces.
    pub sort: Sort,
    /// The precedence group of the rule's form.
    pub prec: Prec,
    /// The rule's form.
    pub regex: Regex,
    /// The named node kind the rule realises.
    pub provenance: &'static str,
    /// Adaptation records, audit data only.
    pub adaptations: Vec<Adaptation>,
}

impl Rule
{
    /// Declares a rule whose provenance is its own name.
    ///
    /// # Specification
    /// - requires: nothing; uniqueness of `name` is checked by [`Pbg::build`].
    /// - ensures: the rule carries no adaptation records.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: For checked rules with distinct names and ordered
    ///   branches, L3 grouped-form and provenance observations catch fabricated
    ///   adaptation records and name/provenance drift; the finite grammar is
    ///   not a census of every possible rule body.
    /// - witness: `tests::pbg::grouped_forms_preserve_branch_and_rule_order`
    #[spec(ensures: |ret| ret.name == name.0 && ret.provenance == name.0 && ret.sort == sort && ret.prec == prec && ret.adaptations.is_empty())]
    #[inline]
    #[must_use]
    pub fn new(
        name: RuleName,
        sort: Sort,
        prec: Prec,
        regex: Regex,
    ) -> Self
    {
        Self {
            provenance: name.0,
            name: name.0,
            sort,
            prec,
            regex,
            adaptations: Vec::new(),
        }
    }

    /// Declares a rule with an explicit provenance.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn with_provenance(
        name: RuleName,
        provenance: Provenance,
        sort: Sort,
        prec: Prec,
        regex: Regex,
    ) -> Self
    {
        Self {
            name: name.0,
            sort,
            prec,
            regex,
            provenance: provenance.0,
            adaptations: Vec::new(),
        }
    }

    /// Declares a rule, provenance its name, with one adaptation record.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn with_adaptation(
        name: RuleName,
        sort: Sort,
        prec: Prec,
        regex: Regex,
        adaptation: Adaptation,
    ) -> Self
    {
        let mut rule = Self::new(name, sort, prec, regex);
        rule.adaptations.push(adaptation);
        rule
    }

    /// The rule's identity.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn name(&self) -> RuleName
    {
        RuleName(self.name)
    }

    /// The sort the rule produces.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn sort(&self) -> Sort
    {
        self.sort
    }

    /// The rule's precedence group.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn prec(&self) -> Prec
    {
        self.prec
    }

    /// The rule's form.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn regex(&self) -> &Regex
    {
        &self.regex
    }

    /// The named node kind the rule realises.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn provenance(&self) -> Provenance
    {
        Provenance(self.provenance)
    }

    /// The rule's adaptation records.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn adaptations(&self) -> &[Adaptation]
    {
        &self.adaptations
    }
}

/// A built precedence DAG with its groups' names.
#[derive(Clone, Debug)]
pub struct PrecTable
{
    /// The DAG.
    dag: PrecDag,
    /// Each group's name and identity.
    names: BTreeMap<PrecName, Prec>,
}

impl PrecTable
{
    /// Pairs a DAG with its groups' names.
    ///
    /// # Specification
    /// - requires: every pair names a group of `dag`.
    /// - ensures: [`get`](Self::get) answers each name with its group.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: For a DAG whose supplied names reference its groups, L3
    ///   built-in group observations catch foreign identities and name
    ///   association errors; the predicate validates stored identities without
    ///   replaying or copying the consumed name iterator.
    /// - witness: `tests::surface::built_in_precedence_bands_are_exact`
    #[spec(ensures: |ret| ret.names.values().all(|&prec| ret.dag.name(prec).is_some()))]
    #[inline]
    #[must_use]
    pub fn new<I>(
        dag: PrecDag,
        names: I,
    ) -> Self
    where
        I: IntoIterator<Item = (PrecName, Prec)>,
    {
        Self {
            dag,
            names: names.into_iter().collect(),
        }
    }

    /// The DAG.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn dag(&self) -> &PrecDag
    {
        &self.dag
    }

    /// Releases the DAG.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn into_dag(self) -> PrecDag
    {
        self.dag
    }

    /// Whether `prec` names a group of the DAG.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn contains(
        &self,
        prec: Prec,
    ) -> PrecPresence
    {
        PrecPresence(self.dag.name(prec).is_some())
    }

    /// Looks up a group by name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn get(
        &self,
        name: PrecName,
    ) -> Option<Prec>
    {
        self.names.get(name.as_ref()).copied()
    }

    /// Looks up a group by name, refusing an unknown one by name.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the group `name` names.
    /// - provides: the checked lookup the built-in rule assemblies use.
    /// - fails: a name the table does not hold.
    /// - panics: none.
    ///
    /// # Errors
    /// [`PbgError::MissingPrec`] naming the absent group.
    ///
    /// # Adequacy
    /// - hypothesis: For the finite built-in name table and an absent name, L3
    ///   exact lookup observations catch swapped identities and fabricated
    ///   acceptance or refusal; arbitrary user-supplied alias maps are outside
    ///   that census.
    /// - witness: `tests::surface::built_in_precedence_bands_are_exact`
    #[spec(ensures: |ret| ret.as_ref().map_or_else(|error| !self.names.contains_key(name.0) && matches!(error, PbgError::MissingPrec { name: missing } if *missing == name.0), |prec| self.names.get(name.0) == Some(prec)))]
    #[inline]
    pub fn prec(
        &self,
        name: PrecName,
    ) -> Result<Prec, PbgError>
    {
        self.get(name).ok_or(PbgError::MissingPrec { name: name.0 })
    }
}

/// Every refusal of grammar construction and lookup.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PbgError
{
    /// A grout tag no sort carries.
    InvalidSort
    {
        /// The tag.
        sort: GroutSort,
    },
    /// A precedence group name the table does not hold.
    MissingPrec
    {
        /// The name.
        name: &'static str,
    },
    /// The precedence specification refused a group or an edge.
    PrecedenceSpec(PrecSpecError),
    /// The precedence relation is cyclic.
    PrecedenceCycle
    {
        /// The groups on the cycle, by name, closed.
        witness: Vec<&'static str>,
    },
    /// The precedence DAG refused its specification for a reason other than
    /// a cycle.
    PrecedenceDag(PrecDagError),
    /// The walk index refused a walk.
    Walk(WalkBuildError),
    /// A rule names a precedence group the DAG does not hold.
    InvalidPrec
    {
        /// The rule.
        rule: &'static str,
        /// The group.
        prec: Prec,
    },
    /// Two rules share a name.
    DuplicateRule
    {
        /// The name.
        name: &'static str,
    },
    /// A rule's form can put two holes side by side (the Operator Form gate).
    AdjacentSorts
    {
        /// The rule.
        rule: &'static str,
        /// The sort of the left hole.
        left: Sort,
        /// The sort of the right hole.
        right: Sort,
    },
    /// Two tile occurrences share a label and a context (the Unique Tiles
    /// gate).
    DuplicateTile
    {
        /// The label.
        label: &'static str,
        /// The sort of the second occurrence's form.
        sort: Sort,
        /// The precedence of the second occurrence's form.
        prec: Prec,
        /// The rule of the first occurrence.
        first_rule: &'static str,
        /// The rule of the second occurrence.
        second_rule: &'static str,
    },
    /// Two distinct sorts can each begin and end the other's forms (the
    /// Assumption 3 gate): `s ∈ FIRST(G(r, p))` and `r ∈ LAST(G(s, q))`.
    Assumption3Conflict
    {
        /// The sort `r`.
        first_sort: Sort,
        /// The sort `s`.
        second_sort: Sort,
    },
    /// The mold table outgrew the 32-bit mold identity.
    MoldOverflow,
    /// A mold id past the table.
    UnknownMold
    {
        /// The id.
        id: MoldId,
    },
    /// A context id past the table.
    UnknownRCtx
    {
        /// The id.
        rctx: RCtxId,
    },
}

impl Display for PbgError
{
    /// Writes the refusal with the values it names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: successful output identifies the refusal and its named
    ///   values.
    /// - fails: propagates a formatter write refusal.
    /// - panics: none.
    /// - executable: none — the formatter is a write-only sink with no
    ///   observation of the emitted text or the originating write error.
    ///
    /// # Adequacy
    /// - hypothesis: For representative local refusals and a wrapped precedence
    ///   error, L3 payload and distinguishability observations catch lost
    ///   identities; a one-byte sink checks write refusal without pinning
    ///   prose. Other formatting flags and every payload value are outside the
    ///   witness.
    /// - witness: `model::tests::grammar_error_messages_keep_payloads_and_refuse_a_full_sink`
    #[inline]
    fn fmt(
        &self,
        f: &mut Formatter<'_>,
    ) -> FmtResult
    {
        match *self {
            | Self::InvalidSort { sort } => {
                write!(f, "invalid grammar sort tag {}", u16::from(sort))
            },
            | Self::MissingPrec { name } => write!(f, "missing precedence group {name}"),
            | Self::PrecedenceSpec(ref error) => Display::fmt(error, f),
            | Self::PrecedenceCycle { ref witness } => {
                f.write_str("precedence cycle")?;
                for name in witness {
                    write!(f, " {name}")?;
                }
                Ok(())
            },
            | Self::PrecedenceDag(ref error) => Display::fmt(error, f),
            | Self::Walk(ref error) => Display::fmt(error, f),
            | Self::InvalidPrec { rule, prec } => {
                write!(f, "rule {rule} names unknown precedence {}", prec.index())
            },
            | Self::DuplicateRule { name } => write!(f, "duplicate grammar rule {name}"),
            | Self::AdjacentSorts { rule, left, right } => write!(
                f,
                "rule {rule} can put a {} hole beside a {} hole",
                left.name(),
                right.name()
            ),
            | Self::DuplicateTile {
                label,
                sort,
                prec,
                first_rule,
                second_rule,
            } => write!(
                f,
                "tile {label} at sort {} precedence {} has one context in rules {first_rule} and {second_rule}",
                sort.name(),
                prec.index()
            ),
            | Self::Assumption3Conflict {
                first_sort,
                second_sort,
            } => write!(
                f,
                "assumption 3 conflict: {} begins a form of {} while {} ends a form of {}",
                second_sort.name(),
                first_sort.name(),
                first_sort.name(),
                second_sort.name()
            ),
            | Self::MoldOverflow => f.write_str("mold table exceeds the 32-bit mold identity"),
            | Self::UnknownMold { id } => write!(f, "unknown mold id {}", u32::from(id)),
            | Self::UnknownRCtx { rctx } => {
                write!(f, "unknown context id {}", u32::from(rctx))
            },
        }
    }
}

impl Error for PbgError
{
    /// The wrapped refusal, for the variants that wrap one.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a wrapped precedence or walk refusal is the typed source;
    ///   local refusals have no source.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: For a wrapped duplicate-name cause and local refusals, L3
    ///   typed downcast observations catch a missing, substituted or fabricated
    ///   source; the predicate covers every wrapper class, but the witness does
    ///   not enumerate every nested cause.
    /// - witness: `model::tests::grammar_error_sources_keep_the_original_cause`
    #[spec(ensures: |ret| match *self {
            Self::PrecedenceSpec(ref error) => ret.and_then(|source| source.downcast_ref::<PrecSpecError>()) == Some(error),
            Self::PrecedenceDag(ref error) => ret.and_then(|source| source.downcast_ref::<PrecDagError>()) == Some(error),
            Self::Walk(ref error) => ret.and_then(|source| source.downcast_ref::<WalkBuildError>()) == Some(error),
            _ => ret.is_none(),
        })]
    #[inline]
    fn source(&self) -> Option<&(dyn Error + 'static)>
    {
        match *self {
            | Self::PrecedenceSpec(ref error) => Some(error),
            | Self::PrecedenceDag(ref error) => Some(error),
            | Self::Walk(ref error) => Some(error),
            | Self::InvalidSort { .. }
            | Self::MissingPrec { .. }
            | Self::PrecedenceCycle { .. }
            | Self::InvalidPrec { .. }
            | Self::DuplicateRule { .. }
            | Self::AdjacentSorts { .. }
            | Self::DuplicateTile { .. }
            | Self::Assumption3Conflict { .. }
            | Self::MoldOverflow
            | Self::UnknownMold { .. }
            | Self::UnknownRCtx { .. } => None,
        }
    }
}

impl From<PrecSpecError> for PbgError
{
    /// Wraps a precedence-specification refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: PrecSpecError) -> Self
    {
        Self::PrecedenceSpec(value)
    }
}

impl From<WalkBuildError> for PbgError
{
    /// Wraps a walk refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: WalkBuildError) -> Self
    {
        Self::Walk(value)
    }
}

/// A checked precedence-bounded grammar.
///
/// A value exists only once its three gates have passed: no form puts two
/// holes side by side (Operator Form), no two tile occurrences share a label
/// and a context (Unique Tiles), and no two sorts can each begin and end the
/// other's forms (Assumption 3).
#[derive(Clone, Debug)]
pub struct Pbg
{
    /// The precedence DAG.
    dag: PrecDag,
    /// The forms grouped by sort and precedence.
    forms: BTreeMap<(Sort, Prec), Regex>,
    /// The rules, in input order.
    rules: Vec<Rule>,
    /// The rule names, ascending.
    rule_names: BTreeSet<RuleName>,
    /// The adaptation records, in rule order.
    adaptations: Vec<Adaptation>,
    /// The mold and context tables.
    molds: MoldTable,
}

impl Pbg
{
    /// Checks `rules` over `dag` and builds the grammar.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success every rule names a group of `dag`, rule names are
    ///   unique, and the Operator Form, Unique Tiles and Assumption 3 gates
    ///   hold; forms are grouped by sort and precedence, alternatives in input
    ///   order, and each tile occurrence has one mold, numbered in rule order
    ///   and left to right within a rule.
    /// - fails: the first violation, checked in that order: headers (unknown
    ///   precedence, duplicate name) rule by rule, Operator Form rule by rule,
    ///   Unique Tiles, then Assumption 3.
    /// - panics: none.
    ///
    /// # Errors
    /// [`PbgError::InvalidPrec`], [`PbgError::DuplicateRule`],
    /// [`PbgError::AdjacentSorts`], [`PbgError::DuplicateTile`],
    /// [`PbgError::MoldOverflow`] or [`PbgError::Assumption3Conflict`].
    ///
    /// # Adequacy
    /// - hypothesis: For finite rule lists over checked DAGs, L3 minimal
    ///   violations and neighboring legal grammars observe error identity,
    ///   refusal priority and grouped-form order, catching skipped gates or
    ///   reordered alternatives; mold-id exhaustion and arbitrary deep forms
    ///   are outside these witnesses.
    /// - witness: `tests::pbg::pbg_rejects_invalid_prec_before_later_header_errors`
    /// - witness: `tests::pbg::pbg_rejects_duplicate_rule_names_deterministically`
    /// - witness: `tests::pbg::pbg_rejects_direct_adjacent_sorts_in_sequence`
    /// - witness: `tests::pbg::pbg_rejects_adjacency_exposed_by_nullable_sequence_paths`
    /// - witness: `tests::pbg::pbg_accepts_terminal_separators_between_sort_uses`
    /// - witness: `tests::pbg::pbg_rejects_duplicate_rctx_tile`
    /// - witness: `tests::pbg::pbg_accepts_same_label_at_distinct_contexts`
    /// - witness: `tests::pbg::assumption_3_contract`
    /// - witness: `tests::pbg::grouped_forms_preserve_branch_and_rule_order`
    #[spec(captures: input = (rules.len(), dag.fingerprint()), ensures: |ret| ret.as_ref().map_or_else(
        |error| matches!(error, PbgError::InvalidPrec { .. } | PbgError::DuplicateRule { .. } | PbgError::AdjacentSorts { .. } | PbgError::DuplicateTile { .. } | PbgError::MoldOverflow | PbgError::Assumption3Conflict { .. }),
        |pbg| pbg.rules.len() == input.0 && pbg.dag.fingerprint() == input.1 && pbg.rule_names.len() == input.0 && pbg.rules.iter().all(|rule| pbg.dag.name(rule.prec).is_some() && pbg.rule_names.contains(rule.name)) && pbg.adaptations.iter().eq(pbg.rules.iter().flat_map(|rule| rule.adaptations.iter()))))]
    #[inline]
    pub fn build(
        dag: PrecDag,
        rules: Vec<Rule>,
    ) -> Result<Self, PbgError>
    {
        validate_rule_headers(&dag, &rules)?;
        for rule in &rules {
            validate_operator_form(rule)?;
        }
        let molds = MoldTable::build(
            &rules,
            GrammarFingerprint::from(u64::from(dag.fingerprint())),
        )?;
        validate_assumption_3(&rules)?;
        let forms = grouped_forms(&rules);
        let rule_names = rules.iter().map(|rule| RuleName(rule.name)).collect();
        let adaptations = rules
            .iter()
            .flat_map(|rule| rule.adaptations.iter().copied())
            .collect();
        Ok(Self {
            dag,
            forms,
            rules,
            rule_names,
            adaptations,
            molds,
        })
    }

    /// Checks `rules` over a table's DAG and builds the grammar.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`build`](Self::build) over `table`'s DAG.
    /// - fails: as [`build`](Self::build).
    /// - panics: none.
    ///
    /// # Errors
    /// As [`build`](Self::build).
    ///
    /// # Adequacy
    /// - hypothesis: For a named checked DAG and finite rules, L3 grouped-form
    ///   observations catch loss of the table identity, rule multiplicity or
    ///   branch order; the delegated gate refusals are witnessed at the build
    ///   boundary.
    /// - witness: `tests::pbg::grouped_forms_preserve_branch_and_rule_order`
    #[spec(captures: input = (rules.len(), table.dag.fingerprint()), ensures: |ret| ret.as_ref().map_or(true, |pbg| pbg.rules.len() == input.0 && pbg.dag.fingerprint() == input.1 && pbg.rule_names.len() == input.0))]
    #[inline]
    pub fn build_table(
        table: PrecTable,
        rules: Vec<Rule>,
    ) -> Result<Self, PbgError>
    {
        Self::build(table.into_dag(), rules)
    }

    /// The precedence DAG.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn dag(&self) -> &PrecDag
    {
        &self.dag
    }

    /// The forms, grouped by sort and precedence: each group one alternation
    /// of its rules' alternatives, in input order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn forms(&self) -> &BTreeMap<(Sort, Prec), Regex>
    {
        &self.forms
    }

    /// The rules, in input order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn rules(&self) -> &[Rule]
    {
        &self.rules
    }

    /// The rule names, ascending.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn rule_names(&self) -> &BTreeSet<RuleName>
    {
        &self.rule_names
    }

    /// The adaptation records, in rule order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn adaptations(&self) -> &[Adaptation]
    {
        &self.adaptations
    }

    /// The mold `id` names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the mold at `id` in the table.
    /// - fails: an id past the table.
    /// - panics: none.
    ///
    /// # Errors
    /// [`PbgError::UnknownMold`] for an id past the table.
    ///
    /// # Adequacy
    /// - hypothesis: For a two-mold grammar, L3 first, last and first-past-id
    ///   observations catch off-by-one acceptance, wrong mold identity and
    ///   incorrect error payloads; arbitrary huge tables are outside the
    ///   witness.
    /// - witness: `tests::walk::mold_lookup_checks_bounds`
    #[spec(ensures: |ret| ret.as_ref().map_or_else(
        |error| usize::try_from(u32::from(id)).map_or(true, |index| index >= self.molds.len().0) && matches!(error, PbgError::UnknownMold { id: missing } if *missing == id),
        |mold| self.molds.mold(id).is_ok_and(|expected| core::ptr::eq(core::ptr::from_ref(*mold), core::ptr::from_ref(expected)))))]
    #[inline]
    pub fn mold(
        &self,
        id: MoldId,
    ) -> Result<&MoldDef, PbgError>
    {
        self.molds.mold(id)
    }

    /// The rule mold `id` belongs to: the rule whose tile occurrence the mold
    /// was numbered for.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the rule's sort and precedence are the mold's; molds are
    ///   numbered in rule order, so ascending ids meet the rules in
    ///   non-decreasing order.
    /// - fails: an id past the table.
    /// - panics: none.
    ///
    /// # Errors
    /// [`PbgError::UnknownMold`] for an id past the table.
    ///
    /// # Adequacy
    /// - hypothesis: For all built-in molds and the first invalid id, L2 finite
    ///   census plus L3 boundary observations catch wrong owner sort,
    ///   precedence, ordering and refusal payload; arbitrary user grammars are
    ///   not exhausted.
    /// - witness: `tests::surface::every_mold_resolves_to_its_rule_and_named_kind`
    #[spec(ensures: |ret| ret.as_ref().map_or_else(
        |error| self.molds.mold(id).is_err() && matches!(error, PbgError::UnknownMold { id: missing } if *missing == id),
        |rule| self.molds.mold(id).is_ok_and(|mold| mold.sort == rule.sort && mold.prec == rule.prec) && self.molds.rule_of(&self.rules, id).is_ok_and(|expected| core::ptr::eq(core::ptr::from_ref(*rule), core::ptr::from_ref(expected)))))]
    #[inline]
    pub fn rule_of(
        &self,
        id: MoldId,
    ) -> Result<&Rule, PbgError>
    {
        self.molds.rule_of(&self.rules, id)
    }

    /// The named kind the form of mold `id` realises: its rule's
    /// provenance.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a total function over the mold table — every id in it
    ///   resolves to the named kind its rule realises, a node kind of the
    ///   surface's committed inventory or one this grammar adds.
    /// - provides: the kind a consumer of a molded tree dispatches on, read
    ///   from the mold a node carries.
    /// - fails: an id past the table.
    /// - panics: none.
    ///
    /// # Errors
    /// [`PbgError::UnknownMold`] for an id past the table.
    ///
    /// # Adequacy
    /// - hypothesis: For every built-in mold and the first invalid id, L2
    ///   finite census and L3 boundary observations catch wrong provenance and
    ///   lost refusal identity; recognition of arbitrary caller-defined
    ///   provenance is not claimed.
    /// - witness: `tests::surface::every_mold_resolves_to_its_rule_and_named_kind`
    #[spec(ensures: |ret| ret.as_ref().map_or_else(
        |error| self.rule_of(id).is_err() && matches!(error, PbgError::UnknownMold { id: missing } if *missing == id),
        |kind| self.rule_of(id).is_ok_and(|rule| kind.0 == rule.provenance)))]
    #[inline]
    pub fn named_kind(
        &self,
        id: MoldId,
    ) -> Result<NamedKind<'static>, PbgError>
    {
        let rule = self.rule_of(id)?;
        Ok(NamedKind(rule.provenance))
    }

    /// The precedence bounds of mold `id`, left and right: its precedence on
    /// a side a hole faces, the root bound on a side it does not.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each side is [`Bound::Value`] of the mold's precedence when a
    ///   hole can face the mold there, and [`Bound::Root`] otherwise.
    /// - fails: an id past the table.
    /// - panics: none.
    ///
    /// # Errors
    /// [`PbgError::UnknownMold`] for an id past the table.
    ///
    /// # Adequacy
    /// - hypothesis: For infix, operand-facing prefix and closed-atom contexts,
    ///   L3 side-specific observations catch swapped root/value bounds and
    ///   wrong precedence; first-past-id rejection covers the lookup boundary,
    ///   not all context shapes.
    /// - witness: `tests::walk::mold_bounds_follow_context_nullability`
    /// - witness: `tests::walk::mold_lookup_checks_bounds`
    #[spec(ensures: |ret| ret.as_ref().map_or_else(
        |error| self.molds.mold(id).is_err() && matches!(error, PbgError::UnknownMold { id: missing } if *missing == id),
        |&(left, right)| self.molds.mold(id).is_ok_and(|mold| (matches!(left, Bound::Root) || left == Bound::Value(mold.prec)) && (matches!(right, Bound::Root) || right == Bound::Value(mold.prec)))))]
    #[inline]
    pub fn bounds(
        &self,
        id: MoldId,
    ) -> Result<(Bound<Prec>, Bound<Prec>), PbgError>
    {
        self.molds.bounds(id)
    }

    /// The symbols a context's zipper crosses stepping out in direction
    /// `dir`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns, ascending, the symbols that can stand next to the
    ///   context on that side.
    /// - fails: a context id past the table.
    /// - panics: none.
    ///
    /// # Errors
    /// [`PbgError::UnknownRCtx`] for an id past the table.
    ///
    /// # Adequacy
    /// - hypothesis: For both directions of a finite infix context and an
    ///   unknown context, L3 observations catch direction swaps, missing
    ///   adjacent symbols and wrong refusal payload; larger context languages
    ///   are not enumerated.
    /// - witness: `tests::walk::rctx_steps_cross_adjacent_symbols`
    /// - witness: `tests::walk::unknown_context_preserves_its_identity`
    #[spec(ensures: |ret| ret.as_ref().map_or_else(|error| matches!(error, PbgError::UnknownRCtx { rctx: missing } if *missing == rctx), |steps| steps.iter().is_sorted_by(|left, right| left.crossed < right.crossed)))]
    #[inline]
    pub fn step(
        &self,
        rctx: RCtxId,
        dir: Dir,
    ) -> Result<&[RCtxStep], PbgError>
    {
        self.molds.step(rctx, dir)
    }

    /// Every mold `label` can take, ascending.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns one mold per occurrence of the label, ascending; an
    ///   undeclared label has none.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: For the built-in label inventory and an absent label, L2
    ///   finite inventory observations catch lost, duplicated or reordered mold
    ///   occurrences; arbitrary grammars are outside the census.
    /// - witness: `tests::walk::declared_mold_candidate_inventory_is_exact`
    #[spec(ensures: |ret| ret.iter().copied().eq(self.molds.iter().filter_map(|(id, mold)| (mold.label == label.0).then_some(id))))]
    #[inline]
    #[must_use]
    pub fn candidates(
        &self,
        label: TileLabel,
    ) -> &[MoldId]
    {
        self.molds.candidates(label)
    }

    /// The molds `label` can take where no form is open: those without a
    /// same-form predecessor, and those that can open a form.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns, ascending, the molds of
    ///   [`candidates`](Self::candidates) that have no same-form predecessor or
    ///   are form-first; each dropped mold needs an open form.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: For every built-in label and an absent label, L2 finite
    ///   inventory observations compare fresh menus with the predecessor-free
    ///   or form-first subset, catching dropped openers and retained dependent
    ///   molds; arbitrary grammars are not enumerated.
    /// - witness: `tests::walk::fresh_menus_keep_exactly_the_form_openers`
    #[spec(ensures: |ret| ret.iter().copied().eq(self.candidates(label).iter().copied().filter(|&mold| !bool::from(self.molds.has_predecessor(mold)) || bool::from(self.molds.is_form_first(mold)))))]
    #[inline]
    #[must_use]
    pub fn fresh_candidates(
        &self,
        label: TileLabel,
    ) -> &[MoldId]
    {
        self.molds.fresh_candidates(label)
    }

    /// Every declared label with how many molds it can take, ascending by
    /// label.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one row per label with at least one occurrence.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: For the complete built-in label inventory, L2 finite
    ///   observations compare ordered labels and exact multiplicities, catching
    ///   omitted labels, duplicate rows and incorrect counts; the inventory is
    ///   not a proof for arbitrary user grammars.
    /// - witness: `tests::walk::declared_mold_candidate_inventory_is_exact`
    #[spec(ensures: |ret| ret.iter().is_sorted_by(|left, right| left.0 < right.0) && ret.iter().all(|&(label, count)| count.0 > 0 && count.0 == self.candidates(label).len()) && ret.iter().try_fold(0_usize, |sum, &(_, count)| sum.checked_add(count.0)) == Some(self.molds.len().0))]
    #[inline]
    #[must_use]
    pub fn candidate_counts(&self) -> Vec<(TileLabel, CandidateCount)>
    {
        self.molds.candidate_counts()
    }

    /// How many molds the grammar declares.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn mold_count(&self) -> MoldCount
    {
        self.molds.len()
    }

    /// Every mold with its id, ascending.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: yields each mold once, in id order.
    /// - panics: none.
    /// - executable: none — the opaque iterator return cannot be named by the
    ///   specification macro; consuming it in a predicate would also consume
    ///   the caller's cursor.
    ///
    /// # Adequacy
    /// - hypothesis: For the finite built-in table, L2 enumeration and
    ///   walk-projection observations catch missing, repeated or reordered mold
    ///   ids; this does not exhaust arbitrary grammars or iterator
    ///   interleavings.
    /// - witness: `tests::walk::walk_index_projects_every_mold_once`
    #[inline]
    pub fn iter_molds(&self) -> impl Iterator<Item = (MoldId, &MoldDef)>
    {
        self.molds.iter()
    }

    /// The same-form adjacency `≐`: pairs of molds consecutive within one
    /// form, holes between them skipped, ascending and unique.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `(left, right)` is present exactly when some form can put
    ///   `right`'s occurrence next after `left`'s, past holes only; returns the
    ///   complete stored table by reference.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: For a bracket form and a closed atom, L3 exact edge
    ///   observations catch cross-hole omissions and invented same-form
    ///   adjacency. Construction checks ordering and ownership; this predicate
    ///   protects borrowed-table identity without rescanning immutable edges.
    ///   Arbitrary regex languages are not exhausted.
    /// - witness: `tests::walk::same_form_adjacency_is_the_eq_relation`
    /// - witness: `tests::walk::form_membership_flags_agree_with_their_lists`
    #[spec(ensures: |ret| core::ptr::eq(core::ptr::from_ref(ret), core::ptr::from_ref(self.molds.adjacencies())))]
    #[inline]
    #[must_use]
    pub fn adjacencies(&self) -> &[(MoldId, MoldId)]
    {
        self.molds.adjacencies()
    }

    /// The [`adjacencies`](Self::adjacencies) pairs whose left is `mold`,
    /// ascending: its same-form successors.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: exactly the pairs of [`adjacencies`](Self::adjacencies) whose
    ///   left is `mold`, in their order; empty for an id past the table.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every built-in mold's run compares with a filter of
    ///   the whole adjacency, and the first id past the table reads empty; a
    ///   run cut short, shifted, or a neighbor's changes a comparison.
    /// - witness: `tests::walk::form_membership_flags_agree_with_their_lists`
    #[spec(ensures: |ret| ret.iter().copied().eq(self.adjacencies().iter().copied().filter(|&(left, _)| left == mold)))]
    #[inline]
    #[must_use]
    pub fn mold_successors(
        &self,
        mold: MoldId,
    ) -> &[(MoldId, MoldId)]
    {
        self.molds.successors(mold)
    }

    /// Whether `left` then `right` are same-form adjacent: `(left, right)` is
    /// one of the [`adjacencies`](Self::adjacencies).
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: true exactly when `(left, right)` is in
    ///   [`adjacencies`](Self::adjacencies).
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every built-in pair, its reverse and a pair past the
    ///   table compare with the whole list; a lookup in the wrong run changes a
    ///   comparison.
    /// - witness: `tests::walk::form_membership_flags_agree_with_their_lists`
    #[spec(ensures: |ret| bool::from(ret) == self.adjacencies().contains(&(left, right)))]
    #[inline]
    #[must_use]
    pub fn molds_adjacent(
        &self,
        left: MoldId,
        right: MoldId,
    ) -> MoldsAdjacent
    {
        self.molds.adjacent(left, right)
    }

    /// The molds that can be a form's first tile, ascending and unique.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a mold is present exactly when its occurrence is in its
    ///   form's FIRST set, holes skipped; a mold behind a nullable prefix
    ///   counts.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: For all built-in molds, L2 ordered-set and membership
    ///   observations catch omitted or duplicated first tiles and inconsistent
    ///   flags; nullable prefixes of arbitrary user forms are not exhausted.
    /// - witness: `tests::walk::form_membership_flags_agree_with_their_lists`
    #[spec(ensures: |ret| ret.iter().copied().eq(self.molds.iter().filter_map(|(id, _)| bool::from(self.molds.is_form_first(id)).then_some(id))))]
    #[inline]
    #[must_use]
    pub fn form_first(&self) -> &[MoldId]
    {
        self.molds.form_first()
    }

    /// The molds that can be a form's last tile, ascending and unique.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a mold is present exactly when its occurrence is in its
    ///   form's LAST set, holes skipped; exactly one of
    ///   [`mold_is_form_last`](Self::mold_is_form_last) and
    ///   [`mold_has_required_tail`](Self::mold_has_required_tail) holds for
    ///   each.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: For all built-in molds, L2 finite membership observations
    ///   catch omissions, duplicates and overlaps between clean completion and
    ///   required tails; arbitrary form languages are outside the census.
    /// - witness: `tests::walk::form_membership_flags_agree_with_their_lists`
    #[spec(ensures: |ret| ret.iter().copied().eq(self.molds.iter().filter_map(|(id, _)| (bool::from(self.molds.is_form_last(id)) || bool::from(self.molds.has_required_tail(id))).then_some(id))))]
    #[inline]
    #[must_use]
    pub fn form_last(&self) -> &[MoldId]
    {
        self.molds.form_last()
    }

    /// Whether `mold` has a same-form predecessor.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: true exactly when some pair of
    ///   [`adjacencies`](Self::adjacencies) ends at `mold`; false for an id
    ///   past the table.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: For every built-in mold and the first invalid id, L2
    ///   finite and L3 boundary observations compare the flag with incoming
    ///   adjacency, catching reversed direction and fabricated out-of-range
    ///   membership. Construction proves the edge/flag relation once; the
    ///   predicate checks the immutable stored answer.
    /// - witness: `tests::walk::form_membership_flags_agree_with_their_lists`
    #[spec(ensures: |ret| bool::from(ret) == bool::from(self.molds.has_predecessor(mold)))]
    #[inline]
    #[must_use]
    pub fn mold_has_predecessor(
        &self,
        mold: MoldId,
    ) -> MoldHasPredecessor
    {
        self.molds.has_predecessor(mold)
    }

    /// Whether `mold` has a same-form successor.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: true exactly when some pair of
    ///   [`adjacencies`](Self::adjacencies) starts at `mold`; false for an id
    ///   past the table.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: For every built-in mold and the first invalid id, L2
    ///   finite and L3 boundary observations compare the flag with outgoing
    ///   adjacency, catching reversed direction and fabricated out-of-range
    ///   membership. Construction proves the edge/flag relation once; the
    ///   predicate checks the immutable stored answer.
    /// - witness: `tests::walk::form_membership_flags_agree_with_their_lists`
    #[spec(ensures: |ret| bool::from(ret) == bool::from(self.molds.has_successor(mold)))]
    #[inline]
    #[must_use]
    pub fn mold_has_successor(
        &self,
        mold: MoldId,
    ) -> MoldHasSuccessor
    {
        self.molds.has_successor(mold)
    }

    /// Whether `mold` can open a form.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: true exactly when `mold` is in
    ///   [`form_first`](Self::form_first).
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: For every built-in mold and the first invalid id, L2
    ///   finite and L3 boundary observations compare first membership with the
    ///   ordered list, catching reversed flags and out-of-range acceptance.
    /// - witness: `tests::walk::form_membership_flags_agree_with_their_lists`
    #[spec(ensures: |ret| bool::from(ret) == self.molds.form_first().contains(&mold))]
    #[inline]
    #[must_use]
    pub fn mold_is_form_first(
        &self,
        mold: MoldId,
    ) -> MoldIsFormFirst
    {
        self.molds.is_form_first(mold)
    }

    /// Whether `mold` can complete its form with no hole still required.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: true exactly when `mold` is in [`form_last`](Self::form_last)
    ///   and the form's remainder after it needs no hole.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: For built-in molds, L2 finite partition observations and
    ///   L3 infix/prefix contrasts catch premature completion and missing clean
    ///   completion; arbitrary user forms are outside the census, and the first
    ///   invalid id is rejected.
    /// - witness: `tests::surface::infix_type_operator_keeps_clean_completion`
    /// - witness: `tests::walk::form_membership_flags_agree_with_their_lists`
    #[spec(ensures: |ret| bool::from(ret) == (self.molds.form_last().contains(&mold) && !bool::from(self.molds.has_required_tail(mold))))]
    #[inline]
    #[must_use]
    pub fn mold_is_form_last(
        &self,
        mold: MoldId,
    ) -> MoldIsFormLast
    {
        self.molds.is_form_last(mold)
    }

    /// Whether `mold` can end its form only once a trailing hole is filled.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: true exactly when `mold` is in [`form_last`](Self::form_last)
    ///   and the form's remainder after it needs a hole.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: For built-in molds, L2 finite partition observations and
    ///   L3 required prefix operands catch lost tails and invented
    ///   requirements; arbitrary user forms are outside the census, and the
    ///   first invalid id is rejected.
    /// - witness: `tests::surface::prefix_formers_keep_required_type_tails_unclosed`
    /// - witness: `tests::walk::form_membership_flags_agree_with_their_lists`
    #[spec(ensures: |ret| bool::from(ret) == (self.molds.form_last().contains(&mold) && !bool::from(self.molds.is_form_last(mold))))]
    #[inline]
    #[must_use]
    pub fn mold_has_required_tail(
        &self,
        mold: MoldId,
    ) -> MoldHasRequiredTail
    {
        self.molds.has_required_tail(mold)
    }

    /// The closing class of `mold`'s form: the bracket family every
    /// completion from `mold` ends in, when they agree on one.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Some(c)` exactly when every completion path from `mold`
    ///   within its own rule ends at a closer of family `c` that the rule also
    ///   opens; `None` when the completions disagree, end at a non-closer,
    ///   close a family the rule never opens, or `mold` is past the table.
    /// - provides: the family a parser's minted closing delimiter stands in
    ///   for; `None` pairs with nothing.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: For repeated containers, non-closer endings and divergent
    ///   branches, L3 class observations catch wrong-family and premature
    ///   pairing; the predicate protects invalid-id refusal, while arbitrary
    ///   completion languages are not enumerated.
    /// - witness: `tests::closing_class::closing_class_is_form_level`
    /// - witness: `tests::closing_class::closing_class_repeat_with_exit_shares_its_component_answer`
    #[spec(ensures: |ret| ret.is_none() || self.molds.mold(mold).is_ok())]
    #[inline]
    #[must_use]
    pub fn closing_class(
        &self,
        mold: MoldId,
    ) -> Option<ClosingClass>
    {
        self.molds.closing_class(mold)
    }

    /// The grammar's fingerprint: the precedence DAG's fingerprint folded
    /// with the mold and context tables.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: two builds of the same rules over the same DAG agree; a
    ///   changed mold, context or precedence group moves it.
    /// - provides: the scope a tree's [`MoldId`]s are read in.
    /// - panics: none.
    /// - executable: none — the returned fingerprint has a private primitive
    ///   field in another crate and no const-readable observer or const
    ///   comparison; direct instrumentation cannot compare it here.
    ///
    /// # Adequacy
    /// - hypothesis: For repeated built-in builds and a renamed precedence
    ///   group, L3 value observations with an external compatibility pin catch
    ///   ignored DAG input and unstable hashing; no collision-freedom or
    ///   universal sensitivity claim follows.
    /// - witness: `tests::walk::pbg_fingerprint_is_stable_and_folds_precdag`
    #[inline]
    #[must_use]
    pub const fn fingerprint(&self) -> GrammarFingerprint
    {
        self.molds.fingerprint()
    }
}

/// Checks every rule's precedence and name before any form is read.
///
/// # Specification
/// - requires: nothing.
/// - ensures: on success every rule's group is in `dag` and the names are
///   unique.
/// - fails: the first rule, in input order, with an unknown group or a name
///   already seen.
/// - panics: none.
///
/// # Errors
/// [`PbgError::InvalidPrec`] or [`PbgError::DuplicateRule`].
///
/// # Adequacy
/// - hypothesis: For finite rules over a checked DAG, L3 duplicate and
///   invalid-group observations catch swapped header priority and lost error
///   identity; the predicate validates successful groups and refusal payloads,
///   not every possible input ordering.
/// - witness: `tests::pbg::pbg_rejects_invalid_prec_before_later_header_errors`
/// - witness: `tests::pbg::pbg_rejects_duplicate_rule_names_deterministically`
#[spec(ensures: |ret| ret.as_ref().map_or_else(
    |error| match *error {
        PbgError::InvalidPrec { rule, prec } => dag.name(prec).is_none() && rules.iter().any(|item| item.name == rule && item.prec == prec),
        PbgError::DuplicateRule { name } => rules.iter().filter(|rule| rule.name == name).take(2).count() == 2,
        _ => false,
    },
    |&()| rules.iter().all(|rule| dag.name(rule.prec).is_some()) && rules.iter().enumerate().all(|(index, rule)| rules.iter().take(index).all(|prior| prior.name != rule.name))))]
fn validate_rule_headers(
    dag: &PrecDag,
    rules: &[Rule],
) -> Result<(), PbgError>
{
    let mut names = BTreeSet::new();
    for rule in rules {
        if dag.name(rule.prec).is_none() {
            return Err(PbgError::InvalidPrec {
                rule: rule.name,
                prec: rule.prec,
            });
        }
        if !names.insert(rule.name) {
            return Err(PbgError::DuplicateRule { name: rule.name });
        }
    }
    Ok(())
}

/// Groups the rules' alternatives by sort and precedence.
///
/// # Specification
/// - requires: nothing.
/// - ensures: each key maps to one alternation of every alternative of every
///   rule with that key, in input order.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For interleaved rule groups, top-level alternatives, nested
///   sequences and an empty alternation, L3 exact branch observations catch
///   sorting by the wrong key, branch loss and flattening below the root;
///   arbitrary regex languages are not enumerated.
/// - witness: `tests::pbg::grouped_forms_preserve_branch_and_rule_order`
#[spec(ensures: |ret| rules.iter().all(|rule| ret.contains_key(&(rule.sort, rule.prec))) && ret.iter().all(|(key, regex)| rules.iter().any(|rule| (rule.sort, rule.prec) == *key) && regex.entries.first().is_some_and(|root| matches!(root.node, RegexNode::Alt(_)))))]
fn grouped_forms(rules: &[Rule]) -> BTreeMap<(Sort, Prec), Regex>
{
    let mut grouped: BTreeMap<(Sort, Prec), Vec<Regex>> = BTreeMap::new();
    for rule in rules {
        grouped
            .entry((rule.sort, rule.prec))
            .or_default()
            .extend(rule.regex.alternatives());
    }
    grouped
        .into_iter()
        .map(|(key, alternatives)| (key, Regex::alt(alternatives)))
        .collect()
}

#[cfg(test)]
mod tests
{
    extern crate std;

    use alloc::string::ToString as _;
    use core::error::Error as _;
    use std::io::Write as _;

    use gandr_theory_graphs::PrecSpecError;

    use super::PbgError;
    use super::Sort;

    #[test]
    fn grammar_error_sources_keep_the_original_cause()
    {
        let cause = PrecSpecError::DuplicateName {
            name: "duplicate-group".into(),
        };
        let wrapped = PbgError::from(cause.clone());
        assert_eq!(
            Some(&cause),
            wrapped
                .source()
                .and_then(|source| source.downcast_ref::<PrecSpecError>())
        );
        assert!(PbgError::MissingPrec { name: "absent" }.source().is_none());
        assert!(PbgError::MoldOverflow.source().is_none());
    }

    #[test]
    fn grammar_error_messages_keep_payloads_and_refuse_a_full_sink()
    {
        let named = PbgError::MissingPrec {
            name: "absent-group",
        };
        assert!(named.to_string().contains("absent-group"));
        let wrapped = PbgError::from(PrecSpecError::DuplicateName {
            name: "duplicate-group".into(),
        });
        assert!(wrapped.to_string().contains("duplicate-group"));
        let messages = [
            named.to_string(),
            wrapped.to_string(),
            PbgError::DuplicateRule {
                name: "duplicate-rule",
            }
            .to_string(),
            PbgError::AdjacentSorts {
                rule: "adjacent-rule",
                left: Sort::Type,
                right: Sort::Pattern,
            }
            .to_string(),
            PbgError::Assumption3Conflict {
                first_sort: Sort::Expression,
                second_sort: Sort::Type,
            }
            .to_string(),
            PbgError::MoldOverflow.to_string(),
        ];
        for (index, left) in messages.iter().enumerate() {
            for right in messages.iter().skip(index.saturating_add(1)) {
                assert_ne!(left, right, "different refusals remain distinguishable");
            }
        }
        let mut bytes = [0_u8; 1];
        let mut sink = bytes.as_mut_slice();
        assert!(write!(&mut sink, "{named}").is_err());
    }
}
