//! The printer's reading of one node, and the trait a caller implements to
//! hand it nodes.
//!
//! The printer never walks an arena of its own choosing. A [`Source`] answers,
//! for each handle, the [`Former`] the node carries and the handles of its
//! children; the printer walks those on its own stack. The core arena is one
//! source ([`crate::CoreSource`]); a table of content nodes a checker hands
//! back is another, implemented beside the face that holds it.
//!
//! # The input is a source
//!
//! The printer asks one question of its input, the former at a node, through
//! the `Source` trait, and reads nothing else. `CoreSource` answers it over the
//! core arena and `ContentSource` over the incremental checker's content
//! tables, the form a checkpoint keeps a signature or a synthesised type in, so
//! every face that reads checkpoints spells their types through one reading.
//!
//! - **Alternatives.** Taking the core arena alone would make a face holding
//!   content tables mint a core arena first, duplicating the checker's own
//!   minting. The content-table reading lived beside the REPL, the one face
//!   that read checkpoints, which kept the incremental tier out of this crate's
//!   dependencies; it moved here when the language server's hover became a
//!   second reader, since a copy per face would let two faces spell one type
//!   differently. The incremental tier is already in every build that prints a
//!   checkpoint's type.
//! - **Reversal.** A second reader needs more than the former per node — a
//!   span, an origin for a binder name — at which point the question widens, or
//!   the per-node dispatch shows in a profile. A build that prints core types
//!   but never reads checkpoints, measured paying for the incremental tier,
//!   moves `ContentSource` behind a feature.

use core::borrow::Borrow;

use anodized::spec;
use gandr_core_term::Sort;
use gandr_core_term::Zone;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Side;

/// A name a node carries, as its source spells it: an abstract type's or a
/// constant's.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Name<'text>(&'text str);

impl<'text> From<&'text str> for Name<'text>
{
    /// Reads the text as a name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(text: &'text str) -> Self
    {
        Self(text)
    }
}

impl AsRef<str> for Name<'_>
{
    /// The name's text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        self.0
    }
}

impl Borrow<str> for Name<'_>
{
    /// The name's text, so a set of names answers a lookup by text.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the text the name holds; two names compare as their texts do,
    ///   so the order a set keeps agrees with the order of the texts.
    /// - provides: lookup of a generated binder name among the names a term
    ///   spells.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a generated binder skips the single mentioned name
    ///   through heterogeneous set lookup. Returning altered text changes that
    ///   spelling; arbitrary key sets and Unicode ordering are not enumerated.
    ///   The predicate asks for the held text itself, by address and length,
    ///   which implies equal text without reading it.
    /// - witness: `goldens::tests::a_binder_skips_the_names_the_type_mentions`
    #[spec(ensures: |ret| core::ptr::eq(core::ptr::from_ref(ret), core::ptr::from_ref(self.0)))]
    #[inline]
    fn borrow(&self) -> &str
    {
        self.0
    }
}

/// How many components a product, a sum or a tuple has.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Arity(usize);

impl From<usize> for Arity
{
    /// The arity of `count` components.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: usize) -> Self
    {
        Self(count)
    }
}

impl From<Arity> for usize
{
    /// The number of components.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(arity: Arity) -> Self
    {
        arity.0
    }
}

/// The position of one component of a product, a sum or a tuple, counting
/// from zero.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Component(usize);

impl From<usize> for Component
{
    /// The component at `position`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: usize) -> Self
    {
        Self(position)
    }
}

impl From<Component> for usize
{
    /// The position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(component: Component) -> Self
    {
        component.0
    }
}

/// One node as the printer reads it: the former, its children as handles of
/// the same source, and the leaf payloads it carries.
///
/// The vocabulary is the core's, read through one lens: every former the
/// printer spells, and the formers it cannot spell named so that the printer
/// writes `?` for them rather than guessing.
///
/// # Specification
/// - requires: the children are handles of the source that answered.
/// - ensures: each variant is one core former, or one of the two readings a
///   handle can have that is no printable former.
/// - provides: the closed input space of the printer.
/// - panics: none.
/// - executable: none — a former holds opaque child handles, not their source
///   or provenance. Their association with the answering source cannot be
///   observed from this value alone; concrete readers check their conversion.
///
/// # Adequacy
/// - hypothesis: L3 — finite core-backed type and value fixtures distinguish
///   variant selection and child order, while malformed table fixtures expose
///   misplaced and dangling children. Provenance across arbitrary source
///   instances is outside the observations available on a former.
/// - witness: `goldens::tests::every_type_former_spells_as_the_grammar_writes_it`
/// - witness: `goldens::tests::every_value_leaf_spells_as_the_surface_writes_it`
/// - witness: `goldens::tests::misplaced_and_unreadable_nodes_spell_unknown`
#[derive(Clone, Copy, Debug)]
pub enum Former<'source, Node>
{
    /// A flat first-class stack, opaque in value-only presentations.
    Reify,
    /// A stack's ordered input and output computation types.
    Stack(Node, Node),
    /// A lazy pair's two computation types.
    With(Node, Node),
    /// The empty native list.
    ListNil,
    /// A native cell with its head and tail.
    ListCons(Node, Node),
    /// A native universe-path classifier over two quoted codes.
    PathUniverse(Node, Node),
    /// Reflexivity at a quoted code.
    PathRefl(Node),
    /// The two translator programs of an equivalence, evidence omitted.
    PathEquiv(Node, Node),
    /// A componentwise product of paths.
    PathProduct(Node, Node),
    /// A rigid base type: `Integer`, `String`, or the numeric atom.
    BaseType(BaseType),
    /// The product of a value type's components, which the source answers by
    /// [`Source::component`]: `Unit` at arity zero, `A * B * …` from two.
    Product(Arity),
    /// The sum of a value type's components, which the source answers by
    /// [`Source::component`]: `Void` at arity zero, `A + B + …` from two.
    Sum(Arity),
    /// The suspension `+U C` of a computation type.
    ThunkType(Node),
    /// The universe of one sort at a level.
    Universe
    {
        /// The family the universe classifies.
        sort: Sort,
        /// The level within that family.
        level: &'source Level,
    },
    /// A universe lift of a value type, which the surface does not write.
    TypeLift,
    /// The value type a code denotes; the code is a value.
    Element(Node),
    /// A sealed abstract type, by its name.
    Abstract(Name<'source>),
    /// The static Pi `A -> B` classifying a type operator, whose codomain
    /// binds nothing.
    StaticPi
    {
        /// The classifier of the operand.
        domain: Node,
        /// The classifier of the result.
        codomain: Node,
    },
    /// The returner `-F A` of a value type.
    Returner(Node),
    /// A returner with a diagnostic row annotation, not a surface grammar form.
    EffectfulReturner
    {
        /// The value returned.
        result: Node,
        /// The canonical effect names, independent of the source's type
        /// handles.
        effects: &'source dyn core::fmt::Debug,
    },
    /// The arrow `A -> C`, whose codomain binds nothing.
    Arrow
    {
        /// The value-type domain.
        domain: Node,
        /// The computation-type codomain.
        codomain: Node,
    },
    /// The dependent arrow `(x : A) -> C`, whose codomain stands under the
    /// domain's binder.
    Pi
    {
        /// The value-type domain.
        domain: Node,
        /// The computation-type codomain, under the binder.
        codomain: Node,
    },
    /// The computation type a code denotes; the code is a value.
    ComputationElement(Node),
    /// A finite-list type.
    List(Node),
    /// A bound variable.
    Variable
    {
        /// The zone its index counts in.
        zone: Zone,
        /// The index, counting binders outward from the occurrence.
        index: DeBruijnIndex,
    },
    /// A constant, by its name.
    Constant(Name<'source>),
    /// The unit value, `unit`.
    Unit,
    /// A literal.
    Literal(&'source Literal),
    /// A tuple of values, which the source answers by [`Source::component`]:
    /// `(a,)` at arity one, `(a, b, …)` from two; the empty tuple is
    /// [`Former::Unit`].
    Tuple(Arity),
    /// A sum injection.
    Injection(Side, Node),
    /// A suspended computation, which the printer shows as opaque.
    Thunk,
    /// A universe lift of a value, which the surface does not write.
    ValueLift,
    /// The code of a value type: a type read where a value is.
    Quote(Node),
    /// The code of a computation type.
    QuoteComputation(Node),
    /// A static abstraction `\a. v`, its body under one binder.
    StaticLambda(Node),
    /// A static application of an operator to one argument; the printer
    /// spells a spine of them as one application, `f(a, b)`.
    StaticApplication(Node, Node),
    /// A computation term, which no position the printer fills admits.
    Computation,
    /// A handle that names no node, or a node whose name the source cannot
    /// spell.
    Unreadable,
}

/// A store of nodes the printer can read.
///
/// An implementation answers one node at a time and never walks; the printer
/// carries the walk. A source may be malformed — a dangling handle, a cycle —
/// and the printer stays total over it.
pub trait Source
{
    /// The handle a node is named by.
    type Node: Copy;

    /// The node `node` names, as the printer reads it.
    ///
    /// # Specification
    /// - requires: nothing; any handle is admissible.
    /// - ensures: the former the node carries, with its children as handles of
    ///   this source; [`Former::Unreadable`] for a handle that names no node
    ///   and for a node whose name the source cannot spell.
    /// - provides: the one question the printer asks of its input.
    /// - fails: never; an unreadable node is a variant.
    /// - panics: none.
    /// - executable: none — the trait exposes neither membership nor a
    ///   denotation observer independent of `read`. Repeating `read` cannot
    ///   establish whether the returned former represents the stored node.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — core-backed and table-backed readers expose exact
    ///   constructor spellings, dangling handles and misplaced children. These
    ///   distinguish wrong node classification and absence handling for the
    ///   supplied readers, not arbitrary trait implementations.
    /// - witness: `goldens::tests::every_type_former_spells_as_the_grammar_writes_it`
    /// - witness: `goldens::tests::every_value_leaf_spells_as_the_surface_writes_it`
    /// - witness: `goldens::tests::misplaced_and_unreadable_nodes_spell_unknown`
    fn read(
        &self,
        node: Self::Node,
    ) -> Former<'_, Self::Node>;

    /// The handle of component `index` of the product, the sum or the tuple
    /// `node` names.
    ///
    /// # Specification
    /// - requires: nothing; any handle and any position are admissible.
    /// - ensures: the handle of the component at `index` when [`read`] answers
    ///   a [`Former::Product`], a [`Former::Sum`] or a [`Former::Tuple`] for
    ///   `node` and `index` is below its arity; none otherwise.
    /// - provides: the children of an n-ary former, which a [`Former`] counts
    ///   but does not hold.
    /// - fails: never; a missing component is an absence, which the printer
    ///   spells `?`.
    /// - panics: none.
    /// - executable: none — as for [`read`], the trait exposes no observer of
    ///   the stored node independent of its own answers.
    ///
    /// [`read`]: Self::read
    ///
    /// # Adequacy
    /// - hypothesis: L3 — core-backed and table-backed readers answer the
    ///   components of products and sums of arity zero, two and three, and of
    ///   tuples of arity one to three, in order, and none past the arity or for
    ///   another former; a reversed or shifted component changes a golden
    ///   spelling.
    /// - witness: `goldens::tests::every_type_former_spells_as_the_grammar_writes_it`
    /// - witness: `goldens::tests::n_ary_products_and_sums_spell_as_one_chain`
    /// - witness: `content_source::tests::value_ty_covers_every_reachable_former`
    fn component(
        &self,
        node: Self::Node,
        index: Component,
    ) -> Option<Self::Node>;
}
