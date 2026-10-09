//! The printer's reading of one node, and the trait a caller implements to
//! hand it nodes.
//!
//! The printer never walks an arena of its own choosing. A [`Source`] answers,
//! for each handle, the [`Former`] the node carries and the handles of its
//! children; the printer walks those on its own stack. The core arena is one
//! source ([`crate::CoreSource`]); a table of content nodes a checker hands
//! back is another, implemented beside the face that holds it.

use core::borrow::Borrow;

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
    #[inline]
    fn borrow(&self) -> &str
    {
        self.0
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
#[derive(Clone, Copy, Debug)]
pub enum Former<'source, Node>
{
    /// A rigid base type: `Integer`, `String`, or the numeric atom.
    BaseType(BaseType),
    /// The unit type, `Unit`.
    UnitType,
    /// The product `A * B` of two value types.
    Product(Node, Node),
    /// The sum `A + B` of two value types.
    Sum(Node, Node),
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
    /// The returner `-F A` of a value type.
    Returner(Node),
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
    /// The unit value, `()`.
    Unit,
    /// A literal.
    Literal(&'source Literal),
    /// A pair of values.
    Pair(Node, Node),
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
    fn read(
        &self,
        node: Self::Node,
    ) -> Former<'_, Self::Node>;
}
