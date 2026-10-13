//! Where a described declaration's members are written.
//!
//! Each name, sort, port and term node is kept at its own bytes beside what
//! the description reads, so a face can answer each node with the type its
//! member states ([`crate::described`]).

use alloc::vec::Vec;

use gandr_surface_syntax::ByteSpan;
use gandr_theory_levitation::Name;
use quenchant_shape::shape::Maybe;

quenchant_shape::reason_enum! {
    /// Why a written term node has no head of its own.
    pub mod head {
        /// The reason a node has no head.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// A variable, a constant constructor or a results tuple: the
            /// node is its whole spelling.
            Leaf,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a port has no written name.
    pub mod port_name {
        /// The reason a port is unnamed.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The port is written as its sort alone, `(Nat, Nat) --> Nat`.
            Unnamed,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a member has no written name.
    pub mod member_name {
        /// The reason a member is unnamed.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// A `data` family's rule, `rule add(Zero, n) ==> n`, which names
            /// its operation rather than itself.
            Anonymous,
        }
    }
}

/// One node of a written term: its bytes, and an application's head.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct WrittenNode
{
    /// The bytes the node covers.
    pub span: ByteSpan,
    /// An application's head; absent for a leaf.
    pub head: Maybe<ByteSpan, head::Absent>,
}

/// Where a term's nodes are written: one per node of the term the reader
/// built, in the order a pre-order walk of that term meets them; a
/// parenthesised single term is the term inside.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct WrittenTerm
{
    /// The nodes, in pre-order.
    pub nodes: Vec<WrittenNode>,
}

/// Where a sort is written: the whole sort, and each index term.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WrittenSort
{
    /// The bytes the sort covers.
    pub span: ByteSpan,
    /// Each index term, in written order.
    pub indices: Vec<WrittenTerm>,
}

/// Where a port is written: its name, when it has one, and its sort.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WrittenPort
{
    /// The port's name tile.
    pub named: Maybe<ByteSpan, port_name::Absent>,
    /// Its sort.
    pub sort: WrittenSort,
}

/// Where a sign's sort is written: `sort Hom(dom : Ob, cod : Ob) : Type`.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WrittenSortMember
{
    /// The sort's name tile.
    pub named: ByteSpan,
    /// Its classifier, `Type`.
    pub classifier: ByteSpan,
    /// Each index, in written order.
    pub indices: Vec<WrittenPort>,
}

/// Where an operation is written: its name and each port.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WrittenOperation
{
    /// The operation's name tile.
    pub named: ByteSpan,
    /// Each input port, in written order.
    pub inputs: Vec<WrittenPort>,
    /// Each output port, in written order.
    pub outputs: Vec<WrittenPort>,
}

/// Where a written face is: its name, when it has one, and both sides.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WrittenFace
{
    /// The rule's name tile.
    pub named: Maybe<ByteSpan, member_name::Absent>,
    /// The side it rewrites from.
    pub left: WrittenTerm,
    /// The side it rewrites to.
    pub right: WrittenTerm,
}

/// A name a circuit writes, where it writes it.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WrittenWire
{
    /// The name as written.
    pub name: Name,
    /// The bytes it covers.
    pub span: ByteSpan,
}

/// A circuit rule's data port: its name, its sort as written, and where.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WrittenCircuitPort
{
    /// The port's name.
    pub name: Name,
    /// Its sort, as written.
    pub sort: Name,
    /// Where the port is written.
    pub written: WrittenPort,
}

/// A circuit rule's rewrite port, `rule p : Nat ==> Nat`: its name and the
/// two sides it rewrites between, each a sort or a wire.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WrittenRewrite
{
    /// The port's name tile.
    pub named: WrittenWire,
    /// The side it rewrites from.
    pub left: WrittenWire,
    /// The side it rewrites to.
    pub right: WrittenWire,
}

/// A circuit body's node line, `node : add(x′, y) --> (z)`.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WrittenFrame
{
    /// The head the line applies.
    pub head: WrittenWire,
    /// The wires it reads, in order.
    pub arguments: Vec<WrittenWire>,
    /// The wires it writes, in order.
    pub outputs: Vec<WrittenWire>,
}

/// Where a circuit rule is written: its name, its boundary and its body.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WrittenCircuit
{
    /// The rule's name tile.
    pub named: ByteSpan,
    /// Its data ports, inputs then outputs.
    pub ports: Vec<WrittenCircuitPort>,
    /// Its rewrite ports.
    pub rewrites: Vec<WrittenRewrite>,
    /// Its body's node lines, in written order.
    pub frames: Vec<WrittenFrame>,
}

/// Where a `data` constructor's signature is written: `Succ : (n : Nat) -->
/// Nat`.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WrittenConstructor
{
    /// The constructor's name tile.
    pub named: ByteSpan,
    /// Each field, in written order; a field written as its type alone is
    /// unnamed.
    pub fields: Vec<WrittenPort>,
    /// The result the constructor returns.
    pub result: ByteSpan,
}

/// Where a described declaration's members are written.
///
/// Each list is parallel to the one the description reads its members into:
/// for a `sign`, the presentation's sorts, operations, laws and circuits; for
/// a `data` family, the description's constructors, operations and rules.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct WrittenMembers
{
    /// A `data` family's constructors.
    pub constructors: Vec<WrittenConstructor>,
    /// The sorts.
    pub sorts: Vec<WrittenSortMember>,
    /// The operations.
    pub operations: Vec<WrittenOperation>,
    /// The written faces.
    pub faces: Vec<WrittenFace>,
    /// The circuit rules.
    pub circuits: Vec<WrittenCircuit>,
}
