//! Where a described declaration's members are written.
//!
//! Each name, sort, port and term node is kept at its own bytes beside what
//! the description reads, so a face can answer each node with the type its
//! member states ([`crate::described`]).

use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;

use anodized::spec;
use gandr_kernel_term::GroundSort;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::NodeIndex;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::RowTail;
use gandr_theory_levitation::RuleFace;
use gandr_theory_levitation::ValueTypeRef;
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
            /// The port belongs to a member an `ext` member generates, which
            /// no source writes.
            Generated,
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
            /// A member an `ext` member generates, an operation or a law,
            /// named by the generation rather than by a written tile.
            Generated,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a law has no written arrow.
    pub mod arrow {
        /// The reason a law's arrow is unwritten.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// A law an `ext` member generates, whose direction the generation
            /// fixes and no source writes.
            Generated,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why an observation states no application of its own family.
    pub mod itself {
        /// The reason the result is no self application.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The observation returns a value type its family does not head.
            Returned,
        }
    }
}

/// Which way a written rule runs.
///
/// # Specification
/// - provides: the two directions the order can admit.
/// - panics: none.
/// - executable: none — a closed pair of directions.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RuleDirection
{
    /// The written left side rewrites to the written right.
    LeftToRight,
    /// The written right side rewrites to the written left.
    RightToLeft,
}

/// How a written rule states its direction.
///
/// `<=>` leaves the direction to the order. `==>` pins left to right, the
/// direction the order must admit.
///
/// # Specification
/// - provides: the two ways a rule states its direction.
/// - panics: none.
/// - executable: none — a closed pair of statements.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RuleOrientation
{
    /// `<=>`: the order chooses the direction.
    Unpinned,
    /// The written arrow pins a direction the order must admit.
    Pinned(RuleDirection),
}

/// One written rule, as the declaration keeps it for the printer.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
pub struct SurfaceRule<'rule>
{
    /// The written terms.
    pub face: &'rule RuleFace,
    /// The written arrow and its nodes.
    pub written: &'rule WrittenFace,
}

impl SurfaceRule<'_>
{
    /// The data spelling, `rule lhs <=> rhs`.
    ///
    /// # Specification
    /// - ensures: the written sides in written order, separated by the arrow
    ///   the orientation states.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an unpinned face prints `<=>` between its written
    ///   sides.
    /// - witness: `description::tests::an_equation_states_no_direction`
    #[spec(ensures: |ref text| text.contains("<=>") || text.contains("==>"))]
    #[inline]
    #[must_use]
    pub fn print_data(&self) -> String
    {
        format!(
            "rule {} {} {}",
            self.face.lhs,
            match self.written.orientation {
                RuleOrientation::Unpinned => "<=>",
                RuleOrientation::Pinned(_) => "==>",
            },
            self.face.rhs
        )
    }

    /// The theory spelling, `rule name : lhs <=> rhs`, closed on the `where`
    /// clause of its freshness conditions when it states any, then on the
    /// `under` clause of its row when it fires under one.
    ///
    /// # Specification
    /// - ensures: `name`, then the written sides in written order, separated by
    ///   the arrow the orientation states, then each condition `a # q` in
    ///   written order after `where`, separated by commas, then the row's
    ///   theories in written order after `under [`, separated by commas, with
    ///   `| r` before the `]` when the row is open.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an unpinned face prints `<=>` in the theory spelling,
    ///   a face stating two conditions prints both in order, and a face under
    ///   an open row prints its theories and its tail.
    /// - witness: `description::tests::an_equation_states_no_direction`
    /// - witness: `description::theory::tests::a_where_clause_states_each_condition_on_its_rule`
    /// - witness: `description::theory::tests::an_under_row_names_each_theory_in_scope_once_2448`
    #[spec(ensures: |ref text| text.contains(name.as_ref()) && (text.contains("<=>") || text.contains("==>")) && text.contains(" where ") != self.face.fresh.is_empty() && text.contains(" under [") == matches!(self.face.under, Maybe::Present(_)))]
    #[inline]
    #[must_use]
    pub fn print_theory(
        &self,
        name: &Name,
    ) -> String
    {
        let conditions: Vec<String> = self
            .face
            .fresh
            .iter()
            .map(|condition| format!("{} # {}", condition.atom, condition.term))
            .collect();
        let row = match self.face.under {
            Maybe::Present(ref under) => {
                let theories: Vec<&str> = under.theories.iter().map(AsRef::as_ref).collect();
                format!(" under [{}{}]", theories.join(", "), match under.tail {
                    RowTail::Closed => "",
                    RowTail::Open => " | r",
                })
            },
            Maybe::Absent(_) => String::new(),
        };
        format!(
            "rule {name} : {} {} {}{}{}{row}",
            self.face.lhs,
            match self.written.orientation {
                RuleOrientation::Unpinned => "<=>",
                RuleOrientation::Pinned(_) => "==>",
            },
            self.face.rhs,
            if conditions.is_empty() { "" } else { " where " },
            conditions.join(", ")
        )
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

/// Where a `pi+` binder over a port is written: `x : VTm(a)` in `t : pi+ (x :
/// VTm(a)) . CTm(b)`.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WrittenBound
{
    /// The binder's name tile.
    pub named: ByteSpan,
    /// Its sort.
    pub sort: WrittenSort,
}

/// Where a port is written: its name, when it has one, its binders and its
/// sort.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WrittenPort
{
    /// The port's name tile.
    pub named: Maybe<ByteSpan, port_name::Absent>,
    /// The `pi+` binders written over its sort, outermost first; none for a
    /// first-order port.
    pub binders: Vec<WrittenBound>,
    /// Its sort.
    pub sort: WrittenSort,
}

/// Where a theory's sort is written: `sort Hom(dom : Ob, cod : Ob) : Type`.
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
    /// The operation's name tile; absent for one an `ext` member generates.
    pub named: Maybe<ByteSpan, member_name::Absent>,
    /// Each input port, in written order.
    pub inputs: Vec<WrittenPort>,
    /// Each output port, in written order.
    pub outputs: Vec<WrittenPort>,
    /// The type formers of a judgment written as a thunk of arrows, the thunk
    /// first, each with the sort of types it forms: `+U` a value type, each
    /// `->` and the returner a computation type; for a nested model, its
    /// model type `Model(T)`, a value type. None for a judgment written as
    /// ports.
    pub formers: Vec<(ByteSpan, GroundSort)>,
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
    /// The bytes the written arrow covers; absent for a law an `ext` member
    /// generates.
    pub arrow: Maybe<ByteSpan, arrow::Absent>,
    /// How the written arrow states its direction.
    pub orientation: RuleOrientation,
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
    /// The family's name tile at the result's head.
    pub head: ByteSpan,
    /// Each argument of the result that repeats a family parameter, with the
    /// parameter's name tile.
    pub parameters: Vec<WrittenUse>,
    /// Each argument of the result, the family's parameters then its
    /// indices, in written order.
    pub arguments: Vec<ByteSpan>,
}

/// Where a codata observation is written: its name, and each node of the
/// type it observes, in pre-order.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WrittenObservation
{
    /// The observation's name tile.
    pub named: ByteSpan,
    /// The nodes of its type: the whole type, then each argument of an
    /// application in written order, each read the same way.
    pub ty: WrittenTerm,
    /// The family applied as the observation's result writes it, at the
    /// arguments written, when the family heads the result.
    pub itself: Maybe<SelfApplication, itself::Absent>,
}

/// A codata family applied as an observation's result writes it.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SelfApplication
{
    /// The application, the family its head.
    pub applied: ValueTypeRef,
    /// The node it is written at.
    pub at: NodeIndex,
}

/// A name a member writes for another member of its block: the bytes of the
/// use and the name tile of the member it names.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct WrittenUse
{
    /// The bytes the use covers.
    pub span: ByteSpan,
    /// The name tile of the member it names.
    pub named: ByteSpan,
}

/// Where a `derive` declaration writes the two sides of the rule it states
/// over a theory: each side's term and its nodes in pre-order.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WrittenDerived
{
    /// The left side, and where each of its nodes is written.
    pub left: (FreeTerm, WrittenTerm),
    /// The right side, and where each of its nodes is written.
    pub right: (FreeTerm, WrittenTerm),
}

/// Where a path type a law writes is: `Path(C, l, r)`, its carrier and its
/// two sides.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WrittenPath
{
    /// The bytes the path type covers.
    pub span: ByteSpan,
    /// Its carrier.
    pub carrier: WrittenSort,
    /// The side it starts at, its nodes in pre-order.
    pub left: WrittenTerm,
    /// The side it ends at, its nodes in pre-order.
    pub right: WrittenTerm,
}

/// Where a stated law is written: `law sym : (a : C, b : C) => Path(Bool,
/// eq(a, b), eq(b, a))`.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WrittenLaw
{
    /// The law's name tile.
    pub named: ByteSpan,
    /// The bytes its statement, a value function type, covers.
    pub statement: ByteSpan,
    /// Each binder over a sort, in written order.
    pub binders: Vec<WrittenPort>,
    /// Each hypothesis: its name tile and the path it assumes, in written
    /// order.
    pub hypotheses: Vec<(ByteSpan, WrittenPath)>,
    /// The path it concludes.
    pub path: WrittenPath,
}

/// Where a described declaration's members are written.
///
/// Each list but `uses` is parallel to the one the description reads its
/// members into: for a `theory`, the presentation's sorts, operations, faces,
/// circuits and stated laws; for a `data` family, the description's
/// constructors, operations and rules; for a `codata` family, the
/// description's observations.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct WrittenMembers
{
    /// A `data` family's constructors.
    pub constructors: Vec<WrittenConstructor>,
    /// A `codata` family's observations.
    pub observations: Vec<WrittenObservation>,
    /// The sorts.
    pub sorts: Vec<WrittenSortMember>,
    /// The operations.
    pub operations: Vec<WrittenOperation>,
    /// The written faces.
    pub faces: Vec<WrittenFace>,
    /// The circuit rules.
    pub circuits: Vec<WrittenCircuit>,
    /// For a `theory`, its stated laws, those of the theories it includes
    /// first.
    pub laws: Vec<WrittenLaw>,
    /// The names an `ext` member writes for the face and the boundary
    /// constant it is stated over.
    pub uses: Vec<WrittenUse>,
    /// For a `theory`, the rules `derive` declarations state over it, in the
    /// order they are collected.
    pub derived: Vec<WrittenDerived>,
}
