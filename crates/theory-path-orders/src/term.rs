//! The term view a path order reads: a side of positioned nodes, each node one
//! of the five formers a second-order algebraic theory's terms are built from,
//! and the valuation of a left side's variables.
//!
//! A side numbers its nodes densely from its root, `0`, and every node's
//! arguments sit at positions past its own, so a table over two sides filled
//! from the last positions up reads every argument pair before the pair above
//! it. Pre-order and breadth-first numberings both qualify.
//!
//! The formers are the signature's own symbols applied to their arguments,
//! and the binding structure of Kaposi and Xie's theory of signatures: a rule
//! variable, a rule variable instantiated at terms (`·⁺`), an abstraction of
//! one name over a body (`lam⁺`) and an occurrence of a name an abstraction
//! binds. A term is read η-long and β-normal, so an instantiation's head is
//! always a variable.

/// A node's position in a side.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Node(usize);

impl From<usize> for Node
{
    /// The node at `position`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: usize) -> Self
    {
        Self(position)
    }
}

impl From<Node> for usize
{
    /// The node's position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(node: Node) -> Self
    {
        node.0
    }
}

/// What a node applies to its arguments.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Former<S, V, B>
{
    /// `f(t̄)`: a symbol of the signature — an operation, a constructor, a
    /// results tuple — applied to the node's arguments.
    Symbol(S),
    /// A rule variable, bare.
    Variable(V),
    /// `x ·⁺ ū`: a rule variable instantiated at the node's arguments, one per
    /// name the binding that binds it binds.
    Application(V),
    /// `lam⁺`: one name bound over the node's one argument, its body.
    Abstraction,
    /// An occurrence of a name an abstraction binds.
    Bound(B),
}

/// One side of a comparison: a term as positioned nodes.
///
/// # Specification
/// - requires: positions `0 .. end` are the side's nodes, `0` its root, and
///   every node's arguments sit at positions past its own and before `end`.
/// - ensures: a path order reads only these three observations.
/// - panics: none.
/// - executable: none — a trait declaration; each implementation's witnesses
///   observe its numbering.
pub trait Term
{
    /// The signature's symbols, compared by identity.
    type Symbol: Copy + Eq;
    /// The rule variables, compared by identity.
    type Variable: Copy + Eq;
    /// The occurrences of bound names, compared by identity.
    type Bound: Copy + Eq;

    /// The position past the last node: the side's node count.
    ///
    /// # Specification
    /// trivial.
    fn end(&self) -> Node;

    /// What the node at `node` applies.
    ///
    /// # Specification
    /// - requires: `node` is before [`Term::end`].
    /// - ensures: the node's former.
    /// - panics: none.
    /// - executable: none — a trait method; implementations state theirs.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the five formers are told apart: a variable and an
    ///   instantiation on the left are above nothing, an instantiation on the
    ///   right is below the application holding its variable, and an
    ///   abstraction and a bound occurrence stand where a ground symbol does.
    /// - witness: `tests::lpo::a_variable_or_an_equal_side_is_above_nothing`
    /// - witness: `tests::lpo::an_instantiation_on_the_left_is_above_nothing`
    /// - witness: `tests::lpo::an_instantiation_is_below_the_application_holding_its_variable`
    /// - witness: `tests::lpo::an_abstraction_and_a_bound_occurrence_stand_where_a_ground_symbol_does`
    fn former(
        &self,
        node: Node,
    ) -> Former<Self::Symbol, Self::Variable, Self::Bound>;

    /// The positions of the node's arguments, left to right.
    ///
    /// # Specification
    /// - requires: `node` is before [`Term::end`].
    /// - ensures: each position is past `node` and before [`Term::end`]; an
    ///   abstraction has exactly one, a variable and a bound occurrence none.
    /// - panics: none.
    /// - executable: none — a trait method; implementations state theirs.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a pattern is read through the abstraction above it,
    ///   and a derivation whose steps name positions the arguments do not
    ///   relate is refused.
    /// - witness: `tests::lpo::a_pattern_under_its_abstraction_holds_its_variable`
    /// - witness: `tests::lpo::a_forged_derivation_is_refused`
    fn arguments(
        &self,
        node: Node,
    ) -> impl Iterator<Item = Node> + Clone;
}

/// A left side whose variables are read by sort.
///
/// # Specification
/// - requires: nothing beyond [`Term`].
/// - ensures: [`Valued::valuation`] answers for every variable of the side.
/// - panics: none.
/// - executable: none — a trait declaration.
pub trait Valued: Term
{
    /// How `variable` stands: a value when every occurrence of it on the side
    /// is an argument at a port of a sort no operation returns, so only
    /// constructors and variables build what it stands for.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the variable's valuation.
    /// - panics: none.
    /// - executable: none — a trait method; implementations state theirs.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an instance argument a value stands for needs no
    ///   cover, where the same argument as a term does.
    /// - witness: `tests::lpo::a_value_needs_no_cover`
    fn valuation(
        &self,
        variable: Self::Variable,
    ) -> Valuation;
}

/// How a left side's variable stands.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Valuation
{
    /// A value: instantiating a pattern at it selects a branch and calls no
    /// operation.
    Value,
    /// Any term of its sort.
    Term,
}
