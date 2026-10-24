//! The evidence an ordering returns when it orients a pair.
//!
//! The evidence is the derivation of the comparison: one step per pair of
//! subterms it compares, each naming the clause of the order that puts its
//! left subterm above its right.
//!
//! A step's premises are other pairs: the arguments it compares, found among
//! the derivation's steps by their positions, and the equalities it reads,
//! which a checker decides by comparing the two subterms. Every premise pairs
//! a position past one of the step's own, so a derivation every step of which
//! holds locally and whose root pair is a step is a derivation of the root:
//! nothing in it is searched for and nothing justifies itself.
//!
//! The clauses are named for the rules of the computability path order of
//! Blanqui, Jouannaud and Rubio that they are, or that they compose.

use alloc::vec::Vec;

use crate::term::Node;

/// What an ordering returns for a pair it orients.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Evidence
{
    /// A path order's derivation.
    Path(Derivation),
}

/// A path order's derivation of one comparison: its steps, ordered by their
/// positions, and the covers the steps name.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Derivation
{
    /// The steps, ordered by left position, then right.
    steps: Vec<Step>,
    /// Each covering step's covers, one per argument of its right subterm, the
    /// step's own run starting at its [`Step::first_cover`].
    covers: Vec<Cover>,
}

impl Derivation
{
    /// The derivation of `steps` and `covers`: the replay a checker decides,
    /// whoever built it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        steps: Vec<Step>,
        covers: Vec<Cover>,
    ) -> Self
    {
        Self { steps, covers }
    }

    /// The steps, ordered by left position, then right.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn steps(&self) -> &[Step]
    {
        &self.steps
    }

    /// The covers.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn covers(&self) -> &[Cover]
    {
        &self.covers
    }
}

/// One step of a derivation: the clause that puts the left subterm at `left`
/// above the right subterm at `right`.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Step
{
    /// The left subterm's position.
    left: Node,
    /// The right subterm's position.
    right: Node,
    /// The clause.
    clause: Clause,
    /// Where the step's covers start, when its clause takes covers.
    first_cover: CoverIndex,
}

impl Step
{
    /// The step putting `left` above `right` by `clause`, its covers, if any,
    /// starting at `first_cover`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        left: Node,
        right: Node,
        clause: Clause,
        first_cover: CoverIndex,
    ) -> Self
    {
        Self {
            left,
            right,
            clause,
            first_cover,
        }
    }

    /// The left subterm's position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn left(&self) -> Node
    {
        self.left
    }

    /// The right subterm's position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn right(&self) -> Node
    {
        self.right
    }

    /// The clause.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn clause(&self) -> Clause
    {
        self.clause
    }

    /// Where the step's covers start.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn first_cover(&self) -> CoverIndex
    {
        self.first_cover
    }
}

/// The clause of the order a step applies.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Clause
{
    /// (F⊳): the left subterm's argument at `argument` is equal to the right
    /// subterm or above it.
    Subterm
    {
        /// Which argument.
        argument: Argument,
        /// How it stands to the right subterm.
        relation: Relation,
    },
    /// (F>): the left head precedes the right head, and the left subterm
    /// covers every argument of the right.
    Precedence,
    /// (F=) at lexicographic status: one head, the arguments before
    /// `argument` pairwise equal and the pair at `argument` ordered, and the
    /// left subterm covers every argument of the right.
    Lexicographic
    {
        /// The first argument pair that differs.
        argument: Argument,
    },
    /// (F=) at multiset status: one head, and the covers match each right
    /// argument with a left one equal to it, no left argument twice, or with
    /// a left argument above it that no right argument equals; some left
    /// argument is matched by no equality.
    Multiset,
    /// (F@) down an instantiation's spine to (F⊳) at its head, read through
    /// (λη): the left subterm's argument at `held` is the variable the right
    /// subterm instantiates, or that variable instantiated under the
    /// abstractions of the names it is applied to; and the left subterm covers
    /// every argument of the instantiation that is not a value.
    Instance
    {
        /// The argument holding the variable.
        held: Argument,
    },
}

/// How a left subterm stands to a right one.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Relation
{
    /// The two are one term.
    Equal,
    /// The left is above the right, by the step at the pair.
    Above,
}

/// How a covering step covers one argument of its right subterm.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Cover
{
    /// The step's left subterm is above the argument, by the step at the pair.
    Above,
    /// The step's left subterm's own argument at `argument` is equal to the
    /// right argument or above it.
    Argument
    {
        /// Which of the left subterm's arguments.
        argument: Argument,
        /// How it stands to the right argument.
        relation: Relation,
    },
    /// The argument is a value, which an instantiation needs no cover of.
    Value,
}

/// An argument's index among its node's arguments, left to right.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Argument(usize);

impl From<usize> for Argument
{
    /// The argument at `index`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: usize) -> Self
    {
        Self(index)
    }
}

impl From<Argument> for usize
{
    /// The argument's index.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(argument: Argument) -> Self
    {
        argument.0
    }
}

/// A cover's index in a derivation.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CoverIndex(usize);

impl From<usize> for CoverIndex
{
    /// The cover at `index`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: usize) -> Self
    {
        Self(index)
    }
}

impl From<CoverIndex> for usize
{
    /// The cover's index.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: CoverIndex) -> Self
    {
        index.0
    }
}
