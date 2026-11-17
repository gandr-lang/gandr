//! The indices, counts and two-way verdicts the duality's operations cross.

/// The most generators a term holds, and the most elements or points a
/// finite poset or a lattice of sets holds: the bits of one machine word.
pub const WIDEST: usize = 64;

/// The most axes a cube has when its vertices fit one machine word: `2⁶`
/// vertices.
pub const WIDEST_CUBE: usize = 6;

wrapper! {
    /// A generator of a free distributive lattice, numbered from zero. It is
    /// also an axis of the cube that is the lattice's spectrum.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Generator(usize);
}

wrapper! {
    /// The number of generators of a free distributive lattice, which is the
    /// number of axes of its cube.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct GeneratorCount(usize);
}

wrapper! {
    /// An element of a finite poset, or a point of the carrier of a lattice
    /// of sets, numbered from zero.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Element(usize);
}

wrapper! {
    /// The number of elements of a finite poset, or of points of a carrier.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct ElementCount(usize);
}

wrapper! {
    /// The most members an enumeration produces before it refuses its input.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Budget(usize);
}

/// Whether one element lies below another in an order.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Comparison
{
    /// The first is below the second, or equal to it.
    Below,
    /// The first is not below the second.
    NotBelow,
}

/// Whether a set holds an element, or whether a polynomial holds at a vertex.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Membership
{
    /// The set holds the element, or the polynomial holds at the vertex.
    Inside,
    /// The set lacks the element, or the polynomial fails at the vertex.
    Outside,
}
