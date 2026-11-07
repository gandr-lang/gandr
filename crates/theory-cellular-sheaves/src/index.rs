//! The names of the positions, sizes and signs that the sheaf reads.

wrapper! {
    /// An entry of a stalk, numbered from zero.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Entry(usize);
}

wrapper! {
    /// The number of entries of a stalk or a section.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Width(usize);
}

wrapper! {
    /// The dimension of a space of cochains or of a cohomology group over the
    /// rationals, or the rank of a map between them.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Dimension(usize);
}

wrapper! {
    /// A member of a cover, by its place in the cover.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct CoverIndex(usize);
}

wrapper! {
    /// A level of a tower, numbered from the first, which is the coarsest.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Level(usize);
}

wrapper! {
    /// A row or a column of a matrix: a position in a space of cochains.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Slot(usize);
}

wrapper! {
    /// A 128-bit integer: the numerator or the denominator of a rational.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Integer(i128);
}

/// The incidence of a face in a cell one rank above it: the sign with which
/// the coboundary adds the face's restriction to the cell.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Incidence
{
    /// The face enters the coboundary with a plus sign, as the head of an
    /// edge does.
    Positive,
    /// The face enters the coboundary with a minus sign, as the tail of an
    /// edge does.
    Negative,
    /// The face enters the coboundary twice with opposite signs, so not at
    /// all, as the one end of a loop does.
    Zero,
}
