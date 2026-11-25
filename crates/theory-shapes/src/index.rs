//! The nominal indices and cardinalities a shape query crosses.

wrapper! {
    /// A point of a finite carrier, numbered from zero.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Point(usize);
}

wrapper! {
    /// The number of points of a finite carrier.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct PointCount(usize);
}

wrapper! {
    /// A shape variable: a position in a query's context.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Variable(usize);
}

wrapper! {
    /// A formula node's position in its flat table.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct NodeId(usize);
}

wrapper! {
    /// A term's position in a monotone normal form, whose terms are sorted by
    /// the variables they meet.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct TermIndex(usize);
}
