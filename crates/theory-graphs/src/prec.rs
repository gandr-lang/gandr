//! The operator-precedence DAG: named precedence groups, each with an
//! associativity, ordered by a tighter-than relation that must be acyclic.
//!
//! [`PrecSpec`] collects the groups and the edges; [`PrecDag::build`] refuses
//! a cyclic relation with the cycle as evidence and otherwise precomputes the
//! transitive closure, so every comparison is a lookup. Comparisons take the
//! associativity a caller asserts beside the two groups: a group compares
//! with itself only in the direction its declared associativity names, and
//! only when the caller asserts the same associativity.

use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::vec::Vec;
use core::error::Error;
use core::fmt::Display;
use core::fmt::Formatter;
use core::fmt::Result as FmtResult;

use crate::EdgeSource;
use crate::Fingerprint;
use crate::FingerprintByte;
use crate::FingerprintWord16;
use crate::FingerprintWord64;
use crate::Fnv64;
use crate::GraphValidationError;
use crate::NodeCount;
use crate::NodeId;
use crate::cycle_witness;
use crate::reachability;
use crate::types::NodePosition;
use crate::types::primitive_newtype;

primitive_newtype! {
    display
    /// The dense index of one precedence group: groups are numbered in
    /// insertion order from zero.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct PrecIndex(u16);
}

impl From<PrecIndex> for u32
{
    /// Widens the index.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: PrecIndex) -> Self
    {
        Self::from(u16::from(value))
    }
}

primitive_newtype! {
    display
    /// How many precedence groups a specification or DAG declares.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct PrecGroupCount(usize);
}

primitive_newtype! {
    /// The answer to one precedence comparison.
    #[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
    pub struct PrecedenceComparison(bool);
}

primitive_newtype! {
    /// Whether a specification or DAG declares no groups.
    #[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
    pub struct PrecSetEmpty(bool);
}

primitive_newtype! {
    /// Whether an id names a group of the DAG or specification at hand.
    #[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
    struct PrecValidity(bool);
}

/// The borrowed name of one precedence group.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PrecName<'name>(&'name str);

impl<'name> From<&'name str> for PrecName<'name>
{
    /// Borrows the name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: &'name str) -> Self
    {
        Self(value)
    }
}

impl<'name> From<PrecName<'name>> for &'name str
{
    /// Reads the borrowed name back out.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: PrecName<'name>) -> Self
    {
        value.0
    }
}

impl AsRef<str> for PrecName<'_>
{
    /// Borrows the name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        self.0
    }
}

impl Display for PrecName<'_>
{
    /// Writes the name.
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

impl PartialEq<PrecName<'_>> for &str
{
    /// Compares the text with the name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn eq(
        &self,
        other: &PrecName<'_>,
    ) -> bool
    {
        *self == other.0
    }
}

impl PartialEq<&str> for PrecName<'_>
{
    /// Compares the name with the text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn eq(
        &self,
        other: &&str,
    ) -> bool
    {
        self.0 == *other
    }
}

/// One precedence group's identity in the specification it was inserted
/// into.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Prec(PrecIndex);

impl Prec
{
    /// Names the group at `index`, without checking that it exists.
    ///
    /// # Specification
    /// - requires: nothing; an index past the groups is a valid probe, and
    ///   every query answers it as an unknown group.
    /// - ensures: [`index`](Self::index) returns `index`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 pointwise — ids built past the last group are refused
    ///   by every query, one past the end included.
    /// - witness: `tests::prec::prec_dag_size_and_boundary_contract`
    #[inline]
    #[must_use]
    pub const fn new(index: PrecIndex) -> Self
    {
        Self(index)
    }

    /// Reports the group's dense index.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn index(self) -> PrecIndex
    {
        self.0
    }
}

/// The associativity a precedence group declares, and the one a comparison
/// asserts.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Assoc
{
    /// Left-associative: the group is greater than itself.
    Left,
    /// Right-associative: the group is less than itself.
    Right,
    /// Non-associative: the group is equal to itself, never less or greater.
    Non,
}

/// A concrete precedence or one of the two virtual bounds around every
/// concrete precedence.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Bound<T>
{
    /// Below every concrete precedence.
    Bottom,
    /// A concrete precedence.
    Value(T),
    /// Above every concrete precedence.
    Root,
}

/// A refused precedence-specification edit.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PrecSpecError
{
    /// Every 16-bit group index is already taken.
    CapacityExceeded,
    /// A group of that name already exists.
    DuplicateName
    {
        /// The refused name.
        name: String,
    },
    /// An edge names a group the specification does not declare.
    InvalidEdge
    {
        /// The tighter endpoint as supplied.
        tighter: Prec,
        /// The looser endpoint as supplied.
        looser: Prec,
        /// How many groups the specification declares.
        node_count: NodeCount,
    },
}

impl Display for PrecSpecError
{
    /// Writes the refusal with the values it names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut Formatter<'_>,
    ) -> FmtResult
    {
        match *self {
            | Self::CapacityExceeded => f.write_str("precedence id capacity exceeded"),
            | Self::DuplicateName { ref name } => write!(f, "duplicate precedence name {name}"),
            | Self::InvalidEdge {
                tighter,
                looser,
                node_count,
            } => write!(
                f,
                "precedence edge {}>{} is outside 0..{node_count}",
                tighter.index(),
                looser.index(),
            ),
        }
    }
}

impl Error for PrecSpecError
{
}

/// Named precedence groups and the tighter-than edges between them, before
/// the relation is checked for cycles.
///
/// # Adequacy
/// - hypothesis: L3 pointwise — size and boundary, duplicate-name,
///   duplicate-edge, invalid-edge and capacity witnesses separate every branch
///   of the builder.
/// - witness: `tests::prec::prec_spec_size_and_boundary_contract`
/// - witness: `tests::prec::duplicate_edge_canonicalization_and_invalid_edges`
/// - witness: `tests::prec::capacity_beyond_u16_is_typed`
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct PrecSpec
{
    /// Group names in index order.
    names: Vec<String>,
    /// The names again, for the duplicate check: a linear scan would make
    /// bulk insertion quadratic. A `BTreeSet` keeps [`PrecSpec::new`] const.
    name_index: BTreeSet<String>,
    /// Group associativity in index order.
    assocs: Vec<Assoc>,
    /// Tighter-to-looser edges, ascending and without repetition.
    edges: Vec<(Prec, Prec)>,
}

impl PrecSpec
{
    /// Starts an empty specification.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new() -> Self
    {
        Self {
            names: Vec::new(),
            name_index: BTreeSet::new(),
            assocs: Vec::new(),
            edges: Vec::new(),
        }
    }

    /// Declares a group and returns its id.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the group's index is the number of groups declared
    ///   before it, and [`name`](Self::name) and [`assoc`](Self::assoc) report
    ///   `name` and `assoc` for it.
    /// - fails: the name is taken, or all 65 536 indices are; a refused
    ///   insertion leaves the specification unchanged.
    /// - panics: none.
    ///
    /// # Errors
    /// [`PrecSpecError::DuplicateName`] for a taken name,
    /// [`PrecSpecError::CapacityExceeded`] past the last 16-bit index.
    ///
    /// # Adequacy
    /// - hypothesis: L3 pointwise — every index of a full specification is
    ///   observed in insertion order and the next insertion is refused; a
    ///   repeated name is refused by name.
    /// - witness: `tests::prec::capacity_beyond_u16_is_typed`
    /// - witness: `tests::prec::duplicate_edge_canonicalization_and_invalid_edges`
    #[inline]
    pub fn insert<N>(
        &mut self,
        name: N,
        assoc: Assoc,
    ) -> Result<Prec, PrecSpecError>
    where
        N: Into<String>,
    {
        let name = name.into();
        if self.name_index.contains(&name) {
            return Err(PrecSpecError::DuplicateName { name });
        }
        let index =
            u16::try_from(self.names.len()).map_err(|_full| PrecSpecError::CapacityExceeded)?;
        self.name_index.insert(name.clone());
        self.names.push(name);
        self.assocs.push(assoc);
        Ok(Prec::new(PrecIndex::from(index)))
    }

    /// Declares that `tighter` binds tighter than `looser`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success [`edges`](Self::edges) contains the pair once,
    ///   however often it is added; the stored edges stay ascending.
    /// - fails: either endpoint is not a declared group.
    /// - panics: none.
    ///
    /// # Errors
    /// [`PrecSpecError::InvalidEdge`] for an undeclared endpoint.
    ///
    /// # Adequacy
    /// - hypothesis: L3 pointwise — a repeated edge is stored once, and an
    ///   endpoint one past the last group is refused naming both endpoints.
    /// - witness: `tests::prec::duplicate_edge_canonicalization_and_invalid_edges`
    /// - witness: `tests::prec::prec_spec_size_and_boundary_contract`
    #[inline]
    pub fn add_edge(
        &mut self,
        tighter: Prec,
        looser: Prec,
    ) -> Result<(), PrecSpecError>
    {
        if !bool::from(valid(&self.names, tighter)) || !bool::from(valid(&self.names, looser)) {
            return Err(PrecSpecError::InvalidEdge {
                tighter,
                looser,
                node_count: group_node_count(&self.names),
            });
        }
        let edge = (tighter, looser);
        if let Err(position) = self.edges.binary_search(&edge) {
            self.edges.insert(position, edge);
        }
        Ok(())
    }

    /// Reports how many groups are declared.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn len(&self) -> PrecGroupCount
    {
        PrecGroupCount::from(self.names.len())
    }

    /// Reports whether no group is declared.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> PrecSetEmpty
    {
        PrecSetEmpty::from(self.names.is_empty())
    }

    /// Reports a group's name; an undeclared id has none.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn name(
        &self,
        prec: Prec,
    ) -> Option<PrecName<'_>>
    {
        name_of(&self.names, prec)
    }

    /// Reports a group's associativity; an undeclared id has none.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn assoc(
        &self,
        prec: Prec,
    ) -> Option<Assoc>
    {
        assoc_of(&self.assocs, prec)
    }

    /// Yields every group with its name and associativity, in index order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn groups(&self) -> impl Iterator<Item = (Prec, PrecName<'_>, Assoc)> + '_
    {
        groups_of(&self.names, &self.assocs)
    }

    /// Yields every edge as a tighter-looser pair, ascending.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn edges(&self) -> impl Iterator<Item = (Prec, Prec)> + '_
    {
        self.edges.iter().copied()
    }
}

/// A closed walk of tighter-than edges: the evidence that a precedence
/// relation is cyclic.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PrecCycle
{
    /// The walk's groups; the first and last are the same group.
    pub witness: Vec<Prec>,
}

impl Display for PrecCycle
{
    /// Writes the walk's group indices in order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut Formatter<'_>,
    ) -> FmtResult
    {
        f.write_str("precedence cycle")?;
        for prec in &self.witness {
            write!(f, " {}", prec.index())?;
        }
        Ok(())
    }
}

impl Error for PrecCycle
{
}

/// Why [`PrecDag::build`] refused a specification.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PrecDagError
{
    /// The tighter-than relation is cyclic.
    Cycle(PrecCycle),
    /// A graph algorithm refused the relation's dense encoding: only on a host
    /// whose address space cannot hold one slot per group.
    Graph(GraphValidationError),
    /// The linear extension of a relation found acyclic left groups
    /// unordered: an internal invariant failed.
    Inconsistent,
}

impl Display for PrecDagError
{
    /// Writes the refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut Formatter<'_>,
    ) -> FmtResult
    {
        match *self {
            | Self::Cycle(ref cycle) => Display::fmt(cycle, f),
            | Self::Graph(ref error) => Display::fmt(error, f),
            | Self::Inconsistent => f.write_str("precedence linear extension is inconsistent"),
        }
    }
}

impl Error for PrecDagError
{
    /// Reports the refusal underneath, if there is one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn source(&self) -> Option<&(dyn Error + 'static)>
    {
        match *self {
            | Self::Cycle(ref cycle) => Some(cycle),
            | Self::Graph(ref error) => Some(error),
            | Self::Inconsistent => None,
        }
    }
}

/// An acyclic precedence relation with its transitive closure and a
/// deterministic linear extension precomputed.
///
/// # Adequacy
/// - hypothesis: L3 pointwise plus L1 cycle evidence — a diamond, integer
///   chains and the virtual bounds separate strict reachability from the
///   reflexive associativity cases; self and three-group cycles are refused
///   with closed walks over input edges.
/// - witness: `tests::prec::prec_dag_contract`
/// - witness: `tests::prec::prec_integer_chain_oracle`
/// - witness: `tests::prec::prec_cycle_witness_contract`
#[derive(Clone, Debug)]
pub struct PrecDag
{
    /// Group names in index order.
    names: Vec<String>,
    /// Group associativity in index order.
    assocs: Vec<Assoc>,
    /// Tighter-to-looser edges, ascending and without repetition.
    edges: Vec<(Prec, Prec)>,
    /// Per group, every group it is strictly tighter than, ascending.
    reachability: Vec<Vec<Prec>>,
    /// Every group, each before every group it is tighter than.
    linear_extension: Vec<Prec>,
}

impl PrecDag
{
    /// Checks a specification for cycles and precomputes its closure.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the DAG carries the specification's groups and
    ///   edges, `a` is strictly tighter than `b` exactly when a non-empty path
    ///   of edges leads from `a` to `b`, and
    ///   [`linear_extension`](Self::linear_extension) lists every group once,
    ///   each before every group it is tighter than, choosing the smallest
    ///   index whenever several are ready.
    /// - fails: the relation is cyclic, with the first cycle a depth-first
    ///   search in index order meets as evidence.
    /// - panics: none.
    ///
    /// # Errors
    /// [`PrecDagError::Cycle`] for a cyclic relation;
    /// [`PrecDagError::Graph`] when the host cannot hold one slot per group;
    /// [`PrecDagError::Inconsistent`] when an internal invariant fails.
    ///
    /// # Adequacy
    /// - hypothesis: L3 pointwise plus L1 cycle evidence — a self edge yields
    ///   the two-element walk; a three-group cycle yields a closed walk over
    ///   input edges; a diamond and chains pin the closure; a disconnected
    ///   relation pins the smallest-ready tie-break.
    /// - witness: `tests::prec::prec_cycle_witness_contract`
    /// - witness: `tests::prec::prec_dag_contract`
    /// - witness: `tests::prec::deterministic_linear_extension_uses_smallest_ready_id`
    #[inline]
    pub fn build(spec: &PrecSpec) -> Result<Self, PrecDagError>
    {
        let graph = PrecGraph::from_spec(spec);
        let cycle = cycle_witness(&graph).map_err(PrecDagError::Graph)?;
        if let Some(found) = cycle {
            let witness = precs_of_nodes(found.nodes)?;
            return Err(PrecDagError::Cycle(PrecCycle { witness }));
        }
        let closure = reachability(&graph).map_err(PrecDagError::Graph)?;
        let mut reachability = Vec::with_capacity(closure.rows.len());
        for row in closure.rows {
            let targets = precs_of_nodes(row.targets)?;
            reachability.push(targets);
        }
        let linear_extension = linear_extension(&graph)?;
        Ok(Self {
            names: spec.names.clone(),
            assocs: spec.assocs.clone(),
            edges: spec.edges.clone(),
            reachability,
            linear_extension,
        })
    }

    /// Reports how many groups the DAG has.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn len(&self) -> PrecGroupCount
    {
        PrecGroupCount::from(self.names.len())
    }

    /// Reports whether the DAG has no group.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> PrecSetEmpty
    {
        PrecSetEmpty::from(self.names.is_empty())
    }

    /// Reports a group's name; an unknown id has none.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn name(
        &self,
        prec: Prec,
    ) -> Option<PrecName<'_>>
    {
        name_of(&self.names, prec)
    }

    /// Reports a group's associativity; an unknown id has none.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn assoc(
        &self,
        prec: Prec,
    ) -> Option<Assoc>
    {
        assoc_of(&self.assocs, prec)
    }

    /// Yields every group with its name and associativity, in index order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn groups(&self) -> impl Iterator<Item = (Prec, PrecName<'_>, Assoc)> + '_
    {
        groups_of(&self.names, &self.assocs)
    }

    /// Yields every edge as a tighter-looser pair, ascending.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn edges(&self) -> impl Iterator<Item = (Prec, Prec)> + '_
    {
        self.edges.iter().copied()
    }

    /// Lists every group, each before every group it is tighter than.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn linear_extension(&self) -> &[Prec]
    {
        &self.linear_extension
    }

    /// Answers whether `left` is less than `right`: whether `right` binds
    /// tighter, or both are one right-associative group asserted
    /// right-associative.
    ///
    /// # Specification
    /// - requires: nothing; unknown ids are valid inputs.
    /// - ensures: for distinct known groups, true exactly when `right` is
    ///   strictly tighter than `left`; for one known group, true exactly when
    ///   it is declared [`Assoc::Right`] and `assoc` is [`Assoc::Right`]; false
    ///   when either id is unknown.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 pointwise plus L2 generative — a diamond and a
    ///   three-group chain pin every pair, incomparable siblings included;
    ///   generated chains check the duality with [`gt`](Self::gt) and that
    ///   `assoc` matters only for a group compared with itself.
    /// - witness: `tests::prec::prec_dag_contract`
    /// - witness: `tests::prec::prec_integer_chain_oracle`
    /// - witness: `tests::prec::lt_gt_duality_for_distinct_chain_nodes`
    /// - witness: `tests::prec::associativity_affects_reflexive_pairs_only`
    #[inline]
    #[must_use]
    pub fn lt(
        &self,
        left: Prec,
        right: Prec,
        assoc: Assoc,
    ) -> PrecedenceComparison
    {
        if !bool::from(self.knows(left)) || !bool::from(self.knows(right)) {
            return PrecedenceComparison::from(false);
        }
        if left == right {
            return PrecedenceComparison::from(
                self.assoc(left) == Some(Assoc::Right) && assoc == Assoc::Right,
            );
        }
        self.strictly_tighter(right, left)
    }

    /// Answers whether `left` is greater than `right`: whether `left` binds
    /// tighter, or both are one left-associative group asserted
    /// left-associative.
    ///
    /// # Specification
    /// - requires: nothing; unknown ids are valid inputs.
    /// - ensures: for distinct known groups, true exactly when `left` is
    ///   strictly tighter than `right`; for one known group, true exactly when
    ///   it is declared [`Assoc::Left`] and `assoc` is [`Assoc::Left`]; false
    ///   when either id is unknown.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 pointwise plus L2 generative — as [`lt`](Self::lt),
    ///   with the left-associative reflexive case.
    /// - witness: `tests::prec::prec_dag_contract`
    /// - witness: `tests::prec::prec_integer_chain_oracle`
    /// - witness: `tests::prec::lt_gt_duality_for_distinct_chain_nodes`
    /// - witness: `tests::prec::associativity_affects_reflexive_pairs_only`
    #[inline]
    #[must_use]
    pub fn gt(
        &self,
        left: Prec,
        right: Prec,
        assoc: Assoc,
    ) -> PrecedenceComparison
    {
        if !bool::from(self.knows(left)) || !bool::from(self.knows(right)) {
            return PrecedenceComparison::from(false);
        }
        if left == right {
            return PrecedenceComparison::from(
                self.assoc(left) == Some(Assoc::Left) && assoc == Assoc::Left,
            );
        }
        self.strictly_tighter(left, right)
    }

    /// Answers whether `left` equals `right`: one non-associative group,
    /// asserted non-associative.
    ///
    /// # Specification
    /// - requires: nothing; unknown ids are valid inputs.
    /// - ensures: true exactly when both ids are one known group declared
    ///   [`Assoc::Non`] and `assoc` is [`Assoc::Non`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 pointwise — a non-associative group equals itself only
    ///   under the non-associative assertion, and an associative group never
    ///   equals itself.
    /// - witness: `tests::prec::prec_dag_contract`
    /// - witness: `tests::prec::bound_value_reflexive_association_tracks_direction`
    #[inline]
    #[must_use]
    pub fn eq(
        &self,
        left: Prec,
        right: Prec,
        assoc: Assoc,
    ) -> PrecedenceComparison
    {
        PrecedenceComparison::from(
            left == right && self.assoc(left) == Some(Assoc::Non) && assoc == Assoc::Non,
        )
    }

    /// Answers whether two groups are ordered at all: equal, or one tighter
    /// than the other.
    ///
    /// # Specification
    /// - requires: nothing; unknown ids are valid inputs.
    /// - ensures: for known groups, true exactly when they are the same group
    ///   or one is strictly tighter than the other; false when either id is
    ///   unknown.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 pointwise plus L2 generative — diamond siblings are
    ///   incomparable and every chain pair is comparable; generated chains
    ///   check symmetry and the refusal of unknown ids.
    /// - witness: `tests::prec::prec_dag_contract`
    /// - witness: `tests::prec::comparable_is_symmetric_and_rejects_invalid_boundaries`
    #[inline]
    #[must_use]
    pub fn comparable(
        &self,
        left: Prec,
        right: Prec,
    ) -> PrecedenceComparison
    {
        if !bool::from(self.knows(left)) || !bool::from(self.knows(right)) {
            return PrecedenceComparison::from(false);
        }
        PrecedenceComparison::from(
            left == right
                || bool::from(self.strictly_tighter(left, right))
                || bool::from(self.strictly_tighter(right, left)),
        )
    }

    /// Answers [`lt`](Self::lt) over bounds: [`Bound::Bottom`] is below and
    /// [`Bound::Root`] above every known group.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: two values compare as [`lt`](Self::lt); `Bottom` is less than
    ///   `Root` and than every known group; every known group is less than
    ///   `Root`; nothing is less than `Bottom` and `Root` is less than nothing.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 pointwise — each pairing of a virtual bound with a
    ///   known group, an unknown group and the other bound is observed.
    /// - witness: `tests::prec::virtual_bound_comparisons`
    /// - witness: `tests::prec::prec_dag_size_and_boundary_contract`
    #[inline]
    #[must_use]
    pub fn bound_lt(
        &self,
        left: Bound<Prec>,
        right: Bound<Prec>,
        assoc: Assoc,
    ) -> PrecedenceComparison
    {
        match (left, right) {
            | (Bound::Root, _) | (_, Bound::Bottom) => PrecedenceComparison::from(false),
            | (Bound::Bottom, Bound::Root) => PrecedenceComparison::from(true),
            | (Bound::Bottom, Bound::Value(prec)) | (Bound::Value(prec), Bound::Root) => {
                PrecedenceComparison::from(bool::from(self.knows(prec)))
            },
            | (Bound::Value(left), Bound::Value(right)) => self.lt(left, right, assoc),
        }
    }

    /// Answers [`gt`](Self::gt) over bounds: [`Bound::Root`] is above and
    /// [`Bound::Bottom`] below every known group.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the mirror image of [`bound_lt`](Self::bound_lt).
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 pointwise — as [`bound_lt`](Self::bound_lt), mirrored.
    /// - witness: `tests::prec::virtual_bound_comparisons`
    /// - witness: `tests::prec::bound_value_reflexive_association_tracks_direction`
    #[inline]
    #[must_use]
    pub fn bound_gt(
        &self,
        left: Bound<Prec>,
        right: Bound<Prec>,
        assoc: Assoc,
    ) -> PrecedenceComparison
    {
        match (left, right) {
            | (Bound::Bottom, _) | (_, Bound::Root) => PrecedenceComparison::from(false),
            | (Bound::Root, Bound::Bottom) => PrecedenceComparison::from(true),
            | (Bound::Root, Bound::Value(prec)) | (Bound::Value(prec), Bound::Bottom) => {
                PrecedenceComparison::from(bool::from(self.knows(prec)))
            },
            | (Bound::Value(left), Bound::Value(right)) => self.gt(left, right, assoc),
        }
    }

    /// Answers [`eq`](Self::eq) over bounds: each virtual bound equals only
    /// itself.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: two values compare as [`eq`](Self::eq); `Bottom` equals
    ///   `Bottom` and `Root` equals `Root`, whatever `assoc`; a virtual bound
    ///   never equals a value or the other bound.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 pointwise — same bottom, same root, bottom against root
    ///   and each bound against a value are observed.
    /// - witness: `tests::prec::virtual_bound_comparisons`
    #[inline]
    #[must_use]
    pub fn bound_eq(
        &self,
        left: Bound<Prec>,
        right: Bound<Prec>,
        assoc: Assoc,
    ) -> PrecedenceComparison
    {
        match (left, right) {
            | (Bound::Value(left), Bound::Value(right)) => self.eq(left, right, assoc),
            | (Bound::Bottom, Bound::Bottom) | (Bound::Root, Bound::Root) => {
                PrecedenceComparison::from(true)
            },
            | (Bound::Bottom, Bound::Root | Bound::Value(_))
            | (Bound::Root, Bound::Bottom | Bound::Value(_))
            | (Bound::Value(_), Bound::Bottom | Bound::Root) => PrecedenceComparison::from(false),
        }
    }

    /// Answers [`comparable`](Self::comparable) over bounds: a virtual bound
    /// is comparable with every known group and with either bound.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: two values compare as [`comparable`](Self::comparable); two
    ///   bounds are comparable; a bound and a value are comparable exactly when
    ///   the value is a known group.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 pointwise plus L2 generative — the one-past-the-end
    ///   group is refused against `Root` while the last group is accepted;
    ///   generated chains accept every group against either bound.
    /// - witness: `tests::prec::prec_dag_size_and_boundary_contract`
    /// - witness: `tests::prec::comparable_is_symmetric_and_rejects_invalid_boundaries`
    #[inline]
    #[must_use]
    pub fn bound_comparable(
        &self,
        left: Bound<Prec>,
        right: Bound<Prec>,
    ) -> PrecedenceComparison
    {
        match (left, right) {
            | (Bound::Bottom | Bound::Root, Bound::Bottom | Bound::Root) => {
                PrecedenceComparison::from(true)
            },
            | (Bound::Bottom | Bound::Root, Bound::Value(prec))
            | (Bound::Value(prec), Bound::Bottom | Bound::Root) => {
                PrecedenceComparison::from(bool::from(self.knows(prec)))
            },
            | (Bound::Value(left), Bound::Value(right)) => self.comparable(left, right),
        }
    }

    /// Fingerprints the groups' names and associativities and the edges.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the FNV-1a hash of the group count, then per group its name's
    ///   byte length, its name and its associativity tag (0 for [`Assoc::Non`],
    ///   1 for [`Assoc::Left`], 2 for [`Assoc::Right`]), then the edge count
    ///   and each ascending edge as two 16-bit indices, every count a 64-bit
    ///   little-endian word; so the fingerprint is independent of edge
    ///   insertion order and repetition, and moves with any name, associativity
    ///   or edge.
    /// - provides: a cache key for tables built over the DAG.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 pointwise plus an external oracle — reordered and
    ///   repeated edges agree, while a renamed group, a changed associativity
    ///   and a changed relation each move the fingerprint; the value of a
    ///   three-group DAG is pinned against the documented stream hashed by an
    ///   independent FNV-1a implementation.
    /// - witness: `tests::prec::stable_fingerprint_sensitivity`
    /// - witness: `tests::prec::fingerprint_stream_is_pinned`
    #[inline]
    #[must_use]
    pub fn fingerprint(&self) -> Fingerprint
    {
        let mut state = Fnv64::new();
        state.write_u64(word_of_len(&self.names));
        for (name, &assoc) in self.names.iter().zip(&self.assocs) {
            state.write_u64(word_of_len(name.as_bytes()));
            state.write_bytes(name.as_bytes());
            state.write_byte(assoc_tag(assoc));
        }
        state.write_u64(word_of_len(&self.edges));
        for &(tighter, looser) in &self.edges {
            state.write_u16(FingerprintWord16::from(u16::from(tighter.index())));
            state.write_u16(FingerprintWord16::from(u16::from(looser.index())));
        }
        state.finish()
    }

    /// Reports whether `prec` names a group of this DAG.
    ///
    /// # Specification
    /// trivial.
    fn knows(
        &self,
        prec: Prec,
    ) -> PrecValidity
    {
        valid(&self.names, prec)
    }

    /// Reports whether `tighter` is strictly tighter than `looser`.
    ///
    /// # Specification
    /// - requires: nothing; an unknown `tighter` has no row.
    /// - ensures: true exactly when `looser` is in `tighter`'s closure row.
    /// - panics: none.
    fn strictly_tighter(
        &self,
        tighter: Prec,
        looser: Prec,
    ) -> PrecedenceComparison
    {
        PrecedenceComparison::from(
            self.reachability
                .get(usize::from(u16::from(tighter.index())))
                .is_some_and(|row| row.binary_search(&looser).is_ok()),
        )
    }
}

/// A specification's edges as a dense graph: group `n` is node `n`.
#[repr(transparent)]
struct PrecGraph
{
    /// Successor rows, ascending and without repetition.
    rows: Vec<Vec<NodeId>>,
}

impl PrecGraph
{
    /// Lays a specification's edges out as successor rows.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one row per group; row `n` holds the looser endpoint of every
    ///   edge whose tighter endpoint is group `n`, ascending.
    /// - panics: none.
    fn from_spec(spec: &PrecSpec) -> Self
    {
        let mut rows = Vec::new();
        rows.resize_with(spec.names.len(), Vec::new);
        for &(tighter, looser) in &spec.edges {
            if let Some(row) = rows.get_mut(usize::from(u16::from(tighter.index()))) {
                row.push(NodeId::from(u32::from(looser.index())));
            }
        }
        Self { rows }
    }
}

impl EdgeSource for PrecGraph
{
    type Successors<'successors>
        = core::iter::Copied<core::slice::Iter<'successors, NodeId>>
    where
        Self: 'successors;

    /// Reports one node per group.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn node_count(&self) -> NodeCount
    {
        group_node_count(&self.rows)
    }

    /// Yields a group's looser neighbours; an unknown node has none.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn successors(
        &self,
        node: NodeId,
    ) -> Self::Successors<'_>
    {
        NodePosition::try_from(node)
            .ok()
            .and_then(|position| self.rows.get(usize::from(position)))
            .map_or(&[][..], Vec::as_slice)
            .iter()
            .copied()
    }
}

/// Orders an acyclic graph's nodes by Kahn's algorithm, taking the smallest
/// ready node first.
///
/// # Specification
/// - requires: `graph` is acyclic.
/// - ensures: every node appears once, each before every node it has an edge
///   to; among the nodes whose predecessors are all placed, the smallest goes
///   next.
/// - fails: a node is never placed, which an acyclic graph never produces.
/// - panics: none.
///
/// # Errors
/// [`PrecDagError::Inconsistent`] when the order leaves a node out.
fn linear_extension(graph: &PrecGraph) -> Result<Vec<Prec>, PrecDagError>
{
    let mut indegree = Vec::new();
    indegree.resize(graph.rows.len(), PredecessorCount::default());
    for &looser in graph.rows.iter().flatten() {
        let count = slot(&mut indegree, looser)?;
        *count = count.succ()?;
    }
    let mut ready = BTreeSet::new();
    for (position, &count) in indegree.iter().enumerate() {
        if count == PredecessorCount::default() {
            ready.insert(NodePosition::from(position));
        }
    }
    let mut order = Vec::with_capacity(graph.rows.len());
    while let Some(position) = ready.pop_first() {
        let node = NodeId::try_from(position).map_err(|_overflow| PrecDagError::Inconsistent)?;
        let prec = prec_of_node(node)?;
        order.push(prec);
        let row = graph
            .rows
            .get(usize::from(position))
            .ok_or(PrecDagError::Inconsistent)?;
        for &looser in row {
            let count = slot(&mut indegree, looser)?;
            *count = count.pred()?;
            if *count == PredecessorCount::default() {
                let next = NodePosition::try_from(looser)
                    .map_err(|_overflow| PrecDagError::Inconsistent)?;
                ready.insert(next);
            }
        }
    }
    if order.len() == graph.rows.len() {
        Ok(order)
    }
    else {
        Err(PrecDagError::Inconsistent)
    }
}

/// How many unplaced predecessors a node has during [`linear_extension`].
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct PredecessorCount(usize);

impl PredecessorCount
{
    /// Counts one more predecessor.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the count rises by one.
    /// - fails: the count is at `usize::MAX`.
    /// - panics: none.
    ///
    /// # Errors
    /// [`PrecDagError::Inconsistent`] on overflow.
    fn succ(self) -> Result<Self, PrecDagError>
    {
        self.0
            .checked_add(1)
            .map(Self)
            .ok_or(PrecDagError::Inconsistent)
    }

    /// Counts one predecessor placed.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the count falls by one.
    /// - fails: the count is already zero.
    /// - panics: none.
    ///
    /// # Errors
    /// [`PrecDagError::Inconsistent`] below zero.
    fn pred(self) -> Result<Self, PrecDagError>
    {
        self.0
            .checked_sub(1)
            .map(Self)
            .ok_or(PrecDagError::Inconsistent)
    }
}

/// Borrows one node's predecessor count.
///
/// # Specification
/// - requires: nothing.
/// - ensures: returns the count at the node's position.
/// - fails: the node has no count.
/// - panics: none.
///
/// # Errors
/// [`PrecDagError::Inconsistent`] for a node without a count.
fn slot(
    indegree: &mut [PredecessorCount],
    node: NodeId,
) -> Result<&mut PredecessorCount, PrecDagError>
{
    let position = NodePosition::try_from(node).map_err(|_overflow| PrecDagError::Inconsistent)?;
    indegree
        .get_mut(usize::from(position))
        .ok_or(PrecDagError::Inconsistent)
}

/// Names the group a dense node stands for.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the group's index equals the node.
/// - fails: the node exceeds 16 bits, which a graph of at most 65 536 groups
///   never produces.
/// - panics: none.
///
/// # Errors
/// [`PrecDagError::Inconsistent`] for a node past 16 bits.
fn prec_of_node(node: NodeId) -> Result<Prec, PrecDagError>
{
    u16::try_from(u32::from(node))
        .map(|index| Prec::new(PrecIndex::from(index)))
        .map_err(|_overflow| PrecDagError::Inconsistent)
}

/// Names the groups a run of dense nodes stands for, in order.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one group per node, in order, as [`prec_of_node`].
/// - fails: as [`prec_of_node`].
/// - panics: none.
///
/// # Errors
/// [`PrecDagError::Inconsistent`] for a node past 16 bits.
fn precs_of_nodes(nodes: Vec<NodeId>) -> Result<Vec<Prec>, PrecDagError>
{
    nodes.into_iter().map(prec_of_node).collect()
}

/// Reports whether `prec` indexes one of `names`.
///
/// # Specification
/// trivial.
fn valid(
    names: &[String],
    prec: Prec,
) -> PrecValidity
{
    PrecValidity::from(usize::from(u16::from(prec.index())) < names.len())
}

/// Reports the node bound of a per-group vector, saturating at `u32::MAX`;
/// a specification holds at most 65 536 groups, so it never saturates.
///
/// # Specification
/// trivial.
fn group_node_count<T>(groups: &[T]) -> NodeCount
{
    NodeCount::from(u32::try_from(groups.len()).unwrap_or(u32::MAX))
}

/// Reads one group's name.
///
/// # Specification
/// trivial.
fn name_of(
    names: &[String],
    prec: Prec,
) -> Option<PrecName<'_>>
{
    names
        .get(usize::from(u16::from(prec.index())))
        .map(|name| PrecName::from(name.as_str()))
}

/// Reads one group's associativity.
///
/// # Specification
/// trivial.
fn assoc_of(
    assocs: &[Assoc],
    prec: Prec,
) -> Option<Assoc>
{
    assocs.get(usize::from(u16::from(prec.index()))).copied()
}

/// Yields every group with its name and associativity, in index order.
///
/// # Specification
/// trivial.
fn groups_of<'groups>(
    names: &'groups [String],
    assocs: &'groups [Assoc],
) -> impl Iterator<Item = (Prec, PrecName<'groups>, Assoc)> + 'groups
{
    names
        .iter()
        .zip(assocs)
        .zip(0_u16 ..)
        .map(|((name, &assoc), index)| {
            (
                Prec::new(PrecIndex::from(index)),
                PrecName::from(name.as_str()),
                assoc,
            )
        })
}

/// Frames a slice's length as a fingerprint word, saturating past 64 bits.
///
/// # Specification
/// trivial.
fn word_of_len<T>(items: &[T]) -> FingerprintWord64
{
    FingerprintWord64::from(u64::try_from(items.len()).unwrap_or(u64::MAX))
}

/// Tags an associativity in the fingerprint stream.
///
/// # Specification
/// trivial.
fn assoc_tag(assoc: Assoc) -> FingerprintByte
{
    match assoc {
        | Assoc::Non => FingerprintByte::from(0_u8),
        | Assoc::Left => FingerprintByte::from(1_u8),
        | Assoc::Right => FingerprintByte::from(2_u8),
    }
}
