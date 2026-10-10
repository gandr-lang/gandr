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

use anodized::spec;

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
    /// - hypothesis: For all 16-bit indices, L3 known and unknown-group probes
    ///   observe the raw identity, distinguishing clamping or a shifted index.
    ///   Membership in a particular graph is not a constructor guarantee.
    /// - witness: `tests::prec::prec_dag_size_and_boundary_contract`
    #[spec(ensures: |result| result.0.0 == index.0)]
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
/// - hypothesis: For empty through full-capacity builders, L3 exact groups,
///   canonical edges and refusal-state equality distinguish lost data,
///   duplicate retention and invalid endpoint acceptance. Construction at the
///   16-bit capacity is witnessed; consuming every group at that capacity
///   remains outside these witnesses.
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
    /// - hypothesis: For builder states and consuming name conversions, the
    ///   predicate observes append position, association, name-index membership
    ///   and unchanged cardinalities on refusal. L3 full-capacity and duplicate
    ///   probes distinguish shifted identities, changed association and refusal
    ///   precedence. Name conversion and prior entry contents are observed by
    ///   witnesses rather than copied into the predicate.
    /// - witness: `tests::prec::capacity_beyond_u16_is_typed`
    /// - witness: `tests::prec::duplicate_edge_canonicalization_and_invalid_edges`
    #[spec(
        captures: [prior = self.names.len(), prior_assocs = self.assocs.len(),
            prior_index = self.name_index.len(), prior_edges = self.edges.len()],
        ensures: |ref result| self.edges.len() == prior_edges && match *result {
            Ok(prec) => usize::from(prec.0.0) == prior && self.names.len() == prior.saturating_add(1)
                && self.assocs.len() == prior_assocs.saturating_add(1)
                && self.name_index.len() == prior_index.saturating_add(1)
                && self.assocs.last() == Some(&assoc)
                && self.names.last().is_some_and(|name| self.name_index.contains(name)),
            Err(PrecSpecError::DuplicateName { ref name }) => self.name_index.contains(name)
                && self.names.len() == prior && self.assocs.len() == prior_assocs && self.name_index.len() == prior_index,
            Err(PrecSpecError::CapacityExceeded) => prior > usize::from(u16::MAX)
                && self.names.len() == prior && self.assocs.len() == prior_assocs && self.name_index.len() == prior_index,
            Err(_) => false,
        },
    )]
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
    /// - hypothesis: For any endpoint identities, the result and edge-set
    ///   observer distinguish a new edge, a repeated edge, and either invalid
    ///   endpoint with its original payload. L3 canonicalization and state
    ///   equality on refusal catch duplicate insertion and collateral mutation.
    ///   Global acyclicity is deliberately deferred to DAG construction.
    /// - witness: `tests::prec::duplicate_edge_canonicalization_and_invalid_edges`
    /// - witness: `tests::prec::prec_spec_size_and_boundary_contract`
    #[spec(
        captures: [prior = self.edges.len(), existed = self.edges.binary_search(&(tighter, looser)).is_ok()],
        ensures: |ref result| match *result {
            Ok(()) => usize::from(tighter.0.0) < self.names.len() && usize::from(looser.0.0) < self.names.len()
                && self.edges.binary_search(&(tighter, looser)).is_ok()
                && self.edges.len() == prior.saturating_add(usize::from(!existed))
                && self.edges.windows(2).all(|pair| matches!(*pair, [left, right] if left < right)),
            Err(PrecSpecError::InvalidEdge { tighter: refused_tighter, looser: refused_looser, node_count }) =>
                refused_tighter == tighter && refused_looser == looser && node_count == group_node_count(&self.names)
                && (usize::from(tighter.0.0) >= self.names.len() || usize::from(looser.0.0) >= self.names.len())
                && self.edges.len() == prior,
            Err(_) => false,
        },
    )]
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
    /// - requires: nothing; builder-produced columns match.
    /// - ensures: yields paired names and associations with their ascending
    ///   ids.
    /// - panics: consuming the last entry of a full 65,536-group table
    ///   overflows the 16-bit enumeration counter when overflow checking is
    ///   enabled.
    /// - executable: none — the backend cannot annotate the closure return type
    ///   for an opaque iterator; complete enumeration is also a lazy
    ///   observation.
    ///
    /// # Adequacy
    /// - hypothesis: For matching columns below full capacity, L3 empty, named
    ///   and diamond tables observe every identity, name and association,
    ///   distinguishing truncation or misaligned columns. Construction at full
    ///   capacity is witnessed separately and does not prove full iterator
    ///   consumption; the 16-bit counter is a known boundary.
    /// - witness: `tests::prec::prec_spec_size_and_boundary_contract`
    /// - witness: `tests::prec::prec_dag_contract`
    /// - witness: `tests::prec::capacity_beyond_u16_is_typed`
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
    /// - requires: nothing.
    /// - ensures: writes the witness indices in their supplied order.
    /// - fails: the output sink refuses a write.
    /// - panics: none.
    /// - executable: none — the formatter is a write-only sink and provides no
    ///   independent observer of bytes emitted or of a refused write.
    ///
    /// # Adequacy
    /// - hypothesis: For arbitrary witness sequences, L3 extraction of numeric
    ///   fields distinguishes dropped, reordered or deduplicated indices, and a
    ///   refusing sink observes initial error propagation. Wording and
    ///   whitespace are not pinned; later sink-failure positions and graph
    ///   validity of the witness are outside these observations.
    /// - witness: `prec::tests::cycle_display_preserves_fields_and_refuses_a_sink`
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
/// - hypothesis: For acyclic diamonds, integer chains and virtual bounds, L3
///   exact relations distinguish orientation, incomparability and association
///   from identity; L1 closed-cycle incidence witnesses refusal of cyclic
///   specifications. These fixtures do not prove least closure for every graph
///   or collision freedom of its fingerprint.
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
    /// - hypothesis: For builder-produced specifications, the predicate
    ///   observes retained group tables, canonical closure rows, direct-edge
    ///   inclusion and valid cycle incidence. L3 diamonds and chains
    ///   distinguish wrong closure, a disconnected relation distinguishes the
    ///   ready-node tie-break, and self and longer cycles distinguish malformed
    ///   refusal evidence. Complete least closure and topological ordering
    ///   remain witness observations; allocator exhaustion is not forced.
    /// - witness: `tests::prec::prec_cycle_witness_contract`
    /// - witness: `tests::prec::prec_dag_contract`
    /// - witness: `tests::prec::deterministic_linear_extension_uses_smallest_ready_id`
    #[spec(ensures: |ref result| match *result {
        Ok(ref dag) => dag.names == spec.names && dag.assocs == spec.assocs && dag.edges == spec.edges
            && (dag.reachability.len(), dag.linear_extension.len()) == (spec.names.len(), spec.names.len())
            && dag.linear_extension.iter().all(|prec| usize::from(prec.0.0) < spec.names.len())
            && dag.reachability.iter().enumerate().all(|(source, row)| row.iter().all(|target|
                usize::from(target.0.0) < spec.names.len() && usize::from(target.0.0) != source)
                && row.windows(2).all(|pair| matches!(*pair, [left, right] if left < right)))
            && spec.edges.iter().all(|&(source, target)| dag.reachability.get(usize::from(source.0.0))
                .is_some_and(|row| row.binary_search(&target).is_ok())),
        Err(PrecDagError::Cycle(ref cycle)) => cycle.witness.len() >= 2
            && cycle.witness.first() == cycle.witness.last()
            && cycle.witness.windows(2).all(|pair| matches!(*pair, [source, target] if spec.edges.binary_search(&(source, target)).is_ok())),
        Err(PrecDagError::Graph(GraphValidationError::NodeCountTooLarge { node_count })) => node_count == group_node_count(&spec.names),
        Err(_) => false,
    })]
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
    /// - requires: nothing; builder-produced columns match.
    /// - ensures: yields paired names and associations with their ascending
    ///   ids.
    /// - panics: consuming the last entry of a full 65,536-group table
    ///   overflows the 16-bit enumeration counter when overflow checking is
    ///   enabled.
    /// - executable: none — the backend cannot annotate the closure return type
    ///   for an opaque iterator; complete enumeration is also a lazy
    ///   observation.
    ///
    /// # Adequacy
    /// - hypothesis: For matching columns below full capacity, L3 empty, named
    ///   and diamond tables observe every identity, name and association,
    ///   distinguishing truncation or misaligned columns. Construction at full
    ///   capacity is witnessed separately and does not prove full iterator
    ///   consumption; the 16-bit counter is a known boundary.
    /// - witness: `tests::prec::prec_spec_size_and_boundary_contract`
    /// - witness: `tests::prec::prec_dag_contract`
    /// - witness: `tests::prec::capacity_beyond_u16_is_typed`
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
    /// - hypothesis: For known or unknown identities, the predicate observes
    ///   direction and the right-associative reflexive case. L3 diamonds and
    ///   chains separate reversal, incomparable siblings and unknown ids; L2
    ///   generated pairs separate association from strict reachability. The
    ///   stored closure's construction is witnessed separately from lookup.
    /// - witness: `tests::prec::prec_dag_contract`
    /// - witness: `tests::prec::prec_integer_chain_oracle`
    /// - witness: `tests::prec::lt_gt_duality_for_distinct_chain_nodes`
    /// - witness: `tests::prec::associativity_affects_reflexive_pairs_only`
    #[spec(ensures: |result| bool::from(result) == (usize::from(left.0.0) < self.names.len()
        && usize::from(right.0.0) < self.names.len()
        && if left == right { self.assocs.get(usize::from(left.0.0)) == Some(&Assoc::Right) && assoc == Assoc::Right }
            else { self.reachability.get(usize::from(right.0.0)).is_some_and(|row| row.contains(&left)) }))]
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
    /// - hypothesis: For known or unknown identities, L3 pair observations and
    ///   L2 generated chains distinguish reversed reachability, a wrong
    ///   left-associative reflexive case and acceptance of unknown groups. The
    ///   predicate observes the stored relation, not its independent
    ///   derivation.
    /// - witness: `tests::prec::prec_dag_contract`
    /// - witness: `tests::prec::prec_integer_chain_oracle`
    /// - witness: `tests::prec::lt_gt_duality_for_distinct_chain_nodes`
    /// - witness: `tests::prec::associativity_affects_reflexive_pairs_only`
    #[spec(ensures: |result| bool::from(result) == (usize::from(left.0.0) < self.names.len()
        && usize::from(right.0.0) < self.names.len()
        && if left == right { self.assocs.get(usize::from(left.0.0)) == Some(&Assoc::Left) && assoc == Assoc::Left }
            else { self.reachability.get(usize::from(left.0.0)).is_some_and(|row| row.contains(&right)) }))]
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
    /// - hypothesis: For any two identities and asserted association, L3
    ///   reflexive, distinct and unknown probes distinguish identity equality
    ///   from the declared-and-asserted non-associative case. The predicate
    ///   reads the association table; its construction is a separate boundary.
    /// - witness: `tests::prec::prec_dag_contract`
    /// - witness: `tests::prec::bound_value_reflexive_association_tracks_direction`
    #[spec(ensures: |result| bool::from(result) == (left == right && assoc == Assoc::Non
        && self.assocs.get(usize::from(left.0.0)) == Some(&Assoc::Non)))]
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
    /// - hypothesis: For any identities, L3 diamond siblings and known/unknown
    ///   probes distinguish incomparability from identity and either strict
    ///   direction; L2 generated pairs check symmetry. This observes the stored
    ///   closure rather than proving it is the least relation.
    /// - witness: `tests::prec::prec_dag_contract`
    /// - witness: `tests::prec::comparable_is_symmetric_and_rejects_invalid_boundaries`
    #[spec(ensures: |result| bool::from(result) == (usize::from(left.0.0) < self.names.len()
        && usize::from(right.0.0) < self.names.len() && (left == right
            || self.reachability.get(usize::from(left.0.0)).is_some_and(|row| row.contains(&right))
            || self.reachability.get(usize::from(right.0.0)).is_some_and(|row| row.contains(&left)))))]
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
    /// - hypothesis: For every virtual/value pairing, L3 known and unknown
    ///   probes distinguish reversed extremes, treating unknown values as
    ///   known, and an incorrect value-reflexive association. Concrete-value
    ///   lookup is the lower-level comparison boundary, not a second closure
    ///   computation.
    /// - witness: `tests::prec::virtual_bound_comparisons`
    /// - witness: `tests::prec::prec_dag_size_and_boundary_contract`
    #[spec(ensures: |result| bool::from(result) == match (left, right) {
        (Bound::Bottom, Bound::Root) => true,
        (Bound::Bottom, Bound::Value(prec)) | (Bound::Value(prec), Bound::Root) => usize::from(prec.0.0) < self.names.len(),
        (Bound::Value(a), Bound::Value(b)) => bool::from(self.lt(a, b, assoc)),
        _ => false,
    })]
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
    /// - hypothesis: For all virtual/value pairings, L3 observations
    ///   distinguish the greater-than orientation, unknown-value refusal and
    ///   left-associative reflexivity. Concrete-value ordering is delegated to
    ///   its independently witnessed comparison; no claim of a total order is
    ///   made.
    /// - witness: `tests::prec::virtual_bound_comparisons`
    /// - witness: `tests::prec::bound_value_reflexive_association_tracks_direction`
    #[spec(ensures: |result| bool::from(result) == match (left, right) {
        (Bound::Root, Bound::Bottom) => true,
        (Bound::Root, Bound::Value(prec)) | (Bound::Value(prec), Bound::Bottom) => usize::from(prec.0.0) < self.names.len(),
        (Bound::Value(a), Bound::Value(b)) => bool::from(self.gt(a, b, assoc)),
        _ => false,
    })]
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
    /// - hypothesis: For all virtual/value pairings, L3 same-extreme, distinct
    ///   extreme and mixed-value probes distinguish virtual equality from value
    ///   reflexivity. Value comparisons retain their association rule; this is
    ///   not ordinary identity equality on every concrete group.
    /// - witness: `tests::prec::virtual_bound_comparisons`
    #[spec(ensures: |result| bool::from(result) == match (left, right) {
        (Bound::Bottom, Bound::Bottom) | (Bound::Root, Bound::Root) => true,
        (Bound::Value(a), Bound::Value(b)) => bool::from(self.eq(a, b, assoc)),
        _ => false,
    })]
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
    /// - hypothesis: For all virtual/value pairings, L3 last-known and
    ///   first-unknown probes and L2 generated chains distinguish valid extreme
    ///   comparisons from accepting foreign ids. Value/value comparability is
    ///   separately witnessed; virtual bounds do not make siblings comparable.
    /// - witness: `tests::prec::prec_dag_size_and_boundary_contract`
    /// - witness: `tests::prec::comparable_is_symmetric_and_rejects_invalid_boundaries`
    #[spec(ensures: |result| bool::from(result) == match (left, right) {
        (Bound::Bottom | Bound::Root, Bound::Bottom | Bound::Root) => true,
        (Bound::Bottom | Bound::Root, Bound::Value(prec)) | (Bound::Value(prec), Bound::Bottom | Bound::Root) => usize::from(prec.0.0) < self.names.len(),
        (Bound::Value(a), Bound::Value(b)) => bool::from(self.comparable(a, b)),
    })]
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
    /// - requires: the builder-established group and canonical-edge invariants.
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
    /// - hypothesis: For coherent builder-produced tables, the predicate checks
    ///   matched group columns and canonical declared edges. L3 independent
    ///   stream and sensitivity witnesses distinguish framing, byte order,
    ///   omitted names or associations, and edge-order dependence. The
    ///   predicate does not duplicate the hash computation, and collision
    ///   freedom is not claimed for a 64-bit fingerprint.
    /// - witness: `tests::prec::stable_fingerprint_sensitivity`
    /// - witness: `tests::prec::fingerprint_stream_is_pinned`
    #[spec(requires: self.names.len() == self.assocs.len()
        && self.edges.windows(2).all(|pair| matches!(*pair, [left, right] if left < right))
        && self.edges.iter().all(|&(source, target)| usize::from(source.0.0) < self.names.len() && usize::from(target.0.0) < self.names.len()))]
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
    ///
    /// # Adequacy
    /// - hypothesis: For any identities in a constructed DAG, the predicate
    ///   compares row membership without binary-search dependence. L3 diamonds
    ///   and unknown-id probes distinguish a wrong row, reversed relation and
    ///   treating absence as reachability. Derivation of the closure itself is
    ///   the builder boundary.
    /// - witness: `tests::prec::prec_dag_contract`
    /// - witness: `tests::prec::prec_dag_size_and_boundary_contract`
    #[spec(ensures: |result| bool::from(result) == self.reachability.get(usize::from(tighter.0.0))
        .is_some_and(|row| row.contains(&looser)))]
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
    ///
    /// # Adequacy
    /// - hypothesis: For builder-produced specifications, the predicate
    ///   compares the flattened labelled rows with the canonical input edge
    ///   stream, including order and multiplicity. L3 diamond and
    ///   duplicate-edge witnesses distinguish reversal, missing rows and
    ///   dropped incidences. It does not establish acyclicity; cyclic rows are
    ///   valid encodings.
    /// - witness: `tests::prec::prec_dag_contract`
    /// - witness: `tests::prec::duplicate_edge_canonicalization_and_invalid_edges`
    /// - witness: `tests::prec::prec_cycle_witness_contract`
    #[spec(ensures: |ref built| built.rows.len() == spec.names.len()
        && built.rows.iter().enumerate().flat_map(|(source, row)| row.iter().map(move |&target| (source, u32::from(target))))
            .eq(spec.edges.iter().map(|&(source, target)| (usize::from(source.0.0), u32::from(target.0.0)))))]
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
    /// - requires: nothing.
    /// - ensures: yields the requested row in order, or no nodes when absent.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: For any dense identity, the cloned borrowed-iterator
    ///   observer checks the exact row or empty fallback. L3 declared, empty
    ///   and first-absent rows distinguish a neighbouring row from absence. The
    ///   adapter does not validate whether row targets are declared.
    /// - witness: `prec::tests::successor_rows_keep_the_absent_boundary`
    #[spec(ensures: |ref result| usize::try_from(u32::from(node)).ok().and_then(|position| self.rows.get(position))
        .map_or_else(|| result.clone().next().is_none(), |row| result.clone().eq(row.iter().copied())))]
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
/// - requires: `graph` is acyclic, dense and uses representable group indices.
/// - ensures: every node appears once, each before every node it has an edge
///   to; among the nodes whose predecessors are all placed, the smallest goes
///   next.
/// - fails: a node is never placed, which an acyclic graph never produces.
/// - panics: none.
///
/// # Errors
/// [`PrecDagError::Inconsistent`] when the order leaves a node out.
///
/// # Adequacy
/// - hypothesis: For acyclic canonical dense rows with representable group
///   indices, the predicates observe input bounds, complete output length, a
///   source first and a sink last. L3 disconnected, diamond and chain witnesses
///   distinguish omitted nodes, reversed dependencies and a wrong ready-node
///   tie-break. Full permutation and topological order are witness boundaries
///   rather than a repeated traversal.
/// - witness: `tests::prec::deterministic_linear_extension_uses_smallest_ready_id`
/// - witness: `tests::prec::prec_dag_contract`
/// - witness: `tests::prec::prec_integer_chain_oracle`
#[spec(
    requires: graph.rows.len() <= usize::from(u16::MAX).saturating_add(1)
        && graph.rows.iter().all(|row| row.iter().all(|&node| usize::try_from(u32::from(node)).is_ok_and(|position| position < graph.rows.len()))
            && row.windows(2).all(|pair| matches!(*pair, [left, right] if left < right))),
    ensures: |ref result| result.as_ref().is_ok_and(|order| order.len() == graph.rows.len()
        && order.iter().all(|prec| usize::from(prec.0.0) < graph.rows.len())
        && order.first().map_or_else(|| graph.rows.is_empty(), |first| graph.rows.iter()
            .all(|row| !row.contains(&NodeId::from(u32::from(first.0.0)))))
        && order.last().map_or_else(|| graph.rows.is_empty(), |last| graph.rows.get(usize::from(last.0.0)).is_some_and(Vec::is_empty))),
)]
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
    ///
    /// # Adequacy
    /// - hypothesis: For every predecessor count, L3 zero and maximum probes
    ///   observe exact increment or typed overflow. They distinguish
    ///   saturation, wrapping and a wrong refusal. Real graph cardinalities
    ///   need not approach the machine limit to witness this arithmetic
    ///   boundary.
    /// - witness: `prec::tests::predecessor_counts_refuse_both_extremes`
    #[spec(ensures: |ref result| match *result {
        Ok(next) => self.0.checked_add(1) == Some(next.0),
        Err(PrecDagError::Inconsistent) => self.0 == usize::MAX,
        Err(_) => false,
    })]
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
    ///
    /// # Adequacy
    /// - hypothesis: For every predecessor count, L3 one, zero and maximum
    ///   probes observe exact decrement or typed underflow. They distinguish
    ///   premature refusal and wrapping. This arithmetic does not prove that
    ///   the original count matches graph incidence.
    /// - witness: `prec::tests::predecessor_counts_refuse_both_extremes`
    #[spec(ensures: |ref result| match *result {
        Ok(next) => next.0.checked_add(1) == Some(self.0),
        Err(PrecDagError::Inconsistent) => self.0 == 0,
        Err(_) => false,
    })]
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
///
/// # Adequacy
/// - hypothesis: For any predecessor slice and node, the pointer observer
///   identifies the mutable slot or an absent entry. L3 mutation of the last
///   valid slot and first-absent refusal distinguish neighbouring aliasing and
///   fallback insertion. The stored count is not validated against a graph
///   here.
/// - witness: `prec::tests::predecessor_slots_and_group_indices_keep_their_bounds`
#[spec(
    captures: expected = usize::try_from(u32::from(node)).ok().and_then(|position| indegree.get(position)).map(core::ptr::from_ref),
    ensures: |ref result| match *result {
        Ok(ref count) => expected == Some(core::ptr::from_ref(*count)),
        Err(PrecDagError::Inconsistent) => expected.is_none(),
        Err(_) => false,
    },
)]
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
///
/// # Adequacy
/// - hypothesis: For any dense node, L3 last-representable and
///   first-unrepresentable probes compare the raw identity and typed refusal,
///   distinguishing truncation and a shifted boundary. Existence of that
///   identity in a particular specification is not checked.
/// - witness: `prec::tests::predecessor_slots_and_group_indices_keep_their_bounds`
#[spec(ensures: |ref result| match *result {
    Ok(prec) => u32::from(prec.0.0) == u32::from(node),
    Err(PrecDagError::Inconsistent) => u32::from(node) > u32::from(u16::MAX),
    Err(_) => false,
})]
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
///
/// # Adequacy
/// - hypothesis: For any owned node sequence, the predicate observes
///   representability, length and both endpoint identities without copying the
///   consumed sequence. L3 ordered, empty and refused sequences distinguish
///   truncation, reversal and dropping a failing interior entry;
///   cycle-incidence witnesses also observe interior order. The endpoint
///   predicate alone does not prove every interior position.
/// - witness: `prec::tests::predecessor_slots_and_group_indices_keep_their_bounds`
/// - witness: `tests::prec::prec_cycle_witness_contract`
#[spec(
    captures: [length = nodes.len(), head = nodes.first().copied(), tail = nodes.last().copied(),
        representable = nodes.iter().all(|&node| u16::try_from(u32::from(node)).is_ok())],
    ensures: |ref result| match *result {
        Ok(ref groups) => representable && groups.len() == length
            && groups.first().map(|prec| u32::from(prec.0.0)) == head.map(u32::from)
            && groups.last().map(|prec| u32::from(prec.0.0)) == tail.map(u32::from),
        Err(PrecDagError::Inconsistent) => !representable,
        Err(_) => false,
    },
)]
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
/// - requires: nothing.
/// - ensures: the slice length, saturated at the largest dense node bound.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For slices of any element type, L3 empty and zero-sized large
///   slices compare length with the saturated bound, distinguishing truncation
///   and a shifted saturation threshold. The large witness is conditional on
///   host width and allocates no backing elements; real precedence tables are
///   much smaller.
/// - witness: `prec::tests::group_counts_saturate_without_materializing_nodes`
#[spec(ensures: |result| u32::from(result) == u32::try_from(groups.len()).unwrap_or(u32::MAX))]
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
/// - requires: matching name and associativity columns.
/// - ensures: yields paired names and associations with their ascending ids.
/// - panics: consuming the last entry of a full 65,536-group table overflows
///   the 16-bit enumeration counter when overflow checking is enabled.
/// - executable: none — the backend cannot annotate the closure return type for
///   an opaque iterator; complete enumeration is also a lazy observation.
///
/// # Adequacy
/// - hypothesis: For matching columns below full capacity, L3 empty, named and
///   diamond tables observe every identity, name and association,
///   distinguishing truncation or misaligned columns. Construction at full
///   capacity is witnessed separately and does not prove full iterator
///   consumption; the 16-bit counter is a known boundary.
/// - witness: `tests::prec::prec_spec_size_and_boundary_contract`
/// - witness: `tests::prec::prec_dag_contract`
/// - witness: `tests::prec::capacity_beyond_u16_is_typed`
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
/// - requires: nothing.
/// - ensures: the slice length, saturated at the largest 64-bit word.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For ordinary and zero-sized slices, the result observer
///   preserves the framed length. L3 large-length and independently hashed
///   precedence streams distinguish truncation and framing omission. Saturation
///   above 64 bits is not reachable on a host with at most 64-bit addresses.
/// - witness: `prec::tests::group_counts_saturate_without_materializing_nodes`
/// - witness: `tests::prec::fingerprint_stream_is_pinned`
#[spec(ensures: |result| u64::from(result) == u64::try_from(items.len()).unwrap_or(u64::MAX))]
fn word_of_len<T>(items: &[T]) -> FingerprintWord64
{
    FingerprintWord64::from(u64::try_from(items.len()).unwrap_or(u64::MAX))
}

/// Tags an associativity in the fingerprint stream.
///
/// # Specification
/// - requires: nothing.
/// - ensures: non-associative, left and right encode as bytes 0, 1 and 2.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For every association variant, the predicate observes its
///   protocol byte. The L3 independent stream fixture includes all three
///   variants and distinguishes a swapped or collapsed tag. This checks the
///   encoding, not collision freedom of the surrounding fingerprint.
/// - witness: `tests::prec::fingerprint_stream_is_pinned`
#[spec(ensures: |result| matches!((assoc, u8::from(result)), (Assoc::Non, 0) | (Assoc::Left, 1) | (Assoc::Right, 2)))]
fn assoc_tag(assoc: Assoc) -> FingerprintByte
{
    match assoc {
        | Assoc::Non => FingerprintByte::from(0_u8),
        | Assoc::Left => FingerprintByte::from(1_u8),
        | Assoc::Right => FingerprintByte::from(2_u8),
    }
}

#[cfg(test)]
mod tests
{
    use alloc::vec;

    use super::*;

    #[test]
    fn predecessor_counts_refuse_both_extremes()
    {
        assert_eq!(PredecessorCount(0).succ(), Ok(PredecessorCount(1)));
        assert_eq!(PredecessorCount(1).pred(), Ok(PredecessorCount(0)));
        assert_eq!(PredecessorCount(0).pred(), Err(PrecDagError::Inconsistent));
        assert_eq!(
            PredecessorCount(usize::MAX).succ(),
            Err(PrecDagError::Inconsistent)
        );
        assert_eq!(
            PredecessorCount(usize::MAX).pred(),
            Ok(PredecessorCount(usize::MAX.saturating_sub(1)))
        );
    }

    #[test]
    fn predecessor_slots_and_group_indices_keep_their_bounds()
    {
        let mut counts = [PredecessorCount(3), PredecessorCount(5)];
        *slot(&mut counts, NodeId::from(1)).expect("last count") = PredecessorCount(4);
        assert_eq!(counts, [PredecessorCount(3), PredecessorCount(4)]);
        assert_eq!(
            slot(&mut counts, NodeId::from(2)),
            Err(PrecDagError::Inconsistent)
        );
        let last = NodeId::from(u32::from(u16::MAX));
        let foreign = NodeId::from(u32::from(u16::MAX).saturating_add(1));
        assert_eq!(prec_of_node(last), Ok(Prec::new(PrecIndex::from(u16::MAX))));
        assert_eq!(prec_of_node(foreign), Err(PrecDagError::Inconsistent));
        let nodes = vec![NodeId::from(7), NodeId::from(2), last];
        assert_eq!(
            precs_of_nodes(nodes)
                .expect("ordered groups")
                .iter()
                .map(|prec| u16::from(prec.index()))
                .collect::<Vec<_>>(),
            vec![7, 2, u16::MAX]
        );
        assert_eq!(
            precs_of_nodes(vec![NodeId::from(0), foreign, NodeId::from(1)]),
            Err(PrecDagError::Inconsistent)
        );
        assert!(precs_of_nodes(Vec::new()).expect("empty groups").is_empty());
    }

    #[test]
    fn successor_rows_keep_the_absent_boundary()
    {
        let graph = PrecGraph {
            rows: vec![vec![NodeId::from(1)], Vec::new()],
        };
        assert_eq!(graph.successors(NodeId::from(0)).collect::<Vec<_>>(), vec![
            NodeId::from(1)
        ]);
        assert_eq!(graph.successors(NodeId::from(1)).next(), None);
        assert_eq!(graph.successors(NodeId::from(2)).next(), None);
    }

    #[test]
    fn group_counts_saturate_without_materializing_nodes()
    {
        assert_eq!(group_node_count::<()>(&[]), NodeCount::from(0));
        assert_eq!(u64::from(word_of_len::<()>(&[])), 0);
        if let Some(length) = usize::try_from(u32::MAX)
            .ok()
            .and_then(|count| count.checked_add(1))
        {
            let groups = vec![(); length];
            assert_eq!(group_node_count(&groups), NodeCount::from(u32::MAX));
            assert_eq!(
                u64::from(word_of_len(&groups)),
                u64::from(u32::MAX).saturating_add(1)
            );
        }
    }

    #[test]
    fn cycle_display_preserves_fields_and_refuses_a_sink()
    {
        /// A formatting destination that refuses every write.
        struct Refuse;

        impl core::fmt::Write for Refuse
        {
            /// Returns the destination's fixed refusal.
            ///
            /// # Specification
            /// trivial.
            fn write_str(
                &mut self,
                _text: &str,
            ) -> FmtResult
            {
                Err(core::fmt::Error)
            }
        }

        let cycle = PrecCycle {
            witness: vec![
                Prec::new(PrecIndex::from(7)),
                Prec::new(PrecIndex::from(1)),
                Prec::new(PrecIndex::from(7)),
            ],
        };
        let rendered = alloc::format!("{cycle}");
        let indices = rendered
            .split(|ch: char| !ch.is_ascii_digit())
            .filter(|part| !part.is_empty())
            .map(|part| part.parse::<u16>().expect("displayed index"))
            .collect::<Vec<_>>();
        assert_eq!(indices, vec![7, 1, 7]);
        assert!(core::fmt::write(&mut Refuse, format_args!("{cycle}")).is_err());
    }
}
