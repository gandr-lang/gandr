//! Shared fixtures for the differential and the probe: the batch acyclicity
//! oracle, a reproducible generator, and the three edge-stream families.
//!
//! The quantities the fixtures pass around carry their own names, for the same
//! reason the crate's own do: a node span, a stream length, a seed and a cost
//! are all integers and none of them is interchangeable with another.

use core::fmt::Display;
use core::fmt::Formatter;
use core::fmt::Result as FmtResult;

use anodized::spec;
use gandr_theory_graphs::EdgeId;
use gandr_theory_graphs::EdgeSource;
use gandr_theory_graphs::NodeCount;
use gandr_theory_graphs::NodeId;
use gandr_theory_graphs::cycle_witness;

/// How many dense nodes a fixture spans.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct NodeSpan(usize);

impl From<usize> for NodeSpan
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: usize) -> Self
    {
        Self(value)
    }
}

impl From<NodeSpan> for usize
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: NodeSpan) -> Self
    {
        value.0
    }
}

impl From<Bound> for NodeSpan
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: Bound) -> Self
    {
        Self(usize::try_from(value.0).expect("a small node bound fits"))
    }
}

/// An exclusive upper bound for a draw.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Bound(u32);

impl From<u32> for Bound
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: u32) -> Self
    {
        Self(value)
    }
}

impl From<Bound> for u32
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: Bound) -> Self
    {
        value.0
    }
}

impl Display for Bound
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut Formatter<'_>,
    ) -> FmtResult
    {
        Display::fmt(&self.0, f)
    }
}

/// A drawn dense index.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Index(u32);

impl From<Index> for u32
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: Index) -> Self
    {
        value.0
    }
}

impl From<Index> for NodeId
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: Index) -> Self
    {
        Self::from(value.0)
    }
}

impl From<Index> for usize
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: Index) -> Self
    {
        Self::try_from(value.0).expect("a small drawn index fits")
    }
}

/// How many offers a generated stream carries.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct StreamLength(usize);

impl From<usize> for StreamLength
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: usize) -> Self
    {
        Self(value)
    }
}

impl From<StreamLength> for usize
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: StreamLength) -> Self
    {
        value.0
    }
}

/// The seed a generator is drawn from.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Seed(u64);

impl Seed
{
    /// A companion seed for a second draw taken beside this one, so the two
    /// streams are not correlated with each other.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn companion(self) -> Self
    {
        Self(self.0 ^ 0x5eed_0f5e_75d1_1a90)
    }
}

impl From<u64> for Seed
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: u64) -> Self
    {
        Self(value)
    }
}

impl Display for Seed
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut Formatter<'_>,
    ) -> FmtResult
    {
        Display::fmt(&self.0, f)
    }
}

/// Work measured in nodes plus edges touched.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Cost(u64);

impl Cost
{
    /// This cost plus another.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn plus(
        self,
        other: Self,
    ) -> Self
    {
        Self(self.0.saturating_add(other.0))
    }
}

impl From<u64> for Cost
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: u64) -> Self
    {
        Self(value)
    }
}

impl From<Cost> for u64
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: Cost) -> Self
    {
        value.0
    }
}

impl Display for Cost
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut Formatter<'_>,
    ) -> FmtResult
    {
        Display::fmt(&self.0, f)
    }
}

/// A tally of events in a fixture run.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Tally(u64);

impl Tally
{
    /// This tally raised by one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn increment(self) -> Self
    {
        Self(self.0.saturating_add(1))
    }

    /// This tally plus another.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn plus(
        self,
        other: Self,
    ) -> Self
    {
        Self(self.0.saturating_add(other.0))
    }

    /// Whether anything was tallied.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn is_positive(self) -> TallyPositive
    {
        TallyPositive(self.0 > 0)
    }
}

impl From<u64> for Tally
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: u64) -> Self
    {
        Self(value)
    }
}

impl From<Tally> for u64
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: Tally) -> Self
    {
        value.0
    }
}

impl Display for Tally
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut Formatter<'_>,
    ) -> FmtResult
    {
        Display::fmt(&self.0, f)
    }
}

/// Whether a tally counted anything at all.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct TallyPositive(bool);

impl From<TallyPositive> for bool
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: TallyPositive) -> Self
    {
        value.0
    }
}

/// A position within a stream.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Depth(usize);

impl From<usize> for Depth
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: usize) -> Self
    {
        Self(value)
    }
}

impl From<Depth> for usize
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: Depth) -> Self
    {
        value.0
    }
}

impl Display for Depth
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut Formatter<'_>,
    ) -> FmtResult
    {
        Display::fmt(&self.0, f)
    }
}

/// An offset a probe run draws for one constraint.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DrawnOffset(i64);

impl From<i64> for DrawnOffset
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: i64) -> Self
    {
        Self(value)
    }
}

impl From<DrawnOffset> for i64
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: DrawnOffset) -> Self
    {
        value.0
    }
}

impl Display for DrawnOffset
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut Formatter<'_>,
    ) -> FmtResult
    {
        Display::fmt(&self.0, f)
    }
}

/// A short name identifying a fixture row.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Label(&'static str);

impl From<&'static str> for Label
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: &'static str) -> Self
    {
        Self(value)
    }
}

impl Display for Label
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut Formatter<'_>,
    ) -> FmtResult
    {
        Display::fmt(self.0, f)
    }
}

/// Whether a fixture graph holds a directed cycle.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct CycleFound(bool);

impl From<CycleFound> for bool
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: CycleFound) -> Self
    {
        value.0
    }
}

/// Whether a fixture graph holds a given edge.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct EdgePresent(bool);

impl From<EdgePresent> for bool
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: EdgePresent) -> Self
    {
        value.0
    }
}

/// A dense adjacency the batch algorithms read directly.
///
/// This is the differential's oracle: it holds an explicit edge set and answers
/// acyclicity by the ordinary batch traversal, with no incremental state of any
/// kind.
#[repr(transparent)]
pub struct BatchGraph
{
    /// Successor rows indexed by dense node id.
    adjacency: Vec<Vec<NodeId>>,
}

impl BatchGraph
{
    /// An edgeless graph spanning `nodes` dense identifiers.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn new(nodes: NodeSpan) -> Self
    {
        Self {
            adjacency: vec![Vec::new(); usize::from(nodes)],
        }
    }

    /// A graph spanning `nodes` identifiers and holding `edges`.
    ///
    /// # Specification
    /// - ensures: includes exactly the distinct offered edges, growing the node
    ///   domain when an endpoint lies outside the initial span.
    /// - panics: an endpoint does not fit the host address space.
    ///
    /// # Adequacy
    /// - hypothesis: L2 finite stream comparisons expose missing candidate
    ///   edges.
    /// - witness: `dynamic_graphs::differential::tests::the_differential_catches_a_seeded_wrong_verdict`
    #[inline]
    #[spec(ensures: |ret| edges.iter().all(|&edge| bool::from(ret.holds(edge))))]
    pub fn with_edges(
        nodes: NodeSpan,
        edges: &[EdgeId],
    ) -> Self
    {
        let mut graph = Self::new(nodes);
        for &edge in edges {
            graph.add(edge);
        }
        graph
    }

    /// Adds one directed edge, growing the node table as needed.
    ///
    /// # Specification
    /// - ensures: the edge is present exactly once, with earlier edges
    ///   retained.
    /// - panics: an endpoint does not fit the host address space.
    ///
    /// # Adequacy
    /// - hypothesis: L2 candidate-graph comparisons distinguish edge omission.
    /// - witness: `dynamic_graphs::differential::tests::the_differential_catches_a_seeded_wrong_verdict`
    #[inline]
    #[spec(ensures: |_| bool::from(self.holds(edge)))]
    pub fn add(
        &mut self,
        edge: EdgeId,
    )
    {
        let source = usize::try_from(u32::from(edge.source)).expect("a test identifier fits");
        let target = usize::try_from(u32::from(edge.target)).expect("a test identifier fits");
        let width = source.max(target).saturating_add(1);
        if self.adjacency.len() < width {
            self.adjacency.resize(width, Vec::new());
        }
        let row = &mut self.adjacency[source];
        if !row.contains(&edge.target) {
            row.push(edge.target);
        }
    }

    /// Whether the graph holds a directed cycle, decided by the batch
    /// traversal.
    ///
    /// # Specification
    /// - ensures: reports exactly the independent batch traversal's verdict.
    /// - panics: the fixture is malformed or its node count cannot fit `u32`.
    ///
    /// # Adequacy
    /// - hypothesis: L2 comparisons distinguish inverted cycle verdicts.
    /// - witness: `dynamic_graphs::differential::tests::the_differential_catches_a_seeded_wrong_verdict`
    #[inline]
    #[spec(ensures: |ret| bool::from(ret) == cycle_witness(self).is_ok_and(|cycle| cycle.is_some()))]
    pub fn has_cycle(&self) -> CycleFound
    {
        CycleFound(
            cycle_witness(self)
                .expect("a dense test graph is well formed")
                .is_some(),
        )
    }

    /// Whether `edge` is present.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn holds(
        &self,
        edge: EdgeId,
    ) -> EdgePresent
    {
        let source = usize::try_from(u32::from(edge.source)).expect("a test identifier fits");
        EdgePresent(
            self.adjacency
                .get(source)
                .is_some_and(|row| row.contains(&edge.target)),
        )
    }

    /// The nodes plus edges one batch recheck would touch.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn batch_cost(&self) -> Cost
    {
        let nodes = u64::try_from(self.adjacency.len()).expect("a test graph is small");
        let edges = self
            .adjacency
            .iter()
            .map(|row| u64::try_from(row.len()).expect("a test row is small"))
            .fold(0u64, u64::saturating_add);
        Cost(nodes.saturating_add(edges))
    }
}

impl EdgeSource for BatchGraph
{
    type Successors<'successors>
        = core::iter::Copied<core::slice::Iter<'successors, NodeId>>
    where
        Self: 'successors;

    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn node_count(&self) -> NodeCount
    {
        NodeCount::from(u32::try_from(self.adjacency.len()).expect("a test graph is small"))
    }

    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn successors(
        &self,
        node: NodeId,
    ) -> Self::Successors<'_>
    {
        let empty: &[NodeId] = &[];
        usize::try_from(u32::from(node))
            .ok()
            .and_then(|index| self.adjacency.get(index))
            .map_or(empty, Vec::as_slice)
            .iter()
            .copied()
    }
}

/// A reproducible generator.
///
/// The streams have to be identical across the differential and the probe, and
/// across runs, so the generator is seeded explicitly rather than drawn from
/// the environment.
#[repr(transparent)]
pub struct Generator
{
    /// The generator's state.
    state: u64,
}

impl Generator
{
    /// A generator from an explicit seed.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn new(seed: Seed) -> Self
    {
        Self {
            state: seed.0 ^ 0x9e37_79b9_7f4a_7c15,
        }
    }

    /// The next raw value, by the `SplitMix64` recurrence.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn draw(&mut self) -> Seed
    {
        self.state = self.state.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut mixed = self.state;
        mixed = (mixed ^ mixed.wrapping_shr(30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        mixed = (mixed ^ mixed.wrapping_shr(27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        Seed(mixed ^ mixed.wrapping_shr(31))
    }

    /// A value below `bound`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn below(
        &mut self,
        bound: Bound,
    ) -> Index
    {
        if bound.0 == 0 {
            return Index(0);
        }
        let drawn = self.draw();
        let reduced = drawn.0.checked_rem(u64::from(bound.0)).unwrap_or(0);
        Index(u32::try_from(reduced).expect("a value below a u32 bound fits"))
    }

    /// One of `choices`, selected by reducing a deterministic draw.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn pick(
        &mut self,
        choices: &[DrawnOffset],
    ) -> DrawnOffset
    {
        if choices.is_empty() {
            return DrawnOffset(0);
        }
        let bound = Bound(u32::try_from(choices.len()).expect("a small choice set fits"));
        let index = usize::from(self.below(bound));
        choices[index]
    }
}

/// Which shape of edge stream a fixture draws.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Family
{
    /// A random acyclic prefix, then offers that mostly violate it — the case
    /// where a long run of cheap admissions is followed by refusals.
    AcyclicThenViolating,
    /// A chain plus offers biased to run backwards along it — the adversarial
    /// case for a topological order, because almost every offer forces a
    /// repair.
    AdversarialBackEdges,
    /// Uniformly random ordered pairs — no structure at all.
    Interleaved,
}

impl Family
{
    /// Every family, for a test that sweeps them.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn all() -> [Self; 3]
    {
        [
            Self::AcyclicThenViolating,
            Self::AdversarialBackEdges,
            Self::Interleaved,
        ]
    }

    /// A short name for a measurement row.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn label(self) -> Label
    {
        match self {
            | Self::AcyclicThenViolating => Label("acyclic-then-violating"),
            | Self::AdversarialBackEdges => Label("adversarial-back-edges"),
            | Self::Interleaved => Label("interleaved"),
        }
    }
}

/// A stream of offers over dense nodes, in the shape `family` names.
///
/// # Specification
/// - ensures: emits at most `length` offers, omitting self-loop draws, with
///   endpoints below `nodes`; the same seed reproduces the same stream.
/// - panics: the finite fixture domain does not fit the host address space.
///
/// # Adequacy
/// - hypothesis: finite fixture streams distinguish invalid graph observations
///   and incomplete comparisons through L2 agreement and L3 exact boundaries.
/// - witness: `dynamic_graphs::differential::tests::every_stream_family_is_drift_free`
#[inline]
#[spec(ensures: |ret| ret.len() <= usize::from(length) && ret.iter().all(|edge| edge.source != edge.target && u32::from(edge.source) < u32::from(nodes) && u32::from(edge.target) < u32::from(nodes)))]
pub fn stream(
    family: Family,
    nodes: Bound,
    length: StreamLength,
    seed: Seed,
) -> Vec<EdgeId>
{
    let width = usize::from(length);
    let span = u32::from(nodes);
    let mut generator = Generator::new(seed);
    let mut offers = Vec::with_capacity(width);
    // A random permutation gives the acyclic prefix a topological order that is
    // not the identity, so a passing run cannot be an artefact of dense ids
    // already agreeing with the order.
    let mut rank: Vec<u32> = (0 .. span).collect();
    for index in (1 .. rank.len()).rev() {
        let bound = Bound(u32::try_from(index.saturating_add(1)).expect("a small index fits"));
        let swap = usize::from(generator.below(bound));
        rank.swap(index, swap);
    }
    let midpoint = width.checked_div(2).unwrap_or(0);
    for step in 0 .. width {
        let left = u32::from(generator.below(nodes));
        let right = u32::from(generator.below(nodes));
        if left == right {
            continue;
        }
        let (source, target) = match family {
            | Family::AcyclicThenViolating => {
                if step < midpoint {
                    // Respect the hidden permutation: an edge always runs from
                    // the lower rank to the higher one.
                    let left_rank = rank[usize::try_from(left).expect("an index fits")];
                    let right_rank = rank[usize::try_from(right).expect("an index fits")];
                    if left_rank < right_rank {
                        (left, right)
                    }
                    else {
                        (right, left)
                    }
                }
                else {
                    (left, right)
                }
            },
            | Family::AdversarialBackEdges => {
                // A chain over the dense ids, offered mostly in reverse.
                let wrapped = step
                    .checked_rem(usize::try_from(span).unwrap_or(1))
                    .unwrap_or(0);
                let here = u32::try_from(wrapped).expect("a small index fits");
                let successor = here.saturating_add(1).checked_rem(span).unwrap_or(0);
                if step.checked_rem(3) == Some(0) {
                    (here, successor)
                }
                else {
                    (successor, here)
                }
            },
            | Family::Interleaved => (left, right),
        };
        offers.push(EdgeId::new(NodeId::from(source), NodeId::from(target)));
    }
    offers
}
