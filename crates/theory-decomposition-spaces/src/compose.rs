//! Sequential certificate composition and its conservative seam-flow gate.
//!
//! # Directed composition and identity
//!
//! The graph restricts the endpoints to the holes of the **left** recorded
//! join, and `endpoints` states which variable of a step meets which hole
//! through the step's substitution. A node is a cell and the hole of its own
//! variable, so positions and multiplicities do not count. A forward endpoint
//! emits, a backward endpoint absorbs, and a mixed endpoint does both. Edges
//! cross between the two supports only from emitters to absorbers.
//!
//! A renaming of a cell's variables does not change the verdict. The gate
//! still reads the cells that a representative records, and their variance
//! metadata, which replay-equivalence does not compare. The admitted graft
//! remains a certificate invariant. Reversing one unordered pair can also
//! change the verdict because it changes the selected seam. Pairwise admission
//! is therefore not a substitute for running the binary gate at each actual
//! fold step.
//!
//! The chosen emit-to-absorb criterion is strictly less conservative than a
//! union-of-variances test: sequential producer-to-consumer seams are admitted
//! without inventing a reverse edge. The alternative union criterion remains a
//! test oracle. Reconsider the representation only when a consumer requires a
//! presentation-invariant gate and supplies the extra data that can decide one;
//! a normalized label alone is insufficient.
//!
//! The graph is built afresh for each query. Keep its gate batch-based:
//! successive certificate pairs can change both the support and the left-join
//! hole filter, so they are not insertion-only updates. The dynamic comparison
//! witness streams each characterized graph in both arrival orders and agrees
//! with the batch gate; `gandr-theory-dynamic-graphs` is a development
//! dependency only. Reconsider the gate only for a consumer retaining one
//! standing graph or accumulating constraints monotonically across calls. No
//! standing dynamic graph, durable step address, comultiplication or antipode
//! is part of this crate. Build-local normal-form labels never acquire a
//! transport type here.
//!
//! # Presentation witnesses
//!
//! Cell metadata retains both faces of a fused rule. An alpha-renamed
//! representative records its holes under other names. Its substitutions
//! carry the seam holes, so it meets the seam as the two-step representative
//! does. Corpus checks compare semantic verdicts and replay, not an incidental
//! count of pairs.
//!
//! # References
//!
//! - `vault:01a178aa-4e61-7143-9414-8eb3d0de397f` — anchor: the seam gate reads
//!   each hole through the substitutions that the steps record, not by its name
//!   (§ gate-substitution-read).

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_theory_cell_complexes::CellAlphabet;
use gandr_theory_cell_complexes::CellId;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::SeamRole;
use gandr_theory_cell_complexes::SequentAlphabet;
use gandr_theory_coherent_resolutions::Tracelet;
use gandr_theory_graphs::CycleWitness;
use gandr_theory_graphs::EdgeSource;
use gandr_theory_graphs::GraphValidationError;
use gandr_theory_graphs::NodeCount;
use gandr_theory_graphs::NodeId;
use gandr_theory_graphs::cycle_witness;
use quenchant_shape::shape::Maybe;

use crate::boundary::VarianceFlowRole;

/// Why directed composition could not produce a certificate.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CompositionObstruction<A: CellAlphabet = SequentAlphabet>
{
    /// A closed variable-flow walk, with no duplicated closing node.
    Cycle
    {
        /// Participating cells and their shared hole.
        cycle: Vec<(CellId, A::Var)>,
    },
    /// The graph exceeds the dense identifier space.
    NodeCapacityExceeded,
    /// Graph validation or allocation failed; never interpreted as acyclicity.
    Graph
    {
        /// The graph operation's exact failure.
        error: GraphValidationError,
    },
}

/// Compose certificates in the invertible coherence lane.
///
/// # Specification
/// - requires: both inputs replay, the cells are invertible, and `a.joins_at ==
///   b.overlap.peak`.
/// - ensures: both paths concatenate in order, retaining the left overlap and
///   right join, and recorded on the left peak as [`graft`] records them.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 seam-role boundaries and replay witnesses separate omitted
///   flow edges, changed boundaries and lost certificate steps.
/// - witness: `tests::composition::invertible_composition_of_a_ground_chain_replays`
#[spec(ensures: |ret| ret.overlap == a.overlap && ret.joins_at == b.joins_at && ret.path_a.iter().eq(a.path_a.iter().chain(&b.path_a)) && ret.path_b.iter().eq(a.path_b.iter().chain(&b.path_b)))]
#[inline]
#[must_use]
pub fn compose_invertible<A>(
    a: &Tracelet<A>,
    b: &Tracelet<A>,
    store: &CellStore<A>,
) -> Tracelet<A>
where
    A: CellAlphabet,
{
    graft(a, b, store)
}

/// Compose directed certificates when their seam variable flow is acyclic.
///
/// This is a single-shot batch gate: its node set depends on the current
/// certificate pair and the left recorded join. Chaining changes the hole
/// filter, so successive graphs are not insertion-only. Retain batch traversal
/// here; reconsider dynamic maintenance only when a composition surface owns
/// a standing graph across calls or its constraint edges genuinely accumulate.
///
/// # Specification
/// - requires: replayable inputs meet at `a.joins_at == b.overlap.peak`; the
///   verdict reads recorded support.
/// - ensures: success is the sequential graft; a cycle returns its
///   cell-and-hole walk.
/// - fails: a cycle, graph validation failure, or identifier exhaustion is
///   reported.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 seam-role boundaries and replay witnesses separate omitted
///   flow edges, changed boundaries and lost certificate steps.
/// - witness: `tests::composition::the_seam_edge_is_drawn_exactly_when_the_left_emits_and_the_right_absorbs`
#[spec(ensures: |ret| match ret { Ok(ref value) => value.overlap == a.overlap && value.joins_at == b.joins_at && value.path_a.iter().eq(a.path_a.iter().chain(&b.path_a)) && value.path_b.iter().eq(a.path_b.iter().chain(&b.path_b)), Err(CompositionObstruction::Cycle { ref cycle }) => !cycle.is_empty(), Err(CompositionObstruction::Graph { .. } | CompositionObstruction::NodeCapacityExceeded) => true })]
/// # Errors
/// Returns a cycle, graph validation failure, or exhausted identifier space.
#[inline]
pub fn compose_directed<A>(
    a: &Tracelet<A>,
    b: &Tracelet<A>,
    store: &CellStore<A>,
) -> Result<Tracelet<A>, CompositionObstruction<A>>
where
    A: CellAlphabet,
{
    let graph = VarFlowGraph::build(a, b, store)?;
    let cycle = cycle_witness(&graph).map_err(|error| CompositionObstruction::Graph { error })?;
    cycle.map_or_else(
        || Ok(graft(a, b, store)),
        |witness| Err(graph.obstruction(&witness)),
    )
}

/// Concatenate both recorded paths at a sequential seam.
///
/// The right certificate recorded its steps on its own peak skolemized. Its
/// join metavariables that the left peak does not hold stay metavariables
/// when the composite replays, so the composite records its paths again on
/// the left peak ([`Tracelet::recorded`]).
///
/// # Specification
/// - ensures: retains the left overlap and right join, with both paths
///   concatenated and recorded on the left peak.
/// - panics: none.
/// - intension: one copy and one firing by match of each step.
///
/// # Adequacy
/// - hypothesis: L3 seam-role boundaries and replay witnesses separate omitted
///   flow edges, changed boundaries and lost certificate steps.
/// - witness: `tests::composition::invertible_composition_of_a_ground_chain_replays`
#[spec(ensures: |ret| ret.overlap == a.overlap && ret.joins_at == b.joins_at && ret.path_a.iter().eq(a.path_a.iter().chain(&b.path_a)) && ret.path_b.iter().eq(a.path_b.iter().chain(&b.path_b)))]
#[inline]
fn graft<A>(
    a: &Tracelet<A>,
    b: &Tracelet<A>,
    store: &CellStore<A>,
) -> Tracelet<A>
where
    A: CellAlphabet,
{
    let path_a = a.path_a.iter().chain(&b.path_a).cloned().collect();
    let path_b = a.path_b.iter().chain(&b.path_b).cloned().collect();
    Tracelet {
        overlap: a.overlap.clone(),
        path_a,
        path_b,
        joins_at: b.joins_at.clone(),
    }
    .recorded(store)
}

/// Dense seam-flow graph, addressed by interned endpoint identifiers.
struct VarFlowGraph<A: CellAlphabet>
{
    /// Semantic endpoint at each dense identifier.
    nodes: Vec<(CellId, A::Var)>,
    /// Outgoing flow edges, one row per endpoint.
    adjacency: Vec<Vec<NodeId>>,
}

impl<A: CellAlphabet> VarFlowGraph<A>
{
    /// Build emit-to-absorb edges across the left recorded join.
    ///
    /// # Specification
    /// - ensures: success contains only in-range edges between interned
    ///   endpoints.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 seam-role boundaries and replay witnesses separate
    ///   omitted flow edges, changed boundaries and lost certificate steps.
    /// - witness: `tests::composition::the_seam_edge_is_drawn_exactly_when_the_left_emits_and_the_right_absorbs`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |graph| graph.nodes.len() == graph.adjacency.len() && graph.adjacency.iter().flatten().all(|node| usize::try_from(u32::from(*node)).is_ok_and(|index| index < graph.nodes.len()))))]
    #[inline]
    fn build(
        a: &Tracelet<A>,
        b: &Tracelet<A>,
        store: &CellStore<A>,
    ) -> Result<Self, CompositionObstruction<A>>
    {
        let holes = seam_holes::<A>(&a.joins_at);
        let a_ends = endpoints(a, &holes, store);
        let b_ends = endpoints(b, &holes, store);
        let mut builder = GraphBuilder::default();
        for (a_endpoints, b_endpoints) in a_ends.iter().zip(&b_ends) {
            for a_endpoint in a_endpoints {
                for b_endpoint in b_endpoints {
                    let node_a = builder.intern(a_endpoint.0, &a_endpoint.1)?;
                    let node_b = builder.intern(b_endpoint.0, &b_endpoint.1)?;
                    if bool::from(emits(a_endpoint.2)) && bool::from(absorbs(b_endpoint.2)) {
                        builder.edge(node_a, node_b);
                    }
                    if bool::from(emits(b_endpoint.2)) && bool::from(absorbs(a_endpoint.2)) {
                        builder.edge(node_b, node_a);
                    }
                }
            }
        }
        Ok(builder.finish())
    }

    /// Map a graph cycle back to semantic cell-and-hole endpoints.
    ///
    /// # Specification
    /// - ensures: the closing duplicate is omitted and every returned endpoint
    ///   comes from the graph.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 seam-role boundaries and replay witnesses separate
    ///   omitted flow edges, changed boundaries and lost certificate steps.
    /// - witness: `tests::composition::the_seam_edge_is_drawn_exactly_when_the_left_emits_and_the_right_absorbs`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "refusal path: the check pairs the cycle with the seam endpoints of one composition, a graph whose builder already paired its endpoints"
        )
    )]
    #[spec(ensures: |ret| matches!(&ret, CompositionObstruction::Cycle { cycle } if !cycle.is_empty() && cycle.iter().all(|node| self.nodes.contains(node))))]
    #[inline]
    fn obstruction(
        &self,
        witness: &CycleWitness,
    ) -> CompositionObstruction<A>
    {
        let walk = witness
            .nodes
            .split_last()
            .map_or(witness.nodes.as_slice(), |(_, rest)| rest);
        let mut cycle = Vec::with_capacity(walk.len());
        for &node in walk {
            if let Some(entry) = usize::try_from(u32::from(node))
                .ok()
                .and_then(|index| self.nodes.get(index))
            {
                cycle.push(entry.clone());
            }
        }
        CompositionObstruction::Cycle { cycle }
    }
}

impl<A: CellAlphabet> EdgeSource for VarFlowGraph<A>
{
    type Successors<'successors>
        = core::iter::Copied<core::slice::Iter<'successors, NodeId>>
    where
        Self: 'successors;

    /// The number of interned endpoints.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn node_count(&self) -> NodeCount
    {
        NodeCount::from(u32::try_from(self.nodes.len()).unwrap_or(u32::MAX))
    }

    /// The outgoing row, or an empty row for an unissued identifier.
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

/// Interned endpoints and their outgoing seam-flow edges.
struct GraphBuilder<A: CellAlphabet>
{
    /// Semantic endpoint at each dense identifier.
    nodes: Vec<(CellId, A::Var)>,
    /// Dense identifier of each cell-and-hole key.
    index: BTreeMap<(CellId, A::Hole), NodeId>,
    /// Outgoing flow edges, one row per endpoint.
    adjacency: Vec<Vec<NodeId>>,
}

impl<A: CellAlphabet> Default for GraphBuilder<A>
{
    /// An empty flow-graph builder.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self {
            nodes: Vec::new(),
            index: BTreeMap::new(),
            adjacency: Vec::new(),
        }
    }
}

impl<A: CellAlphabet> GraphBuilder<A>
{
    /// Intern one cell-and-hole endpoint with a stable dense identifier.
    ///
    /// # Specification
    /// - ensures: success resolves to the offered cell and hole; exhaustion is
    ///   typed.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 seam-role boundaries and replay witnesses separate
    ///   omitted flow edges, changed boundaries and lost certificate steps.
    /// - witness: `tests::composition::the_seam_edge_is_drawn_exactly_when_the_left_emits_and_the_right_absorbs`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |id| self.index.get(&(cell, A::hole_of(var))) == Some(id) && usize::try_from(u32::from(*id)).is_ok_and(|index| self.nodes.get(index).is_some_and(|entry| entry.0 == cell && A::hole_of(&entry.1) == A::hole_of(var)))))]
    #[inline]
    fn intern(
        &mut self,
        cell: CellId,
        var: &A::Var,
    ) -> Result<NodeId, CompositionObstruction<A>>
    {
        let key = (cell, A::hole_of(var));
        if let Some(&id) = self.index.get(&key) {
            return Ok(id);
        }
        let index = u32::try_from(self.nodes.len())
            .map_err(|_error| CompositionObstruction::NodeCapacityExceeded)?;
        if index == u32::MAX {
            return Err(CompositionObstruction::NodeCapacityExceeded);
        }
        let id = NodeId::from(index);
        self.nodes.push((cell, var.clone()));
        self.adjacency.push(Vec::new());
        self.index.insert(key, id);
        Ok(id)
    }

    /// Insert one flow edge without parallel duplicates.
    ///
    /// # Specification
    /// - ensures: an in-range source contains the target exactly once after
    ///   insertion.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 seam-role boundaries and replay witnesses separate
    ///   omitted flow edges, changed boundaries and lost certificate steps.
    /// - witness: `tests::composition::the_seam_edge_is_drawn_exactly_when_the_left_emits_and_the_right_absorbs`
    #[spec(ensures: |ret| usize::try_from(u32::from(from)).ok().and_then(|index| self.adjacency.get(index)).is_none_or(|row| row.iter().filter(|node| **node == to).count() == 1))]
    #[inline]
    fn edge(
        &mut self,
        from: NodeId,
        to: NodeId,
    )
    {
        if let Some(row) = usize::try_from(u32::from(from))
            .ok()
            .and_then(|index| self.adjacency.get_mut(index))
            && !row.contains(&to)
        {
            row.push(to);
        }
    }

    /// Move the interned rows into a graph.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn finish(self) -> VarFlowGraph<A>
    {
        VarFlowGraph {
            nodes: self.nodes,
            adjacency: self.adjacency,
        }
    }
}

/// Classify the producer half of a seam endpoint.
///
/// # Specification
/// - ensures: only forward and mixed roles emit.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 seam-role boundaries and replay witnesses separate omitted
///   flow edges, changed boundaries and lost certificate steps.
/// - witness: `tests::composition::the_seam_edge_is_drawn_exactly_when_the_left_emits_and_the_right_absorbs`
#[spec(ensures: |ret| bool::from(ret) == matches!(role, SeamRole::Forward | SeamRole::Both))]
#[inline]
fn emits(role: SeamRole) -> VarianceFlowRole
{
    VarianceFlowRole::from(matches!(role, SeamRole::Forward | SeamRole::Both))
}

/// Classify the consumer half of a seam endpoint.
///
/// # Specification
/// - ensures: only backward and mixed roles absorb.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 seam-role boundaries and replay witnesses separate omitted
///   flow edges, changed boundaries and lost certificate steps.
/// - witness: `tests::composition::the_seam_edge_is_drawn_exactly_when_the_left_emits_and_the_right_absorbs`
#[spec(ensures: |ret| bool::from(ret) == matches!(role, SeamRole::Backward | SeamRole::Both))]
#[inline]
fn absorbs(role: SeamRole) -> VarianceFlowRole
{
    VarianceFlowRole::from(matches!(role, SeamRole::Backward | SeamRole::Both))
}

/// Collect the distinct holes of a seam term.
///
/// # Specification
/// - ensures: each observed hole occurs exactly once, without introducing a
///   hole.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 seam-role boundaries and replay witnesses separate omitted
///   flow edges, changed boundaries and lost certificate steps.
/// - witness: `tests::composition::the_seam_edge_is_drawn_exactly_when_the_left_emits_and_the_right_absorbs`
#[spec(ensures: |ret| A::metavariables(cmd).iter().all(|var| ret.iter().filter(|hole| **hole == A::hole_of(var)).count() == 1) && ret.iter().all(|hole| A::metavariables(cmd).iter().any(|var| A::hole_of(var) == *hole)))]
#[inline]
fn seam_holes<A>(cmd: &A::Cmd) -> Vec<A::Hole>
where
    A: CellAlphabet,
{
    let mut seen: BTreeSet<A::Hole> = BTreeSet::new();
    let mut holes: Vec<A::Hole> = Vec::new();
    for var in A::metavariables(cmd) {
        let hole = A::hole_of(&var);
        if seen.insert(hole.clone()) {
            holes.push(hole);
        }
    }
    holes
}

/// The seam endpoints of `side` at each hole of `holes`, in the order of
/// `holes`.
///
/// A variable of a step's cell carries a hole when the step's substitution
/// binds it to an image that holds the hole ([`CellAlphabet::image_holds`]).
/// A wire, which the left-hand side does not bind, carries the hole that its
/// name spells. Each carrying variable gives the endpoints that the cell's
/// metadata holds for the variable's own hole, with their roles
/// ([`CellAlphabet::hole_flow`]). A step whose cell the store does not hold
/// gives no endpoint.
///
/// # Specification
/// - ensures: one list for each hole of `holes`. Each endpoint names the cell
///   of a step of `side` that the store holds, and an entry of that cell's hole
///   flow for the hole of a variable that carries the hole. No list holds one
///   endpoint twice.
/// - panics: none.
/// - intension: one read of each left-hand-side image for each step and hole.
///
/// # Adequacy
/// - hypothesis: L3 — two certificates that share a seam hole by flow meet
///   there, and a cell variable that only spells the seam hole's name is no
///   endpoint. Keying an endpoint by its variable's name, or dropping the image
///   read, changes the verdict.
/// - witness: `tests::composition::an_unrelated_hole_spelled_alike_is_no_seam_endpoint`
/// - witness: `tests::composition::the_seam_edge_is_drawn_exactly_when_the_left_emits_and_the_right_absorbs`
#[spec(ensures: |ret| ret.len() == holes.len() && ret.iter().zip(holes).all(|(ends, hole)| ends.iter().enumerate().all(|(index, endpoint)|
    !ends.iter().take(index).any(|earlier| earlier == endpoint)
    && side.path_a.iter().chain(&side.path_b).any(|step| step.cell == endpoint.0 && matches!(store.get(endpoint.0), Maybe::Present(entry)
        if A::metavariables(entry.lhs()).iter()
            .filter(|var| matches!(A::image(&step.subst, var), Maybe::Present(image) if bool::from(A::image_holds(image, hole))))
            .chain(entry.wires().iter().filter(|wire| A::hole_of(wire) == *hole))
            .any(|var| A::hole_flow(entry.meta(), &A::hole_of(var)).contains(&(endpoint.1.clone(), endpoint.2))))))))]
#[inline]
fn endpoints<A>(
    side: &Tracelet<A>,
    holes: &[A::Hole],
    store: &CellStore<A>,
) -> Vec<Vec<(CellId, A::Var, SeamRole)>>
where
    A: CellAlphabet,
{
    let mut out: Vec<Vec<(CellId, A::Var, SeamRole)>> = holes.iter().map(|_| Vec::new()).collect();
    // A cell gives the same endpoints for one of its own holes at every step,
    // and two of its holes give disjoint ones, so each is given once.
    let mut given: BTreeSet<(usize, CellId, A::Hole)> = BTreeSet::new();
    for step in side.path_a.iter().chain(&side.path_b) {
        let Maybe::Present(entry) = store.get(step.cell)
        else {
            continue;
        };
        let mut give = |index: usize, var: &A::Var| {
            let own = A::hole_of(var);
            if !given.insert((index, step.cell, own.clone())) {
                return;
            }
            if let Some(ends) = out.get_mut(index) {
                ends.extend(
                    A::hole_flow(entry.meta(), &own)
                        .into_iter()
                        .map(|(flowing, role)| (step.cell, flowing, role)),
                );
            }
        };
        for var in &A::metavariables(entry.lhs()) {
            let Maybe::Present(image) = A::image(&step.subst, var)
            else {
                continue;
            };
            for (index, hole) in holes.iter().enumerate() {
                if bool::from(A::image_holds(image, hole)) {
                    give(index, var);
                }
            }
        }
        for wire in entry.wires() {
            let spelled = A::hole_of(wire);
            for (index, hole) in holes.iter().enumerate() {
                if *hole == spelled {
                    give(index, wire);
                }
            }
        }
    }
    out
}
