//! The atom-occurrence flow projection: a certificate-side identity relation
//! that sits beside replay-equivalence and the tracelet normal form, and that
//! nothing in the crate consumes.
//!
//! [`replay_equivalent`](gandr_theory_coherent_resolutions::replay_equivalent)
//! remains the identity criterion and [`nf_equal`](crate::nf_equal) the
//! decidable fast path. This module measures one question: whether tracking
//! cell and atom occurrences across a recorded leg, and forgetting the
//! formula-level arrangement, yields a relation that coincides with
//! certificate identity. It answers by disagreeing with both neighbours on
//! recorded fixtures, and the disagreements are the deliverable; the
//! integration suite's `flow` area holds them.
//!
//! # The construction being instantiated
//!
//! The source object is the atomic flow of Guglielmi and Gundersen,
//! "Normalisation control in deep inference via atomic flows", LMCS 4(1:9)
//! 2008, Definition 3.2: a tuple `(V, E, η, up, lo)` where `V` is a finite
//! vertex set, `E` a finite edge set, `η` labels each vertex with the rule
//! instance it stands for, and `up`/`lo` map each edge to a vertex or to one of
//! two special vertices `⊤`, which creates the premiss's atom occurrences, and
//! `⊥`, which destroys the conclusion's. Edges are atom occurrences; the
//! logical structure of the formulas is discarded.
//!
//! The instantiation replaces two components and keeps the rest:
//!
//! - `V` is the cell-application events of one recorded leg.
//! - `η` labels a vertex with the firing cell's position-free content address
//!   ([`cell_address`]). The position is absent on purpose:
//!   [`prim_address`](crate::prim_address) digests the position too, and a flow
//!   labelled by primitive addresses would re-import the arrangement the
//!   projection is defined to forget.
//! - `E`, `up`, `lo`, `⊤` and `⊥` are the source's: an edge is one atom
//!   occurrence's thread, `⊤` creates the peak's occurrences, and `⊥` destroys
//!   the occurrences surviving to the leg's end.
//!
//! The consequence that carries weight is that [`Flow`] has no alphabet
//! parameter. Once the arrangement is discarded nothing alphabet-shaped is
//! left: a flow is combinatorial data, and only [`project_flow`] is generic.
//!
//! What is imported is the projection's shape. The source line's
//! normalisation control (streamlining, its splitting measures, the flow
//! rewriting that drives them) is stated for classical deep-inference systems
//! and none of it is used here: this module defines a relation and decides it,
//! and every soundness argument it rests on is discharged in this crate.
//!
//! One boundary convention diverges from the source on purpose. The source's
//! flows forget the premiss and conclusion outright; this projection anchors
//! `⊤`, so a peak occurrence's thread carries which occurrence of the peak it
//! is, because the relation compares two legs of one peak and an unanchored
//! comparison would identify legs consuming different parts of it.
//!
//! # The resolution ceiling
//!
//! An atom occurrence is an entry of
//! [`CellAlphabet::command_positions`], so the projection is exactly as fine
//! as the alphabet's address vocabulary. Over the sequent alphabet a term has
//! one address and every leg projects to a chain through one thread per step;
//! the differential suite therefore runs on the toy alphabet, whose terms nest
//! commands.
//!
//! # The strict projection
//!
//! A step consumes every occurrence its match image covers and creates every
//! occurrence the image covers afterwards; occurrences outside the image
//! thread through at unchanged addresses. Nothing inside a redex is traced
//! from one side of the step to the other. The lax projection would carry a
//! redex's hole contents across the step, which needs a residual map on
//! positions that [`CellApp`] has no room for. The strict projection is sound
//! without it, since refusing to identify two occurrences is the safe
//! direction, and exact on the permutation-tile class, where the two images
//! are disjoint and nothing needs transporting.
//!
//! # The convexity fence
//!
//! Convexity is formula-level arrangement, so a flow cannot see it: applying
//! one rule can create a directed path that destroys another match's
//! convexity on hyperedge sets that never met (Bonchi, Gadducci, Kissinger,
//! Sobociński and Zanasi, *String Diagram Rewrite Theory II*). The projection
//! is sound on exactly the fence
//! [`ConvexityDischarge::StronglyConnectedOverAcyclicTarget`] names; every
//! [`Flow`] carries the discharge it was taken under, and two flows taken
//! under different discharges are never identified.
//!
//! # Where this sits between its neighbours
//!
//! On certificate data the three relations nest strictly, each strictness
//! with a fixture in the integration suite:
//!
//! - Shift equivalence is strictly inside flow equality. The shift guard
//!   refuses a pair whose cells overlap even at incomparable positions, because
//!   it asks a question about the alphabet; the projection reads the instance,
//!   where two disjoint images share no occurrence, and identifies the pair.
//! - Flow equality is strictly inside replay-equivalence. Replay-equivalence
//!   compares a boundary and asks each side to replay, ignoring the recorded
//!   paths; the engine's fused certificate is one boundary whose two legs carry
//!   different vertex labels, replay-equal and flow-distinct.
//!
//! The second containment holds for a relation that compares certificates,
//! boundaries included. Comparing the projected flows alone is not inside
//! replay-equivalence: one cell fired on two unrelated ground instances gives
//! one flow over two boundaries. So [`TraceletFlow`] carries the peak and the
//! join beside the two flows, [`tracelet_flow`] refuses a leg landing anywhere
//! else, and containment follows from what the datum is. [`Flow`] stays
//! alphabet-free; the parameter the boundary brings sits on [`TraceletFlow`].
//!
//! # Refuse where a choice would be arbitrary
//!
//! [`Flow::canonical`] gives no canonical form to a flow whose vertices share
//! a re-indexing key, and the fence gives no identification under
//! [`ConvexityDischarge::ReCheckRequired`]. Both follow one rule: an
//! identification not made is always sound, and one made wrongly is not. A
//! negative from this module means "not identified here", never "distinct".
//!
//! # Cost
//!
//! Unoptimized on purpose: one rewrite per recorded step, a linear scan of the
//! term's addresses per step and a quadratic address lookup inside it. It is
//! a measurement instrument, not a fast path.

use alloc::boxed::Box;
use alloc::vec::Vec;

use anodized::spec;
use gandr_theory_cell_complexes::CellAlphabet;
use gandr_theory_cell_complexes::CellId;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::ConvexityDischarge;
use gandr_theory_cell_complexes::PositionOrder;
use gandr_theory_cell_complexes::SequentAlphabet;
use gandr_theory_coherent_resolutions::CellApp;
use gandr_theory_coherent_resolutions::Tracelet;
use gandr_theory_coherent_resolutions::rewrite_at;
use quenchant_shape::shape::Maybe;

use crate::boundary::CausalDepth;
use crate::boundary::FlowEquality;
use crate::boundary::FlowPortIndex;
use crate::boundary::FlowVertexIndex;
use crate::boundary::PeakOccurrenceIndex;
use crate::normal_form::CellAddress;
use crate::normal_form::cell_address;

quenchant_shape::reason_enum! {
    /// Why a flow has no canonical form.
    pub mod flow_canonical {
        /// The reason no canonical vertex order is determined.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// Two vertices share a re-indexing key, so ordering them would be
            /// an arbitrary choice.
            IndistinguishableVertices,
        }
    }
}

wrapper! {
    /// The number of upper or lower incidences one flow vertex carries.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    struct IncidenceCount(usize);
}

wrapper! {
    /// Whether one address lies inside a step's match image.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
    struct ImageCoverage(bool);
}

/// One end of an atom-occurrence thread: a vertex of the flow, or one of the
/// two special vertices.
///
/// The variant order is the comparison order the canonical form sorts on, and
/// reads top-down: the premiss boundary, the body, the conclusion boundary.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum FlowEnd
{
    /// The special vertex that creates every atom occurrence of the peak,
    /// carrying which occurrence of the peak this thread starts at.
    Peak
    {
        /// The occurrence's index in the peak's enumerated addresses.
        occurrence: PeakOccurrenceIndex,
    },
    /// A cell-application event, at one of its upper or lower ports.
    Vertex
    {
        /// Which event.
        vertex: FlowVertexIndex,
        /// Which incidence of that event, in its match image's address order.
        port: FlowPortIndex,
    },
    /// The special vertex that destroys every atom occurrence surviving to the
    /// end of the leg.
    Join,
}

/// One atom-occurrence thread: an edge of the flow, with the source's `up`
/// and `lo` maps read off it.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FlowThread
{
    /// Where the occurrence is created.
    pub up: FlowEnd,
    /// Where the occurrence is destroyed.
    pub lo: FlowEnd,
}

/// The atom-occurrence flow of one recorded leg.
///
/// It carries no alphabet parameter: once the formula-level arrangement is
/// discarded there is nothing alphabet-shaped left in it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Flow
{
    /// `η`: one content address per cell-application event, indexed by
    /// [`FlowEnd::Vertex`]'s `vertex` field.
    pub labels: Vec<CellAddress>,
    /// `E` with its `up` and `lo` maps.
    pub threads: Vec<FlowThread>,
    /// The warrant the projection's soundness fence was discharged under,
    /// carried rather than recomputed.
    pub convexity: ConvexityDischarge,
}

/// The flow of a certificate: its boundary, and its two legs' flows.
///
/// A certificate is a boundary together with derivations of it, so a datum
/// standing for one without its endpoints stands for less than a certificate.
/// The alphabet parameter sits here and not on [`Flow`]: the combinatorial
/// datum stays alphabet-free, and only the boundary it is a flow of is
/// alphabet-shaped.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TraceletFlow<A: CellAlphabet = SequentAlphabet>
{
    /// The term both legs are derivations from, as recorded; the projection
    /// skolemizes it.
    pub peak: A::Cmd,
    /// The term both legs reach, as recorded.
    pub joins_at: A::Cmd,
    /// The first leg's flow.
    pub path_a: Flow,
    /// The second leg's flow.
    pub path_b: Flow,
}

/// Why a recorded leg could not be projected to a flow.
///
/// A recorded step list that is not a derivation of the peak has no flow.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum FlowObstruction<A: CellAlphabet = SequentAlphabet>
{
    /// A recorded step names a cell the store does not hold.
    UnknownCell
    {
        /// The identifier that resolved to nothing.
        cell: CellId,
    },
    /// A recorded step does not fire at its recorded position, so the leg is
    /// not a derivation and there is nothing to project.
    StepDoesNotFire
    {
        /// The step that failed to fire.
        step: Box<CellApp<A>>,
    },
    /// Every recorded step fired and the leg landed somewhere other than the
    /// certificate's recorded join: a derivation, of a different boundary.
    ///
    /// Only [`tracelet_flow`] raises it, because only a certificate has a join
    /// to miss.
    LegMissesTheJoin
    {
        /// The skolemized term the leg reached.
        reached: Box<A::Cmd>,
    },
}

/// An atom occurrence still alive at some point in the walk.
#[derive(Clone, Debug)]
struct LiveAtom<A: CellAlphabet>
{
    /// Where the occurrence was created.
    birth: FlowEnd,
    /// The address it currently sits at.
    at: A::Pos,
}

/// The re-indexing key of one flow vertex.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct VertexKey
{
    /// The causal layer, compared first.
    depth: CausalDepth,
    /// The cell content address.
    label: CellAddress,
    /// The peak occurrences this vertex consumes, sorted.
    from_peak: Vec<PeakOccurrenceIndex>,
    /// How many occurrences it consumes.
    upper: IncidenceCount,
    /// How many it creates.
    lower: IncidenceCount,
}

impl Flow
{
    /// The canonical form: the same flow with its vertices re-indexed by a key
    /// that does not depend on the order the leg recorded them in.
    ///
    /// The key is the causal depth, then the label, then the sorted peak
    /// occurrences the vertex consumes, then its two incidence counts.
    ///
    /// # Specification
    /// - ensures: a flow whose `labels` are the input's re-indexed by key order
    ///   and whose `threads` are the input's rewritten to the new indices and
    ///   sorted, carrying the input's convexity discharge; two flows differing
    ///   only in the order their legs recorded independent events have equal
    ///   canonical forms.
    /// - provides: the comparison form [`flows_equal`] decides on;
    ///   [`flow_canonical::Absent::IndistinguishableVertices`] when two
    ///   vertices share a key, the conservative direction, since an
    ///   identification not made is always sound.
    /// - panics: none.
    /// - intension: one forward pass for the depths, the recorded order being
    ///   topological because an occurrence is created before it is consumed,
    ///   then one sort of the vertices and one of the threads.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the two outcomes own separate decision surfaces,
    ///   separated by the permutation tile, whose two legs record one pair of
    ///   events in opposite orders and canonicalize together, and by a flow
    ///   whose two vertices share a label, a depth and no peak incidence, which
    ///   is refused rather than ordered. A projected pair with equal labels and
    ///   opposite recording order has an exact canonical thread list: peak
    ///   anchors select the order and both endpoint indices change without
    ///   changing ports. Dropped threads, lost boundary ends or one-sided
    ///   re-indexing change that list.
    /// - witness: `tests::flow::the_two_legs_of_a_permutation_tile_have_one_flow`
    /// - witness: `flow::tests::indistinguishable_vertices_are_refused_a_canonical_order`
    /// - witness: `flow::tests::canonical_reindexing_preserves_peak_anchors_and_ports`
    #[inline]
    #[spec(ensures: |output| {
    let depths = self.causal_depths();
    let mut keys: Vec<(VertexKey, FlowVertexIndex)> = self.labels.iter().enumerate().map(|(index, label)| (self.vertex_key(FlowVertexIndex::from(index), *label, depths.get(index).copied().unwrap_or_default()), FlowVertexIndex::from(index))).collect();
    keys.sort_by(|left, right| left.0.cmp(&right.0));
    let tied = keys.iter().zip(keys.iter().skip(1)).any(|(left, right)| left.0 == right.0);
    match output {
        Maybe::Absent(flow_canonical::Absent::IndistinguishableVertices) => tied,
        Maybe::Present(ref canonical) => !tied && {
            let mut rank = alloc::vec![FlowVertexIndex::default(); keys.len()];
            for (fresh, entry) in keys.iter().enumerate() { if let Some(slot) = rank.get_mut(usize::from(entry.1)) { *slot = FlowVertexIndex::from(fresh); } }
            let mut threads: Vec<FlowThread> = self.threads.iter().map(|thread| FlowThread { up: reindex_end(thread.up, &rank), lo: reindex_end(thread.lo, &rank) }).collect();
            threads.sort_unstable();
            canonical.convexity == self.convexity && canonical.labels.iter().copied().eq(keys.iter().map(|entry| entry.0.label)) && canonical.threads == threads
        },
    }
})]
    pub fn canonical(&self) -> Maybe<Self, flow_canonical::Absent>
    {
        let depths = self.causal_depths();
        let mut keys: Vec<(VertexKey, FlowVertexIndex)> = self
            .labels
            .iter()
            .enumerate()
            .map(|(index, label)| {
                let vertex = FlowVertexIndex::from(index);
                let depth = depths.get(index).copied().unwrap_or_default();
                (self.vertex_key(vertex, *label, depth), vertex)
            })
            .collect();
        keys.sort_by(|left, right| left.0.cmp(&right.0));
        if keys
            .iter()
            .zip(keys.iter().skip(1_usize))
            .any(|(left, right)| left.0 == right.0)
        {
            return Maybe::Absent(flow_canonical::Absent::IndistinguishableVertices);
        }
        // `rank[old] = new`, built by walking the sorted keys.
        let mut rank: Vec<FlowVertexIndex> = alloc::vec![FlowVertexIndex::default(); keys.len()];
        let mut labels = Vec::with_capacity(keys.len());
        for (fresh, entry) in keys.iter().enumerate() {
            let old = usize::from(entry.1);
            if let Some(slot) = rank.get_mut(old) {
                *slot = FlowVertexIndex::from(fresh);
            }
            labels.push(entry.0.label);
        }
        let mut threads: Vec<FlowThread> = self
            .threads
            .iter()
            .map(|thread| FlowThread {
                up: reindex_end(thread.up, &rank),
                lo: reindex_end(thread.lo, &rank),
            })
            .collect();
        threads.sort_unstable();
        Maybe::Present(Self {
            labels,
            threads,
            convexity: self.convexity,
        })
    }

    /// The causal layering: each vertex's depth in the dependence order the
    /// threads induce.
    ///
    /// # Specification
    /// - requires: every `Vertex` end's index is in range for `labels`, which
    ///   [`project_flow`] establishes.
    /// - ensures: one entry per vertex; zero for a vertex consuming no
    ///   occurrence another vertex created, and otherwise one more than the
    ///   greatest depth among those creators.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a dependent pair layers its two vertices apart, and
    ///   two same-labelled vertices under one creator share a layer, which is
    ///   what makes their keys tie. A consumer receiving occurrences from
    ///   creators at different depths must use the greatest depth, not the
    ///   first incoming edge. The same projected graph has unequal incidence
    ///   counts, separating the key’s port counts.
    /// - witness: `tests::flow::a_consumed_creation_is_one_thread_between_two_vertices`
    /// - witness: `tests::flow::the_games_quotient_identifies_a_tile_the_flow_declines_a_canonical_form`
    /// - witness: `flow::tests::mixed_depth_creators_determine_the_maximum_layer`
    #[spec(requires: self.threads.iter().all(|thread| [thread.up, thread.lo].into_iter().all(|end| match end { FlowEnd::Vertex { vertex, .. } => usize::from(vertex) < self.labels.len(), FlowEnd::Peak { .. } | FlowEnd::Join => true })), ensures: |output| {
    let mut expected = alloc::vec![CausalDepth::default(); self.labels.len()];
    for thread in &self.threads {
        if let (FlowEnd::Vertex { vertex: up, .. }, FlowEnd::Vertex { vertex: lo, .. }) = (thread.up, thread.lo) {
            let lifted = output.get(usize::from(up)).map(|depth| CausalDepth::from(usize::from(*depth).saturating_add(1_usize))).unwrap_or_default();
            if let Some(slot) = expected.get_mut(usize::from(lo)) { *slot = (*slot).max(lifted); }
        }
    }
    output == expected
})]
    fn causal_depths(&self) -> Vec<CausalDepth>
    {
        let mut depths: Vec<CausalDepth> = alloc::vec![CausalDepth::default(); self.labels.len()];
        // The recorded order is topological: a thread runs from the event that
        // created an occurrence to the event that consumed it, and creation
        // precedes consumption in the leg.
        for thread in &self.threads {
            let (FlowEnd::Vertex { vertex: up, .. }, FlowEnd::Vertex { vertex: lo, .. }) =
                (thread.up, thread.lo)
            else {
                continue;
            };
            let source = depths.get(usize::from(up)).copied().unwrap_or_default();
            let lifted = CausalDepth::from(usize::from(source).saturating_add(1_usize));
            if let Some(slot) = depths.get_mut(usize::from(lo))
                && *slot < lifted
            {
                *slot = lifted;
            }
        }
        depths
    }

    /// The sort key of one vertex.
    ///
    /// # Specification
    /// - ensures: a key built only from data invariant under reordering
    ///   independent events: the depth, the label, the peak occurrences
    ///   consumed, and the two incidence counts.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the permutation tile's two legs key their vertices
    ///   alike, and one cell fired at two peak occurrences keys apart on the
    ///   occurrence it consumes. Unequal match-image sizes give distinct upper
    ///   and lower incidence counts, observed directly on a projected vertex.
    ///   Omitting or counting boundary incidences twice changes the key.
    /// - witness: `tests::flow::the_two_legs_of_a_permutation_tile_have_one_flow`
    /// - witness: `tests::flow::the_projection_forgets_where_a_cell_fired`
    /// - witness: `flow::tests::mixed_depth_creators_determine_the_maximum_layer`
    #[spec(ensures: |output| {
    let mut from_peak = Vec::new();
    let mut upper = 0_usize; let mut lower = 0_usize;
    for thread in &self.threads {
        if matches!(thread.lo, FlowEnd::Vertex { vertex: at, .. } if at == vertex) {
            upper = upper.saturating_add(1_usize);
            if let FlowEnd::Peak { occurrence } = thread.up { from_peak.push(occurrence); }
        }
        if matches!(thread.up, FlowEnd::Vertex { vertex: at, .. } if at == vertex) { lower = lower.saturating_add(1_usize); }
    }
    from_peak.sort_unstable();
    output.depth == depth && output.label == label && output.from_peak == from_peak && usize::from(output.upper) == upper && usize::from(output.lower) == lower
})]
    fn vertex_key(
        &self,
        vertex: FlowVertexIndex,
        label: CellAddress,
        depth: CausalDepth,
    ) -> VertexKey
    {
        let mut from_peak: Vec<PeakOccurrenceIndex> = Vec::new();
        let mut upper = 0_usize;
        let mut lower = 0_usize;
        for thread in &self.threads {
            if matches!(thread.lo, FlowEnd::Vertex { vertex: at, .. } if at == vertex) {
                upper = upper.saturating_add(1_usize);
                if let FlowEnd::Peak { occurrence } = thread.up {
                    from_peak.push(occurrence);
                }
            }
            if matches!(thread.up, FlowEnd::Vertex { vertex: at, .. } if at == vertex) {
                lower = lower.saturating_add(1_usize);
            }
        }
        from_peak.sort_unstable();
        VertexKey {
            depth,
            label,
            from_peak,
            upper: IncidenceCount::from(upper),
            lower: IncidenceCount::from(lower),
        }
    }
}

/// Rewrite one thread end through a vertex re-indexing.
///
/// # Specification
/// - ensures: `Peak` and `Join` ends unchanged; a `Vertex` end re-indexed
///   through `rank`, or left alone when its index is out of range, which
///   [`project_flow`]'s output never produces.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the permutation tile's legs index their two vertices in
///   opposite orders and compare equal only once both are re-indexed. The exact
///   canonical graph retains peak and join ends and nonzero ports; an index
///   past the rank table is unchanged rather than clamped or defaulted.
/// - witness: `tests::flow::the_two_legs_of_a_permutation_tile_have_one_flow`
/// - witness: `flow::tests::canonical_reindexing_preserves_peak_anchors_and_ports`
#[spec(ensures: |output| output == match end {
    FlowEnd::Vertex { vertex, port } => rank.get(usize::from(vertex)).map_or(end, |fresh| FlowEnd::Vertex { vertex: *fresh, port }),
    FlowEnd::Peak { .. } | FlowEnd::Join => end,
})]
fn reindex_end(
    end: FlowEnd,
    rank: &[FlowVertexIndex],
) -> FlowEnd
{
    let FlowEnd::Vertex { vertex, port } = end
    else {
        return end;
    };
    let Some(fresh) = rank.get(usize::from(vertex))
    else {
        return end;
    };
    FlowEnd::Vertex {
        vertex: *fresh,
        port,
    }
}

/// Whether `at` covers `position`: the match image test.
///
/// # Specification
/// - ensures: positive for the redex root and every address it encloses,
///   negative for an ancestor and for an incomparable address.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a redex at the root covers the whole term, and two
///   redexes at sibling positions each leave the other's occurrences and the
///   frame above them uncovered.
/// - witness: `tests::flow::a_single_step_leg_threads_the_whole_term_through_one_vertex`
/// - witness: `tests::flow::disjoint_steps_share_no_thread`
#[spec(ensures: |output| bool::from(output) == matches!(A::position_order(at, position), PositionOrder::Same | PositionOrder::Encloses))]
fn covered_by<A>(
    at: &A::Pos,
    position: &A::Pos,
) -> ImageCoverage
where
    A: CellAlphabet,
{
    ImageCoverage::from(matches!(
        A::position_order(at, position),
        PositionOrder::Same | PositionOrder::Encloses
    ))
}

/// Project a recorded leg to its atom-occurrence flow, or refuse it.
///
/// The peak is skolemized first, as replay does, so the projection is taken
/// over the ground derivation. Each recorded step is run rather than reasoned
/// about: a step that does not fire has no transition to attach a vertex to.
///
/// # Specification
/// - requires: `path` is the leg recorded from `peak` against `store`.
/// - ensures: a flow whose `labels` are the firing cells' position-free content
///   addresses in recorded order; whose `threads` carry one edge per atom
///   occurrence, from the peak or the event that created it to the event that
///   consumed it or the conclusion; which carries the alphabet's convexity
///   discharge for `store`; and in which every occurrence a step's match image
///   covers is consumed, every occurrence it covers afterwards is created, and
///   every occurrence outside it threads through at an unchanged address.
/// - provides: the alphabet-independent datum flow equality is decided on.
/// - fails: [`FlowObstruction::UnknownCell`] for an unresolvable identifier and
///   [`FlowObstruction::StepDoesNotFire`] for a step that does not fire at its
///   recorded position.
/// - panics: none.
/// - intension: one rewrite and two address enumerations per step. A vertex's
///   ports are numbered inside its match image, so one step's numbering never
///   depends on what another step did elsewhere; `⊤`'s edges come out in the
///   peak's enumeration order and `⊥`'s in the conclusion's.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — the three occurrence classes own separate decision
///   surfaces, separated by a single step consuming the whole term, by two
///   steps at incomparable positions with an untouched frame, and by a second
///   step consuming what the first created; the refusals by an unstored
///   identifier and a non-firing step. An empty leg retains every skolemized
///   peak occurrence as a boundary thread. A recorded identity remains one
///   vertex with every consumed and created port, so erasing identity steps or
///   losing boundary atoms changes the projection.
/// - witness: `tests::flow::a_single_step_leg_threads_the_whole_term_through_one_vertex`
/// - witness: `tests::flow::disjoint_steps_share_no_thread`
/// - witness: `tests::flow::a_consumed_creation_is_one_thread_between_two_vertices`
/// - witness: `flow::tests::a_leg_that_does_not_fire_has_no_flow`
/// - witness: `flow::tests::empty_and_identity_legs_preserve_their_occurrences`
#[inline]
#[spec(ensures: |output| output == project_walk(store, peak, path).map(|(flow, _reached)| flow))]
pub fn project_flow<A>(
    store: &CellStore<A>,
    peak: &A::Cmd,
    path: &[CellApp<A>],
) -> Result<Flow, FlowObstruction<A>>
where
    A: CellAlphabet,
{
    project_walk(store, peak, path).map(|(flow, _reached)| flow)
}

/// [`project_flow`], keeping the term the leg reached.
///
/// # Specification
/// - ensures: [`project_flow`]'s flow, paired with the skolemized term the last
///   recorded step produced, or the skolemized peak for an empty path.
/// - fails: as [`project_flow`].
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — the reached term is what [`tracelet_flow`] checks, and a
///   leg landing short of its recorded join is refused with the term it
///   reached. The empty leg reaches the skolemized peak and carries no labels;
///   a recorded identity keeps that term but adds its real incidences. A wrong
///   skolemization or no-op deletion changes the observer.
/// - witness: `tests::flow::a_leg_that_lands_off_the_join_has_no_certificate_flow`
/// - witness: `flow::tests::a_leg_that_does_not_fire_has_no_flow`
/// - witness: `flow::tests::empty_and_identity_legs_preserve_their_occurrences`
#[spec(ensures: |output| {
    let initial = A::skolemize(peak);
    let initial_count = A::command_positions(&initial).len();
    let replayed: Result<_, FlowObstruction<A>> = path.iter().try_fold((initial, Vec::<(usize, usize)>::new()), |(current, mut incidences), step| {
        match store.get(step.cell) {
            Maybe::Absent(_) => Err(FlowObstruction::UnknownCell { cell: step.cell }),
            Maybe::Present(cell) => match rewrite_at(cell, &current, &step.at) {
                Maybe::Absent(_) => Err(FlowObstruction::StepDoesNotFire { step: Box::new(step.clone()) }),
                Maybe::Present(next) => {
                    let upper = A::command_positions(&current).iter().filter(|position| bool::from(covered_by::<A>(&step.at, position))).count();
                    let lower = A::command_positions(&next).iter().filter(|position| bool::from(covered_by::<A>(&step.at, position))).count();
                    incidences.push((upper, lower));
                    Ok((next, incidences))
                },
            },
        }
    });
    replayed.map_or_else(|expected| matches!(output, Err(ref reason) if *reason == expected), |(reached, incidences)| {
        output.as_ref().is_ok_and(|result| {
            let flow = &result.0;
            let mut upper: Vec<FlowEnd> = flow.threads.iter().map(|thread| thread.up).collect();
            let mut lower: Vec<FlowEnd> = flow.threads.iter().map(|thread| thread.lo).collect();
            upper.sort_unstable(); lower.sort_unstable();
            let expected_upper = (0..initial_count).map(|occurrence| FlowEnd::Peak { occurrence: PeakOccurrenceIndex::from(occurrence) })
                .chain(incidences.iter().enumerate().flat_map(|(index, counts)| (0..counts.1).map(move |port| FlowEnd::Vertex { vertex: FlowVertexIndex::from(index), port: FlowPortIndex::from(port) })));
            let expected_lower = incidences.iter().enumerate().flat_map(|(index, counts)| (0..counts.0).map(move |port| FlowEnd::Vertex { vertex: FlowVertexIndex::from(index), port: FlowPortIndex::from(port) }))
                .chain(core::iter::repeat_n(FlowEnd::Join, A::command_positions(&reached).len()));
            result.1 == reached && flow.convexity == A::convexity_discharge(store)
                && flow.labels.iter().copied().eq(path.iter().filter_map(|step| match store.get(step.cell) { Maybe::Present(cell) => Some(cell_address(cell)), Maybe::Absent(_) => None }))
                && upper.into_iter().eq(expected_upper) && lower.into_iter().eq(expected_lower)
                && flow.threads.iter().all(|thread| match (thread.up, thread.lo) {
                    (FlowEnd::Vertex { vertex: up, .. }, FlowEnd::Vertex { vertex: lo, .. }) => up < lo,
                    _ => true,
                })
        })
    })
})]
fn project_walk<A>(
    store: &CellStore<A>,
    peak: &A::Cmd,
    path: &[CellApp<A>],
) -> Result<(Flow, A::Cmd), FlowObstruction<A>>
where
    A: CellAlphabet,
{
    let mut current = A::skolemize(peak);
    let mut live: Vec<LiveAtom<A>> = A::command_positions(&current)
        .into_iter()
        .enumerate()
        .map(|(index, at)| LiveAtom {
            birth: FlowEnd::Peak {
                occurrence: PeakOccurrenceIndex::from(index),
            },
            at,
        })
        .collect();
    let mut labels: Vec<CellAddress> = Vec::with_capacity(path.len());
    let mut threads: Vec<FlowThread> = Vec::new();
    for (index, step) in path.iter().enumerate() {
        let Maybe::Present(cell) = store.get(step.cell)
        else {
            return Err(FlowObstruction::UnknownCell { cell: step.cell });
        };
        let Maybe::Present(next) = rewrite_at(cell, &current, &step.at)
        else {
            return Err(FlowObstruction::StepDoesNotFire {
                step: Box::new(step.clone()),
            });
        };
        let vertex = FlowVertexIndex::from(index);
        labels.push(cell_address(cell));
        // Ports are numbered inside the match image, never across the whole
        // term, so a vertex's incidences are its own.
        let before_covered: Vec<A::Pos> = A::command_positions(&current)
            .into_iter()
            .filter(|position| bool::from(covered_by::<A>(&step.at, position)))
            .collect();
        let after_covered: Vec<A::Pos> = A::command_positions(&next)
            .into_iter()
            .filter(|position| bool::from(covered_by::<A>(&step.at, position)))
            .collect();
        // Upper edges: everything the match image covers is consumed.
        let mut surviving: Vec<LiveAtom<A>> = Vec::with_capacity(live.len());
        for atom in live {
            if !bool::from(covered_by::<A>(&step.at, &atom.at)) {
                surviving.push(atom);
                continue;
            }
            let port = before_covered
                .iter()
                .position(|candidate| *candidate == atom.at)
                .map_or_else(FlowPortIndex::default, FlowPortIndex::from);
            threads.push(FlowThread {
                up: atom.birth,
                lo: FlowEnd::Vertex { vertex, port },
            });
        }
        live = surviving;
        // Lower edges: everything the image covers afterwards is created.
        for (port, at) in after_covered.into_iter().enumerate() {
            live.push(LiveAtom {
                birth: FlowEnd::Vertex {
                    vertex,
                    port: FlowPortIndex::from(port),
                },
                at,
            });
        }
        current = next;
    }
    // The conclusion's own enumeration orders `⊥`'s edges, as the source's does.
    let final_positions = A::command_positions(&current);
    live.sort_by_key(|atom| {
        final_positions
            .iter()
            .position(|candidate| *candidate == atom.at)
    });
    for atom in live {
        threads.push(FlowThread {
            up: atom.birth,
            lo: FlowEnd::Join,
        });
    }
    Ok((
        Flow {
            labels,
            threads,
            convexity: A::convexity_discharge(store),
        },
        current,
    ))
}

/// Whether two flows are the same flow.
///
/// # Specification
/// - requires: both flows were projected by [`project_flow`], so their vertex
///   indices are in range and their boundaries are anchored in one vocabulary.
/// - ensures: positive exactly when both flows have a canonical form, the two
///   forms are equal, and both were taken under one convexity discharge.
/// - provides: the identification the projection licenses. A flow with no
///   canonical order answers negatively, so a negative means "not identified
///   here", never "distinct".
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the positive and negative surfaces are separated by the
///   permutation tile, whose two legs are identified, by the fused certificate,
///   whose two legs carry different label multisets, and by one empty flow
///   under two discharges.
/// - witness: `tests::flow::the_two_legs_of_a_permutation_tile_have_one_flow`
/// - witness: `tests::flow::flow_equality_is_strictly_finer_than_replay_equivalence`
/// - witness: `flow::tests::a_flow_taken_under_a_different_discharge_is_not_identified`
#[inline]
#[must_use]
#[spec(ensures: |output| bool::from(output) == (left.convexity == right.convexity && match (left.canonical(), right.canonical()) {
    (Maybe::Present(ref left), Maybe::Present(ref right)) => left == right,
    _ => false,
}))]
pub fn flows_equal(
    left: &Flow,
    right: &Flow,
) -> FlowEquality
{
    if left.convexity != right.convexity {
        return FlowEquality::from(false);
    }
    let (Maybe::Present(left), Maybe::Present(right)) = (left.canonical(), right.canonical())
    else {
        return FlowEquality::from(false);
    };
    FlowEquality::from(left == right)
}

/// Project a certificate to its boundary and its two legs' flows.
///
/// Both legs are projected from the shared peak and each must reach the
/// recorded join, so a [`TraceletFlow`] exists only for a certificate that
/// replays. That is what makes [`tracelets_flow_equal`] a subrelation of
/// replay-equivalence: replay-equivalence is equal peaks, equal joins and two
/// successful replays, and projecting establishes the last while the datum
/// carries the first two.
///
/// # Specification
/// - requires: the tracelet's paths are the legs recorded from its peak against
///   `store`.
/// - ensures: the certificate's recorded peak and join and each leg's flow,
///   only when both legs fire step by step from the skolemized peak and reach
///   the skolemized join, exactly when the certificate replays.
/// - provides: the certificate-level datum [`tracelets_flow_equal`] compares.
/// - fails: [`FlowObstruction`], from whichever leg is refused first, including
///   [`FlowObstruction::LegMissesTheJoin`] for a leg that fires throughout and
///   lands elsewhere.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — the reached-the-join requirement owns its own decision
///   surface, separated by a certificate that replays and one whose leg fires
///   completely and lands off the recorded join.
/// - witness: `tests::flow::a_certificate_has_its_own_flow`
/// - witness: `tests::flow::a_leg_that_lands_off_the_join_has_no_certificate_flow`
#[inline]
#[spec(ensures: |output| {
    let target = A::skolemize(&tracelet.joins_at);
    project_leg(store, &tracelet.overlap.peak, &target, &tracelet.path_a).map_or_else(|expected| matches!(output, Err(ref reason) if *reason == expected), |path_a| {
        project_leg(store, &tracelet.overlap.peak, &target, &tracelet.path_b).map_or_else(|expected| matches!(output, Err(ref reason) if *reason == expected), |path_b| {
            output.as_ref().is_ok_and(|projected| projected.peak == tracelet.overlap.peak && projected.joins_at == tracelet.joins_at && projected.path_a == path_a && projected.path_b == path_b)
        })
    })
})]
pub fn tracelet_flow<A>(
    tracelet: &Tracelet<A>,
    store: &CellStore<A>,
) -> Result<TraceletFlow<A>, FlowObstruction<A>>
where
    A: CellAlphabet,
{
    let target = A::skolemize(&tracelet.joins_at);
    let path_a = project_leg(store, &tracelet.overlap.peak, &target, &tracelet.path_a)?;
    let path_b = project_leg(store, &tracelet.overlap.peak, &target, &tracelet.path_b)?;
    Ok(TraceletFlow {
        peak: tracelet.overlap.peak.clone(),
        joins_at: tracelet.joins_at.clone(),
        path_a,
        path_b,
    })
}

/// Project one leg of a certificate, refusing it unless it reaches `target`.
///
/// # Specification
/// - requires: `target` is the skolemized recorded join.
/// - ensures: [`project_flow`]'s flow when the leg reaches `target`.
/// - fails: [`FlowObstruction::LegMissesTheJoin`] when it fires throughout and
///   lands elsewhere, or whatever [`project_flow`] refuses it for.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — a leg landing off the join is refused with the term it
///   reached.
/// - witness: `tests::flow::a_leg_that_lands_off_the_join_has_no_certificate_flow`
#[spec(ensures: |output| project_walk(store, peak, path).map_or_else(|expected| matches!(output, Err(ref reason) if *reason == expected), |(flow, reached)| {
    if reached == *target { output == Ok(flow) } else { matches!(output, Err(FlowObstruction::LegMissesTheJoin { reached: ref actual }) if **actual == reached) }
}))]
fn project_leg<A>(
    store: &CellStore<A>,
    peak: &A::Cmd,
    target: &A::Cmd,
    path: &[CellApp<A>],
) -> Result<Flow, FlowObstruction<A>>
where
    A: CellAlphabet,
{
    let (flow, reached) = project_walk(store, peak, path)?;
    if reached == *target {
        return Ok(flow);
    }
    Err(FlowObstruction::LegMissesTheJoin {
        reached: Box::new(reached),
    })
}

/// Whether a tracelet's two legs have one flow: the tile-internal reading.
///
/// On the permutation-tile class it decides the shift identification, which
/// [`derive_shift_equivalence`](crate::derive_shift_equivalence) confirms by
/// running both sequentializations and comparing the terms they reach.
///
/// # Specification
/// - requires: the tracelet's paths are the legs recorded from its peak.
/// - ensures: positive exactly when both legs project and their flows are
///   equal.
/// - fails: [`FlowObstruction`] when either leg is not a derivation of the
///   recorded boundary.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surface is one flow comparison, separated by
///   a certificate whose legs differ in length (unequal over a boundary that
///   replays) and by a duplicated tile whose legs have no canonical form.
/// - witness: `tests::flow::flow_equality_is_strictly_finer_than_replay_equivalence`
/// - witness: `tests::flow::the_games_quotient_identifies_a_tile_the_flow_declines_a_canonical_form`
/// - witness: `flow::tests::a_two_step_leg_and_a_one_step_leg_have_different_flows`
#[inline]
#[spec(ensures: |output| output == tracelet_flow(tracelet, store).map(|projected| flows_equal(&projected.path_a, &projected.path_b)))]
pub fn legs_flow_equal<A>(
    tracelet: &Tracelet<A>,
    store: &CellStore<A>,
) -> Result<FlowEquality, FlowObstruction<A>>
where
    A: CellAlphabet,
{
    let projected = tracelet_flow(tracelet, store)?;
    Ok(flows_equal(&projected.path_a, &projected.path_b))
}

/// Whether two tracelets are the same certificate under the projection: one
/// boundary, and one flow per leg.
///
/// The boundary is part of the comparison. Comparing flows alone answers
/// positively for two certificates that transform different peaks into
/// different joins by one combinatorial pattern, which replay-equivalence
/// separates.
///
/// # Specification
/// - requires: both tracelets' paths are the legs recorded from their own
///   peaks, and both are read against `store`.
/// - ensures: positive exactly when both certificates project, so both replay,
///   their peaks agree, their joins agree, and their two flows agree pairwise;
///   a positive answer therefore implies replay-equivalence.
/// - provides: the relation measured against replay-equivalence, strictly finer
///   than it. A negative means "not identified here", never "distinct".
/// - fails: [`FlowObstruction`] when either tracelet is not a pair of
///   derivations of its own recorded boundary.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L2 — the boundary conjunct and the flow conjunct own separate
///   decision surfaces, separated by a certificate against itself, by two
///   replay-equivalent certificates whose legs carry different flows, and by
///   two certificates whose flows are equal over different boundaries; the
///   implication into replay-equivalence is checked pairwise over every
///   certificate the suite builds.
/// - witness: `tests::flow::a_certificate_has_its_own_flow`
/// - witness: `tests::flow::replay_equivalent_certificates_can_carry_different_flows`
/// - witness: `tests::flow::equal_flows_over_different_boundaries_are_not_one_certificate`
/// - witness: `tests::flow::flow_equality_implies_replay_equivalence`
#[inline]
#[spec(ensures: |output| output == tracelet_flow(left, store).and_then(|left| tracelet_flow(right, store).map(|right| FlowEquality::from(left.peak == right.peak && left.joins_at == right.joins_at && bool::from(flows_equal(&left.path_a, &right.path_a)) && bool::from(flows_equal(&left.path_b, &right.path_b))))))]
pub fn tracelets_flow_equal<A>(
    left: &Tracelet<A>,
    right: &Tracelet<A>,
    store: &CellStore<A>,
) -> Result<FlowEquality, FlowObstruction<A>>
where
    A: CellAlphabet,
{
    let left = tracelet_flow(left, store)?;
    let right = tracelet_flow(right, store)?;
    if left.peak != right.peak || left.joins_at != right.joins_at {
        return Ok(FlowEquality::from(false));
    }
    let heads = flows_equal(&left.path_a, &right.path_a);
    let tails = flows_equal(&left.path_b, &right.path_b);
    Ok(FlowEquality::from(bool::from(heads) && bool::from(tails)))
}

#[cfg(test)]
mod tests
{
    use gandr_theory_cell_complexes::Cell;
    use gandr_theory_cell_complexes::CellProvenance;
    use gandr_theory_cell_complexes::CmdPat;
    use gandr_theory_cell_complexes::ConsPat;
    use gandr_theory_cell_complexes::Orientation;
    use gandr_theory_cell_complexes::Polarity;
    use gandr_theory_cell_complexes::Pos;
    use gandr_theory_cell_complexes::PositionStep;
    use gandr_theory_cell_complexes::ProdPat;
    use gandr_theory_cell_complexes::Sym;
    use gandr_theory_cell_complexes::frame_defining_cell;
    use gandr_theory_cell_complexes_tools::Toy;
    use gandr_theory_cell_complexes_tools::ToyAlphabet;
    use gandr_theory_cell_complexes_tools::toy_cell;
    use gandr_theory_coherent_resolutions::OverlapKind;
    use gandr_theory_coherent_resolutions::derive_fused;
    use gandr_theory_coherent_resolutions::enumerate_overlaps;

    use super::*;

    /// (add-S): `⟨Succ(m) | add(n; α)⟩ ~> ⟨m | add(n; Succ⁻(α))⟩`.
    ///
    /// # Specification
    /// trivial.
    fn add_s() -> Cell
    {
        let lhs = CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Succ", [ProdPat::meta("m")]),
            ConsPat::op("add", [ProdPat::meta("n")], ConsPat::meta("alpha")),
        );
        let rhs = CmdPat::cut(
            Polarity::Positive,
            ProdPat::meta("m"),
            ConsPat::op(
                "add",
                [ProdPat::meta("n")],
                ConsPat::frame("Succ", ConsPat::meta("alpha")),
            ),
        );
        Cell::new(
            lhs,
            rhs,
            Orientation::PolarityDerived,
            CellProvenance::SurfaceRule,
        )
    }

    #[test]
    fn the_cell_address_forgets_the_position()
    {
        let frame = frame_defining_cell(&Sym::new("Succ"));
        let other = frame_defining_cell(&Sym::new("Pred"));
        assert_eq!(
            cell_address(&frame),
            cell_address(&frame),
            "one cell's address is a function of its content"
        );
        assert_ne!(
            cell_address(&frame),
            cell_address(&other),
            "two cells with different content have different addresses"
        );
    }

    #[test]
    fn the_sequent_alphabet_gives_the_projection_one_occurrence_to_work_with()
    {
        // The projection is only as fine as the alphabet's address vocabulary.
        // A sequent command pattern has one command position, so the whole
        // term is one atom occurrence and every leg over it projects to a
        // chain through one thread per step, which is why the differential
        // suite runs on the toy alphabet.
        let mut store = CellStore::new();
        let frame = store.insert(frame_defining_cell(&Sym::new("Succ")));
        let term = CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Zero", []),
            ConsPat::frame("Succ", ConsPat::top()),
        );
        let flow = project_flow(&store, &term, &[CellApp {
            cell: frame,
            at: Pos::root(),
        }])
        .expect("the frame-defining cell fires at the root");
        assert_eq!(
            1_usize,
            flow.labels.len(),
            "one cell application, one vertex"
        );
        assert_eq!(
            2_usize,
            flow.threads.len(),
            "one occurrence consumed from the peak, one created and reaching the join"
        );
    }

    #[test]
    fn a_leg_that_does_not_fire_has_no_flow()
    {
        let mut store = CellStore::new();
        let frame = store.insert(frame_defining_cell(&Sym::new("Succ")));
        let term = CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Zero", []),
            ConsPat::top(),
        );
        let step = CellApp {
            cell: frame,
            at: Pos::root(),
        };
        assert_eq!(
            Err(FlowObstruction::StepDoesNotFire {
                step: Box::new(step.clone()),
            }),
            project_flow(&store, &term, &[step]),
            "a leg is a derivation or it is nothing"
        );
        let missing = CellId::from(97_usize);
        assert_eq!(
            Err(FlowObstruction::UnknownCell { cell: missing }),
            project_flow(&store, &term, &[CellApp {
                cell: missing,
                at: Pos::root(),
            }]),
            "and an unresolvable identifier is refused before the term is read"
        );
    }

    #[test]
    fn indistinguishable_vertices_are_refused_a_canonical_order()
    {
        // Two vertices at one depth, under one label, consuming nothing from
        // the peak: the key cannot tell them apart, so the flow is refused a
        // canonical order rather than given an arbitrary one.
        let label = cell_address(&frame_defining_cell(&Sym::new("Succ")));
        let flow = Flow {
            labels: alloc::vec![label, label],
            threads: alloc::vec![
                FlowThread {
                    up: FlowEnd::Vertex {
                        vertex: FlowVertexIndex::from(0_usize),
                        port: FlowPortIndex::default(),
                    },
                    lo: FlowEnd::Join,
                },
                FlowThread {
                    up: FlowEnd::Vertex {
                        vertex: FlowVertexIndex::from(1_usize),
                        port: FlowPortIndex::default(),
                    },
                    lo: FlowEnd::Join,
                },
            ],
            convexity: ConvexityDischarge::StronglyConnectedOverAcyclicTarget,
        };
        assert!(
            matches!(
                flow.canonical(),
                Maybe::Absent(flow_canonical::Absent::IndistinguishableVertices)
            ),
            "a tie in the key is refused, never broken arbitrarily"
        );
        assert!(
            !bool::from(flows_equal(&flow, &flow)),
            "and the refusal surfaces as a negative, the conservative direction"
        );
    }

    #[test]
    fn a_flow_taken_under_a_different_discharge_is_not_identified()
    {
        let empty = Flow {
            labels: Vec::new(),
            threads: Vec::new(),
            convexity: ConvexityDischarge::StronglyConnectedOverAcyclicTarget,
        };
        let rechecked = Flow {
            labels: Vec::new(),
            threads: Vec::new(),
            convexity: ConvexityDischarge::ReCheckRequired,
        };
        assert!(
            bool::from(flows_equal(&empty, &empty)),
            "one discharge identifies a flow with itself"
        );
        assert!(
            !bool::from(flows_equal(&empty, &rechecked)),
            "and the fence is part of the flow, so two discharges never identify"
        );
    }

    #[test]
    fn a_two_step_leg_and_a_one_step_leg_have_different_flows()
    {
        // The fused-certificate gap over the sequent alphabet: the two-step leg
        // has two vertices and the fused leg one, so no re-indexing makes the
        // label lists agree.
        let mut store = CellStore::new();
        let frame = store.insert(frame_defining_cell(&Sym::new("Succ")));
        let add = store.insert(add_s());
        let composition = enumerate_overlaps(&store)
            .into_iter()
            .find(|overlap| {
                overlap.kind == OverlapKind::Composition
                    && overlap.left == frame
                    && overlap.right == add
            })
            .expect("the composition overlap exists");
        let (_fused, tracelet) =
            derive_fused(&composition, &mut store).expect("the fused cell derives");
        let projected = tracelet_flow(&tracelet, &store).expect("both legs project");
        assert_eq!(2_usize, projected.path_a.labels.len(), "the two-step leg");
        assert_eq!(
            1_usize,
            projected.path_b.labels.len(),
            "the single fused step"
        );
        assert!(
            !bool::from(legs_flow_equal(&tracelet, &store).expect("both legs project")),
            "one boundary, two flows: the projection is strictly finer than the boundary"
        );
    }

    #[test]
    fn empty_and_identity_legs_preserve_their_occurrences()
    {
        let peak = Toy::add(Toy::var("x"), Toy::zero());
        let ground = ToyAlphabet::skolemize(&peak);
        let mut store = CellStore::new();
        let (empty, reached) =
            project_walk(&store, &peak, &[]).expect("the empty leg is a derivation");
        assert_eq!(ground, reached);
        assert!(empty.labels.is_empty());
        let boundary: Vec<FlowThread> = (0 .. 3_usize)
            .map(|index| FlowThread {
                up: FlowEnd::Peak {
                    occurrence: PeakOccurrenceIndex::from(index),
                },
                lo: FlowEnd::Join,
            })
            .collect();
        assert_eq!(boundary, empty.threads);
        let identity = store.insert(toy_cell(Toy::var("q"), Toy::var("q")));
        let (identity_flow, reached) = project_walk(&store, &peak, &[CellApp {
            cell: identity,
            at: ToyAlphabet::root_position(),
        }])
        .expect("the recorded identity fires");
        assert_eq!(ground, reached);
        assert_eq!(1_usize, identity_flow.labels.len());
        let expected: Vec<FlowThread> = (0 .. 3_usize)
            .map(|index| FlowThread {
                up: FlowEnd::Peak {
                    occurrence: PeakOccurrenceIndex::from(index),
                },
                lo: FlowEnd::Vertex {
                    vertex: FlowVertexIndex::from(0_usize),
                    port: FlowPortIndex::from(index),
                },
            })
            .chain((0 .. 3_usize).map(|index| FlowThread {
                up: FlowEnd::Vertex {
                    vertex: FlowVertexIndex::from(0_usize),
                    port: FlowPortIndex::from(index),
                },
                lo: FlowEnd::Join,
            }))
            .collect();
        assert_eq!(expected, identity_flow.threads);
        assert!(!bool::from(flows_equal(&empty, &identity_flow)));
    }

    #[test]
    fn canonical_reindexing_preserves_peak_anchors_and_ports()
    {
        let mut store = CellStore::new();
        let cell = store.insert(toy_cell(Toy::succ(Toy::zero()), Toy::zero()));
        let peak = Toy::add(Toy::succ(Toy::zero()), Toy::succ(Toy::zero()));
        let steps = [
            CellApp {
                cell,
                at: ToyAlphabet::position_at_path(&[PositionStep::from(1_usize)]),
            },
            CellApp {
                cell,
                at: ToyAlphabet::position_at_path(&[PositionStep::from(0_usize)]),
            },
        ];
        let flow = project_flow(&store, &peak, &steps).expect("the two reductions fire");
        let Maybe::Present(canonical) = flow.canonical()
        else {
            panic!("the peak anchors separate equal labels");
        };
        let peak_end = |occurrence| FlowEnd::Peak {
            occurrence: PeakOccurrenceIndex::from(occurrence),
        };
        let vertex_end = |vertex, port| FlowEnd::Vertex {
            vertex: FlowVertexIndex::from(vertex),
            port: FlowPortIndex::from(port),
        };
        let left_sites = [
            ToyAlphabet::position_at_path(&[PositionStep::from(0_usize)]),
            ToyAlphabet::position_at_path(&[
                PositionStep::from(0_usize),
                PositionStep::from(0_usize),
            ]),
        ];
        let right_sites = [
            ToyAlphabet::position_at_path(&[PositionStep::from(1_usize)]),
            ToyAlphabet::position_at_path(&[
                PositionStep::from(1_usize),
                PositionStep::from(0_usize),
            ]),
        ];
        let positions = ToyAlphabet::command_positions(&peak);
        let left_anchor = positions
            .iter()
            .position(|position| Some(position) == left_sites.first())
            .expect("the left redex is a peak occurrence");
        let right_anchor = positions
            .iter()
            .position(|position| Some(position) == right_sites.first())
            .expect("the right redex is a peak occurrence");
        let (left_rank, right_rank) = if left_anchor < right_anchor {
            (0_usize, 1_usize)
        }
        else {
            (1_usize, 0_usize)
        };
        let mut expected: Vec<FlowThread> = positions
            .iter()
            .enumerate()
            .map(|(index, position)| {
                let lo = if *position == ToyAlphabet::root_position() {
                    FlowEnd::Join
                }
                else if let Some(port) = left_sites.iter().position(|site| site == position) {
                    vertex_end(left_rank, port)
                }
                else if let Some(port) = right_sites.iter().position(|site| site == position) {
                    vertex_end(right_rank, port)
                }
                else {
                    panic!("the fixture contains only the frame and the two redexes");
                };
                FlowThread {
                    up: peak_end(index),
                    lo,
                }
            })
            .chain([
                FlowThread {
                    up: vertex_end(left_rank, 0_usize),
                    lo: FlowEnd::Join,
                },
                FlowThread {
                    up: vertex_end(right_rank, 0_usize),
                    lo: FlowEnd::Join,
                },
            ])
            .collect();
        expected.sort_unstable();
        assert_eq!(expected, canonical.threads);
        assert_eq!(flow.labels, canonical.labels);
        let outside = vertex_end(2_usize, 7_usize);
        assert_eq!(
            outside,
            reindex_end(outside, &[
                FlowVertexIndex::from(1_usize),
                FlowVertexIndex::from(0_usize)
            ])
        );
    }

    #[test]
    fn mixed_depth_creators_determine_the_maximum_layer()
    {
        let mut store = CellStore::new();
        let shrink = store.insert(toy_cell(Toy::succ(Toy::var("x")), Toy::var("x")));
        let collapse = store.insert(toy_cell(
            Toy::add(Toy::var("x"), Toy::var("y")),
            Toy::zero(),
        ));
        let peak = Toy::add(Toy::succ(Toy::zero()), Toy::succ(Toy::succ(Toy::zero())));
        let left = ToyAlphabet::position_at_path(&[PositionStep::from(0_usize)]);
        let right = ToyAlphabet::position_at_path(&[PositionStep::from(1_usize)]);
        let steps = [
            CellApp {
                cell: shrink,
                at: left,
            },
            CellApp {
                cell: shrink,
                at: right.clone(),
            },
            CellApp {
                cell: shrink,
                at: right,
            },
            CellApp {
                cell: collapse,
                at: ToyAlphabet::root_position(),
            },
        ];
        let flow = project_flow(&store, &peak, &steps)
            .expect("both branches reduce before the root consumes them");
        assert_eq!(
            [0_usize, 0_usize, 1_usize, 2_usize]
                .map(CausalDepth::from)
                .as_slice(),
            flow.causal_depths().as_slice()
        );
        let key = flow.vertex_key(
            FlowVertexIndex::from(1_usize),
            *flow
                .labels
                .get(1)
                .expect("the first right reduction has a label"),
            CausalDepth::from(0_usize),
        );
        assert_eq!(IncidenceCount::from(3_usize), key.upper);
        assert_eq!(IncidenceCount::from(2_usize), key.lower);
        let right_sites = [
            ToyAlphabet::position_at_path(&[PositionStep::from(1_usize)]),
            ToyAlphabet::position_at_path(&[
                PositionStep::from(1_usize),
                PositionStep::from(0_usize),
            ]),
            ToyAlphabet::position_at_path(&[
                PositionStep::from(1_usize),
                PositionStep::from(0_usize),
                PositionStep::from(0_usize),
            ]),
        ];
        let expected: Vec<PeakOccurrenceIndex> = ToyAlphabet::command_positions(&peak)
            .iter()
            .enumerate()
            .filter(|entry| right_sites.contains(entry.1))
            .map(|(index, _)| PeakOccurrenceIndex::from(index))
            .collect();
        assert_eq!(expected, key.from_peak);
    }
}
