//! The conflict-free, two-colour causal web over one tracelet leg.
//!
//! A [`CausalWeb`] is a read-only analysis of an existing [`EventOrder`]. Its
//! green relation is the order's transitive precedence; its white relation is
//! the complement on distinct vertices, the independence relation of the one
//! recorded run. A tracelet is one run, so no conflict colour is representable
//! here. The web is an analysis surface only: not an evaluator, a certificate
//! format, or a wire representation.
//!
//! [`refines`] decides the one refinement fragment that needs no vertex
//! correspondence: a finer web over the same labelled events that turns white
//! independence into green precedence, one pair at a time, the slice-chain
//! weakening of the logical-time graphs of Acclavio, Horne, Mauw and
//! Straßburger. Anything that would need a correspondence between different
//! events is refused by name rather than guessed.
//!
//! # The causal web and refinement
//!
//! `causal_web` moves one event order into its canonical coordinates as a
//! conflict-free two-colour web: green is the order's precedence, white its
//! complement on distinct events. It computes no second dependence relation; it
//! materializes the order's precedence by one pass in recorded order, folding
//! each direct dependence's finished ancestor row, latest dependence first and
//! skipping one already reached. A per-pair reachability search would cost a
//! search per ordered pair, which a long dependence chain makes quartic; the
//! fold makes a chain quadratic. `refines(finer, coarser)` decides one
//! fragment: two webs over the same labelled events, where `finer` keeps every
//! precedence of `coarser` and adds precedence only to pairs `coarser` leaves
//! independent. It answers `Refines` with the `SliceChain` naming each added
//! pair, `DoesNotRefine` with the first pair in canonical order whose required
//! relation is missing, and `Refused` with a named frontier for anything
//! needing a correspondence between different events: an equal-size label
//! mismatch, a size mismatch, or a malformed web. Over one fixed event set it
//! checks that an order respects a happens-before or that a schedule weakens
//! one. It offers no comparison across event sets, no conflict relation and
//! no persistence, and a web over n events holds n² bits.
//!
//! # Logical time
//!
//! A green edge is happens-before, and the slice rule reads a partial order
//! as the set of its linearizations. `DependenceBits::closure` builds the
//! green relation of a web whose events a caller supplies, from its direct
//! edges; `linearizes`, on that relation or on a [`CausalWeb`], admits a run
//! exactly when it names every event once and places each edge's source
//! first, and refuses one by the edge it inverts. A session's recorded
//! dialogue is the consumer: its events are the endpoints' moves, its edges
//! each endpoint's own order and each message's send before its receipt.

use alloc::boxed::Box;
use alloc::vec::Vec;

use anodized::spec;
use gandr_theory_cell_complexes::CellAlphabet;
use quenchant_shape::shape::Maybe;

use crate::boundary::EventIndex;
use crate::boundary::SliceStepCount;
use crate::boundary::WebIndependence;
use crate::boundary::WebPrecedence;
use crate::boundary::WebShapeValidity;
use crate::boundary::WebVertex;
use crate::boundary::WebVertexCount;
use crate::causal::EventKey;
use crate::causal::EventOrder;

quenchant_shape::reason_enum! {
    /// Why a causal web holds no event at a coordinate.
    pub mod web_lookup {
        /// The reason the lookup finds no event.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The coordinate is at or past the web's vertex count.
            OutOfRange,
        }
    }
}

/// Whether two web vertices carry a green directed edge or the white
/// independence relation.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum WebRelation
{
    /// `left` causally precedes `right`.
    Precedes,
    /// `right` causally precedes `left`.
    Follows,
    /// Neither vertex precedes the other in this conflict-free run.
    Independent,
    /// At least one coordinate names no web vertex, or the two coincide.
    Missing,
}

/// The transitive precedence relation of a causal web.
///
/// The rows are indexed by canonical [`WebVertex`] coordinates. Independence
/// is not stored as a second matrix: it is the white non-edge complement of
/// this relation on distinct, valid vertices.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DependenceBits
{
    /// A square, canonical-coordinate matrix of transitive precedence bits.
    rows: Box<[Box<[bool]>]>,
}

impl DependenceBits
{
    /// Whether the relation contains the directed edge `earlier → later`.
    ///
    /// # Specification
    /// - ensures: positive exactly when both coordinates are in range and the
    ///   bit at `(earlier, later)` is set; an out-of-range coordinate reads as
    ///   no edge.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an independent pair reads no edge either way, a
    ///   dependent pair reads its one direction, and an out-of-range coordinate
    ///   reads no edge.
    /// - witness: `causal_web::tests::a_tracelet_fixture_builds_the_two_colour_web`
    /// - witness: `causal_web::tests::a_dependent_pair_is_a_green_edge`
    #[inline]
    #[must_use]
    #[spec(ensures: |output| bool::from(output) == self.rows.get(usize::from(earlier)).and_then(|row| row.get(usize::from(later))).copied().unwrap_or(false))]
    pub fn contains(
        &self,
        earlier: WebVertex,
        later: WebVertex,
    ) -> WebPrecedence
    {
        let Some(row) = self.rows.get(usize::from(earlier))
        else {
            return WebPrecedence::from(false);
        };
        WebPrecedence::from(row.get(usize::from(later)).copied().unwrap_or(false))
    }

    /// The number of coordinates the relation represents.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a two-event order's relation has two coordinates.
    /// - witness: `causal_web::tests::the_precedence_relation_has_one_coordinate_per_event`
    #[inline]
    #[must_use]
    pub fn vertex_count(&self) -> WebVertexCount
    {
        WebVertexCount::from(self.rows.len())
    }

    /// Whether the relation is square for `count` vertices.
    ///
    /// # Specification
    /// - ensures: positive exactly when the relation has `count` rows and every
    ///   row has `count` columns.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a web whose event list was emptied under a two-vertex
    ///   relation is refused as malformed. A ragged relation with the correct
    ///   row count still fails; the empty square is valid. Ignoring any column
    ///   length changes the shape verdict.
    /// - witness: `causal_web::tests::a_malformed_web_refuses_structural_comparison`
    /// - witness: `causal_web::tests::empty_and_ragged_matrices_separate_shape_from_lookup`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body checks the same row lengths"
        )
    )]
    #[spec(ensures: |output| bool::from(output) == (self.rows.len() == usize::from(count) && self.rows.iter().all(|row| row.len() == usize::from(count))))]
    fn has_shape(
        &self,
        count: WebVertexCount,
    ) -> WebShapeValidity
    {
        let count = usize::from(count);
        WebShapeValidity::from(
            self.rows.len() == count && self.rows.iter().all(|row| row.len() == count),
        )
    }

    /// Materialize the order's precedence relation in canonical coordinates.
    ///
    /// Every dependence edge points to a strictly earlier event, so one pass
    /// in recorded order finds each direct dependence's ancestor row already
    /// finished and folds it in. Dependences are visited latest first, and one
    /// already reached through a later dependence is skipped: its row is
    /// contained in the row that reached it.
    ///
    /// # Specification
    /// - requires: `canonical` holds event indices of `order`.
    /// - ensures: each bit agrees with [`EventOrder::precedes`] on the two
    ///   indices its coordinates name.
    /// - panics: none.
    /// - intension: one fold of an ancestor row per direct dependence not
    ///   already reached, so a dependence chain costs a quadratic number of bit
    ///   operations rather than a search per pair.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an independent pair builds no edge, a dependent pair
    ///   builds its one direction, a precedence reached only through an
    ///   intermediate event is folded in, and a chain far longer than a small
    ///   stack is materialized end to end. The supplied coordinates may select,
    ///   repeat or reverse valid event indices. Omitting unselected ancestors
    ///   or assuming coordinate order changes the projected bits.
    /// - witness: `causal_web::tests::a_tracelet_fixture_builds_the_two_colour_web`
    /// - witness: `causal_web::tests::a_dependent_pair_is_a_green_edge`
    /// - witness: `tests::causal_web::a_precedence_reached_only_through_an_intermediate_event_is_green`
    /// - witness: `tests::deep_derivation::a_deep_derivation_is_ordered_normalized_and_dropped_on_a_small_stack`
    /// - witness: `causal_web::tests::precedence_projection_preserves_repeated_and_reversed_coordinates`
    #[spec(requires: canonical.iter().all(|index| usize::from(*index) < order.events().len()), ensures: |output|
        output.rows.len() == canonical.len() && (canonical.is_empty() || {
            let direct: Vec<&[EventIndex]> = (0..order.events().len()).map(|index| order.direct_dependences(EventIndex::from(index))).collect();
            output.rows.iter().zip(canonical).all(|(row, source)| {
                let mut reached = alloc::vec![false; order.events().len()];
                for later in usize::from(*source).saturating_add(1_usize)..order.events().len() {
                    let inherited = direct.get(later).copied().unwrap_or_default().iter().rev().any(|prior| prior == source || reached.get(usize::from(*prior)).copied().unwrap_or(false));
                    if let Some(slot) = reached.get_mut(later) { *slot = inherited; }
                }
                row.len() == canonical.len() && row.iter().zip(canonical).all(|(bit, target)| *bit == reached.get(usize::from(*target)).copied().unwrap_or(false))
            })
        }))]
    fn from_order<A>(
        order: &EventOrder<A>,
        canonical: &[EventIndex],
    ) -> Self
    where
        A: CellAlphabet,
    {
        let count = order.events().len();
        // `ancestors[later][earlier]`: `earlier` precedes `later`, in recorded
        // coordinates.
        let mut ancestors: Vec<Box<[bool]>> = Vec::with_capacity(count);
        for later in 0 .. count {
            let mut row = alloc::vec![false; count].into_boxed_slice();
            for earlier in order
                .direct_dependences(EventIndex::from(later))
                .iter()
                .rev()
            {
                let Some(reached) = row.get_mut(usize::from(*earlier))
                else {
                    continue;
                };
                if *reached {
                    continue;
                }
                *reached = true;
                if let Some(inherited) = ancestors.get(usize::from(*earlier)) {
                    for (bit, held) in row.iter_mut().zip(inherited.iter()) {
                        *bit |= *held;
                    }
                }
            }
            ancestors.push(row);
        }
        let rows: Vec<Box<[bool]>> = canonical
            .iter()
            .map(|left| {
                canonical
                    .iter()
                    .map(|right| {
                        ancestors
                            .get(usize::from(*right))
                            .and_then(|row| row.get(usize::from(*left)))
                            .copied()
                            .unwrap_or(false)
                    })
                    .collect()
            })
            .collect();
        Self {
            rows: rows.into_boxed_slice(),
        }
    }

    /// The transitive precedence `direct` generates over `count` vertices:
    /// the green relation of a web whose events a caller supplies, each
    /// direct edge `earlier → later` and every edge they compose to.
    ///
    /// # Specification
    /// - ensures: square over `count` vertices; it contains every direct edge
    ///   whose coordinates are in range, and an edge exactly when a path of
    ///   in-range direct edges joins its two vertices. A cycle sets a vertex's
    ///   own bit, and no run linearizes it.
    /// - panics: none.
    /// - intension: cubic in `count`, one row fold per intermediate vertex.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a two-edge chain closes to its composite, an
    ///   independent pair stays white, an out-of-range edge is dropped, and a
    ///   cycle leaves no linearization.
    /// - witness: `causal_web::tests::a_chain_of_direct_edges_closes_to_its_composite`
    /// - witness: `causal_web::tests::a_cycle_has_no_linearization`
    #[inline]
    #[must_use]
    #[spec(ensures: |output| bool::from(output.has_shape(count)) && direct.iter().all(|&(earlier, later)| usize::from(earlier) >= usize::from(count) || usize::from(later) >= usize::from(count) || bool::from(output.contains(earlier, later))))]
    pub fn closure(
        count: WebVertexCount,
        direct: &[(WebVertex, WebVertex)],
    ) -> Self
    {
        let count = usize::from(count);
        let mut bits = alloc::vec![false; count.saturating_mul(count)];
        for &(earlier, later) in direct {
            let (earlier, later) = (usize::from(earlier), usize::from(later));
            if earlier < count
                && later < count
                && let Some(bit) = bits.get_mut(earlier.saturating_mul(count).saturating_add(later))
            {
                *bit = true;
            }
        }
        // Warshall's closure: after the pass over `middle`, a bit is set
        // exactly when a path through intermediates at most `middle` joins
        // its two vertices.
        for middle in 0 .. count {
            for from in 0 .. count {
                let reaches = bits
                    .get(from.saturating_mul(count).saturating_add(middle))
                    .copied()
                    .unwrap_or(false);
                if !reaches {
                    continue;
                }
                for to in 0 .. count {
                    let onward = bits
                        .get(middle.saturating_mul(count).saturating_add(to))
                        .copied()
                        .unwrap_or(false);
                    if onward
                        && let Some(bit) =
                            bits.get_mut(from.saturating_mul(count).saturating_add(to))
                    {
                        *bit = true;
                    }
                }
            }
        }
        let rows: Vec<Box<[bool]>> = if count == 0 {
            Vec::new()
        }
        else {
            bits.chunks(count).map(Box::from).collect()
        };
        Self {
            rows: rows.into_boxed_slice(),
        }
    }

    /// Whether `run` is a linearization of the relation: every vertex once,
    /// and no vertex placed after one it precedes.
    ///
    /// # Specification
    /// - ensures: `Ok` exactly when `run` names every vertex of the relation
    ///   once and, for every edge `earlier → later`, places `earlier` first.
    /// - fails: [`LinearizationRefusal::Unknown`] for the first vertex past the
    ///   relation's count, [`LinearizationRefusal::Repeated`] for the first
    ///   named twice, [`LinearizationRefusal::Omitted`] for the least vertex
    ///   never named, and [`LinearizationRefusal::Inverted`] for the first
    ///   edge, in run order of its later-placed end, that the run places
    ///   backwards. A vertex only a direct edge to itself makes precede itself
    ///   is that edge, read once every pair is in order.
    /// - panics: none.
    ///
    /// # Errors
    /// As above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — both orders of an independent pair linearize; a
    ///   dependent pair placed backwards is refused with its edge; a short, a
    ///   repeating and an out-of-range run are each refused by name.
    /// - witness: `causal_web::tests::a_run_linearizes_the_web_it_respects`
    /// - witness: `causal_web::tests::a_run_that_is_not_one_ordering_of_the_web_is_refused_by_name`
    #[inline]
    #[spec(ensures: |output| output.is_err() || run.len() == self.rows.len())]
    pub fn linearizes(
        &self,
        run: &[WebVertex],
    ) -> Result<(), LinearizationRefusal>
    {
        let mut placed = alloc::vec![false; self.rows.len()];
        for &vertex in run {
            let Some(seen) = placed.get_mut(usize::from(vertex))
            else {
                return Err(LinearizationRefusal::Unknown { vertex });
            };
            if *seen {
                return Err(LinearizationRefusal::Repeated { vertex });
            }
            *seen = true;
        }
        for (index, seen) in placed.iter().enumerate() {
            if !*seen {
                return Err(LinearizationRefusal::Omitted {
                    vertex: WebVertex::from(index),
                });
            }
        }
        for (position, &vertex) in run.iter().enumerate() {
            for &before in run.get(.. position).unwrap_or_default() {
                if bool::from(self.contains(vertex, before)) {
                    return Err(LinearizationRefusal::Inverted {
                        earlier: vertex,
                        later: before,
                    });
                }
            }
        }
        for &vertex in run {
            if bool::from(self.contains(vertex, vertex)) {
                return Err(LinearizationRefusal::Inverted {
                    earlier: vertex,
                    later: vertex,
                });
            }
        }
        Ok(())
    }
}

/// Why a run is not one linearization of a web.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum LinearizationRefusal
{
    /// The run names a vertex past the web's count.
    Unknown
    {
        /// The vertex.
        vertex: WebVertex,
    },
    /// The run names a vertex a second time.
    Repeated
    {
        /// The vertex.
        vertex: WebVertex,
    },
    /// The run never names a vertex of the web.
    Omitted
    {
        /// The vertex.
        vertex: WebVertex,
    },
    /// The run places `later` before `earlier`, where the web's green edge
    /// runs `earlier → later`.
    Inverted
    {
        /// The edge's source, which the run places second.
        earlier: WebVertex,
        /// The edge's target, which the run places first.
        later: WebVertex,
    },
}

/// A causal web over the canonical events of one recorded tracelet leg.
///
/// Event labels are canonical [`EventKey`]s and `precedes` is the transitive
/// green relation. White independence is read through [`Self::relation`] or
/// [`Self::independent`]; there is no conflict relation, because one tracelet
/// is one conflict-free run. The fields are public so a caller can state a
/// candidate web to compare, and [`refines`] refuses one whose shape is not
/// square.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CausalWeb
{
    /// One vertex per event, ordered by the source order's canonical schedule.
    pub events: Box<[EventKey]>,
    /// The transitive precedence relation over [`Self::events`].
    pub precedes: DependenceBits,
}

impl CausalWeb
{
    /// The number of canonical event vertices.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn vertex_count(&self) -> WebVertexCount
    {
        WebVertexCount::from(self.events.len())
    }

    /// The canonical event key at `vertex`.
    ///
    /// # Specification
    /// - ensures: the key at `vertex` in the canonical event list.
    /// - provides: [`web_lookup::Absent::OutOfRange`] for a coordinate at or
    ///   past the vertex count.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a one-event web returns its source key at the valid
    ///   coordinate and a typed absence at the next coordinate. Shifting the
    ///   lookup or returning a key for absence changes this boundary.
    /// - witness: `causal_web::tests::a_single_event_is_the_boundary_web`
    #[inline]
    #[spec(ensures: |output| self.events.get(usize::from(vertex)).map_or_else(|| output == Maybe::Absent(web_lookup::Absent::OutOfRange), |key| output == Maybe::Present(key)))]
    pub fn event(
        &self,
        vertex: WebVertex,
    ) -> Maybe<&EventKey, web_lookup::Absent>
    {
        self.events.get(usize::from(vertex)).map_or(
            Maybe::Absent(web_lookup::Absent::OutOfRange),
            Maybe::Present,
        )
    }

    /// Read the two-colour relation between two web vertices.
    ///
    /// # Specification
    /// - ensures: [`WebRelation::Precedes`] or [`WebRelation::Follows`] for a
    ///   green edge in that direction, [`WebRelation::Independent`] for two
    ///   distinct vertices with no edge either way, and
    ///   [`WebRelation::Missing`] when a coordinate is out of range or the two
    ///   coincide.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every arm is separated: an independent pair in both
    ///   directions, a dependent pair in both directions, a vertex against
    ///   itself, and a coordinate past the end.
    /// - witness: `causal_web::tests::a_tracelet_fixture_builds_the_two_colour_web`
    /// - witness: `causal_web::tests::a_dependent_pair_is_a_green_edge`
    #[inline]
    #[must_use]
    #[spec(ensures: |output| output == if left == right || usize::from(left) >= self.events.len() || usize::from(right) >= self.events.len() {
    WebRelation::Missing
} else if bool::from(self.precedes.contains(left, right)) { WebRelation::Precedes }
else if bool::from(self.precedes.contains(right, left)) { WebRelation::Follows }
else { WebRelation::Independent })]
    pub fn relation(
        &self,
        left: WebVertex,
        right: WebVertex,
    ) -> WebRelation
    {
        let count = self.events.len();
        if usize::from(left) >= count || usize::from(right) >= count || left == right {
            return WebRelation::Missing;
        }
        if bool::from(self.precedes.contains(left, right)) {
            return WebRelation::Precedes;
        }
        if bool::from(self.precedes.contains(right, left)) {
            return WebRelation::Follows;
        }
        WebRelation::Independent
    }

    /// Whether two distinct vertices are in the white independence relation.
    ///
    /// # Specification
    /// - ensures: positive exactly when [`Self::relation`] reads
    ///   [`WebRelation::Independent`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct independent and dependent pairs, plus an
    ///   empty web, distinguish white edges from green edges and missing
    ///   vertices. Complementing precedence without rejecting missing vertices
    ///   changes the decision.
    /// - witness: `causal_web::tests::a_tracelet_fixture_builds_the_two_colour_web`
    /// - witness: `causal_web::tests::a_dependent_pair_is_a_green_edge`
    /// - witness: `causal_web::tests::empty_and_ragged_matrices_separate_shape_from_lookup`
    #[inline]
    #[must_use]
    #[spec(ensures: |output| bool::from(output) == (self.relation(left, right) == WebRelation::Independent))]
    pub fn independent(
        &self,
        left: WebVertex,
        right: WebVertex,
    ) -> WebIndependence
    {
        WebIndependence::from(self.relation(left, right) == WebRelation::Independent)
    }

    /// Whether `run`, a sequence of the web's vertices, is one of its
    /// linearizations: the slice rule's reading of a partial order as the set
    /// of its linear extensions.
    ///
    /// # Specification
    /// - ensures: as [`DependenceBits::linearizes`] over [`Self::precedes`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`DependenceBits::linearizes`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the canonical schedule of a dependent pair linearizes
    ///   its web and the reversed schedule is refused with the edge.
    /// - witness: `causal_web::tests::a_run_linearizes_the_web_it_respects`
    #[inline]
    #[spec(ensures: |output| output == self.precedes.linearizes(run))]
    pub fn linearizes(
        &self,
        run: &[WebVertex],
    ) -> Result<(), LinearizationRefusal>
    {
        self.precedes.linearizes(run)
    }

    /// Whether the event list and the precedence relation have one shape.
    ///
    /// # Specification
    /// - ensures: positive exactly for a square relation matching the event
    ///   list's length.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a web whose event list was emptied under a two-vertex
    ///   relation is refused as malformed. A short row with the correct event
    ///   count is also refused, whichever operand holds it; the empty web
    ///   remains a valid boundary.
    /// - witness: `causal_web::tests::a_malformed_web_refuses_structural_comparison`
    /// - witness: `causal_web::tests::empty_and_ragged_matrices_separate_shape_from_lookup`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body's `has_shape` checks the same row lengths"
        )
    )]
    #[spec(ensures: |output| bool::from(output) == (self.precedes.rows.len() == self.events.len() && self.precedes.rows.iter().all(|row| row.len() == self.events.len())))]
    pub(crate) fn has_valid_shape(&self) -> WebShapeValidity
    {
        self.precedes.has_shape(self.vertex_count())
    }
}

/// Build the causal web of one tracelet leg's event order.
///
/// The event order is the only source of event identity and of pairwise
/// independence. This computes no second dependence relation: it moves to the
/// canonical event list's coordinates and materializes the precedence the
/// order already decided.
///
/// # Specification
/// - requires: `order` was returned by this crate's causal or normal-form
///   constructors.
/// - ensures: the web holds exactly the order's canonical event keys, in
///   canonical order, and `precedes` agrees with [`EventOrder::precedes`] for
///   every event pair.
/// - provides: the conflict-free two-colour web [`refines`] compares.
/// - panics: none.
/// - intension: quadratic in the number of events for a dependence chain; in
///   general one fold of an event-wide row per direct dependence not already
///   reached through a later one.
///
/// # Adequacy
/// - hypothesis: L3 — pointwise over an independent pair, a dependent pair, a
///   one-event boundary order, a precedence reached only through an
///   intermediate event, and a chain far longer than a small stack.
/// - witness: `causal_web::tests::a_tracelet_fixture_builds_the_two_colour_web`
/// - witness: `causal_web::tests::a_dependent_pair_is_a_green_edge`
/// - witness: `causal_web::tests::a_single_event_is_the_boundary_web`
/// - witness: `tests::causal_web::a_precedence_reached_only_through_an_intermediate_event_is_green`
/// - witness: `tests::deep_derivation::a_deep_derivation_is_ordered_normalized_and_dropped_on_a_small_stack`
#[inline]
#[must_use]
#[spec(ensures: |output| {
    let canonical = order.canonical_order();
    output.events.len() == canonical.len() && output.events.iter().zip(&canonical).all(|(key, index)| order.key(*index) == Maybe::Present(*key))
        && output.precedes == DependenceBits::from_order(order, &canonical)
})]
pub fn causal_web<A>(order: &EventOrder<A>) -> CausalWeb
where
    A: CellAlphabet,
{
    let canonical = order.canonical_order();
    let events: Vec<EventKey> = canonical
        .iter()
        .filter_map(|index| match order.key(*index) {
            Maybe::Present(key) => Some(key),
            Maybe::Absent(_) => None,
        })
        .collect();
    CausalWeb {
        events: events.into_boxed_slice(),
        precedes: DependenceBits::from_order(order, &canonical),
    }
}

/// One licensed independence-to-order weakening in a slice chain.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct SliceStep
{
    /// The vertex that is earlier after the weakening.
    pub earlier: WebVertex,
    /// The vertex that is later after the weakening.
    pub later: WebVertex,
}

/// Evidence that a finer web is obtained from a coarser one by slice-chain
/// weakenings only.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SliceChain
{
    /// The weakenings, in canonical pair order.
    steps: Box<[SliceStep]>,
}

impl SliceChain
{
    /// The licensed independence-to-order steps, in canonical pair order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn steps(&self) -> &[SliceStep]
    {
        &self.steps
    }

    /// The number of licensed steps in the witness.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn step_count(&self) -> SliceStepCount
    {
        SliceStepCount::from(self.steps.len())
    }
}

/// The first pair that prevents a same-vertex-set slice-chain refinement.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct RefinementCounterexample
{
    /// The pair's earlier coordinate in the canonical web list.
    pub earlier: WebVertex,
    /// The pair's later coordinate in the canonical web list.
    pub later: WebVertex,
    /// The relation the coarser web requires.
    pub required: WebRelation,
    /// The relation the finer web supplies.
    pub observed: WebRelation,
}

/// The named frontier where [`refines`] declines to decide a general graph
/// simulation.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum HomomorphismFrontier
{
    /// A same-cardinality web needs an event correspondence the canonical
    /// event labels do not provide.
    EdgeStrengtheningSimulation,
    /// A different-cardinality web would need the open h↓ homomorphism rule,
    /// whose cut elimination is not established.
    OpenHDownHomomorphism,
    /// The public fields do not describe a square precedence relation.
    MalformedWeb,
}

/// The result of the slice-chain refinement check.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RefinementVerdict
{
    /// The finer web adds only precedence to pairs independent in the coarser
    /// web, with a witness for every added edge.
    Refines
    {
        /// The slice-chain witness.
        witness: SliceChain,
    },
    /// The same labelled vertices disagree with a precedence obligation.
    DoesNotRefine
    {
        /// The first separating pair in canonical order.
        witness: RefinementCounterexample,
    },
    /// The comparison leaves the identity-correspondence fragment and would
    /// need an undecided graph homomorphism.
    Refused
    {
        /// The named obstruction at the frontier.
        obstruction: HomomorphismFrontier,
    },
}

/// Decide the slice-chain refinement fragment.
///
/// `finer` may replace any white independence of `coarser` by one green
/// directed edge. Every precedence `coarser` already holds must stay oriented
/// the same way. The event labels and their number must agree, because
/// changing the vertex correspondence is the refused edge-strengthening
/// simulation and open h↓ homomorphism fragment.
///
/// # Specification
/// - ensures: [`RefinementVerdict::Refines`] exactly for the identity
///   correspondence whose only changes are independence-to-order weakenings,
///   with one [`SliceStep`] per weakening; [`RefinementVerdict::DoesNotRefine`]
///   with the first separating pair for a lost or reversed precedence; and a
///   named [`RefinementVerdict::Refused`] for a malformed web or a
///   correspondence outside the fragment.
/// - panics: none.
/// - intension: quadratic in the shared vertex count, with no replay.
///
/// # Adequacy
/// - hypothesis: L3 — pointwise over every verdict: an equal web is the empty
///   chain, one added edge is one licensed step, a lost edge is the separating
///   pair, and a malformed shape, an equal-cardinality label mismatch and a
///   cardinality mismatch are each refused by their own name. A reverse
///   weakening retains its direction, and a lost pair after a preserved pair
///   retains canonical scan priority. Missing a row-length check, reversing an
///   added edge or choosing a later counterexample changes the observer.
/// - witness: `causal_web::tests::an_equal_web_is_the_empty_slice_chain`
/// - witness: `causal_web::tests::an_independence_to_order_change_is_licensed`
/// - witness: `causal_web::tests::a_lost_precedence_is_a_negative_witness`
/// - witness: `causal_web::tests::a_malformed_web_refuses_structural_comparison`
/// - witness: `causal_web::tests::a_label_mismatch_refuses_edge_strengthening_simulation`
/// - witness: `causal_web::tests::a_cardinality_mismatch_refuses_open_h_down`
/// - witness: `causal_web::tests::reverse_weakening_and_first_losses_preserve_pair_order`
#[inline]
#[must_use]
#[spec(ensures: |output| {
    if !bool::from(finer.has_valid_shape()) || !bool::from(coarser.has_valid_shape()) {
        output == RefinementVerdict::Refused { obstruction: HomomorphismFrontier::MalformedWeb }
    } else if finer.events.len() != coarser.events.len() {
        output == RefinementVerdict::Refused { obstruction: HomomorphismFrontier::OpenHDownHomomorphism }
    } else if finer.events != coarser.events {
        output == RefinementVerdict::Refused { obstruction: HomomorphismFrontier::EdgeStrengtheningSimulation }
    } else {
        let pairs = (0_usize..finer.events.len()).flat_map(|left| (left.saturating_add(1_usize)..finer.events.len()).map(move |right| {
            let left = WebVertex::from(left); let right = WebVertex::from(right);
            (left, right, coarser.relation(left, right), finer.relation(left, right))
        }));
        let failed = pairs.clone().find(|pair| !matches!((pair.2, pair.3),
            (WebRelation::Precedes, WebRelation::Precedes) | (WebRelation::Follows, WebRelation::Follows)
            | (WebRelation::Independent, WebRelation::Independent | WebRelation::Precedes | WebRelation::Follows)));
        failed.map_or_else(|| {
            let steps = pairs.filter_map(|(left, right, required, observed)| match (required, observed) {
                (WebRelation::Independent, WebRelation::Precedes) => Some(SliceStep { earlier: left, later: right }),
                (WebRelation::Independent, WebRelation::Follows) => Some(SliceStep { earlier: right, later: left }),
                _ => None,
            });
            matches!(output, RefinementVerdict::Refines { ref witness } if witness.steps.iter().copied().eq(steps))
        }, |(left, right, required, observed)| {
            if required == WebRelation::Missing {
                output == RefinementVerdict::Refused { obstruction: HomomorphismFrontier::MalformedWeb }
            } else {
                let (earlier, later) = if required == WebRelation::Follows { (right, left) } else { (left, right) };
                matches!(output, RefinementVerdict::DoesNotRefine { ref witness } if witness.earlier == earlier && witness.later == later && witness.required == required && witness.observed == observed)
            }
        })
    }
})]
pub fn refines(
    finer: &CausalWeb,
    coarser: &CausalWeb,
) -> RefinementVerdict
{
    if !bool::from(finer.has_valid_shape()) || !bool::from(coarser.has_valid_shape()) {
        return RefinementVerdict::Refused {
            obstruction: HomomorphismFrontier::MalformedWeb,
        };
    }
    if finer.events.len() != coarser.events.len() {
        return RefinementVerdict::Refused {
            obstruction: HomomorphismFrontier::OpenHDownHomomorphism,
        };
    }
    if finer.events != coarser.events {
        return RefinementVerdict::Refused {
            obstruction: HomomorphismFrontier::EdgeStrengtheningSimulation,
        };
    }
    let count = finer.events.len();
    let mut steps = Vec::new();
    for left_index in 0_usize .. count {
        for right_index in left_index.saturating_add(1) .. count {
            let left = WebVertex::from(left_index);
            let right = WebVertex::from(right_index);
            let required = coarser.relation(left, right);
            let observed = finer.relation(left, right);
            let lost = |earlier: WebVertex, later: WebVertex| RefinementVerdict::DoesNotRefine {
                witness: RefinementCounterexample {
                    earlier,
                    later,
                    required,
                    observed,
                },
            };
            match (required, observed) {
                (WebRelation::Precedes, WebRelation::Precedes)
                | (WebRelation::Follows, WebRelation::Follows)
                | (WebRelation::Independent, WebRelation::Independent) => {},
                (WebRelation::Precedes, _) | (WebRelation::Independent, WebRelation::Missing) => {
                    return lost(left, right);
                },
                (WebRelation::Follows, _) => return lost(right, left),
                (WebRelation::Independent, WebRelation::Precedes) => {
                    steps.push(SliceStep {
                        earlier: left,
                        later: right,
                    });
                },
                (WebRelation::Independent, WebRelation::Follows) => {
                    steps.push(SliceStep {
                        earlier: right,
                        later: left,
                    });
                },
                (WebRelation::Missing, _) => {
                    return RefinementVerdict::Refused {
                        obstruction: HomomorphismFrontier::MalformedWeb,
                    };
                },
            }
        }
    }
    RefinementVerdict::Refines {
        witness: SliceChain {
            steps: steps.into_boxed_slice(),
        },
    }
}

#[cfg(test)]
mod tests
{
    use alloc::vec;

    use gandr_theory_cell_complexes::Cell;
    use gandr_theory_cell_complexes::CellStore;
    use gandr_theory_cell_complexes::PositionStep;
    use gandr_theory_cell_complexes_tools::Toy;
    use gandr_theory_cell_complexes_tools::ToyAlphabet;
    use gandr_theory_cell_complexes_tools::toy_cell;
    use gandr_theory_coherent_resolutions::CellApp;

    use super::*;
    use crate::normal_form::event_order;

    /// A toy position from child indices, read from the root outward.
    macro_rules! at {
        ($($step:expr),* $(,)?) => {
            <ToyAlphabet as CellAlphabet>::position_at_path(&[$({
                let step: usize = $step;
                PositionStep::from(step)
            }),*])
        };
    }

    /// The order of `cell` fired at both arguments of
    /// `Add(Succ(Zero), Succ(Zero))`: two events at incomparable positions.
    ///
    /// # Specification
    /// - requires: the supplied cell fires on and changes Succ(Zero).
    /// - ensures: two surviving events at the two child sites, carrying the
    ///   supplied cell’s primitive addresses.
    /// - panics: when the two steps do not replay, which is a fixture defect.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — cells that change the ground redex yield exactly two
    ///   surviving events at distinct child sites; their web separates
    ///   independence from changed labels. Dropping an event or substituting
    ///   the rule identity changes these observations.
    /// - witness: `causal_web::tests::a_tracelet_fixture_builds_the_two_colour_web`
    /// - witness: `causal_web::tests::a_label_mismatch_refuses_edge_strengthening_simulation`
    #[spec(requires: { let redex = Toy::succ(Toy::zero()); matches!(gandr_theory_coherent_resolutions::rewrite_at(&cell, &redex, &at![]), Maybe::Present(ref after) if *after != redex) }, captures: addresses = [crate::normal_form::prim_address(&cell, &at![0]), crate::normal_form::prim_address(&cell, &at![1])], ensures: |output| output.events().len() == 2 && output.events().iter().zip(addresses).enumerate().all(|(index, (event, address))| event.address() == address && event.step().at == ToyAlphabet::position_at_path(&[gandr_theory_cell_complexes::PositionStep::from(index)])))]
    fn two_event_order(cell: Cell<ToyAlphabet>) -> EventOrder<ToyAlphabet>
    {
        let mut store = CellStore::new();
        let cell = store.insert(cell);
        let peak = Toy::add(Toy::succ(Toy::zero()), Toy::succ(Toy::zero()));
        let path = vec![CellApp { cell, at: at![0] }, CellApp { cell, at: at![1] }];
        event_order(&store, &peak, &path).expect("the two-event fixture replays")
    }

    /// The order of `cell` fired once at the root of `Succ(Zero)`.
    ///
    /// # Specification
    /// - requires: the supplied cell fires on and changes Succ(Zero).
    /// - ensures: one surviving root event carrying the supplied cell’s
    ///   primitive address.
    /// - panics: when the step does not replay, which is a fixture defect.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a cell changing the ground root yields one event with
    ///   that cell’s address; the valid vertex and first missing vertex
    ///   separate lookup, cardinality and wrong-site mutations.
    /// - witness: `causal_web::tests::a_single_event_is_the_boundary_web`
    #[spec(requires: { let redex = Toy::succ(Toy::zero()); matches!(gandr_theory_coherent_resolutions::rewrite_at(&cell, &redex, &at![]), Maybe::Present(ref after) if *after != redex) }, captures: address = crate::normal_form::prim_address(&cell, &at![]), ensures: |output| output.events().len() == 1 && output.events().first().is_some_and(|event| event.address() == address && event.step().at == at![]))]
    fn one_event_order(cell: Cell<ToyAlphabet>) -> EventOrder<ToyAlphabet>
    {
        let mut store = CellStore::new();
        let cell = store.insert(cell);
        let peak = Toy::succ(Toy::zero());
        let path = vec![CellApp { cell, at: at![] }];
        event_order(&store, &peak, &path).expect("the one-event fixture replays")
    }

    /// The order of (add-Z) fired twice at the root of
    /// `Add(Zero, Add(Zero, Zero))`: the second step needs the first's result,
    /// so the two events are dependent.
    ///
    /// # Specification
    /// - ensures: two root events with the second directly dependent on the
    ///   first.
    /// - panics: when the two steps do not replay, which is a fixture defect.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the concrete two-root-step derivation yields one
    ///   forward precedence and no reverse precedence. Flattening the
    ///   dependency or reversing its direction changes the two-colour observer.
    /// - witness: `causal_web::tests::a_dependent_pair_is_a_green_edge`
    #[spec(ensures: |output| output.events().len() == 2 && output.events().iter().all(|event| event.step().at == at![]) && bool::from(output.depends_directly(EventIndex::from(1_usize), EventIndex::from(0_usize))))]
    fn dependent_order() -> EventOrder<ToyAlphabet>
    {
        let mut store = CellStore::new();
        let cell = store.insert(toy_cell(
            Toy::add(Toy::zero(), Toy::var("x")),
            Toy::var("x"),
        ));
        let peak = Toy::add(Toy::zero(), Toy::add(Toy::zero(), Toy::zero()));
        let path = vec![CellApp { cell, at: at![] }, CellApp { cell, at: at![] }];
        event_order(&store, &peak, &path).expect("the dependent two-event fixture replays")
    }

    /// (f): `Succ(Zero) ~> Zero`.
    ///
    /// # Specification
    /// trivial.
    fn f_cell() -> Cell<ToyAlphabet>
    {
        toy_cell(Toy::succ(Toy::zero()), Toy::zero())
    }

    /// `Succ(Zero) ~> Succ(Succ(Zero))`: the same redex as (f) with a
    /// different right-hand side, so its events carry different keys.
    ///
    /// # Specification
    /// trivial.
    fn alternate_cell() -> Cell<ToyAlphabet>
    {
        toy_cell(Toy::succ(Toy::zero()), Toy::succ(Toy::succ(Toy::zero())))
    }

    #[test]
    fn a_tracelet_fixture_builds_the_two_colour_web()
    {
        let order = two_event_order(f_cell());
        let web = causal_web(&order);
        let left = WebVertex::from(0_usize);
        let right = WebVertex::from(1_usize);
        assert_eq!(WebVertexCount::from(2_usize), web.vertex_count());
        assert_eq!(WebRelation::Independent, web.relation(left, right));
        assert_eq!(WebRelation::Independent, web.relation(right, left));
        assert!(bool::from(web.independent(left, right)));
        assert_eq!(WebRelation::Missing, web.relation(left, left));
        assert_eq!(
            WebRelation::Missing,
            web.relation(left, WebVertex::from(2_usize))
        );
        assert!(!bool::from(
            web.precedes.contains(left, WebVertex::from(2_usize))
        ));
        assert_eq!(2_usize, web.events.len());
    }

    #[test]
    fn a_dependent_pair_is_a_green_edge()
    {
        let order = dependent_order();
        let web = causal_web(&order);
        let left = WebVertex::from(0_usize);
        let right = WebVertex::from(1_usize);
        assert_eq!(WebVertexCount::from(2_usize), web.vertex_count());
        assert_eq!(WebRelation::Precedes, web.relation(left, right));
        assert_eq!(WebRelation::Follows, web.relation(right, left));
        assert!(!bool::from(web.independent(left, right)));
    }

    #[test]
    fn a_run_linearizes_the_web_it_respects()
    {
        let left = WebVertex::from(0_usize);
        let right = WebVertex::from(1_usize);
        let independent = causal_web(&two_event_order(f_cell()));
        assert_eq!(Ok(()), independent.linearizes(&[left, right]));
        assert_eq!(Ok(()), independent.linearizes(&[right, left]));
        let dependent = causal_web(&dependent_order());
        assert_eq!(Ok(()), dependent.linearizes(&[left, right]));
        assert_eq!(
            Err(LinearizationRefusal::Inverted {
                earlier: left,
                later: right,
            }),
            dependent.linearizes(&[right, left])
        );
    }

    #[test]
    fn a_run_that_is_not_one_ordering_of_the_web_is_refused_by_name()
    {
        let web = causal_web(&two_event_order(f_cell()));
        let left = WebVertex::from(0_usize);
        let right = WebVertex::from(1_usize);
        let past = WebVertex::from(2_usize);
        assert_eq!(
            Err(LinearizationRefusal::Omitted { vertex: right }),
            web.linearizes(&[left])
        );
        assert_eq!(
            Err(LinearizationRefusal::Repeated { vertex: left }),
            web.linearizes(&[left, left, right])
        );
        assert_eq!(
            Err(LinearizationRefusal::Unknown { vertex: past }),
            web.linearizes(&[left, past, right])
        );
    }

    #[test]
    fn a_chain_of_direct_edges_closes_to_its_composite()
    {
        let [first, second, third, apart] = [0_usize, 1, 2, 3].map(WebVertex::from);
        let bits = DependenceBits::closure(WebVertexCount::from(4_usize), &[
            (first, second),
            (second, third),
            (third, WebVertex::from(9_usize)),
        ]);
        assert!(bool::from(bits.has_shape(WebVertexCount::from(4_usize))));
        assert!(bool::from(bits.contains(first, third)));
        assert!(!bool::from(bits.contains(third, first)));
        assert!(!bool::from(bits.contains(first, apart)));
        assert!(!bool::from(bits.contains(apart, first)));
        assert_eq!(Ok(()), bits.linearizes(&[apart, first, second, third]));
        assert_eq!(Ok(()), bits.linearizes(&[first, apart, second, third]));
        assert_eq!(
            Err(LinearizationRefusal::Inverted {
                earlier: first,
                later: third,
            }),
            bits.linearizes(&[third, first, second, apart])
        );
    }

    #[test]
    fn a_cycle_has_no_linearization()
    {
        let [first, second] = [0_usize, 1].map(WebVertex::from);
        let bits = DependenceBits::closure(WebVertexCount::from(2_usize), &[
            (first, second),
            (second, first),
        ]);
        assert!(bool::from(bits.contains(first, first)));
        assert_eq!(
            Err(LinearizationRefusal::Inverted {
                earlier: second,
                later: first,
            }),
            bits.linearizes(&[first, second])
        );
        assert_eq!(
            Err(LinearizationRefusal::Inverted {
                earlier: first,
                later: second,
            }),
            bits.linearizes(&[second, first])
        );
        let alone = WebVertex::from(0_usize);
        let looped = DependenceBits::closure(WebVertexCount::from(1_usize), &[(alone, alone)]);
        assert_eq!(
            Err(LinearizationRefusal::Inverted {
                earlier: alone,
                later: alone,
            }),
            looped.linearizes(&[alone])
        );
    }

    #[test]
    fn the_precedence_relation_has_one_coordinate_per_event()
    {
        let web = causal_web(&dependent_order());
        assert_eq!(WebVertexCount::from(2_usize), web.precedes.vertex_count());
    }

    #[test]
    fn a_single_event_is_the_boundary_web()
    {
        let order = one_event_order(f_cell());
        let web = causal_web(&order);
        let Maybe::Present(key) = order.key(order.canonical_order()[0])
        else {
            panic!("the one-event order holds its event");
        };
        assert_eq!(Maybe::Present(&key), web.event(WebVertex::from(0_usize)));
        assert_eq!(
            Maybe::Absent(web_lookup::Absent::OutOfRange),
            web.event(WebVertex::from(1_usize))
        );
    }

    #[test]
    fn an_equal_web_is_the_empty_slice_chain()
    {
        let web = causal_web(&two_event_order(f_cell()));
        let RefinementVerdict::Refines { witness } = refines(&web, &web)
        else {
            panic!("an identical web is the boundary refinement");
        };
        assert_eq!(SliceStepCount::from(0_usize), witness.step_count());
    }

    #[test]
    fn an_independence_to_order_change_is_licensed()
    {
        let coarser = causal_web(&two_event_order(f_cell()));
        let mut precedes = coarser.precedes.clone();
        precedes.rows[0][1] = true;
        let finer = CausalWeb {
            events: coarser.events.clone(),
            precedes,
        };
        let RefinementVerdict::Refines { witness } = refines(&finer, &coarser)
        else {
            panic!("an independence-to-order change is the slice fragment");
        };
        assert_eq!(SliceStepCount::from(1_usize), witness.step_count());
        assert_eq!(
            Some(&SliceStep {
                earlier: WebVertex::from(0_usize),
                later: WebVertex::from(1_usize),
            }),
            witness.steps().first(),
        );
    }

    #[test]
    fn a_lost_precedence_is_a_negative_witness()
    {
        let independent = causal_web(&two_event_order(f_cell()));
        let mut coarser_precedes = independent.precedes.clone();
        coarser_precedes.rows[0][1] = true;
        let coarser = CausalWeb {
            events: independent.events.clone(),
            precedes: coarser_precedes,
        };
        let RefinementVerdict::DoesNotRefine { witness } = refines(&independent, &coarser)
        else {
            panic!("a lost precedence must remain a negative verdict");
        };
        assert_eq!(WebVertex::from(0_usize), witness.earlier);
        assert_eq!(WebVertex::from(1_usize), witness.later);
        assert_eq!(WebRelation::Precedes, witness.required);
        assert_eq!(WebRelation::Independent, witness.observed);
    }

    #[test]
    fn a_label_mismatch_refuses_edge_strengthening_simulation()
    {
        let coarser = causal_web(&two_event_order(f_cell()));
        let finer = causal_web(&two_event_order(alternate_cell()));
        assert_eq!(
            RefinementVerdict::Refused {
                obstruction: HomomorphismFrontier::EdgeStrengtheningSimulation,
            },
            refines(&finer, &coarser),
        );
    }

    #[test]
    fn a_cardinality_mismatch_refuses_open_h_down()
    {
        let finer = causal_web(&one_event_order(f_cell()));
        let coarser = causal_web(&two_event_order(f_cell()));
        assert_eq!(
            RefinementVerdict::Refused {
                obstruction: HomomorphismFrontier::OpenHDownHomomorphism,
            },
            refines(&finer, &coarser),
        );
    }

    #[test]
    fn a_malformed_web_refuses_structural_comparison()
    {
        let source = causal_web(&two_event_order(f_cell()));
        let malformed = CausalWeb {
            events: Box::default(),
            precedes: source.precedes.clone(),
        };
        assert_eq!(
            RefinementVerdict::Refused {
                obstruction: HomomorphismFrontier::MalformedWeb,
            },
            refines(&malformed, &source),
        );
    }

    #[test]
    fn empty_and_ragged_matrices_separate_shape_from_lookup()
    {
        let order = EventOrder::<ToyAlphabet>::of_events(
            &CellStore::new(),
            Vec::new(),
            gandr_theory_cell_complexes::ConvexityDischarge::StronglyConnectedOverAcyclicTarget,
        );
        let empty = causal_web(&order);
        assert_eq!(WebVertexCount::from(0_usize), empty.vertex_count());
        assert!(bool::from(empty.has_valid_shape()));
        assert_eq!(
            WebRelation::Missing,
            empty.relation(WebVertex::from(0_usize), WebVertex::from(1_usize))
        );
        assert!(!bool::from(empty.independent(
            WebVertex::from(0_usize),
            WebVertex::from(1_usize)
        )));
        let RefinementVerdict::Refines { witness } = refines(&empty, &empty)
        else {
            panic!("the empty web refines itself");
        };
        assert!(witness.steps().is_empty());
        let source = causal_web(&two_event_order(f_cell()));
        let ragged = DependenceBits {
            rows: vec![
                vec![false].into_boxed_slice(),
                vec![true, false].into_boxed_slice(),
            ]
            .into_boxed_slice(),
        };
        assert!(!bool::from(ragged.has_shape(WebVertexCount::from(2_usize))));
        assert!(bool::from(
            ragged.contains(WebVertex::from(1_usize), WebVertex::from(0_usize))
        ));
        assert!(!bool::from(
            ragged.contains(WebVertex::from(0_usize), WebVertex::from(1_usize))
        ));
        assert!(!bool::from(
            ragged.contains(WebVertex::from(2_usize), WebVertex::from(0_usize))
        ));
        let malformed = CausalWeb {
            events: source.events.clone(),
            precedes: ragged,
        };
        assert_eq!(
            RefinementVerdict::Refused {
                obstruction: HomomorphismFrontier::MalformedWeb
            },
            refines(&malformed, &source)
        );
        assert_eq!(
            RefinementVerdict::Refused {
                obstruction: HomomorphismFrontier::MalformedWeb
            },
            refines(&source, &malformed)
        );
    }

    #[test]
    fn precedence_projection_preserves_repeated_and_reversed_coordinates()
    {
        let mut store = CellStore::new();
        let cell = store.insert(toy_cell(Toy::succ(Toy::var("x")), Toy::var("x")));
        let peak = Toy::succ(Toy::succ(Toy::succ(Toy::zero())));
        let step = CellApp { cell, at: at![] };
        let order = event_order(&store, &peak, &[step.clone(), step.clone(), step])
            .expect("the three root reductions fire");
        let projected = DependenceBits::from_order(&order, &[
            EventIndex::from(2_usize),
            EventIndex::from(0_usize),
            EventIndex::from(2_usize),
        ]);
        assert_eq!(
            vec![
                vec![false, false, false].into_boxed_slice(),
                vec![true, false, true].into_boxed_slice(),
                vec![false, false, false].into_boxed_slice()
            ]
            .into_boxed_slice(),
            projected.rows
        );
        assert!(DependenceBits::from_order(&order, &[]).rows.is_empty());
    }

    #[test]
    fn reverse_weakening_and_first_losses_preserve_pair_order()
    {
        let coarser = causal_web(&two_event_order(f_cell()));
        let mut reversed = coarser.clone();
        reversed.precedes.rows[1][0] = true;
        let RefinementVerdict::Refines { witness } = refines(&reversed, &coarser)
        else {
            panic!("a reverse white-to-green edge is licensed");
        };
        assert_eq!(
            &[SliceStep {
                earlier: WebVertex::from(1_usize),
                later: WebVertex::from(0_usize)
            }],
            witness.steps()
        );
        let mut store = CellStore::new();
        let cell = store.insert(f_cell());
        let redex = Toy::succ(Toy::zero());
        let peak = Toy::add(redex.clone(), Toy::add(redex.clone(), redex));
        let path = [
            CellApp { cell, at: at![0] },
            CellApp {
                cell,
                at: at![1, 0],
            },
            CellApp {
                cell,
                at: at![1, 1],
            },
        ];
        let order =
            event_order(&store, &peak, &path).expect("the three independent reductions fire");
        let mut required = causal_web(&order);
        let mut supplied = required.clone();
        *required
            .precedes
            .rows
            .get_mut(0)
            .expect("first vertex")
            .get_mut(2)
            .expect("third coordinate") = true;
        *required
            .precedes
            .rows
            .get_mut(1)
            .expect("second vertex")
            .get_mut(2)
            .expect("third coordinate") = true;
        *supplied
            .precedes
            .rows
            .get_mut(1)
            .expect("second vertex")
            .get_mut(2)
            .expect("third coordinate") = true;
        assert_eq!(
            RefinementVerdict::DoesNotRefine {
                witness: RefinementCounterexample {
                    earlier: WebVertex::from(0_usize),
                    later: WebVertex::from(2_usize),
                    required: WebRelation::Precedes,
                    observed: WebRelation::Independent
                }
            },
            refines(&supplied, &required)
        );
    }
}
