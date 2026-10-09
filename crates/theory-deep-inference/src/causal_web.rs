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

use alloc::boxed::Box;
use alloc::vec::Vec;

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
    ///   relation is refused as malformed.
    /// - witness: `causal_web::tests::a_malformed_web_refuses_structural_comparison`
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
    ///   stack is materialized end to end.
    /// - witness: `causal_web::tests::a_tracelet_fixture_builds_the_two_colour_web`
    /// - witness: `causal_web::tests::a_dependent_pair_is_a_green_edge`
    /// - witness: `tests::causal_web::a_precedence_reached_only_through_an_intermediate_event_is_green`
    /// - witness: `tests::deep_derivation::a_deep_derivation_is_ordered_normalized_and_dropped_on_a_small_stack`
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
    /// - hypothesis: L2 — the one-event web's vertex reads back the key its
    ///   source order holds for its one canonical event.
    /// - witness: `causal_web::tests::a_single_event_is_the_boundary_web`
    #[inline]
    pub fn event(
        &self,
        vertex: WebVertex,
    ) -> Maybe<&EventKey, web_lookup::Absent>
    {
        match self.events.get(usize::from(vertex)) {
            | Some(key) => Maybe::Present(key),
            | None => Maybe::Absent(web_lookup::Absent::OutOfRange),
        }
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
    /// - hypothesis: L2 — the oracle is [`Self::relation`] on the same pair,
    ///   over an independent pair and a dependent one.
    /// - witness: `causal_web::tests::a_tracelet_fixture_builds_the_two_colour_web`
    /// - witness: `causal_web::tests::a_dependent_pair_is_a_green_edge`
    #[inline]
    #[must_use]
    pub fn independent(
        &self,
        left: WebVertex,
        right: WebVertex,
    ) -> WebIndependence
    {
        WebIndependence::from(self.relation(left, right) == WebRelation::Independent)
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
    ///   relation is refused as malformed.
    /// - witness: `causal_web::tests::a_malformed_web_refuses_structural_comparison`
    fn has_valid_shape(&self) -> WebShapeValidity
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
pub fn causal_web<A>(order: &EventOrder<A>) -> CausalWeb
where
    A: CellAlphabet,
{
    let canonical = order.canonical_order();
    let events: Vec<EventKey> = canonical
        .iter()
        .filter_map(|index| match order.key(*index) {
            | Maybe::Present(key) => Some(key),
            | Maybe::Absent(_) => None,
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
///   cardinality mismatch are each refused by their own name.
/// - witness: `causal_web::tests::an_equal_web_is_the_empty_slice_chain`
/// - witness: `causal_web::tests::an_independence_to_order_change_is_licensed`
/// - witness: `causal_web::tests::a_lost_precedence_is_a_negative_witness`
/// - witness: `causal_web::tests::a_malformed_web_refuses_structural_comparison`
/// - witness: `causal_web::tests::a_label_mismatch_refuses_edge_strengthening_simulation`
/// - witness: `causal_web::tests::a_cardinality_mismatch_refuses_open_h_down`
#[inline]
#[must_use]
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
                | (WebRelation::Precedes, WebRelation::Precedes)
                | (WebRelation::Follows, WebRelation::Follows)
                | (WebRelation::Independent, WebRelation::Independent) => {},
                | (WebRelation::Precedes, _) | (WebRelation::Independent, WebRelation::Missing) => {
                    return lost(left, right);
                },
                | (WebRelation::Follows, _) => return lost(right, left),
                | (WebRelation::Independent, WebRelation::Precedes) => {
                    steps.push(SliceStep {
                        earlier: left,
                        later: right,
                    });
                },
                | (WebRelation::Independent, WebRelation::Follows) => {
                    steps.push(SliceStep {
                        earlier: right,
                        later: left,
                    });
                },
                | (WebRelation::Missing, _) => {
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
    /// - panics: when the two steps do not replay, which is a fixture defect.
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
    /// - panics: when the step does not replay, which is a fixture defect.
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
    /// - panics: when the two steps do not replay, which is a fixture defect.
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
}
