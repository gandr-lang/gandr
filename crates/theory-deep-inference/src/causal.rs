//! The finite event partial order of a recorded derivation: the causal
//! structure the tracelet normal form quotients by, kept as data.
//!
//! A derivation that has survived unit elimination is a finite sequence of
//! events, one cell application each, in the order they were recorded. Two
//! events are dependent when the crate's single independence relation (the
//! shift guard) refuses to commute them, and the causal order is the
//! transitive closure of "earlier in the recording and dependent". That order
//! is a strict partial order on a finite set, the dependence order of a
//! Mazurkiewicz trace, and the object the canonical schedule is a linear
//! extension of.
//!
//! # Why this is a type
//!
//! The normal form needs one linear extension of this order, and a schedule
//! says which order to fire in but not which steps could have fired together.
//! A parallel replay plan, a critical-path cost and a rendering of a
//! derivation as a poset all need that structure, so the order is built once,
//! as [`EventOrder`], and the normal form's schedule is one of its projections
//! ([`EventOrder::canonical_order`]) beside the layer grouping
//! ([`EventOrder::layers`]).
//!
//! # What this module does not decide
//!
//! It does not decide certificate identity. Everything here reads the recorded
//! steps of one derivation, while the semantic oracle,
//! [`replay_equivalent`](gandr_theory_coherent_resolutions::replay_equivalent),
//! reads only the boundary and whether the paths replay. The event order is a
//! presentation of one derivation, and two presentations of one certificate
//! may differ.
//!
//! # The independence relation is asked, never restated
//!
//! [`step_independence_with_support`] delegates to
//! [`check_shift_guard_with_support`] and reads any refusal as dependence,
//! the conservative direction: refusing to commute keeps the recorded order,
//! which is always a valid derivation. The relation is symmetric, a fact about
//! the guard rather than an assumption here: its first conjunct answers
//! [`PositionOrder::Incomparable`](gandr_theory_cell_complexes::PositionOrder::Incomparable)
//! for a pair exactly when it does for the swap, its second asks the overlap
//! enumerator in both ordered directions, and its third does not read the
//! pair.
//!
//! # The premise no conjunct checks
//!
//! Independence is sound only if the alphabet's term algebra is local: a
//! rewrite at one position leaves every incomparable position alone
//! ([`CellAlphabet::splice_cmd_at`]'s own clause). Two applications can
//! satisfy every conjunct honestly and still fail to commute if that clause is
//! broken. Nothing in this module can see that failure; the normal form's
//! replay of the schedule this order induces catches it.

use alloc::vec::Vec;

use gandr_theory_cell_complexes::CellAlphabet;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::ConvexityDischarge;
use gandr_theory_cell_complexes::SequentAlphabet;
use gandr_theory_coherent_resolutions::CellApp;
use gandr_theory_coherent_resolutions::OverlapSupport;
use gandr_theory_coherent_resolutions::StepIndependence;
use quenchant_shape::shape::Maybe;

use crate::boundary::CausalDepth;
use crate::boundary::EventConcurrency;
use crate::boundary::EventCount;
use crate::boundary::EventDependence;
use crate::boundary::EventIndex;
use crate::boundary::EventPrecedence;
use crate::boundary::SchedulePosition;
use crate::boundary::TranspositionCount;
use crate::normal_form::CausalPast;
use crate::normal_form::PrimId;
use crate::normal_form::causal_past_address;
use crate::shift::check_shift_guard_with_support;

quenchant_shape::reason_enum! {
    /// Why an event order holds nothing at an index.
    pub mod event_lookup {
        /// The reason the lookup finds no event.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The index is past the last event of the order.
            OutOfRange,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why an exchange witness does not apply to a sequentialization.
    pub mod exchange_application {
        /// The reason the witness's transpositions cannot be performed.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// A transposition names a position the sequentialization does not
            /// hold, so it was not the one the witness was built from.
            PositionOutOfRange,
        }
    }
}

/// One event of a recorded derivation: a step that moved the term, with the
/// content address of the primitive it applies.
///
/// It is distinct from a [`CellApp`] because the two are read differently: a
/// [`CellApp`] is a step of a path, which may be a unit and whose place is the
/// recorded one, while an event is a node of a partial order, never a unit and
/// placed by the order rather than by the recording.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct DerivationEvent<A: CellAlphabet = SequentAlphabet>
{
    /// The step this event fires, as recorded.
    step: CellApp<A>,
    /// The content address of the primitive it applies.
    address: PrimId,
}

impl<A: CellAlphabet> DerivationEvent<A>
{
    /// An event from a surviving step and its content address.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        step: CellApp<A>,
        address: PrimId,
    ) -> Self
    {
        Self { step, address }
    }

    /// The step this event fires.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn step(&self) -> &CellApp<A>
    {
        &self.step
    }

    /// The content address of the primitive this event applies.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn address(&self) -> PrimId
    {
        self.address
    }
}

/// The finite event partial order of one recorded derivation.
///
/// The events are held in recorded order; the order proper is the transitive
/// closure of the direct dependence edges, and [`EventOrder::depth`] is the
/// layering induced by it. A value is a presentation of one derivation, not a
/// certificate: it says nothing about the boundary and cannot say whether the
/// derivation replays. The normal form's replay witness carries both.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EventOrder<A: CellAlphabet = SequentAlphabet>
{
    /// The events, in recorded order.
    events: Vec<DerivationEvent<A>>,
    /// For each event, the strictly earlier events it depends on directly.
    dependences: Vec<Vec<EventIndex>>,
    /// For each event, its layer in the dependence order.
    depths: Vec<CausalDepth>,
    /// For each event, its intrinsic sort key.
    keys: Vec<EventKey>,
    /// The warrant the independence relation's convexity conjunct was decided
    /// under, carried rather than recomputed.
    convexity: ConvexityDischarge,
}

/// The intrinsic key of an event: the content-derived value that orders two
/// events sharing a causal depth.
///
/// It is the primitive's content address refined by a digest of the event's
/// labeled causal past, compared in that order. The refinement matters because
/// the address alone is not injective: [`core::hash::Hash`] never promises
/// injectivity, so an alphabet may legally give two applications at different
/// sites one address, and where those two sit over different causes the past
/// digest separates them.
///
/// Neither component reads arrival order or a store-local index. The address
/// digests the resolved cell's content and the position, never the
/// [`CellId`](gandr_theory_cell_complexes::CellId) the cell was interned
/// under; the past digest folds over the sorted predecessor digests, so it
/// cannot see which linear extension was recorded. The key is therefore a
/// function of the labeled causal order, and so is the canonical order.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct EventKey
{
    /// The content address of the primitive the event applies.
    address: PrimId,
    /// The digest of the event's labeled causal past.
    past: CausalPast,
}

impl EventKey
{
    /// The content address of the primitive the event applies.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn address(&self) -> PrimId
    {
        self.address
    }

    /// The digest of the event's labeled causal past.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn past(&self) -> CausalPast
    {
        self.past
    }
}

/// Two distinct events that tie on the canonical sort key.
///
/// A tie means the canonical order is not determined by the labeled causal
/// order: the sort would fall back on its own stability and so on the arrival
/// order, which would make the normal form depend on which sequentialization
/// was recorded. Refusing is the conservative direction, the one the normal
/// form takes for a content-address collision.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct KeyCollision
{
    /// The earlier of the two tying events, in recorded order.
    pub earlier: EventIndex,
    /// The later of them.
    pub later: EventIndex,
    /// The depth both sit at.
    pub depth: CausalDepth,
    /// The key both carry.
    pub key: EventKey,
}

/// Why an exchange between two sequentializations was refused.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ExchangeObstruction
{
    /// The target order is not a rearrangement of the source order: they
    /// differ in length, or one holds an event the other does not.
    NotARearrangement,
    /// The exchange kill signal: reaching the target order requires
    /// transposing a pair the independence relation calls dependent.
    ///
    /// Two sequentializations related only by such a swap are not in one trace
    /// class, so identifying them would be unsound. A caller asking for the
    /// canonical order and receiving this has a canonical key that is not a
    /// linear extension of the causal order.
    DependentTransposition
    {
        /// The event that sits earlier in the sequence being transposed.
        earlier: EventIndex,
        /// The event that sits later in it.
        later: EventIndex,
    },
}

/// One licensed adjacent transposition of a sequentialization: the swap of
/// the events at `position` and the position after it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Transposition
{
    /// The lower of the two positions swapped.
    position: SchedulePosition,
}

impl Transposition
{
    /// The lower of the two positions this transposition swaps.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn position(&self) -> SchedulePosition
    {
        self.position
    }
}

/// The exchange witness carrying one sequentialization of a derivation to
/// another: the adjacent transpositions that do it, each one licensed.
///
/// It is the evidence behind "these two orders are the same trace". Every
/// transposition it holds was checked against the crate's single independence
/// relation at construction, so performing the witness is a rearrangement no
/// dependence edge objects to.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct ExchangeWitness
{
    /// The transpositions, in the order they are performed.
    transpositions: Vec<Transposition>,
}

impl ExchangeWitness
{
    /// The transpositions, in the order they are performed.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn transpositions(&self) -> &[Transposition]
    {
        &self.transpositions
    }

    /// How many transpositions this witness performs.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn transposition_count(&self) -> TranspositionCount
    {
        TranspositionCount::from(self.transpositions.len())
    }

    /// Perform the witness's transpositions on `order`.
    ///
    /// This is what makes the witness checkable rather than recorded: a caller
    /// performs it and compares, instead of trusting that it describes the
    /// rearrangement it claims.
    ///
    /// # Specification
    /// - requires: `order` is the sequentialization the witness was built from.
    /// - ensures: `order` with every transposition applied in turn.
    /// - provides: [`exchange_application::Absent::PositionOutOfRange`] when a
    ///   transposition names a position `order` does not hold, which
    ///   [`EventOrder::exchange_between`] cannot produce for the order it was
    ///   given.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the result is checked against an independent answer
    ///   rather than a predicted one: the witness is applied to the recorded
    ///   order and compared with the canonical order the same [`EventOrder`]
    ///   computed separately.
    /// - witness: `causal::tests::the_exchange_witness_carries_the_recorded_order_to_the_canonical_one`
    /// - witness: `tests::normal_form::an_exchange_witness_replays_to_its_target_order`
    #[inline]
    pub fn apply(
        &self,
        order: &[EventIndex],
    ) -> Maybe<Vec<EventIndex>, exchange_application::Absent>
    {
        let mut current = order.to_vec();
        for transposition in &self.transpositions {
            let below = usize::from(transposition.position);
            let above = below.saturating_add(1_usize);
            if above >= current.len() {
                return Maybe::Absent(exchange_application::Absent::PositionOutOfRange);
            }
            current.swap(below, above);
        }
        Maybe::Present(current)
    }
}

impl<A: CellAlphabet> EventOrder<A>
{
    /// Build the event order of a derivation's surviving steps.
    ///
    /// # Specification
    /// - requires: `events` are the steps of one recorded derivation that moved
    ///   the term, in recorded order, addressed against `store`.
    /// - ensures: event `i` depends directly on every strictly earlier event
    ///   the independence relation refuses to commute it with, and takes the
    ///   depth one more than the deepest of those, or zero when there are none.
    /// - provides: the causal structure the shift quotient quotients by,
    ///   decided through the crate's single independence relation.
    /// - panics: none.
    /// - intension: quadratic in the number of events, one logarithmic support
    ///   lookup per ordered pair after one store-wide support build.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the depth recurrence needs three layers to bite: its
    ///   two residues, the maximum over every earlier dependence against the
    ///   nearest or first one, and the one added to the prior depth, are not
    ///   separated by a two-layer derivation. A depth read off the earlier
    ///   step's position index instead of its depth is still a valid layering
    ///   and survives every single-chain fixture; two interleaved chains
    ///   recorded in two orders separate it.
    /// - witness: `tests::normal_form::the_dependence_edges_are_the_pairs_the_guard_refuses`
    /// - witness: `tests::normal_form::a_three_layer_derivation_gives_three_layers`
    /// - witness: `tests::normal_form::a_layered_derivation_keeps_its_dependent_step_last`
    /// - witness: `tests::normal_form::a_three_layer_derivation_orders_each_layer_by_content_address`
    /// - witness: `tests::normal_form::two_interleaved_dependence_chains_layer_by_depth_and_not_by_position`
    #[inline]
    #[must_use]
    pub fn of_events(
        store: &CellStore<A>,
        events: Vec<DerivationEvent<A>>,
        convexity: ConvexityDischarge,
    ) -> Self
    {
        let support = OverlapSupport::from_store(store);
        let mut dependences: Vec<Vec<EventIndex>> = Vec::with_capacity(events.len());
        let mut depths: Vec<CausalDepth> = Vec::with_capacity(events.len());
        let mut keys: Vec<EventKey> = Vec::with_capacity(events.len());
        for (index, current) in events.iter().enumerate() {
            let mut edges: Vec<EventIndex> = Vec::new();
            let mut depth = CausalDepth::default();
            for (earlier, prior) in events.iter().enumerate().take(index) {
                if bool::from(step_independence_with_support(
                    store,
                    &prior.step,
                    &current.step,
                    convexity,
                    &support,
                )) {
                    continue;
                }
                edges.push(EventIndex::from(earlier));
                let prior_depth = depths.get(earlier).copied().unwrap_or_default();
                let above = CausalDepth::from(usize::from(prior_depth).saturating_add(1_usize));
                depth = depth.max(above);
            }
            let inherited: Vec<CausalPast> = edges
                .iter()
                .map(|earlier| {
                    keys.get(usize::from(*earlier))
                        .map(EventKey::past)
                        .unwrap_or_default()
                })
                .collect();
            keys.push(EventKey {
                address: current.address,
                past: causal_past_address(current.address, &inherited),
            });
            dependences.push(edges);
            depths.push(depth);
        }
        Self {
            events,
            dependences,
            depths,
            keys,
            convexity,
        }
    }

    /// The events, in recorded order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn events(&self) -> &[DerivationEvent<A>]
    {
        &self.events
    }

    /// How many events the derivation has, after unit elimination.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn event_count(&self) -> EventCount
    {
        EventCount::from(self.events.len())
    }

    /// The event at `at`.
    ///
    /// # Specification
    /// - ensures: the event recorded at `at`.
    /// - provides: [`event_lookup::Absent::OutOfRange`] when the index names no
    ///   event.
    /// - panics: none.
    #[inline]
    pub fn event(
        &self,
        at: EventIndex,
    ) -> Maybe<&DerivationEvent<A>, event_lookup::Absent>
    {
        match self.events.get(usize::from(at)) {
            | Some(event) => Maybe::Present(event),
            | None => Maybe::Absent(event_lookup::Absent::OutOfRange),
        }
    }

    /// The layer of the event at `at`.
    ///
    /// # Specification
    /// - ensures: the depth of the event recorded at `at`.
    /// - provides: [`event_lookup::Absent::OutOfRange`] when the index names no
    ///   event.
    /// - panics: none.
    #[inline]
    pub fn depth(
        &self,
        at: EventIndex,
    ) -> Maybe<CausalDepth, event_lookup::Absent>
    {
        match self.depths.get(usize::from(at)) {
            | Some(depth) => Maybe::Present(*depth),
            | None => Maybe::Absent(event_lookup::Absent::OutOfRange),
        }
    }

    /// The intrinsic sort key of the event at `at`.
    ///
    /// # Specification
    /// - ensures: the key of the event recorded at `at`.
    /// - provides: [`event_lookup::Absent::OutOfRange`] when the index names no
    ///   event.
    /// - panics: none.
    #[inline]
    pub fn key(
        &self,
        at: EventIndex,
    ) -> Maybe<EventKey, event_lookup::Absent>
    {
        match self.keys.get(usize::from(at)) {
            | Some(key) => Maybe::Present(*key),
            | None => Maybe::Absent(event_lookup::Absent::OutOfRange),
        }
    }

    /// Refuse this order if two distinct events tie on the canonical sort key.
    ///
    /// # Specification
    /// - ensures: success exactly when `(depth, key)` is a strict total order
    ///   on the events, which makes [`EventOrder::canonical_order`] a function
    ///   of the labeled causal order rather than of the recorded one.
    /// - provides: the enforcement of the injectivity the canonical order
    ///   claims: both public constructors of an order run it before returning
    ///   one.
    /// - fails: [`KeyCollision`], naming both events, the depth they share and
    ///   the key they share.
    /// - panics: none.
    /// - intension: one pass over the canonical order, because a tie in a
    ///   sorted sequence is between neighbours.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the neighbour comparison is separated by an order
    ///   whose keys are distinct, one whose two events share a key at one
    ///   depth, and one whose two events share a key at different depths, which
    ///   is not a tie and must pass since every repeated primitive produces it.
    ///   The tying inputs are assembled directly: over both shipped alphabets a
    ///   shared address forces a shared position and so distinct depths, which
    ///   is a fact about those alphabets rather than evidence the check is
    ///   redundant.
    /// - witness: `causal::tests::an_order_whose_keys_are_distinct_is_accepted`
    /// - witness: `causal::tests::two_events_tying_on_depth_and_key_are_refused`
    /// - witness: `causal::tests::a_repeated_primitive_at_two_depths_is_not_a_tie`
    #[inline]
    pub(crate) fn refuse_key_collisions(&self) -> Result<(), KeyCollision>
    {
        let mut held: Option<(EventIndex, CausalDepth, EventKey)> = None;
        for index in self.canonical_order() {
            let (Maybe::Present(depth), Maybe::Present(key)) = (self.depth(index), self.key(index))
            else {
                continue;
            };
            if let Some((previous, previous_depth, previous_key)) = held
                && previous_depth == depth
                && previous_key == key
            {
                return Err(KeyCollision {
                    earlier: previous.min(index),
                    later: previous.max(index),
                    depth,
                    key,
                });
            }
            held = Some((index, depth, key));
        }
        Ok(())
    }

    /// The warrant this order's independence relation was decided under.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn convexity(&self) -> ConvexityDischarge
    {
        self.convexity
    }

    /// Whether `later` depends directly on `earlier`.
    ///
    /// Direct dependence is not transitive: `x` may depend on `y` and `y` on
    /// `z` with `x` and `z` independent. The transitive relation is
    /// [`EventOrder::precedes`].
    ///
    /// # Specification
    /// - ensures: positive exactly when `earlier` is strictly earlier in the
    ///   recording than `later` and the independence relation refuses the pair;
    ///   negative for an index naming no event.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — membership in one event's edge list is separated by a
    ///   dependent pair, an independent pair, the same pair asked backwards,
    ///   and an out-of-range index.
    /// - witness: `tests::normal_form::the_dependence_edges_are_the_pairs_the_guard_refuses`
    /// - witness: `causal::tests::an_out_of_range_index_depends_on_nothing`
    #[inline]
    #[must_use]
    pub fn depends_directly(
        &self,
        later: EventIndex,
        earlier: EventIndex,
    ) -> EventDependence
    {
        let Some(edges) = self.dependences.get(usize::from(later))
        else {
            return EventDependence::from(false);
        };
        EventDependence::from(edges.contains(&earlier))
    }

    /// The events `later` depends on directly, ascending in recorded order.
    ///
    /// # Specification
    /// - ensures: exactly the indices [`EventOrder::depends_directly`] answers
    ///   positive for against `later`, ascending; empty for an index naming no
    ///   event.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the causal web materializes precedence from these
    ///   edges alone and is checked against [`EventOrder::precedes`] pair by
    ///   pair, over a precedence reached only through an intermediate event, so
    ///   a missing or extra edge fails.
    /// - witness: `causal_web::tests::a_tracelet_fixture_builds_the_two_colour_web`
    /// - witness: `tests::causal_web::a_precedence_reached_only_through_an_intermediate_event_is_green`
    pub(crate) fn direct_dependences(
        &self,
        later: EventIndex,
    ) -> &[EventIndex]
    {
        self.dependences
            .get(usize::from(later))
            .map_or(&[], Vec::as_slice)
    }

    /// Whether two events are licensed to commute.
    ///
    /// This is the symmetric complement of direct dependence, and the relation
    /// an exchange consults: an adjacent transposition is licensed exactly when
    /// the pair it swaps is independent.
    ///
    /// # Specification
    /// - ensures: positive exactly when the two indices name distinct events
    ///   the independence relation licenses; the answer does not depend on the
    ///   argument order.
    /// - ensures: negative for an event against itself and for an index naming
    ///   no event, the conservative direction: reading an absent event as
    ///   commuting freely would license a transposition nothing decided.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the complement, the reflexive case and the range
    ///   guard are separated by an independent pair asked both ways, a
    ///   dependent pair, one event against itself and an index outside the
    ///   order.
    /// - witness: `causal::tests::an_event_is_never_independent_of_itself`
    /// - witness: `causal::tests::an_out_of_range_index_depends_on_nothing`
    /// - witness: `tests::normal_form::independence_is_symmetric_and_irreflexive`
    #[inline]
    #[must_use]
    pub fn independent(
        &self,
        left: EventIndex,
        right: EventIndex,
    ) -> StepIndependence
    {
        let count = EventIndex::from(self.events.len());
        if left == right || left >= count || right >= count {
            return StepIndependence::from(false);
        }
        let (earlier, later) = if left < right {
            (left, right)
        }
        else {
            (right, left)
        };
        StepIndependence::from(!bool::from(self.depends_directly(later, earlier)))
    }

    /// Whether `earlier` causally precedes `later`: the strict partial order
    /// proper.
    ///
    /// # Specification
    /// - ensures: positive exactly when `later` reaches `earlier` along one or
    ///   more direct dependence edges; irreflexive, asymmetric and transitive,
    ///   because every edge points from a strictly later recorded index to a
    ///   strictly earlier one.
    /// - provides: the finite partial order the canonical schedule is a linear
    ///   extension of.
    /// - panics: none.
    /// - intension: an iterative sweep over an explicit worklist, bounded by
    ///   the number of edges.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — reachability rather than adjacency is separated by a
    ///   chain asked forwards and backwards; L2 — the order laws are asserted
    ///   over generated derivations, because a relation wrong on a shape no
    ///   fixture has passes every pointwise test.
    /// - witness: `causal::tests::precedence_is_the_transitive_closure_of_dependence`
    /// - witness: `tests::normal_form::causal_precedence_is_a_strict_partial_order`
    #[inline]
    #[must_use]
    pub fn precedes(
        &self,
        earlier: EventIndex,
        later: EventIndex,
    ) -> EventPrecedence
    {
        if earlier == later {
            return EventPrecedence::from(false);
        }
        let Some(seeds) = self.dependences.get(usize::from(later))
        else {
            return EventPrecedence::from(false);
        };
        let mut visited: Vec<bool> = alloc::vec![false; self.events.len()];
        let mut frontier: Vec<EventIndex> = seeds.clone();
        while let Some(index) = frontier.pop() {
            if index == earlier {
                return EventPrecedence::from(true);
            }
            let Some(seen) = visited.get_mut(usize::from(index))
            else {
                continue;
            };
            if *seen {
                continue;
            }
            *seen = true;
            if let Some(next) = self.dependences.get(usize::from(index)) {
                frontier.extend_from_slice(next);
            }
        }
        EventPrecedence::from(false)
    }

    /// Whether two distinct events are causally unordered: neither precedes
    /// the other.
    ///
    /// Concurrency is coarser than independence: two independent events are
    /// always concurrent, but two events can be concurrent while one depends
    /// on something the other does not touch.
    ///
    /// # Specification
    /// - ensures: positive exactly when the two indices name distinct events
    ///   with no precedence either way; the answer does not depend on the
    ///   argument order; negative for an index naming no event.
    /// - provides: the "could have fired together" relation a parallel replay
    ///   plan reads, which a flattened schedule cannot express.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the two precedence questions and the reflexive case
    ///   are separated by a dependent pair, an independent pair and one event
    ///   against itself; L2 — events sharing a depth are pairwise concurrent
    ///   over generated derivations.
    /// - witness: `causal::tests::an_event_is_never_concurrent_with_itself`
    /// - witness: `causal::tests::an_out_of_range_index_depends_on_nothing`
    /// - witness: `tests::normal_form::events_sharing_a_layer_are_pairwise_concurrent`
    #[inline]
    #[must_use]
    pub fn concurrent(
        &self,
        left: EventIndex,
        right: EventIndex,
    ) -> EventConcurrency
    {
        let count = EventIndex::from(self.events.len());
        if left == right || left >= count || right >= count {
            return EventConcurrency::from(false);
        }
        let forwards = bool::from(self.precedes(left, right));
        let backwards = bool::from(self.precedes(right, left));
        EventConcurrency::from(!forwards && !backwards)
    }

    /// The events in recorded order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn recorded_order(&self) -> Vec<EventIndex>
    {
        (0 .. self.events.len()).map(EventIndex::from).collect()
    }

    /// The events in canonical order: the causal layering, flattened.
    ///
    /// The canonical schedule is the earliest causal position of every event,
    /// and its invariant has four clauses, each checked rather than asserted:
    ///
    /// 1. The order is the lexicographic sort by `(causal depth, event key)`.
    /// 2. Depth is the length of the longest dependence chain strictly below
    ///    the event under the transitive closure of dependence. The recurrence
    ///    at [`EventOrder::of_events`] computes it over the direct edges, which
    ///    is the same number: the closure of a finite acyclic relation adds
    ///    only shortcuts, and a shortcut is never longer than the chain it
    ///    skips.
    /// 3. The key is content-derived, total, injective over the events of one
    ///    derivation, and independent of arrival order and of store-local
    ///    indices. [`EventKey`] carries all but injectivity by construction;
    ///    injectivity is enforced by [`EventOrder::refuse_key_collisions`],
    ///    which every public constructor runs.
    /// 4. The result depends only on the labeled causal partial order:
    ///    transposing an adjacent independent pair in the recorded derivation
    ///    leaves it unchanged.
    ///
    /// # Specification
    /// - ensures: the recorded order sorted by `(depth, key)`; the sort is
    ///   stable, and its stability is unobservable on an order that has passed
    ///   [`EventOrder::refuse_key_collisions`].
    /// - provides: the linear extension of the causal order the normal form's
    ///   schedule is built from: a canonical representative of the shift class,
    ///   determined by the labeled causal order alone.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the key's components are separated independently: the
    ///   depth by a layered derivation whose dependent step must stay last, the
    ///   address by a two-occupant layer whose ascending order is observable,
    ///   and the causal past by two events sharing an address over different
    ///   causes; L2 — the depth agrees with the longest chain under the closure
    ///   and every adjacent independent transposition leaves the order fixed,
    ///   over generated derivations.
    /// - witness: `tests::normal_form::a_three_layer_derivation_orders_each_layer_by_content_address`
    /// - witness: `tests::normal_form::the_canonical_key_never_ties`
    /// - witness: `tests::normal_form::the_depth_is_the_longest_chain_strictly_below`
    /// - witness: `tests::normal_form::every_adjacent_independent_transposition_leaves_the_canonical_order_fixed`
    /// - witness: `tests::normal_form::the_canonical_order_is_the_same_in_two_differently_ordered_stores`
    /// - witness: `causal::tests::the_causal_past_separates_two_events_sharing_an_address`
    #[inline]
    #[must_use]
    pub fn canonical_order(&self) -> Vec<EventIndex>
    {
        let mut order = self.recorded_order();
        order.sort_by(|left, right| {
            let left_rank = (
                self.depths.get(usize::from(*left)),
                self.keys.get(usize::from(*left)),
            );
            let right_rank = (
                self.depths.get(usize::from(*right)),
                self.keys.get(usize::from(*right)),
            );
            left_rank.cmp(&right_rank)
        });
        order
    }

    /// The layers of the causal order: the events grouped by depth, each layer
    /// in ascending key order.
    ///
    /// Every event in one layer is concurrent with every other in it, so a
    /// layer is a batch that could fire together, and the number of layers is
    /// the derivation's causal critical path.
    ///
    /// # Specification
    /// - ensures: a partition of every event into consecutive groups of equal
    ///   depth, in ascending depth order, whose concatenation is
    ///   [`EventOrder::canonical_order`].
    /// - provides: the parallel batches a replay plan schedules and the
    ///   critical-path length a cost model reads.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the group boundary is separated by a three-layer
    ///   derivation with a two-occupant first layer and singleton layers after
    ///   it; L2 — the concatenation and the antichain property over generated
    ///   derivations.
    /// - witness: `tests::normal_form::a_three_layer_derivation_gives_three_layers`
    /// - witness: `tests::normal_form::the_layers_concatenate_to_the_canonical_order`
    /// - witness: `tests::normal_form::events_sharing_a_layer_are_pairwise_concurrent`
    #[inline]
    #[must_use]
    pub fn layers(&self) -> Vec<Vec<EventIndex>>
    {
        let mut layers: Vec<Vec<EventIndex>> = Vec::new();
        let mut current: Vec<EventIndex> = Vec::new();
        let mut held: Option<CausalDepth> = None;
        for index in self.canonical_order() {
            let depth = self
                .depths
                .get(usize::from(index))
                .copied()
                .unwrap_or_default();
            if held != Some(depth) {
                if !current.is_empty() {
                    layers.push(core::mem::take(&mut current));
                }
                held = Some(depth);
            }
            current.push(index);
        }
        if !current.is_empty() {
            layers.push(current);
        }
        layers
    }

    /// The exchange witness carrying `from` to `to`, or the refusal that says
    /// they are not one trace.
    ///
    /// The decision procedure for "are these two sequentializations of one
    /// derivation shift-equivalent", answered with evidence: a list of
    /// adjacent transpositions, each checked against the independence relation
    /// before it was recorded.
    ///
    /// # Specification
    /// - requires: `from` and `to` name events of this order.
    /// - ensures: a witness whose transpositions, applied in turn to `from`,
    ///   give `to`, each swapping an independent pair.
    /// - provides: shift equivalence of two sequentializations, decided and
    ///   witnessed.
    /// - fails: [`ExchangeObstruction::NotARearrangement`] when `to` is not a
    ///   permutation of `from`;
    ///   [`ExchangeObstruction::DependentTransposition`], the exchange kill
    ///   signal, when reaching `to` would swap a dependent pair.
    /// - panics: none.
    /// - intension: a selection pass bringing each wanted event down to its
    ///   target position by adjacent swaps, so the witness holds exactly the
    ///   inversions between the two orders, quadratic in the worst case.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each failure mode is separated by a fixture
    ///   triggering only it: a target holding an event the source does not, and
    ///   a target inverting a dependent pair; L2 — the canonical order is
    ///   reachable over generated derivations, each transposition re-asked of
    ///   the independence relation.
    /// - witness: `causal::tests::the_exchange_witness_carries_the_recorded_order_to_the_canonical_one`
    /// - witness: `causal::tests::a_target_that_is_not_a_rearrangement_is_refused`
    /// - witness: `causal::tests::a_target_inverting_a_dependent_pair_is_refused`
    /// - witness: `tests::normal_form::an_independent_pair_is_reordered_by_licensed_transpositions`
    /// - witness: `tests::normal_form::a_containment_dependent_pair_refuses_its_transposition`
    /// - witness: `tests::normal_form::the_canonical_order_is_always_reachable_by_licensed_transpositions`
    #[inline]
    pub fn exchange_between(
        &self,
        from: &[EventIndex],
        to: &[EventIndex],
    ) -> Result<ExchangeWitness, ExchangeObstruction>
    {
        if from.len() != to.len() {
            return Err(ExchangeObstruction::NotARearrangement);
        }
        let mut current: Vec<EventIndex> = from.to_vec();
        let mut transpositions: Vec<Transposition> = Vec::new();
        for (target, wanted) in to.iter().enumerate() {
            let Some(found) = current.iter().skip(target).position(|held| held == wanted)
            else {
                return Err(ExchangeObstruction::NotARearrangement);
            };
            let mut position = target.saturating_add(found);
            while position > target {
                let below = position.saturating_sub(1_usize);
                let (Some(&lower), Some(&upper)) = (current.get(below), current.get(position))
                else {
                    return Err(ExchangeObstruction::NotARearrangement);
                };
                if !bool::from(self.independent(lower, upper)) {
                    return Err(ExchangeObstruction::DependentTransposition {
                        earlier: lower,
                        later: upper,
                    });
                }
                current.swap(below, position);
                transpositions.push(Transposition {
                    position: SchedulePosition::from(below),
                });
                position = below;
            }
        }
        Ok(ExchangeWitness { transpositions })
    }

    /// The exchange witness carrying the recorded order to the canonical one.
    ///
    /// # Specification
    /// - ensures: a witness whose transpositions carry
    ///   [`EventOrder::recorded_order`] to [`EventOrder::canonical_order`].
    /// - provides: the evidence that canonicalization stays inside the trace
    ///   class.
    /// - fails: [`ExchangeObstruction::DependentTransposition`] when the
    ///   canonical key is not a linear extension of the causal order. While
    ///   depths come from [`EventOrder::of_events`] a dependent pair has
    ///   strictly increasing depth, so this arm is a tripwire for a future key
    ///   rather than a reachable failure, witnessed through
    ///   [`EventOrder::exchange_between`].
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the witness is applied to the recorded order and
    ///   compared with the canonical one; the refusal arm is separated at
    ///   [`EventOrder::exchange_between`].
    /// - witness: `causal::tests::the_exchange_witness_carries_the_recorded_order_to_the_canonical_one`
    /// - witness: `tests::normal_form::the_canonical_order_is_always_reachable_by_licensed_transpositions`
    #[inline]
    pub fn exchange_to_canonical(&self) -> Result<ExchangeWitness, ExchangeObstruction>
    {
        self.exchange_between(&self.recorded_order(), &self.canonical_order())
    }
}

/// Whether two recorded steps are licensed to commute.
///
/// The question is delegated to the crate's single shift guard rather than
/// restated, and any refusal (a comparable position, a genuine overlap, an
/// undischarged convexity conjunct, an unresolvable identifier) is read as
/// dependence, the conservative direction.
///
/// # Specification
/// - ensures: positive exactly when the guard's conjuncts hold for the pair
///   under `convexity`; the answer does not depend on which step is `left`.
/// - provides: the independence relation the causal order is built from.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the conjuncts are witnessed at the guard's own suite;
///   what this adds is the direction of the collapse, separated by an
///   overlapping pair whose two orders reach one term and which the quotient
///   still refuses, and by a withheld warrant that empties the quotient. Its
///   soundness rests on the term algebra's locality, which no conjunct reads;
///   the normal form's replay of the schedule catches a breach.
/// - witness: `tests::normal_form::an_overlapping_pair_keeps_its_recorded_order`
/// - witness: `tests::normal_form::a_layered_derivation_keeps_its_dependent_step_last`
/// - witness: `tests::normal_form::a_withheld_convexity_warrant_empties_the_shift_quotient`
/// - witness: `tests::normal_form::a_non_local_term_algebra_trips_the_kill_signal_at_the_join`
fn step_independence_with_support<A>(
    store: &CellStore<A>,
    left: &CellApp<A>,
    right: &CellApp<A>,
    convexity: ConvexityDischarge,
    support: &OverlapSupport,
) -> StepIndependence
where
    A: CellAlphabet,
{
    StepIndependence::from(
        check_shift_guard_with_support(store, left, right, convexity, support).is_ok(),
    )
}

#[cfg(test)]
mod tests
{
    use gandr_theory_cell_complexes::Cell;
    use gandr_theory_cell_complexes::CellId;
    use gandr_theory_cell_complexes::CellProvenance;
    use gandr_theory_cell_complexes::CmdPat;
    use gandr_theory_cell_complexes::ConsPat;
    use gandr_theory_cell_complexes::Orientation;
    use gandr_theory_cell_complexes::Polarity;
    use gandr_theory_cell_complexes::Pos;
    use gandr_theory_cell_complexes::ProdPat;

    use super::*;
    use crate::normal_form::event_order;
    use crate::normal_form::prim_address;

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

    /// A store holding (add-S), and the two-step derivation
    /// `⟨Succ(Succ(Zero)) | add(Zero; ★)⟩ ~>* ⟨Zero | add(Zero;
    /// Succ⁻(Succ⁻(★)))⟩`.
    ///
    /// A sequent term has one command position, so the two steps are at the
    /// same position and dependent: a two-event chain.
    ///
    /// # Specification
    /// trivial.
    fn chain_fixture() -> (CellStore, CmdPat, [CellApp; 2])
    {
        let mut store = CellStore::new();
        let add = store.insert(add_s());
        let peak = CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Succ", [ProdPat::ctor("Succ", [ProdPat::ctor("Zero", [])])]),
            ConsPat::op("add", [ProdPat::ctor("Zero", [])], ConsPat::top()),
        );
        let steps = [
            CellApp {
                cell: add,
                at: Pos::root(),
            },
            CellApp {
                cell: add,
                at: Pos::root(),
            },
        ];
        (store, peak, steps)
    }

    /// The chain fixture's event order.
    ///
    /// # Specification
    /// - panics: when the chain does not replay, which is a fixture defect.
    fn chain_order() -> EventOrder
    {
        let (store, peak, steps) = chain_fixture();
        event_order(&store, &peak, &steps).expect("the chain replays")
    }

    #[test]
    fn precedence_is_the_transitive_closure_of_dependence()
    {
        let order = chain_order();
        let first = EventIndex::from(0_usize);
        let second = EventIndex::from(1_usize);
        assert!(
            bool::from(order.depends_directly(second, first)),
            "the two steps share the one command position, so they are dependent"
        );
        assert!(
            bool::from(order.precedes(first, second)),
            "and dependence gives precedence"
        );
        assert!(
            !bool::from(order.precedes(second, first)),
            "precedence is asymmetric: the edges only point backwards"
        );
        assert!(
            !bool::from(order.depends_directly(first, second)),
            "and direct dependence is recorded in one direction only"
        );
    }

    #[test]
    fn an_event_is_never_independent_of_itself()
    {
        let order = chain_order();
        let first = EventIndex::from(0_usize);
        assert!(
            !bool::from(order.independent(first, first)),
            "a step is always dependent on itself: its position order with itself is Same"
        );
    }

    #[test]
    fn an_event_is_never_concurrent_with_itself()
    {
        let order = chain_order();
        let first = EventIndex::from(0_usize);
        assert!(
            !bool::from(order.concurrent(first, first)),
            "concurrency is irreflexive"
        );
    }

    #[test]
    fn an_out_of_range_index_depends_on_nothing()
    {
        let order = chain_order();
        let beyond = EventIndex::from(9_usize);
        let first = EventIndex::from(0_usize);
        assert!(
            matches!(
                order.event(beyond),
                Maybe::Absent(event_lookup::Absent::OutOfRange)
            ),
            "the index names no event, so there is nothing to read"
        );
        assert_eq!(
            Maybe::Absent(event_lookup::Absent::OutOfRange),
            order.depth(beyond),
            "and no depth either"
        );
        assert!(
            !bool::from(order.depends_directly(beyond, first)),
            "an index outside the order depends on nothing rather than panicking"
        );
        assert!(
            !bool::from(order.precedes(first, beyond)),
            "and precedes nothing"
        );
        // The conservative direction, which the two symmetric relations get
        // wrong if written as plain complements: an absent event read through
        // `depends_directly` alone depends on nothing, which would make it
        // independent of and concurrent with everything.
        assert!(
            !bool::from(order.independent(beyond, first)),
            "an index outside the order commutes with nothing"
        );
        assert!(
            !bool::from(order.concurrent(beyond, first)),
            "and is concurrent with nothing"
        );
    }

    #[test]
    fn a_dependent_chain_is_its_own_canonical_order()
    {
        let order = chain_order();
        assert_eq!(
            order.recorded_order(),
            order.canonical_order(),
            "a totally ordered derivation has one sequentialization"
        );
        assert_eq!(
            2_usize,
            order.layers().len(),
            "and every event sits in a layer of its own"
        );
    }

    #[test]
    fn the_exchange_witness_carries_the_recorded_order_to_the_canonical_one()
    {
        let order = chain_order();
        let witness = order
            .exchange_to_canonical()
            .expect("the canonical key is a linear extension of the causal order");
        assert_eq!(
            TranspositionCount::from(0_usize),
            witness.transposition_count(),
            "a chain is already canonical, so no transposition is licensed or needed"
        );
        assert_eq!(
            Maybe::Present(order.canonical_order()),
            witness.apply(&order.recorded_order()),
            "and applying the witness reproduces the canonical order"
        );
    }

    #[test]
    fn a_target_that_is_not_a_rearrangement_is_refused()
    {
        let order = chain_order();
        let recorded = order.recorded_order();
        let short = order.exchange_between(&recorded, &[EventIndex::from(0_usize)]);
        assert_eq!(
            Err(ExchangeObstruction::NotARearrangement),
            short,
            "a target of a different length is not a rearrangement"
        );
        let foreign = order.exchange_between(&recorded, &[
            EventIndex::from(0_usize),
            EventIndex::from(7_usize),
        ]);
        assert_eq!(
            Err(ExchangeObstruction::NotARearrangement),
            foreign,
            "and neither is a target naming an event the source does not hold"
        );
    }

    /// An event order assembled directly from depths and keys.
    ///
    /// The refusal it exercises cannot be reached through a derivation over
    /// either shipped alphabet: an equal address forces an equal position,
    /// which forces dependence and so distinct depths. The moment an
    /// alphabet's `Hash` maps two sites to one address the tie is reachable, so
    /// the witnesses assemble the order instead of deriving it.
    ///
    /// # Specification
    /// trivial.
    fn assembled_order(entries: &[(CellApp, CausalDepth, EventKey)]) -> EventOrder
    {
        EventOrder {
            events: entries
                .iter()
                .map(|entry| DerivationEvent::new(entry.0.clone(), entry.2.address()))
                .collect(),
            dependences: entries.iter().map(|_entry| Vec::new()).collect(),
            depths: entries.iter().map(|entry| entry.1).collect(),
            keys: entries.iter().map(|entry| entry.2).collect(),
            convexity: ConvexityDischarge::StronglyConnectedOverAcyclicTarget,
        }
    }

    /// Two distinct content addresses, taken over two distinct cells.
    ///
    /// # Specification
    /// - panics: when the two addresses coincide, which is a fixture defect.
    fn two_addresses() -> (PrimId, PrimId)
    {
        let left = add_s();
        let right: Cell = Cell::new(
            CmdPat::cut(
                Polarity::Positive,
                ProdPat::ctor("Zero", []),
                ConsPat::top(),
            ),
            CmdPat::cut(
                Polarity::Positive,
                ProdPat::ctor("Zero", []),
                ConsPat::top(),
            ),
            Orientation::PolarityDerived,
            CellProvenance::SurfaceRule,
        );
        let addresses = (
            prim_address(&left, &Pos::root()),
            prim_address(&right, &Pos::root()),
        );
        assert_ne!(
            addresses.0, addresses.1,
            "the two cells differ in content, so their addresses differ"
        );
        addresses
    }

    /// One step at the root of the first cell, shared by the assembled orders.
    ///
    /// # Specification
    /// trivial.
    fn root_step() -> CellApp
    {
        CellApp {
            cell: CellId::from(0_usize),
            at: Pos::root(),
        }
    }

    #[test]
    fn an_order_whose_keys_are_distinct_is_accepted()
    {
        let (left, right) = two_addresses();
        let order = assembled_order(&[
            (root_step(), CausalDepth::from(0_usize), EventKey {
                address: left,
                past: causal_past_address(left, &[]),
            }),
            (root_step(), CausalDepth::from(0_usize), EventKey {
                address: right,
                past: causal_past_address(right, &[]),
            }),
        ]);
        assert_eq!(
            Ok(()),
            order.refuse_key_collisions(),
            "two events at one depth with different keys are totally ordered"
        );
    }

    #[test]
    fn two_events_tying_on_depth_and_key_are_refused()
    {
        // Two events at one depth carrying one key: the sort would fall back
        // on its own stability and so on the arrival order, which would make
        // the canonical order a property of the presentation rather than of
        // the trace. It is refused instead.
        let (address, _other) = two_addresses();
        let key = EventKey {
            address,
            past: causal_past_address(address, &[]),
        };
        let order = assembled_order(&[
            (root_step(), CausalDepth::from(1_usize), key),
            (root_step(), CausalDepth::from(1_usize), key),
        ]);
        assert_eq!(
            Err(KeyCollision {
                earlier: EventIndex::from(0_usize),
                later: EventIndex::from(1_usize),
                depth: CausalDepth::from(1_usize),
                key,
            }),
            order.refuse_key_collisions(),
            "the refusal names both events, the shared depth, and the shared key"
        );
    }

    #[test]
    fn a_repeated_primitive_at_two_depths_is_not_a_tie()
    {
        // The graded-multiplicity case, which must not be refused: a repeated
        // primitive shares its address by design, and the depth separates the
        // two occurrences. A check on the key alone would reject every
        // derivation that fires one primitive twice.
        let (address, _other) = two_addresses();
        let key = EventKey {
            address,
            past: causal_past_address(address, &[]),
        };
        let order = assembled_order(&[
            (root_step(), CausalDepth::from(0_usize), key),
            (root_step(), CausalDepth::from(1_usize), key),
        ]);
        assert_eq!(
            Ok(()),
            order.refuse_key_collisions(),
            "one primitive at two depths is two events the depth already separates"
        );
    }

    #[test]
    fn the_causal_past_separates_two_events_sharing_an_address()
    {
        // Why the key is not the address alone. Two events at one depth with
        // one address, which an alphabet may produce legally since
        // `core::hash::Hash` promises no injectivity, are separated by what
        // they sit over. Drop the past component and this pair ties.
        let (address, other) = two_addresses();
        let rootless = EventKey {
            address,
            past: causal_past_address(address, &[]),
        };
        let caused = EventKey {
            address,
            past: causal_past_address(address, &[causal_past_address(other, &[])]),
        };
        assert_ne!(
            rootless.past(),
            caused.past(),
            "one address over two different causal pasts gives two keys"
        );
        assert_eq!(
            rootless.address(),
            caused.address(),
            "and the address component alone cannot tell them apart"
        );
        let order = assembled_order(&[
            (root_step(), CausalDepth::from(0_usize), rootless),
            (root_step(), CausalDepth::from(0_usize), caused),
        ]);
        assert_eq!(
            Ok(()),
            order.refuse_key_collisions(),
            "so the pair is totally ordered rather than refused"
        );
    }

    #[test]
    fn a_target_inverting_a_dependent_pair_is_refused()
    {
        // The exchange kill signal, raised. The two steps of the chain are
        // dependent, so the reversed order is a different trace and the swap
        // that would reach it is refused rather than performed.
        let order = chain_order();
        let first = EventIndex::from(0_usize);
        let second = EventIndex::from(1_usize);
        let reversed = order.exchange_between(&order.recorded_order(), &[second, first]);
        assert_eq!(
            Err(ExchangeObstruction::DependentTransposition {
                earlier: first,
                later: second,
            }),
            reversed,
            "reaching the reversed order needs a transposition of a dependent pair"
        );
    }
}
