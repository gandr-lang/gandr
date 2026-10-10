//! The earned shift-equivalence witness: the identification of two
//! sequentializations, granted per redex pair against a guard and never
//! imposed.
//!
//! Two adjacent applications at disjoint positions with trivial overlap
//! commute, so a two-redex body's two sequentializations are one composite
//! transformation rather than two. That identification is what a normal-form
//! fast path decides, so it is granted per pair, against a guard, and refused
//! when the guard does not hold.
//!
//! # The guard, and why it is three conjuncts rather than one
//!
//! Disjointness of supports does not imply independence once matches must be
//! convex: two rule applications on disjoint hyperedge sets can block one
//! another, because applying one creates a directed path that destroys the
//! other's convexity (Bonchi, Gadducci, Kissinger, Sobociński and Zanasi,
//! *String Diagram Rewrite Theory II*). So the guard is:
//!
//! 1. **the positions are incomparable**: neither position a prefix of the
//!    other ([`CellAlphabet::position_order`]), which is what makes the two
//!    applications address disjoint subtrees;
//! 2. **the cell pair has trivial overlap**: the overlap enumerator's own
//!    verdict, taken per ordered pair in both orders ([`overlaps_between`]);
//! 3. **each match image is still convex in the other's reduct**: the conjunct
//!    the first two do not give, and the only new one.
//!
//! # The third conjunct is carried, not computed
//!
//! Convexity of one match is a directed reachability sweep over the whole
//! target, keyed by term and position, so unlike the overlap conjunct it
//! cannot be cached across terms. On a store whose left-hand sides are
//! strongly connected over an acyclic target it is constant-true, so it is
//! skipped rather than run, and the witness carries the name of that warrant
//! ([`ConvexityDischarge`]) instead of a recomputed sweep.
//!
//! The discharge is a fence over the alphabet's grammar and never a refutation
//! of the hazard. An alphabet that admits multi-output or disconnected
//! left-hand sides breaks the forcing argument, must answer
//! [`ConvexityDischarge::ReCheckRequired`], and is refused the witness here
//! until the re-check is built.
//!
//! # Where the extension is empty
//!
//! Over [`SequentAlphabet`] a command pattern is a single cut whose children
//! are a producer and a consumer, so the only command position in a term is
//! the root: two applications are never incomparable, and the shift quotient's
//! extension over the sequent alphabet is empty. The guard is live the moment
//! an alphabet nests commands, which the toy alphabet does and a circuit-shaped
//! body will.
//!
//! # Cost
//!
//! One guarded commutation costs what one replay step costs. What the guard
//! can lose to is the number of questions: a canonical schedule reached by
//! adjacent transpositions asks a quadratic number of independence questions
//! in the path length, which the integration suite measures rather than
//! assumes.

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
use gandr_theory_coherent_resolutions::Overlap;
use gandr_theory_coherent_resolutions::OverlapSupport;
use gandr_theory_coherent_resolutions::overlaps_between;
use gandr_theory_coherent_resolutions::replay_from_peak;
use gandr_theory_coherent_resolutions::rewrite_at;
use quenchant_shape::shape::Maybe;

use crate::boundary::ShiftReplay;

/// A shift-equivalence witness: evidence that two adjacent applications
/// commute, so their two sequentializations are one composite.
///
/// The witness is a boundary (`peak`, `joins_at`), the two applications that
/// span it in either order, and the warrant its convexity conjunct was
/// discharged under. It is replayed, not trusted
/// ([`ShiftEquivalence::replay`]): holding one records which guard granted the
/// identification and a boundary that can be re-executed.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ShiftEquivalence<A: CellAlphabet = SequentAlphabet>
{
    /// The term both sequentializations start from.
    pub peak: A::Cmd,
    /// The application recorded first.
    pub first: CellApp<A>,
    /// The application recorded second.
    pub second: CellApp<A>,
    /// The composite: the term both sequentializations reach.
    pub joins_at: A::Cmd,
    /// The warrant the convexity conjunct was discharged under, carried rather
    /// than recomputed.
    pub convexity: ConvexityDischarge,
}

impl<A: CellAlphabet> ShiftEquivalence<A>
{
    /// The sequentialization that fires [`ShiftEquivalence::first`] first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn first_then_second(&self) -> Vec<CellApp<A>>
    {
        alloc::vec![self.first.clone(), self.second.clone()]
    }

    /// The sequentialization that fires [`ShiftEquivalence::second`] first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn second_then_first(&self) -> Vec<CellApp<A>>
    {
        alloc::vec![self.second.clone(), self.first.clone()]
    }

    /// Replay the identification: re-execute both sequentializations from the
    /// peak and check they both reach the composite.
    ///
    /// The engine's peak-rooted replay ([`replay_from_peak`]) read on a shift
    /// boundary: the two orders share a peak and a join by construction, so
    /// both replaying is exactly replay-equality of the two derivations.
    ///
    /// # Specification
    /// - ensures: positive exactly when, with the peak and the composite
    ///   skolemized to constants, both orders fire step by step and land on the
    ///   skolemized composite; a step that no longer fires, a stale cell
    ///   identifier, or either order landing elsewhere is a negative.
    /// - provides: the confirmation half of the identification, separate from
    ///   the guard that licensed it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision is the conjunction of two path replays
    ///   against one boundary, separated by a derived witness that replays and
    ///   by the same witness with its composite retargeted to a term neither
    ///   order reaches. A candidate with exactly one firing order is rejected
    ///   in either orientation, even when its declared join is the successful
    ///   order’s actual result. Dropping either replay conjunct changes that
    ///   boundary.
    /// - witness: `tests::shift::the_cong2_composite_replays_under_both_sequentializations`
    /// - witness: `tests::shift::a_retargeted_composite_no_longer_replays`
    /// - witness: `shift::tests::paired_firing_and_one_sided_replay_preserve_boundaries`
    #[inline]
    #[must_use]
    #[spec(ensures: |output| bool::from(output) == bool::from(replay_from_peak(store, &self.peak, &self.joins_at,
    &[self.first.clone(), self.second.clone()], &[self.second.clone(), self.first.clone()])))]
    pub fn replay(
        &self,
        store: &CellStore<A>,
    ) -> ShiftReplay
    {
        let replayed = replay_from_peak(
            store,
            &self.peak,
            &self.joins_at,
            &self.first_then_second(),
            &self.second_then_first(),
        );
        ShiftReplay::from(bool::from(replayed))
    }
}

/// Why a pair of adjacent applications was refused the shift-equivalence
/// witness.
///
/// A pair the guard does not cover keeps its two sequentializations distinct,
/// and the variant says which conjunct or which instance check declined it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ShiftObstruction<A: CellAlphabet = SequentAlphabet>
{
    /// An application names a cell the store does not hold.
    UnknownCell
    {
        /// The identifier that resolved to nothing.
        cell: CellId,
    },
    /// The positions are comparable: one application addresses a subtree
    /// containing the other's, so the two are nested rather than adjacent.
    ComparablePositions
    {
        /// How the two positions relate.
        order: PositionOrder,
    },
    /// The cell pair has a genuine overlap, so the two applications may
    /// interfere through the cells rather than through the term.
    GenuineOverlap
    {
        /// The first overlap witnessing the interference, in enumeration order.
        overlap: Box<Overlap<A>>,
    },
    /// The convexity conjunct is not discharged on this store, and the
    /// per-pair re-check is not built, so the shift is refused rather than
    /// assumed.
    ConvexityNotDischarged,
    /// A recorded application does not fire at its recorded position in the
    /// sequentialization that reaches it.
    StepDoesNotFire
    {
        /// The step that failed to fire.
        step: Box<CellApp<A>>,
    },
    /// Both orders fire but reach different terms, so there is no composite to
    /// identify them at.
    ///
    /// On an alphabet whose incomparable positions address disjoint subtrees
    /// this is unreachable, since splicing at disjoint positions commutes; it
    /// is the check that catches an alphabet where they do not.
    SequentializationsDiffer
    {
        /// The term reached by firing the first application first.
        first_then_second: Box<A::Cmd>,
        /// The term reached by firing the second application first.
        second_then_first: Box<A::Cmd>,
    },
}

/// Derive the shift-equivalence witness for a pair of adjacent applications
/// in `peak`, or refuse it.
///
/// The three guard conjuncts are checked, never assumed: the positions must be
/// incomparable, the cell pair must have trivial overlap in both orders, and
/// the convexity conjunct must be discharged by the store's own warrant
/// ([`CellAlphabet::convexity_discharge`]). A pair that clears the guard is
/// then exercised: both orders must fire and reach one term, which becomes the
/// composite.
///
/// # Specification
/// - requires: `first` and `second` are applications intended at positions of
///   `peak`; the alphabet answers [`CellAlphabet::convexity_discharge`]
///   honestly for `store`.
/// - ensures: a witness only when all three conjuncts hold and both
///   sequentializations fire from `peak` to one common term; the witness
///   records that term as its composite and carries the discharge it was
///   granted under.
/// - provides: the per-pair licence a normal-form fast path needs, with its
///   evidence attached.
/// - fails: [`ShiftObstruction`]: an unresolvable cell identifier, comparable
///   positions, a genuine overlap, an undischarged convexity conjunct, a step
///   that does not fire, or two orders that reach different terms.
/// - panics: none.
/// - intension: the conjuncts are decided in the guard's own order (cell
///   resolution, positions, overlap, convexity, then the two
///   sequentializations), so a pair failing several is refused by the earliest.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — each conjunct is separated by a pair failing only it: the
///   cong2 pair clears all three; a nested pair whose cells also overlap fails
///   positions first; an overlapping pair at incomparable positions fails the
///   overlap conjunct; a withheld discharge fails the third; and an unknown
///   identifier and a non-firing step separate the two instance checks. Both
///   overlap directions and the two lookup positions are independently
///   exercised before later refusals. Wrong failure precedence changes the
///   variant or its attached identity.
/// - witness: `tests::shift::the_cong2_pair_earns_its_shift_equivalence_witness`
/// - witness: `shift::tests::a_nested_pair_is_refused_before_the_overlap_conjunct`
/// - witness: `shift::tests::a_genuinely_overlapping_pair_is_refused_the_witness`
/// - witness: `shift::tests::an_undischarged_convexity_conjunct_refuses_the_pair`
/// - witness: `shift::tests::an_unknown_cell_identifier_is_refused`
/// - witness: `shift::tests::a_step_that_does_not_fire_is_refused`
/// - witness: `shift::tests::guard_lookup_and_reverse_overlap_precedence_are_exact`
#[inline]
#[spec(ensures: |output| {
    let convexity = A::convexity_discharge(store);
    check_shift_guard(store, first, second, convexity).map_or_else(|reason| output == Err(reason), |()| {
        run_pair(store, peak, first, second).map_or_else(|reason| output == Err(reason), |forward| {
            run_pair(store, peak, second, first).map_or_else(|reason| output == Err(reason), |backward| {
                if forward == backward {
                    output.as_ref().is_ok_and(|witness| witness.peak == *peak && witness.first == *first && witness.second == *second && witness.joins_at == forward && witness.convexity == convexity)
                } else {
                    matches!(output, Err(ShiftObstruction::SequentializationsDiffer { ref first_then_second, ref second_then_first }) if **first_then_second == forward && **second_then_first == backward)
                }
            })
        })
    })
})]
pub fn derive_shift_equivalence<A>(
    store: &CellStore<A>,
    peak: &A::Cmd,
    first: &CellApp<A>,
    second: &CellApp<A>,
) -> Result<ShiftEquivalence<A>, ShiftObstruction<A>>
where
    A: CellAlphabet,
{
    let convexity = A::convexity_discharge(store);
    check_shift_guard(store, first, second, convexity)?;
    let forward = run_pair(store, peak, first, second)?;
    let backward = run_pair(store, peak, second, first)?;
    if forward != backward {
        return Err(ShiftObstruction::SequentializationsDiffer {
            first_then_second: Box::new(forward),
            second_then_first: Box::new(backward),
        });
    }
    Ok(ShiftEquivalence {
        peak: peak.clone(),
        first: first.clone(),
        second: second.clone(),
        joins_at: forward,
        convexity,
    })
}

/// The three guard conjuncts, with the convexity discharge and the overlap
/// support supplied.
///
/// This is the crate's one independence relation: the causal order decides
/// which steps depend on which by asking this guard, so no second copy of the
/// conjuncts can drift from it. That reader takes any refusal as dependence,
/// the conservative direction, since refusing to commute is always sound. The
/// support is supplied so a reader asking about many pairs over one store
/// builds it once.
///
/// # Specification
/// - requires: `support` is [`OverlapSupport::from_store`] over `store`.
/// - ensures: success exactly when both cells resolve, the positions are
///   incomparable, the cell pair has no overlap in either order, and
///   `convexity` is [`ConvexityDischarge::StronglyConnectedOverAcyclicTarget`].
/// - fails: the corresponding [`ShiftObstruction`] variant, decided in that
///   order.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — the conjunct order is a decision surface, separated by a
///   nested pair whose cells also overlap and by an identical pair under a
///   withheld discharge. An overlap found only in the reverse query still
///   precedes convexity; each missing identifier precedes position comparison
///   and two missing identifiers report the first.
/// - witness: `shift::tests::a_nested_pair_is_refused_before_the_overlap_conjunct`
/// - witness: `shift::tests::an_undischarged_convexity_conjunct_refuses_the_pair`
/// - witness: `shift::tests::guard_lookup_and_reverse_overlap_precedence_are_exact`
#[inline]
#[spec(ensures: |output| match store.get(first.cell) {
    Maybe::Absent(_) => matches!(output, Err(ShiftObstruction::UnknownCell { cell }) if cell == first.cell),
    Maybe::Present(first_cell) => match store.get(second.cell) {
        Maybe::Absent(_) => matches!(output, Err(ShiftObstruction::UnknownCell { cell }) if cell == second.cell),
        Maybe::Present(second_cell) => {
            let order = A::position_order(&first.at, &second.at);
            if order == PositionOrder::Incomparable {
                let overlap = if bool::from(support.independent(first.cell, second.cell)) { None } else {
                    overlaps_between((first.cell, first_cell), (second.cell, second_cell)).into_iter()
                        .chain(overlaps_between((second.cell, second_cell), (first.cell, first_cell))).next()
                };
                overlap.as_ref().map_or_else(
                    || output == if convexity == ConvexityDischarge::StronglyConnectedOverAcyclicTarget { Ok(()) } else { Err(ShiftObstruction::ConvexityNotDischarged) },
                    |expected| matches!(output, Err(ShiftObstruction::GenuineOverlap { ref overlap }) if **overlap == *expected),
                )
            } else { output == Err(ShiftObstruction::ComparablePositions { order }) }
        },
    },
})]
pub fn check_shift_guard_with_support<A>(
    store: &CellStore<A>,
    first: &CellApp<A>,
    second: &CellApp<A>,
    convexity: ConvexityDischarge,
    support: &OverlapSupport,
) -> Result<(), ShiftObstruction<A>>
where
    A: CellAlphabet,
{
    let Maybe::Present(first_cell) = store.get(first.cell)
    else {
        return Err(ShiftObstruction::UnknownCell { cell: first.cell });
    };
    let Maybe::Present(second_cell) = store.get(second.cell)
    else {
        return Err(ShiftObstruction::UnknownCell { cell: second.cell });
    };
    let order = A::position_order(&first.at, &second.at);
    if order != PositionOrder::Incomparable {
        return Err(ShiftObstruction::ComparablePositions { order });
    }
    if !bool::from(support.independent(first.cell, second.cell)) {
        let mut overlaps = overlaps_between((first.cell, first_cell), (second.cell, second_cell));
        overlaps.extend(overlaps_between(
            (second.cell, second_cell),
            (first.cell, first_cell),
        ));
        if let Some(overlap) = overlaps.into_iter().next() {
            return Err(ShiftObstruction::GenuineOverlap {
                overlap: Box::new(overlap),
            });
        }
    }
    if convexity != ConvexityDischarge::StronglyConnectedOverAcyclicTarget {
        return Err(ShiftObstruction::ConvexityNotDischarged);
    }
    Ok(())
}

/// The independence guard, with the overlap support built for this one call.
///
/// # Specification
/// - ensures: exactly [`check_shift_guard_with_support`] over the support of
///   `store`.
/// - fails: as [`check_shift_guard_with_support`] fails.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — with support built from the same store, missing
///   identifiers precede comparable positions, and either overlap direction
///   precedes a withheld discharge. A reversed lookup order or omitted overlap
///   direction changes the typed refusal.
/// - witness: `shift::tests::guard_lookup_and_reverse_overlap_precedence_are_exact`
#[inline]
#[spec(ensures: |output| output == check_shift_guard_with_support(store, first, second, convexity, &OverlapSupport::from_store(store)))]
pub fn check_shift_guard<A>(
    store: &CellStore<A>,
    first: &CellApp<A>,
    second: &CellApp<A>,
    convexity: ConvexityDischarge,
) -> Result<(), ShiftObstruction<A>>
where
    A: CellAlphabet,
{
    let support = OverlapSupport::from_store(store);
    check_shift_guard_with_support(store, first, second, convexity, &support)
}

/// Fire `lead` then `trail` from `term`, refusing the step that does not fire.
///
/// # Specification
/// - ensures: the term both steps reach when each fires at its recorded
///   position in sequence.
/// - fails: [`ShiftObstruction::UnknownCell`] for a stale identifier and
///   [`ShiftObstruction::StepDoesNotFire`] for a position that carries no redex
///   for its cell.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — concrete root rules reach a distinct composite only in
///   the specified order; a failed lead precedes an unknown trail, and a
///   successful lead exposes the trail refusal. Reversing, skipping or
///   misreporting a step changes the term or error.
/// - witness: `shift::tests::paired_firing_and_one_sided_replay_preserve_boundaries`
#[spec(ensures: |output| output == fire_step(store, term, lead).and_then(|after| fire_step(store, &after, trail)))]
fn run_pair<A>(
    store: &CellStore<A>,
    term: &A::Cmd,
    lead: &CellApp<A>,
    trail: &CellApp<A>,
) -> Result<A::Cmd, ShiftObstruction<A>>
where
    A: CellAlphabet,
{
    let after_lead = fire_step(store, term, lead)?;
    fire_step(store, &after_lead, trail)
}

/// Fire one recorded step, refusing rather than reporting an absence.
///
/// # Specification
/// - ensures: the term after `step`'s cell fires at its recorded position.
/// - fails: [`ShiftObstruction::UnknownCell`] for a stale identifier and
///   [`ShiftObstruction::StepDoesNotFire`] when no redex is there.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — issued firing, issued non-firing and unissued steps
///   produce distinct outcomes on concrete terms. Omitting lookup, accepting a
///   failed match or returning the wrong step changes the pair observer.
/// - witness: `shift::tests::paired_firing_and_one_sided_replay_preserve_boundaries`
#[spec(ensures: |output| match store.get(step.cell) {
    Maybe::Absent(_) => matches!(output, Err(ShiftObstruction::UnknownCell { cell }) if cell == step.cell),
    Maybe::Present(cell) => match rewrite_at(cell, term, &step.at) {
        Maybe::Present(ref result) => matches!(output, Ok(ref actual) if actual == result),
        Maybe::Absent(_) => matches!(output, Err(ShiftObstruction::StepDoesNotFire { step: ref refused }) if **refused == *step),
    },
})]
fn fire_step<A>(
    store: &CellStore<A>,
    term: &A::Cmd,
    step: &CellApp<A>,
) -> Result<A::Cmd, ShiftObstruction<A>>
where
    A: CellAlphabet,
{
    let Maybe::Present(cell) = store.get(step.cell)
    else {
        return Err(ShiftObstruction::UnknownCell { cell: step.cell });
    };
    match rewrite_at(cell, term, &step.at) {
        | Maybe::Present(result) => Ok(result),
        | Maybe::Absent(_) => Err(ShiftObstruction::StepDoesNotFire {
            step: Box::new(step.clone()),
        }),
    }
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
    use gandr_theory_cell_complexes::path_order;
    use gandr_theory_cell_complexes_tools::Toy;
    use gandr_theory_cell_complexes_tools::ToyAlphabet;
    use gandr_theory_cell_complexes_tools::toy_cell;

    use super::*;

    /// A sequent position from child indices.
    macro_rules! pos {
        ($($step:expr),* $(,)?) => {
            Pos::from_steps([$({
                let step: usize = $step;
                PositionStep::from(step)
            }),*])
        };
    }

    /// The path order of two child-index paths.
    ///
    /// # Specification
    /// trivial.
    fn order_of(
        left: &Pos,
        right: &Pos,
    ) -> PositionOrder
    {
        path_order(left.steps().iter().copied(), right.steps().iter().copied())
    }

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

    /// The two-cell store whose pair the enumerator reports overlapping.
    ///
    /// # Specification
    /// trivial.
    fn overlapping_store() -> (CellStore, CellId, CellId)
    {
        let mut store = CellStore::new();
        let frame = store.insert(frame_defining_cell(&Sym::new("Succ")));
        let add = store.insert(add_s());
        (store, frame, add)
    }

    /// (add-zero): `⟨Zero | add(Zero; ★)⟩ ~> ⟨Zero | ★⟩`.
    ///
    /// A ground rule whose right-hand side offers no seam any left-hand side
    /// unifies with, so the cell overlaps nothing, not even itself: the
    /// sequent fixture for the conjuncts after the overlap one.
    ///
    /// # Specification
    /// trivial.
    fn add_zero_ground() -> Cell
    {
        Cell::new(
            CmdPat::cut(
                Polarity::Positive,
                ProdPat::ctor("Zero", []),
                ConsPat::op("add", [ProdPat::ctor("Zero", [])], ConsPat::top()),
            ),
            CmdPat::cut(
                Polarity::Positive,
                ProdPat::ctor("Zero", []),
                ConsPat::top(),
            ),
            Orientation::PolarityDerived,
            CellProvenance::SurfaceRule,
        )
    }

    /// The single-cell store whose only cell overlaps nothing.
    ///
    /// # Specification
    /// - ensures: exactly one issued cell and no confluence or composition
    ///   overlap.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the same fixture passes the position and overlap
    ///   guards with a discharge and refuses when that warrant is withheld. A
    ///   self-overlapping replacement would refuse earlier.
    /// - witness: `shift::tests::an_undischarged_convexity_conjunct_refuses_the_pair`
    #[spec(ensures: |output| usize::from(output.0.len()) == 1 && matches!(output.0.get(output.1), Maybe::Present(_)) && gandr_theory_coherent_resolutions::enumerate_overlaps(&output.0).is_empty())]
    fn trivial_overlap_store() -> (CellStore, CellId)
    {
        let mut store = CellStore::new();
        let ground = store.insert(add_zero_ground());
        (store, ground)
    }

    /// The command `⟨Zero | Succ⁻(★)⟩` both overlapping-store fixtures fire
    /// at.
    ///
    /// # Specification
    /// trivial.
    fn frame_term() -> CmdPat
    {
        CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Zero", []),
            ConsPat::frame("Succ", ConsPat::top()),
        )
    }

    #[test]
    fn the_path_order_separates_its_four_outcomes()
    {
        assert_eq!(
            PositionOrder::Same,
            order_of(&pos![0, 1], &pos![0, 1]),
            "equal paths are the same position"
        );
        assert_eq!(
            PositionOrder::Encloses,
            order_of(&pos![0], &pos![0, 1]),
            "a proper prefix encloses"
        );
        assert_eq!(
            PositionOrder::EnclosedBy,
            order_of(&pos![0, 1], &pos![0]),
            "and the relation is symmetric up to swapping the two nesting sides"
        );
        assert_eq!(
            PositionOrder::Incomparable,
            order_of(&pos![0, 1], &pos![0, 2]),
            "paths diverging at a shared depth address disjoint subtrees"
        );
        assert_eq!(
            PositionOrder::Encloses,
            order_of(&Pos::root(), &pos![1]),
            "the root encloses every other position"
        );
    }

    #[test]
    fn the_sequent_alphabet_offers_only_the_root_command_position()
    {
        // The shift quotient's extension over this alphabet is empty, and this
        // is why: a command pattern is one cut whose children are a producer
        // and a consumer, neither of which is a command, so no term has two
        // positions to be incomparable at.
        let term = CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Succ", [ProdPat::ctor("Zero", [])]),
            ConsPat::op("add", [ProdPat::ctor("Zero", [])], ConsPat::top()),
        );
        assert_eq!(
            alloc::vec![Pos::root()],
            SequentAlphabet::command_positions(&term),
            "a nested-looking sequent term still has exactly one command position"
        );
    }

    #[test]
    fn two_applications_at_one_position_are_refused()
    {
        let (store, frame, add) = overlapping_store();
        let refusal = derive_shift_equivalence(
            &store,
            &frame_term(),
            &CellApp {
                cell: frame,
                at: Pos::root(),
            },
            &CellApp {
                cell: add,
                at: Pos::root(),
            },
        )
        .expect_err("one position is not two");
        assert_eq!(
            ShiftObstruction::ComparablePositions {
                order: PositionOrder::Same
            },
            refusal,
            "the same position is refused by the first conjunct"
        );
    }

    #[test]
    fn a_nested_pair_is_refused_before_the_overlap_conjunct()
    {
        // The cells of this pair do overlap, so the pair fails two conjuncts;
        // the declared order says the positions decide it.
        let (store, frame, add) = overlapping_store();
        let refusal = derive_shift_equivalence(
            &store,
            &frame_term(),
            &CellApp {
                cell: frame,
                at: Pos::root(),
            },
            &CellApp {
                cell: add,
                at: pos![0],
            },
        )
        .expect_err("a nested pair is refused");
        assert_eq!(
            ShiftObstruction::ComparablePositions {
                order: PositionOrder::Encloses
            },
            refusal,
            "the position conjunct is decided before the overlap conjunct"
        );
    }

    #[test]
    fn a_genuinely_overlapping_pair_is_refused_the_witness()
    {
        // Incomparable positions, so the first conjunct passes; the cell pair
        // composes at a seam, so the second refuses it. The positions are
        // fabricated: this alphabet has no two command positions to fire at,
        // which is exactly the emptiness the module documents.
        let (store, frame, add) = overlapping_store();
        let refusal = derive_shift_equivalence(
            &store,
            &frame_term(),
            &CellApp {
                cell: frame,
                at: pos![0],
            },
            &CellApp {
                cell: add,
                at: pos![1],
            },
        )
        .expect_err("an overlapping cell pair is refused");
        let ShiftObstruction::GenuineOverlap { overlap } = refusal
        else {
            panic!("the overlap conjunct is what refuses this pair");
        };
        assert_eq!(
            frame, overlap.left,
            "the refusal carries the overlap that witnesses the interference"
        );
        assert_eq!(add, overlap.right, "in the order the enumerator found it");
    }

    #[test]
    fn an_undischarged_convexity_conjunct_refuses_the_pair()
    {
        // The first two conjuncts are cleared here (a cell that overlaps
        // nothing, at incomparable positions), and the identical pair is still
        // refused when the discharge is withheld: the third conjunct is a
        // check, not a comment.
        let (store, ground) = trivial_overlap_store();
        let step = CellApp {
            cell: ground,
            at: pos![0],
        };
        let other = CellApp {
            cell: ground,
            at: pos![1],
        };
        assert_eq!(
            Ok(()),
            check_shift_guard(
                &store,
                &step,
                &other,
                ConvexityDischarge::StronglyConnectedOverAcyclicTarget
            ),
            "the guard passes when the store carries the discharge"
        );
        assert_eq!(
            Err(ShiftObstruction::ConvexityNotDischarged),
            check_shift_guard(&store, &step, &other, ConvexityDischarge::ReCheckRequired),
            "and refuses the identical pair when it does not"
        );
    }

    #[test]
    fn a_step_that_does_not_fire_is_refused()
    {
        // The guard passes (the cell overlaps nothing and the positions are
        // incomparable), and the instance check is what declines: neither
        // fabricated position carries a redex, because a sequent term has no
        // command subterm below the root.
        let (store, ground) = trivial_overlap_store();
        let term = CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Zero", []),
            ConsPat::op("add", [ProdPat::ctor("Zero", [])], ConsPat::top()),
        );
        let step = CellApp {
            cell: ground,
            at: pos![0],
        };
        let other = CellApp {
            cell: ground,
            at: pos![1],
        };
        let refusal = derive_shift_equivalence(&store, &term, &step, &other)
            .expect_err("no redex sits at either fabricated position");
        assert_eq!(
            ShiftObstruction::StepDoesNotFire {
                step: Box::new(step)
            },
            refusal,
            "the refusal names the step that did not fire, and the guard is not what declined"
        );
    }

    #[test]
    fn the_sequent_store_carries_the_strongly_connected_discharge()
    {
        let (store, _frame, _add) = overlapping_store();
        assert_eq!(
            ConvexityDischarge::StronglyConnectedOverAcyclicTarget,
            SequentAlphabet::convexity_discharge(&store),
            "every expressible left-hand side is cut-rooted, so the re-check is constant-true"
        );
        assert_eq!(
            ConvexityDischarge::StronglyConnectedOverAcyclicTarget,
            SequentAlphabet::convexity_discharge(&CellStore::new()),
            "the warrant is the grammar's, so an empty store carries it too"
        );
    }

    #[test]
    fn an_unknown_cell_identifier_is_refused()
    {
        let (store, frame, _add) = overlapping_store();
        let missing = CellId::from(99_usize);
        let refusal = derive_shift_equivalence(
            &store,
            &frame_term(),
            &CellApp {
                cell: frame,
                at: pos![0],
            },
            &CellApp {
                cell: missing,
                at: pos![1],
            },
        )
        .expect_err("an unresolvable identifier is refused");
        assert_eq!(
            ShiftObstruction::UnknownCell { cell: missing },
            refusal,
            "the refusal names the identifier that resolved to nothing"
        );
    }

    #[test]
    fn paired_firing_and_one_sided_replay_preserve_boundaries()
    {
        let mut store = CellStore::new();
        let lead_id = store.insert(toy_cell(Toy::succ(Toy::zero()), Toy::zero()));
        let trail_id = store.insert(toy_cell(Toy::zero(), Toy::add(Toy::zero(), Toy::zero())));
        let lead = CellApp {
            cell: lead_id,
            at: ToyAlphabet::root_position(),
        };
        let trail = CellApp {
            cell: trail_id,
            at: ToyAlphabet::root_position(),
        };
        let peak = Toy::succ(Toy::zero());
        let joined = Toy::add(Toy::zero(), Toy::zero());
        assert_eq!(Ok(joined.clone()), run_pair(&store, &peak, &lead, &trail));
        assert_eq!(
            Err(ShiftObstruction::StepDoesNotFire {
                step: Box::new(trail.clone())
            }),
            run_pair(&store, &peak, &trail, &lead)
        );
        assert_eq!(
            Err(ShiftObstruction::StepDoesNotFire {
                step: Box::new(lead.clone())
            }),
            run_pair(&store, &peak, &lead, &lead)
        );
        let missing = CellApp {
            cell: CellId::from(99_usize),
            at: ToyAlphabet::root_position(),
        };
        assert_eq!(
            Err(ShiftObstruction::UnknownCell { cell: missing.cell }),
            run_pair(&store, &peak, &lead, &missing)
        );
        assert_eq!(
            Err(ShiftObstruction::StepDoesNotFire {
                step: Box::new(lead.clone())
            }),
            run_pair(&store, &Toy::zero(), &lead, &missing)
        );
        assert_eq!(
            Err(ShiftObstruction::UnknownCell { cell: missing.cell }),
            run_pair(&store, &peak, &missing, &trail)
        );
        let mut candidate = ShiftEquivalence {
            peak,
            first: lead,
            second: trail,
            joins_at: joined,
            convexity: ConvexityDischarge::StronglyConnectedOverAcyclicTarget,
        };
        assert!(!bool::from(candidate.replay(&store)));
        core::mem::swap(&mut candidate.first, &mut candidate.second);
        assert!(!bool::from(candidate.replay(&store)));
    }

    #[test]
    fn guard_lookup_and_reverse_overlap_precedence_are_exact()
    {
        let mut store = CellStore::new();
        let lead_id = store.insert(toy_cell(Toy::succ(Toy::zero()), Toy::zero()));
        let trail_id = store.insert(toy_cell(Toy::zero(), Toy::add(Toy::zero(), Toy::zero())));
        let lead = CellApp {
            cell: lead_id,
            at: ToyAlphabet::root_position(),
        };
        let trail = CellApp {
            cell: trail_id,
            at: ToyAlphabet::root_position(),
        };
        let first_missing = CellApp {
            cell: CellId::from(99_usize),
            at: ToyAlphabet::root_position(),
        };
        let second_missing = CellApp {
            cell: CellId::from(100_usize),
            at: ToyAlphabet::root_position(),
        };
        let support = OverlapSupport::from_store(&store);
        for (first, second, expected) in [
            (&first_missing, &trail, first_missing.cell),
            (&lead, &second_missing, second_missing.cell),
            (&first_missing, &second_missing, first_missing.cell),
        ] {
            assert_eq!(
                Err(ShiftObstruction::UnknownCell { cell: expected }),
                check_shift_guard_with_support(
                    &store,
                    first,
                    second,
                    ConvexityDischarge::ReCheckRequired,
                    &support
                )
            );
        }
        let reverse_first = CellApp {
            cell: trail_id,
            at: ToyAlphabet::position_at_path(&[PositionStep::from(0_usize)]),
        };
        let reverse_second = CellApp {
            cell: lead_id,
            at: ToyAlphabet::position_at_path(&[PositionStep::from(1_usize)]),
        };
        let refusal = check_shift_guard(
            &store,
            &reverse_first,
            &reverse_second,
            ConvexityDischarge::ReCheckRequired,
        );
        let Err(ShiftObstruction::GenuineOverlap { overlap }) = refusal
        else {
            panic!("the reverse composition precedes the withheld discharge");
        };
        assert_eq!((lead_id, trail_id), (overlap.left, overlap.right));
        assert_eq!(
            gandr_theory_coherent_resolutions::OverlapKind::Composition,
            overlap.kind
        );
    }
}
