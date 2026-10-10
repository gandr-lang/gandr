//! Replayable coherence certificates, generic over the [`CellAlphabet`].
//!
//! A [`Tracelet`] is a peak — an overlap's superposition — and two recorded
//! rewrite paths from it that both reach one join. It is evidence checked by
//! replay, never trusted: [`Tracelet::replay`] skolemizes the peak and the
//! join, re-fires every recorded step by ground rewriting, and answers whether
//! both paths land on the join. Two certificates are the same transformation
//! when they share a boundary and each replays ([`replay_equivalent`]); that
//! relation is certificate identity, kept apart from the structural equality
//! of the two values.
//!
//! - A confluence certificate ([`confluence_tracelet`]) joins the two reducts
//!   of a critical pair.
//! - A composition certificate ([`derive_fused`]) certifies a fused cell: one
//!   path is the two-step derivation, the other the single fused step, and both
//!   reach the composite.

use alloc::vec::Vec;

use gandr_theory_cell_complexes::Cell;
use gandr_theory_cell_complexes::CellAlphabet;
use gandr_theory_cell_complexes::CellId;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::SequentAlphabet;
use quenchant_shape::shape::Maybe;

use crate::boundary::NormalizationBudget;
use crate::boundary::TraceletEquivalence;
use crate::boundary::TraceletReplay;
use crate::overlap::Overlap;
use crate::overlap::OverlapKind;
use crate::overlap::OverlapRefusal;
use crate::rewrite::CellApp;
use crate::rewrite::Normalization;
use crate::rewrite::firing;
use crate::rewrite::normalize;
use crate::rewrite::rewrite_at;

/// A coherence certificate: a peak and two replayable paths from it that
/// reach one join.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Tracelet<A: CellAlphabet = SequentAlphabet>
{
    /// The overlap the certificate is rooted at; its peak is the start of
    /// both paths.
    pub overlap: Overlap<A>,
    /// The first path from the peak to [`Tracelet::joins_at`].
    pub path_a: Vec<CellApp<A>>,
    /// The second path from the peak to [`Tracelet::joins_at`].
    pub path_b: Vec<CellApp<A>>,
    /// The term both paths reach.
    pub joins_at: A::Cmd,
}

/// One step a replay fired.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReplayStep<A: CellAlphabet = SequentAlphabet>
{
    /// The recorded application that fired.
    pub application: CellApp<A>,
    /// The term it produced.
    pub result: A::Cmd,
}

/// Why a replayed step did not fire.
///
/// # Specification
/// - provides: [`Self::UnissuedCell`] for an ill-formed query whose cell is
///   absent; [`Self::DoesNotFire`] for a foreign answer whose issued cell
///   cannot fire at the recorded position, preserving the firing reason. A
///   reached term different from the join is a path disagreement, carried by
///   [`ReplayPathOutcome::Reached`] rather than a stuck step.
///
/// # Adequacy
/// - hypothesis: L3 — absent identifiers and issued cells at nonmatching or
///   absent positions retain distinct, exact reasons in the replay trace.
/// - witness: `tracelet::tests::every_stuck_step_carries_its_pinned_class`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum StuckStep
{
    /// The store holds no cell under the step's identifier.
    UnissuedCell,
    /// The cell the identifier resolves to does not fire at the step's
    /// position.
    DoesNotFire(firing::Absent),
}

/// How one replayed path ended.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ReplayPathOutcome<A: CellAlphabet = SequentAlphabet>
{
    /// Every recorded step fired, producing this term.
    Reached(A::Cmd),
    /// Replay stopped at the first step that did not fire.
    Stuck
    {
        /// The first recorded step that did not fire.
        application: CellApp<A>,
        /// Why it did not.
        reason: StuckStep,
    },
}

/// The observable replay of one recorded path.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReplayPath<A: CellAlphabet = SequentAlphabet>
{
    /// The skolemized peak replay started from.
    pub started_at: A::Cmd,
    /// Every step that fired, in order.
    pub steps: Vec<ReplayStep<A>>,
    /// The term reached, or the first step that did not fire.
    pub outcome: ReplayPathOutcome<A>,
}

/// The observable replay of both paths of a certificate.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReplayTrace<A: CellAlphabet = SequentAlphabet>
{
    /// The first path's replay.
    pub path_a: ReplayPath<A>,
    /// The second path's replay.
    pub path_b: ReplayPath<A>,
    /// The skolemized join both paths must reach.
    pub joins_at: A::Cmd,
}

impl<A: CellAlphabet> ReplayTrace<A>
{
    /// Whether both replayed paths reached the join.
    ///
    /// # Specification
    /// - ensures: positive exactly when both outcomes are
    ///   [`ReplayPathOutcome::Reached`] at [`ReplayTrace::joins_at`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fused certificate's trace over its own store is
    ///   positive, and the same certificate over a permuted store, stuck on its
    ///   first step, is negative.
    /// - witness: `tests::differential::replay_is_pure_over_a_fixed_certificate_and_store`
    /// - witness: `tests::differential::store_permutation_is_not_an_indexed_certificate_invariant`
    #[inline]
    #[must_use]
    pub fn verdict(&self) -> TraceletReplay
    {
        TraceletReplay::from(
            bool::from(reached(&self.path_a.outcome, &self.joins_at))
                && bool::from(reached(&self.path_b.outcome, &self.joins_at)),
        )
    }
}

impl<A: CellAlphabet> Tracelet<A>
{
    /// Replay the certificate: re-fire both paths from the peak and check
    /// they reach the join.
    ///
    /// # Specification
    /// - ensures: [`replay_from_peak`] over the overlap's peak, the join and
    ///   the two recorded paths: positive exactly when, with the peak's and the
    ///   join's metavariables skolemized to constants, every recorded step of
    ///   both paths fires in order and both land on the skolemized join.
    /// - ensures: a recorded [`CellId`] resolves as an insertion-order index
    ///   into `store`, never by cell content: clones and append-only extensions
    ///   of the store keep the verdict, a permutation may change it.
    /// - panics: none.
    /// - intension: retains no step; [`Tracelet::replay_trace`] is the
    ///   evidence-bearing replay.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — a certificate is evidence checked by replay: fused
    ///   and confluence certificates replay over their stores, and one
    ///   retargeted at a join its paths do not reach fails.
    /// - witness: `tracelet::tests::a_fused_cell_certificate_replays`
    /// - witness: `tracelet::tests::a_derivation_that_misses_its_boundary_is_not_self_equivalent`
    /// - witness: `tests::differential::the_fused_cell_certificate_replays_over_the_store`
    /// - witness: `tests::differential::completion_certificates_replay`
    #[inline]
    #[must_use]
    pub fn replay(
        &self,
        store: &CellStore<A>,
    ) -> TraceletReplay
    {
        replay_from_peak(
            store,
            &self.overlap.peak,
            &self.joins_at,
            &self.path_a,
            &self.path_b,
        )
    }

    /// Replay the certificate and keep every step that fired.
    ///
    /// # Specification
    /// - ensures: both paths start at the skolemized peak; each records every
    ///   step that fired with its result, in order, and ends at the term
    ///   reached or at the first step that did not fire, with its reason;
    ///   [`ReplayTrace::joins_at`] is the skolemized join.
    /// - ensures: [`ReplayTrace::verdict`] equals [`Tracelet::replay`] over the
    ///   same store.
    /// - ensures: identifiers resolve by insertion-order index, as
    ///   [`Tracelet::replay`] resolves them, so a permutation that rebinds one
    ///   is observable as the step it stops at.
    /// - panics: none.
    /// - intension: one step vector per path, sized to the recorded path.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — repeated and cloned-store replays give equal traces,
    ///   an append-only extension keeps the trace, and a permutation that
    ///   rebinds a recorded identifier shows the exact step it stops at; L2 —
    ///   every one of those traces' verdicts agrees with the non-tracing
    ///   replay.
    /// - witness: `tests::differential::replay_is_pure_over_a_fixed_certificate_and_store`
    /// - witness: `tests::differential::append_only_store_extension_preserves_replay_trace`
    /// - witness: `tests::differential::store_permutation_is_not_an_indexed_certificate_invariant`
    #[inline]
    #[must_use]
    pub fn replay_trace(
        &self,
        store: &CellStore<A>,
    ) -> ReplayTrace<A>
    {
        let peak = A::skolemize(&self.overlap.peak);
        ReplayTrace {
            path_a: trace_path(store, peak.clone(), &self.path_a),
            path_b: trace_path(store, peak, &self.path_b),
            joins_at: A::skolemize(&self.joins_at),
        }
    }
}

/// Replay two recorded paths from one peak against one join: the replay every
/// certificate check is, with the boundary supplied rather than read from an
/// [`Overlap`].
///
/// A boundary need not be a critical pair. Two adjacent applications commuted
/// past each other start at one peak and must reach one join, and no
/// enumerator found an overlap there; this is the replay that checks them, and
/// [`Tracelet::replay`] is this replay on a certificate's overlap peak.
///
/// # Specification
/// - ensures: positive exactly when, with `peak` and `joins_at` skolemized to
///   constants, every step of `path_a` and of `path_b` fires in order from the
///   skolemized peak and both land on the skolemized `joins_at`.
/// - ensures: negative when a step names an identifier `store` did not issue,
///   when a step's cell does not fire at its position, or when a path lands on
///   another term.
/// - ensures: a recorded [`CellId`] resolves as an insertion-order index into
///   `store`, never by cell content.
/// - panics: none.
/// - intension: retains no step.
///
/// # Adequacy
/// - hypothesis: L3 — one recorded path pair, replayed from its peak, is
///   separated by the join alone: positive against the join both paths reach,
///   negative against a retargeted join, and negative when one path is
///   truncated so it stops short of the join.
/// - witness: `tracelet::tests::replay_from_peak_separates_a_reached_join_from_a_missed_one`
#[inline]
#[must_use]
pub fn replay_from_peak<A>(
    store: &CellStore<A>,
    peak: &A::Cmd,
    joins_at: &A::Cmd,
    path_a: &[CellApp<A>],
    path_b: &[CellApp<A>],
) -> TraceletReplay
where
    A: CellAlphabet,
{
    let peak = A::skolemize(peak);
    let target = A::skolemize(joins_at);
    let ran_a = run_path(store, peak.clone(), path_a, &mut Discard);
    let ran_b = run_path(store, peak, path_b, &mut Discard);
    TraceletReplay::from(
        bool::from(reached(&ran_a, &target)) && bool::from(reached(&ran_b, &target)),
    )
}

/// Whether two certificates are replay-equivalent: the definition of when two
/// certificates are one transformation.
///
/// Two certificates sharing a peak and a join, each of which replays, denote
/// one transformation however their recorded paths differ: identity is
/// proof-irrelevant up to replay. The derived [`PartialEq`] on [`Tracelet`]
/// compares whole values and is finer; this is the certificate quotient.
///
/// # Specification
/// - ensures: positive exactly when the two share a peak and a join and both
///   [`Tracelet::replay`] positively over `store`; the recorded paths are
///   otherwise not compared.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a fused certificate is equivalent to itself and to the
///   structurally distinct certificate that takes the two-step path twice, and
///   a certificate that misses its join is not equivalent even to itself.
/// - witness: `tracelet::tests::a_certificate_is_replay_equivalent_to_itself`
/// - witness: `tracelet::tests::distinct_derivations_of_one_boundary_are_replay_equivalent`
/// - witness: `tracelet::tests::a_derivation_that_misses_its_boundary_is_not_self_equivalent`
#[inline]
#[must_use]
pub fn replay_equivalent<A>(
    a: &Tracelet<A>,
    b: &Tracelet<A>,
    store: &CellStore<A>,
) -> TraceletEquivalence
where
    A: CellAlphabet,
{
    TraceletEquivalence::from(
        a.overlap.peak == b.overlap.peak
            && a.joins_at == b.joins_at
            && bool::from(a.replay(store))
            && bool::from(b.replay(store)),
    )
}

quenchant_shape::reason_enum! {
    /// Why a critical pair carries no confluence certificate.
    pub mod confluence_join {
        /// The reason the two reducts are not joined.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// A reduct did not reach a normal form within the budget, so
            /// whether the pair joins is not decided.
            BudgetExhausted,
            /// Both reducts reached normal forms, and they differ: the pair
            /// diverges.
            NormalFormsDiffer,
        }
    }
}

/// The confluence certificate of a critical pair whose reducts join.
///
/// # Specification
/// - ensures: when both reducts normalize within `budget` to one term, the
///   certificate with `path_a` the left cell at the root then the left reduct's
///   normalization, `path_b` likewise for the right, and that normal form as
///   the join.
/// - provides: [`confluence_join::Absent::BudgetExhausted`] when a reduct does
///   not reach a normal form within `budget`;
///   [`confluence_join::Absent::NormalFormsDiffer`] when the normal forms
///   differ.
/// - fails: [`OverlapRefusal::NotAConfluence`] for a composition;
///   [`OverlapRefusal::UnissuedCell`] when `store` holds no cell under the
///   overlap's left identifier.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L1 — every certificate completion emits for a joinable pair is
///   this certificate, and replays over the completed store.
/// - witness: `tests::differential::completion_certificates_replay`
/// - witness: `tests::second_inhabitant::completion_orients_and_certifies_over_the_toy_alphabet`
#[inline]
pub fn confluence_tracelet<A>(
    overlap: &Overlap<A>,
    store: &CellStore<A>,
    budget: NormalizationBudget,
) -> Result<Maybe<Tracelet<A>, confluence_join::Absent>, OverlapRefusal>
where
    A: CellAlphabet,
{
    if overlap.kind != OverlapKind::Confluence {
        return Err(OverlapRefusal::NotAConfluence);
    }
    let left_reduct = overlap.left_reduct(store)?;
    let left = normalize(store, &left_reduct, budget);
    let right = normalize(store, &overlap.right_reduct(), budget);
    Ok(joined(overlap, left, right))
}

/// The confluence certificate of `overlap` from its two reducts'
/// normalizations, when they join.
///
/// # Specification
/// - requires: `left` and `right` normalize the overlap's left and right
///   reducts under one store and one budget.
/// - ensures: the certificate [`confluence_tracelet`] describes when both
///   normalizations reached one normal form.
/// - provides: [`confluence_join::Absent::BudgetExhausted`] when either was
///   stopped by its budget; [`confluence_join::Absent::NormalFormsDiffer`] when
///   the normal forms differ.
/// - panics: none.
pub fn joined<A>(
    overlap: &Overlap<A>,
    left: Normalization<A>,
    right: Normalization<A>,
) -> Maybe<Tracelet<A>, confluence_join::Absent>
where
    A: CellAlphabet,
{
    if bool::from(left.exhausted) || bool::from(right.exhausted) {
        return Maybe::Absent(confluence_join::Absent::BudgetExhausted);
    }
    if left.normal != right.normal {
        return Maybe::Absent(confluence_join::Absent::NormalFormsDiffer);
    }
    Maybe::Present(Tracelet {
        overlap: overlap.clone(),
        path_a: rooted_path(overlap.left, left.path),
        path_b: rooted_path(overlap.right, right.path),
        joins_at: left.normal,
    })
}

/// `cell` at the root, then `rest`.
///
/// # Specification
/// trivial.
fn rooted_path<A>(
    cell: CellId,
    rest: Vec<CellApp<A>>,
) -> Vec<CellApp<A>>
where
    A: CellAlphabet,
{
    let mut path = Vec::with_capacity(rest.len().saturating_add(1));
    path.push(CellApp {
        cell,
        at: A::root_position(),
    });
    path.extend(rest);
    path
}

/// Derive the fused cell of a composition and its certificate, inserting the
/// fused cell into `store`.
///
/// # Specification
/// - ensures: the identifier of the fused cell `peak ~> composite`, tagged with
///   the alphabet's derived orientation and provenance, and the certificate
///   whose `path_a` is the left cell at the root then the right cell at the
///   seam, whose `path_b` is the fused cell at the root, and whose join is the
///   composite.
/// - ensures: `store` gains the fused cell, or is unchanged when it already
///   holds that cell, whose identifier is then the one returned.
/// - fails: as [`Overlap::composite`] fails, before `store` is touched.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — the frame and successor cells fuse into a certificate of
///   a two-step and a one-step path that replays, over the sequent alphabet and
///   the toy alphabet; L2 — the fused cell agrees with the two-step derivation
///   on generated ground instances.
/// - witness: `tracelet::tests::a_fused_cell_certificate_replays`
/// - witness: `tests::second_inhabitant::the_enumerator_finds_the_toy_composition_overlap`
/// - witness: `tests::differential::fused_equals_two_step`
#[inline]
pub fn derive_fused<A>(
    overlap: &Overlap<A>,
    store: &mut CellStore<A>,
) -> Result<(CellId, Tracelet<A>), OverlapRefusal>
where
    A: CellAlphabet,
{
    let composite = overlap.composite(store)?;
    let fused = Cell::new(
        overlap.peak.clone(),
        composite.clone(),
        A::derived_orientation(),
        A::derived_provenance(),
    );
    let fused_id = store.insert(fused);
    let tracelet = Tracelet {
        overlap: overlap.clone(),
        path_a: alloc::vec![
            CellApp {
                cell: overlap.left,
                at: A::root_position(),
            },
            CellApp {
                cell: overlap.right,
                at: overlap.seam.clone(),
            },
        ],
        path_b: alloc::vec![CellApp {
            cell: fused_id,
            at: A::root_position(),
        }],
        joins_at: composite,
    };
    Ok((fused_id, tracelet))
}

/// Whether a replayed path reached `target`.
///
/// # Specification
/// trivial.
fn reached<A>(
    outcome: &ReplayPathOutcome<A>,
    target: &A::Cmd,
) -> TraceletReplay
where
    A: CellAlphabet,
{
    TraceletReplay::from(matches!(*outcome, ReplayPathOutcome::Reached(ref term) if term == target))
}

/// Where a replay puts the steps that fired.
trait StepRecord<A: CellAlphabet>
{
    /// Note that `application` fired, producing `result`.
    ///
    /// # Specification
    /// trivial.
    fn record(
        &mut self,
        application: &CellApp<A>,
        result: &A::Cmd,
    );
}

/// A record that keeps nothing: the verdict-only replay.
struct Discard;

impl<A: CellAlphabet> StepRecord<A> for Discard
{
    /// Keeps nothing.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn record(
        &mut self,
        _application: &CellApp<A>,
        _result: &A::Cmd,
    )
    {
    }
}

impl<A: CellAlphabet> StepRecord<A> for Vec<ReplayStep<A>>
{
    /// Appends the step and its result.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn record(
        &mut self,
        application: &CellApp<A>,
        result: &A::Cmd,
    )
    {
        self.push(ReplayStep {
            application: application.clone(),
            result: result.clone(),
        });
    }
}

/// Replay `path` from `start`, handing every step that fires to `record`.
///
/// # Specification
/// - ensures: [`ReplayPathOutcome::Reached`] with the final term when every
///   step fires in order; otherwise [`ReplayPathOutcome::Stuck`] at the first
///   step whose identifier `store` did not issue or whose cell does not fire at
///   its position, with that reason.
/// - ensures: `record` receives exactly the steps that fired, in order.
/// - panics: none.
fn run_path<A, R>(
    store: &CellStore<A>,
    start: A::Cmd,
    path: &[CellApp<A>],
    record: &mut R,
) -> ReplayPathOutcome<A>
where
    A: CellAlphabet,
    R: StepRecord<A>,
{
    let mut current = start;
    for step in path {
        let Maybe::Present(cell) = store.get(step.cell)
        else {
            return ReplayPathOutcome::Stuck {
                application: step.clone(),
                reason: StuckStep::UnissuedCell,
            };
        };
        let result = match rewrite_at(cell, &current, &step.at) {
            | Maybe::Present(result) => result,
            | Maybe::Absent(reason) => {
                return ReplayPathOutcome::Stuck {
                    application: step.clone(),
                    reason: StuckStep::DoesNotFire(reason),
                };
            },
        };
        record.record(step, &result);
        current = result;
    }
    ReplayPathOutcome::Reached(current)
}

/// Replay `path` from `start` and keep its observable execution.
///
/// # Specification
/// - ensures: [`ReplayPath::started_at`] is `start`; the steps and the outcome
///   are [`run_path`]'s over the same inputs.
/// - panics: none.
fn trace_path<A>(
    store: &CellStore<A>,
    start: A::Cmd,
    path: &[CellApp<A>],
) -> ReplayPath<A>
where
    A: CellAlphabet,
{
    let mut steps = Vec::with_capacity(path.len());
    let outcome = run_path(store, start.clone(), path, &mut steps);
    ReplayPath {
        started_at: start,
        steps,
        outcome,
    }
}

#[cfg(test)]
mod tests
{
    use gandr_theory_cell_complexes::CellProvenance;
    use gandr_theory_cell_complexes::CmdPat;
    use gandr_theory_cell_complexes::ConsPat;
    use gandr_theory_cell_complexes::Orientation;
    use gandr_theory_cell_complexes::Polarity;
    use gandr_theory_cell_complexes::PositionStep;
    use gandr_theory_cell_complexes::ProdPat;
    use gandr_theory_cell_complexes::Sym;
    use gandr_theory_cell_complexes::frame_defining_cell;
    use gandr_theory_cell_complexes_tools::Toy;
    use gandr_theory_cell_complexes_tools::ToyAlphabet;
    use gandr_theory_cell_complexes_tools::toy_cell;

    use super::*;
    use crate::overlap::enumerate_overlaps;

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

    /// The frame and (add-S) store after deriving their fused cell, and the
    /// fused cell's certificate.
    ///
    /// # Specification
    /// - panics: when the composition is not found or does not fuse, which is a
    ///   fixture defect.
    fn fused_fixture() -> (CellStore, Tracelet)
    {
        let mut store = CellStore::new();
        let frame = store.insert(frame_defining_cell(&Sym::new("Succ")));
        let add = store.insert(add_s());
        let composition = enumerate_overlaps(&store)
            .into_iter()
            .find(|o| o.kind == OverlapKind::Composition && o.left == frame && o.right == add)
            .expect("the composition overlap exists");
        let (_fused, tracelet) =
            derive_fused(&composition, &mut store).expect("the fused cell is derived");
        (store, tracelet)
    }

    #[test]
    fn a_fused_cell_certificate_replays()
    {
        let (store, tracelet) = fused_fixture();
        assert!(
            bool::from(tracelet.replay(&store)),
            "the fused≡two-step certificate replays"
        );
        assert_eq!(2_usize, tracelet.path_a.len(), "a two-step path");
        assert_eq!(1_usize, tracelet.path_b.len(), "a single fused step");
    }

    #[test]
    fn a_certificate_is_replay_equivalent_to_itself()
    {
        let (store, tracelet) = fused_fixture();
        assert!(
            bool::from(replay_equivalent(&tracelet, &tracelet, &store)),
            "a valid certificate is replay-equivalent to itself"
        );
    }

    #[test]
    fn distinct_derivations_of_one_boundary_are_replay_equivalent()
    {
        // Identity is replay equivalence, not structural equality: a second
        // certificate over the same boundary whose `path_b` is also the
        // two-step derivation is a structurally distinct derivation of one
        // transformation.
        let (store, fused_derivation) = fused_fixture();
        let two_step_derivation = Tracelet {
            overlap: fused_derivation.overlap.clone(),
            path_a: fused_derivation.path_a.clone(),
            path_b: fused_derivation.path_a.clone(),
            joins_at: fused_derivation.joins_at.clone(),
        };
        assert_ne!(
            fused_derivation, two_step_derivation,
            "the two certificates differ structurally"
        );
        assert!(
            bool::from(replay_equivalent(
                &fused_derivation,
                &two_step_derivation,
                &store
            )),
            "distinct derivations of one boundary are one certificate"
        );
    }

    #[test]
    fn a_derivation_that_misses_its_boundary_is_not_self_equivalent()
    {
        // Replay identity is falsifiable: a certificate whose paths do not
        // reach its join fails replay, so it is not equivalent even to itself.
        let (store, tracelet) = fused_fixture();
        let mut broken = tracelet;
        broken.joins_at = CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Zero", []),
            ConsPat::top(),
        );
        assert!(
            !bool::from(broken.replay(&store)),
            "the retargeted certificate no longer replays"
        );
        assert!(
            !bool::from(replay_equivalent(&broken, &broken, &store)),
            "a certificate that does not replay is not replay-equivalent, even to itself"
        );
    }

    #[test]
    fn replay_from_peak_separates_a_reached_join_from_a_missed_one()
    {
        // The boundary is supplied, not read from an overlap: the same path
        // pair from the same peak is positive against the join it reaches and
        // negative against any other.
        let (store, tracelet) = fused_fixture();
        let peak = &tracelet.overlap.peak;
        assert!(
            bool::from(replay_from_peak(
                &store,
                peak,
                &tracelet.joins_at,
                &tracelet.path_a,
                &tracelet.path_b,
            )),
            "both paths reach the recorded join"
        );
        let retargeted = CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Zero", []),
            ConsPat::top(),
        );
        assert!(
            !bool::from(replay_from_peak(
                &store,
                peak,
                &retargeted,
                &tracelet.path_a,
                &tracelet.path_b,
            )),
            "the same pair misses a retargeted join"
        );
        let (first_step, _) = tracelet.path_a.split_at(1);
        assert!(
            !bool::from(replay_from_peak(
                &store,
                peak,
                &tracelet.joins_at,
                first_step,
                &tracelet.path_b,
            )),
            "a path stopping one step short misses the join"
        );
        assert_eq!(
            tracelet.replay(&store),
            replay_from_peak(
                &store,
                peak,
                &tracelet.joins_at,
                &tracelet.path_a,
                &tracelet.path_b,
            ),
            "the certificate's replay is the peak-rooted replay of its boundary"
        );
    }

    #[test]
    fn every_stuck_step_carries_its_pinned_class()
    {
        let mut store = CellStore::new();
        let issued = store.insert(toy_cell(Toy::succ(Toy::var("x")), Toy::var("x")));
        let rows = [
            (
                CellApp {
                    cell: CellId::from(1_usize),
                    at: ToyAlphabet::root_position(),
                },
                StuckStep::UnissuedCell,
                "ill-formed query",
            ),
            (
                CellApp {
                    cell: issued,
                    at: ToyAlphabet::root_position(),
                },
                StuckStep::DoesNotFire(firing::Absent::NoMatch),
                "foreign answer",
            ),
            (
                CellApp {
                    cell: issued,
                    at: ToyAlphabet::position_at_path(&[PositionStep::from(0_usize)]),
                },
                StuckStep::DoesNotFire(firing::Absent::NoCommand(
                    gandr_theory_cell_complexes::command_subterm::Absent::OffTerm,
                )),
                "foreign answer",
            ),
        ];
        let mut covered = [false; 2];
        for (application, reason, class) in rows {
            let row = match reason {
                | StuckStep::UnissuedCell => 0,
                | StuckStep::DoesNotFire(_) => 1,
            };
            covered[row] = true;
            assert_eq!(
                trace_path(&store, Toy::zero(), core::slice::from_ref(&application)).outcome,
                ReplayPathOutcome::Stuck {
                    application,
                    reason
                },
                "{class} keeps {reason:?}",
            );
        }
        assert_eq!(covered, [true; 2]);
    }
}
