//! The fused cell against the two-step derivation it replaces, certificate
//! replay and what it is invariant under, the completion budget's decline, and
//! the η polarity pin.
//!
//! The fused cell a composition derives is, by construction, the two-step
//! composite of its parts, so over generated ground configurations firing it
//! must agree with firing the two constituent cells in sequence. A
//! disagreement is a defect in matching, substitution or splicing, never a
//! tolerated divergence: the concurrency theorem of compositional rewriting
//! is adopted as a property test rather than implemented as proof machinery.

use gandr_theory_cell_complexes::Cell;
use gandr_theory_cell_complexes::CellId;
use gandr_theory_cell_complexes::CellProvenance;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::CmdPat;
use gandr_theory_cell_complexes::ConsPat;
use gandr_theory_cell_complexes::EtaKind;
use gandr_theory_cell_complexes::Orientation;
use gandr_theory_cell_complexes::Polarity;
use gandr_theory_cell_complexes::Pos;
use gandr_theory_cell_complexes::ProdPat;
use gandr_theory_cell_complexes::Sym;
use gandr_theory_cell_complexes::frame_defining_cell;
use gandr_theory_coherent_resolutions::CompletionBudget;
use gandr_theory_coherent_resolutions::CompletionCellBudget;
use gandr_theory_coherent_resolutions::CompletionOutcome;
use gandr_theory_coherent_resolutions::CompletionStepBudget;
use gandr_theory_coherent_resolutions::DeclineReason;
use gandr_theory_coherent_resolutions::NormalizationBudget;
use gandr_theory_coherent_resolutions::Overlap;
use gandr_theory_coherent_resolutions::OverlapKind;
use gandr_theory_coherent_resolutions::ReplayPathOutcome;
use gandr_theory_coherent_resolutions::StuckStep;
use gandr_theory_coherent_resolutions::Tracelet;
use gandr_theory_coherent_resolutions::complete;
use gandr_theory_coherent_resolutions::derive_fused;
use gandr_theory_coherent_resolutions::enumerate_overlaps;
use gandr_theory_coherent_resolutions::firing;
use gandr_theory_coherent_resolutions::rewrite_at;
use proptest::prelude::*;
use quenchant_shape::shape::Maybe;

use crate::fixture::add_s;
use crate::fixture::joinable_store;
use crate::fixture::peano_store;
use crate::fixture::rule;

/// The Peano store's composition of the frame cell (id 0) into (add-S)
/// (id 2).
///
/// # Specification
/// - panics: when the store has no such overlap, which is a fixture defect.
fn frame_into_add(store: &CellStore) -> Overlap
{
    enumerate_overlaps(store)
        .into_iter()
        .find(|candidate| {
            candidate.kind == OverlapKind::Composition
                && candidate.left == CellId::from(0_usize)
                && candidate.right == CellId::from(2_usize)
        })
        .expect("the frame ∘ add-S composition overlap exists")
}

/// The fused commutation cell `⟨w | Succ⁻(add(n; α))⟩ ~> ⟨w | add(n;
/// Succ⁻(α))⟩`, built from the composition's peak and composite.
///
/// # Specification
/// - panics: when the composite cannot be formed, which is a fixture defect.
fn fused_commutation_cell() -> Cell
{
    let base = peano_store();
    let overlap = frame_into_add(&base);
    let composite = overlap.composite(&base).expect("the composite is formed");
    Cell::new(
        overlap.peak,
        composite,
        Orientation::CompletionDerived,
        CellProvenance::DerivedByCompletion,
    )
}

/// The Peano store after deriving its fused cell, and the certificate.
///
/// # Specification
/// - panics: when the fused cell is not derived, which is a fixture defect.
fn fusion_fixture() -> (CellStore, Tracelet)
{
    let mut store = peano_store();
    let overlap = frame_into_add(&store);
    let (_id, tracelet) = derive_fused(&overlap, &mut store).expect("the fused cell is derived");
    (store, tracelet)
}

/// Generated Peano numerals `Succ^k(Zero)`, `k` below 64.
///
/// # Specification
/// trivial.
fn nat() -> impl Strategy<Value = ProdPat>
{
    proptest::collection::vec(Just(()), 0 .. 64_usize).prop_map(|successors| {
        let mut numeral = ProdPat::ctor("Zero", []);
        for () in successors {
            numeral = ProdPat::ctor("Succ", [numeral]);
        }
        numeral
    })
}

/// A completion budget with the given step ceiling, room for the joinable
/// system's cells, and a generous normalization budget.
///
/// # Specification
/// trivial.
fn joinable_budget(steps: CompletionStepBudget) -> CompletionBudget
{
    CompletionBudget::new(
        steps,
        CompletionCellBudget::from(32_usize),
        NormalizationBudget::from(128_usize),
    )
}

#[test]
fn the_fused_cell_certificate_replays_over_the_store()
{
    let (store, tracelet) = fusion_fixture();
    assert!(
        bool::from(tracelet.replay(&store)),
        "the fused ≡ two-step certificate replays"
    );
}

#[test]
fn replay_is_pure_over_a_fixed_certificate_and_store()
{
    let (store, tracelet) = fusion_fixture();
    let first = tracelet.replay_trace(&store);
    let second = tracelet.replay_trace(&store);
    #[expect(
        clippy::redundant_clone,
        reason = "the witness replays over a store that is a distinct clone of the original"
    )]
    let over_clone = tracelet.replay_trace(&store.clone());
    let fired = |steps: &[gandr_theory_coherent_resolutions::ReplayStep]| {
        steps
            .iter()
            .map(|step| step.application.clone())
            .collect::<Vec<_>>()
    };
    assert_eq!(
        tracelet.path_a,
        fired(&first.path_a.steps),
        "the first path fires both recorded applications"
    );
    assert_eq!(
        tracelet.path_b,
        fired(&first.path_b.steps),
        "the second path fires the recorded fused application"
    );
    assert_eq!(
        ReplayPathOutcome::Reached(first.joins_at.clone()),
        first.path_a.outcome,
        "the first path reaches the skolemized join"
    );
    assert_eq!(
        ReplayPathOutcome::Reached(first.joins_at.clone()),
        first.path_b.outcome,
        "the second path reaches the skolemized join"
    );
    assert_eq!(first, second, "repeating replay gives the same trace");
    assert_eq!(first, over_clone, "cloning the store keeps the trace");
    assert_eq!(
        tracelet.replay(&store),
        first.verdict(),
        "the trace verdict agrees with the non-tracing replay"
    );
}

#[test]
fn append_only_store_extension_preserves_replay_trace()
{
    let (mut store, tracelet) = fusion_fixture();
    let before = tracelet.replay_trace(&store);
    store.insert(rule(
        CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("Unrelated", []),
            ConsPat::top(),
        ),
        CmdPat::cut(
            Polarity::Positive,
            ProdPat::ctor("UnrelatedResult", []),
            ConsPat::top(),
        ),
    ));
    let after = tracelet.replay_trace(&store);
    assert_eq!(
        before, after,
        "appending an unrelated cell keeps an indexed certificate's replay"
    );
    assert_eq!(
        tracelet.replay(&store),
        after.verdict(),
        "and the trace verdict still agrees with the non-tracing replay"
    );
}

#[test]
fn store_permutation_is_not_an_indexed_certificate_invariant()
{
    let (store, tracelet) = fusion_fixture();
    let canonical = tracelet.replay_trace(&store);
    let cells: Vec<Cell> = store.iter().map(|(_id, cell)| cell.clone()).collect();
    assert_eq!(
        4_usize,
        cells.len(),
        "the fixture has three primitive cells and one fused cell"
    );
    let mut permuted = CellStore::new();
    for index in [2_usize, 1_usize, 0_usize, 3_usize] {
        let cell = cells.get(index).expect("the permutation index is in range");
        permuted.insert(cell.clone());
    }
    assert!(
        store
            .iter()
            .all(|(_id, cell)| permuted.iter().any(|(_other, other)| other == cell)),
        "the permuted store holds the same cells"
    );
    let replayed = tracelet.replay_trace(&permuted);
    assert_ne!(
        canonical.path_a, replayed.path_a,
        "rebinding identifier zero changes the first path"
    );
    assert_eq!(
        canonical.path_b, replayed.path_b,
        "the fused cell keeps identifier three, so the second path is unchanged"
    );
    assert_eq!(
        ReplayPathOutcome::Stuck {
            application: tracelet
                .path_a
                .first()
                .expect("the two-step path has a first application")
                .clone(),
            reason: StuckStep::DoesNotFire(firing::Absent::NoMatch),
        },
        replayed.path_a.outcome,
        "replay stops at the first application the permutation rebound, which no longer matches"
    );
    assert!(
        !bool::from(replayed.verdict()),
        "an indexed certificate is not invariant under store permutation"
    );
    assert_eq!(
        tracelet.replay(&permuted),
        replayed.verdict(),
        "and the tracing and non-tracing replays agree under the permutation"
    );
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(4_096_u32))]

    /// Firing the fused commutation cell once agrees with firing the frame
    /// cell then (add-S), on every generated ground instance
    /// `⟨Succ^a(Zero) | Succ⁻(add(Succ^b(Zero); ★))⟩`.
    #[test]
    fn fused_equals_two_step(a in nat(), b in nat())
    {
        let fused = fused_commutation_cell();
        let frame = frame_defining_cell(&Sym::new("Succ"));
        let successor = add_s();
        let instance = CmdPat::cut(
            Polarity::Positive,
            a,
            ConsPat::frame("Succ", ConsPat::op("add", [b], ConsPat::top())),
        );
        let via_fused = rewrite_at(&fused, &instance, &Pos::root());
        let via_two_step = rewrite_at(&frame, &instance, &Pos::root())
            .and_then(|after_frame| rewrite_at(&successor, &after_frame, &Pos::root()));
        prop_assert!(
            matches!(via_fused, Maybe::Present(_)),
            "the fused cell fires on the instance"
        );
        prop_assert_eq!(
            via_fused,
            via_two_step,
            "the fused cell and the two-step derivation agree"
        );
    }
}

#[test]
fn completion_certificates_replay()
{
    let outcome = complete(
        joinable_store(),
        joinable_budget(CompletionStepBudget::from(64_usize)),
    );
    assert!(
        bool::from(outcome.is_completed()),
        "the joinable system completes"
    );
    assert!(
        !outcome.certificates().is_empty(),
        "a joinable critical pair emits a certificate"
    );
    for certificate in outcome.certificates() {
        assert!(
            bool::from(certificate.replay(outcome.store())),
            "every coherence certificate replays"
        );
    }
}

#[test]
fn a_starved_completion_declines_with_what_was_left()
{
    // The joinable system has two confluence overlaps, (r1, r2) and (r2, r1);
    // a one-step budget cannot drain the worklist, so completion declines
    // carrying the rest.
    let outcome = complete(
        joinable_store(),
        joinable_budget(CompletionStepBudget::from(1_usize)),
    );
    let CompletionOutcome::Declined {
        reason, pending, ..
    } = outcome
    else {
        panic!("a one-step budget over a two-overlap system must decline");
    };
    assert_eq!(DeclineReason::StepBudget, reason, "the step ceiling bit");
    assert!(
        !pending.is_empty(),
        "the pending overlaps are carried, not dropped"
    );
}

#[test]
fn eta_at_the_wrong_polarity_is_rejected()
{
    // A data-η cell requires a positive cut and must not fire at a negative
    // one; a codata-η cell requires a negative cut and fires there.
    let negative_cut = CmdPat::cut(Polarity::Negative, ProdPat::meta("x"), ConsPat::meta("a"));
    let eta = |kind| -> Cell {
        Cell::new(
            negative_cut.clone(),
            negative_cut.clone(),
            Orientation::PolarityDerived,
            CellProvenance::Eta(kind),
        )
    };
    assert_eq!(
        Maybe::Absent(firing::Absent::Refused),
        rewrite_at(&eta(EtaKind::Data), &negative_cut, &Pos::root()),
        "data-η is refused at a negative cut"
    );
    assert_eq!(
        Maybe::Present(negative_cut.clone()),
        rewrite_at(&eta(EtaKind::Codata), &negative_cut, &Pos::root()),
        "codata-η is admitted at a negative cut"
    );
}
