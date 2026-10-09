//! Budgeted completion: its ceilings, decline and resume, and the typed
//! declines of the supplied-overlap seam.

use gandr_theory_cell_complexes::CellId;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::ConsPat;
use gandr_theory_cell_complexes::Subst;
use gandr_theory_cell_complexes::Sym;
use gandr_theory_coherent_resolutions::BatchIndex;
use gandr_theory_coherent_resolutions::CompletionBudget;
use gandr_theory_coherent_resolutions::CompletionCellBudget;
use gandr_theory_coherent_resolutions::CompletionOutcome;
use gandr_theory_coherent_resolutions::CompletionStepBudget;
use gandr_theory_coherent_resolutions::DeclineReason;
use gandr_theory_coherent_resolutions::NormalizationBudget;
use gandr_theory_coherent_resolutions::Overlap;
use gandr_theory_coherent_resolutions::OverlapIndex;
use gandr_theory_coherent_resolutions::OverlapKind;
use gandr_theory_coherent_resolutions::SuppliedOverlapError;
use gandr_theory_coherent_resolutions::complete;
use gandr_theory_coherent_resolutions::complete_with_overlap_source;
use gandr_theory_coherent_resolutions::scheduled_confluence_batches;
use quenchant_shape::shape::Maybe;

use crate::fixture::ground_rule;
use crate::fixture::independent_rule_clusters;
use crate::fixture::overlapping_rules;

/// A budget of `steps` critical pairs and `cells` cells, with a generous
/// normalization budget.
///
/// # Specification
/// trivial.
fn budget(
    steps: CompletionStepBudget,
    cells: CompletionCellBudget,
) -> CompletionBudget
{
    CompletionBudget::new(steps, cells, NormalizationBudget::from(64_usize))
}

/// The budget the supplied-input witnesses run under: ample for the fixture.
///
/// # Specification
/// trivial.
fn ample() -> CompletionBudget
{
    budget(
        CompletionStepBudget::from(64_usize),
        CompletionCellBudget::from(16_usize),
    )
}

/// The budget a resume runs under: far beyond anything the fixture needs.
///
/// # Specification
/// trivial.
fn vast() -> CompletionBudget
{
    CompletionBudget::new(
        CompletionStepBudget::from(4_096_usize),
        CompletionCellBudget::from(4_096_usize),
        NormalizationBudget::from(4_096_usize),
    )
}

/// The overlapping fixture's first scheduled confluence overlap.
///
/// # Specification
/// - panics: when the fixture schedules none, which is a fixture defect.
fn first_scheduled(store: &CellStore) -> Overlap
{
    scheduled_confluence_batches(store)
        .into_iter()
        .flatten()
        .next()
        .expect("the fixture schedules one confluence overlap")
}

/// The first scheduled overlap rebuilt through the supplied-overlap
/// constructor under `unifier`.
///
/// # Specification
/// - panics: when the fixture's cells are missing, which is a fixture defect.
fn rebuilt(
    store: &CellStore,
    unifier: Subst,
) -> Overlap
{
    let scheduled = first_scheduled(store);
    let (Maybe::Present(left), Maybe::Present(right)) =
        (store.get(scheduled.left), store.get(scheduled.right))
    else {
        panic!("both cells of the scheduled overlap are stored");
    };
    Overlap::from_supplied_confluence(
        (scheduled.left, left),
        (scheduled.right, right),
        unifier,
        scheduled.seam,
    )
}

/// The first scheduled overlap supplied with an empty unifier, under which
/// its right leg misses the peak.
///
/// # Specification
/// - panics: when the fixture's cells are missing, which is a fixture defect.
fn non_unifying(store: &CellStore) -> Overlap
{
    rebuilt(store, Subst::new())
}

/// The pending residue of a decline one step into the leading batch: that
/// batch without its first member, then every later batch unchanged.
///
/// # Specification
/// - panics: when the schedule is empty, which is a fixture defect.
fn residue_after_leading_step(scheduled: &[Vec<Overlap>]) -> Vec<Vec<Overlap>>
{
    let (leading, later) = scheduled
        .split_first()
        .expect("the schedule has a leading batch");
    let mut residue = Vec::with_capacity(scheduled.len());
    residue.push(leading.iter().skip(1_usize).cloned().collect());
    residue.extend(later.iter().cloned());
    residue
}

#[test]
fn completion_processes_within_budget()
{
    let outcome = complete(overlapping_rules(), ample());
    assert!(
        bool::from(outcome.is_completed()),
        "the small system completes within budget"
    );
}

#[test]
fn supplied_overlap_validation_returns_typed_declines()
{
    let store = overlapping_rules();
    let valid = first_scheduled(&store);
    let origin = (BatchIndex::from(0_usize), OverlapIndex::from(0_usize));

    let accepted = rebuilt(&store, valid.unifier.clone());
    assert_eq!(
        valid, accepted,
        "the constructor rebuilds the enumerator's overlap from its own evidence"
    );
    let outcome =
        complete_with_overlap_source(store.clone(), ample(), move |_| vec![vec![accepted]]);
    assert!(
        bool::from(outcome.is_completed()),
        "the enumerator's own overlap is valid supplied input"
    );

    let mut unknown_left = valid.clone();
    unknown_left.left = CellId::from(usize::MAX);
    let expected = unknown_left.clone();
    let outcome =
        complete_with_overlap_source(store.clone(), ample(), move |_| vec![vec![unknown_left]]);
    let CompletionOutcome::Declined {
        reason:
            DeclineReason::InvalidSuppliedOverlap(SuppliedOverlapError::UnknownLeftCell {
                batch,
                overlap,
                cell,
            }),
        pending,
        ..
    } = outcome
    else {
        panic!("an unissued supplied left identifier is a typed decline");
    };
    assert_eq!(origin, (batch, overlap), "the decline names the entry");
    assert_eq!(
        CellId::from(usize::MAX),
        cell,
        "and the unissued identifier"
    );
    assert_eq!(
        vec![vec![expected]],
        pending,
        "and carries the supplied work"
    );

    let mut unknown_right = valid.clone();
    unknown_right.right = CellId::from(usize::MAX);
    let expected = unknown_right.clone();
    let outcome =
        complete_with_overlap_source(store.clone(), ample(), move |_| vec![vec![unknown_right]]);
    let CompletionOutcome::Declined {
        reason:
            DeclineReason::InvalidSuppliedOverlap(SuppliedOverlapError::UnknownRightCell {
                batch,
                overlap,
                cell,
            }),
        pending,
        ..
    } = outcome
    else {
        panic!("an unissued supplied right identifier is a typed decline");
    };
    assert_eq!(origin, (batch, overlap), "the decline names the entry");
    assert_eq!(
        CellId::from(usize::MAX),
        cell,
        "and the unissued identifier"
    );
    assert_eq!(
        vec![vec![expected]],
        pending,
        "and carries the supplied work"
    );

    let mut composition = valid;
    composition.kind = OverlapKind::Composition;
    let outcome = complete_with_overlap_source(store, ample(), move |_| vec![vec![composition]]);
    let CompletionOutcome::Declined {
        reason:
            DeclineReason::InvalidSuppliedOverlap(SuppliedOverlapError::NonConfluence {
                batch,
                overlap,
            }),
        ..
    } = outcome
    else {
        panic!("a supplied composition is a typed decline");
    };
    assert_eq!(origin, (batch, overlap), "the decline names the entry");
}

// The non-unifying refusal has three witnesses of its own, because it widens
// the invalid-input domain at three paths: initial validation, terminal
// resume, and the revalidation of a budget decline's pending work.

#[test]
fn supplied_non_unifying_decline_is_typed()
{
    let store = overlapping_rules();
    let supplied = non_unifying(&store);
    let expected = supplied.clone();
    let outcome = complete_with_overlap_source(store, ample(), move |_| vec![vec![supplied]]);
    let CompletionOutcome::Declined {
        reason:
            DeclineReason::InvalidSuppliedOverlap(SuppliedOverlapError::NonUnifyingSubstitution {
                batch,
                overlap,
            }),
        derived,
        certificates,
        pending,
        ..
    } = outcome
    else {
        panic!("a supplied unifier whose legs miss the peak is a typed decline");
    };
    assert!(
        derived.is_empty(),
        "validation declines before any cell is derived"
    );
    assert!(
        certificates.is_empty(),
        "and before any certificate is emitted"
    );
    assert_eq!(
        (BatchIndex::from(0_usize), OverlapIndex::from(0_usize)),
        (batch, overlap),
        "the decline names the entry"
    );
    assert_eq!(
        vec![vec![expected]],
        pending,
        "and carries the supplied work"
    );
}

#[test]
fn a_supplied_overlap_naming_another_left_cell_is_declined()
{
    // An entry whose left identifier names a stored cell other than the one
    // its peak was built from: the right leg still meets the peak, and only
    // reading the stored left cell's left-hand side catches the entry.
    let mut store = overlapping_rules();
    let elsewhere = store.insert(ground_rule(
        &Sym::new("Nil"),
        &Sym::new("g"),
        ConsPat::meta("alpha"),
    ));
    let mut retargeted = first_scheduled(&store);
    retargeted.left = elsewhere;
    let outcome = complete_with_overlap_source(store, ample(), move |_| vec![vec![retargeted]]);
    let CompletionOutcome::Declined {
        reason:
            DeclineReason::InvalidSuppliedOverlap(SuppliedOverlapError::NonUnifyingSubstitution {
                batch,
                overlap,
            }),
        derived,
        ..
    } = outcome
    else {
        panic!("a left leg that misses the peak is a typed decline");
    };
    assert_eq!(
        (BatchIndex::from(0_usize), OverlapIndex::from(0_usize)),
        (batch, overlap),
        "the decline names the entry"
    );
    assert!(derived.is_empty(), "and comes before any work");
}

#[test]
fn non_unifying_supplied_decline_is_terminal_on_resume()
{
    let store = overlapping_rules();
    let supplied = non_unifying(&store);
    let outcome = complete_with_overlap_source(store, ample(), move |_| vec![vec![supplied]]);
    let resumed = outcome.clone().resume(vast());
    assert_eq!(
        outcome, resumed,
        "a non-unifying supplied decline remains a typed terminal refusal"
    );
}

#[test]
fn budget_decline_revalidates_non_unifying_pending_overlap()
{
    let store = overlapping_rules();
    let supplied = non_unifying(&store);
    let expected = supplied.clone();
    let outcome = CompletionOutcome::Declined {
        store,
        derived: Vec::new(),
        certificates: Vec::new(),
        pending: vec![vec![supplied]],
        reason: DeclineReason::StepBudget,
    };
    let CompletionOutcome::Declined {
        reason:
            DeclineReason::InvalidSuppliedOverlap(SuppliedOverlapError::NonUnifyingSubstitution {
                batch,
                overlap,
            }),
        pending,
        ..
    } = outcome.resume(vast())
    else {
        panic!("resume revalidates malformed pending work before completing it");
    };
    assert_eq!(
        (BatchIndex::from(0_usize), OverlapIndex::from(0_usize)),
        (batch, overlap),
        "the decline names the entry"
    );
    assert_eq!(
        vec![vec![expected]],
        pending,
        "and carries the pending work"
    );
}

#[test]
fn invalid_supplied_decline_is_terminal_on_resume()
{
    let store = overlapping_rules();
    let mut unknown = first_scheduled(&store);
    unknown.right = CellId::from(usize::MAX);
    let outcome = complete_with_overlap_source(store, ample(), move |_| vec![vec![unknown]]);
    let resumed = outcome.clone().resume(vast());
    assert_eq!(
        outcome, resumed,
        "invalid supplied input remains a typed terminal refusal"
    );
}

#[test]
fn cell_budget_decline_preserves_pending_work()
{
    // The cell ceiling is reached at the leading batch's second overlap, the
    // first that diverges, so the decline carries the same residue a one-step
    // budget does and differs from it only in its reason.
    let scheduled = scheduled_confluence_batches(&independent_rule_clusters());
    let outcome = complete(
        independent_rule_clusters(),
        budget(
            CompletionStepBudget::from(64_usize),
            CompletionCellBudget::from(6_usize),
        ),
    );
    let CompletionOutcome::Declined {
        reason,
        pending,
        derived,
        certificates,
        ..
    } = outcome
    else {
        panic!("the cell ceiling must decline before inserting a derived rule");
    };
    assert_eq!(
        DeclineReason::CellBudget,
        reason,
        "the cell ceiling, not the step ceiling, stopped this run"
    );
    assert!(
        derived.is_empty(),
        "the ceiling is reached before the divergence is oriented, so nothing was derived"
    );
    assert_eq!(
        1_usize,
        certificates.len(),
        "the joinable leading pair was certified before the ceiling was reached"
    );
    assert_eq!(
        residue_after_leading_step(&scheduled),
        pending,
        "the decline keeps the rest of the leading batch and every later batch unchanged"
    );
}

#[test]
fn decline_resume_matches_uninterrupted_completion()
{
    let scheduled = scheduled_confluence_batches(&independent_rule_clusters());
    assert_eq!(
        2_usize,
        scheduled.len(),
        "the fixture schedules its six critical pairs into two independent batches"
    );
    assert!(
        scheduled
            .first()
            .is_some_and(|batch| batch.len() == 3_usize),
        "the leading batch holds three overlaps, so a one-step budget stops inside it"
    );
    let uninterrupted = complete(
        independent_rule_clusters(),
        budget(
            CompletionStepBudget::from(64_usize),
            CompletionCellBudget::from(64_usize),
        ),
    );
    let declined = complete(
        independent_rule_clusters(),
        budget(
            CompletionStepBudget::from(1_usize),
            CompletionCellBudget::from(64_usize),
        ),
    );
    let CompletionOutcome::Declined {
        reason,
        ref pending,
        ref derived,
        ..
    } = declined
    else {
        panic!("a one-step budget must decline inside the leading batch");
    };
    assert_eq!(
        DeclineReason::StepBudget,
        reason,
        "the step ceiling stopped this run"
    );
    assert!(
        derived.is_empty(),
        "the one step taken was the joinable leading pair, which derives nothing"
    );
    // One step was taken, so the residue is the leading batch without its
    // first member, then every later batch: a partition that drops the
    // interrupted overlap, or the unfinished batch, fails here.
    assert_eq!(
        residue_after_leading_step(&scheduled),
        *pending,
        "the decline carries the rest of the leading batch and every later batch unchanged"
    );
    let resumed = declined.resume(budget(
        CompletionStepBudget::from(64_usize),
        CompletionCellBudget::from(64_usize),
    ));
    assert!(
        bool::from(resumed.is_completed()),
        "resuming from the carried batches finishes the worklist"
    );
    assert!(
        !uninterrupted.derived().is_empty(),
        "the fixture derives cells, so the comparison reaches past the first batch"
    );
    assert_eq!(
        uninterrupted, resumed,
        "and reaches the uninterrupted outcome: same store, derived cells and certificates"
    );
}

#[test]
fn a_starved_budget_declines_with_pending()
{
    let initial = overlapping_rules();
    let expected = scheduled_confluence_batches(&initial);
    let outcome = complete(
        initial,
        budget(
            CompletionStepBudget::from(0_usize),
            CompletionCellBudget::from(16_usize),
        ),
    );
    let CompletionOutcome::Declined {
        reason, pending, ..
    } = outcome
    else {
        panic!("a zero step budget must decline");
    };
    assert_eq!(
        DeclineReason::StepBudget,
        reason,
        "the step ceiling was zero"
    );
    assert_eq!(
        expected, pending,
        "the decline carries the schedule in batch and first-appearance order"
    );
}
