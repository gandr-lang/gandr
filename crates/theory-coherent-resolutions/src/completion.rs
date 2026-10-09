//! Budgeted Knuth–Bendix and Squier completion, generic over the
//! [`CellAlphabet`].
//!
//! [`complete`] runs confluence completion over a store. It normalizes both
//! reducts of every confluence critical pair; a pair that joins contributes a
//! coherence certificate, and a pair that diverges is oriented by the
//! alphabet's reduction order into a derived cell whose own critical pairs
//! join the worklist. Termination is the [`CompletionBudget`]'s: reaching the
//! step or cell ceiling returns a [`CompletionOutcome::Declined`] carrying the
//! pending batches, never a divergence or a panic, and
//! [`CompletionOutcome::resume`] continues from exactly that state.
//!
//! Three obstructions are left in place rather than guessed at: a reduct the
//! normalization budget does not bring to a normal form, a divergence the
//! reduction order does not orient, and a derived cell the store already
//! holds.
//!
//! [`complete_with_overlap_source`] is the seam through which a caller's own
//! matcher seeds the worklist with confluence overlaps this crate's generic
//! unifier would not find, without this crate depending on the matcher. The
//! supplied overlaps are validated before any of them reaches the loop, and an
//! invalid one declines with its position.
//!
//! Fusion is the separate [`crate::derive_fused`] on a composition overlap;
//! completion here is the confluence engine.

use alloc::collections::VecDeque;
use alloc::vec::Vec;

use anodized::spec;
use gandr_theory_cell_complexes::Cell;
use gandr_theory_cell_complexes::CellAlphabet;
use gandr_theory_cell_complexes::CellId;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::SequentAlphabet;
use quenchant_shape::shape::Maybe;

use crate::boundary::BatchIndex;
use crate::boundary::CompletionCellBudget;
use crate::boundary::CompletionStatus;
use crate::boundary::CompletionStepBudget;
use crate::boundary::NormalizationBudget;
use crate::boundary::OverlapIndex;
use crate::overlap::Overlap;
use crate::overlap::OverlapKind;
use crate::overlap::OverlapSupport;
use crate::overlap::enumerate_overlaps;
use crate::rewrite::normalize;
use crate::tracelet::Tracelet;
use crate::tracelet::joined;

/// The ceilings that make completion terminate with a decline rather than
/// diverge.
///
/// Each is the most admitted, not the point of failure: a run that needs no
/// more than a ceiling completes under it.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct CompletionBudget
{
    /// The most critical pairs one run processes.
    pub max_steps: CompletionStepBudget,
    /// The most cells the store may hold before completion declines to insert
    /// another.
    pub max_cells: CompletionCellBudget,
    /// The step budget of each normalization.
    pub norm_budget: NormalizationBudget,
}

impl CompletionBudget
{
    /// A budget from its three ceilings.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        max_steps: CompletionStepBudget,
        max_cells: CompletionCellBudget,
        norm_budget: NormalizationBudget,
    ) -> Self
    {
        Self {
            max_steps,
            max_cells,
            norm_budget,
        }
    }
}

/// Why completion declined.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum DeclineReason
{
    /// The step ceiling was reached with work pending.
    StepBudget,
    /// The cell ceiling was reached by a cell completion would have inserted.
    CellBudget,
    /// A supplied overlap broke the completion input contract.
    InvalidSuppliedOverlap(SuppliedOverlapError),
}

/// The first invalid entry of a supplied overlap worklist, in batch order.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum SuppliedOverlapError
{
    /// The entry is a composition, and completion reads confluences.
    NonConfluence
    {
        /// The batch holding the entry.
        batch: BatchIndex,
        /// The entry's position in its batch.
        overlap: OverlapIndex,
    },
    /// The store holds no cell under the entry's left identifier.
    UnknownLeftCell
    {
        /// The batch holding the entry.
        batch: BatchIndex,
        /// The entry's position in its batch.
        overlap: OverlapIndex,
        /// The unissued identifier.
        cell: CellId,
    },
    /// The store holds no cell under the entry's right identifier.
    UnknownRightCell
    {
        /// The batch holding the entry.
        batch: BatchIndex,
        /// The entry's position in its batch.
        overlap: OverlapIndex,
        /// The unissued identifier.
        cell: CellId,
    },
    /// The supplied unifier does not make the two legs meet at one peak.
    NonUnifyingSubstitution
    {
        /// The batch holding the entry.
        batch: BatchIndex,
        /// The entry's position in its batch.
        overlap: OverlapIndex,
    },
}

impl core::fmt::Display for SuppliedOverlapError
{
    /// Names the invalid entry and what is wrong with it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        let (batch, overlap) = match *self {
            | Self::NonConfluence { batch, overlap }
            | Self::UnknownLeftCell { batch, overlap, .. }
            | Self::UnknownRightCell { batch, overlap, .. }
            | Self::NonUnifyingSubstitution { batch, overlap } => (batch, overlap),
        };
        write!(
            f,
            "supplied overlap {} of batch {}: ",
            usize::from(overlap),
            usize::from(batch)
        )?;
        match *self {
            | Self::NonConfluence { .. } => f.write_str("a composition, not a confluence"),
            | Self::UnknownLeftCell { cell, .. } => {
                write!(f, "the store holds no left cell {}", usize::from(cell))
            },
            | Self::UnknownRightCell { cell, .. } => {
                write!(f, "the store holds no right cell {}", usize::from(cell))
            },
            | Self::NonUnifyingSubstitution { .. } => {
                f.write_str("the unifier does not make both legs meet the peak")
            },
        }
    }
}

impl core::error::Error for SuppliedOverlapError
{
}

/// The outcome of completion: a completed store, or a decline carrying what
/// was left.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CompletionOutcome<A: CellAlphabet = SequentAlphabet>
{
    /// Completion processed the whole worklist within budget.
    Completed
    {
        /// The final store: the original cells and every derived one.
        store: CellStore<A>,
        /// The derived cells, in derivation order.
        derived: Vec<CellId>,
        /// The certificates of the critical pairs that joined.
        certificates: Vec<Tracelet<A>>,
    },
    /// Completion declined at a ceiling or on invalid supplied input.
    Declined
    {
        /// The store as of the decline.
        store: CellStore<A>,
        /// The cells derived before the decline.
        derived: Vec<CellId>,
        /// The certificates emitted before the decline.
        certificates: Vec<Tracelet<A>>,
        /// The batches left unprocessed, the interrupted one first.
        pending: Vec<Vec<Overlap<A>>>,
        /// The ceiling reached, or the invalid supplied entry.
        reason: DeclineReason,
    },
}

impl<A: CellAlphabet> CompletionOutcome<A>
{
    /// The store, completed or as of the decline.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn store(&self) -> &CellStore<A>
    {
        match *self {
            | Self::Completed { ref store, .. } | Self::Declined { ref store, .. } => store,
        }
    }

    /// The certificates emitted.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn certificates(&self) -> &[Tracelet<A>]
    {
        match *self {
            | Self::Completed {
                ref certificates, ..
            }
            | Self::Declined {
                ref certificates, ..
            } => certificates,
        }
    }

    /// The derived cells.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn derived(&self) -> &[CellId]
    {
        match *self {
            | Self::Completed { ref derived, .. } | Self::Declined { ref derived, .. } => derived,
        }
    }

    /// Whether completion processed its whole worklist.
    ///
    /// # Specification
    /// - ensures: positive exactly for [`CompletionOutcome::Completed`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a small overlapping system completes, and a run
    ///   declined then resumed completes. Zero-budget and invalid-input
    ///   declines remain negative. Swapping variants or treating pending work
    ///   as completed changes the flag.
    /// - witness: `tests::completion::completion_processes_within_budget`
    /// - witness: `tests::completion::decline_resume_matches_uninterrupted_completion`
    /// - witness: `tests::completion::a_starved_budget_declines_with_pending`
    #[inline]
    #[must_use]
    #[spec(ensures: |output| bool::from(output) == matches!(*self, Self::Completed { .. }))]
    pub fn is_completed(&self) -> CompletionStatus
    {
        CompletionStatus::from(matches!(*self, Self::Completed { .. }))
    }

    /// Resume a budget decline from its pending batches; an invalid-input
    /// decline and a completed outcome are returned unchanged.
    ///
    /// # Specification
    /// - ensures: a step- or cell-budget decline continues the completion loop
    ///   from its store, derived cells, certificates and pending batches, in
    ///   order, under `budget`, so the result is the one an uninterrupted run
    ///   reaches from that state.
    /// - ensures: the pending batches are validated as supplied input first,
    ///   and an invalid entry turns the decline into
    ///   [`DeclineReason::InvalidSuppliedOverlap`] without running the loop.
    /// - ensures: an [`DeclineReason::InvalidSuppliedOverlap`] decline and a
    ///   [`CompletionOutcome::Completed`] outcome are returned unchanged:
    ///   invalid input is terminal.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a run declined one step into its leading batch and
    ///   resumed equals the uninterrupted run; L3 — every invalid supplied
    ///   decline is unchanged by resume, and a budget decline whose pending
    ///   work is malformed is revalidated into a typed decline. Completed
    ///   outcomes stay unchanged even under zero ceilings. Lost accumulated
    ///   evidence, skipped validation or restarted work changes the outcome.
    /// - witness: `tests::completion::decline_resume_matches_uninterrupted_completion`
    /// - witness: `tests::completion::invalid_supplied_decline_is_terminal_on_resume`
    /// - witness: `tests::completion::non_unifying_supplied_decline_is_terminal_on_resume`
    /// - witness: `tests::completion::budget_decline_revalidates_non_unifying_pending_overlap`
    /// - witness: `completion::tests::terminal_outcomes_and_empty_sources_preserve_state`
    #[inline]
    #[must_use]
    #[spec(captures: before = self.clone(), ensures: |output| if matches!(before, Self::Completed { .. } | Self::Declined { reason: DeclineReason::InvalidSuppliedOverlap(_), .. }) {
        output == before
    } else {
        before.store().iter().all(|(id, cell)| output.store().get(id) == Maybe::Present(cell))
        && output.derived().starts_with(before.derived()) && output.certificates().starts_with(before.certificates())
        && output.derived().len() <= before.derived().len().saturating_add(usize::from(budget.max_steps))
        && output.certificates().len() <= before.certificates().len().saturating_add(usize::from(budget.max_steps))
        && usize::from(output.store().len()) <= core::cmp::max(usize::from(before.store().len()), usize::from(budget.max_cells))
    })]
    pub fn resume(
        self,
        budget: CompletionBudget,
    ) -> Self
    {
        match self {
            | Self::Completed { .. }
            | Self::Declined {
                reason: DeclineReason::InvalidSuppliedOverlap(_),
                ..
            } => self,
            | Self::Declined {
                store,
                derived,
                certificates,
                pending,
                reason: DeclineReason::StepBudget | DeclineReason::CellBudget,
            } => {
                if let Err(error) = validate_supplied_batches(&store, &pending) {
                    return Self::Declined {
                        store,
                        derived,
                        certificates,
                        pending,
                        reason: DeclineReason::InvalidSuppliedOverlap(error),
                    };
                }
                complete_with_worklist(store, budget, derived, certificates, pending.into())
            },
        }
    }
}

/// Run confluence completion over `store` under `budget`.
///
/// # Specification
/// - ensures: [`CompletionOutcome::Completed`] when every confluence critical
///   pair, those of derived cells included, was processed within budget: each
///   joining pair contributes a certificate and each divergence the reduction
///   order orients contributes a derived cell; otherwise
///   [`CompletionOutcome::Declined`] at the first ceiling reached, carrying the
///   unprocessed batches.
/// - ensures: the worklist is [`scheduled_confluence_batches`] of `store`,
///   processed batch by batch in order.
/// - panics: none.
/// - intension: at most `budget.max_steps` critical pairs are processed.
///
/// # Adequacy
/// - hypothesis: L3 — a small sequent system completes within budget, a zero
///   step budget declines with the whole schedule pending, and the toy alphabet
///   drives the same loop to one oriented cell and replaying certificates; L1 —
///   every certificate it emits replays. An empty store completes with zero
///   ceilings. Extra work, lost original identities or exceeded ceilings
///   changes the outcome.
/// - witness: `tests::completion::completion_processes_within_budget`
/// - witness: `tests::completion::a_starved_budget_declines_with_pending`
/// - witness: `tests::second_inhabitant::completion_orients_and_certifies_over_the_toy_alphabet`
/// - witness: `tests::differential::completion_certificates_replay`
/// - witness: `completion::tests::terminal_outcomes_and_empty_sources_preserve_state`
#[inline]
#[must_use]
#[spec(captures: before = store.clone(), ensures: |output| before.iter().all(|(id, cell)| output.store().get(id) == Maybe::Present(cell))
    && usize::from(output.store().len()) == usize::from(before.len()).saturating_add(output.derived().len())
    && output.derived().iter().enumerate().all(|(index, id)| *id == CellId::from(usize::from(before.len()).saturating_add(index)))
    && output.derived().len() <= usize::from(budget.max_steps) && output.certificates().len() <= usize::from(budget.max_steps)
    && usize::from(output.store().len()) <= core::cmp::max(usize::from(before.len()), usize::from(budget.max_cells)))]
pub fn complete<A>(
    store: CellStore<A>,
    budget: CompletionBudget,
) -> CompletionOutcome<A>
where
    A: CellAlphabet,
{
    let initial = scheduled_confluence_batches(&store);
    complete_with_worklist(store, budget, Vec::new(), Vec::new(), initial.into())
}

/// Run completion from a caller-supplied initial overlap family.
///
/// The source is called once, before the loop starts, and its batches seed the
/// worklist [`complete`] would otherwise schedule; cells the loop derives are
/// scheduled through [`scheduled_confluence_batches`] as usual. This is the
/// seam for a consumer whose own matcher supplies the critical pairs, without
/// this crate entering the matcher's dependency graph.
///
/// # Specification
/// - requires: each supplied overlap's right leg is the stored right cell
///   renamed apart from the stored left cell, as
///   [`Overlap::from_supplied_confluence`] builds it.
/// - ensures: when every supplied entry is valid, the loop processes exactly
///   the supplied batches and then the batches of every cell it derives, under
///   the same ceilings as [`complete`].
/// - ensures: a supplied entry is valid when it is a confluence, both its
///   identifiers address cells of `store`, and its unifier sends the stored
///   left cell's left-hand side and the renamed right cell's left-hand side
///   both to its peak.
/// - ensures: otherwise [`CompletionOutcome::Declined`] with
///   [`DeclineReason::InvalidSuppliedOverlap`] naming the first invalid entry
///   in batch order, every supplied batch pending, nothing derived and nothing
///   certified; the decline is terminal under [`CompletionOutcome::resume`].
/// - provides: a matcher-neutral supply point: the source reads the generic
///   store and returns generic overlaps.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — one witness per refusal: an unissued left identifier, an
///   unissued right identifier, a composition, a unifier whose right leg misses
///   the peak, and a left identifier retargeted to another stored cell each
///   decline with the entry's position before any work, and the enumerator's
///   own overlap rebuilt through the constructor is accepted. An empty supplied
///   schedule calls the source once and preserves the input store. Repeated or
///   omitted invocation and validation after mutation change the observations.
/// - witness: `tests::completion::supplied_overlap_validation_returns_typed_declines`
/// - witness: `tests::completion::supplied_non_unifying_decline_is_typed`
/// - witness: `tests::completion::a_supplied_overlap_naming_another_left_cell_is_declined`
/// - witness: `completion::tests::terminal_outcomes_and_empty_sources_preserve_state`
#[inline]
#[must_use]
#[spec(captures: before = store.clone(), ensures: |output| before.iter().all(|(id, cell)| output.store().get(id) == Maybe::Present(cell))
    && usize::from(output.store().len()) == usize::from(before.len()).saturating_add(output.derived().len())
    && output.derived().len() <= usize::from(budget.max_steps) && output.certificates().len() <= usize::from(budget.max_steps)
    && usize::from(output.store().len()) <= core::cmp::max(usize::from(before.len()), usize::from(budget.max_cells))
    && match output {
        CompletionOutcome::Declined { ref store, ref derived, ref certificates, ref pending, reason: DeclineReason::InvalidSuppliedOverlap(error) } => *store == before && derived.is_empty() && certificates.is_empty() && validate_supplied_batches(store, pending) == Err(error),
        CompletionOutcome::Completed { .. } | CompletionOutcome::Declined { .. } => true,
    })]
pub fn complete_with_overlap_source<A, F>(
    store: CellStore<A>,
    budget: CompletionBudget,
    source: F,
) -> CompletionOutcome<A>
where
    A: CellAlphabet,
    F: FnOnce(&CellStore<A>) -> Vec<Vec<Overlap<A>>>,
{
    let initial = source(&store);
    if let Err(error) = validate_supplied_batches(&store, &initial) {
        return CompletionOutcome::Declined {
            store,
            derived: Vec::new(),
            certificates: Vec::new(),
            pending: initial,
            reason: DeclineReason::InvalidSuppliedOverlap(error),
        };
    }
    complete_with_worklist(store, budget, Vec::new(), Vec::new(), initial.into())
}

/// Validate a supplied worklist before it reaches the loop.
///
/// # Specification
/// - ensures: success exactly when every entry is valid as
///   [`complete_with_overlap_source`] defines it.
/// - fails: the first invalid entry in batch order, with its position and the
///   first rule it breaks, checked in the order kind, left identifier, right
///   identifier, legs.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — compositions, missing identifiers and independently
///   non-unifying legs refuse at the first offending batch position. Changing
///   validation order, dropping a leg or ignoring an earlier entry changes the
///   typed decline.
/// - witness: `tests::completion::supplied_overlap_validation_returns_typed_declines`
/// - witness: `tests::completion::supplied_non_unifying_decline_is_typed`
/// - witness: `tests::completion::a_supplied_overlap_naming_another_left_cell_is_declined`
#[spec(ensures: |output| output == batches.iter().enumerate().find_map(|(batch, entries)| entries.iter().enumerate().find_map(|(overlap, item)| {
    let batch = BatchIndex::from(batch);
    let overlap = OverlapIndex::from(overlap);
    if item.kind != OverlapKind::Confluence { return Some(SuppliedOverlapError::NonConfluence { batch, overlap }); }
    match store.get(item.left) {
        Maybe::Absent(_) => Some(SuppliedOverlapError::UnknownLeftCell { batch, overlap, cell: item.left }),
        Maybe::Present(left) => if matches!(store.get(item.right), Maybe::Absent(_)) {
            Some(SuppliedOverlapError::UnknownRightCell { batch, overlap, cell: item.right })
        } else if legs_meet_peak(item, left) == LegAgreement::Miss {
            Some(SuppliedOverlapError::NonUnifyingSubstitution { batch, overlap })
        } else { None },
    }
})).map_or(Ok(()), Err))]
fn validate_supplied_batches<A>(
    store: &CellStore<A>,
    batches: &[Vec<Overlap<A>>],
) -> Result<(), SuppliedOverlapError>
where
    A: CellAlphabet,
{
    for (batch, overlaps) in batches.iter().enumerate() {
        let batch = BatchIndex::from(batch);
        for (overlap, item) in overlaps.iter().enumerate() {
            let overlap = OverlapIndex::from(overlap);
            if item.kind != OverlapKind::Confluence {
                return Err(SuppliedOverlapError::NonConfluence { batch, overlap });
            }
            let Maybe::Present(left) = store.get(item.left)
            else {
                return Err(SuppliedOverlapError::UnknownLeftCell {
                    batch,
                    overlap,
                    cell: item.left,
                });
            };
            if let Maybe::Absent(_) = store.get(item.right) {
                return Err(SuppliedOverlapError::UnknownRightCell {
                    batch,
                    overlap,
                    cell: item.right,
                });
            }
            if legs_meet_peak(item, left) == LegAgreement::Miss {
                return Err(SuppliedOverlapError::NonUnifyingSubstitution { batch, overlap });
            }
        }
    }
    Ok(())
}

/// Whether a supplied unifier sends both legs of an overlap to its peak.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum LegAgreement
{
    /// Both left-hand sides instantiate to the peak.
    Meet,
    /// At least one does not.
    Miss,
}

/// Whether `overlap`'s unifier sends `left`'s left-hand side and the renamed
/// right cell's left-hand side both to the peak.
///
/// # Specification
/// - ensures: positive exactly when both substituted left-hand sides equal the
///   peak.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — valid supplied overlaps meet the peak on both legs; wrong
///   left identity and a mismatching right leg decline. A one-leg check or
///   reversed conjunction changes acceptance.
/// - witness: `tests::completion::a_supplied_overlap_naming_another_left_cell_is_declined`
/// - witness: `tests::completion::supplied_non_unifying_decline_is_typed`
#[spec(ensures: |output| (output == LegAgreement::Meet) == (A::apply_subst(&overlap.unifier, left.lhs()) == overlap.peak && A::apply_subst(&overlap.unifier, overlap.right_renamed().lhs()) == overlap.peak))]
fn legs_meet_peak<A>(
    overlap: &Overlap<A>,
    left: &Cell<A>,
) -> LegAgreement
where
    A: CellAlphabet,
{
    let meets = |lhs: &A::Cmd| A::apply_subst(&overlap.unifier, lhs) == overlap.peak;
    if meets(left.lhs()) && meets(overlap.right_renamed().lhs()) {
        return LegAgreement::Meet;
    }
    LegAgreement::Miss
}

/// The pending residue of a decline: the interrupted batch from `index` on,
/// then every later batch.
///
/// # Specification
/// - ensures: the interrupted batch suffix is first, including an empty suffix,
///   followed by every later batch unchanged and in order.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — declines inside a batch preserve its exact suffix and
///   every following batch. Zero, final and past-end indices separate suffix
///   truncation from loss or reordering of later work.
/// - witness: `completion::tests::empty_schedules_orientation_and_pending_boundaries_are_exact`
#[spec(captures: tail = worklist.clone(), ensures: |output| output.len() == tail.len().saturating_add(1)
    && output.first().is_some_and(|head| head.iter().eq(batch.iter().skip(usize::from(index))))
    && output.iter().skip(1).eq(tail.iter()))]
fn pending_from<A>(
    batch: &[Overlap<A>],
    index: OverlapIndex,
    worklist: VecDeque<Vec<Overlap<A>>>,
) -> Vec<Vec<Overlap<A>>>
where
    A: CellAlphabet,
{
    let mut pending = Vec::with_capacity(worklist.len().saturating_add(1));
    pending.push(batch.iter().skip(usize::from(index)).cloned().collect());
    pending.extend(worklist);
    pending
}

/// Run the completion loop from a worklist and the results already reached.
///
/// The one body behind [`complete`], [`complete_with_overlap_source`] and
/// [`CompletionOutcome::resume`]: a fresh run enters with its schedule and
/// nothing accumulated, a resumed one with the batches and results its decline
/// carried, so decline and resume are transparent by construction.
///
/// # Specification
/// - ensures: the outcome an uninterrupted run reaches from this state.
/// - ensures: the input store and accumulated evidence remain prefixes; new
///   cells and certificates number at most the step budget, and the store grows
///   only within the greater of its initial size and cell ceiling.
/// - panics: none.
/// - intension: at most `budget.max_steps` critical pairs are processed, and
///   each pair's reducts are normalized once, the certificate built from those
///   normalizations.
///
/// # Adequacy
/// - hypothesis: L3 — zero and partial budgets preserve pending work, store
///   identities and accumulated evidence; resumed outcomes equal uninterrupted
///   outcomes. Lost prefixes, extra insertions and an off-by-one ceiling change
///   those observations.
/// - witness: `tests::completion::decline_resume_matches_uninterrupted_completion`
/// - witness: `tests::completion::cell_budget_decline_preserves_pending_work`
#[spec(captures: before = (store.clone(), derived.clone(), certificates.clone()), ensures: |output| before.0.iter().all(|(id, cell)| output.store().get(id) == Maybe::Present(cell))
    && output.derived().starts_with(&before.1) && output.certificates().starts_with(&before.2)
    && output.derived().len() <= before.1.len().saturating_add(usize::from(budget.max_steps))
    && output.certificates().len() <= before.2.len().saturating_add(usize::from(budget.max_steps))
    && usize::from(output.store().len()) == usize::from(before.0.len()).saturating_add(output.derived().len().saturating_sub(before.1.len()))
    && usize::from(output.store().len()) <= core::cmp::max(usize::from(before.0.len()), usize::from(budget.max_cells)))]
fn complete_with_worklist<A>(
    mut store: CellStore<A>,
    budget: CompletionBudget,
    mut derived: Vec<CellId>,
    mut certificates: Vec<Tracelet<A>>,
    mut worklist: VecDeque<Vec<Overlap<A>>>,
) -> CompletionOutcome<A>
where
    A: CellAlphabet,
{
    let mut steps = 0_usize;
    while let Some(batch) = worklist.pop_front() {
        for (index, overlap) in batch.iter().enumerate() {
            if steps >= usize::from(budget.max_steps) {
                return CompletionOutcome::Declined {
                    pending: pending_from(&batch, OverlapIndex::from(index), worklist),
                    store,
                    derived,
                    certificates,
                    reason: DeclineReason::StepBudget,
                };
            }
            steps = steps.saturating_add(1);
            // Validation, or the enumerator, guarantees the left cell; an
            // overlap naming one the store lost is left in place.
            let Ok(left_reduct) = overlap.left_reduct(&store)
            else {
                continue;
            };
            let left = normalize(&store, &left_reduct, budget.norm_budget);
            let right = normalize(&store, &overlap.right_reduct(), budget.norm_budget);
            if bool::from(left.exhausted) || bool::from(right.exhausted) {
                // Undecided within the normalization budget: neither certified
                // nor oriented.
                continue;
            }
            if left.normal == right.normal {
                if let Maybe::Present(certificate) = joined(overlap, left, right) {
                    certificates.push(certificate);
                }
                continue;
            }
            let Maybe::Present((bigger, smaller)) = orient::<A>(left.normal, right.normal)
            else {
                // The reduction order does not separate the divergence: an
                // obstruction left for a stronger order.
                continue;
            };
            let new_cell = Cell::new(
                bigger,
                smaller,
                A::derived_orientation(),
                A::derived_provenance(),
            );
            if store.iter().any(|(_, cell)| *cell == new_cell) {
                continue;
            }
            if usize::from(store.len()) >= usize::from(budget.max_cells) {
                return CompletionOutcome::Declined {
                    pending: pending_from(&batch, OverlapIndex::from(index), worklist),
                    store,
                    derived,
                    certificates,
                    reason: DeclineReason::CellBudget,
                };
            }
            let id = store.insert(new_cell);
            derived.push(id);
            // economy: rescheduling enumerates the whole store after each
            // derived cell and keeps the batches that touch it; restricting the
            // sweep to the new cell's pairs through `overlaps_between` is the
            // known improvement once a store is large enough to measure it.
            worklist.extend(
                scheduled_confluence_batches(&store)
                    .into_iter()
                    .filter(|candidate| {
                        candidate
                            .iter()
                            .any(|scheduled| scheduled.left == id || scheduled.right == id)
                    }),
            );
        }
    }
    CompletionOutcome::Completed {
        store,
        derived,
        certificates,
    }
}

/// The confluence overlaps of `store` scheduled into independent batches: the
/// completion worklist.
///
/// # Specification
/// - ensures: the confluence entries of [`enumerate_overlaps`], in its order,
///   partitioned by [`OverlapSupport::batches`] under the store's support.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — three independent clusters schedule into two batches of
///   three, and a starved run declines with exactly this schedule pending.
///   Empty schedules stay empty; a composition cannot enter a confluence batch.
///   Wrong filtering or lost members changes the pending work.
/// - witness: `tests::completion::decline_resume_matches_uninterrupted_completion`
/// - witness: `tests::completion::a_starved_budget_declines_with_pending`
/// - witness: `completion::tests::empty_schedules_orientation_and_pending_boundaries_are_exact`
#[inline]
#[must_use]
#[spec(ensures: |output| output.iter().all(|batch| !batch.is_empty() && batch.iter().all(|overlap| overlap.kind == OverlapKind::Confluence))
    && output.iter().map(Vec::len).sum::<usize>() == enumerate_overlaps(store).iter().filter(|overlap| overlap.kind == OverlapKind::Confluence).count())]
pub fn scheduled_confluence_batches<A>(store: &CellStore<A>) -> Vec<Vec<Overlap<A>>>
where
    A: CellAlphabet,
{
    let overlaps: Vec<Overlap<A>> = enumerate_overlaps(store)
        .into_iter()
        .filter(|overlap| overlap.kind == OverlapKind::Confluence)
        .collect();
    OverlapSupport::from_store(store).batches(&overlaps)
}

quenchant_shape::reason_enum! {
    /// Why a divergent pair is not oriented into a cell.
    mod orientation {
        /// The reason no rule is built.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub enum Absent {
            /// The reduction order does not separate the two terms.
            Unorientable,
        }
    }
}

/// Orient a divergent pair by the reduction order, the larger term first.
///
/// # Specification
/// - ensures: `(left, right)` when the order puts `left` above `right`, and
///   `(right, left)` when it puts `right` above.
/// - provides: [`orientation::Absent::Unorientable`] when the order does not
///   separate them.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — unequal sizes orient in both argument orders; equal size
///   and missing hole domination refuse. Reversing the result or treating
///   obstruction as a direction changes the exact outcome.
/// - witness: `completion::tests::empty_schedules_orientation_and_pending_boundaries_are_exact`
#[spec(captures: pair = (left.clone(), right.clone()), ensures: |output| match output {
    Maybe::Present(ref actual) => match A::reduction_cmp(&pair.0, &pair.1) {
        core::cmp::Ordering::Greater => actual.0 == pair.0 && actual.1 == pair.1,
        core::cmp::Ordering::Less => actual.0 == pair.1 && actual.1 == pair.0,
        core::cmp::Ordering::Equal => false,
    },
    Maybe::Absent(orientation::Absent::Unorientable) => A::reduction_cmp(&pair.0, &pair.1) == core::cmp::Ordering::Equal,
})]
fn orient<A>(
    left: A::Cmd,
    right: A::Cmd,
) -> Maybe<(A::Cmd, A::Cmd), orientation::Absent>
where
    A: CellAlphabet,
{
    match A::reduction_cmp(&left, &right) {
        | core::cmp::Ordering::Greater => Maybe::Present((left, right)),
        | core::cmp::Ordering::Less => Maybe::Present((right, left)),
        | core::cmp::Ordering::Equal => Maybe::Absent(orientation::Absent::Unorientable),
    }
}

#[cfg(test)]
mod tests
{
    use gandr_theory_cell_complexes_tools::Toy;
    use gandr_theory_cell_complexes_tools::ToyAlphabet;
    use gandr_theory_cell_complexes_tools::toy_cell;

    use super::*;

    #[test]
    fn empty_schedules_orientation_and_pending_boundaries_are_exact()
    {
        let small = Toy::zero();
        let large = Toy::succ(small.clone());
        assert_eq!(
            Maybe::Present((large.clone(), small.clone())),
            orient::<ToyAlphabet>(large.clone(), small.clone())
        );
        assert_eq!(
            Maybe::Present((large.clone(), small.clone())),
            orient::<ToyAlphabet>(small.clone(), large.clone())
        );
        assert_eq!(
            Maybe::Absent(orientation::Absent::Unorientable),
            orient::<ToyAlphabet>(small.clone(), small.clone())
        );
        assert_eq!(
            Maybe::Absent(orientation::Absent::Unorientable),
            orient::<ToyAlphabet>(Toy::succ(Toy::var("x")), Toy::var("y"))
        );
        let mut store = CellStore::<ToyAlphabet>::new();
        assert!(scheduled_confluence_batches(&store).is_empty());
        let first = toy_cell(small.clone(), small);
        let second = toy_cell(large.clone(), large);
        let first_id = store.insert(first.clone());
        let second_id = store.insert(second.clone());
        let a = crate::overlap::overlaps_between((first_id, &first), (first_id, &first)).remove(0);
        let b =
            crate::overlap::overlaps_between((second_id, &second), (second_id, &second)).remove(0);
        assert!(scheduled_confluence_batches(&store).is_empty());
        let batch = alloc::vec![a.clone(), b.clone()];
        let tail = VecDeque::from([alloc::vec![a.clone()], Vec::new(), alloc::vec![b.clone()]]);
        assert_eq!(
            alloc::vec![
                batch.clone(),
                alloc::vec![a.clone()],
                Vec::new(),
                alloc::vec![b.clone()]
            ],
            pending_from(&batch, OverlapIndex::from(0_usize), tail.clone())
        );
        assert_eq!(
            alloc::vec![
                alloc::vec![b.clone()],
                alloc::vec![a.clone()],
                Vec::new(),
                alloc::vec![b.clone()]
            ],
            pending_from(&batch, OverlapIndex::from(1_usize), tail.clone())
        );
        for index in [2_usize, usize::MAX] {
            assert_eq!(
                alloc::vec![Vec::new(), alloc::vec![a.clone()], Vec::new(), alloc::vec![
                    b.clone()
                ]],
                pending_from(&batch, OverlapIndex::from(index), tail.clone())
            );
        }
        assert_eq!(
            alloc::vec![Vec::<Overlap<ToyAlphabet>>::new()],
            pending_from::<ToyAlphabet>(&[], OverlapIndex::from(0_usize), VecDeque::new())
        );
    }

    #[test]
    fn terminal_outcomes_and_empty_sources_preserve_state()
    {
        let zero = CompletionBudget::new(
            CompletionStepBudget::from(0_usize),
            CompletionCellBudget::from(0_usize),
            NormalizationBudget::from(0_usize),
        );
        let empty = complete(CellStore::<ToyAlphabet>::new(), zero);
        assert_eq!(
            CompletionOutcome::Completed {
                store: CellStore::new(),
                derived: Vec::new(),
                certificates: Vec::new()
            },
            empty
        );
        let mut store = CellStore::new();
        let _shrinking = store.insert(toy_cell(Toy::succ(Toy::zero()), Toy::zero()));
        let _identity = store.insert(toy_cell(Toy::succ(Toy::zero()), Toy::succ(Toy::zero())));
        let completed = complete(
            store.clone(),
            CompletionBudget::new(
                CompletionStepBudget::from(2_usize),
                CompletionCellBudget::from(0_usize),
                NormalizationBudget::from(1_usize),
            ),
        );
        assert!(bool::from(completed.is_completed()));
        assert_eq!(2, completed.certificates().len());
        assert_eq!(completed, completed.clone().resume(zero));
        let automatic = complete(store.clone(), zero);
        assert!(matches!(automatic, CompletionOutcome::Declined {
            reason: DeclineReason::StepBudget,
            ..
        }));
        let called = core::cell::Cell::new(false);
        let source = alloc::vec![Vec::new()];
        let supplied = complete_with_overlap_source(store.clone(), zero, |_| {
            assert!(!called.replace(true));
            source
        });
        assert!(called.get());
        assert_eq!(
            CompletionOutcome::Completed {
                store,
                derived: Vec::new(),
                certificates: Vec::new()
            },
            supplied
        );
    }
}
