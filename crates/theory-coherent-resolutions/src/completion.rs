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
//!
//! [`join_critical_pairs`] is completion's check with no derivation: it
//! decides whether a store's critical pairs already join, reporting the first
//! divergence, or the first pair the budget leaves undecided, instead of
//! orienting it. [`PairJoining`] is that check over a store a caller grows by
//! appending cells: it resumes at the pair it stopped at, so a caller that
//! derives a cell from each divergence decides no joined pair again, only the
//! pair that parted and those after it.
//!
//! # Completion
//!
//! `complete` schedules the store's confluence overlaps into independent
//! batches and runs them in order. A pair whose reducts normalize to one term
//! contributes a certificate; a pair whose normal forms differ is oriented by
//! the alphabet's reduction order into a derived cell, whose own critical pairs
//! join the worklist. Three obstructions are left rather than guessed at: a
//! reduct the normalization budget does not bring to a normal form, a
//! divergence the order does not separate, and a derived cell the store already
//! holds. Each pair's reducts are normalized once, and the certificate is built
//! from those normalizations rather than recomputed.
//!
//! The `CompletionBudget` is three ceilings — critical pairs processed, cells
//! the store may hold, steps per normalization — each the most admitted rather
//! than the point of failure. Reaching the step or cell ceiling returns
//! `CompletionOutcome::Declined` with the interrupted batch's remainder first
//! and every later batch unchanged, never a divergence or a truncated answer.
//! `resume` continues the same loop from that state, so a declined-then-resumed
//! run equals the uninterrupted one by construction rather than by agreement
//! between two loops.
//!
//! After each derived cell the loop re-enumerates the store and keeps the
//! batches that touch the new cell. Restricting the sweep to the new cell's
//! pairs through `overlaps_between` is the known improvement; it waits for a
//! store large enough to measure the difference.
//!
//! # Supplied overlaps
//!
//! `complete_with_overlap_source` is the seam through which a caller's own
//! matcher seeds the worklist with confluence overlaps the generic unifier
//! would not find. The source is a parameter, not a dependency: this crate
//! depends on the substrate and `quenchant-shape` and on no matcher crate, in
//! any dependency table, and a matcher-owning crate reaches completion by
//! calling it. `Overlap::from_supplied_confluence` builds an entry from the
//! matcher's unifier and seam without re-running the generic unifier.
//!
//! Every supplied entry is validated before any reaches the loop: it must be a
//! confluence, both its identifiers must address stored cells, and its unifier
//! must send both legs — the stored left cell's left-hand side to its peak and
//! the renamed right cell's to the peak's subterm at its seam. The first
//! invalid entry declines with
//! `DeclineReason::InvalidSuppliedOverlap`, naming its batch and position, with
//! every supplied batch pending and nothing derived. An invalid-input decline
//! is terminal under `resume`, and a budget decline's pending work is
//! revalidated before it resumes, so an invalid entry never reaches the loop by
//! either route.
//!
//! The leg check reads both legs. Checking the right leg alone would accept an
//! entry whose left identifier was changed to another stored cell, since the
//! peak is computed from the left cell the entry was built with; reading the
//! stored left cell closes that, and
//! `a_supplied_overlap_naming_another_left_cell_is_declined` holds it. That the
//! right leg is the stored right cell renamed apart from the stored left one is
//! the constructor's guarantee and stays a precondition.
//!
//! # Joinability without derivation
//!
//! `join_critical_pairs` reads each unordered pair of distinct cells' root
//! entry once — the enumerator's confluence entry for a pair and for its
//! mirror share a peak, and their certificates are one transformation — and
//! every ordered pair's interior entries, a cell's pair with itself included,
//! since an interior overlap and its mirror are different peaks. Over an
//! alphabet whose only command position is the root the interior family is
//! empty. It normalizes both reducts as completion does, and keeps the
//! certificate of each pair that joins. A pair that diverges is reported with
//! both normal forms, never oriented: the caller is asking whether the rules it
//! was given are confluent, and a derived cell would answer a different
//! question, whether some extension of them is. A store whose rewriting
//! terminates and whose pairs all join is confluent (Newman's lemma with the
//! critical-pair lemma), so a caller holding the termination half asks this
//! for the other.
//! **Alternative.** Running `complete` and reading its derived cells: a
//! completed run that derived nothing says the same, but a divergence is
//! oriented into a cell and the loop continues past it, so the pair that
//! diverged would have to be recovered from the derivation.
//!
//! # Composite pairs
//!
//! [`PairJoining::resume_with`] asks a [`PairScheme`] for the class of each
//! pair before it joins the pair. A pair whose peak holds a redex strictly
//! below its seam is composite. When the rewriting terminates, its join
//! follows from the joins of the other pairs (Kapur, Musser and Narendran). The
//! joining skips the join of a composite pair and keeps the match as the
//! pair's witness ([`CompositePair`]). [`CompositePair::replay`] checks each
//! witness, so the scheme is no trusted decision. A pair with no witness joins.
//! [`PairJoining::resume`] runs with [`NoScheme`], which classes no pair. The
//! scheme of a term reading is `CompositeCriterion` in
//! `gandr-theory-computads`, which walks the peak below the seam with no
//! allocation for each pair.

use alloc::collections::VecDeque;
use alloc::vec::Vec;

use anodized::spec;
use gandr_theory_cell_complexes::Cell;
use gandr_theory_cell_complexes::CellAlphabet;
use gandr_theory_cell_complexes::CellId;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes::PositionOrder;
use gandr_theory_cell_complexes::SequentAlphabet;
use quenchant_shape::shape::Maybe;

use crate::boundary::BatchIndex;
use crate::boundary::CompletionCellBudget;
use crate::boundary::CompletionStatus;
use crate::boundary::CompletionStepBudget;
use crate::boundary::NormalizationBudget;
use crate::boundary::OverlapIndex;
use crate::boundary::PairDecisions;
use crate::overlap::Overlap;
use crate::overlap::OverlapKind;
use crate::overlap::OverlapSupport;
use crate::overlap::enumerate_overlaps;
use crate::overlap::interior_overlaps_between;
use crate::overlap::root_overlaps_between;
use crate::rewrite::CellApp;
use crate::rewrite::normalize;
use crate::rewrite::rewrite_at;
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
            Self::NonConfluence { batch, overlap }
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
            Self::NonConfluence { .. } => f.write_str("a composition, not a confluence"),
            Self::UnknownLeftCell { cell, .. } => {
                write!(f, "the store holds no left cell {}", usize::from(cell))
            },
            Self::UnknownRightCell { cell, .. } => {
                write!(f, "the store holds no right cell {}", usize::from(cell))
            },
            Self::NonUnifyingSubstitution { .. } => {
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
        /// The store at the decline.
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
    /// The store, completed or at the decline.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn store(&self) -> &CellStore<A>
    {
        match *self {
            Self::Completed { ref store, .. } | Self::Declined { ref store, .. } => store,
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
            Self::Completed {
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
            Self::Completed { ref derived, .. } | Self::Declined { ref derived, .. } => derived,
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
    ///   evidence, skipped validation or restarted work changes the outcome. A
    ///   terminal outcome is moved back out whole, and the completion loop only
    ///   appends to the store, the derived cells and the certificates, so the
    ///   predicate reads their lengths and the witnesses compare whole
    ///   outcomes.
    /// - witness: `tests::completion::decline_resume_matches_uninterrupted_completion`
    /// - witness: `tests::completion::invalid_supplied_decline_is_terminal_on_resume`
    /// - witness: `tests::completion::non_unifying_supplied_decline_is_terminal_on_resume`
    /// - witness: `tests::completion::budget_decline_revalidates_non_unifying_pending_overlap`
    /// - witness: `completion::tests::terminal_outcomes_and_empty_sources_preserve_state`
    #[inline]
    #[must_use]
    #[spec(captures: [
        terminal = matches!(self, Self::Completed { .. } | Self::Declined { reason: DeclineReason::InvalidSuppliedOverlap(_), .. }),
        completed = bool::from(self.is_completed()),
        cells = usize::from(self.store().len()),
        derived = self.derived().len(),
        certificates = self.certificates().len(),
    ], ensures: |output| if terminal {
        bool::from(output.is_completed()) == completed
        && usize::from(output.store().len()) == cells
        && output.derived().len() == derived && output.certificates().len() == certificates
    } else {
        usize::from(output.store().len()) >= cells
        && output.derived().len() >= derived && output.certificates().len() >= certificates
        && output.derived().len() <= derived.saturating_add(usize::from(budget.max_steps))
        && output.certificates().len() <= certificates.saturating_add(usize::from(budget.max_steps))
        && usize::from(output.store().len()) <= core::cmp::max(cells, usize::from(budget.max_cells))
    })]
    pub fn resume(
        self,
        budget: CompletionBudget,
    ) -> Self
    {
        match self {
            Self::Completed { .. }
            | Self::Declined {
                reason: DeclineReason::InvalidSuppliedOverlap(_),
                ..
            } => self,
            Self::Declined {
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
///   left cell's left-hand side to its peak and the renamed right cell's
///   left-hand side to the peak's subterm at its seam.
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
    /// Both left-hand sides instantiate to the peak, the right one at the seam.
    Meet,
    /// At least one does not.
    Miss,
}

/// Whether `overlap`'s unifier sends `left`'s left-hand side to the peak and
/// the renamed right cell's left-hand side to the peak's subterm at the seam.
///
/// # Specification
/// - ensures: positive exactly when the substituted left left-hand side equals
///   the peak and the substituted right one equals the peak's subterm at the
///   seam, which at the root is the peak.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — valid supplied overlaps meet the peak on both legs; wrong
///   left identity and a mismatching right leg decline. A one-leg check or
///   reversed conjunction changes acceptance.
/// - witness: `tests::completion::a_supplied_overlap_naming_another_left_cell_is_declined`
/// - witness: `tests::completion::supplied_non_unifying_decline_is_typed`
#[spec(ensures: |output| (output == LegAgreement::Meet) == (A::apply_subst(&overlap.unifier, left.lhs()) == overlap.peak
    && A::subterm_cmd_at(&overlap.peak, &overlap.seam) == Maybe::Present(A::apply_subst(&overlap.unifier, overlap.right_renamed().lhs()))))]
fn legs_meet_peak<A>(
    overlap: &Overlap<A>,
    left: &Cell<A>,
) -> LegAgreement
where
    A: CellAlphabet,
{
    if A::apply_subst(&overlap.unifier, left.lhs()) != overlap.peak {
        return LegAgreement::Miss;
    }
    match A::subterm_cmd_at(&overlap.peak, &overlap.seam) {
        Maybe::Present(at_seam)
            if at_seam == A::apply_subst(&overlap.unifier, overlap.right_renamed().lhs()) =>
        {
            LegAgreement::Meet
        },
        Maybe::Present(_) | Maybe::Absent(_) => LegAgreement::Miss,
    }
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
/// - witness: `completion::tests::a_pair_one_reduct_of_which_is_starved_is_neither_certified_nor_oriented`
/// - witness: `completion::tests::a_derived_cell_reschedules_only_the_pairs_it_takes_part_in`
/// - witness: `completion::tests::a_derived_cell_is_paired_with_the_cells_it_overlaps`
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
            // Validation, or the enumerator, guarantees the left cell and a
            // seam the peak holds; an overlap naming a cell the store lost is
            // left in place.
            let (Ok(left_reduct), Ok(right_reduct)) =
                (overlap.left_reduct(&store), overlap.right_reduct())
            else {
                continue;
            };
            let left = normalize(&store, &left_reduct, budget.norm_budget);
            let right = normalize(&store, &right_reduct, budget.norm_budget);
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

/// Whether every confluence critical pair of a store joins, decided with no
/// cell derived.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Joinability<A: CellAlphabet = SequentAlphabet>
{
    /// Every pair joins: one certificate per pair, in enumeration order, and
    /// none when no two cells overlap.
    Joined(Vec<Tracelet<A>>),
    /// The first pair whose two reducts reach different normal forms.
    Diverges
    {
        /// The pair.
        overlap: Overlap<A>,
        /// The left reduct's normal form.
        left: A::Cmd,
        /// The steps from the left reduct to `left`.
        left_steps: Vec<CellApp<A>>,
        /// The right reduct's normal form.
        right: A::Cmd,
        /// The steps from the right reduct to `right`.
        right_steps: Vec<CellApp<A>>,
    },
    /// The first pair a reduct of which reached no normal form within the
    /// budget: whether it joins is not decided.
    Undecided(Overlap<A>),
}

/// Decide whether every confluence critical pair of `store` joins: the check
/// completion makes of each pair, with a divergence reported rather than
/// oriented into a derived cell.
///
/// A store whose rewriting terminates and whose critical pairs all join is
/// confluent, so every strategy reaches one normal form from every term; a
/// caller that has the termination half asks this for the other. Each pair is
/// decided, a composite one too. A caller that skips the join of a composite
/// pair gives a scheme to [`PairJoining::resume_with`].
///
/// # Specification
/// - ensures: the pairs are taken in order of their later cell: for each cell
///   in store order and each cell up to it, the root confluence entries of
///   [`overlaps_between`](crate::overlap::overlaps_between) with the earlier
///   cell on the left, so a pair and its mirror are decided once, then the
///   entries of [`interior_overlaps_between`] with the earlier cell on the left
///   and then on the right, the diagonal once; every pair a cell makes with the
///   cells before it is decided before any pair of a later cell, so a store
///   growing by cells reaches each pair; each pair's two reducts are normalized
///   under `budget`; [`Joinability::Joined`] carries one replaying certificate
///   per pair decided when every one of them joins; otherwise the first that
///   does not, as [`Joinability::Undecided`] when a reduct ran out of budget
///   and as [`Joinability::Diverges`] with both normal forms, and the steps
///   that reached each, when they differ.
/// - panics: none.
/// - intension: a fresh [`PairJoining`] resumed once.
///
/// # Adequacy
/// - hypothesis: L3 — over the toy alphabet, two additions that overlap at
///   `add(Zero, Zero)` and agree there join with a certificate that replays,
///   the same pair with one side made `Succ` diverges with both normal forms, a
///   reduct needing a step under a zero budget is undecided, and a store with
///   no overlap joins with no certificate; a rule overlapping a successor below
///   an addition diverges at that interior seam and a rule overlapping itself
///   one position down joins with a certificate stepping at the seam; deciding
///   a mirrored root pair twice, skipping an interior pair, reporting a starved
///   pair as divergent or dropping a certificate changes one of them.
/// - witness: `completion::tests::joinability_separates_joined_divergent_and_undecided_pairs`
/// - witness: `tests::second_inhabitant::interior_overlaps_reach_below_the_root_and_join_or_diverge`
#[spec(ensures: |output| match output {
    Joinability::Joined(ref certificates) => certificates.iter().all(|certificate|
        certificate.overlap.kind == OverlapKind::Confluence
            && (certificate.overlap.seam != A::root_position() || certificate.overlap.left < certificate.overlap.right)
            && bool::from(certificate.replay(store))),
    Joinability::Diverges { ref overlap, ref left, ref left_steps, ref right, ref right_steps } => overlap.kind == OverlapKind::Confluence && left != right
        && overlap.left_reduct(store).is_ok_and(|reduct| normalize(store, &reduct, budget).path == *left_steps)
        && overlap.right_reduct().is_ok_and(|reduct| normalize(store, &reduct, budget).path == *right_steps),
    Joinability::Undecided(ref overlap) => overlap.kind == OverlapKind::Confluence,
})]
#[inline]
#[must_use]
pub fn join_critical_pairs<A>(
    store: &CellStore<A>,
    budget: NormalizationBudget,
) -> Joinability<A>
where
    A: CellAlphabet,
{
    PairJoining::new().resume(store, budget)
}

/// The class that a scheme gives a critical pair before a joining decides it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PairClass<A: CellAlphabet = SequentAlphabet>
{
    /// A rule matches the pair's peak strictly below its seam, by this step.
    /// The pair is composite, so the joining skips its join.
    Composite(CellApp<A>),
    /// The scheme finds no witness, so the joining joins the pair.
    Unclassed,
}

/// Why the witness of a composite pair does not replay.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum CompositeRefusal
{
    /// The pair is a composition, not a confluence.
    NotAConfluence,
    /// The store holds no cell under an identifier that the witness names.
    UnissuedCell(CellId),
    /// The pair's left cell does not fire at the peak's root, or its right
    /// cell does not fire at the seam.
    NotAPeak,
    /// The witness's position is not strictly below the seam.
    NotBelow,
    /// The witness's cell does not fire at the witness's position.
    Unmatched,
}

impl core::fmt::Display for CompositeRefusal
{
    /// Names the refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            Self::NotAConfluence => f.write_str("the pair is not a confluence"),
            Self::UnissuedCell(cell) => {
                write!(f, "the store holds no cell {}", usize::from(cell))
            },
            Self::NotAPeak => f.write_str("the pair's cells do not fire at its peak"),
            Self::NotBelow => f.write_str("the witness is not strictly below the seam"),
            Self::Unmatched => f.write_str("the witness's cell does not fire at its position"),
        }
    }
}

impl core::error::Error for CompositeRefusal
{
}

/// A critical pair that a joining skips, with the match that makes it
/// composite.
///
/// # Specification
/// - ensures: the pair, and the step of a cell that matches the pair's peak
///   strictly below its seam; [`Self::replay`] checks the step.
/// - executable: none — a datum; [`Self::replay`] carries the predicate.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Self::replay`].
/// - witness: `completion::tests::a_composite_pair_is_skipped_and_its_witness_is_checked`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CompositePair<A: CellAlphabet = SequentAlphabet>
{
    /// The pair.
    pub overlap: Overlap<A>,
    /// The cell that matches the peak strictly below the seam, and where.
    pub below: CellApp<A>,
}

impl<A> CompositePair<A>
where
    A: CellAlphabet,
{
    /// Check the witness against `store`.
    ///
    /// # Specification
    /// - ensures: `Ok` exactly when the pair is a confluence, its left cell
    ///   fires at the peak's root and its right cell at the seam, the witness's
    ///   position is strictly below the seam, and the witness's cell fires at
    ///   that position; otherwise the first check that fails, in that order.
    /// - panics: none.
    /// - executable: none — the body is the predicate.
    ///
    /// # Errors
    /// The first check that fails, as a [`CompositeRefusal`] names it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — over the toy alphabet, the witness of a composite
    ///   pair replays. A witness moved to the seam, a witness whose cell does
    ///   not match at its position, a witness that names no cell of the store,
    ///   and a pair whose left cell is another are each refused by name.
    /// - witness: `completion::tests::a_composite_pair_is_skipped_and_its_witness_is_checked`
    #[inline]
    pub fn replay(
        &self,
        store: &CellStore<A>,
    ) -> Result<(), CompositeRefusal>
    {
        let &Self {
            ref overlap,
            ref below,
        } = self;
        if overlap.kind != OverlapKind::Confluence {
            return Err(CompositeRefusal::NotAConfluence);
        }
        let fires = |cell: CellId, at: &A::Pos| match store.get(cell) {
            Maybe::Present(found) => Ok(matches!(
                rewrite_at(found, &overlap.peak, at),
                Maybe::Present(_)
            )),
            Maybe::Absent(_) => Err(CompositeRefusal::UnissuedCell(cell)),
        };
        if !fires(overlap.left, &A::root_position())? || !fires(overlap.right, &overlap.seam)? {
            return Err(CompositeRefusal::NotAPeak);
        }
        if A::position_order(&overlap.seam, &below.at) != PositionOrder::Encloses {
            return Err(CompositeRefusal::NotBelow);
        }
        if !fires(below.cell, &below.at)? {
            return Err(CompositeRefusal::Unmatched);
        }
        Ok(())
    }
}

/// How a joining classes each critical pair before it decides it.
pub trait PairScheme<A: CellAlphabet>
{
    /// The class of `overlap`, a confluence critical pair of `store`.
    ///
    /// # Specification
    /// - ensures: [`PairClass::Composite`] only with a step whose cell matches
    ///   the peak of `overlap` strictly below its seam, so that the pair's
    ///   [`CompositePair::replay`] holds; [`PairClass::Unclassed`] when the
    ///   scheme finds no such step.
    /// - panics: none.
    /// - executable: none — a type-level block: a required method has no body
    ///   of its own, and each implementation states its own checks.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — [`NoScheme`] classes no pair, and a scheme that finds
    ///   the first step below the seam classes the composite pair of a toy
    ///   store and not its prime pair. The criterion on terms states its own
    ///   witnesses.
    /// - witness: `completion::tests::a_composite_pair_is_skipped_and_its_witness_is_checked`
    fn class(
        &mut self,
        store: &CellStore<A>,
        overlap: &Overlap<A>,
    ) -> PairClass<A>;
}

/// The scheme that classes no pair, so a joining joins each pair.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct NoScheme;

impl<A> PairScheme<A> for NoScheme
where
    A: CellAlphabet,
{
    /// [`PairClass::Unclassed`] for every pair.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn class(
        &mut self,
        _store: &CellStore<A>,
        _overlap: &Overlap<A>,
    ) -> PairClass<A>
    {
        PairClass::Unclassed
    }
}

/// The confluence critical pairs of a store that grows by appended cells,
/// decided in [`join_critical_pairs`]'s order and resumed at the pair the last
/// decision stopped at.
///
/// A pair decided joined stays joined as the store grows: its certificate's
/// steps are steps of every larger store. So completion, which derives a cell
/// from the pair that parted and appends it, resumes at that pair rather than
/// deciding every earlier pair again: one round decides the pair that parted
/// and the pairs after it, the new cell's among them. A composite pair stays
/// composite as the store grows, because its witness's cell stays in the
/// store, so the joining skips it in every round and keeps its witness once.
///
/// # Specification
/// - requires: between two [`Self::resume_with`]s on one joining, the store
///   keeps its cells and their order and only gains cells after them.
/// - ensures: the certificates of the pairs decided joined since the joining
///   began or last answered [`Joinability::Joined`], in order; the position of
///   the next pair to decide; the count of pairs decided; and the composite
///   pairs skipped since the joining began or last gave them, each with its
///   witness.
/// - executable: none — a datum; [`Self::resume_with`] carries the predicate.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Self::resume_with`].
/// - witness: `completion::tests::a_resumed_joining_decides_no_joined_pair_again_1576`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PairJoining<A: CellAlphabet = SequentAlphabet>
{
    /// The certificates of the pairs decided joined, in order.
    certificates: Vec<Tracelet<A>>,
    /// The store position of the later cell of the next cell pair.
    later: usize,
    /// The store position of the earlier cell of the next cell pair.
    earlier: usize,
    /// How many of that cell pair's critical pairs are decided joined.
    within: usize,
    /// How many pairs have been decided.
    decided: usize,
    /// The composite pairs skipped, each with its witness, in order.
    composites: Vec<CompositePair<A>>,
}

impl<A> Default for PairJoining<A>
where
    A: CellAlphabet,
{
    /// A joining that has decided nothing.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self {
            certificates: Vec::new(),
            later: 0,
            earlier: 0,
            within: 0,
            decided: 0,
            composites: Vec::new(),
        }
    }
}

impl<A> PairJoining<A>
where
    A: CellAlphabet,
{
    /// A joining that has decided nothing.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new() -> Self
    {
        Self::default()
    }

    /// How many pairs the joining has decided, a pair decided again after its
    /// store grew counted again.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn decided(&self) -> PairDecisions
    {
        PairDecisions::from(self.decided)
    }

    /// The composite pairs that the joining skipped since it began or last
    /// gave them, in order, each with its witness.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn take_composites(&mut self) -> Vec<CompositePair<A>>
    {
        core::mem::take(&mut self.composites)
    }

    /// Decide the pairs of `store` from the pair the last decision stopped at,
    /// in [`join_critical_pairs`]'s order, each joined.
    ///
    /// # Specification
    /// - ensures: as [`Self::resume_with`] under [`NoScheme`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::resume_with`].
    /// - witness: `completion::tests::a_resumed_joining_decides_no_joined_pair_again_1576`
    #[inline]
    pub fn resume(
        &mut self,
        store: &CellStore<A>,
        budget: NormalizationBudget,
    ) -> Joinability<A>
    {
        self.resume_with(store, budget, &mut NoScheme)
    }

    /// Decide the pairs of `store` from the pair the last decision stopped at,
    /// in [`join_critical_pairs`]'s order, each classed by `scheme` first.
    ///
    /// # Specification
    /// - requires: as [`PairJoining`]: `store` is the store of the last resume,
    ///   grown only by cells appended after its others.
    /// - ensures: [`Joinability::Joined`] with the certificate of every pair
    ///   decided joined since the joining began or last answered `Joined`, when
    ///   every pair from the stopping one on joins or is skipped; otherwise the
    ///   first that does not, as `join_critical_pairs` reports it, the joining
    ///   stopped at it so the next resume decides it first. A pair that
    ///   `scheme` classes [`PairClass::Composite`] is skipped, and its witness
    ///   is kept for [`Self::take_composites`]. A pair that it classes
    ///   [`PairClass::Unclassed`] is joined. Each pair reached adds one to
    ///   [`Self::decided`].
    /// - panics: none.
    /// - intension: the store's cells read once into positions; the overlaps of
    ///   each cell pair enumerated once per resume that reaches it, the pairs
    ///   already decided skipped, and the root entries read without the
    ///   composition entries no pair is made of; a composite pair costs its
    ///   class and never a normalization, and its overlap moves into its
    ///   witness.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — over the toy alphabet, a joining stopped at a parting
    ///   pair and resumed over the store with a cell derived from it decides
    ///   that pair and the ones after it, fewer than a fresh joining of the
    ///   grown store decides to the same verdict, and reaches the verdict the
    ///   fresh joining does; deciding every pair again, or skipping the pair
    ///   that parted, changes a count or the verdict. A composite pair carries
    ///   no certificate and its witness replays, and with [`NoScheme`] the same
    ///   pair is joined.
    /// - witness: `completion::tests::a_resumed_joining_decides_no_joined_pair_again_1576`
    /// - witness: `completion::tests::joinability_separates_joined_divergent_and_undecided_pairs`
    /// - witness: `completion::tests::a_composite_pair_is_skipped_and_its_witness_is_checked`
    #[spec(
        captures: before = (self.decided, self.composites.len()),
        ensures: |output| self.decided >= before.0 && self.composites.len() >= before.1
            && self.composites.iter().skip(before.1).all(|pair| pair.replay(store).is_ok()) && match output {
            Joinability::Joined(ref certificates) => certificates.iter().all(|certificate|
                certificate.overlap.kind == OverlapKind::Confluence && bool::from(certificate.replay(store))),
            Joinability::Diverges { ref overlap, ref left, ref left_steps, ref right, ref right_steps } => overlap.kind == OverlapKind::Confluence && left != right
                && overlap.left_reduct(store).is_ok_and(|reduct| normalize(store, &reduct, budget).path == *left_steps)
                && overlap.right_reduct().is_ok_and(|reduct| normalize(store, &reduct, budget).path == *right_steps),
            Joinability::Undecided(ref overlap) => overlap.kind == OverlapKind::Confluence,
        },
    )]
    #[inline]
    pub fn resume_with<S>(
        &mut self,
        store: &CellStore<A>,
        budget: NormalizationBudget,
        scheme: &mut S,
    ) -> Joinability<A>
    where
        S: PairScheme<A>,
    {
        let cells: Vec<(CellId, &Cell<A>)> = store.iter().collect();
        while let Some(&later) = cells.get(self.later) {
            while self.earlier <= self.later {
                let Some(&earlier) = cells.get(self.earlier)
                else {
                    break;
                };
                let (root, mirrored) = if self.earlier < self.later {
                    (
                        root_overlaps_between(earlier, later),
                        interior_overlaps_between(later, earlier),
                    )
                }
                else {
                    (Vec::new(), Vec::new())
                };
                let pairs = root
                    .into_iter()
                    .chain(interior_overlaps_between(earlier, later))
                    .chain(mirrored)
                    .skip(self.within);
                for overlap in pairs {
                    self.decided = self.decided.saturating_add(1);
                    if let PairClass::Composite(below) = scheme.class(store, &overlap) {
                        self.composites.push(CompositePair { overlap, below });
                        self.within = self.within.saturating_add(1);
                        continue;
                    }
                    let (Ok(left_reduct), Ok(right_reduct)) =
                        (overlap.left_reduct(store), overlap.right_reduct())
                    else {
                        self.within = self.within.saturating_add(1);
                        continue;
                    };
                    let left = normalize(store, &left_reduct, budget);
                    let right = normalize(store, &right_reduct, budget);
                    if bool::from(left.exhausted) || bool::from(right.exhausted) {
                        return Joinability::Undecided(overlap);
                    }
                    if left.normal != right.normal {
                        return Joinability::Diverges {
                            overlap,
                            left: left.normal,
                            left_steps: left.path,
                            right: right.normal,
                            right_steps: right.path,
                        };
                    }
                    if let Maybe::Present(certificate) = joined(&overlap, left, right) {
                        self.certificates.push(certificate);
                    }
                    self.within = self.within.saturating_add(1);
                }
                self.earlier = self.earlier.saturating_add(1);
                self.within = 0;
            }
            self.later = self.later.saturating_add(1);
            self.earlier = 0;
        }
        Joinability::Joined(core::mem::take(&mut self.certificates))
    }
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
        core::cmp::Ordering::Greater => Maybe::Present((left, right)),
        core::cmp::Ordering::Less => Maybe::Present((right, left)),
        core::cmp::Ordering::Equal => Maybe::Absent(orientation::Absent::Unorientable),
    }
}

#[cfg(test)]
mod tests
{
    use gandr_theory_cell_complexes_tools::Toy;
    use gandr_theory_cell_complexes_tools::ToyAlphabet;
    use gandr_theory_cell_complexes_tools::ToyPos;
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

    #[test]
    fn a_pair_one_reduct_of_which_is_starved_is_neither_certified_nor_oriented()
    {
        let mut store = CellStore::<ToyAlphabet>::new();
        let _left_unit = store.insert(toy_cell(
            Toy::add(Toy::zero(), Toy::var("y")),
            Toy::var("y"),
        ));
        let _swap = store.insert(toy_cell(
            Toy::add(Toy::var("x"), Toy::zero()),
            Toy::add(Toy::zero(), Toy::var("x")),
        ));
        let outcome = complete(
            store.clone(),
            CompletionBudget::new(
                CompletionStepBudget::from(8_usize),
                CompletionCellBudget::from(8_usize),
                NormalizationBudget::from(0_usize),
            ),
        );
        assert_eq!(
            CompletionOutcome::Completed {
                store,
                derived: Vec::new(),
                certificates: Vec::new()
            },
            outcome,
            "`Zero` is normal, `add(Zero, Zero)` needs the step the budget withholds"
        );
    }

    #[test]
    fn a_derived_cell_reschedules_only_the_pairs_it_takes_part_in()
    {
        let mut store = CellStore::<ToyAlphabet>::new();
        let _left_unit = store.insert(toy_cell(
            Toy::add(Toy::zero(), Toy::var("y")),
            Toy::var("y"),
        ));
        let _successor = store.insert(toy_cell(
            Toy::add(Toy::var("x"), Toy::zero()),
            Toy::succ(Toy::var("x")),
        ));
        let outcome = complete(
            store,
            CompletionBudget::new(
                CompletionStepBudget::from(16_usize),
                CompletionCellBudget::from(8_usize),
                NormalizationBudget::from(8_usize),
            ),
        );
        assert!(bool::from(outcome.is_completed()), "{outcome:?}");
        assert_eq!(1, outcome.derived().len(), "{outcome:?}");
        assert_eq!(
            1,
            outcome.certificates().len(),
            "the mirror pair joins through the derived cell, once: {outcome:?}"
        );
    }

    #[test]
    fn a_derived_cell_is_paired_with_the_cells_it_overlaps()
    {
        let mut store = CellStore::<ToyAlphabet>::new();
        let _left_unit = store.insert(toy_cell(
            Toy::add(Toy::zero(), Toy::var("y")),
            Toy::var("y"),
        ));
        let _left_successor = store.insert(toy_cell(
            Toy::add(Toy::zero(), Toy::var("y")),
            Toy::succ(Toy::var("y")),
        ));
        let _one = store.insert(toy_cell(Toy::succ(Toy::zero()), Toy::zero()));
        let outcome = complete(
            store,
            CompletionBudget::new(
                CompletionStepBudget::from(16_usize),
                CompletionCellBudget::from(8_usize),
                NormalizationBudget::from(8_usize),
            ),
        );
        assert!(bool::from(outcome.is_completed()), "{outcome:?}");
        assert_eq!(1, outcome.derived().len(), "`succ(y)` is oriented to `y`");
        let pairs: Vec<(CellId, CellId)> = outcome
            .certificates()
            .iter()
            .map(|certificate| (certificate.overlap.left, certificate.overlap.right))
            .collect();
        assert_eq!(
            alloc::vec![
                (CellId::from(1_usize), CellId::from(0_usize)),
                (CellId::from(2_usize), CellId::from(3_usize)),
                (CellId::from(3_usize), CellId::from(2_usize)),
            ],
            pairs,
            "the derived cell meets `succ(Zero)` at the root, both ways, and joins"
        );
    }

    #[test]
    fn joinability_separates_joined_divergent_and_undecided_pairs()
    {
        let budget = NormalizationBudget::from(8_usize);
        let store_of = |cells: &[(Toy, Toy)]| {
            let mut store = CellStore::<ToyAlphabet>::new();
            for cell in cells {
                let _id = store.insert(toy_cell(cell.0.clone(), cell.1.clone()));
            }
            store
        };
        let left_unit = (Toy::add(Toy::zero(), Toy::var("y")), Toy::var("y"));
        let agreeing = store_of(&[
            left_unit.clone(),
            (Toy::add(Toy::var("x"), Toy::zero()), Toy::var("x")),
        ]);
        let Joinability::Joined(certificates) = join_critical_pairs(&agreeing, budget)
        else {
            panic!("both sides send `add(Zero, Zero)` to `Zero`");
        };
        assert_eq!(1, certificates.len(), "the pair and its mirror are one");
        assert!(
            certificates
                .iter()
                .all(|certificate| bool::from(certificate.replay(&agreeing)))
        );
        let disagreeing = store_of(&[
            left_unit.clone(),
            (
                Toy::add(Toy::var("x"), Toy::zero()),
                Toy::succ(Toy::var("x")),
            ),
        ]);
        let Joinability::Diverges { left, right, .. } = join_critical_pairs(&disagreeing, budget)
        else {
            panic!("`Zero` and `Succ(Zero)` are both normal");
        };
        assert_eq!(
            (Toy::zero(), Toy::succ(Toy::zero())),
            (left, right),
            "both normal forms are reported, the left cell's first"
        );
        let starved = store_of(&[
            left_unit.clone(),
            (
                Toy::add(Toy::var("x"), Toy::zero()),
                Toy::add(Toy::zero(), Toy::var("x")),
            ),
        ]);
        assert!(matches!(
            join_critical_pairs(&starved, NormalizationBudget::from(0_usize)),
            Joinability::Undecided(_)
        ));
        assert!(
            matches!(
                join_critical_pairs(&starved, budget),
                Joinability::Joined(ref certificates) if certificates.len() == 1
            ),
            "the same pair joins once its reduct may take its step"
        );
        assert_eq!(
            Joinability::Joined(Vec::new()),
            join_critical_pairs(
                &store_of(&[left_unit, (Toy::succ(Toy::var("x")), Toy::var("x"))]),
                budget
            ),
            "cells that never overlap join with nothing to certify"
        );
    }

    #[test]
    fn a_resumed_joining_decides_no_joined_pair_again_1576()
    {
        let budget = NormalizationBudget::from(8_usize);
        let mut store = CellStore::<ToyAlphabet>::new();
        // Two units that agree at `add(Zero, Zero)`, then a third rule that
        // parts from the first there: `Zero` against `Succ(Zero)`.
        for (lhs, rhs) in [
            (Toy::add(Toy::zero(), Toy::var("y")), Toy::var("y")),
            (Toy::add(Toy::var("x"), Toy::zero()), Toy::var("x")),
            (
                Toy::add(Toy::var("x"), Toy::zero()),
                Toy::succ(Toy::var("x")),
            ),
        ] {
            let _id = store.insert(toy_cell(lhs, rhs));
        }
        let mut joining = PairJoining::new();
        let Joinability::Diverges { left, right, .. } = joining.resume(&store, budget)
        else {
            panic!("`Zero` and `Succ(Zero)` part");
        };
        let stopped = usize::from(joining.decided());
        let Maybe::Present((lhs, rhs)) = orient::<ToyAlphabet>(left, right)
        else {
            panic!("`Succ(Zero)` is above `Zero`");
        };
        let _derived = store.insert(toy_cell(lhs, rhs));
        let resumed = joining.resume(&store, budget);
        let mut fresh = PairJoining::new();
        assert_eq!(
            fresh.resume(&store, budget),
            resumed,
            "resuming reaches the verdict a fresh joining of the grown store does"
        );
        // The first resume decides the units' pair and the parting one. The
        // round decides the parting pair again, now joined through the derived
        // cell, and the two `add(x, Zero)` rules' pair after it, which parts at
        // `x` against `Succ(x)`; a fresh joining decides the units' pair a
        // second time on the way.
        let round = usize::from(joining.decided()).saturating_sub(stopped);
        assert_eq!(
            (stopped, round, usize::from(fresh.decided())),
            (2, 2, 3),
            "the round decides the pair that parted and those after it"
        );
    }

    #[test]
    fn a_composite_pair_is_skipped_and_its_witness_is_checked()
    {
        /// The criterion as its definition states it: the first position
        /// strictly below the seam, in the listing's order, at which a cell
        /// fires, and the first such cell.
        struct Below;

        impl PairScheme<ToyAlphabet> for Below
        {
            /// The first step below the seam.
            ///
            /// # Specification
            /// trivial.
            fn class(
                &mut self,
                store: &CellStore<ToyAlphabet>,
                overlap: &Overlap<ToyAlphabet>,
            ) -> PairClass<ToyAlphabet>
            {
                for at in ToyAlphabet::command_positions(&overlap.peak) {
                    if ToyAlphabet::position_order(&overlap.seam, &at) != PositionOrder::Encloses {
                        continue;
                    }
                    for (cell, rule) in store.iter() {
                        if let Maybe::Present(_) = rewrite_at(rule, &overlap.peak, &at) {
                            return PairClass::Composite(CellApp { cell, at });
                        }
                    }
                }
                PairClass::Unclassed
            }
        }

        let budget = NormalizationBudget::from(8_usize);
        let mut store = CellStore::<ToyAlphabet>::new();
        // The second rule meets the first's addition at the addition's root,
        // instantiating `x` to `add(Zero, Zero)`, which the second rule
        // rewrites again one position down: that pair is composite. The same
        // rule meets the inner `add(Zero, Zero)` itself, with nothing below
        // it to rewrite: that pair is prime, and the third rule joins both.
        let peak = Toy::succ(Toy::add(Toy::add(Toy::zero(), Toy::zero()), Toy::zero()));
        let first = store.insert(toy_cell(peak, Toy::zero()));
        let second = store.insert(toy_cell(
            Toy::add(Toy::var("x"), Toy::zero()),
            Toy::var("x"),
        ));
        let third = store.insert(toy_cell(Toy::succ(Toy::zero()), Toy::zero()));
        let at = |steps: &[usize]| {
            let steps: Vec<gandr_theory_cell_complexes::PositionStep> =
                steps.iter().copied().map(Into::into).collect();
            ToyAlphabet::position_at_path(&steps)
        };
        let (addition, inner) = (at(&[0]), at(&[0, 0]));
        let seams = |certificates: &[Tracelet<ToyAlphabet>]| -> Vec<ToyPos> {
            certificates
                .iter()
                .map(|certificate| certificate.overlap.seam.clone())
                .collect()
        };
        let mut plain = PairJoining::new();
        let Joinability::Joined(every) = plain.resume(&store, budget)
        else {
            panic!("both pairs reach `Zero`");
        };
        let every = seams(&every);
        assert!(
            every.len() == 2 && every.contains(&addition) && every.contains(&inner),
            "with no scheme, the pair at the addition and the pair inside it both join: {every:?}"
        );
        let mut joining = PairJoining::new();
        let Joinability::Joined(certificates) = joining.resume_with(&store, budget, &mut Below)
        else {
            panic!("the prime pair reaches `Zero`");
        };
        assert_eq!(
            (seams(&certificates), usize::from(joining.decided())),
            (alloc::vec![inner.clone()], 2),
            "both pairs are counted and only the prime one is joined"
        );
        let composites = joining.take_composites();
        let [ref composite] = *composites
        else {
            panic!("one composite pair: {composites:?}");
        };
        assert_eq!(
            (&composite.overlap.seam, &composite.below),
            (&addition, &CellApp {
                cell: second,
                at: inner
            }),
            "the pair at the addition is composite by the second rule one position down"
        );
        assert_eq!(composite.replay(&store), Ok(()), "the witness replays");
        let refused = |change: &dyn Fn(&mut CompositePair<ToyAlphabet>)| {
            let mut forged = composite.clone();
            change(&mut forged);
            forged.replay(&store)
        };
        assert_eq!(
            [
                refused(&|forged| forged.below.at = addition.clone()),
                refused(&|forged| forged.below.cell = third),
                refused(&|forged| forged.overlap.left = third),
                refused(&|forged| forged.overlap.kind = OverlapKind::Composition),
                composite.replay(&CellStore::new()),
            ],
            [
                Err(CompositeRefusal::NotBelow),
                Err(CompositeRefusal::Unmatched),
                Err(CompositeRefusal::NotAPeak),
                Err(CompositeRefusal::NotAConfluence),
                Err(CompositeRefusal::UnissuedCell(first)),
            ],
            "a forged witness is refused by name"
        );
    }
}
