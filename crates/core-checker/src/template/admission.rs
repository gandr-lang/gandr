//! Producer transport into the additive kernel judgment; no admission
//! authority.
//!
//! `Candidate::admission_candidate` exports only the skeleton, distinct arms
//! and source-derived rows, as the canonical proposal: arms in guard order,
//! which is first occurrence in member order, and nodes and classifiers in the
//! canonical order `Graph::admission_proposal` states. `Template::proposal`
//! emits the same proposal from a produced or drafted template. The kernel
//! checks inheritance and transparency itself. Its instance judgment uses
//! exact content identities without re-deriving the local equation. The
//! release observer's `COMPRESSED` rows price serial and scoped-thread
//! admission, charging materialized consumer-side work separately.
//! Complete-certificate readmission retains ordinary replay; this adapter
//! grants no endpoint-typing authority.
//!
//! A member's row is the deep-inference [`TemplateRow`]: the guard at each
//! entry, in entry order. The kernel keeps its own input, a [`Choice`] for
//! each point. [`kernel_choices`] writes the kernel's choices for a row at
//! the kernel call, so the kernel does not depend on the producer's types.

use anodized::spec;
use gandr_kernel_core::admission::Choice;
use gandr_kernel_core::admission::Guard;
use gandr_kernel_core::admission::Point;
use gandr_kernel_core::admission::Proposal;
use gandr_theory_deep_inference::TemplateRow;

use super::Candidate;
use super::Entry;
use super::GuardId;
use super::Id;
use super::StageError;
use super::Template;
use super::Vec;

/// A kernel proposal and independent point-ordered rows for harvested members.
pub struct AdmissionCandidate
{
    /// Untrusted schema; only kernel checking can establish inheritance.
    pub proposal: Proposal,
    /// The row of each member, in member order, retaining no member syntax.
    pub rows: Vec<TemplateRow>,
}

/// Append to `into` the kernel's choices for `row`: the guard of each entry
/// at the point of that entry, in entry order.
///
/// An entry's point is its place among the template's entries, because the
/// generalization numbers each point when it adds the point's entry.
///
/// # Specification
/// - ensures: `into` keeps its choices and gains one choice for each guard of
///   `row`, the guard at place `p` as the choice at point `p`.
/// - panics: none.
/// - intension: linear in the guards; allocates only when `into` grows.
///
/// # Adequacy
/// - hypothesis: L2 — the kernel admits each harvested member under the choices
///   of its row, so a guard at the wrong point refuses the member.
/// - witness: `template::tests::compressed_admission_matches_plain_families`
#[inline]
#[spec(captures: before = into.len(), ensures: |_| into.get(before ..).is_some_and(|added|
    added.len() == row.guards().len()
        && added.iter().zip(row.guards()).enumerate().all(|(point, (choice, guard))|
            choice.point == Point(point) && choice.guard.0 == usize::from(*guard))))]
pub fn kernel_choices(
    row: &TemplateRow,
    into: &mut Vec<Choice>,
)
{
    into.extend(
        row.guards()
            .iter()
            .enumerate()
            .map(|(point, guard)| Choice {
                point: Point(point),
                guard: Guard(usize::from(*guard)),
            }),
    );
}

impl Entry
{
    /// List this point's arms in guard order.
    ///
    /// # Specification
    /// - ensures: position `g` holds the arm guarded by `g`; every arm appears
    ///   once.
    /// - fails: Unbalanced when the guards are not exactly `0 .. arms`.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `StageError::Unbalanced`.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every harvested row's guard is checked by the kernel
    ///   against the arm at that position, so a misplaced arm refuses a member.
    /// - witness: `template::tests::compressed_admission_matches_plain_families`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body places every arm once; the check reads each arm's slot once"
        )
    )]
    #[spec(ensures: |output| output.as_ref().ok().is_none_or(|arms| arms.len() == self.arms.len()
        && self.arms.iter().all(|(id, guard)| arms.get(usize::from(*guard)) == Some(id))))]
    pub(super) fn ordered(&self) -> Result<Vec<Id>, StageError>
    {
        let mut arms = alloc::vec![None; self.arms.len()];
        for (id, guard) in &self.arms {
            let slot = arms
                .get_mut(usize::from(*guard))
                .ok_or(StageError::Unbalanced)?;
            if slot.replace(*id).is_some() {
                return Err(StageError::Unbalanced);
            }
        }
        arms.into_iter()
            .map(|arm| arm.ok_or(StageError::Unbalanced))
            .collect()
    }
}

impl Template
{
    /// Emit this template's canonical kernel proposal.
    ///
    /// # Specification
    /// - ensures: the sides, decision and arms of this template in guard order,
    ///   numbered canonically; equal to the analyzed candidate's proposal for
    ///   the same members.
    /// - fails: a malformed graph or guard partition.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `StageError::Unbalanced`.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every drafted family of the edit-pair corpus compares
    ///   this proposal with a fresh run's byte for byte.
    /// - witness: `template::tests::drafts_equal_fresh_runs_across_the_edit_traces`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|proposal|
        proposal.equation.rule == self.rule
        && proposal.arms.iter().zip(&self.entries).all(|(arms, entry)| arms.len() == entry.arms.len())))]
    pub fn proposal(&self) -> Result<Proposal, StageError>
    {
        let arms = self
            .entries
            .iter()
            .map(Entry::ordered)
            .collect::<Result<Vec<_>, _>>()?;
        self.graph.admission_proposal(self.sides, self.rule, &arms)
    }
}

impl Candidate
{
    /// Translate the analyzed skeleton and source columns into kernel input.
    ///
    /// # Specification
    /// - ensures: every row holds one guard for each entry, in entry order, and
    ///   the guard selects the member's source arm at that entry; arms are in
    ///   guard order and the proposal is canonical; retains no producer cache
    ///   as evidence.
    /// - fails: a malformed graph or column.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `StageError::Unbalanced`.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — all harvested rows compare against their original
    ///   sides; analysis refuses every family with a target-only point, so no
    ///   candidate carries one into schema input.
    /// - witness: `template::tests::compressed_admission_matches_plain_families`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|candidate|
        candidate.proposal.equation.rule == self.rule
        && candidate.proposal.arms.len() == self.entries.len()
        && candidate.rows.len() == usize::from(self.cost.members)
        && candidate.rows.iter().all(|row| row.guards().len() == self.entries.len()
            && row.guards().iter().zip(&candidate.proposal.arms).all(|(guard, arms)|
                usize::from(*guard) < arms.len()))))]
    pub fn admission_candidate(&self) -> Result<AdmissionCandidate, StageError>
    {
        let mut guards: Vec<Vec<GuardId>> =
            core::iter::repeat_with(|| Vec::with_capacity(self.entries.len()))
                .take(usize::from(self.cost.members))
                .collect();
        let mut arms = Vec::with_capacity(self.entries.len());
        for (entry, column) in self.entries.iter().zip(&self.arms) {
            for (row, arm) in guards.iter_mut().zip(column) {
                row.push(*entry.arms.get(arm).ok_or(StageError::Unbalanced)?);
            }
            arms.push(entry.ordered()?);
        }
        let proposal = self
            .graph
            .admission_proposal(self.sides, self.rule, &arms)?;
        Ok(AdmissionCandidate {
            proposal,
            rows: guards.into_iter().map(TemplateRow::from).collect(),
        })
    }
}
