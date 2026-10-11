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

use anodized::spec;
use gandr_kernel_core::admission::Choice;
use gandr_kernel_core::admission::Guard;
use gandr_kernel_core::admission::Point;
use gandr_kernel_core::admission::Proposal;

use super::Candidate;
use super::Entry;
use super::Id;
use super::StageError;
use super::Template;
use super::Vec;

/// A kernel proposal and independent point-ordered rows for harvested members.
pub struct AdmissionCandidate
{
    /// Untrusted schema; only kernel checking can establish inheritance.
    pub proposal: Proposal,
    /// Source-derived choices, retaining no member syntax.
    pub rows: Vec<Vec<Choice>>,
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
    /// - ensures: every row selects the corresponding source arm in point
    ///   order; arms are in guard order and the proposal is canonical; retains
    ///   no producer cache as evidence.
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
        && candidate.rows.iter().all(|row| row.len() == self.entries.len()
            && row.iter().zip(&self.entries).zip(&candidate.proposal.arms).all(|((choice, entry), arms)|
                choice.point == Point(usize::from(entry.point)) && choice.guard.0 < arms.len()))))]
    pub fn admission_candidate(&self) -> Result<AdmissionCandidate, StageError>
    {
        let mut rows =
            alloc::vec![Vec::with_capacity(self.entries.len()); usize::from(self.cost.members)];
        let mut arms = Vec::with_capacity(self.entries.len());
        for (entry, column) in self.entries.iter().zip(&self.arms) {
            for (row, arm) in rows.iter_mut().zip(column) {
                let guard = entry.arms.get(arm).ok_or(StageError::Unbalanced)?;
                row.push(Choice {
                    point: Point(usize::from(entry.point)),
                    guard: Guard(usize::from(*guard)),
                });
            }
            arms.push(entry.ordered()?);
        }
        let proposal = self
            .graph
            .admission_proposal(self.sides, self.rule, &arms)?;
        Ok(AdmissionCandidate { proposal, rows })
    }
}
