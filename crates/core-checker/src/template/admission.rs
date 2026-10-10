//! Producer transport into the additive kernel judgment; no admission
//! authority.
//!
//! `Candidate::admission_candidate` exports only the compacted skeleton,
//! distinct arms and source-derived rows. The kernel checks inheritance and
//! transparency itself. Its instance judgment uses exact content identities
//! without re-deriving the local equation. The release observer's `COMPRESSED`
//! rows price serial and scoped-thread admission, charging materialized
//! consumer-side work separately. Complete-certificate readmission retains
//! ordinary replay; this adapter grants no endpoint-typing authority.

use gandr_kernel_core::admission::Choice;
use gandr_kernel_core::admission::Guard;
use gandr_kernel_core::admission::Point;
use gandr_kernel_core::admission::Proposal;

use super::Candidate;
use super::PeakRoots;
use super::StageError;
use super::Step;
use super::TermId;
use super::Vec;

/// A kernel proposal and independent point-ordered rows for harvested members.
pub struct AdmissionCandidate
{
    /// Untrusted schema; only kernel checking can establish inheritance.
    pub proposal: Proposal,
    /// Source-derived choices, retaining no member syntax.
    pub rows: Vec<Vec<Choice>>,
}

impl Candidate
{
    /// Translate the analyzed skeleton and source columns into kernel input.
    ///
    /// # Specification
    /// - ensures: every row selects the corresponding source arm in point
    ///   order; retains no producer cache as evidence. Target-only points
    ///   refuse.
    /// - fails: an unrooted point or malformed graph/column.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns `StageError::InvalidCertificate` or `StageError::Unbalanced`.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — all harvested rows compare against their original
    ///   sides, while target-only candidates cannot mint schema input.
    /// - witness: `template::tests::compressed_admission_matches_plain_families`
    #[inline]
    pub fn admission_candidate(&self) -> Result<AdmissionCandidate, StageError>
    {
        if !matches!(self.peak_roots, PeakRoots::Complete) {
            return Err(StageError::InvalidCertificate);
        }
        let mut retained = Vec::from(self.sides);
        retained.extend(
            self.entries
                .iter()
                .flat_map(|entry| entry.arms.keys().copied()),
        );
        let (graph, map) = self.graph.compact(&retained)?;
        let mut rows =
            alloc::vec![Vec::with_capacity(self.entries.len()); usize::from(self.cost.members)];
        let mut arms = Vec::with_capacity(self.entries.len());
        for (entry, column) in self.entries.iter().zip(&self.arms) {
            let dictionary: Vec<_> = entry.arms.keys().copied().collect();
            for (row, arm) in rows.iter_mut().zip(column) {
                let guard = dictionary
                    .binary_search(arm)
                    .map_err(|_insertion| StageError::Unbalanced)?;
                row.push(Choice {
                    point: Point(usize::from(entry.point)),
                    guard: Guard(guard),
                });
            }
            arms.push(
                dictionary
                    .into_iter()
                    .map(|id| {
                        map.get(&id)
                            .map(|id| TermId(id.0))
                            .ok_or(StageError::Unbalanced)
                    })
                    .collect::<Result<_, _>>()?,
            );
        }
        let [source, target] = self.sides;
        let source = *map.get(&source).ok_or(StageError::Unbalanced)?;
        let target = *map.get(&target).ok_or(StageError::Unbalanced)?;
        let equation = Step {
            source: TermId(source.0),
            target: TermId(target.0),
            rule: self.rule,
        };
        let proposal = graph.admission_proposal(equation, arms)?;
        Ok(AdmissionCandidate { proposal, rows })
    }
}
