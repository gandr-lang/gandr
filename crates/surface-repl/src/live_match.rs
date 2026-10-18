//! Transcript presentation for a retained live match.

use anodized::spec;
use gandr_core_checker::Exhaustiveness;
use gandr_core_nbe::Selection;
use gandr_core_term::pattern::BranchStatus;
use gandr_surface_render_remote::OutKind;
use gandr_surface_render_remote::TranscriptBlock;
use gandr_surface_session::MatchAnalysis;

/// Render per-arm answers, ordered selection and independent coverage.
///
/// # Specification
/// - requires: the analysis belongs to the match being presented.
/// - ensures: every arm is presented in order, followed by selection and
///   coverage. A possible first arm is reported as stuck, not taken.
/// - provides: one transcript representation for terminal and remote faces.
/// - fails: never; a coverage refusal remains a diagnostic.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an external consumer observes possible branches before a
///   fill and distinct yes/no branches after it, through the real writer.
/// - witness: `tests::live_match::a_fill_updates_the_external_match_transcript`
#[spec(ensures: |ret| ret.lines.len() == analysis.branches().len().saturating_add(2))]
#[inline]
#[must_use]
pub fn encode_match(analysis: &MatchAnalysis) -> TranscriptBlock
{
    let mut lines = Vec::with_capacity(analysis.branches().len().saturating_add(2));
    for (arm, status) in analysis.branches().iter().enumerate() {
        let word = match *status {
            BranchStatus::Satisfied => "yes",
            BranchStatus::Refuted => "no",
            BranchStatus::Possibly => "possibly",
        };
        lines.push((OutKind::Info, format!("arm {arm}: {word}")));
    }
    let selected = match *analysis.selection() {
        Selection::Taken { arm, .. } => {
            (OutKind::Info, format!("selected arm {}", usize::from(arm)))
        },
        Selection::Indeterminate { arm } => {
            (OutKind::Stuck, format!("held at arm {}", usize::from(arm)))
        },
        Selection::Exhausted => (OutKind::Stuck, String::from("no arm selected")),
    };
    lines.push(selected);
    lines.push(match *analysis.coverage() {
        Ok(ref coverage) => {
            let word = match coverage.exhaustiveness() {
                Exhaustiveness::Exhaustive => "yes",
                Exhaustiveness::Inexhaustive => "no",
                Exhaustiveness::Possibly => "possibly",
            };
            (OutKind::Info, format!("exhaustive: {word}"))
        },
        Err(ref fault) => (OutKind::Diag, format!("coverage unavailable: {fault:?}")),
    });
    TranscriptBlock {
        lines,
        ..TranscriptBlock::default()
    }
}
