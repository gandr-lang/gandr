//! The check of a model's proposal: the trial of the filled document against
//! the diagnostics that the document published.
//!
//! The proposals themselves, and the surfaces through which an editor reads
//! them, are in `gandr-surface-lsp-base`.

use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_lsp_base::proposal::ErrorCount;
use gandr_surface_lsp_base::proposal::ProposalRefusal;
use gandr_surface_lsp_base::proposal::errors;

use crate::protocol::Diagnostic;
use crate::recheck::Reached;
use crate::recheck::Tried;

/// The diagnostics of `tried`, the trial of a fill, when it checks against a
/// document whose published diagnostics are `published`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the trial's diagnostics exactly when it judged the filled
///   document and they carry no error, or fewer errors than `published`: a fill
///   that settles a hole adds none, and a fill that repairs one refusal of
///   several removes one. A fill refused whole or faulted never checks, and is
///   refused as [`ProposalRefusal::Unchecked`] with its trial's diagnostics.
/// - provides: the gate every proposal passes before the editor sees it.
/// - fails: [`ProposalRefusal::Unchecked`] for a fill that does not check.
/// - panics: none.
///
/// # Errors
/// [`ProposalRefusal::Unchecked`] for a fill that does not check.
///
/// # Adequacy
/// - hypothesis: L3 — a fill that settles the document, one that leaves its
///   refusal, and one refused whole are kept, refused and refused.
/// - witness: `gandr-surface-lsp::server::tests::a_proposal_is_kept_only_once_it_checks`
#[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|kept| {
    let after = errors(kept);
    after == ErrorCount::default() || after < errors(published)
}))]
#[inline]
pub fn check(
    tried: Tried,
    published: &[Diagnostic],
) -> Result<Vec<Diagnostic>, ProposalRefusal>
{
    let after = errors(&tried.diagnostics);
    if tried.reached == Reached::Judged
        && (after == ErrorCount::default() || after < errors(published))
    {
        Ok(tried.diagnostics)
    }
    else {
        Err(ProposalRefusal::Unchecked {
            diagnostics: tried.diagnostics,
        })
    }
}
