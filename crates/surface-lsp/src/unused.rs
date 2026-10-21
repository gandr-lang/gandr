//! Unused binders: each binder a document writes that no use refers to, as a
//! hint the editor fades.
//!
//! The binders are the judgement's own, kept beside its verdicts: a lambda's
//! or a bind's binder no variable reads, written in a declaration the checker
//! accepted. Leaving a linear binder or a consumable capability unused is the
//! checker's refusal, so an accepted declaration holds none; a refused one is
//! not answered. A name starting with `_` says it is meant to go unused and
//! is not marked.

use alloc::format;
use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_render_remote::LineIndex;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;

use crate::goto::ranged;
use crate::protocol::Diagnostic;
use crate::protocol::DiagnosticTag;
use crate::protocol::Severity;

/// The code an unused binder's hint carries.
pub const UNUSED_BINDER: &str = "UnusedBinder";

/// The hints marking each of `binders`, written in `text` and ranged through
/// `index`.
///
/// # Specification
/// - requires: `binders` are the unused binders a recheck of `text` answered,
///   and `index` was built over `text`.
/// - ensures: one hint per binder whose name does not start with `_`, in order:
///   at the name, severity hint, code [`UNUSED_BINDER`], the message `` `name`
///   is never used ``, tagged unnecessary.
/// - provides: the hints published beside a document's judgement.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an unused parameter, `run` binder, pattern variable and
///   lambda binder are hinted; a used binder, a name starting with `_`, an
///   unused fork end and an unused consumable capability are not.
/// - witness: `server::tests::a_binder_no_use_refers_to_is_published_unnecessary`
#[spec(ensures: |ret| ret.iter().all(|hint| hint.severity == Severity::HINT
    && hint.tags == [DiagnosticTag::UNNECESSARY]))]
#[must_use]
pub fn unused(
    binders: &[ByteSpan],
    text: SourceText<'_>,
    index: &LineIndex<'_>,
) -> Vec<Diagnostic>
{
    let written = <&str>::from(text);
    binders
        .iter()
        .filter_map(|&span| {
            let name = written.get(usize::from(span.start()) .. usize::from(span.end()))?;
            if name.starts_with('_') {
                return None;
            }
            let mut hint = Diagnostic::new(
                ranged(index, span)?,
                Severity::HINT,
                format!("`{name}` is never used"),
            );
            hint.code = Some(UNUSED_BINDER.into());
            hint.tags = Vec::from([DiagnosticTag::UNNECESSARY]);
            Some(hint)
        })
        .collect()
}
