//! Unused binders and imports: each binder a document writes that no use
//! refers to, and each import no name is read through, as a hint the editor
//! fades.
//!
//! The binders are the judgement's own, kept beside its verdicts: a lambda's
//! or a bind's binder no variable reads, written in a declaration the checker
//! accepted. Leaving a linear binder or a consumable capability unused is the
//! checker's refusal, so an accepted declaration holds none; a refused one is
//! not answered. A name starting with `_` says it is meant to go unused and
//! is not marked.
//!
//! The imports are the lowering's: each path import of the document that no
//! name lookup was answered through, whether the name was read unqualified,
//! through the import's alias, as a dotted path whose module the import
//! brought into the unit, or as a method, a model's theory or an include. A
//! document holding a declaration the lowering refused answers none, the names
//! past the refusal never looked up.

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

/// The code an unused import's hint carries.
pub const UNUSED_IMPORT: &str = "UnusedImport";

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

/// The hints marking each of `imports`, written in `text` and ranged through
/// `index`.
///
/// # Specification
/// - requires: `imports` are the imports a recheck of `text` answered no name
///   lookup reached, and `index` was built over `text`.
/// - ensures: one hint per import, in order: over the whole import, severity
///   hint, code [`UNUSED_IMPORT`], the message ``import `address` is never
///   used`` naming the address written between its quotes, tagged unnecessary.
/// - provides: the hints published beside a document's judgement.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an import nothing is read through is hinted; an import a
///   name is read through is not.
/// - witness: `server::tests::an_import_no_lookup_reaches_is_published_unnecessary_1116`
#[spec(ensures: |ret| ret.iter().all(|hint| hint.severity == Severity::HINT
    && hint.tags == [DiagnosticTag::UNNECESSARY]))]
#[must_use]
pub fn unreached(
    imports: &[ByteSpan],
    text: SourceText<'_>,
    index: &LineIndex<'_>,
) -> Vec<Diagnostic>
{
    let written = <&str>::from(text);
    imports
        .iter()
        .filter_map(|&span| {
            let import = written.get(usize::from(span.start()) .. usize::from(span.end()))?;
            let address = import.split('"').nth(1_usize).unwrap_or(import);
            let mut hint = Diagnostic::new(
                ranged(index, span)?,
                Severity::HINT,
                format!("import `{address}` is never used"),
            );
            hint.code = Some(UNUSED_IMPORT.into());
            hint.tags = Vec::from([DiagnosticTag::UNNECESSARY]);
            Some(hint)
        })
        .collect()
}
