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
//! past the refusal never looked up. Each hinted import is offered its removal
//! as a quick fix, and every hinted import of the document at once when it
//! holds several.

use alloc::collections::BTreeMap;
use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_render_remote::ByteOffset;
use gandr_surface_render_remote::LineIndex;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;
use serde::Deserialize as _;
use serde_json::Value;

use crate::goto::ranged;
use crate::position::Range;
use crate::protocol::CodeAction;
use crate::protocol::Diagnostic;
use crate::protocol::DiagnosticTag;
use crate::protocol::DocumentUri;
use crate::protocol::Severity;
use crate::protocol::TextEdit;
use crate::protocol::WorkspaceEdit;

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

/// The quick fixes removing the unused imports of the document at `uri` that
/// `published` hints and `asked` meets, written in `text` and ranged through
/// `index`.
///
/// # Specification
/// - requires: `published` are the diagnostics last published for `text`,
///   `index` was built over `text`, and `diagnostics` are the request's, each
///   as the client sent it.
/// - ensures: for each [`UNUSED_IMPORT`] hint of `published` whose range meets
///   `asked` (neither ends before the other starts), in order, a preferred
///   quick fix titled ``Remove the unused import `address` ``, deleting the
///   import as [`deletion`] spans it and naming each of `diagnostics` coded
///   [`UNUSED_IMPORT`] whose range meets the hint's. Then, when one was offered
///   and `published` hints more than one import, the quick fix `Remove all
///   unused imports`, deleting each alike in one edit and naming each such
///   diagnostic the hints' ranges meet.
/// - provides: the import removals of `textDocument/codeAction`.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a range over an unused import is offered its removal,
///   which leaves a document that still checks with the import's line gone; a
///   range elsewhere is offered none; a document hinting two imports is offered
///   their removal at once besides.
/// - witness: `server::tests::an_unused_import_is_offered_its_removal_1116`
#[spec(ensures: |ret| ret.iter().all(|action| action.kind == "quickfix"
    && action.edit.changes.as_ref().is_some_and(|changes| changes.len() == 1)))]
#[must_use]
pub fn removals(
    uri: &DocumentUri,
    published: &[Diagnostic],
    (text, index): (SourceText<'_>, &LineIndex<'_>),
    (asked, diagnostics): (Range, &[Value]),
) -> Vec<CodeAction>
{
    let meets = |range: Range, other: Range| range.start <= other.end && other.start <= range.end;
    let hints: Vec<&Diagnostic> = published
        .iter()
        .filter(|hint| hint.code.as_deref() == Some(UNUSED_IMPORT))
        .collect();
    let answered = |ranges: &[Range]| -> Vec<Value> {
        diagnostics
            .iter()
            .filter(|diagnostic| {
                diagnostic.get("code").and_then(Value::as_str) == Some(UNUSED_IMPORT)
                    && diagnostic
                        .get("range")
                        .and_then(|range| Range::deserialize(range).ok())
                        .is_some_and(|range| ranges.iter().any(|&hinted| meets(range, hinted)))
            })
            .cloned()
            .collect()
    };
    let removal = |title: String, hinted: &[&Diagnostic], is_preferred: bool| {
        let ranges: Vec<Range> = hinted.iter().map(|hint| hint.range).collect();
        CodeAction {
            title,
            kind: "quickfix",
            diagnostics: answered(&ranges),
            is_preferred,
            edit: WorkspaceEdit::of(BTreeMap::from([(
                uri.clone(),
                ranges
                    .iter()
                    .map(|&range| TextEdit {
                        range: deletion(range, (text, index)),
                        new_text: String::new(),
                    })
                    .collect(),
            )])),
        }
    };
    let mut offered: Vec<CodeAction> = hints
        .iter()
        .filter(|hint| meets(hint.range, asked))
        .map(|&hint| {
            let address = hint.message.split('`').nth(1_usize).unwrap_or_default();
            removal(
                format!("Remove the unused import `{address}`"),
                &[hint],
                true,
            )
        })
        .collect();
    if !offered.is_empty() && hints.len() > 1_usize {
        offered.push(removal("Remove all unused imports".into(), &hints, false));
    }
    offered
}

/// The range deleting the import written at `range` of `text`, ranged through
/// `index`.
///
/// # Specification
/// - requires: `index` was built over `text`.
/// - ensures: when only blanks share the import's lines, from the start of its
///   first line through the line break ending its last, or to the end of the
///   text when none ends it; otherwise `range` itself.
/// - fails: never.
/// - panics: none.
/// - executable: none — the line search reads the text the clause names.
///
/// # Adequacy
/// - hypothesis: L3 — an import alone on its line takes the line with it.
/// - witness: `server::tests::an_unused_import_is_offered_its_removal_1116`
fn deletion(
    range: Range,
    (text, index): (SourceText<'_>, &LineIndex<'_>),
) -> Range
{
    let written = <&str>::from(text);
    let start = usize::from(range.start.byte(index));
    let end = usize::from(range.end.byte(index));
    let (Some(before), Some(after)) = (written.get(.. start), written.get(end ..))
    else {
        return range;
    };
    let line_start = before
        .rfind('\n')
        .map_or(0_usize, |at| at.saturating_add(1_usize));
    let (rest, through) = after.find('\n').map_or((after, after.len()), |at| {
        (
            after.get(.. at).unwrap_or(after),
            at.saturating_add(1_usize),
        )
    });
    let alone = before
        .get(line_start ..)
        .is_some_and(|lead| lead.trim().is_empty())
        && rest.trim().is_empty();
    if !alone {
        return range;
    }
    Range::of_bytes(
        index,
        ByteOffset::from(line_start),
        ByteOffset::from(end.saturating_add(through)),
    )
    .unwrap_or(range)
}
