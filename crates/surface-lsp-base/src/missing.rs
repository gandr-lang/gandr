//! Missing imports: the quick fixes importing a source that declares a name
//! the document writes and nothing in scope declares.
//!
//! The lowering refuses a name that names nothing, and the refusal is
//! published as an [`UNRESOLVED_NAME`] diagnostic over the name itself. A
//! code-action request can meet such a diagnostic. Then the server offers one
//! quick fix for each source that can bring the name into scope. Each such
//! source is in a project that an opened folder roots, and the document does
//! not import it. The quick fix writes its import. The sources and their names
//! are the ones a completion offers from ([`Elsewhere`]), and
//! a source is admitted as the completion admits it: by the slot the name is
//! written in ([`unimported_as`]), so a name written as a type finds a family
//! and a name written as a value finds a value or a constructor.

use alloc::collections::BTreeMap;
use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_grammar::Pbg;
use gandr_surface_render_remote::LineIndex;
use gandr_surface_syntax::SourceText;
use serde::Deserialize as _;
use serde_json::Value;

use crate::elsewhere::Elsewhere;
use crate::elsewhere::Unimported;
use crate::elsewhere::unimported_as;
use crate::inline::Labeled;
use crate::inline::Slot;
use crate::position::Range;
use crate::protocol::CodeAction;
use crate::protocol::Diagnostic;
use crate::protocol::DocumentUri;
use crate::protocol::WorkspaceEdit;

/// The code the refusal of a name that names nothing carries.
pub const UNRESOLVED_NAME: &str = "UnresolvedName";

/// The quick fixes that import a source for each name that names nothing.
///
/// Each name is one of the document at `uri` that `published` refuses as
/// naming nothing and `asked` meets, the name read in `text` and its slot
/// under `grammar`, the sources `elsewhere` holds.
///
/// # Specification
/// - requires: `published` are the diagnostics last published for `text`, and
///   `diagnostics` are the request's, each as the client sent it.
/// - ensures: for each [`UNRESOLVED_NAME`] diagnostic of `published` whose
///   range meets `asked` (neither ends before the other starts), in order, the
///   name its range covers and the slot [`Labeled::slot`] reads where it
///   starts; for an open slot, one quick fix per source of `elsewhere`, in its
///   order, that declares a name equal to it which [`unimported_as`] admits in
///   that slot: titled ``Import `address` ``, the address its import writes,
///   making that import as `elsewhere` writes it, naming each of `diagnostics`
///   coded [`UNRESOLVED_NAME`] whose range meets the refusal's, and preferred
///   when it is the one source offered for the name. A source whose import
///   writes nothing is not offered.
/// - provides: the missing imports of `textDocument/codeAction`.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a value no import reaches is offered the one import
///   exporting it, preferred, and not a source declaring it privately; a name
///   two sources export is offered both, none preferred; a name written as a
///   type is not offered a source declaring it only as a value; a range
///   elsewhere is offered none.
/// - witness: `gandr-surface-lsp-core::search::tests::an_unresolved_name_is_offered_the_import_declaring_it`
#[spec(ensures: |ret| ret.iter().all(|action| action.kind == "quickfix"
    && action.edit.changes.as_ref().is_some_and(|changes| changes.len() == 1)))]
#[must_use]
#[inline]
pub fn additions(
    uri: &DocumentUri,
    grammar: &Pbg,
    (published, text): (&[Diagnostic], SourceText<'_>),
    (asked, diagnostics): (Range, &[Value]),
    elsewhere: Elsewhere<'_>,
) -> Vec<CodeAction>
{
    let meets = |range: Range, other: Range| range.start <= other.end && other.start <= range.end;
    let written = <&str>::from(text);
    let index = LineIndex::new(written.into());
    let whole = Labeled::new(text);
    let mut offered = Vec::new();
    let mut answered: Vec<Value> = Vec::new();
    let mut declaring: Vec<&Unimported<'_>> = Vec::new();
    for refusal in published.iter().filter(|refusal| {
        refusal.code.as_deref() == Some(UNRESOLVED_NAME) && meets(refusal.range, asked)
    }) {
        let start = refusal.range.start.byte(&index);
        let end = refusal.range.end.byte(&index);
        let Some(name) = written.get(usize::from(start) .. usize::from(end))
        else {
            continue;
        };
        let Slot::Open(category) = whole.cut(start).slot(grammar)
        else {
            continue;
        };
        answered.clear();
        answered.extend(
            diagnostics
                .iter()
                .filter(|diagnostic| {
                    diagnostic.get("code").and_then(Value::as_str) == Some(UNRESOLVED_NAME)
                        && diagnostic
                            .get("range")
                            .and_then(|range| Range::deserialize(range).ok())
                            .is_some_and(|range| meets(range, refusal.range))
                })
                .cloned(),
        );
        declaring.clear();
        declaring.extend(elsewhere.sources.iter().filter(|source| {
            source.names.iter().any(|declared| {
                declared.name == name && unimported_as(category, declared, source.names).is_some()
            })
        }));
        let preferred = declaring.len() == 1_usize;
        for source in &declaring {
            let edit = (elsewhere.import)(source.path);
            let Some(line) = edit
                .first()
                .map(|first| String::from(first.new_text.trim()))
            else {
                continue;
            };
            let address = line.split('"').nth(1_usize).unwrap_or(line.as_str());
            offered.push(CodeAction {
                title: format!("Import `{address}`"),
                kind: "quickfix",
                diagnostics: answered.clone(),
                is_preferred: preferred,
                edit: WorkspaceEdit::of(BTreeMap::from([(uri.clone(), edit)])),
            });
        }
    }
    offered
}
