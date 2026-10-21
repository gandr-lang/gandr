//! Quick fixes for the forms the source left unfinished.
//!
//! The parser closes a form the source never finished with a repair, and the
//! lowering refuses the form as malformed at the point the repair stands: past
//! the last token a body writes for a missing `}`, past a definition's value
//! for a missing `;`. A fix inserts there what the grammar expects to finish
//! the form, its cheapest closing as inline completion weighs it
//! ([`Labeled::closing`]), its holes tab stops.
//!
//! A client that takes snippet edits (3.18 `snippetEditSupport`, with
//! versioned edits) is sent the closing as a snippet. Any other client is sent
//! a closing with no hole as its text, and no fix for a closing with one,
//! whose hole it could not fill.

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

use crate::inline::Forms;
use crate::inline::Labeled;
use crate::position::Range;
use crate::protocol::CodeAction;
use crate::protocol::DocumentEdit;
use crate::protocol::DocumentUri;
use crate::protocol::DocumentVersion;
use crate::protocol::EditedDocument;
use crate::protocol::EditsShaped;
use crate::protocol::SnippetEdit;
use crate::protocol::StringValue;
use crate::protocol::TextDocumentEdit;
use crate::protocol::TextEdit;
use crate::protocol::WorkspaceEdit;

/// The code of the refusal a repaired form is reported under.
const MALFORMED: &str = "MalformedForm";

/// One quick fix per diagnostic of `diagnostics` that refuses a malformed form
/// of `text`, the document at `uri` at `version`, and meets `asked`: the
/// closing the grammar expects where the refusal stands.
///
/// # Specification
/// - requires: `forms` is [`Forms::new`] of `grammar`; `diagnostics` are the
///   request's, each as the client sent it.
/// - ensures: in the order sent, for each diagnostic whose `code` is
///   `MalformedForm` and whose range reads and meets `asked` (neither ends
///   before the other starts), where [`Labeled::closing`] answers at the
///   range's start: a preferred `quickfix` naming that diagnostic alone and
///   inserting the closing at that point. When `shaped.snippets` holds, the
///   edit is the closing as a snippet, versioned at `version`; otherwise it is
///   the closing's text by URI, and a closing holding a tab stop offers no fix.
/// - provides: the repairs' share of `textDocument/codeAction`.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a definition missing its `}` is offered the brace past
///   its body as text and as a snippet, a diagnostic of another code or
///   elsewhere is offered nothing, and a form missing a term is offered its
///   hole only as a snippet.
/// - witness: `fix::tests::a_repair_is_offered_as_the_closing_it_owes`
/// - witness: `server::tests::a_repaired_form_is_offered_its_closing`
#[spec(ensures: |ret| ret.len() <= diagnostics.len()
    && ret.iter().all(|action| action.kind == "quickfix"
        && action.is_preferred
        && action.diagnostics.len() == 1))]
#[must_use]
pub fn repairs(
    (grammar, forms): (&Pbg, &Forms),
    (uri, version): (&DocumentUri, DocumentVersion),
    text: SourceText<'_>,
    (asked, diagnostics): (Range, &[Value]),
    shaped: EditsShaped,
) -> Vec<CodeAction>
{
    let meets = |range: Range| range.start <= asked.end && asked.start <= range.end;
    let index = LineIndex::new(<&str>::from(text).into());
    let whole = Labeled::new(text);
    let mut found = Vec::new();
    for diagnostic in diagnostics {
        if diagnostic.get("code").and_then(Value::as_str) != Some(MALFORMED) {
            continue;
        }
        let Some(range) = diagnostic
            .get("range")
            .and_then(|range| Range::deserialize(range).ok())
            .filter(|&range| meets(range))
        else {
            continue;
        };
        let at = range.start.byte(&index);
        let Some(closing) = whole.closing(&whole.cut(at), grammar, forms)
        else {
            continue;
        };
        let point = Range {
            start: range.start,
            end: range.start,
        };
        let plain = closing.plain();
        let title = plain.as_deref().map_or_else(
            || String::from("Finish the form"),
            |inserted| format!("Insert `{}`", inserted.trim()),
        );
        let edit = if shaped.snippets {
            WorkspaceEdit {
                changes: None,
                document_changes: Vec::from([TextDocumentEdit {
                    text_document: EditedDocument {
                        uri: uri.clone(),
                        version: Some(version),
                    },
                    edits: Vec::from([DocumentEdit::Snippet(SnippetEdit {
                        range: point,
                        snippet: StringValue {
                            kind: "snippet",
                            value: String::from(closing),
                        },
                    })]),
                }]),
                change_annotations: BTreeMap::new(),
            }
        }
        else {
            let Some(inserted) = plain
            else {
                continue;
            };
            WorkspaceEdit::of(BTreeMap::from([(
                uri.clone(),
                Vec::from([TextEdit {
                    range: point,
                    new_text: inserted,
                }]),
            )]))
        };
        found.push(CodeAction {
            title,
            kind: "quickfix",
            diagnostics: Vec::from([diagnostic.clone()]),
            is_preferred: true,
            edit,
        });
    }
    found
}

#[cfg(test)]
mod tests
{
    use gandr_surface_syntax::SourceText;
    use serde_json::Value;
    use serde_json::json;

    use super::repairs;
    use crate::position::Character;
    use crate::position::Line;
    use crate::position::Position;
    use crate::position::Range;
    use crate::protocol::DocumentUri;
    use crate::protocol::DocumentVersion;
    use crate::protocol::EditsShaped;
    use crate::recheck::forms;
    use crate::recheck::grammar;

    /// A client that takes versioned edits and snippet edits.
    const SNIPPETS: EditsShaped = EditsShaped {
        versioned: true,
        annotated: false,
        snippets: true,
    };

    /// The fixes `text` is offered for `diagnostics`, asked over `asked`, to a
    /// client taking edits as `shaped`, as JSON.
    ///
    /// # Specification
    /// trivial.
    fn offered(
        text: SourceText<'_>,
        asked: Range,
        diagnostics: &[Value],
        shaped: EditsShaped,
    ) -> Value
    {
        serde_json::to_value(repairs(
            (
                grammar().expect("the grammar builds"),
                forms().expect("the forms build"),
            ),
            (
                &DocumentUri::from("file:///unclosed.gandr"),
                serde_json::from_value::<DocumentVersion>(json!(3_i32)).expect("a version reads"),
            ),
            text,
            (asked, diagnostics),
            shaped,
        ))
        .expect("the fixes serialise")
    }

    /// The empty range at `(line, character)`.
    ///
    /// # Specification
    /// trivial.
    fn point((line, character): (Line, Character)) -> Range
    {
        let at = Position { line, character };
        Range { start: at, end: at }
    }

    /// A refusal of `code` at `range`, as a client sends it back.
    ///
    /// # Specification
    /// trivial.
    fn refused(
        code: SourceText<'_>,
        range: Range,
    ) -> Value
    {
        json!({"range": range, "severity": 1_u8, "code": <&str>::from(code), "source": "gandr",
            "message": "this def value is missing its closing `}`"})
    }

    /// The recovery fixture of #1391 leaves its definition's body open: the
    /// fix inserts the brace past `return n + 1`, as text to any client and as
    /// a snippet to one that takes them, naming the refusal it answers. A
    /// refusal of another code, or asked about elsewhere, is offered nothing,
    /// and a definition missing its value is offered the value's hole only as
    /// a snippet, the hole its tab stop.
    #[test]
    #[expect(
        clippy::literal_string_with_formatting_args,
        reason = "a snippet's tab stop is spelled `${n:name}`, which reads as a format argument"
    )]
    fn a_repair_is_offered_as_the_closing_it_owes()
    {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../surface-parser/tests/fixtures/unclosed-body.gandr");
        let read = std::fs::read_to_string(&path).expect("the fixture is read");
        let written = SourceText::from(read.as_str());
        let malformed = SourceText::from("MalformedForm");
        let end = point((Line::from(4_u32), Character::from(14_u32)));
        let brace = refused(malformed, end);
        let by_uri = EditsShaped::BY_URI;
        assert_eq!(
            offered(written, end, core::slice::from_ref(&brace), by_uri),
            json!([{
                "title": "Insert `}`",
                "kind": "quickfix",
                "diagnostics": [brace],
                "isPreferred": true,
                "edit": {"changes": {"file:///unclosed.gandr": [{"range": end, "newText": " }"}]}},
            }]),
            "past the body, the brace as text"
        );
        assert_eq!(
            offered(written, end, core::slice::from_ref(&brace), SNIPPETS).pointer("/0/edit"),
            Some(&json!({"documentChanges": [{
                "textDocument": {"uri": "file:///unclosed.gandr", "version": 3_i32},
                "edits": [{"range": end, "snippet": {"kind": "snippet", "value": " \\}"}}],
            }]})),
            "to a client that takes snippet edits, the brace as a snippet at the document's version"
        );
        assert_eq!(
            offered(
                written,
                end,
                &[refused(SourceText::from("TypeMismatch"), end)],
                by_uri
            ),
            json!([]),
            "a refusal of another code is not a repair"
        );
        assert_eq!(
            offered(
                written,
                point((Line::from(0_u32), Character::from(0_u32))),
                core::slice::from_ref(&brace),
                by_uri
            ),
            json!([]),
            "a range away from the refusal offers nothing"
        );
        let missing = SourceText::from("def a : Integer ;\ndef a = ;\n");
        let value = point((Line::from(1_u32), Character::from(7_u32)));
        let operand = refused(malformed, value);
        assert_eq!(
            offered(missing, value, core::slice::from_ref(&operand), by_uri),
            json!([]),
            "a closing with a hole is offered only to a client that fills it"
        );
        let filled = offered(missing, value, core::slice::from_ref(&operand), SNIPPETS);
        assert_eq!(
            (
                filled.pointer("/0/title"),
                filled.pointer("/0/edit/documentChanges/0/edits/0/snippet/value")
            ),
            (Some(&json!("Finish the form")), Some(&json!(" ${1:value}"))),
            "a closing with a hole is a snippet to a client that takes them, the hole its tab stop"
        );
    }
}
