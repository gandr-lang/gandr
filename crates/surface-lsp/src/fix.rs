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
//!
//! A written hole, `?` or `?name`, is a term the source left unfinished. Each
//! name in scope where it stands, as completion offers it, is tried in its
//! place in one trial of the document, the one a model's candidate fills
//! pass. A name the trial judges, leaving no more errors than the document
//! publishes, is offered as a fix, best first.

use alloc::collections::BTreeMap;
use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;
use core::iter;

use anodized::spec;
use gandr_surface_grammar::Pbg;
use gandr_surface_pretty::Style;
use gandr_surface_render_remote::HlRole;
use gandr_surface_render_remote::HlSpan;
use gandr_surface_render_remote::LineIndex;
use gandr_surface_session::CandidateIndex;
use gandr_surface_syntax::SourceText;
use serde::Deserialize as _;
use serde_json::Value;

use crate::complete::Elsewhere;
use crate::complete::completions;
use crate::hover::Hovering;
use crate::inline::Forms;
use crate::inline::Labeled;
use crate::position::Range;
use crate::protocol::CodeAction;
use crate::protocol::CompletionItemKind;
use crate::protocol::Diagnostic;
use crate::protocol::DocumentEdit;
use crate::protocol::DocumentUri;
use crate::protocol::DocumentVersion;
use crate::protocol::EditedDocument;
use crate::protocol::EditsShaped;
use crate::protocol::LabelsDetailed;
use crate::protocol::Severity;
use crate::protocol::SnippetEdit;
use crate::protocol::StringValue;
use crate::protocol::TakesSnippets;
use crate::protocol::TextDocumentEdit;
use crate::protocol::TextEdit;
use crate::protocol::WorkspaceEdit;
use crate::recheck::Reached;
use crate::recheck::Tried;

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

/// The most names one hole is tried with: as many as one trial a model's
/// candidate fills pass through judges.
const MOST_FILLS: usize = 32;

/// A written hole the asked range meets, and the names it is tried with.
///
/// # Specification
/// - requires: built by [`holes`].
/// - ensures: `names` holds between one and [`MOST_FILLS`] names.
/// - panics: none.
/// - executable: none — a carrier; [`holes`] states what it holds.
///
/// # Adequacy
/// - hypothesis: L3 — as [`holes`].
/// - witness: `server::tests::a_hole_is_offered_the_names_that_settle_it`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Hole
{
    /// The hole's range: its `?` and a name written right after it.
    pub range: Range,
    /// The names in scope where it stands, as completion offers them.
    pub names: Vec<String>,
}

/// The written holes of `text` that meet `asked`, each with the names it is
/// tried with.
///
/// # Specification
/// - requires: `spans` are the highlighter's spans of `text`, in text order;
///   `hovering` was read off `text`, the document at `uri`; `forms` is
///   [`Forms::new`] of `grammar`.
/// - ensures: in text order, one hole per `Hole` span whose range, extended
///   over a `Label` span starting where it ends, reads and meets `asked`
///   (neither ends before the other starts): the first [`MOST_FILLS`] names
///   [`completions`] offers at the hole's start, keywords left out, binders
///   innermost first, then declared names by name. A hole offered no name is
///   left out.
/// - provides: the candidates of the hole fills `textDocument/codeAction`
///   offers.
/// - fails: never.
/// - panics: none.
/// - intension: one line index, then one completion per hole the range meets.
///
/// # Adequacy
/// - hypothesis: L3 — a hole in a declaration with a parameter is tried with
///   the parameter and the declared names, and a range meeting no hole is
///   offered no fill.
/// - witness: `server::tests::a_hole_is_offered_the_names_that_settle_it`
#[spec(ensures: |ret| ret.iter().all(|hole| (1 ..= MOST_FILLS).contains(&hole.names.len())))]
#[must_use]
pub fn holes(
    (grammar, forms): (&Pbg, &Forms),
    (text, spans): (SourceText<'_>, &[HlSpan]),
    (hovering, printer): (&Hovering, Style),
    (uri, asked): (&DocumentUri, Range),
) -> Vec<Hole>
{
    let index = LineIndex::new(<&str>::from(text).into());
    let following = spans.iter().skip(1).map(Some).chain(iter::once(None));
    let mut found = Vec::new();
    for (span, next) in spans.iter().zip(following) {
        if span.role != HlRole::Hole {
            continue;
        }
        let end = next
            .filter(|next| next.role == HlRole::Label && next.range.start() == span.range.end())
            .map_or_else(|| span.range.end(), |next| next.range.end());
        let Some(range) = Range::of_bytes(&index, span.range.start(), end)
            .ok()
            .filter(|range| range.start <= asked.end && asked.start <= range.end)
        else {
            continue;
        };
        let names: Vec<String> = completions(
            grammar,
            forms,
            text,
            hovering,
            (uri, range.start),
            (printer, LabelsDetailed(false), TakesSnippets(false)),
            Elsewhere {
                sources: &[],
                import: &|_| Vec::new(),
            },
        )
        .items
        .into_iter()
        .filter(|item| item.kind != CompletionItemKind::KEYWORD)
        .take(MOST_FILLS)
        .map(|item| item.label)
        .collect();
        if !names.is_empty() {
            found.push(Hole { range, names });
        }
    }
    found
}

/// The quick fixes that fill `hole` of the document at `uri` with each of its
/// names `tried` judged, best first.
///
/// # Specification
/// - requires: `tried` is a trial of candidates among which `hole`'s names,
///   each alone written over its range, stand in order from `first`, ranked as
///   the trial ranks them; `published` is the document's published diagnostics,
///   and `diagnostics` the request's, each as the client sent it.
/// - ensures: fewest errors left first, then in the trial's order, one
///   `quickfix` per name the trial judged whose diagnostics hold no error whose
///   range holds the hole's start (the name, or a form or declaration around
///   it, refused) and no more errors than `published`, replacing the hole's
///   range with the name and naming each diagnostic of `diagnostics` whose
///   range reads and meets the hole's; preferred when it is the only such fix
///   and leaves no error.
/// - provides: the hole fills' share of `textDocument/codeAction`.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a hole of a path type is offered the parameter that
///   settles its declaration and a downstream one, and none of the names the
///   trial refuses at the hole, in the trial's order.
/// - witness: `server::tests::a_hole_is_offered_the_names_that_settle_it`
#[spec(ensures: |ret| ret.len() <= tried.len()
    && ret.iter().all(|action| action.kind == "quickfix")
    && ret.iter().filter(|action| action.is_preferred).count() <= 1)]
#[must_use]
pub fn fills(
    uri: &DocumentUri,
    (hole, first): (&Hole, CandidateIndex),
    tried: &[Tried],
    (published, diagnostics): (&[Diagnostic], &[Value]),
) -> Vec<CodeAction>
{
    let errors = |judged: &[Diagnostic]| {
        judged
            .iter()
            .filter(|diagnostic| diagnostic.severity == Severity::ERROR)
            .count()
    };
    let at = hole.range.start;
    let refused = |judged: &[Diagnostic]| {
        judged.iter().any(|diagnostic| {
            diagnostic.severity == Severity::ERROR
                && diagnostic.range.start <= at
                && at <= diagnostic.range.end
        })
    };
    let before = errors(published);
    let mut kept: Vec<(&String, usize)> = tried
        .iter()
        .filter(|tried| tried.reached == Reached::Judged && !refused(&tried.diagnostics))
        .filter_map(|tried| {
            let after = errors(&tried.diagnostics);
            usize::from(tried.candidate)
                .checked_sub(usize::from(first))
                .and_then(|at| hole.names.get(at))
                .filter(|_| after <= before)
                .map(|name| (name, after))
        })
        .collect();
    kept.sort_by_key(|&(_, after)| after);
    let named: Vec<Value> = diagnostics
        .iter()
        .filter(|diagnostic| {
            diagnostic
                .get("range")
                .and_then(|range| Range::deserialize(range).ok())
                .is_some_and(|range| range.start <= hole.range.end && hole.range.start <= range.end)
        })
        .cloned()
        .collect();
    let alone = kept.len() == 1;
    kept.into_iter()
        .map(|(name, after)| CodeAction {
            title: format!("Fill the hole with `{name}`"),
            kind: "quickfix",
            diagnostics: named.clone(),
            is_preferred: alone && after == 0,
            edit: WorkspaceEdit::of(BTreeMap::from([(
                uri.clone(),
                Vec::from([TextEdit {
                    range: hole.range,
                    new_text: name.clone(),
                }]),
            )])),
        })
        .collect()
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
