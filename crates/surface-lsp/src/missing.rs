//! Missing imports: the quick fixes importing a source that declares a name
//! the document writes and nothing in scope declares.
//!
//! The lowering refuses a name that names nothing, and the refusal is
//! published as an [`UNRESOLVED_NAME`] diagnostic over the name itself. For
//! each such diagnostic a code-action request meets, every source under the
//! opened folders the document does not import whose declarations bring the
//! name into scope is offered as a quick fix writing its import. The sources
//! and their names are the ones a completion offers from ([`Elsewhere`]), and
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

use crate::complete::Elsewhere;
use crate::complete::Unimported;
use crate::complete::unimported_as;
use crate::inline::Labeled;
use crate::inline::Slot;
use crate::position::Range;
use crate::protocol::CodeAction;
use crate::protocol::Diagnostic;
use crate::protocol::DocumentUri;
use crate::protocol::WorkspaceEdit;

/// The code the refusal of a name that names nothing carries.
pub const UNRESOLVED_NAME: &str = "UnresolvedName";

/// The quick fixes importing a source for each name of the document at `uri`
/// that `published` refuses as naming nothing and `asked` meets, the name read
/// in `text` and its slot under `grammar`, the sources `elsewhere` holds.
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
///   declaring it, preferred; a name two sources declare is offered both, none
///   preferred; a name written as a type is not offered a source declaring it
///   only as a value; a range elsewhere is offered none.
/// - witness: `missing::tests::an_unresolved_name_is_offered_the_import_declaring_it`
#[spec(ensures: |ret| ret.iter().all(|action| action.kind == "quickfix"
    && action.edit.changes.as_ref().is_some_and(|changes| changes.len() == 1)))]
#[must_use]
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

#[cfg(test)]
mod tests
{
    use std::path::Path;

    use gandr_surface_syntax::SourceText;

    use super::UNRESOLVED_NAME;
    use super::additions;
    use crate::complete::Elsewhere;
    use crate::complete::Unimported;
    use crate::position::Range;
    use crate::protocol::Diagnostic;
    use crate::protocol::DocumentUri;
    use crate::protocol::Severity;
    use crate::protocol::TextEdit;
    use crate::recheck::grammar;
    use crate::search::declared;

    #[test]
    fn an_unresolved_name_is_offered_the_import_declaring_it()
    {
        let far = declared(SourceText::from(
            "data Shape : Type {\n  Circle : Shape;\n}\ndef faraway : Integer ;\ndef faraway = 7 \
             ;\n",
        ));
        let twin = declared(SourceText::from(
            "def faraway : Integer ;\ndef faraway = 8 ;\ndef Shape : Integer ;\ndef Shape = 1 ;\n",
        ));
        let far = Unimported {
            path: Path::new("/folder/far.gandr"),
            names: &far,
        };
        let twin = Unimported {
            path: Path::new("/folder/twin.gandr"),
            names: &twin,
        };
        let uri = DocumentUri::from("file:///folder/typing.gandr");
        let range = |line: u32, start: u32, end: u32| -> Range {
            serde_json::from_value(
                serde_json::json!({"start": {"line": line, "character": start},
                "end": {"line": line, "character": end}}),
            )
            .expect("a range")
        };
        let import = |path: &Path| {
            Vec::from([TextEdit {
                range: Range::default(),
                new_text: format!(
                    "import \"./{}\" ;\n",
                    path.file_name().unwrap_or_default().display()
                ),
            }])
        };
        let offered = |text: &str, (refused, asked): (Range, Range), sources: &[Unimported<'_>]| {
            let mut refusal = Diagnostic::new(refused, Severity::ERROR, String::from("nothing"));
            refusal.code = Some(String::from(UNRESOLVED_NAME));
            additions(
                &uri,
                grammar().expect("the grammar builds"),
                (&[refusal], SourceText::from(text)),
                (asked, &[]),
                Elsewhere {
                    sources,
                    import: &import,
                },
            )
            .into_iter()
            .map(|action| (action.title, action.is_preferred))
            .collect::<Vec<_>>()
        };
        let value = "def here : Integer ;\ndef here = faraway ;\n";
        let at_value = range(1, 11, 18);
        assert_eq!(
            offered(value, (at_value, at_value), &[far]),
            [(String::from("Import `./far.gandr`"), true)],
            "the one source declaring the value is offered, preferred"
        );
        assert_eq!(
            offered(value, (at_value, at_value), &[far, twin]),
            [
                (String::from("Import `./far.gandr`"), false),
                (String::from("Import `./twin.gandr`"), false)
            ],
            "two sources declaring it are each offered, neither preferred"
        );
        let at_type = range(0, 11, 16);
        assert_eq!(
            offered("def here : Shape ;\n", (at_type, at_type), &[far, twin]),
            [(String::from("Import `./far.gandr`"), true)],
            "a name written as a type finds the family, never a value of its name"
        );
        assert_eq!(
            offered(value, (at_value, range(0, 0, 3)), &[far]),
            [],
            "a range elsewhere is offered no import"
        );
    }
}
