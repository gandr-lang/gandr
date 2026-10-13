//! What a hover shows: the type of whatever the cursor is in, and a
//! declaration's documentation.
//!
//! # A hover answers the innermost node
//!
//! A hover reads the declarations the text's [`Reading`] holds — those the
//! outline reads off the tree, each with its declaring form's key — and the
//! document's type table (`TypeTable`), which [`hovering`] builds once per
//! revision of the copy and the copy keeps until it changes. It answers, in
//! order:
//!
//! - **A declaration's name** — from its first character to just past its last
//!   — with a fenced `gandr` block holding the name and, when the table types
//!   the declaration, ` : ` and its type, then the documentation the session's
//!   latest accepted lowering filed for the declaring form, after a blank line,
//!   about the name's range. The table keys a declaration by each of its forms,
//!   so a signature and the definition completing it both answer the one
//!   declaration they make.
//! - **The innermost typed node holding the cursor**, about its span: a term
//!   with its type, and, when an outer judgement checked it against a type
//!   spelled otherwise, that type after it; a binder with its name and the type
//!   of its uses; a written type with its text and its universe. A keyword or a
//!   delimiter inside a term answers that term, so `return` and `{` answer the
//!   computation they open.
//! - **The innermost declaration holding the cursor**, about its range, as for
//!   its name: the keyword that introduces it, the colon of its signature, the
//!   layout and documentation inside it.
//!
//! A position in no declaration hovers nothing, and so does a document whose
//! grammar did not build. Every type is spelled through the shared printer at
//! 80 columns.
//!
//! The alternative was to look the name under the cursor up among the
//! session's items by its occurrence among the document's declarations: it
//! answers declaration names only, and counts a signature and its definition
//! as two occurrences of one item. The choice reverses when the session keeps
//! the typed run's table itself, and the hover then reads it there rather than
//! judging the copy's text again.

use alloc::format;
use alloc::string::String;

use anodized::spec;
use gandr_surface_dispatcher::Declared;
use gandr_surface_dispatcher::Subject;
use gandr_surface_dispatcher::TypeTable;
use gandr_surface_dispatcher::TypedSpan;
use gandr_surface_pretty::PageWidth;
use gandr_surface_render_remote::ByteOffset as RenderOffset;
use gandr_surface_render_remote::LineIndex;
use gandr_surface_session::Session;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::position::Position;
use crate::position::Range;
use crate::protocol::Hover;
use crate::protocol::MarkupContent;
use crate::protocol::SymbolKind;
use crate::reading::Declaration;
use crate::reading::Reading;
use crate::recheck::grammar;

/// The page width a hover lays a type out at.
const HOVER_WIDTH: u32 = 80;

quenchant_shape::reason_enum! {
    /// Why a position hovers nothing.
    pub mod hovered {
        /// The reason nothing is shown.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The grammar did not build or the text did not parse.
            Unparsed,
            /// The position is in no typed node and no declaration.
            Untyped,
            /// The session knows neither a type nor documentation for the
            /// declaration.
            Unknown,
        }
    }
}

/// What a document copy keeps for its hovers until its text changes: the type
/// table of its text.
#[derive(Clone, Debug)]
#[repr(transparent)]
pub struct Hovering
{
    /// The type of every node of the text, and of every declaration.
    table: TypeTable,
}

/// What the hovers of `text` read, built under the process's grammar: one
/// typed run per text, rather than one per hover.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`TypeTable::of`] over `text`, the empty table when the grammar
///   did not build or the text did not parse.
/// - provides: what a document copy keeps for its hovers.
/// - fails: never; a refusal answers the empty table.
/// - panics: none.
/// - executable: none — the table is the dispatcher's typed run, whose own
///   specification states what it holds; restating it here would run the typed
///   run again.
///
/// # Adequacy
/// - hypothesis: L3 — a hover over every kind of position reads what this
///   builds, so a table of another text, or an empty one, changes a typed
///   answer.
/// - witness: `hover::tests::each_marked_position_hovers_its_answer`
#[must_use]
pub fn hovering(text: SourceText<'_>) -> Hovering
{
    let table = match grammar() {
        | Ok(grammar) => TypeTable::of(grammar, text).unwrap_or_default(),
        | Err(_) => TypeTable::default(),
    };
    Hovering { table }
}

/// What a hover at `position` of `text` shows, read against the text's
/// `reading`, its `hovering` and `session`.
///
/// # Specification
/// - requires: `reading` and `hovering` were read off `text`, and `session`
///   last checked `text`, as the server's synchronisation leaves them; a stale
///   session answers the documentation it last accepted.
/// - ensures: on a declaration's name — from its first character to just past
///   its last — a fenced `gandr` block holding the name and, when the table
///   types the declaration by its form's key, ` : ` and its type, or, when the
///   table holds the lowering's refusal of it, that refusal after a blank line;
///   then the documentation the session filed for the form after a blank line,
///   about the name's range; else, on the innermost typed node holding the
///   position, a fenced block of its type — a binder's name or a written type's
///   text before ` : ` — and, for a term checked against a type spelled
///   otherwise, that type in a second block, about the node's range; else,
///   inside a non-module declaration, as on its name, about its range. Absent
///   elsewhere, and absent for a declaration with neither a type, a refusal nor
///   documentation.
/// - provides: the answer to `textDocument/hover`.
/// - fails: never; an absence names its reason.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a documented definition, an undocumented one, a member of
///   a module sharing its name with another module's, a signature and its
///   definition, a function and one the lowering refused, a binder, a use,
///   written value and computation types, a mismatched term, a term past a
///   refusal in its body, a keyword, layout inside a declaration, a word in a
///   comment and a position past the last declaration are asserted at their
///   exact answers.
/// - witness: `hover::tests::a_declaration_hovers_its_type_and_documentation`
/// - witness: `hover::tests::each_marked_position_hovers_its_answer`
/// - witness: `hover::tests::each_member_hovers_its_own_type`
#[spec(ensures: |ref ret| match *ret {
    Maybe::Present(ref hover) => hover.contents.value.starts_with("```gandr\n")
        && hover.range.start <= position && position <= hover.range.end,
    Maybe::Absent(_) => true,
})]
pub fn hover<Store, Blocks>(
    text: SourceText<'_>,
    session: &Session<Store, Blocks>,
    reading: &Reading,
    hovering: &Hovering,
    position: Position,
) -> Maybe<Hover, hovered::Absent>
{
    let Maybe::Present(found) = reading.declarations()
    else {
        return Maybe::Absent(hovered::Absent::Unparsed);
    };
    let table = &hovering.table;
    let index = LineIndex::new(<&str>::from(text).into());
    if let Some(named) = found.iter().find(|found| {
        found.symbol.selection_range.start <= position
            && position <= found.symbol.selection_range.end
    }) {
        return declared(session, table, named, named.symbol.selection_range);
    }
    let offset = ByteOffset::from(usize::from(position.byte(&index)));
    if let Maybe::Present(entry) = table.at(offset, PageWidth::from(HOVER_WIDTH))
        && let Ok(range) = Range::of_bytes(
            &index,
            RenderOffset::from(usize::from(entry.span().start())),
            RenderOffset::from(usize::from(entry.span().end())),
        )
    {
        return Maybe::Present(Hover {
            contents: MarkupContent {
                kind: "markdown",
                value: typed(text, &entry),
            },
            range,
        });
    }
    let enclosing = found.iter().rfind(|found| {
        found.symbol.kind != SymbolKind::MODULE
            && found.symbol.range.start <= position
            && position < found.symbol.range.end
    });
    match enclosing {
        | Some(enclosing) => declared(session, table, enclosing, enclosing.symbol.range),
        | None => Maybe::Absent(hovered::Absent::Untyped),
    }
}

/// The hover of the declaration `declaration`, about `range`.
///
/// # Specification
/// - requires: `range` holds the hovered position.
/// - ensures: a fenced `gandr` block of the name and, when `table` types the
///   declaration by its form's key and the symbol is no module, ` : ` and its
///   type; when `table` holds the lowering's refusal of it instead, that
///   refusal after a blank line; then the documentation `session` filed under
///   the form's key after a blank line; absent when none is known.
/// - provides: the declaration half of [`hover`].
/// - fails: never; an absence names its reason.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`hover`]'s declaration rows.
/// - witness: `hover::tests::a_declaration_hovers_its_type_and_documentation`
/// - witness: `hover::tests::each_member_hovers_its_own_type`
/// - witness: `hover::tests::each_marked_position_hovers_its_answer`
#[spec(ensures: |ref ret| match *ret {
    Maybe::Present(ref hover) => hover.range == range
        && hover.contents.value.starts_with(&format!("```gandr\n{}", declaration.symbol.name)),
    Maybe::Absent(reason) => reason == hovered::Absent::Unknown,
})]
fn declared<Store, Blocks>(
    session: &Session<Store, Blocks>,
    table: &TypeTable,
    declaration: &Declaration,
    range: Range,
) -> Maybe<Hover, hovered::Absent>
{
    let symbol = &declaration.symbol;
    let key = declaration.key;
    let held = match key {
        | Some(key) if symbol.kind != SymbolKind::MODULE => {
            match table.declared(key, PageWidth::from(HOVER_WIDTH)) {
                | Maybe::Present(held) => Some(held),
                | Maybe::Absent(_) => None,
            }
        },
        | Some(_) | None => None,
    };
    let documented = key.and_then(|key| match session.documentation(key) {
        | Maybe::Present(text) => Some(text),
        | Maybe::Absent(_) => None,
    });
    if held.is_none() && documented.is_none() {
        return Maybe::Absent(hovered::Absent::Unknown);
    }
    let mut value = match held {
        | Some(Declared::Typed(spelled)) => {
            format!("```gandr\n{} : {}\n```", symbol.name, spelled.as_ref())
        },
        | Some(Declared::Refused(refusal)) => {
            format!("```gandr\n{}\n```\n\nrefused: {refusal}", symbol.name)
        },
        | None => format!("```gandr\n{}\n```", symbol.name),
    };
    if let Some(text) = documented {
        value.push_str("\n\n");
        value.push_str(text.as_ref());
    }
    Maybe::Present(Hover {
        contents: MarkupContent {
            kind: "markdown",
            value,
        },
        range,
    })
}

/// The hover text of the typed node `entry` of `text`.
///
/// # Specification
/// - requires: `entry` was read from the table of `text`.
/// - ensures: a fenced `gandr` block: a term's type alone; a binder's name and
///   a written type's text, each when it is one line of the source, then ` : `
///   and the entry's type; for a term checked against a type spelled otherwise,
///   a second block of that type after a line saying so.
/// - provides: the node half of [`hover`].
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a use, a binder, a written type and a mismatched term are
///   asserted at their exact texts.
/// - witness: `hover::tests::each_marked_position_hovers_its_answer`
#[spec(ensures: |ret| ret.starts_with("```gandr\n") && ret.contains(entry.ty().as_ref()))]
fn typed(
    text: SourceText<'_>,
    entry: &TypedSpan,
) -> String
{
    let written = <&str>::from(text)
        .get(usize::from(entry.span().start()) .. usize::from(entry.span().end()))
        .filter(|written| !written.contains('\n'));
    let mut value = match (entry.subject(), written) {
        | (Subject::Binder | Subject::Type, Some(written)) => {
            format!("```gandr\n{written} : {}\n```", entry.ty().as_ref())
        },
        | (Subject::Term, _) | (Subject::Binder | Subject::Type, None) => {
            format!("```gandr\n{}\n```", entry.ty().as_ref())
        },
    };
    if let Maybe::Present(expected) = entry.expected() {
        value.push_str("\n\nchecked against\n\n```gandr\n");
        value.push_str(expected.as_ref());
        value.push_str("\n```");
    }
    value
}

#[cfg(test)]
mod tests
{
    use gandr_core_incremental::BackendArtifact;
    use gandr_core_incremental::MemoryCheckpointStore;
    use gandr_storage_records::InMemoryBlockStore;
    use gandr_surface_dispatcher::SourceRoot;
    use gandr_surface_render_remote::ByteOffset as RenderOffset;
    use gandr_surface_render_remote::LineIndex;
    use gandr_surface_session::Session;
    use gandr_surface_syntax::SourceText;
    use quenchant_shape::shape::Maybe;

    use super::hover;
    use super::hovered;
    use super::hovering;
    use crate::position::Character;
    use crate::position::Line;
    use crate::position::Position;
    use crate::reading::Reading;
    use crate::recheck::grammar;

    /// A session that has checked `text`.
    ///
    /// # Specification
    /// trivial.
    fn checked(text: SourceText<'_>) -> Session<MemoryCheckpointStore, InMemoryBlockStore>
    {
        let mut session = Session::new(
            grammar().expect("the grammar builds").clone(),
            SourceRoot::Strict,
            MemoryCheckpointStore::default(),
            InMemoryBlockStore::default(),
            BackendArtifact::from(b"hover".as_slice()),
        );
        let _judged = session.judge(text).expect("the session does not fault");
        session
    }

    /// What a hover at `line` and `character` of `text` shows, or why not.
    ///
    /// # Specification
    /// trivial.
    fn shown(
        text: SourceText<'_>,
        (line, character): (Line, Character),
    ) -> Result<String, hovered::Absent>
    {
        shown_at(text, Position { line, character })
    }

    /// What a hover at `position` of `text` shows, or why not.
    ///
    /// # Specification
    /// trivial.
    fn shown_at(
        text: SourceText<'_>,
        position: Position,
    ) -> Result<String, hovered::Absent>
    {
        let session = checked(text);
        match hover(
            text,
            &session,
            &Reading::of(text),
            &hovering(text),
            position,
        ) {
            | Maybe::Present(shown) => Ok(shown.contents.value),
            | Maybe::Absent(reason) => Err(reason),
        }
    }

    /// The marker `$0`'s position in `fixture`, and the fixture without it;
    /// panics when the marker is missing.
    ///
    /// # Specification
    /// trivial.
    fn marker(fixture: SourceText<'_>) -> (String, Position)
    {
        let written = <&str>::from(fixture);
        let at = written.find("$0").expect("the fixture is marked");
        let text = written.replacen("$0", "", 1);
        let index = LineIndex::new(text.as_str().into());
        let position =
            Position::of_byte(&index, RenderOffset::from(at)).expect("the marker is on a boundary");
        (text, position)
    }

    /// A hover's text: one fenced block holding `block`.
    ///
    /// # Specification
    /// trivial.
    fn fenced(block: SourceText<'_>) -> String
    {
        format!("```gandr\n{}\n```", <&str>::from(block))
    }

    #[test]
    fn each_marked_position_hovers_its_answer()
    {
        let rows: [(&str, &str, Result<String, hovered::Absent>); 15] = [
            (
                "a synthesised declaration's name",
                "def ans$0wer = 42 ;\n",
                Ok(fenced(SourceText::from("answer : Integer"))),
            ),
            (
                "the definition half of a signed declaration",
                "def answer : Integer ;\ndef ans$0wer = 42 ;\n",
                Ok(fenced(SourceText::from("answer : Integer"))),
            ),
            (
                "a function's name",
                "def $0f(x: Integer) -> -F Integer { return x }\n",
                Ok(fenced(SourceText::from("f : +U (Integer -> -F Integer)"))),
            ),
            (
                "the name of a function the lowering refused",
                "def $0f(x: Integer) -> -F Integer { pure x }\n",
                Ok(String::from(
                    "```gandr\nf\n```\n\nrefused: the body's path ends without an exit; a path \
                     through a body ends in `return` or `become`",
                )),
            ),
            (
                "a binder",
                "def f($0x: Integer) -> -F Integer { return x }\n",
                Ok(fenced(SourceText::from("x : Integer"))),
            ),
            (
                "a use",
                "def f(x: Integer) -> -F Integer { return $0x }\n",
                Ok(fenced(SourceText::from("Integer"))),
            ),
            (
                "a written value type",
                "def answer : Inte$0ger ;\n",
                Ok(fenced(SourceText::from("Integer : Type"))),
            ),
            (
                "a written computation type",
                "def f(x: Integer) -> -$0F Integer { return x }\n",
                Ok(fenced(SourceText::from("-F Integer : Type[-]"))),
            ),
            (
                "a keyword opening a term",
                "def f(x: Integer) -> -F Integer { ret$0urn x }\n",
                Ok(fenced(SourceText::from("-F Integer"))),
            ),
            (
                "the keyword introducing a declaration",
                "d$0ef answer = 42 ;\n",
                Ok(fenced(SourceText::from("answer : Integer"))),
            ),
            (
                "layout inside a declaration",
                "def answer =$0 42 ;\n",
                Ok(fenced(SourceText::from("answer : Integer"))),
            ),
            (
                "a mismatched term",
                "def bad : Integer ;\ndef bad = u$0nit ;\n",
                Ok(String::from(
                    "```gandr\nUnit\n```\n\nchecked against\n\n```gandr\nInteger\n```",
                )),
            ),
            (
                "a term past a refusal in its body",
                "def g(x: Integer) -> -F Integer { run y <- force 1 ; return $0x }\n",
                Ok(fenced(SourceText::from("Integer"))),
            ),
            (
                "a comment between declarations",
                "def a = 1 ;\n// a $0word\ndef b = 2 ;\n",
                Err(hovered::Absent::Untyped),
            ),
            (
                "past the last declaration",
                "def later : Integer ;\n$0",
                Err(hovered::Absent::Untyped),
            ),
        ];
        for (position, fixture, expected) in rows {
            let (text, at) = marker(SourceText::from(fixture));
            assert_eq!(
                shown_at(SourceText::from(text.as_str()), at),
                expected,
                "{position}"
            );
        }
    }

    #[test]
    fn a_declaration_hovers_its_type_and_documentation()
    {
        let text = SourceText::from(
            "/// The answer, said once.\ndef answer = 42 ;\ndef plain : String ;\n",
        );
        assert_eq!(
            shown(text, (1.into(), 5.into())),
            Ok(String::from(
                "```gandr\nanswer : Integer\n```\n\nThe answer, said once."
            ))
        );
        assert_eq!(
            shown(text, (2.into(), 4.into())),
            Ok(String::from("```gandr\nplain : String\n```"))
        );
        assert_eq!(
            shown(text, (1.into(), 0.into())),
            Ok(String::from(
                "```gandr\nanswer : Integer\n```\n\nThe answer, said once."
            )),
            "the keyword answers the declaration it introduces"
        );
    }

    #[test]
    fn each_member_hovers_its_own_type()
    {
        let text =
            SourceText::from("module A {\n  def x = 1 ;\n}\nmodule B {\n  def x = \"one\" ;\n}\n");
        assert_eq!(
            shown(text, (1.into(), 6.into())),
            Ok(String::from("```gandr\nx : Integer\n```"))
        );
        assert_eq!(
            shown(text, (4.into(), 6.into())),
            Ok(String::from("```gandr\nx : String\n```"))
        );
        assert_eq!(
            shown(text, (0.into(), 7.into())),
            Err(hovered::Absent::Unknown),
            "an undocumented module has no type to show"
        );
    }
}
