//! What a hover shows over a declaration's name: the type the latest check
//! gives it and the documentation written for it.
//!
//! The declaration is read off the parsed tree as the outline reads it; its
//! type off the session's latest resume, by the occurrence of its name the
//! declaration is; its documentation off the session's latest accepted
//! lowering, under the declaring form's content identity, which its
//! documentation does not reach.

use alloc::format;

use anodized::spec;
use gandr_core_incremental::ItemKey;
use gandr_core_incremental::Occurrence;
use gandr_core_incremental::Reference;
use gandr_surface_parser::parse;
use gandr_surface_pretty::PageWidth;
use gandr_surface_render_remote::LineIndex;
use gandr_surface_session::Session;
use gandr_surface_session::type_at;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::outline::declarations;
use crate::position::Position;
use crate::protocol::Hover;
use crate::protocol::MarkupContent;
use crate::protocol::SymbolKind;
use crate::recheck::grammar;
use crate::recheck::roles;

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
            /// The position is on no declaration's name.
            Undeclared,
            /// The session knows neither a type nor documentation for the
            /// declaration.
            Unknown,
        }
    }
}

/// What a hover at `position` of `text` shows, read against `session`.
///
/// # Specification
/// - requires: `session` last checked `text`, as the server's synchronisation
///   leaves it; a stale session answers what it last accepted.
/// - ensures: on the name of a declaration — from its first character to just
///   past its last — a fenced `gandr` block holding the name and, when the
///   session's latest resume spells it, ` : ` and its type, followed by the
///   documentation the latest accepted revision filed for the declaring form,
///   after a blank line; the range is the name's. The type is the one of the
///   occurrence of the name this declaration is among the document's non-module
///   declarations. Absent elsewhere, and absent when neither a type nor
///   documentation is known.
/// - provides: the answer to `textDocument/hover`.
/// - fails: never; an absence names its reason.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a documented definition, an undocumented one, a member of
///   a module sharing its name with another module's, a parameter, a word in a
///   comment and the cursor at either edge of a name are asserted at their
///   exact answers. Hovering a parameter as a definition, reading another
///   occurrence's type or dropping the documentation changes them.
/// - witness: `hover::tests::a_declaration_hovers_its_type_and_documentation`
/// - witness: `hover::tests::only_a_declared_name_hovers`
#[spec(ensures: |ref ret| match *ret {
    Maybe::Present(ref hover) => hover.contents.value.starts_with("```gandr\n")
        && hover.range.start <= position && position <= hover.range.end,
    Maybe::Absent(_) => true,
})]
pub fn hover<Store, Blocks>(
    text: SourceText<'_>,
    session: &Session<Store, Blocks>,
    position: Position,
) -> Maybe<Hover, hovered::Absent>
{
    let (Ok(grammar), Ok(roles)) = (grammar(), roles())
    else {
        return Maybe::Absent(hovered::Absent::Unparsed);
    };
    let Ok(parsed) = parse(grammar, text)
    else {
        return Maybe::Absent(hovered::Absent::Unparsed);
    };
    let tree = parsed.into_tree();
    let index = LineIndex::new(<&str>::from(text).into());
    let found = declarations(grammar, roles, &tree, &index);
    let on_name = |found: &(_, crate::protocol::DocumentSymbol)| {
        found.1.selection_range.start <= position && position <= found.1.selection_range.end
    };
    let Some(at) = found.iter().position(on_name)
    else {
        return Maybe::Absent(hovered::Absent::Undeclared);
    };
    let (earlier, rest) = found.split_at(at);
    let Some(&(form, ref symbol)) = rest.first()
    else {
        return Maybe::Absent(hovered::Absent::Undeclared);
    };
    let typed = if symbol.kind == SymbolKind::MODULE {
        None
    }
    else {
        let occurrence = earlier
            .iter()
            .filter(|other| other.1.name == symbol.name && other.1.kind != SymbolKind::MODULE)
            .count();
        let reference = Reference::Item {
            key: ItemKey::from(symbol.name.as_str()),
            occurrence: Occurrence::from(occurrence),
        };
        match type_at(session.last(), &reference, PageWidth::from(HOVER_WIDTH)) {
            | Maybe::Present(spelled) => Some(spelled),
            | Maybe::Absent(_) => None,
        }
    };
    let documented = tree
        .node(form)
        .and_then(|node| match session.documentation(node.digest()) {
            | Maybe::Present(text) => Some(text),
            | Maybe::Absent(_) => None,
        });
    if typed.is_none() && documented.is_none() {
        return Maybe::Absent(hovered::Absent::Unknown);
    }
    let mut value = match typed {
        | Some(spelled) => format!("```gandr\n{} : {spelled}\n```", symbol.name),
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
        range: symbol.selection_range,
    })
}

#[cfg(test)]
mod tests
{
    use gandr_core_incremental::BackendArtifact;
    use gandr_core_incremental::MemoryCheckpointStore;
    use gandr_storage_records::InMemoryBlockStore;
    use gandr_surface_dispatcher::SourceRoot;
    use gandr_surface_session::Session;
    use gandr_surface_syntax::SourceText;
    use quenchant_shape::shape::Maybe;

    use super::hover;
    use super::hovered;
    use crate::position::Character;
    use crate::position::Line;
    use crate::position::Position;
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
        let session = checked(text);
        match hover(text, &session, Position { line, character }) {
            | Maybe::Present(shown) => Ok(shown.contents.value),
            | Maybe::Absent(reason) => Err(reason),
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
    }

    #[test]
    fn only_a_declared_name_hovers()
    {
        let text = SourceText::from("def x = 1 ;\n// x\ndef f(x: String) -> -F String { ret x }\n");
        assert!(
            shown(text, (0.into(), 4.into())).is_ok(),
            "the name's first character hovers"
        );
        assert!(
            shown(text, (0.into(), 5.into())).is_ok(),
            "just past the name hovers"
        );
        assert_eq!(
            shown(text, (0.into(), 6.into())),
            Err(hovered::Absent::Undeclared)
        );
        assert_eq!(
            shown(text, (1.into(), 3.into())),
            Err(hovered::Absent::Undeclared),
            "a word in a comment is no declaration"
        );
        assert_eq!(
            shown(text, (2.into(), 6.into())),
            Err(hovered::Absent::Undeclared),
            "a parameter is no declaration"
        );
        assert_eq!(
            shown(
                SourceText::from("def later : Integer ;\n"),
                (1.into(), 0.into())
            ),
            Err(hovered::Absent::Undeclared)
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
