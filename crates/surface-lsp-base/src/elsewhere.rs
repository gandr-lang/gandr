//! The names that sources elsewhere declare.
//!
//! A source under a folder that an editor opened can declare a name that the
//! document's import closure does not reach. [`Declared`] is one name that a
//! source declares. [`Unimported`] is a source that the document does not
//! import, with its names. [`Elsewhere`] holds those sources and the edit
//! that imports one of them. [`unimported_as`] reads how a slot offers such a
//! name: a completion offers it with its import, and a code action imports
//! it for a name that names nothing.

use alloc::string::String;
use alloc::vec::Vec;
use std::path::Path;

use gandr_surface_lowering::Visibility;

use crate::inline::Category;
use crate::position::Range;
use crate::protocol::CompletionItemKind;
use crate::protocol::SymbolKind;
use crate::protocol::TextEdit;

/// One name a text declares: its name, the name folded to lower case, what it
/// declares, the declaration holding it and the range of its name in the
/// text.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Declared
{
    /// The name folded to lower case, which a query is compared with.
    pub folded: String,
    /// The name as written.
    pub name: String,
    /// What it declares, as the outline names it.
    pub kind: SymbolKind,
    /// The name of the declaration holding it; none at the top of its
    /// source.
    pub container: Option<String>,
    /// The range of its name in the text.
    pub range: Range,
    /// Whether its source exports it, as the outline reads its `pub` mark.
    pub exported: Visibility,
}

/// A source the document's import closure does not reach, under a folder an
/// editor opened: its path and the names its file declares.
#[derive(Clone, Copy, Debug)]
pub struct Unimported<'held>
{
    /// Its path, as the dispatcher's `named_path` names it.
    pub path: &'held Path,
    /// The names its file declares, as the server's `search::declared` reads
    /// them.
    pub names: &'held [Declared],
}

/// The sources of the opened folders' projects a document does not import, and
/// how an import of one is written into it.
#[derive(Clone, Copy)]
pub struct Elsewhere<'held>
{
    /// The sources, each once.
    pub sources: &'held [Unimported<'held>],
    /// The edit importing the source at a path into the document, as the
    /// server's reading of the document writes it.
    pub import: &'held dyn Fn(&Path) -> Vec<TextEdit>,
}

/// How a slot of `category` offers `declared`, a name of a source the document
/// does not import, among `names`, every name that source declares: as the
/// protocol's kind for it, or not at all.
///
/// # Specification
/// - ensures: only a name its source exports is offered, since importing the
///   source brings no other into scope: a value or a computation offers a value
///   declared at its source's top as a function; a value, a computation or a
///   pattern offers a constructor whose family is declared at its source's top
///   as a constructor; a type offers a family declared at its source's top as
///   an enum; nothing else is offered, a module's or a theory's member among
///   it.
/// - fails: never.
/// - panics: none.
/// - executable: none — the clause is the match itself.
///
/// # Adequacy
/// - hypothesis: L3 — the unimported witness offers a function in a body, a
///   family in a type and a constructor in a pattern, and a module's member and
///   a private value nowhere.
/// - witness: `gandr-surface-lsp::complete::tests::a_name_no_import_reaches_is_offered_with_its_import`
#[must_use]
#[inline]
pub fn unimported_as(
    category: Category,
    declared: &Declared,
    names: &[Declared],
) -> Option<CompletionItemKind>
{
    if declared.exported == Visibility::Private {
        return None;
    }
    let top = declared.container.is_none();
    match (category, declared.kind) {
        (Category::Value | Category::Computation, SymbolKind::FUNCTION | SymbolKind::VARIABLE)
            if top =>
        {
            Some(CompletionItemKind::FUNCTION)
        },
        (Category::Value | Category::Computation | Category::Pattern, SymbolKind::CONSTRUCTOR)
            if names.iter().any(|family| {
                family.container.is_none()
                    && matches!(family.kind, SymbolKind::ENUM | SymbolKind::STRUCT)
                    && declared.container.as_deref() == Some(family.name.as_str())
            }) =>
        {
            Some(CompletionItemKind::CONSTRUCTOR)
        },
        (Category::Type, SymbolKind::ENUM | SymbolKind::STRUCT) if top => {
            Some(CompletionItemKind::ENUM)
        },
        _ => None,
    }
}
