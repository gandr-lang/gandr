//! Definitions: where what a written name refers to is written, and where the
//! families the type of a node names are declared.
//!
//! A definition request reads the referent index the document's type table
//! keeps ([`TypeTable::referent`]): every use the lowering resolved, with the
//! binder or declaration it resolved to, built once per text beside the types
//! a hover reads. A type-definition request reads the families the chosen
//! node's type names ([`TypeTable::type_referents`]). Neither resolves a name
//! again, and neither reads the text for one.
//!
//! A referent in a sibling the document imports is answered at the sibling's
//! path, its position counted in the sibling's text as the closure laid it out.
//! A position just past a name answers the name, as a caret left at a name's
//! end means it.
//!
//! [`TypeTable::referent`]: gandr_surface_dispatcher::TypeTable::referent
//! [`TypeTable::type_referents`]: gandr_surface_dispatcher::TypeTable::type_referents

use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_dispatcher::Referent;
use gandr_surface_render_remote::ByteOffset as RenderOffset;
use gandr_surface_render_remote::LineIndex;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::hover::Hovering;
use crate::position::Position;
use crate::position::Range;
use crate::protocol::Answer;
use crate::protocol::DocumentUri;
use crate::protocol::Linked;
use crate::protocol::Location;
use crate::protocol::LocationLink;

/// Which request a definition answers.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Goto
{
    /// `textDocument/definition`: what the name at the position refers to.
    Definition,
    /// `textDocument/typeDefinition`: the families the type of the node at
    /// the position names.
    TypeDefinition,
}

/// The range `span` covers in the text `index` indexes.
///
/// # Specification
/// trivial.
fn ranged(
    index: &LineIndex<'_>,
    span: ByteSpan,
) -> Option<Range>
{
    Range::of_bytes(
        index,
        RenderOffset::from(usize::from(span.start())),
        RenderOffset::from(usize::from(span.end())),
    )
    .ok()
}

/// What a `goto` request at `position` of `text`, the document at `uri` whose
/// copy keeps `hovering`, answers to a client that takes links as `linked`
/// says.
///
/// # Specification
/// - requires: `hovering` was read off `text`.
/// - ensures: for [`Goto::Definition`], the referent of the use holding the
///   position's byte, or else the byte before it; for [`Goto::TypeDefinition`],
///   the declaration of each family the type of the node there names, in the
///   order the table answers them. Each target is named by the request's URI
///   when it stands in the document itself, and by its source's path as a
///   `file` URI when it stands in a sibling, its ranges counted in that
///   source's text: links from the use, or from the node, to the whole binder
///   or declaring form with its name selected when `linked` holds, the name's
///   location otherwise. A target whose source names no path or no range is
///   dropped; none is the empty answer.
/// - provides: the answer to `textDocument/definition` and
///   `textDocument/typeDefinition` for a held document.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a parameter's use, a declaration's use and a constructor
///   in a pattern answer their sites, as links and as locations; a caret just
///   past a name answers it; a keyword answers nothing; a use's type answers
///   its family; a name a sibling declares answers the sibling's path.
/// - witness: `server::tests::definition_answers_what_a_use_refers_to_795`
/// - witness: `server::tests::type_definition_answers_the_family_a_use_s_type_names_795`
/// - witness: `tests::session::a_definition_in_a_sibling_answers_the_sibling_s_path_795`
#[spec(ensures: |ret| matches!(ret, Answer::Links(_) | Answer::Locations(_))
    && matches!(ret, Answer::Links(_)) == linked.0)]
#[must_use]
pub fn targets(
    text: SourceText<'_>,
    uri: &DocumentUri,
    hovering: &Hovering,
    position: Position,
    goto: Goto,
    linked: Linked,
) -> Answer
{
    let table = hovering.table();
    let index = LineIndex::new(<&str>::from(text).into());
    let at = ByteOffset::from(usize::from(position.byte(&index)));
    let before = usize::from(at).checked_sub(1_usize).map(ByteOffset::from);
    let (origin, referents): (Option<ByteSpan>, Vec<Referent>) = match goto {
        Goto::Definition => {
            let found = match table.referent(at) {
                Maybe::Present(found) => Some(found),
                Maybe::Absent(_) => before.and_then(|before| match table.referent(before) {
                    Maybe::Present(found) => Some(found),
                    Maybe::Absent(_) => None,
                }),
            };
            match found {
                Some((span, referent)) => (Some(span), Vec::from([referent])),
                None => (None, Vec::new()),
            }
        },
        Goto::TypeDefinition => {
            let probe = if table.answering(at).is_some() {
                Some(at)
            }
            else {
                before.filter(|&before| table.answering(before).is_some())
            };
            probe.map_or_else(
                || (None, Vec::new()),
                |probe| (table.answering(probe), table.type_referents(probe)),
            )
        },
    };
    let origin = origin.and_then(|span| ranged(&index, span));
    let own = table.own_source();
    let mut links = Vec::with_capacity(referents.len());
    for referent in referents {
        let (target, ranges) = if referent.source() == own {
            (
                uri.clone(),
                ranged(&index, referent.extent()).zip(ranged(&index, referent.named())),
            )
        }
        else {
            let Some(target) = hovering.path(&referent).and_then(DocumentUri::of_path)
            else {
                continue;
            };
            let Some(sibling) = table.source_text(referent.source())
            else {
                continue;
            };
            let sibling = LineIndex::new(<&str>::from(sibling).into());
            (
                target,
                ranged(&sibling, referent.extent()).zip(ranged(&sibling, referent.named())),
            )
        };
        if let (Some(origin), Some((whole, named))) = (origin, ranges) {
            links.push(LocationLink {
                origin_selection_range: origin,
                target_uri: target,
                target_range: whole,
                target_selection_range: named,
            });
        }
    }
    if linked.0 {
        Answer::Links(links)
    }
    else {
        Answer::Locations(
            links
                .into_iter()
                .map(|link| Location {
                    uri: link.target_uri,
                    range: link.target_selection_range,
                })
                .collect(),
        )
    }
}
