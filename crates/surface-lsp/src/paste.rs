//! Paste with imports: the sources declaring what a copied range of a
//! document names, so that a paste into another document can import them.
//!
//! A copy asks `gandr/copiedSources` with the ranges copied; the editor keeps
//! the answer with the copied text, and a paste into another gandr document
//! asks `gandr/importFiles` for the imports of those sources it lacks. A use
//! counts when the copy holds it whole and it names a declaration of the
//! unit, not a binder; a declaration the copy itself holds is pasted with it,
//! and its source is not answered for it.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_dispatcher::Referent;
use gandr_surface_render_remote::LineIndex;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;

use crate::hover::Hovering;
use crate::position::Range;
use crate::protocol::DocumentUri;

/// The sources declaring what `ranges` of the document at `uri` name, the
/// document read through `hovering` and indexed by `index`, each once,
/// ascending.
///
/// # Specification
/// - requires: `hovering` and `index` were made from the document's held text.
/// - ensures: the URI of each source declaring the referent of a use some range
///   holds whole, where that referent is a name the unit declares and, for the
///   document's own source, its declaring form lies outside every range: `uri`
///   for the document's own source, a sibling's path as a `file` URI otherwise;
///   a sibling with no path is not answered. An inverted range holds nothing.
/// - provides: the answer to `gandr/copiedSources`, which a copy asks.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a copied use of a sibling's declaration answers the
///   sibling; of the document's own declaration outside the copy, the document;
///   of one the copy holds, and of a binder, nothing.
/// - witness: `server::tests::a_copy_answers_the_sources_its_names_are_declared_in`
#[spec(ensures: |ret| ret.is_sorted() && ret.windows(2).all(|pair| pair.first() != pair.last()))]
#[must_use]
pub fn copied(
    hovering: &Hovering,
    (uri, index): (&DocumentUri, &LineIndex<'_>),
    ranges: &[Range],
) -> Vec<DocumentUri>
{
    let table = hovering.table();
    let own = table.own_source();
    let declared = table.declared_names();
    let spans: Vec<ByteSpan> = ranges
        .iter()
        .filter_map(|range| {
            ByteSpan::new(
                ByteOffset::from(usize::from(range.start.byte(index))),
                ByteOffset::from(usize::from(range.end.byte(index))),
            )
            .ok()
        })
        .collect();
    let held = |referent: &Referent| {
        spans.iter().any(|span| {
            span.start() <= referent.extent().start() && referent.extent().end() <= span.end()
        })
    };
    spans
        .iter()
        .flat_map(|&span| table.uses_within(span))
        .map(|(_, referent)| referent)
        .filter(|referent| {
            declared
                .binary_search_by_key(referent, |&(named, _)| named)
                .is_ok()
                && (referent.source() != own || !held(referent))
        })
        .filter_map(|referent| {
            if referent.source() == own {
                Some(uri.clone())
            }
            else {
                hovering.path(&referent).and_then(DocumentUri::of_path)
            }
        })
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}
