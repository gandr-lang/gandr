//! Inlay hints: the type of each binder whose form writes none, drawn after
//! its name as the hover over the name spells it.
//!
//! A binder is an entry the type table keeps as one, written in the source:
//! a lambda's parameter, a pattern's field, a `run` or `for` binder, a
//! handler's arguments. Its name is one tile of the copy's reading that
//! nothing refers through: a use, a constructor in a pattern and a
//! declaration's own name each answer a referent, and none is hinted. A
//! binder whose form follows its name with `:` writes its type, as a
//! parameter `(n : Nat)` and an annotated `run m : Nat <-` do, and is not
//! hinted either.
//!
//! A label is cut where the printer wrote a declaration's name
//! ([`TypeTable::written_referents`]): each such name is a part linked to the
//! declaration's name, in the document or the sibling declaring it, the text
//! between names parts of their own. A client that resolves a label's
//! locations gets the parts unlinked with the document to resolve them from,
//! and `inlayHint/resolve` lays the one hint out again and links it
//! ([`hint_at`]): placing a name in a sibling indexes that sibling's text,
//! which a range of hints would otherwise pay for every name it draws.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_dispatcher::Referent;
use gandr_surface_dispatcher::TypeTable;
use gandr_surface_dispatcher::TypedSpan;
use gandr_surface_pretty::PageWidth;
use gandr_surface_pretty::Presentation;
use gandr_surface_pretty::Style;
use gandr_surface_pretty::WrittenName;
use gandr_surface_render_remote::ByteOffset;
use gandr_surface_render_remote::LineIndex;
use gandr_surface_syntax::ByteSpan;
use quenchant_shape::shape::Maybe;

use crate::goto::Locator;
use crate::hover::Hovering;
use crate::position::Position;
use crate::protocol::DocumentUri;
use crate::protocol::HintData;
use crate::protocol::HintLabel;
use crate::protocol::HintLabelPart;
use crate::protocol::InlayHint;
use crate::protocol::InlayHintKind;
use crate::protocol::Location;
use crate::protocol::ResolvesHintLocations;
use crate::reading::Tile;

/// The columns a hint's type is laid out on: wide enough that the printer
/// writes on one line any type a line of the editor can hold.
const HINT_WIDTH: u32 = 1_000;

/// The hints over `window` of the copy of the document at `uri` whose
/// reading's tiles are `tiles` and whose hovers `hovering` answers, each type
/// spelled in `style`, in document order, each name a label writes for a
/// declaration located now or, when `deferred` holds, by a resolution.
///
/// # Specification
/// - requires: `hovering` and `tiles` were read off the same text, which
///   `index` indexes.
/// - ensures: one hint per binder [`TypedSpan`] the table answers in `window`
///   whose span is a tile of `tiles` its form writes no type for, at whose
///   start the table answers no referent, and whose type is spelled on one
///   line; the latest such entry for a span, as a hover chooses it. The hint
///   stands at the end of the name, labelled `: ` and the type, a type hint. A
///   type naming no declaration is labelled whole; one naming any is labelled
///   in parts, each name the type writes for a declaration a part of its own,
///   located at the declaration's name unless `deferred` holds, in which case
///   no part is located and the hint carries `uri` for its resolution.
/// - fails: never; a span the index cannot place is skipped, and a name no
///   document places is a part without a location.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a lambda's, a pattern's, a `run`'s, a `for`'s and a
///   handler's binders are hinted; a parameter, an annotated `run`, a use, a
///   constructor in a pattern and a declaration's name are not; a window holds
///   only the hints inside it; a type's family names are parts linked to their
///   declarations, in the document or a sibling.
/// - witness: `inlay::tests::each_binder_that_writes_no_type_is_hinted`
/// - witness: `server::tests::an_inlay_hint_request_answers_the_binders_in_its_range`
/// - witness: `server::tests::an_inlay_hint_links_the_families_its_type_names_764`
#[spec(ensures: |ret| ret.is_sorted_by(|before, after| before.position <= after.position)
    && ret.iter().all(|hint| hint.data.is_none() || deferred.0))]
#[must_use]
pub fn hints(
    (hovering, tiles): (&Hovering, &[Tile]),
    (uri, index): (&DocumentUri, &LineIndex<'_>),
    window: ByteSpan,
    (style, deferred): (Style, ResolvesHintLocations),
) -> Vec<InlayHint>
{
    let table = hovering.table();
    let bare: BTreeSet<ByteSpan> = tiles
        .iter()
        .filter(|tile| {
            !tile.annotated && tile.span.start() < window.end() && window.start() < tile.span.end()
        })
        .map(|tile| tile.span)
        .collect();
    let mut locator = (!deferred.0).then(|| Locator::new(hovering, uri, index));
    table
        .binders(window, PageWidth::from(HINT_WIDTH), style)
        .filter_map(|binder| match binder {
            Maybe::Present(binder) => Some((binder.span(), binder)),
            Maybe::Absent(_) => None,
        })
        .filter(|&(span, _)| {
            bare.contains(&span) && matches!(table.referent(span.start()), Maybe::Absent(_))
        })
        .fold(
            BTreeMap::new(),
            |mut latest: BTreeMap<ByteSpan, TypedSpan>, (span, binder)| {
                let _earlier = latest.insert(span, binder);
                latest
            },
        )
        .into_values()
        .filter_map(|binder| {
            let ty: &str = binder.ty().as_ref();
            if ty.contains('\n') {
                return None;
            }
            let position =
                Position::of_byte(index, ByteOffset::from(usize::from(binder.span().end())))
                    .ok()?;
            let label = label(table, binder.ty(), locator.as_mut());
            let data = (deferred.0 && matches!(label, HintLabel::Parts(_)))
                .then(|| HintData { uri: uri.clone() });
            Some(InlayHint {
                position,
                label,
                kind: InlayHintKind::TYPE,
                data,
            })
        })
        .collect()
}

/// The hint drawn at `position` of the copy of the document at `uri`, as
/// [`hints`] answers it with every name located: what `inlayHint/resolve`
/// answers.
///
/// # Specification
/// - requires: as [`hints`].
/// - ensures: the hint [`hints`] answers over the bytes around `position` with
///   nothing deferred whose position is `position`; none when no hint stands
///   there, as after the text changed under it.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a deferred hint resolves to the same label with each
///   family name located.
/// - witness: `server::tests::an_inlay_hint_links_the_families_its_type_names_764`
#[spec(ensures: |ret| ret.as_ref().is_none_or(|hint| hint.position == position && hint.data.is_none()))]
#[must_use]
pub fn hint_at(
    (hovering, tiles): (&Hovering, &[Tile]),
    (uri, index): (&DocumentUri, &LineIndex<'_>),
    position: Position,
    style: Style,
) -> Option<InlayHint>
{
    let at = usize::from(position.byte(index));
    let window = ByteSpan::new(
        gandr_surface_syntax::ByteOffset::from(at.saturating_sub(1_usize)),
        gandr_surface_syntax::ByteOffset::from(at.saturating_add(1_usize)),
    )
    .ok()?;
    hints(
        (hovering, tiles),
        (uri, index),
        window,
        (style, ResolvesHintLocations(false)),
    )
    .into_iter()
    .find(|hint| hint.position == position)
}

/// The label of a hint whose type `presented` spells: `: ` and the type,
/// whole when it writes no declaration's name, and otherwise in parts, each
/// such name a part located by `locator` when one is given.
///
/// # Specification
/// - requires: `table` spelled `presented`.
/// - ensures: the parts, or the whole text, read `: ` and the type; each name
///   [`TypeTable::written_referents`] pairs is a part of its own, located at
///   its declaration's name when `locator` places it; the text between names is
///   unlocated, and no part is empty.
/// - fails: never; a name whose bytes do not fit the text labels the type
///   whole.
/// - panics: none.
/// - executable: none — a part's location is counted in a text the predicate
///   would index again.
///
/// # Adequacy
/// - hypothesis: L3 — as [`hints`].
/// - witness: `server::tests::an_inlay_hint_links_the_families_its_type_names_764`
fn label(
    table: &TypeTable,
    presented: &Presentation,
    mut locator: Option<&mut Locator<'_, '_>>,
) -> HintLabel
{
    let text: &str = presented.as_ref();
    let written = table.written_referents(presented);
    let bytes = |name: &WrittenName| {
        Some((
            usize::try_from(u64::from(name.start())).ok()?,
            usize::try_from(u64::from(name.end())).ok()?,
        ))
    };
    let cuts: Option<Vec<(usize, usize, &Referent)>> = written
        .iter()
        .map(|&(ref name, ref referent)| {
            let (start, end) = bytes(name)?;
            text.get(start .. end).map(|_| (start, end, referent))
        })
        .collect();
    let Some(cuts) = cuts.filter(|cuts| !cuts.is_empty())
    else {
        return HintLabel::Text(format!(": {text}"));
    };
    let tail = cuts.last().map_or(0_usize, |&(_, end, _)| end);
    let pieces = cuts
        .iter()
        .scan(0_usize, |from, &(start, end, referent)| {
            let gap = (*from, start, None);
            *from = end;
            Some([gap, (start, end, Some(referent))])
        })
        .flatten()
        .chain(core::iter::once((tail, text.len(), None)));
    HintLabel::Parts(
        core::iter::once(HintLabelPart {
            value: String::from(": "),
            location: None,
        })
        .chain(pieces.filter_map(|(start, end, referent)| {
            let value = text.get(start .. end).filter(|value| !value.is_empty())?;
            let location = referent
                .and_then(|referent| locator.as_mut()?.place(referent))
                .map(|placed| Location {
                    uri: placed.uri,
                    range: placed.named,
                });
            Some(HintLabelPart {
                value: String::from(value),
                location,
            })
        }))
        .collect(),
    )
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;
    use alloc::vec::Vec;

    use gandr_core_incremental::BackendArtifact;
    use gandr_core_incremental::MemoryCheckpointStore;
    use gandr_storage_records::InMemoryBlockStore;
    use gandr_surface_dispatcher::SourceRoot;
    use gandr_surface_pretty::Form;
    use gandr_surface_pretty::Spelling;
    use gandr_surface_render_remote::LineIndex;
    use gandr_surface_session::Session;
    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::ByteSpan;
    use gandr_surface_syntax::SourceText;

    use super::hints;
    use crate::hover::hovering;
    use crate::reading::Reading;
    use crate::recheck::grammar;

    #[test]
    fn each_binder_that_writes_no_type_is_hinted()
    {
        // The hints over the lines `lines` of the corpus source at `file`, each
        // as its line and character, one-based, and its label.
        let hinted = |file: &str, lines: core::ops::Range<usize>| -> Vec<String> {
            let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../surface-corpus")
                .join(file);
            let written = std::fs::read_to_string(&path).expect("the corpus source is read");
            let text = SourceText::from(written.as_str());
            let grammar = grammar().expect("the grammar builds");
            let mut session = Session::new(
                grammar.clone(),
                SourceRoot::Strict,
                MemoryCheckpointStore::default(),
                InMemoryBlockStore::default(),
                BackendArtifact::from(b"inlay".as_slice()),
            );
            let _judged = session.judge(text).expect("the session does not fault");
            let hovering = hovering(text, &path, &session, &gandr_surface_dispatcher::Unshadowed);
            let reading = Reading::of(text);
            let index = LineIndex::new(written.as_str().into());
            let offset = |line: usize| {
                ByteOffset::from(
                    written
                        .split_inclusive('\n')
                        .take(line)
                        .map(str::len)
                        .sum::<usize>(),
                )
            };
            let window = ByteSpan::new(
                offset(lines.start.saturating_sub(1)),
                offset(lines.end.saturating_sub(1)),
            )
            .expect("an ordered window");
            let style = gandr_surface_pretty::Style {
                form: Form::Sugared,
                spelling: Spelling::Unicode,
            };
            let uri = crate::protocol::DocumentUri::from("file:///corpus/hinted.gandr");
            hints(
                (&hovering, reading.tiles()),
                (&uri, &index),
                window,
                (style, crate::protocol::ResolvesHintLocations(false)),
            )
            .into_iter()
            .map(|hint| {
                let at = serde_json::to_value(hint.position).expect("a position serializes");
                std::format!(
                    "{}:{} {}",
                    at["line"].as_u64().unwrap_or_default().saturating_add(1),
                    at["character"]
                        .as_u64()
                        .unwrap_or_default()
                        .saturating_add(1),
                    hint.label
                )
            })
            .collect()
        };
        assert_eq!(
            hinted("fixture/surface/control-flow.gandr", 1 .. 1_000),
            [
                "27:8 : Nat",
                "38:8 : Nat",
                "41:13 : Nat",
                "57:13 : Nat",
                "97:13 : Nat",
                "111:10 : Nat",
                "114:11 : Nat",
                "115:19 : Integer",
                "115:22 : Stack(-F [Div] Unit, -F [Div] Nat)",
                "146:8 : Nat",
                "149:13 : Nat",
                "167:8 : Nat",
                "174:8 : Nat",
                "174:17 : Nat",
            ],
            "each `run`, `for`, pattern and handler binder, an unread one among them (#1439), and \
             no parameter, use or constructor"
        );
        assert_eq!(
            hinted("fixture/surface/typed-bind.gandr", 1 .. 1_000),
            ["25:35 : Nat"],
            "the lambda's binder, and no annotated `run`"
        );
        assert_eq!(
            hinted("fixture/surface/control-flow.gandr", 167 .. 168),
            ["167:8 : Nat"],
            "a window holds the hints inside it alone"
        );
        assert_eq!(
            hinted("fixture/surface/typed-bind.gandr", 27 .. 1_000),
            [""; 0],
            "a window past every unannotated binder holds none"
        );
    }
}
