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

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::format;
use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_dispatcher::TypedSpan;
use gandr_surface_pretty::PageWidth;
use gandr_surface_pretty::Style;
use gandr_surface_render_remote::ByteOffset;
use gandr_surface_render_remote::LineIndex;
use gandr_surface_syntax::ByteSpan;
use quenchant_shape::shape::Maybe;

use crate::hover::Hovering;
use crate::position::Position;
use crate::protocol::InlayHint;
use crate::protocol::InlayHintKind;
use crate::reading::Tile;

/// The columns a hint's type is laid out on: wide enough that the printer
/// writes on one line any type a line of the editor can hold.
const HINT_WIDTH: u32 = 1_000;

/// The hints over `window` of a copy whose reading's tiles are `tiles` and
/// whose hovers `hovering` answers, each type spelled in `style`, in
/// document order.
///
/// # Specification
/// - requires: `hovering` and `tiles` were read off the same text, which
///   `index` indexes.
/// - ensures: one hint per binder [`TypedSpan`] the table answers in `window`
///   whose span is a tile of `tiles` its form writes no type for, at whose
///   start the table answers no referent, and whose type is spelled on one
///   line; the latest such entry for a span, as a hover chooses it. The hint
///   stands at the end of the name, labelled `: ` and the type, a type hint.
/// - fails: never; a span the index cannot place is skipped.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a lambda's, a pattern's, a `run`'s, a `for`'s and a
///   handler's binders are hinted; a parameter, an annotated `run`, a use, a
///   constructor in a pattern and a declaration's name are not; a window holds
///   only the hints inside it.
/// - witness: `inlay::tests::each_binder_that_writes_no_type_is_hinted`
/// - witness: `server::tests::an_inlay_hint_request_answers_the_binders_in_its_range`
#[spec(ensures: |ret| ret.is_sorted_by(|before, after| before.position <= after.position))]
#[must_use]
pub fn hints(
    (hovering, tiles): (&Hovering, &[Tile]),
    index: &LineIndex<'_>,
    window: ByteSpan,
    style: Style,
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
            Some(InlayHint {
                position: Position::of_byte(
                    index,
                    ByteOffset::from(usize::from(binder.span().end())),
                )
                .ok()?,
                label: format!(": {ty}"),
                kind: InlayHintKind::TYPE,
            })
        })
        .collect()
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
            hints((&hovering, reading.tiles()), &index, window, style)
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
                "39:8 : Nat",
                "42:13 : Nat",
                "59:13 : Nat",
                "103:13 : Nat",
                "118:10 : Nat",
                "121:11 : Nat",
                "122:19 : Integer",
                "122:22 : Stack(-F [Div] Unit, -F [Div] Nat)",
                "154:8 : Nat",
                "157:13 : Nat",
                "177:8 : Nat",
                "184:8 : Nat",
                "184:17 : Nat",
            ],
            "each `run`, `for`, pattern and handler binder, an unread one among them (#1439), and \
             no parameter, use or constructor"
        );
        assert_eq!(
            hinted("fixture/surface/typed-bind.gandr", 1 .. 1_000),
            ["26:35 : Nat"],
            "the lambda's binder, and no annotated `run`"
        );
        assert_eq!(
            hinted("fixture/surface/control-flow.gandr", 177 .. 178),
            ["177:8 : Nat"],
            "a window holds the hints inside it alone"
        );
        assert_eq!(
            hinted("fixture/surface/typed-bind.gandr", 27 .. 1_000),
            [""; 0],
            "a window past every unannotated binder holds none"
        );
    }
}
