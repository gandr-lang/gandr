//! The report card of a judged text.

use alloc::sync::Arc;

use gandr_surface_diagnostics::Verbosity;
use gandr_surface_lsp_core::view::report;
use gandr_surface_render_remote::ByteOffset;
use gandr_surface_render_remote::ByteRange;
use gandr_surface_render_remote::DiagnosticCode;
use gandr_surface_render_remote::MarkKind;
use gandr_surface_syntax::SourceText;

use crate::position::Character;
use crate::position::Line;
use crate::position::Position;
use crate::position::Range;
use crate::protocol::Diagnostic;
use crate::protocol::DocumentUri;
use crate::protocol::Severity;
use crate::reading::Reading;
use crate::recheck::open;
use crate::recheck::recheck;

/// The byte range `[start, end)`.
///
/// # Specification
/// trivial.
fn bytes(
    start: ByteOffset,
    end: ByteOffset,
) -> ByteRange
{
    ByteRange::new(start, end).expect("an ordered range")
}

#[test]
fn a_report_cards_errors_and_marks_holes()
{
    let uri = DocumentUri::from("file:///strict/view.gandr");
    let text = include_str!("view/unformatted/a-report-cards-errors-and-marks-holes.gandr");
    let mut published = recheck(
        &uri,
        &mut open(&uri, &Arc::default()),
        SourceText::from(text),
        &gandr_surface_dispatcher::Unshadowed,
        Verbosity::User,
        gandr_surface_grammar::Spelling::Unicode,
        quenchant_shape::shape::Maybe::Absent(
            gandr_surface_lsp_base::quiet::formless::Absent::Uncareted,
        ),
    )
    .diagnostics;
    // The pipeline publishes no goal for a hole yet; one is published as
    // a goal report would be, at the hole.
    let at = |character: u32| Position {
        line: Line::from(1_u32),
        character: Character::from(character),
    };
    published.push(Diagnostic::new(
        Range {
            start: at(8_u32),
            end: at(12_u32),
        },
        Severity::INFORMATION,
        String::from("goal ?gap : Integer"),
    ));
    let view = report(
        SourceText::from(text),
        &Reading::of(SourceText::from(text)),
        &published,
    );
    assert_eq!(view.source, text, "the text travels whole");
    assert!(!view.highlights.is_empty(), "the text is highlighted");
    let refusal = text.find("\"one\"").expect("the refused literal");
    let hole = text.find("?gap").expect("the hole");
    assert_eq!(
        view.diagnostics
            .iter()
            .map(|card| (card.code, card.span))
            .collect::<Vec<_>>(),
        [(
            DiagnosticCode::Other,
            Some(bytes(
                ByteOffset::from(refusal),
                ByteOffset::from(refusal + "\"one\"".len())
            ))
        )],
        "the refusal is the one card, at its bytes"
    );
    assert!(
        view.diagnostics[0].message.starts_with('['),
        "the refusal's identifier leads its message: {}",
        view.diagnostics[0].message
    );
    assert_eq!(
        view.marks
            .iter()
            .map(|mark| (mark.kind, usize::from(mark.range.start())))
            .collect::<Vec<_>>(),
        [(MarkKind::Error, refusal), (MarkKind::EmptyHole, hole)],
        "the refusal is underlined and the hole tinted"
    );
    let faulted = report(
        SourceText::from(text),
        &Reading::of(SourceText::from(text)),
        &[Diagnostic::at_origin(String::from("the session faulted"))],
    );
    assert_eq!(
        faulted
            .diagnostics
            .iter()
            .map(|card| (card.span, card.message.as_str()))
            .collect::<Vec<_>>(),
        [(None, "the session faulted")],
        "a fault at the origin is a card placed nowhere"
    );
    assert!(faulted.marks.is_empty(), "an unplaced fault marks nothing");
}
