//! The render bus's report of a document: its text, highlights, marks and
//! cards, read off the diagnostics its last synchronisation published.

use alloc::string::String;
use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_render_remote::ByteRange;
use gandr_surface_render_remote::DiagCard;
use gandr_surface_render_remote::DiagnosticCode;
use gandr_surface_render_remote::LineIndex;
use gandr_surface_render_remote::MarkKind;
use gandr_surface_render_remote::MarkSpan;
use gandr_surface_render_remote::ReportView;
use gandr_surface_syntax::SourceText;

use crate::position::Range;
use crate::protocol::Diagnostic;
use crate::protocol::Severity;
use crate::recheck::highlight;

/// The report the render bus carries for `text`, whose last synchronisation
/// published `published`.
///
/// # Specification
/// - requires: `published` was published for `text`.
/// - ensures: the report carries `text` whole and the highlighter's spans over
///   it. Each error and warning becomes one diagnostic card, in the order
///   published: its code the registry's when the diagnostic's code is a
///   registry spelling and `Other` otherwise, its message the diagnostic's,
///   after the code in brackets when that is not a registry spelling, its span
///   the diagnostic's range in bytes — absent for one at the origin, where an
///   unlocated report is published — and its chain the related information's
///   messages, in order. Each located error is also an error mark over its
///   range, and each goal an empty-hole mark carrying its message. No goal card
///   is made: a goal's expected type reaches the report once goals carry
///   spelled types.
/// - provides: the projection from what an editor shows to what a render-bus
///   client paints.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a document with a refused declaration and a hole carries
///   one card at the refusal's bytes, an error mark there and a hole mark at
///   the hole; a fault at the origin is a card with no span.
/// - witness: `view::tests::a_report_cards_errors_and_marks_holes`
#[spec(ensures: |ret| ret.source == text.as_ref()
    && ret.diagnostics.len() == published.iter()
        .filter(|diagnostic| diagnostic.severity != Severity::INFORMATION).count()
    && ret.goals.is_empty())]
#[must_use]
pub fn report(
    text: SourceText<'_>,
    published: &[Diagnostic],
) -> ReportView
{
    let index = LineIndex::new(text.as_ref().into());
    let bytes = |range: Range| {
        if range == Range::default() {
            return None;
        }
        ByteRange::new(range.start.byte(&index), range.end.byte(&index)).ok()
    };
    let mut view = ReportView {
        source: String::from(text.as_ref()),
        highlights: highlight(text),
        ..ReportView::default()
    };
    for diagnostic in published {
        let span = bytes(diagnostic.range);
        if diagnostic.severity == Severity::INFORMATION {
            if let Some(range) = span {
                view.marks.push(MarkSpan {
                    range,
                    kind: MarkKind::EmptyHole,
                    message: diagnostic.message.clone(),
                });
            }
            continue;
        }
        let registered = diagnostic
            .code
            .as_deref()
            .and_then(|code| code.parse::<DiagnosticCode>().ok());
        let message = match (registered, diagnostic.code.as_deref()) {
            | (None, Some(identifier)) => alloc::format!("[{identifier}] {}", diagnostic.message),
            | (Some(_) | None, _) => diagnostic.message.clone(),
        };
        if diagnostic.severity == Severity::ERROR
            && let Some(range) = span
        {
            view.marks.push(MarkSpan {
                range,
                kind: MarkKind::Error,
                message: String::from(diagnostic.message.lines().next().unwrap_or_default()),
            });
        }
        view.diagnostics.push(DiagCard {
            code: registered.unwrap_or(DiagnosticCode::Other),
            message,
            span,
            expr: None,
            elaboration: None,
            chain: diagnostic
                .related_information
                .iter()
                .map(|related| related.message.clone())
                .collect::<Vec<_>>(),
        });
    }
    view
}

#[cfg(test)]
mod tests
{
    use gandr_surface_diagnostics::Verbosity;
    use gandr_surface_render_remote::ByteOffset;
    use gandr_surface_render_remote::ByteRange;
    use gandr_surface_render_remote::DiagnosticCode;
    use gandr_surface_render_remote::MarkKind;
    use gandr_surface_syntax::SourceText;

    use super::report;
    use crate::position::Character;
    use crate::position::Line;
    use crate::position::Position;
    use crate::position::Range;
    use crate::protocol::Diagnostic;
    use crate::protocol::DocumentUri;
    use crate::protocol::Severity;
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
        let text = "def g : Integer ;\ndef g = ?gap ;\ndef f : Integer ;\ndef f = \"one\" ;\n";
        let mut published = recheck(
            &uri,
            &mut open(&uri),
            SourceText::from(text),
            Verbosity::User,
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
        let view = report(SourceText::from(text), &published);
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
        let faulted = report(SourceText::from(text), &[Diagnostic::at_origin(
            String::from("the session faulted"),
        )]);
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
}
