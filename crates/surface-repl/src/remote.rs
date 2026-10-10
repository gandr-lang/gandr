//! The parse repairs of a chunk, projected onto the renderer seam's cards.
//!
//! The recovering parser repairs what it cannot read and records each repair
//! as an obligation. Until the recovery engine publishes its own vocabulary,
//! the renderer seam carries every repair as one [`DiagCard`] under
//! [`DiagnosticCode::ParseRepair`], its class spelled into the message.

use alloc::string::String;
use alloc::string::ToString as _;
use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_parser::Oblig;
use gandr_surface_parser::ObligationInstance;
use gandr_surface_render_remote::ByteOffset;
use gandr_surface_render_remote::ByteRange;
use gandr_surface_render_remote::DiagCard;
use gandr_surface_render_remote::DiagnosticCode;
use gandr_surface_render_remote::DiagnosticMessage;
use gandr_surface_syntax::ByteOffset as SourceOffset;

/// How a repair of `class` reads in a card's message.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one phrase per class, naming what the parser found in plain
///   words; distinct classes read distinctly.
/// - provides: the `{class}` argument of the repair message.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — eight repair classes remain distinguishable in their
///   messages; chunk boundaries and shifted repair loci are exact.
/// - witness: `remote::tests::cards_preserve_the_report_rows`
/// - witness: `remote::tests::repair_boundaries_preserve_locations_and_distinct_classes`
#[spec(ensures: |ret| !ret.is_empty() && ret.trim() == ret
    && !ret.contains(['\r', '\n']))]
fn class_phrase(class: Oblig) -> String
{
    String::from(match class {
        | Oblig::MissingMeld => "a missing term",
        | Oblig::MissingTile => "a missing delimiter",
        | Oblig::IncompleteTile => "a partially typed keyword",
        | Oblig::UnmoldedTok => "a token outside the grammar",
        | Oblig::InconMeld => "a term of the wrong sort",
        | Oblig::ExtraMeld => "two terms where one was expected",
        | Oblig::ReservedKeyword => "a reserved keyword used as a name",
        | Oblig::AmbiguousPrec => "operators of incomparable precedence",
    })
}

/// The renderer seam's cards for the repairs `obligations` records in the text
/// from `chunk` on.
///
/// # Specification
/// - requires: `obligations` and `chunk` are measured against the same
///   revision, and the text from `chunk` to the revision's end is the newly
///   submitted chunk.
/// - ensures: one card per obligation starting at or after `chunk`, in the
///   order the parser recorded them, each under [`DiagnosticCode::ParseRepair`]
///   with the repair message naming its class; the card's span is the
///   obligation's, measured from `chunk`, so it addresses the echoed chunk. An
///   obligation before `chunk` belongs to text the loop already accepted and
///   has no card.
/// - provides: the repair rows of a transcript block.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — repairs at, after and across the chunk boundary retain
///   exactly their selected codes and shifted spans; all eight classes stay
///   distinguishable. A clean parse has no cards and an unclosed group has
///   repairs.
/// - witness: `remote::tests::cards_preserve_the_report_rows`
/// - witness: `remote::tests::a_clean_source_produces_no_cards`
/// - witness: `remote::tests::repair_boundaries_preserve_locations_and_distinct_classes`
#[spec(ensures: |ret| {
    let mut expected = obligations.iter().filter(|obligation| chunk <= obligation.span.start());
    ret.iter().all(|card| expected.next().is_some_and(|obligation|
        card.code == DiagnosticCode::ParseRepair && card.expr.is_none()
            && card.elaboration.is_none() && card.chain.is_empty()
            && card.span.is_some_and(|span|
                usize::from(span.start()) == usize::from(obligation.span.start()).saturating_sub(usize::from(chunk))
                    && usize::from(span.end()) == usize::from(obligation.span.end()).saturating_sub(usize::from(chunk)))))
        && expected.next().is_none()
})]
#[inline]
#[must_use]
pub fn repair_cards(
    obligations: &[ObligationInstance],
    chunk: SourceOffset,
) -> Vec<DiagCard>
{
    let base = usize::from(chunk);
    obligations
        .iter()
        .filter(|obligation| chunk <= obligation.span.start())
        .map(|obligation| {
            let start = usize::from(obligation.span.start()).saturating_sub(base);
            let end = usize::from(obligation.span.end()).saturating_sub(base);
            let span = match ByteRange::new(ByteOffset::from(start), ByteOffset::from(end)) {
                | Ok(range) => Some(range),
                | Err(_) => None,
            };
            DiagCard {
                code: DiagnosticCode::ParseRepair,
                message: DiagnosticMessage::ParseRepair {
                    class: class_phrase(obligation.class),
                }
                .to_string(),
                span,
                expr: None,
                elaboration: None,
                chain: Vec::new(),
            }
        })
        .collect()
}

#[cfg(test)]
mod tests
{
    use anodized::spec;
    use gandr_surface_grammar::built_in;
    use gandr_surface_parser::Oblig;
    use gandr_surface_parser::ObligationInstance;
    use gandr_surface_parser::parse;
    use gandr_surface_render_remote::ByteOffset;
    use gandr_surface_render_remote::ByteRange;
    use gandr_surface_render_remote::DiagnosticCode;
    use gandr_surface_syntax::ByteSpan;
    use gandr_surface_syntax::SourceText;

    use super::repair_cards;

    /// A start and an end offset, written as two counts.
    struct Bytes(usize, usize);

    /// The revision span a [`Bytes`] pair spells.
    ///
    /// # Specification
    /// - requires: `start <= end`.
    /// - ensures: the exact revision-relative byte endpoints.
    /// - provides: the span oracle for chunk-relative repair cards.
    /// - fails: never.
    /// - panics: if the endpoints are inverted.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nonzero starts and an empty repair locus distinguish
    ///   incorrect subtraction and dropped zero-width spans.
    /// - witness: `remote::tests::cards_preserve_the_report_rows`
    #[spec(requires: start <= end, ensures: |ret|
        usize::from(ret.start()) == start && usize::from(ret.end()) == end)]
    fn span(Bytes(start, end): Bytes) -> ByteSpan
    {
        ByteSpan::new(start.into(), end.into()).expect("the test span is ordered")
    }

    /// Each repair inside the chunk becomes one card: its code, its class in
    /// the message and its span measured from the chunk's start; a repair
    /// before the chunk has none.
    #[test]
    fn cards_preserve_the_report_rows()
    {
        let obligations = [
            ObligationInstance {
                class: Oblig::UnmoldedTok,
                span: span(Bytes(2, 3)),
            },
            ObligationInstance {
                class: Oblig::MissingTile,
                span: span(Bytes(10, 10)),
            },
            ObligationInstance {
                class: Oblig::UnmoldedTok,
                span: span(Bytes(12, 13)),
            },
        ];
        let cards = repair_cards(&obligations, 8.into());
        let rows: Vec<_> = cards.iter().map(|card| (card.code, card.span)).collect();
        let range = |start: usize, end: usize| {
            ByteRange::new(ByteOffset::from(start), ByteOffset::from(end)).ok()
        };
        assert_eq!(rows, [
            (DiagnosticCode::ParseRepair, range(2, 2)),
            (DiagnosticCode::ParseRepair, range(4, 5)),
        ]);
        assert!(
            cards
                .iter()
                .all(|card| card.chain.is_empty() && card.expr.is_none())
        );
    }

    /// A source the parser reads without a repair projects to no card.
    #[test]
    fn a_clean_source_produces_no_cards()
    {
        let grammar = built_in().expect("the built-in grammar builds");
        let text = "def answer : Integer ;\ndef answer = 42 ;";
        let parsed = parse(&grammar, SourceText::from(text)).expect("the parser commits a tree");
        assert!(
            parsed.obligations().is_empty(),
            "the corpus shape parses clean"
        );
        assert!(repair_cards(parsed.obligations(), 0.into()).is_empty());
        let broken = "def answer = ( ;";
        let parsed = parse(&grammar, SourceText::from(broken)).expect("the parser commits a tree");
        assert!(
            !repair_cards(parsed.obligations(), 0.into()).is_empty(),
            "an unclosed group is repaired, so the empty answer above is not vacuous"
        );
    }

    /// A repair crossing from accepted text is omitted, a zero-width repair
    /// at the chunk boundary is kept, and eight repair classes stay distinct.
    #[test]
    fn repair_boundaries_preserve_locations_and_distinct_classes()
    {
        let mut obligations = vec![ObligationInstance {
            class: Oblig::MissingTile,
            span: span(Bytes(0, 4)),
        }];
        let classes = [
            Oblig::MissingMeld,
            Oblig::MissingTile,
            Oblig::IncompleteTile,
            Oblig::UnmoldedTok,
            Oblig::InconMeld,
            Oblig::ExtraMeld,
            Oblig::ReservedKeyword,
            Oblig::AmbiguousPrec,
        ];
        obligations.extend(classes.into_iter().enumerate().map(|(index, class)| {
            let start = index.saturating_add(2);
            ObligationInstance {
                class,
                span: span(Bytes(start, start.saturating_add(usize::from(index != 0)))),
            }
        }));
        let cards = repair_cards(&obligations, 2.into());
        let expected: Vec<_> = (0_usize .. 8)
            .map(|start| {
                ByteRange::new(
                    start.into(),
                    start.saturating_add(usize::from(start != 0)).into(),
                )
                .ok()
            })
            .collect();
        assert_eq!(
            cards.iter().map(|card| card.span).collect::<Vec<_>>(),
            expected
        );
        let mut messages = alloc::collections::BTreeSet::new();
        for card in cards {
            assert_eq!(card.code, DiagnosticCode::ParseRepair);
            assert!(
                messages.insert(card.message),
                "different repair classes must remain distinguishable"
            );
        }
    }
}
