//! The parse repairs of a chunk, projected onto the renderer seam's cards.
//!
//! The recovering parser repairs what it cannot read and records each repair
//! as an obligation. Until the recovery engine publishes its own vocabulary,
//! the renderer seam carries every repair as one [`DiagCard`] under
//! [`DiagnosticCode::ParseRepair`], its class spelled into the message.

use alloc::string::String;
use alloc::string::ToString as _;
use alloc::vec::Vec;

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
/// - hypothesis: L3 — two classes are asserted at their exact phrase in a
///   card's message.
/// - witness: `remote::tests::cards_preserve_the_report_rows`
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
/// - hypothesis: L3 — two repairs inside the chunk and one before it are
///   projected to exactly two cards, each class, message and shifted span
///   asserted; a clean parse projects to none, and an unclosed group to some.
/// - witness: `remote::tests::cards_preserve_the_report_rows`
/// - witness: `remote::tests::a_clean_source_produces_no_cards`
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
    /// trivial.
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
        let rows: Vec<_> = cards
            .iter()
            .map(|card| (card.code, card.message.as_str(), card.span))
            .collect();
        let range = |start: usize, end: usize| {
            ByteRange::new(ByteOffset::from(start), ByteOffset::from(end)).ok()
        };
        assert_eq!(rows, [
            (
                DiagnosticCode::ParseRepair,
                "parse repaired: a missing delimiter",
                range(2, 2)
            ),
            (
                DiagnosticCode::ParseRepair,
                "parse repaired: a token outside the grammar",
                range(4, 5)
            ),
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
}
