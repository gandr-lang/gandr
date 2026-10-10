//! Semantic tokens: the highlighter's spans re-encoded as the protocol's
//! integer stream.
//!
//! The spans are the grammar's own classification, the [`HlRole`] a terminal
//! face styles too; this module maps each role onto the protocol's standard
//! token types and performs the delta encoding: five integers per token — the
//! line delta, the start delta, the length, the legend index of its type and
//! its modifier bits — with a span crossing lines split into one token per
//! line, its terminators dropped. Lengths and columns count UTF-16 code units,
//! read through the renderer seam's [`LineIndex`].

use gandr_surface_render_remote::ByteOffset;
use gandr_surface_render_remote::HlRole;
use gandr_surface_render_remote::HlSpan;
use gandr_surface_render_remote::LineIndex;
use gandr_surface_render_remote::PositionRow;
use gandr_surface_render_remote::Utf16Pos;
use quenchant_shape::shape::Maybe;
use serde::Serialize;

/// The advertised token types, in the order a token's type integer indexes.
pub const TOKEN_TYPES: [&str; 14] = [
    "keyword",
    "operator",
    "function",
    "variable",
    "parameter",
    "property",
    "enumMember",
    "type",
    "typeParameter",
    "number",
    "string",
    "comment",
    "macro",
    "label",
];

/// The advertised token modifiers, in the order a token's modifier bits
/// index.
pub const TOKEN_MODIFIERS: [&str; 2] = ["declaration", "defaultLibrary"];

/// The integers one token occupies in the stream.
const INTEGERS_PER_TOKEN: usize = 5;

quenchant_shape::reason_enum! {
    /// Why a role emits no token.
    mod token_of_role {
        /// The reason a role is not sent.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The highlighter classified the bytes as nothing in particular.
            Unclassified,
        }
    }
}

/// The legend index of a token type.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct TokenType(u32);

/// A token's modifier bits, over [`TOKEN_MODIFIERS`].
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct TokenModifiers(u32);

impl TokenModifiers
{
    /// The token declares its name.
    const DECLARATION: Self = Self(1);
    /// The token names something the language provides.
    const DEFAULT_LIBRARY: Self = Self(2);
    /// No modifier.
    const NONE: Self = Self(0);
}

/// The protocol's token stream: five integers per token.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize)]
#[serde(transparent)]
pub struct TokenStream(Vec<u32>);

impl From<Vec<u32>> for TokenStream
{
    /// Read the integers as a stream.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(integers: Vec<u32>) -> Self
    {
        Self(integers)
    }
}

impl AsRef<[u32]> for TokenStream
{
    /// The stream's integers.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u32]
    {
        &self.0
    }
}

/// The token type and modifiers `role` is sent as.
///
/// # Specification
/// - requires: nothing.
/// - ensures: every index lies inside [`TOKEN_TYPES`] and names the standard
///   type the role means, and every bit set names a modifier of
///   [`TOKEN_MODIFIERS`]: a definition's name declares it, a built-in type is
///   of the default library.
/// - provides: the one map from the grammar's roles onto the legend.
/// - fails: never; [`HlRole::Other`] is the
///   [`token_of_role::Absent::Unclassified`] absence.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — all 23 roles, including absence, are checked against
///   independent type and modifier names, distinguishing legend permutations,
///   wrong classifications and lost declaration or built-in bits.
/// - witness: `tokens::tests::every_classified_role_maps_inside_the_legend`
/// - witness: `tokens::tests::the_legend_index_a_role_emits_names_what_that_role_means`
#[anodized::spec(ensures: |ret| match ret {
    Maybe::Present((kind, modifiers)) => role != HlRole::Other
        && usize::try_from(kind.0).is_ok_and(|index| index < TOKEN_TYPES.len())
        && modifiers.0 & !3_u32 == 0,
    Maybe::Absent(_) => role == HlRole::Other,
})]
fn token_of_role(role: HlRole) -> Maybe<(TokenType, TokenModifiers), token_of_role::Absent>
{
    let plain = |index: u32| Maybe::Present((TokenType(index), TokenModifiers::NONE));
    match role {
        | HlRole::Keyword | HlRole::Boolean => plain(0),
        | HlRole::Operator => plain(1),
        | HlRole::FunctionDef => Maybe::Present((TokenType(2), TokenModifiers::DECLARATION)),
        | HlRole::FunctionCall => plain(2),
        | HlRole::VariableDef => Maybe::Present((TokenType(3), TokenModifiers::DECLARATION)),
        | HlRole::Variable => plain(3),
        | HlRole::VariableParam => plain(4),
        | HlRole::Member => plain(5),
        | HlRole::Constructor => plain(6),
        | HlRole::Type => plain(7),
        | HlRole::TypeBuiltin => Maybe::Present((TokenType(7), TokenModifiers::DEFAULT_LIBRARY)),
        | HlRole::TypeVariable => plain(8),
        | HlRole::Number => plain(9),
        | HlRole::StringLit | HlRole::Character | HlRole::Escape | HlRole::Path => plain(10),
        | HlRole::Comment => plain(11),
        | HlRole::Hole | HlRole::Directive => plain(12),
        | HlRole::Label => plain(13),
        | HlRole::Other => Maybe::Absent(token_of_role::Absent::Unclassified),
    }
}

/// The token stream of `spans` over the text `index` was built from.
///
/// # Specification
/// - requires: `spans` are sorted and pairwise disjoint, each on character
///   boundaries of the text, as the highlighter yields them.
/// - ensures: one token per line each classified span touches, in span order,
///   covering the span's bytes on that line with the line's terminator
///   excluded; columns and lengths count UTF-16 code units; each token's line
///   and start are deltas from the token before it, the first from the
///   document's origin. A span of [`HlRole::Other`], and a piece of a span
///   holding only a terminator, sends nothing.
/// - provides: the `data` of a semantic-tokens result.
/// - fails: never; a span offset inside a character, which the requirement
///   excludes, sends nothing rather than a token at a guessed column.
/// - panics: none.
/// - intension: one projection per span end and per line piece, each a binary
///   search over the index's line starts and a walk of one line.
///
/// # Adequacy
/// - hypothesis: L3 — a one-line keyword and a span over two lines are each
///   asserted at their exact integers; L2 — over every corpus source, the
///   decoded stream covers exactly the highlighter's classified bytes, line by
///   line.
/// - witness: `tokens::tests::a_one_line_keyword_encodes_as_five_integers`
/// - witness: `tokens::tests::a_multiline_span_splits_and_drops_the_terminator`
/// - witness: `session::session::corpus_tokens_cover_the_highlighted_bytes`
#[anodized::spec(ensures: |ret| ret.0.len().is_multiple_of(INTEGERS_PER_TOKEN)
    && ret.0.chunks_exact(INTEGERS_PER_TOKEN).all(|token|
        matches!(token, &[_, _, length, kind, bits] if length > 0
            && usize::try_from(kind).is_ok_and(|index| index < TOKEN_TYPES.len())
            && bits & !3_u32 == 0))
    && (!spans.iter().all(|span| span.role == HlRole::Other) || ret.0.is_empty()))]
#[inline]
#[must_use]
pub fn encode(
    index: &LineIndex<'_>,
    spans: &[HlSpan],
) -> TokenStream
{
    let wire = |count: usize| u32::try_from(count).unwrap_or(u32::MAX);
    let mut data = Vec::with_capacity(spans.len().saturating_mul(INTEGERS_PER_TOKEN));
    let mut previous = Utf16Pos::default();
    for span in spans {
        let Maybe::Present((kind, modifiers)) = token_of_role(span.role)
        else {
            continue;
        };
        let (Ok(first), Ok(last)) = (
            index.utf16_pos_of_byte(span.range.start()),
            index.utf16_pos_of_byte(span.range.end()),
        )
        else {
            continue;
        };
        for row in usize::from(first.row) ..= usize::from(last.row) {
            let line = index.row_bytes(PositionRow::from(row));
            let start = span.range.start().max(line.start());
            let end = span.range.end().min(line.end());
            if start >= end {
                continue;
            }
            let (Ok(from), Ok(to)) = (index.utf16_pos_of_byte(start), index.utf16_pos_of_byte(end))
            else {
                continue;
            };
            let column = usize::from(from.col);
            let line_delta = row.saturating_sub(usize::from(previous.row));
            let start_delta = if line_delta == 0 {
                column.saturating_sub(usize::from(previous.col))
            }
            else {
                column
            };
            let length = usize::from(to.col).saturating_sub(column);
            data.extend([
                wire(line_delta),
                wire(start_delta),
                wire(length),
                kind.0,
                modifiers.0,
            ]);
            previous = from;
        }
    }
    TokenStream(data)
}

/// The spans of `spans` overlapping the bytes from `start` up to `end`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: each span whose bytes share at least one with the half-open
///   range, kept whole rather than clipped to it, in order; an empty or an
///   inverted range keeps none.
/// - provides: the spans a range request encodes, so its stream's deltas still
///   run from the document's origin.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — all ordered spans and all query endpoint pairs in 0..=4
///   are compared with byte-set intersection, including empty spans, empty and
///   inverted queries, touching edges and unsorted input. Exact retained spans
///   distinguish boundary inclusions, clipping and reordering; directed wire
///   cases retain document-relative token deltas.
/// - witness: `tokens::tests::overlap_observes_half_open_bytes_including_empty_spans`
/// - witness: `server::tests::a_range_returns_only_the_tokens_it_covers`
/// - witness: `server::tests::a_range_over_the_whole_document_agrees_with_the_full_stream`
/// - witness: `server::tests::a_token_straddling_the_range_edge_is_returned_whole`
/// - witness: `server::tests::an_inverted_range_yields_no_tokens`
/// - witness: `server::tests::an_empty_range_yields_no_tokens`
#[anodized::spec(
    captures: count = spans.iter().filter(|span| start < end
        && span.range.start() < span.range.end()
        && span.range.start() < end && start < span.range.end()).count(),
    ensures: |ret| ret.len() == count && ret.iter().all(|span|
        span.range.start().max(start) < span.range.end().min(end)),
)]
#[inline]
#[must_use]
pub fn overlapping(
    spans: Vec<HlSpan>,
    start: ByteOffset,
    end: ByteOffset,
) -> Vec<HlSpan>
{
    if end <= start {
        return Vec::new();
    }
    spans
        .into_iter()
        .filter(|span| span.range.start().max(start) < span.range.end().min(end))
        .collect()
}

#[cfg(test)]
mod tests
{
    use gandr_surface_render_remote::ByteOffset;
    use gandr_surface_render_remote::ByteRange;
    use gandr_surface_render_remote::HlRole;
    use gandr_surface_render_remote::HlSpan;
    use gandr_surface_render_remote::LineIndex;
    use gandr_surface_render_remote::SourceText;
    use quenchant_shape::shape::Maybe;

    use super::TOKEN_MODIFIERS;
    use super::TOKEN_TYPES;
    use super::TokenModifiers;
    use super::TokenStream;
    use super::encode;
    use super::token_of_role;

    /// Every role the highlighter classifies; [`HlRole::Other`] is not one.
    const CLASSIFIED: [HlRole; 22] = [
        HlRole::Keyword,
        HlRole::Operator,
        HlRole::FunctionDef,
        HlRole::FunctionCall,
        HlRole::VariableDef,
        HlRole::VariableParam,
        HlRole::Member,
        HlRole::Variable,
        HlRole::Constructor,
        HlRole::Type,
        HlRole::TypeBuiltin,
        HlRole::TypeVariable,
        HlRole::Number,
        HlRole::Boolean,
        HlRole::Character,
        HlRole::StringLit,
        HlRole::Escape,
        HlRole::Comment,
        HlRole::Hole,
        HlRole::Label,
        HlRole::Path,
        HlRole::Directive,
    ];

    /// The standard token type a role means, and the modifiers it sets.
    struct Meaning
    {
        /// The token type's name in the legend.
        name: &'static str,
        /// The modifier names, in bit order.
        modifiers: &'static [&'static str],
    }

    /// The modifier names a bit set selects, in bit order.
    #[repr(transparent)]
    struct Names(Vec<&'static str>);

    /// A start and an end offset, written as two counts.
    struct Bytes(usize, usize);

    /// The standard token type and modifiers each role means, stated apart
    /// from both [`TOKEN_TYPES`]'s order and [`token_of_role()`]'s indices: a
    /// client observes the pair of an index and the name the legend gives it,
    /// and neither side states that pair alone. The match is exhaustive, so a
    /// new role does not compile here until its meaning is stated.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: every classified role has its standard type and modifier
    ///   names; only Other has no meaning.
    /// - provides: a name-based oracle independent of wire indices.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — all classified roles and Other distinguish absent,
    ///   swapped or wrongly modified meanings by the independently encoded
    ///   stream's interpretation under the advertised legend.
    /// - witness: `tokens::tests::the_legend_index_a_role_emits_names_what_that_role_means`
    #[anodized::spec(ensures: |ret| match ret {
        Maybe::Present(ref meaning) => role != HlRole::Other && !meaning.name.is_empty()
            && meaning.modifiers.iter().all(|&name| matches!(name, "declaration" | "defaultLibrary")),
        Maybe::Absent(()) => role == HlRole::Other,
    })]
    fn meaning(role: HlRole) -> Maybe<Meaning, ()>
    {
        const DECLARED: &[&str] = &["declaration"];
        const BUILT_IN: &[&str] = &["defaultLibrary"];
        const PLAIN: &[&str] = &[];
        let means = |name, modifiers| Maybe::Present(Meaning { name, modifiers });
        match role {
            | HlRole::Keyword | HlRole::Boolean => means("keyword", PLAIN),
            | HlRole::Operator => means("operator", PLAIN),
            | HlRole::FunctionDef => means("function", DECLARED),
            | HlRole::FunctionCall => means("function", PLAIN),
            | HlRole::VariableDef => means("variable", DECLARED),
            | HlRole::Variable => means("variable", PLAIN),
            | HlRole::VariableParam => means("parameter", PLAIN),
            | HlRole::Member => means("property", PLAIN),
            | HlRole::Constructor => means("enumMember", PLAIN),
            | HlRole::Type => means("type", PLAIN),
            | HlRole::TypeBuiltin => means("type", BUILT_IN),
            | HlRole::TypeVariable => means("typeParameter", PLAIN),
            | HlRole::Number => means("number", PLAIN),
            | HlRole::StringLit | HlRole::Character | HlRole::Escape | HlRole::Path => {
                means("string", PLAIN)
            },
            | HlRole::Comment => means("comment", PLAIN),
            | HlRole::Hole | HlRole::Directive => means("macro", PLAIN),
            | HlRole::Label => means("label", PLAIN),
            | HlRole::Other => Maybe::Absent(()),
        }
    }

    /// The modifier names `modifiers` selects, in bit order.
    ///
    /// # Specification
    /// - requires: nothing; high bits are ignored.
    /// - ensures: the selected low-bit modifier names appear in legend order.
    /// - provides: the client's interpretation of modifier bits.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — all four low-bit combinations, also with a high bit
    ///   set, distinguish wrong bit selection and order through exact names.
    /// - witness: `tokens::tests::modifier_bits_and_skipped_spans_keep_their_meaning`
    #[anodized::spec(ensures: |ret| ret.0.iter().copied().eq(
        TOKEN_MODIFIERS.into_iter().zip([1_u32, 2_u32])
            .filter_map(|(name, bit)| (modifiers.0 & bit != 0).then_some(name))))]
    fn modifier_names(modifiers: TokenModifiers) -> Names
    {
        Names(
            TOKEN_MODIFIERS
                .iter()
                .zip([1_u32, 2_u32])
                .filter(|&(_, bit)| modifiers.0 & bit == bit)
                .map(|(&name, _)| name)
                .collect(),
        )
    }

    /// A span of `role` over the bytes a [`Bytes`] pair spells.
    ///
    /// # Specification
    /// - requires: start is no greater than end.
    /// - ensures: both offsets and the role are retained exactly.
    /// - provides: an ordered span for semantic-token witnesses.
    /// - fails: never in the valid domain.
    /// - panics: an inverted range violates the requirement.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — all ordered endpoints in 0..=4, including empty
    ///   spans, distinguish endpoint shifts through byte-set intersection.
    /// - witness: `tokens::tests::overlap_observes_half_open_bytes_including_empty_spans`
    #[anodized::spec(requires: start <= end, ensures: |ret|
        ret.range.start() == ByteOffset::from(start)
            && ret.range.end() == ByteOffset::from(end) && ret.role == role)]
    fn span(
        Bytes(start, end): Bytes,
        role: HlRole,
    ) -> HlSpan
    {
        HlSpan {
            range: ByteRange::new(ByteOffset::from(start), ByteOffset::from(end))
                .expect("an ordered range"),
            role,
        }
    }

    #[test]
    fn every_classified_role_maps_inside_the_legend()
    {
        for role in CLASSIFIED {
            let Maybe::Present((kind, modifiers)) = token_of_role(role)
            else {
                panic!("{role:?} is classified, so it maps");
            };
            assert!(
                usize::try_from(kind.0).is_ok_and(|index| index < TOKEN_TYPES.len()),
                "{role:?} emits index {}, outside the legend",
                kind.0
            );
            assert_eq!(
                modifiers.0 & !3_u32,
                0_u32,
                "{role:?} sets a bit past the modifier legend"
            );
        }
        assert!(
            matches!(token_of_role(HlRole::Other), Maybe::Absent(_)),
            "an unclassified span sends nothing"
        );
    }

    /// Swapping two entries of [`TOKEN_TYPES`] leaves the bounds check above
    /// green while every token of either kind paints as the other; this test
    /// reads each emitted index back through the legend, so it goes red under
    /// exactly that permutation.
    #[test]
    fn the_legend_index_a_role_emits_names_what_that_role_means()
    {
        for role in CLASSIFIED {
            let (Maybe::Present(Meaning { name, modifiers }), Maybe::Present((kind, bits))) =
                (meaning(role), token_of_role(role))
            else {
                panic!("{role:?} is classified, so it has a meaning and a token");
            };
            let index = usize::try_from(kind.0).expect("a legend index fits usize");
            assert_eq!(
                TOKEN_TYPES.get(index).copied(),
                Some(name),
                "{role:?} emits index {index}, which must name {name}"
            );
            assert_eq!(
                modifier_names(bits).0,
                modifiers.to_vec(),
                "{role:?} sets the modifiers it means"
            );
        }
        assert!(
            matches!(meaning(HlRole::Other), Maybe::Absent(())),
            "an unclassified span means nothing"
        );
    }

    #[test]
    fn a_one_line_keyword_encodes_as_five_integers()
    {
        let index = LineIndex::new(SourceText::from("def x"));
        assert_eq!(
            encode(&index, &[span(Bytes(0, 3), HlRole::Keyword)]),
            TokenStream::from(vec![0, 0, 3, 0, 0]),
            "line 0, column 0, three units, a keyword, no modifier"
        );
    }

    #[test]
    fn a_multiline_span_splits_and_drops_the_terminator()
    {
        let index = LineIndex::new(SourceText::from("ab\r\ncd"));
        assert_eq!(
            encode(&index, &[span(Bytes(0, 6), HlRole::Comment)]),
            TokenStream::from(vec![0, 0, 2, 11, 0, 1, 0, 2, 11, 0]),
            "one comment token per line, the terminator in neither"
        );
        let astral = LineIndex::new(SourceText::from("𝄞\n𝄞"));
        assert_eq!(
            encode(&astral, &[span(Bytes(0, 9), HlRole::StringLit)]),
            TokenStream::from(vec![0, 0, 2, 10, 0, 1, 0, 2, 10, 0]),
            "each piece's length counts UTF-16 units"
        );
    }
    #[test]
    fn overlap_observes_half_open_bytes_including_empty_spans()
    {
        let mut spans = Vec::new();
        for start in (0_usize ..= 4).rev() {
            for end in start ..= 4 {
                spans.push(span(Bytes(start, end), HlRole::Keyword));
            }
        }
        for start in 0_usize ..= 4 {
            for end in 0_usize ..= 4 {
                let expected: Vec<_> = spans
                    .iter()
                    .copied()
                    .filter(|candidate| {
                        (0_usize .. 4).any(|byte| {
                            usize::from(candidate.range.start()) <= byte
                                && byte < usize::from(candidate.range.end())
                                && start <= byte
                                && byte < end
                        })
                    })
                    .collect();
                assert_eq!(
                    super::overlapping(
                        spans.clone(),
                        ByteOffset::from(start),
                        ByteOffset::from(end)
                    ),
                    expected,
                    "range {start}..{end}",
                );
            }
        }
    }
    #[test]
    fn modifier_bits_and_skipped_spans_keep_their_meaning()
    {
        for (bits, expected) in [
            (0_u32, Vec::new()),
            (1, vec!["declaration"]),
            (2, vec!["defaultLibrary"]),
            (3, vec!["declaration", "defaultLibrary"]),
        ] {
            assert_eq!(modifier_names(TokenModifiers(bits)).0, expected);
            assert_eq!(
                modifier_names(TokenModifiers(bits | 0x8000_0000)).0,
                expected
            );
        }
        let index = LineIndex::new(SourceText::from("a\r\n\rb"));
        assert_eq!(encode(&index, &[]), TokenStream::default());
        assert_eq!(
            encode(&index, &[
                span(Bytes(0, 1), HlRole::Other),
                span(Bytes(1, 3), HlRole::Comment),
                span(Bytes(3, 4), HlRole::Comment),
                span(Bytes(4, 5), HlRole::VariableDef),
            ]),
            TokenStream::from(vec![2, 0, 1, 3, 1])
        );
    }
}
