//! The echo's highlight spans: the grammar's role table over the submitted
//! buffer.

use anodized::spec;
use gandr_surface_grammar::Pbg;
use gandr_surface_grammar::RoleTable;
use gandr_surface_parser::parse;
use gandr_surface_render_remote::HlSpan;
use gandr_surface_syntax::SourceText;

/// How a list of highlight spans is ordered.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum SpanOrder
{
    /// Each span ends at or before the next one starts.
    SortedAndDisjoint,
    /// Some span starts before its predecessor ends.
    Overlapping,
}

/// How `spans` are ordered.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`SpanOrder::SortedAndDisjoint`] exactly when every span ends at
///   or before its successor starts; the empty list and a single span are
///   sorted and disjoint.
/// - provides: the order every face's painter assumes when it walks the echo
///   once, left to right.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an overlapping pair, a pair out of order, and a shared
///   boundary each answer exactly; the highlighter's output answers sorted.
/// - witness: `highlight::tests::the_disjointness_predicate_rejects_an_overlap`
/// - witness: `highlight::tests::spans_are_sorted_and_disjoint`
#[spec(ensures: |ret| (ret == SpanOrder::SortedAndDisjoint)
    == spans.iter().zip(spans.iter().skip(1)).all(|(a, b)| a.range.end() <= b.range.start()))]
#[inline]
#[must_use]
pub fn span_order(spans: &[HlSpan]) -> SpanOrder
{
    let ordered = spans
        .windows(2)
        .all(|pair| matches!(pair, [earlier, later] if earlier.range.end() <= later.range.start()));
    if ordered {
        SpanOrder::SortedAndDisjoint
    }
    else {
        SpanOrder::Overlapping
    }
}

/// The highlight spans over `buffer`, as `roles` classifies its parse under
/// `grammar`.
///
/// # Specification
/// - requires: `roles` was built from `grammar`.
/// - ensures: one span per tile and per comment of `buffer`'s parse tree, each
///   classified by its role, sorted and pairwise disjoint; none when the parser
///   could not commit a tree, when the role table refused the tree, or when the
///   spans it gave were not sorted and disjoint. Each of those is a fault the
///   submission's own diagnostics name, or a highlighter defect, and the echo
///   reads plain rather than mispainted.
/// - provides: the spans a transcript block echoes its source with.
/// - fails: never.
/// - panics: none.
/// - intension: one parse of `buffer`.
///
/// # Adequacy
/// - hypothesis: L3 — a definition's `def` is classified as a keyword; spans
///   over a declaration are sorted and disjoint; text the grammar cannot read
///   yields spans inside the buffer; Unicode string bytes retain their role
///   without splitting scalar values.
/// - witness: `highlight::tests::a_keyword_is_classified`
/// - witness: `highlight::tests::spans_are_sorted_and_disjoint`
/// - witness: `highlight::tests::an_unclassifiable_buffer_yields_no_panic`
/// - witness: `loop::tests::a_submission_carries_highlight_spans`
/// - witness: `highlight::tests::unicode_literals_keep_their_byte_boundaries`
#[spec(ensures: |ret| ret.iter().zip(ret.iter().skip(1))
    .all(|(left, right)| left.range.end() <= right.range.start())
    && ret.iter().all(|span| <&str>::from(buffer).is_char_boundary(usize::from(span.range.start()))
        && <&str>::from(buffer).is_char_boundary(usize::from(span.range.end()))))]
#[inline]
#[must_use]
pub fn highlight_source(
    grammar: &Pbg,
    roles: &RoleTable,
    buffer: SourceText<'_>,
) -> Vec<HlSpan>
{
    let Ok(parsed) = parse(grammar, buffer)
    else {
        return Vec::new();
    };
    let Ok(spans) = roles.highlight(&parsed.into_tree())
    else {
        return Vec::new();
    };
    match span_order(&spans) {
        | SpanOrder::SortedAndDisjoint => spans,
        | SpanOrder::Overlapping => Vec::new(),
    }
}

#[cfg(test)]
mod tests
{
    use anodized::spec;
    use gandr_surface_grammar::Pbg;
    use gandr_surface_grammar::RoleTable;
    use gandr_surface_grammar::built_in;
    use gandr_surface_render_remote::ByteOffset;
    use gandr_surface_render_remote::ByteRange;
    use gandr_surface_render_remote::HlRole;
    use gandr_surface_render_remote::HlSpan;
    use gandr_surface_syntax::SourceText;

    use super::SpanOrder;
    use super::highlight_source;
    use super::span_order;

    /// The built-in grammar and its role table.
    ///
    /// # Specification
    /// - requires: the built-in grammar and its role table are valid.
    /// - ensures: a nonempty grammar and a role for every mold it defines.
    /// - provides: the grammar and role pair used by the highlighting
    ///   witnesses.
    /// - fails: never.
    /// - panics: if either fixture construction fails.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exact keyword classification observes the pair
    ///   together; the predicate checks that no mold lacks its role entry.
    /// - witness: `highlight::tests::a_keyword_is_classified`
    #[spec(ensures: |ret| !ret.0.rules().is_empty()
        && ret.0.iter_molds().all(|(mold, _)| ret.1.role_of(mold).is_ok()))]
    fn toolkit() -> (Pbg, RoleTable)
    {
        let grammar = built_in().expect("the built-in grammar builds");
        let roles = RoleTable::build(&grammar).expect("the built-in role table builds");
        (grammar, roles)
    }

    /// A start and an end offset, written as two counts.
    struct Bytes(usize, usize);

    /// A span of `role` over the bytes a [`Bytes`] pair spells.
    ///
    /// # Specification
    /// - requires: `start <= end`.
    /// - ensures: the exact byte endpoints and role.
    /// - provides: an explicit span oracle.
    /// - fails: never.
    /// - panics: if the endpoints are inverted.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exact keyword and ordered, overlapping or inverted
    ///   pairs distinguish changed endpoints and classifications.
    /// - witness: `highlight::tests::a_keyword_is_classified`
    /// - witness: `highlight::tests::the_disjointness_predicate_rejects_an_overlap`
    #[spec(requires: start <= end, ensures: |ret|
        usize::from(ret.range.start()) == start && usize::from(ret.range.end()) == end && ret.role == role)]
    fn span(
        Bytes(start, end): Bytes,
        role: HlRole,
    ) -> HlSpan
    {
        HlSpan {
            range: ByteRange::new(ByteOffset::from(start), ByteOffset::from(end))
                .expect("the test range is ordered"),
            role,
        }
    }

    /// The `def` opening a definition is classified as a keyword, at exactly
    /// its three bytes.
    #[test]
    fn a_keyword_is_classified()
    {
        let (grammar, roles) = toolkit();
        let spans = highlight_source(&grammar, &roles, SourceText::from("def one = 1 ;"));
        assert!(
            spans.contains(&span(Bytes(0, 3), HlRole::Keyword)),
            "`def` is a keyword span over 0..3: {spans:?}"
        );
    }

    /// The spans over a declaration with several tiles are sorted and pairwise
    /// disjoint.
    #[test]
    fn spans_are_sorted_and_disjoint()
    {
        let (grammar, roles) = toolkit();
        let spans = highlight_source(
            &grammar,
            &roles,
            SourceText::from("def answer : Integer ;\ndef answer = 42 ;"),
        );

        assert_eq!(span_order(&spans), SpanOrder::SortedAndDisjoint);
    }

    /// The predicate rejects an overlap and an inversion, and accepts two spans
    /// that share only a boundary.
    #[test]
    fn the_disjointness_predicate_rejects_an_overlap()
    {
        let overlapping = [
            span(Bytes(0, 3), HlRole::Keyword),
            span(Bytes(2, 5), HlRole::Variable),
        ];
        assert_eq!(span_order(&overlapping), SpanOrder::Overlapping);
        let inverted = [
            span(Bytes(4, 6), HlRole::Keyword),
            span(Bytes(0, 3), HlRole::Variable),
        ];
        assert_eq!(span_order(&inverted), SpanOrder::Overlapping);
        let adjacent = [
            span(Bytes(0, 3), HlRole::Keyword),
            span(Bytes(3, 5), HlRole::Variable),
        ];
        assert_eq!(span_order(&adjacent), SpanOrder::SortedAndDisjoint);
        assert_eq!(span_order(&[]), SpanOrder::SortedAndDisjoint);
    }

    /// Text the grammar cannot read still yields spans that are sorted,
    /// disjoint and inside the buffer.
    #[test]
    fn an_unclassifiable_buffer_yields_no_panic()
    {
        let (grammar, roles) = toolkit();
        let buffer = "@@@ !! nonsense";
        let spans = highlight_source(&grammar, &roles, SourceText::from(buffer));
        assert_eq!(span_order(&spans), SpanOrder::SortedAndDisjoint);
        assert!(
            spans
                .iter()
                .all(|each| usize::from(each.range.end()) <= buffer.len()),
            "every span lies inside the buffer: {spans:?}"
        );
    }

    /// UTF-8 byte offsets never split a multibyte string literal or its scalar
    /// values.
    #[test]
    fn unicode_literals_keep_their_byte_boundaries()
    {
        let (grammar, roles) = toolkit();
        let text = "def f = \"é𐍈\" ;\r\n";
        let spans = highlight_source(&grammar, &roles, SourceText::from(text));
        let string_bytes: Vec<_> = spans
            .iter()
            .filter(|span| span.role == HlRole::StringLit)
            .flat_map(|span| usize::from(span.range.start()) .. usize::from(span.range.end()))
            .collect();
        assert_eq!(string_bytes, (8_usize .. 16).collect::<Vec<_>>());
        assert!(spans.iter().all(
            |span| text.is_char_boundary(usize::from(span.range.start()))
                && text.is_char_boundary(usize::from(span.range.end()))
        ));
        assert_eq!(span_order(&spans), SpanOrder::SortedAndDisjoint);
    }
}
