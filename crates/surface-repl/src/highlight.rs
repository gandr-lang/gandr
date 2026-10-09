//! The echo's highlight spans: the grammar's role table over the submitted
//! buffer.

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
///   yields spans inside the buffer.
/// - witness: `highlight::tests::a_keyword_is_classified`
/// - witness: `highlight::tests::spans_are_sorted_and_disjoint`
/// - witness: `highlight::tests::an_unclassifiable_buffer_yields_no_panic`
/// - witness: `loop::tests::a_submission_carries_highlight_spans`
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
    /// trivial.
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
    /// trivial.
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
    /// disjoint, and there is more than one of them.
    #[test]
    fn spans_are_sorted_and_disjoint()
    {
        let (grammar, roles) = toolkit();
        let spans = highlight_source(
            &grammar,
            &roles,
            SourceText::from("def answer : Integer ;\ndef answer = 42 ;"),
        );
        assert!(spans.len() > 4, "every tile is classified: {spans:?}");
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
}
