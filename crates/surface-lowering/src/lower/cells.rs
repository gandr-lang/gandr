//! The lowering of a `cells` node, a composite or a filler written over named
//! cells. The pasting reading reads the cells' types into the shape the former
//! is checked at. Until that reading lands, the lowering refuses the node by
//! one refusal, classed under the reading's tracking issue.
//!
//! # Witnesses
//! - `lower::cells::tests::a_cells_node_is_refused_for_the_pasting_reading`

use anodized::spec;
use gandr_surface_syntax::Cells;

use crate::error::LoweringRefusal;

/// The refusal a `cells` node lowers to until the pasting reading lands.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`LoweringRefusal::UnreadCells`] at the node's span, naming the
///   node's former.
/// - provides: the one diagnostic a `cells` node reports.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the refusal carries the node's span and former, and its
///   class names the pasting reading's tracking issue.
/// - witness: `lower::cells::tests::a_cells_node_is_refused_for_the_pasting_reading`
#[spec(
    ensures: |ret| matches!(
        ret,
        LoweringRefusal::UnreadCells { span, kind } if span == cells.span() && kind == cells.kind()
    ),
)]
#[inline]
#[must_use]
pub fn refuse_cells<'source>(cells: &Cells) -> LoweringRefusal<'source>
{
    LoweringRefusal::UnreadCells {
        span: cells.span(),
        kind: cells.kind(),
    }
}

#[cfg(test)]
mod tests
{
    use alloc::vec;

    use gandr_core_term::TrackingIssue;
    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::Cells;
    use gandr_surface_syntax::CellsKind;
    use gandr_surface_syntax::NamedCell;
    use gandr_surface_syntax::NodeIndex;

    use super::refuse_cells;
    use crate::classify::FailureClass;
    use crate::error::LoweringRefusal;
    use crate::fixture::span;

    #[test]
    fn a_cells_node_is_refused_for_the_pasting_reading()
    {
        let at = span(ByteOffset::from(4_usize), ByteOffset::from(19_usize));
        let node = Cells::new(at, CellsKind::Fill, Some(NodeIndex::from(2_usize)), vec![
            NamedCell::bound(NodeIndex::from(3_usize)),
            NamedCell::given(NodeIndex::from(4_usize), NodeIndex::from(5_usize)),
        ]);
        let refusal = refuse_cells(&node);

        assert_eq!(
            refusal,
            LoweringRefusal::UnreadCells {
                span: at,
                kind: CellsKind::Fill,
            },
            "the refusal sits on the node and names its former"
        );
        assert_eq!(
            refusal.classify(),
            FailureClass::Unimplemented(TrackingIssue::PASTING_READING),
            "the refusal names the issue the pasting reading lands under"
        );
    }
}
