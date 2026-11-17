//! The edits a client sends to a held text: each content change applied in
//! order, and the caret that the last change leaves.

use anodized::spec;
use gandr_surface_render_remote::LineIndex;
use gandr_surface_syntax::ByteOffset;
use quenchant_shape::shape::Maybe;

use crate::protocol::ContentChange;

quenchant_shape::reason_enum! {
    /// Why a copy has no caret.
    pub mod uncareted {
        /// The reason the caret is unknown.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub enum Absent {
            /// The copy was opened, or its last change named no range: the
            /// whole text arrived at once, and nothing in it is being typed.
            Unranged,
        }
    }
}

/// `text` with `change` applied, and where the change left the caret.
///
/// # Specification
/// - requires: nothing; any range is admissible input.
/// - ensures: a change naming no range replaces the whole text and leaves no
///   caret; a ranged one replaces the bytes between its two ends, each resolved
///   through the line index of the text as it stands as
///   [`crate::position::Position::byte`] states, an end before the start read
///   as the start, and leaves the caret at the end of the text it inserted.
/// - provides: incremental synchronisation, with full synchronisation as the
///   change that names no range; the caret the quiet publication reads.
/// - fails: never.
/// - panics: none; a resolved end is always a character boundary.
///
/// # Adequacy
/// - hypothesis: L3 — successive ranged changes, one after a character beyond
///   the basic plane, an inverted range, and a rangeless change, each asserted
///   at the exact text it leaves and the caret it leaves.
/// - witness: `gandr-surface-lsp::server::tests::ranged_changes_edit_the_held_text_in_order`
#[spec(
    captures: [length = text.len(), replaced = change.text.len(), whole = change.range.is_none()],
    ensures: |ret| if whole { text.len() == replaced && matches!(ret, Maybe::Absent(_)) }
        else { replaced <= text.len() && text.len() <= length.saturating_add(replaced)
            && matches!(ret, Maybe::Present(caret) if usize::from(caret) <= text.len()) },
)]
#[inline]
pub fn apply(
    text: &mut String,
    change: ContentChange,
) -> Maybe<ByteOffset, uncareted::Absent>
{
    let Some(range) = change.range
    else {
        *text = change.text;
        return Maybe::Absent(uncareted::Absent::Unranged);
    };
    let index = LineIndex::new(text.as_str().into());
    let start = usize::from(range.start.byte(&index));
    let end = usize::from(range.end.byte(&index)).max(start);
    text.replace_range(start .. end, &change.text);
    Maybe::Present(ByteOffset::from(start.saturating_add(change.text.len())))
}

/// `text` with `change` applied, as [`apply`] states, the caret it leaves
/// unread.
///
/// # Specification
/// trivial.
#[inline]
pub fn edit_text(
    text: &mut String,
    change: ContentChange,
)
{
    let _caret = apply(text, change);
}
