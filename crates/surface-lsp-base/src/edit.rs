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
/// - witness: `edit::tests::ranged_changes_edit_the_text_in_order`
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

#[cfg(test)]
mod tests
{
    use gandr_surface_syntax::ByteOffset;
    use quenchant_shape::shape::Maybe;

    use super::apply;
    use super::uncareted;
    use crate::protocol::ContentChange;

    #[test]
    fn ranged_changes_edit_the_text_in_order()
    {
        let changes: Vec<ContentChange> = serde_json::from_str(include_str!(
            "edit/unformatted/ranged-changes-edit-the-text-in-order.gandr"
        ))
        .expect("the changes decode");
        let mut text = String::from("def f = 42 ;\n");
        let carets: Vec<_> = changes
            .into_iter()
            .map(|change| apply(&mut text, change))
            .collect();
        assert_eq!(
            text, "def f = 7 !;\ndef g = \"𝄞x\" ;\n",
            "each change applies to the text the ones before it left, counted in UTF-16 units, \
             an inverted range inserting at its start"
        );
        assert_eq!(
            carets.last(),
            Some(&Maybe::Present(ByteOffset::from(11_usize))),
            "the caret is where the last change's text ends: after its `!`"
        );
        let whole: ContentChange =
            serde_json::from_str(r#"{"text":"def f = 42 ;\n"}"#).expect("the change decodes");
        assert_eq!(
            apply(&mut text, whole),
            Maybe::Absent(uncareted::Absent::Unranged),
            "a rangeless change leaves no caret"
        );
        assert_eq!(
            text, "def f = 42 ;\n",
            "a rangeless change replaces the whole text"
        );
    }
}
