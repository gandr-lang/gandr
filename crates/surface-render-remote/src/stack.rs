//! The stack card: the context stack at the cursor of one document, one row
//! for each spine that encloses the cursor, the innermost first.
//!
//! A [`StackCard`] names the byte offset of the cursor that the editor asked
//! about last. A [`SpineRow`] holds the head as the text writes it, the type of
//! the head, the run of that type that the parameter of the cursor's slot
//! writes, the slot and the arity, and the type that the judgement checked the
//! slot's argument against. A field that the producer does not know is absent
//! and takes no bytes on the wire.
//!
//! The hub sends the whole card each time the stack at the cursor changes, and
//! nothing when it stays the same. A card is one per document and holds one row
//! for each spine, so an edit list would cost more than the rows it saves.

use alloc::string::String;
use alloc::vec::Vec;

use crate::present::ByteOffset;
use crate::present::ByteRange;
use crate::visual::Count;

/// One spine of a stack card.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct SpineRow
{
    /// The head, as the text writes it.
    pub head: String,
    /// The type of the head on one line: the parameters and the result of its
    /// declared head, or the type that the judgement gives the head when it
    /// has no declared head; absent when the producer knows neither.
    #[cfg_attr(
        feature = "serde",
        serde(rename = "type", default, skip_serializing_if = "Option::is_none")
    )]
    pub ty: Option<String>,
    /// The run of [`SpineRow::ty`] that the parameter of the cursor's slot
    /// writes; absent past the last parameter and with no declared head.
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub filled: Option<ByteRange>,
    /// The slot that the cursor fills, from zero.
    pub slot: Count,
    /// How many parameters the declared head takes; absent with no declared
    /// head.
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub arity: Option<Count>,
    /// The type that the judgement checked the argument of the slot against;
    /// absent when the slot writes no argument that the judgement typed.
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub expected: Option<String>,
}

/// The context stack at the cursor of one document.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct StackCard
{
    /// The byte offset of the cursor in the document's text.
    pub offset: ByteOffset,
    /// One row for each spine that encloses the cursor, the innermost first.
    pub rows: Vec<SpineRow>,
}
