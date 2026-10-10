//! The dense slot index both maintenance structures address their per-node
//! tables by.

use anodized::spec;
use gandr_theory_graphs::NodeId;

/// A dense vector position holding one node's per-node state.
///
/// Node identities and the table positions that hold their state are different
/// things, and conflating them is how an identifier from one structure comes to
/// index another's table. This wrapper keeps the conversion explicit and
/// fallible in the one direction that can fail.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SlotIndex(usize);

impl From<usize> for SlotIndex
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: usize) -> Self
    {
        return Self(value);
    }
}

impl From<SlotIndex> for usize
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: SlotIndex) -> Self
    {
        return value.0;
    }
}

impl TryFrom<NodeId> for SlotIndex
{
    type Error = core::num::TryFromIntError;

    /// Convert a dense identity to a checked host slot.
    ///
    /// # Specification
    /// - ensures: returns the same numeric index when the host can represent
    ///   it.
    /// - fails: returns `TryFromIntError` when the index exceeds `usize`.
    /// - panics: none.
    ///
    /// # Errors
    /// Propagates the standard checked integer conversion error.
    ///
    /// # Adequacy
    /// - hypothesis: L3 dense-node fixtures distinguish a shifted or lost slot
    ///   mapping; host-width failure is delegated to the standard conversion.
    /// - witness: `maintenance::tests::the_maintained_order_is_topological`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().map(|slot| slot.0) == usize::try_from(u32::from(value)).as_ref().copied())]
    fn try_from(value: NodeId) -> Result<Self, Self::Error>
    {
        return usize::try_from(u32::from(value)).map(Self);
    }
}
