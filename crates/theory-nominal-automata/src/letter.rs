//! The free-use, allocation, deallocation and immediate-release alphabet.

/// A lifecycle event over a caller-owned name.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Letter<A>
{
    /// Use a remembered name.
    Free(A),
    /// Allocate a name fresh for the current store.
    Open(A),
    /// Release a remembered name.
    Close(A),
    /// Allocate and release a fresh name without storing it.
    OpenClose(A),
}
impl<A: Copy> Letter<A>
{
    /// The event's name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn atom(&self) -> A
    {
        match *self {
            | Self::Free(atom) | Self::Open(atom) | Self::Close(atom) | Self::OpenClose(atom) => {
                atom
            },
        }
    }
}
