//! The connections that one workspace serves, each named by its number.

use core::fmt;

/// One connection among those a workspace serves.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Peer(u64);

impl From<u64> for Peer
{
    /// The connection numbered `number`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(number: u64) -> Self
    {
        Self(number)
    }
}

impl fmt::Display for Peer
{
    /// Writes the connection's number, as a progress token names it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "{}", self.0)
    }
}

impl Peer
{
    /// The peer of the face beside the hub's socket. The hub numbers its
    /// connections from one, so no connection takes it.
    pub const BESIDE: Self = Self(0);
}
