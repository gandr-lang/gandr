//! The content key of a core node: the name of a node outside the arena of
//! one session.
//!
//! An arena id names a node by the order that one session mints it in. The
//! content key names the node by its canonical content. So two sessions that
//! judge the same text give each node the same key, in whatever order they
//! mint their nodes.
//!
//! # References
//!
//! - `vault:01a178aa-7772-7e72-a3d0-5855883d3db1` — anchor: § Decisions, item 2
//!   — an arena id is not canonical. So the name of a node outside its arena is
//!   the digest of its content.

use gandr_kernel_check_memo::ContentDigest;

/// The content key of a core node: the digest of its canonical content.
///
/// Two keys that differ name nodes of different content. Two keys that agree
/// name nodes of the same content, but for a collision of the digest's sixteen
/// bytes. The key is `Copy`, as an arena id is.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct NodeKey(ContentDigest);

impl From<ContentDigest> for NodeKey
{
    /// The key that `digest` is: the digest of a node's canonical content.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(digest: ContentDigest) -> Self
    {
        Self(digest)
    }
}

impl From<NodeKey> for ContentDigest
{
    /// The digest that `key` is.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(key: NodeKey) -> Self
    {
        key.0
    }
}
