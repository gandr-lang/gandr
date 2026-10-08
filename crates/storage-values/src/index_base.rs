//! Child references name a chunk by digest and an offset within that chunk.
//!
//! # Child representation
//!
//! Constructors nest in place. A cut subtree becomes a child record naming
//! its chunk at offset zero, so an insertion cannot renumber sibling
//! references through a shared index table. See the
//! [byte languages](https://github.com/gandr-lang/gandr/blob/main/crates/storage-values/README.md#byte-languages).
//!
//! [`crate::cam_commit`] accepts [`ChildIndexBase::Absolute`] and refuses
//! [`ChildIndexBase::ChunkLocal`], because the encoding carries no relative
//! index base.

use core::fmt;

/// How a child reference names its target inside a chunk body.
///
/// The base is bound into [`crate::ValueProfile`], so two deployments that
/// disagree hold different profiles and refuse each other rather than
/// silently producing different addresses for the same value.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ChildIndexBase
{
    /// A child reference names a whole chunk by digest, at an offset counted
    /// from that chunk's own start: what this encoding writes.
    Absolute,
    /// A child reference is an index relative to the chunk carrying it, with
    /// the base carried at each seam: not representable in this encoding.
    ChunkLocal,
}

impl fmt::Display for ChildIndexBase
{
    /// Writes the representation's name.
    ///
    /// # Specification
    /// - requires: nothing; every variant renders.
    /// - ensures: writes `absolute` or `chunk-local`.
    /// - provides: the name an unsupported-base refusal carries.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            | Self::Absolute => "absolute",
            | Self::ChunkLocal => "chunk-local",
        })
    }
}
