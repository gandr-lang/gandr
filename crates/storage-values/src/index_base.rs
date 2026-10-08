//! The child-reference representation, and why this encoding answers the
//! question by construction.
//!
//! # The question
//!
//! A format whose child references are indices into a table must say what an
//! index counts from. **Absolute** indices count from the start of the whole
//! value, so inserting one constructor early renumbers every index after it:
//! every downstream chunk mentions a moved index, every one changes, and
//! sharing across two versions of a value collapses to the prefix before the
//! edit. **Chunk-local** indices count from the start of the chunk carrying
//! them, with the base carried at each seam, so an edit renumbers only within
//! its own chunk and the seams absorb the shift.
//!
//! # The answer here
//!
//! This token stream has no child indices. A constructor's children are
//! emitted nested, in place, between its open and close records; a cut
//! subtree is replaced by a child record naming its chunk's digest at offset
//! zero. There is no table and no numbering, so nothing an early insertion
//! could renumber: an edit rewrites the chunks on its own path to the root and
//! leaves every sibling chunk byte-identical, because no sibling's bytes ever
//! mentioned a position that moved.
//!
//! [`crate::cam_commit`] therefore refuses [`ChildIndexBase::ChunkLocal`]
//! rather than ignoring it — accepting it would let a manifest claim a
//! representation the chunks do not carry — and the measurement the question
//! asks for is [`crate::LocalityMeasurement`] taken over an early edit: the
//! chunks the edit added against the chunks it left shared.

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
