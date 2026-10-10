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
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Errors
    /// Propagates the formatter's write failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on both variants observes distinct names and exact
    ///   refusal from a sink that accepts no text. It distinguishes collapsed
    ///   variants and swallowed errors without pinning diagnostic wording or
    ///   claiming that every alternate formatter mode was exercised.
    /// - witness: `index_base::tests::bases_remain_distinct_and_propagate_refusal`
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

#[cfg(test)]
mod tests
{
    use alloc::string::ToString as _;

    use super::ChildIndexBase;

    /// A formatting sink that refuses every write.
    #[derive(Debug)]
    struct RefusingSink;

    impl core::fmt::Write for RefusingSink
    {
        /// Refuses any offered text.
        ///
        /// # Specification
        /// - requires: nothing.
        /// - ensures: returns the formatting error.
        /// - provides: the index-base formatter's refusal observer.
        /// - fails: always returns the formatting error.
        /// - panics: none.
        ///
        /// # Errors
        /// Always returns the formatting error.
        ///
        /// # Adequacy
        /// - hypothesis: L3 on both index-base renderings observes exact write
        ///   refusal, distinguishing a sink that silently accepts text.
        /// - witness: `index_base::tests::bases_remain_distinct_and_propagate_refusal`
        #[anodized::spec(ensures: |ret| ret == Err(core::fmt::Error))]
        fn write_str(
            &mut self,
            _s: &str,
        ) -> core::fmt::Result
        {
            Err(core::fmt::Error)
        }
    }

    #[test]
    fn bases_remain_distinct_and_propagate_refusal()
    {
        assert_ne!(
            ChildIndexBase::Absolute.to_string(),
            ChildIndexBase::ChunkLocal.to_string()
        );
        for base in [ChildIndexBase::Absolute, ChildIndexBase::ChunkLocal] {
            assert_eq!(
                core::fmt::write(&mut RefusingSink, format_args!("{base}")),
                Err(core::fmt::Error),
            );
        }
    }
}
