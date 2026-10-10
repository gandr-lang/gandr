//! Hierarchical names: [`Segment`], [`NamePath`] and the dotted boundary.
//!
//! A path is the only thing the modifier language manipulates. It is
//! reachability, not identity: written by an author, inert, and never compared
//! against a minted identity.
//!
//! # Ordering is load-bearing
//!
//! [`NamePath`]'s [`Ord`] is the lexicographic order on its segments, so the
//! extensions of a path are order-convex: if `a < b < c` and both `a` and `c`
//! extend `p`, then `b` extends `p`. A trie walked in preorder over its
//! children in segment order therefore lists its bindings in path order.

use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use quenchant_shape::shape::Maybe;

quenchant_shape::reason_enum! {
    /// Why a path has no remainder after a candidate prefix.
    pub mod remainder {
        /// The candidate does not prefix the path.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// Some segment of the candidate differs, or the candidate is
            /// longer than the path.
            NotAPrefix,
        }
    }
}

/// One segment of a hierarchical name: `nat`, `plus` or `assoc` in
/// `nat.plus.assoc`.
///
/// A segment is opaque text. Nothing here interprets it, so a segment holding
/// the separator is representable and does not round-trip through
/// [`DottedName`].
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Segment(String);

impl From<&str> for Segment
{
    /// The segment spelled by `text`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(text: &str) -> Self
    {
        Self(String::from(text))
    }
}

impl From<String> for Segment
{
    /// The segment spelled by `text`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(text: String) -> Self
    {
        Self(text)
    }
}

impl AsRef<str> for Segment
{
    /// The segment's text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        self.0.as_str()
    }
}

impl fmt::Display for Segment
{
    /// Writes the segment's text, with no separator of its own.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(self.0.as_str())
    }
}

/// The dotted rendering of a hierarchical name at a text boundary: `nat.plus`,
/// with the empty string naming the root.
///
/// The root's spelling as a bare period belongs to a surface syntax this layer
/// does not have, so the boundary takes the empty string; [`NamePath`]'s
/// [`fmt::Display`] writes the root as `.` for diagnostics.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DottedName<'text>(&'text str);

impl<'text> From<&'text str> for DottedName<'text>
{
    /// The rendering `text`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(text: &'text str) -> Self
    {
        Self(text)
    }
}

impl AsRef<str> for DottedName<'_>
{
    /// The rendering's text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        self.0
    }
}

/// The number of segments in a hierarchical name.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SegmentCount(usize);

impl From<usize> for SegmentCount
{
    /// The count `count`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: usize) -> Self
    {
        Self(count)
    }
}

impl From<SegmentCount> for usize
{
    /// The number `count` holds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: SegmentCount) -> Self
    {
        count.0
    }
}

impl fmt::Display for SegmentCount
{
    /// Writes the count in decimal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        fmt::Display::fmt(&self.0, f)
    }
}

/// A hierarchical name: the ordered segments that reach a binding.
///
/// The empty path is the root, and it prefixes every path, which is why
/// renaming the root to `p` qualifies a namespace under `p` and renaming `p`
/// to the root unqualifies it.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct NamePath(Vec<Segment>);

impl NamePath
{
    /// The root path: no segments.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn root() -> Self
    {
        Self(Vec::new())
    }

    /// The path's segments, in order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn segments(&self) -> &[Segment]
    {
        self.0.as_slice()
    }

    /// The number of segments in this path.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the number of segments; the root has none.
    /// - provides: the depth a resolution reports a governing namespace at.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a two-segment path and the root, each asserted as the
    ///   exact count, separate segments from characters.
    /// - witness: `namespace::path::tests::depth_counts_segments`
    #[spec(
        ensures: |ret| ret.0 == self.0.len(),
    )]
    #[inline]
    #[must_use]
    pub fn depth(&self) -> SegmentCount
    {
        SegmentCount(self.0.len())
    }

    /// This path with `prefix` prepended.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the result's segments are `prefix`'s followed by this path's,
    ///   in that order; prepending the root is the identity.
    /// - provides: the path a binding acquires when its namespace is grafted
    ///   under `prefix`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — operand order is separated by the root prefix and by
    ///   a two-sided case asserted exactly both ways round.
    /// - witness: `namespace::path::tests::prefixing_by_root_is_the_identity`
    /// - witness: `namespace::path::tests::prefixing_prepends_in_order`
    #[spec(
        ensures: |ret| ret.0.iter().eq(prefix.0.iter().chain(&self.0)),
    )]
    #[inline]
    #[must_use]
    pub fn prefixed_by(
        &self,
        prefix: &Self,
    ) -> Self
    {
        let mut segments = Vec::with_capacity(prefix.0.len().saturating_add(self.0.len()));
        segments.extend_from_slice(prefix.0.as_slice());
        segments.extend_from_slice(self.0.as_slice());
        Self(segments)
    }

    /// This path with `suffix` appended.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: this path's segments followed by the suffix's, in order.
    /// - provides: the accumulated prefix a run under `in p` reports its events
    ///   at.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a shadow inside a nested modifier reports the full
    ///   accumulated path and still selects the correct binding. This observes
    ///   composition through the namespace consumer rather than another path
    ///   helper's implementation.
    /// - witness: `namespace::namespace::a_nested_shadow_reports_the_accumulated_prefix`
    #[spec(
        ensures: |ret| ret.0.iter().eq(self.0.iter().chain(&suffix.0)),
    )]
    #[inline]
    #[must_use]
    pub fn extended(
        &self,
        suffix: &Self,
    ) -> Self
    {
        suffix.prefixed_by(self)
    }

    /// The remainder of this path after `prefix`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: present with `suffix` exactly when
    ///   `suffix.prefixed_by(prefix)` equals this path; stripping the root
    ///   returns this path unchanged.
    /// - provides: the subtree-relative key of a binding.
    /// - fails: never; a non-prefix is an absence.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the prefix test is separated by the root, an exact
    ///   match, a proper prefix, a segment-wise near miss and a longer
    ///   candidate, each asserted as the exact answer.
    /// - witness: `namespace::path::tests::stripping_the_root_is_the_identity`
    /// - witness: `namespace::path::tests::stripping_an_exact_match_yields_the_root`
    /// - witness: `namespace::path::tests::stripping_a_proper_prefix_yields_the_remainder`
    /// - witness: `namespace::path::tests::a_near_miss_segment_is_not_a_prefix`
    #[spec(
        ensures: |ret| match ret {
            | Maybe::Present(ref suffix) => prefix.0.iter().chain(&suffix.0).eq(self.0.iter()),
            | Maybe::Absent(remainder::Absent::NotAPrefix) => !self.0.starts_with(&prefix.0),
        },
    )]
    #[inline]
    pub fn strip_prefix(
        &self,
        prefix: &Self,
    ) -> Maybe<Self, remainder::Absent>
    {
        match self.0.strip_prefix(prefix.0.as_slice()) {
            | Some(suffix) => Maybe::Present(Self(suffix.to_vec())),
            | None => Maybe::Absent(remainder::Absent::NotAPrefix),
        }
    }
}

impl From<DottedName<'_>> for NamePath
{
    /// The path `text` renders; the empty string is the root.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the empty rendering is the zero-segment root, not one empty
    ///   segment; any other rendering splits on the separator and nothing else,
    ///   in order.
    /// - provides: the text boundary paths are written at.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty, non-empty, Unicode and repeated/trailing
    ///   separator cases distinguish root, segment boundaries and preserved
    ///   empty segments. A raw segment containing a dot remains one segment.
    /// - witness: `namespace::path::tests::the_empty_dotted_rendering_is_the_root`
    /// - witness: `namespace::path::tests::segments_round_trip_through_the_dotted_boundary`
    /// - witness: `namespace::path::tests::dotted_paths_preserve_empty_and_unicode_segments`
    /// - witness: `namespace::path::tests::opaque_segments_stay_distinct_through_composition`
    #[spec(
        ensures: |ret| {
            if text.0.is_empty() {
                ret.0.is_empty()
            }
            else {
                ret.0.iter().map(Segment::as_ref).eq(text.0.split('.'))
            }
        },
    )]
    #[inline]
    fn from(text: DottedName<'_>) -> Self
    {
        if text.0.is_empty() {
            return Self::root();
        }
        Self(text.0.split('.').map(Segment::from).collect())
    }
}

impl From<Vec<Segment>> for NamePath
{
    /// The path of `segments`, in order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(segments: Vec<Segment>) -> Self
    {
        Self(segments)
    }
}

impl fmt::Display for NamePath
{
    /// Writes the root as `.` and any other path as its segments joined by
    /// `.`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the root renders as `.`; any other path as its segments in
    ///   order, separated by `.`.
    /// - provides: the path spelling of every rejection message.
    /// - fails: propagates the formatter's error.
    /// - panics: none.
    /// - executable: none — the formatter exposes neither its written output
    ///   nor a failure-status observer. Its return alone cannot certify the
    ///   emitted path; notation and writer failures are observed by witnesses.
    ///
    /// # Errors
    /// The formatter's error.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — root and multi-segment paths distinguish the two
    ///   notation branches. A writer refusing the separator observes error
    ///   propagation and that no later segment is written after refusal.
    /// - witness: `namespace::path::tests::the_root_renders_as_a_bare_period`
    /// - witness: `namespace::path::tests::a_path_renders_dot_joined`
    /// - witness: `namespace::path::tests::formatting_propagates_a_later_writer_refusal`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let Some((first, rest)) = self.0.split_first()
        else {
            return f.write_str(".");
        };
        f.write_str(first.as_ref())?;
        for segment in rest {
            f.write_str(".")?;
            f.write_str(segment.as_ref())?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests
{
    use alloc::format;
    use alloc::vec::Vec;

    use anodized::spec;
    use quenchant_shape::shape::Maybe;

    use super::DottedName;
    use super::NamePath;
    use super::Segment;
    use super::SegmentCount;
    use super::remainder;

    /// The path `text` renders.
    ///
    /// # Specification
    /// trivial.
    fn path<Text>(text: Text) -> NamePath
    where
        Text: Into<DottedName<'static>>,
    {
        NamePath::from(text.into())
    }

    /// Whether `candidate` extends `prefix`.
    ///
    /// # Specification
    /// trivial.
    fn extends(
        candidate: &NamePath,
        prefix: &NamePath,
    ) -> Extends
    {
        Extends(candidate.segments().starts_with(prefix.segments()))
    }

    /// Whether a path extends a prefix.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct Extends(bool);

    #[test]
    fn prefixing_by_root_is_the_identity()
    {
        let subject = path("nat.plus");
        assert_eq!(
            subject.prefixed_by(&NamePath::root()),
            subject,
            "the root prefixes every path without changing it"
        );
    }

    #[test]
    fn prefixing_prepends_in_order()
    {
        assert_eq!(
            path("plus.assoc").prefixed_by(&path("nat")),
            path("nat.plus.assoc"),
            "the prefix's segments precede the subject's"
        );
        assert_eq!(
            path("nat").prefixed_by(&path("plus.assoc")),
            path("plus.assoc.nat"),
            "the operands are not interchangeable"
        );
    }

    #[test]
    fn stripping_the_root_is_the_identity()
    {
        let subject = path("nat.plus");
        assert_eq!(
            subject.strip_prefix(&NamePath::root()),
            Maybe::Present(subject),
            "the root prefixes everything, so stripping it changes nothing"
        );
    }

    #[test]
    fn stripping_an_exact_match_yields_the_root()
    {
        assert_eq!(
            path("nat.plus").strip_prefix(&path("nat.plus")),
            Maybe::Present(NamePath::root()),
            "a path is its own prefix, with the root as remainder"
        );
    }

    #[test]
    fn stripping_a_proper_prefix_yields_the_remainder()
    {
        assert_eq!(
            path("nat.plus.assoc").strip_prefix(&path("nat")),
            Maybe::Present(path("plus.assoc")),
            "the remainder is the subtree-relative key"
        );
    }

    #[test]
    fn a_near_miss_segment_is_not_a_prefix()
    {
        assert_eq!(
            path("nat.plus").strip_prefix(&path("na")),
            Maybe::Absent(remainder::Absent::NotAPrefix),
            "prefixes are segment-wise, never character-wise"
        );
        assert_eq!(
            path("nat").strip_prefix(&path("nat.plus")),
            Maybe::Absent(remainder::Absent::NotAPrefix),
            "a longer candidate cannot prefix a shorter path"
        );
    }

    #[test]
    fn extensions_of_a_path_are_order_convex()
    {
        let mut sorted = Vec::from([
            path("zero"),
            path("nat.times.assoc"),
            path("natural"),
            path("nat"),
            path("nat.plus"),
        ]);
        sorted.sort();
        let prefix = path("nat");
        let flags: Vec<Extends> = sorted
            .iter()
            .map(|candidate| extends(candidate, &prefix))
            .collect();
        assert_eq!(
            flags,
            Vec::from([
                Extends(true),
                Extends(true),
                Extends(true),
                Extends(false),
                Extends(false)
            ]),
            "the extensions of `nat` occupy one contiguous run of the sorted keys"
        );
    }

    #[test]
    fn the_root_renders_as_a_bare_period()
    {
        assert_eq!(
            format!("{}", NamePath::root()),
            ".",
            "the root renders as a bare period in diagnostics"
        );
    }

    #[test]
    fn a_path_renders_dot_joined()
    {
        assert_eq!(
            format!("{}", path("nat.plus.assoc")),
            "nat.plus.assoc",
            "segments are joined by the separator"
        );
    }

    #[test]
    fn depth_counts_segments()
    {
        assert_eq!(
            path("nat.plus").depth(),
            SegmentCount::from(2_usize),
            "depth is the segment count, not the character count"
        );
        assert_eq!(
            NamePath::root().depth(),
            SegmentCount::from(0_usize),
            "the root has no segments"
        );
    }

    #[test]
    fn segments_round_trip_through_the_dotted_boundary()
    {
        assert_eq!(
            path("nat.plus").segments(),
            [Segment::from("nat"), Segment::from("plus")].as_slice(),
            "the dotted boundary splits on the separator and nothing else"
        );
    }

    #[test]
    fn the_empty_dotted_rendering_is_the_root()
    {
        assert_eq!(
            path(""),
            NamePath::root(),
            "the empty rendering must not split into one segment whose text is empty"
        );
        assert_eq!(
            path("").depth(),
            SegmentCount::from(0_usize),
            "the root carries no segments, which is what makes it prefix every path"
        );
    }

    #[test]
    fn dotted_paths_preserve_empty_and_unicode_segments()
    {
        let split = path(".α..β.");
        assert_eq!(split.segments(), [
            Segment::from(""),
            Segment::from("α"),
            Segment::from(""),
            Segment::from("β"),
            Segment::from(""),
        ]);
        assert_eq!(split.depth(), SegmentCount::from(5_usize));
        let period = path(".");
        assert_eq!(period.segments(), [Segment::from(""), Segment::from("")]);
        assert_ne!(period, NamePath::root());
    }

    #[test]
    fn opaque_segments_stay_distinct_through_composition()
    {
        let opaque = NamePath::from(Vec::from([Segment::from("a.b")]));
        let suffix = NamePath::from(Vec::from([Segment::from("")]));
        assert_eq!(opaque.depth(), SegmentCount::from(1_usize));
        assert_ne!(opaque, path("a.b"));
        let joined = opaque.extended(&suffix);
        assert_eq!(joined.segments(), [Segment::from("a.b"), Segment::from("")]);
        assert_eq!(joined.strip_prefix(&opaque), Maybe::Present(suffix));
        assert_eq!(
            joined.strip_prefix(&path("a")),
            Maybe::Absent(remainder::Absent::NotAPrefix)
        );
    }

    /// The next observable stage of a writer that refuses one separator.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum WriteStep
    {
        /// The first segment can be written.
        First,
        /// The separator is refused.
        Separator,
        /// Refusal has occurred; the formatter must stop.
        Refused,
        /// A write occurred after refusal and was accepted to expose it.
        Continued,
    }

    /// A real formatting sink whose second write fails, then accepts writes.
    #[derive(Debug)]
    #[repr(transparent)]
    struct SeparatorFailure
    {
        /// The next write's policy and evidence of any write after refusal.
        step: WriteStep,
    }

    impl core::fmt::Write for SeparatorFailure
    {
        /// Refuse the second write and record whether formatting continues.
        ///
        /// # Specification
        /// - requires: nothing.
        /// - ensures: only the separator-stage write fails; each call advances
        ///   the stage, and a call after refusal records Continued.
        /// - provides: an observer for swallowed errors and later writes.
        /// - fails: the separator stage returns the formatter error.
        /// - panics: none.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — formatting a two-segment path observes an
        ///   accepted first segment and a refused separator. The final stage
        ///   distinguishes immediate propagation from continued output; the
        ///   accepting continuation makes a swallowed error observable.
        /// - witness: `namespace::path::tests::formatting_propagates_a_later_writer_refusal`
        #[spec(
            captures: before = self.step,
            ensures: |ret| match before {
                | WriteStep::First => self.step == WriteStep::Separator && ret.is_ok(),
                | WriteStep::Separator => self.step == WriteStep::Refused && ret.is_err(),
                | WriteStep::Refused | WriteStep::Continued => {
                    self.step == WriteStep::Continued && ret.is_ok()
                },
            },
        )]
        fn write_str(
            &mut self,
            _text: &str,
        ) -> core::fmt::Result
        {
            match self.step {
                | WriteStep::First => {
                    self.step = WriteStep::Separator;
                    Ok(())
                },
                | WriteStep::Separator => {
                    self.step = WriteStep::Refused;
                    Err(core::fmt::Error)
                },
                | WriteStep::Refused | WriteStep::Continued => {
                    self.step = WriteStep::Continued;
                    Ok(())
                },
            }
        }
    }

    #[test]
    fn formatting_propagates_a_later_writer_refusal()
    {
        let mut writer = SeparatorFailure {
            step: WriteStep::First,
        };
        assert!(core::fmt::write(&mut writer, format_args!("{}", path("nat.plus"))).is_err());
        assert_eq!(writer.step, WriteStep::Refused);
    }
}
