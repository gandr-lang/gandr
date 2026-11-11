//! The memo tally: how many goals the goal memo of each plane answered, and
//! how many it missed, over the runs of one checking context.
//!
//! # The context counts each consult under the `instrument` feature
//!
//! **Choice.** A [`CheckingContext`](crate::CheckingContext) holds one
//! [`MemoTally`] when the crate is built with its `instrument` feature. Each
//! run of the machine adds one to it where it consults its goal memo: a hit
//! when the memo answers the goal, a miss when the goal is keyed and the memo
//! holds no answer. A goal that the memo cannot key, or a run where the memo
//! is closed, is no consult. A build without the feature holds no field and
//! makes no add, so the driver and each recipe pay nothing. The counts layer
//! of the instrument reads the tally before and after each item it judges.
//!
//! **Alternatives.** A sink that each run takes as a type parameter costs the
//! same nothing in a build without the feature. It changes each entry of the
//! checker and each of their callers, and the hub then compiles the checker
//! once for each sink. A count that each run returns beside its answer
//! changes the same entries.
//!
//! **Reversal.** A second reader that needs the count on a path that the
//! context does not reach makes the site generic over the sink. The tally then
//! goes, and the column that the counts layer keeps does not change.
//!
//! # References
//!
//! - `engine-surface.md` § engine-surface-layers (vault reference
//!   `vault:01a1c68b-1e9e-7942-aa36-b8d9096dec0e`): the counts layer and what
//!   it costs when it is off.
//! - `core-kernel-reassessment.md` § kernel-reassessment-memo (vault reference
//!   `vault:01a178aa-6917-7983-b5cd-86e2af86b3ec`): the hits and the misses of
//!   a check memo, on each plane.

use anodized::spec;

/// How many consults of one kind the goal memo counted.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MemoCount(u64);

impl From<MemoCount> for u64
{
    /// The count as a number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: MemoCount) -> Self
    {
        count.0
    }
}

impl MemoCount
{
    /// One more, up to the representation's ceiling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    const fn successor(self) -> Self
    {
        Self(self.0.saturating_add(1))
    }

    /// This count less `earlier`, zero when `earlier` is the larger.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    const fn less(
        self,
        earlier: Self,
    ) -> Self
    {
        Self(self.0.saturating_sub(earlier.0))
    }

    /// This count and `other`, up to the representation's ceiling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    const fn plus(
        self,
        other: Self,
    ) -> Self
    {
        Self(self.0.saturating_add(other.0))
    }
}

/// The hits and the misses of the goal memo on each plane: the value
/// judgements, and the value type formations.
///
/// # Specification
/// - requires: nothing.
/// - ensures: each count holds the consults of its kind on its plane, up to the
///   representation's ceiling.
/// - provides: what the counts layer reads of the checker's memo for one item,
///   as the difference of two tallies.
/// - panics: none.
/// - executable: none — the counts are a projection of the runs' consults,
///   which the tally does not keep.
///
/// # Adequacy
/// - hypothesis: L3 — a shared pair consults its repeated goals, and the tally
///   counts a hit for each goal that the memo answers and a miss for each goal
///   that it keys first.
/// - witness: `judgement::memo::tests::the_tally_counts_a_hit_for_each_goal_met_again`
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct MemoTally
{
    /// The value judgements the memo answered.
    term_hits: MemoCount,
    /// The value judgements the memo keyed and held no answer for.
    term_misses: MemoCount,
    /// The value type formations the memo answered.
    type_hits: MemoCount,
    /// The value type formations the memo keyed and held no answer for.
    type_misses: MemoCount,
}

impl MemoTally
{
    /// The value judgements the memo answered.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn term_hits(&self) -> MemoCount
    {
        self.term_hits
    }

    /// The value judgements the memo keyed and held no answer for.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn term_misses(&self) -> MemoCount
    {
        self.term_misses
    }

    /// The value type formations the memo answered.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn type_hits(&self) -> MemoCount
    {
        self.type_hits
    }

    /// The value type formations the memo keyed and held no answer for.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn type_misses(&self) -> MemoCount
    {
        self.type_misses
    }

    /// The goals the memo answered on both planes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn hits(&self) -> MemoCount
    {
        self.term_hits.plus(self.type_hits)
    }

    /// The goals the memo keyed and held no answer for, on both planes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn misses(&self) -> MemoCount
    {
        self.term_misses.plus(self.type_misses)
    }

    /// The consults this tally counted after `earlier`, a tally of the same
    /// context read before it.
    ///
    /// # Specification
    /// - requires: `earlier` is a tally of the same context, read before this
    ///   one.
    /// - ensures: each count less the count of `earlier`, zero where `earlier`
    ///   holds more.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`MemoTally`].
    /// - witness: `judgement::memo::tests::the_tally_counts_a_hit_for_each_goal_met_again`
    #[spec(ensures: |ret| u64::from(ret.term_hits) == u64::from(self.term_hits).saturating_sub(u64::from(earlier.term_hits))
        && u64::from(ret.term_misses) == u64::from(self.term_misses).saturating_sub(u64::from(earlier.term_misses))
        && u64::from(ret.type_hits) == u64::from(self.type_hits).saturating_sub(u64::from(earlier.type_hits))
        && u64::from(ret.type_misses) == u64::from(self.type_misses).saturating_sub(u64::from(earlier.type_misses)))]
    #[inline]
    #[must_use]
    pub fn since(
        self,
        earlier: Self,
    ) -> Self
    {
        Self {
            term_hits: self.term_hits.less(earlier.term_hits),
            term_misses: self.term_misses.less(earlier.term_misses),
            type_hits: self.type_hits.less(earlier.type_hits),
            type_misses: self.type_misses.less(earlier.type_misses),
        }
    }

    /// Count one value judgement the memo answered.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn term_hit(&mut self)
    {
        self.term_hits = self.term_hits.successor();
    }

    /// Count one value judgement the memo keyed and held no answer for.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn term_miss(&mut self)
    {
        self.term_misses = self.term_misses.successor();
    }

    /// Count one value type formation the memo answered.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn type_hit(&mut self)
    {
        self.type_hits = self.type_hits.successor();
    }

    /// Count one value type formation the memo keyed and held no answer for.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn type_miss(&mut self)
    {
        self.type_misses = self.type_misses.successor();
    }
}
