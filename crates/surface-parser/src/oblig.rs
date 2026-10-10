//! The obligation taxonomy and the `Delta` minimization order.
//!
//! The taxonomy descends from tylr's `structure/Oblig.re` with gandr's
//! `AmbiguousPrec` addition. The Rust enum is declared in **severity order** so
//! `derive(Ord)` is the truth: tylr orders severity via its `all` list rather
//! than its variant declaration order, and gandr fixes the order at the type
//! level.

use core::cmp::Ordering;

use anodized::spec;
use gandr_surface_syntax::ByteSpan;

/// The number of obligation severity classes.
pub const OBLIG_CLASS_COUNT: usize = 8;

/// Dense index into the fixed obligation severity ladder.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ObligClassIndex(usize);

impl From<ObligClassIndex> for usize
{
    /// Read the index back as a host position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: ObligClassIndex) -> Self
    {
        index.0
    }
}

impl From<ObligClassIndex> for u8
{
    /// Narrow the index to a byte; every class index fits in one.
    ///
    /// # Specification
    /// - ensures: the byte is exactly the dense severity index.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — all eight severity classes retain their exact rank
    ///   through the host and wire observers; shifted or truncated ranks
    ///   differ.
    /// - witness: `oblig::tests::index_matches_ord_rank`
    #[inline]
    #[spec(ensures: |ret| usize::from(ret) == index.0)]
    fn from(index: ObligClassIndex) -> Self
    {
        Self::try_from(usize::from(index)).unwrap_or(0)
    }
}

/// Count of obligations in one severity class.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
pub struct ObligationCount(u32);

impl ObligationCount
{
    /// No obligations.
    pub const ZERO: Self = Self(0);
    /// One obligation.
    pub const ONE: Self = Self(1);
}

impl From<u32> for ObligationCount
{
    /// Adopt a raw count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: u32) -> Self
    {
        Self(count)
    }
}

impl From<ObligationCount> for u32
{
    /// Read the raw count back.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: ObligationCount) -> Self
    {
        count.0
    }
}

impl From<ObligationCount> for usize
{
    /// Widen the count to a host count, saturating on a narrower host.
    ///
    /// # Specification
    /// - ensures: the host count equals the wire count when representable,
    ///   otherwise it saturates at the host maximum.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero, one and the wire ceiling distinguish exact
    ///   conversion from shifted counts and wrapping at a narrower host
    ///   boundary.
    /// - witness: `oblig::tests::counts_convert_at_zero_and_the_wire_ceiling`
    #[inline]
    #[spec(ensures: |ret| ret == Self::try_from(count.0).unwrap_or(Self::MAX))]
    fn from(count: ObligationCount) -> Self
    {
        Self::try_from(u32::from(count)).unwrap_or(Self::MAX)
    }
}

/// Whether a delta records no obligation changes.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct DeltaEmptyStatus(bool);

impl From<bool> for DeltaEmptyStatus
{
    /// Wrap the emptiness answer.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(is_empty: bool) -> Self
    {
        Self(is_empty)
    }
}

impl From<DeltaEmptyStatus> for bool
{
    /// Read the emptiness answer back.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(is_empty: DeltaEmptyStatus) -> Self
    {
        is_empty.0
    }
}

/// A syntactic obligation class, ordered low severity to high.
///
/// The variant order **is** the severity order: `derive(Ord)` compares by
/// discriminant, so [`MissingMeld`](Oblig::MissingMeld) is the least severe and
/// [`AmbiguousPrec`](Oblig::AmbiguousPrec) — gandr's addition — is the most
/// severe. `Delta` minimization folds the per-class counts from
/// [`AmbiguousPrec`](Oblig::AmbiguousPrec) down, so a repair introducing an
/// ambiguity is chosen only when no alternative exists.
///
/// # Specification
/// - requires: none.
/// - ensures: `derive(Ord)` ranks the classes exactly `MissingMeld <
///   MissingTile < IncompleteTile < UnmoldedTok < InconMeld < ExtraMeld <
///   ReservedKeyword < AmbiguousPrec`.
/// - provides: the closed obligation vocabulary the melder buffers and the
///   query surface exposes.
/// - fails: never.
/// - panics: none.
/// - executable: none — this type has no call boundary; the class, recording
///   and comparison operations carry its executable obligations.
///
/// # Adequacy
/// - hypothesis: L3 — the pinned severity ladder distinguishes every adjacent
///   pair, and the `AmbiguousPrec`-at-maximum property is observed directly.
/// - witness: `oblig::tests::severity_ladder_is_low_to_high`
/// - witness: `oblig::tests::ambiguous_prec_is_maximally_severe`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Oblig
{
    /// Convex grout: no term where one was expected.
    MissingMeld,
    /// Ghost tile: an absent delimiter.
    MissingTile,
    /// Partially typed keyword.
    IncompleteTile,
    /// Token not in the grammar.
    UnmoldedTok,
    /// Pre/postfix grout: a term of the wrong sort.
    InconMeld,
    /// Infix grout: two terms where one was expected.
    ExtraMeld,
    /// A reserved keyword used as an ordinary name.
    ReservedKeyword,
    /// gandr's addition: precedence-incomparable operators, at maximum
    /// severity.
    AmbiguousPrec,
}

impl Oblig
{
    /// Return this class's dense severity index (`0..OBLIG_CLASS_COUNT`).
    ///
    /// # Specification
    /// - requires: none.
    /// - ensures: returns the discriminant, equal to the class's rank under
    ///   `Ord`, in `0..OBLIG_CLASS_COUNT`.
    /// - provides: the array index for [`Delta`]'s per-class counts.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every variant maps to a distinct index matching its
    ///   `Ord` rank.
    /// - witness: `oblig::tests::index_matches_ord_rank`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.0 == match self { Self::MissingMeld => 0, Self::MissingTile => 1, Self::IncompleteTile => 2, Self::UnmoldedTok => 3, Self::InconMeld => 4, Self::ExtraMeld => 5, Self::ReservedKeyword => 6, Self::AmbiguousPrec => 7 })]
    pub const fn index(self) -> ObligClassIndex
    {
        ObligClassIndex(match self {
            | Self::MissingMeld => 0,
            | Self::MissingTile => 1,
            | Self::IncompleteTile => 2,
            | Self::UnmoldedTok => 3,
            | Self::InconMeld => 4,
            | Self::ExtraMeld => 5,
            | Self::ReservedKeyword => 6,
            | Self::AmbiguousPrec => 7,
        })
    }

    /// Return every obligation class in ascending severity order.
    ///
    /// # Specification
    /// - requires: none.
    /// - ensures: returns all [`OBLIG_CLASS_COUNT`] classes in `Ord` order.
    /// - provides: the deterministic class enumeration for folds and tests.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every class is pinned in the eight-row severity
    ///   table; adjacent comparisons and exact enumeration distinguish
    ///   reordered, duplicated or omitted classes.
    /// - witness: `oblig::tests::severity_ladder_is_low_to_high`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| matches!(ret, [Self::MissingMeld, Self::MissingTile, Self::IncompleteTile, Self::UnmoldedTok, Self::InconMeld, Self::ExtraMeld, Self::ReservedKeyword, Self::AmbiguousPrec]))]
    pub const fn all() -> [Self; OBLIG_CLASS_COUNT]
    {
        [
            Self::MissingMeld,
            Self::MissingTile,
            Self::IncompleteTile,
            Self::UnmoldedTok,
            Self::InconMeld,
            Self::ExtraMeld,
            Self::ReservedKeyword,
            Self::AmbiguousPrec,
        ]
    }
}

/// One buffered obligation: a class and the source span responsible for it.
///
/// # Specification
/// - requires: `span` is a monotone source range in the melder's assembled
///   source buffer.
/// - ensures: preserves the class and span exactly.
/// - provides: the per-instance obligation datum accumulated during a parse and
///   surfaced by the query API; the span is the smallest responsible region so
///   consumers can render statement-local diagnostics.
/// - fails: never.
/// - panics: none.
/// - executable: none — this type has no call boundary; the class, recording
///   and comparison operations carry its executable obligations.
///
/// # Adequacy
/// - hypothesis: L3 — one instance observes exact class and span preservation.
/// - witness: `meld::tests::degrout_flags_one_ambiguous_prec_at_the_smallest_span`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct ObligationInstance
{
    /// The obligation class.
    pub class: Oblig,
    /// The smallest source span responsible for the obligation.
    pub span: ByteSpan,
}

impl ObligationInstance
{
    /// Construct an obligation instance from its class and responsible span.
    ///
    /// # Specification
    /// - requires: `span` is a monotone source range.
    /// - ensures: preserves `class` and `span` exactly.
    /// - provides: the melder's obligation constructor.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a conflicting pair of operators emits the exact class
    ///   and smallest responsible span; changing either constructor field
    ///   alters this consumer-visible diagnostic.
    /// - witness: `meld::tests::degrout_flags_one_ambiguous_prec_at_the_smallest_span`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.class.index().0 == class.index().0)]
    pub const fn new(
        class: Oblig,
        span: ByteSpan,
    ) -> Self
    {
        Self { class, span }
    }
}

/// A per-class obligation `(removed, inserted)` count.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct ClassCount
{
    /// Obligations of this class removed by a candidate repair.
    removed: ObligationCount,
    /// Obligations of this class inserted by a candidate repair.
    inserted: ObligationCount,
}

/// Net obligation change (`inserted - removed`) for one severity class.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ObligationNet(i64);

impl From<ClassCount> for ObligationNet
{
    /// Take a class's net change: inserted minus removed.
    ///
    /// # Specification
    /// - ensures: the signed net is inserted minus removed, without overflow
    ///   for any pair of 32-bit counts.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — removal-only, insertion-only and cancelling counts at
    ///   the wire ceiling distinguish sign reversal, narrowing and lost removal
    ///   through the delta ordering observed by candidate minimization.
    /// - witness: `oblig::tests::net_precedes_gross_and_is_signed`
    #[inline]
    #[spec(ensures: |ret| ret.0 == i64::from(count.inserted.0).saturating_sub(i64::from(count.removed.0)))]
    fn from(count: ClassCount) -> Self
    {
        Self(i64::wrapping_sub(
            i64::from(u32::from(count.inserted)),
            i64::from(u32::from(count.removed)),
        ))
    }
}

/// The lexicographic obligation delta of a candidate melder decision.
///
/// A `Delta` is a fixed-size per-class count array — one `(removed, inserted)`
/// pair per [`Oblig`] class — never a materialized obligation set, so the
/// molder's per-candidate loop allocates nothing. Its order is tylr's
/// `Delta.compare`, ported exactly: fold the per-class comparison from the
/// **highest** severity down, comparing net (`inserted - removed`) then gross
/// (`inserted`); the first differing class decides. Lower is better, so the
/// melder minimizes obligations and never selects a repair introducing an
/// [`AmbiguousPrec`](Oblig::AmbiguousPrec) when a lower-severity alternative
/// exists.
///
/// # Specification
/// - requires: none.
/// - ensures: `Ord` ranks two deltas by net-then-gross comparison folded from
///   [`AmbiguousPrec`](Oblig::AmbiguousPrec) down to
///   [`MissingMeld`](Oblig::MissingMeld); [`Delta::default`] is the empty (all
///   zero) delta.
/// - provides: the minimization key for candidate melder decisions, comparable
///   without materializing candidate obligation sets.
/// - fails: never; per-class counts saturate at `u32::MAX`.
/// - panics: none.
/// - executable: none — this type has no call boundary; its recording and
///   comparison operations carry the executable obligations.
///
/// # Adequacy
/// - hypothesis: L3 — high-severity-dominance, net-before-gross, and
///   `AmbiguousPrec`-never-chosen witnesses distinguish the fold order.
/// - witness: `oblig::tests::higher_severity_class_dominates_the_order`
/// - witness: `oblig::tests::equal_net_breaks_ties_on_gross_inserted`
/// - witness: `oblig::tests::minimization_never_prefers_ambiguous_prec`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Delta
{
    /// Per-class `(removed, inserted)` counts, indexed by [`Oblig::index`].
    counts: [ClassCount; OBLIG_CLASS_COUNT],
}

impl Delta
{
    /// Return the empty delta (no obligations removed or inserted).
    ///
    /// # Specification
    /// - requires: none.
    /// - ensures: returns a delta whose every per-class count is zero.
    /// - provides: the minimization identity and the baseline of a happy-path
    ///   push.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty and removal-only deltas distinguish zero from
    ///   nonzero changes; every class is checked at zero before saturation.
    /// - witness: `oblig::tests::recording_saturates_each_class_without_cross_talk`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| { let mut remaining: &[ClassCount] = &ret.counts; let mut zero = true; while let Some((count, rest)) = remaining.split_first() { zero = zero && count.removed.0 == 0 && count.inserted.0 == 0; remaining = rest; } zero })]
    pub const fn empty() -> Self
    {
        Self {
            counts: [ClassCount {
                removed: ObligationCount::ZERO,
                inserted: ObligationCount::ZERO,
            }; OBLIG_CLASS_COUNT],
        }
    }

    /// Record `removed` and `inserted` obligations of `class` into the delta.
    ///
    /// Counts accumulate and saturate at `u32::MAX`, so repeated recording
    /// never overflows on the hot path.
    ///
    /// # Specification
    /// - requires: none.
    /// - ensures: adds `removed`/`inserted` to `class`'s counts, saturating.
    /// - provides: the sole mutation of a candidate delta.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every class is recorded at zero, one below the
    ///   ceiling, the ceiling and past it. Exact inserted counts and unchanged
    ///   other classes detect wrapping, wrong slots and lost removal counts.
    /// - witness: `oblig::tests::recording_saturates_each_class_without_cross_talk`
    #[inline]
    #[spec(captures: before = self.counts,
        ensures: self.counts.iter().zip(before).enumerate().all(|(index, (after, before))| {
            if index == usize::from(class.index()) {
                after.removed.0 == before.removed.0.saturating_add(removed.0)
                    && after.inserted.0 == before.inserted.0.saturating_add(inserted.0)
            } else { *after == before }
        }))]
    pub fn record(
        &mut self,
        class: Oblig,
        removed: ObligationCount,
        inserted: ObligationCount,
    )
    {
        if let Some(count) = self.counts.get_mut(usize::from(class.index())) {
            count.removed =
                ObligationCount::from(u32::from(count.removed).saturating_add(u32::from(removed)));
            count.inserted = ObligationCount::from(
                u32::from(count.inserted).saturating_add(u32::from(inserted)),
            );
        }
    }

    /// Record a single inserted obligation of `class`.
    ///
    /// # Specification
    /// - requires: none.
    /// - ensures: increments `class`'s inserted count by one, saturating.
    /// - provides: the melder's per-obligation shorthand over
    ///   [`Delta::record`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — repeated unit insertion reaches and stays at the wire
    ///   ceiling while retaining removals; exact counts distinguish wrapping,
    ///   double increments and mutations of other classes.
    /// - witness: `oblig::tests::recording_saturates_each_class_without_cross_talk`
    #[inline]
    #[spec(captures: before = self.counts.get(usize::from(class.index())).copied(),
        ensures: self.counts.get(usize::from(class.index())).zip(before).is_some_and(|(after, before)| {
            after.removed == before.removed && after.inserted.0 == before.inserted.0.saturating_add(1)
        }))]
    pub fn insert(
        &mut self,
        class: Oblig,
    )
    {
        self.record(class, ObligationCount::ZERO, ObligationCount::ONE);
    }

    /// Return the `inserted` count recorded for `class`.
    ///
    /// # Specification
    /// - requires: none.
    /// - ensures: returns the accumulated inserted count for `class`.
    /// - provides: the per-class read for tests and consumers.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each class is observed before and after saturation;
    ///   zero in every untouched class detects a wrong-slot projection.
    /// - witness: `oblig::tests::recording_saturates_each_class_without_cross_talk`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| self.counts.get(usize::from(class.index())).is_some_and(|count| ret == count.inserted))]
    pub fn inserted(
        &self,
        class: Oblig,
    ) -> ObligationCount
    {
        self.counts
            .get(usize::from(class.index()))
            .map_or(ObligationCount::ZERO, |count| count.inserted)
    }

    /// Return whether the delta records no obligation change.
    ///
    /// # Specification
    /// - requires: none.
    /// - ensures: returns `true` exactly when every per-class count is zero.
    /// - provides: the happy-path predicate.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero, insertion-only, removal-only and cancelling
    ///   deltas distinguish empty state from zero net change.
    /// - witness: `oblig::tests::net_precedes_gross_and_is_signed`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| bool::from(ret) == self.counts.iter().all(|count| count.removed.0 == 0 && count.inserted.0 == 0))]
    pub fn is_empty(&self) -> DeltaEmptyStatus
    {
        DeltaEmptyStatus::from(self.counts.iter().all(|count| {
            count.removed == ObligationCount::ZERO && count.inserted == ObligationCount::ZERO
        }))
    }
}

impl Ord for Delta
{
    /// Compare two deltas by net-then-gross, folded from highest severity down.
    ///
    /// # Specification
    /// - ensures: the first differing severity, from highest to lowest,
    ///   decides; signed net precedes gross insertion count within that class.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — high versus low classes, negative and positive nets,
    ///   equal-net gross ties and equal deltas are observed as strict order or
    ///   equality; reversed severity, unsigned subtraction and gross-first
    ///   folds change those candidate rankings.
    /// - witness: `oblig::tests::higher_severity_class_dominates_the_order`
    /// - witness: `oblig::tests::equal_net_breaks_ties_on_gross_inserted`
    /// - witness: `oblig::tests::net_precedes_gross_and_is_signed`
    #[inline]
    #[spec(ensures: |ret| ret == self.counts.iter().rev().map(|count| (i64::from(count.inserted.0).saturating_sub(i64::from(count.removed.0)), count.inserted)).cmp(other.counts.iter().rev().map(|count| (i64::from(count.inserted.0).saturating_sub(i64::from(count.removed.0)), count.inserted))))]
    fn cmp(
        &self,
        other: &Self,
    ) -> Ordering
    {
        for class in Oblig::all().into_iter().rev() {
            let index = usize::from(class.index());
            let (Some(here), Some(there)) = (self.counts.get(index), other.counts.get(index))
            else {
                continue;
            };
            let net = ObligationNet::from(*here).cmp(&ObligationNet::from(*there));
            if net != Ordering::Equal {
                return net;
            }
            let gross = here.inserted.cmp(&there.inserted);
            if gross != Ordering::Equal {
                return gross;
            }
        }
        Ordering::Equal
    }
}

impl PartialOrd for Delta
{
    /// Order deltas totally, as [`Ord`] does.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn partial_cmp(
        &self,
        other: &Self,
    ) -> Option<Ordering>
    {
        Some(self.cmp(other))
    }
}

#[cfg(test)]
mod tests
{
    use super::Delta;
    use super::OBLIG_CLASS_COUNT;
    use super::Oblig;
    use super::ObligationCount;

    #[test]
    fn counts_convert_at_zero_and_the_wire_ceiling()
    {
        for value in [0_u32, 1, u32::MAX] {
            assert_eq!(
                usize::from(ObligationCount::from(value)),
                usize::try_from(value).unwrap_or(usize::MAX)
            );
        }
    }

    #[test]
    fn recording_saturates_each_class_without_cross_talk()
    {
        for class in Oblig::all() {
            let mut delta = Delta::empty();
            assert!(bool::from(delta.is_empty()));
            let below = ObligationCount::from(u32::MAX.saturating_sub(1));
            delta.record(class, below, below);
            delta.insert(class);
            delta.insert(class);
            assert_eq!(delta.inserted(class), ObligationCount::from(u32::MAX));
            assert_eq!(
                delta
                    .counts
                    .get(usize::from(class.index()))
                    .map(|count| count.removed),
                Some(below)
            );
            delta.record(class, ObligationCount::from(2), ObligationCount::from(2));
            for (index, count) in delta.counts.iter().enumerate() {
                let expected = if index == usize::from(class.index()) {
                    u32::MAX
                }
                else {
                    0
                };
                assert_eq!(count.removed, ObligationCount::from(expected));
                assert_eq!(count.inserted, ObligationCount::from(expected));
            }
        }
    }

    #[test]
    fn net_precedes_gross_and_is_signed()
    {
        for class in Oblig::all() {
            let mut removed = Delta::empty();
            removed.record(
                class,
                ObligationCount::from(u32::MAX),
                ObligationCount::ZERO,
            );
            let mut inserted = Delta::empty();
            inserted.record(
                class,
                ObligationCount::ZERO,
                ObligationCount::from(u32::MAX),
            );
            let mut cancelled = Delta::empty();
            cancelled.record(
                class,
                ObligationCount::from(u32::MAX),
                ObligationCount::from(u32::MAX),
            );
            assert!(removed < Delta::empty());
            assert!(Delta::empty() < cancelled);
            assert!(cancelled < inserted);
            assert!(!bool::from(removed.is_empty()));
            assert!(!bool::from(cancelled.is_empty()));
            assert_eq!(cancelled.cmp(&cancelled), core::cmp::Ordering::Equal);
            assert_eq!(
                removed.partial_cmp(&inserted),
                Some(core::cmp::Ordering::Less)
            );
            let mut net_minus_one = Delta::empty();
            net_minus_one.record(class, ObligationCount::from(11), ObligationCount::from(10));
            assert!(net_minus_one < Delta::empty());
        }
    }

    #[test]
    fn severity_ladder_is_low_to_high()
    {
        let ladder = Oblig::all();
        assert_eq!(ladder, [
            Oblig::MissingMeld,
            Oblig::MissingTile,
            Oblig::IncompleteTile,
            Oblig::UnmoldedTok,
            Oblig::InconMeld,
            Oblig::ExtraMeld,
            Oblig::ReservedKeyword,
            Oblig::AmbiguousPrec
        ]);
        for pair in ladder.windows(2) {
            if let &[lower, higher] = pair {
                assert!(
                    lower < higher,
                    "{lower:?} must be strictly less severe than {higher:?}"
                );
            }
        }
        assert_eq!(Oblig::MissingMeld, ladder[0]);
        assert_eq!(Oblig::AmbiguousPrec, ladder[OBLIG_CLASS_COUNT - 1]);
    }

    #[test]
    fn ambiguous_prec_is_maximally_severe()
    {
        for class in Oblig::all() {
            assert!(class <= Oblig::AmbiguousPrec);
        }
    }

    #[test]
    fn index_matches_ord_rank()
    {
        let ladder = Oblig::all();
        for (rank, class) in ladder.into_iter().enumerate() {
            assert_eq!(usize::from(class.index()), rank);
            assert_eq!(usize::from(u8::from(class.index())), rank);
        }
    }

    #[test]
    fn empty_delta_is_empty()
    {
        assert!(bool::from(Delta::empty().is_empty()));
        let mut delta = Delta::empty();
        delta.insert(Oblig::MissingMeld);
        assert!(!bool::from(delta.is_empty()));
    }

    #[test]
    fn insert_is_record_of_one_inserted()
    {
        let mut delta = Delta::empty();
        delta.insert(Oblig::ExtraMeld);
        delta.insert(Oblig::ExtraMeld);
        assert_eq!(2, u32::from(delta.inserted(Oblig::ExtraMeld)));
        assert_eq!(0, u32::from(delta.inserted(Oblig::MissingMeld)));
    }

    #[test]
    fn higher_severity_class_dominates_the_order()
    {
        // A single high-severity insertion outranks any number of low-severity
        // insertions: the fold decides at the highest differing class.
        let mut low = Delta::empty();
        for _ in 0 .. 100_u32 {
            low.insert(Oblig::MissingMeld);
        }
        let mut high = Delta::empty();
        high.insert(Oblig::InconMeld);
        assert!(high > low, "one InconMeld outranks 100 MissingMeld");
    }

    #[test]
    fn equal_net_breaks_ties_on_gross_inserted()
    {
        // Equal net change at the deciding class breaks the tie on gross
        // inserted (tylr `Delta.compare` net-then-gross).
        let mut removed_and_inserted = Delta::empty();
        removed_and_inserted.record(
            Oblig::ExtraMeld,
            ObligationCount::from(1),
            ObligationCount::from(1),
        ); // net 0, gross 1
        let mut only_inserted_more = Delta::empty();
        only_inserted_more.record(
            Oblig::ExtraMeld,
            ObligationCount::from(2),
            ObligationCount::from(2),
        ); // net 0, gross 2
        assert!(
            only_inserted_more > removed_and_inserted,
            "equal net breaks the tie on gross inserted"
        );
    }

    #[test]
    fn minimization_never_prefers_ambiguous_prec()
    {
        // l605 (a)/(b) at the Delta seam: a candidate that inserts an
        // AmbiguousPrec is strictly worse than any candidate that does not, so
        // `min` never chooses ambiguity when an alternative exists.
        let mut ambiguous = Delta::empty();
        ambiguous.insert(Oblig::AmbiguousPrec);

        let mut lower_severity_alternatives = [Delta::empty(); OBLIG_CLASS_COUNT - 1];
        for (slot, class) in lower_severity_alternatives.iter_mut().zip(Oblig::all()) {
            // Even ten insertions of a lower-severity class stay below one
            // AmbiguousPrec.
            for _ in 0 .. 10_u32 {
                slot.insert(class);
            }
        }

        for alternative in lower_severity_alternatives {
            assert!(
                alternative < ambiguous,
                "the AmbiguousPrec delta must be the maximum, so minimization avoids it"
            );
        }

        let best = lower_severity_alternatives
            .into_iter()
            .chain(core::iter::once(ambiguous))
            .min()
            .expect("non-empty candidate set");
        assert_ne!(
            u32::from(best.inserted(Oblig::AmbiguousPrec)),
            1,
            "the minimum candidate never introduces an ambiguity"
        );
    }
}
