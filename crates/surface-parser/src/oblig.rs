//! The obligation taxonomy and the `Delta` minimization order.
//!
//! The taxonomy descends from tylr's `structure/Oblig.re` with gandr's
//! `AmbiguousPrec` addition. The Rust enum is declared in **severity order** so
//! `derive(Ord)` is the truth: tylr orders severity via its `all` list rather
//! than its variant declaration order, and gandr fixes the order at the type
//! level.

use core::cmp::Ordering;

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
    /// trivial.
    #[inline]
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
    /// trivial.
    #[inline]
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
    /// - hypothesis: L1 — a constant projection; contents are witnessed by the
    ///   ladder test.
    /// - witness: `oblig::tests::severity_ladder_is_low_to_high`
    #[inline]
    #[must_use]
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
    /// - hypothesis: L1 — a direct field initialization; retention is witnessed
    ///   where the melder emits instances.
    /// - witness: `meld::tests::degrout_flags_one_ambiguous_prec_at_the_smallest_span`
    #[inline]
    #[must_use]
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
    /// trivial.
    #[inline]
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
    /// - hypothesis: L1 — the zero delta; behavior is witnessed by the order
    ///   tests that compare against it.
    /// - witness: `oblig::tests::minimization_never_prefers_ambiguous_prec`
    #[inline]
    #[must_use]
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
    /// - hypothesis: L3 — recording into distinct classes shifts the order at
    ///   exactly the recorded class.
    /// - witness: `oblig::tests::higher_severity_class_dominates_the_order`
    #[inline]
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
    /// - hypothesis: L1 — a thin wrapper over [`Delta::record`]; behavior is
    ///   witnessed there.
    /// - witness: `oblig::tests::insert_is_record_of_one_inserted`
    #[inline]
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
    /// - hypothesis: L1 — a projection; witnessed by the recording tests.
    /// - witness: `oblig::tests::insert_is_record_of_one_inserted`
    #[inline]
    #[must_use]
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
    /// - hypothesis: L3 — the empty delta and any non-empty delta separate the
    ///   predicate.
    /// - witness: `oblig::tests::empty_delta_is_empty`
    #[inline]
    #[must_use]
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
    /// trivial.
    #[inline]
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
    fn severity_ladder_is_low_to_high()
    {
        let ladder = Oblig::all();
        assert_eq!(OBLIG_CLASS_COUNT, ladder.len());
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
