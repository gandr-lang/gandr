//! The **expansion census**: how many goals each machine expanded, how many
//! this check's memo answered, and how many an earlier admission's kept
//! outcome answered, per plane.
//!
//! # Why this is an obligation rather than telemetry
//!
//! A differential can be green while never reaching the code it tests, so every
//! reuse harness here **asserts** its exercised-path counts rather than
//! reporting them. That needs a declared projection: the counts are the
//! observation the collapse law, the anti-vacuity cases and the poisoned-entry
//! cases are all stated over.
//!
//! The census is an intensional projection of checking, separate from its
//! verdict. Its own arithmetic and event routing have executable predicates;
//! retuning checker accounting leaves extensional verdict obligations intact.
//!
//! # References
//!
//! - `vault:01a178aa-6917-7983-b5cd-86e2af86b3ec` — background: the
//!   reassessment's probe counts local hits, cross hits and misses, the three
//!   counts a goal is routed to here.

use anodized::spec;
use quenchant_arith::arith;

use crate::support::SupportPlane;

/// How many goal expansions one plane performed, or was served.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ExpansionCount(u64);

impl ExpansionCount
{
    /// The count of a machine that has done nothing.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn zero() -> Self
    {
        Self(0)
    }

    /// The next count up, saturating at the ceiling.
    ///
    /// Saturating rather than refusing: this is a measurement and not a
    /// verdict, so a count at its ceiling must not be able to turn a check into
    /// a refusal. A saturated count is visibly wrong to the assertion that
    /// reads it, which is the failure mode a measurement can afford.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the count one greater than `self`, and `self` itself at the
    ///   ceiling.
    /// - provides: the only increment this census performs, so a measurement
    ///   can be visibly wrong but never turn a check into a refusal.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 at an ordinary count, the predecessor of the ceiling
    ///   and the ceiling; exact selected-counter values distinguish omission,
    ///   premature clamping and wrapping.
    /// - witness: `census::tests::records_charge_only_the_selected_counter_through_saturation`
    #[spec(ensures: |ret| ret.0 == self.0.saturating_add(1))]
    #[inline]
    #[must_use]
    fn successor(self) -> Self
    {
        // reason: census measurements clamp at u64::MAX without refusing a check.
        Self(u64::from(arith::saturating_add(
            arith::Int::from(self.0),
            arith::Int::from(1_u64),
        )))
    }

    /// The sum of two counts, saturating at the ceiling.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the sum of the two counts, and the ceiling when the sum would
    ///   leave the range.
    /// - provides: the per-plane totals both public projections are folded
    ///   with.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on zero, unequal ordinary operands, an exact ceiling
    ///   sum and an overflowing sum; public totals distinguish operand loss,
    ///   premature clamping and wrapping.
    /// - witness: `census::tests::plane_totals_saturate_without_mixing_kinds`
    #[spec(ensures: |ret| ret.0 == self.0.saturating_add(other.0))]
    #[inline]
    #[must_use]
    fn plus(
        self,
        other: Self,
    ) -> Self
    {
        // reason: the combined measurement has the same u64::MAX ceiling.
        Self(u64::from(arith::saturating_add(
            arith::Int::from(self.0),
            arith::Int::from(other.0),
        )))
    }
}

impl From<u64> for ExpansionCount
{
    /// The count of `count` goals.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: u64) -> Self
    {
        Self(count)
    }
}

impl From<ExpansionCount> for u64
{
    /// How many goals `count` counts.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: ExpansionCount) -> Self
    {
        count.0
    }
}

/// Whether a goal was expanded or answered without being read, and by which
/// store.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ExpansionKind
{
    /// The machine read the node and ran its rule.
    Expanded,
    /// This check's memo answered, so the node was not read.
    Recalled,
    /// An outcome an earlier admission kept answered, so the node was not
    /// read.
    Kept,
}

/// The per-plane expansion, recall and kept counts of one check call.
///
/// # Specification
/// - requires: one census per check call; a census reused across calls sums
///   them, which is a measurement error rather than a soundness one.
/// - ensures: [`Self::expansions`] counts goals whose rules ran,
///   [`Self::recalls`] goals this check's memo answered and [`Self::kept`]
///   goals an earlier admission's kept outcome answered, up to the
///   representation ceiling, each split by plane so neither machine's collapse
///   hides behind the other's numbers.
/// - provides: the declared intensional projection the acceptance suite uses to
///   observe exercised paths, and the tally an admission keeps on its entry.
/// - fails: never.
/// - panics: none.
/// - executable: none — a stored census does not retain the check-call or
///   goal-event history needed to compare its counts with those events.
/// - intension: the counts are goal expansions of the two iterative machines,
///   one per loop iteration, in the order the machines run. Nothing extensional
///   depends on them.
///
/// # Adequacy
/// - hypothesis: L2 on shared composites at depths 8, 12 and 16, comparing
///   per-plane counts with closed forms; L2 on a declaration admitted twice,
///   whose second admission is answered by the first's kept outcomes; L3 on six
///   event choices and the saturation boundary. These finite traces distinguish
///   mischarging and lost counts, not universal correspondence with every
///   checker event.
/// - witness: `tests::acceptance::the_collapse_is_a_closed_form_at_three_depths`
/// - witness: `env::tests::a_repeated_declaration_is_answered_by_the_kept_outcomes_of_the_first`
/// - witness: `census::tests::records_charge_only_the_selected_counter_through_saturation`
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct ExpansionCensus
{
    /// Goals the checker's loop expanded.
    term_expanded: ExpansionCount,
    /// Goals this check's memo answered for the checker's loop.
    term_recalled: ExpansionCount,
    /// Goals an earlier admission's kept outcome answered for the checker's
    /// loop.
    term_kept: ExpansionCount,
    /// Goals the type-formation walk expanded.
    type_expanded: ExpansionCount,
    /// Goals this check's memo answered for the type-formation walk.
    type_recalled: ExpansionCount,
    /// Goals an earlier admission's kept outcome answered for the
    /// type-formation walk.
    type_kept: ExpansionCount,
}

impl ExpansionCensus
{
    /// A census over nothing.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new() -> Self
    {
        Self {
            term_expanded: ExpansionCount::zero(),
            term_recalled: ExpansionCount::zero(),
            term_kept: ExpansionCount::zero(),
            type_expanded: ExpansionCount::zero(),
            type_recalled: ExpansionCount::zero(),
            type_kept: ExpansionCount::zero(),
        }
    }

    /// Record one goal on `plane`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: updates the counter selected by `plane` and `kind` to its
    ///   saturating successor; the other five counters remain unchanged.
    /// - provides: the recording side of the declared intensional projection,
    ///   so an expansion, a recall and a kept answer are never charged to the
    ///   same counter.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 exhausts the plane/kind choices from distinct counts
    ///   and across the successor ceiling; all six projections distinguish
    ///   misrouting, extra charges, omission and wrapping.
    /// - witness: `census::tests::records_charge_only_the_selected_counter_through_saturation`
    #[spec(captures: before = *self,
    ensures: self.term_expanded.0 == before.term_expanded.0.saturating_add(
            u64::from(matches!((plane, kind), (SupportPlane::Term, ExpansionKind::Expanded))))
        && self.term_recalled.0 == before.term_recalled.0.saturating_add(
            u64::from(matches!((plane, kind), (SupportPlane::Term, ExpansionKind::Recalled))))
        && self.term_kept.0 == before.term_kept.0.saturating_add(
            u64::from(matches!((plane, kind), (SupportPlane::Term, ExpansionKind::Kept))))
        && self.type_expanded.0 == before.type_expanded.0.saturating_add(
            u64::from(matches!((plane, kind), (SupportPlane::Type, ExpansionKind::Expanded))))
        && self.type_recalled.0 == before.type_recalled.0.saturating_add(
            u64::from(matches!((plane, kind), (SupportPlane::Type, ExpansionKind::Recalled))))
        && self.type_kept.0 == before.type_kept.0.saturating_add(
            u64::from(matches!((plane, kind), (SupportPlane::Type, ExpansionKind::Kept)))))]
    #[inline]
    pub(crate) fn record(
        &mut self,
        plane: SupportPlane,
        kind: ExpansionKind,
    )
    {
        match (plane, kind) {
            (SupportPlane::Term, ExpansionKind::Expanded) => {
                self.term_expanded = self.term_expanded.successor();
            },
            (SupportPlane::Term, ExpansionKind::Recalled) => {
                self.term_recalled = self.term_recalled.successor();
            },
            (SupportPlane::Term, ExpansionKind::Kept) => {
                self.term_kept = self.term_kept.successor();
            },
            (SupportPlane::Type, ExpansionKind::Expanded) => {
                self.type_expanded = self.type_expanded.successor();
            },
            (SupportPlane::Type, ExpansionKind::Recalled) => {
                self.type_recalled = self.type_recalled.successor();
            },
            (SupportPlane::Type, ExpansionKind::Kept) => {
                self.type_kept = self.type_kept.successor();
            },
        }
    }

    /// How many goals `plane` expanded.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn plane_expansions(
        &self,
        plane: SupportPlane,
    ) -> ExpansionCount
    {
        match plane {
            SupportPlane::Term => self.term_expanded,
            SupportPlane::Type => self.type_expanded,
        }
    }

    /// How many goals this check's memo answered for `plane`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn plane_recalls(
        &self,
        plane: SupportPlane,
    ) -> ExpansionCount
    {
        match plane {
            SupportPlane::Term => self.term_recalled,
            SupportPlane::Type => self.type_recalled,
        }
    }

    /// How many goals an earlier admission's kept outcome answered for
    /// `plane`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn plane_kept(
        &self,
        plane: SupportPlane,
    ) -> ExpansionCount
    {
        match plane {
            SupportPlane::Term => self.term_kept,
            SupportPlane::Type => self.type_kept,
        }
    }

    /// How many goals both machines expanded.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the saturating sum of the two planes' expansion counts.
    /// - provides: the expansion total without counting a goal answered unread.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on zero, distinct per-plane counts and sums at and
    ///   above the ceiling; exact totals distinguish plane/kind mixing, omitted
    ///   operands and wrapping.
    /// - witness: `census::tests::plane_totals_saturate_without_mixing_kinds`
    #[spec(ensures: |ret| ret.0 == self.term_expanded.0.saturating_add(self.type_expanded.0))]
    #[inline]
    #[must_use]
    pub fn expansions(&self) -> ExpansionCount
    {
        self.term_expanded.plus(self.type_expanded)
    }

    /// How many goals this check's memo answered across both machines.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the saturating sum of the two planes' recall counts.
    /// - provides: the recall total without counting expanded or kept goals.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on zero, distinct per-plane counts and sums at and
    ///   above the ceiling; exact totals distinguish plane/kind mixing, omitted
    ///   operands and wrapping.
    /// - witness: `census::tests::plane_totals_saturate_without_mixing_kinds`
    #[spec(ensures: |ret| ret.0 == self.term_recalled.0.saturating_add(self.type_recalled.0))]
    #[inline]
    #[must_use]
    pub fn recalls(&self) -> ExpansionCount
    {
        self.term_recalled.plus(self.type_recalled)
    }

    /// How many goals an earlier admission's kept outcome answered across
    /// both machines.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the saturating sum of the two planes' kept counts.
    /// - provides: the cross-admission total without counting expanded or
    ///   recalled goals.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on zero, distinct per-plane counts and sums at and
    ///   above the ceiling; exact totals distinguish plane/kind mixing, omitted
    ///   operands and wrapping.
    /// - witness: `census::tests::plane_totals_saturate_without_mixing_kinds`
    #[spec(ensures: |ret| ret.0 == self.term_kept.0.saturating_add(self.type_kept.0))]
    #[inline]
    #[must_use]
    pub fn kept(&self) -> ExpansionCount
    {
        self.term_kept.plus(self.type_kept)
    }
}

#[cfg(test)]
mod tests
{
    use super::ExpansionCensus;
    use super::ExpansionCount;
    use super::ExpansionKind;
    use crate::support::SupportPlane;

    #[test]
    fn a_census_splits_by_plane_and_by_kind()
    {
        let mut census = ExpansionCensus::new();
        census.record(SupportPlane::Term, ExpansionKind::Expanded);
        census.record(SupportPlane::Term, ExpansionKind::Expanded);
        census.record(SupportPlane::Term, ExpansionKind::Recalled);
        census.record(SupportPlane::Type, ExpansionKind::Expanded);
        census.record(SupportPlane::Type, ExpansionKind::Kept);
        assert_eq!(
            ExpansionCount::from(2),
            census.plane_expansions(SupportPlane::Term)
        );
        assert_eq!(
            ExpansionCount::from(1),
            census.plane_recalls(SupportPlane::Term)
        );
        assert_eq!(
            ExpansionCount::zero(),
            census.plane_kept(SupportPlane::Term)
        );
        assert_eq!(
            ExpansionCount::from(1),
            census.plane_expansions(SupportPlane::Type)
        );
        assert_eq!(
            ExpansionCount::zero(),
            census.plane_recalls(SupportPlane::Type),
            "a plane that recalled nothing counts zero rather than borrowing the other's number"
        );
        assert_eq!(
            ExpansionCount::from(1),
            census.plane_kept(SupportPlane::Type)
        );
        assert_eq!(ExpansionCount::from(3), census.expansions());
        assert_eq!(ExpansionCount::from(1), census.recalls());
        assert_eq!(ExpansionCount::from(1), census.kept());
    }

    #[test]
    fn records_charge_only_the_selected_counter_through_saturation()
    {
        let below = u64::MAX.saturating_sub(1);
        let counts = |census: &ExpansionCensus| {
            [
                census.plane_expansions(SupportPlane::Term),
                census.plane_recalls(SupportPlane::Term),
                census.plane_kept(SupportPlane::Term),
                census.plane_expansions(SupportPlane::Type),
                census.plane_recalls(SupportPlane::Type),
                census.plane_kept(SupportPlane::Type),
            ]
            .map(u64::from)
        };
        let census_of = |[
            term_expanded,
            term_recalled,
            term_kept,
            type_expanded,
            type_recalled,
            type_kept,
        ]: [u64; 6]| {
            ExpansionCensus {
                term_expanded: ExpansionCount::from(term_expanded),
                term_recalled: ExpansionCount::from(term_recalled),
                term_kept: ExpansionCount::from(term_kept),
                type_expanded: ExpansionCount::from(type_expanded),
                type_recalled: ExpansionCount::from(type_recalled),
                type_kept: ExpansionCount::from(type_kept),
            }
        };
        let start: [u64; 6] = [2, 3, 4, 5, 7, 11];
        let choices = [
            (SupportPlane::Term, ExpansionKind::Expanded),
            (SupportPlane::Term, ExpansionKind::Recalled),
            (SupportPlane::Term, ExpansionKind::Kept),
            (SupportPlane::Type, ExpansionKind::Expanded),
            (SupportPlane::Type, ExpansionKind::Recalled),
            (SupportPlane::Type, ExpansionKind::Kept),
        ];
        for (selected, (plane, kind)) in choices.into_iter().enumerate() {
            let mut ordinary = start;
            let mut ceiling = [below; 6];
            if let (Some(count), Some(top)) =
                (ordinary.get_mut(selected), ceiling.get_mut(selected))
            {
                *count = count.saturating_add(1);
                *top = u64::MAX;
            }
            let mut census = census_of(start);
            census.record(plane, kind);
            assert_eq!(
                counts(&census),
                ordinary,
                "{plane:?} {kind:?} charges its own counter"
            );
            let mut census = census_of([below; 6]);
            census.record(plane, kind);
            assert_eq!(counts(&census), ceiling);
            census.record(plane, kind);
            assert_eq!(counts(&census), ceiling);
        }
    }

    #[test]
    fn plane_totals_saturate_without_mixing_kinds()
    {
        let below = u64::MAX.saturating_sub(1);
        let cases = [
            ([0, 0, 0, 0, 0, 0], [0, 0, 0]),
            ([2, 3, 4, 5, 7, 11], [7, 10, 15]),
            ([below, 1, 1, 1, below, below], [
                u64::MAX,
                u64::MAX,
                u64::MAX,
            ]),
            ([u64::MAX, 1, 1, 1, u64::MAX, u64::MAX], [
                u64::MAX,
                u64::MAX,
                u64::MAX,
            ]),
        ];
        for (fields, expected) in cases {
            let [
                term_expanded,
                term_recalled,
                term_kept,
                type_expanded,
                type_recalled,
                type_kept,
            ] = fields.map(ExpansionCount::from);
            let census = ExpansionCensus {
                term_expanded,
                term_recalled,
                term_kept,
                type_expanded,
                type_recalled,
                type_kept,
            };
            assert_eq!(
                [
                    u64::from(census.expansions()),
                    u64::from(census.recalls()),
                    u64::from(census.kept())
                ],
                expected
            );
        }
    }
}
