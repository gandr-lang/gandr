//! The **expansion census**: how many goals each machine expanded, and how many
//! it was served from the memo, per plane.
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

/// Whether a goal was expanded or served from the memo.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ExpansionKind
{
    /// The machine read the node and ran its rule.
    Expanded,
    /// The memo answered, so the node was not read.
    Recalled,
}

/// The per-plane expansion and recall counts of one check call.
///
/// # Specification
/// - requires: one census per check call; a census reused across calls sums
///   them, which is a measurement error rather than a soundness one.
/// - ensures: [`Self::expansions`] counts goals whose rules ran and
///   [`Self::recalls`] goals the memo answered, up to the representation
///   ceiling, each split by plane so neither machine's collapse hides behind
///   the other's numbers.
/// - provides: the declared intensional projection the acceptance suite uses to
///   observe exercised paths.
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
///   per-plane counts with closed forms; L3 on four event choices and the
///   saturation boundary. These finite traces distinguish mischarging and lost
///   counts, not universal correspondence with every checker event.
/// - witness: `acceptance::acceptance::the_collapse_is_a_closed_form_at_three_depths`
/// - witness: `census::tests::records_charge_only_the_selected_counter_through_saturation`
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct ExpansionCensus
{
    /// Goals the checker's loop expanded.
    term_expanded: ExpansionCount,
    /// Goals the memo answered for the checker's loop.
    term_recalled: ExpansionCount,
    /// Goals the type-formation walk expanded.
    type_expanded: ExpansionCount,
    /// Goals the memo answered for the type-formation walk.
    type_recalled: ExpansionCount,
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
            type_expanded: ExpansionCount::zero(),
            type_recalled: ExpansionCount::zero(),
        }
    }

    /// Record one goal on `plane`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: updates the counter selected by `plane` and `kind` to its
    ///   saturating successor; the other three counters remain unchanged.
    /// - provides: the recording side of the declared intensional projection,
    ///   so an expansion and a recall are never charged to the same counter.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 exhausts the plane/kind choices from distinct counts
    ///   and across the successor ceiling; all four projections distinguish
    ///   misrouting, extra charges, omission and wrapping.
    /// - witness: `census::tests::records_charge_only_the_selected_counter_through_saturation`
    #[spec(captures: before = *self,
    ensures: self.term_expanded.0 == before.term_expanded.0.saturating_add(
            u64::from(matches!((plane, kind), (SupportPlane::Term, ExpansionKind::Expanded))))
        && self.term_recalled.0 == before.term_recalled.0.saturating_add(
            u64::from(matches!((plane, kind), (SupportPlane::Term, ExpansionKind::Recalled))))
        && self.type_expanded.0 == before.type_expanded.0.saturating_add(
            u64::from(matches!((plane, kind), (SupportPlane::Type, ExpansionKind::Expanded))))
        && self.type_recalled.0 == before.type_recalled.0.saturating_add(
            u64::from(matches!((plane, kind), (SupportPlane::Type, ExpansionKind::Recalled)))))]
    #[inline]
    pub(crate) fn record(
        &mut self,
        plane: SupportPlane,
        kind: ExpansionKind,
    )
    {
        match (plane, kind) {
            | (SupportPlane::Term, ExpansionKind::Expanded) => {
                self.term_expanded = self.term_expanded.successor();
            },
            | (SupportPlane::Term, ExpansionKind::Recalled) => {
                self.term_recalled = self.term_recalled.successor();
            },
            | (SupportPlane::Type, ExpansionKind::Expanded) => {
                self.type_expanded = self.type_expanded.successor();
            },
            | (SupportPlane::Type, ExpansionKind::Recalled) => {
                self.type_recalled = self.type_recalled.successor();
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
            | SupportPlane::Term => self.term_expanded,
            | SupportPlane::Type => self.type_expanded,
        }
    }

    /// How many goals the memo answered for `plane`.
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
            | SupportPlane::Term => self.term_recalled,
            | SupportPlane::Type => self.type_recalled,
        }
    }

    /// How many goals both machines expanded.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the saturating sum of the two planes' expansion counts.
    /// - provides: the expansion total without counting memo recalls.
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

    /// How many goals the memo answered across both machines.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the saturating sum of the two planes' recall counts.
    /// - provides: the recall total without counting expanded goals.
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
        assert_eq!(
            ExpansionCount::from(2),
            census.plane_expansions(SupportPlane::Term)
        );
        assert_eq!(
            ExpansionCount::from(1),
            census.plane_recalls(SupportPlane::Term)
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
        assert_eq!(ExpansionCount::from(3), census.expansions());
        assert_eq!(ExpansionCount::from(1), census.recalls());
    }

    #[test]
    fn records_charge_only_the_selected_counter_through_saturation()
    {
        let below = u64::MAX.saturating_sub(1);
        let counts = |census: &ExpansionCensus| {
            [
                census.plane_expansions(SupportPlane::Term),
                census.plane_recalls(SupportPlane::Term),
                census.plane_expansions(SupportPlane::Type),
                census.plane_recalls(SupportPlane::Type),
            ]
            .map(u64::from)
        };
        let cases = [
            (SupportPlane::Term, ExpansionKind::Expanded, [3, 3, 5, 7], [
                u64::MAX,
                below,
                below,
                below,
            ]),
            (SupportPlane::Term, ExpansionKind::Recalled, [2, 4, 5, 7], [
                below,
                u64::MAX,
                below,
                below,
            ]),
            (SupportPlane::Type, ExpansionKind::Expanded, [2, 3, 6, 7], [
                below,
                below,
                u64::MAX,
                below,
            ]),
            (SupportPlane::Type, ExpansionKind::Recalled, [2, 3, 5, 8], [
                below,
                below,
                below,
                u64::MAX,
            ]),
        ];
        for (plane, kind, ordinary, ceiling) in cases {
            let mut census = ExpansionCensus {
                term_expanded: ExpansionCount::from(2),
                term_recalled: ExpansionCount::from(3),
                type_expanded: ExpansionCount::from(5),
                type_recalled: ExpansionCount::from(7),
            };
            census.record(plane, kind);
            assert_eq!(counts(&census), ordinary);
            let mut census = ExpansionCensus {
                term_expanded: ExpansionCount::from(below),
                term_recalled: ExpansionCount::from(below),
                type_expanded: ExpansionCount::from(below),
                type_recalled: ExpansionCount::from(below),
            };
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
            ([0, 0, 0, 0], [0, 0]),
            ([2, 3, 5, 7], [7, 10]),
            ([below, 1, 1, below], [u64::MAX, u64::MAX]),
            ([u64::MAX, 1, 1, u64::MAX], [u64::MAX, u64::MAX]),
        ];
        for (fields, expected) in cases {
            let [term_expanded, term_recalled, type_expanded, type_recalled] =
                fields.map(ExpansionCount::from);
            let census = ExpansionCensus {
                term_expanded,
                term_recalled,
                type_expanded,
                type_recalled,
            };
            assert_eq!(
                [u64::from(census.expansions()), u64::from(census.recalls())],
                expected
            );
        }
    }
}
