//! The **expansion census**: how many goals each machine expanded, and how many
//! it was served from the memo, per plane.
//!
//! # Why this is a contract rather than telemetry
//!
//! A differential can be green while never reaching the code it tests, so every
//! reuse harness here **asserts** its exercised-path counts rather than
//! reporting them. That needs a declared projection: the counts are the
//! observation the collapse law, the anti-vacuity cases and the teeth are all
//! stated over.
//!
//! It is an intensional projection — it says how the computation proceeded, not
//! what it returned — so no extensional clause anywhere references it, and
//! retuning it leaves every verdict witness green.

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
    #[inline]
    #[must_use]
    const fn successor(self) -> Self
    {
        Self(self.0.saturating_add(1))
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
    #[inline]
    #[must_use]
    const fn plus(
        self,
        other: Self,
    ) -> Self
    {
        Self(self.0.saturating_add(other.0))
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
/// - ensures: [`Self::expansions`] counts every goal whose rule actually ran
///   and [`Self::recalls`] every goal the memo answered, each split by plane so
///   neither machine's collapse hides behind the other's numbers.
/// - provides: the declared intensional projection the acceptance suite asserts
///   its exercised paths through. These lifecycle and event-count claims remain
///   prose-only: a data specification cannot observe the check calls or goal
///   events that update this census.
/// - fails: never.
/// - panics: none.
/// - intension: the counts are goal expansions of the two iterative machines,
///   one per loop iteration, in the order the machines run. Nothing extensional
///   depends on them.
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
    /// - ensures: exactly one of the four counters moves — the one `plane` and
    ///   `kind` name — and it moves by one, saturating at the ceiling.
    /// - provides: the recording side of the declared intensional projection,
    ///   so an expansion and a recall are never charged to the same counter.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    pub(crate) const fn record(
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
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn expansions(&self) -> ExpansionCount
    {
        self.term_expanded.plus(self.type_expanded)
    }

    /// How many goals the memo answered across both machines.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn recalls(&self) -> ExpansionCount
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
}
