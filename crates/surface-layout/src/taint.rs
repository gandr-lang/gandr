//! Width taint and exact deferred promises.
//!
//! Taint is a semantic state, not an error or truncation marker. It preserves
//! the exact context that fell outside the computation theorem and keeps the
//! resolver able to produce a complete plan.

use alloc::vec::Vec;

use quenchant_shape::shape::Maybe;

use crate::arena::NodeId;
use crate::error::RenderError;
use crate::measure::Measure;
use crate::units::Column;
use crate::units::Indentation;

quenchant_shape::reason_enum! {
    /// Why a measure set offers no first measure.
    pub(crate) mod first {
        /// The reason none is offered.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub(crate) enum Absent {
            /// The frontier holds no measure.
            Empty,
            /// The promise is deferred and has not been forced.
            Deferred,
        }
    }
}

/// A private measure result: an untainted frontier or one retained promise.
///
/// # Specification
/// - requires: a frontier was normalized by the resolver.
/// - ensures: a frontier is sorted by cost and holds no dominated measure.
/// - provides: the value every resolver step produces and consumes.
/// - panics: none.
#[derive(Clone, Debug)]
pub(crate) enum MeasureSet
{
    /// A non-empty Pareto frontier.
    Frontier(Vec<Measure>),
    /// A width-tainted promise.
    Tainted(TaintPromise),
}

/// The exact promise retained by a tainted state.
///
/// # Specification
/// - requires: a deferred promise carries the exact context it left.
/// - ensures: forcing a deferred promise resolves exactly that context.
/// - provides: width taint without truncation.
/// - panics: none.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum TaintPromise
{
    /// A concrete least-cost measure retained without forcing another branch.
    Ready(Measure),
    /// A subproblem deferred with its exact context.
    Deferred
    {
        /// The document identity to force.
        doc: NodeId,
        /// The exact incoming column.
        column: Column,
        /// The exact indentation.
        indentation: Indentation,
    },
}

/// Keeps the first frontier measure as a ready taint promise and reports
/// discarded ready measures to `release`.
///
/// # Specification
/// - requires: `set` is a valid resolver result.
/// - ensures: a frontier retains only its first least-cost measure, and every
///   other measure reaches `release` once, in frontier order.
/// - provides: the taint operation of the resolution algebra.
/// - fails: the first error `release` returns.
/// - panics: none.
///
/// # Errors
/// Returns the first error `release` returns.
///
/// # Adequacy
/// - hypothesis: L3 — a two-measure frontier keeps its first measure and
///   releases exactly the second.
/// - witness: `taint::tests::taint_reports_discarded_frontier_measures`
#[inline]
pub(crate) fn taint(
    set: MeasureSet,
    mut release: impl FnMut(Measure) -> Result<(), RenderError>,
) -> Result<MeasureSet, RenderError>
{
    match set {
        | MeasureSet::Frontier(frontier) => {
            let mut iter = frontier.into_iter();
            match iter.next() {
                | Some(first) => {
                    for measure in iter {
                        release(measure)?;
                    }
                    Ok(MeasureSet::Tainted(TaintPromise::Ready(first)))
                },
                | None => Ok(MeasureSet::Frontier(Vec::new())),
            }
        },
        | MeasureSet::Tainted(promise) => Ok(MeasureSet::Tainted(promise)),
    }
}

/// Constructs an exact deferred promise for an out-of-bound state.
///
/// # Specification
/// - requires: `doc`, `column`, and `indentation` are the exact context.
/// - ensures: no in-bound frontier is substituted for this promise.
/// - provides: context-preserving width taint.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — two contexts of one node defer to two promises that each
///   carry their own column and indentation.
/// - witness: `resolve::tests::tainted_promises_retain_distinct_contexts_and_forced_measures`
#[inline]
pub(crate) fn deferred(
    doc: NodeId,
    column: Column,
    indentation: Indentation,
) -> MeasureSet
{
    MeasureSet::Tainted(TaintPromise::Deferred {
        doc,
        column,
        indentation,
    })
}

/// Merges two choice results with the prescribed taint bias and reports
/// discarded ready promises to `release`.
///
/// # Specification
/// - requires: both values came from the same resolution context.
/// - ensures: frontier/frontier concatenates left then right, a frontier wins
///   over taint, and taint/taint returns the left promise unforced; every
///   discarded promise reaches `release` once.
/// - provides: the choice merge of the resolution algebra.
/// - fails: the first error `release` returns, or a frontier that cannot grow.
/// - panics: none.
///
/// # Errors
/// Returns [`RenderError::AllocationFailed`] when the combined frontier cannot
/// be reserved, and the first error `release` returns.
///
/// # Adequacy
/// - hypothesis: L3 — a frontier merged with a ready promise keeps the frontier
///   and releases the promise's measure.
/// - witness: `taint::tests::merge_frontier_wins_over_ready_taint`
#[inline]
pub(crate) fn merge(
    left: MeasureSet,
    right: MeasureSet,
    mut release: impl FnMut(TaintPromise) -> Result<(), RenderError>,
) -> Result<MeasureSet, RenderError>
{
    match (left, right) {
        | (MeasureSet::Frontier(left), MeasureSet::Frontier(right)) => {
            let mut combined = left;
            combined
                .try_reserve(right.len())
                .map_err(|_error| RenderError::AllocationFailed {
                    site: crate::error::RenderAllocationSite::Frontier,
                })?;
            combined.extend(right);
            Ok(MeasureSet::Frontier(combined))
        },
        | (MeasureSet::Frontier(frontier), MeasureSet::Tainted(promise))
        | (MeasureSet::Tainted(promise), MeasureSet::Frontier(frontier)) => {
            release(promise)?;
            Ok(MeasureSet::Frontier(frontier))
        },
        | (MeasureSet::Tainted(left), MeasureSet::Tainted(right)) => {
            release(right)?;
            Ok(MeasureSet::Tainted(left))
        },
    }
}

/// Returns the first measure from a set when it is ready.
///
/// # Specification
/// - requires: the set is valid.
/// - ensures: a frontier exposes its least-cost measure and a ready promise its
///   retained one.
/// - provides: the least-cost fallback seed; [`first::Absent::Empty`] for an
///   empty frontier and [`first::Absent::Deferred`] for a promise not yet
///   forced.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the retained measure of a tainted frontier is the first
///   one, the one the release callback did not receive.
/// - witness: `taint::tests::taint_reports_discarded_frontier_measures`
#[inline]
pub(crate) fn first(set: &MeasureSet) -> Maybe<Measure, first::Absent>
{
    match *set {
        | MeasureSet::Frontier(ref frontier) => match frontier.first() {
            | Some(&measure) => Maybe::Present(measure),
            | None => Maybe::Absent(first::Absent::Empty),
        },
        | MeasureSet::Tainted(TaintPromise::Ready(measure)) => Maybe::Present(measure),
        | MeasureSet::Tainted(TaintPromise::Deferred { .. }) => {
            Maybe::Absent(first::Absent::Deferred)
        },
    }
}

#[cfg(test)]
mod tests
{
    use super::*;
    use crate::limits::RenderLimits;
    use crate::limits::RenderMeter;
    use crate::measure::LayoutCost;
    use crate::plan::PlanArena;
    use crate::plan::PlanNode;
    use crate::units::Column;
    use crate::units::OutputBytes;

    /// A zero-cost measure ending at `column`, over a fresh empty plan.
    ///
    /// # Specification
    /// trivial.
    fn measure(
        plans: &mut PlanArena,
        meter: &mut RenderMeter,
        column: Column,
    ) -> Measure
    {
        let plan = plans.alloc(PlanNode::Empty, meter).unwrap();
        Measure {
            last_column: column,
            cost: LayoutCost::zero(),
            plan,
            output_bytes: OutputBytes::from(0u64),
        }
    }

    /// Taint keeps the first candidate and reports every discarded candidate.
    #[test]
    fn taint_reports_discarded_frontier_measures()
    {
        let mut plans = PlanArena::new();
        let mut meter = RenderMeter::new(RenderLimits::default());
        let first_measure = measure(&mut plans, &mut meter, Column::from(1u32));
        let second_measure = measure(&mut plans, &mut meter, Column::from(2u32));
        let mut discarded = Vec::new();
        let result = taint(
            MeasureSet::Frontier(alloc::vec![first_measure, second_measure]),
            |measure| {
                discarded.push(measure.plan);
                Ok(())
            },
        )
        .unwrap();
        assert_eq!(first(&result), Maybe::Present(first_measure));
        assert_eq!(discarded, alloc::vec![second_measure.plan]);
    }

    /// Taint merging keeps a frontier and releases a discarded ready promise.
    #[test]
    fn merge_frontier_wins_over_ready_taint()
    {
        let mut plans = PlanArena::new();
        let mut meter = RenderMeter::new(RenderLimits::default());
        let frontier_measure = measure(&mut plans, &mut meter, Column::from(1u32));
        let tainted_measure = measure(&mut plans, &mut meter, Column::from(2u32));
        let mut discarded = Vec::new();
        let result = merge(
            MeasureSet::Frontier(alloc::vec![frontier_measure]),
            MeasureSet::Tainted(TaintPromise::Ready(tainted_measure)),
            |promise| {
                if let TaintPromise::Ready(measure) = promise {
                    discarded.push(measure.plan);
                }
                Ok(())
            },
        )
        .unwrap();
        assert!(
            matches!(result, MeasureSet::Frontier(ref frontier) if frontier.as_slice() == [frontier_measure]),
            "the frontier is kept whole"
        );
        assert_eq!(discarded, alloc::vec![tainted_measure.plan]);
    }
}
