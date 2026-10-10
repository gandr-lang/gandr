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
/// - requires: all measures and promises belong to the current resolution
///   context.
/// - ensures: the variants distinguish a finite frontier, possibly empty, from
///   one exact tainted promise; the resolver normalizes retained frontiers.
/// - provides: the intermediate and normalized results of the resolution
///   algebra.
/// - panics: none.
/// - executable: none — the variant carrier has no invocation boundary; taint,
///   merge, projection and resolver normalization carry executable predicates.
///
/// # Adequacy
/// - hypothesis: L3 — empty and multi-entry frontiers, ready and deferred
///   promises, both mixed merge orders and a callback failure expose exact
///   retained measures, full sequence order, released values and the first
///   error. Reversing bias, losing a context, dropping a boundary entry or
///   continuing after refusal changes those observations. Predicates retain
///   only bounded summaries; witnesses observe complete callback traces without
///   replaying callbacks.
/// - witness: `taint::tests::taint_and_merge_preserve_bias_order_context_and_first_failure`
#[derive(Clone, Debug)]
pub(crate) enum MeasureSet
{
    /// A frontier, normalized by the resolver before Pareto selection.
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
/// - executable: none — this promise is a data carrier; construction, selection
///   and forcing are its executable boundaries.
///
/// # Adequacy
/// - hypothesis: L3 — empty and multi-entry frontiers, ready and deferred
///   promises, both mixed merge orders and a callback failure expose exact
///   retained measures, full sequence order, released values and the first
///   error. Reversing bias, losing a context, dropping a boundary entry or
///   continuing after refusal changes those observations. Predicates retain
///   only bounded summaries; witnesses observe complete callback traces without
///   replaying callbacks.
/// - witness: `taint::tests::taint_and_merge_preserve_bias_order_context_and_first_failure`
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
/// - hypothesis: L3 — empty and multi-entry frontiers, ready and deferred
///   promises, both mixed merge orders and a callback failure expose exact
///   retained measures, full sequence order, released values and the first
///   error. Reversing bias, losing a context, dropping a boundary entry or
///   continuing after refusal changes those observations. Predicates retain
///   only bounded summaries; witnesses observe complete callback traces without
///   replaying callbacks.
/// - witness: `taint::tests::taint_and_merge_preserve_bias_order_context_and_first_failure`
#[anodized::spec(
    captures: before = match set { MeasureSet::Frontier(ref frontier) => (frontier.first().copied().map(TaintPromise::Ready), frontier.len() > 1), MeasureSet::Tainted(promise) => (Some(promise), false) },
    ensures: |ret| ret.as_ref().map_or_else(|_error| before.1,
        |set| match *set { MeasureSet::Frontier(ref frontier) => before.0.is_none()
            && frontier.is_empty(), MeasureSet::Tainted(promise) => before.0 == Some(promise) })
)]
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
/// - hypothesis: L3 — empty and multi-entry frontiers, ready and deferred
///   promises, both mixed merge orders and a callback failure expose exact
///   retained measures, full sequence order, released values and the first
///   error. Reversing bias, losing a context, dropping a boundary entry or
///   continuing after refusal changes those observations. Predicates retain
///   only bounded summaries; witnesses observe complete callback traces without
///   replaying callbacks.
/// - witness: `taint::tests::taint_and_merge_preserve_bias_order_context_and_first_failure`
#[anodized::spec(
    ensures: |ret| matches!(ret, MeasureSet::Tainted(TaintPromise::Deferred { doc: actual_doc, column: actual_column, indentation: actual_indentation }) if actual_doc == doc
            && actual_column == column
            && actual_indentation == indentation)
)]
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
/// - hypothesis: L3 — empty and multi-entry frontiers, ready and deferred
///   promises, both mixed merge orders and a callback failure expose exact
///   retained measures, full sequence order, released values and the first
///   error. Reversing bias, losing a context, dropping a boundary entry or
///   continuing after refusal changes those observations. Predicates retain
///   only bounded summaries; witnesses observe complete callback traces without
///   replaying callbacks.
/// - witness: `taint::tests::taint_and_merge_preserve_bias_order_context_and_first_failure`
#[anodized::spec(
    captures: before = (match left { MeasureSet::Frontier(ref frontier) => (frontier.len(), frontier.first().copied(), frontier.last().copied(), None), MeasureSet::Tainted(promise) => (0, None, None, Some(promise)) }, match right { MeasureSet::Frontier(ref frontier) => (frontier.len(), frontier.first().copied(), frontier.last().copied(), None), MeasureSet::Tainted(promise) => (0, None, None, Some(promise)) }),
    ensures: |ret| ret.as_ref().map_or_else(|error| before.0.3.is_some() || before.1.3.is_some() || *error == RenderError::AllocationFailed { site: crate::error::RenderAllocationSite::Frontier },
        |set| match (before.0.3, before.1.3) { (None, None) => matches!(*set, MeasureSet::Frontier(ref frontier) if before.0.0.checked_add(before.1.0) == Some(frontier.len())
            && (before.0.0 == 0 || (frontier.first() == before.0.1.as_ref()
            && frontier.get(before.0.0.saturating_sub(1)) == before.0.2.as_ref()))
            && (before.1.0 == 0 || (frontier.get(before.0.0) == before.1.1.as_ref()
            && frontier.last() == before.1.2.as_ref()))), (None, Some(_)) => matches!(*set, MeasureSet::Frontier(ref frontier) if frontier.len() == before.0.0
            && frontier.first() == before.0.1.as_ref()
            && frontier.last() == before.0.2.as_ref()), (Some(_), None) => matches!(*set, MeasureSet::Frontier(ref frontier) if frontier.len() == before.1.0
            && frontier.first() == before.1.1.as_ref()
            && frontier.last() == before.1.2.as_ref()), (Some(left), Some(_)) => matches!(*set, MeasureSet::Tainted(actual) if left == actual) })
)]
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
/// - hypothesis: L3 — empty and multi-entry frontiers, ready and deferred
///   promises, both mixed merge orders and a callback failure expose exact
///   retained measures, full sequence order, released values and the first
///   error. Reversing bias, losing a context, dropping a boundary entry or
///   continuing after refusal changes those observations. Predicates retain
///   only bounded summaries; witnesses observe complete callback traces without
///   replaying callbacks.
/// - witness: `taint::tests::taint_and_merge_preserve_bias_order_context_and_first_failure`
#[anodized::spec(
    ensures: |ret| ret == match *set { MeasureSet::Frontier(ref frontier) => frontier.first().copied().map_or(Maybe::Absent(first::Absent::Empty), Maybe::Present), MeasureSet::Tainted(TaintPromise::Ready(measure)) => Maybe::Present(measure), MeasureSet::Tainted(TaintPromise::Deferred { .. }) => Maybe::Absent(first::Absent::Deferred) }
)]
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
    /// - requires: the caller supplies the test plan arena and its owning
    ///   meter.
    /// - ensures: the result ends at `column`, has zero cost and bytes, and
    ///   owns a live empty plan.
    /// - provides: distinct valid plan identities for callback and selection
    ///   witnesses.
    /// - panics: when the test allocation or budget refuses.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty and multi-entry frontiers, ready and deferred
    ///   promises, both mixed merge orders and a callback failure expose exact
    ///   retained measures, full sequence order, released values and the first
    ///   error. Reversing bias, losing a context, dropping a boundary entry or
    ///   continuing after refusal changes those observations. Predicates retain
    ///   only bounded summaries; witnesses observe complete callback traces
    ///   without replaying callbacks.
    /// - witness: `taint::tests::taint_and_merge_preserve_bias_order_context_and_first_failure`
    #[anodized::spec(
        ensures: |ret| ret.last_column == column
                && ret.cost == LayoutCost::zero()
                && u64::from(ret.output_bytes) == 0
                && plans.get(ret.plan) == Maybe::Present(PlanNode::Empty)
    )]
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

    /// Selection preserves full order and context, and a refused release stops
    /// the callback trace.
    #[test]
    fn taint_and_merge_preserve_bias_order_context_and_first_failure()
    {
        let mut plans = PlanArena::new();
        let mut meter = RenderMeter::new(RenderLimits::default());
        let a = measure(&mut plans, &mut meter, Column::from(1_u32));
        let b = measure(&mut plans, &mut meter, Column::from(2_u32));
        let c = measure(&mut plans, &mut meter, Column::from(3_u32));
        let d = measure(&mut plans, &mut meter, Column::from(4_u32));
        let failure = || RenderError::Invariant {
            invariant: crate::error::RenderInvariant::PlanIdentity,
        };
        let empty = taint(MeasureSet::Frontier(Vec::new()), |_| {
            panic!("empty frontier releases nothing")
        })
        .expect("empty taint");
        assert!(matches!(empty, MeasureSet::Frontier(ref entries) if entries.is_empty()));
        assert_eq!(first(&empty), Maybe::Absent(first::Absent::Empty));
        let singleton = taint(MeasureSet::Frontier(alloc::vec![a]), |_| {
            panic!("retained measure is not released")
        })
        .expect("singleton taint");
        assert!(
            matches!(singleton, MeasureSet::Tainted(TaintPromise::Ready(actual)) if actual == a)
        );
        let mut released = Vec::new();
        let result = taint(MeasureSet::Frontier(alloc::vec![a, b, c, d]), |value| {
            released.push(value);
            Ok(())
        })
        .expect("frontier taint");
        assert_eq!(first(&result), Maybe::Present(a));
        assert_eq!(released.as_slice(), [b, c, d].as_slice());
        released.clear();
        let refused = taint(MeasureSet::Frontier(alloc::vec![a, b, c, d]), |value| {
            released.push(value);
            if value == c { Err(failure()) } else { Ok(()) }
        });
        assert!(matches!(refused, Err(error) if error == failure()));
        assert_eq!(released.as_slice(), [b, c].as_slice());
        let left_deferred = TaintPromise::Deferred {
            doc: NodeId::from(7_u32),
            column: Column::from(11_u32),
            indentation: Indentation::from(13_u32),
        };
        let right_deferred = TaintPromise::Deferred {
            doc: NodeId::from(7_u32),
            column: Column::from(17_u32),
            indentation: Indentation::from(19_u32),
        };
        let deferred_set = deferred(
            NodeId::from(7_u32),
            Column::from(11_u32),
            Indentation::from(13_u32),
        );
        assert!(matches!(deferred_set, MeasureSet::Tainted(actual) if actual == left_deferred));
        assert_eq!(first(&deferred_set), Maybe::Absent(first::Absent::Deferred));
        for promise in [TaintPromise::Ready(a), left_deferred] {
            let result = taint(MeasureSet::Tainted(promise), |_| {
                panic!("existing promise is not released")
            })
            .expect("retained promise");
            assert!(matches!(result, MeasureSet::Tainted(actual) if actual == promise));
        }
        let result = merge(
            MeasureSet::Frontier(alloc::vec![a, b]),
            MeasureSet::Frontier(alloc::vec![c, d]),
            |_| panic!("frontier concatenation releases nothing"),
        )
        .expect("frontier merge");
        assert!(
            matches!(result, MeasureSet::Frontier(ref entries) if entries.as_slice() == [a, b, c, d].as_slice())
        );
        for (left, right) in [(Vec::new(), alloc::vec![a]), (alloc::vec![a], Vec::new())] {
            let result = merge(
                MeasureSet::Frontier(left),
                MeasureSet::Frontier(right),
                |_| panic!("empty join releases nothing"),
            )
            .expect("empty join");
            assert!(
                matches!(result, MeasureSet::Frontier(ref entries) if entries.as_slice() == [a].as_slice())
            );
        }
        for promise in [TaintPromise::Ready(c), right_deferred] {
            for frontier_first in [true, false] {
                let frontier = MeasureSet::Frontier(alloc::vec![a, b]);
                let tainted = MeasureSet::Tainted(promise);
                let (left, right) = if frontier_first {
                    (frontier, tainted)
                }
                else {
                    (tainted, frontier)
                };
                let mut discarded = Vec::new();
                let result = merge(left, right, |value| {
                    discarded.push(value);
                    Ok(())
                })
                .expect("frontier wins");
                assert!(
                    matches!(result, MeasureSet::Frontier(ref entries) if entries.as_slice() == [a, b].as_slice())
                );
                assert_eq!(discarded.as_slice(), [promise].as_slice());
                let frontier = MeasureSet::Frontier(alloc::vec![a, b]);
                let tainted = MeasureSet::Tainted(promise);
                let (left, right) = if frontier_first {
                    (frontier, tainted)
                }
                else {
                    (tainted, frontier)
                };
                discarded.clear();
                let refused = merge(left, right, |value| {
                    discarded.push(value);
                    Err(failure())
                });
                assert!(matches!(refused, Err(error) if error == failure()));
                assert_eq!(discarded.as_slice(), [promise].as_slice());
            }
        }
        for left in [TaintPromise::Ready(a), left_deferred] {
            for right in [TaintPromise::Ready(d), right_deferred] {
                let mut discarded = Vec::new();
                let result = merge(
                    MeasureSet::Tainted(left),
                    MeasureSet::Tainted(right),
                    |value| {
                        discarded.push(value);
                        Ok(())
                    },
                )
                .expect("left promise wins");
                assert!(matches!(result, MeasureSet::Tainted(actual) if actual == left));
                assert_eq!(discarded.as_slice(), [right].as_slice());
                discarded.clear();
                let refused = merge(
                    MeasureSet::Tainted(left),
                    MeasureSet::Tainted(right),
                    |value| {
                        discarded.push(value);
                        Err(failure())
                    },
                );
                assert!(matches!(refused, Err(error) if error == failure()));
                assert_eq!(discarded.as_slice(), [right].as_slice());
            }
        }
    }
}
