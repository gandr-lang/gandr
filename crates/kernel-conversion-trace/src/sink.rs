//! The sink: one interface, a null implementation and a recording one.

use alloc::vec::Vec;

use anodized::spec;

use crate::decision::ConversionDecision;

/// Whether a [`TraceSink`] implementation ever retains a decision.
///
/// Read at compile time through [`TraceSink::ACTIVITY`], the same discipline
/// the check-memo seam takes, and for the same reason: a conversion path
/// instantiated at [`NullSink`] should not build the decision values it is
/// about to discard. A consumer matches on it directly —
/// `matches!(S::ACTIVITY, SinkActivity::Inactive)` — so the guard stays a
/// constant the optimizer folds away and no boolean crosses an interface.
///
/// # Specification
/// - requires: nothing.
/// - ensures: an implementation that retains nothing declares `Inactive` and
///   one that retains declares `Active`, so a consumer branching on the
///   constant skips decision construction exactly when the decision would be
///   discarded.
/// - provides: the compile-time guard separating an inactive sink from one that
///   retains decisions.
/// - panics: none.
/// - executable: none — this law relates an implementation's associated
///   constant to its external recording behavior, not to one enum value.
///
/// # Adequacy
/// - hypothesis: L2 — four layered-term cases compare verdicts and exact
///   retained counts at both shipped implementations. They distinguish a
///   suppressed active path and nonzero null counts. They do not measure
///   optimizer elimination of decision construction.
/// - witness: `differential::differential::the_exercised_recording_paths_are_asserted_rather_than_reported`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum SinkActivity
{
    /// The sink retains what it is given, so the consumer builds decisions.
    Active,
    /// The sink retains nothing, so the consumer may skip the whole
    /// interaction — decision construction included.
    Inactive,
}

/// How many decisions a sink has retained.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DecisionCount(usize);

impl From<usize> for DecisionCount
{
    /// The count of `value` retained decisions.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: usize) -> Self
    {
        Self(value)
    }
}

impl From<DecisionCount> for usize
{
    /// How many decisions `value` counts.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: DecisionCount) -> Self
    {
        value.0
    }
}

/// A statically dispatched receiver of conversion decisions.
///
/// # Specification
/// - requires: the consumer records decisions in the order the strategy made
///   them, since a replay reads them in that order.
/// - ensures: recording never changes a verdict — an implementation observes,
///   and the conversion path is the same function at either instantiation.
/// - provides: the emit operation with storage and policy owned by the sink.
/// - panics: none.
/// - executable: none — verdict invariance relates two external runs, and trait
///   instrumentation changes the required implementor-method interface.
///
/// # Adequacy
/// - hypothesis: L2 — four finite layered-term cases run one strategy at both
///   shipped sinks, comparing exact verdicts and retained counts. Shared heads,
///   distinct atoms and asymmetric layers distinguish interference and a
///   recording path that was never exercised; arbitrary sinks are not covered.
/// - witness: `differential::differential::recording_does_not_move_the_verdict`
/// - witness: `differential::differential::the_exercised_recording_paths_are_asserted_rather_than_reported`
pub trait TraceSink<Id>
{
    /// Whether this implementation ever retains a decision, known at compile
    /// time.
    ///
    /// # Specification
    /// - requires: the implementation declares `Inactive` only when
    ///   [`TraceSink::record`] retains nothing.
    /// - ensures: the value is a constant, so a consumer's branch on it folds
    ///   away at monomorphization.
    /// - provides: the discriminator guarding decision construction.
    /// - panics: none.
    /// - executable: none — the macro does not accept associated constants;
    ///   consistency with retention is an obligation on the implementation.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — four valid comparisons observe zero retained
    ///   decisions with the null sink and exact nonzero counts with the log.
    ///   This separates a suppressed active path, not generated-code costs.
    /// - witness: `differential::differential::the_exercised_recording_paths_are_asserted_rather_than_reported`
    const ACTIVITY: SinkActivity;

    /// Record one decision without imposing a storage policy on the caller.
    ///
    /// # Specification
    /// - requires: the caller records decisions in the order the strategy made
    ///   them, since a replay reads them in that order.
    /// - ensures: an implementation either retains the decision — and reports
    ///   it through [`TraceSink::recorded_count`] and its own reader — or
    ///   retains nothing, consistently with its declared
    ///   [`TraceSink::ACTIVITY`]; either way the caller's verdict is unchanged.
    /// - provides: the storage-independent emit operation.
    /// - panics: none.
    /// - executable: none — instrumenting this declaration generates additional
    ///   required trait methods; the shipped bodies carry predicates instead.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — both shipped implementations preserve the verdict on
    ///   four layered-term cases while exposing exact retained counts. L3 the
    ///   log preserves a mixed, repeated sequence element for element. These
    ///   observers separate dropped or reordered events, not every possible
    ///   implementation of the declaration.
    /// - witness: `differential::differential::recording_does_not_move_the_verdict`
    /// - witness: `sink::tests::a_trace_log_retains_every_decision_in_order`
    fn record(
        &mut self,
        decision: ConversionDecision<Id>,
    );

    /// How many decisions have been retained.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: counts every decision [`TraceSink::record`] retained, and
    ///   answers zero for an implementation declaring
    ///   [`SinkActivity::Inactive`].
    /// - provides: the projection that establishes which recording paths ran.
    /// - panics: none.
    /// - executable: none — a predicate on this declaration changes the
    ///   required trait-method interface; storage belongs to implementations.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty and populated logs expose exact counts, while
    ///   recording two decisions at the null sink leaves zero. These
    ///   distinguish constant answers, off-by-one counts and crossed
    ///   implementations for the shipped stores, not arbitrary downstream
    ///   implementations.
    /// - witness: `sink::tests::a_trace_log_retains_every_decision_in_order`
    /// - witness: `sink::tests::the_null_sink_retains_nothing`
    fn recorded_count(&self) -> DecisionCount;
}

/// The default sink: recording is compiled away at the call site.
///
/// Zero-sized, and every method is a constant, so a conversion path
/// instantiated here has no recording state and no dynamic dispatch to pay for.
///
/// # Specification
/// - requires: nothing.
/// - ensures: retains nothing it is given and reports a count of zero, which is
///   what makes it the sink-off side of the differential.
/// - provides: recording-free state for callers that do not request a trace.
/// - panics: none.
/// - executable: none — the unit representation has no stored decisions; the
///   record and count methods carry the operational predicates.
///
/// # Adequacy
/// - hypothesis: L0 — the unit representation has no owned recording state. L3
///   — exact zero counts before and after two distinct decisions separate a
///   nonzero reported count. L2 — the finite workload observes the same
///   verdicts at both sinks; hidden global state is outside this observer.
/// - witness: `sink::tests::the_null_sink_retains_nothing`
/// - witness: `differential::differential::the_exercised_recording_paths_are_asserted_rather_than_reported`
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct NullSink;

impl<Id> TraceSink<Id> for NullSink
{
    /// Declares the sink-off side, so a consumer's guard folds away here.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: reports [`SinkActivity::Inactive`], consistently with a
    ///   `record` that retains nothing.
    /// - provides: the constant guarding the recording-free path.
    /// - panics: none.
    /// - executable: none — the macro does not accept associated constants.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the finite workload observes zero retained decisions
    ///   and unchanged verdicts at this instantiation. Generated-code cost is
    ///   not measured by these witnesses.
    /// - witness: `differential::differential::recording_does_not_move_the_verdict`
    /// - witness: `differential::differential::the_exercised_recording_paths_are_asserted_rather_than_reported`
    const ACTIVITY: SinkActivity = SinkActivity::Inactive;

    /// Discards the decision.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: retains nothing, so the reported count stays zero however
    ///   many decisions arrive.
    /// - provides: the sink-off recording path, which is no path at all.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surface is whether the argument is
    ///   retained; recorded decisions are followed by an exact zero-count
    ///   assertion, which a retaining body cannot pass.
    /// - witness: `sink::tests::the_null_sink_retains_nothing`
    #[inline]
    #[spec(ensures: usize::from(<Self as TraceSink<Id>>::recorded_count(self)) == 0)]
    fn record(
        &mut self,
        _decision: ConversionDecision<Id>,
    )
    {
    }

    /// Reports the constant zero.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: answers zero unconditionally, since nothing is retained.
    /// - provides: the sink-off half of the exercised-path assertion.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one value, asserted exactly after decisions have been
    ///   handed to the sink rather than before.
    /// - witness: `sink::tests::the_null_sink_retains_nothing`
    #[inline]
    #[spec(ensures: |ret| usize::from(ret) == 0)]
    fn recorded_count(&self) -> DecisionCount
    {
        DecisionCount::from(0)
    }
}

/// The recording sink: decisions retained in the order they were made.
///
/// This is the sink a conversion run emits replay evidence through, and the one
/// a differential counts through — a suite that only ever instantiates
/// [`NullSink`] can be green while reaching no recording code at all.
///
/// Storage is a flat vector. A trace is a session artifact whose lifetime is
/// the consumer's, so there is no eviction policy and no persistence here.
///
/// # Specification
/// - requires: the consumer records decisions in the order the strategy made
///   them, and keeps the log within the scope in which its identifiers resolve.
/// - ensures: retains every decision it is given, once, in recording order, and
///   reports that many.
/// - provides: the recorded replay input and the sink-on count projection.
/// - panics: none.
/// - executable: none — the input event history is external to the stored
///   sequence, and data-item expansion does not check construction.
///
/// # Adequacy
/// - hypothesis: L3 — empty and mixed logs retain every event in order,
///   including every kind, side changes, position boundaries and a repeated
///   decision. Exact counts after each append distinguish loss, duplication,
///   deduplication and reordering. L2 replay independently checks the bounded
///   strategy workload, not arbitrary consumer traces.
/// - witness: `sink::tests::a_trace_log_retains_every_decision_in_order`
/// - witness: `differential::differential::the_kernel_replays_the_trace_without_searching`
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TraceLog<Id>
{
    /// The decisions, in the order they were recorded.
    decisions: Vec<ConversionDecision<Id>>,
}

impl<Id> TraceLog<Id>
{
    /// A log holding no decisions.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new() -> Self
    {
        Self {
            decisions: Vec::new(),
        }
    }

    /// The recorded decisions, in the order they were made.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: yields every decision [`TraceSink::record`] was given, once,
    ///   in recording order.
    /// - provides: the ordered replay input without consuming the log.
    /// - panics: none.
    /// - executable: none — expansion places the opaque return type in a
    ///   closure signature, which Rust rejects; consuming it would also change
    ///   the value returned to the caller.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty, non-Copy-identifier and mixed logs distinguish
    ///   early exhaustion, reordering, payload loss and extra output through
    ///   exact iteration to exhaustion. Reading leaves the retained count
    ///   unchanged, and exhaustion yields no later decision.
    /// - witness: `sink::tests::a_trace_log_retains_every_decision_in_order`
    /// - witness: `sink::tests::iteration_preserves_noncopy_payloads_and_exhaustion`
    #[inline]
    pub fn decisions(&self) -> impl Iterator<Item = &ConversionDecision<Id>>
    {
        self.decisions.iter()
    }
}

impl<Id> TraceSink<Id> for TraceLog<Id>
{
    /// Declares the sink-on side, so a consumer builds the decisions it emits.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: reports [`SinkActivity::Active`], consistently with a
    ///   `record` that retains.
    /// - provides: the constant guarding decision construction for the log.
    /// - panics: none.
    /// - executable: none — the macro does not accept associated constants.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — four valid comparisons expose exact nonzero retained
    ///   counts, distinguishing a guard that suppresses the recording path.
    ///   This witnesses the shipped log, not optimizer behavior.
    /// - witness: `differential::differential::the_exercised_recording_paths_are_asserted_rather_than_reported`
    const ACTIVITY: SinkActivity = SinkActivity::Active;

    /// Appends the decision to the log.
    ///
    /// # Specification
    /// - requires: nothing beyond the trait's ordering requirement.
    /// - ensures: the decision becomes the last element of the log, and no
    ///   earlier element moves.
    /// - provides: the recording path a differential counts its exercised route
    ///   through.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surfaces are retention and position; a
    ///   recorded sequence is compared element for element against the sequence
    ///   handed in, so an append that dropped, duplicated or reordered a
    ///   decision is separated.
    /// - witness: `sink::tests::a_trace_log_retains_every_decision_in_order`
    #[inline]
    #[spec(captures: [entry_count = self.decisions.len()], ensures: entry_count.checked_add(1) == Some(self.decisions.len()))]
    fn record(
        &mut self,
        decision: ConversionDecision<Id>,
    )
    {
        self.decisions.push(decision);
    }

    /// Reports how many decisions the log holds.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: answers the number of decisions recorded so far, which is
    ///   zero for a fresh log.
    /// - provides: the sink-on half of the exercised-path assertion.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the count is asserted exactly, at zero on a fresh log
    ///   and at the number handed in afterwards, so an off-by-one or a constant
    ///   answer is separated.
    /// - witness: `sink::tests::a_trace_log_retains_every_decision_in_order`
    /// - witness: `differential::differential::the_exercised_recording_paths_are_asserted_rather_than_reported`
    #[inline]
    #[spec(ensures: |ret| usize::from(ret) == self.decisions.len())]
    fn recorded_count(&self) -> DecisionCount
    {
        DecisionCount::from(self.decisions.len())
    }
}

#[cfg(test)]
mod tests
{
    use super::DecisionCount;
    use super::NullSink;
    use super::TraceLog;
    use super::TraceSink;
    use crate::decision::ConversionDecision;
    use crate::decision::ConversionSide;
    use crate::decision::SubgoalPosition;

    /// An identifier standing in for a consumer's own node identifier.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct TestId(u8);

    #[test]
    fn the_null_sink_retains_nothing()
    {
        let mut sink = NullSink;
        assert_eq!(
            DecisionCount::from(0),
            TraceSink::<TestId>::recorded_count(&sink),
        );
        sink.record(ConversionDecision::Force { thunk: TestId(1) });
        sink.record(ConversionDecision::ReduceLeft { redex: TestId(2) });
        assert_eq!(
            DecisionCount::from(0),
            TraceSink::<TestId>::recorded_count(&sink),
            "the null sink forgets what it was told, which is what makes it the sink-off side"
        );
    }

    #[test]
    fn a_trace_log_retains_every_decision_in_order()
    {
        let mut log: TraceLog<TestId> = TraceLog::new();
        assert_eq!(
            DecisionCount::from(0),
            log.recorded_count(),
            "a fresh log holds nothing"
        );
        let recorded = [
            ConversionDecision::ReduceLeft { redex: TestId(1) },
            ConversionDecision::ReduceRight { redex: TestId(2) },
            ConversionDecision::ConstShortcut {
                constant: TestId(3),
            },
            ConversionDecision::Unfold {
                constant: TestId(4),
            },
            ConversionDecision::Postpone {
                constant: TestId(4),
            },
            ConversionDecision::Freeze {
                constant: TestId(3),
                side: ConversionSide::Left,
            },
            ConversionDecision::Freeze {
                constant: TestId(3),
                side: ConversionSide::Right,
            },
            ConversionDecision::EtaExpand {
                side: ConversionSide::Right,
                variable: TestId(5),
            },
            ConversionDecision::Force { thunk: TestId(6) },
            ConversionDecision::ComparedShared {
                left: TestId(1),
                right: TestId(2),
            },
            ConversionDecision::NegativeSubgoal {
                position: SubgoalPosition::from(0),
            },
            ConversionDecision::NegativeSubgoal {
                position: SubgoalPosition::from(1),
            },
            ConversionDecision::NegativeSubgoal {
                position: SubgoalPosition::from(u32::MAX),
            },
            ConversionDecision::ReduceLeft { redex: TestId(1) },
        ];
        for (index, decision) in recorded.into_iter().enumerate() {
            log.record(decision);
            assert_eq!(
                DecisionCount::from(index.checked_add(1).expect("bounded event sequence")),
                log.recorded_count(),
            );
        }
        assert_eq!(
            DecisionCount::from(recorded.len()),
            log.recorded_count(),
            "every event, including the repeat, is retained"
        );
        let held: alloc::vec::Vec<ConversionDecision<TestId>> = log.decisions().copied().collect();
        assert_eq!(
            recorded.as_slice(),
            held.as_slice(),
            "in the order they were made, side and all"
        );
    }

    #[test]
    fn iteration_preserves_noncopy_payloads_and_exhaustion()
    {
        let mut log: TraceLog<alloc::string::String> = TraceLog::new();
        assert_eq!(DecisionCount::from(0), log.recorded_count());
        assert!(log.decisions().next().is_none());
        log.record(ConversionDecision::Force {
            thunk: alloc::string::String::from("first"),
        });
        log.record(ConversionDecision::Force {
            thunk: alloc::string::String::from("second"),
        });
        let mut decisions = log.decisions();
        assert!(
            matches!(decisions.next(), Some(ConversionDecision::Force { thunk }) if thunk == "first")
        );
        assert!(
            matches!(decisions.next(), Some(ConversionDecision::Force { thunk }) if thunk == "second")
        );
        assert!(decisions.next().is_none());
        assert!(decisions.next().is_none());
        assert_eq!(DecisionCount::from(2), log.recorded_count());
    }
}
