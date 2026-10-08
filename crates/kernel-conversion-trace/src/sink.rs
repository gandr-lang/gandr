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
/// - provides: the compile-time guard that makes sink-off conversion the same
///   function at a different type parameter rather than a second
///   implementation. This stays prose: the claim relates each implementation's
///   declared constant to what its `record` retains, and a data-item `#[spec]`
///   states an invariant of one value that the pinned expansion never checks at
///   construction.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L0 — the two answers are variants rather than a `bool`, so a
///   consumer cannot read the constant as anything but a sink activity; the
///   residue is that the two shipped implementations declare opposite values,
///   asserted pointwise by exact variant.
/// - witness: `sink::tests::the_two_implementations_declare_opposite_activities`
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
/// - provides: the emit half of the trace seam, with storage and policy in the
///   implementation rather than in the conversion path. This stays prose:
///   verdict invariance is a law over two runs, and a clause on a trait
///   declaration requires the trait itself to carry `#[spec]`, which turns each
///   declaration into a wrapper over a generated required method and changes
///   what an implementor implements.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the seam's whole claim is that recording is an
///   observation, so the oracle is the differential: one strategy instantiated
///   at both shipped implementations, verdict for verdict, with the exercised
///   recording path asserted rather than reported.
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
    /// - provides: the sink-off/sink-on discriminator a conversion path guards
    ///   decision construction with. This stays prose: the pinned macro refuses
    ///   an associated constant, and the requirement is an obligation on the
    ///   implementation's `record`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L0 — the constant is a variant rather than a `bool`; the
    ///   residue is that the shipped implementations disagree, asserted by
    ///   exact variant at both instantiations.
    /// - witness: `sink::tests::the_two_implementations_declare_opposite_activities`
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
    /// - provides: the emit operation of the seam. This stays prose: the
    ///   declaration has no body to instrument, and a clause here requires the
    ///   trait itself to carry `#[spec]`, which turns the declaration into a
    ///   wrapper over a generated required method and changes what an
    ///   implementor implements. The two shipped implementations carry their
    ///   own clauses.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L0 — the declaration fixes the shape and has no behaviour
    ///   of its own; every claim above is a claim about an implementation.
    /// - declaration-only: the two shipped implementations are witnessed at
    ///   their own impl items, and the declaration has no body a mutant could
    ///   change.
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
    /// - provides: the exercised-path projection a differential asserts on, so
    ///   a green run cannot have skipped the recording path. This stays prose
    ///   for the same reason as [`TraceSink::record`]: a clause on the
    ///   declaration would change what an implementor implements, and both
    ///   shipped implementations carry the clause instead.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L0 — the declaration fixes the shape and has no behaviour
    ///   of its own.
    /// - declaration-only: the two shipped implementations are witnessed at
    ///   their own impl items, and the declaration has no body a mutant could
    ///   change.
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
/// - provides: the instantiation a conversion path takes when no trace is
///   wanted, at no representation cost. This stays prose: a data-item `#[spec]`
///   states an invariant of one value, which the pinned expansion never checks
///   at construction; retention and count are clauses on the two methods below.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surface is whether anything is retained at
///   all, and the class is finite: decisions are recorded and the count is
///   asserted to be exactly zero, so an implementation that quietly kept them
///   is separated.
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
    /// - provides: the constant a conversion path skips decision construction
    ///   on. This stays prose: the pinned macro refuses an associated constant.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one value, asserted by exact variant against the
    ///   recording sink's opposite one.
    /// - witness: `sink::tests::the_two_implementations_declare_opposite_activities`
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
/// - provides: the replay input, and the sink-on side of the differential. This
///   stays prose: the ordering requirement is an obligation on the consumer,
///   and a data-item `#[spec]` states an invariant of one value that the pinned
///   expansion never checks at construction; retention and count are clauses on
///   the methods below.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surfaces are retention, order and count, and
///   the class is finite: a recorded sequence is compared element for element
///   including a pair differing only in its side, and its length is asserted
///   exactly. The L2 rung above it is the replay, an external oracle sharing no
///   code with the strategy that produced the log.
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
    /// - provides: the replay input, and the projection a differential asserts
    ///   its exercised path through. This stays prose: a closure-form
    ///   postcondition cannot name the `impl Iterator` return type, and
    ///   counting the yielded decisions would consume the returned iterator.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 only — the decision surfaces are whether a decision is
    ///   retained at all and in what order, separated by a recorded sequence
    ///   whose every element and whose length are asserted exactly, including a
    ///   pair of decisions that differ only in their side.
    /// - witness: `sink::tests::a_trace_log_retains_every_decision_in_order`
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
    /// - provides: the constant a conversion path builds decision values on.
    ///   This stays prose: the pinned macro refuses an associated constant.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one value, asserted by exact variant against the null
    ///   sink's opposite one.
    /// - witness: `sink::tests::the_two_implementations_declare_opposite_activities`
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
    #[spec(captures: [entry_count = self.decisions.len()], ensures: self.decisions.len() == entry_count.saturating_add(1))]
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
    use super::SinkActivity;
    use super::TraceLog;
    use super::TraceSink;
    use crate::decision::ConversionDecision;
    use crate::decision::ConversionSide;

    /// An identifier standing in for a consumer's own node identifier.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct TestId(u8);

    #[test]
    fn the_two_implementations_declare_opposite_activities()
    {
        assert_eq!(
            SinkActivity::Inactive,
            <NullSink as TraceSink<TestId>>::ACTIVITY,
            "the null sink declares itself inactive so the consumer's branch is constant"
        );
        assert_eq!(
            SinkActivity::Active,
            <TraceLog<TestId> as TraceSink<TestId>>::ACTIVITY,
            "and the recording sink declares itself active, so the two are distinguishable at compile time"
        );
    }

    #[test]
    fn the_null_sink_retains_nothing()
    {
        let mut sink = NullSink;
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
            ConversionDecision::Freeze {
                constant: TestId(3),
                side: ConversionSide::Left,
            },
            // Same constant, other side: a vocabulary that dropped the side
            // would collapse these two into one decision.
            ConversionDecision::Freeze {
                constant: TestId(3),
                side: ConversionSide::Right,
            },
        ];
        for decision in recorded {
            log.record(decision);
        }
        assert_eq!(
            DecisionCount::from(4),
            log.recorded_count(),
            "four decisions were made and four were retained"
        );
        let held: alloc::vec::Vec<ConversionDecision<TestId>> = log.decisions().copied().collect();
        assert_eq!(
            recorded.as_slice(),
            held.as_slice(),
            "in the order they were made, side and all"
        );
    }

    #[test]
    fn the_nine_decision_kinds_are_distinct_values()
    {
        let kinds = [
            ConversionDecision::ReduceLeft { redex: TestId(0) },
            ConversionDecision::ReduceRight { redex: TestId(0) },
            ConversionDecision::ConstShortcut {
                constant: TestId(0),
            },
            ConversionDecision::Unfold {
                constant: TestId(0),
            },
            ConversionDecision::Postpone {
                constant: TestId(0),
            },
            ConversionDecision::Freeze {
                constant: TestId(0),
                side: ConversionSide::Left,
            },
            ConversionDecision::EtaExpand {
                side: ConversionSide::Left,
                variable: TestId(0),
            },
            ConversionDecision::Force { thunk: TestId(0) },
            ConversionDecision::ComparedShared {
                left: TestId(0),
                right: TestId(0),
            },
        ];
        let mut log: TraceLog<TestId> = TraceLog::new();
        for decision in kinds {
            log.record(decision);
        }
        assert_eq!(
            DecisionCount::from(9),
            log.recorded_count(),
            "the eight rows of the decision table name nine kinds, since unfold and postpone share a row"
        );
        // Every kind carries the same identifier, so any two that compared equal
        // would be indistinguishable to a replay reading the trace.
        for (first_index, first) in kinds.iter().enumerate() {
            for (second_index, second) in kinds.iter().enumerate() {
                assert_eq!(
                    first_index == second_index,
                    first == second,
                    "a decision kind equals only itself, even carrying identical identifiers"
                );
            }
        }
    }
}
