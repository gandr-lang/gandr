//! The sink-off/sink-on differential, and the replay the trace exists for.
//!
//! The workload is a miniature convertibility strategy over two chains of
//! definition layers, written once and generic in the sink. Three properties
//! are asserted.
//!
//! - **Recording does not move the verdict.** The strategy is the same function
//!   at [`NullSink`] and at [`TraceLog`], and the two instantiations agree
//!   verdict for verdict — including on the refusals.
//! - **The sink-off side holds no recording state.** Its decision count is
//!   asserted to be zero rather than reported, and the sink-on side's count is
//!   asserted exactly, so a green differential cannot have skipped the
//!   recording path.
//! - **Replay is search-free, and it is an external oracle.** A sequential
//!   rechecker consumes the recorded decisions in order, has at most one
//!   applicable rule at every step, and re-derives the verdict from the inputs.
//!   It shares no code with the strategy, so a strategy that recorded the wrong
//!   branch is refused rather than agreed with.
//!
//! One consequence of the vocabulary is pinned here: **the trace records that
//! two occurrences met, not that they agreed.** A refutation and a proof carry
//! the same final decision, and the verdict is recomputed by the replay from
//! the terms. So a trace is replay evidence and never an equality.
#[cfg(test)]
mod differential
{

    use gandr_kernel_conversion_trace::ConversionDecision;
    use gandr_kernel_conversion_trace::DecisionCount;
    use gandr_kernel_conversion_trace::NullSink;
    use gandr_kernel_conversion_trace::SinkActivity;
    use gandr_kernel_conversion_trace::TraceLog;
    use gandr_kernel_conversion_trace::TraceSink;

    /// The consumer's identifier: a definition head, a redex head, or an atom.
    ///
    /// One type, because the seam's identifier parameter is one type. What a
    /// given identifier names is read from the decision that carries it.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
    struct NodeName(u32);

    /// One side of a comparison: a stack of definition layers over an atom.
    ///
    /// The last layer is the head. Unfolding pops one layer; when the stack is
    /// empty the atom is exposed.
    #[derive(Clone, Debug, Eq, PartialEq)]
    struct Side
    {
        /// The definition layers, outermost last.
        layers: Vec<NodeName>,
        /// The head reached once every layer is unfolded.
        atom: NodeName,
    }

    /// The answer a comparison produces.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum Verdict
    {
        /// The two terms are convertible.
        Convertible,
        /// The two terms are not convertible.
        NotConvertible,
    }

    /// A trace the replay refuses.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum ReplayError
    {
        /// A decision named a constant that is not the head of the side it acts
        /// on.
        HeadMismatch,
        /// A reduction step arrived with no unfolding decision before it, or an
        /// unfolding decision arrived with one already pending.
        UnpairedUnfold,
        /// The comparison closed while a side still had layers to unfold.
        ClosedTooEarly,
        /// A decision arrived after the comparison had already closed.
        DecisionAfterClose,
        /// The trace ended without closing the comparison.
        NeverClosed,
        /// A decision kind this replay has no rule for.
        UnexpectedDecision,
    }

    /// The miniature convertibility strategy, generic in the sink.
    ///
    /// This is the function the differential compares against itself. Every
    /// recording is guarded on `Sink::ACTIVITY`, so the [`NullSink`]
    /// instantiation monomorphizes to the strategy this would be with no
    /// seam at all.
    ///
    /// # Specification
    /// - requires: `left` and `right` carry finite layer stacks, and `sink` is
    ///   the instantiation whose verdicts the differential compares.
    /// - ensures: answers `Convertible` exactly when the two sides expose the
    ///   same atom once every layer is unfolded, and hands the sink one
    ///   decision per step it took, in the order it took them.
    /// - provides: the one strategy both instantiations run, so the
    ///   differential compares a function against itself rather than against a
    ///   second implementation.
    /// - fails: never.
    /// - panics: none.
    fn convert<Sink>(
        left: &Side,
        right: &Side,
        sink: &mut Sink,
    ) -> Verdict
    where
        Sink: TraceSink<NodeName>,
    {
        let mut left_layers = left.layers.clone();
        let mut right_layers = right.layers.clone();
        loop {
            let heads = (left_layers.last().copied(), right_layers.last().copied());
            match heads {
                // Both sides head the same defined constant, so the comparison
                // closes on it without unrolling either side.
                | (Some(left_head), Some(right_head)) if left_head == right_head => {
                    record(sink, ConversionDecision::ConstShortcut {
                        constant: left_head,
                    });
                    let _popped = left_layers.pop();
                    let _popped = right_layers.pop();
                },
                // Otherwise unfold the left side if it has anything to unfold.
                | (Some(left_head), _) => {
                    record(sink, ConversionDecision::Unfold {
                        constant: left_head,
                    });
                    record(sink, ConversionDecision::ReduceLeft { redex: left_head });
                    let _popped = left_layers.pop();
                },
                | (None, Some(right_head)) => {
                    record(sink, ConversionDecision::Unfold {
                        constant: right_head,
                    });
                    record(sink, ConversionDecision::ReduceRight { redex: right_head });
                    let _popped = right_layers.pop();
                },
                // Both sides are down to their atoms: the comparison closes.
                | (None, None) => {
                    record(sink, ConversionDecision::ComparedShared {
                        left: left.atom,
                        right: right.atom,
                    });
                    return if left.atom == right.atom {
                        Verdict::Convertible
                    }
                    else {
                        Verdict::NotConvertible
                    };
                },
            }
        }
    }

    /// Records one decision, building it only when the sink is live.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: forwards `decision` to `sink` exactly when `Sink::ACTIVITY`
    ///   is `SinkActivity::Active`, and returns without touching the sink
    ///   otherwise, so the sink-off instantiation monomorphizes to the strategy
    ///   with no seam at all.
    /// - provides: the guarded emit every recording site in the strategy goes
    ///   through.
    /// - fails: never.
    /// - panics: none.
    fn record<Sink>(
        sink: &mut Sink,
        decision: ConversionDecision<NodeName>,
    ) where
        Sink: TraceSink<NodeName>,
    {
        if matches!(Sink::ACTIVITY, SinkActivity::Inactive) {
            return;
        }
        sink.record(decision);
    }

    /// The kernel's half: a sequential rechecker with no queue and no fairness.
    ///
    /// With the recorded side choices in hand there is at most one applicable
    /// rule at every step, so this reads the decisions in order and checks
    /// each against the terms. It shares no code with [`convert`], which is
    /// what makes it an external oracle rather than a second run of the
    /// same logic.
    ///
    /// # Specification
    /// - requires: `decisions` is the trace one `convert` run recorded for
    ///   `left` and `right`, in recording order.
    /// - ensures: `Ok(verdict)` re-derived from the atoms the trace closed on,
    ///   having checked every decision against the terms — a named constant
    ///   heads the side its decision acts on, a reduction follows its own
    ///   unfolding, and the comparison closes only once both layer stacks are
    ///   empty.
    /// - provides: the external oracle the differential holds `convert` to;
    ///   sharing no code with the strategy is what makes a wrongly recorded
    ///   branch refused rather than agreed with.
    /// - fails: `ReplayError::HeadMismatch` for a decision naming a constant
    ///   that does not head its side; `ReplayError::UnpairedUnfold` for a
    ///   reduction with no pending unfolding, or an unfolding with one already
    ///   pending; `ReplayError::ClosedTooEarly` when the close arrives with
    ///   layers left; `ReplayError::DecisionAfterClose` for a decision past the
    ///   close; `ReplayError::NeverClosed` when the trace ends unclosed;
    ///   `ReplayError::UnexpectedDecision` for a kind this replay has no rule
    ///   for.
    /// - panics: none.
    fn replay(
        left: &Side,
        right: &Side,
        decisions: &[ConversionDecision<NodeName>],
    ) -> Result<Verdict, ReplayError>
    {
        let mut left_layers = left.layers.clone();
        let mut right_layers = right.layers.clone();
        let mut pending: Option<NodeName> = None;
        let mut verdict: Option<Verdict> = None;
        for decision in decisions {
            if verdict.is_some() {
                return Err(ReplayError::DecisionAfterClose);
            }
            match *decision {
                | ConversionDecision::ConstShortcut { constant } => {
                    if pending.is_some() {
                        return Err(ReplayError::UnpairedUnfold);
                    }
                    if left_layers.last().copied() != Some(constant)
                        || right_layers.last().copied() != Some(constant)
                    {
                        return Err(ReplayError::HeadMismatch);
                    }
                    let _popped = left_layers.pop();
                    let _popped = right_layers.pop();
                },
                | ConversionDecision::Unfold { constant } => {
                    if pending.is_some() {
                        return Err(ReplayError::UnpairedUnfold);
                    }
                    pending = Some(constant);
                },
                | ConversionDecision::ReduceLeft { redex } => {
                    if pending != Some(redex) {
                        return Err(ReplayError::UnpairedUnfold);
                    }
                    if left_layers.last().copied() != Some(redex) {
                        return Err(ReplayError::HeadMismatch);
                    }
                    let _popped = left_layers.pop();
                    pending = None;
                },
                | ConversionDecision::ReduceRight { redex } => {
                    if pending != Some(redex) {
                        return Err(ReplayError::UnpairedUnfold);
                    }
                    if right_layers.last().copied() != Some(redex) {
                        return Err(ReplayError::HeadMismatch);
                    }
                    let _popped = right_layers.pop();
                    pending = None;
                },
                | ConversionDecision::ComparedShared {
                    left: left_head,
                    right: right_head,
                } => {
                    if pending.is_some() {
                        return Err(ReplayError::UnpairedUnfold);
                    }
                    if !left_layers.is_empty() || !right_layers.is_empty() {
                        return Err(ReplayError::ClosedTooEarly);
                    }
                    if left_head != left.atom || right_head != right.atom {
                        return Err(ReplayError::HeadMismatch);
                    }
                    // The trace says the two occurrences met. Whether they agreed
                    // is recomputed here, from the terms.
                    verdict = Some(if left_head == right_head {
                        Verdict::Convertible
                    }
                    else {
                        Verdict::NotConvertible
                    });
                },
                | _ => return Err(ReplayError::UnexpectedDecision),
            }
        }
        verdict.ok_or(ReplayError::NeverClosed)
    }

    /// One comparison the differential runs, with the decision count its trace
    /// must have.
    struct Case
    {
        /// The left-hand term.
        left: Side,
        /// The right-hand term.
        right: Side,
        /// The verdict both instantiations must produce.
        verdict: Verdict,
        /// The number of decisions the recording instantiation must retain.
        decisions: DecisionCount,
    }

    /// The comparisons the differential runs.
    ///
    /// # Specification
    /// trivial.
    fn cases() -> Vec<Case>
    {
        vec![
            // Two identical atoms with no layers: one decision, the close.
            Case {
                left: Side {
                    layers: Vec::new(),
                    atom: NodeName(1),
                },
                right: Side {
                    layers: Vec::new(),
                    atom: NodeName(1),
                },
                verdict: Verdict::Convertible,
                decisions: DecisionCount::from(1),
            },
            // Distinct atoms: the same one decision, the opposite verdict. The
            // trace of a refutation has the shape of the trace of a proof.
            Case {
                left: Side {
                    layers: Vec::new(),
                    atom: NodeName(1),
                },
                right: Side {
                    layers: Vec::new(),
                    atom: NodeName(2),
                },
                verdict: Verdict::NotConvertible,
                decisions: DecisionCount::from(1),
            },
            // A shared outer constant: the shortcut fires once, then each side
            // unfolds its own remaining layer, then the close. 1 + 2 + 2 + 1.
            Case {
                left: Side {
                    layers: vec![NodeName(10), NodeName(20)],
                    atom: NodeName(1),
                },
                right: Side {
                    layers: vec![NodeName(11), NodeName(20)],
                    atom: NodeName(1),
                },
                verdict: Verdict::Convertible,
                decisions: DecisionCount::from(6),
            },
            // A left-heavy chain: three left unfoldings at two decisions each,
            // then the close.
            Case {
                left: Side {
                    layers: vec![NodeName(30), NodeName(31), NodeName(32)],
                    atom: NodeName(5),
                },
                right: Side {
                    layers: Vec::new(),
                    atom: NodeName(5),
                },
                verdict: Verdict::Convertible,
                decisions: DecisionCount::from(7),
            },
        ]
    }

    #[test]
    fn recording_does_not_move_the_verdict()
    {
        for case in cases() {
            let mut off = NullSink;
            let sink_off = convert(&case.left, &case.right, &mut off);
            let mut on: TraceLog<NodeName> = TraceLog::new();
            let sink_on = convert(&case.left, &case.right, &mut on);
            assert_eq!(
                case.verdict, sink_off,
                "the sink-off run answers what the case says"
            );
            assert_eq!(
                sink_off, sink_on,
                "and the sink-on run answers the same, because it is the same function at another type \
                 parameter"
            );
        }
    }

    #[test]
    fn the_exercised_recording_paths_are_asserted_rather_than_reported()
    {
        for case in cases() {
            let mut off = NullSink;
            let _verdict = convert(&case.left, &case.right, &mut off);
            assert_eq!(
                DecisionCount::from(0),
                TraceSink::<NodeName>::recorded_count(&off),
                "the sink-off run holds no recording state at all"
            );
            let mut on: TraceLog<NodeName> = TraceLog::new();
            let _verdict = convert(&case.left, &case.right, &mut on);
            assert_eq!(
                case.decisions,
                on.recorded_count(),
                "and the sink-on run retains exactly the decisions the case names, so a green \
                 differential cannot have skipped the recording path"
            );
        }
    }

    #[test]
    fn the_kernel_replays_the_trace_without_searching()
    {
        for case in cases() {
            let mut on: TraceLog<NodeName> = TraceLog::new();
            let engine = convert(&case.left, &case.right, &mut on);
            let trace: Vec<ConversionDecision<NodeName>> = on.decisions().copied().collect();
            assert_eq!(
                Ok(engine),
                replay(&case.left, &case.right, &trace),
                "the kernel's sequential rechecker re-derives the engine's verdict from the trace and \
                 the terms"
            );
        }
    }

    #[test]
    fn a_trace_that_names_the_wrong_branch_is_refused_rather_than_agreed_with()
    {
        let left = Side {
            layers: vec![NodeName(30)],
            atom: NodeName(5),
        };
        let right = Side {
            layers: Vec::new(),
            atom: NodeName(5),
        };
        let mut on: TraceLog<NodeName> = TraceLog::new();
        let engine = convert(&left, &right, &mut on);
        assert_eq!(Verdict::Convertible, engine);

        // The side is what a proof search must record and a heuristic need not.
        // Swapping it produces a trace of the same length and the same kinds that
        // no longer describes this comparison.
        let corrupted: Vec<ConversionDecision<NodeName>> = on
            .decisions()
            .map(|decision| match *decision {
                | ConversionDecision::ReduceLeft { redex } => {
                    ConversionDecision::ReduceRight { redex }
                },
                | other => other,
            })
            .collect();
        assert_eq!(
            Err(ReplayError::HeadMismatch),
            replay(&left, &right, &corrupted),
            "replaying a reduction against the side that has nothing to reduce is refused, which is \
             what makes the recorded side load-bearing rather than decorative"
        );

        // Dropping the unfolding that pairs with the reduction is refused too.
        let truncated: Vec<ConversionDecision<NodeName>> = on
            .decisions()
            .filter(|decision| !matches!(**decision, ConversionDecision::Unfold { .. }))
            .copied()
            .collect();
        assert_eq!(
            Err(ReplayError::UnpairedUnfold),
            replay(&left, &right, &truncated),
            "and so is a reduction with no unfolding decision before it"
        );
    }
}
