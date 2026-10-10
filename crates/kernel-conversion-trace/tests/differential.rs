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

    use anodized::spec;
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
    ///
    /// # Specification
    /// - ensures: the last layer is the next definition head; removing all
    ///   layers exposes the carried atom.
    /// - panics: none.
    /// - executable: none — these are the consumer's interpretation rules for a
    ///   data value; conversion and replay check them at use sites.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — finite empty, asymmetric and shared-head stacks are
    ///   observed through exact decisions and replayed verdicts. A refuting
    ///   comparison appended to an existing log separates atom identity from
    ///   layer identity and checks order.
    /// - witness: `differential::differential::the_kernel_replays_the_trace_without_searching`
    /// - witness: `differential::differential::conversion_appends_a_refutation_to_an_existing_log`
    #[derive(Clone, Debug, Eq, PartialEq)]
    struct Side
    {
        /// The definition layers, outermost last.
        layers: Vec<NodeName>,
        /// The head reached once every layer is unfolded.
        atom: NodeName,
    }

    /// The answer a comparison produces.
    ///
    /// # Specification
    /// - ensures: convertible means the compared sides expose the same atom;
    ///   not convertible means their exposed atoms differ.
    /// - panics: none.
    /// - executable: none — the compared sides are external to this answer.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — four finite comparisons and an appended layered
    ///   refutation have exact atom-derived answers, separating always-positive
    ///   and layer-derived judgements. Replay recomputes those answers from the
    ///   recorded decisions.
    /// - witness: `differential::differential::recording_does_not_move_the_verdict`
    /// - witness: `differential::differential::conversion_appends_a_refutation_to_an_existing_log`
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum Verdict
    {
        /// The two terms are convertible.
        Convertible,
        /// The two terms are not convertible.
        NotConvertible,
    }

    /// A trace the replay refuses.
    ///
    /// # Specification
    /// - ensures: identifies the first invalid transition, an event after a
    ///   valid close, or a trace that ends without a valid close.
    /// - panics: none.
    /// - executable: none — classification depends on the external terms,
    ///   decision sequence and replay state, none of which this tag retains.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the refusal matrix distinguishes all six reasons and
    ///   the guards on shortcut, unfolding, reduction and closing. An event
    ///   after a close must be refused as such before its own kind is
    ///   interpreted.
    /// - witness: `differential::differential::replay_refuses_each_invalid_transition`
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
    /// - requires: the sink obeys its declared recording behavior.
    /// - ensures: answers `Convertible` exactly when the two sides expose the
    ///   same atom once every layer is unfolded, and hands the sink one
    ///   decision per step it took, in the order it took them.
    /// - provides: the one strategy both instantiations run, so the
    ///   differential compares a function against itself rather than against a
    ///   second implementation.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — four finite comparisons expose exact verdicts at both
    ///   shipped sinks; replay independently checks their decisions. L3 an
    ///   existing log receives a layered refutation without losing its prefix,
    ///   separating clearing, premature success and recording in the wrong
    ///   order.
    /// - witness: `differential::differential::recording_does_not_move_the_verdict`
    /// - witness: `differential::differential::the_kernel_replays_the_trace_without_searching`
    /// - witness: `differential::differential::conversion_appends_a_refutation_to_an_existing_log`
    #[spec(ensures: |ret| (ret == Verdict::Convertible) == (left.atom == right.atom))]
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

    /// Sends a decision only when the sink is live.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: forwards the already constructed decision to an active sink;
    ///   an inactive sink is left unchanged.
    /// - provides: the guarded emit every recording site in the strategy goes
    ///   through.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the finite workload observes exact nonzero recording
    ///   counts and zero null counts; an existing log retains its prefix. These
    ///   distinguish dropped active events and altered state on the inactive
    ///   path, not the cost of constructing an argument before this function is
    ///   entered.
    /// - witness: `differential::differential::the_exercised_recording_paths_are_asserted_rather_than_reported`
    /// - witness: `differential::differential::conversion_appends_a_refutation_to_an_existing_log`
    #[spec(captures: [before = sink.recorded_count()], ensures:
        !matches!(Sink::ACTIVITY, SinkActivity::Inactive) || sink.recorded_count() == before)]
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
    /// - requires: nothing; arbitrary decision sequences are admitted and
    ///   malformed traces are refused.
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
    ///
    /// # Errors
    /// - `ReplayError::HeadMismatch`: a named head or atom disagrees.
    /// - `ReplayError::UnpairedUnfold`: unfolding and reduction do not pair.
    /// - `ReplayError::ClosedTooEarly`: a close leaves unprocessed layers.
    /// - `ReplayError::DecisionAfterClose`: an event follows a valid close.
    /// - `ReplayError::NeverClosed`: the trace ends without a valid close.
    /// - `ReplayError::UnexpectedDecision`: this replay has no rule for a kind.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — valid traces rederive exact atom-based verdicts
    ///   independently of the strategy. L3 every refusal guard is exercised
    ///   with a malformed finite trace, including error precedence after
    ///   closing. Exact error variants separate skipped checks, mismatched
    ///   heads and incorrect state transitions.
    /// - witness: `differential::differential::the_kernel_replays_the_trace_without_searching`
    /// - witness: `differential::differential::a_trace_that_names_the_wrong_branch_is_refused_rather_than_agreed_with`
    /// - witness: `differential::differential::replay_refuses_each_invalid_transition`
    #[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|verdict|
        (*verdict == Verdict::Convertible) == (left.atom == right.atom)
        && matches!(decisions.last(), Some(ConversionDecision::ComparedShared { left: first, right: second })
            if *first == left.atom && *second == right.atom)))]
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
    ///
    /// # Specification
    /// - ensures: the verdict agrees with the exposed atoms, and the count
    ///   names the strategy's retained decisions including its closing event.
    /// - panics: none.
    /// - executable: none — data-item expansion does not check construction;
    ///   the fixture builder checks verdicts and differential runs check
    ///   counts.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — each of the four fixture comparisons is run at both
    ///   sinks; its verdict and exact retained count are observed. Shared
    ///   heads, bare unequal atoms and asymmetric layers separate incorrect
    ///   expected answers or counts.
    /// - witness: `differential::differential::recording_does_not_move_the_verdict`
    /// - witness: `differential::differential::the_exercised_recording_paths_are_asserted_rather_than_reported`
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
    /// - ensures: fixture verdicts agree with their atoms; every case closes
    ///   with at least one recorded decision, and both verdicts are
    ///   represented.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the four fixture cases are executed at both sinks and
    ///   replayed; exact answers and event counts reject inconsistent fixture
    ///   metadata. The predicate checks the atom relation and coverage, not the
    ///   whole trace count.
    /// - witness: `differential::differential::recording_does_not_move_the_verdict`
    /// - witness: `differential::differential::the_exercised_recording_paths_are_asserted_rather_than_reported`
    /// - witness: `differential::differential::the_kernel_replays_the_trace_without_searching`
    #[spec(ensures: |ret| ret.iter().all(|case|
        (case.verdict == Verdict::Convertible) == (case.left.atom == case.right.atom)
        && usize::from(case.decisions) >= 1)
        && ret.iter().any(|case| case.verdict == Verdict::Convertible)
        && ret.iter().any(|case| case.verdict == Verdict::NotConvertible))]
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
    #[test]
    fn conversion_appends_a_refutation_to_an_existing_log()
    {
        let left = Side {
            layers: vec![NodeName(1), NodeName(2)],
            atom: NodeName(5),
        };
        let right = Side {
            layers: vec![NodeName(2)],
            atom: NodeName(6),
        };
        let mut log = TraceLog::new();
        log.record(ConversionDecision::Force {
            thunk: NodeName(99),
        });
        assert_eq!(Verdict::NotConvertible, convert(&left, &right, &mut log));
        let expected = [
            ConversionDecision::Force {
                thunk: NodeName(99),
            },
            ConversionDecision::ConstShortcut {
                constant: NodeName(2),
            },
            ConversionDecision::Unfold {
                constant: NodeName(1),
            },
            ConversionDecision::ReduceLeft { redex: NodeName(1) },
            ConversionDecision::ComparedShared {
                left: NodeName(5),
                right: NodeName(6),
            },
        ];
        assert_eq!(DecisionCount::from(5), log.recorded_count());
        assert!(log.decisions().copied().eq(expected));
    }

    #[test]
    fn replay_refuses_each_invalid_transition()
    {
        let layered = Side {
            layers: vec![NodeName(1)],
            atom: NodeName(5),
        };
        let bare = Side {
            layers: Vec::new(),
            atom: NodeName(5),
        };
        let failures: [(&Side, &Side, &[ConversionDecision<NodeName>], ReplayError); 14] = [
            (&bare, &bare, &[], ReplayError::NeverClosed),
            (
                &layered,
                &bare,
                &[
                    ConversionDecision::Unfold {
                        constant: NodeName(1),
                    },
                    ConversionDecision::Unfold {
                        constant: NodeName(1),
                    },
                ],
                ReplayError::UnpairedUnfold,
            ),
            (
                &layered,
                &bare,
                &[ConversionDecision::ReduceRight { redex: NodeName(1) }],
                ReplayError::UnpairedUnfold,
            ),
            (
                &layered,
                &bare,
                &[
                    ConversionDecision::Unfold {
                        constant: NodeName(2),
                    },
                    ConversionDecision::ReduceLeft { redex: NodeName(2) },
                ],
                ReplayError::HeadMismatch,
            ),
            (
                &layered,
                &bare,
                &[
                    ConversionDecision::Unfold {
                        constant: NodeName(2),
                    },
                    ConversionDecision::ReduceLeft { redex: NodeName(1) },
                ],
                ReplayError::UnpairedUnfold,
            ),
            (
                &bare,
                &layered,
                &[ConversionDecision::ConstShortcut {
                    constant: NodeName(1),
                }],
                ReplayError::HeadMismatch,
            ),
            (
                &layered,
                &bare,
                &[ConversionDecision::ConstShortcut {
                    constant: NodeName(1),
                }],
                ReplayError::HeadMismatch,
            ),
            (
                &layered,
                &layered,
                &[
                    ConversionDecision::Unfold {
                        constant: NodeName(1),
                    },
                    ConversionDecision::ConstShortcut {
                        constant: NodeName(1),
                    },
                ],
                ReplayError::UnpairedUnfold,
            ),
            (
                &layered,
                &bare,
                &[
                    ConversionDecision::Unfold {
                        constant: NodeName(1),
                    },
                    ConversionDecision::ComparedShared {
                        left: NodeName(5),
                        right: NodeName(5),
                    },
                ],
                ReplayError::UnpairedUnfold,
            ),
            (
                &layered,
                &bare,
                &[ConversionDecision::ComparedShared {
                    left: NodeName(5),
                    right: NodeName(5),
                }],
                ReplayError::ClosedTooEarly,
            ),
            (
                &bare,
                &layered,
                &[ConversionDecision::ComparedShared {
                    left: NodeName(5),
                    right: NodeName(5),
                }],
                ReplayError::ClosedTooEarly,
            ),
            (
                &bare,
                &bare,
                &[ConversionDecision::ComparedShared {
                    left: NodeName(6),
                    right: NodeName(5),
                }],
                ReplayError::HeadMismatch,
            ),
            (
                &bare,
                &bare,
                &[ConversionDecision::ComparedShared {
                    left: NodeName(5),
                    right: NodeName(6),
                }],
                ReplayError::HeadMismatch,
            ),
            (
                &bare,
                &bare,
                &[
                    ConversionDecision::ComparedShared {
                        left: NodeName(5),
                        right: NodeName(5),
                    },
                    ConversionDecision::Force { thunk: NodeName(9) },
                ],
                ReplayError::DecisionAfterClose,
            ),
        ];
        for (left, right, decisions, expected) in failures {
            assert_eq!(Err(expected), replay(left, right, decisions));
        }
        assert_eq!(
            Err(ReplayError::UnexpectedDecision),
            replay(&bare, &bare, &[ConversionDecision::Force {
                thunk: NodeName(9)
            }]),
        );
    }
}
