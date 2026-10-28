//! The decision vocabulary: which side reduced, and which branch was taken.
//!
//! The vocabulary is at the grain of a proof search. `Unfold`, `Postpone`,
//! `Force` and `ComparedShared` suffice for a heuristic unfolding strategy;
//! `ReduceLeft`, `ReduceRight`, `ConstShortcut`, `Freeze`, `EtaExpand` and
//! `NegativeSubgoal` add the side of every reduction, the branch taken at
//! every choice point and the premise every refutation of a decomposition
//! rests on, which a search-free replay needs. `Unfold` and `Postpone` are the
//! two outcomes of one unfolding choice. `ReturnEta` and `Reassociate` are the
//! two commuting conversions of `F`, each acting on one side, and `Discard`
//! drops an unread call on one side. The variants are those of
//! [`ConversionDecision`].
//!
//! # The refuted premise
//!
//! `NegativeSubgoal` carries the one premise a refutation of a decomposition
//! rests on. A decomposition — two applications of one rigid head, or two
//! formers compared child by child — is refuted by any one premise, and the
//! rule that refutes it has that one premise and no other. A replay that met
//! the decomposition with no position would have to try every premise until
//! one refuted, which is search; the position names the premise, so the replay
//! checks one.
//!
//! **Alternatives.** Emit the refuted premise alone and let the replay find
//! where it fits, which is the same search moved one step; or emit every
//! premise's derivation, which would make a refutation as long as the
//! agreement it contradicts. **Reversal.** A replay that can locate the
//! refuted premise from the terms without trying the others, which would make
//! the position redundant.
//!
//! # Structural selection and sides
//!
//! `Decompose` selects a structural rule before the next child dialogue. It
//! preserves paired-trace boundaries when a component begins with
//! `ComparedShared`: that shortcut must not close the enclosing pair instead.
//! The consumer checks that the current goal has structural premises; it
//! refuses the decision at leaves and at goals requiring unfolding, force or
//! eta.
//!
//! [`ConversionSide`] is a type. `Freeze` records which side froze,
//! `EtaExpand` which side was applied to the fresh variable, and `ReturnEta`,
//! `Reassociate` and `Discard` which side was rewritten; `ReduceLeft` and
//! `ReduceRight` carry the side structurally. A trace whose side is implicit
//! cannot be replayed without searching for it, and search-free replay is what
//! the seam exists to deliver.
//!
//! # The commuting conversions of `F`
//!
//! Two neutral computations over one head can differ only in how their binds
//! sit: `M` against `M to x. return x`, the η-rule of `F`, and
//! `(M to x. N) to y. P` against `M to x. (N to y. P)`, the associativity of
//! bind. `Reassociate` names the side whose spine carries two binds in a row
//! and rewrites the pair nearest the head into one; `ReturnEta` names the
//! side whose spine stops where the other's continues by one bind, and reads
//! it as its bind into `return`. Applied until neither fires, the two spines
//! carry no two binds in a row and end at one length, so the decomposition
//! that follows compares continuations position by position.
//!
//! `Discard` names the side whose computation is a call of a variable that
//! returns, bound last into a continuation that never reads the value: `M to
//! x. N` reads as `N`. The call performs nothing and runs to its end, so
//! dropping it changes no observation. The engine knows which variables
//! return from their types; the kernel, whose fragment is pure and total,
//! knows it of every variable.
//!
//! # Evaluation
//!
//! `Evaluate` closes a goal by the consumer's own evaluation instead of
//! recorded steps: a pair of closed terms runs to its normal forms, which
//! the consumer compares. It names no node, since nothing in the pair is
//! chosen: a closed term's evaluation has one result. A consumer reads it
//! only where it can check that both sides are closed, and refuses it
//! anywhere else.

/// Which of the two compared terms a one-sided decision acted on.
///
/// A conversion derivation is a valley with a left leg and a right leg, and the
/// side assignment is forced rather than chosen — so a decision that does not
/// say which leg it belongs to cannot be replayed without searching for the
/// answer.
///
/// # Specification
/// - requires: nothing; both sides are always inhabited.
/// - ensures: the two sides are distinct values, so a decision carrying a side
///   separates the leg it acted on from the other one.
/// - provides: the side component that makes a one-sided choice replayable.
/// - panics: none.
/// - executable: none — distinct variants are fixed by the enum representation;
///   their meaning relates a decision to the consumer's external comparison.
///
/// # Adequacy
/// - hypothesis: L0 — the enum distinguishes the two sides. L3 — a mixed
///   recorded sequence preserves side-specific payloads, and replay refuses a
///   reduction moved to the empty side. These observers separate side loss and
///   side reversal for the bounded fixtures, not arbitrary consumer arenas.
/// - witness: `sink::tests::a_trace_log_retains_every_decision_in_order`
/// - witness: `tests::differential::a_trace_that_names_the_wrong_branch_is_refused_rather_than_agreed_with`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ConversionSide
{
    /// The left-hand term.
    Left,
    /// The right-hand term.
    Right,
}

/// Where one subgoal stands in a decomposition, counted from zero.
///
/// Both consumers enumerate a former's subgoals in one order — a spine's
/// eliminations innermost first, a case's left branch before its right, a
/// pair's first component before its second — so a position names the same
/// subgoal on either side of the seam without either sharing an identifier.
///
/// # Specification
/// - requires: the consumers agree on the enumeration order stated above.
/// - ensures: the carried count is the subgoal's position in that order.
/// - provides: the premise a refutation names, keeping its replay search-free.
/// - panics: none.
/// - executable: none — the consumer's decomposition and enumeration order are
///   external to the carried position.
///
/// # Adequacy
/// - hypothesis: L3 — a recorded sequence carries positions zero, one and the
///   u32 ceiling without collapsing or narrowing them. Exact replay inputs
///   distinguish lost positions; interpreting a position in an arbitrary
///   decomposition remains the consumer's obligation.
/// - witness: `sink::tests::a_trace_log_retains_every_decision_in_order`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SubgoalPosition(u32);

impl From<u32> for SubgoalPosition
{
    /// The subgoal at `position`, counted from zero.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: u32) -> Self
    {
        Self(position)
    }
}

impl From<SubgoalPosition> for u32
{
    /// The count a position carries.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: SubgoalPosition) -> Self
    {
        position.0
    }
}

/// One decision made by a conversion strategy.
///
/// The identifier type is owned by the consumer. In the untrusted engine it
/// names a semantic or closure node; in the kernel it names an arena node.
/// Nothing here interprets those values, and nothing here stores, orders, or
/// serializes a trace: the enum is a shared vocabulary, and a trace is a
/// session artifact rather than a wire format.
///
/// # Why the vocabulary has this shape
///
/// The variants cover the branching rules of the convertibility judgement, not
/// the steps of a heuristic strategy. A heuristic unfolder needs only to say
/// what it unfolded; a proof search must record **the side of every reduction
/// and the branch taken at every choice point**, because that is exactly what
/// makes the kernel's replay search-free — with the recorded choices in hand
/// the rechecker has at most one applicable rule at every step, so it is a
/// sequential worklist with no queue, no wait map, and no fairness.
///
/// A trace individuates strictly more finely than convertibility: two
/// convertible terms can carry different traces. It is replay evidence and
/// never an equality, so comparing two traces decides something finer than
/// conversion and is not a conversion test.
///
/// # Specification
/// - requires: every identifier is meaningful in the consumer's own arena or
///   value space, and the consumer keeps the trace within the scope in which
///   those identifiers resolve.
/// - ensures: a decision records the branch taken, so a replay reading the
///   sequence in order never chooses.
/// - provides: the seam where an untrusted engine records its search choices
///   and a kernel replays them.
/// - panics: none.
/// - executable: none — identifier resolution and branch validity depend on the
///   consumer's external arena and comparison state.
///
/// # Adequacy
/// - hypothesis: L0 — distinct variants retain the branch vocabulary. L3 — the
///   mixed trace includes every kind, side changes, position boundaries and a
///   repeated decision; exact storage distinguishes loss, duplication,
///   deduplication and reordering. L2 — replay recomputes the verdict and
///   refuses malformed branches on the bounded layered-term workload.
/// - witness: `sink::tests::a_trace_log_retains_every_decision_in_order`
/// - witness: `tests::differential::a_trace_that_names_the_wrong_branch_is_refused_rather_than_agreed_with`
/// - witness: `tests::differential::the_kernel_replays_the_trace_without_searching`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ConversionDecision<Id>
{
    /// A reduction step on the left-hand term.
    ReduceLeft
    {
        /// The consumer's identifier for the redex head.
        redex: Id,
    },
    /// A reduction step on the right-hand term.
    ReduceRight
    {
        /// The consumer's identifier for the redex head.
        redex: Id,
    },
    /// Two applications of one defined constant were proved convertible
    /// without unrolling it.
    ConstShortcut
    {
        /// The consumer's identifier for the shared constant.
        constant: Id,
    },
    /// A defined constant was expanded to continue the comparison.
    Unfold
    {
        /// The consumer's identifier for the definition head.
        constant: Id,
    },
    /// A defined constant was left for a later choice point.
    Postpone
    {
        /// The consumer's identifier for the definition head.
        constant: Id,
    },
    /// The frozen-constant branch of a two-sided constant comparison.
    Freeze
    {
        /// The consumer's identifier for the frozen definition head.
        constant: Id,
        /// Which side froze.
        side: ConversionSide,
    },
    /// The eta branch: one side was applied to a fresh variable.
    EtaExpand
    {
        /// Which side was applied.
        side: ConversionSide,
        /// The consumer's identifier for the fresh variable.
        variable: Id,
    },
    /// The η-rule of `F`: the computation on one side was read as its bind
    /// into `return`, `M ≡ M to x. return x`.
    ReturnEta
    {
        /// Which side was expanded.
        side: ConversionSide,
    },
    /// Bind associativity: on one side the two binds nearest the head became
    /// one, `(M to x. N) to y. P ≡ M to x. (N to y. P)`.
    Reassociate
    {
        /// Which side was reassociated.
        side: ConversionSide,
    },
    /// The discard of an unread call: on one side `M to x. N`, its bind the
    /// last elimination and `x` unread in `N`, became `N`, since `M`
    /// returns.
    Discard
    {
        /// Which side was discarded.
        side: ConversionSide,
    },
    /// A suspended computation or thunk was forced for the comparison.
    Force
    {
        /// The consumer's identifier for the suspended computation.
        thunk: Id,
    },
    /// The comparison closed on two already-shared nodes.
    ComparedShared
    {
        /// The left consumer-owned node identifier.
        left: Id,
        /// The right consumer-owned node identifier.
        right: Id,
    },
    /// Select structural decomposition before a following child dialogue.
    /// Unlike a leading shared comparison, this cannot close the whole pair;
    /// concatenated component traces therefore retain their boundaries.
    Decompose,
    /// A decomposition was refuted by one of its subgoals: the single
    /// negative premise of the rule separating two applications of one rigid
    /// head, and of every former compared child by child.
    NegativeSubgoal
    {
        /// Which subgoal, in the order [`SubgoalPosition`] states.
        position: SubgoalPosition,
    },
    /// The goal was closed by the consumer's own evaluation of two closed
    /// sides, compared at their normal forms.
    Evaluate,
}

impl<Id> ConversionDecision<Id>
{
    /// The same decision, each identifier it carries passed through
    /// `anchor`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the variant, side and subgoal position of `self`, each
    ///   identifier replaced by `anchor` of it, in field order; `anchor` runs
    ///   once per identifier and never otherwise.
    /// - provides: re-anchoring a trace in another consumer's identifiers, and
    ///   erasing them for evidence that names no arena.
    /// - panics: whenever `anchor` does.
    /// - executable: none — the call consumes `anchor`, so no predicate can run
    ///   it again to state the image, and `Id` carries no bound a captured copy
    ///   of `self` would need.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every variant, re-anchored, keeps its kind, side and
    ///   position and carries the mapped identifiers in field order; erasing to
    ///   `()` keeps the branch vocabulary.
    /// - witness: `decision::tests::reanchoring_keeps_every_branch`
    #[inline]
    #[must_use]
    pub fn map<Other, Anchor>(
        self,
        mut anchor: Anchor,
    ) -> ConversionDecision<Other>
    where
        Anchor: FnMut(Id) -> Other,
    {
        match self {
            Self::ReduceLeft { redex } => ConversionDecision::ReduceLeft {
                redex: anchor(redex),
            },
            Self::ReduceRight { redex } => ConversionDecision::ReduceRight {
                redex: anchor(redex),
            },
            Self::ConstShortcut { constant } => ConversionDecision::ConstShortcut {
                constant: anchor(constant),
            },
            Self::Unfold { constant } => ConversionDecision::Unfold {
                constant: anchor(constant),
            },
            Self::Postpone { constant } => ConversionDecision::Postpone {
                constant: anchor(constant),
            },
            Self::Freeze { constant, side } => ConversionDecision::Freeze {
                constant: anchor(constant),
                side,
            },
            Self::EtaExpand { side, variable } => ConversionDecision::EtaExpand {
                side,
                variable: anchor(variable),
            },
            Self::ReturnEta { side } => ConversionDecision::ReturnEta { side },
            Self::Reassociate { side } => ConversionDecision::Reassociate { side },
            Self::Discard { side } => ConversionDecision::Discard { side },
            Self::Force { thunk } => ConversionDecision::Force {
                thunk: anchor(thunk),
            },
            Self::ComparedShared { left, right } => {
                let left = anchor(left);
                ConversionDecision::ComparedShared {
                    left,
                    right: anchor(right),
                }
            },
            Self::Decompose => ConversionDecision::Decompose,
            Self::NegativeSubgoal { position } => ConversionDecision::NegativeSubgoal { position },
            Self::Evaluate => ConversionDecision::Evaluate,
        }
    }
}

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;

    use super::ConversionDecision;
    use super::ConversionSide;
    use super::SubgoalPosition;

    #[test]
    fn reanchoring_keeps_every_branch()
    {
        let trace = [
            ConversionDecision::ReduceLeft { redex: 1_u8 },
            ConversionDecision::ReduceRight { redex: 2 },
            ConversionDecision::ConstShortcut { constant: 3 },
            ConversionDecision::Unfold { constant: 4 },
            ConversionDecision::Postpone { constant: 5 },
            ConversionDecision::Freeze {
                constant: 6,
                side: ConversionSide::Right,
            },
            ConversionDecision::EtaExpand {
                side: ConversionSide::Left,
                variable: 7,
            },
            ConversionDecision::ReturnEta {
                side: ConversionSide::Right,
            },
            ConversionDecision::Reassociate {
                side: ConversionSide::Left,
            },
            ConversionDecision::Discard {
                side: ConversionSide::Right,
            },
            ConversionDecision::Force { thunk: 8 },
            ConversionDecision::ComparedShared { left: 9, right: 10 },
            ConversionDecision::Decompose,
            ConversionDecision::NegativeSubgoal {
                position: SubgoalPosition::from(11),
            },
            ConversionDecision::Evaluate,
        ];
        let mut seen = Vec::new();
        let shifted: Vec<_> = trace
            .into_iter()
            .map(|decision| {
                decision.map(|anchor| {
                    seen.push(anchor);
                    u16::from(anchor) + 100
                })
            })
            .collect();
        assert_eq!(
            seen,
            Vec::from([1, 2, 3, 4, 5, 6, 7, 8, 9, 10]),
            "every identifier is mapped once, in field order"
        );
        let expected = [
            ConversionDecision::ReduceLeft { redex: 101_u16 },
            ConversionDecision::ReduceRight { redex: 102 },
            ConversionDecision::ConstShortcut { constant: 103 },
            ConversionDecision::Unfold { constant: 104 },
            ConversionDecision::Postpone { constant: 105 },
            ConversionDecision::Freeze {
                constant: 106,
                side: ConversionSide::Right,
            },
            ConversionDecision::EtaExpand {
                side: ConversionSide::Left,
                variable: 107,
            },
            ConversionDecision::ReturnEta {
                side: ConversionSide::Right,
            },
            ConversionDecision::Reassociate {
                side: ConversionSide::Left,
            },
            ConversionDecision::Discard {
                side: ConversionSide::Right,
            },
            ConversionDecision::Force { thunk: 108 },
            ConversionDecision::ComparedShared {
                left: 109,
                right: 110,
            },
            ConversionDecision::Decompose,
            ConversionDecision::NegativeSubgoal {
                position: SubgoalPosition::from(11),
            },
            ConversionDecision::Evaluate,
        ];
        assert_eq!(
            shifted.as_slice(),
            expected.as_slice(),
            "kind, side and position survive"
        );
        let erased: Vec<_> = trace
            .into_iter()
            .map(|decision| decision.map(|_| ()))
            .collect();
        assert_eq!(
            erased.get(5),
            Some(&ConversionDecision::Freeze {
                constant: (),
                side: ConversionSide::Right,
            }),
            "erasing the anchors keeps the branch"
        );
        assert_eq!(erased.len(), trace.len());
    }
}
