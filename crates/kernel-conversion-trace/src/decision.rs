//! The decision vocabulary: which side reduced, and which branch was taken.
//!
//! The vocabulary is at the grain of a proof search. `Unfold`, `Postpone`,
//! `Force` and `ComparedShared` suffice for a heuristic unfolding strategy;
//! `ReduceLeft`, `ReduceRight`, `ConstShortcut`, `Freeze`, `EtaExpand` and
//! `NegativeSubgoal` add the side of every reduction, the branch taken at
//! every choice point and the premise every refutation of a decomposition
//! rests on, which a search-free replay needs. `Unfold` and `Postpone` are the
//! two outcomes of one unfolding choice. The variants are those of
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
//! [`ConversionSide`] is a type. `Freeze` records which side froze and
//! `EtaExpand` which side was applied to the fresh variable; `ReduceLeft` and
//! `ReduceRight` carry the side structurally. A trace whose side is implicit
//! cannot be replayed without searching for it, and search-free replay is what
//! the seam exists to deliver.

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
/// - witness: `differential::differential::a_trace_that_names_the_wrong_branch_is_refused_rather_than_agreed_with`
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
/// - witness: `differential::differential::a_trace_that_names_the_wrong_branch_is_refused_rather_than_agreed_with`
/// - witness: `differential::differential::the_kernel_replays_the_trace_without_searching`
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
}
