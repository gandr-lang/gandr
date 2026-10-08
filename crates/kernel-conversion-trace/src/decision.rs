//! The decision vocabulary: which side reduced, and which branch was taken.

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
/// - provides: the side component of every one-sided decision, which is what
///   makes replay search-free at a two-sided choice point. This stays prose: a
///   data-item `#[spec]` states an invariant of one value, which the pinned
///   expansion never checks at construction, and distinctness relates the two
///   variants to each other.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L0 — the two legs are separate variants rather than a flag, so
///   a strategy cannot omit the side; the residue is that the variants must not
///   compare equal, pinned pointwise by a pair of recorded decisions differing
///   only in their side.
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
/// - provides: the seam that makes the engine untrusted — the engine searches,
///   the kernel replays what it found. This stays prose: the requirement is an
///   obligation on the consumer's identifier space, which no value carries, and
///   a data-item `#[spec]` states an invariant of one value that the pinned
///   expansion never checks at construction.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surface is which branch a decision names,
///   and the disagreement class is finite: the nine kinds are enumerated
///   exhaustively and every pair is asserted to compare unequal while carrying
///   identical identifiers, so a vocabulary that collapsed two branches into
///   one is separated. The L2 rung above it is the replay, which refuses a
///   trace naming the wrong branch rather than agreeing with it.
/// - witness: `sink::tests::the_nine_decision_kinds_are_distinct_values`
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
}
