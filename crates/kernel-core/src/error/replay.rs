//! The kernel's verdict on a replayed claim, and why the kernel declines or
//! refuses a claim.

use core::fmt;

use anodized::spec;

/// The kernel's verdict on a replayed claim.
///
/// # Specification
/// - provides: two certified verdicts and a decline carrying its reason. For
///   fixed sides, unfoldings and budget, traces carrying the same claim are
///   equivalent evidence only when both replay to a certified verdict. A
///   declining trace is not equivalent to itself: this is a partial
///   equivalence, distinct from this enum's Rust equality. The unit and
///   composition laws quantify over certified verdicts only. Purity also
///   preserves declines, without making them certified evidence.
/// - executable: none — evidence equivalence needs two traces and their replay
///   context, not one stored verdict.
///
/// | Class | Verdict or reason |
/// | --- | --- |
/// | Ill-formed query | `Refused(Unreadable)` |
/// | Foreign answer | `Refused(Inapplicable { at })`, `Refused(NonAuthoritative { at })` |
/// | Path disagreement | `Refused(Contradicted { at })`, `Refused(Exhausted)`, `Refused(Leftover { at })` |
/// | No dialogue | `EngineDeclined` |
/// | Budget | `Budget` |
/// | Partial recursion | `PartialFixpoint` |
/// | Certified negative | `NotConvertible`: an element, never a refusal |
///
/// Refused reasons are [`ReplayRefusal`] variants inside
/// [`ReplayDecline::Refused`], their class [`ReplayRefusal::class`]; every
/// decline is inside [`Self::Declined`].
///
/// # Adequacy
/// - hypothesis: L3 — a pinned table of replay inputs separates every refusal
///   variant; the unit witnesses distinguish both certified answers from
///   disagreement and budget exhaustion.
/// - witness: `tests::replay_laws::every_replay_refusal_carries_its_pinned_class`
/// - witness: `replay::tests::a_compared_pair_closes_on_alpha_equality_or_rigid_separation`
/// - witness: `replay::tests::an_engine_decline_and_an_exhausted_budget_decline`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum KernelVerdict
{
    /// Certified: the replay re-derived convertibility.
    Convertible,
    /// Certified: the replay re-derived a refutation.
    NotConvertible,
    /// No verdict, and no evidence for either.
    Declined(ReplayDecline),
}

/// Why the kernel declined a claim.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ReplayDecline
{
    /// The engine claimed no verdict, so there is nothing to replay.
    EngineDeclined,
    /// The replay's step budget ran out.
    Budget,
    /// A fixpoint without termination evidence stood at its unfolding gate:
    /// conversion never unfolds a partial fixpoint, so it neither converts
    /// nor refutes.
    PartialFixpoint,
    /// The trace did not replay.
    Refused(ReplayRefusal),
}

impl fmt::Display for ReplayDecline
{
    /// Why the kernel declined: no dialogue, the budget, a partial fixpoint,
    /// or the trace's refusal.
    ///
    /// # Specification
    /// - ensures: a refused trace writes its [`ReplayRefusal`]; every other
    ///   decline writes its own account.
    /// - fails: propagates the formatter's write failure.
    /// - panics: none.
    /// - executable: none — the formatter owns the emitted text.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`ReplayRefusal`]'s display, reached through the
    ///   decline that carries it.
    /// - witness: `tests::replay_laws::an_ill_formed_query_and_a_path_disagreement_are_two_diagnostics`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::EngineDeclined => f.write_str("no dialogue: the engine claimed no verdict"),
            Self::Budget => f.write_str("the replay's step budget ran out before a verdict"),
            Self::PartialFixpoint => {
                f.write_str("a fixpoint without termination evidence stood at its unfolding gate")
            },
            Self::Refused(refusal) => refusal.fmt(f),
        }
    }
}

/// Why a trace failed to replay.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ReplayRefusal
{
    /// The trace ended while a goal still needed a decision.
    Exhausted,
    /// Every goal closed with decisions still unread, the first at `at`.
    Leftover
    {
        /// The first unread decision.
        at: TracePosition,
    },
    /// The decision at `at` names a rule the goal it was read at does not
    /// admit.
    Inapplicable
    {
        /// The decision that does not apply.
        at: TracePosition,
    },
    /// The decision at `at` would carry a refutation through a frozen constant
    /// or a shortcut, which proves nothing.
    NonAuthoritative
    {
        /// The decision that cannot refute.
        at: TracePosition,
    },
    /// A goal closed against the verdict its derivation owes.
    Contradicted
    {
        /// The next unread decision when the goal closed.
        at: TracePosition,
    },
    /// A term the replay reached does not resolve in the arena, or is in no
    /// shape a rule reads.
    Unreadable,
}

impl ReplayRefusal
{
    /// What the refusal says of the dialogue: a question with no answer, an
    /// answer outside its question's answers, or a well-posed dialogue that
    /// reaches no verdict or the wrong one.
    ///
    /// # Specification
    /// - ensures: [`RefusalClass::IllFormedQuery`] for
    ///   [`ReplayRefusal::Unreadable`]; [`RefusalClass::ForeignAnswer`] for
    ///   [`ReplayRefusal::Inapplicable`] and
    ///   [`ReplayRefusal::NonAuthoritative`];
    ///   [`RefusalClass::PathDisagreement`] for
    ///   [`ReplayRefusal::Contradicted`], [`ReplayRefusal::Exhausted`] and
    ///   [`ReplayRefusal::Leftover`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one replay input per refusal variant, each reaching
    ///   its variant through the public replay, is classed as the table on
    ///   [`KernelVerdict`] states; moving any variant to another class changes
    ///   a row.
    /// - witness: `tests::replay_laws::every_replay_refusal_carries_its_pinned_class`
    #[spec(ensures: |ret| match self {
        Self::Unreadable => matches!(ret, RefusalClass::IllFormedQuery),
        Self::Inapplicable { .. } | Self::NonAuthoritative { .. } => matches!(ret, RefusalClass::ForeignAnswer),
        Self::Contradicted { .. } | Self::Exhausted | Self::Leftover { .. } => matches!(ret, RefusalClass::PathDisagreement),
    })]
    #[inline]
    #[must_use]
    pub const fn class(self) -> RefusalClass
    {
        match self {
            Self::Unreadable => RefusalClass::IllFormedQuery,
            Self::Inapplicable { .. } | Self::NonAuthoritative { .. } => {
                RefusalClass::ForeignAnswer
            },
            Self::Contradicted { .. } | Self::Exhausted | Self::Leftover { .. } => {
                RefusalClass::PathDisagreement
            },
        }
    }
}

impl fmt::Display for ReplayRefusal
{
    /// The refusal's class, then what the replay met.
    ///
    /// # Specification
    /// - ensures: writes [`ReplayRefusal::class`] first, then the refusal's own
    ///   account, naming the decision's position where the refusal has one.
    /// - fails: propagates the formatter's write failure.
    /// - panics: none.
    /// - executable: none — the formatter owns the emitted text.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an ill-formed query and a path disagreement write
    ///   different diagnostics, each led by its class.
    /// - witness: `tests::replay_laws::an_ill_formed_query_and_a_path_disagreement_are_two_diagnostics`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "{}: ", self.class())?;
        match *self {
            Self::Unreadable => {
                f.write_str("the replay reached a term the arena does not resolve or no rule reads")
            },
            Self::Inapplicable { at } => write!(
                f,
                "decision {} names a rule the goal it is read at does not admit",
                usize::from(at)
            ),
            Self::NonAuthoritative { at } => write!(
                f,
                "decision {} refutes through a frozen constant or a shortcut, which proves \
                 nothing",
                usize::from(at)
            ),
            Self::Contradicted { at } => write!(
                f,
                "a goal closed against the verdict its derivation owes, before decision {}",
                usize::from(at)
            ),
            Self::Exhausted => f.write_str("the trace ended while a goal still needed a decision"),
            Self::Leftover { at } => write!(
                f,
                "every goal closed with decision {} still unread",
                usize::from(at)
            ),
        }
    }
}

/// Where a decision stands in a trace, counted from zero.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TracePosition(usize);

impl TracePosition
{
    /// The position `index` decisions from the trace's start.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub(crate) const fn new(index: usize) -> Self
    {
        Self(index)
    }

    /// The count of decisions before the position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub(crate) const fn index(self) -> usize
    {
        self.0
    }
}

impl From<usize> for TracePosition
{
    /// The decision at `position`, counted from zero.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `usize::from(ret) == position`.
    /// - provides: the position's construction.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3: refusals at positions zero, one, and two retain their
    ///   exact decision index; no larger trace is claimed.
    /// - witness: `replay::tests::the_replay_refuses_a_trace_that_does_not_replay`
    /// - witness: `replay::tests::eta_and_force_open_the_suspended_sides`
    #[spec(ensures: |ret| ret.0 == position)]
    #[inline]
    fn from(position: usize) -> Self
    {
        Self(position)
    }
}

impl From<TracePosition> for usize
{
    /// The count `position` carries.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: inverse of `TracePosition::from`.
    /// - provides: the position's count.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3: consuming a decision at the position ceiling cannot
    ///   wrap its reported index; consuming the end leaves it unchanged.
    /// - witness: `replay::tests::trace_consumption_preserves_the_end_and_position_ceiling`
    #[spec(ensures: |ret| ret == position.0)]
    #[inline]
    fn from(position: TracePosition) -> Self
    {
        position.0
    }
}

/// What a refused trace's refusal says of its dialogue.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum RefusalClass
{
    /// A question with no answer: the replay reached a term it cannot read.
    /// Asked, such a query would certify anything, so the replay refuses it
    /// before reading another decision.
    IllFormedQuery,
    /// A recorded answer outside the answers its question admits: a decision
    /// naming a rule the goal does not admit, or a refutation through a frozen
    /// constant or a shortcut.
    ForeignAnswer,
    /// A well-posed dialogue that reaches no verdict or the wrong one: the
    /// trace ran out, ran over, or closed a goal against the verdict it owes.
    PathDisagreement,
}

impl fmt::Display for RefusalClass
{
    /// The class's name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            Self::IllFormedQuery => "an ill-formed query",
            Self::ForeignAnswer => "a foreign answer",
            Self::PathDisagreement => "a path disagreement",
        })
    }
}
