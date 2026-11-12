//! The trace: one fixed-size record for each step of the judgement machine,
//! which the trace layer of the hub's instrument folds into the tree of the
//! judgement's nodes.
//!
//! # The context holds the buffer that each run writes its steps into
//!
//! **Choice.** A [`CheckingContext`](crate::CheckingContext) holds one
//! [`StepBuffer`] when the crate is built with its `instrument` feature and a
//! tracer lends it one. Each run of the machine writes one [`Step`] when it
//! opens and when it closes, and one at each step of its loop: a goal that
//! starts, a goal that the memo answers, a result that the machine hands to a
//! frame, and a rule that refuses. A record names a node and a type by their
//! arena ids, so no record copies a term. The buffer is a vector whose
//! capacity is fixed when the buffer is made. A record past the capacity is
//! not kept. The buffer then answers no steps until it is cleared. So no
//! record allocates, and no reader takes a prefix for the whole run. The
//! thread that holds the context writes the buffer, and the tracer reads it
//! on the same thread between two items. So the buffer has no atomic and no
//! lock. A build without the feature has no field and writes no record. A
//! build with the feature and no buffer pays one branch for each step.
//!
//! **Alternatives.** A lock-free ring for each thread, as the activity layer
//! keeps, lets a thread that does not hold the context read the records. Only
//! the thread that holds the context runs the machine, so no other thread
//! reads them. A sink that each run takes as a type parameter changes each
//! entry of the checker and each of their callers, as the memo tally states.
//!
//! **Reversal.** When the machine forks the goals of one run onto the pool,
//! each worker writes a ring of its own, and the fold merges the rings by a
//! sequence number.
//!
//! # References
//!
//! - `engine-surface.md` § engine-surface-derivation (vault reference
//!   `vault:01a1c68b-1e9e-7942-aa36-b8d9096dec0e`): the columns of a derivation
//!   node, which the records carry.

use alloc::vec::Vec;
use core::num::NonZeroUsize;

use gandr_core_fork::activity::Nanos;
use gandr_core_fork::activity::Slots;
use gandr_core_term::CompTypeId;
use gandr_core_term::Relocated;
use gandr_core_term::ValueTypeId;
use quenchant_shape::shape::Maybe;

pub use crate::answer::unanswered;
use crate::failure::judged;
use crate::refusal::CoreNode;
use crate::refusal::TypeNode;

quenchant_shape::reason_enum! {
    /// Why a context holds no buffer of steps.
    pub mod untraced {
        /// The reason it holds none.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No tracer lent the context a buffer.
            Unlent,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a buffer keeps no whole run of steps.
    pub mod unkept {
        /// The reason it keeps none.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// A step was written past the buffer's capacity, so the steps it
            /// keeps are a prefix of those written.
            Overflowed,
        }
    }
}

/// How many frames wait on the machine's stack when it writes a step.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Height(u32);

impl From<usize> for Height
{
    /// The height of a stack of `frames` frames, up to the representation's
    /// ceiling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(frames: usize) -> Self
    {
        Self(u32::try_from(frames).unwrap_or(u32::MAX))
    }
}

impl From<Height> for u32
{
    /// The height as a number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(height: Height) -> Self
    {
        height.0
    }
}

/// How many binders the memo key of a goal reads.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Cover(u32);

impl From<usize> for Cover
{
    /// The cover of a key that reads `binders` binders, up to the
    /// representation's ceiling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(binders: usize) -> Self
    {
        Self(u32::try_from(binders).unwrap_or(u32::MAX))
    }
}

impl From<Cover> for u32
{
    /// The cover as a number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(cover: Cover) -> Self
    {
        cover.0
    }
}

/// What a finished goal hands to the frame that waits for it.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Handed
{
    /// The value type that the goal synthesised, read through the relocation
    /// it carries.
    Value(Relocated<ValueTypeId>),
    /// The computation type that the goal synthesised.
    Computation(CompTypeId),
    /// A check that succeeded, or a type that formed.
    Checked,
}

/// One step of the judgement machine, as the trace records it.
///
/// A run opens, writes the steps of its loop, and closes. A goal starts at
/// the height of the frame stack where the machine meets it. A result handed
/// at a height finishes each goal of the run that started at that height or
/// above it, so the steps of a run nest as the run's goals do. A run that a
/// rule opens inside another run nests under the goal that the outer run has
/// under way.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Step
{
    /// A run of the machine opens.
    Opened
    {
        /// The clock when the run opened.
        clock: Nanos,
    },
    /// The machine starts the rule of a goal that the memo did not answer.
    Started
    {
        /// The node the goal judges or forms.
        node: CoreNode,
        /// The type the node is checked against, or why it has none.
        against: Maybe<TypeNode, judged::Absent>,
        /// Why the memo gave no answer.
        memo: unanswered::Absent,
        /// The binders that the goal's memo key reads, zero when the memo
        /// keyed no goal.
        cover: Cover,
        /// The height of the frame stack.
        height: Height,
        /// The clock when the goal started.
        clock: Nanos,
    },
    /// The memo answered a goal, which starts and finishes on this step.
    Answered
    {
        /// The node the goal judges or forms.
        node: CoreNode,
        /// The type the node is checked against, or why it has none.
        against: Maybe<TypeNode, judged::Absent>,
        /// The binders that the goal's memo key reads.
        cover: Cover,
        /// The height of the frame stack.
        height: Height,
        /// The clock when the memo answered.
        clock: Nanos,
    },
    /// A goal's rule handed its result: each goal that started at `height`
    /// or above it finishes.
    Finished
    {
        /// What the rule handed.
        handed: Handed,
        /// The height of the frame stack.
        height: Height,
        /// The clock when the rule handed its result.
        clock: Nanos,
    },
    /// A rule refused, or the run's allowance ran out: the innermost goal
    /// under way refused.
    Refused
    {
        /// The clock when the rule refused.
        clock: Nanos,
    },
    /// A run of the machine closes. Each goal of the run still under way
    /// refused.
    Closed
    {
        /// The clock when the run closed.
        clock: Nanos,
    },
}

/// Whether a buffer kept each step written since it was made or cleared.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Fill
{
    /// It kept each one.
    Whole,
    /// A step was written past the capacity and not kept.
    Overflowed,
}

/// The steps of the machine's runs, in the order they were written, in a
/// buffer whose capacity is fixed when it is made.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the steps written since the buffer was made or cleared, oldest
///   first, while they fit its capacity; once a step does not fit, none is
///   answered until the buffer is cleared.
/// - provides: the records that the trace layer folds into the tree of a
///   declaration's judgement.
/// - panics: none.
/// - executable: none — the steps are a projection of the runs, which the
///   buffer does not keep.
///
/// # Adequacy
/// - hypothesis: L3 — a shared pair writes one answered step for each goal that
///   the memo answers and one started step for each goal that it keys first, as
///   the tally counts; a buffer of two slots answers no steps for the pair's
///   check, and an empty run once it is cleared.
/// - witness: `judgement::memo::tests::the_trace_writes_a_step_for_each_consult_the_tally_counts`
/// - witness: `judgement::memo::tests::a_full_buffer_answers_no_steps_until_it_is_cleared`
#[derive(Clone, Debug)]
pub struct StepBuffer
{
    /// The steps, oldest first; the capacity never grows.
    steps: Vec<Step>,
    /// Whether each step written since the buffer was cleared was kept.
    fill: Fill,
    /// The clock that each step reads.
    clock: fn() -> Nanos,
}

impl StepBuffer
{
    /// An empty buffer of `slots` steps, each step reading `clock`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new(
        slots: Slots,
        clock: fn() -> Nanos,
    ) -> Self
    {
        Self {
            steps: Vec::with_capacity(NonZeroUsize::from(slots).get()),
            fill: Fill::Whole,
            clock,
        }
    }

    /// The steps written since the buffer was made or cleared, oldest first,
    /// or [`unkept::Absent::Overflowed`] when one of them did not fit.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn steps(&self) -> Maybe<&[Step], unkept::Absent>
    {
        match self.fill {
            Fill::Whole => Maybe::Present(&self.steps),
            Fill::Overflowed => Maybe::Absent(unkept::Absent::Overflowed),
        }
    }

    /// Forget each step, and keep the capacity.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn clear(&mut self)
    {
        self.steps.clear();
        self.fill = Fill::Whole;
    }

    /// Write the step that `step` makes of the clock's reading, or mark the
    /// buffer overflowed when it is full.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn write<Make>(
        &mut self,
        step: Make,
    ) where
        Make: FnOnce(Nanos) -> Step,
    {
        if self.steps.len() < self.steps.capacity() {
            self.steps.push(step((self.clock)()));
        }
        else {
            self.fill = Fill::Overflowed;
        }
    }
}
