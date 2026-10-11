//! The L machine: an environment machine stepping commands over the
//! two-region [`Store`].
//!
//! A run is a loop over one control state, each iteration one transition:
//!
//! ```text
//! run ⟨p |ε c⟩ ρ        p a μ, unless ε is − and c a μ̃:
//!                         load c, bind α to its mark, run the μ's body
//!                       otherwise: evaluate p to a value, deliver it to c
//! deliver v α ρ         return v to the mark α reads
//! deliver v ★ ρ         return v to the base of the frame region
//! deliver v μ̃x.s ρ      run s with x bound to v
//! deliver v case ρ      run the arm of v's constructor, its fields bound
//! deliver v D(ā; c) ρ   load c, observe v by D with the arguments ā
//! return v m            shrink the frame region to m, then pop
//! pop v                 the top frame receives v; an empty region halts
//! ```
//!
//! Loading a consumer pushes the frames it denotes and answers the mark of
//! the continuation it names: a chain of destructor frames over a
//! covariable or `★` shrinks to that base first, and one over a `μ̃` or a
//! match pushes onto the current region. Observing a thunk by `force` opens
//! its memo cell: a forced cell returns its cached value, an opened one
//! pushes an update frame under the body's return point, and a re-entrant one
//! runs the body inline. Observing a copattern object runs the arm its
//! destructor selects. A suspended `μ` delivered anywhere but to a `μ̃` runs
//! against the consumer it meets.
//!
//! Producers evaluate to heap values without a transition: constructors
//! allocate their evaluated fields, a thunk allocates a fresh cell, a
//! copattern object or a `μ` closes over the environment, and a constant
//! unfolds its [`Definition`] once per machine, a cycle among definitions
//! stopping the run. Every walk is a loop over an explicit stack.

use alloc::boxed::Box;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::Zone;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_theory_cell_complexes::Polarity;

use crate::boundary::StepCount;
use crate::il::CommandArena;
use crate::il::CommandId;
use crate::il::CommandNode;
use crate::il::ConstructorTag;
use crate::il::ConsumerId;
use crate::il::ConsumerNode;
use crate::il::CovariableIndex;
use crate::il::DestructorTag;
use crate::il::ProducerId;
use crate::il::ProducerNode;
use crate::readback::ReadbackRefusal;
use crate::readback::read_back_terminal;
use crate::readback::read_back_value;
use crate::store::ContinuationMark;
use crate::store::Environment;
use crate::store::ForceEntry;
use crate::store::Frame;
use crate::store::HeapValue;
use crate::store::HeapValueId;
use crate::store::Store;
use crate::store::StoreFault;
/// What a constant stands for when a run meets it.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Definition
{
    /// A definition with a body: its focused value, closed.
    Transparent(ProducerId),
    /// A declaration with no body to run, owed or refused, which a run
    /// carries as itself.
    Opaque,
}

/// The definitions a run unfolds, by admission position.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Definitions
{
    /// Each constant's definition, at its admission position.
    entries: Vec<Definition>,
}

impl Definitions
{
    /// No definitions.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new() -> Self
    {
        Self::default()
    }

    /// Admit the next definition.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the definition is admitted at the next position, which is
    ///   returned.
    /// - provides: the one way a constant gets a definition.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a constant admitted transparent unfolds, one admitted
    ///   opaque is carried as itself, and a position never admitted stops the
    ///   run.
    /// - witness: `machine::tests::constants_unfold_once_and_opaque_ones_stay_opaque`
    #[inline]
    #[spec(
        captures: [entry = self.entries.len()],
        ensures: |ret| usize::from(ret) == entry && entry.checked_add(1) == Some(self.entries.len())
            && self.entries.get(entry) == Some(&definition),
    )]
    pub fn push(
        &mut self,
        definition: Definition,
    ) -> ConstantIndex
    {
        let position = ConstantIndex::from(self.entries.len());
        self.entries.push(definition);
        position
    }

    /// The definition admitted at a position, or `None`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn get(
        &self,
        constant: ConstantIndex,
    ) -> Option<Definition>
    {
        self.entries.get(usize::from(constant)).copied()
    }

    /// How many definitions are admitted.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn len(&self) -> crate::NodeCount
    {
        crate::NodeCount::from(self.entries.len())
    }
}

/// Why a run stopped short of a value.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Stuck
{
    /// A native operation refused its arguments, including zero division.
    Primitive(gandr_core_term::primitive::PrimitiveError),
    /// A native operand has no scalar interpretation, retaining its blame site.
    NonScalar(HeapValueId),
    /// A producer variable no binding of the environment answers.
    UnboundVariable
    {
        /// The variable's zone.
        zone: Zone,
        /// The variable's index.
        index: DeBruijnIndex,
    },
    /// A covariable no binding of the environment answers.
    UnboundCovariable(CovariableIndex),
    /// A constant with no admitted definition.
    UndefinedConstant(ConstantIndex),
    /// A constant whose definition needs its own value.
    CyclicConstant(ConstantIndex),
    /// A destructor met a value it cannot observe.
    Unobservable
    {
        /// The value.
        value: HeapValueId,
        /// The destructor.
        head: DestructorTag,
    },
    /// A match has no arm for the value it met.
    Unmatched
    {
        /// The value.
        value: HeapValueId,
        /// The match.
        arms: ConsumerId,
    },
    /// A command the arena does not hold.
    IllFormedCommand(CommandId),
    /// A producer the arena does not hold, or one whose children contradict
    /// its head.
    IllFormedProducer(ProducerId),
    /// A consumer the arena does not hold, or one whose children contradict
    /// its head.
    IllFormedConsumer(ConsumerId),
}

impl fmt::Display for Stuck
{
    /// Names what stopped the run.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            | Self::Primitive(error) => write!(f, "native operation: {error}"),
            | Self::NonScalar(value) => write!(f, "native operand {value} is not a scalar"),
            | Self::UnboundVariable { index, .. } => {
                write!(f, "variable {} is unbound", u32::from(index))
            },
            | Self::UnboundCovariable(index) => write!(f, "covariable {index} is unbound"),
            | Self::UndefinedConstant(constant) => {
                write!(f, "constant {} has no definition", usize::from(constant))
            },
            | Self::CyclicConstant(constant) => {
                write!(f, "constant {} needs its own value", usize::from(constant))
            },
            | Self::Unobservable { value, .. } => write!(f, "value {value} cannot be observed"),
            | Self::Unmatched { value, arms } => {
                write!(f, "match {arms} has no arm for value {value}")
            },
            | Self::IllFormedCommand(id) => write!(f, "command {id} is not well formed"),
            | Self::IllFormedProducer(id) => write!(f, "producer {id} is not well formed"),
            | Self::IllFormedConsumer(id) => write!(f, "consumer {id} is not well formed"),
        }
    }
}

/// How a run ended.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Outcome
{
    /// The value returned to an empty frame region.
    Halted(HeapValueId),
    /// The run stopped short of a value.
    Stuck(Stuck),
}

/// Why a run could not go on.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum MachineFault
{
    /// The step budget ran out.
    OutOfSteps,
    /// The store refused an operation.
    Store(StoreFault),
}

impl fmt::Display for MachineFault
{
    /// Names the fault.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            | Self::OutOfSteps => f.write_str("the step budget ran out"),
            | Self::Store(fault) => write!(f, "the store refused: {fault}"),
        }
    }
}

impl core::error::Error for MachineFault
{
}

impl From<StoreFault> for MachineFault
{
    /// Carries the store's refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(fault: StoreFault) -> Self
    {
        Self::Store(fault)
    }
}

/// What stops a transition: the run is stuck, or it faulted.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Stop
{
    /// The run is stuck.
    Stuck(Stuck),
    /// The run faulted.
    Fault(MachineFault),
}

impl From<Stuck> for Stop
{
    /// Stops on a stuck state.
    ///
    /// # Specification
    /// trivial.
    fn from(stuck: Stuck) -> Self
    {
        Self::Stuck(stuck)
    }
}

impl From<StoreFault> for Stop
{
    /// Stops on a store fault.
    ///
    /// # Specification
    /// trivial.
    fn from(fault: StoreFault) -> Self
    {
        Self::Fault(MachineFault::Store(fault))
    }
}

/// The machine's control state.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Control
{
    /// Run a command under an environment.
    Run(CommandId, Environment),
    /// Hand a value to a consumer under an environment.
    Deliver(HeapValueId, ConsumerId, Environment),
    /// Return a value to the continuation at a mark.
    Return(HeapValueId, ContinuationMark),
    /// Hand a value to the top of the frame region.
    Pop(HeapValueId),
}

/// What one transition leads to.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Next
{
    /// The next control state.
    Continue(Control),
    /// The run halted with a value.
    Halt(HeapValueId),
}

/// How far a constant's unfolding has got.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Unfolding
{
    /// Not yet met.
    Pending,
    /// Being evaluated: meeting it again is a cycle.
    Running,
    /// Evaluated, to this value.
    Done(HeapValueId),
}

/// The position of a field in a constructed value, counted from the left.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct FieldPosition(usize);

/// One pending unit of producer evaluation.
#[derive(Clone, Copy, Debug)]
enum Evaluation
{
    /// Apply a table operation to the evaluated operands.
    Primitive(ProducerId),
    /// Evaluate a producer under an environment; leaves one value.
    Producer(ProducerId, Environment),
    /// Pop a constructor's evaluated fields and allocate it.
    Construct(ProducerId),
    /// Record the value on top as a constant's.
    Remember(ConstantIndex, ProducerId),
}

/// The L machine over one arena and its definitions.
#[derive(Clone, Debug)]
pub struct Machine<'program>
{
    /// The commands run.
    arena: &'program CommandArena,
    /// The constants' definitions.
    definitions: &'program Definitions,
    /// The heap and frame regions.
    store: Store,
    /// Each constant's unfolding, by admission position.
    unfoldings: Vec<Unfolding>,
}

impl<'program> Machine<'program>
{
    /// A machine with an empty store.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new(
        arena: &'program CommandArena,
        definitions: &'program Definitions,
    ) -> Self
    {
        Self {
            arena,
            definitions,
            store: Store::new(),
            unfoldings: alloc::vec![Unfolding::Pending; usize::from(definitions.len())],
        }
    }

    /// The store, for readback and inspection.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn store(&self) -> &Store
    {
        &self.store
    }

    /// Read a run's terminal back as a core computation.
    ///
    /// # Specification
    /// - requires: `value` is a value this machine's runs allocated.
    /// - ensures: on success `return v` for a positive value `v`, and the
    ///   function a copattern object denotes; a thunk's or a function's body is
    ///   decoded and closed over its captured environment's readbacks.
    /// - provides: the readback of a halted run.
    /// - fails: [`ReadbackRefusal`] naming the first value with no core
    ///   reading; `core` is then exactly as on entry.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a function and a thunk read back closed over their
    ///   environments, and a suspended capture is refused with the core arena
    ///   back at its mark.
    /// - witness: `machine::tests::a_function_terminal_reads_back_closed_over_its_environment`
    /// - witness: `machine::tests::a_thunk_reads_back_closed_over_its_environment`
    /// - witness: `machine::tests::a_suspended_capture_has_no_reading`
    #[inline]
    #[spec(
        requires: self.store.value(value).is_some(),
        captures: [entry = core.watermark()],
        ensures: |ret| match ret {
            | Ok(read) => core.computation(read).is_some(),
            | Err(_) => core.watermark() == entry,
        },
    )]
    pub fn read_back(
        &self,
        value: HeapValueId,
        core: &mut CoreArena,
    ) -> Result<ComputationId, ReadbackRefusal>
    {
        read_back_terminal(self.arena, &self.store, value, core)
    }

    /// Read a positive value back as a core value.
    ///
    /// # Specification
    /// - requires: as [`Self::read_back`].
    /// - ensures: on success the closed core value `value` denotes.
    /// - provides: the readback of a value, such as a constant's.
    /// - fails: as [`Self::read_back`], and for a closure, with the same
    ///   rollback.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::read_back`].
    /// - witness: `machine::tests::a_thunk_reads_back_closed_over_its_environment`
    #[inline]
    #[spec(
        requires: self.store.value(value).is_some(),
        captures: [entry = core.watermark()],
        ensures: |ret| match ret {
            | Ok(read) => core.value(read).is_some(),
            | Err(_) => core.watermark() == entry,
        },
    )]
    pub fn read_back_value(
        &self,
        value: HeapValueId,
        core: &mut CoreArena,
    ) -> Result<ValueId, ReadbackRefusal>
    {
        read_back_value(self.arena, &self.store, value, core)
    }

    /// Run a command from an empty frame region.
    ///
    /// # Specification
    /// - requires: `command` passes [`check_command`](crate::check_command)
    ///   closed; otherwise the run may stop [`Outcome::Stuck`] on what the
    ///   check would refuse.
    /// - ensures: the frame region is first shrunk to its base, declining every
    ///   forcing an earlier run abandoned; then [`Outcome::Halted`] with the
    ///   value returned to the empty region, or [`Outcome::Stuck`] naming what
    ///   stopped the run. The heap and the constants' values persist across
    ///   runs of one machine.
    /// - provides: the L machine's one entry.
    /// - fails: [`MachineFault::OutOfSteps`] after `budget` transitions, and
    ///   [`MachineFault::Store`] when the store refuses an operation.
    /// - panics: none.
    /// - intension: one loop iteration per transition; producer evaluation is
    ///   linear in the producer's size and runs within a transition.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — generated closed pure terms and stuck outcomes are
    ///   compared with the independent normaliser. L3 — hand-built formers, the
    ///   polarity-sensitive critical pair, exact budget boundaries and nominal
    ///   memo observations distinguish wrong reductions and ordering; this
    ///   covers the bounded generator and named cases, not all programs.
    /// - witness: `machine::tests::ret_is_a_terminal_value`
    /// - witness: `machine::tests::bind_threads_a_value`
    /// - witness: `machine::tests::force_runs_a_thunk_body`
    /// - witness: `machine::tests::case_selects_the_matching_arm`
    /// - witness: `machine::tests::application_binds_the_argument`
    /// - witness: `machine::tests::a_shared_thunk_is_forced_once`
    /// - witness: `machine::tests::constants_unfold_once_and_opaque_ones_stay_opaque`
    /// - witness: `machine::tests::the_step_budget_bounds_a_run`
    /// - witness: `tests::differential::the_l_machine_agrees_with_normalisation_by_evaluation`
    /// - witness: `machine::tests::polarity_decides_whether_a_capture_is_evaluated`
    /// - witness: `machine::tests::forcing_reentry_shares_updates_and_abandonment_declines_them`
    /// - witness: `machine::tests::failed_unfolding_resets_every_active_constant`
    #[inline]
    #[spec(ensures: |ref ret| match ret.as_ref() {
        | Ok(&Outcome::Halted(value)) => usize::from(budget) > 0 && self.store.value(value).is_some()
            && self.store.mark() == ContinuationMark::BASE,
        | Ok(&Outcome::Stuck(_)) => usize::from(budget) > 0,
        | Err(_) => true,
    })]
    pub fn run(
        &mut self,
        command: CommandId,
        budget: StepCount,
    ) -> Result<Outcome, MachineFault>
    {
        self.store.shrink_to(ContinuationMark::BASE)?;
        let mut control = Control::Run(command, Environment::EMPTY);
        let mut remaining = usize::from(budget);
        loop {
            remaining = remaining.checked_sub(1).ok_or(MachineFault::OutOfSteps)?;
            match self.step(control) {
                | Ok(Next::Continue(next)) => control = next,
                | Ok(Next::Halt(value)) => return Ok(Outcome::Halted(value)),
                | Err(Stop::Stuck(stuck)) => return Ok(Outcome::Stuck(stuck)),
                | Err(Stop::Fault(fault)) => return Err(fault),
            }
        }
    }

    /// One transition.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the transition the module documentation's table gives.
    /// - provides: the machine's step relation.
    /// - fails: a stuck state or a store fault.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the return path has an exact transition budget,
    ///   reentrant forcing shares the update continuation, and a halted run has
    ///   no frames. L2 — composed reductions compare with an independent
    ///   normaliser, distinguishing swapped control states and skipped returns.
    /// - witness: `machine::tests::the_step_budget_bounds_a_run`
    /// - witness: `machine::tests::forcing_reentry_shares_updates_and_abandonment_declines_them`
    /// - witness: `tests::differential::the_l_machine_agrees_with_normalisation_by_evaluation`
    #[spec(ensures: |ref ret| match (control, ret.as_ref().copied()) {
        | (Control::Return(value, mark), Ok(next)) => next == Next::Continue(Control::Pop(value)) && self.store.mark() == mark,
        | (Control::Pop(value), Ok(Next::Halt(held))) => held == value && self.store.mark() == ContinuationMark::BASE,
        | (Control::Run(..) | Control::Deliver(..), Ok(Next::Halt(_))) => false,
        | _ => true,
    })]
    fn step(
        &mut self,
        control: Control,
    ) -> Result<Next, Stop>
    {
        match control {
            | Control::Run(command, environment) => self.cut(command, environment),
            | Control::Deliver(value, consumer, environment) => {
                self.deliver(value, consumer, environment)
            },
            | Control::Return(value, mark) => {
                self.store.shrink_to(mark)?;
                Ok(Next::Continue(Control::Pop(value)))
            },
            | Control::Pop(value) => self.pop(value),
        }
    }

    /// Run a cut.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a `μ` producer runs its body against its loaded consumer,
    ///   except at a negative cut against a `μ̃`, where it is suspended and
    ///   bound; any other producer is evaluated and delivered.
    /// - provides: the critical pair's resolution by the cut's polarity.
    /// - fails: as [`Self::step`].
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one closed capture whose body would get stuck is cut
    ///   against an ignoring binder at each polarity. The positive cut is stuck
    ///   and the negative cut returns unit, distinguishing the critical pair,
    ///   not merely the shape of the next control state. Missing commands have
    ///   exact refusals. L2 — pure reductions compare with normalisation.
    /// - witness: `machine::tests::polarity_decides_whether_a_capture_is_evaluated`
    /// - witness: `machine::tests::transition_refusals_name_the_first_invalid_endpoint`
    /// - witness: `tests::differential::the_l_machine_agrees_with_normalisation_by_evaluation`
    #[spec(ensures: |ref ret| match ret.as_ref().copied() {
        | Err(_) => self.arena.command(id).is_some() || *ret == Err(Stop::Stuck(Stuck::IllFormedCommand(id))),
        | Ok(next) => self.arena.command(id).is_some_and(|&CommandNode::Cut { polarity, producer, consumer }| {
            let strict_capture = self.arena.producer(producer).and_then(|node| match *node {
                | ProducerNode::Mu { body } if polarity != Polarity::Negative
                    || !matches!(self.arena.consumer(consumer), Some(&ConsumerNode::MuTilde { .. })) => Some(body),
                | _ => None,
            });
            match (strict_capture, next) {
                | (Some(body), Next::Continue(Control::Run(found, inner))) => body == found
                    && inner.values() == environment.values()
                    && self.store.lookup_covalue(inner, CovariableIndex::from(0_u32)) == Some(self.store.mark()),
                | (None, Next::Continue(Control::Deliver(value, found, inner))) => consumer == found
                    && inner == environment && self.store.value(value).is_some(),
                | _ => false,
            }
        }),
    })]
    fn cut(
        &mut self,
        id: CommandId,
        environment: Environment,
    ) -> Result<Next, Stop>
    {
        let arena = self.arena;
        let &CommandNode::Cut {
            polarity,
            producer,
            consumer,
        } = arena.command(id).ok_or(Stuck::IllFormedCommand(id))?;
        if let Some(&ProducerNode::Mu { body }) = arena.producer(producer) {
            let by_name = polarity == Polarity::Negative
                && matches!(
                    arena.consumer(consumer),
                    Some(&ConsumerNode::MuTilde { .. })
                );
            if !by_name {
                let mark = self.load(consumer, environment)?;
                let inner = self.store.bind_covalue(environment, mark)?;
                return Ok(Next::Continue(Control::Run(body, inner)));
            }
        }
        let value = self.evaluate(producer, environment)?;
        Ok(Next::Continue(Control::Deliver(
            value,
            consumer,
            environment,
        )))
    }

    /// Hand a value to a consumer.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the delivery rows of the module documentation's table; a
    ///   suspended `μ` met by anything but a `μ̃` runs against it.
    /// - provides: the consumer side of a cut.
    /// - fails: as [`Self::step`].
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — direct return, binding, matching, forcing and the
    ///   polarity-sensitive capture have distinct terminal or stuck outcomes;
    ///   unbound and missing consumers have exact refusals. L2 — generated pure
    ///   spines compare with normalisation. These observe consumer dispatch,
    ///   environment extension and continuation selection.
    /// - witness: `machine::tests::polarity_decides_whether_a_capture_is_evaluated`
    /// - witness: `machine::tests::transition_refusals_name_the_first_invalid_endpoint`
    /// - witness: `machine::tests::pattern_fields_bind_last_innermost`
    /// - witness: `tests::differential::hand_built_pure_spine_cases_agree`
    #[spec(ensures: |ref ret| ret.is_err() || ret.as_ref().is_ok_and(|&next|
        self.arena.consumer(consumer).is_some_and(|node| {
            if let Some((body, captured)) = self.suspended_capture(value)
                && !matches!(node, &ConsumerNode::MuTilde { .. }) {
                return matches!(next, Next::Continue(Control::Run(found, inner)) if found == body
                    && inner.values() == captured.values()
                    && self.store.lookup_covalue(inner, CovariableIndex::from(0_u32)) == Some(self.store.mark()));
            }
            match *node {
                | ConsumerNode::Top => next == Next::Continue(Control::Return(value, ContinuationMark::BASE)),
                | ConsumerNode::Covariable(index) => matches!(next, Next::Continue(Control::Return(found, mark))
                    if found == value && self.store.lookup_covalue(environment, index) == Some(mark)),
                | ConsumerNode::MuTilde { body } => matches!(next, Next::Continue(Control::Run(found, inner)) if found == body
                    && inner.covalues() == environment.covalues()
                    && self.store.lookup_value(inner, DeBruijnIndex::from(0_u32)) == Some(value)),
                | ConsumerNode::Case { .. } => matches!(next, Next::Continue(Control::Run(..))),
                | ConsumerNode::Destructor { .. } => matches!(next, Next::Continue(Control::Run(..) | Control::Return(..))),
            }
        })))]
    fn deliver(
        &mut self,
        value: HeapValueId,
        consumer: ConsumerId,
        environment: Environment,
    ) -> Result<Next, Stop>
    {
        let arena = self.arena;
        let node = arena
            .consumer(consumer)
            .ok_or(Stuck::IllFormedConsumer(consumer))?;
        if let Some((body, captured)) = self.suspended_capture(value)
            && !matches!(*node, ConsumerNode::MuTilde { .. })
        {
            let mark = self.load(consumer, environment)?;
            let inner = self.store.bind_covalue(captured, mark)?;
            return Ok(Next::Continue(Control::Run(body, inner)));
        }
        match *node {
            | ConsumerNode::Covariable(index) => {
                let mark = self
                    .store
                    .lookup_covalue(environment, index)
                    .ok_or(Stuck::UnboundCovariable(index))?;
                Ok(Next::Continue(Control::Return(value, mark)))
            },
            | ConsumerNode::Top => Ok(Next::Continue(Control::Return(
                value,
                ContinuationMark::BASE,
            ))),
            | ConsumerNode::MuTilde { body } => {
                let inner = self.store.bind_value(environment, value)?;
                Ok(Next::Continue(Control::Run(body, inner)))
            },
            | ConsumerNode::Case { .. } => self.select(value, consumer, environment),
            | ConsumerNode::Destructor {
                tag,
                ref producers,
                ref consumers,
            } => {
                let &[then] = consumers.as_ref()
                else {
                    return Err(Stuck::IllFormedConsumer(consumer).into());
                };
                let arguments = self.evaluate_all(producers, environment)?;
                let mark = self.load(then, environment)?;
                self.observe(value, tag, &arguments, mark)
            },
        }
    }

    /// The body and environment of a suspended `μ`, when `value` is one.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the body and captured environment exactly when the held value
    ///   is a closure of a present capture producer; otherwise none.
    /// - provides: delayed capture recognition before ordinary delivery.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — delaying a capture at a negative cut and later
    ///   delivering one to a non-binder distinguish eager capture dispatch from
    ///   ordinary closures. Missing and non-capture values return none.
    /// - witness: `machine::tests::polarity_decides_whether_a_capture_is_evaluated`
    /// - witness: `machine::tests::transition_refusals_name_the_first_invalid_endpoint`
    #[spec(ensures: |ret| ret == match self.store.value(value) {
        | Some(&HeapValue::Closure { producer, environment }) => match self.arena.producer(producer) {
            | Some(&ProducerNode::Mu { body }) => Some((body, environment)),
            | _ => None,
        },
        | _ => None,
    })]
    fn suspended_capture(
        &self,
        value: HeapValueId,
    ) -> Option<(CommandId, Environment)>
    {
        let &HeapValue::Closure {
            producer,
            environment,
        } = self.store.value(value)?
        else {
            return None;
        };
        let arena = self.arena;
        let &ProducerNode::Mu { body } = arena.producer(producer)?
        else {
            return None;
        };
        Some((body, environment))
    }

    /// Hand a value to the top frame, or halt on an empty region.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a destructor frame observes the value, a binder frame binds
    ///   it, a match frame selects on it, and an update frame writes it back to
    ///   its cell and passes it on.
    /// - provides: returning into the frame region.
    /// - fails: as [`Self::step`].
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — returning through bind, match, destructor and update
    ///   frames is observed by the resulting value and memo cell; an empty
    ///   region halts at the exact return budget. Reentrant forcing
    ///   distinguishes duplicate updates and skipped write-back.
    /// - witness: `machine::tests::the_step_budget_bounds_a_run`
    /// - witness: `machine::tests::bind_threads_a_value`
    /// - witness: `machine::tests::case_selects_the_matching_arm`
    /// - witness: `machine::tests::a_shared_thunk_is_forced_once`
    /// - witness: `machine::tests::forcing_reentry_shares_updates_and_abandonment_declines_them`
    #[spec(
        captures: [height = self.store.frame_height()],
        ensures: |ref ret| if usize::from(height) == 0 { *ret == Ok(Next::Halt(value)) }
            else { !matches!(ret, &Ok(Next::Halt(_))) },
    )]
    fn pop(
        &mut self,
        value: HeapValueId,
    ) -> Result<Next, Stop>
    {
        let Some(frame) = self.store.pop_frame()
        else {
            return Ok(Next::Halt(value));
        };
        match frame {
            | Frame::Destructor { tag, arguments } => {
                let mark = self.store.mark();
                self.observe(value, tag, &arguments, mark)
            },
            | Frame::Bind { body, environment } => {
                let inner = self.store.bind_value(environment, value)?;
                Ok(Next::Continue(Control::Run(body, inner)))
            },
            | Frame::Case { arms, environment } => self.select(value, arms, environment),
            | Frame::Update { cell } => {
                self.store.write_back(cell, value)?;
                Ok(Next::Continue(Control::Pop(value)))
            },
        }
    }

    /// Observe a value by a destructor, continuing at `mark`.
    ///
    /// # Specification
    /// - requires: the frame region's top is `mark`.
    /// - ensures: `force` on a thunk follows its cell's protocol; any
    ///   destructor on a copattern object runs the arm it selects with the
    ///   arguments and `mark` bound.
    /// - provides: the elimination of the negative values and thunks.
    /// - fails: [`Stuck::Unobservable`] for any other value or a missing arm,
    ///   and the store's faults.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — first force, reentry and a cached force distinguish
    ///   the three cell states by continuation marks, the unique update frame
    ///   and exact cached address. Abandonment declines the update before a new
    ///   run. L2 — captured and curried functions compare with normal forms.
    /// - witness: `machine::tests::forcing_reentry_shares_updates_and_abandonment_declines_them`
    /// - witness: `machine::tests::a_shared_thunk_is_forced_once`
    /// - witness: `machine::tests::transition_refusals_name_the_first_invalid_endpoint`
    /// - witness: `tests::differential::hand_built_exact_readback_cases_agree`
    #[spec(
        requires: self.store.mark() == mark,
        captures: [forcing = match self.store.value(value) {
            | Some(&HeapValue::Thunk { body, environment, cell }) if head == DestructorTag::Force =>
                Some((body, environment, cell, self.store.cell(cell))),
            | _ => None,
        }],
        ensures: |ref ret| match ret.as_ref().copied() {
            | Err(_) => true,
            | Ok(next) => if let Some((body, captured, cell, state)) = forcing {
                match state {
                    | Some(crate::store::MemoState::Forced(cached)) => next == Next::Continue(Control::Return(cached, mark))
                        && self.store.cell(cell) == state && self.store.mark() == mark,
                    | Some(crate::store::MemoState::Unforced | crate::store::MemoState::InProgress) =>
                        matches!(next, Next::Continue(Control::Run(found, inner)) if found == body
                            && inner.values() == captured.values()
                            && self.store.lookup_covalue(inner, CovariableIndex::from(0_u32)) == Some(self.store.mark()))
                        && self.store.cell(cell) == Some(crate::store::MemoState::InProgress)
                        && if state == Some(crate::store::MemoState::Unforced) {
                            usize::from(mark.height()).checked_add(1) == Some(usize::from(self.store.frame_height()))
                        } else { self.store.mark() == mark },
                    | None => false,
                }
            } else {
                self.store.value(value).is_some_and(|held| match *held {
                    | HeapValue::Closure { producer, .. } => self.arena.producer(producer).is_some_and(|node|
                        matches!(*node, ProducerNode::Cocase { ref arms } if arms.iter().find(|arm| arm.destructor == head)
                            .is_some_and(|arm| matches!(next, Next::Continue(Control::Run(body, inner)) if body == arm.body
                                && self.store.lookup_covalue(inner, CovariableIndex::from(0_u32)) == Some(mark)
                                && arguments.iter().rev().enumerate().all(|(position, argument)|
                                    u32::try_from(position).is_ok_and(|index|
                                        self.store.lookup_value(inner, DeBruijnIndex::from(index)) == Some(*argument))))))),
                    | _ => false,
                })
            },
        },
    )]
    fn observe(
        &mut self,
        value: HeapValueId,
        head: DestructorTag,
        arguments: &[HeapValueId],
        mark: ContinuationMark,
    ) -> Result<Next, Stop>
    {
        let unobservable = Stuck::Unobservable { value, head };
        match self.store.value(value) {
            | Some(&HeapValue::Thunk {
                body,
                environment,
                cell,
            }) if head == DestructorTag::Force => match self.store.begin_force(cell)? {
                | ForceEntry::Cached(cached) => Ok(Next::Continue(Control::Return(cached, mark))),
                | ForceEntry::Opened => {
                    self.store.push_frame(Frame::Update { cell })?;
                    let inner = self.store.bind_covalue(environment, self.store.mark())?;
                    Ok(Next::Continue(Control::Run(body, inner)))
                },
                | ForceEntry::Reentrant => {
                    let inner = self.store.bind_covalue(environment, mark)?;
                    Ok(Next::Continue(Control::Run(body, inner)))
                },
            },
            | Some(&HeapValue::Closure {
                producer,
                environment,
            }) => {
                let arena = self.arena;
                let Some(object) = arena.producer(producer)
                else {
                    return Err(unobservable.into());
                };
                let ProducerNode::Cocase { ref arms } = *object
                else {
                    return Err(unobservable.into());
                };
                let arm = arms
                    .iter()
                    .find(|arm| arm.destructor == head)
                    .ok_or(unobservable)?;
                let mut inner = environment;
                for &argument in arguments {
                    inner = self.store.bind_value(inner, argument)?;
                }
                inner = self.store.bind_covalue(inner, mark)?;
                Ok(Next::Continue(Control::Run(arm.body, inner)))
            },
            | _ => Err(unobservable.into()),
        }
    }

    /// Run the arm a match selects for a value, its fields bound left to
    /// right.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the arm of the value's constructor runs under `environment`
    ///   extended by the value's fields, the last innermost.
    /// - provides: the elimination of the constructed values.
    /// - fails: [`Stuck::Unmatched`] for a value that is not constructed or a
    ///   constructor no arm answers; [`Stuck::IllFormedConsumer`] when `arms`
    ///   is not a match.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a pair match returns both unequal fields in source
    ///   order after binding the last innermost, distinguishing omitted,
    ///   duplicated and reversed fields. Missing and non-match consumers and
    ///   unhandled heads have exact refusals; both sum injections are compared
    ///   independently in the pure-spine cases.
    /// - witness: `machine::tests::pattern_fields_bind_last_innermost`
    /// - witness: `machine::tests::transition_refusals_name_the_first_invalid_endpoint`
    /// - witness: `tests::differential::hand_built_pure_spine_cases_agree`
    #[spec(ensures: |ref ret| ret.is_err() || ret.as_ref().is_ok_and(|&next|
        self.arena.consumer(arms).zip(self.store.value(value)).is_some_and(|(node, held)|
            match (node, held) {
                | (&ConsumerNode::Case { arms: ref choices }, &HeapValue::Constructed { ref tag, ref fields }) =>
                    choices.iter().find(|arm| arm.constructor == *tag).is_some_and(|arm|
                        matches!(next, Next::Continue(Control::Run(body, inner)) if body == arm.body
                            && inner.covalues() == environment.covalues()
                            && fields.iter().rev().enumerate().all(|(position, field)|
                                u32::try_from(position).is_ok_and(|index|
                                    self.store.lookup_value(inner, DeBruijnIndex::from(index)) == Some(*field))))),
                | _ => false,
            })))]
    fn select(
        &mut self,
        value: HeapValueId,
        arms: ConsumerId,
        environment: Environment,
    ) -> Result<Next, Stop>
    {
        let arena = self.arena;
        let Some(node) = arena.consumer(arms)
        else {
            return Err(Stuck::IllFormedConsumer(arms).into());
        };
        let ConsumerNode::Case { arms: ref choices } = *node
        else {
            return Err(Stuck::IllFormedConsumer(arms).into());
        };
        let unmatched = Stuck::Unmatched { value, arms };
        let Some(held) = self.store.value(value)
        else {
            return Err(unmatched.into());
        };
        let HeapValue::Constructed { ref tag, .. } = *held
        else {
            return Err(unmatched.into());
        };
        let arm = choices
            .iter()
            .find(|arm| arm.constructor == *tag)
            .ok_or(unmatched)?;
        let mut inner = environment;
        let mut position = FieldPosition(0);
        while let Some(field) = self.field(value, position) {
            inner = self.store.bind_value(inner, field)?;
            position = FieldPosition(position.0.saturating_add(1));
        }
        Ok(Next::Continue(Control::Run(arm.body, inner)))
    }

    /// The field at `position` of a constructed value, or `None`.
    ///
    /// # Specification
    /// trivial.
    fn field(
        &self,
        value: HeapValueId,
        position: FieldPosition,
    ) -> Option<HeapValueId>
    {
        let HeapValue::Constructed { ref fields, .. } = *self.store.value(value)?
        else {
            return None;
        };
        fields.get(position.0).copied()
    }

    /// Push the frames a consumer denotes and answer its continuation's mark.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a chain of destructor frames over a covariable or `★` shrinks
    ///   the region to that base, then pushes the chain's frames, the first
    ///   observation on top; a chain over a `μ̃` or a match pushes its frames
    ///   onto the current region. The answer is the mark of the resulting top.
    /// - provides: a consumer as a continuation.
    /// - fails: an unbound covariable, a frame with other than one
    ///   continuation, and the store's faults.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the critical pair loads a binder continuation;
    ///   reentry and abandonment observe exact frame marks, and malformed
    ///   continuations and unbound covariables have exact refusals. L2 —
    ///   composed application and forcing spines compare with normalisation,
    ///   distinguishing reversed frames and the wrong base continuation.
    /// - witness: `machine::tests::polarity_decides_whether_a_capture_is_evaluated`
    /// - witness: `machine::tests::forcing_reentry_shares_updates_and_abandonment_declines_them`
    /// - witness: `machine::tests::transition_refusals_name_the_first_invalid_endpoint`
    /// - witness: `tests::differential::hand_built_pure_spine_cases_agree`
    #[spec(
        captures: [height = self.store.frame_height()],
        ensures: |ref ret| ret.is_err() || ret.as_ref().is_ok_and(|&mark| self.store.mark() == mark
            && self.arena.consumer(consumer).is_some_and(|node| match *node {
                | ConsumerNode::Top => mark == ContinuationMark::BASE,
                | ConsumerNode::Covariable(index) => self.store.lookup_covalue(environment, index) == Some(mark),
                | ConsumerNode::MuTilde { .. } | ConsumerNode::Case { .. } => usize::from(height).checked_add(1) == Some(usize::from(mark.height())),
                | ConsumerNode::Destructor { .. } => true,
            })),
    )]
    fn load(
        &mut self,
        consumer: ConsumerId,
        environment: Environment,
    ) -> Result<ContinuationMark, Stop>
    {
        let arena = self.arena;
        let mut pending: Vec<Frame> = Vec::new();
        let mut cursor = consumer;
        let base = loop {
            let node = arena
                .consumer(cursor)
                .ok_or(Stuck::IllFormedConsumer(cursor))?;
            match *node {
                | ConsumerNode::Covariable(index) => {
                    let mark = self
                        .store
                        .lookup_covalue(environment, index)
                        .ok_or(Stuck::UnboundCovariable(index))?;
                    break Some(mark);
                },
                | ConsumerNode::Top => break Some(ContinuationMark::BASE),
                | ConsumerNode::MuTilde { body } => {
                    pending.push(Frame::Bind { body, environment });
                    break None;
                },
                | ConsumerNode::Case { .. } => {
                    pending.push(Frame::Case {
                        arms: cursor,
                        environment,
                    });
                    break None;
                },
                | ConsumerNode::Destructor {
                    tag,
                    ref producers,
                    ref consumers,
                } => {
                    let &[then] = consumers.as_ref()
                    else {
                        return Err(Stuck::IllFormedConsumer(cursor).into());
                    };
                    let arguments = self.evaluate_all(producers, environment)?;
                    pending.push(Frame::Destructor { tag, arguments });
                    cursor = then;
                },
            }
        };
        if let Some(base) = base {
            self.store.shrink_to(base)?;
        }
        while let Some(frame) = pending.pop() {
            self.store.push_frame(frame)?;
        }
        Ok(self.store.mark())
    }

    /// Evaluate producers left to right.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one value per producer, in order.
    /// - provides: a frame's or constructor's arguments.
    /// - fails: as [`Self::evaluate`].
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two unequal literal producers are evaluated as an
    ///   argument list and observed in order; the same payloads pass through a
    ///   two-field match. L2 — application spines compare with the normaliser.
    ///   These distinguish reordering, omission and duplicated results.
    /// - witness: `machine::tests::pattern_fields_bind_last_innermost`
    /// - witness: `tests::differential::hand_built_pure_spine_cases_agree`
    #[spec(ensures: |ref ret| ret.is_err() || ret.as_ref().is_ok_and(|values|
        values.len() == producers.len() && values.iter().all(|value| self.store.value(*value).is_some())))]
    fn evaluate_all(
        &mut self,
        producers: &[ProducerId],
        environment: Environment,
    ) -> Result<Box<[HeapValueId]>, Stop>
    {
        let mut values = Vec::with_capacity(producers.len());
        for &producer in producers {
            values.push(self.evaluate(producer, environment)?);
        }
        Ok(values.into_boxed_slice())
    }

    /// Evaluate a producer to a heap value.
    ///
    /// # Specification
    /// - requires: no constant unfolding is currently running.
    /// - ensures: a variable reads its binding; a literal and a constructor
    ///   over its evaluated fields are allocated; a thunk is allocated with a
    ///   fresh cell; a copattern object or a `μ` closes over `environment`; a
    ///   constant reads its value, unfolding its definition in the empty
    ///   environment the first time it is met.
    /// - provides: the value side of a cut.
    /// - fails: an unbound variable, an undefined or cyclic constant, a
    ///   constructor carrying a consumer, and the store's faults; a constant
    ///   whose unfolding was cut short is reset, so a later run meets it
    ///   afresh.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exact constant identities, a nested failed unfolding
    ///   followed by a retry, both variable zones and malformed endpoints
    ///   distinguish wrong lookup and poisoned memo state. Distinct constructor
    ///   fields observe order. L2 — generated pure terms compare with the
    ///   independent normaliser.
    /// - witness: `machine::tests::constants_unfold_once_and_opaque_ones_stay_opaque`
    /// - witness: `machine::tests::failed_unfolding_resets_every_active_constant`
    /// - witness: `machine::tests::transition_refusals_name_the_first_invalid_endpoint`
    /// - witness: `machine::tests::pattern_fields_bind_last_innermost`
    /// - witness: `tests::differential::the_l_machine_agrees_with_normalisation_by_evaluation`
    #[spec(
        requires: !self.unfoldings.contains(&Unfolding::Running),
        ensures: |ref ret| !self.unfoldings.contains(&Unfolding::Running)
            && (ret.is_err() || ret.as_ref().is_ok_and(|&value|
                self.arena.producer(root).zip(self.store.value(value)).is_some_and(|(node, held)| match *node {
                    | ProducerNode::Primitive { .. } => self.scalar(value).is_ok(),
                    | ProducerNode::Variable { zone, index } => zone == Zone::Intuitionistic
                        && self.store.lookup_value(environment, index) == Some(value),
                    | ProducerNode::Constant(constant) => self.unfolding(constant) == Ok(Unfolding::Done(value)),
                    | ProducerNode::Literal(ref literal) => matches!(*held, HeapValue::Literal(ref found) if literal == found),
                    | ProducerNode::Constructor { ref tag, ref producers, ref consumers } => consumers.is_empty()
                        && matches!(*held, HeapValue::Constructed { tag: ref found, ref fields } if tag == found && fields.len() == producers.len()),
                    | ProducerNode::Thunk { body } => matches!(*held, HeapValue::Thunk { body: found, environment: captured, cell }
                        if found == body && captured == environment && self.store.cell(cell) == Some(crate::store::MemoState::Unforced)),
                    | ProducerNode::Cocase { .. } | ProducerNode::Mu { .. } => matches!(*held,
                        HeapValue::Closure { producer, environment: captured } if producer == root && captured == environment),
                }))),
    )]
    fn evaluate(
        &mut self,
        root: ProducerId,
        environment: Environment,
    ) -> Result<HeapValueId, Stop>
    {
        let mut tasks = alloc::vec![Evaluation::Producer(root, environment)];
        let mut results: Vec<HeapValueId> = Vec::new();
        if let Err(stop) = self.drive(&mut tasks, &mut results) {
            for task in tasks {
                if let Evaluation::Remember(constant, _) = task {
                    self.record(constant, Unfolding::Pending);
                }
            }
            return Err(stop);
        }
        match results.as_slice() {
            | &[value] => Ok(value),
            | _ => Err(Stuck::IllFormedProducer(root).into()),
        }
    }

    /// Run producer evaluation tasks to completion.
    ///
    /// # Specification
    /// - requires: any results already on the stack resolve in the store.
    /// - ensures: on success every task has run and left its value.
    /// - provides: [`Self::evaluate`]'s loop.
    /// - fails: as [`Self::evaluate`], leaving the unrun tasks in `tasks`.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nested constants recover from a failed unfolding;
    ///   distinct constructor fields retain order and fresh thunks share their
    ///   nominal cell on repeat force. L2 — generated pure computations compare
    ///   with the normaliser, distinguishing missing tasks, wrong result-stack
    ///   order and incorrect constructor or constant completion.
    /// - witness: `machine::tests::failed_unfolding_resets_every_active_constant`
    /// - witness: `machine::tests::pattern_fields_bind_last_innermost`
    /// - witness: `machine::tests::a_shared_thunk_is_forced_once`
    /// - witness: `tests::differential::the_l_machine_agrees_with_normalisation_by_evaluation`
    #[spec(
        requires: results.iter().all(|value| self.store.value(*value).is_some()),
        ensures: |ref ret| ret.is_err() || (tasks.is_empty() && results.iter().all(|value| self.store.value(*value).is_some())),
    )]
    fn drive(
        &mut self,
        tasks: &mut Vec<Evaluation>,
        results: &mut Vec<HeapValueId>,
    ) -> Result<(), Stop>
    {
        let arena = self.arena;
        while let Some(task) = tasks.pop() {
            match task {
                | Evaluation::Producer(id, environment) => {
                    let node = arena.producer(id).ok_or(Stuck::IllFormedProducer(id))?;
                    let value = match *node {
                        | ProducerNode::Primitive { arguments, .. } => {
                            tasks.push(Evaluation::Primitive(id));
                            for argument in arguments.iter().rev() {
                                tasks.push(Evaluation::Producer(*argument, environment));
                            }
                            continue;
                        },
                        | ProducerNode::Variable { zone, index } => {
                            let bound = match zone {
                                | Zone::Intuitionistic => {
                                    self.store.lookup_value(environment, index)
                                },
                                | Zone::Linear => None,
                            };
                            bound.ok_or(Stuck::UnboundVariable { zone, index })?
                        },
                        | ProducerNode::Constant(constant) => match self.unfolding(constant)? {
                            | Unfolding::Done(value) => value,
                            | Unfolding::Running => {
                                return Err(Stuck::CyclicConstant(constant).into());
                            },
                            | Unfolding::Pending => match self.definitions.get(constant) {
                                | Some(Definition::Transparent(body)) => {
                                    self.record(constant, Unfolding::Running);
                                    tasks.push(Evaluation::Remember(constant, body));
                                    tasks.push(Evaluation::Producer(body, Environment::EMPTY));
                                    continue;
                                },
                                | Some(Definition::Opaque) => {
                                    let value = self.store.allocate(HeapValue::Opaque(constant))?;
                                    self.record(constant, Unfolding::Done(value));
                                    value
                                },
                                | None => return Err(Stuck::UndefinedConstant(constant).into()),
                            },
                        },
                        | ProducerNode::Literal(ref literal) => {
                            self.store.allocate(HeapValue::Literal(literal.clone()))?
                        },
                        | ProducerNode::Constructor {
                            ref producers,
                            ref consumers,
                            ..
                        } => {
                            if !consumers.is_empty() {
                                return Err(Stuck::IllFormedProducer(id).into());
                            }
                            tasks.push(Evaluation::Construct(id));
                            for &field in producers.iter().rev() {
                                tasks.push(Evaluation::Producer(field, environment));
                            }
                            continue;
                        },
                        | ProducerNode::Thunk { body } => {
                            let cell = self.store.allocate_cell()?;
                            self.store.allocate(HeapValue::Thunk {
                                body,
                                environment,
                                cell,
                            })?
                        },
                        | ProducerNode::Cocase { .. } | ProducerNode::Mu { .. } => {
                            self.store.allocate(HeapValue::Closure {
                                producer: id,
                                environment,
                            })?
                        },
                    };
                    results.push(value);
                },
                | Evaluation::Construct(id) => {
                    let Some(node) = arena.producer(id)
                    else {
                        return Err(Stuck::IllFormedProducer(id).into());
                    };
                    let ProducerNode::Constructor {
                        ref tag,
                        ref producers,
                        ..
                    } = *node
                    else {
                        return Err(Stuck::IllFormedProducer(id).into());
                    };
                    let start = results
                        .len()
                        .checked_sub(producers.len())
                        .ok_or(Stuck::IllFormedProducer(id))?;
                    let fields: Box<[HeapValueId]> = results.drain(start ..).collect();
                    let value = self.store.allocate(HeapValue::Constructed {
                        tag: tag.clone(),
                        fields,
                    })?;
                    results.push(value);
                },
                | Evaluation::Primitive(id) => {
                    use gandr_core_term::primitive::Arguments;
                    use gandr_core_term::primitive::Scalar;
                    let Some(&ProducerNode::Primitive {
                        primitive,
                        arguments,
                    }) = arena.producer(id)
                    else {
                        return Err(Stuck::IllFormedProducer(id).into());
                    };
                    let last = results.pop().ok_or(Stuck::IllFormedProducer(id))?;
                    let last = self.scalar(last)?;
                    let arguments = match arguments {
                        | Arguments::Unary(_) => Arguments::Unary(last),
                        | Arguments::Binary(_) => {
                            let first = results.pop().ok_or(Stuck::IllFormedProducer(id))?;
                            Arguments::Binary([self.scalar(first)?, last])
                        },
                    };
                    let result = primitive.evaluate(&arguments).map_err(Stuck::Primitive)?;
                    let value = match result {
                        | Scalar::Integer(integer) => self.store.allocate(HeapValue::Literal(
                            gandr_kernel_term::Literal::Integer(integer),
                        ))?,
                        | Scalar::Boolean(side) => {
                            let unit = self.store.allocate(HeapValue::Constructed {
                                tag: ConstructorTag::Unit,
                                fields: Box::from([]),
                            })?;
                            self.store.allocate(HeapValue::Constructed {
                                tag: ConstructorTag::Injection(side),
                                fields: Box::from([unit]),
                            })?
                        },
                    };
                    results.push(value);
                },
                | Evaluation::Remember(constant, body) => {
                    let &value = results.last().ok_or(Stuck::IllFormedProducer(body))?;
                    self.record(constant, Unfolding::Done(value));
                },
            }
        }
        Ok(())
    }

    /// How far a constant's unfolding has got.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the recorded state of an admitted constant.
    /// - provides: the memo of constants' values.
    /// - fails: [`Stuck::UndefinedConstant`] for a position never admitted.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — transparent, opaque, cyclic and undefined
    ///   declarations have distinct outcomes; a two-level failed unfolding is
    ///   retried and both records are pending, distinguishing wrong admission
    ///   indexing and retained running states.
    /// - witness: `machine::tests::constants_unfold_once_and_opaque_ones_stay_opaque`
    /// - witness: `machine::tests::failed_unfolding_resets_every_active_constant`
    #[spec(ensures: |ref ret| *ret == self.unfoldings.get(usize::from(constant)).copied().ok_or(Stuck::UndefinedConstant(constant)))]
    fn unfolding(
        &self,
        constant: ConstantIndex,
    ) -> Result<Unfolding, Stuck>
    {
        self.unfoldings
            .get(usize::from(constant))
            .copied()
            .ok_or(Stuck::UndefinedConstant(constant))
    }

    /// Record a constant's unfolding state.
    ///
    /// # Specification
    /// trivial.
    fn record(
        &mut self,
        constant: ConstantIndex,
        state: Unfolding,
    )
    {
        if let Some(slot) = self.unfoldings.get_mut(usize::from(constant)) {
            *slot = state;
        }
    }

    /// Read the native scalar carried by a terminal operand.
    ///
    /// # Specification
    /// - ensures: integers and unit injections retain their exact payload; all
    ///   other shapes are refused.
    /// - fails: a non-scalar operand yields the table's argument-type refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the native argument-type refusal for malformed or non-scalar
    /// values.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — unequal operands and both injection tags separate
    ///   classifier and order errors.
    /// - witness: `machine::tests::native_arithmetic_and_partial_application`
    #[spec(ensures: |ref ret| ret.is_ok() || matches!(ret, Err(Stop::Stuck(Stuck::NonScalar(actual))) if *actual == value))]
    fn scalar(
        &self,
        value: HeapValueId,
    ) -> Result<gandr_core_term::primitive::Scalar<&gandr_kernel_term::IntegerLiteral>, Stop>
    {
        use gandr_core_term::primitive::Scalar;
        match self.store.value(value) {
            | Some(&HeapValue::Literal(gandr_kernel_term::Literal::Integer(ref integer))) => {
                Ok(Scalar::Integer(integer))
            },
            | Some(&HeapValue::Constructed {
                tag: ConstructorTag::Injection(side),
                ref fields,
            }) => {
                if let &[body] = fields.as_ref()
                    && matches!(self.store.value(body), Some(&HeapValue::Constructed { tag: ConstructorTag::Unit, ref fields }) if fields.is_empty())
                {
                    Ok(Scalar::Boolean(side))
                }
                else {
                    Err(Stuck::NonScalar(value).into())
                }
            },
            | _ => Err(Stuck::NonScalar(value).into()),
        }
    }
}

#[cfg(test)]
mod tests
{

    #[test]
    fn native_arithmetic_and_partial_application()
    {
        let mut core = CoreArena::new();
        let sub = gandr_core_term::primitive::PRELUDE
            .iter()
            .copied()
            .find(|primitive| primitive.name().as_ref() == "sub")
            .unwrap();
        let value = sub.thunk(&mut core);
        let forced = core.computation_force(value);
        let first = integer(&mut core, Digits("19"));
        let partial = core.computation_application(forced, first);
        let mut arena = CommandArena::new();
        let mut provenance = Provenance::new();
        let command = focus_computation(&core, partial, &mut arena, &mut provenance).unwrap();
        let definitions = Definitions::new();
        let mut machine = Machine::new(&arena, &definitions);
        let Outcome::Halted(value) = machine.run(command, budget()).unwrap()
        else {
            panic!("partial application halts with a closure");
        };
        let partial = machine.read_back(value, &mut core).unwrap();
        let second = integer(&mut core, Digits("7"));
        let saturated = core.computation_application(partial, second);
        assert_eq!(evaluated(&mut core, saturated), "⟨12 |+ ★⟩");
    }

    use alloc::string::String;

    use gandr_core_term::Computation;
    use gandr_kernel_term::IntegerLiteral;
    use gandr_kernel_term::Literal;
    use gandr_kernel_term::Magnitude;
    use gandr_kernel_term::Side;
    use gandr_kernel_term::Sign;

    use super::*;
    use crate::focus::Provenance;
    use crate::focus::focus_computation;
    use crate::focus::focus_value;
    use crate::pretty::render_command;
    use crate::readback::ReadbackRefusal;
    use crate::store::MemoState;

    /// A prelude spelling used by a native fixture.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug)]
    struct NativeName(&'static str);

    /// Apply a named prelude primitive to the supplied core values.
    ///
    /// # Specification
    /// - requires: the name occurs in the prelude and every argument resolves.
    /// - ensures: the resulting computation resolves in the same arena.
    /// - provides: the ordinary thunk, force and curried-application path.
    /// - panics: if the prelude does not contain the fixture's name.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct integer operands and both boolean sides
    ///   distinguish wrong primitive selection, dropped arguments and reversal.
    ///   Evidence covers the named scalar fixtures, not arbitrary core values.
    /// - witness: `machine::tests::const_applied_returns_its_first_argument`
    /// - witness: `machine::tests::native_integer_addition_returns_sum`
    /// - witness: `machine::tests::native_boolean_and_returns_false`
    #[spec(
        requires: gandr_core_term::primitive::PRELUDE.iter().any(|row| row.name().as_ref() == name.0)
            && arguments.iter().all(|&argument| core.value(argument).is_some()),
        ensures: |ret| core.computation(ret).is_some(),
    )]
    fn native(
        core: &mut CoreArena,
        name: NativeName,
        arguments: &[ValueId],
    ) -> ComputationId
    {
        let primitive = gandr_core_term::primitive::PRELUDE
            .iter()
            .find(|row| row.name().as_ref() == name.0)
            .expect("a named prelude primitive");
        let thunk = primitive.thunk(core);
        let mut term = core.computation_force(thunk);
        for &argument in arguments {
            term = core.computation_application(term, argument);
        }
        term
    }

    /// Native identity preserves its integer argument.
    #[test]
    fn identity_applied_returns_its_argument()
    {
        let mut core = CoreArena::new();
        let argument = integer(&mut core, Digits("5"));
        let term = native(&mut core, NativeName("prim.id"), &[argument]);
        assert_eq!(evaluated(&mut core, term), "⟨5 |+ ★⟩");
    }

    /// Native constant keeps the first of two distinct arguments.
    #[test]
    fn const_applied_returns_its_first_argument()
    {
        let mut core = CoreArena::new();
        let first = integer(&mut core, Digits("7"));
        let second = integer(&mut core, Digits("9"));
        let term = native(&mut core, NativeName("prim.const"), &[first, second]);
        assert_eq!(evaluated(&mut core, term), "⟨7 |+ ★⟩");
    }

    /// Saturated native addition returns the exact sum.
    #[test]
    fn native_integer_addition_returns_sum()
    {
        let mut core = CoreArena::new();
        let first = integer(&mut core, Digits("1"));
        let second = integer(&mut core, Digits("2"));
        let term = native(&mut core, NativeName("add"), &[first, second]);
        assert_eq!(evaluated(&mut core, term), "⟨3 |+ ★⟩");
    }

    /// Native comparison returns the true injection for increasing integers.
    #[test]
    fn native_integer_less_than_returns_true()
    {
        let mut core = CoreArena::new();
        let first = integer(&mut core, Digits("1"));
        let second = integer(&mut core, Digits("2"));
        let term = native(&mut core, NativeName("lt"), &[first, second]);
        let unit = core.value_unit();
        let truth = core.value_injection(Side::Left, unit);
        let expected = core.computation_return(truth);
        assert_eq!(evaluated(&mut core, term), shown(&core, expected));
    }

    /// Native conjunction selects false from true and false.
    #[test]
    fn native_boolean_and_returns_false()
    {
        let mut core = CoreArena::new();
        let unit = core.value_unit();
        let truth = core.value_injection(Side::Left, unit);
        let falsity = core.value_injection(Side::Right, unit);
        let term = native(&mut core, NativeName("and"), &[truth, falsity]);
        let expected = core.computation_return(falsity);
        assert_eq!(evaluated(&mut core, term), shown(&core, expected));
    }

    /// An admitted prelude thunk unfolds through the ordinary constant path.
    #[test]
    fn a_forced_prelude_name_resolves_to_its_builtin()
    {
        let mut core = CoreArena::new();
        let primitive = gandr_core_term::primitive::PRELUDE
            .iter()
            .find(|row| row.name().as_ref() == "prim.id")
            .expect("the identity prelude binding");
        let thunk = primitive.thunk(&mut core);
        let mut arena = CommandArena::new();
        let mut provenance = Provenance::new();
        let binding = focus_value(&core, thunk, &mut arena, &mut provenance).unwrap();
        let mut definitions = Definitions::new();
        let constant = definitions.push(Definition::Transparent(binding));
        let reference = core.value_constant(constant);
        let forced = core.computation_force(reference);
        let argument = integer(&mut core, Digits("5"));
        let term = core.computation_application(forced, argument);
        let root = focus_computation(&core, term, &mut arena, &mut provenance).unwrap();
        let mut machine = Machine::new(&arena, &definitions);
        let Outcome::Halted(value) = machine.run(root, budget()).unwrap()
        else {
            panic!("the forced prelude binding must return its argument");
        };
        let read = machine.read_back(value, &mut core).unwrap();
        assert_eq!(shown(&core, read), "⟨5 |+ ★⟩");
    }

    /// The decimal digits of a test literal.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug)]
    struct Digits(&'static str);

    /// A budget no test term comes near.
    ///
    /// # Specification
    /// trivial.
    fn budget() -> StepCount
    {
        StepCount::from(1_000_usize)
    }

    /// The non-negative integer literal `digits` in `core`.
    ///
    /// # Specification
    /// - requires: digits is a nonempty unsigned decimal spelling.
    /// - ensures: a core literal containing that nonnegative integer, in
    ///   canonical decimal form.
    /// - provides: numeric input for the machine's semantic fixtures.
    /// - panics: on a malformed decimal spelling.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — nonnegative literals pass through return, binding and
    ///   application with their expected numeric readings. Under enforcement
    ///   the canonical payload is checked at construction, distinguishing the
    ///   wrong sign, value or node kind. Invalid decimal spellings are outside
    ///   these fixtures.
    /// - witness: `machine::tests::ret_is_a_terminal_value`
    /// - witness: `machine::tests::bind_threads_a_value`
    /// - witness: `machine::tests::application_binds_the_argument`
    #[spec(
        requires: !digits.0.is_empty() && digits.0.bytes().all(|byte| byte.is_ascii_digit()),
        ensures: |ret| match core.value(ret) {
            | Some(&gandr_core_term::Value::Literal(Literal::Integer(ref integer))) => {
                let significant = digits.0.trim_start_matches('0');
                let expected = if significant.is_empty() { "0" } else { significant };
                let actual: &str = integer.magnitude().as_ref();
                integer.sign() == Sign::NonNegative && actual == expected
            },
            | _ => false,
        },
    )]
    fn integer(
        core: &mut CoreArena,
        digits: Digits,
    ) -> ValueId
    {
        let magnitude =
            Magnitude::from_decimal_text(String::from(digits.0)).expect("decimal digits");
        core.value_literal(Literal::Integer(IntegerLiteral::new(
            Sign::NonNegative,
            magnitude,
        )))
    }

    /// A core computation as the IL renders its focusing.
    ///
    /// # Specification
    /// - requires: computation is in the pure focusing domain.
    /// - ensures: the bounded IL rendering of its focused command.
    /// - provides: a semantic observation shared by machine fixtures.
    /// - panics: when focusing refuses the supplied term.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exact return, binding and application readings
    ///   distinguish omitted values, wrong binding and an incorrect focused
    ///   command. Only supported finite fixture computations are rendered; this
    ///   helper does not claim a lossless textual encoding.
    /// - witness: `machine::tests::ret_is_a_terminal_value`
    /// - witness: `machine::tests::bind_threads_a_value`
    /// - witness: `machine::tests::application_binds_the_argument`
    #[spec(requires: core.computation(computation).is_some(), ensures: |ref ret| ret.starts_with('⟨') && ret.ends_with('⟩'))]
    fn shown(
        core: &CoreArena,
        computation: ComputationId,
    ) -> String
    {
        let mut arena = CommandArena::new();
        let mut provenance = Provenance::new();
        let command = focus_computation(core, computation, &mut arena, &mut provenance)
            .expect("a read-back term focuses");
        render_command(&arena, command)
    }

    /// Focus a closed computation, run it with no definitions, and show its
    /// terminal's readback.
    ///
    /// # Specification
    /// - requires: a closed pure computation that halts within the fixture
    ///   budget and whose terminal can be read back.
    /// - ensures: the bounded rendering of that terminal's core reading,
    ///   retaining the source computation in the extended core arena.
    /// - provides: a full focus, execution, readback and display observation.
    /// - panics: on focusing, execution or readback failure, or a stuck run.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — return, binding, force, both case arms and
    ///   application have exact terminal readings. These distinguish the wrong
    ///   environment, branch and delivered value; captured function readings
    ///   additionally observe closure. Only terminating pure fixtures within
    ///   the fixed budget are covered.
    /// - witness: `machine::tests::ret_is_a_terminal_value`
    /// - witness: `machine::tests::bind_threads_a_value`
    /// - witness: `machine::tests::force_runs_a_thunk_body`
    /// - witness: `machine::tests::case_selects_the_matching_arm`
    /// - witness: `machine::tests::application_binds_the_argument`
    /// - witness: `machine::tests::a_function_terminal_reads_back_closed_over_its_environment`
    #[spec(requires: core.computation(computation).is_some(), ensures: |ref ret|
        core.computation(computation).is_some() && ret.starts_with('⟨') && ret.ends_with('⟩'))]
    fn evaluated(
        core: &mut CoreArena,
        computation: ComputationId,
    ) -> String
    {
        let mut arena = CommandArena::new();
        let mut provenance = Provenance::new();
        let command = focus_computation(core, computation, &mut arena, &mut provenance)
            .expect("a closed term focuses");
        let definitions = Definitions::new();
        let mut machine = Machine::new(&arena, &definitions);
        let outcome = machine.run(command, budget()).expect("the run completes");
        let Outcome::Halted(value) = outcome
        else {
            panic!("the run halts: {outcome:?}");
        };
        let back = machine
            .read_back(value, core)
            .expect("the terminal reads back");
        shown(core, back)
    }

    /// `return 1` halts with `1`.
    #[test]
    fn ret_is_a_terminal_value()
    {
        let mut core = CoreArena::new();
        let one = integer(&mut core, Digits("1"));
        let returned = core.computation_return(one);
        assert_eq!(
            "⟨1 |+ ★⟩",
            evaluated(&mut core, returned),
            "the returned value"
        );
    }

    /// `x ← return 7; return x` binds and returns the value.
    #[test]
    fn bind_threads_a_value()
    {
        let mut core = CoreArena::new();
        let seven = integer(&mut core, Digits("7"));
        let head = core.computation_return(seven);
        let bound = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let body = core.computation_return(bound);
        let program = core.computation_bind(head, body);
        assert_eq!("⟨7 |+ ★⟩", evaluated(&mut core, program), "the bound value");
    }

    /// `force (thunk (return 2))` runs the body.
    #[test]
    fn force_runs_a_thunk_body()
    {
        let mut core = CoreArena::new();
        let two = integer(&mut core, Digits("2"));
        let body = core.computation_return(two);
        let thunk = core.value_thunk(body);
        let program = core.computation_force(thunk);
        assert_eq!(
            "⟨2 |+ ★⟩",
            evaluated(&mut core, program),
            "the body's value"
        );
    }

    /// A match on an injection runs the arm of its side with the payload
    /// bound.
    #[test]
    fn case_selects_the_matching_arm()
    {
        for (side, expected) in [(Side::Left, "⟨3 |+ ★⟩"), (Side::Right, "⟨0 |+ ★⟩")] {
            let mut core = CoreArena::new();
            let three = integer(&mut core, Digits("3"));
            let scrutinee = core.value_injection(side, three);
            let payload = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
            let on_left = core.computation_return(payload);
            let zero = integer(&mut core, Digits("0"));
            let on_right = core.computation_return(zero);
            let program = core.computation_case(scrutinee, on_left, on_right);
            assert_eq!(
                expected,
                evaluated(&mut core, program),
                "the arm of {side:?}"
            );
        }
    }

    /// `((λ. λ. return x1) 1) 2` binds each argument at its own binder.
    #[test]
    fn application_binds_the_argument()
    {
        let mut core = CoreArena::new();
        let outer = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
        let body = core.computation_return(outer);
        let inner = core.computation_lambda(body);
        let function = core.computation_lambda(inner);
        let one = integer(&mut core, Digits("1"));
        let two = integer(&mut core, Digits("2"));
        let once = core.computation_application(function, one);
        let program = core.computation_application(once, two);
        assert_eq!(
            "⟨1 |+ ★⟩",
            evaluated(&mut core, program),
            "x1 is the first argument"
        );
    }

    /// `t ← return (thunk (return 2)); _ ← force t; force t`: the second
    /// force returns the value the first wrote back, by address.
    #[test]
    fn a_shared_thunk_is_forced_once()
    {
        let mut core = CoreArena::new();
        let two = integer(&mut core, Digits("2"));
        let body = core.computation_return(two);
        let thunk = core.value_thunk(body);
        let head = core.computation_return(thunk);
        let first_use = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let first = core.computation_force(first_use);
        let second_use = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
        let second = core.computation_force(second_use);
        let forced_twice = core.computation_bind(first, second);
        let program = core.computation_bind(head, forced_twice);

        let mut arena = CommandArena::new();
        let mut provenance = Provenance::new();
        let command = focus_computation(&core, program, &mut arena, &mut provenance)
            .expect("a closed term focuses");
        let definitions = Definitions::new();
        let mut machine = Machine::new(&arena, &definitions);
        let Ok(Outcome::Halted(value)) = machine.run(command, budget())
        else {
            panic!("the run halts");
        };
        let cells = usize::from(machine.store().cell_count());
        assert_eq!(1, cells, "one thunk, one cell");
        assert_eq!(
            Some(MemoState::Forced(value)),
            machine.store().cell(crate::store::CellId::from(0_u32)),
            "the second force returned the cell's cached value itself"
        );
        let literals = (0 .. usize::from(machine.store().value_count()))
            .filter_map(|offset| u32::try_from(offset).ok())
            .filter(|&offset| {
                matches!(
                    machine.store().value(HeapValueId::from(offset)),
                    Some(&HeapValue::Literal(_))
                )
            })
            .count();
        assert_eq!(1, literals, "the body ran once");
    }

    /// A transparent constant unfolds once per machine, an opaque one reads
    /// back as itself, a cyclic one and an undefined one stop the run.
    #[test]
    fn constants_unfold_once_and_opaque_ones_stay_opaque()
    {
        let mut core = CoreArena::new();
        let five = integer(&mut core, Digits("5"));
        let five_body = core.computation_return(five);
        let suspended = core.value_thunk(five_body);
        let first = core.value_constant(ConstantIndex::from(0_usize));
        let opaque = core.value_constant(ConstantIndex::from(1_usize));
        let cyclic = core.value_constant(ConstantIndex::from(2_usize));
        let undefined = core.value_constant(ConstantIndex::from(9_usize));

        let mut arena = CommandArena::new();
        let mut provenance = Provenance::new();
        let mut definitions = Definitions::new();
        let body =
            focus_value(&core, suspended, &mut arena, &mut provenance).expect("a thunk focuses");
        definitions.push(Definition::Transparent(body));
        definitions.push(Definition::Opaque);
        let loops =
            focus_value(&core, cyclic, &mut arena, &mut provenance).expect("a constant focuses");
        definitions.push(Definition::Transparent(loops));

        let forced = core.computation_force(first);
        let again = core.computation_force(first);
        let pair = core.value_pair(opaque, first);
        let returned = core.computation_return(pair);
        let tail = core.computation_bind(again, returned);
        let program = core.computation_bind(forced, tail);
        let command = focus_computation(&core, program, &mut arena, &mut provenance)
            .expect("a closed term focuses");
        let looping_return = core.computation_return(cyclic);
        let looping =
            focus_computation(&core, looping_return, &mut arena, &mut provenance).expect("focuses");
        let undefined_return = core.computation_return(undefined);
        let missing = focus_computation(&core, undefined_return, &mut arena, &mut provenance)
            .expect("focuses");

        let mut machine = Machine::new(&arena, &definitions);
        let Ok(Outcome::Halted(value)) = machine.run(command, budget())
        else {
            panic!("the run halts");
        };
        assert_eq!(
            1,
            usize::from(machine.store().cell_count()),
            "the constant's thunk exists once"
        );
        let back = machine
            .read_back(value, &mut core)
            .expect("the terminal reads back");
        assert_eq!(
            "⟨pair(c1, {force(α) ⇒ ⟨5 |+ α0⟩}) |+ ★⟩",
            shown(&core, back),
            "the opaque constant stays itself and the transparent one unfolds"
        );
        assert_eq!(
            Ok(Outcome::Stuck(Stuck::CyclicConstant(ConstantIndex::from(
                2_usize
            )))),
            machine.run(looping, budget()),
            "a definition needing its own value stops the run"
        );
        assert_eq!(
            Ok(Outcome::Stuck(Stuck::UndefinedConstant(
                ConstantIndex::from(9_usize)
            ))),
            machine.run(missing, budget()),
            "a position never admitted stops the run"
        );
    }

    /// `return 1` takes four transitions: the cut, the delivery to `★`, the
    /// return to the base and the pop of the empty region.
    #[test]
    fn the_step_budget_bounds_a_run()
    {
        let mut core = CoreArena::new();
        let one = integer(&mut core, Digits("1"));
        let returned = core.computation_return(one);
        let mut arena = CommandArena::new();
        let mut provenance = Provenance::new();
        let command = focus_computation(&core, returned, &mut arena, &mut provenance)
            .expect("a closed term focuses");
        let definitions = Definitions::new();
        let mut machine = Machine::new(&arena, &definitions);
        assert_eq!(
            Err(MachineFault::OutOfSteps),
            machine.run(command, StepCount::from(3_usize)),
            "three transitions are one short"
        );
        assert!(
            matches!(
                machine.run(command, StepCount::from(4_usize)),
                Ok(Outcome::Halted(_))
            ),
            "four transitions halt"
        );
    }

    /// `x ← return 4; λ. return x1` halts with a function closed over `x`.
    #[test]
    fn a_function_terminal_reads_back_closed_over_its_environment()
    {
        let mut core = CoreArena::new();
        let four = integer(&mut core, Digits("4"));
        let head = core.computation_return(four);
        let captured = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
        let body = core.computation_return(captured);
        let function = core.computation_lambda(body);
        let program = core.computation_bind(head, function);
        assert_eq!(
            "⟨cocase {apply(x; α) ⇒ ⟨4 |+ α0⟩} |− ★⟩",
            evaluated(&mut core, program),
            "the function with its captured variable substituted"
        );
    }

    /// `x ← return 4; return (thunk (return x))` halts with a thunk closed
    /// over `x`.
    #[test]
    fn a_thunk_reads_back_closed_over_its_environment()
    {
        let mut core = CoreArena::new();
        let four = integer(&mut core, Digits("4"));
        let head = core.computation_return(four);
        let captured = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let body = core.computation_return(captured);
        let thunk = core.value_thunk(body);
        let returned = core.computation_return(thunk);
        let program = core.computation_bind(head, returned);
        assert_eq!(
            "⟨{force(α) ⇒ ⟨4 |+ α0⟩} |+ ★⟩",
            evaluated(&mut core, program),
            "the thunk with its captured variable substituted"
        );

        let mut arena = CommandArena::new();
        let mut provenance = Provenance::new();
        let command = focus_computation(&core, program, &mut arena, &mut provenance)
            .expect("a closed term focuses");
        let definitions = Definitions::new();
        let mut machine = Machine::new(&arena, &definitions);
        let Ok(Outcome::Halted(value)) = machine.run(command, budget())
        else {
            panic!("the run halts");
        };
        let read = machine
            .read_back_value(value, &mut core)
            .expect("a thunk is a value");
        let wrapped = core.computation_return(read);
        assert_eq!(
            "⟨{force(α) ⇒ ⟨4 |+ α0⟩} |+ ★⟩",
            shown(&core, wrapped),
            "the value readback is the thunk itself"
        );
        assert!(
            matches!(core.computation(wrapped), Some(&Computation::Return(_))),
            "and the terminal readback only wraps it"
        );
    }

    /// `⟨pair(μα. ⟨() |+ α0⟩, ()) |+ ★⟩` halts with a suspended capture as a
    /// field, which has no core reading; the core arena is left at its mark.
    #[test]
    fn a_suspended_capture_has_no_reading()
    {
        let mut arena = CommandArena::new();
        let unit = arena
            .mint_producer(ProducerNode::Constructor {
                tag: crate::il::ConstructorTag::Unit,
                producers: Box::from([]),
                consumers: Box::from([]),
            })
            .expect("a leaf mints");
        let inner_return = arena
            .mint_consumer(ConsumerNode::Covariable(CovariableIndex::from(0_u32)))
            .expect("a leaf mints");
        let body = arena
            .mint_cut(Polarity::Positive, unit, inner_return)
            .expect("children resolve");
        let capture = arena
            .mint_producer(ProducerNode::Mu { body })
            .expect("the body resolves");
        let pair = arena
            .mint_producer(ProducerNode::Constructor {
                tag: crate::il::ConstructorTag::Pair,
                producers: Box::from([capture, unit]),
                consumers: Box::from([]),
            })
            .expect("fields resolve");
        let top = arena
            .mint_consumer(ConsumerNode::Top)
            .expect("a leaf mints");
        let command = arena
            .mint_cut(Polarity::Positive, pair, top)
            .expect("children resolve");

        let definitions = Definitions::new();
        let mut machine = Machine::new(&arena, &definitions);
        let Ok(Outcome::Halted(value)) = machine.run(command, budget())
        else {
            panic!("the run halts");
        };
        let mut core = CoreArena::new();
        let kept = core.value_unit();
        let mark = core.watermark();
        let refused = machine.read_back(value, &mut core);
        assert!(
            matches!(refused, Err(ReadbackRefusal::Unreadable(_))),
            "the capture has no reading: {refused:?}"
        );
        assert_eq!(mark, core.watermark(), "the core arena is back at its mark");
        assert!(core.value(kept).is_some(), "earlier nodes are kept");
    }

    /// Polarity delays a capture only against a binder, and later use resumes
    /// it.
    #[test]
    fn polarity_decides_whether_a_capture_is_evaluated()
    {
        let mut arena = CommandArena::new();
        let unit = arena
            .mint_producer(ProducerNode::Constructor {
                tag: crate::il::ConstructorTag::Unit,
                producers: Box::from([]),
                consumers: Box::from([]),
            })
            .expect("leaf");
        let top = arena.mint_consumer(ConsumerNode::Top).expect("leaf");
        let back = arena
            .mint_consumer(ConsumerNode::Covariable(0_u32.into()))
            .expect("leaf");
        let force = arena
            .mint_consumer(ConsumerNode::Destructor {
                tag: DestructorTag::Force,
                producers: Box::from([]),
                consumers: Box::from([back]),
            })
            .expect("continuation resolves");
        let body = arena
            .mint_cut(Polarity::Positive, unit, force)
            .expect("children resolve");
        let capture = arena
            .mint_producer(ProducerNode::Mu { body })
            .expect("body resolves");
        let ignored_body = arena
            .mint_cut(Polarity::Positive, unit, top)
            .expect("children resolve");
        let ignoring = arena
            .mint_consumer(ConsumerNode::MuTilde { body: ignored_body })
            .expect("body resolves");
        let variable = arena
            .mint_producer(ProducerNode::Variable {
                zone: Zone::Intuitionistic,
                index: 0_u32.into(),
            })
            .expect("leaf");
        let used_body = arena
            .mint_cut(Polarity::Positive, variable, top)
            .expect("children resolve");
        let using = arena
            .mint_consumer(ConsumerNode::MuTilde { body: used_body })
            .expect("body resolves");
        let positive = arena
            .mint_cut(Polarity::Positive, capture, ignoring)
            .expect("children resolve");
        let negative = arena
            .mint_cut(Polarity::Negative, capture, ignoring)
            .expect("children resolve");
        let resumed = arena
            .mint_cut(Polarity::Negative, capture, using)
            .expect("children resolve");
        let definitions = Definitions::new();
        let mut machine = Machine::new(&arena, &definitions);
        let Ok(Outcome::Stuck(Stuck::Unobservable {
            value: strict,
            head: DestructorTag::Force,
        })) = machine.run(positive, budget())
        else {
            panic!("positive cut runs the capture");
        };
        assert_eq!(
            Some(&HeapValue::Constructed {
                tag: crate::il::ConstructorTag::Unit,
                fields: Box::from([])
            }),
            machine.store.value(strict)
        );
        let Ok(Outcome::Halted(delayed)) = machine.run(negative, budget())
        else {
            panic!("negative cut leaves an ignored capture suspended");
        };
        assert_eq!(
            Some(&HeapValue::Constructed {
                tag: crate::il::ConstructorTag::Unit,
                fields: Box::from([])
            }),
            machine.store.value(delayed)
        );
        assert_eq!(ContinuationMark::BASE, machine.store.mark());
        let Ok(Outcome::Stuck(Stuck::Unobservable {
            value: forced,
            head: DestructorTag::Force,
        })) = machine.run(resumed, budget())
        else {
            panic!("using the suspended capture resumes its body");
        };
        assert_eq!(
            Some(&HeapValue::Constructed {
                tag: crate::il::ConstructorTag::Unit,
                fields: Box::from([])
            }),
            machine.store.value(forced)
        );
    }

    /// Invalid endpoints, zones and eliminators retain their exact refusal
    /// identity.
    #[test]
    fn transition_refusals_name_the_first_invalid_endpoint()
    {
        let mut arena = CommandArena::new();
        let unit = arena
            .mint_producer(ProducerNode::Constructor {
                tag: crate::il::ConstructorTag::Unit,
                producers: Box::from([]),
                consumers: Box::from([]),
            })
            .expect("leaf");
        let intuitionistic = arena
            .mint_producer(ProducerNode::Variable {
                zone: Zone::Intuitionistic,
                index: 0_u32.into(),
            })
            .expect("leaf");
        let linear = arena
            .mint_producer(ProducerNode::Variable {
                zone: Zone::Linear,
                index: 0_u32.into(),
            })
            .expect("leaf");
        let top = arena.mint_consumer(ConsumerNode::Top).expect("leaf");
        let unbound = arena
            .mint_consumer(ConsumerNode::Covariable(0_u32.into()))
            .expect("leaf");
        let malformed = arena
            .mint_consumer(ConsumerNode::Destructor {
                tag: DestructorTag::Force,
                producers: Box::from([]),
                consumers: Box::from([]),
            })
            .expect("empty children");
        let choices = arena
            .mint_consumer(ConsumerNode::Case {
                arms: Box::from([]),
            })
            .expect("empty arms");
        let non_value = arena
            .mint_producer(ProducerNode::Constructor {
                tag: crate::il::ConstructorTag::Unit,
                producers: Box::from([]),
                consumers: Box::from([top]),
            })
            .expect("children resolve");
        let definitions = Definitions::new();
        let mut machine = Machine::new(&arena, &definitions);
        let value = machine.evaluate(unit, Environment::EMPTY).expect("unit");
        let missing_command = CommandId::from(u32::MAX);
        let missing_producer = ProducerId::from(u32::MAX);
        let missing_consumer = ConsumerId::from(u32::MAX);
        let missing_value = HeapValueId::from(u32::MAX);
        assert_eq!(
            Err(Stop::Stuck(Stuck::IllFormedCommand(missing_command))),
            machine.cut(missing_command, Environment::EMPTY)
        );
        assert_eq!(
            Err(Stop::Stuck(Stuck::IllFormedProducer(missing_producer))),
            machine.evaluate(missing_producer, Environment::EMPTY)
        );
        assert_eq!(
            Err(Stop::Stuck(Stuck::IllFormedProducer(non_value))),
            machine.evaluate(non_value, Environment::EMPTY)
        );
        assert_eq!(
            Err(Stop::Stuck(Stuck::UnboundVariable {
                zone: Zone::Intuitionistic,
                index: 0_u32.into()
            })),
            machine.evaluate(intuitionistic, Environment::EMPTY)
        );
        let bound = machine
            .store
            .bind_value(Environment::EMPTY, value)
            .expect("room");
        assert_eq!(Ok(value), machine.evaluate(intuitionistic, bound));
        assert_eq!(
            Err(Stop::Stuck(Stuck::UnboundVariable {
                zone: Zone::Linear,
                index: 0_u32.into()
            })),
            machine.evaluate(linear, bound)
        );
        for consumer in [missing_consumer, malformed] {
            assert_eq!(
                Err(Stop::Stuck(Stuck::IllFormedConsumer(consumer))),
                machine.deliver(value, consumer, Environment::EMPTY)
            );
            assert_eq!(
                Err(Stop::Stuck(Stuck::IllFormedConsumer(consumer))),
                machine.load(consumer, Environment::EMPTY)
            );
        }
        assert_eq!(
            Err(Stop::Stuck(Stuck::UnboundCovariable(0_u32.into()))),
            machine.deliver(value, unbound, Environment::EMPTY)
        );
        assert_eq!(
            Err(Stop::Stuck(Stuck::UnboundCovariable(0_u32.into()))),
            machine.load(unbound, Environment::EMPTY)
        );
        for consumer in [missing_consumer, top] {
            assert_eq!(
                Err(Stop::Stuck(Stuck::IllFormedConsumer(consumer))),
                machine.select(value, consumer, Environment::EMPTY)
            );
        }
        for value in [value, missing_value] {
            assert_eq!(
                Err(Stop::Stuck(Stuck::Unmatched {
                    value,
                    arms: choices
                })),
                machine.select(value, choices, Environment::EMPTY)
            );
            assert_eq!(None, machine.suspended_capture(value));
        }
        let non_capture = machine
            .store
            .allocate(HeapValue::Closure {
                producer: unit,
                environment: Environment::EMPTY,
            })
            .expect("room");
        assert_eq!(None, machine.suspended_capture(non_capture));
        for value in [value, non_capture] {
            assert_eq!(
                Err(Stop::Stuck(Stuck::Unobservable {
                    value,
                    head: DestructorTag::Force
                })),
                machine.observe(value, DestructorTag::Force, &[], ContinuationMark::BASE)
            );
        }
    }

    /// A two-field pattern binds the last field innermost without losing source
    /// order.
    #[test]
    fn pattern_fields_bind_last_innermost()
    {
        let mut core = CoreArena::new();
        let first_source = integer(&mut core, Digits("2"));
        let last_source = integer(&mut core, Digits("3"));
        let mut arena = CommandArena::new();
        let mut provenance = Provenance::new();
        let first = focus_value(&core, first_source, &mut arena, &mut provenance).expect("literal");
        let last = focus_value(&core, last_source, &mut arena, &mut provenance).expect("literal");
        let outer = arena
            .mint_producer(ProducerNode::Variable {
                zone: Zone::Intuitionistic,
                index: 1_u32.into(),
            })
            .expect("leaf");
        let inner = arena
            .mint_producer(ProducerNode::Variable {
                zone: Zone::Intuitionistic,
                index: 0_u32.into(),
            })
            .expect("leaf");
        let result = arena
            .mint_producer(ProducerNode::Constructor {
                tag: crate::il::ConstructorTag::Pair,
                producers: Box::from([outer, inner]),
                consumers: Box::from([]),
            })
            .expect("fields resolve");
        let top = arena.mint_consumer(ConsumerNode::Top).expect("leaf");
        let body = arena
            .mint_cut(Polarity::Positive, result, top)
            .expect("children resolve");
        let matched = arena
            .mint_consumer(ConsumerNode::Case {
                arms: Box::from([crate::il::PatternArm {
                    constructor: crate::il::ConstructorTag::Pair,
                    body,
                }]),
            })
            .expect("body resolves");
        let pair = arena
            .mint_producer(ProducerNode::Constructor {
                tag: crate::il::ConstructorTag::Pair,
                producers: Box::from([first, last]),
                consumers: Box::from([]),
            })
            .expect("fields resolve");
        let root = arena
            .mint_cut(Polarity::Positive, pair, matched)
            .expect("children resolve");
        let definitions = Definitions::new();
        let mut machine = Machine::new(&arena, &definitions);
        let arguments = machine
            .evaluate_all(&[first, last], Environment::EMPTY)
            .expect("literal arguments");
        let &[first_argument, last_argument] = arguments.as_ref()
        else {
            panic!("one result per producer");
        };
        for (source, argument) in [(first_source, first_argument), (last_source, last_argument)] {
            let gandr_core_term::Value::Literal(ref expected) =
                *core.value(source).expect("source resolves")
            else {
                panic!("literal source");
            };
            assert_eq!(
                Some(&HeapValue::Literal(expected.clone())),
                machine.store.value(argument)
            );
        }
        let Ok(Outcome::Halted(value)) = machine.run(root, budget())
        else {
            panic!("pair pattern returns");
        };
        let read = machine
            .read_back_value(value, &mut core)
            .expect("positive pair");
        let Some(&gandr_core_term::Value::Pair(first_read, last_read)) = core.value(read)
        else {
            panic!("pair reading");
        };
        assert_eq!(core.value(first_source), core.value(first_read));
        assert_eq!(core.value(last_source), core.value(last_read));
    }

    /// Reentry shares one update, cache returns its value, and even a
    /// zero-budget run declines abandonment.
    #[test]
    fn forcing_reentry_shares_updates_and_abandonment_declines_them()
    {
        let mut arena = CommandArena::new();
        let unit = arena
            .mint_producer(ProducerNode::Constructor {
                tag: crate::il::ConstructorTag::Unit,
                producers: Box::from([]),
                consumers: Box::from([]),
            })
            .expect("leaf");
        let back = arena
            .mint_consumer(ConsumerNode::Covariable(0_u32.into()))
            .expect("leaf");
        let body = arena
            .mint_cut(Polarity::Positive, unit, back)
            .expect("children resolve");
        let top = arena.mint_consumer(ConsumerNode::Top).expect("leaf");
        let plain = arena
            .mint_cut(Polarity::Positive, unit, top)
            .expect("children resolve");
        let definitions = Definitions::new();
        let mut machine = Machine::new(&arena, &definitions);
        let cell = machine.store.allocate_cell().expect("room");
        let thunk = machine
            .store
            .allocate(HeapValue::Thunk {
                body,
                environment: Environment::EMPTY,
                cell,
            })
            .expect("room");
        let first = machine
            .observe(thunk, DestructorTag::Force, &[], ContinuationMark::BASE)
            .expect("first force opens");
        let update = machine.store.mark();
        assert!(
            matches!(first, Next::Continue(Control::Run(found, inner)) if found == body && machine.store.lookup_covalue(inner, 0_u32.into()) == Some(update))
        );
        assert_eq!(Some(MemoState::InProgress), machine.store.cell(cell));
        assert_eq!(1_usize, usize::from(machine.store.frame_height()));
        assert!(
            matches!(machine.store.frames().next(), Some(&Frame::Update { cell: found }) if found == cell)
        );
        let mut next = machine
            .observe(thunk, DestructorTag::Force, &[], update)
            .expect("reentry runs without another update");
        assert_eq!(update, machine.store.mark());
        let mut halted = None;
        for _ in 0_usize .. 16 {
            match next {
                | Next::Halt(value) => {
                    halted = Some(value);
                    break;
                },
                | Next::Continue(control) => {
                    next = machine
                        .step(control)
                        .expect("unit body returns through its update");
                },
            }
        }
        let value = halted.expect("the bounded return path halts");
        assert_eq!(Some(MemoState::Forced(value)), machine.store.cell(cell));
        assert_eq!(
            Some(&HeapValue::Constructed {
                tag: crate::il::ConstructorTag::Unit,
                fields: Box::from([])
            }),
            machine.store.value(value)
        );
        assert_eq!(
            Ok(Next::Continue(Control::Return(
                value,
                ContinuationMark::BASE
            ))),
            machine.observe(thunk, DestructorTag::Force, &[], ContinuationMark::BASE)
        );
        let abandoned = machine.store.allocate_cell().expect("room");
        let unfinished = machine
            .store
            .allocate(HeapValue::Thunk {
                body,
                environment: Environment::EMPTY,
                cell: abandoned,
            })
            .expect("room");
        machine
            .observe(
                unfinished,
                DestructorTag::Force,
                &[],
                ContinuationMark::BASE,
            )
            .expect("open another force");
        assert_eq!(
            Err(MachineFault::OutOfSteps),
            machine.run(plain, StepCount::from(0_usize))
        );
        assert_eq!(Some(MemoState::Unforced), machine.store.cell(abandoned));
        assert_eq!(Some(MemoState::Forced(value)), machine.store.cell(cell));
        assert_eq!(ContinuationMark::BASE, machine.store.mark());
    }

    /// A failed nested unfolding may be retried without turning into a false
    /// cycle.
    #[test]
    fn failed_unfolding_resets_every_active_constant()
    {
        let mut arena = CommandArena::new();
        let root = arena
            .mint_producer(ProducerNode::Constant(0_usize.into()))
            .expect("leaf");
        let first_body = arena
            .mint_producer(ProducerNode::Constant(1_usize.into()))
            .expect("leaf");
        let second_body = arena
            .mint_producer(ProducerNode::Constant(2_usize.into()))
            .expect("leaf");
        let top = arena.mint_consumer(ConsumerNode::Top).expect("leaf");
        let command = arena
            .mint_cut(Polarity::Positive, root, top)
            .expect("children resolve");
        let mut definitions = Definitions::new();
        definitions.push(Definition::Transparent(first_body));
        definitions.push(Definition::Transparent(second_body));
        let mut machine = Machine::new(&arena, &definitions);
        assert_eq!(
            Ok(Outcome::Stuck(Stuck::UndefinedConstant(2_usize.into()))),
            machine.run(command, budget())
        );
        assert_eq!(
            Ok(Outcome::Stuck(Stuck::UndefinedConstant(2_usize.into()))),
            machine.run(command, budget()),
            "a retry encounters the same missing definition, not a poisoned memo"
        );
        assert_eq!(
            [Unfolding::Pending, Unfolding::Pending],
            machine.unfoldings.as_slice()
        );
    }
}
