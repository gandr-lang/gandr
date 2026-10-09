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
    /// - hypothesis: L3 — one hand-built case per core former, application at
    ///   two binders, memoised forcing observed by address, constants unfolding
    ///   once, cyclic and undefined, and the exact transition count of a
    ///   return.
    /// - witness: `machine::tests::ret_is_a_terminal_value`
    /// - witness: `machine::tests::bind_threads_a_value`
    /// - witness: `machine::tests::force_runs_a_thunk_body`
    /// - witness: `machine::tests::case_selects_the_matching_arm`
    /// - witness: `machine::tests::application_binds_the_argument`
    /// - witness: `machine::tests::a_shared_thunk_is_forced_once`
    /// - witness: `machine::tests::constants_unfold_once_and_opaque_ones_stay_opaque`
    /// - witness: `machine::tests::the_step_budget_bounds_a_run`
    #[inline]
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
    /// trivial.
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
    /// - requires: nothing.
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
    /// - requires: nothing.
    /// - ensures: on success every task has run and left its value.
    /// - provides: [`Self::evaluate`]'s loop.
    /// - fails: as [`Self::evaluate`], leaving the unrun tasks in `tasks`.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
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
}

#[cfg(test)]
mod tests
{
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
    /// trivial.
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
    /// trivial.
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
    /// trivial.
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
}
