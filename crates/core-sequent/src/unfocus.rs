//! Unfocusing: `𝓕⁻¹`, reading a command back as the core computation it
//! focuses, and a producer back as its core value.
//!
//! A command `⟨p |ε c⟩` decodes as a head read from `p` — a `μ`'s body, a
//! copattern object's function, or a value — and a spine read from `c`: an
//! application frame applies, `μ̃` binds, a force frame forces, a match cases,
//! and the current return point ends the spine. The current return point is
//! `★` at the root and covariable `0` under a `μ`, a thunk or a copattern
//! arm; any other covariable escapes the computation and is refused. Every
//! command focusing builds decodes, and `𝓕⁻¹ ∘ 𝓕` is the identity on core
//! terms; IL outside that image is refused by name.
//!
//! The walk can close a term as it goes: a producer variable counting past
//! the decoded root's own binders is replaced by the closed core value the
//! caller supplies for it. The machine's readback closes a closure's body
//! over its environment this way; the public entry points close nothing.
//!
//! Decoding writes into a caller's [`CoreArena`] and truncates it to its entry
//! watermark when refused.

use alloc::vec::Vec;
use core::fmt;

use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::Zone;
use gandr_kernel_strata::Level;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::Side;

use crate::il::CommandArena;
use crate::il::CommandId;
use crate::il::CommandNode;
use crate::il::ConstructorTag;
use crate::il::ConsumerId;
use crate::il::ConsumerNode;
use crate::il::DestructorTag;
use crate::il::ProducerId;
use crate::il::ProducerNode;

/// Why a command or producer has no core reading.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum UnfocusRefusal
{
    /// A command address names no command of the arena.
    DanglingCommand(CommandId),
    /// A producer address names no producer of the arena.
    DanglingProducer(ProducerId),
    /// A consumer address names no consumer of the arena.
    DanglingConsumer(ConsumerId),
    /// The producer stands where no focused term puts it: a `μ` or a
    /// copattern object as a value, or a head with another arity or shape.
    ProducerOutsideTheImage(ProducerId),
    /// The consumer stands where no focused term puts it: a force frame or a
    /// match after a computation, or a frame with another arity or shape.
    ConsumerOutsideTheImage(ConsumerId),
    /// A covariable or `★` that is not the current return point: a jump out
    /// of the computation being decoded.
    EscapingContinuation(ConsumerId),
    /// An internal invariant broke: a builder found no result where its own
    /// children should have left one. Unreachable while the walk's own pushes
    /// are the only source of tasks; reported rather than asserted.
    DecodeInvariant,
}

impl fmt::Display for UnfocusRefusal
{
    /// Names the node with no core reading.
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
            | Self::DanglingCommand(id) => write!(f, "command {id} is not in the arena"),
            | Self::DanglingProducer(id) => write!(f, "producer {id} is not in the arena"),
            | Self::DanglingConsumer(id) => write!(f, "consumer {id} is not in the arena"),
            | Self::ProducerOutsideTheImage(id) => {
                write!(f, "producer {id} is not in focused form")
            },
            | Self::ConsumerOutsideTheImage(id) => {
                write!(f, "consumer {id} is not in focused form")
            },
            | Self::EscapingContinuation(id) => {
                write!(
                    f,
                    "consumer {id} jumps out of the computation being decoded"
                )
            },
            | Self::DecodeInvariant => f.write_str("the decoding lost a result it pushed"),
        }
    }
}

impl core::error::Error for UnfocusRefusal
{
}

/// Decode a command as the core computation it focuses, with `★` as its
/// return point.
///
/// # Specification
/// - requires: nothing.
/// - ensures: on success a core computation `M` with `𝓕⟦M⟧★` equal to the
///   command up to node sharing; free producer variables stay free.
/// - provides: the left inverse of
///   [`focus_computation`](crate::focus_computation).
/// - fails: [`UnfocusRefusal`] naming the first node with no core reading;
///   `core` is then exactly as it was on entry.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L1 — decoding inverts focusing on generated closed core
///   computations, over an L3 residue: a jump out of the computation and a `μ`
///   standing as a value are refused by name with the core arena back at its
///   mark.
/// - witness: `tests::focus_properties::unfocusing_inverts_focusing_on_generated_computations`
/// - witness: `unfocus::tests::an_escaping_covariable_is_refused_and_rolled_back`
/// - witness: `unfocus::tests::a_capture_standing_as_a_value_is_outside_the_image`
#[inline]
pub fn unfocus_command(
    arena: &CommandArena,
    command: CommandId,
    core: &mut CoreArena,
) -> Result<ComputationId, UnfocusRefusal>
{
    let decoded = decode(arena, Root::Command(command), core, &[])?;
    match decoded {
        | Decoded::Computation(computation) => Ok(computation),
        | Decoded::Value(_) => Err(UnfocusRefusal::DecodeInvariant),
    }
}

/// Decode a producer as the core value it focuses.
///
/// # Specification
/// - requires: nothing.
/// - ensures: on success a core value `v` with `𝓥⟦v⟧` equal to the producer up
///   to node sharing.
/// - provides: the left inverse of [`focus_value`](crate::focus_value).
/// - fails: as [`unfocus_command`], with the same rollback.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L1 — as [`unfocus_command`], over generated values.
/// - witness: `tests::focus_properties::unfocusing_inverts_focusing_on_generated_values`
#[inline]
pub fn unfocus_value(
    arena: &CommandArena,
    producer: ProducerId,
    core: &mut CoreArena,
) -> Result<ValueId, UnfocusRefusal>
{
    let decoded = decode(arena, Root::Value(producer), core, &[])?;
    match decoded {
        | Decoded::Value(value) => Ok(value),
        | Decoded::Computation(_) => Err(UnfocusRefusal::DecodeInvariant),
    }
}

/// The binder depths a node is decoded under.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Depth
{
    /// Producer binders opened since the decoded root.
    producers: u32,
    /// Covariable binders opened since the decoded root, counting the
    /// root's own return point when it is one.
    covariables: u32,
}

impl Depth
{
    /// The root of a decoding: no binder opened, `★` the return point.
    const ROOT: Self = Self {
        producers: 0,
        covariables: 0,
    };

    /// The depth under one more producer binder.
    ///
    /// # Specification
    /// - ensures: the producer count is one higher, saturating at a ceiling no
    ///   arena of at most `u32::MAX` nodes per family can reach.
    fn under_producer(self) -> Self
    {
        Self {
            producers: self.producers.saturating_add(1),
            covariables: self.covariables,
        }
    }

    /// The depth under one more covariable binder.
    ///
    /// # Specification
    /// - ensures: the covariable count is one higher, saturating as
    ///   [`Self::under_producer`] does.
    fn under_covariable(self) -> Self
    {
        Self {
            producers: self.producers,
            covariables: self.covariables.saturating_add(1),
        }
    }

    /// The depth under a copattern arm of `apply`: one producer, one
    /// covariable.
    ///
    /// # Specification
    /// trivial.
    fn under_function_arm(self) -> Self
    {
        self.under_producer().under_covariable()
    }
}

/// What a decoding starts from.
#[derive(Clone, Copy, Debug)]
pub enum Root
{
    /// A command, read as a computation returning to `★`.
    Command(CommandId),
    /// A producer, read as a value.
    Value(ProducerId),
    /// A thunk's suspended command, read as the thunk.
    ThunkBody(CommandId),
    /// A copattern object of one `apply` arm, read as the function it is.
    Function(ProducerId),
}

/// What a decoding produced.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Decoded
{
    /// A core value.
    Value(ValueId),
    /// A core computation.
    Computation(ComputationId),
}

/// Decode a root into `core`, closing producer variables past the root's own
/// binders with `closing`, innermost first.
///
/// # Specification
/// - requires: every id in `closing` is a closed value of `core`.
/// - ensures: on success the decoded term; a producer variable of the
///   intuitionistic zone counting `k` past the binders opened since the root
///   reads `closing[k]` where present, and counting past the closing it stays a
///   variable, shifted down past the `closing.len()` bindings substituted.
/// - provides: the one walk both the public inverse and the machine's readback
///   run.
/// - fails: as [`unfocus_command`]; `core` is then exactly as on entry.
/// - panics: none.
/// - intension: one iteration per task, a constant number of tasks per IL node.
///
/// # Errors
/// As the failure clause states.
pub fn decode(
    arena: &CommandArena,
    root: Root,
    core: &mut CoreArena,
    closing: &[ValueId],
) -> Result<Decoded, UnfocusRefusal>
{
    let mark = core.watermark();
    let mut walk = Unfocusing {
        arena,
        core,
        closing,
        tasks: Vec::new(),
        values: Vec::new(),
        computations: Vec::new(),
    };
    let answer = walk.run(root);
    if answer.is_err() {
        core.truncate_to(mark);
    }
    answer
}

/// One unit of pending decoding work.
#[derive(Clone, Debug)]
enum Task
{
    /// Decode a producer as a value; leaves one value.
    Value(ProducerId, Depth),
    /// Decode a command as a computation; leaves one computation.
    Command(CommandId, Depth),
    /// Extend the computation on top by the spine of `consumer`.
    Spine(ConsumerId, Depth),
    /// Pop two values and build their pair.
    Pair,
    /// Pop one value and build its injection.
    Injection(Side),
    /// Pop one value and build its lift.
    Lift(Level),
    /// Pop one computation and build its thunk.
    Thunk,
    /// Pop one value and build its return.
    Return,
    /// Pop one value and build its force.
    Force,
    /// Pop one computation and build its lambda.
    Lambda,
    /// Pop an argument value and a head computation and build the
    /// application.
    Application,
    /// Pop a body and a head computation and build the bind.
    Bind,
    /// Pop the right and left branches and the scrutinee and build the case.
    Case,
}

/// The state of one decoding.
struct Unfocusing<'run>
{
    /// The IL read from.
    arena: &'run CommandArena,
    /// The core arena built into.
    core: &'run mut CoreArena,
    /// The closed values free producer variables read, innermost first.
    closing: &'run [ValueId],
    /// The pending work, the next task last.
    tasks: Vec<Task>,
    /// Decoded values awaiting their parent.
    values: Vec<ValueId>,
    /// Decoded computations awaiting their parent.
    computations: Vec<ComputationId>,
}

impl Unfocusing<'_>
{
    /// Decode `root` to completion.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the single decoded term.
    /// - provides: the loop every decoding drives; no task recurses.
    /// - fails: the first refusal a task raises, or
    ///   [`UnfocusRefusal::DecodeInvariant`] for a result count other than one.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    fn run(
        &mut self,
        root: Root,
    ) -> Result<Decoded, UnfocusRefusal>
    {
        match root {
            | Root::Command(command) => self.tasks.push(Task::Command(command, Depth::ROOT)),
            | Root::Value(producer) => self.tasks.push(Task::Value(producer, Depth::ROOT)),
            | Root::ThunkBody(body) => {
                self.tasks.push(Task::Thunk);
                self.tasks
                    .push(Task::Command(body, Depth::ROOT.under_covariable()));
            },
            | Root::Function(producer) => self.function_head(producer, Depth::ROOT)?,
        }
        while let Some(task) = self.tasks.pop() {
            self.step(task)?;
        }
        match (self.values.as_slice(), self.computations.as_slice()) {
            | (&[value], &[]) => Ok(Decoded::Value(value)),
            | (&[], &[computation]) => Ok(Decoded::Computation(computation)),
            | _ => Err(UnfocusRefusal::DecodeInvariant),
        }
    }

    /// Run one task.
    ///
    /// # Specification
    /// - requires: a builder's children have left their results.
    /// - ensures: the task's result, or its follow-up tasks, are pushed.
    /// - provides: the decoding table of the module documentation.
    /// - fails: a dangling address, a node outside the image, an escaping
    ///   continuation, or a missing result.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    fn step(
        &mut self,
        task: Task,
    ) -> Result<(), UnfocusRefusal>
    {
        match task {
            | Task::Value(producer, depth) => self.value(producer, depth),
            | Task::Command(command, depth) => self.command(command, depth),
            | Task::Spine(consumer, depth) => self.spine(consumer, depth),
            | Task::Pair => {
                let second = self.pop_value()?;
                let first = self.pop_value()?;
                let pair = self.core.value_pair(first, second);
                self.values.push(pair);
                Ok(())
            },
            | Task::Injection(side) => {
                let body = self.pop_value()?;
                let injection = self.core.value_injection(side, body);
                self.values.push(injection);
                Ok(())
            },
            | Task::Lift(level) => {
                let body = self.pop_value()?;
                let lift = self.core.value_lift(level, body);
                self.values.push(lift);
                Ok(())
            },
            | Task::Thunk => {
                let body = self.pop_computation()?;
                let thunk = self.core.value_thunk(body);
                self.values.push(thunk);
                Ok(())
            },
            | Task::Return => {
                let value = self.pop_value()?;
                let returned = self.core.computation_return(value);
                self.computations.push(returned);
                Ok(())
            },
            | Task::Force => {
                let value = self.pop_value()?;
                let forced = self.core.computation_force(value);
                self.computations.push(forced);
                Ok(())
            },
            | Task::Lambda => {
                let body = self.pop_computation()?;
                let lambda = self.core.computation_lambda(body);
                self.computations.push(lambda);
                Ok(())
            },
            | Task::Application => {
                let argument = self.pop_value()?;
                let head = self.pop_computation()?;
                let applied = self.core.computation_application(head, argument);
                self.computations.push(applied);
                Ok(())
            },
            | Task::Bind => {
                let body = self.pop_computation()?;
                let head = self.pop_computation()?;
                let bound = self.core.computation_bind(head, body);
                self.computations.push(bound);
                Ok(())
            },
            | Task::Case => {
                let on_right = self.pop_computation()?;
                let on_left = self.pop_computation()?;
                let scrutinee = self.pop_value()?;
                let cased = self.core.computation_case(scrutinee, on_left, on_right);
                self.computations.push(cased);
                Ok(())
            },
        }
    }

    /// Decode a producer as a value, or schedule its children.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a leaf's value is pushed, a closed variable reading its
    ///   closing value; a composite's builder and children are scheduled.
    /// - provides: the `𝓥⁻¹` rows.
    /// - fails: a dangling address, or a `μ`, a copattern object or a head of
    ///   the wrong arity as [`UnfocusRefusal::ProducerOutsideTheImage`].
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    fn value(
        &mut self,
        id: ProducerId,
        depth: Depth,
    ) -> Result<(), UnfocusRefusal>
    {
        let node = self
            .arena
            .producer(id)
            .ok_or(UnfocusRefusal::DanglingProducer(id))?;
        let leaf = match *node {
            | ProducerNode::Variable { zone, index } => {
                self.variable(zone, index, depth);
                return Ok(());
            },
            | ProducerNode::Constant(constant) => self.core.value_constant(constant),
            | ProducerNode::Literal(ref literal) => self.core.value_literal(literal.clone()),
            | ProducerNode::Constructor {
                ref tag,
                ref producers,
                ref consumers,
            } => {
                if !consumers.is_empty() || producers.len() != usize::from(tag.producer_arity()) {
                    return Err(UnfocusRefusal::ProducerOutsideTheImage(id));
                }
                match (tag, producers.as_ref()) {
                    | (&ConstructorTag::Unit, &[]) => self.core.value_unit(),
                    | (&ConstructorTag::Pair, &[first, second]) => {
                        self.tasks.push(Task::Pair);
                        self.tasks.push(Task::Value(second, depth));
                        self.tasks.push(Task::Value(first, depth));
                        return Ok(());
                    },
                    | (&ConstructorTag::Injection(side), &[body]) => {
                        self.tasks.push(Task::Injection(side));
                        self.tasks.push(Task::Value(body, depth));
                        return Ok(());
                    },
                    | (&ConstructorTag::Lift(ref level), &[body]) => {
                        self.tasks.push(Task::Lift(level.clone()));
                        self.tasks.push(Task::Value(body, depth));
                        return Ok(());
                    },
                    | _ => return Err(UnfocusRefusal::ProducerOutsideTheImage(id)),
                }
            },
            | ProducerNode::Thunk { body } => {
                self.tasks.push(Task::Thunk);
                self.tasks
                    .push(Task::Command(body, depth.under_covariable()));
                return Ok(());
            },
            | ProducerNode::Cocase { .. } | ProducerNode::Mu { .. } => {
                return Err(UnfocusRefusal::ProducerOutsideTheImage(id));
            },
        };
        self.values.push(leaf);
        Ok(())
    }

    /// Push the value a producer variable reads.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: an intuitionistic variable counting `k` past `depth`'s
    ///   producer binders reads `closing[k]` where present and is rebuilt
    ///   `closing.len()` lower past it; every other variable is rebuilt as
    ///   itself.
    /// - provides: the closing substitution, fused into the walk.
    /// - fails: never.
    /// - panics: none.
    fn variable(
        &mut self,
        zone: Zone,
        index: DeBruijnIndex,
        depth: Depth,
    )
    {
        let past = match zone {
            | Zone::Intuitionistic => u32::from(index).checked_sub(depth.producers),
            | Zone::Linear => None,
        };
        let closed = past
            .and_then(|past| usize::try_from(past).ok())
            .and_then(|past| self.closing.get(past))
            .copied();
        let value = match (closed, past) {
            | (Some(closed), _) => closed,
            | (None, Some(_)) => {
                let substituted = u32::try_from(self.closing.len()).unwrap_or(u32::MAX);
                let shifted = u32::from(index).saturating_sub(substituted);
                self.core.value_variable(zone, DeBruijnIndex::from(shifted))
            },
            | (None, None) => self.core.value_variable(zone, index),
        };
        self.values.push(value);
    }

    /// Decode a command as a computation: its head, then its spine.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the head is scheduled and the spine after it; a value head
    ///   met by a force frame or a match is decoded with it.
    /// - provides: the `𝓕⁻¹` rows for a cut.
    /// - fails: a dangling address, or a node outside the image.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    fn command(
        &mut self,
        id: CommandId,
        depth: Depth,
    ) -> Result<(), UnfocusRefusal>
    {
        let &CommandNode::Cut {
            producer, consumer, ..
        } = self
            .arena
            .command(id)
            .ok_or(UnfocusRefusal::DanglingCommand(id))?;
        let head = self
            .arena
            .producer(producer)
            .ok_or(UnfocusRefusal::DanglingProducer(producer))?;
        match *head {
            | ProducerNode::Mu { body } => {
                self.tasks.push(Task::Spine(consumer, depth));
                self.tasks
                    .push(Task::Command(body, depth.under_covariable()));
                return Ok(());
            },
            | ProducerNode::Cocase { .. } => {
                self.tasks.push(Task::Spine(consumer, depth));
                return self.function_head(producer, depth);
            },
            | ProducerNode::Variable { .. }
            | ProducerNode::Constant(_)
            | ProducerNode::Literal(_)
            | ProducerNode::Constructor { .. }
            | ProducerNode::Thunk { .. } => {},
        }
        let observer = self
            .arena
            .consumer(consumer)
            .ok_or(UnfocusRefusal::DanglingConsumer(consumer))?;
        match *observer {
            | ConsumerNode::Destructor {
                tag: DestructorTag::Force,
                ref producers,
                ref consumers,
            } => {
                let (&[], &[then]) = (producers.as_ref(), consumers.as_ref())
                else {
                    return Err(UnfocusRefusal::ConsumerOutsideTheImage(consumer));
                };
                self.tasks.push(Task::Spine(then, depth));
                self.tasks.push(Task::Force);
            },
            | ConsumerNode::Case { ref arms } => {
                let [ref left, ref right] = **arms
                else {
                    return Err(UnfocusRefusal::ConsumerOutsideTheImage(consumer));
                };
                if left.constructor != ConstructorTag::Injection(Side::Left)
                    || right.constructor != ConstructorTag::Injection(Side::Right)
                {
                    return Err(UnfocusRefusal::ConsumerOutsideTheImage(consumer));
                }
                self.tasks.push(Task::Case);
                self.tasks
                    .push(Task::Command(right.body, depth.under_producer()));
                self.tasks
                    .push(Task::Command(left.body, depth.under_producer()));
            },
            | ConsumerNode::Covariable(_)
            | ConsumerNode::Top
            | ConsumerNode::MuTilde { .. }
            | ConsumerNode::Destructor { .. } => {
                self.tasks.push(Task::Spine(consumer, depth));
                self.tasks.push(Task::Return);
            },
        }
        self.tasks.push(Task::Value(producer, depth));
        Ok(())
    }

    /// Schedule a copattern object's decoding as a lambda.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the lambda builder and its body are scheduled.
    /// - provides: the head rule for a function.
    /// - fails: a dangling address, or an object with any arm other than one
    ///   application arm.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    fn function_head(
        &mut self,
        id: ProducerId,
        depth: Depth,
    ) -> Result<(), UnfocusRefusal>
    {
        let node = self
            .arena
            .producer(id)
            .ok_or(UnfocusRefusal::DanglingProducer(id))?;
        let ProducerNode::Cocase { ref arms } = *node
        else {
            return Err(UnfocusRefusal::ProducerOutsideTheImage(id));
        };
        let &[arm] = arms.as_ref()
        else {
            return Err(UnfocusRefusal::ProducerOutsideTheImage(id));
        };
        if arm.destructor != DestructorTag::Apply {
            return Err(UnfocusRefusal::ProducerOutsideTheImage(id));
        }
        self.tasks.push(Task::Lambda);
        self.tasks
            .push(Task::Command(arm.body, depth.under_function_arm()));
        Ok(())
    }

    /// Extend the computation on top by a consumer's spine.
    ///
    /// # Specification
    /// - requires: a computation is on top.
    /// - ensures: the return point ends the spine; an application frame and a
    ///   value binder schedule their builders and continue.
    /// - provides: the spine rows.
    /// - fails: [`UnfocusRefusal::EscapingContinuation`] for a covariable or
    ///   `★` that is not the return point, and
    ///   [`UnfocusRefusal::ConsumerOutsideTheImage`] for a force frame, a match
    ///   or a frame of the wrong arity after a computation.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    fn spine(
        &mut self,
        id: ConsumerId,
        depth: Depth,
    ) -> Result<(), UnfocusRefusal>
    {
        let node = self
            .arena
            .consumer(id)
            .ok_or(UnfocusRefusal::DanglingConsumer(id))?;
        match *node {
            | ConsumerNode::Covariable(index) => {
                if u32::from(index) == 0 && depth.covariables > 0 {
                    Ok(())
                }
                else {
                    Err(UnfocusRefusal::EscapingContinuation(id))
                }
            },
            | ConsumerNode::Top => {
                if depth.covariables == 0 {
                    Ok(())
                }
                else {
                    Err(UnfocusRefusal::EscapingContinuation(id))
                }
            },
            | ConsumerNode::MuTilde { body } => {
                self.tasks.push(Task::Bind);
                self.tasks.push(Task::Command(body, depth.under_producer()));
                Ok(())
            },
            | ConsumerNode::Destructor {
                tag: DestructorTag::Apply,
                ref producers,
                ref consumers,
            } => {
                let (&[argument], &[then]) = (producers.as_ref(), consumers.as_ref())
                else {
                    return Err(UnfocusRefusal::ConsumerOutsideTheImage(id));
                };
                self.tasks.push(Task::Spine(then, depth));
                self.tasks.push(Task::Application);
                self.tasks.push(Task::Value(argument, depth));
                Ok(())
            },
            | ConsumerNode::Destructor {
                tag: DestructorTag::Force,
                ..
            }
            | ConsumerNode::Case { .. } => Err(UnfocusRefusal::ConsumerOutsideTheImage(id)),
        }
    }

    /// Pop a decoded value.
    ///
    /// # Specification
    /// trivial.
    fn pop_value(&mut self) -> Result<ValueId, UnfocusRefusal>
    {
        self.values.pop().ok_or(UnfocusRefusal::DecodeInvariant)
    }

    /// Pop a decoded computation.
    ///
    /// # Specification
    /// trivial.
    fn pop_computation(&mut self) -> Result<ComputationId, UnfocusRefusal>
    {
        self.computations
            .pop()
            .ok_or(UnfocusRefusal::DecodeInvariant)
    }
}

#[cfg(test)]
mod tests
{
    use alloc::boxed::Box;

    use gandr_theory_cell_complexes::Polarity;

    use super::*;
    use crate::il::CovariableIndex;

    /// `λ. ⟨() |+ α1⟩` decoded from the root: the arm's covariable `1` is the
    /// root's `★`, a jump out of the lambda the core cannot state.
    #[test]
    fn an_escaping_covariable_is_refused_and_rolled_back()
    {
        let mut arena = CommandArena::new();
        let unit = arena
            .mint_producer(ProducerNode::Constructor {
                tag: ConstructorTag::Unit,
                producers: Box::from([]),
                consumers: Box::from([]),
            })
            .expect("a leaf mints");
        let outer = arena
            .mint_consumer(ConsumerNode::Covariable(CovariableIndex::from(1_u32)))
            .expect("a leaf mints");
        let body = arena
            .mint_cut(Polarity::Positive, unit, outer)
            .expect("children resolve");
        let object = arena
            .mint_producer(ProducerNode::Cocase {
                arms: Box::from([crate::il::CopatternArm {
                    destructor: DestructorTag::Apply,
                    body,
                }]),
            })
            .expect("the body resolves");
        let top = arena
            .mint_consumer(ConsumerNode::Top)
            .expect("a leaf mints");
        let root = arena
            .mint_cut(Polarity::Negative, object, top)
            .expect("children resolve");

        let mut core = CoreArena::new();
        let kept = core.value_unit();
        let mark = core.watermark();
        assert_eq!(
            Err(UnfocusRefusal::EscapingContinuation(outer)),
            unfocus_command(&arena, root, &mut core),
            "the arm returns past its own return point"
        );
        assert_eq!(mark, core.watermark(), "the core arena is back at its mark");
        assert!(core.value(kept).is_some(), "earlier nodes are kept");
    }

    /// A `μ` standing as a pair's field has no core reading, and neither has a
    /// match whose arms are not the two injections.
    #[test]
    fn a_capture_standing_as_a_value_is_outside_the_image()
    {
        let mut arena = CommandArena::new();
        let unit = arena
            .mint_producer(ProducerNode::Constructor {
                tag: ConstructorTag::Unit,
                producers: Box::from([]),
                consumers: Box::from([]),
            })
            .expect("a leaf mints");
        let top = arena
            .mint_consumer(ConsumerNode::Top)
            .expect("a leaf mints");
        let inner = arena
            .mint_cut(Polarity::Positive, unit, top)
            .expect("children resolve");
        let capture = arena
            .mint_producer(ProducerNode::Mu { body: inner })
            .expect("the body resolves");
        let pair = arena
            .mint_producer(ProducerNode::Constructor {
                tag: ConstructorTag::Pair,
                producers: Box::from([capture, unit]),
                consumers: Box::from([]),
            })
            .expect("fields resolve");
        let mut core = CoreArena::new();
        assert_eq!(
            Err(UnfocusRefusal::ProducerOutsideTheImage(capture)),
            unfocus_value(&arena, pair, &mut core),
            "a capture is not a value"
        );

        let matcher = arena
            .mint_consumer(ConsumerNode::Case {
                arms: Box::from([crate::il::PatternArm {
                    constructor: ConstructorTag::Unit,
                    body: inner,
                }]),
            })
            .expect("the arm resolves");
        let matched = arena
            .mint_cut(Polarity::Positive, unit, matcher)
            .expect("children resolve");
        assert_eq!(
            Err(UnfocusRefusal::ConsumerOutsideTheImage(matcher)),
            unfocus_command(&arena, matched, &mut core),
            "the core cases on a sum alone"
        );
        assert_eq!(
            CoreArena::new().watermark(),
            core.watermark(),
            "nothing is left behind"
        );
    }
}
