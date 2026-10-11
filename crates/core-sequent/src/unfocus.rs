//! Unfocusing: `𝓕⁻¹`, reading a command back as the core computation it
//! focuses, and a producer back as its core value.
//!
//! A command `⟨p |ε c⟩` decodes as a head read from `p` — a `μ`'s body, a
//! copattern object's function, a recursive thunk forced, or a value — and a
//! spine read from `c`: an application frame applies, `μ̃` binds, a force
//! frame forces, a match cases, and the current return point ends the spine.
//! The current return point is `★` at the root and covariable `0` under a
//! `μ`, a thunk, a recursive thunk or a copattern arm; any other covariable
//! escapes the computation and is refused. Every command focusing builds
//! decodes, and `𝓕⁻¹ ∘ 𝓕` is the identity on core terms up to the types
//! focusing erases: a datatype constructor reads back at the unknown value
//! type and a nominal case at the unknown motive. IL outside that image is
//! refused by name.
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

use anodized::spec;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::Zone;
use gandr_kernel_strata::Level;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::Side;

use crate::boundary::NodeCount;
use crate::boundary::ProducerArity;
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
    /// A control command contains annotations outside the focused image.
    CommandOutsideTheImage(CommandId),
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
            | Self::CommandOutsideTheImage(id) => write!(f, "command {id} is not in focused form"),
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
/// - hypothesis: L2 — source terms and their independently focused image expose
///   wrong formers, child order and binder shifts on bounded generated
///   computations. L3 — dangling roots, malformed heads and escaping
///   continuations are refused with exact payloads and rollback.
/// - witness: `tests::focus_properties::unfocusing_inverts_focusing_on_generated_computations`
/// - witness: `unfocus::tests::an_escaping_covariable_is_refused_and_rolled_back`
/// - witness: `unfocus::tests::a_capture_standing_as_a_value_is_outside_the_image`
/// - witness: `unfocus::tests::decoding_refuses_missing_roots_and_malformed_heads`
#[inline]
#[spec(
    captures: [mark = core.watermark()],
    ensures: |ret| match ret {
        | Ok(id) => core.computation(id).is_some(),
        | Err(_) => core.watermark() == mark,
    },
)]
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
/// - hypothesis: L2 — bounded generated source values are the independent
///   expected reading. L3 — wrong arities, suspended heads and dangling roots
///   expose lost image checks through exact refusal and rollback.
/// - witness: `tests::focus_properties::unfocusing_inverts_focusing_on_generated_values`
/// - witness: `unfocus::tests::decoding_refuses_missing_roots_and_malformed_heads`
#[inline]
#[spec(
    captures: [mark = core.watermark()],
    ensures: |ret| match ret {
        | Ok(id) => core.value(id).is_some(),
        | Err(_) => core.watermark() == mark,
    },
)]
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
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the product of zero, one, the penultimate count and
    ///   the ceiling observes each successor and the untouched opposite depth.
    ///   Swapped counters, wrapping and premature saturation are distinguished.
    /// - witness: `unfocus::tests::binder_depths_saturate_independently`
    #[spec(ensures: |ret| ret.producers == self.producers.saturating_add(1)
        && ret.covariables == self.covariables
    )]
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
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the product of zero, one, the penultimate count and
    ///   the ceiling observes each successor and the untouched opposite depth.
    ///   Swapped counters, wrapping and premature saturation are distinguished.
    /// - witness: `unfocus::tests::binder_depths_saturate_independently`
    #[spec(ensures: |ret| ret.covariables == self.covariables.saturating_add(1)
        && ret.producers == self.producers
    )]
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
    /// A recursive thunk's suspended command, read as the thunk of the
    /// fixpoint it suspends.
    FixpointBody(CommandId, gandr_kernel_term::FixpointEvidence),
    /// A copattern object, read as its lambda or lazy pair of computations.
    Copattern(ProducerId),
    /// A stack bind body, open in one producer and one return covariable.
    BindBody(CommandId),
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
///
/// # Adequacy
/// - hypothesis: L2 — bounded generated source terms and machine closure
///   readbacks observe decoding independently of the IL traversal. L3 —
///   substitution at binder/closing boundaries, malformed heads and exact
///   dangling-root rollback distinguish shift and image-check defects.
/// - witness: `tests::focus_properties::hand_built_cases_cover_every_former`
/// - witness: `tests::focus_properties::unfocusing_inverts_focusing_on_generated_computations`
/// - witness: `tests::focus_properties::unfocusing_inverts_focusing_on_generated_values`
/// - witness: `unfocus::tests::closing_substitution_distinguishes_binders_and_zones`
/// - witness: `unfocus::tests::decoding_refuses_missing_roots_and_malformed_heads`
/// - witness: `machine::tests::a_function_terminal_reads_back_closed_over_its_environment`
/// - witness: `machine::tests::a_thunk_reads_back_closed_over_its_environment`
#[spec(
    requires: closing.iter().all(|id| core.value(*id).is_some()),
    captures: [mark = core.watermark()],
    ensures: |ret| match ret {
        | Ok(Decoded::Value(id)) => core.value(id).is_some(),
        | Ok(Decoded::Computation(id)) => core.computation(id).is_some(),
        | Err(_) => core.watermark() == mark,
    },
)]
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
    /// Assemble a literal stack after its independent frame children.
    Reify(ProducerId),
    /// Assemble an effect or control instruction at its ambient depth.
    Control(CommandId, Depth),
    /// Assemble a lazy computation pair.
    With,
    /// Project one component of a decoded computation.
    Project(Side),
    /// Mint a native list cell from its decoded head and tail.
    ListCons,
    /// Rebuild a native fold from decoded branches and its list.
    ListFold(gandr_core_term::ValueTypeId, gandr_core_term::ValueTypeId),
    /// Mint a saturated core operation from decoded arguments.
    Primitive(
        gandr_core_term::primitive::Primitive,
        gandr_core_term::primitive::Arguments<ProducerId>,
    ),
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
    /// Pop a datatype constructor's field values and build it.
    Native
    {
        /// The constructor's ordinal.
        tag: gandr_kernel_term::ConstructorTag,
        /// Its field count.
        arity: ProducerArity,
    },
    /// Pop one computation and build its thunk.
    Thunk,
    /// Pop one computation and build the fixpoint over it.
    Fixpoint(gandr_kernel_term::FixpointEvidence),
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
    /// Pop the branches and the scrutinee and build the nominal case.
    DataCase(NodeCount),
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
    ///
    /// # Adequacy
    /// - hypothesis: L2 — source terms compared with independently focused and
    ///   decoded bounded generated inputs expose wrong formers, child order and
    ///   binder shifts. L3 — malformed heads and exact refusal payloads cover
    ///   the directed image boundary.
    /// - witness: `tests::focus_properties::hand_built_cases_cover_every_former`
    /// - witness: `tests::focus_properties::unfocusing_inverts_focusing_on_generated_computations`
    /// - witness: `tests::focus_properties::unfocusing_inverts_focusing_on_generated_values`
    /// - witness: `unfocus::tests::decoding_result_stacks_refuse_underflow_and_surplus`
    #[spec(ensures: |ret| ret.is_err() || (self.tasks.is_empty()
        && match ret {
            | Ok(Decoded::Value(id)) => self.values.as_slice() == [id] && self.computations.is_empty(),
            | Ok(Decoded::Computation(id)) => self.computations.as_slice() == [id] && self.values.is_empty(),
            | Err(_) => false,
        })
    )]
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
            | Root::FixpointBody(body, evidence) => {
                self.tasks.push(Task::Thunk);
                self.tasks.push(Task::Fixpoint(evidence));
                self.tasks.push(Task::Command(
                    body,
                    Depth::ROOT.under_producer().under_covariable(),
                ));
            },
            | Root::Copattern(producer) => self.copattern_head(producer, Depth::ROOT)?,
            | Root::BindBody(body) => self
                .tasks
                .push(Task::Command(body, Depth::ROOT.under_function_arm())),
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
    ///
    /// # Adequacy
    /// - hypothesis: L2 — source terms compared with independently focused and
    ///   decoded bounded generated inputs expose wrong formers, child order and
    ///   binder shifts. L3 — malformed heads and exact refusal payloads cover
    ///   the directed image boundary.
    /// - witness: `tests::focus_properties::hand_built_cases_cover_every_former`
    /// - witness: `tests::focus_properties::unfocusing_inverts_focusing_on_generated_computations`
    /// - witness: `tests::focus_properties::unfocusing_inverts_focusing_on_generated_values`
    #[spec(
        requires: match &task {
            | &Task::Reify(source) => self.arena.producer(source).is_none_or(|node| match *node {
                ProducerNode::Reify(ref frames) => self.values.len() >= frames.iter().filter(|frame| matches!(frame, gandr_core_term::control::StackFrame::Apply(_))).count()
                    && self.computations.len() >= frames.iter().filter(|frame| matches!(frame, gandr_core_term::control::StackFrame::Bind(_))).count(),
                _ => true,
            }),
            | &Task::Control(source, _) => self.arena.command(source).is_none_or(|node| match *node {
                CommandNode::Perform { .. } => !self.values.is_empty(),
                CommandNode::Handle { ref clauses, .. } => self.computations.len() >= clauses.len().saturating_add(2),
                CommandNode::Resume { .. } => !self.values.is_empty() && !self.computations.is_empty(),
                CommandNode::Reset { .. } | CommandNode::Shift { .. } => !self.computations.is_empty(),
                CommandNode::Cut { .. } => true,
            }),
            | &Task::With | &Task::Bind => self.computations.len() >= 2,
            | &Task::Project(_) | &Task::Thunk | &Task::Fixpoint(_) | &Task::Lambda | &Task::Spine(..) => !self.computations.is_empty(),
            | &Task::Primitive(_, arguments) => self.values.len() >= arguments.len(),
            | &Task::Pair | &Task::ListCons => self.values.len() >= 2,
            | &Task::Injection(_) | &Task::Lift(_) | &Task::Return | &Task::Force => !self.values.is_empty(),
            | &Task::Application => !self.values.is_empty() && !self.computations.is_empty(),
            | &Task::Case | &Task::ListFold(..) => !self.values.is_empty() && self.computations.len() >= 2,
            | &Task::Native { arity, .. } => self.values.len() >= usize::from(arity),
            | &Task::DataCase(branches) => !self.values.is_empty() && self.computations.len() >= usize::from(branches),
            | &Task::Value(..) | &Task::Command(..) => true,
        },
        ensures: |ret| ret.is_err() || (self.values.last().is_none_or(|id| self.core.value(*id).is_some())
            && self.computations.last().is_none_or(|id| self.core.computation(*id).is_some())),
    )]
    fn step(
        &mut self,
        task: Task,
    ) -> Result<(), UnfocusRefusal>
    {
        match task {
            | Task::Reify(source) => self.complete_reify(source),
            | Task::Control(source, depth) => self.complete_control(source, depth),
            | Task::With => {
                let right = self.pop_computation()?;
                let left = self.pop_computation()?;
                self.computations
                    .push(self.core.computation_with(left, right));
                Ok(())
            },
            | Task::Project(side) => {
                let subject = self.pop_computation()?;
                self.computations
                    .push(self.core.computation_project(side, subject));
                Ok(())
            },
            | Task::ListFold(element, result) => {
                let list = self.pop_value()?;
                let on_cons = self.pop_computation()?;
                let on_nil = self.pop_computation()?;
                let folded = self
                    .core
                    .computation_list_fold(element, result, list, on_nil, on_cons);
                self.computations.push(folded);
                Ok(())
            },
            | Task::Primitive(primitive, arguments) => {
                use gandr_core_term::primitive::Arguments;
                let arguments = match arguments {
                    | Arguments::Unary(_) => Arguments::Unary(self.pop_value()?),
                    | Arguments::Binary(_) => {
                        let second = self.pop_value()?;
                        Arguments::Binary([self.pop_value()?, second])
                    },
                };
                let computation = self.core.computation_primitive(primitive, arguments);
                self.computations.push(computation);
                Ok(())
            },
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
            | Task::ListCons => {
                let tail = self.pop_value()?;
                let head = self.pop_value()?;
                self.values.push(self.core.value_list_cons(head, tail));
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
            | Task::Native { tag, arity } => {
                let start = self
                    .values
                    .len()
                    .checked_sub(usize::from(arity))
                    .ok_or(UnfocusRefusal::DecodeInvariant)?;
                let fields: Vec<ValueId> = self.values.drain(start ..).collect();
                let datatype = self.core.value_type_unknown();
                let constructed = self.core.value_constructor(datatype, tag, fields);
                self.values.push(constructed);
                Ok(())
            },
            | Task::Thunk => {
                let body = self.pop_computation()?;
                let thunk = self.core.value_thunk(body);
                self.values.push(thunk);
                Ok(())
            },
            | Task::Fixpoint(evidence) => {
                let body = self.pop_computation()?;
                let fixpoint = self.core.computation_fixpoint(body, evidence);
                self.computations.push(fixpoint);
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
            | Task::DataCase(count) => {
                let start = self
                    .computations
                    .len()
                    .checked_sub(usize::from(count))
                    .ok_or(UnfocusRefusal::DecodeInvariant)?;
                let branches: Vec<ComputationId> = self.computations.drain(start ..).collect();
                let scrutinee = self.pop_value()?;
                let motive = self.core.comp_type_unknown();
                let cased = self.core.computation_data_case(scrutinee, motive, branches);
                self.computations.push(cased);
                Ok(())
            },
        }
    }

    /// Rebuild a literal stack without nesting independent frame scopes.
    ///
    /// # Specification
    /// - ensures: source frame order is retained, with translated operands and
    ///   separately closed bind bodies.
    /// - fails: missing child results or a malformed source producer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — mixed frames with free variables distinguish
    ///   accidental nesting and reversed operands.
    /// - witness: `tests::focus_properties::hand_built_control_cases_cover_every_former`
    #[spec(ensures: |ret| ret.is_err() || self.values.last().is_some_and(|id|
        matches!((self.arena.producer(source), self.core.value(*id)), (Some(ProducerNode::Reify(source)), Some(gandr_core_term::Value::Reify(frames))) if source.len() == frames.len())))]
    fn complete_reify(
        &mut self,
        source: ProducerId,
    ) -> Result<(), UnfocusRefusal>
    {
        let arena = self.arena;
        let node = arena
            .producer(source)
            .ok_or(UnfocusRefusal::ProducerOutsideTheImage(source))?;
        let ProducerNode::Reify(ref source) = *node
        else {
            return Err(UnfocusRefusal::ProducerOutsideTheImage(source));
        };
        let mut frames = Vec::with_capacity(source.len());
        for frame in source.iter().rev() {
            frames.push(match *frame {
                | gandr_core_term::control::StackFrame::Apply(_) => {
                    gandr_core_term::control::StackFrame::Apply(self.pop_value()?)
                },
                | gandr_core_term::control::StackFrame::Bind(_) => {
                    gandr_core_term::control::StackFrame::Bind(self.pop_computation()?)
                },
                | gandr_core_term::control::StackFrame::Project(side) => {
                    gandr_core_term::control::StackFrame::Project(side)
                },
            });
        }
        frames.reverse();
        self.values.push(self.core.value_reify(frames.into()));
        Ok(())
    }

    /// Import an interface and close only its ambient type-code variables.
    ///
    /// # Specification
    /// - ensures: names survive, type handles belong to the destination, and
    ///   substitution protects every producer binder opened inside this root.
    /// - fails: a dangling annotation within the source command.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct payload and reply codes beneath handler
    ///   binders distinguish foreign handles and capturing ambient
    ///   substitutions.
    /// - witness: `tests::focus_properties::hand_built_control_cases_cover_every_former`
    #[spec(ensures: |ref ret| ret.is_err() || ret.as_ref().is_ok_and(|found|
        found.name() == signature.name() && found.types().all(|id| self.core.value_type(id).is_some())))]
    fn signature(
        &mut self,
        at: CommandId,
        signature: &gandr_core_term::effect::EffectSig,
        depth: Depth,
    ) -> Result<gandr_core_term::effect::EffectSig, UnfocusRefusal>
    {
        let signature = {
            let mut annotations =
                gandr_core_term::TypeImporter::new(self.arena.annotations(), self.core);
            signature.try_map_types(gandr_core_term::effect::TypeOrder::Forward, |id| {
                annotations
                    .value_type(id)
                    .map_err(|gandr_core_term::ImportFault| {
                        UnfocusRefusal::CommandOutsideTheImage(at)
                    })
            })?
        };
        if self.closing.is_empty() {
            return Ok(signature);
        }
        signature.try_map_types(gandr_core_term::effect::TypeOrder::Forward, |mut ty| {
            for &closed in self.closing {
                ty = gandr_core_term::instantiate_value_type_under(
                    self.core,
                    ty,
                    closed,
                    gandr_core_term::Binders::from(depth.producers),
                );
            }
            Ok(ty)
        })
    }

    /// Assemble decoded control children into their source instruction.
    ///
    /// # Specification
    /// - ensures: operation names, clause order and body roles are preserved;
    ///   signature annotations close at the command's ambient binder depth.
    /// - fails: missing child results or malformed source annotations.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — independent round trips with unequal children and
    ///   type codes expose swapped clauses, lost names and incorrect annotation
    ///   scope.
    /// - witness: `tests::focus_properties::hand_built_control_cases_cover_every_former`
    #[spec(ensures: |ret| ret.is_err() || self.computations.last().is_some_and(|id| self.core.computation(*id).is_some()))]
    fn complete_control(
        &mut self,
        source: CommandId,
        depth: Depth,
    ) -> Result<(), UnfocusRefusal>
    {
        let arena = self.arena;
        let node = arena
            .command(source)
            .ok_or(UnfocusRefusal::DanglingCommand(source))?;
        let computation = match *node {
            | CommandNode::Perform {
                ref signature,
                ref operation,
                ..
            } => {
                let signature = self.signature(source, signature, depth)?;
                let payload = self.pop_value()?;
                self.core
                    .computation_perform(signature, operation.clone(), payload)
            },
            | CommandNode::Handle {
                ref signature,
                ref clauses,
                ..
            } => {
                let signature = self.signature(source, signature, depth)?;
                let mut translated = Vec::with_capacity(clauses.len());
                for clause in clauses.iter().rev() {
                    translated.push(gandr_core_term::control::EffectClause {
                        operation: clause.operation.clone(),
                        body: self.pop_computation()?,
                    });
                }
                translated.reverse();
                let on_return = self.pop_computation()?;
                let subject = self.pop_computation()?;
                self.core
                    .computation_handle(signature, subject, on_return, translated.into())
            },
            | CommandNode::Resume { .. } => {
                let body = self.pop_computation()?;
                let stack = self.pop_value()?;
                self.core.computation_resume(stack, body)
            },
            | CommandNode::Reset { .. } => {
                let body = self.pop_computation()?;
                self.core.computation_reset(body)
            },
            | CommandNode::Shift { .. } => {
                let body = self.pop_computation()?;
                self.core.computation_shift(body)
            },
            | CommandNode::Cut { .. } => {
                return Err(UnfocusRefusal::CommandOutsideTheImage(source));
            },
        };
        self.computations.push(computation);
        Ok(())
    }

    /// Decode control bodies under their individual producer and return
    /// binders.
    ///
    /// # Specification
    /// - ensures: the caller's spine follows the instruction, never its inner
    ///   bodies; each clause and shift sees only its declared local binders.
    /// - fails: a missing command.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — round trips under nontrivial outer spines distinguish
    ///   a duplicated caller from each body's fresh return point.
    /// - witness: `tests::focus_properties::hand_built_control_cases_cover_every_former`
    #[spec(captures: work = self.tasks.len(), ensures: |ret| ret.is_err() || self.tasks.len() > work)]
    fn control_command(
        &mut self,
        source: CommandId,
        depth: Depth,
    ) -> Result<(), UnfocusRefusal>
    {
        let node = self
            .arena
            .command(source)
            .ok_or(UnfocusRefusal::DanglingCommand(source))?;
        match *node {
            | CommandNode::Cut { .. } => self.tasks.push(Task::Command(source, depth)),
            | CommandNode::Perform {
                payload,
                continuation,
                ..
            } => {
                self.tasks.push(Task::Spine(continuation, depth));
                self.tasks.push(Task::Control(source, depth));
                self.tasks.push(Task::Value(payload, depth));
            },
            | CommandNode::Handle {
                subject,
                on_return,
                ref clauses,
                continuation,
                ..
            } => {
                self.tasks.push(Task::Spine(continuation, depth));
                self.tasks.push(Task::Control(source, depth));
                for clause in clauses.iter().rev() {
                    self.tasks.push(Task::Command(
                        clause.body,
                        depth.under_covariable().under_producer().under_producer(),
                    ));
                }
                self.tasks
                    .push(Task::Command(on_return, depth.under_function_arm()));
                self.tasks
                    .push(Task::Command(subject, depth.under_covariable()));
            },
            | CommandNode::Resume {
                stack,
                body,
                continuation,
            } => {
                self.tasks.push(Task::Spine(continuation, depth));
                self.tasks.push(Task::Control(source, depth));
                self.tasks
                    .push(Task::Command(body, depth.under_covariable()));
                self.tasks.push(Task::Value(stack, depth));
            },
            | CommandNode::Reset { body, continuation } => {
                self.tasks.push(Task::Spine(continuation, depth));
                self.tasks.push(Task::Control(source, depth));
                self.tasks
                    .push(Task::Command(body, depth.under_covariable()));
            },
            | CommandNode::Shift { body, continuation } => {
                self.tasks.push(Task::Spine(continuation, depth));
                self.tasks.push(Task::Control(source, depth));
                self.tasks
                    .push(Task::Command(body, depth.under_function_arm()));
            },
        }
        Ok(())
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
    ///
    /// # Adequacy
    /// - hypothesis: L2 — source terms compared with independently focused and
    ///   decoded bounded generated inputs expose wrong formers, child order and
    ///   binder shifts. L3 — malformed heads and exact refusal payloads cover
    ///   the directed image boundary.
    /// - witness: `tests::focus_properties::hand_built_cases_cover_every_former`
    /// - witness: `tests::focus_properties::unfocusing_inverts_focusing_on_generated_computations`
    /// - witness: `tests::focus_properties::unfocusing_inverts_focusing_on_generated_values`
    /// - witness: `unfocus::tests::decoding_refuses_missing_roots_and_malformed_heads`
    #[spec(
        captures: [work = self.tasks.len(), results = self.values.len()],
        ensures: |ret| if self.arena.producer(id).is_none() {
            ret == Err(UnfocusRefusal::DanglingProducer(id))
        } else { ret.is_err() || self.tasks.len() > work || self.values.len() > results },
    )]
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
            | ProducerNode::Reify(ref frames) => {
                self.tasks.push(Task::Reify(id));
                for frame in frames.iter().rev() {
                    match *frame {
                        | gandr_core_term::control::StackFrame::Apply(value) => {
                            self.tasks.push(Task::Value(value, depth));
                        },
                        | gandr_core_term::control::StackFrame::Bind(body) => self
                            .tasks
                            .push(Task::Command(body, depth.under_function_arm())),
                        | gandr_core_term::control::StackFrame::Project(_) => {},
                    }
                }
                return Ok(());
            },
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
                    | (&ConstructorTag::ListNil, &[]) => self.core.value_list_nil(),
                    | (&ConstructorTag::ListCons, &[head, tail]) => {
                        self.tasks.push(Task::ListCons);
                        self.tasks.push(Task::Value(tail, depth));
                        self.tasks.push(Task::Value(head, depth));
                        return Ok(());
                    },
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
                    | (&ConstructorTag::Data { tag, arity }, fields) => {
                        self.tasks.push(Task::Native { tag, arity });
                        for &field in fields.iter().rev() {
                            self.tasks.push(Task::Value(field, depth));
                        }
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
            | ProducerNode::Primitive { .. }
            | ProducerNode::Fixpoint { .. }
            | ProducerNode::Cocase { .. }
            | ProducerNode::Mu { .. } => {
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the first bound variable, each closing entry, the
    ///   first variable past closing and the linear zone are observed at exact
    ///   value identity or variable index. Wrong subtraction, binder capture
    ///   and accidental linear substitution change these boundary readings.
    /// - witness: `unfocus::tests::closing_substitution_distinguishes_binders_and_zones`
    #[spec(ensures: self.values.last().is_some_and(|value| {
        let past = if zone == Zone::Intuitionistic {
            u32::from(index).checked_sub(depth.producers)
        } else { None };
        match past {
            | Some(past) => match usize::try_from(past).ok().and_then(|offset| self.closing.get(offset)) {
                | Some(closed) => value == closed,
                | None => self.core.value(*value) == Some(&gandr_core_term::Value::Variable {
                    zone, index: DeBruijnIndex::from(u32::from(index).saturating_sub(u32::try_from(self.closing.len()).unwrap_or(u32::MAX))),
                }),
            },
            | None => self.core.value(*value) == Some(&gandr_core_term::Value::Variable { zone, index }),
        }
    }))]
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
    ///
    /// # Adequacy
    /// - hypothesis: L2 — source terms compared with independently focused and
    ///   decoded bounded generated inputs expose wrong formers, child order and
    ///   binder shifts. L3 — malformed heads and exact refusal payloads cover
    ///   the directed image boundary.
    /// - witness: `tests::focus_properties::hand_built_cases_cover_every_former`
    /// - witness: `tests::focus_properties::unfocusing_inverts_focusing_on_generated_computations`
    /// - witness: `tests::focus_properties::unfocusing_inverts_focusing_on_generated_values`
    /// - witness: `unfocus::tests::decoding_refuses_missing_roots_and_malformed_heads`
    #[spec(
        captures: [work = self.tasks.len()],
        ensures: |ret| if self.arena.command(id).is_none() {
            ret == Err(UnfocusRefusal::DanglingCommand(id))
        } else { ret.is_err() || self.tasks.len() > work },
    )]
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
            .ok_or(UnfocusRefusal::DanglingCommand(id))?
        else {
            return self.control_command(id, depth);
        };
        let head = self
            .arena
            .producer(producer)
            .ok_or(UnfocusRefusal::DanglingProducer(producer))?;
        match *head {
            | ProducerNode::Primitive {
                primitive,
                arguments,
            } => {
                self.tasks.push(Task::Spine(consumer, depth));
                self.tasks.push(Task::Primitive(primitive, arguments));
                for argument in arguments.iter().rev() {
                    self.tasks.push(Task::Value(*argument, depth));
                }
                return Ok(());
            },
            | ProducerNode::Mu { body } => {
                self.tasks.push(Task::Spine(consumer, depth));
                self.tasks
                    .push(Task::Command(body, depth.under_covariable()));
                return Ok(());
            },
            | ProducerNode::Cocase { .. } => {
                self.tasks.push(Task::Spine(consumer, depth));
                return self.copattern_head(producer, depth);
            },
            | ProducerNode::Fixpoint { body, evidence } => {
                let observer = self
                    .arena
                    .consumer(consumer)
                    .ok_or(UnfocusRefusal::DanglingConsumer(consumer))?;
                let ConsumerNode::Destructor {
                    tag: DestructorTag::Force,
                    ref producers,
                    ref consumers,
                } = *observer
                else {
                    return Err(UnfocusRefusal::ProducerOutsideTheImage(producer));
                };
                let (&[], &[then]) = (producers.as_ref(), consumers.as_ref())
                else {
                    return Err(UnfocusRefusal::ConsumerOutsideTheImage(consumer));
                };
                self.tasks.push(Task::Spine(then, depth));
                self.tasks.push(Task::Fixpoint(evidence));
                self.tasks.push(Task::Command(
                    body,
                    depth.under_producer().under_covariable(),
                ));
                return Ok(());
            },
            | ProducerNode::Reify(_)
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
            | ConsumerNode::ListFold {
                element,
                result,
                on_nil,
                on_cons,
                continuation,
            } => {
                let mut annotations =
                    gandr_core_term::TypeImporter::new(self.arena.annotations(), self.core);
                let element =
                    annotations
                        .value_type(element)
                        .map_err(|gandr_core_term::ImportFault| {
                            UnfocusRefusal::ConsumerOutsideTheImage(consumer)
                        })?;
                let result =
                    annotations
                        .value_type(result)
                        .map_err(|gandr_core_term::ImportFault| {
                            UnfocusRefusal::ConsumerOutsideTheImage(consumer)
                        })?;
                let mut element = element;
                let mut result = result;
                for &closed in self.closing {
                    let under = gandr_core_term::Binders::from(depth.producers);
                    element = gandr_core_term::instantiate_value_type_under(
                        self.core, element, closed, under,
                    );
                    result = gandr_core_term::instantiate_value_type_under(
                        self.core, result, closed, under,
                    );
                }
                self.tasks.push(Task::Spine(continuation, depth));
                self.tasks.push(Task::ListFold(element, result));
                self.tasks.push(Task::Value(producer, depth));
                self.tasks.push(Task::Command(
                    on_cons,
                    depth.under_covariable().under_producer().under_producer(),
                ));
                self.tasks
                    .push(Task::Command(on_nil, depth.under_covariable()));
                return Ok(());
            },
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
            | ConsumerNode::DataCase { ref branches, then } => {
                self.tasks.push(Task::Spine(then, depth));
                self.tasks
                    .push(Task::DataCase(NodeCount::from(branches.len())));
                for &branch in branches.iter().rev() {
                    let node = self
                        .arena
                        .producer(branch)
                        .ok_or(UnfocusRefusal::DanglingProducer(branch))?;
                    let ProducerNode::Thunk { body } = *node
                    else {
                        return Err(UnfocusRefusal::ProducerOutsideTheImage(branch));
                    };
                    self.tasks
                        .push(Task::Command(body, depth.under_covariable()));
                }
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

    /// Schedule a copattern object's decoding as a lambda or a lazy pair.
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a missing producer, a non-function and copattern
    ///   objects with zero, one valid, one wrong and two arms distinguish shape
    ///   and head checks by exact refusal. L2 — generated lambda readings
    ///   observe the scheduled body and binders.
    /// - witness: `unfocus::tests::decoding_refuses_missing_roots_and_malformed_heads`
    /// - witness: `tests::focus_properties::unfocusing_inverts_focusing_on_generated_computations`
    #[spec(ensures: |ret| ret == match self.arena.producer(id) {
        | None => Err(UnfocusRefusal::DanglingProducer(id)),
        | Some(&ProducerNode::Cocase { ref arms }) if matches!(arms.as_ref(),
            &[crate::il::CopatternArm { destructor: DestructorTag::Apply, .. }]
            | &[crate::il::CopatternArm { destructor: DestructorTag::Project(Side::Left), .. }, crate::il::CopatternArm { destructor: DestructorTag::Project(Side::Right), .. }]) => Ok(()),
        | Some(_) => Err(UnfocusRefusal::ProducerOutsideTheImage(id)),
    })]
    fn copattern_head(
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
        match arms.as_ref() {
            | &[
                crate::il::CopatternArm {
                    destructor: DestructorTag::Apply,
                    body,
                },
            ] => {
                self.tasks.push(Task::Lambda);
                self.tasks
                    .push(Task::Command(body, depth.under_function_arm()));
            },
            | &[
                crate::il::CopatternArm {
                    destructor: DestructorTag::Project(Side::Left),
                    body: left,
                },
                crate::il::CopatternArm {
                    destructor: DestructorTag::Project(Side::Right),
                    body: right,
                },
            ] => {
                self.tasks.push(Task::With);
                self.tasks
                    .push(Task::Command(right, depth.under_covariable()));
                self.tasks
                    .push(Task::Command(left, depth.under_covariable()));
            },
            | _ => return Err(UnfocusRefusal::ProducerOutsideTheImage(id)),
        }
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — base versus bound return points, a nonzero
    ///   covariable, both destructor arities and a match observe exact
    ///   continuation/image refusals. L2 — independent source readings expose
    ///   misplaced application and binder tasks.
    /// - witness: `unfocus::tests::spines_distinguish_return_points_and_frame_arities`
    /// - witness: `unfocus::tests::an_escaping_covariable_is_refused_and_rolled_back`
    /// - witness: `tests::focus_properties::hand_built_cases_cover_every_former`
    /// - witness: `tests::focus_properties::unfocusing_inverts_focusing_on_generated_computations`
    /// - witness: `tests::focus_properties::unfocusing_inverts_focusing_on_generated_values`
    #[spec(
        requires: !self.computations.is_empty(),
        captures: [work = self.tasks.len()],
        ensures: |ret| match self.arena.consumer(id) {
            | None => ret == Err(UnfocusRefusal::DanglingConsumer(id)),
            | Some(&ConsumerNode::Covariable(index)) => if u32::from(index) == 0 && depth.covariables > 0 {
                ret.is_ok() && self.tasks.len() == work
            } else { ret == Err(UnfocusRefusal::EscapingContinuation(id)) },
            | Some(&ConsumerNode::Top) => if depth.covariables == 0 {
                ret.is_ok() && self.tasks.len() == work
            } else { ret == Err(UnfocusRefusal::EscapingContinuation(id)) },
            | Some(&ConsumerNode::ListFold { .. } | &ConsumerNode::Destructor { tag: DestructorTag::Force, .. } | &ConsumerNode::Case { .. } | &ConsumerNode::DataCase { .. }) =>
                ret == Err(UnfocusRefusal::ConsumerOutsideTheImage(id)),
            | Some(&ConsumerNode::Destructor { tag, ref producers, ref consumers })
                if producers.len() != usize::from(tag.producer_arity()) || consumers.len() != 1 => ret == Err(UnfocusRefusal::ConsumerOutsideTheImage(id)),
            | Some(_) => ret.is_ok() && self.tasks.len() > work,
        },
    )]
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
                tag: DestructorTag::Project(side),
                ref producers,
                ref consumers,
            } => {
                let (&[], &[then]) = (producers.as_ref(), consumers.as_ref())
                else {
                    return Err(UnfocusRefusal::ConsumerOutsideTheImage(id));
                };
                self.tasks.push(Task::Spine(then, depth));
                self.tasks.push(Task::Project(side));
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
            | ConsumerNode::ListFold { .. }
            | ConsumerNode::Case { .. }
            | ConsumerNode::DataCase { .. } => Err(UnfocusRefusal::ConsumerOutsideTheImage(id)),
        }
    }

    /// Pop a decoded value.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the last value is removed and returned; an empty stack is
    ///   unchanged and refused.
    /// - provides: the checked result pop used by decoding builders.
    /// - fails: [`UnfocusRefusal::DecodeInvariant`] on an empty stack.
    /// - panics: none.
    ///
    /// # Errors
    /// The missing-result invariant.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct results expose wrong-end removal; the exact
    ///   empty-stack refusal exposes silent or stale underflow.
    /// - witness: `unfocus::tests::decoding_result_stacks_refuse_underflow_and_surplus`
    #[spec(
        captures: [last = self.values.last().copied(), length = self.values.len()],
        ensures: |ret| ret == last.ok_or(UnfocusRefusal::DecodeInvariant)
            && self.values.len() == length.saturating_sub(1),
    )]
    fn pop_value(&mut self) -> Result<ValueId, UnfocusRefusal>
    {
        self.values.pop().ok_or(UnfocusRefusal::DecodeInvariant)
    }

    /// Pop a decoded computation.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the last computation is removed and returned; an empty stack
    ///   is unchanged and refused.
    /// - provides: the checked result pop used by decoding builders.
    /// - fails: [`UnfocusRefusal::DecodeInvariant`] on an empty stack.
    /// - panics: none.
    ///
    /// # Errors
    /// The missing-result invariant.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct results expose wrong-end removal; the exact
    ///   empty-stack refusal exposes silent or stale underflow.
    /// - witness: `unfocus::tests::decoding_result_stacks_refuse_underflow_and_surplus`
    #[spec(
        captures: [last = self.computations.last().copied(), length = self.computations.len()],
        ensures: |ret| ret == last.ok_or(UnfocusRefusal::DecodeInvariant)
            && self.computations.len() == length.saturating_sub(1),
    )]
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

    /// Each binder counter saturates without changing the other counter.
    #[test]
    fn binder_depths_saturate_independently()
    {
        let bounds = [
            (0_u32, 1_u32),
            (1, 2),
            (u32::MAX.saturating_sub(1), u32::MAX),
            (u32::MAX, u32::MAX),
        ];
        for (producers, next_producers) in bounds {
            for (covariables, next_covariables) in bounds {
                let depth = Depth {
                    producers,
                    covariables,
                };
                assert_eq!(
                    Depth {
                        producers: next_producers,
                        covariables
                    },
                    depth.under_producer()
                );
                assert_eq!(
                    Depth {
                        producers,
                        covariables: next_covariables
                    },
                    depth.under_covariable()
                );
            }
        }
    }

    /// Substitution respects the binder boundary, closing order, residual index
    /// and zone.
    #[test]
    fn closing_substitution_distinguishes_binders_and_zones()
    {
        use gandr_core_term::Value;

        let arena = CommandArena::new();
        let mut core = CoreArena::new();
        let first = core.value_unit();
        let second = core.value_constant(7_usize.into());
        let closing = [first, second];
        for (zone, index, producers, length, expected) in [
            (Zone::Intuitionistic, 0_u32, 0_u32, 2_usize, Value::Unit),
            (
                Zone::Intuitionistic,
                1,
                0,
                2,
                Value::Constant(7_usize.into()),
            ),
            (Zone::Intuitionistic, 2, 0, 2, Value::Variable {
                zone: Zone::Intuitionistic,
                index: 0_u32.into(),
            }),
            (Zone::Intuitionistic, 0, 1, 2, Value::Variable {
                zone: Zone::Intuitionistic,
                index: 0_u32.into(),
            }),
            (Zone::Intuitionistic, 1, 1, 2, Value::Unit),
            (
                Zone::Intuitionistic,
                2,
                1,
                2,
                Value::Constant(7_usize.into()),
            ),
            (Zone::Intuitionistic, 3, 1, 2, Value::Variable {
                zone: Zone::Intuitionistic,
                index: 1_u32.into(),
            }),
            (Zone::Intuitionistic, 1, 0, 0, Value::Variable {
                zone: Zone::Intuitionistic,
                index: 1_u32.into(),
            }),
            (Zone::Linear, 2, 1, 2, Value::Variable {
                zone: Zone::Linear,
                index: 2_u32.into(),
            }),
        ] {
            let mut walk = Unfocusing {
                arena: &arena,
                core: &mut core,
                closing: &closing[.. length],
                tasks: Vec::new(),
                values: Vec::new(),
                computations: Vec::new(),
            };
            walk.variable(zone, index.into(), Depth {
                producers,
                covariables: 0,
            });
            let value = walk.pop_value().expect("one variable reading");
            assert_eq!(Some(&expected), walk.core.value(value));
            match expected {
                | Value::Unit => assert_eq!(first, value),
                | Value::Constant(_) => assert_eq!(second, value),
                | _ => {},
            }
        }
    }

    #[test]
    fn closing_fold_annotations_substitutes_captured_codes()
    {
        use gandr_core_term::Computation;
        use gandr_core_term::ValueType;
        let mut source = CoreArena::new();
        let captured = source.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let element = source.value_type_element(captured, gandr_kernel_strata::Level::zero());
        let result = source.value_type_list(element);
        let nil = source.value_list_nil();
        let on_nil = source.computation_return(nil);
        let head = source.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
        let tail = source.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let cell = source.value_list_cons(head, tail);
        let on_cons = source.computation_return(cell);
        let fold = source.computation_list_fold(element, result, nil, on_nil, on_cons);
        let mut arena = CommandArena::new();
        let mut provenance = crate::focus::Provenance::new();
        let root = crate::focus::focus_computation(&source, fold, &mut arena, &mut provenance)
            .expect("open annotation focuses");
        let mut core = CoreArena::new();
        let unit = core.value_type_unit();
        let code = core.value_quote(unit);
        let Decoded::Computation(closed) =
            decode(&arena, Root::Command(root), &mut core, &[code]).expect("captured code closes")
        else {
            panic!("computation");
        };
        let &Computation::ListFold {
            element,
            result,
            on_cons,
            ..
        } = core.computation(closed).expect("fold")
        else {
            panic!("native fold");
        };
        assert_eq!(core.value_type(element), Some(&ValueType::Unit));
        assert!(
            matches!(core.value_type(result), Some(&ValueType::List(inner)) if core.value_type(inner) == Some(&ValueType::Unit))
        );
        let &Computation::Return(cell) = core.computation(on_cons).expect("cons branch")
        else {
            panic!("return");
        };
        let &gandr_core_term::Value::ListCons(head, tail) = core.value(cell).expect("cell")
        else {
            panic!("native cell");
        };
        for (id, index) in [(head, 1_u32), (tail, 0_u32)] {
            assert_eq!(
                core.value(id),
                Some(&gandr_core_term::Value::Variable {
                    zone: Zone::Intuitionistic,
                    index: DeBruijnIndex::from(index)
                })
            );
        }
    }

    /// Missing roots and malformed positive and negative heads are refused
    /// without residue.
    #[test]
    fn decoding_refuses_missing_roots_and_malformed_heads()
    {
        let mut arena = CommandArena::new();
        let mut core = CoreArena::new();
        core.value_unit();
        let mark = core.watermark();
        let missing_command = CommandId::from(0_u32);
        let missing_producer = ProducerId::from(0_u32);
        assert_eq!(
            Err(UnfocusRefusal::DanglingCommand(missing_command)),
            unfocus_command(&arena, missing_command, &mut core)
        );
        assert_eq!(
            Err(UnfocusRefusal::DanglingProducer(missing_producer)),
            unfocus_value(&arena, missing_producer, &mut core)
        );
        assert_eq!(
            Err(UnfocusRefusal::DanglingProducer(missing_producer)),
            decode(&arena, Root::Copattern(missing_producer), &mut core, &[])
        );
        assert_eq!(mark, core.watermark());
        let unit = arena
            .mint_producer(ProducerNode::Constructor {
                tag: ConstructorTag::Unit,
                producers: Box::from([]),
                consumers: Box::from([]),
            })
            .expect("leaf");
        let top = arena.mint_consumer(ConsumerNode::Top).expect("leaf");
        let back = arena
            .mint_consumer(ConsumerNode::Covariable(CovariableIndex::from(0_u32)))
            .expect("leaf");
        let body = arena
            .mint_cut(Polarity::Positive, unit, back)
            .expect("live children");
        assert_eq!(
            Err(UnfocusRefusal::ProducerOutsideTheImage(unit)),
            decode(&arena, Root::Copattern(unit), &mut core, &[])
        );
        for node in [
            ProducerNode::Constructor {
                tag: ConstructorTag::Unit,
                producers: Box::from([unit]),
                consumers: Box::from([]),
            },
            ProducerNode::Constructor {
                tag: ConstructorTag::Pair,
                producers: Box::from([]),
                consumers: Box::from([]),
            },
            ProducerNode::Constructor {
                tag: ConstructorTag::Injection(Side::Left),
                producers: Box::from([]),
                consumers: Box::from([]),
            },
            ProducerNode::Constructor {
                tag: ConstructorTag::Lift(Level::zero()),
                producers: Box::from([]),
                consumers: Box::from([]),
            },
            ProducerNode::Constructor {
                tag: ConstructorTag::Unit,
                producers: Box::from([]),
                consumers: Box::from([top]),
            },
        ] {
            let bad = arena.mint_producer(node).expect("references resolve");
            assert_eq!(
                Err(UnfocusRefusal::ProducerOutsideTheImage(bad)),
                unfocus_value(&arena, bad, &mut core)
            );
            assert_eq!(mark, core.watermark());
        }
        let apply = crate::il::CopatternArm {
            destructor: DestructorTag::Apply,
            body,
        };
        let force = crate::il::CopatternArm {
            destructor: DestructorTag::Force,
            body,
        };
        let shapes: [Box<[crate::il::CopatternArm]>; 3] =
            [Box::from([]), Box::from([force]), Box::from([apply, apply])];
        for arms in shapes {
            let bad = arena
                .mint_producer(ProducerNode::Cocase { arms })
                .expect("references resolve");
            assert_eq!(
                Err(UnfocusRefusal::ProducerOutsideTheImage(bad)),
                decode(&arena, Root::Copattern(bad), &mut core, &[])
            );
            assert_eq!(
                Err(UnfocusRefusal::ProducerOutsideTheImage(bad)),
                unfocus_value(&arena, bad, &mut core)
            );
            assert_eq!(mark, core.watermark());
        }
        for node in [
            ConsumerNode::Destructor {
                tag: DestructorTag::Force,
                producers: Box::from([unit]),
                consumers: Box::from([top]),
            },
            ConsumerNode::Destructor {
                tag: DestructorTag::Force,
                producers: Box::from([]),
                consumers: Box::from([]),
            },
            ConsumerNode::Case {
                arms: Box::from([
                    crate::il::PatternArm {
                        constructor: ConstructorTag::Injection(Side::Right),
                        body,
                    },
                    crate::il::PatternArm {
                        constructor: ConstructorTag::Injection(Side::Left),
                        body,
                    },
                ]),
            },
        ] {
            let bad = arena.mint_consumer(node).expect("references resolve");
            let root = arena
                .mint_cut(Polarity::Positive, unit, bad)
                .expect("references resolve");
            assert_eq!(
                Err(UnfocusRefusal::ConsumerOutsideTheImage(bad)),
                unfocus_command(&arena, root, &mut core)
            );
            assert_eq!(mark, core.watermark());
        }
    }

    /// Return-point depth and application arities select distinct spine
    /// outcomes.
    #[test]
    fn spines_distinguish_return_points_and_frame_arities()
    {
        let mut arena = CommandArena::new();
        let mut core = CoreArena::new();
        let value = core.value_unit();
        let result = core.computation_return(value);
        let producer = arena
            .mint_producer(ProducerNode::Constant(0_usize.into()))
            .expect("leaf");
        let top = arena.mint_consumer(ConsumerNode::Top).expect("leaf");
        let zero = arena
            .mint_consumer(ConsumerNode::Covariable(CovariableIndex::from(0_u32)))
            .expect("leaf");
        let one = arena
            .mint_consumer(ConsumerNode::Covariable(CovariableIndex::from(1_u32)))
            .expect("leaf");
        for (consumer, depth, expected) in [
            (top, 0_u32, Ok(())),
            (top, 1, Err(UnfocusRefusal::EscapingContinuation(top))),
            (zero, 0, Err(UnfocusRefusal::EscapingContinuation(zero))),
            (zero, 1, Ok(())),
            (one, 1, Err(UnfocusRefusal::EscapingContinuation(one))),
        ] {
            let mut walk = Unfocusing {
                arena: &arena,
                core: &mut core,
                closing: &[],
                tasks: Vec::new(),
                values: Vec::new(),
                computations: alloc::vec![result],
            };
            assert_eq!(
                expected,
                walk.spine(consumer, Depth {
                    producers: 0,
                    covariables: depth
                })
            );
            assert_eq!([result], walk.computations.as_slice());
        }
        for node in [
            ConsumerNode::Destructor {
                tag: DestructorTag::Apply,
                producers: Box::from([]),
                consumers: Box::from([top]),
            },
            ConsumerNode::Destructor {
                tag: DestructorTag::Apply,
                producers: Box::from([producer]),
                consumers: Box::from([]),
            },
            ConsumerNode::Destructor {
                tag: DestructorTag::Force,
                producers: Box::from([]),
                consumers: Box::from([top]),
            },
            ConsumerNode::Case {
                arms: Box::from([]),
            },
        ] {
            let consumer = arena.mint_consumer(node).expect("references resolve");
            let mut walk = Unfocusing {
                arena: &arena,
                core: &mut core,
                closing: &[],
                tasks: Vec::new(),
                values: Vec::new(),
                computations: alloc::vec![result],
            };
            assert_eq!(
                Err(UnfocusRefusal::ConsumerOutsideTheImage(consumer)),
                walk.spine(consumer, Depth::ROOT)
            );
        }
        let missing = ConsumerId::from(u32::MAX);
        let mut walk = Unfocusing {
            arena: &arena,
            core: &mut core,
            closing: &[],
            tasks: Vec::new(),
            values: Vec::new(),
            computations: alloc::vec![result],
        };
        assert_eq!(
            Err(UnfocusRefusal::DanglingConsumer(missing)),
            walk.spine(missing, Depth::ROOT)
        );
    }

    /// Decoding pops exact last results and rejects both underflow and a
    /// surplus root.
    #[test]
    fn decoding_result_stacks_refuse_underflow_and_surplus()
    {
        let mut arena = CommandArena::new();
        let unit = arena
            .mint_producer(ProducerNode::Constructor {
                tag: ConstructorTag::Unit,
                producers: Box::from([]),
                consumers: Box::from([]),
            })
            .expect("leaf");
        let mut core = CoreArena::new();
        let first = core.value_unit();
        let last = core.value_constant(1_usize.into());
        let before = core.computation_return(first);
        let after = core.computation_return(last);
        let mut walk = Unfocusing {
            arena: &arena,
            core: &mut core,
            closing: &[],
            tasks: Vec::new(),
            values: alloc::vec![first, last],
            computations: alloc::vec![before, after],
        };
        assert_eq!(Ok(last), walk.pop_value());
        assert_eq!(Ok(first), walk.pop_value());
        assert_eq!(Err(UnfocusRefusal::DecodeInvariant), walk.pop_value());
        assert_eq!(Ok(after), walk.pop_computation());
        assert_eq!(Ok(before), walk.pop_computation());
        assert_eq!(Err(UnfocusRefusal::DecodeInvariant), walk.pop_computation());
        walk.values.push(first);
        assert_eq!(
            Err(UnfocusRefusal::DecodeInvariant),
            walk.run(Root::Value(unit))
        );
    }
}
