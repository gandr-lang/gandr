//! Focusing: the translation `𝓕⟦M⟧c` of a core computation under a
//! continuation into a command, and `𝓥⟦v⟧` of a core value into a producer.
//!
//! ```text
//! 𝓥⟦x⟧            = x                       𝓥⟦thunk M⟧ = {force(α) ⇒ 𝓕⟦M⟧α}
//! 𝓥⟦()⟧, 𝓥⟦(v, w)⟧, 𝓥⟦inj v⟧, 𝓥⟦lift v⟧    = the constructor over the images
//!
//! 𝓕⟦return v⟧c    = ⟨𝓥⟦v⟧ |+ c⟩
//! 𝓕⟦force v⟧c     = ⟨𝓥⟦v⟧ |+ force(c)⟩
//! 𝓕⟦M v⟧c         = 𝓕⟦M⟧(apply(𝓥⟦v⟧; c))
//! 𝓕⟦λ. M⟧c        = ⟨cocase {apply(x; α) ⇒ 𝓕⟦M⟧α} |− c⟩
//! 𝓕⟦x ← M; N⟧c    = 𝓕⟦M⟧(μ̃x. 𝓕⟦N⟧c)                       c a tail
//!                 = ⟨μα. 𝓕⟦M⟧(μ̃x. 𝓕⟦N⟧α) |ε c⟩              otherwise
//! 𝓕⟦case v {l, r}⟧c = ⟨𝓥⟦v⟧ |+ case {inl(x) ⇒ 𝓕⟦l⟧c, inr(x) ⇒ 𝓕⟦r⟧c}⟩   c a tail
//!                 = ⟨μα. ⟨𝓥⟦v⟧ |+ case {… 𝓕⟦·⟧α …}⟩ |ε c⟩     otherwise
//! ```
//!
//! A tail is a covariable or `★`. A continuation that is not a tail is never
//! placed under a binder: a bind or a case names it with a `μ`, at the
//! polarity of what it observes. Every continuation passed under a binder is
//! therefore a tail, every focused covariable is index `0`, and producer
//! indices are the core's own, so the translation shifts nothing and mints no
//! name. A core value is never a `μ`, so every argument of a focused frame
//! and every field of a focused constructor is a value.
//!
//! Every walk here is a loop over an explicit task stack, so no term's depth
//! reaches the call stack. A refused translation truncates the arena and the
//! provenance table to the marks taken on entry.

use alloc::vec::Vec;
use core::fmt;

use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_kernel_strata::Level;
use gandr_kernel_term::Side;
use gandr_theory_cell_complexes::Polarity;

use crate::boundary::NodeCount;
use crate::il::CommandArena;
use crate::il::CommandId;
use crate::il::ConstructorTag;
use crate::il::ConsumerId;
use crate::il::ConsumerNode;
use crate::il::CopatternArm;
use crate::il::CovariableIndex;
use crate::il::DestructorTag;
use crate::il::MintRefusal;
use crate::il::PatternArm;
use crate::il::ProducerId;
use crate::il::ProducerNode;

/// The source construct a focused command was created for: the un-sugaring
/// view of a focused term.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum FocusOrigin
{
    /// `return v`: the cut of the value against the continuation.
    Return,
    /// `force v`: the cut of the thunk against a force frame.
    Force,
    /// `λ. M`: the cut of the copattern object against the continuation.
    Lambda,
    /// `case v {…}`: the cut of the scrutinee against the match, or the cut
    /// naming the continuation the match's arms share.
    Case,
    /// `x ← M; N`: the cut naming the continuation a bind passes under its
    /// binder.
    Bind,
    /// A declaration's value, cut against `★`.
    TopValue,
}

/// The provenance table: the [`FocusOrigin`] of every command focusing
/// created, in creation order.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
#[repr(transparent)]
pub struct Provenance
{
    /// Each created command with its origin, in increasing command address.
    origins: Vec<(CommandId, FocusOrigin)>,
}

impl Provenance
{
    /// An empty table.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new() -> Self
    {
        Self::default()
    }

    /// The origin recorded for a command, or `None` when focusing did not
    /// create it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Some(origin)` exactly when a translation recorded the
    ///   command.
    /// - provides: the per-command un-sugaring lookup.
    /// - fails: `None` for a command no translation created.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub fn origin(
        &self,
        command: CommandId,
    ) -> Option<FocusOrigin>
    {
        self.origins
            .binary_search_by_key(&command, |&(recorded, _)| recorded)
            .ok()
            .and_then(|offset| self.origins.get(offset))
            .map(|&(_, origin)| origin)
    }

    /// Every recorded command with its origin, in creation order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn entries(&self) -> impl Iterator<Item = (CommandId, FocusOrigin)>
    {
        self.origins.iter().copied()
    }

    /// The number of recorded commands.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn len(&self) -> NodeCount
    {
        NodeCount::from(self.origins.len())
    }

    /// Record a command's origin.
    ///
    /// # Specification
    /// - requires: `command` is above every command already recorded, which
    ///   minting order guarantees.
    /// - ensures: the table answers `origin` for `command`.
    /// - provides: the one write of the table.
    /// - fails: never.
    /// - panics: none.
    fn record(
        &mut self,
        command: CommandId,
        origin: FocusOrigin,
    )
    {
        self.origins.push((command, origin));
    }

    /// Truncate the table to an earlier length.
    ///
    /// # Specification
    /// trivial.
    fn truncate_to(
        &mut self,
        length: NodeCount,
    )
    {
        self.origins.truncate(usize::from(length));
    }
}

/// Why a translation was refused.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum FocusRefusal
{
    /// Native universe transport has no command-IL destructor.
    UniverseTransport(ComputationId),
    /// A core value id names no node of the core arena.
    DanglingValue(ValueId),
    /// A core computation id names no node of the core arena.
    DanglingComputation(ComputationId),
    /// The command arena refused a node.
    Mint(MintRefusal),
    /// A code or universe-path certificate: the command IL carries no types, so
    /// a quoted type, a type operator or a static application has no
    /// producer to become.
    Code(ValueId),
    /// An internal invariant broke: a finishing task found no result where
    /// its own children should have left one. Unreachable while the
    /// translation's own pushes are the only source of tasks; reported rather
    /// than asserted.
    TranslationInvariant,
}

impl fmt::Display for FocusRefusal
{
    /// Names the refused input.
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
            | Self::UniverseTransport(_) => {
                f.write_str("universe transport has no command-IL destructor")
            },
            | Self::DanglingValue(_) => f.write_str("a core value id names no node"),
            | Self::DanglingComputation(_) => f.write_str("a core computation id names no node"),
            | Self::Mint(refusal) => write!(f, "the command arena refused a node: {refusal}"),
            | Self::TranslationInvariant => f.write_str("the translation lost a result it pushed"),
            | Self::Code(_) => f.write_str("a code has no producer in the command IL"),
        }
    }
}

impl core::error::Error for FocusRefusal
{
}

impl From<MintRefusal> for FocusRefusal
{
    /// Carries the arena's refusal in its own vocabulary.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(refusal: MintRefusal) -> Self
    {
        Self::Mint(refusal)
    }
}

/// Focus a core computation against the terminal continuation `★`.
///
/// # Specification
/// - requires: `computation` is a closed term of `core`, or one whose free
///   variables the caller binds.
/// - ensures: on success the command `𝓕⟦computation⟧★`, every command it
///   created recorded in `provenance`; equal inputs mint identical nodes.
/// - provides: the entry of a computation into the IL.
/// - fails: [`FocusRefusal`] at the first dangling core id, code or refused
///   mint; `arena` and `provenance` are then exactly as they were on entry.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L1 — focusing then unfocusing is the identity on generated
///   closed core computations, over an L3 residue: one hand-built case per
///   former, the refusal truncating to the entry marks, and two focusings of
///   one term building identical arenas.
/// - witness: `tests::focus_properties::unfocusing_inverts_focusing_on_generated_computations`
/// - witness: `tests::focus_properties::focusing_is_total_on_generated_computations`
/// - witness: `tests::focus_properties::hand_built_cases_cover_every_former`
/// - witness: `focus::tests::a_refused_focusing_leaves_the_arena_at_its_mark`
/// - witness: `focus::tests::a_code_is_refused_by_name`
/// - witness: `focus::tests::focusing_mints_no_name`
#[inline]
pub fn focus_computation(
    core: &CoreArena,
    computation: ComputationId,
    arena: &mut CommandArena,
    provenance: &mut Provenance,
) -> Result<CommandId, FocusRefusal>
{
    transactional(arena, provenance, |arena, provenance| {
        let top = arena.mint_consumer(ConsumerNode::Top)?;
        let mut run = Focusing::new(core, arena, provenance);
        run.tasks.push(Task::Computation {
            computation,
            continuation: top,
        });
        run.drive()?;
        run.single_command()
    })
}

/// Focus a core value into a producer.
///
/// # Specification
/// - requires: as [`focus_computation`].
/// - ensures: on success the producer `𝓥⟦value⟧`, which is never a `μ`.
/// - provides: the entry of a value into the IL.
/// - fails: as [`focus_computation`], with the same rollback.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L1 — as [`focus_computation`], over generated values.
/// - witness: `tests::focus_properties::unfocusing_inverts_focusing_on_generated_values`
#[inline]
pub fn focus_value(
    core: &CoreArena,
    value: ValueId,
    arena: &mut CommandArena,
    provenance: &mut Provenance,
) -> Result<ProducerId, FocusRefusal>
{
    transactional(arena, provenance, |arena, provenance| {
        let mut run = Focusing::new(core, arena, provenance);
        run.tasks.push(Task::Value(value));
        run.drive()?;
        run.single_producer()
    })
}

/// Focus a declaration's value against `★`: the command `⟨𝓥⟦value⟧ |+ ★⟩`.
///
/// # Specification
/// - requires: as [`focus_computation`].
/// - ensures: on success the cut of `𝓥⟦value⟧` against `★`, recorded as
///   [`FocusOrigin::TopValue`].
/// - provides: the entry a declaration is run from.
/// - fails: as [`focus_computation`], with the same rollback.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — a literal declaration focuses to one positive cut against
///   `★`, checked and recorded as a top value.
/// - witness: `tests::focus_properties::top_level_value_focuses_against_top`
#[inline]
pub fn focus_top_value(
    core: &CoreArena,
    value: ValueId,
    arena: &mut CommandArena,
    provenance: &mut Provenance,
) -> Result<CommandId, FocusRefusal>
{
    transactional(arena, provenance, |arena, provenance| {
        let top = arena.mint_consumer(ConsumerNode::Top)?;
        let mut run = Focusing::new(core, arena, provenance);
        run.tasks.push(Task::Cut {
            origin: FocusOrigin::TopValue,
            polarity: Polarity::Positive,
            consumer: top,
        });
        run.tasks.push(Task::Value(value));
        run.drive()?;
        run.single_command()
    })
}

/// Run a translation, truncating the arena and the provenance table to their
/// entry marks if it is refused.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `build`'s answer; on refusal, `arena` and `provenance` are
///   exactly as on entry.
/// - provides: the one rollback every entry point shares.
/// - fails: `build`'s refusal, unchanged.
/// - panics: none.
///
/// # Errors
/// As the failure clause states.
fn transactional<Answer, Build>(
    arena: &mut CommandArena,
    provenance: &mut Provenance,
    build: Build,
) -> Result<Answer, FocusRefusal>
where
    Build: FnOnce(&mut CommandArena, &mut Provenance) -> Result<Answer, FocusRefusal>,
{
    let arena_mark = arena.watermark();
    let provenance_mark = provenance.len();
    let answer = build(arena, provenance);
    if answer.is_err() {
        arena.truncate_to(arena_mark);
        provenance.truncate_to(provenance_mark);
    }
    answer
}

/// One unit of pending translation work.
#[derive(Clone, Debug)]
enum Task
{
    /// Translate a value; leaves one producer.
    Value(ValueId),
    /// Translate a computation under a continuation; leaves one command.
    Computation
    {
        /// The computation.
        computation: ComputationId,
        /// The continuation it returns to.
        continuation: ConsumerId,
    },
    /// Pop two producers and mint their pair.
    Pair,
    /// Pop one producer and mint its injection.
    Injection(Side),
    /// Pop one producer and mint its lift.
    Lift(Level),
    /// Pop one command and mint the thunk suspending it.
    Thunk,
    /// Pop one producer and mint its cut against `consumer`.
    Cut
    {
        /// The construct the cut is created for.
        origin: FocusOrigin,
        /// The cut's polarity.
        polarity: Polarity,
        /// The consumer.
        consumer: ConsumerId,
    },
    /// Pop the argument's producer, mint `apply(argument; continuation)`, and
    /// translate `head` under it.
    Apply
    {
        /// The applied computation.
        head: ComputationId,
        /// The continuation the application returns to.
        continuation: ConsumerId,
    },
    /// Pop the body's command and mint `⟨cocase {apply ⇒ body} |− c⟩`.
    Lambda
    {
        /// The continuation the function is sent to.
        continuation: ConsumerId,
    },
    /// Pop the bind's body, mint `μ̃x. body`, and translate `head` under it.
    Bind
    {
        /// The bound computation.
        head: ComputationId,
    },
    /// Pop the arms' commands and the scrutinee's producer, and mint the cut
    /// of the scrutinee against the match.
    Case,
    /// Pop one command and mint `⟨μα. command |polarity continuation⟩`.
    Name
    {
        /// The construct the naming cut is created for.
        origin: FocusOrigin,
        /// The polarity of what the continuation observes.
        polarity: Polarity,
        /// The named continuation.
        continuation: ConsumerId,
    },
}

/// The state of one translation.
struct Focusing<'run>
{
    /// The core arena read from.
    core: &'run CoreArena,
    /// The command arena minted into.
    arena: &'run mut CommandArena,
    /// The provenance table recorded into.
    provenance: &'run mut Provenance,
    /// The pending work, the next task last.
    tasks: Vec<Task>,
    /// Translated producers awaiting their parent.
    producers: Vec<ProducerId>,
    /// Translated commands awaiting their parent.
    commands: Vec<CommandId>,
}

impl<'run> Focusing<'run>
{
    /// A translation with no work.
    ///
    /// # Specification
    /// trivial.
    fn new(
        core: &'run CoreArena,
        arena: &'run mut CommandArena,
        provenance: &'run mut Provenance,
    ) -> Self
    {
        Self {
            core,
            arena,
            provenance,
            tasks: Vec::new(),
            producers: Vec::new(),
            commands: Vec::new(),
        }
    }

    /// Run every pending task.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the task stack is empty and each translated root
    ///   left its one result.
    /// - provides: the loop every translation drives; no task recurses.
    /// - fails: the first refusal a task raises.
    /// - panics: none.
    /// - intension: one iteration per task; a value or computation node is
    ///   translated by a constant number of tasks.
    ///
    /// # Errors
    /// As the failure clause states.
    fn drive(&mut self) -> Result<(), FocusRefusal>
    {
        while let Some(task) = self.tasks.pop() {
            self.step(task)?;
        }
        Ok(())
    }

    /// Run one task.
    ///
    /// # Specification
    /// - requires: a finishing task's children have left their results.
    /// - ensures: the task's result, or its follow-up tasks, are pushed.
    /// - provides: the translation table of the module documentation, one arm
    ///   per row.
    /// - fails: a dangling core id, a refused mint, or a missing result.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    fn step(
        &mut self,
        task: Task,
    ) -> Result<(), FocusRefusal>
    {
        match task {
            | Task::Value(value) => self.value(value),
            | Task::Computation {
                computation,
                continuation,
            } => self.computation(computation, continuation),
            | Task::Pair => {
                let second = self.pop_producer()?;
                let first = self.pop_producer()?;
                self.constructor(ConstructorTag::Pair, &[first, second])
            },
            | Task::Injection(side) => {
                let body = self.pop_producer()?;
                self.constructor(ConstructorTag::Injection(side), &[body])
            },
            | Task::Lift(level) => {
                let body = self.pop_producer()?;
                self.constructor(ConstructorTag::Lift(level), &[body])
            },
            | Task::Thunk => {
                let body = self.pop_command()?;
                let thunk = self.arena.mint_producer(ProducerNode::Thunk { body })?;
                self.producers.push(thunk);
                Ok(())
            },
            | Task::Cut {
                origin,
                polarity,
                consumer,
            } => {
                let producer = self.pop_producer()?;
                self.cut(origin, polarity, producer, consumer)
            },
            | Task::Apply { head, continuation } => {
                let argument = self.pop_producer()?;
                let frame = self.arena.mint_consumer(ConsumerNode::Destructor {
                    tag: DestructorTag::Apply,
                    producers: alloc::boxed::Box::from([argument]),
                    consumers: alloc::boxed::Box::from([continuation]),
                })?;
                self.tasks.push(Task::Computation {
                    computation: head,
                    continuation: frame,
                });
                Ok(())
            },
            | Task::Lambda { continuation } => {
                let body = self.pop_command()?;
                let object = self.arena.mint_producer(ProducerNode::Cocase {
                    arms: alloc::boxed::Box::from([CopatternArm {
                        destructor: DestructorTag::Apply,
                        body,
                    }]),
                })?;
                self.cut(
                    FocusOrigin::Lambda,
                    Polarity::Negative,
                    object,
                    continuation,
                )
            },
            | Task::Bind { head } => {
                let body = self.pop_command()?;
                let binder = self.arena.mint_consumer(ConsumerNode::MuTilde { body })?;
                self.tasks.push(Task::Computation {
                    computation: head,
                    continuation: binder,
                });
                Ok(())
            },
            | Task::Case => {
                let scrutinee = self.pop_producer()?;
                let on_right = self.pop_command()?;
                let on_left = self.pop_command()?;
                let matcher = self.arena.mint_consumer(ConsumerNode::Case {
                    arms: alloc::boxed::Box::from([
                        PatternArm {
                            constructor: ConstructorTag::Injection(Side::Left),
                            body: on_left,
                        },
                        PatternArm {
                            constructor: ConstructorTag::Injection(Side::Right),
                            body: on_right,
                        },
                    ]),
                })?;
                self.cut(FocusOrigin::Case, Polarity::Positive, scrutinee, matcher)
            },
            | Task::Name {
                origin,
                polarity,
                continuation,
            } => {
                let body = self.pop_command()?;
                let capture = self.arena.mint_producer(ProducerNode::Mu { body })?;
                self.cut(origin, polarity, capture, continuation)
            },
        }
    }

    /// Translate one value node, or schedule its children.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a leaf's producer is pushed; a composite's finishing task and
    ///   its children's tasks are scheduled, children left to right.
    /// - provides: the `𝓥` rows.
    /// - fails: [`FocusRefusal::DanglingValue`], [`FocusRefusal::Code`] for a
    ///   quote of either sort, a static lambda or a static application, or a
    ///   refused mint.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    fn value(
        &mut self,
        id: ValueId,
    ) -> Result<(), FocusRefusal>
    {
        let node = self.core.value(id).ok_or(FocusRefusal::DanglingValue(id))?;
        let leaf = match *node {
            | Value::Variable { zone, index } => ProducerNode::Variable { zone, index },
            | Value::Constant(constant) => ProducerNode::Constant(constant),
            | Value::Literal(ref literal) => ProducerNode::Literal(literal.clone()),
            | Value::Unit => ProducerNode::Constructor {
                tag: ConstructorTag::Unit,
                producers: alloc::boxed::Box::from([]),
                consumers: alloc::boxed::Box::from([]),
            },
            | Value::Pair(first, second) => {
                self.tasks.push(Task::Pair);
                self.tasks.push(Task::Value(second));
                self.tasks.push(Task::Value(first));
                return Ok(());
            },
            | Value::Injection(side, body) => {
                self.tasks.push(Task::Injection(side));
                self.tasks.push(Task::Value(body));
                return Ok(());
            },
            | Value::Lift { ref target, body } => {
                self.tasks.push(Task::Lift(target.clone()));
                self.tasks.push(Task::Value(body));
                return Ok(());
            },
            | Value::Thunk(body) => {
                let return_point = self.innermost_covariable()?;
                self.tasks.push(Task::Thunk);
                self.tasks.push(Task::Computation {
                    computation: body,
                    continuation: return_point,
                });
                return Ok(());
            },
            | Value::PathRefl(_)
            | Value::PathProduct(..)
            | Value::PathEquiv { .. }
            | Value::Quote(_)
            | Value::QuoteComputation(_)
            | Value::StaticLambda(_)
            | Value::StaticApplication(..) => return Err(FocusRefusal::Code(id)),
        };
        let producer = self.arena.mint_producer(leaf)?;
        self.producers.push(producer);
        Ok(())
    }

    /// Translate one computation node under a continuation, or schedule its
    /// children.
    ///
    /// # Specification
    /// - requires: `continuation` was minted for the binder depth `id` stands
    ///   at.
    /// - ensures: the `𝓕` row for the node's former is scheduled or minted; a
    ///   continuation that is not a tail is placed under no binder.
    /// - provides: the `𝓕` rows.
    /// - fails: [`FocusRefusal::DanglingComputation`] or a refused mint.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    fn computation(
        &mut self,
        id: ComputationId,
        continuation: ConsumerId,
    ) -> Result<(), FocusRefusal>
    {
        let node = self
            .core
            .computation(id)
            .ok_or(FocusRefusal::DanglingComputation(id))?;
        match *node {
            | Computation::Transport(..) => return Err(FocusRefusal::UniverseTransport(id)),
            | Computation::Return(value) => {
                self.tasks.push(Task::Cut {
                    origin: FocusOrigin::Return,
                    polarity: Polarity::Positive,
                    consumer: continuation,
                });
                self.tasks.push(Task::Value(value));
            },
            | Computation::Force(value) => {
                let frame = self.arena.mint_consumer(ConsumerNode::Destructor {
                    tag: DestructorTag::Force,
                    producers: alloc::boxed::Box::from([]),
                    consumers: alloc::boxed::Box::from([continuation]),
                })?;
                self.tasks.push(Task::Cut {
                    origin: FocusOrigin::Force,
                    polarity: Polarity::Positive,
                    consumer: frame,
                });
                self.tasks.push(Task::Value(value));
            },
            | Computation::Application(head, argument) => {
                self.tasks.push(Task::Apply { head, continuation });
                self.tasks.push(Task::Value(argument));
            },
            | Computation::Lambda(body) => {
                let return_point = self.innermost_covariable()?;
                self.tasks.push(Task::Lambda { continuation });
                self.tasks.push(Task::Computation {
                    computation: body,
                    continuation: return_point,
                });
            },
            | Computation::Bind(head, body) => {
                let inner = self.share_or_name(FocusOrigin::Bind, continuation)?;
                self.tasks.push(Task::Bind { head });
                self.tasks.push(Task::Computation {
                    computation: body,
                    continuation: inner,
                });
            },
            | Computation::Case {
                scrutinee,
                on_left,
                on_right,
            } => {
                let inner = self.share_or_name(FocusOrigin::Case, continuation)?;
                self.tasks.push(Task::Case);
                self.tasks.push(Task::Value(scrutinee));
                self.tasks.push(Task::Computation {
                    computation: on_right,
                    continuation: inner,
                });
                self.tasks.push(Task::Computation {
                    computation: on_left,
                    continuation: inner,
                });
            },
        }
        Ok(())
    }

    /// The continuation a binder's body is translated under: `continuation`
    /// itself when it is a tail, otherwise the innermost covariable, with the
    /// naming cut scheduled to run once the body's command is built.
    ///
    /// # Specification
    /// - requires: `continuation` resolves.
    /// - ensures: a tail is returned unchanged and nothing is scheduled; any
    ///   other continuation is named by a [`Task::Name`] at the polarity of
    ///   what it observes, and covariable `0` is returned.
    /// - provides: the rule that keeps a continuation from being copied under a
    ///   binder.
    /// - fails: a dangling continuation, as
    ///   [`FocusRefusal::TranslationInvariant`], or a refused mint.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    fn share_or_name(
        &mut self,
        origin: FocusOrigin,
        continuation: ConsumerId,
    ) -> Result<ConsumerId, FocusRefusal>
    {
        let polarity = match *self
            .arena
            .consumer(continuation)
            .ok_or(FocusRefusal::TranslationInvariant)?
        {
            | ConsumerNode::Covariable(_) | ConsumerNode::Top => return Ok(continuation),
            | ConsumerNode::Destructor { tag, .. } => tag.polarity(),
            | ConsumerNode::MuTilde { .. } | ConsumerNode::Case { .. } => Polarity::Positive,
        };
        self.tasks.push(Task::Name {
            origin,
            polarity,
            continuation,
        });
        self.innermost_covariable()
    }

    /// Mint the covariable `0`.
    ///
    /// # Specification
    /// trivial.
    fn innermost_covariable(&mut self) -> Result<ConsumerId, FocusRefusal>
    {
        Ok(self
            .arena
            .mint_consumer(ConsumerNode::Covariable(CovariableIndex::from(0_u32)))?)
    }

    /// Mint a constructor over producer fields and push it.
    ///
    /// # Specification
    /// - requires: `fields` has the head's arity.
    /// - ensures: the constructor is pushed.
    /// - provides: the one constructor mint of `𝓥`.
    /// - fails: a refused mint.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    fn constructor(
        &mut self,
        tag: ConstructorTag,
        fields: &[ProducerId],
    ) -> Result<(), FocusRefusal>
    {
        let producer = self.arena.mint_producer(ProducerNode::Constructor {
            tag,
            producers: alloc::boxed::Box::from(fields),
            consumers: alloc::boxed::Box::from([]),
        })?;
        self.producers.push(producer);
        Ok(())
    }

    /// Mint a cut, record its origin, and push it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the cut is pushed and recorded with `origin`.
    /// - provides: the one cut mint of `𝓕`, so every created command has an
    ///   origin.
    /// - fails: a refused mint.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    fn cut(
        &mut self,
        origin: FocusOrigin,
        polarity: Polarity,
        producer: ProducerId,
        consumer: ConsumerId,
    ) -> Result<(), FocusRefusal>
    {
        let command = self.arena.mint_cut(polarity, producer, consumer)?;
        self.provenance.record(command, origin);
        self.commands.push(command);
        Ok(())
    }

    /// Pop a translated producer.
    ///
    /// # Specification
    /// trivial.
    fn pop_producer(&mut self) -> Result<ProducerId, FocusRefusal>
    {
        self.producers
            .pop()
            .ok_or(FocusRefusal::TranslationInvariant)
    }

    /// Pop a translated command.
    ///
    /// # Specification
    /// trivial.
    fn pop_command(&mut self) -> Result<CommandId, FocusRefusal>
    {
        self.commands
            .pop()
            .ok_or(FocusRefusal::TranslationInvariant)
    }

    /// The one command a computation's translation leaves.
    ///
    /// # Specification
    /// - requires: the translation has been driven.
    /// - ensures: the single command, with no producer left over.
    /// - provides: the result of a computation entry point.
    /// - fails: [`FocusRefusal::TranslationInvariant`] for any other shape.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    fn single_command(mut self) -> Result<CommandId, FocusRefusal>
    {
        let command = self.pop_command()?;
        if self.commands.is_empty() && self.producers.is_empty() {
            Ok(command)
        }
        else {
            Err(FocusRefusal::TranslationInvariant)
        }
    }

    /// The one producer a value's translation leaves.
    ///
    /// # Specification
    /// - requires: the translation has been driven.
    /// - ensures: the single producer, with no command left over.
    /// - provides: the result of a value entry point.
    /// - fails: [`FocusRefusal::TranslationInvariant`] for any other shape.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    fn single_producer(mut self) -> Result<ProducerId, FocusRefusal>
    {
        let producer = self.pop_producer()?;
        if self.commands.is_empty() && self.producers.is_empty() {
            Ok(producer)
        }
        else {
            Err(FocusRefusal::TranslationInvariant)
        }
    }
}

#[cfg(test)]
mod tests
{
    use super::*;

    /// `λ. (return () to y. return d)` where `d` is an id the arena holds no
    /// node for: the translation mints several nodes before it meets `d`.
    ///
    /// # Specification
    /// trivial.
    fn lambda_over_a_dangling_value(core: &mut CoreArena) -> ComputationId
    {
        let mut elsewhere = CoreArena::new();
        let mut dangling = elsewhere.value_unit();
        for _ in 0_u32 .. 64_u32 {
            dangling = elsewhere.value_unit();
        }
        let unit = core.value_unit();
        let bound = core.computation_return(unit);
        let body = core.computation_return(dangling);
        let bind = core.computation_bind(bound, body);
        core.computation_lambda(bind)
    }

    /// A translation refused part-way leaves the arena and the provenance
    /// table exactly at the marks they had on entry, though it had minted
    /// nodes before the refusal.
    #[test]
    fn a_refused_focusing_leaves_the_arena_at_its_mark()
    {
        let mut core = CoreArena::new();
        let refused = lambda_over_a_dangling_value(&mut core);
        let fine_value = core.value_unit();
        let fine = core.computation_return(fine_value);

        let mut arena = CommandArena::new();
        let mut provenance = Provenance::new();
        let earlier = focus_computation(&core, fine, &mut arena, &mut provenance)
            .expect("a closed return focuses");
        let arena_mark = arena.watermark();
        let provenance_mark = provenance.len();

        let outcome = focus_computation(&core, refused, &mut arena, &mut provenance);
        assert!(
            matches!(outcome, Err(FocusRefusal::DanglingValue(_))),
            "the dangling value is refused by name: {outcome:?}"
        );
        assert_eq!(
            arena_mark,
            arena.watermark(),
            "the arena is back at its mark"
        );
        assert_eq!(
            provenance_mark,
            provenance.len(),
            "the provenance table is back at its mark"
        );
        assert_eq!(
            Some(FocusOrigin::Return),
            provenance.origin(earlier),
            "the earlier translation is untouched"
        );
    }

    /// A code has no producer: `return ⌜Integer⌝` and `return ⌜F Integer⌝`
    /// are each refused naming the quote, and the arena is left at its mark.
    #[test]
    fn a_code_is_refused_by_name()
    {
        let mut core = CoreArena::new();
        let integer = core.value_type_base(gandr_kernel_term::BaseType::Integer);
        let returns_integer = core.comp_type_returner(integer);
        let quoted = core.value_quote(integer);
        let quoted_computation = core.value_quote_computation(returns_integer);
        for code in [quoted, quoted_computation] {
            let term = core.computation_return(code);
            let mut arena = CommandArena::new();
            let mut provenance = Provenance::new();
            let mark = arena.watermark();
            assert_eq!(
                focus_computation(&core, term, &mut arena, &mut provenance),
                Err(FocusRefusal::Code(code)),
                "the quote is refused by name"
            );
            assert_eq!(mark, arena.watermark(), "the arena is back at its mark");
        }
    }

    /// Focusing threads no name supply: one term focused into two fresh
    /// arenas builds identical arenas, and every covariable it mints is the
    /// innermost one.
    #[test]
    fn focusing_mints_no_name()
    {
        let mut core = CoreArena::new();
        let unit = core.value_unit();
        let returned = core.computation_return(unit);
        let identity_body =
            core.value_variable(gandr_core_term::Zone::Intuitionistic, 0_u32.into());
        let identity_return = core.computation_return(identity_body);
        let identity = core.computation_lambda(identity_return);
        let thunk = core.value_thunk(identity);
        let forced = core.computation_force(thunk);
        let applied = core.computation_application(forced, unit);
        let bound = core.computation_bind(applied, returned);
        let function = core.computation_lambda(bound);
        let term = core.computation_application(function, unit);

        let focus_fresh = |core: &CoreArena| {
            let mut arena = CommandArena::new();
            let mut provenance = Provenance::new();
            let root = focus_computation(core, term, &mut arena, &mut provenance)
                .expect("a closed term focuses");
            (arena, provenance, root)
        };
        let (first, first_provenance, first_root) = focus_fresh(&core);
        let (second, second_provenance, second_root) = focus_fresh(&core);
        assert_eq!(first, second, "equal inputs build identical arenas");
        assert_eq!(
            first_provenance, second_provenance,
            "and identical provenance"
        );
        assert_eq!(first_root, second_root, "and the same root");

        let consumers = usize::from(first.consumer_count());
        for offset in 0 .. consumers {
            let id = ConsumerId::from(u32::try_from(offset).expect("a small arena"));
            if let Some(&ConsumerNode::Covariable(index)) = first.consumer(id) {
                assert_eq!(
                    CovariableIndex::from(0_u32),
                    index,
                    "every focused covariable is the innermost one"
                );
            }
        }
    }
}
