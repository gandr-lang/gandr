//! The typed-IL check: the well-formedness every command the machine runs is
//! held to.
//!
//! [`check_command`] walks a command and every node below it and refuses, by
//! name:
//!
//! - **reference integrity** — an address the arena does not hold;
//! - **arity** — a constructor or destructor whose producer or consumer
//!   children contradict the counts its head declares, and a match or copattern
//!   object answering one head twice;
//! - **focus** — a `μ` standing as a constructor field or a frame argument,
//!   where only a value may stand;
//! - **polarity** — a cut whose producer or consumer observes the other
//!   polarity: constructors, literals, thunks, matches, selections and force
//!   frames are positive; copattern objects and application frames are
//!   negative; variables, constants, `μ`, covariables, `μ̃` and `★` take the
//!   cut's polarity.
//!
//! On success it answers the command's free variables and covariables, as
//! indices counted from the command itself, so scope is checked by the caller
//! asking for a closed command. The walk is a loop over an explicit stack.
//!
//! # The typed-IL check
//!
//! `check_command` walks a command and every node below it and refuses, by
//! name, an address the arena does not hold; a constructor or destructor whose
//! producer or consumer children contradict the counts its head declares; a
//! match or copattern object answering one head twice; a `μ` standing where
//! only a value may; and a cut whose producer or consumer observes the other
//! polarity. Constructors, literals, thunks, recursive thunks, matches, nominal
//! matches, selections and force frames are positive, copattern objects and
//! application frames negative, and variables, constants, `μ`, covariables,
//! `μ̃` and `★` take the cut's polarity. On success it answers the command's
//! free variables and covariables, counted from the command, so a caller asks
//! for a closed command by asking for an empty `FreeSet`. A linear variable is
//! bound only by a memory form's hold or access body; every other binder
//! leaves it free.
//!
//! The arena is acyclic by construction, so the walk is a loop with no depth
//! limit. The alternative was a full two-sided type check, which needs the
//! source types the IL does not carry; the check covers what is decidable from
//! a command alone. The choice reverses if the IL comes to carry types.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_core_term::Zone;
use gandr_core_term::memory::MemoryForm;
use gandr_kernel_term::DeBruijnIndex;
use gandr_theory_cell_complexes::Polarity;

use crate::boundary::ConsumerArity;
use crate::boundary::ProducerArity;
use crate::il::CommandArena;
use crate::il::CommandId;
use crate::il::CommandNode;
use crate::il::ConstructorTag;
use crate::il::ConsumerId;
use crate::il::ConsumerNode;
use crate::il::CovariableIndex;
use crate::il::DestructorTag;
use crate::il::Introduces;
use crate::il::ProducerId;
use crate::il::ProducerNode;
use crate::il::Route;

/// A head whose arity a node is held to.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum ArityHead
{
    /// A constructor head.
    Constructor(ConstructorTag),
    /// A destructor head.
    Destructor(DestructorTag),
}

/// Why a command is not well formed.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum CheckRefusal
{
    /// A command address the arena does not hold.
    DanglingCommand(CommandId),
    /// A producer address the arena does not hold.
    DanglingProducer(ProducerId),
    /// A consumer address the arena does not hold.
    DanglingConsumer(ConsumerId),
    /// A `μ` standing where only a value may.
    NonValueArgument(ProducerId),
    /// A cut whose side observes the other polarity.
    PolarityMismatch
    {
        /// The cut.
        command: CommandId,
        /// The cut's polarity.
        cut: Polarity,
        /// The polarity a side observes.
        observed: Polarity,
    },
    /// Producer children contradicting the head's declaration.
    ProducerArity
    {
        /// The head.
        head: ArityHead,
        /// The declared count.
        expected: ProducerArity,
        /// The count found.
        found: ProducerArity,
    },
    /// Consumer children contradicting the head's declaration.
    ConsumerArity
    {
        /// The head.
        head: ArityHead,
        /// The declared count.
        expected: ConsumerArity,
        /// The count found.
        found: ConsumerArity,
    },
    /// A match or copattern object answering one head twice.
    DuplicateArm(ArityHead),
}

impl fmt::Display for CheckRefusal
{
    /// Names the ill-formed node and the rule it breaks.
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
            Self::DanglingCommand(id) => write!(f, "command {id} is not in the arena"),
            Self::DanglingProducer(id) => write!(f, "producer {id} is not in the arena"),
            Self::DanglingConsumer(id) => write!(f, "consumer {id} is not in the arena"),
            Self::NonValueArgument(id) => {
                write!(f, "producer {id} is a capture where a value must stand")
            },
            Self::PolarityMismatch { command, .. } => {
                write!(f, "command {command} cuts a side of the other polarity")
            },
            Self::ProducerArity {
                expected, found, ..
            } => {
                write!(
                    f,
                    "a head declaring {expected} producer children has {found}"
                )
            },
            Self::ConsumerArity {
                expected, found, ..
            } => {
                write!(
                    f,
                    "a head declaring {expected} consumer children has {found}"
                )
            },
            Self::DuplicateArm(_) => f.write_str("a head is answered by two arms"),
        }
    }
}

impl core::error::Error for CheckRefusal
{
}

/// The free variables and covariables of a well-formed command, counted from
/// the command itself.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct FreeSet
{
    /// The free producer variables, by zone and index.
    producers: BTreeSet<(Zone, DeBruijnIndex)>,
    /// The free covariables.
    covariables: BTreeSet<CovariableIndex>,
}

impl FreeSet
{
    /// The free producer variables, by zone and index.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn producers(&self) -> &BTreeSet<(Zone, DeBruijnIndex)>
    {
        &self.producers
    }

    /// The free covariables.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn covariables(&self) -> &BTreeSet<CovariableIndex>
    {
        &self.covariables
    }
}

/// Check a command and everything below it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: on success the command's free producer variables and covariables,
///   each index counted from the command; the command is then reference-intact,
///   arity-correct, focused and polarity-consistent.
/// - provides: the one well-formedness judgement over the IL.
/// - fails: the first [`CheckRefusal`] a depth-first walk meets.
/// - panics: none.
/// - intension: one stack entry per node occurrence below the command.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — each refusal is reached by a minimal command that breaks
///   only its rule and asserted by exact variant and payload; the arity rule is
///   separated from a constant by one count admitted at one head and refused at
///   the other; scope by one variable free and the same variable bound.
/// - witness: `check::tests::terminal_cut_is_wellformed`
/// - witness: `check::tests::scope_tracks_binders`
/// - witness: `check::tests::dangling_reference_is_rejected`
/// - witness: `check::tests::non_value_argument_is_rejected`
/// - witness: `check::tests::polarity_mismatch_is_rejected`
/// - witness: `check::tests::constructor_arity_is_checked`
/// - witness: `check::tests::constructor_consumer_arity_is_checked`
/// - witness: `check::tests::destructor_consumer_arity_is_checked`
/// - witness: `check::tests::consumer_arity_follows_the_head_not_a_constant`
/// - witness: `check::tests::a_head_answered_twice_is_rejected`
/// - witness: `tests::focus_properties::focusing_is_total_on_generated_computations`
#[inline]
#[spec(ensures: |ref ret| match ret.as_ref() {
    | Err(error) => arena.command(command).is_some() || *error == CheckRefusal::DanglingCommand(command),
    | Ok(free) => arena.command(command).is_some_and(|node| {
        let &CommandNode::Cut { producer, consumer, .. } = node else { return true; };
        (match arena.producer(producer) {
            | Some(&ProducerNode::Variable { zone, index }) => free.producers.contains(&(zone, index)),
            | Some(_) => true,
            | None => false,
        }) && match arena.consumer(consumer) {
            | Some(&ConsumerNode::Covariable(index)) => free.covariables.contains(&index),
            | Some(_) => true,
            | None => false,
        }
    }),
})]
pub fn check_command(
    arena: &CommandArena,
    command: CommandId,
) -> Result<FreeSet, CheckRefusal>
{
    let mut walk = Walk {
        arena,
        stack: alloc::vec![Visit::Command(command, Depth::default())],
        free: FreeSet::default(),
    };
    while let Some(visit) = walk.stack.pop() {
        match visit {
            Visit::Command(id, depth) => walk.command(id, depth)?,
            Visit::Producer(id, depth) => walk.producer(id, depth)?,
            Visit::Consumer(id, depth) => walk.consumer(id, depth)?,
        }
    }
    Ok(walk.free)
}

/// The binders opened above a node.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct Depth
{
    /// Producer binders.
    producers: u32,
    /// Covariable binders.
    covariables: u32,
    /// Linear producer binders: the held values and views of the memory
    /// forms above.
    linears: u32,
}

impl Depth
{
    /// The depth under further binders, saturating at a ceiling no arena of at
    /// most `u32::MAX` nodes per family can reach.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each depth is increased by its corresponding arity, with
    ///   arities wider than `u32` and sums past its ceiling saturating there;
    ///   the linear depth is unchanged.
    /// - provides: independent scope offsets for the two binding namespaces.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero, ordinary and ceiling-crossing arities are
    ///   applied to distinct producer and covariable depths. Exact paired
    ///   counts distinguish exchanged arities, wrapping and premature clamping.
    /// - witness: `check::tests::scope_depths_widen_and_saturate_independently`
    #[spec(ensures: |ret|
        ret.producers == self.producers.saturating_add(u32::try_from(usize::from(producers)).unwrap_or(u32::MAX))
            && ret.covariables == self.covariables.saturating_add(u32::try_from(usize::from(covariables)).unwrap_or(u32::MAX))
            && ret.linears == self.linears
    )]
    fn under(
        self,
        producers: ProducerArity,
        covariables: ConsumerArity,
    ) -> Self
    {
        let widen = |count: usize| u32::try_from(count).unwrap_or(u32::MAX);
        Self {
            producers: self.producers.saturating_add(widen(usize::from(producers))),
            covariables: self
                .covariables
                .saturating_add(widen(usize::from(covariables))),
            linears: self.linears,
        }
    }

    /// The depth under one more linear binder, saturating at the ceiling.
    ///
    /// # Specification
    /// trivial.
    const fn under_linear(self) -> Self
    {
        Self {
            linears: self.linears.saturating_add(1),
            ..self
        }
    }
}

/// One pending node of the walk.
#[derive(Clone, Copy, Debug)]
enum Visit
{
    /// A command at a depth.
    Command(CommandId, Depth),
    /// A producer at a depth.
    Producer(ProducerId, Depth),
    /// A consumer at a depth.
    Consumer(ConsumerId, Depth),
}

/// The state of one check.
struct Walk<'run>
{
    /// The arena checked.
    arena: &'run CommandArena,
    /// The pending nodes, the next one last.
    stack: Vec<Visit>,
    /// The free set gathered so far.
    free: FreeSet,
}

impl Walk<'_>
{
    /// Check one cut's polarity and schedule its two sides.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the producer and consumer are scheduled at the cut's depth.
    /// - provides: the polarity rule.
    /// - fails: a dangling side, or a side observing the other polarity.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — both polarities and inherited heads distinguish
    ///   polarity inversions; a missing root distinguishes skipped lookup.
    ///   Exact free sets and refusals observe the scheduled sides.
    /// - witness: `check::tests::terminal_cut_is_wellformed`
    /// - witness: `check::tests::scope_tracks_binders`
    /// - witness: `check::tests::dangling_reference_is_rejected`
    /// - witness: `check::tests::polarity_mismatch_is_rejected`
    /// - witness: `check::tests::every_node_kind_declares_its_intrinsic_polarity`
    #[spec(
        captures: [work = self.stack.len()],
        ensures: |ref ret| ret.is_err() || self.arena.command(id).is_some_and(|node| match *node {
            CommandNode::Cut { producer, consumer, .. } => work.checked_add(2) == Some(self.stack.len())
                && matches!(self.stack.get(work), Some(&Visit::Consumer(found, under)) if found == consumer && under == depth)
                && matches!(self.stack.last(), Some(&Visit::Producer(found, under)) if found == producer && under == depth),
            CommandNode::Perform { .. } | CommandNode::Handle { .. } | CommandNode::Resume { .. } | CommandNode::Reset { .. } | CommandNode::Shift { .. } | CommandNode::Memory { .. } => self.stack.len() > work,
        }),
    )]
    fn command(
        &mut self,
        id: CommandId,
        depth: Depth,
    ) -> Result<(), CheckRefusal>
    {
        let &CommandNode::Cut {
            polarity,
            producer,
            consumer,
        } = self
            .arena
            .command(id)
            .ok_or(CheckRefusal::DanglingCommand(id))?
        else {
            return self.control_command(id, depth);
        };
        let sent = self
            .arena
            .producer(producer)
            .ok_or(CheckRefusal::DanglingProducer(producer))?;
        let received = self
            .arena
            .consumer(consumer)
            .ok_or(CheckRefusal::DanglingConsumer(consumer))?;
        for observed in [producer_polarity(sent), consumer_polarity(received)]
            .into_iter()
            .flatten()
        {
            if observed != polarity {
                return Err(CheckRefusal::PolarityMismatch {
                    command: id,
                    cut: polarity,
                    observed,
                });
            }
        }
        self.stack.push(Visit::Consumer(consumer, depth));
        self.stack.push(Visit::Producer(producer, depth));
        Ok(())
    }

    /// Schedule control children under their declared value and return binders.
    ///
    /// # Specification
    /// - ensures: signatures erase no runtime binding; an exercise reads its
    ///   capability beside its payload; subjects, resumes and resets bind one
    ///   return, a scope's subject its capability first, shift binds a stack,
    ///   and handler clauses bind payload then stack independently from the
    ///   return clause's one value.
    /// - fails: a missing or non-control command.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exact free sets outside each local binder distinguish
    ///   captured ambient variables and covariables from clause-local indices.
    /// - witness: `check::tests::control_scopes_are_local_to_each_body`
    #[spec(captures: work = self.stack.len(), ensures: |ret| ret.is_err() || self.stack.len() > work)]
    fn control_command(
        &mut self,
        id: CommandId,
        depth: Depth,
    ) -> Result<(), CheckRefusal>
    {
        let node = self
            .arena
            .command(id)
            .ok_or(CheckRefusal::DanglingCommand(id))?;
        match *node {
            CommandNode::Cut { .. } => self.stack.push(Visit::Command(id, depth)),
            CommandNode::Perform {
                route,
                payload,
                continuation,
                ..
            } => {
                self.stack.push(Visit::Consumer(continuation, depth));
                self.stack.push(Visit::Producer(payload, depth));
                if let Route::Capability(capability) = route {
                    self.stack.push(Visit::Producer(capability, depth));
                }
            },
            CommandNode::Handle {
                introduces,
                subject,
                on_return,
                ref clauses,
                continuation,
                ..
            } => {
                self.stack.push(Visit::Consumer(continuation, depth));
                for clause in clauses.iter().rev() {
                    self.stack.push(Visit::Command(
                        clause.body,
                        depth.under(ProducerArity::TWO, ConsumerArity::ONE),
                    ));
                }
                self.stack.push(Visit::Command(
                    on_return,
                    depth.under(ProducerArity::ONE, ConsumerArity::ONE),
                ));
                let bound = match introduces {
                    Introduces::Nothing => ProducerArity::ZERO,
                    Introduces::Capability => ProducerArity::ONE,
                };
                self.stack.push(Visit::Command(
                    subject,
                    depth.under(bound, ConsumerArity::ONE),
                ));
            },
            CommandNode::Resume {
                stack,
                body,
                continuation,
            } => {
                self.stack.push(Visit::Consumer(continuation, depth));
                self.stack.push(Visit::Command(
                    body,
                    depth.under(ProducerArity::ZERO, ConsumerArity::ONE),
                ));
                self.stack.push(Visit::Producer(stack, depth));
            },
            CommandNode::Reset { body, continuation } => {
                self.stack.push(Visit::Consumer(continuation, depth));
                self.stack.push(Visit::Command(
                    body,
                    depth.under(ProducerArity::ZERO, ConsumerArity::ONE),
                ));
            },
            CommandNode::Shift { body, continuation } => {
                self.stack.push(Visit::Consumer(continuation, depth));
                self.stack.push(Visit::Command(
                    body,
                    depth.under(ProducerArity::ONE, ConsumerArity::ONE),
                ));
            },
            CommandNode::Memory {
                ref form,
                continuation,
            } => {
                self.stack.push(Visit::Consumer(continuation, depth));
                for (body, linears) in form.scoped() {
                    let under = depth.under(ProducerArity::ZERO, ConsumerArity::ONE);
                    let under = if linears == gandr_core_term::Binders::NONE {
                        under
                    }
                    else {
                        under.under_linear()
                    };
                    self.stack.push(Visit::Command(body, under));
                }
                for value in form.values() {
                    self.stack.push(Visit::Producer(value, depth));
                }
                match *form {
                    MemoryForm::Access { held: index, .. }
                    | MemoryForm::Resume { view: index, .. }
                    | MemoryForm::Abort { view: index } => self.linear(index, depth),
                    MemoryForm::Hold { .. } => {},
                }
            },
        }
        Ok(())
    }

    /// Record a linear occurrence free when it counts past the linear binders
    /// above it.
    ///
    /// # Specification
    /// trivial.
    fn linear(
        &mut self,
        index: DeBruijnIndex,
        depth: Depth,
    )
    {
        if let Some(past) = u32::from(index).checked_sub(depth.linears) {
            self.free
                .producers
                .insert((Zone::Linear, DeBruijnIndex::from(past)));
        }
    }

    /// Check one producer and schedule its children.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a free variable is recorded; children are scheduled under the
    ///   binders their parent opens.
    /// - provides: the arity, focus and scope rules for producers.
    /// - fails: a dangling address, an arity or duplicate-arm violation, or a
    ///   `μ` field.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — free and bound producer occurrences, linear
    ///   occurrences under binders, exact arities and duplicate heads
    ///   distinguish wrong index shifts and missing structural checks.
    /// - witness: `check::tests::scope_tracks_binders`
    /// - witness: `check::tests::constructor_arity_is_checked`
    /// - witness: `check::tests::constructor_consumer_arity_is_checked`
    /// - witness: `check::tests::non_value_argument_is_rejected`
    /// - witness: `check::tests::a_head_answered_twice_is_rejected`
    /// - witness: `check::tests::child_refusals_follow_declared_precedence`
    /// - witness: `check::tests::scope_boundaries_keep_linear_variables_free`
    #[spec(
        captures: [free = self.free.producers.len()],
        ensures: |ref ret| ret.is_err() || self.arena.producer(id).is_some_and(|node| match *node {
            | ProducerNode::Variable { zone, index } => u32::from(index).checked_sub(match zone {
                | Zone::Linear => depth.linears,
                | Zone::Intuitionistic => depth.producers,
            })
                .map_or_else(|| self.free.producers.len() == free,
                    |past| self.free.producers.contains(&(zone, DeBruijnIndex::from(past)))),
            | _ => true,
        }),
    )]
    fn producer(
        &mut self,
        id: ProducerId,
        depth: Depth,
    ) -> Result<(), CheckRefusal>
    {
        let node = self
            .arena
            .producer(id)
            .ok_or(CheckRefusal::DanglingProducer(id))?;
        match *node {
            ProducerNode::Reify(ref frames) => {
                for frame in frames.iter().rev() {
                    match *frame {
                        gandr_core_term::control::StackFrame::Apply(value) => {
                            self.stack.push(Visit::Producer(value, depth));
                        },
                        gandr_core_term::control::StackFrame::Bind(body) => {
                            self.stack.push(Visit::Command(
                                body,
                                depth.under(ProducerArity::ONE, ConsumerArity::ONE),
                            ));
                        },
                        gandr_core_term::control::StackFrame::Project(_) => {},
                    }
                }
            },
            ProducerNode::Primitive { arguments, .. } => {
                for argument in arguments.iter().rev() {
                    self.stack.push(Visit::Producer(*argument, depth));
                }
            },
            ProducerNode::Variable { zone, index } => match zone {
                Zone::Intuitionistic => {
                    if let Some(past) = u32::from(index).checked_sub(depth.producers) {
                        self.free
                            .producers
                            .insert((zone, DeBruijnIndex::from(past)));
                    }
                },
                Zone::Linear => self.linear(index, depth),
            },
            ProducerNode::Constant(_) | ProducerNode::Literal(_) => {},
            ProducerNode::Constructor {
                ref tag,
                ref producers,
                ref consumers,
            } => {
                let head = ArityHead::Constructor(tag.clone());
                self.children(
                    head,
                    tag.producer_arity(),
                    tag.consumer_arity(),
                    producers,
                    consumers,
                    depth,
                )?;
            },
            ProducerNode::Thunk { body } | ProducerNode::Mu { body } => {
                self.stack.push(Visit::Command(
                    body,
                    depth.under(ProducerArity::ZERO, ConsumerArity::ONE),
                ));
            },
            ProducerNode::Fixpoint { body, .. } => {
                self.stack.push(Visit::Command(
                    body,
                    depth.under(ProducerArity::ONE, ConsumerArity::ONE),
                ));
            },
            ProducerNode::Cocase { ref arms } => {
                let mut seen = BTreeSet::new();
                for arm in arms {
                    if !seen.insert(arm.destructor) {
                        return Err(CheckRefusal::DuplicateArm(ArityHead::Destructor(
                            arm.destructor,
                        )));
                    }
                    let under = depth.under(
                        arm.destructor.producer_arity(),
                        arm.destructor.consumer_arity(),
                    );
                    self.stack.push(Visit::Command(arm.body, under));
                }
            },
        }
        Ok(())
    }

    /// Check one consumer and schedule its children.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a free covariable is recorded; children are scheduled under
    ///   the binders their parent opens.
    /// - provides: the arity, focus and scope rules for consumers.
    /// - fails: a dangling address, an arity or duplicate-arm violation, or a
    ///   `μ` argument.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — free and bound covariables, both destructor arities
    ///   and duplicate pattern heads distinguish wrong scope offsets, ignored
    ///   continuations and missing uniqueness checks by exact sets and errors.
    /// - witness: `check::tests::scope_tracks_binders`
    /// - witness: `check::tests::destructor_consumer_arity_is_checked`
    /// - witness: `check::tests::consumer_arity_follows_the_head_not_a_constant`
    /// - witness: `check::tests::a_head_answered_twice_is_rejected`
    /// - witness: `check::tests::child_refusals_follow_declared_precedence`
    /// - witness: `check::tests::scope_boundaries_keep_linear_variables_free`
    #[spec(
        captures: [free = self.free.covariables.len()],
        ensures: |ref ret| ret.is_err() || self.arena.consumer(id).is_some_and(|node| match *node {
            | ConsumerNode::Covariable(index) => u32::from(index).checked_sub(depth.covariables)
                .map_or_else(|| self.free.covariables.len() == free,
                    |past| self.free.covariables.contains(&CovariableIndex::from(past))),
            | _ => true,
        }),
    )]
    fn consumer(
        &mut self,
        id: ConsumerId,
        depth: Depth,
    ) -> Result<(), CheckRefusal>
    {
        let node = self
            .arena
            .consumer(id)
            .ok_or(CheckRefusal::DanglingConsumer(id))?;
        match *node {
            ConsumerNode::Covariable(index) => {
                if let Some(past) = u32::from(index).checked_sub(depth.covariables) {
                    self.free.covariables.insert(CovariableIndex::from(past));
                }
            },
            ConsumerNode::Top => {},
            ConsumerNode::ListFold {
                on_nil,
                on_cons,
                continuation,
                ..
            } => {
                self.stack.push(Visit::Consumer(continuation, depth));
                self.stack.push(Visit::Command(
                    on_nil,
                    depth.under(ProducerArity::ZERO, ConsumerArity::ONE),
                ));
                self.stack.push(Visit::Command(
                    on_cons,
                    depth.under(ProducerArity::TWO, ConsumerArity::ONE),
                ));
            },
            ConsumerNode::MuTilde { body } => {
                self.stack.push(Visit::Command(
                    body,
                    depth.under(ProducerArity::ONE, ConsumerArity::ZERO),
                ));
            },
            ConsumerNode::Destructor {
                tag,
                ref producers,
                ref consumers,
            } => {
                let head = ArityHead::Destructor(tag);
                self.children(
                    head,
                    tag.producer_arity(),
                    tag.consumer_arity(),
                    producers,
                    consumers,
                    depth,
                )?;
            },
            ConsumerNode::Case { ref arms } => {
                let mut seen: Vec<&ConstructorTag> = Vec::new();
                for arm in arms {
                    if seen.contains(&&arm.constructor) {
                        return Err(CheckRefusal::DuplicateArm(ArityHead::Constructor(
                            arm.constructor.clone(),
                        )));
                    }
                    seen.push(&arm.constructor);
                    let under = depth.under(
                        arm.constructor.producer_arity(),
                        arm.constructor.consumer_arity(),
                    );
                    self.stack.push(Visit::Command(arm.body, under));
                }
            },
            ConsumerNode::DataCase { ref branches, then } => {
                for &branch in branches {
                    let node = self
                        .arena
                        .producer(branch)
                        .ok_or(CheckRefusal::DanglingProducer(branch))?;
                    if let ProducerNode::Mu { .. } = *node {
                        return Err(CheckRefusal::NonValueArgument(branch));
                    }
                }
                self.stack.push(Visit::Consumer(then, depth));
                for &branch in branches.iter().rev() {
                    self.stack.push(Visit::Producer(branch, depth));
                }
            },
            ConsumerNode::Select { then, .. } => {
                self.stack.push(Visit::Consumer(then, depth));
            },
        }
        Ok(())
    }

    /// Hold a constructor's or destructor's children to its head's
    /// declaration and schedule them.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the children are scheduled at `depth`.
    /// - provides: the shared arity and focus rule of both kinds of head.
    /// - fails: [`CheckRefusal::ProducerArity`] before
    ///   [`CheckRefusal::ConsumerArity`], then
    ///   [`CheckRefusal::NonValueArgument`] for the first `μ` child, or a
    ///   dangling child.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — simultaneous wrong counts distinguish producer before
    ///   consumer arity; bad producer addresses and captures at opposite field
    ///   positions distinguish first-field refusal. Valid children are observed
    ///   through the root free set; consumer lookup is deferred to its
    ///   scheduled visit.
    /// - witness: `check::tests::child_refusals_follow_declared_precedence`
    /// - witness: `check::tests::constructor_arity_is_checked`
    /// - witness: `check::tests::destructor_consumer_arity_is_checked`
    /// - witness: `check::tests::scope_tracks_binders`
    #[spec(
        captures: [work = self.stack.len()],
        ensures: |ref ret| if ret.is_ok() {
            producers.len() == usize::from(producer_arity)
                && consumers.len() == usize::from(consumer_arity)
                && work.checked_add(producers.len()).and_then(|count| count.checked_add(consumers.len())) == Some(self.stack.len())
                && producers.iter().all(|id| self.arena.producer(*id)
                    .is_some_and(|node| !matches!(node, &ProducerNode::Mu { .. })))
        } else { self.stack.len() == work },
    )]
    fn children(
        &mut self,
        head: ArityHead,
        producer_arity: ProducerArity,
        consumer_arity: ConsumerArity,
        producers: &[ProducerId],
        consumers: &[ConsumerId],
        depth: Depth,
    ) -> Result<(), CheckRefusal>
    {
        let found = ProducerArity::from(producers.len());
        if found != producer_arity {
            return Err(CheckRefusal::ProducerArity {
                head,
                expected: producer_arity,
                found,
            });
        }
        let found = ConsumerArity::from(consumers.len());
        if found != consumer_arity {
            return Err(CheckRefusal::ConsumerArity {
                head,
                expected: consumer_arity,
                found,
            });
        }
        for &producer in producers {
            let node = self
                .arena
                .producer(producer)
                .ok_or(CheckRefusal::DanglingProducer(producer))?;
            if let ProducerNode::Mu { .. } = *node {
                return Err(CheckRefusal::NonValueArgument(producer));
            }
        }
        for &consumer in consumers.iter().rev() {
            self.stack.push(Visit::Consumer(consumer, depth));
        }
        for &producer in producers.iter().rev() {
            self.stack.push(Visit::Producer(producer, depth));
        }
        Ok(())
    }
}

/// The polarity a producer observes, or `None` when it takes the cut's.
///
/// # Specification
/// - ensures: positive for literals, constructors and thunks; negative for
///   copattern objects; `None` for variables, constants and `μ`.
///
/// # Adequacy
/// - hypothesis: L3 — every producer node kind is assigned its exact intrinsic
///   polarity or inherited polarity. Reclassified literals, functions, thunks
///   and captures change the table observation.
/// - witness: `check::tests::every_node_kind_declares_its_intrinsic_polarity`
#[spec(ensures: |ret| ret == match *node {
    | ProducerNode::Reify(_) | ProducerNode::Primitive { .. } | ProducerNode::Literal(_) | ProducerNode::Constructor { .. } | ProducerNode::Thunk { .. } | ProducerNode::Fixpoint { .. } => Some(Polarity::Positive),
    | ProducerNode::Cocase { .. } => Some(Polarity::Negative),
    | ProducerNode::Variable { .. } | ProducerNode::Constant(_) | ProducerNode::Mu { .. } => None,
})]
fn producer_polarity(node: &ProducerNode) -> Option<Polarity>
{
    match *node {
        ProducerNode::Reify(_)
        | ProducerNode::Primitive { .. }
        | ProducerNode::Literal(_)
        | ProducerNode::Constructor { .. }
        | ProducerNode::Thunk { .. }
        | ProducerNode::Fixpoint { .. } => Some(Polarity::Positive),
        ProducerNode::Cocase { .. } => Some(Polarity::Negative),
        ProducerNode::Variable { .. } | ProducerNode::Constant(_) | ProducerNode::Mu { .. } => None,
    }
}

/// The polarity a consumer observes, or `None` when it takes the cut's.
///
/// # Specification
/// - ensures: positive for matches and selections, the polarity its head
///   observes for a destructor frame, `None` for covariables, `μ̃` and `★`.
///
/// # Adequacy
/// - hypothesis: L3 — every consumer node kind, including both destructor
///   heads, is observed at its exact intrinsic or inherited polarity. Swapped
///   observations and incorrectly fixed tails are distinguished.
/// - witness: `check::tests::every_node_kind_declares_its_intrinsic_polarity`
#[spec(ensures: |ret| ret == match *node {
    | ConsumerNode::ListFold { .. } | ConsumerNode::Case { .. } | ConsumerNode::DataCase { .. } | ConsumerNode::Select { .. } | ConsumerNode::Destructor { tag: DestructorTag::Force, .. } => Some(Polarity::Positive),
    | ConsumerNode::Destructor { tag: DestructorTag::Apply | DestructorTag::Project(_), .. } => Some(Polarity::Negative),
    | ConsumerNode::Covariable(_) | ConsumerNode::MuTilde { .. } | ConsumerNode::Top => None,
})]
fn consumer_polarity(node: &ConsumerNode) -> Option<Polarity>
{
    match *node {
        ConsumerNode::ListFold { .. }
        | ConsumerNode::Case { .. }
        | ConsumerNode::DataCase { .. }
        | ConsumerNode::Select { .. } => Some(Polarity::Positive),
        ConsumerNode::Destructor { tag, .. } => Some(tag.polarity()),
        ConsumerNode::Covariable(_) | ConsumerNode::MuTilde { .. } | ConsumerNode::Top => None,
    }
}

#[cfg(test)]
mod tests;
