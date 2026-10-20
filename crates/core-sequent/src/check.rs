//! The typed-IL check: the well-formedness every command the machine runs is
//! held to.
//!
//! [`check_command`] visits a command and every node below it and refuses, by
//! name:
//!
//! - **reference integrity** — an address the arena does not hold, and an
//!   annotation its annotation arena does not hold;
//! - **arity** — a constructor or destructor whose producer or consumer
//!   children contradict the counts its head declares, and a match or copattern
//!   object answering one head twice;
//! - **focus** — a `μ` standing as a constructor field or a frame argument,
//!   where only a value may stand;
//! - **polarity** — a cut whose producer or consumer observes the other
//!   polarity: constructors, literals, thunks, recursive thunks, matches,
//!   nominal matches, selections and force frames are positive; copattern
//!   objects and application frames are negative; variables, constants, `μ`,
//!   covariables, `μ̃` and `★` take the cut's polarity.
//!
//! Scope is carried, not walked (`il` § Scope is carried): minting alone
//! writes a node's support, the union of what the node names and its
//! children's supports past the binders it opens over each, so the check
//! reads scope rather than rebuilding it. On success it answers the command's
//! free variables and covariables, read off the root's carried support and
//! counted from the command, so a caller asks for a closed command by asking
//! for an empty [`FreeSet`]. A linear variable is bound only by a memory form's
//! hold or access body; every other binder leaves it free. An annotation's
//! support is read off the core type's root, which carries it.
//!
//! The arena is acyclic by construction, so the visit is a loop over an
//! explicit stack with no depth limit. The check covers what is decidable from
//! a command alone: the IL carries no source types for a two-sided type check.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
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
use crate::il::NodeAddress;
use crate::il::NodeScope;
use crate::il::ProducerId;
use crate::il::ProducerNode;
use crate::il::command_children;
use crate::il::command_signature;
use crate::il::consumer_annotations;
use crate::il::consumer_children;
use crate::il::producer_children;

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
    /// A node naming an annotation the annotation arena does not hold.
    DanglingAnnotation(NodeAddress),
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
            Self::DanglingAnnotation(node) => {
                write!(f, "{node} names an annotation that is not in the arena")
            },
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

    /// The free set a carried scope selects.
    ///
    /// # Specification
    /// trivial.
    fn of(scope: NodeScope<'_>) -> Self
    {
        let producers = [Zone::Intuitionistic, Zone::Linear]
            .into_iter()
            .flat_map(|zone| {
                scope
                    .producers()
                    .indices(zone)
                    .map(move |index| (zone, index))
            })
            .collect();
        let covariables = scope
            .covariables()
            .indices(Zone::Intuitionistic)
            .map(|index| CovariableIndex::from(u32::from(index)))
            .collect();
        Self {
            producers,
            covariables,
        }
    }
}

/// Check a command and everything below it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: on success the command's free producer variables and covariables,
///   each index counted from the command, as its carried support selects them;
///   the command is then reference-intact, arity-correct, focused and
///   polarity-consistent.
/// - provides: the one well-formedness judgement over the IL.
/// - fails: the first [`CheckRefusal`] a depth-first visit meets.
/// - panics: none.
/// - intension: one stack entry and one presence read per node occurrence below
///   the command, one presence read per annotation, and one support read at the
///   root.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — each refusal is reached by a minimal command that breaks
///   only its rule and asserted by exact variant and payload; the arity rule is
///   separated from a constant by one count admitted at one head and refused at
///   the other; scope by one variable free and the same variable bound. L2 — on
///   every command of every generated focused term the answer equals the free
///   set an independent walk computes.
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
/// - witness: `tests::focus_properties::root_support_equals_the_walk_on_every_focused_term`
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
        stack: alloc::vec![NodeAddress::Command(command)],
    };
    while let Some(node) = walk.stack.pop() {
        match node {
            NodeAddress::Command(id) => walk.command(id)?,
            NodeAddress::Producer(id) => walk.producer(id)?,
            NodeAddress::Consumer(id) => walk.consumer(id)?,
        }
    }
    let root = arena
        .node_scope(NodeAddress::Command(command))
        .ok_or(CheckRefusal::DanglingCommand(command))?;
    Ok(FreeSet::of(root))
}

/// The state of one check.
struct Walk<'run>
{
    /// The arena checked.
    arena: &'run CommandArena,
    /// The pending nodes, the next one last.
    stack: Vec<NodeAddress>,
}

impl Walk<'_>
{
    /// Check one command and schedule its children.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the command's children are scheduled in edge
    ///   order, the first on top.
    /// - provides: the polarity rule.
    /// - fails: a dangling command, side or child; a cut side observing the
    ///   other polarity; an annotation the arena does not hold.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — both polarities and inherited heads distinguish
    ///   polarity inversions; a missing root distinguishes skipped lookup;
    ///   exact free sets of control commands distinguish a body's binder
    ///   leaking into the command's scope.
    /// - witness: `check::tests::terminal_cut_is_wellformed`
    /// - witness: `check::tests::dangling_reference_is_rejected`
    /// - witness: `check::tests::polarity_mismatch_is_rejected`
    /// - witness: `check::tests::control_scopes_are_local_to_each_body`
    #[spec(
        captures: [work = self.stack.len()],
        ensures: |ref ret| ret.is_err() || self.arena.command(id).is_some_and(|node| {
            let mut listed = 0_usize;
            let _listing = command_children(node, |_, _| {
                listed = listed.saturating_add(1);
                Ok::<(), CheckRefusal>(())
            });
            work.checked_add(listed) == Some(self.stack.len())
        }),
    )]
    fn command(
        &mut self,
        id: CommandId,
    ) -> Result<(), CheckRefusal>
    {
        let arena = self.arena;
        let node = arena
            .command(id)
            .ok_or_else(|| dangling(NodeAddress::Command(id)))?;
        if let CommandNode::Cut {
            polarity,
            producer,
            consumer,
        } = *node
        {
            let sent = arena
                .producer(producer)
                .ok_or_else(|| dangling(NodeAddress::Producer(producer)))?;
            let received = arena
                .consumer(consumer)
                .ok_or_else(|| dangling(NodeAddress::Consumer(consumer)))?;
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
        }
        if let Some(signature) = command_signature(node) {
            self.annotated(NodeAddress::Command(id), signature.types())?;
        }
        let work = self.stack.len();
        command_children(node, |child, _| self.schedule(child))?;
        if let Some(pushed) = self.stack.get_mut(work ..) {
            pushed.reverse();
        }
        Ok(())
    }

    /// Check one producer and schedule its children.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the producer's children are scheduled in edge
    ///   order, the first on top.
    /// - provides: the arity and focus rules for producers.
    /// - fails: a dangling address, an arity or duplicate-arm violation, or a
    ///   `μ` field.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — free and bound producer occurrences, exact arities
    ///   and duplicate heads distinguish wrong crossings and missing structural
    ///   checks.
    /// - witness: `check::tests::scope_tracks_binders`
    /// - witness: `check::tests::constructor_arity_is_checked`
    /// - witness: `check::tests::constructor_consumer_arity_is_checked`
    /// - witness: `check::tests::non_value_argument_is_rejected`
    /// - witness: `check::tests::a_head_answered_twice_is_rejected`
    /// - witness: `check::tests::child_refusals_follow_declared_precedence`
    /// - witness: `check::tests::scope_boundaries_keep_linear_variables_free`
    #[spec(
        captures: [work = self.stack.len()],
        ensures: |ref ret| ret.is_err() || self.arena.producer(id).is_some_and(|node| {
            let mut listed = 0_usize;
            let _listing = producer_children(node, |_, _| {
                listed = listed.saturating_add(1);
                Ok::<(), CheckRefusal>(())
            });
            work.checked_add(listed) == Some(self.stack.len())
        }),
    )]
    fn producer(
        &mut self,
        id: ProducerId,
    ) -> Result<(), CheckRefusal>
    {
        let arena = self.arena;
        let node = arena
            .producer(id)
            .ok_or_else(|| dangling(NodeAddress::Producer(id)))?;
        match *node {
            ProducerNode::Constructor {
                ref tag,
                ref producers,
                ref consumers,
            } => {
                let head = ArityHead::Constructor(tag.clone());
                self.fields(
                    head,
                    tag.producer_arity(),
                    tag.consumer_arity(),
                    producers,
                    consumers,
                )?;
            },
            ProducerNode::Cocase { ref arms } => {
                let mut seen = BTreeSet::new();
                for arm in arms {
                    if !seen.insert(arm.destructor) {
                        return Err(CheckRefusal::DuplicateArm(ArityHead::Destructor(
                            arm.destructor,
                        )));
                    }
                }
            },
            ProducerNode::Reify(_)
            | ProducerNode::Primitive { .. }
            | ProducerNode::Variable { .. }
            | ProducerNode::Constant(_)
            | ProducerNode::Literal(_)
            | ProducerNode::Code(_)
            | ProducerNode::Thunk { .. }
            | ProducerNode::Fixpoint { .. }
            | ProducerNode::Mu { .. } => {},
        }
        let work = self.stack.len();
        producer_children(node, |child, _| self.schedule(child))?;
        if let Some(pushed) = self.stack.get_mut(work ..) {
            pushed.reverse();
        }
        Ok(())
    }

    /// Check one consumer and schedule its children.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the consumer's children are scheduled in edge
    ///   order, the first on top.
    /// - provides: the arity and focus rules for consumers.
    /// - fails: a dangling address, an arity or duplicate-arm violation, a `μ`
    ///   argument, or an annotation the arena does not hold.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — free and bound covariables, both destructor arities
    ///   and duplicate pattern heads distinguish wrong crossings, ignored
    ///   continuations and missing uniqueness checks by exact sets and errors.
    /// - witness: `check::tests::scope_tracks_binders`
    /// - witness: `check::tests::destructor_consumer_arity_is_checked`
    /// - witness: `check::tests::consumer_arity_follows_the_head_not_a_constant`
    /// - witness: `check::tests::a_head_answered_twice_is_rejected`
    /// - witness: `check::tests::child_refusals_follow_declared_precedence`
    /// - witness: `check::tests::scope_boundaries_keep_linear_variables_free`
    #[spec(
        captures: [work = self.stack.len()],
        ensures: |ref ret| ret.is_err() || self.arena.consumer(id).is_some_and(|node| {
            let mut listed = 0_usize;
            let _listing = consumer_children(node, |_, _| {
                listed = listed.saturating_add(1);
                Ok::<(), CheckRefusal>(())
            });
            work.checked_add(listed) == Some(self.stack.len())
        }),
    )]
    fn consumer(
        &mut self,
        id: ConsumerId,
    ) -> Result<(), CheckRefusal>
    {
        let arena = self.arena;
        let node = arena
            .consumer(id)
            .ok_or_else(|| dangling(NodeAddress::Consumer(id)))?;
        match *node {
            ConsumerNode::Destructor {
                tag,
                ref producers,
                ref consumers,
            } => {
                let head = ArityHead::Destructor(tag);
                self.fields(
                    head,
                    tag.producer_arity(),
                    tag.consumer_arity(),
                    producers,
                    consumers,
                )?;
            },
            #[cfg_attr(
                dylint_lib = "quenchant_dylints",
                expect(
                    linear_search_in_loop,
                    reason = "bounded: `seen` holds the arms one case writes; a constructor head \
                              has no order to key a set by, and the crate takes no hasher"
                )
            )]
            ConsumerNode::Case { ref arms } => {
                let mut seen: Vec<&ConstructorTag> = Vec::new();
                for arm in arms {
                    if seen.contains(&&arm.constructor) {
                        return Err(CheckRefusal::DuplicateArm(ArityHead::Constructor(
                            arm.constructor.clone(),
                        )));
                    }
                    seen.push(&arm.constructor);
                }
            },
            ConsumerNode::DataCase { ref branches, .. } => {
                for &branch in branches {
                    let node = arena
                        .producer(branch)
                        .ok_or_else(|| dangling(NodeAddress::Producer(branch)))?;
                    if let ProducerNode::Mu { .. } = *node {
                        return Err(CheckRefusal::NonValueArgument(branch));
                    }
                }
            },
            ConsumerNode::Covariable(_)
            | ConsumerNode::Top
            | ConsumerNode::ListFold { .. }
            | ConsumerNode::MuTilde { .. }
            | ConsumerNode::Select { .. } => {},
        }
        self.annotated(NodeAddress::Consumer(id), consumer_annotations(node))?;
        let work = self.stack.len();
        consumer_children(node, |child, _| self.schedule(child))?;
        if let Some(pushed) = self.stack.get_mut(work ..) {
            pushed.reverse();
        }
        Ok(())
    }

    /// Hold a constructor's or destructor's children to its head's
    /// declaration.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the counts match the head's and no producer child
    ///   is a `μ`; nothing is scheduled.
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
    ///   through the root free set; consumer lookup is deferred to the cover
    ///   check.
    /// - witness: `check::tests::child_refusals_follow_declared_precedence`
    /// - witness: `check::tests::constructor_arity_is_checked`
    /// - witness: `check::tests::destructor_consumer_arity_is_checked`
    /// - witness: `check::tests::scope_tracks_binders`
    #[spec(
        captures: [work = self.stack.len()],
        ensures: |ref ret| self.stack.len() == work && (ret.is_err() || (
            producers.len() == usize::from(producer_arity)
                && consumers.len() == usize::from(consumer_arity)
                && producers.iter().all(|id| self.arena.producer(*id)
                    .is_some_and(|node| !matches!(node, &ProducerNode::Mu { .. }))))),
    )]
    fn fields(
        &self,
        head: ArityHead,
        producer_arity: ProducerArity,
        consumer_arity: ConsumerArity,
        producers: &[ProducerId],
        consumers: &[ConsumerId],
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
                .ok_or_else(|| dangling(NodeAddress::Producer(producer)))?;
            if let ProducerNode::Mu { .. } = *node {
                return Err(CheckRefusal::NonValueArgument(producer));
            }
        }
        Ok(())
    }

    /// Hold `node`'s annotations to the annotation arena.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: success exactly when the annotation arena holds every
    ///   annotation.
    /// - fails: [`CheckRefusal::DanglingAnnotation`] naming `node`.
    /// - panics: none.
    /// - executable: none — `annotations` is consumed by the call, so a
    ///   predicate has no second walk of it.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fold over annotations the arena holds is accepted
    ///   and reads its annotation's variable off the root's support.
    /// - witness: `il::tests::an_annotation_counts_in_its_nodes_support`
    #[inline]
    fn annotated<Annotations>(
        &self,
        node: NodeAddress,
        annotations: Annotations,
    ) -> Result<(), CheckRefusal>
    where
        Annotations: IntoIterator<Item = ValueTypeId>,
    {
        let types = self.arena.annotations();
        for annotation in annotations {
            if types.value_type(annotation).is_none() {
                return Err(CheckRefusal::DanglingAnnotation(node));
            }
        }
        Ok(())
    }

    /// Schedule a child, refusing it first when the arena does not hold it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the child is pushed.
    /// - fails: a dangling child, nothing pushed.
    /// - panics: none.
    /// - executable: none — a per-child step of the check; the visiting node's
    ///   own specification counts what it pushed.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a dangling child of each family and a live one
    ///   separate the refusal from the schedule.
    /// - witness: `check::tests::dangling_reference_is_rejected`
    #[inline]
    fn schedule(
        &mut self,
        child: NodeAddress,
    ) -> Result<(), CheckRefusal>
    {
        if self.arena.slots(child).is_none() {
            return Err(dangling(child));
        }
        self.stack.push(child);
        Ok(())
    }
}

/// The refusal naming a node the arena does not hold.
///
/// # Specification
/// trivial.
const fn dangling(node: NodeAddress) -> CheckRefusal
{
    match node {
        NodeAddress::Producer(id) => CheckRefusal::DanglingProducer(id),
        NodeAddress::Consumer(id) => CheckRefusal::DanglingConsumer(id),
        NodeAddress::Command(id) => CheckRefusal::DanglingCommand(id),
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
    | ProducerNode::Reify(_) | ProducerNode::Primitive { .. } | ProducerNode::Literal(_) | ProducerNode::Code(_) | ProducerNode::Constructor { .. } | ProducerNode::Thunk { .. } | ProducerNode::Fixpoint { .. } => Some(Polarity::Positive),
    | ProducerNode::Cocase { .. } => Some(Polarity::Negative),
    | ProducerNode::Variable { .. } | ProducerNode::Constant(_) | ProducerNode::Mu { .. } => None,
})]
fn producer_polarity(node: &ProducerNode) -> Option<Polarity>
{
    match *node {
        ProducerNode::Reify(_)
        | ProducerNode::Primitive { .. }
        | ProducerNode::Literal(_)
        | ProducerNode::Code(_)
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
