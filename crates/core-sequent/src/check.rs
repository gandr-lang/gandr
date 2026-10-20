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
//!   covariables, `μ̃` and `★` take the cut's polarity;
//! - **scope** — a scope the node carries that is not its own: a support that
//!   misses an index the node, its annotations or a child past the binders the
//!   node opens over it names, or selects an index none of them names.
//!
//! Scope is carried, not walked (`il` § Scope is carried): each node's support
//! is held to the union of what it names and its children's carried supports,
//! so a scope that passes at every node of a command is, by induction from the
//! leaves, the command's exact support. On success the check answers the
//! command's free variables and covariables, read off the root's carried
//! support and counted from the command, so a caller asks for a closed command
//! by asking for an empty [`FreeSet`]. A linear variable is bound only by a
//! memory form's hold or access body; every other binder leaves it free. An
//! annotation's support is read off the core type's root, which carries it.
//!
//! The arena is acyclic by construction, so the visit is a loop over an
//! explicit stack with no depth limit. The alternative was a full two-sided
//! type check, which needs the source types the IL does not carry; the check
//! covers what is decidable from a command alone. The choice reverses if the
//! IL comes to carry types.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::support::Agreement;
use gandr_core_term::support::ThinningRef;
use gandr_kernel_term::DeBruijnIndex;
use gandr_theory_cell_complexes::Polarity;
use quenchant_shape::shape::Maybe;

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
use crate::il::Opens;
use crate::il::ProducerId;
use crate::il::ProducerNode;
use crate::il::Scoping;
use crate::il::Slots;
use crate::il::command_annotations;
use crate::il::command_children;
use crate::il::command_named;
use crate::il::consumer_annotations;
use crate::il::consumer_children;
use crate::il::consumer_named;
use crate::il::producer_children;
use crate::il::producer_named;

/// A head whose arity a node is held to.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum ArityHead
{
    /// A constructor head.
    Constructor(ConstructorTag),
    /// A destructor head.
    Destructor(DestructorTag),
}

/// The binders a scope counts: producer variables or covariables.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum BindingSpace
{
    /// Producer variables, in the zones `Γ; Σ`.
    Producers,
    /// Covariables, in `Δ`.
    Covariables,
}

/// What is wrong with a support a node carries.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ScopeFault
{
    /// The node, its annotations or a child past the binders the node opens
    /// over it names an index the node's support does not select.
    Unselected,
    /// The node's support selects an index nothing the node holds names.
    Unused,
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
    /// A node carrying a scope that is not its own.
    ForgedScope
    {
        /// The node.
        node: NodeAddress,
        /// The binders the forged support counts.
        space: BindingSpace,
        /// What is wrong with it.
        fault: ScopeFault,
    },
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
            Self::ForgedScope { node, space, .. } => {
                let counted = match space {
                    BindingSpace::Producers => "variable",
                    BindingSpace::Covariables => "covariable",
                };
                write!(f, "{node} carries a {counted} support that is not its own")
            },
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
///   the command is then reference-intact, arity-correct, focused,
///   polarity-consistent, and every node below it carries its own scope.
/// - provides: the one well-formedness judgement over the IL.
/// - fails: the first [`CheckRefusal`] a depth-first visit meets.
/// - panics: none.
/// - intension: one stack entry per node occurrence below the command; one
///   union per occurrence, linear in the node's children and its support, and
///   one support read per annotation.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — each refusal is reached by a minimal command that breaks
///   only its rule and asserted by exact variant and payload; the arity rule is
///   separated from a constant by one count admitted at one head and refused at
///   the other; scope by one variable free and the same variable bound, and a
///   forged scope in each space and each fault refused by name. L2 — on every
///   command of every generated focused term the answer equals the free set an
///   independent walk computes.
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
/// - witness: `check::tests::a_forged_scope_is_refused_by_name`
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
        scoping: Scoping::new(),
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
    /// The scope rebuilt for the node being checked, empty between nodes.
    scoping: Scoping,
}

impl Walk<'_>
{
    /// Check one command and schedule its children.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the command's children are scheduled in edge
    ///   order, the first on top, and its scope is the union of what it and its
    ///   interface name and its children's scopes.
    /// - provides: the polarity rule, and the scope rule for commands.
    /// - fails: a dangling command, side or child; a cut side observing the
    ///   other polarity; an annotation the arena does not hold; a forged scope.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — both polarities and inherited heads distinguish
    ///   polarity inversions; a missing root distinguishes skipped lookup;
    ///   exact free sets of control commands distinguish a child scheduled
    ///   under the wrong binders, and a forged command scope is refused.
    /// - witness: `check::tests::terminal_cut_is_wellformed`
    /// - witness: `check::tests::dangling_reference_is_rejected`
    /// - witness: `check::tests::polarity_mismatch_is_rejected`
    /// - witness: `check::tests::control_scopes_are_local_to_each_body`
    /// - witness: `check::tests::a_forged_scope_is_refused_by_name`
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
        let (node, carried) = arena
            .command_scoped(id)
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
        let address = NodeAddress::Command(id);
        self.scoping.name(command_named(node), core::iter::empty());
        self.annotated(address, command_annotations(node))?;
        let work = self.stack.len();
        command_children(node, |child, opens| self.scope_child(child, opens))?;
        if let Some(pushed) = self.stack.get_mut(work ..) {
            pushed.reverse();
        }
        self.held(address, carried)
    }

    /// Check one producer and schedule its children.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the producer's children are scheduled in edge
    ///   order, the first on top, and its scope is the union of what it names
    ///   and its children's scopes.
    /// - provides: the arity, focus and scope rules for producers.
    /// - fails: a dangling address, an arity or duplicate-arm violation, a `μ`
    ///   field, or a forged scope.
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
        let (node, carried) = arena
            .producer_scoped(id)
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
        let address = NodeAddress::Producer(id);
        self.scoping.name(producer_named(node), core::iter::empty());
        let work = self.stack.len();
        producer_children(node, |child, opens| self.scope_child(child, opens))?;
        if let Some(pushed) = self.stack.get_mut(work ..) {
            pushed.reverse();
        }
        self.held(address, carried)
    }

    /// Check one consumer and schedule its children.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the consumer's children are scheduled in edge
    ///   order, the first on top, and its scope is the union of what it and its
    ///   annotations name and its children's scopes.
    /// - provides: the arity, focus and scope rules for consumers.
    /// - fails: a dangling address, an arity or duplicate-arm violation, a `μ`
    ///   argument, an annotation the arena does not hold, or a forged scope.
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
        let (node, carried) = arena
            .consumer_scoped(id)
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
        let address = NodeAddress::Consumer(id);
        self.scoping.name(core::iter::empty(), consumer_named(node));
        self.annotated(address, consumer_annotations(node))?;
        let work = self.stack.len();
        consumer_children(node, |child, opens| self.scope_child(child, opens))?;
        if let Some(pushed) = self.stack.get_mut(work ..) {
            pushed.reverse();
        }
        self.held(address, carried)
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

    /// Add the intuitionistic indices `annotations` name, each read where
    /// `node` stands, to the walk's scope being rebuilt.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the walk's scoping holds every intuitionistic
    ///   index each annotation's carried support selects — the same indices
    ///   minting counted.
    /// - provides: the reader's own derivation of what a node's annotations add
    ///   to its support.
    /// - fails: [`CheckRefusal::DanglingAnnotation`] for an annotation the
    ///   annotation arena does not hold.
    /// - panics: none.
    /// - executable: none — `annotations` is consumed by the call, so a
    ///   predicate has no second walk of it, and the scoping is read only by
    ///   finishing it; the witness reads the support back through the check.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fold whose element type names a variable no term
    ///   names is accepted with that variable free, which an ignored annotation
    ///   would refuse as an unused index.
    /// - witness: `il::tests::an_annotation_counts_in_its_nodes_support`
    #[inline]
    fn annotated<Annotations>(
        &mut self,
        node: NodeAddress,
        annotations: Annotations,
    ) -> Result<(), CheckRefusal>
    where
        Annotations: IntoIterator<Item = ValueTypeId>,
    {
        let types = self.arena.annotations();
        for annotation in annotations {
            let support = types
                .value_type_support(annotation)
                .ok_or(CheckRefusal::DanglingAnnotation(node))?;
            self.scoping.annotation(support);
        }
        Ok(())
    }

    /// Add a child's scope, past the binders its node opens over it, to the
    /// walk's scope being rebuilt, and schedule the child.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the walk's scoping holds the child's supports past
    ///   `opens` and the child is pushed.
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
    fn scope_child(
        &mut self,
        child: NodeAddress,
        opens: Opens,
    ) -> Result<(), CheckRefusal>
    {
        let slots = self.arena.slots(child).ok_or_else(|| dangling(child))?;
        self.scoping.child(slots, self.arena.words(), opens);
        self.stack.push(child);
        Ok(())
    }

    /// Hold `carried`, the scope `node` stores, to the one the walk rebuilt
    /// from what it names and its children's scopes, and empty the walk's
    /// scoping for the next node.
    ///
    /// # Specification
    /// - requires: the walk's scoping holds the node's own occurrences, its
    ///   annotations' and every child's scope past the binders it opens over
    ///   the child.
    /// - ensures: on success the node's carried support equals the rebuilt one
    ///   in each space, and the walk's scoping is empty.
    /// - provides: the scope rule.
    /// - fails: [`CheckRefusal::ForgedScope`] naming the space and the fault,
    ///   the producer space first.
    /// - panics: none.
    /// - executable: none — a per-node step of the check; the visiting node's
    ///   own specification states the stack it leaves.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one forged scope per fault and space, each refused by
    ///   exactly its own name; every scope minting builds passes.
    /// - witness: `check::tests::a_forged_scope_is_refused_by_name`
    /// - witness: `tests::focus_properties::root_support_equals_the_walk_on_every_focused_term`
    #[inline]
    fn held(
        &mut self,
        node: NodeAddress,
        carried: Slots,
    ) -> Result<(), CheckRefusal>
    {
        match self.scoping.holds(carried, self.arena.words()) {
            Agreement::Same => {
                self.scoping.clear();
                Ok(())
            },
            Agreement::Different => {
                let rebuilt = core::mem::take(&mut self.scoping).finish();
                forged(node, self.arena.scope_at(carried), rebuilt.view())
            },
        }
    }
}

/// The refusal for a node whose carried scope is not the one rebuilt for it,
/// the producer space first.
///
/// # Specification
/// - requires: `rebuilt` is the scope rebuilt for `node`.
/// - ensures: success exactly when `carried` and `rebuilt` agree in both
///   spaces; otherwise the first space's refusal, as [`space`] names it.
/// - panics: none.
///
/// # Errors
/// As the ensures clause states.
///
/// # Adequacy
/// - hypothesis: L3 — as [`space`], a forged scope in each space.
/// - witness: `check::tests::a_forged_scope_is_refused_by_name`
#[spec(ensures: |ret| ret.as_ref().map_or_else(
    |refusal| matches!(*refusal, CheckRefusal::ForgedScope { node: found, .. } if found == node),
    |&()| carried == rebuilt))]
#[cold]
fn forged(
    node: NodeAddress,
    carried: NodeScope<'_>,
    rebuilt: NodeScope<'_>,
) -> Result<(), CheckRefusal>
{
    space(
        node,
        BindingSpace::Producers,
        carried.producers(),
        rebuilt.producers(),
    )?;
    space(
        node,
        BindingSpace::Covariables,
        carried.covariables(),
        rebuilt.covariables(),
    )
}

/// Hold one space's carried support to the one rebuilt for its node.
///
/// # Specification
/// - requires: `rebuilt` is the union of what the node names and its children's
///   carried supports in this space.
/// - ensures: success exactly when the two are equal.
/// - fails: [`CheckRefusal::ForgedScope`] with [`ScopeFault::Unselected`] when
///   `carried` misses an index `rebuilt` selects, otherwise
///   [`ScopeFault::Unused`].
/// - panics: none.
/// - intension: one comparison of two words while both are inline.
///
/// # Errors
/// As the failure clause states.
///
/// # Adequacy
/// - hypothesis: L3 — a forged support missing an index and one selecting an
///   extra one, in each space, are each refused by exactly their own name;
///   every support minting builds passes.
/// - witness: `check::tests::a_forged_scope_is_refused_by_name`
#[spec(ensures: |ret| ret.as_ref().map_or_else(
    |refusal| matches!(*refusal, CheckRefusal::ForgedScope { node: found, space: counted, .. } if found == node && counted == space),
    |&()| carried == rebuilt))]
#[cold]
fn space(
    node: NodeAddress,
    space: BindingSpace,
    carried: ThinningRef<'_>,
    rebuilt: ThinningRef<'_>,
) -> Result<(), CheckRefusal>
{
    if carried == rebuilt {
        return Ok(());
    }
    let unselected = [Zone::Intuitionistic, Zone::Linear]
        .into_iter()
        .any(|zone| {
            rebuilt
                .indices(zone)
                .any(|index| matches!(carried.rank(zone, index), Maybe::Absent(_)))
        });
    Err(CheckRefusal::ForgedScope {
        node,
        space,
        fault: if unselected {
            ScopeFault::Unselected
        }
        else {
            ScopeFault::Unused
        },
    })
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
