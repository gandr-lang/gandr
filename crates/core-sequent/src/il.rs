//! The command IL: producers, consumers and commands of the polarized
//! sequent calculus, resident in one append-only [`CommandArena`].
//!
//! A command `⟨p |ε c⟩` cuts a producer against a consumer at a polarity.
//! Producers are variables, constants, literals, constructor applications
//! `K(p̄; c̄)`, thunks `{force(α) ⇒ s}`, copattern objects `cocase {…}` and
//! context captures `μα. s`; consumers are covariables, value binders
//! `μ̃x. s`, destructor frames `D(p̄; c̄)`, pattern matches `case {…}` and the
//! terminal `★`. The heads a constructor or destructor carries are a closed
//! vocabulary over the core language — [`ConstructorTag`] and
//! [`DestructorTag`] — and each declares its own producer and consumer arity.
//!
//! # Names are indices
//!
//! A producer variable is the core's `(zone, de Bruijn index)` pair, counting
//! the IL's producer binders outward, and a covariable is a
//! [`CovariableIndex`] counting covariable binders outward. Producer and
//! covariable binders are separate index spaces, so a binder of one kind does
//! not shift indices of the other. Nothing mints a name: α-equivalence is
//! syntactic identity, and two equal inputs to a translation build identical
//! nodes.
//!
//! The binders: `μ̃x. s` binds one producer variable; `μα. s` and a thunk's
//! body bind one covariable; a pattern arm binds its constructor's producer
//! fields, left to right, so the last field is index `0`; a copattern arm binds
//! its destructor's producer arguments the same way and its consumer arguments
//! as covariables, the last one index `0`.
//!
//! # Children before parents
//!
//! A node is minted only over children the arena already holds, so every child
//! address is below the moment its parent was minted and the arena is acyclic
//! by construction. [`CommandArena::watermark`] and
//! [`CommandArena::truncate_to`] drop exactly the nodes minted after a mark,
//! which is how a refused multi-node build leaves the arena as it found it.

use alloc::boxed::Box;
use alloc::vec::Vec;
use core::fmt;

use gandr_core_term::Zone;
use gandr_kernel_strata::Level;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Side;
use gandr_theory_cell_complexes::Polarity;

use crate::boundary::ConsumerArity;
use crate::boundary::NodeCount;
use crate::boundary::ProducerArity;
use crate::boundary::address_wrapper;
use crate::boundary::index_wrapper;

address_wrapper! {
    /// The address of a [`ProducerNode`] in a [`CommandArena`].
    pub struct ProducerId;
}

address_wrapper! {
    /// The address of a [`ConsumerNode`] in a [`CommandArena`].
    pub struct ConsumerId;
}

address_wrapper! {
    /// The address of a [`CommandNode`] in a [`CommandArena`].
    pub struct CommandId;
}

index_wrapper! {
    /// A bound covariable, as a de Bruijn index counting covariable binders
    /// outward: `0` is the nearest enclosing `μα`, thunk body or copattern
    /// arm's consumer argument.
    pub struct CovariableIndex;
}

/// A constructor head `K` of a positive type.
///
/// The vocabulary is the core language's positive introductions: the unit,
/// the pair, the two injections and the explicit universe lift. Each head
/// declares its arity; the typed-IL check and the machine read the
/// declaration rather than a constant.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum ConstructorTag
{
    /// The unit `()`, of no fields.
    Unit,
    /// The pair `(p₁, p₂)`.
    Pair,
    /// A sum injection on the given side, of one field.
    Injection(Side),
    /// An explicit lift to the target level, of one field.
    Lift(Level),
}

impl ConstructorTag
{
    /// The number of producer fields the head declares.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `0` for the unit, `2` for the pair, `1` for an injection and
    ///   a lift.
    /// - provides: the one arity table a constructor node is held to.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every head is pinned to its exact count.
    /// - witness: `il::tests::tag_arities_are_stable`
    #[inline]
    #[must_use]
    pub const fn producer_arity(&self) -> ProducerArity
    {
        match *self {
            | Self::Unit => ProducerArity::ZERO,
            | Self::Pair => ProducerArity::TWO,
            | Self::Injection(_) | Self::Lift(_) => ProducerArity::ONE,
        }
    }

    /// The number of consumer children the head declares: none, for every
    /// constructor of the core's positive types.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `0` for every head.
    /// - provides: the consumer half of the arity table.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every head is pinned to its exact count.
    /// - witness: `il::tests::tag_consumer_arities_are_declared`
    #[inline]
    #[must_use]
    pub const fn consumer_arity(&self) -> ConsumerArity
    {
        match *self {
            | Self::Unit | Self::Pair | Self::Injection(_) | Self::Lift(_) => ConsumerArity::ZERO,
        }
    }
}

/// A destructor head `D`: an observation a consumer frame makes.
///
/// `Apply` observes a function, of the negative type `A → C`; `Force` observes
/// a thunk, of the positive type `U C`, and is answered by a thunk producer
/// rather than a copattern object.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum DestructorTag
{
    /// Application to one argument, returning to one continuation.
    Apply,
    /// Forcing a thunk, returning to one continuation.
    Force,
}

impl DestructorTag
{
    /// The number of producer arguments the head declares.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `1` for application, `0` for force.
    /// - provides: the one arity table a destructor node is held to.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every head is pinned to its exact count.
    /// - witness: `il::tests::tag_arities_are_stable`
    #[inline]
    #[must_use]
    pub const fn producer_arity(self) -> ProducerArity
    {
        match self {
            | Self::Apply => ProducerArity::ONE,
            | Self::Force => ProducerArity::ZERO,
        }
    }

    /// The number of consumer arguments the head declares: the one
    /// continuation the observation returns to.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `1` for every head.
    /// - provides: the consumer half of the arity table.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every head is pinned to its exact count.
    /// - witness: `il::tests::tag_consumer_arities_are_declared`
    #[inline]
    #[must_use]
    pub const fn consumer_arity(self) -> ConsumerArity
    {
        match self {
            | Self::Apply | Self::Force => ConsumerArity::ONE,
        }
    }

    /// The polarity of the type the head observes.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: negative for application, positive for force.
    /// - provides: the polarity the typed-IL check holds a destructor frame to.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — both heads are pinned.
    /// - witness: `il::tests::tag_arities_are_stable`
    #[inline]
    #[must_use]
    pub const fn polarity(self) -> Polarity
    {
        match self {
            | Self::Apply => Polarity::Negative,
            | Self::Force => Polarity::Positive,
        }
    }
}

/// One arm of a pattern match: a constructor head and the command run when a
/// value of that head arrives, under the head's producer fields.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct PatternArm
{
    /// The constructor head the arm answers.
    pub constructor: ConstructorTag,
    /// The arm's body, binding the head's fields, the last one innermost.
    pub body: CommandId,
}

/// One arm of a copattern object: a destructor head and the command run when
/// a frame of that head arrives, under the head's producer and consumer
/// arguments.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct CopatternArm
{
    /// The destructor head the arm answers.
    pub destructor: DestructorTag,
    /// The arm's body, binding the head's producer arguments as variables and
    /// its consumer arguments as covariables, the last of each innermost.
    pub body: CommandId,
}

/// A producer node: something a cut sends.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum ProducerNode
{
    /// A bound producer variable in a zone of the unified context.
    Variable
    {
        /// The zone whose binder stack the index counts in.
        zone: Zone,
        /// The de Bruijn index, counting producer binders outward.
        index: DeBruijnIndex,
    },
    /// A reference to a prior declaration.
    Constant(ConstantIndex),
    /// A base-type literal.
    Literal(Literal),
    /// A constructor application `K(p̄; c̄)`.
    Constructor
    {
        /// The head.
        tag: ConstructorTag,
        /// The producer fields, left to right.
        producers: Box<[ProducerId]>,
        /// The consumer fields, left to right.
        consumers: Box<[ConsumerId]>,
    },
    /// A thunk `{force(α) ⇒ s}`: a suspended command awaiting the continuation
    /// a force supplies.
    Thunk
    {
        /// The suspended command, binding one covariable.
        body: CommandId,
    },
    /// A copattern object `cocase {D(x̄; ᾱ) ⇒ s, …}` of a negative type.
    Cocase
    {
        /// The arms, one per destructor head the object answers.
        arms: Box<[CopatternArm]>,
    },
    /// A context capture `μα. s`.
    Mu
    {
        /// The command, binding one covariable.
        body: CommandId,
    },
}

/// A consumer node: something a cut sends to.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum ConsumerNode
{
    /// A bound covariable.
    Covariable(CovariableIndex),
    /// A value binder `μ̃x. s`.
    MuTilde
    {
        /// The command, binding one producer variable.
        body: CommandId,
    },
    /// A destructor frame `D(p̄; c̄)`.
    Destructor
    {
        /// The head.
        tag: DestructorTag,
        /// The producer arguments, left to right.
        producers: Box<[ProducerId]>,
        /// The consumer arguments, left to right.
        consumers: Box<[ConsumerId]>,
    },
    /// A pattern match `case {K(x̄) ⇒ s, …}` of a positive type.
    Case
    {
        /// The arms, one per constructor head the match answers.
        arms: Box<[PatternArm]>,
    },
    /// The terminal consumer `★`: the run's answer is what reaches it.
    Top,
}

/// A command node.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum CommandNode
{
    /// A cut `⟨p |ε c⟩`.
    Cut
    {
        /// The cut's polarity `ε`.
        polarity: Polarity,
        /// The producer sent.
        producer: ProducerId,
        /// The consumer it is sent to.
        consumer: ConsumerId,
    },
}

/// The three node families of the arena.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum NodeFamily
{
    /// The producer family.
    Producer,
    /// The consumer family.
    Consumer,
    /// The command family.
    Command,
}

/// Why the arena refused to mint a node.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum MintRefusal
{
    /// A producer child names no producer the arena holds.
    DanglingProducer(ProducerId),
    /// A consumer child names no consumer the arena holds.
    DanglingConsumer(ConsumerId),
    /// A command child names no command the arena holds.
    DanglingCommand(CommandId),
    /// The family has reached its address ceiling.
    FamilyFull(NodeFamily),
}

impl fmt::Display for MintRefusal
{
    /// Names the child that resolved to nothing, or the full family.
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
            | Self::DanglingProducer(id) => write!(f, "producer {id} is not in the arena"),
            | Self::DanglingConsumer(id) => write!(f, "consumer {id} is not in the arena"),
            | Self::DanglingCommand(id) => write!(f, "command {id} is not in the arena"),
            | Self::FamilyFull(family) => {
                let name = match family {
                    | NodeFamily::Producer => "producer",
                    | NodeFamily::Consumer => "consumer",
                    | NodeFamily::Command => "command",
                };
                write!(f, "the {name} family is full")
            },
        }
    }
}

impl core::error::Error for MintRefusal
{
}

/// A snapshot of the three family lengths.
///
/// Restoring an arena to a watermark drops exactly the nodes minted after it.
/// The default is the empty arena's watermark.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SequentWatermark
{
    /// The producer family length.
    producers: NodeCount,
    /// The consumer family length.
    consumers: NodeCount,
    /// The command family length.
    commands: NodeCount,
}

/// The append-only arena owning every IL node of one translation or run.
///
/// The three families are parallel append-only vectors and a node's children
/// are addresses into the same arena, so cloning or dropping an arena is a
/// flat vector operation on any term depth.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct CommandArena
{
    /// The producer nodes, in minting order.
    producers: Vec<ProducerNode>,
    /// The consumer nodes, in minting order.
    consumers: Vec<ConsumerNode>,
    /// The command nodes, in minting order.
    commands: Vec<CommandNode>,
}

impl CommandArena
{
    /// An empty arena.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new() -> Self
    {
        Self::default()
    }

    /// The current watermark: the three family lengths.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn watermark(&self) -> SequentWatermark
    {
        SequentWatermark {
            producers: NodeCount::from(self.producers.len()),
            consumers: NodeCount::from(self.consumers.len()),
            commands: NodeCount::from(self.commands.len()),
        }
    }

    /// Truncate every family back to `watermark`, dropping later nodes.
    ///
    /// # Specification
    /// - requires: `watermark` was taken from this arena; no address minted
    ///   after it is retained by the caller.
    /// - ensures: each family holds exactly the lesser of its watermark length
    ///   and its length on entry, so a mark above the current length leaves
    ///   that family as it was. Every node kept was minted before the mark and
    ///   so names only kept children: truncation never leaves a dangling child
    ///   inside the arena.
    /// - provides: the rollback every fallible multi-node build takes on
    ///   refusal.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a mark below the current lengths and a lookup of a
    ///   dropped address, asserted absent, separate the truncation from a
    ///   no-op.
    /// - witness: `il::tests::truncation_drops_exactly_the_later_nodes`
    #[inline]
    pub fn truncate_to(
        &mut self,
        watermark: SequentWatermark,
    )
    {
        self.producers.truncate(usize::from(watermark.producers));
        self.consumers.truncate(usize::from(watermark.consumers));
        self.commands.truncate(usize::from(watermark.commands));
    }

    /// Resolve a producer address, or `None` when it dangles.
    ///
    /// # Specification
    /// - requires: nothing; a dangling address is admissible.
    /// - ensures: `Some(node)` exactly when the arena holds the address.
    /// - provides: the read side of the producer family; absence is the one
    ///   reason, a dangling address.
    /// - fails: `None` on a dangling address.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub fn producer(
        &self,
        id: ProducerId,
    ) -> Option<&ProducerNode>
    {
        id.read_in(&self.producers)
    }

    /// Resolve a consumer address, or `None` when it dangles.
    ///
    /// # Specification
    /// - requires: nothing; a dangling address is admissible.
    /// - ensures: `Some(node)` exactly when the arena holds the address.
    /// - provides: the read side of the consumer family.
    /// - fails: `None` on a dangling address.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub fn consumer(
        &self,
        id: ConsumerId,
    ) -> Option<&ConsumerNode>
    {
        id.read_in(&self.consumers)
    }

    /// Resolve a command address, or `None` when it dangles.
    ///
    /// # Specification
    /// - requires: nothing; a dangling address is admissible.
    /// - ensures: `Some(node)` exactly when the arena holds the address.
    /// - provides: the read side of the command family.
    /// - fails: `None` on a dangling address.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub fn command(
        &self,
        id: CommandId,
    ) -> Option<&CommandNode>
    {
        id.read_in(&self.commands)
    }

    /// The number of producer nodes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn producer_count(&self) -> NodeCount
    {
        NodeCount::from(self.producers.len())
    }

    /// The number of consumer nodes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn consumer_count(&self) -> NodeCount
    {
        NodeCount::from(self.consumers.len())
    }

    /// The number of command nodes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn command_count(&self) -> NodeCount
    {
        NodeCount::from(self.commands.len())
    }

    /// Mint a producer node over children the arena holds.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the node is appended and its fresh address
    ///   returned; every child it names resolves.
    /// - provides: the one append point of the producer family.
    /// - fails: [`MintRefusal::DanglingProducer`],
    ///   [`MintRefusal::DanglingConsumer`] or [`MintRefusal::DanglingCommand`]
    ///   naming the first child that does not resolve, and
    ///   [`MintRefusal::FamilyFull`] at the address ceiling; the arena is then
    ///   unchanged.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a node over resolving children and a node over a
    ///   dangling child separate the two outcomes, the refusal asserted by
    ///   variant and the population asserted unchanged.
    /// - witness: `il::tests::arena_allocates_and_reads_back`
    /// - witness: `il::tests::minting_refuses_a_dangling_child`
    #[inline]
    pub fn mint_producer(
        &mut self,
        node: ProducerNode,
    ) -> Result<ProducerId, MintRefusal>
    {
        self.producer_children_resolve(&node)?;
        let id = ProducerId::next_in(&self.producers)
            .ok_or(MintRefusal::FamilyFull(NodeFamily::Producer))?;
        self.producers.push(node);
        Ok(id)
    }

    /// Mint a consumer node over children the arena holds.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the node is appended and its fresh address
    ///   returned; every child it names resolves.
    /// - provides: the one append point of the consumer family.
    /// - fails: as [`Self::mint_producer`]; the arena is then unchanged.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::mint_producer`].
    /// - witness: `il::tests::arena_allocates_and_reads_back`
    /// - witness: `il::tests::minting_refuses_a_dangling_child`
    #[inline]
    pub fn mint_consumer(
        &mut self,
        node: ConsumerNode,
    ) -> Result<ConsumerId, MintRefusal>
    {
        self.consumer_children_resolve(&node)?;
        let id = ConsumerId::next_in(&self.consumers)
            .ok_or(MintRefusal::FamilyFull(NodeFamily::Consumer))?;
        self.consumers.push(node);
        Ok(id)
    }

    /// Mint a command node over children the arena holds.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the node is appended and its fresh address
    ///   returned; its producer and consumer resolve.
    /// - provides: the one append point of the command family.
    /// - fails: as [`Self::mint_producer`]; the arena is then unchanged.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::mint_producer`].
    /// - witness: `il::tests::arena_allocates_and_reads_back`
    /// - witness: `il::tests::minting_refuses_a_dangling_child`
    #[inline]
    pub fn mint_command(
        &mut self,
        node: CommandNode,
    ) -> Result<CommandId, MintRefusal>
    {
        let CommandNode::Cut {
            producer, consumer, ..
        } = node;
        self.producer_resolves(producer)?;
        self.consumer_resolves(consumer)?;
        let id = CommandId::next_in(&self.commands)
            .ok_or(MintRefusal::FamilyFull(NodeFamily::Command))?;
        self.commands.push(node);
        Ok(id)
    }

    /// Mint the cut `⟨producer |polarity consumer⟩`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`Self::mint_command`] over [`CommandNode::Cut`].
    /// - provides: the shorthand every translation mints its cuts through.
    /// - fails: as [`Self::mint_command`].
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    #[inline]
    pub fn mint_cut(
        &mut self,
        polarity: Polarity,
        producer: ProducerId,
        consumer: ConsumerId,
    ) -> Result<CommandId, MintRefusal>
    {
        self.mint_command(CommandNode::Cut {
            polarity,
            producer,
            consumer,
        })
    }

    /// Refuse a producer address the arena does not hold.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Ok(())` exactly when `id` resolves.
    /// - provides: the per-child check minting reads.
    /// - fails: [`MintRefusal::DanglingProducer`] naming `id`.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    fn producer_resolves(
        &self,
        id: ProducerId,
    ) -> Result<(), MintRefusal>
    {
        self.producer(id)
            .map(|_| ())
            .ok_or(MintRefusal::DanglingProducer(id))
    }

    /// Refuse a consumer address the arena does not hold.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Ok(())` exactly when `id` resolves.
    /// - provides: the per-child check minting reads.
    /// - fails: [`MintRefusal::DanglingConsumer`] naming `id`.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    fn consumer_resolves(
        &self,
        id: ConsumerId,
    ) -> Result<(), MintRefusal>
    {
        self.consumer(id)
            .map(|_| ())
            .ok_or(MintRefusal::DanglingConsumer(id))
    }

    /// Refuse a command address the arena does not hold.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Ok(())` exactly when `id` resolves.
    /// - provides: the per-child check minting reads.
    /// - fails: [`MintRefusal::DanglingCommand`] naming `id`.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    fn command_resolves(
        &self,
        id: CommandId,
    ) -> Result<(), MintRefusal>
    {
        self.command(id)
            .map(|_| ())
            .ok_or(MintRefusal::DanglingCommand(id))
    }

    /// Refuse a producer node naming a child the arena does not hold.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Ok(())` exactly when every child of `node` resolves.
    /// - provides: the reference integrity minting a producer rests on.
    /// - fails: the first dangling child, in field order.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    fn producer_children_resolve(
        &self,
        node: &ProducerNode,
    ) -> Result<(), MintRefusal>
    {
        match *node {
            | ProducerNode::Variable { .. }
            | ProducerNode::Constant(_)
            | ProducerNode::Literal(_) => Ok(()),
            | ProducerNode::Constructor {
                ref producers,
                ref consumers,
                ..
            } => self.children_resolve(producers, consumers),
            | ProducerNode::Thunk { body } | ProducerNode::Mu { body } => {
                self.command_resolves(body)
            },
            | ProducerNode::Cocase { ref arms } => {
                for arm in arms {
                    self.command_resolves(arm.body)?;
                }
                Ok(())
            },
        }
    }

    /// Refuse a consumer node naming a child the arena does not hold.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Ok(())` exactly when every child of `node` resolves.
    /// - provides: the reference integrity minting a consumer rests on.
    /// - fails: the first dangling child, in field order.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    fn consumer_children_resolve(
        &self,
        node: &ConsumerNode,
    ) -> Result<(), MintRefusal>
    {
        match *node {
            | ConsumerNode::Covariable(_) | ConsumerNode::Top => Ok(()),
            | ConsumerNode::MuTilde { body } => self.command_resolves(body),
            | ConsumerNode::Destructor {
                ref producers,
                ref consumers,
                ..
            } => self.children_resolve(producers, consumers),
            | ConsumerNode::Case { ref arms } => {
                for arm in arms {
                    self.command_resolves(arm.body)?;
                }
                Ok(())
            },
        }
    }

    /// Refuse a child list naming an address the arena does not hold.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Ok(())` exactly when every listed address resolves.
    /// - provides: the shared check of a constructor's and a destructor's
    ///   children.
    /// - fails: the first dangling child, producers before consumers.
    /// - panics: none.
    ///
    /// # Errors
    /// As the failure clause states.
    fn children_resolve(
        &self,
        producers: &[ProducerId],
        consumers: &[ConsumerId],
    ) -> Result<(), MintRefusal>
    {
        for &producer in producers {
            self.producer_resolves(producer)?;
        }
        for &consumer in consumers {
            self.consumer_resolves(consumer)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;

    use gandr_kernel_term::IntegerLiteral;
    use gandr_kernel_term::Magnitude;
    use gandr_kernel_term::Sign;

    use super::*;

    /// The decimal digits a test literal is spelled with.
    #[repr(transparent)]
    #[derive(Clone, Copy, Debug)]
    struct Digits(&'static str);

    /// The non-negative integer literal spelled by `digits`.
    ///
    /// # Specification
    /// trivial.
    fn integer(digits: Digits) -> Literal
    {
        Literal::Integer(IntegerLiteral::new(
            Sign::NonNegative,
            Magnitude::from_decimal_text(String::from(digits.0)).expect("decimal digits"),
        ))
    }

    /// Every head's producer arity, and each destructor's polarity, is pinned:
    /// a change to the table is a change to what the check and the machine
    /// accept.
    #[test]
    fn tag_arities_are_stable()
    {
        let level = Level::zero();
        let cases = [
            (ConstructorTag::Unit, 0_usize),
            (ConstructorTag::Pair, 2_usize),
            (ConstructorTag::Injection(Side::Left), 1_usize),
            (ConstructorTag::Injection(Side::Right), 1_usize),
            (ConstructorTag::Lift(level), 1_usize),
        ];
        for (tag, arity) in cases {
            assert_eq!(
                ProducerArity::from(arity),
                tag.producer_arity(),
                "{tag:?} declares {arity} fields"
            );
        }
        assert_eq!(
            ProducerArity::ONE,
            DestructorTag::Apply.producer_arity(),
            "apply takes one argument"
        );
        assert_eq!(
            ProducerArity::ZERO,
            DestructorTag::Force.producer_arity(),
            "force takes none"
        );
        assert_eq!(
            Polarity::Negative,
            DestructorTag::Apply.polarity(),
            "a function is negative"
        );
        assert_eq!(
            Polarity::Positive,
            DestructorTag::Force.polarity(),
            "a thunk is positive"
        );
    }

    /// Every head declares its consumer arity: no constructor of the core's
    /// positive types carries a consumer, and every destructor returns to
    /// exactly one continuation.
    #[test]
    fn tag_consumer_arities_are_declared()
    {
        for tag in [
            ConstructorTag::Unit,
            ConstructorTag::Pair,
            ConstructorTag::Injection(Side::Left),
            ConstructorTag::Lift(Level::zero()),
        ] {
            assert_eq!(
                ConsumerArity::ZERO,
                tag.consumer_arity(),
                "{tag:?} carries no consumer"
            );
        }
        for tag in [DestructorTag::Apply, DestructorTag::Force] {
            assert_eq!(
                ConsumerArity::ONE,
                tag.consumer_arity(),
                "{tag:?} returns to one continuation"
            );
        }
    }

    /// A minted node reads back as itself, and each family counts its own
    /// nodes.
    #[test]
    fn arena_allocates_and_reads_back()
    {
        let mut arena = CommandArena::new();
        let literal = ProducerNode::Literal(integer(Digits("7")));
        let producer = arena.mint_producer(literal.clone()).expect("a leaf mints");
        let consumer = arena
            .mint_consumer(ConsumerNode::Top)
            .expect("a leaf mints");
        let command = arena
            .mint_cut(Polarity::Positive, producer, consumer)
            .expect("both children resolve");
        assert_eq!(
            Some(&literal),
            arena.producer(producer),
            "the producer reads back"
        );
        assert_eq!(
            Some(&ConsumerNode::Top),
            arena.consumer(consumer),
            "the consumer reads back"
        );
        assert_eq!(
            Some(&CommandNode::Cut {
                polarity: Polarity::Positive,
                producer,
                consumer,
            }),
            arena.command(command),
            "the cut reads back"
        );
        assert_eq!(
            (
                NodeCount::from(1_usize),
                NodeCount::from(1_usize),
                NodeCount::from(1_usize)
            ),
            (
                arena.producer_count(),
                arena.consumer_count(),
                arena.command_count()
            ),
            "one node per family"
        );
    }

    /// A node over a child the arena does not hold is refused by the child's
    /// family and address, and the arena is unchanged.
    #[test]
    fn minting_refuses_a_dangling_child()
    {
        let mut arena = CommandArena::new();
        let top = arena
            .mint_consumer(ConsumerNode::Top)
            .expect("a leaf mints");
        let entry = arena.watermark();
        let phantom = ProducerId::from(3_u32);
        assert_eq!(
            Err(MintRefusal::DanglingProducer(phantom)),
            arena.mint_cut(Polarity::Positive, phantom, top),
            "the producer child dangles"
        );
        assert_eq!(
            Err(MintRefusal::DanglingCommand(CommandId::from(0_u32))),
            arena.mint_producer(ProducerNode::Mu {
                body: CommandId::from(0_u32),
            }),
            "the command child dangles"
        );
        assert_eq!(
            Err(MintRefusal::DanglingConsumer(ConsumerId::from(5_u32))),
            arena.mint_consumer(ConsumerNode::Destructor {
                tag: DestructorTag::Force,
                producers: Box::from([]),
                consumers: Box::from([ConsumerId::from(5_u32)]),
            }),
            "the consumer child dangles"
        );
        assert_eq!(entry, arena.watermark(), "a refused mint appends nothing");
    }

    /// Truncation drops exactly the nodes minted after the mark: a dropped
    /// address no longer resolves, and a kept one still does.
    #[test]
    fn truncation_drops_exactly_the_later_nodes()
    {
        let mut arena = CommandArena::new();
        let kept = arena
            .mint_consumer(ConsumerNode::Top)
            .expect("a leaf mints");
        let mark = arena.watermark();
        let unit = arena
            .mint_producer(ProducerNode::Constructor {
                tag: ConstructorTag::Unit,
                producers: Box::from([]),
                consumers: Box::from([]),
            })
            .expect("a leaf mints");
        let cut = arena
            .mint_cut(Polarity::Positive, unit, kept)
            .expect("children resolve");
        arena.truncate_to(mark);
        assert_eq!(mark, arena.watermark(), "the arena is back at its mark");
        assert_eq!(None, arena.producer(unit), "the later producer is dropped");
        assert_eq!(None, arena.command(cut), "the later command is dropped");
        assert_eq!(
            Some(&ConsumerNode::Top),
            arena.consumer(kept),
            "the earlier node is kept"
        );
    }
}
