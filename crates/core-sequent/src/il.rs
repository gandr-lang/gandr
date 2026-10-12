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
//!
//! # Covariables are indices
//!
//! A covariable is a `CovariableIndex` counting covariable binders outward, in
//! an index space separate from the producer variables' `(zone,
//! DeBruijnIndex)`. A `μα`, a thunk's body and a copattern arm's consumer
//! arguments bind covariables; a `μ̃x`, a pattern arm's fields and a copattern
//! arm's producer arguments bind producer variables. Nothing mints a name:
//! α-equivalent IL is identical IL, a translation needs no counter threaded
//! through it, and two runs over equal input build identical arenas. The
//! producer index space is the core's own, so a core variable crosses into the
//! IL unchanged.
//!
//! The alternatives were named covariables drawn from a fresh-name supply,
//! every translation threading a counter and every comparison working modulo
//! renaming, and a counter newtype standing in for a name, which keeps the
//! supply and only types it. The choice reverses if a consumer of the IL needs
//! to address a covariable by identity across terms, which no reader of a
//! command does.
//!
//! # Children before parents
//!
//! Every `mint_*` call checks that each child it is given resolves in the arena
//! before appending, so each node's children were minted strictly before it,
//! across all three families, and the arena is acyclic by construction. A
//! `SequentWatermark` records the three family lengths; truncating to it keeps
//! exactly the nodes minted before it, and since those name only earlier nodes,
//! truncation never leaves a dangling child inside the arena. A build that
//! mints several nodes and then refuses truncates to the mark it took on entry,
//! so a refusal leaves the arena as it found it.
//!
//! The alternatives were unchecked minting, which admits a forward reference
//! and with it a cycle every walk would then need a depth limit against, and a
//! staging buffer committed at the end of a build, which copies every node
//! twice. The choice reverses if a measured build shows the per-child check
//! dominating minting.

use alloc::boxed::Box;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_core_term::Zone;
use gandr_kernel_strata::Level;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Summand;
use gandr_theory_cell_complexes::Polarity;

use crate::boundary::ConsumerArity;
use crate::boundary::FamilyAddress as _;
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
/// The vocabulary is the core language's positive introductions: a tuple of
/// any arity (the unit its empty case), an injection into a summand by
/// position, the explicit universe lift and a nominal datatype's
/// constructors. Each head declares its arity; the typed-IL check
/// and the machine read the declaration rather than a constant.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum ConstructorTag
{
    /// The tuple `(p₁, …, pₙ)` of this many fields; the unit `()` is the
    /// tuple of none.
    Tuple(ProducerArity),
    /// The empty native list.
    ListNil,
    /// A native list cell with head and tail fields.
    ListCons,
    /// A sum injection into the summand at this position, of one field.
    Injection(Summand),
    /// An explicit lift to the target level, of one field.
    Lift(Level),
    /// A nominal datatype's constructor, by its ordinal in the declaration,
    /// with the number of fields it carries. The datatype itself is a type,
    /// which the IL does not carry.
    Data
    {
        /// The constructor's ordinal in its declaration.
        tag: gandr_kernel_term::ConstructorTag,
        /// The number of fields the constructor carries.
        arity: ProducerArity,
    },
}

impl ConstructorTag
{
    /// The number of producer fields the head declares.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a tuple's and a datatype constructor's own field count, `0`
    ///   for the empty list, `2` for a list cell, `1` for an injection and a
    ///   lift.
    /// - provides: the one arity table a constructor node is held to.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — all constructor and destructor heads are observed by
    ///   exact arity and polarity. Replaced counts, swapped heads and polarity
    ///   inversions are distinguished; level payloads do not affect arity and
    ///   the witness uses level zero.
    /// - witness: `il::tests::tag_arities_are_stable`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| match *self {
        | Self::ListNil => matches!(ret, ProducerArity::ZERO),
        | Self::ListCons => matches!(ret, ProducerArity::TWO),
        | Self::Injection(_) | Self::Lift(_) => matches!(ret, ProducerArity::ONE),
        | Self::Tuple(arity) | Self::Data { arity, .. } => ret == arity,
    })]
    pub fn producer_arity(&self) -> ProducerArity
    {
        match *self {
            | Self::ListNil => ProducerArity::ZERO,
            | Self::ListCons => ProducerArity::TWO,
            | Self::Injection(_) | Self::Lift(_) => ProducerArity::ONE,
            | Self::Tuple(arity) | Self::Data { arity, .. } => arity,
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
    /// - hypothesis: L3 — all constructor and destructor heads are observed by
    ///   exact arity and polarity. Replaced counts, swapped heads and polarity
    ///   inversions are distinguished; level payloads do not affect arity and
    ///   the witness uses level zero.
    /// - witness: `il::tests::tag_consumer_arities_are_declared`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| matches!(ret, ConsumerArity::ZERO))]
    pub const fn consumer_arity(&self) -> ConsumerArity
    {
        match *self {
            | Self::Tuple(_)
            | Self::ListNil
            | Self::ListCons
            | Self::Injection(_)
            | Self::Lift(_)
            | Self::Data { .. } => ConsumerArity::ZERO,
        }
    }
}

/// A destructor head `D`: an observation a consumer frame makes.
///
/// `Apply` observes a function, of the negative type `A → C`; `Force` observes
/// a thunk, of the positive type `U C`, and is answered by a thunk producer
/// rather than a copattern object.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum DestructorTag
{
    /// Application to one argument, returning to one continuation.
    Apply,
    /// Forcing a thunk, returning to one continuation.
    Force,
    /// Observe one component of a lazy computation pair.
    Project(gandr_kernel_term::Side),
}

impl Ord for DestructorTag
{
    /// Order observation labels without imposing an ordering on source sums.
    ///
    /// # Specification
    /// - ensures: distinct observations compare unequal; application precedes
    ///   force, followed by the left and right projections.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — accepting both projections and rejecting a duplicate
    ///   arm distinguishes observation-label collisions.
    /// - witness: `check::tests::control_scopes_are_local_to_each_body`
    #[inline]
    #[spec(ensures: |ret| (ret == core::cmp::Ordering::Equal) == (self == other))]
    fn cmp(
        &self,
        other: &Self,
    ) -> core::cmp::Ordering
    {
        let rank = |tag: &Self| match *tag {
            | Self::Apply => 0_u8,
            | Self::Force => 1,
            | Self::Project(gandr_kernel_term::Side::Left) => 2,
            | Self::Project(gandr_kernel_term::Side::Right) => 3,
        };
        rank(self).cmp(&rank(other))
    }
}

impl PartialOrd for DestructorTag
{
    /// Delegate partial comparison to the observation-label order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn partial_cmp(
        &self,
        other: &Self,
    ) -> Option<core::cmp::Ordering>
    {
        Some(self.cmp(other))
    }
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
    /// - hypothesis: L3 — all constructor and destructor heads are observed by
    ///   exact arity and polarity. Replaced counts, swapped heads and polarity
    ///   inversions are distinguished; level payloads do not affect arity and
    ///   the witness uses level zero.
    /// - witness: `il::tests::tag_arities_are_stable`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| matches!((self, ret),
        (Self::Apply, ProducerArity::ONE) | (Self::Force | Self::Project(_), ProducerArity::ZERO)
    ))]
    pub const fn producer_arity(self) -> ProducerArity
    {
        match self {
            | Self::Apply => ProducerArity::ONE,
            | Self::Force | Self::Project(_) => ProducerArity::ZERO,
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
    /// - hypothesis: L3 — all constructor and destructor heads are observed by
    ///   exact arity and polarity. Replaced counts, swapped heads and polarity
    ///   inversions are distinguished; level payloads do not affect arity and
    ///   the witness uses level zero.
    /// - witness: `il::tests::tag_consumer_arities_are_declared`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| matches!(ret, ConsumerArity::ONE))]
    pub const fn consumer_arity(self) -> ConsumerArity
    {
        match self {
            | Self::Apply | Self::Force | Self::Project(_) => ConsumerArity::ONE,
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
    /// - hypothesis: L3 — all constructor and destructor heads are observed by
    ///   exact arity and polarity. Replaced counts, swapped heads and polarity
    ///   inversions are distinguished; level payloads do not affect arity and
    ///   the witness uses level zero.
    /// - witness: `il::tests::tag_arities_are_stable`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| matches!((self, ret),
        (Self::Apply | Self::Project(_), Polarity::Negative) | (Self::Force, Polarity::Positive)
    ))]
    pub const fn polarity(self) -> Polarity
    {
        match self {
            | Self::Apply | Self::Project(_) => Polarity::Negative,
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
    /// A first-class stack in innermost-to-outermost observation order.
    /// Bind bodies introduce one value binder and one return covariable;
    /// neither binder scopes over a later frame.
    Reify(alloc::sync::Arc<[gandr_core_term::control::StackFrame<ProducerId, CommandId>]>),
    /// A saturated operation whose arguments are evaluated in source order.
    Primitive
    {
        /// The shared vocabulary row.
        primitive: gandr_core_term::primitive::Primitive,
        /// Value-producing operands.
        arguments: gandr_core_term::primitive::Arguments<ProducerId>,
    },
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
    /// A recursive thunk `fix{x; force(α) ⇒ s}`: a thunk whose suspended
    /// command binds the thunk itself as its innermost producer variable `x`,
    /// beside the continuation a force supplies. It is the image of a core
    /// fixpoint `fix x. M`.
    Fixpoint
    {
        /// The suspended command, binding one producer variable and one
        /// covariable.
        body: CommandId,
        /// The termination claim the core fixpoint carries.
        evidence: gandr_kernel_term::FixpointEvidence,
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
    /// A nominal match `datacase(t̄; c)`: the value it receives is a datatype's
    /// constructor `K_i(v̄)`, and the branch `t_i` — a thunk of a function over
    /// the constructor's fields — is forced against `apply(v̄; c)`. The match
    /// opens no binder, so its continuation `c` is any consumer.
    DataCase
    {
        /// One branch per constructor, in ordinal order.
        branches: Box<[ProducerId]>,
        /// The continuation each branch returns to.
        then: ConsumerId,
    },
    /// A pure native fold, retaining annotations for inverse focusing.
    ListFold
    {
        /// Element type in this arena's annotation arena.
        element: gandr_core_term::ValueTypeId,
        /// Fold result type in the ambient context.
        result: gandr_core_term::ValueTypeId,
        /// Empty branch, binding only its return covariable.
        on_nil: CommandId,
        /// Cell branch, binding head, folded result and return covariable.
        on_cons: CommandId,
        /// Where the complete fold returns.
        continuation: ConsumerId,
    },
    /// The terminal consumer `★`: the run's answer is what reaches it.
    Top,
}

/// A command node.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum CommandNode
{
    /// Request an operation against the live continuation.
    Perform
    {
        /// Inline interface types belong to this arena's annotation arena.
        signature: gandr_core_term::effect::EffectSig,
        /// The operation within that interface.
        operation: gandr_core_term::effect::OperationName,
        /// Its eager payload.
        payload: ProducerId,
        /// The continuation installed before propagation.
        continuation: ConsumerId,
    },
    /// Install a deep interface handler around a subject.
    Handle
    {
        /// The interface this delimiter handles.
        signature: gandr_core_term::effect::EffectSig,
        /// The subject, binding one return covariable.
        subject: CommandId,
        /// Return clause: one value binder and one return covariable.
        on_return: CommandId,
        /// Operation clauses: payload, resumption, then return covariable.
        clauses: alloc::sync::Arc<[gandr_core_term::control::EffectClause<CommandId>]>,
        /// The continuation outside the delimiter.
        continuation: ConsumerId,
    },
    /// Run a computation through a first-class stack.
    Resume
    {
        /// The stack value.
        stack: ProducerId,
        /// The fed computation, binding one return covariable.
        body: CommandId,
        /// Where the resumed stack delivers its answer.
        continuation: ConsumerId,
    },
    /// Install an answer delimiter.
    Reset
    {
        /// The body, binding one return covariable.
        body: CommandId,
        /// The continuation outside the delimiter.
        continuation: ConsumerId,
    },
    /// Capture to the nearest reachable reset.
    Shift
    {
        /// The body, binding the captured stack and one return covariable.
        body: CommandId,
        /// The local continuation captured before the body runs.
        continuation: ConsumerId,
    },
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
    /// A type annotation does not resolve in the annotation arena.
    DanglingAnnotation(gandr_core_term::ValueTypeId),
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
            | Self::DanglingAnnotation(_) => f.write_str("a List-fold annotation does not resolve"),
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
    /// The attached annotation graph's family lengths.
    annotations: gandr_core_term::ArenaWatermark,
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
    /// Portable type annotations; runtime transitions do not inspect them.
    annotations: gandr_core_term::CoreArena,
}

impl CommandArena
{
    /// Borrow the arena owning retained fold annotations.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn annotations(&self) -> &gandr_core_term::CoreArena
    {
        &self.annotations
    }

    /// Append annotations before minting a consumer which references them.
    ///
    /// Existing referenced annotations must not be truncated independently.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn annotations_mut(&mut self) -> &mut gandr_core_term::CoreArena
    {
        &mut self.annotations
    }

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
            annotations: self.annotations.watermark(),
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
    /// - hypothesis: L3 — distinct populations and two successive marks
    ///   distinguish a skipped family, an off-by-one truncation and growth to a
    ///   future mark. Reads of retained and dropped nodes observe both
    ///   preservation and removal; an empty mark closes the lower boundary.
    /// - witness: `il::tests::truncation_drops_exactly_the_later_nodes`
    /// - witness: `il::tests::truncation_keeps_future_marks_and_drops_each_family`
    #[inline]
    #[spec(
        captures: [entry = self.watermark()],
        ensures: self.producers.len() == usize::from(watermark.producers).min(usize::from(entry.producers))
            && self.consumers.len() == usize::from(watermark.consumers).min(usize::from(entry.consumers))
            && self.commands.len() == usize::from(watermark.commands).min(usize::from(entry.commands)),
    )]
    pub fn truncate_to(
        &mut self,
        watermark: SequentWatermark,
    )
    {
        self.producers.truncate(usize::from(watermark.producers));
        self.consumers.truncate(usize::from(watermark.consumers));
        self.commands.truncate(usize::from(watermark.commands));
        self.annotations.truncate_to(watermark.annotations);
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exact producer nodes at the first and last live
    ///   offsets, the first missing offset and truncation distinguish shifted
    ///   lookup, a wrong family and stale membership.
    /// - witness: `il::tests::lookup_boundaries_follow_each_family`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| match ret {
        | Some(node) => usize::try_from(u32::from(id)).ok()
            .and_then(|offset| self.producers.get(offset))
            .is_some_and(|held| core::ptr::eq(core::ptr::from_ref(held), core::ptr::from_ref(node))),
        | None => usize::try_from(u32::from(id))
            .map_or(true, |offset| offset >= self.producers.len()),
    })]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exact consumer nodes at the first and last live
    ///   offsets, the first missing offset and truncation distinguish shifted
    ///   lookup, a wrong family and stale membership.
    /// - witness: `il::tests::lookup_boundaries_follow_each_family`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| match ret {
        | Some(node) => usize::try_from(u32::from(id)).ok()
            .and_then(|offset| self.consumers.get(offset))
            .is_some_and(|held| core::ptr::eq(core::ptr::from_ref(held), core::ptr::from_ref(node))),
        | None => usize::try_from(u32::from(id))
            .map_or(true, |offset| offset >= self.consumers.len()),
    })]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exact command nodes at the first and last live
    ///   offsets, the first missing offset and truncation distinguish shifted
    ///   lookup, a wrong family and stale membership.
    /// - witness: `il::tests::lookup_boundaries_follow_each_family`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| match ret {
        | Some(node) => usize::try_from(u32::from(id)).ok()
            .and_then(|offset| self.commands.get(offset))
            .is_some_and(|held| core::ptr::eq(core::ptr::from_ref(held), core::ptr::from_ref(node))),
        | None => usize::try_from(u32::from(id))
            .map_or(true, |offset| offset >= self.commands.len()),
    })]
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
    /// - hypothesis: L3 — every node form is minted over live children and
    ///   refused at a dangling child, observing the exact refusal and unchanged
    ///   watermark. Multiple bad children distinguish field-order precedence.
    ///   The shared address helper covers the excluded ceiling using zero-sized
    ///   slices; the arena tests do not allocate a ceiling-sized node family.
    /// - witness: `il::tests::arena_allocates_and_reads_back`
    /// - witness: `il::tests::minting_refuses_a_dangling_child`
    /// - witness: `il::tests::every_node_form_checks_its_child_families`
    /// - witness: `il::tests::the_first_dangling_child_wins`
    /// - witness: `boundary::tests::addresses_refuse_exactly_at_the_u32_ceiling`
    #[inline]
    #[spec(
        captures: [entry = self.watermark()],
        ensures: |ret| match ret {
            | Ok(id) => usize::try_from(u32::from(id)) == Ok(usize::from(entry.producers))
                && usize::from(entry.producers).checked_add(1) == Some(self.producers.len())
                && self.consumer_count() == entry.consumers
                && self.command_count() == entry.commands,
            | Err(_) => self.watermark() == entry,
        },
    )]
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
    /// - hypothesis: L3 — live and dangling children of every node form
    ///   distinguish omitted validation, reordered failures and partial appends
    ///   by exact node, refusal and watermark. The shared helper witnesses the
    ///   address ceiling; a full-sized arena is outside the test domain.
    /// - witness: `il::tests::arena_allocates_and_reads_back`
    /// - witness: `il::tests::minting_refuses_a_dangling_child`
    /// - witness: `il::tests::every_node_form_checks_its_child_families`
    /// - witness: `il::tests::the_first_dangling_child_wins`
    /// - witness: `boundary::tests::addresses_refuse_exactly_at_the_u32_ceiling`
    #[inline]
    #[spec(
        captures: [entry = self.watermark()],
        ensures: |ret| match ret {
            | Ok(id) => usize::try_from(u32::from(id)) == Ok(usize::from(entry.consumers))
                && usize::from(entry.consumers).checked_add(1) == Some(self.consumers.len())
                && self.producer_count() == entry.producers
                && self.command_count() == entry.commands,
            | Err(_) => self.watermark() == entry,
        },
    )]
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
    /// - hypothesis: L3 — live and dangling children of every node form
    ///   distinguish omitted validation, reordered failures and partial appends
    ///   by exact node, refusal and watermark. The shared helper witnesses the
    ///   address ceiling; a full-sized arena is outside the test domain.
    /// - witness: `il::tests::arena_allocates_and_reads_back`
    /// - witness: `il::tests::minting_refuses_a_dangling_child`
    /// - witness: `il::tests::every_node_form_checks_its_child_families`
    /// - witness: `il::tests::the_first_dangling_child_wins`
    /// - witness: `boundary::tests::addresses_refuse_exactly_at_the_u32_ceiling`
    #[inline]
    #[spec(
        captures: [entry = self.watermark()],
        ensures: |ret| match ret {
            | Ok(id) => usize::try_from(u32::from(id)) == Ok(usize::from(entry.commands))
                && usize::from(entry.commands).checked_add(1) == Some(self.commands.len())
                && self.producer_count() == entry.producers
                && self.consumer_count() == entry.consumers,
            | Err(_) => self.watermark() == entry,
        },
    )]
    pub fn mint_command(
        &mut self,
        node: CommandNode,
    ) -> Result<CommandId, MintRefusal>
    {
        match node {
            | CommandNode::Cut {
                producer, consumer, ..
            } => {
                self.producer_resolves(producer)?;
                self.consumer_resolves(consumer)?;
            },
            | CommandNode::Perform {
                ref signature,
                payload,
                continuation,
                ..
            } => {
                self.signature_resolves(signature)?;
                self.producer_resolves(payload)?;
                self.consumer_resolves(continuation)?;
            },
            | CommandNode::Handle {
                ref signature,
                subject,
                on_return,
                ref clauses,
                continuation,
            } => {
                self.signature_resolves(signature)?;
                self.command_resolves(subject)?;
                self.command_resolves(on_return)?;
                for clause in clauses.iter() {
                    self.command_resolves(clause.body)?;
                }
                self.consumer_resolves(continuation)?;
            },
            | CommandNode::Resume {
                stack,
                body,
                continuation,
            } => {
                self.producer_resolves(stack)?;
                self.command_resolves(body)?;
                self.consumer_resolves(continuation)?;
            },
            | CommandNode::Reset { body, continuation }
            | CommandNode::Shift { body, continuation } => {
                self.command_resolves(body)?;
                self.consumer_resolves(continuation)?;
            },
        }
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — cuts with live and missing children observe polarity,
    ///   both endpoints and exact producer-before-consumer refusal. The
    ///   watermark distinguishes refusal from a partial append.
    /// - witness: `il::tests::arena_allocates_and_reads_back`
    /// - witness: `il::tests::the_first_dangling_child_wins`
    #[inline]
    #[spec(
        captures: [entry = self.watermark()],
        ensures: |ret| match ret {
            | Ok(id) => self.command(id) == Some(&CommandNode::Cut { polarity, producer, consumer }),
            | Err(_) => self.watermark() == entry,
        },
    )]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the exact last live and first missing producer
    ///   addresses distinguish wrong-family lookup and endpoint acceptance. The
    ///   refusal must retain the missing address.
    /// - witness: `il::tests::every_node_form_checks_its_child_families`
    /// - witness: `il::tests::the_first_dangling_child_wins`
    #[spec(ensures: |ret| match ret {
        | Ok(()) => self.producer(id).is_some(),
        | Err(error) => error == MintRefusal::DanglingProducer(id) && self.producer(id).is_none(),
    })]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the exact last live and first missing consumer
    ///   addresses distinguish wrong-family lookup and endpoint acceptance. The
    ///   refusal must retain the missing address.
    /// - witness: `il::tests::every_node_form_checks_its_child_families`
    /// - witness: `il::tests::the_first_dangling_child_wins`
    #[spec(ensures: |ret| match ret {
        | Ok(()) => self.consumer(id).is_some(),
        | Err(error) => error == MintRefusal::DanglingConsumer(id) && self.consumer(id).is_none(),
    })]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the exact last live and first missing command
    ///   addresses distinguish wrong-family lookup and endpoint acceptance. The
    ///   refusal must retain the missing address.
    /// - witness: `il::tests::every_node_form_checks_its_child_families`
    /// - witness: `il::tests::the_first_dangling_child_wins`
    #[spec(ensures: |ret| match ret {
        | Ok(()) => self.command(id).is_some(),
        | Err(error) => error == MintRefusal::DanglingCommand(id) && self.command(id).is_none(),
    })]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each producer form is supplied live children and one
    ///   dangling child per referenced family. Exact errors and multiple
    ///   missing children expose omitted arms and changed failure precedence.
    /// - witness: `il::tests::every_node_form_checks_its_child_families`
    /// - witness: `il::tests::the_first_dangling_child_wins`
    #[spec(ensures: |ref ret| ret.is_ok() == match *node {
        | ProducerNode::Reify(ref frames) => frames.iter().all(|frame| match *frame { gandr_core_term::control::StackFrame::Apply(value) => self.producer(value).is_some(), gandr_core_term::control::StackFrame::Bind(body) => self.command(body).is_some(), gandr_core_term::control::StackFrame::Project(_) => true }),
        | ProducerNode::Primitive { arguments, .. } => arguments.iter().all(|id| self.producer(*id).is_some()),
        | ProducerNode::Variable { .. } | ProducerNode::Constant(_) | ProducerNode::Literal(_) => true,
        | ProducerNode::Constructor { ref producers, ref consumers, .. } =>
            producers.iter().all(|id| self.producer(*id).is_some())
                && consumers.iter().all(|id| self.consumer(*id).is_some()),
        | ProducerNode::Thunk { body } | ProducerNode::Mu { body } | ProducerNode::Fixpoint { body, .. } => self.command(body).is_some(),
        | ProducerNode::Cocase { ref arms } => arms.iter().all(|arm| self.command(arm.body).is_some()),
    })]
    fn producer_children_resolve(
        &self,
        node: &ProducerNode,
    ) -> Result<(), MintRefusal>
    {
        match *node {
            | ProducerNode::Reify(ref frames) => {
                for frame in frames.iter() {
                    match *frame {
                        | gandr_core_term::control::StackFrame::Apply(value) => {
                            self.producer_resolves(value)?;
                        },
                        | gandr_core_term::control::StackFrame::Bind(body) => {
                            self.command_resolves(body)?;
                        },
                        | gandr_core_term::control::StackFrame::Project(_) => {},
                    }
                }
                Ok(())
            },
            | ProducerNode::Primitive { arguments, .. } => self.children_resolve(&arguments, &[]),
            | ProducerNode::Variable { .. }
            | ProducerNode::Constant(_)
            | ProducerNode::Literal(_) => Ok(()),
            | ProducerNode::Constructor {
                ref producers,
                ref consumers,
                ..
            } => self.children_resolve(producers, consumers),
            | ProducerNode::Thunk { body }
            | ProducerNode::Mu { body }
            | ProducerNode::Fixpoint { body, .. } => self.command_resolves(body),
            | ProducerNode::Cocase { ref arms } => {
                for arm in arms {
                    self.command_resolves(arm.body)?;
                }
                Ok(())
            },
        }
    }

    /// Check the interface's annotation edges before accepting a command.
    ///
    /// # Specification
    /// - ensures: success exactly when every payload and reply type resolves.
    /// - fails: the first dangling annotation in canonical operation order.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — imported host interfaces retain distinct payload and
    ///   reply types.
    /// - witness: `machine::tests::hand_built_effect_cases_agree`
    #[spec(ensures: |ret| ret.is_ok() == signature.types().all(|ty| self.annotations.value_type(ty).is_some()))]
    fn signature_resolves(
        &self,
        signature: &gandr_core_term::effect::EffectSig,
    ) -> Result<(), MintRefusal>
    {
        for ty in signature.types() {
            if self.annotations.value_type(ty).is_none() {
                return Err(MintRefusal::DanglingAnnotation(ty));
            }
        }
        Ok(())
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each consumer form is supplied live children and one
    ///   dangling child per referenced family. Exact errors and multiple
    ///   missing children expose omitted arms and changed failure precedence.
    /// - witness: `il::tests::every_node_form_checks_its_child_families`
    /// - witness: `il::tests::the_first_dangling_child_wins`
    #[spec(ensures: |ref ret| ret.is_ok() == match *node {
        | ConsumerNode::Covariable(_) | ConsumerNode::Top => true,
        | ConsumerNode::MuTilde { body } => self.command(body).is_some(),
        | ConsumerNode::Destructor { ref producers, ref consumers, .. } =>
            producers.iter().all(|id| self.producer(*id).is_some())
                && consumers.iter().all(|id| self.consumer(*id).is_some()),
        | ConsumerNode::Case { ref arms } => arms.iter().all(|arm| self.command(arm.body).is_some()),
        | ConsumerNode::DataCase { ref branches, then } =>
            branches.iter().all(|id| self.producer(*id).is_some()) && self.consumer(then).is_some(),
        | ConsumerNode::ListFold { element, result, on_nil, on_cons, continuation } => self.annotations.value_type(element).is_some() && self.annotations.value_type(result).is_some() && self.command(on_nil).is_some() && self.command(on_cons).is_some() && self.consumer(continuation).is_some(),
    })]
    fn consumer_children_resolve(
        &self,
        node: &ConsumerNode,
    ) -> Result<(), MintRefusal>
    {
        match *node {
            | ConsumerNode::Covariable(_) | ConsumerNode::Top => Ok(()),
            | ConsumerNode::ListFold {
                element,
                result,
                on_nil,
                on_cons,
                continuation,
            } => {
                for annotation in [element, result] {
                    if self.annotations.value_type(annotation).is_none() {
                        return Err(MintRefusal::DanglingAnnotation(annotation));
                    }
                }
                self.command_resolves(on_nil)?;
                self.command_resolves(on_cons)?;
                self.consumer_resolves(continuation)
            },
            | ConsumerNode::MuTilde { body } => self.command_resolves(body),
            | ConsumerNode::Destructor {
                ref producers,
                ref consumers,
                ..
            } => self.children_resolve(producers, consumers),
            | ConsumerNode::DataCase { ref branches, then } => {
                self.children_resolve(branches, core::slice::from_ref(&then))
            },
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty lists, each dangling family and several bad
    ///   addresses distinguish omitted validation, wrong payloads and failure
    ///   precedence. The observer is the exact first refusal.
    /// - witness: `il::tests::every_node_form_checks_its_child_families`
    /// - witness: `il::tests::the_first_dangling_child_wins`
    #[spec(ensures: |ref ret| *ret == producers.iter()
        .find(|id| self.producer(**id).is_none())
        .map(|id| MintRefusal::DanglingProducer(*id))
        .or_else(|| consumers.iter().find(|id| self.consumer(**id).is_none())
            .map(|id| MintRefusal::DanglingConsumer(*id)))
        .map_or(Ok(()), Err)
    )]
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
    use gandr_kernel_term::Side;
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
            (ConstructorTag::Tuple(ProducerArity::ZERO), 0_usize),
            (ConstructorTag::Tuple(ProducerArity::TWO), 2_usize),
            (ConstructorTag::Injection(Side::Left.into()), 1_usize),
            (ConstructorTag::Injection(Side::Right.into()), 1_usize),
            (ConstructorTag::Tuple(ProducerArity::from(3_usize)), 3_usize),
            (ConstructorTag::Injection(Summand::from(2_usize)), 1_usize),
            (ConstructorTag::Lift(level), 1_usize),
            (
                ConstructorTag::Data {
                    tag: gandr_kernel_term::ConstructorTag::from(1_usize),
                    arity: ProducerArity::from(3_usize),
                },
                3_usize,
            ),
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
            ConstructorTag::Tuple(ProducerArity::ZERO),
            ConstructorTag::Tuple(ProducerArity::TWO),
            ConstructorTag::Injection(Side::Left.into()),
            ConstructorTag::Injection(Side::Right.into()),
            ConstructorTag::Lift(Level::zero()),
            ConstructorTag::Data {
                tag: gandr_kernel_term::ConstructorTag::from(0_usize),
                arity: ProducerArity::TWO,
            },
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
        assert_eq!(
            Err(MintRefusal::DanglingCommand(CommandId::from(2_u32))),
            arena.mint_producer(ProducerNode::Fixpoint {
                body: CommandId::from(2_u32),
                evidence: gandr_kernel_term::FixpointEvidence::Partial,
            }),
            "the recursive thunk's body dangles"
        );
        assert_eq!(
            Err(MintRefusal::DanglingProducer(ProducerId::from(4_u32))),
            arena.mint_consumer(ConsumerNode::DataCase {
                branches: Box::from([ProducerId::from(4_u32)]),
                then: top,
            }),
            "a nominal match's branch dangles"
        );
        assert_eq!(
            Err(MintRefusal::DanglingConsumer(ConsumerId::from(6_u32))),
            arena.mint_consumer(ConsumerNode::DataCase {
                branches: Box::from([]),
                then: ConsumerId::from(6_u32),
            }),
            "a nominal match's continuation dangles"
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
                tag: ConstructorTag::Tuple(ProducerArity::ZERO),
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

    /// Each family's offsets select its own exact nodes, including empty and
    /// end boundaries.
    #[test]
    fn lookup_boundaries_follow_each_family()
    {
        let mut arena = CommandArena::new();
        assert_eq!(None, arena.producer(ProducerId::from(0_u32)));
        assert_eq!(None, arena.consumer(ConsumerId::from(0_u32)));
        assert_eq!(None, arena.command(CommandId::from(0_u32)));
        let first = arena
            .mint_producer(ProducerNode::Constant(0_usize.into()))
            .expect("leaf");
        let last = arena
            .mint_producer(ProducerNode::Constant(7_usize.into()))
            .expect("leaf");
        let top = arena.mint_consumer(ConsumerNode::Top).expect("leaf");
        let covariable = ConsumerNode::Covariable(CovariableIndex::from(3_u32));
        let back = arena.mint_consumer(covariable.clone()).expect("leaf");
        let first_cut = CommandNode::Cut {
            polarity: Polarity::Positive,
            producer: first,
            consumer: top,
        };
        let last_cut = CommandNode::Cut {
            polarity: Polarity::Negative,
            producer: last,
            consumer: back,
        };
        let before = arena
            .mint_command(first_cut.clone())
            .expect("live children");
        let after = arena.mint_command(last_cut.clone()).expect("live children");
        assert_eq!(
            Some(&ProducerNode::Constant(0_usize.into())),
            arena.producer(first)
        );
        assert_eq!(
            Some(&ProducerNode::Constant(7_usize.into())),
            arena.producer(last)
        );
        assert_eq!(Some(&ConsumerNode::Top), arena.consumer(top));
        assert_eq!(Some(&covariable), arena.consumer(back));
        assert_eq!(Some(&first_cut), arena.command(before));
        assert_eq!(Some(&last_cut), arena.command(after));
        assert_eq!(None, arena.producer(ProducerId::from(2_u32)));
        assert_eq!(None, arena.consumer(ConsumerId::from(2_u32)));
        assert_eq!(None, arena.command(CommandId::from(2_u32)));
    }

    /// Future marks never grow truncated families, and the empty mark clears
    /// all three.
    #[test]
    fn truncation_keeps_future_marks_and_drops_each_family()
    {
        let mut arena = CommandArena::new();
        let empty = arena.watermark();
        let kept = arena
            .mint_producer(ProducerNode::Constant(0_usize.into()))
            .expect("leaf");
        let top = arena.mint_consumer(ConsumerNode::Top).expect("leaf");
        let cut = arena
            .mint_cut(Polarity::Positive, kept, top)
            .expect("live children");
        let mark = arena.watermark();
        let later = arena
            .mint_producer(ProducerNode::Constant(1_usize.into()))
            .expect("leaf");
        let back = arena
            .mint_consumer(ConsumerNode::Covariable(CovariableIndex::from(0_u32)))
            .expect("leaf");
        let dropped = arena
            .mint_cut(Polarity::Negative, later, back)
            .expect("live children");
        arena
            .mint_producer(ProducerNode::Constant(2_usize.into()))
            .expect("leaf");
        let future = arena.watermark();
        arena.truncate_to(mark);
        assert_eq!(mark, arena.watermark());
        assert_eq!(None, arena.producer(later));
        assert_eq!(None, arena.consumer(back));
        assert_eq!(None, arena.command(dropped));
        arena.truncate_to(future);
        assert_eq!(mark, arena.watermark());
        assert_eq!(
            Some(&ProducerNode::Constant(0_usize.into())),
            arena.producer(kept)
        );
        assert_eq!(Some(&ConsumerNode::Top), arena.consumer(top));
        assert_eq!(
            Some(&CommandNode::Cut {
                polarity: Polarity::Positive,
                producer: kept,
                consumer: top
            }),
            arena.command(cut)
        );
        arena.truncate_to(empty);
        assert_eq!(empty, arena.watermark());
        assert_eq!(None, arena.producer(kept));
        assert_eq!(None, arena.consumer(top));
        assert_eq!(None, arena.command(cut));
    }

    /// Every node form checks its distinct child positions before appending.
    #[test]
    fn every_node_form_checks_its_child_families()
    {
        let mut arena = CommandArena::new();
        let leaf = arena
            .mint_producer(ProducerNode::Constant(0_usize.into()))
            .expect("leaf");
        let top = arena.mint_consumer(ConsumerNode::Top).expect("leaf");
        let body = arena
            .mint_cut(Polarity::Positive, leaf, top)
            .expect("live children");
        for node in [
            ProducerNode::Variable {
                zone: Zone::Intuitionistic,
                index: DeBruijnIndex::from(0_u32),
            },
            ProducerNode::Constant(1_usize.into()),
            ProducerNode::Literal(integer(Digits("17"))),
            ProducerNode::Constructor {
                tag: ConstructorTag::Tuple(ProducerArity::TWO),
                producers: Box::from([leaf]),
                consumers: Box::from([top]),
            },
            ProducerNode::Thunk { body },
            ProducerNode::Mu { body },
            ProducerNode::Cocase {
                arms: Box::from([CopatternArm {
                    destructor: DestructorTag::Apply,
                    body,
                }]),
            },
        ] {
            let id = arena
                .mint_producer(node.clone())
                .expect("all references live");
            assert_eq!(Some(&node), arena.producer(id));
        }
        for node in [
            ConsumerNode::Top,
            ConsumerNode::Covariable(CovariableIndex::from(4_u32)),
            ConsumerNode::MuTilde { body },
            ConsumerNode::Destructor {
                tag: DestructorTag::Apply,
                producers: Box::from([leaf]),
                consumers: Box::from([top]),
            },
            ConsumerNode::Case {
                arms: Box::from([PatternArm {
                    constructor: ConstructorTag::Tuple(ProducerArity::ZERO),
                    body,
                }]),
            },
        ] {
            let id = arena
                .mint_consumer(node.clone())
                .expect("all references live");
            assert_eq!(Some(&node), arena.consumer(id));
        }
        let missing = CommandId::from(1_u32);
        let entry = arena.watermark();
        for node in [
            ProducerNode::Thunk { body: missing },
            ProducerNode::Mu { body: missing },
            ProducerNode::Cocase {
                arms: Box::from([
                    CopatternArm {
                        destructor: DestructorTag::Apply,
                        body,
                    },
                    CopatternArm {
                        destructor: DestructorTag::Force,
                        body: missing,
                    },
                ]),
            },
        ] {
            assert_eq!(
                Err(MintRefusal::DanglingCommand(missing)),
                arena.mint_producer(node)
            );
            assert_eq!(entry, arena.watermark());
        }
        for node in [
            ConsumerNode::MuTilde { body: missing },
            ConsumerNode::Case {
                arms: Box::from([
                    PatternArm {
                        constructor: ConstructorTag::Tuple(ProducerArity::ZERO),
                        body,
                    },
                    PatternArm {
                        constructor: ConstructorTag::Tuple(ProducerArity::TWO),
                        body: missing,
                    },
                ]),
            },
        ] {
            assert_eq!(
                Err(MintRefusal::DanglingCommand(missing)),
                arena.mint_consumer(node)
            );
            assert_eq!(entry, arena.watermark());
        }
    }

    /// Missing producer fields precede consumer fields, and each list keeps
    /// field order.
    #[test]
    fn the_first_dangling_child_wins()
    {
        let mut arena = CommandArena::new();
        let leaf = arena
            .mint_producer(ProducerNode::Constant(0_usize.into()))
            .expect("leaf");
        let top = arena.mint_consumer(ConsumerNode::Top).expect("leaf");
        let missing_producer = ProducerId::from(1_u32);
        let missing_consumer = ConsumerId::from(1_u32);
        let entry = arena.watermark();
        for (producers, consumers, expected) in [
            (
                &[leaf, missing_producer, ProducerId::from(2_u32)][..],
                &[missing_consumer][..],
                MintRefusal::DanglingProducer(missing_producer),
            ),
            (
                &[leaf][..],
                &[top, missing_consumer, ConsumerId::from(2_u32)][..],
                MintRefusal::DanglingConsumer(missing_consumer),
            ),
        ] {
            assert_eq!(
                Err(expected),
                arena.mint_producer(ProducerNode::Constructor {
                    tag: ConstructorTag::Tuple(ProducerArity::TWO),
                    producers: Box::from(producers),
                    consumers: Box::from(consumers),
                })
            );
            assert_eq!(
                Err(expected),
                arena.mint_consumer(ConsumerNode::Destructor {
                    tag: DestructorTag::Apply,
                    producers: Box::from(producers),
                    consumers: Box::from(consumers),
                })
            );
            assert_eq!(entry, arena.watermark());
        }
        assert_eq!(
            Err(MintRefusal::DanglingProducer(missing_producer)),
            arena.mint_cut(Polarity::Positive, missing_producer, missing_consumer)
        );
        assert_eq!(
            Err(MintRefusal::DanglingConsumer(missing_consumer)),
            arena.mint_cut(Polarity::Negative, leaf, missing_consumer)
        );
        assert_eq!(entry, arena.watermark());
    }
}
