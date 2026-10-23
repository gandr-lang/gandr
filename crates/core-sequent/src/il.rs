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
//!
//! # Scope is carried
//!
//! Every node has its support — the variables and covariables it mentions,
//! as a selection from the binders in scope where it stands — in the co-de
//! Bruijn carrier of [`gandr_core_term::support`]. A node's [`NodeScope`] is
//! its support in each binding space: the union of what the node names, its
//! annotations and its children's scopes, each lowered past the binders the
//! node opens over that child, so a scope is computed where it is built and
//! never by a walk below it. A binder whose body ignores its bound name has a
//! body support that does not select it, and the binder's own support is the
//! body's lowered past the name.
//!
//! Every node keeps its scope beside it, in its family's row: two slots, one
//! per space, each the code itself when it is one word and a handle into the
//! arena's word arena ([`gandr_core_term::support::WordArena`]) otherwise, so
//! a scope is 16 bytes with no heap block on every term of ordinary depth.
//! Minting alone writes a scope: it gathers a node's in the pass that resolves
//! the node's children and stores it once the node is admitted, so the scope a
//! row carries is its own by construction and the check reads the root's
//! rather than rebuilding any. A node stores no edges: the edge from a node to
//! a child — the child's support as a selection from the node's support
//! extended by the bound names — is a function of the two supports and the
//! crossing, so it is derived where a reader needs it.
//!
//! The IL counts three zones. Producer variables live in the core's two, the
//! intuitionistic `Γ` and the linear `Σ`, under the core's crossings: a
//! memory form's hold and access bodies open one linear binder, every other
//! producer binder an intuitionistic one. Covariables live in a zone of the
//! IL's own, `Δ`, carried as a second support beside the first. `Δ` is
//! cartesian, as `Γ` is — a continuation may be named by both sides of a cut
//! and by every arm of a match — so its support is carried in the carrier's
//! intuitionistic zone. A support's kind is read off its zone, never stored.
//!
//! What each datum is, read as deep inference over the IL:
//!
//! - a support on a cut is the data half of the cut's dependence web: an event
//!   under `μ̃x. s` depends on the cut's producer exactly when its support holds
//!   `x`;
//! - a bound name a body's support does not select is a weakening (`aw↓`): a
//!   value bound and never read needs no store, and a covariable never named
//!   drops its continuation;
//! - a linear support partitions its node's `Σ` among the children — the switch
//!   instances splitting the context — while a `Γ` or `Δ` support is cartesian,
//!   its overlap the contractions (`ac↓`);
//! - a support over the arms of a `case`, a `datacase` or a `cocase` is
//!   additive: an index two arms share is no copy;
//! - a closure's capture is its root support: a thunk, a fixpoint, a copattern
//!   object, a capture or a stack's bind frame captures exactly the
//!   intuitionistic bindings its support selects, which
//!   [`CommandArena::captures`] names.
//!
//! A fold's element and result types and an interface's types are core types
//! in the arena's annotation arena, and they name variables too, so a node's
//! support counts what its annotations name: a closure must capture what its
//! annotations read for readback to close them. Core nodes carry their
//! supports, so an annotation's support is read off its root.
//!
//! A carried support is syntactic and over-approximates dependence: a
//! β-removable use still occurs. It keys, schedules and bounds capture, where
//! an over-approximation splits work and never merges two answers; it never
//! decides a strengthening.
//!
//! The node families are plain vectors beside their scope tables, so every
//! reader that matches on a node is unchanged: the printer, the inspector and
//! readback read the de Bruijn nodes, the projection, as before. The
//! alternatives were a scope field on every node variant, which changes
//! every match on a node across the tree for data most readers never touch,
//! and a pass computing scopes over a built term, which walks every term a
//! second time.

use alloc::boxed::Box;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_core_term::BinderDepth;
use gandr_core_term::Zone;
use gandr_core_term::support::Crossing;
use gandr_core_term::support::Indices;
use gandr_core_term::support::ThinningRef;
use gandr_core_term::support::Union;
use gandr_core_term::support::WordArena;
use gandr_core_term::support::WordMark;
use gandr_kernel_strata::Level;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Summand;
use gandr_theory_cell_complexes::Polarity;

pub use self::carried::Slots;
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
/// any arity (the unit its empty case), a structural record by its labels, an
/// injection into a summand by position, the explicit universe lift and a
/// nominal datatype's constructors. Each head declares its arity; the typed-IL
/// check and the machine read the declaration rather than a constant.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum ConstructorTag
{
    /// The tuple `(p₁, …, pₙ)` of this many fields; the unit `()` is the
    /// tuple of none.
    Tuple(ProducerArity),
    /// The structural record `{l₁ = p₁, …, lₙ = pₙ}`, one field per label, the
    /// labels in the core's canonical order: strictly increasing as UTF-8
    /// bytes. The record of no labels is a record, not the unit.
    Record(alloc::sync::Arc<[gandr_core_term::FieldLabel]>),
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
    /// which the IL does not carry; the declaration that names its family is
    /// carried when the core names one, so a value read back names its
    /// constructor. The machine never reads it: a data case matches by
    /// ordinal alone.
    Data
    {
        /// The constructor's ordinal in its declaration.
        tag: gandr_kernel_term::ConstructorTag,
        /// The number of fields the constructor carries.
        arity: ProducerArity,
        /// The declaration of the family, when the core's classifier names
        /// one.
        family: Option<gandr_kernel_term::ConstantIndex>,
    },
    /// A recorded run: its moves in order, each send's and receive's payload
    /// a producer field in move order. A choice's label and a close live in
    /// the head, which carries no value.
    Recorded(alloc::sync::Arc<[gandr_core_term::session::RecordedMove<()>]>),
}

impl ConstructorTag
{
    /// The number of producer fields the head declares.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a tuple's and a datatype constructor's own field count, a
    ///   record's label count, `0` for the empty list, `2` for a list cell, `1`
    ///   for an injection and a lift, and a recorded run's sends and receives.
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
        | Self::Record(ref labels) => ret == ProducerArity::from(labels.len()),
        | Self::Recorded(ref moves) => ret == recorded_payloads(moves),
    })]
    pub fn producer_arity(&self) -> ProducerArity
    {
        match *self {
            Self::ListNil => ProducerArity::ZERO,
            Self::ListCons => ProducerArity::TWO,
            Self::Injection(_) | Self::Lift(_) => ProducerArity::ONE,
            Self::Tuple(arity) | Self::Data { arity, .. } => arity,
            Self::Record(ref labels) => ProducerArity::from(labels.len()),
            Self::Recorded(ref moves) => recorded_payloads(moves),
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
            Self::Tuple(_)
            | Self::Record(_)
            | Self::ListNil
            | Self::ListCons
            | Self::Injection(_)
            | Self::Lift(_)
            | Self::Data { .. }
            | Self::Recorded(_) => ConsumerArity::ZERO,
        }
    }
}

/// The producer fields of a recorded run: one per move that carries a
/// payload.
///
/// # Specification
/// trivial.
fn recorded_payloads(moves: &[gandr_core_term::session::RecordedMove<()>]) -> ProducerArity
{
    ProducerArity::from(
        moves
            .iter()
            .filter(|movement| {
                matches!(
                    movement,
                    gandr_core_term::session::RecordedMove::Sent(())
                        | gandr_core_term::session::RecordedMove::Received(())
                )
            })
            .count(),
    )
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
    /// Observe one component of a lazy product.
    Project(gandr_kernel_term::Component),
}

impl Ord for DestructorTag
{
    /// Order observation labels without imposing an ordering on source sums.
    ///
    /// # Specification
    /// - ensures: distinct observations compare unequal; application precedes
    ///   force, followed by the projections in component order.
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
            Self::Apply => (0_u8, 0_usize),
            Self::Force => (1, 0),
            Self::Project(component) => (2, usize::from(component)),
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
            Self::Apply => ProducerArity::ONE,
            Self::Force | Self::Project(_) => ProducerArity::ZERO,
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
            Self::Apply | Self::Force | Self::Project(_) => ConsumerArity::ONE,
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
            Self::Apply | Self::Project(_) => Polarity::Negative,
            Self::Force => Polarity::Positive,
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
    /// A code: a quoted type or computation type, held in the command arena's
    /// annotations. It passes where a type argument stands and is read back as
    /// itself; no command observes it.
    Code(gandr_core_term::ValueId),
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
        /// Each constructor's field count, in ordinal order, as its data
        /// declaration states it: how many of its branch's curried objects
        /// take fields, and the size of its cell. A loop arm after the
        /// constructors' branches has none.
        arities: Box<[gandr_kernel_term::FieldCount]>,
        /// The continuation each branch returns to.
        then: ConsumerId,
    },
    /// A selection `select[f](c)`: the value it receives is a tuple or a
    /// record, and the field `f` names is delivered to `c`. The width is read
    /// from the constructor the selection meets, never stated, so a record
    /// wider than the type it was checked at still answers by label. The
    /// selection opens no binder, so its continuation `c` is any consumer.
    Select
    {
        /// The field the selection reads.
        selector: Selector,
        /// The continuation the field is delivered to.
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

/// The field a [`ConsumerNode::Select`] reads from the value it meets.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Selector
{
    /// A tuple's component, by its position from zero.
    Component(gandr_core_term::Component),
    /// A record's field, by its label.
    Label(gandr_core_term::FieldLabel),
}

/// What a handler binds over its subject besides the subject's return
/// covariable.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Introduces
{
    /// Nothing: a handler of the core's anonymous `handle`, which an
    /// operation reaches by being the nearest delimiter.
    Nothing,
    /// A capability: the subject binds one producer, the capability the
    /// handler introduces, and an exercise through it reaches this handler
    /// whatever stands between.
    Capability,
}

/// How an operation request finds the handler that answers it.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Route
{
    /// The nearest delimiter decides: a handler of the operation's interface
    /// answers, any other delimiter offers the request to the host.
    Nearest,
    /// The capability the producer evaluates to decides: the handler that
    /// introduced it answers, across every frame above it; a capability no
    /// handler introduced — one the host holds — offers the request to the
    /// host.
    Capability(ProducerId),
}

/// The interface a reached hole performs, named so no source can claim it.
///
/// Its one operation, [`REACHED`], carries the hole's name as an integer;
/// no handler a source writes claims it, so the request is offered to the
/// host.
pub const REACHED_HOLE: &str = "?hole";

/// The one operation of [`REACHED_HOLE`].
pub const REACHED: &str = "reached";

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
        /// How the request finds its handler.
        route: Route,
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
        /// What the subject binds besides its return covariable.
        introduces: Introduces,
        /// The subject, binding the introduced capability, when there is
        /// one, and one return covariable.
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
    /// End a first-class stack without resuming it: the unwind of each access
    /// it captured runs, innermost first, and the unit is delivered.
    Abandon
    {
        /// The stack value, never resumed.
        stack: ProducerId,
        /// Where the unit is delivered.
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
    /// A memory form `𝓜` with its continuation. A hold runs its body with
    /// the held value bound as the innermost linear producer; an access
    /// pushes the frame that writes its view back on a resume and runs its
    /// unwind on an abort, then runs its body with the view bound so; an
    /// eliminator records how its view ends on that frame and returns the
    /// unit.
    Memory
    {
        /// The form. A hold's and an access's body each bind one linear
        /// producer and one return covariable; an access's unwind binds one
        /// return covariable.
        form: gandr_core_term::memory::MemoryForm<ProducerId, CommandId>,
        /// The continuation outside the form.
        continuation: ConsumerId,
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
            Self::DanglingProducer(id) => write!(f, "producer {id} is not in the arena"),
            Self::DanglingConsumer(id) => write!(f, "consumer {id} is not in the arena"),
            Self::DanglingCommand(id) => write!(f, "command {id} is not in the arena"),
            Self::DanglingAnnotation(_) => f.write_str("a List-fold annotation does not resolve"),
            Self::FamilyFull(family) => {
                let name = match family {
                    NodeFamily::Producer => "producer",
                    NodeFamily::Consumer => "consumer",
                    NodeFamily::Command => "command",
                };
                write!(f, "the {name} family is full")
            },
        }
    }
}

impl core::error::Error for MintRefusal
{
}

/// The address of a node of any of the three families.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum NodeAddress
{
    /// A producer.
    Producer(ProducerId),
    /// A consumer.
    Consumer(ConsumerId),
    /// A command.
    Command(CommandId),
}

impl fmt::Display for NodeAddress
{
    /// Writes the family and the address.
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
            Self::Producer(id) => write!(f, "producer {id}"),
            Self::Consumer(id) => write!(f, "consumer {id}"),
            Self::Command(id) => write!(f, "command {id}"),
        }
    }
}

/// The binders a node opens over one of its children: producer binders in
/// the core's zones `Γ; Σ`, covariable binders in the IL's own `Δ`.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Opens
{
    /// The producer binders, per zone.
    pub producers: Crossing,
    /// The covariable binders, counted in the carrier's intuitionistic zone.
    pub covariables: Crossing,
}

impl Opens
{
    /// `producers` intuitionistic producer binders and `covariables`
    /// covariables.
    ///
    /// # Specification
    /// trivial.
    fn binding(
        producers: ProducerArity,
        covariables: ConsumerArity,
    ) -> Self
    {
        Self {
            producers: Crossing::of(
                Zone::Intuitionistic,
                BinderDepth::from(usize::from(producers)),
            ),
            covariables: Crossing::of(
                Zone::Intuitionistic,
                BinderDepth::from(usize::from(covariables)),
            ),
        }
    }

    /// `linear` linear producer binders and one covariable: a memory form's
    /// body.
    ///
    /// # Specification
    /// trivial.
    fn memory(linear: gandr_core_term::Binders) -> Self
    {
        Self {
            producers: Crossing::of(
                Zone::Linear,
                BinderDepth::from(usize::try_from(u32::from(linear)).unwrap_or(usize::MAX)),
            ),
            covariables: Crossing::of(Zone::Intuitionistic, BinderDepth::from(1_usize)),
        }
    }
}

/// A node's scope, read in place: its support in the producer zones `Γ; Σ`
/// and its support in the covariable zone `Δ`.
///
/// # Specification
/// - executable: none — a data declaration; minting builds both supports as the
///   union of what the node names and its children's scopes past the binders it
///   opens over each, in the order [`producer_children`], [`consumer_children`]
///   and [`command_children`] list them, which makes each exactly the node's
///   free indices.
///
/// # Adequacy
/// - hypothesis: L3 — a binder whose body ignores its bound name and one whose
///   body reads it, in each zone, separate a lowered support from a kept bound
///   name; L2 — every command of every generated focused term has the support
///   an independent walk computes.
/// - witness: `il::tests::an_unused_binder_thins_to_zero`
/// - witness: `tests::focus_properties::root_support_equals_the_walk_on_every_focused_term`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NodeScope<'arena>
{
    /// The producer support.
    producers: ThinningRef<'arena>,
    /// The covariable support.
    covariables: ThinningRef<'arena>,
}

impl<'arena> NodeScope<'arena>
{
    /// The producer variables the node names, in `Γ; Σ`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn producers(self) -> ThinningRef<'arena>
    {
        self.producers
    }

    /// The covariables the node names, in `Δ`'s carrier zone.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn covariables(self) -> ThinningRef<'arena>
    {
        self.covariables
    }
}

/// A node's scope under construction at its mint: what the node names, its
/// annotations' supports and its children's carried scopes past the binders
/// it opens over each, fed in any order.
///
/// # Specification
/// trivial.
#[derive(Debug, Default)]
pub struct Scoping
{
    /// The producer support under construction.
    producers: Union,
    /// The covariable support under construction.
    covariables: Union,
}

impl Scoping
{
    /// The empty scope.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new() -> Self
    {
        Self {
            producers: Union::new(),
            covariables: Union::new(),
        }
    }

    /// Add the producer and covariable occurrences the node names itself.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn name<Producers, Covariables>(
        &mut self,
        producers: Producers,
        covariables: Covariables,
    ) where
        Producers: IntoIterator<Item = (Zone, DeBruijnIndex)>,
        Covariables: IntoIterator<Item = (Zone, DeBruijnIndex)>,
    {
        for (zone, index) in producers {
            self.producers.name(zone, index);
        }
        for (zone, index) in covariables {
            self.covariables.name(zone, index);
        }
    }

    /// Add the intuitionistic indices an annotation's carried support
    /// selects, read where the node it annotates stands.
    ///
    /// # Specification
    /// - ensures: the producer support holds every intuitionistic index
    ///   `support` selects; a linear occurrence in a type is not counted, as no
    ///   type binds into the linear zone.
    /// - panics: none.
    /// - executable: none — the scoping is read only by finishing it, which
    ///   consumes it; the witness reads the support back off the minted node.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fold whose element type names a variable no term of
    ///   the fold names, beside one whose types are closed, separates a counted
    ///   annotation from an ignored one.
    /// - witness: `il::tests::an_annotation_counts_in_its_nodes_support`
    #[inline]
    pub fn annotation(
        &mut self,
        support: ThinningRef<'_>,
    )
    {
        for index in support.indices(Zone::Intuitionistic) {
            self.producers.name(Zone::Intuitionistic, index);
        }
    }

    /// Add a child's scope, as `slots` keep it in `words`, past the binders
    /// the node opens over it.
    ///
    /// # Specification
    /// - ensures: each space holds the child's support there, read off its slot
    ///   past the binders of that space `opens` names.
    /// - panics: none.
    /// - executable: none — this runs once per child on the mint and check
    ///   paths; the witnesses hold every scope it builds to an independent
    ///   walk.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Union::stored_child`], once per space.
    /// - witness: `tests::focus_properties::root_support_equals_the_walk_on_every_focused_term`
    #[inline]
    pub(crate) fn child(
        &mut self,
        slots: Slots,
        words: &WordArena,
        opens: Opens,
    )
    {
        let [producers, covariables] = slots;
        self.producers
            .stored_child(producers, words, opens.producers);
        self.covariables
            .stored_child(covariables, words, opens.covariables);
    }
}

/// A suspended command a run closes over the bindings it captures: what a
/// store value or a stack's bind frame holds.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Suspension
{
    /// A thunk, a recursive thunk, a copattern object or a context capture,
    /// by its producer.
    Producer(ProducerId),
    /// A thunk's body, which binds a covariable and no producer.
    Thunk(CommandId),
    /// A recursive thunk's body, which binds the thunk itself and a
    /// covariable.
    Fixpoint(CommandId),
    /// A stack's bind frame body, which binds the value it is resumed with
    /// and a covariable.
    Bind(CommandId),
}

/// The intuitionistic bindings a suspension captures where it is created,
/// as de Bruijn indices counted there, innermost first.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug)]
pub struct Captures<'arena>
{
    /// The suspended command's selected indices past its own binders,
    /// ascending.
    selected: Indices<'arena>,
    /// The producer binders the suspension's own former opens.
    past: u32,
}

impl Captures<'_>
{
    /// `index` read where the suspension is created.
    ///
    /// # Specification
    /// trivial.
    fn outer(
        &self,
        index: DeBruijnIndex,
    ) -> DeBruijnIndex
    {
        // reason: the selection was cut at the first index past the
        // suspension's own binders, so the difference never underflows; the
        // saturating step keeps the read total.
        DeBruijnIndex::from(u32::from(index).saturating_sub(self.past))
    }
}

impl Iterator for Captures<'_>
{
    type Item = DeBruijnIndex;

    /// The next captured index, innermost first.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn next(&mut self) -> Option<DeBruijnIndex>
    {
        let index = self.selected.next()?;
        Some(self.outer(index))
    }

    /// The captures left, exactly.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>)
    {
        self.selected.size_hint()
    }
}

impl DoubleEndedIterator for Captures<'_>
{
    /// The next captured index from the outermost end.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn next_back(&mut self) -> Option<DeBruijnIndex>
    {
        let index = self.selected.next_back()?;
        Some(self.outer(index))
    }
}

impl ExactSizeIterator for Captures<'_>
{
}

/// A snapshot of the three family lengths and the scopes' word arena.
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
    /// The scopes' word arena length.
    words: WordMark,
    /// The attached annotation graph's family lengths.
    annotations: gandr_core_term::ArenaWatermark,
}

/// A node beside the slots its scope is kept in: one row of its family's
/// table.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Row<Node>
{
    /// The node.
    node: Node,
    /// The scope minting built for it.
    scope: carried::Slots,
}

/// The append-only arena owning every IL node of one translation or run.
///
/// The three families are append-only vectors and a node's children are
/// addresses into the same arena, so cloning or dropping an arena is a flat
/// vector operation on any term depth. Each node's scope sits beside it, in
/// its family's row at the node's address, and the word arena holds the
/// codes wider than a slot.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct CommandArena
{
    /// The producer nodes and their scopes, in minting order.
    producers: Vec<Row<ProducerNode>>,
    /// The consumer nodes and their scopes, in minting order.
    consumers: Vec<Row<ConsumerNode>>,
    /// The command nodes and their scopes, in minting order.
    commands: Vec<Row<CommandNode>>,
    /// The words of every scope wider than a slot.
    words: WordArena,
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

    /// The current watermark: the three family lengths and the word arena's.
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
            words: self.words.mark(),
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
    ///   that family as it was, each kept node with its scope. Every node kept
    ///   was minted before the mark and so names only kept children: truncation
    ///   never leaves a dangling child inside the arena.
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
        self.words.truncate(watermark.words);
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
            .is_some_and(|held| core::ptr::eq(&raw const held.node, core::ptr::from_ref(node))),
        | None => usize::try_from(u32::from(id))
            .map_or(true, |offset| offset >= self.producers.len()),
    })]
    pub fn producer(
        &self,
        id: ProducerId,
    ) -> Option<&ProducerNode>
    {
        id.read_in(&self.producers).map(|row| &row.node)
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
            .is_some_and(|held| core::ptr::eq(&raw const held.node, core::ptr::from_ref(node))),
        | None => usize::try_from(u32::from(id))
            .map_or(true, |offset| offset >= self.consumers.len()),
    })]
    pub fn consumer(
        &self,
        id: ConsumerId,
    ) -> Option<&ConsumerNode>
    {
        id.read_in(&self.consumers).map(|row| &row.node)
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
            .is_some_and(|held| core::ptr::eq(&raw const held.node, core::ptr::from_ref(node))),
        | None => usize::try_from(u32::from(id))
            .map_or(true, |offset| offset >= self.commands.len()),
    })]
    pub fn command(
        &self,
        id: CommandId,
    ) -> Option<&CommandNode>
    {
        id.read_in(&self.commands).map(|row| &row.node)
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
    ///   returned; every child it names resolves; its scope, the union of the
    ///   scopes its children have and the variable it names, is recorded at the
    ///   same address.
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
    /// - witness: `il::tests::an_unused_binder_thins_to_zero`
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
                && self.command_count() == entry.commands
                && self.producer(id).is_some_and(|node| match *node {
                    | ProducerNode::Reify(ref frames) => frames.iter().all(|frame| match *frame {
                        | gandr_core_term::control::StackFrame::Apply(value) => self.producer(value).is_some(),
                        | gandr_core_term::control::StackFrame::Bind(body) => self.command(body).is_some(),
                        | gandr_core_term::control::StackFrame::Project(_) => true,
                    }),
                    | ProducerNode::Primitive { arguments, .. } => arguments.iter().all(|child| self.producer(*child).is_some()),
                    | ProducerNode::Variable { .. } | ProducerNode::Constant(_) | ProducerNode::Literal(_) | ProducerNode::Code(_) => true,
                    | ProducerNode::Constructor { ref producers, ref consumers, .. } =>
                        producers.iter().all(|child| self.producer(*child).is_some())
                            && consumers.iter().all(|child| self.consumer(*child).is_some()),
                    | ProducerNode::Thunk { body } | ProducerNode::Mu { body } | ProducerNode::Fixpoint { body, .. } => self.command(body).is_some(),
                    | ProducerNode::Cocase { ref arms } => arms.iter().all(|arm| self.command(arm.body).is_some()),
                }),
            | Err(_) => self.watermark() == entry,
        },
    )]
    pub fn mint_producer(
        &mut self,
        node: ProducerNode,
    ) -> Result<ProducerId, MintRefusal>
    {
        let scoping = self.producer_scoping(&node)?;
        let id = ProducerId::next_in(&self.producers)
            .ok_or(MintRefusal::FamilyFull(NodeFamily::Producer))?;
        let scope = scoping.store(&mut self.words);
        self.producers.push(Row { node, scope });
        Ok(id)
    }

    /// Mint a consumer node over children the arena holds.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the node is appended and its fresh address
    ///   returned; every child it names resolves; its scope, the union of the
    ///   scopes its children have, the covariable it names and the variables
    ///   its annotations name, is recorded at the same address.
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
    /// - witness: `il::tests::an_unused_binder_thins_to_zero`
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
                && self.command_count() == entry.commands
                && self.consumer(id).is_some_and(|node| match *node {
                    | ConsumerNode::Covariable(_) | ConsumerNode::Top => true,
                    | ConsumerNode::MuTilde { body } => self.command(body).is_some(),
                    | ConsumerNode::Destructor { ref producers, ref consumers, .. } =>
                        producers.iter().all(|child| self.producer(*child).is_some())
                            && consumers.iter().all(|child| self.consumer(*child).is_some()),
                    | ConsumerNode::Case { ref arms } => arms.iter().all(|arm| self.command(arm.body).is_some()),
                    | ConsumerNode::DataCase { ref branches, then, .. } =>
                        branches.iter().all(|child| self.producer(*child).is_some()) && self.consumer(then).is_some(),
                    | ConsumerNode::Select { then, .. } => self.consumer(then).is_some(),
                    | ConsumerNode::ListFold { element, result, on_nil, on_cons, continuation } =>
                        self.annotations.value_type(element).is_some()
                            && self.annotations.value_type(result).is_some()
                            && self.command(on_nil).is_some()
                            && self.command(on_cons).is_some()
                            && self.consumer(continuation).is_some(),
                }),
            | Err(_) => self.watermark() == entry,
        },
    )]
    pub fn mint_consumer(
        &mut self,
        node: ConsumerNode,
    ) -> Result<ConsumerId, MintRefusal>
    {
        let scoping = self.consumer_scoping(&node)?;
        let id = ConsumerId::next_in(&self.consumers)
            .ok_or(MintRefusal::FamilyFull(NodeFamily::Consumer))?;
        let scope = scoping.store(&mut self.words);
        self.consumers.push(Row { node, scope });
        Ok(id)
    }

    /// Mint a command node over children the arena holds.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the node is appended and its fresh address
    ///   returned; its children resolve; its scope, the union of the scopes its
    ///   children have, the linear slot it names and the variables its
    ///   interface names, is recorded at the same address.
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
    /// - witness: `il::tests::an_unused_binder_thins_to_zero`
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
                && self.consumer_count() == entry.consumers
                && self.command(id).is_some_and(|node| {
                    command_signature(node).is_none_or(|signature| signature.types().all(|ty| self.annotations.value_type(ty).is_some()))
                        && command_children(node, |child, _| self.slots(child).map(|_| ()).ok_or(())).is_ok()
                }),
            | Err(_) => self.watermark() == entry,
        },
    )]
    pub fn mint_command(
        &mut self,
        node: CommandNode,
    ) -> Result<CommandId, MintRefusal>
    {
        let scoping = self.command_scoping(&node)?;
        let id = CommandId::next_in(&self.commands)
            .ok_or(MintRefusal::FamilyFull(NodeFamily::Command))?;
        let scope = scoping.store(&mut self.words);
        self.commands.push(Row { node, scope });
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

    /// The intuitionistic bindings `suspension` captures where it is
    /// created: its support's intuitionistic selection past the producer
    /// binders its own former opens, innermost first.
    ///
    /// # Specification
    /// - requires: nothing; a dangling address is admissible.
    /// - ensures: `Some` exactly when the arena holds the suspension's node;
    ///   then every intuitionistic index the node's support selects at or past
    ///   the binders its former opens — none for a thunk, a copattern object or
    ///   a capture, the thunk itself for a fixpoint's body, the value for a
    ///   bind frame's body — lowered past them, ascending, and no other.
    /// - provides: what a closure captures, which a run's transfer binds and
    ///   readback reads an environment through.
    /// - fails: `None` on a dangling address.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a thunk, a fixpoint, a copattern object and a bind
    ///   frame each over a support with an index below, at and past its own
    ///   binders separate the lowering from identity and the four former
    ///   offsets from each other; a dangling body is absent. L2 — every closure
    ///   a generated run answers with reads back closed over exactly these
    ///   bindings.
    /// - witness: `il::tests::captures_skip_each_suspensions_own_binders`
    /// - witness: `tests::run::a_captured_environment_holds_exactly_its_support`
    #[spec(ensures: |ret| ret.is_some() == match suspension {
        | Suspension::Producer(id) => self.producer(id).is_some(),
        | Suspension::Thunk(body) | Suspension::Fixpoint(body) | Suspension::Bind(body) => self.command(body).is_some(),
    })]
    #[inline]
    #[must_use]
    pub fn captures(
        &self,
        suspension: Suspension,
    ) -> Option<Captures<'_>>
    {
        let (node, past) = match suspension {
            Suspension::Producer(id) => (NodeAddress::Producer(id), 0_u32),
            Suspension::Thunk(body) => (NodeAddress::Command(body), 0_u32),
            Suspension::Fixpoint(body) | Suspension::Bind(body) => {
                (NodeAddress::Command(body), 1_u32)
            },
        };
        let scope = self.node_scope(node)?;
        let crossed = BinderDepth::from(usize::try_from(past).unwrap_or(usize::MAX));
        Some(Captures {
            selected: scope.producers().outside(Zone::Intuitionistic, crossed),
            past,
        })
    }
}

/// Visit the children of a producer, each beside the binders the producer
/// opens over it, in edge order, stopping at the first refusal `each`
/// answers.
///
/// # Specification
/// - ensures: a stack's frames in order, an application frame's argument under
///   nothing and a bind frame's body under one producer binder and one
///   covariable; a primitive's arguments; a constructor's producer fields then
///   its consumer fields; a thunk's or a capture's body under one covariable; a
///   fixpoint's body under one producer binder and one covariable; a copattern
///   object's arms in order, each under its head's producer and consumer
///   arities; nothing for a variable, a constant or a literal. `each`'s first
///   refusal is answered and no later child visited.
/// - panics: none.
/// - intension: allocates nothing, so a mint and a check visit a node's
///   children at the cost of the visit.
/// - executable: none — the listing is the statement; the witnesses observe it
///   through the supports and the checks it shapes.
///
/// # Errors
/// The first refusal `each` answers.
///
/// # Adequacy
/// - hypothesis: L2 — every producer former the generated focused terms build
///   is listed, and the carried supports agree with an independent walk; L3 — a
///   fixpoint's, a thunk's and an arm's supports are read at the bound names.
/// - witness: `tests::focus_properties::root_support_equals_the_walk_on_every_focused_term`
/// - witness: `il::tests::an_unused_binder_thins_to_zero`
#[inline]
pub fn producer_children<Refusal, Each>(
    node: &ProducerNode,
    mut each: Each,
) -> Result<(), Refusal>
where
    Each: FnMut(NodeAddress, Opens) -> Result<(), Refusal>,
{
    let at = Opens::default();
    match *node {
        ProducerNode::Reify(ref frames) => {
            for frame in frames.iter() {
                match *frame {
                    gandr_core_term::control::StackFrame::Apply(value) => {
                        each(NodeAddress::Producer(value), at)?;
                    },
                    gandr_core_term::control::StackFrame::Bind(body) => {
                        each(
                            NodeAddress::Command(body),
                            Opens::binding(ProducerArity::ONE, ConsumerArity::ONE),
                        )?;
                    },
                    gandr_core_term::control::StackFrame::Project(_) => {},
                }
            }
        },
        ProducerNode::Primitive { ref arguments, .. } => {
            for &argument in arguments.iter() {
                each(NodeAddress::Producer(argument), at)?;
            }
        },
        ProducerNode::Variable { .. }
        | ProducerNode::Constant(_)
        | ProducerNode::Literal(_)
        | ProducerNode::Code(_) => {},
        ProducerNode::Constructor {
            ref producers,
            ref consumers,
            ..
        } => fields(producers, consumers, &mut each)?,
        ProducerNode::Thunk { body } | ProducerNode::Mu { body } => {
            each(
                NodeAddress::Command(body),
                Opens::binding(ProducerArity::ZERO, ConsumerArity::ONE),
            )?;
        },
        ProducerNode::Fixpoint { body, .. } => {
            each(
                NodeAddress::Command(body),
                Opens::binding(ProducerArity::ONE, ConsumerArity::ONE),
            )?;
        },
        ProducerNode::Cocase { ref arms } => {
            for arm in arms {
                each(
                    NodeAddress::Command(arm.body),
                    Opens::binding(
                        arm.destructor.producer_arity(),
                        arm.destructor.consumer_arity(),
                    ),
                )?;
            }
        },
    }
    Ok(())
}

/// Visit the children of a consumer, each beside the binders the consumer
/// opens over it, in edge order, stopping at the first refusal `each`
/// answers.
///
/// # Specification
/// - ensures: a `μ̃`'s body under one producer binder; a frame's producer
///   arguments then its consumer arguments; a match's arms in order, each under
///   its head's producer and consumer arities; a nominal match's branches then
///   its continuation; a selection's continuation; a fold's empty branch under
///   one covariable, its cell branch under two producer binders and one
///   covariable, then its continuation; nothing for a covariable or `★`.
///   `each`'s first refusal is answered and no later child visited.
/// - panics: none.
/// - intension: allocates nothing.
/// - executable: none — the listing is the statement; the witnesses observe it
///   through the supports and the checks it shapes.
///
/// # Errors
/// The first refusal `each` answers.
///
/// # Adequacy
/// - hypothesis: L2 — every consumer former the generated focused terms build
///   is listed, and the carried supports agree with an independent walk; L3 — a
///   `μ̃`'s and a match arm's supports are read at the bound names.
/// - witness: `tests::focus_properties::root_support_equals_the_walk_on_every_focused_term`
/// - witness: `il::tests::an_unused_binder_thins_to_zero`
#[inline]
pub fn consumer_children<Refusal, Each>(
    node: &ConsumerNode,
    mut each: Each,
) -> Result<(), Refusal>
where
    Each: FnMut(NodeAddress, Opens) -> Result<(), Refusal>,
{
    let at = Opens::default();
    match *node {
        ConsumerNode::Covariable(_) | ConsumerNode::Top => {},
        ConsumerNode::MuTilde { body } => {
            each(
                NodeAddress::Command(body),
                Opens::binding(ProducerArity::ONE, ConsumerArity::ZERO),
            )?;
        },
        ConsumerNode::Destructor {
            ref producers,
            ref consumers,
            ..
        } => fields(producers, consumers, &mut each)?,
        ConsumerNode::Case { ref arms } => {
            for arm in arms {
                each(
                    NodeAddress::Command(arm.body),
                    Opens::binding(
                        arm.constructor.producer_arity(),
                        arm.constructor.consumer_arity(),
                    ),
                )?;
            }
        },
        ConsumerNode::DataCase {
            ref branches, then, ..
        } => {
            fields(branches, core::slice::from_ref(&then), &mut each)?;
        },
        ConsumerNode::Select { then, .. } => each(NodeAddress::Consumer(then), at)?,
        ConsumerNode::ListFold {
            on_nil,
            on_cons,
            continuation,
            ..
        } => {
            each(
                NodeAddress::Command(on_nil),
                Opens::binding(ProducerArity::ZERO, ConsumerArity::ONE),
            )?;
            each(
                NodeAddress::Command(on_cons),
                Opens::binding(ProducerArity::TWO, ConsumerArity::ONE),
            )?;
            each(NodeAddress::Consumer(continuation), at)?;
        },
    }
    Ok(())
}

/// Visit the children of a command, each beside the binders the command
/// opens over it, in edge order, stopping at the first refusal `each`
/// answers.
///
/// # Specification
/// - ensures: an operation's capability when it routes by one, its payload, its
///   continuation; a handler's subject under its introduced capability and one
///   covariable, its return clause under one producer binder and one
///   covariable, each operation clause under two producer binders and one
///   covariable, its continuation; a resume's stack, its body under one
///   covariable, its continuation; a reset's body under one covariable, its
///   continuation; a shift's body under one producer binder and one covariable,
///   its continuation; a cut's producer and consumer; a memory form's values,
///   its bodies each under the linear binders the form opens over it and one
///   covariable, its continuation. `each`'s first refusal is answered and no
///   later child visited.
/// - panics: none.
/// - intension: allocates nothing.
/// - executable: none — the listing is the statement; the witnesses observe it
///   through the supports and the checks it shapes.
///
/// # Errors
/// The first refusal `each` answers.
///
/// # Adequacy
/// - hypothesis: L2 — every command former the generated focused terms build is
///   listed, and the carried supports agree with an independent walk; L3 — the
///   control formers' scopes are read off their roots, and a cut's two children
///   are read.
/// - witness: `tests::focus_properties::root_support_equals_the_walk_on_every_focused_term`
/// - witness: `check::tests::control_scopes_are_local_to_each_body`
/// - witness: `check::tests::scope_boundaries_keep_linear_variables_free`
#[inline]
pub fn command_children<Refusal, Each>(
    node: &CommandNode,
    mut each: Each,
) -> Result<(), Refusal>
where
    Each: FnMut(NodeAddress, Opens) -> Result<(), Refusal>,
{
    let at = Opens::default();
    let returns = Opens::binding(ProducerArity::ZERO, ConsumerArity::ONE);
    match *node {
        CommandNode::Perform {
            route,
            payload,
            continuation,
            ..
        } => {
            if let Route::Capability(capability) = route {
                each(NodeAddress::Producer(capability), at)?;
            }
            each(NodeAddress::Producer(payload), at)?;
            each(NodeAddress::Consumer(continuation), at)?;
        },
        CommandNode::Handle {
            introduces,
            subject,
            on_return,
            ref clauses,
            continuation,
            ..
        } => {
            let introduced = match introduces {
                Introduces::Nothing => ProducerArity::ZERO,
                Introduces::Capability => ProducerArity::ONE,
            };
            each(
                NodeAddress::Command(subject),
                Opens::binding(introduced, ConsumerArity::ONE),
            )?;
            each(
                NodeAddress::Command(on_return),
                Opens::binding(ProducerArity::ONE, ConsumerArity::ONE),
            )?;
            for clause in clauses.iter() {
                each(
                    NodeAddress::Command(clause.body),
                    Opens::binding(ProducerArity::TWO, ConsumerArity::ONE),
                )?;
            }
            each(NodeAddress::Consumer(continuation), at)?;
        },
        CommandNode::Resume {
            stack,
            body,
            continuation,
        } => {
            each(NodeAddress::Producer(stack), at)?;
            each(NodeAddress::Command(body), returns)?;
            each(NodeAddress::Consumer(continuation), at)?;
        },
        CommandNode::Reset { body, continuation } => {
            each(NodeAddress::Command(body), returns)?;
            each(NodeAddress::Consumer(continuation), at)?;
        },
        CommandNode::Shift { body, continuation } => {
            each(
                NodeAddress::Command(body),
                Opens::binding(ProducerArity::ONE, ConsumerArity::ONE),
            )?;
            each(NodeAddress::Consumer(continuation), at)?;
        },
        CommandNode::Cut {
            producer, consumer, ..
        }
        | CommandNode::Abandon {
            stack: producer,
            continuation: consumer,
        } => {
            each(NodeAddress::Producer(producer), at)?;
            each(NodeAddress::Consumer(consumer), at)?;
        },
        CommandNode::Memory {
            ref form,
            continuation,
        } => {
            for value in form.values() {
                each(NodeAddress::Producer(value), at)?;
            }
            for (body, linear) in form.scoped() {
                each(NodeAddress::Command(body), Opens::memory(linear))?;
            }
            each(NodeAddress::Consumer(continuation), at)?;
        },
    }
    Ok(())
}

/// Visit a constructor's or a frame's children: its producer fields then its
/// consumer fields, each under nothing.
///
/// # Specification
/// trivial.
fn fields<Refusal, Each>(
    producers: &[ProducerId],
    consumers: &[ConsumerId],
    each: &mut Each,
) -> Result<(), Refusal>
where
    Each: FnMut(NodeAddress, Opens) -> Result<(), Refusal>,
{
    for &producer in producers {
        each(NodeAddress::Producer(producer), Opens::default())?;
    }
    for &consumer in consumers {
        each(NodeAddress::Consumer(consumer), Opens::default())?;
    }
    Ok(())
}

/// The producer occurrence a producer names itself: a variable's own.
///
/// # Specification
/// trivial.
#[inline]
pub fn producer_named(node: &ProducerNode) -> core::option::IntoIter<(Zone, DeBruijnIndex)>
{
    match *node {
        ProducerNode::Variable { zone, index } => Some((zone, index)),
        ProducerNode::Reify(_)
        | ProducerNode::Primitive { .. }
        | ProducerNode::Constant(_)
        | ProducerNode::Literal(_)
        | ProducerNode::Code(_)
        | ProducerNode::Constructor { .. }
        | ProducerNode::Thunk { .. }
        | ProducerNode::Fixpoint { .. }
        | ProducerNode::Cocase { .. }
        | ProducerNode::Mu { .. } => None,
    }
    .into_iter()
}

/// The covariable a consumer names itself, in the carrier's intuitionistic
/// zone: a covariable's own.
///
/// # Specification
/// trivial.
#[inline]
pub fn consumer_named(node: &ConsumerNode) -> core::option::IntoIter<(Zone, DeBruijnIndex)>
{
    match *node {
        ConsumerNode::Covariable(index) => {
            Some((Zone::Intuitionistic, DeBruijnIndex::from(u32::from(index))))
        },
        ConsumerNode::MuTilde { .. }
        | ConsumerNode::Destructor { .. }
        | ConsumerNode::Case { .. }
        | ConsumerNode::DataCase { .. }
        | ConsumerNode::Select { .. }
        | ConsumerNode::ListFold { .. }
        | ConsumerNode::Top => None,
    }
    .into_iter()
}

/// The producer occurrence a command names itself: the linear slot a memory
/// form lends, ends or consumes.
///
/// # Specification
/// trivial.
#[inline]
pub fn command_named(node: &CommandNode) -> core::option::IntoIter<(Zone, DeBruijnIndex)>
{
    match *node {
        CommandNode::Memory { ref form, .. } => match *form {
            gandr_core_term::memory::MemoryForm::Access { held: index, .. }
            | gandr_core_term::memory::MemoryForm::Consume { held: index }
            | gandr_core_term::memory::MemoryForm::Resume { view: index, .. }
            | gandr_core_term::memory::MemoryForm::Abort { view: index } => {
                Some((Zone::Linear, index))
            },
            gandr_core_term::memory::MemoryForm::Hold { .. } => None,
        },
        CommandNode::Perform { .. }
        | CommandNode::Handle { .. }
        | CommandNode::Resume { .. }
        | CommandNode::Abandon { .. }
        | CommandNode::Reset { .. }
        | CommandNode::Shift { .. }
        | CommandNode::Cut { .. } => None,
    }
    .into_iter()
}

/// The annotations a consumer carries: a fold's element and result types.
///
/// # Specification
/// trivial.
#[inline]
pub fn consumer_annotations(
    node: &ConsumerNode
) -> core::iter::Flatten<core::option::IntoIter<[gandr_core_term::ValueTypeId; 2]>>
{
    match *node {
        ConsumerNode::ListFold {
            element, result, ..
        } => Some([element, result]),
        ConsumerNode::Covariable(_)
        | ConsumerNode::MuTilde { .. }
        | ConsumerNode::Destructor { .. }
        | ConsumerNode::Case { .. }
        | ConsumerNode::DataCase { .. }
        | ConsumerNode::Select { .. }
        | ConsumerNode::Top => None,
    }
    .into_iter()
    .flatten()
}

/// The interface a command carries, whose types are its annotations: an
/// operation's or a handler's.
///
/// # Specification
/// trivial.
#[inline]
pub const fn command_signature(node: &CommandNode) -> Option<&gandr_core_term::effect::EffectSig>
{
    match *node {
        CommandNode::Perform { ref signature, .. } | CommandNode::Handle { ref signature, .. } => {
            Some(signature)
        },
        CommandNode::Resume { .. }
        | CommandNode::Abandon { .. }
        | CommandNode::Reset { .. }
        | CommandNode::Shift { .. }
        | CommandNode::Cut { .. }
        | CommandNode::Memory { .. } => None,
    }
}

mod carried;

#[cfg(test)]
mod tests;
