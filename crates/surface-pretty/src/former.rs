//! The printer's reading of one node, and the trait a caller implements to
//! hand it nodes.
//!
//! The printer never walks an arena of its own choosing. A [`Source`] answers,
//! for each handle, the [`Former`] the node carries and the handles of its
//! children; the printer walks those on its own stack. The core arena is one
//! source ([`crate::CoreSource`]); a table of content nodes a checker hands
//! back is another, implemented beside the face that holds it.
//!
//! # The input is a source
//!
//! The printer asks one question of its input, the former at a node, through
//! the `Source` trait, and reads nothing else. `CoreSource` answers it over the
//! core arena and `ContentSource` over the incremental checker's content
//! tables, the form a checkpoint keeps a signature or a synthesised type in, so
//! every face that reads checkpoints spells their types through one reading.
//!
//! - **Alternatives.** Taking the core arena alone would make a face holding
//!   content tables mint a core arena first, duplicating the checker's own
//!   minting. The content-table reading lived beside the REPL, the one face
//!   that read checkpoints, which kept the incremental tier out of this crate's
//!   dependencies; it moved here when the language server's hover became a
//!   second reader, since a copy per face would let two faces spell one type
//!   differently. The incremental tier is already in every build that prints a
//!   checkpoint's type.
//! - **Reversal.** A second reader needs more than the former per node — a
//!   span, an origin for a binder name — at which point the question widens, or
//!   the per-node dispatch shows in a profile. A build that prints core types
//!   but never reads checkpoints, measured paying for the incremental tier,
//!   moves `ContentSource` behind a feature.

use core::borrow::Borrow;

use anodized::spec;
use gandr_core_term::Sort;
use gandr_core_term::Zone;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::Literal;

/// An effect row as the printer spells it: a capability's authority, operation
/// by operation, or a returner's row, interface by interface.
pub trait Authority: core::fmt::Debug
{
    /// Each granted operation's name, interface by interface, each
    /// interface's in name order.
    ///
    /// # Specification
    /// trivial.
    fn granted(&self) -> alloc::vec::Vec<Name<'_>>;

    /// Each interface's name, in row order.
    ///
    /// # Specification
    /// trivial.
    fn interfaces(&self) -> alloc::vec::Vec<Name<'_>>;
}

impl<Id> Authority for gandr_core_term::effect::EffectRow<Id>
where
    Id: Copy + Eq + core::fmt::Debug + 'static,
{
    /// The operations of every restricted interface, in row order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn granted(&self) -> alloc::vec::Vec<Name<'_>>
    {
        self.signatures()
            .flat_map(|signature| {
                signature
                    .operations()
                    .map(|operation| Name::from(operation.name.as_ref()))
            })
            .collect()
    }

    /// The name of every interface, in row order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn interfaces(&self) -> alloc::vec::Vec<Name<'_>>
    {
        self.signatures()
            .map(|signature| Name::from(signature.name().as_ref()))
            .collect()
    }
}

/// One move of a recorded run as the printer spells it: its action and, for a
/// choice, the label it names.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Move<'text>
{
    /// What the move does.
    pub action: gandr_core_term::session::ActionKind,
    /// The label a selection or an offer names; none for another move.
    pub label: Option<Name<'text>>,
}

/// Where a constructor's name stands to its fields.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: an applied constructor writes its fields as a call's arguments; a
///   consed one is a word's letter, written before the one field it conses
///   onto.
/// - executable: none — the tag holds no constructor to check it against.
///
/// # Adequacy
/// - hypothesis: L3 — a word of two letters spells as a right-nested cons, and
///   an applied constructor as its call.
/// - witness: `tests::goldens::every_value_leaf_spells_as_the_surface_writes_it`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Placement
{
    /// `C(a, …)`, or the bare name with no fields.
    Applied,
    /// `g ∷ p`: a word's letter before the rest of the word.
    Consed,
}

/// The moves of a recorded run, as the printer spells them.
pub trait Moves: core::fmt::Debug
{
    /// Each move, in order.
    ///
    /// # Specification
    /// trivial.
    fn moves(&self) -> alloc::vec::Vec<Move<'_>>;
}

impl<V> Moves for alloc::sync::Arc<[gandr_core_term::session::RecordedMove<V>]>
where
    V: Copy + core::fmt::Debug,
{
    /// Each move's action, and the label of a selection or an offer.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn moves(&self) -> alloc::vec::Vec<Move<'_>>
    {
        self.iter()
            .map(|step| Move {
                action: step.kind(),
                label: match *step {
                    gandr_core_term::session::RecordedMove::Selected(ref label)
                    | gandr_core_term::session::RecordedMove::Offered(ref label) => {
                        Some(Name::from(label.as_ref()))
                    },
                    gandr_core_term::session::RecordedMove::Sent(_)
                    | gandr_core_term::session::RecordedMove::Received(_)
                    | gandr_core_term::session::RecordedMove::Closed => None,
                },
            })
            .collect()
    }
}

/// A name a node carries, as its source spells it: an abstract type's or a
/// constant's.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Name<'text>(&'text str);

impl<'text> From<&'text str> for Name<'text>
{
    /// Reads the text as a name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(text: &'text str) -> Self
    {
        Self(text)
    }
}

impl AsRef<str> for Name<'_>
{
    /// The name's text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        self.0
    }
}

impl Borrow<str> for Name<'_>
{
    /// The name's text, so a set of names answers a lookup by text.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the text the name holds; two names compare as their texts do,
    ///   so the order a set keeps agrees with the order of the texts.
    /// - provides: lookup of a generated binder name among the names a term
    ///   spells.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a generated binder skips the single mentioned name
    ///   through heterogeneous set lookup. Returning altered text changes that
    ///   spelling; arbitrary key sets and Unicode ordering are not enumerated.
    ///   The predicate asks for the held text itself, by address and length,
    ///   which implies equal text without reading it.
    /// - witness: `tests::goldens::a_binder_skips_the_names_the_type_mentions`
    #[spec(ensures: |ret| core::ptr::eq(core::ptr::from_ref(ret), core::ptr::from_ref(self.0)))]
    #[inline]
    fn borrow(&self) -> &str
    {
        self.0
    }
}

/// How many components a product, a sum, a tuple or a record has.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Arity(usize);

impl From<usize> for Arity
{
    /// The arity of `count` components.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: usize) -> Self
    {
        Self(count)
    }
}

impl From<Arity> for usize
{
    /// The number of components.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(arity: Arity) -> Self
    {
        arity.0
    }
}

/// The position of one component of a product, a sum, a tuple or a record,
/// counting from zero; a record's fields count in label order.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Component(usize);

impl From<usize> for Component
{
    /// The component at `position`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: usize) -> Self
    {
        Self(position)
    }
}

impl From<Component> for usize
{
    /// The position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(component: Component) -> Self
    {
        component.0
    }
}

/// One node as the printer reads it: the former, its children as handles of
/// the same source, and the leaf payloads it carries.
///
/// The vocabulary is the core's, read through one lens: every former the
/// printer spells, and the formers it cannot spell named so that the printer
/// writes `?` for them rather than guessing. A computation's formers are
/// spelled only under [`crate::present_computation`], from its root and in the
/// bodies of the thunks it reaches; a type or a value presented alone admits
/// none.
///
/// # Specification
/// - requires: the children are handles of the source that answered.
/// - ensures: each variant is one core former, or one of the two readings a
///   handle can have that is no printable former.
/// - provides: the closed input space of the printer.
/// - panics: none.
/// - executable: none — a former holds opaque child handles, not their source
///   or provenance. Their association with the answering source cannot be
///   observed from this value alone; concrete readers check their conversion.
///
/// # Adequacy
/// - hypothesis: L3 — finite core-backed type and value fixtures distinguish
///   variant selection and child order, while malformed table fixtures expose
///   misplaced and dangling children. Provenance across arbitrary source
///   instances is outside the observations available on a former.
/// - witness: `tests::goldens::every_type_former_spells_as_the_grammar_writes_it`
/// - witness: `tests::goldens::every_value_leaf_spells_as_the_surface_writes_it`
/// - witness: `tests::goldens::misplaced_and_unreadable_nodes_spell_unknown`
#[derive(Clone, Copy, Debug)]
pub enum Former<'source, Node>
{
    /// A flat first-class stack, opaque in value-only presentations.
    Reify,
    /// A stack's ordered input and output computation types.
    Stack(Node, Node),
    /// A lazy pair's two computation types: `&{C, D}`.
    With(Node, Node),
    /// The empty native list.
    ListNil,
    /// A native cell with its head and tail.
    ListCons(Node, Node),
    /// A native universe-path classifier over two quoted codes.
    PathUniverse(Node, Node),
    /// Reflexivity at a quoted code.
    PathRefl(Node),
    /// The two translator programs of an equivalence, evidence omitted.
    PathEquiv(Node, Node),
    /// A componentwise product of paths.
    PathProduct(Node, Node),
    /// A rigid base type: `Integer`, `String`, or the numeric atom.
    BaseType(BaseType),
    /// The product of a value type's components, which the source answers by
    /// [`Source::component`]: `Unit` at arity zero, `#{A, …}` from one.
    Product(Arity),
    /// The sum of a value type's components, which the source answers by
    /// [`Source::component`]: `Void` at arity zero, `+{A, …}` from one.
    Sum(Arity),
    /// A record type of this many fields, which the source answers in label
    /// order by [`Source::component`] and [`Source::label`]: `#{l : A, …}`.
    RecordType(Arity),
    /// The suspension `+U C` of a computation type.
    ThunkType(Node),
    /// The universe of one sort at a level.
    Universe
    {
        /// The family the universe classifies.
        sort: Sort,
        /// The level within that family.
        level: &'source Level,
    },
    /// The value type a code denotes; the code is a value.
    Element(Node),
    /// A sealed abstract type, by its name.
    Abstract(Name<'source>),
    /// The static Pi `A -> B` classifying a type operator, whose codomain
    /// binds nothing.
    StaticPi
    {
        /// The classifier of the operand.
        domain: Node,
        /// The classifier of the result.
        codomain: Node,
    },
    /// The dependent pair `#{x : A, y : B}`, whose second factor binds the
    /// first.
    Sigma
    {
        /// The classifier of the first component.
        first: Node,
        /// The classifier of the second, under the first's binder.
        second: Node,
    },
    /// The capability `Cap {op, …}`, `Cap[1] {op, …}` at the consumable
    /// grade; a scoped region has no spelling.
    Capability
    {
        /// The authority it carries.
        authority: &'source dyn Authority,
        /// How often it may be exercised.
        grade: gandr_core_term::effect::capability::CapabilityGrade,
        /// How long it lives.
        region: gandr_core_term::effect::capability::Region,
    },
    /// A session type: the protocol it reads, the state it stands at, and how
    /// many payload types its sends and receives read, which the source
    /// answers by [`Source::component`] in slot order: `?A. mu t. +{l : S}`.
    Session
    {
        /// The protocol, shared by the session type and its peer's.
        protocol: &'source gandr_core_term::session::Protocol,
        /// The state the session type stands at.
        state: gandr_core_term::session::ProtocolState,
        /// How many payload types the protocol reads.
        payloads: Arity,
    },
    /// The returner `-F A` of a value type.
    Returner(Node),
    /// The returner `-F [I, …] A` of a value type whose computation may
    /// request the interfaces of its row.
    EffectfulReturner
    {
        /// The value returned.
        result: Node,
        /// The row of interfaces.
        effects: &'source dyn Authority,
    },
    /// The arrow `A -> C`, whose codomain binds nothing.
    Arrow
    {
        /// The value-type domain.
        domain: Node,
        /// The computation-type codomain.
        codomain: Node,
    },
    /// The dependent arrow `(x : A) -> C`, whose codomain stands under the
    /// domain's binder.
    Pi
    {
        /// The value-type domain.
        domain: Node,
        /// The computation-type codomain, under the binder.
        codomain: Node,
    },
    /// The computation type a code denotes; the code is a value.
    ComputationElement(Node),
    /// A finite-list type.
    List(Node),
    /// A bound variable.
    Variable
    {
        /// The zone its index counts in.
        zone: Zone,
        /// The index, counting binders outward from the occurrence.
        index: DeBruijnIndex,
    },
    /// A constant, by its name.
    Constant(Name<'source>),
    /// The unit value, `unit`.
    Unit,
    /// A literal.
    Literal(&'source Literal),
    /// A tuple of values, which the source answers by [`Source::component`]:
    /// `#{a, …}` from arity one; the empty tuple is [`Former::Unit`].
    Tuple(Arity),
    /// A record value of this many fields, which the source answers in label
    /// order by [`Source::component`] and [`Source::label`]: `#{.l = a, …}`.
    Record(Arity),
    /// An injection into the summand at this position: `+{.i = v}`.
    Injection(Component, Node),
    /// A suspended computation over its body: `thunk { c }` in a presentation
    /// of a computation, opaque in a presentation of a value.
    Thunk(Node),
    /// The code of a value type: a type read where a value is.
    Quote(Node),
    /// The code of a computation type.
    QuoteComputation(Node),
    /// A static abstraction `\a. v`, its body under one binder.
    StaticLambda(Node),
    /// A static application of an operator to one argument; the printer
    /// spells a spine of them as one application, `f(a, b)`.
    StaticApplication(Node, Node),
    /// Element identity `here(a)`, the reflexivity the surface writes.
    Here(Node),
    /// Function extensionality `funext(f, g)` over its two functions.
    Funext(Node, Node),
    /// Universe equivalence `equiv(f, g)` over its two translators.
    Equiv(Node, Node),
    /// Univalence `ua(e)` over its record; the forward map the core node
    /// carries is derived from the record and never written.
    Univalence(Node),
    /// A session statement, `bisim(a, b)` or `sim(a, b)`, over its two codes.
    SessionRelated(gandr_core_term::session::SessionRelation, Node, Node),
    /// Directed reflexivity `stay(a)`.
    Stay(Node),
    /// Directed composition, `f then g`.
    Then(Node, Node),
    /// The product of two universe flows, `flowProduct(p, q)`.
    FlowProduct(Node, Node),
    /// A forward flow `forward(f)` over its translator.
    Forward(Node),
    /// A function flow `arrow(d, c)` over its domain and codomain flows.
    FunctionFlow(Node, Node),
    /// The recorded runs of a session code, `Run(s)`.
    RunType(Node),
    /// The returner over its value: `v` where a path through a body ends,
    /// `pure v` anywhere else.
    Return(Node),
    /// A sequencing bind over the computation it runs and the rest, which
    /// stands under one binder for the value returned: `run x <- c ; rest`.
    Bind(Node, Node),
    /// A force of a thunk value: `force v`.
    Force(Node),
    /// An application of a computation to one value argument; the printer
    /// spells a spine of them as one call, `f(a, b)`, a forced value at its
    /// head as the value itself.
    Application(Node, Node),
    /// A lambda over its body, which stands under one binder: `fn (x) { c }`.
    Lambda(Node),
    /// A computation written where a value is read, which the checker runs
    /// or suspends as the type there decides: the computation itself, `f(a)`,
    /// its run left out.
    Nested(Node),
    /// A computation run where a value is read, as written: `run c`.
    Run(Node),
    /// Univalence at a stratum, `ua[n, k](a, b, f, g)`, over its two
    /// translator records.
    Ua
    {
        /// The degree and the catalogue bound.
        stratum: gandr_core_term::ua::Stratum,
        /// The source description's name.
        source: Name<'source>,
        /// The target description's name.
        target: Name<'source>,
        /// The forward translator record.
        forward: Node,
        /// The backward translator record.
        backward: Node,
    },
    /// Element identity `Path(A, x, y)`: the carrier and the two endpoints.
    Path
    {
        /// The carrier, a value type.
        carrier: Node,
        /// The left endpoint.
        left: Node,
        /// The right endpoint.
        right: Node,
    },
    /// A data family applied to its arguments, which the source answers by
    /// [`Source::component`]: `List(Nat)`, or the bare name at arity zero.
    Data
    {
        /// The family's name; none where the source cannot name it, spelled
        /// `?` before arguments still spelled.
        name: Option<Name<'source>>,
        /// How many arguments it is applied to.
        arity: Arity,
    },
    /// A constructor applied to its fields, which the source answers by
    /// [`Source::component`]: `Succ(Zero)`, or the bare name with no fields;
    /// a word's letter before the rest of the word, `loop ∷ p`.
    Constructor
    {
        /// The constructor's name; none where the source cannot name it,
        /// spelled `?` before fields still spelled.
        name: Option<Name<'source>>,
        /// How many fields it holds.
        arity: Arity,
        /// Where its name stands to its fields.
        placement: Placement,
        /// The family applied to its arguments, when it takes any: the type a
        /// parameterised constructor is written against, `(C : T)`, which
        /// source that reads back needs.
        classifier: Option<Node>,
    },
    /// Directed identity `Flow(A, x, y)`: the carrier and the two endpoints.
    Flow
    {
        /// The carrier, a value type.
        carrier: Node,
        /// The source endpoint.
        left: Node,
        /// The target endpoint.
        right: Node,
    },
    /// A relation between two types written infix, `A ≃ B`, `A ≅ B` or
    /// `A ⇝ B`: the type the relation abbreviates, spelled as written.
    Relation
    {
        /// Which relation.
        relation: gandr_core_term::identity::Relation,
        /// The left operand: a value type for the equivalence and the
        /// quasi-inverse, the code of one for the flow.
        left: Node,
        /// The right operand, read as the left one is.
        right: Node,
    },
    /// A recorded run, `recorded(sent(v), selected(l), closed)`: its moves in
    /// order, each send's and receive's payload a value the source answers by
    /// [`Source::component`] in move order.
    Recorded
    {
        /// The moves, read for their actions and labels.
        moves: &'source dyn Moves,
        /// How many of them carry a payload.
        payloads: Arity,
    },
    /// The value a computation returns, standing where a value is read: the
    /// computation itself, `n + 1` as `add(n, 1)`.
    Returned(Node),
    /// A saturated native operation over its arguments, which the source
    /// answers by [`Source::component`]: the call `name(a, …)` of the prelude
    /// function it saturates.
    Primitive
    {
        /// The prelude function's name.
        name: Name<'source>,
        /// How many arguments it takes.
        arity: Arity,
    },
    /// Transport along a native universe path, `transport(p, x)`.
    Transport(Node, Node),
    /// Transport along an element path, `transport(\a. M, p, x)`: the
    /// motive, a value type under one binder, the path and the value.
    PathTransport
    {
        /// The motive, under one binder.
        motive: Node,
        /// The path.
        path: Node,
        /// The value transported.
        value: Node,
    },
    /// Transport over a two-entry telescope, `transport(+U M, p, s, q, x)`:
    /// the motive, a computation type whose arrows bind the telescope.
    TelescopeTransport
    {
        /// The motive.
        motive: Node,
        /// The identity in the carrier.
        path: Node,
        /// The family element at the path's source.
        start: Node,
        /// The identity over the path.
        over: Node,
        /// The value transported.
        value: Node,
    },
    /// Transport along a flow, `ride(\a. M, f, x)`: the motive, a value type
    /// under one binder, the flow and the value.
    Ride
    {
        /// The motive, under one binder.
        motive: Node,
        /// The flow.
        flow: Node,
        /// The value moved.
        value: Node,
    },
    /// A fixpoint over its body, which stands under the self binder: `rec f
    /// { c }`.
    Fixpoint(Node),
    /// A sum elimination over its scrutinee and one branch per summand, which
    /// the source answers by [`Source::component`], each under one binder:
    /// `case v { +{.0 = a} => c, … }`.
    Case
    {
        /// The scrutinee.
        scrutinee: Node,
        /// How many branches it has.
        arity: Arity,
    },
    /// A product elimination, its body under one binder per component:
    /// `case v { #{a, b} => c }`.
    Split
    {
        /// The scrutinee.
        scrutinee: Node,
        /// How many components it binds.
        arity: Arity,
        /// The body.
        body: Node,
    },
    /// A nominal elimination over its scrutinee and one branch per
    /// constructor, which the source answers by [`Source::component`] and
    /// names by [`Source::constructor`]: `case n { Zero => c, Succ(m) => d }`.
    DataCase
    {
        /// The scrutinee.
        scrutinee: Node,
        /// How many branches it has.
        arity: Arity,
    },
    /// A record field's projection, `v.l`.
    RecordProjection(Node, Name<'source>),
    /// A tuple component's projection, `v.i`.
    TupleProjection(Node, Component),
    /// A pure right fold of a native list: `fold xs { nil => n, cons(h, r)
    /// => c }`, the cell branch under the head's and the folded result's
    /// binders.
    ListFold
    {
        /// The list folded.
        list: Node,
        /// The empty branch.
        nil: Node,
        /// The cell branch.
        cons: Node,
    },
    /// An operation performed on its payload, `op(v)`.
    Perform
    {
        /// The operation's name.
        operation: Name<'source>,
        /// The payload.
        payload: Node,
    },
    /// A deep handler, `handle { c } with { pure(x) => r, oper op(p, k) => b,
    /// … }`: the subject, the return clause under one binder, and the
    /// operation clauses the source answers by [`Source::component`] and
    /// names by [`Source::label`], each under the payload's and the
    /// resumption's binders.
    Handle
    {
        /// The subject.
        subject: Node,
        /// The return clause.
        on_return: Node,
        /// How many operation clauses it has.
        clauses: Arity,
    },
    /// An operation exercised through a capability, `c.op(v)`.
    Exercise
    {
        /// The capability.
        capability: Node,
        /// The operation's name.
        operation: Name<'source>,
        /// The payload.
        payload: Node,
    },
    /// A capability scope, `handle c : I { c } with { … }`: a handler whose
    /// subject stands under the capability's binder.
    Scope
    {
        /// The handled interface's name.
        interface: Name<'source>,
        /// The subject, under the capability's binder.
        subject: Node,
        /// The return clause.
        on_return: Node,
        /// How many operation clauses it has.
        clauses: Arity,
    },
    /// A computation fed to a first-class stack, `resume(k, c)`.
    Resume(Node, Node),
    /// A delimited-control boundary, `reset { c }`.
    Reset(Node),
    /// A capture to the nearest boundary, its body under the stack's binder:
    /// `shift k { c }`.
    Shift(Node),
    /// A lazy pair of computations, `&{c, d}`.
    Lazy(Node, Node),
    /// A computation checked against the computation type it is ascribed.
    /// The surface writes one only as the bound computation of a typed bind,
    /// `run x : A <- c ; rest`, ascribed `-F A`; the printer spells that bind
    /// whole and any other ascription as its body, approximately.
    Ascription
    {
        /// The computation ascribed.
        body: Node,
        /// The computation type it is checked against.
        ty: Node,
    },
    /// An observation of one component of a lazy pair, `c.0` or `c.1`.
    Project(Component, Node),
    /// A send on a linear endpoint, `send(e, v)`.
    Send
    {
        /// The endpoint, a linear index.
        endpoint: DeBruijnIndex,
        /// The payload.
        payload: Node,
    },
    /// A receive on a linear endpoint, `recv(e)`.
    Receive(DeBruijnIndex),
    /// A selection on a linear endpoint, `select(e, l)`.
    Select
    {
        /// The endpoint, a linear index.
        endpoint: DeBruijnIndex,
        /// The label chosen.
        label: Name<'source>,
    },
    /// An offer on a linear endpoint, `offer(e) { l => c, … }`, one arm per
    /// label, which the source answers by [`Source::component`] and names by
    /// [`Source::label`].
    Offer
    {
        /// The endpoint, a linear index.
        endpoint: DeBruijnIndex,
        /// How many arms it has.
        arms: Arity,
    },
    /// A close of a linear endpoint, `close(e)`.
    Close(DeBruijnIndex),
    /// A fork, `fork (c : S) { t } as d ; u`: the child under its end's
    /// linear binder, the parent under the dual end's.
    Fork
    {
        /// The session type of the child's end.
        protocol: Node,
        /// The child.
        child: Node,
        /// The continuation.
        parent: Node,
    },
    /// A hold, `hold x = v ; t`: the scope under the held slot's linear
    /// binder.
    Hold
    {
        /// The value held.
        value: Node,
        /// The scope.
        body: Node,
    },
    /// An access, `access x as w { t } unwind { u }`: the body under the
    /// view's linear binder.
    Access
    {
        /// The held slot lent, a linear index.
        held: DeBruijnIndex,
        /// The body.
        body: Node,
        /// The unwind.
        unwind: Node,
    },
    /// A view's resume, `resume(w, v)`.
    ResumeView
    {
        /// The view, a linear index.
        view: DeBruijnIndex,
        /// The value written back.
        value: Node,
    },
    /// A view's abort, `abort(w)`.
    AbortView(DeBruijnIndex),
    /// A handle at a world, `A at w`.
    Located
    {
        /// The type of the value the handle names.
        inner: Node,
        /// The world, when the source names it.
        world: Option<Name<'source>>,
    },
    /// A hold of a value at the world it is computed at, `hold v`.
    WorldHold(Node),
    /// A handle opened, `leta x = v ; t`: the rest under the opened value's
    /// binder.
    Leta
    {
        /// The handle.
        value: Node,
        /// The rest.
        body: Node,
    },
    /// A migration, `migrate [w] { t }`.
    Migrate
    {
        /// The world migrated to, when the source names it.
        world: Option<Name<'source>>,
        /// The body run there.
        body: Node,
    },
    /// A node with no former the printer spells, and why.
    Unreadable(Unreadable),
}

/// Why a node reads as no former the printer spells: the honest set, whose
/// every member the printer writes `?`.
///
/// The set is closed and each member names its reason. A core former the
/// surface writes is never here: [`crate::CoreSource`] matches every core
/// former without a wildcard, so a former added to the core fails to compile
/// until it is read as a [`Former`] or named here.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Unreadable
{
    /// A handle that names no node of its source: a malformed source.
    Dangling,
    /// A constant, an abstract type, a data family or a constructor whose
    /// name the source does not hold: a malformed naming table.
    Unnamed,
    /// The unknown value or computation type, what a hole or a mark
    /// synthesises: the checker knows no more.
    UnknownType,
    /// A hole: a term the author has not written.
    Hole,
    /// A mark: a term the elaborator could not type, kept as written.
    Mark,
    /// A universe lift of a type or a value: the core's explicit cumulativity,
    /// which the surface grammar has no syntax for and the checker admits only
    /// where it raises a level.
    Lift,
    /// The numeric base atom: the type of a numeric literal, which the surface
    /// grammar has no name for.
    NumericAtom,
    /// A world's capability: the linear resource a migration spends, which
    /// the checker opens where a run enters and the surface never writes.
    WorldCapability,
}

/// Why the printer wrote `?` at a node: the node read as no former it
/// spells, or the node and its position or its source disagree.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Unspelled
{
    /// The node read as a member of the honest set.
    Unreadable(Unreadable),
    /// A node of a sort its position does not admit.
    Misplaced,
    /// A component or a field label the source does not answer.
    Missing,
    /// A variable past every binder open around it.
    Unbound,
    /// A binder the generated names ran out for.
    Exhausted,
    /// A name a line cannot hold: empty, or holding a line break or a tab.
    Unprintable,
    /// A universe over a sort parameter or at a level that mentions a
    /// variable.
    Universe,
    /// A session type at a state its protocol does not hold.
    Protocol,
    /// A source taking more visits than one presentation makes: a cycle.
    OverBudget,
}

/// A store of nodes the printer can read.
///
/// An implementation answers one node at a time and never walks; the printer
/// carries the walk. A source may be malformed — a dangling handle, a cycle —
/// and the printer stays total over it.
pub trait Source
{
    /// The handle a node is named by.
    type Node: Copy;

    /// The node `node` names, as the printer reads it.
    ///
    /// # Specification
    /// - requires: nothing; any handle is admissible.
    /// - ensures: the former the node carries, with its children as handles of
    ///   this source; [`Former::Unreadable`] for a handle that names no node
    ///   and for a node whose name the source cannot spell.
    /// - provides: the one question the printer asks of its input.
    /// - fails: never; an unreadable node is a variant.
    /// - panics: none.
    /// - executable: none — the trait exposes neither membership nor a
    ///   denotation observer independent of `read`. Repeating `read` cannot
    ///   establish whether the returned former represents the stored node.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — core-backed and table-backed readers expose exact
    ///   constructor spellings, dangling handles and misplaced children. These
    ///   distinguish wrong node classification and absence handling for the
    ///   supplied readers, not arbitrary trait implementations.
    /// - witness: `tests::goldens::every_type_former_spells_as_the_grammar_writes_it`
    /// - witness: `tests::goldens::every_value_leaf_spells_as_the_surface_writes_it`
    /// - witness: `tests::goldens::misplaced_and_unreadable_nodes_spell_unknown`
    fn read(
        &self,
        node: Self::Node,
    ) -> Former<'_, Self::Node>;

    /// The handle of component `index` of the n-ary former `node` names.
    ///
    /// # Specification
    /// - requires: nothing; any handle and any position are admissible.
    /// - ensures: the handle of the component at `index` when [`read`] answers
    ///   a [`Former::Product`], a [`Former::Sum`], a [`Former::Tuple`], a
    ///   [`Former::Record`], a [`Former::RecordType`], a [`Former::Session`], a
    ///   [`Former::Data`], a [`Former::Constructor`], a [`Former::Primitive`],
    ///   a [`Former::Case`], a [`Former::DataCase`], a [`Former::Handle`], a
    ///   [`Former::Scope`] or a [`Former::Offer`] for `node` and `index` is
    ///   below its arity: a record's fields in label order, a session type's
    ///   payloads in slot order, a family's arguments and a constructor's
    ///   fields in telescope order, a primitive's arguments, a case's branches,
    ///   a handler's operation clauses and an offer's arms in order; none
    ///   otherwise.
    /// - provides: the children of an n-ary former, which a [`Former`] counts
    ///   but does not hold.
    /// - fails: never; a missing component is an absence, which the printer
    ///   spells `?`.
    /// - panics: none.
    /// - executable: none — as for [`read`], the trait exposes no observer of
    ///   the stored node independent of its own answers.
    ///
    /// [`read`]: Self::read
    ///
    /// # Adequacy
    /// - hypothesis: L3 — core-backed and table-backed readers answer the
    ///   components of products and sums of arity zero to three, of tuples of
    ///   arity one to three and of records of two fields, in order, and none
    ///   past the arity or for another former; a reversed or shifted component
    ///   changes a golden spelling.
    /// - witness: `tests::goldens::every_type_former_spells_as_the_grammar_writes_it`
    /// - witness: `tests::goldens::n_ary_products_and_sums_spell_between_their_braces`
    /// - witness: `tests::goldens::session_types_spell_their_protocol_and_payloads`
    /// - witness: `tests::goldens::records_spell_their_fields_in_label_order`
    /// - witness: `content_source::tests::value_ty_covers_every_reachable_former`
    fn component(
        &self,
        node: Self::Node,
        index: Component,
    ) -> Option<Self::Node>;

    /// The label of entry `index` of the record, the record type, the
    /// handler or the offer `node` names.
    ///
    /// # Specification
    /// - requires: nothing; any handle and any position are admissible.
    /// - ensures: the label of the entry [`component`] answers at `index` when
    ///   [`read`] answers a [`Former::Record`] or a [`Former::RecordType`] —
    ///   its field's label —, a [`Former::Handle`] or a [`Former::Scope`] — the
    ///   operation its clause answers — or a [`Former::Offer`] — its arm's
    ///   label — for `node` and `index` is below its arity; none otherwise.
    /// - provides: the labels a record's fields, a handler's clauses and an
    ///   offer's arms are written under, which a [`Former`] counts but does not
    ///   hold.
    /// - fails: never; a missing label is an absence, which the printer spells
    ///   `?`.
    /// - panics: none.
    /// - executable: none — as for [`read`].
    ///
    /// [`component`]: Self::component
    /// [`read`]: Self::read
    ///
    /// # Adequacy
    /// - hypothesis: L3 — core-backed records of two fields spell each field
    ///   under its own label, and a handler's clauses each under its operation;
    ///   a shifted or swapped label changes the golden.
    /// - witness: `tests::goldens::records_spell_their_fields_in_label_order`
    /// - witness: `tests::goldens::an_elaborated_body_prints_with_its_exits_elided`
    fn label(
        &self,
        node: Self::Node,
        index: Component,
    ) -> Option<Name<'_>>;

    /// The constructor branch `index` of the data case `node` names matches,
    /// and how many fields it binds.
    ///
    /// # Specification
    /// - requires: nothing; any handle and any position are admissible.
    /// - ensures: the name and the field count of the constructor at tag
    ///   `index` of the family `node`'s scrutinee belongs to, when [`read`]
    ///   answers a [`Former::DataCase`] and the source knows the family; none
    ///   otherwise, which the printer spells `?`. The default knows no family.
    /// - provides: the patterns a data case's branches are written under, which
    ///   the core, matching by tag, does not hold.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — as for [`read`].
    ///
    /// [`read`]: Self::read
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a data case over a family of a nullary and a unary
    ///   constructor spells each branch under its constructor's pattern, its
    ///   field bound; a shifted tag changes the golden.
    /// - witness: `tests::goldens::an_elaborated_body_prints_with_its_exits_elided`
    #[inline]
    fn constructor(
        &self,
        node: Self::Node,
        index: Component,
    ) -> Option<(Name<'_>, Arity)>
    {
        let _ = (node, index);
        None
    }

    /// The names of the intuitionistic binders the presented root stands
    /// under, outermost first; an entry the source cannot name is none.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one entry per binder enclosing the root, so a variable past
    ///   every binder the walk opens reads as the entry it counts out to,
    ///   innermost last. The default is the empty context: a closed root.
    /// - provides: the names of a typed node's context, which a type at a term
    ///   inside a body mentions.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — as for [`read`].
    ///
    /// [`read`]: Self::read
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a type under two named context binders and one
    ///   unnamed spells each free variable by its own binder's name and the
    ///   unnamed one `?`; reversed context order changes the golden.
    /// - witness: `tests::goldens::every_type_former_spells_as_the_grammar_writes_it`
    #[inline]
    fn context(&self) -> &[Option<Name<'_>>]
    {
        &[]
    }

    /// The names of the capability scopes the presented root stands in,
    /// outermost first; an entry the source cannot name is none.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one entry per capability scope enclosing the root, so a
    ///   capability type living in the region at depth `d` reads as the `d`-th
    ///   entry, counted from one. The default is no scope: a root no scope
    ///   encloses.
    /// - provides: the scope a capability type's region names, which a type
    ///   inside a scope's subject mentions.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — as for [`read`].
    ///
    /// [`read`]: Self::read
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a capability in the region of a named scope spells
    ///   `at` that scope's name, and one past the named scopes spells without
    ///   it, approximately.
    /// - witness: `tests::goldens::a_scoped_capability_names_its_scope_400`
    #[inline]
    fn regions(&self) -> &[Option<Name<'_>>]
    {
        &[]
    }

    /// The name the source writes for the one binder `node` opens, when
    /// `node` is a dependent arrow whose binder the source names: the core
    /// carries no name, so a source that keeps one beside the node answers it
    /// here.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the written name, or none; the default names nothing, so
    ///   every binder takes a generated name.
    /// - provides: the name a printed declared type spells its parameters by,
    ///   as the declaration writes them.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — as for [`read`].
    ///
    /// [`read`]: Self::read
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a dependent arrow whose binder the source names
    ///   spells that name at the binder and at every occurrence.
    /// - witness: `tests::goldens::an_arrow_binder_spells_as_the_source_names_it`
    #[inline]
    fn arrow_binder(
        &self,
        node: Self::Node,
    ) -> Option<Name<'_>>
    {
        let _ = node;
        None
    }
}
