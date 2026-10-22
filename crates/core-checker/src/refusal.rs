//! The checker's refusal vocabulary and the classifier every refusal answers
//! to.
//!
//! # Every refusal names the node it is about
//!
//! The checker reads core nodes only, so a refusal names the arena id of the
//! node a rule refused at; the driver resolves that id through the origin table
//! the producer of the terms kept, and the checker learns nothing of spans or
//! names. A refusal about a declaration as a whole names its admission
//! position instead.
//!
//! # Whose fact a refusal is, decided by its variant alone
//!
//! [`CheckRefusal::classify`] sorts every refusal into one of the four classes
//! of [`FailureClass`]. It is a `const`, exhaustive, wildcard-free match that
//! binds no payload, so a classification cannot vary with a node id and a
//! refusal added without a class does not compile.
//!
//! Actual judgements witness each refusal's class. The alternative, a
//! variant-to-class table in the tests, would restate the match rather than
//! observe it; it reverses if a class ever depends on a payload no judgement
//! reaches.
//!
//! A type mismatch, a shape mismatch, a checking form in synthesis position, an
//! unknown constant, a universe of the wrong sort or level, a bind whose type
//! mentions its binder, a static application past its head's arity or at an
//! argument of the wrong classifier, a static lambda handed to a dynamic
//! parameter and a static Pi over a classifier that holds no codes are
//! malformed source, the author's mistake. A former outside the fragment is
//! unimplemented, naming the issue that tracks it. An unbound index, an
//! exhausted allowance, a dangling id, an admission out of order, a sealing
//! site claimed twice, a machine invariant and an unfolding the normaliser did
//! not certify are engine faults: a producer that resolves binders and
//! positions never hands the checker an unbound index or an out-of-order
//! admission, and one that numbers each ascription's abstract components never
//! repeats a site, so each is the producer's fault, not the author's; the
//! machine invariant reports a miscount of the machine's own frames instead of
//! asserting it. An abstract type's kind that is no value universe, a
//! representation above it and an atom naming no admitted abstract type are the
//! author's. The alternative for the unbound index — classing it as the
//! author's — would hide a resolution bug in the producer behind a source
//! diagnostic; it reverses if a producer ever hands over unresolved author
//! text. A session action the endpoint's state does not admit and every break
//! of an endpoint's linear use are the author's, an action naming a linear
//! index no fork or receive bound among them: the linearity refusal is one
//! variant, and the lowering binds every endpoint it names, so that defect is
//! unreachable from source.
//!
//! # The absence class has no refusal, and that is the point
//!
//! The obligation ledger is fed by a declaration's shape — a signature whose
//! body is a hole — through an [`Absence`], never by a refusal, so nothing the
//! checker refuses can be spelled as an obligation. The class stays empty here
//! as it does in the lowering.
//!
//! [`Absence`]: crate::Absence

use anodized::spec;
use gandr_core_term::BinderDepth;
use gandr_core_term::CompTypeId;
use gandr_core_term::ComputationId;
use gandr_core_term::FailureClass;
use gandr_core_term::TrackingIssue;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use quenchant_shape::shape::Maybe;

use crate::context::CheckBudget;
use crate::seal::SealSite;

/// A term node of the core arena.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum TermNode
{
    /// A value node.
    Value(ValueId),
    /// A computation node.
    Computation(ComputationId),
}

/// A type node of the core arena.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum TypeNode
{
    /// A value-type node.
    Value(ValueTypeId),
    /// A computation-type node.
    Computation(CompTypeId),
}

/// Any node of the core arena.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum CoreNode
{
    /// A term node.
    Term(TermNode),
    /// A type node.
    Type(TypeNode),
}

/// The former a rule required of the type it met.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ExpectedShape
{
    /// A nominal datatype classifier.
    Data,
    /// A structural record classifier.
    Record,
    /// A first-class stack from an input computation to an output computation.
    Stack,
    /// A lazy computation pair observed by projection.
    With,
    /// A native universe-path classifier.
    PathUniverse,
    /// An element path type `Path(A, a, b)`: what reflexivity is checked
    /// against and what a transported path must synthesise.
    Path,
    /// A sum classifier.
    Sum,
    /// A thunk type `U C`: what a thunk is checked against and what a forced
    /// value must synthesise.
    Thunk,
    /// A returner `F A`: what a return is checked against.
    Returner,
    /// An arrow `A → C`: what a lambda is checked against and what the head of
    /// an application must synthesise.
    Arrow,
    /// An eager product `A₀ × … × Aₙ`: what a tuple is checked against and
    /// what a tuple projection's operand must synthesise.
    Product,
    /// A dependent pair `Σ (x : A). B`: what a dependent split's scrutinee
    /// must synthesise, and what a pair of other than two components meets.
    Sigma,
    /// A native List, required by nil and cons introductions.
    List,
    /// A static Pi: what a static lambda is checked against.
    StaticPi,
    /// A telescope transport's motive `Π (y : A). Π (z : B). F C`: what the
    /// motive of a transport along a path and an identity over it must be.
    Telescope,
    /// A capability `Cap E`: what an exercised operation's capability must
    /// synthesise.
    Capability,
    /// A session type: what a fork's protocol annotation must denote.
    Session,
    /// A directed identity `Flow(A, a, b)`: what a ride moves along and what
    /// a composite's two flows must synthesise.
    Flow,
    /// A run type `Run(S)` or a prefix type `Prefix(S)`: what a recorded run is
    /// checked against.
    Run,
}

/// A checking-only form, met where a type had to be synthesised.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum CheckingForm
{
    /// A first-class stack literal needs its input and output types.
    Reify(ValueId),
    /// A deep handler needs its answer type.
    Handle(ComputationId),
    /// A reset establishes an answer type from its expected type.
    Reset(ComputationId),
    /// A shift needs the type of the captured continuation.
    Shift(ComputationId),
    /// A lazy product needs its expected computation types.
    With(ComputationId),
    /// A sum injection needs its other summand from the expected type.
    Injection(ValueId),
    /// A native List introduction needs its element classifier.
    List(ValueId),
    /// A sum case or a list case is checked against a common result type.
    Case(ComputationId),
    /// A thunk value.
    Thunk(ValueId),
    /// A lambda.
    Lambda(ComputationId),
    /// A fixpoint: its type is the type it is checked at.
    Fixpoint(ComputationId),
    /// A hole: the body of the declaration at this admission position, which
    /// no definition supplies.
    Hole(ConstantIndex),
    /// A static lambda.
    StaticLambda(ValueId),
    /// A computation written where a value is read: the type expected there
    /// decides whether it is suspended or run, so there is nothing to decide
    /// by without one.
    Nested(ValueId),
    /// An offer is checked against the type its arms share.
    Offer(ComputationId),
    /// A capability scope needs its answer type.
    Scope(ComputationId),
    /// A recorded run is checked against the run type naming its protocol.
    Run(ValueId),
}

/// A former of the core vocabulary the judgement has no rule for.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum UnadmittedFormer
{
    /// An explicit universe lift of a value.
    ValueLift,
    /// A numeric literal.
    NumericLiteral,

    /// The numeric base atom.
    NumericAtom,

    /// A lift of a value type whose target does not lie above the type's
    /// level: the judgement has a rule only for a lift that raises.
    TypeLift,
    /// A sealed abstract type.
    Abstract,
    /// A universe over a sort parameter, which has no ground reading until
    /// the prenex sort binders that would bind it.
    SortParameter,
    /// A universe at the greatest representable level, whose own universe
    /// has no level to stand at.
    TopUniverse,
    /// A static lambda the readmission cannot normalize away: an argument of
    /// a static application whose head no definition unfolds, which the
    /// kernel has no former for.
    StaticLambda,
    /// A nonempty returner effect row, which cannot cross the pure kernel
    /// boundary.
    EffectRow,
    /// A first-class stack literal, outside pure kernel syntax.
    Reify,
    /// A stack classifier, outside pure kernel types.
    Stack,
    /// An operation request.
    Perform,
    /// A deep handler.
    Handle,
    /// Application of a first-class stack.
    Resume,
    /// A delimited-control boundary.
    Reset,
    /// Capture of a delimited continuation.
    Shift,
    /// A capability classifier: authority has no kernel reading.
    Capability,
    /// An operation exercised through a capability.
    Exercise,
    /// A capability scope.
    Scope,
    /// A run type, a recorded run or a ride: runs move by the recorded-run
    /// consumer, and the kernel's lowering of a session flow refuses to run
    /// one.
    Run,
    /// A memory form: the kernel has no store, so a held value and its
    /// accesses stay on the checker's side.
    Memory,
    /// A stage the kernel cannot read: one of a structural fixpoint named in a
    /// term, since the kernel mints its own fixpoints' stages; one naming no
    /// binder of its declaration's signature; or one refining no data type,
    /// which a signature's mark cannot place.
    Stage,
    /// The buffer type: a receive's binder lives on the checker's side, and the
    /// kernel has no buffer.
    Buffer,
    /// Abandonment of a first-class stack.
    Abandon,
}

impl UnadmittedFormer
{
    /// Whose fact the judgement's refusal of this former records.
    ///
    /// # Specification
    /// - requires: nothing; the function is total over the formers.
    /// - ensures: a stage the source places where none stands and a lift that
    ///   does not raise are malformed source; a universe at the greatest
    ///   representable level is an engine fault, the bound being the
    ///   representation's; a numeric literal, the numeric atom, a value lift
    ///   and a universe over a sort parameter are unimplemented, naming the
    ///   holding issue no source reaches past the lowering; every other former
    ///   has a rule in the judgement, so its refusal there is an engine fault.
    /// - provides: the class of [`CheckRefusal::OutOfFragment`].
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every former is pinned to its class by a census row.
    /// - witness: `refusal::tests::each_unadmitted_former_carries_its_pinned_class`
    #[spec(ensures: |ret| match self {
        | Self::Stage | Self::TypeLift => matches!(ret, FailureClass::MalformedSource),
        | Self::NumericLiteral | Self::NumericAtom | Self::ValueLift | Self::SortParameter => matches!(ret, FailureClass::Unimplemented(TrackingIssue::UNFILED)),
        | Self::TopUniverse | Self::Abstract | Self::StaticLambda | Self::EffectRow | Self::Reify | Self::Stack | Self::Perform | Self::Handle | Self::Resume | Self::Reset | Self::Shift | Self::Capability | Self::Exercise | Self::Scope | Self::Run | Self::Memory | Self::Buffer | Self::Abandon => matches!(ret, FailureClass::EngineFault),
    })]
    #[inline]
    #[must_use]
    pub const fn judged(self) -> FailureClass
    {
        match self {
            Self::Stage | Self::TypeLift => FailureClass::MalformedSource,
            Self::NumericLiteral | Self::NumericAtom | Self::ValueLift | Self::SortParameter => {
                FailureClass::Unimplemented(TrackingIssue::UNFILED)
            },
            Self::TopUniverse
            | Self::Abstract
            | Self::StaticLambda
            | Self::EffectRow
            | Self::Reify
            | Self::Stack
            | Self::Perform
            | Self::Handle
            | Self::Resume
            | Self::Reset
            | Self::Shift
            | Self::Capability
            | Self::Exercise
            | Self::Scope
            | Self::Run
            | Self::Memory
            | Self::Buffer
            | Self::Abandon => FailureClass::EngineFault,
        }
    }
}

/// A count of static arguments: how many a static application passes, or how
/// many static Pis a head's type opens.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct StaticArity(u32);

impl From<u32> for StaticArity
{
    /// The arity of a raw count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: u32) -> Self
    {
        Self(count)
    }
}

impl From<StaticArity> for u32
{
    /// The raw count of an arity.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(arity: StaticArity) -> Self
    {
        arity.0
    }
}

/// The position of an argument among a static application's arguments,
/// counted from zero at the argument nearest the head.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ArgumentPosition(u32);

impl From<u32> for ArgumentPosition
{
    /// The position of a raw count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: u32) -> Self
    {
        Self(position)
    }
}

impl From<ArgumentPosition> for u32
{
    /// The raw count of a position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: ArgumentPosition) -> Self
    {
        position.0
    }
}

/// A zero-based position among a recorded run's moves; a count past `u32`
/// saturates.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RunStep(u32);

impl From<u32> for RunStep
{
    /// The step of a raw position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(step: u32) -> Self
    {
        Self(step)
    }
}

impl From<RunStep> for u32
{
    /// The raw position of a step.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(step: RunStep) -> Self
    {
        step.0
    }
}

/// Why a session refuses a recorded run.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum RunFault
{
    /// The move at the step is of another kind or direction than the action
    /// the protocol owes there.
    WrongDirection(RunStep),
    /// The move at the step takes a label the choice there does not name.
    WrongLabel(RunStep),
    /// The move at the step follows the close.
    ResumeAfterEnd(RunStep),
    /// The run stops at the step, its count of moves, without closing.
    Incomplete(RunStep),
    /// An open run rides a flow that narrows an offer: some run of the source
    /// takes a label the target does not offer.
    OfferNarrowed,
}

/// A synthesised type that does not convert to the type it was checked
/// against.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Mismatch
{
    /// At a value: the value bridge.
    Value
    {
        /// The synthesising value checked.
        at: ValueId,
        /// The type it synthesised.
        synthesised: ValueTypeId,
        /// The type it was checked against.
        expected: ValueTypeId,
    },
    /// At a computation: the computation bridge.
    Computation
    {
        /// The synthesising computation checked.
        at: ComputationId,
        /// The type it synthesised.
        synthesised: CompTypeId,
        /// The type it was checked against.
        expected: CompTypeId,
    },
}

/// Why a case over a looped sort is not shown to respect one of its loops.
///
/// # Specification
/// - provides: the reason a loop obligation refuses, beside the loop it names.
/// - panics: none.
/// - executable: none — closed classification.
///
/// # Adequacy
/// - hypothesis: L3 — the circle's contractibility is refused apart, and a case
///   nested over a second looped scrutinee at a fibre that is no path type over
///   a looped sort is refused as no set.
/// - witness: `tests::native_formers::a_case_over_the_circle_owes_its_loop_377`
/// - witness: `tests::native_formers::a_nested_loop_obligation_owes_its_square_off_a_set_464`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum LoopRespect
{
    /// Carried along the loop, the answer at its point does not convert with
    /// that answer.
    Apart,
    /// The answer at the loop's point is a case over another looped
    /// scrutinee, and the case's fibre is not presented as a set: the square
    /// between the two loops is owed, and no rule reads it.
    NotPresentedSet,
}

/// Why the solver bound no solution to the hole a call nominated for an
/// implicit it omits.
///
/// # Specification
/// - provides: the reason an omitted implicit is refused unsolved: nothing
///   constrained it, or the solver's reason for the comparison that waits on
///   it.
/// - panics: none.
/// - executable: none — closed classification.
///
/// # Adequacy
/// - hypothesis: L3 — an implicit no comparison meets is unforced, and one
///   whose only solution names a binder of an argument's own lambda waits on
///   its escape.
/// - witness: `elaboration::tests::an_implicit_no_argument_forces_is_unsolved_1216`
/// - witness: `elaboration::tests::an_implicit_solved_past_its_scope_escapes_1216`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Unsolved
{
    /// No comparison constrained it.
    Unforced,
    /// It met a definition, which only unfolding could decide.
    Unfolding,
    /// It met the unknown type or a hole no call nominated.
    Gradual,
    /// It stands applied to arguments.
    Spine,
    /// It met a former the solver does not decompose.
    Outside,
    /// It met a side of another family.
    Families,
    /// It met a variable or a stuck elimination.
    Neutral,
    /// It met a decode at another level.
    Levels,
    /// Its solution would mention an implicit of a wider context.
    Pruning,
    /// Its solution would name a binder the call does not stand under.
    Escape,
    /// Its solution would mention itself.
    Occurs,
    /// It stands under fewer binders than its context holds.
    Scope,
    /// It met a linear variable.
    Linear,
    /// It met a node the arena does not hold.
    Dangling,
    /// The solver spent its steps before deciding it.
    Budget,
}

impl From<gandr_core_unify::Reason> for Unsolved
{
    /// The solver's reason, without the metavariables it names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(reason: gandr_core_unify::Reason) -> Self
    {
        match reason {
            gandr_core_unify::Reason::Unfolding => Self::Unfolding,
            gandr_core_unify::Reason::Gradual => Self::Gradual,
            gandr_core_unify::Reason::Spine => Self::Spine,
            gandr_core_unify::Reason::Outside => Self::Outside,
            gandr_core_unify::Reason::Families => Self::Families,
            gandr_core_unify::Reason::Neutral => Self::Neutral,
            gandr_core_unify::Reason::Levels => Self::Levels,
            gandr_core_unify::Reason::Pruning { .. } => Self::Pruning,
            gandr_core_unify::Reason::Escape { .. } => Self::Escape,
            gandr_core_unify::Reason::Occurs { .. } => Self::Occurs,
            gandr_core_unify::Reason::Scope { .. } => Self::Scope,
            gandr_core_unify::Reason::Linear => Self::Linear,
            gandr_core_unify::Reason::Dangling => Self::Dangling,
            gandr_core_unify::Reason::Budget => Self::Budget,
        }
    }
}

/// Why the judgement refused a term, a type or a declaration.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum CheckRefusal
{
    /// The nominal identity has no successfully admitted data signature.
    NotADataType(ConstantIndex),
    /// A data declaration's kind is not a value universe.
    DataKindNotUniverse(ValueTypeId),
    /// A constructor field exceeds the declared universe.
    DataFieldLevel
    {
        /// The offending field classifier.
        field: ValueTypeId,
        /// The declaration's universe.
        kind: ValueTypeId,
    },
    /// A data declaration's rules do not present its type: a rule is not
    /// constructor-headed, linear and decreasing over its constructor table.
    RuleNotPresentable
    {
        /// The declaration's universe, which locates the declaration.
        kind: ValueTypeId,
        /// The first rule that does not present the type, and why.
        refusal: gandr_kernel_term::RuleRefusal,
    },
    /// A case over a presented type is not shown to respect one of the type's
    /// rules: under its arms the rule's two sides do not convert, so it might
    /// tell apart two terms the rule identifies.
    RuleNotRespected
    {
        /// The case.
        at: ComputationId,
        /// The first rule the case is not shown to respect.
        rule: gandr_kernel_term::RuleIndex,
        /// The rule's left side, built over one fresh variable per pattern
        /// variable.
        left: ValueId,
        /// The rule's right side, over the same variables.
        right: ValueId,
    },
    /// A case of no branches over a path type whose endpoints are not shown
    /// apart: the apartness rule admits it only between two terms of a data
    /// type whose normal forms first differ at two constructors.
    NotApart
    {
        /// The case.
        at: ComputationId,
        /// Why the endpoints are not apart: they agree, differ only at a
        /// subterm of another type, are open, or the type's rules diverge.
        reason: gandr_kernel_term::Apartness,
    },
    /// A case over a sort its words loop at is not shown to respect one of
    /// the loops: carried along the loop, its answer at the loop's point does
    /// not convert with itself, so it would eliminate the sort as if the loop
    /// were not there; or that answer is a case over another looped scrutinee
    /// at a fibre not presented as a set, where the square is owed.
    LoopNotRespected
    {
        /// The case.
        at: ComputationId,
        /// The first loop the case is not shown to respect, its position
        /// among its words' cells.
        cell: gandr_kernel_term::CellIndex,
        /// The answer at the point carried along the loop.
        left: ComputationId,
        /// The answer at the point.
        right: ComputationId,
        /// Why the loop is not shown respected.
        reason: LoopRespect,
    },
    /// A case's obligation for one of its sort's loops ran past the budget
    /// of the conversion that decides it: unfolding the definitions its sides
    /// run neither met nor parted them in the steps allowed.
    LoopUndecided
    {
        /// The case.
        at: ComputationId,
        /// The loop whose obligation was left undecided, its position among
        /// its words' cells.
        cell: gandr_kernel_term::CellIndex,
    },
    /// An abstract type's kind is not a value universe.
    AbstractKindNotUniverse(ValueTypeId),
    /// A sealed representation forms above its abstract type's universe.
    RepresentationAboveKind
    {
        /// The representation.
        representation: ValueTypeId,
        /// The abstract type's universe.
        kind: ValueTypeId,
    },
    /// A sealed atom names no admitted abstract type: none was declared at
    /// the position, or its declaration was refused.
    NotAnAbstractType(ConstantIndex),
    /// An introduction checked at the identity of a sealed atom whose
    /// interface states its relation and reflexivity but no transport law:
    /// without the law the relation is no identity, so the identity stays
    /// the atom's own neutral fibre and nothing introduces it but
    /// reflexivity.
    AtomTransport
    {
        /// The introduction.
        at: ValueId,
        /// The atom's admission position.
        atom: ConstantIndex,
    },
    /// Two abstract types claimed one sealing site. The producer issues one
    /// site per abstract component of each ascription, so this is its fault.
    SealSiteRepeated(SealSite),
    /// A nominal application supplies the wrong number of parameters.
    DataArgumentArity(ValueTypeId),
    /// The constructor tag is not in the nominal declaration.
    UnknownConstructor
    {
        /// The constructor value.
        at: ValueId,
        /// Its unknown tag.
        tag: gandr_core_term::ConstructorTag,
    },
    /// A constructor supplies the wrong number of fields.
    ConstructorArity(ValueId),
    /// A case scrutinises a value of an indexed family, whose branches would
    /// each learn the index their constructor stands at.
    IndexedCase(ComputationId),
    /// A case omits or adds constructor branches.
    NonExhaustiveDataCase(ComputationId),
    /// A leaf of a match's tree is one of its pattern holes: which arm runs
    /// for some value is left undecided, so the match is not shown to cover
    /// its scrutinee.
    UndecidedCoverage(ComputationId),
    /// A projection names no field in its operand's record type.
    AbsentRecordField(ComputationId),
    /// A tuple projection names a component past its operand's product
    /// arity.
    AbsentTupleComponent(ComputationId),
    /// A record literal lacks a required field.
    MissingRecordField
    {
        /// The record literal.
        at: ValueId,
        /// The required record type.
        expected: ValueTypeId,
    },
    /// A perform names no operation in its supplied interface.
    UnknownOperation
    {
        /// The operation request.
        at: ComputationId,
    },
    /// Handler clauses do not cover the interface exactly once.
    HandlerCoverage
    {
        /// The handler with a missing, repeated or unknown clause.
        at: ComputationId,
    },
    /// A shift has no enclosing reset answer type.
    ShiftWithoutReset
    {
        /// The shift.
        at: ComputationId,
    },
    /// A stack bind's result type depends on the value it binds.
    DependentStack
    {
        /// The stack literal.
        at: ValueId,
        /// The body type before its binder is removed.
        synthesised: CompTypeId,
    },
    /// A native path endpoint was not a quoted closed first-order code.
    PathCode(ValueId),
    /// Reflexivity was checked against a path type whose endpoints its point
    /// does not both convert to.
    EndpointMismatch
    {
        /// The reflexivity.
        at: ValueId,
        /// The path type's left endpoint.
        left: ValueId,
        /// The path type's right endpoint.
        right: ValueId,
    },
    /// A compound endpoint stands for a computation that returns no pure
    /// value: its type is no returner, or its returner performs effects.
    CompoundEndpoint
    {
        /// The compound endpoint.
        at: ValueId,
        /// The type its computation synthesised.
        synthesised: CompTypeId,
    },
    /// A function extensionality past the first-order boundary. The
    /// description-code fragment is first order by a decidability choice, so
    /// every domain the rule decides has a finite kernel coverage: open
    /// functions have free variables no coverage reaches; the classifier must
    /// be a thunk of a pure non-dependent arrow, dependent arrows keeping their
    /// own evaluation; the result and every function argument's domain and
    /// result must be built from the unit type, the base atoms and binary sums
    /// and products, since a function argument over functions would need
    /// function identity between the inputs it is applied at.
    FunextUnsupported
    {
        /// The `funext`.
        at: ValueId,
        /// The type its first function synthesised.
        classifier: ValueTypeId,
    },
    /// A function extensionality whose two functions are not identified: at
    /// some input the coverage reaches they return values that do not convert,
    /// apply their function argument at inputs that do not convert, or neither
    /// return nor apply it. This is the rule's verdict, not a gap.
    PointwiseDistinct
    {
        /// The `funext`.
        at: ValueId,
    },
    /// A universe equivalence the rule does not decide: its translators are
    /// open, its forward classifier is no thunk of a pure non-dependent arrow,
    /// or a code is outside the unit type, the base atoms, sums of at least
    /// one summand, products and lists.
    EquivUnsupported
    {
        /// The `equiv`.
        at: ValueId,
        /// The forward translator's type, or the code the coverage stopped at.
        classifier: ValueTypeId,
    },
    /// A universe equivalence one of whose round trips does not convert at a
    /// list cell whose tail is a fresh variable: the cell is lost, or the
    /// conversion it lacks is the round trip at the tail, which the rule does
    /// not assume; with the tail rigid the two are not told apart.
    UncertifiedStratum
    {
        /// The `equiv`.
        at: ValueId,
        /// The List code whose tail the pattern leaves unobserved.
        code: ValueTypeId,
    },
    /// A universe equivalence one of whose round trips does not return its
    /// input at some pattern the coverage reaches.
    RoundTripDistinct
    {
        /// The `equiv`.
        at: ValueId,
    },
    /// A telescope transport's second identity does not lie over its path: it
    /// does not synthesise the identity, in the family's fibre at the path's
    /// target, from the start transported along the path.
    NotOver
    {
        /// The identity over the path.
        at: ValueId,
        /// The type it synthesised.
        synthesised: ValueTypeId,
        /// The identity over the path the transport owes.
        expected: ValueTypeId,
    },
    /// Univalence at a stratum the checker does not certify: a degree no
    /// shape of the catalogue reaches, a catalogue whose site fails the
    /// corolla or the Segal condition, or a bound past the catalogue it
    /// enumerates.
    UaUncertified
    {
        /// The `ua`.
        at: ValueId,
        /// Why the stratum is not certified.
        stratum: crate::ua::StratumDefect,
    },
    /// Univalence at a certified stratum whose translators are no equivalence
    /// of the two species there.
    UaInequivalent
    {
        /// The `ua`.
        at: ValueId,
        /// What the translators fail.
        defect: crate::ua::UaDefect,
    },
    /// A synthesising term in checking position synthesised a type the expected
    /// type does not convert to.
    TypeMismatch(Mismatch),
    /// Two rows give incompatible operation types to the same effect name.
    EffectSignatureConflict
    {
        /// The sequencing computation.
        at: ComputationId,
        /// The bound computation's type.
        first: CompTypeId,
        /// The continuation's type.
        second: CompTypeId,
    },
    /// A rule met a type of another former than the one it requires: a thunk,
    /// lambda or return checked against the wrong former, a forced value
    /// synthesising no thunk type, or an application head synthesising no
    /// arrow.
    ShapeMismatch
    {
        /// The term whose type lacks the shape.
        at: TermNode,
        /// The former the rule required.
        wanted: ExpectedShape,
        /// The type met instead.
        found: TypeNode,
    },
    /// A checking-only form stands where a type must be synthesised.
    NotSynthesisable
    {
        /// The form.
        form: CheckingForm,
    },
    /// A constant names no declaration the checking context holds a type for:
    /// one not yet admitted, one whose body synthesised nothing, or one the
    /// producer withheld.
    UnknownConstant
    {
        /// The constant value.
        at: ValueId,
        /// The admission position it names.
        constant: ConstantIndex,
    },
    /// A former the judgement has no rule for.
    OutOfFragment
    {
        /// The node carrying the former.
        at: CoreNode,
        /// The former.
        former: UnadmittedFormer,
    },
    /// A variable's index counts past every binder its zone holds. The terms a
    /// lowering produces resolve every binder, so this is the producer's
    /// fault.
    UnboundIndex
    {
        /// The variable.
        at: ValueId,
        /// The zone the index counts in.
        zone: Zone,
        /// The index.
        index: DeBruijnIndex,
        /// The binders the zone held.
        depth: BinderDepth,
    },
    /// The step allowance ran out before the judgement finished.
    BudgetExceeded
    {
        /// The allowance the checking context set.
        budget: CheckBudget,
    },
    /// An id names no node of the arena the checking context reads: the caller
    /// paired terms with another arena.
    DanglingNode
    {
        /// The id.
        node: CoreNode,
    },
    /// A declaration's admission position is not above every position already
    /// admitted, so resolution by position would be unsound.
    AdmissionOrder
    {
        /// The position offered.
        constant: ConstantIndex,
        /// The highest position admitted before it.
        admitted: ConstantIndex,
    },
    /// The machine's own bookkeeping disagreed with itself: a frame received a
    /// result of another kind than it awaits, or the binder stack was not where
    /// the machine left it. Unreachable while the machine's own pushes are the
    /// only source of frames and binders; reported rather than asserted, so a
    /// miscount surfaces as a refusal.
    MachineInvariant,
    /// A code was checked at a universe of the other sort: a value type's code
    /// at a computation universe, or a computation type's at a value universe.
    SortMismatch
    {
        /// The code.
        at: ValueId,
        /// The universe it synthesised, naming its sort and level.
        synthesised: ValueTypeId,
        /// The universe it was checked at.
        expected: ValueTypeId,
    },
    /// A code was checked at a universe of its own sort whose level it does
    /// not fit: above the universe's level, or below a computation universe's,
    /// which no lift of a computation type reaches.
    LevelMismatch
    {
        /// The code.
        at: ValueId,
        /// The universe it synthesised, naming its sort and level.
        synthesised: ValueTypeId,
        /// The universe it was checked at.
        expected: ValueTypeId,
    },
    /// A bind's body synthesised a type that mentions the value the bind
    /// introduced: the binder is opaque to types, so the type has no reading
    /// outside it.
    DependentBind
    {
        /// The bind.
        at: ComputationId,
        /// The type its body synthesised, under the binder.
        synthesised: CompTypeId,
    },
    /// The normaliser's conversion did not certify the unfolding of a code
    /// constant to its body or the static step at a code, which hold by
    /// definition: its budget ran out or its search declined.
    Undecided
    {
        /// The code.
        at: ValueId,
    },
    /// A static application applies its head to more arguments than the
    /// head's static Pis take.
    FamilyArity
    {
        /// The static application, outermost.
        at: ValueId,
        /// How many static Pis the head's type opens.
        expected: StaticArity,
        /// How many arguments the application passes.
        actual: StaticArity,
    },
    /// A static application passes an argument whose classifier is not the
    /// domain of the static Pi it meets.
    FamilyArgumentClassifier
    {
        /// The argument.
        at: ValueId,
        /// Its position among the application's arguments, from zero.
        position: ArgumentPosition,
        /// The classifier it synthesised.
        synthesised: ValueTypeId,
        /// The domain it was passed at.
        expected: ValueTypeId,
    },
    /// A dynamic application passes a type operator that does not normalize
    /// away: a static lambda, or a code that reduces to one, is a value the
    /// kernel would have to type.
    StaticLambdaArgument
    {
        /// The argument.
        at: ValueId,
    },
    /// A static Pi stands over a type that classifies no codes: neither a
    /// universe nor a static Pi at its weak head.
    StaticClassifierExpected
    {
        /// The static Pi.
        at: ValueTypeId,
        /// The child that classifies no codes.
        found: ValueTypeId,
    },
    /// A data declaration's own family occurs under a function's domain where
    /// no stage reaches it: at other arguments, inside a term, or through a
    /// parameter that is not strictly positive.
    NegativeOccurrence(gandr_kernel_term::OccurrenceSite),
    /// A data declaration's own family occurs nested through another family's
    /// parameter that is not strictly positive, or under a former that places
    /// nothing.
    NestedOccurrence(gandr_kernel_term::OccurrenceSite),
    /// A data declaration's own family occurs inside a term a type reads, or
    /// in its own parameter telescope.
    IndexOccurrence(gandr_kernel_term::OccurrenceSite),
    /// A data declaration's own family is applied to arguments other than its
    /// parameter variables in telescope order.
    NonUniformOccurrence(gandr_kernel_term::OccurrenceSite),
    /// A data declaration names an admission position after its own: a
    /// reference outside its block.
    CrossBlockReference
    {
        /// The parameter or field that names it.
        site: gandr_kernel_term::OccurrenceSite,
        /// The later position.
        index: ConstantIndex,
    },
    /// A value checked where the recursion typing wants a stage it does not
    /// stand at or below: a self-reference's argument not strictly below the
    /// fixpoint's stage, a constructor with no recursive field where no value
    /// in scope shows a stage below the one wanted, or a value at no stage
    /// where one is wanted.
    StageNotBelow
    {
        /// The value.
        at: ValueId,
        /// Where it stands.
        found: gandr_kernel_term::Standing,
        /// The stage it was wanted at or below.
        bound: gandr_kernel_term::Stage,
    },
    /// Two arguments of a call show stages for one binder of a definition
    /// quantified over stages that no stage satisfies together.
    StagesDisagree
    {
        /// The argument whose reading the solved stage does not satisfy.
        at: ValueId,
        /// The binder, by its position in the signature.
        binder: gandr_kernel_term::StageBinder,
    },
    /// A session action the session type of its endpoint does not admit.
    SessionMismatch
    {
        /// The action.
        at: ComputationId,
        /// The endpoint it acts on.
        endpoint: crate::session::Endpoint,
        /// The endpoint's session type when it acted.
        state: ValueTypeId,
        /// What the state refuses.
        defect: crate::session::ProtocolDefect,
    },
    /// An endpoint escaped its one linear use: left unconsumed, used after
    /// its close or twice, captured, read as a value, left in two
    /// states by an offer's arms, or a session type outside the linear zone.
    Linearity
    {
        /// The node the discipline breaks at.
        at: CoreNode,
        /// How it breaks.
        defect: crate::session::LinearityDefect,
    },
    /// A held value or a view broke the access discipline: a held value
    /// read or accessed while lent, or captured; a view escaped, left live,
    /// used after its end, or named where no view stands; an unwind that
    /// performs an effect (see [`crate::access`]).
    Access
    {
        /// The node the discipline breaks at.
        at: CoreNode,
        /// How it breaks.
        defect: crate::access::AccessDefect,
    },
    /// A codata declaration or application is refused: its head names no
    /// admitted codata declaration, its kind is no computation universe, it
    /// states no observation, an observation exceeds its universe or names the
    /// declaration off its result, or an application supplies another number
    /// of arguments (see [`crate::codata`]).
    Codata
    {
        /// The declaration's kind, its observation or the application refused.
        at: CoreNode,
        /// Why it is refused.
        fault: crate::codata::CodataFault,
    },
    /// A located judgement broke: a value crossed where its type does not, a
    /// migration found no capability or stands where one may run twice, a
    /// hypothesis was used at another world, or an entry, a world or a
    /// mobility mark does not hold (see [`crate::worlds`]).
    Located
    {
        /// The node the judgement breaks at.
        at: CoreNode,
        /// How it breaks.
        defect: crate::worlds::LocatedDefect,
    },
    /// A computation written where a value is read and run there, with no
    /// computation enclosing it to run before: one in a definition's own
    /// value, or under static content.
    UnenclosedRun
    {
        /// The nested computation or written run.
        at: ValueId,
    },
    /// A call omits an implicit that neither its arguments nor the type it is
    /// checked against determine: the solver bound no solution to the hole
    /// the call nominated for it.
    ImplicitUnsolved
    {
        /// The hole the call nominated.
        at: ValueId,
        /// Why the solver bound it nothing.
        reason: Unsolved,
    },
    /// A term stands at a capability type without being a capability
    /// hypothesis: only a capability the host holds or the binder a
    /// capability scope introduces carries authority, so no term forms one.
    CapabilityForged
    {
        /// The term at the capability type.
        at: ValueId,
        /// The capability type it stands at.
        expected: ValueTypeId,
    },
    /// A capability stands where one granting an operation its own authority
    /// does not grant is expected: authority only narrows.
    CapabilityAmplified(Mismatch),
    /// An operation is exercised through a capability whose authority does
    /// not grant it.
    CapabilityOutsideAuthority
    {
        /// The exercise.
        at: ComputationId,
        /// The capability's type.
        capability: ValueTypeId,
    },
    /// A capability would outlive the scope that introduced it: it stands
    /// where one of a longer region is expected, or a scope's answer type
    /// mentions the scope's own region.
    CapabilityEscaped
    {
        /// The term the capability escapes through.
        at: TermNode,
        /// The type that carries the scoped capability out.
        found: TypeNode,
    },
    /// A consumable capability, which belongs in the linear zone that no
    /// former binds into: it could be neither spent nor kept from being
    /// dropped.
    CapabilityConsumable(ValueTypeId),
    /// A held capability claims authority the host did not grant at the
    /// checker's entry.
    CapabilityUngranted
    {
        /// The held capability's declaration.
        constant: ConstantIndex,
        /// Its declared capability type.
        declared: ValueTypeId,
    },
    /// A bisimilarity statement `bisim(A, B)` whose two sessions are not
    /// bisimilar: some observation of one is no observation of the other.
    SessionNotEquivalent
    {
        /// The statement.
        at: ValueId,
    },
    /// A simulation `sim(A, B)` whose source session is no Gay–Hole subtype of
    /// its target, or a ride along a flow whose sessions are not so related.
    SessionNotSubtype
    {
        /// The statement, or the flow ridden.
        at: ValueId,
    },
    /// A session statement's operand, a run's protocol or a flow endpoint a
    /// run rides from or to that is no closed session code at its protocol's
    /// root.
    SessionCodeExpected
    {
        /// The code.
        at: ValueId,
    },
    /// A session type whose payload reads a binder outside it, formed
    /// anywhere but a run's protocol: a session's payload codes form in the
    /// empty term context, so a payload can name no variable a motive or a
    /// telescope binds around it.
    OpenSessionPayload
    {
        /// The session type.
        at: ValueTypeId,
    },
    /// A ride whose motive reads its code variable anywhere but a covariant
    /// position: a flow moves forward only, so no ride derives its reverse.
    NonCovariantMotive
    {
        /// The ride.
        at: ComputationId,
    },
    /// A ride the checker cannot move: along a flow between distinct session
    /// codes, a motive that is no run over the code — the recorded-run
    /// consumer moves runs, and nothing else crosses a session flow; along a
    /// flow at the value universe, a motive no row of the directed computation
    /// table moves, so no translator computes it.
    RideUnsupported
    {
        /// The ride.
        at: ComputationId,
    },
    /// A recorded run its session does not admit: a literal checked at a
    /// protocol whose moves it breaks, or a run ridden to a target that does
    /// not admit it.
    RunNotAdmitted
    {
        /// The run.
        at: ValueId,
        /// What the session refuses.
        fault: RunFault,
    },
    /// A `forward` the rule does not decide: its translator is open, its
    /// classifier is no thunk of a pure non-dependent arrow, a code is outside
    /// the unit type, the base atoms, sums of at least one summand and
    /// products, or an image the translator computes at a covering input is
    /// not leaf-natural — a literal, a fresh value or a leaf of another type
    /// where the target's shape names a source leaf.
    ForwardUnsupported
    {
        /// The `forward`.
        at: ValueId,
    },
    /// A function flow's boundary that runs against the variance its position
    /// fixes: the domain flow must run from the target's argument code to the
    /// source's, the codomain flow from the source's result code to the
    /// target's.
    Boundary
    {
        /// The boundary flow.
        at: ValueId,
    },
}

impl CheckRefusal
{
    /// Whose fact this refusal records.
    ///
    /// # Specification
    /// - requires: nothing; the function is total over the vocabulary.
    /// - ensures: the class is a function of the variant alone, but for a
    ///   former outside the fragment, whose class is its former's
    ///   ([`UnadmittedFormer::judged`]). A type mismatch, a shape mismatch, a
    ///   checking-only form in synthesis position, an unknown constant, a sort
    ///   mismatch, a level mismatch, a dependent bind, a family at the wrong
    ///   arity or with an argument at the wrong classifier, a static lambda at
    ///   a dynamic parameter, a static Pi over a type that classifies no codes,
    ///   an occurrence of a data declaration's own family outside a strictly
    ///   positive, uniform field, rules that do not present their type, a
    ///   reference past its block, a recursive call whose argument stands below
    ///   no stage its recursion wants, reflexivity at endpoints its point does
    ///   not reach, a compound endpoint that returns no pure value, an abstract
    ///   type's kind that is no universe, a representation above it, an atom
    ///   naming no abstract type, translators that are no equivalence of
    ///   species, a run with no computation enclosing it, a session action its
    ///   endpoint's state refuses, a break of an endpoint's linear use, a
    ///   forged, amplified, escaping, consumable or ungranted capability or one
    ///   exercised outside its authority, sessions that are not bisimilar or
    ///   not related by subtyping, an operand that is no session code, a ride
    ///   whose motive is not covariant, a run its session does not admit and a
    ///   function flow's boundary against its variance are malformed source; a
    ///   case on an indexed family, a function extensionality or a universe
    ///   equivalence or a `forward` the rule does not decide, a list round trip
    ///   reading its tail, univalence at a stratum the checker does not certify
    ///   and a ride the checker does not move are unimplemented, each naming
    ///   the issue tracking it; an unbound index, an exhausted allowance, a
    ///   dangling id, an admission out of order, a repeated sealing site, a
    ///   machine invariant and an undecided unfolding are engine faults;
    ///   nothing is a user absence.
    /// - provides: the fact a report groups by and an exit code reads.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a rejected literal carries its exact mismatch and
    ///   malformed-source class; misclassifying it changes the report rather
    ///   than turning the rejection into an obligation.
    /// - witness: `judgement::tests::a_mismatched_literal_is_refused_with_both_types`
    #[spec(ensures: |ret| match *self {
        | Self::OutOfFragment { former, .. } => ret == former.judged(),
        | Self::IndexedCase(_)
        | Self::FunextUnsupported { .. } | Self::EquivUnsupported { .. } | Self::UncertifiedStratum { .. } | Self::UaUncertified { .. } | Self::RideUnsupported { .. } | Self::ForwardUnsupported { .. } => matches!(ret, FailureClass::Unimplemented(_)),
        | Self::UnboundIndex { .. }
        | Self::BudgetExceeded { .. }
        | Self::DanglingNode { .. }
        | Self::AdmissionOrder { .. }
        | Self::SealSiteRepeated(_)
        | Self::MachineInvariant
        | Self::Undecided { .. }
        | Self::LoopUndecided { .. } => matches!(ret, FailureClass::EngineFault),
        | Self::PathCode(_) | Self::EndpointMismatch { .. } | Self::CompoundEndpoint { .. } | Self::PointwiseDistinct { .. } | Self::RoundTripDistinct { .. } | Self::NotOver { .. } | Self::UaInequivalent { .. }
        | Self::NotADataType(_) | Self::DataKindNotUniverse(_) | Self::DataFieldLevel { .. } | Self::RuleNotPresentable { .. } | Self::RuleNotRespected { .. } | Self::NotApart { .. } | Self::LoopNotRespected { .. } | Self::AbstractKindNotUniverse(_) | Self::RepresentationAboveKind { .. } | Self::NotAnAbstractType(_) | Self::AtomTransport { .. } | Self::DataArgumentArity(_) | Self::UnknownConstructor { .. } | Self::ConstructorArity(_) | Self::NonExhaustiveDataCase(_) | Self::UndecidedCoverage(_) | Self::AbsentRecordField(_) | Self::AbsentTupleComponent(_) | Self::MissingRecordField { .. }
        | Self::TypeMismatch(_)
        | Self::EffectSignatureConflict { .. }
        | Self::UnknownOperation { .. } | Self::HandlerCoverage { .. }
        | Self::ShiftWithoutReset { .. } | Self::DependentStack { .. }
        | Self::ShapeMismatch { .. }
        | Self::NotSynthesisable { .. }
        | Self::UnknownConstant { .. }
        | Self::SortMismatch { .. }
        | Self::LevelMismatch { .. }
        | Self::DependentBind { .. }
        | Self::FamilyArity { .. }
        | Self::FamilyArgumentClassifier { .. }
        | Self::StaticLambdaArgument { .. }
        | Self::StaticClassifierExpected { .. }
        | Self::NegativeOccurrence(_) | Self::NestedOccurrence(_) | Self::IndexOccurrence(_) | Self::NonUniformOccurrence(_) | Self::CrossBlockReference { .. } | Self::StageNotBelow { .. } | Self::StagesDisagree { .. } | Self::UnenclosedRun { .. } | Self::ImplicitUnsolved { .. }
        | Self::SessionMismatch { .. } | Self::Linearity { .. } | Self::Access { .. } | Self::Codata { .. } | Self::Located { .. }
        | Self::CapabilityForged { .. } | Self::CapabilityAmplified(_) | Self::CapabilityOutsideAuthority { .. } | Self::CapabilityEscaped { .. } | Self::CapabilityConsumable(_) | Self::CapabilityUngranted { .. }
        | Self::SessionNotEquivalent { .. } | Self::SessionNotSubtype { .. } | Self::SessionCodeExpected { .. } | Self::OpenSessionPayload { .. } | Self::NonCovariantMotive { .. } | Self::RunNotAdmitted { .. } | Self::Boundary { .. } => matches!(ret, FailureClass::MalformedSource),
    })]
    #[inline]
    #[must_use]
    pub fn classify(&self) -> FailureClass
    {
        match *self {
            Self::PathCode(_)
            | Self::EndpointMismatch { .. }
            | Self::CompoundEndpoint { .. }
            | Self::PointwiseDistinct { .. }
            | Self::RoundTripDistinct { .. }
            | Self::NotOver { .. }
            | Self::UaInequivalent { .. }
            | Self::NotADataType(_)
            | Self::DataKindNotUniverse(_)
            | Self::DataFieldLevel { .. }
            | Self::RuleNotPresentable { .. }
            | Self::RuleNotRespected { .. }
            | Self::NotApart { .. }
            | Self::LoopNotRespected { .. }
            | Self::AbstractKindNotUniverse(_)
            | Self::RepresentationAboveKind { .. }
            | Self::NotAnAbstractType(_)
            | Self::AtomTransport { .. }
            | Self::DataArgumentArity(_)
            | Self::UnknownConstructor { .. }
            | Self::ConstructorArity(_)
            | Self::NonExhaustiveDataCase(_)
            | Self::UndecidedCoverage(_)
            | Self::AbsentRecordField(_)
            | Self::AbsentTupleComponent(_)
            | Self::MissingRecordField { .. }
            | Self::TypeMismatch(_)
            | Self::EffectSignatureConflict { .. }
            | Self::UnknownOperation { .. }
            | Self::HandlerCoverage { .. }
            | Self::ShiftWithoutReset { .. }
            | Self::DependentStack { .. }
            | Self::ShapeMismatch { .. }
            | Self::NotSynthesisable { .. }
            | Self::UnknownConstant { .. }
            | Self::SortMismatch { .. }
            | Self::LevelMismatch { .. }
            | Self::DependentBind { .. }
            | Self::FamilyArity { .. }
            | Self::FamilyArgumentClassifier { .. }
            | Self::StaticLambdaArgument { .. }
            | Self::StaticClassifierExpected { .. }
            | Self::NegativeOccurrence(_)
            | Self::NestedOccurrence(_)
            | Self::IndexOccurrence(_)
            | Self::NonUniformOccurrence(_)
            | Self::CrossBlockReference { .. }
            | Self::StageNotBelow { .. }
            | Self::StagesDisagree { .. }
            | Self::UnenclosedRun { .. }
            | Self::ImplicitUnsolved { .. }
            | Self::SessionMismatch { .. }
            | Self::Linearity { .. }
            | Self::Access { .. }
            | Self::Codata { .. }
            | Self::Located { .. }
            | Self::CapabilityForged { .. }
            | Self::CapabilityAmplified(_)
            | Self::CapabilityOutsideAuthority { .. }
            | Self::CapabilityEscaped { .. }
            | Self::CapabilityConsumable(_)
            | Self::CapabilityUngranted { .. }
            | Self::SessionNotEquivalent { .. }
            | Self::SessionNotSubtype { .. }
            | Self::SessionCodeExpected { .. }
            | Self::OpenSessionPayload { .. }
            | Self::NonCovariantMotive { .. }
            | Self::RunNotAdmitted { .. }
            | Self::Boundary { .. } => FailureClass::MalformedSource,
            Self::IndexedCase(_) => FailureClass::Unimplemented(TrackingIssue::INDEXED),
            Self::OutOfFragment { former, .. } => former.judged(),
            Self::FunextUnsupported { .. } => FailureClass::Unimplemented(TrackingIssue::FUNEXT),
            Self::EquivUnsupported { .. } => FailureClass::Unimplemented(TrackingIssue::EQUIV),
            Self::UncertifiedStratum { .. } => {
                FailureClass::Unimplemented(TrackingIssue::LIST_TAIL)
            },
            Self::UaUncertified { .. } => FailureClass::Unimplemented(TrackingIssue::UNIVALENCE),
            Self::RideUnsupported { .. } => FailureClass::Unimplemented(TrackingIssue::RIDE),
            Self::ForwardUnsupported { .. } => FailureClass::Unimplemented(TrackingIssue::FORWARD),
            Self::UnboundIndex { .. }
            | Self::BudgetExceeded { .. }
            | Self::DanglingNode { .. }
            | Self::AdmissionOrder { .. }
            | Self::SealSiteRepeated(_)
            | Self::MachineInvariant
            | Self::Undecided { .. }
            | Self::LoopUndecided { .. } => FailureClass::EngineFault,
        }
    }

    /// The types the refusal sets against each other.
    ///
    /// # Specification
    /// - requires: nothing; the function is total over the vocabulary.
    /// - ensures: a type, sort, level or family-argument mismatch and an
    ///   amplified capability expect the type it was checked at and found the
    ///   type it synthesised; a shape mismatch found the type it met, a
    ///   dependent bind or stack and a compound endpoint the type its body
    ///   synthesised, a static Pi over no classifier of codes the child it
    ///   stands over, a session action and a leftover endpoint the endpoint's
    ///   session type, and a capability refusal the capability type it met,
    ///   each expecting a former the refusal names rather than a type; a forged
    ///   capability expects the capability type it stood at and found nothing;
    ///   every other refusal compares no types.
    /// - provides: the type nodes a face spells beside the refusal's locus.
    /// - fails: never; a side the refusal sets no type on is the
    ///   [`compared::Absent::Unnamed`] absence.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a value mismatch, a computation mismatch, a shape
    ///   mismatch and a refusal comparing nothing expose each side's node and
    ///   its absence, distinguishing swapped, dropped and invented sides.
    /// - witness: `refusal::tests::a_refusal_compares_the_types_it_names`
    /// - witness: `refusal::tests::each_refusal_naming_types_reports_them_on_its_own_sides`
    #[spec(ensures: |ret| match *self {
        | Self::TypeMismatch(Mismatch::Value { synthesised, expected, .. })
        | Self::CapabilityAmplified(Mismatch::Value { synthesised, expected, .. })
        | Self::SortMismatch { synthesised, expected, .. }
        | Self::LevelMismatch { synthesised, expected, .. }
        | Self::FamilyArgumentClassifier { synthesised, expected, .. }
        | Self::NotOver { synthesised, expected, .. } =>
            ret == Compared { expected: Maybe::Present(TypeNode::Value(expected)), found: Maybe::Present(TypeNode::Value(synthesised)) },
        | Self::TypeMismatch(Mismatch::Computation { synthesised, expected, .. })
        | Self::CapabilityAmplified(Mismatch::Computation { synthesised, expected, .. }) =>
            ret == Compared { expected: Maybe::Present(TypeNode::Computation(expected)), found: Maybe::Present(TypeNode::Computation(synthesised)) },
        | Self::ShapeMismatch { found, .. } | Self::CapabilityEscaped { found, .. } => ret.found == Maybe::Present(found) && ret.expected == UNNAMED,
        | Self::CapabilityForged { expected, .. } => ret.expected == Maybe::Present(TypeNode::Value(expected)) && ret.found == UNNAMED,
        | Self::DependentBind { synthesised, .. } | Self::DependentStack { synthesised, .. } | Self::CompoundEndpoint { synthesised, .. } =>
            ret.found == Maybe::Present(TypeNode::Computation(synthesised)) && ret.expected == UNNAMED,
        | Self::StaticClassifierExpected { found, .. } | Self::FunextUnsupported { classifier: found, .. }
        | Self::CapabilityOutsideAuthority { capability: found, .. } | Self::CapabilityConsumable(found) | Self::CapabilityUngranted { declared: found, .. }
        | Self::EquivUnsupported { classifier: found, .. } | Self::UncertifiedStratum { code: found, .. }
        | Self::SessionMismatch { state: found, .. }
        | Self::Linearity { defect: crate::session::LinearityDefect::Residue { state: found, .. }, .. } =>
            ret.found == Maybe::Present(TypeNode::Value(found)) && ret.expected == UNNAMED,
        | _ => ret == Compared { expected: UNNAMED, found: UNNAMED },
    })]
    #[inline]
    #[must_use]
    pub fn compared(&self) -> Compared
    {
        let (expected, found) = match *self {
            Self::TypeMismatch(Mismatch::Value {
                synthesised,
                expected,
                ..
            })
            | Self::CapabilityAmplified(Mismatch::Value {
                synthesised,
                expected,
                ..
            })
            | Self::SortMismatch {
                synthesised,
                expected,
                ..
            }
            | Self::LevelMismatch {
                synthesised,
                expected,
                ..
            }
            | Self::FamilyArgumentClassifier {
                synthesised,
                expected,
                ..
            }
            | Self::NotOver {
                synthesised,
                expected,
                ..
            } => (
                Maybe::Present(TypeNode::Value(expected)),
                Maybe::Present(TypeNode::Value(synthesised)),
            ),
            Self::TypeMismatch(Mismatch::Computation {
                synthesised,
                expected,
                ..
            })
            | Self::CapabilityAmplified(Mismatch::Computation {
                synthesised,
                expected,
                ..
            }) => (
                Maybe::Present(TypeNode::Computation(expected)),
                Maybe::Present(TypeNode::Computation(synthesised)),
            ),
            Self::ShapeMismatch { found, .. } | Self::CapabilityEscaped { found, .. } => {
                (UNNAMED, Maybe::Present(found))
            },
            Self::CapabilityForged { expected, .. } => {
                (Maybe::Present(TypeNode::Value(expected)), UNNAMED)
            },
            Self::DependentBind { synthesised, .. }
            | Self::DependentStack { synthesised, .. }
            | Self::CompoundEndpoint { synthesised, .. } => {
                (UNNAMED, Maybe::Present(TypeNode::Computation(synthesised)))
            },
            Self::StaticClassifierExpected { found, .. }
            | Self::CapabilityOutsideAuthority {
                capability: found, ..
            }
            | Self::CapabilityConsumable(found)
            | Self::CapabilityUngranted {
                declared: found, ..
            }
            | Self::FunextUnsupported {
                classifier: found, ..
            }
            | Self::EquivUnsupported {
                classifier: found, ..
            }
            | Self::UncertifiedStratum { code: found, .. }
            | Self::SessionMismatch { state: found, .. }
            | Self::Linearity {
                defect: crate::session::LinearityDefect::Residue { state: found, .. },
                ..
            } => (UNNAMED, Maybe::Present(TypeNode::Value(found))),
            Self::NotADataType(_)
            | Self::DataKindNotUniverse(_)
            | Self::DataFieldLevel { .. }
            | Self::RuleNotPresentable { .. }
            | Self::RuleNotRespected { .. }
            | Self::NotApart { .. }
            | Self::LoopNotRespected { .. }
            | Self::AbstractKindNotUniverse(_)
            | Self::RepresentationAboveKind { .. }
            | Self::NotAnAbstractType(_)
            | Self::AtomTransport { .. }
            | Self::SealSiteRepeated(_)
            | Self::DataArgumentArity(_)
            | Self::UnknownConstructor { .. }
            | Self::ConstructorArity(_)
            | Self::IndexedCase(_)
            | Self::NonExhaustiveDataCase(_)
            | Self::UndecidedCoverage(_)
            | Self::AbsentRecordField(_)
            | Self::AbsentTupleComponent(_)
            | Self::MissingRecordField { .. }
            | Self::UnknownOperation { .. }
            | Self::HandlerCoverage { .. }
            | Self::ShiftWithoutReset { .. }
            | Self::PathCode(_)
            | Self::EndpointMismatch { .. }
            | Self::PointwiseDistinct { .. }
            | Self::RoundTripDistinct { .. }
            | Self::UaUncertified { .. }
            | Self::UaInequivalent { .. }
            | Self::EffectSignatureConflict { .. }
            | Self::NotSynthesisable { .. }
            | Self::UnknownConstant { .. }
            | Self::OutOfFragment { .. }
            | Self::UnboundIndex { .. }
            | Self::BudgetExceeded { .. }
            | Self::DanglingNode { .. }
            | Self::AdmissionOrder { .. }
            | Self::MachineInvariant
            | Self::Undecided { .. }
            | Self::LoopUndecided { .. }
            | Self::FamilyArity { .. }
            | Self::StaticLambdaArgument { .. }
            | Self::NegativeOccurrence(_)
            | Self::NestedOccurrence(_)
            | Self::IndexOccurrence(_)
            | Self::NonUniformOccurrence(_)
            | Self::CrossBlockReference { .. }
            | Self::StageNotBelow { .. }
            | Self::StagesDisagree { .. }
            | Self::UnenclosedRun { .. }
            | Self::ImplicitUnsolved { .. }
            | Self::Linearity { .. }
            | Self::Access { .. }
            | Self::Codata { .. }
            | Self::Located { .. }
            | Self::SessionNotEquivalent { .. }
            | Self::SessionNotSubtype { .. }
            | Self::SessionCodeExpected { .. }
            | Self::OpenSessionPayload { .. }
            | Self::NonCovariantMotive { .. }
            | Self::RideUnsupported { .. }
            | Self::RunNotAdmitted { .. }
            | Self::ForwardUnsupported { .. }
            | Self::Boundary { .. } => (UNNAMED, UNNAMED),
        };
        Compared { expected, found }
    }
}

quenchant_shape::reason_enum! {
    /// Why a refusal names no type on one side of a comparison.
    pub mod compared {
        /// The reason a side is empty.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The refusal sets no type on this side: it names a former, or
            /// nothing to compare.
            Unnamed,
        }
    }
}

/// No type on a side of a comparison.
const UNNAMED: Maybe<TypeNode, compared::Absent> = Maybe::Absent(compared::Absent::Unnamed);

/// The types a refusal sets against each other: the one its rule expected and
/// the one it found.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Compared
{
    /// The type the rule required.
    pub expected: Maybe<TypeNode, compared::Absent>,
    /// The type the rule met.
    pub found: Maybe<TypeNode, compared::Absent>,
}

#[cfg(test)]
mod tests;
