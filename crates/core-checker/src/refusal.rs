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
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use quenchant_shape::shape::Maybe;

use crate::context::CheckBudget;

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
    /// An eager product `A × B`: what a pair is checked against.
    Product,
    /// A native List, required by nil and cons introductions.
    List,
    /// A static Pi: what a static lambda is checked against.
    StaticPi,
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
    /// A lazy pair needs the two expected computation types.
    With(ComputationId),
    /// A sum injection needs its other summand from the expected type.
    Injection(ValueId),
    /// A native List introduction needs its element classifier.
    List(ValueId),
    /// A sum case is checked against a common result type.
    Case(ComputationId),
    /// A thunk value.
    Thunk(ValueId),
    /// A lambda.
    Lambda(ComputationId),
    /// A return.
    Return(ComputationId),
    /// A fixpoint: its type is the type it is checked at.
    Fixpoint(ComputationId),
    /// A hole: the body of the declaration at this admission position, which
    /// no definition supplies.
    Hole(ConstantIndex),
    /// A static lambda.
    StaticLambda(ValueId),
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
    /// A lazy computation pair or its classifier.
    With,
    /// Observation of a lazy computation pair.
    Project,
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
    /// A case omits or adds constructor branches.
    NonExhaustiveDataCase(ComputationId),
    /// A projection names no field in its operand's record type.
    AbsentRecordField(ComputationId),
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
    /// A data declaration's own family occurs under a function's domain.
    NegativeOccurrence(gandr_kernel_term::OccurrenceSite),
    /// A data declaration's own family occurs inside another former or
    /// another family's arguments.
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
    /// A fixpoint's structural-descent claim does not replay.
    DescentNotReplayed
    {
        /// The fixpoint.
        at: ComputationId,
        /// The first reason the descent walk met.
        reason: gandr_kernel_term::DescentRefusal,
    },
}

impl CheckRefusal
{
    /// Whose fact this refusal records.
    ///
    /// # Specification
    /// - requires: nothing; the function is total over the vocabulary.
    /// - ensures: the class is a function of the variant alone — two refusals
    ///   of one variant classify alike whatever their payloads hold. A type
    ///   mismatch, a shape mismatch, a checking-only form in synthesis
    ///   position, an unknown constant, a sort mismatch, a level mismatch, a
    ///   dependent bind, a family at the wrong arity or with an argument at the
    ///   wrong classifier, a static lambda at a dynamic parameter, a static Pi
    ///   over a type that classifies no codes, an occurrence of a data
    ///   declaration's own family outside a strictly positive, uniform field, a
    ///   reference past its block and a descent claim that does not replay are
    ///   malformed source; a former outside the fragment is unrepresentable; an
    ///   unbound index, an exhausted allowance, a dangling id, an admission out
    ///   of order, a machine invariant and an undecided unfolding are engine
    ///   faults; nothing is a user absence.
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
        | Self::OutOfFragment { .. } => matches!(ret, FailureClass::Unrepresentable),
        | Self::UnboundIndex { .. }
        | Self::BudgetExceeded { .. }
        | Self::DanglingNode { .. }
        | Self::AdmissionOrder { .. }
        | Self::MachineInvariant
        | Self::Undecided { .. } => matches!(ret, FailureClass::EngineFault),
        | Self::PathCode(_)
        | Self::NotADataType(_) | Self::DataKindNotUniverse(_) | Self::DataFieldLevel { .. } | Self::DataArgumentArity(_) | Self::UnknownConstructor { .. } | Self::ConstructorArity(_) | Self::NonExhaustiveDataCase(_) | Self::AbsentRecordField(_) | Self::MissingRecordField { .. }
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
        | Self::NegativeOccurrence(_) | Self::NestedOccurrence(_) | Self::IndexOccurrence(_) | Self::NonUniformOccurrence(_) | Self::CrossBlockReference { .. } | Self::DescentNotReplayed { .. } => matches!(ret, FailureClass::MalformedSource),
    })]
    #[inline]
    #[must_use]
    pub const fn classify(&self) -> FailureClass
    {
        match *self {
            | Self::PathCode(_)
            | Self::NotADataType(_)
            | Self::DataKindNotUniverse(_)
            | Self::DataFieldLevel { .. }
            | Self::DataArgumentArity(_)
            | Self::UnknownConstructor { .. }
            | Self::ConstructorArity(_)
            | Self::NonExhaustiveDataCase(_)
            | Self::AbsentRecordField(_)
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
            | Self::DescentNotReplayed { .. } => FailureClass::MalformedSource,
            | Self::OutOfFragment { .. } => FailureClass::Unrepresentable,
            | Self::UnboundIndex { .. }
            | Self::BudgetExceeded { .. }
            | Self::DanglingNode { .. }
            | Self::AdmissionOrder { .. }
            | Self::MachineInvariant
            | Self::Undecided { .. } => FailureClass::EngineFault,
        }
    }

    /// The types the refusal sets against each other.
    ///
    /// # Specification
    /// - requires: nothing; the function is total over the vocabulary.
    /// - ensures: a type, sort, level or family-argument mismatch expects the
    ///   type it was checked at and found the type it synthesised; a shape
    ///   mismatch found the type it met, a dependent bind or stack the type its
    ///   body synthesised, and a static Pi over no classifier of codes the
    ///   child it stands over, each expecting a former the refusal names rather
    ///   than a type; every other refusal compares no types.
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
    #[spec(ensures: |ret| match *self {
        | Self::TypeMismatch(Mismatch::Value { synthesised, expected, .. })
        | Self::SortMismatch { synthesised, expected, .. }
        | Self::LevelMismatch { synthesised, expected, .. }
        | Self::FamilyArgumentClassifier { synthesised, expected, .. } =>
            ret == Compared { expected: Maybe::Present(TypeNode::Value(expected)), found: Maybe::Present(TypeNode::Value(synthesised)) },
        | Self::TypeMismatch(Mismatch::Computation { synthesised, expected, .. }) =>
            ret == Compared { expected: Maybe::Present(TypeNode::Computation(expected)), found: Maybe::Present(TypeNode::Computation(synthesised)) },
        | Self::ShapeMismatch { found, .. } => ret.found == Maybe::Present(found) && ret.expected == UNNAMED,
        | Self::DependentBind { synthesised, .. } | Self::DependentStack { synthesised, .. } =>
            ret.found == Maybe::Present(TypeNode::Computation(synthesised)) && ret.expected == UNNAMED,
        | Self::StaticClassifierExpected { found, .. } =>
            ret.found == Maybe::Present(TypeNode::Value(found)) && ret.expected == UNNAMED,
        | _ => ret == Compared { expected: UNNAMED, found: UNNAMED },
    })]
    #[inline]
    #[must_use]
    pub fn compared(&self) -> Compared
    {
        let (expected, found) = match *self {
            | Self::TypeMismatch(Mismatch::Value {
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
            } => (
                Maybe::Present(TypeNode::Value(expected)),
                Maybe::Present(TypeNode::Value(synthesised)),
            ),
            | Self::TypeMismatch(Mismatch::Computation {
                synthesised,
                expected,
                ..
            }) => (
                Maybe::Present(TypeNode::Computation(expected)),
                Maybe::Present(TypeNode::Computation(synthesised)),
            ),
            | Self::ShapeMismatch { found, .. } => (UNNAMED, Maybe::Present(found)),
            | Self::DependentBind { synthesised, .. }
            | Self::DependentStack { synthesised, .. } => {
                (UNNAMED, Maybe::Present(TypeNode::Computation(synthesised)))
            },
            | Self::StaticClassifierExpected { found, .. } => {
                (UNNAMED, Maybe::Present(TypeNode::Value(found)))
            },
            | Self::NotADataType(_)
            | Self::DataKindNotUniverse(_)
            | Self::DataFieldLevel { .. }
            | Self::DataArgumentArity(_)
            | Self::UnknownConstructor { .. }
            | Self::ConstructorArity(_)
            | Self::NonExhaustiveDataCase(_)
            | Self::AbsentRecordField(_)
            | Self::MissingRecordField { .. }
            | Self::UnknownOperation { .. }
            | Self::HandlerCoverage { .. }
            | Self::ShiftWithoutReset { .. }
            | Self::PathCode(_)
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
            | Self::FamilyArity { .. }
            | Self::StaticLambdaArgument { .. }
            | Self::NegativeOccurrence(_)
            | Self::NestedOccurrence(_)
            | Self::IndexOccurrence(_)
            | Self::NonUniformOccurrence(_)
            | Self::CrossBlockReference { .. }
            | Self::DescentNotReplayed { .. } => (UNNAMED, UNNAMED),
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
mod tests
{
    use gandr_core_term::CoreArena;
    use quenchant_shape::shape::Maybe;

    use super::CheckRefusal;
    use super::CheckingForm;
    use super::Compared;
    use super::ExpectedShape;
    use super::Mismatch;
    use super::TermNode;
    use super::TypeNode;
    use super::compared;

    #[test]
    fn a_refusal_compares_the_types_it_names()
    {
        let mut arena = CoreArena::new();
        let unit = arena.value_type_unit();
        let list = arena.value_type_list(unit);
        let returns_unit = arena.comp_type_returner(unit);
        let returns_list = arena.comp_type_returner(list);
        let term = arena.value_unit();
        let body = arena.computation_return(term);
        let unnamed = Maybe::Absent(compared::Absent::Unnamed);
        assert_eq!(
            CheckRefusal::TypeMismatch(Mismatch::Value {
                at: term,
                synthesised: list,
                expected: unit,
            })
            .compared(),
            Compared {
                expected: Maybe::Present(TypeNode::Value(unit)),
                found: Maybe::Present(TypeNode::Value(list)),
            },
            "a value mismatch expects the checked type and found the synthesised one"
        );
        assert_eq!(
            CheckRefusal::TypeMismatch(Mismatch::Computation {
                at: body,
                synthesised: returns_list,
                expected: returns_unit,
            })
            .compared(),
            Compared {
                expected: Maybe::Present(TypeNode::Computation(returns_unit)),
                found: Maybe::Present(TypeNode::Computation(returns_list)),
            },
            "a computation mismatch compares computation types"
        );
        assert_eq!(
            CheckRefusal::ShapeMismatch {
                at: TermNode::Value(term),
                wanted: ExpectedShape::Thunk,
                found: TypeNode::Value(unit),
            }
            .compared(),
            Compared {
                expected: unnamed,
                found: Maybe::Present(TypeNode::Value(unit)),
            },
            "a shape mismatch expects a former, not a type"
        );
        assert_eq!(
            CheckRefusal::NotSynthesisable {
                form: CheckingForm::Thunk(term),
            }
            .compared(),
            Compared {
                expected: unnamed,
                found: unnamed,
            },
            "a checking-only form compares nothing"
        );
    }
}
