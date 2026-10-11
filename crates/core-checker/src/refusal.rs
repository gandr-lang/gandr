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
    /// A static Pi: what a static lambda is checked against.
    StaticPi,
}

/// A checking-only form, met where a type had to be synthesised.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum CheckingForm
{
    /// A sum injection needs its other summand from the expected type.
    Injection(ValueId),
    /// A sum case is checked against a common result type.
    Case(ComputationId),
    /// A thunk value.
    Thunk(ValueId),
    /// A lambda.
    Lambda(ComputationId),
    /// A return.
    Return(ComputationId),
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
    /// A native path endpoint was not a quoted closed first-order code.
    PathCode(ValueId),
    /// A synthesising term in checking position synthesised a type the expected
    /// type does not convert to.
    TypeMismatch(Mismatch),
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
    ///   wrong classifier, a static lambda at a dynamic parameter and a static
    ///   Pi over a type that classifies no codes are malformed source; a former
    ///   outside the fragment is unrepresentable; an unbound index, an
    ///   exhausted allowance, a dangling id, an admission out of order, a
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
        | Self::ShapeMismatch { .. }
        | Self::NotSynthesisable { .. }
        | Self::UnknownConstant { .. }
        | Self::SortMismatch { .. }
        | Self::LevelMismatch { .. }
        | Self::DependentBind { .. }
        | Self::FamilyArity { .. }
        | Self::FamilyArgumentClassifier { .. }
        | Self::StaticLambdaArgument { .. }
        | Self::StaticClassifierExpected { .. } => matches!(ret, FailureClass::MalformedSource),
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
            | Self::ShapeMismatch { .. }
            | Self::NotSynthesisable { .. }
            | Self::UnknownConstant { .. }
            | Self::SortMismatch { .. }
            | Self::LevelMismatch { .. }
            | Self::DependentBind { .. }
            | Self::FamilyArity { .. }
            | Self::FamilyArgumentClassifier { .. }
            | Self::StaticLambdaArgument { .. }
            | Self::StaticClassifierExpected { .. } => FailureClass::MalformedSource,
            | Self::OutOfFragment { .. } => FailureClass::Unrepresentable,
            | Self::UnboundIndex { .. }
            | Self::BudgetExceeded { .. }
            | Self::DanglingNode { .. }
            | Self::AdmissionOrder { .. }
            | Self::MachineInvariant
            | Self::Undecided { .. } => FailureClass::EngineFault,
        }
    }
}
