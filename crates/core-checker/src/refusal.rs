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
    /// A sum injection.
    Injection,
    /// An explicit universe lift of a value.
    ValueLift,
    /// A numeric literal.
    NumericLiteral,
    /// A sum elimination.
    Case,
    /// The numeric base atom.
    NumericAtom,
    /// The sum type.
    Sum,
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
    /// - hypothesis: L3 — the vocabulary is a finite class, enumerated
    ///   exhaustively against a pinned class table; payload blindness is
    ///   separated by two inhabitants of one variant differing in every payload
    ///   field, asserted to classify alike.
    /// - witness: `refusal::tests::every_refusal_carries_its_pinned_class`
    /// - witness: `refusal::tests::the_classification_ignores_the_payload`
    /// - witness: `refusal::tests::the_absence_class_has_no_inhabitant`
    #[inline]
    #[must_use]
    pub const fn classify(&self) -> FailureClass
    {
        match *self {
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

#[cfg(test)]
mod tests
{
    use gandr_core_term::BinderDepth;
    use gandr_core_term::CoreArena;
    use gandr_core_term::FailureClass;
    use gandr_core_term::Zone;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;

    use super::ArgumentPosition;
    use super::CheckRefusal;
    use super::CheckingForm;
    use super::CoreNode;
    use super::ExpectedShape;
    use super::Mismatch;
    use super::StaticArity;
    use super::TermNode;
    use super::TypeNode;
    use super::UnadmittedFormer;
    use crate::context::CheckBudget;

    /// One inhabitant of every variant beside the class it must carry, and a
    /// second inhabitant of every variant that carries a payload, differing in
    /// every payload field.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one row per variant of [`CheckRefusal`], in declaration
    ///   order; the variant set is pinned by the exhaustive match in
    ///   `every_refusal_carries_its_pinned_class`.
    /// - provides: the table both classification witnesses read.
    /// - panics: none.
    fn table() -> [(CheckRefusal, CheckRefusal, FailureClass); 18]
    {
        let mut arena = CoreArena::new();
        let first_value = arena.value_unit();
        let second_value = arena.value_unit();
        let first_comp = arena.computation_return(first_value);
        let second_comp = arena.computation_return(second_value);
        let first_type = arena.value_type_unit();
        let second_type = arena.value_type_base(BaseType::Integer);
        let first_comp_type = arena.comp_type_returner(first_type);
        let second_comp_type = arena.comp_type_returner(second_type);
        let zero = ConstantIndex::from(0_usize);
        let one = ConstantIndex::from(1_usize);
        [
            (
                CheckRefusal::TypeMismatch(Mismatch::Value {
                    at: first_value,
                    synthesised: first_type,
                    expected: second_type,
                }),
                CheckRefusal::TypeMismatch(Mismatch::Computation {
                    at: second_comp,
                    synthesised: second_comp_type,
                    expected: first_comp_type,
                }),
                FailureClass::MalformedSource,
            ),
            (
                CheckRefusal::ShapeMismatch {
                    at: TermNode::Value(first_value),
                    wanted: ExpectedShape::Thunk,
                    found: TypeNode::Value(first_type),
                },
                CheckRefusal::ShapeMismatch {
                    at: TermNode::Computation(second_comp),
                    wanted: ExpectedShape::Arrow,
                    found: TypeNode::Computation(second_comp_type),
                },
                FailureClass::MalformedSource,
            ),
            (
                CheckRefusal::NotSynthesisable {
                    form: CheckingForm::Thunk(first_value),
                },
                CheckRefusal::NotSynthesisable {
                    form: CheckingForm::Hole(one),
                },
                FailureClass::MalformedSource,
            ),
            (
                CheckRefusal::UnknownConstant {
                    at: first_value,
                    constant: zero,
                },
                CheckRefusal::UnknownConstant {
                    at: second_value,
                    constant: one,
                },
                FailureClass::MalformedSource,
            ),
            (
                CheckRefusal::OutOfFragment {
                    at: CoreNode::Term(TermNode::Value(first_value)),
                    former: UnadmittedFormer::Injection,
                },
                CheckRefusal::OutOfFragment {
                    at: CoreNode::Type(TypeNode::Value(second_type)),
                    former: UnadmittedFormer::SortParameter,
                },
                FailureClass::Unrepresentable,
            ),
            (
                CheckRefusal::UnboundIndex {
                    at: first_value,
                    zone: Zone::Intuitionistic,
                    index: DeBruijnIndex::from(0_u32),
                    depth: BinderDepth::from(0_usize),
                },
                CheckRefusal::UnboundIndex {
                    at: second_value,
                    zone: Zone::Linear,
                    index: DeBruijnIndex::from(3_u32),
                    depth: BinderDepth::from(2_usize),
                },
                FailureClass::EngineFault,
            ),
            (
                CheckRefusal::BudgetExceeded {
                    budget: CheckBudget::from(1_usize),
                },
                CheckRefusal::BudgetExceeded {
                    budget: CheckBudget::DEFAULT,
                },
                FailureClass::EngineFault,
            ),
            (
                CheckRefusal::DanglingNode {
                    node: CoreNode::Term(TermNode::Computation(first_comp)),
                },
                CheckRefusal::DanglingNode {
                    node: CoreNode::Type(TypeNode::Value(second_type)),
                },
                FailureClass::EngineFault,
            ),
            (
                CheckRefusal::AdmissionOrder {
                    constant: zero,
                    admitted: zero,
                },
                CheckRefusal::AdmissionOrder {
                    constant: zero,
                    admitted: one,
                },
                FailureClass::EngineFault,
            ),
            (
                CheckRefusal::MachineInvariant,
                CheckRefusal::MachineInvariant,
                FailureClass::EngineFault,
            ),
            (
                CheckRefusal::SortMismatch {
                    at: first_value,
                    synthesised: first_type,
                    expected: second_type,
                },
                CheckRefusal::SortMismatch {
                    at: second_value,
                    synthesised: second_type,
                    expected: first_type,
                },
                FailureClass::MalformedSource,
            ),
            (
                CheckRefusal::LevelMismatch {
                    at: first_value,
                    synthesised: first_type,
                    expected: second_type,
                },
                CheckRefusal::LevelMismatch {
                    at: second_value,
                    synthesised: second_type,
                    expected: first_type,
                },
                FailureClass::MalformedSource,
            ),
            (
                CheckRefusal::DependentBind {
                    at: first_comp,
                    synthesised: first_comp_type,
                },
                CheckRefusal::DependentBind {
                    at: second_comp,
                    synthesised: second_comp_type,
                },
                FailureClass::MalformedSource,
            ),
            (
                CheckRefusal::Undecided { at: first_value },
                CheckRefusal::Undecided { at: second_value },
                FailureClass::EngineFault,
            ),
            (
                CheckRefusal::FamilyArity {
                    at: first_value,
                    expected: StaticArity::from(1_u32),
                    actual: StaticArity::from(2_u32),
                },
                CheckRefusal::FamilyArity {
                    at: second_value,
                    expected: StaticArity::from(0_u32),
                    actual: StaticArity::from(3_u32),
                },
                FailureClass::MalformedSource,
            ),
            (
                CheckRefusal::FamilyArgumentClassifier {
                    at: first_value,
                    position: ArgumentPosition::from(0_u32),
                    synthesised: first_type,
                    expected: second_type,
                },
                CheckRefusal::FamilyArgumentClassifier {
                    at: second_value,
                    position: ArgumentPosition::from(1_u32),
                    synthesised: second_type,
                    expected: first_type,
                },
                FailureClass::MalformedSource,
            ),
            (
                CheckRefusal::StaticLambdaArgument { at: first_value },
                CheckRefusal::StaticLambdaArgument { at: second_value },
                FailureClass::MalformedSource,
            ),
            (
                CheckRefusal::StaticClassifierExpected {
                    at: first_type,
                    found: second_type,
                },
                CheckRefusal::StaticClassifierExpected {
                    at: second_type,
                    found: first_type,
                },
                FailureClass::MalformedSource,
            ),
        ]
    }

    #[test]
    fn every_refusal_carries_its_pinned_class()
    {
        let mut covered = [false; 18];
        for (refusal, _, class) in table() {
            let row = match refusal {
                | CheckRefusal::TypeMismatch(_) => 0_usize,
                | CheckRefusal::ShapeMismatch { .. } => 1_usize,
                | CheckRefusal::NotSynthesisable { .. } => 2_usize,
                | CheckRefusal::UnknownConstant { .. } => 3_usize,
                | CheckRefusal::OutOfFragment { .. } => 4_usize,
                | CheckRefusal::UnboundIndex { .. } => 5_usize,
                | CheckRefusal::BudgetExceeded { .. } => 6_usize,
                | CheckRefusal::DanglingNode { .. } => 7_usize,
                | CheckRefusal::AdmissionOrder { .. } => 8_usize,
                | CheckRefusal::MachineInvariant => 9_usize,
                | CheckRefusal::SortMismatch { .. } => 10_usize,
                | CheckRefusal::LevelMismatch { .. } => 11_usize,
                | CheckRefusal::DependentBind { .. } => 12_usize,
                | CheckRefusal::Undecided { .. } => 13_usize,
                | CheckRefusal::FamilyArity { .. } => 14_usize,
                | CheckRefusal::FamilyArgumentClassifier { .. } => 15_usize,
                | CheckRefusal::StaticLambdaArgument { .. } => 16_usize,
                | CheckRefusal::StaticClassifierExpected { .. } => 17_usize,
            };
            covered[row] = true;
            assert_eq!(
                refusal.classify(),
                class,
                "{refusal:?} must classify as {class}"
            );
        }
        assert_eq!(covered, [true; 18], "the table names every variant once");
    }

    #[test]
    fn the_classification_ignores_the_payload()
    {
        for (first, second, _) in table() {
            assert_eq!(
                first.classify(),
                second.classify(),
                "two inhabitants of one variant classify alike: {first:?} and {second:?}"
            );
        }
    }

    #[test]
    fn the_absence_class_has_no_inhabitant()
    {
        for (refusal, ..) in table() {
            assert_ne!(
                refusal.classify(),
                FailureClass::UserAbsence,
                "no refusal may become an obligation: {refusal:?}"
            );
        }
    }
}
