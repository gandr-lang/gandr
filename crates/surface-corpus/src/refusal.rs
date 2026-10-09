//! The closed refusal vocabulary a `refuses` payload names, the corpus's own
//! refusal, and one view over the refusals of every producer.
//!
//! # A refusal is named by its variant
//!
//! [`RefusalName`] holds one name per refusal variant the lowering, the
//! checker and this crate raise, spelled as the variant is. A payload is
//! matched byte for byte: no case folding, no trimming, no prefix match, so a
//! near miss names nothing and the expectation that wrote it fails rather
//! than passing on a guess. The lowering and the checker each have an
//! `OutOfFragment` and a `BudgetExceeded`; each pair is one name, because an
//! expectation states which refusal a declaration carries, not which pass
//! noticed it.
//!
//! # The vocabulary follows the producers
//!
//! The maps from each producer's refusals to their names are exhaustive,
//! wildcard-free matches, so a refusal variant added upstream fails to compile
//! here until it is named.

use core::error::Error;
use core::fmt;

use gandr_core_checker::CheckRefusal;
use gandr_core_term::FailureClass;
use gandr_kernel_term::StringLiteral;
use gandr_surface_lowering::LoweringRefusal;
use gandr_surface_syntax::ByteSpan;
use quenchant_shape::shape::Maybe;

use crate::expectation::ExpectationSchema;

quenchant_shape::reason_enum! {
    /// Why a spelling names no refusal.
    pub mod refusal_name {
        /// The vocabulary holds no refusal spelled so.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No refusal of the vocabulary is spelled byte for byte as the
            /// payload is.
            Unnamed,
        }
    }
}

/// The refusal this crate raises.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum CorpusRefusal
{
    /// An `owes` or `refuses` attribute on a declaration under the strict
    /// root, which admits `checks` alone.
    ExpectationOutsideFixtureRoot
    {
        /// The schema the attribute names.
        schema: ExpectationSchema,
        /// The bytes the attribute covers.
        span: ByteSpan,
    },
}

impl CorpusRefusal
{
    /// Whose fact this refusal records.
    ///
    /// # Specification
    /// - requires: nothing; the function is total over the vocabulary.
    /// - ensures: [`FailureClass::MalformedSource`] for every variant: the
    ///   author wrote an expectation where the root admits none.
    /// - provides: the class a report counts the refusal under.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one variant, asserted at its pinned class in the
    ///   vocabulary table.
    /// - witness: `refusal::tests::every_refusal_is_named_by_its_variant`
    #[inline]
    #[must_use]
    pub const fn classify(&self) -> FailureClass
    {
        match *self {
            | Self::ExpectationOutsideFixtureRoot { .. } => FailureClass::MalformedSource,
        }
    }
}

impl fmt::Display for CorpusRefusal
{
    /// Writes the refusal and the attribute it refuses.
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
            | Self::ExpectationOutsideFixtureRoot { schema, span } => write!(
                f,
                "`{schema}` at {span} states an expectation the strict root refuses; only `checks` is admitted outside the fixture root"
            ),
        }
    }
}

impl Error for CorpusRefusal
{
}

/// The spelling of a refusal name, as a `refuses` payload writes it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RefusalSpelling(&'static str);

impl AsRef<str> for RefusalSpelling
{
    /// The spelling's text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        self.0
    }
}

impl fmt::Display for RefusalSpelling
{
    /// Writes the spelling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(self.0)
    }
}

/// One name of the closed refusal vocabulary: every refusal the lowering, the
/// checker and this crate raise, named by its variant.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum RefusalName
{
    /// A term name no binder or earlier declaration answers.
    UnresolvedName,
    /// A type head no table entry answers.
    UnresolvedTypeHead,
    /// A second signature for one name.
    DuplicateSignature,
    /// A second definition for one name.
    DuplicateDefinition,
    /// A second import of one alias.
    DuplicateImportAlias,
    /// A declared name or binder over a builtin, under the reject policy.
    ShadowedBuiltin,
    /// A form the fragment does not admit, from the lowering or the checker.
    OutOfFragment,
    /// A literal whose text is not a lexeme of its kind.
    MalformedLiteral,
    /// A form whose pieces fall short of its rule.
    MalformedForm,
    /// An attribute name the registry does not hold.
    UnknownAttribute,
    /// One attribute written twice for one name.
    DuplicateAttribute,
    /// An attribute whose schema takes a payload, written with none.
    MissingPayload,
    /// An attribute payload that is not a value.
    NonValuePayload,
    /// An attribute payload whose form its schema does not admit.
    IllTypedPayload,
    /// A work allowance ran out, the lowering's or the checker's.
    BudgetExceeded,
    /// A tree lowered under another grammar than it was molded under.
    GrammarMismatch,
    /// A mold the grammar's table does not hold.
    UnknownMold,
    /// A synthesised type that does not convert to the expected one.
    TypeMismatch,
    /// A type of another former than the rule requires.
    ShapeMismatch,
    /// A checking-only form where a type must be synthesised.
    NotSynthesisable,
    /// A constant naming no declaration the checker holds a type for.
    UnknownConstant,
    /// A variable index past every binder of its zone.
    UnboundIndex,
    /// An id naming no node of the arena the checker reads.
    DanglingNode,
    /// A declaration offered out of admission order.
    AdmissionOrder,
    /// The checking machine's bookkeeping disagreed with itself.
    MachineInvariant,
    /// A code checked at a universe of the other sort.
    SortMismatch,
    /// A code checked at a universe of its sort it does not fit.
    LevelMismatch,
    /// A bind whose body's type mentions the bound name.
    DependentBind,
    /// A code constant's unfolding the normaliser did not certify.
    Undecided,
    /// An expectation the strict root refuses.
    ExpectationOutsideFixtureRoot,
}

impl RefusalName
{
    /// Every name of the vocabulary, in declaration order.
    pub const VOCABULARY: [Self; 30_usize] = [
        Self::UnresolvedName,
        Self::UnresolvedTypeHead,
        Self::DuplicateSignature,
        Self::DuplicateDefinition,
        Self::DuplicateImportAlias,
        Self::ShadowedBuiltin,
        Self::OutOfFragment,
        Self::MalformedLiteral,
        Self::MalformedForm,
        Self::UnknownAttribute,
        Self::DuplicateAttribute,
        Self::MissingPayload,
        Self::NonValuePayload,
        Self::IllTypedPayload,
        Self::BudgetExceeded,
        Self::GrammarMismatch,
        Self::UnknownMold,
        Self::TypeMismatch,
        Self::ShapeMismatch,
        Self::NotSynthesisable,
        Self::UnknownConstant,
        Self::UnboundIndex,
        Self::DanglingNode,
        Self::AdmissionOrder,
        Self::MachineInvariant,
        Self::SortMismatch,
        Self::LevelMismatch,
        Self::DependentBind,
        Self::Undecided,
        Self::ExpectationOutsideFixtureRoot,
    ];

    /// The name as a `refuses` payload spells it: the name of the variant it
    /// names.
    ///
    /// # Specification
    /// - requires: nothing; the function is total over the vocabulary.
    /// - ensures: each name's spelling is its own variant's identifier, and no
    ///   two names share one.
    /// - provides: the one spelling a payload is matched against and a report
    ///   writes.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the vocabulary is a finite class, every name reached
    ///   from a producer's refusal and asserted at its exact spelling, so a
    ///   swapped or misspelt arm breaks its row.
    /// - witness: `refusal::tests::every_refusal_is_named_by_its_variant`
    #[inline]
    #[must_use]
    pub const fn spelling(self) -> RefusalSpelling
    {
        RefusalSpelling(match self {
            | Self::UnresolvedName => "UnresolvedName",
            | Self::UnresolvedTypeHead => "UnresolvedTypeHead",
            | Self::DuplicateSignature => "DuplicateSignature",
            | Self::DuplicateDefinition => "DuplicateDefinition",
            | Self::DuplicateImportAlias => "DuplicateImportAlias",
            | Self::ShadowedBuiltin => "ShadowedBuiltin",
            | Self::OutOfFragment => "OutOfFragment",
            | Self::MalformedLiteral => "MalformedLiteral",
            | Self::MalformedForm => "MalformedForm",
            | Self::UnknownAttribute => "UnknownAttribute",
            | Self::DuplicateAttribute => "DuplicateAttribute",
            | Self::MissingPayload => "MissingPayload",
            | Self::NonValuePayload => "NonValuePayload",
            | Self::IllTypedPayload => "IllTypedPayload",
            | Self::BudgetExceeded => "BudgetExceeded",
            | Self::GrammarMismatch => "GrammarMismatch",
            | Self::UnknownMold => "UnknownMold",
            | Self::TypeMismatch => "TypeMismatch",
            | Self::ShapeMismatch => "ShapeMismatch",
            | Self::NotSynthesisable => "NotSynthesisable",
            | Self::UnknownConstant => "UnknownConstant",
            | Self::UnboundIndex => "UnboundIndex",
            | Self::DanglingNode => "DanglingNode",
            | Self::AdmissionOrder => "AdmissionOrder",
            | Self::MachineInvariant => "MachineInvariant",
            | Self::SortMismatch => "SortMismatch",
            | Self::LevelMismatch => "LevelMismatch",
            | Self::DependentBind => "DependentBind",
            | Self::Undecided => "Undecided",
            | Self::ExpectationOutsideFixtureRoot => "ExpectationOutsideFixtureRoot",
        })
    }

    /// The name `literal` spells, when the vocabulary holds it.
    ///
    /// # Specification
    /// - requires: nothing — any text is admissible input.
    /// - ensures: the name whose spelling equals the literal's content byte for
    ///   byte; no case folding, trimming or prefix match.
    /// - provides: the reading of a `refuses` payload.
    /// - fails: never; text naming nothing is the [`refusal_name::Absent`]
    ///   absence, which the expectation reader turns into a fixture failure.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every name's own spelling asserted to name it, and
    ///   the match separated from looser ones by a dropped letter, a case
    ///   shift, padding, a suffix and the empty text, each asserted to name
    ///   nothing.
    /// - witness: `refusal::tests::every_refusal_is_named_by_its_variant`
    /// - witness: `refusal::tests::a_near_miss_names_no_refusal`
    #[inline]
    pub fn named_by(literal: &StringLiteral) -> Maybe<Self, refusal_name::Absent>
    {
        let written: &str = literal.as_ref();
        Self::VOCABULARY
            .into_iter()
            .find(|name| name.spelling().0 == written)
            .map_or(Maybe::Absent(refusal_name::Absent::Unnamed), Maybe::Present)
    }
}

impl fmt::Display for RefusalName
{
    /// Writes the name's spelling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        fmt::Display::fmt(&self.spelling(), f)
    }
}

/// A refusal, whichever producer raised it.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Refusal<'source>
{
    /// The lowering refused the declaration.
    Lowering(LoweringRefusal<'source>),
    /// The checker refused the declaration.
    Checking(CheckRefusal),
    /// The corpus root refused an expectation the declaration carries.
    Corpus(CorpusRefusal),
}

impl Refusal<'_>
{
    /// The vocabulary name of this refusal.
    ///
    /// # Specification
    /// - requires: nothing; the function is total over every producer's
    ///   vocabulary.
    /// - ensures: the name spelled as the refusal's own variant, read from the
    ///   variant alone; the lowering's and the checker's `OutOfFragment` and
    ///   `BudgetExceeded` share a name each.
    /// - provides: the produced side of a `refuses` comparison.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every variant of the three producers, one inhabitant
    ///   each, asserted at its exact name, so an arm naming a sibling breaks
    ///   its row; the source-reached refusals are also settled end to end
    ///   against fixtures naming them.
    /// - witness: `refusal::tests::every_refusal_is_named_by_its_variant`
    /// - witness: `settle::tests::every_refusal_a_source_reaches_settles_the_fixture_naming_it`
    #[inline]
    #[must_use]
    pub const fn name(&self) -> RefusalName
    {
        match *self {
            | Self::Lowering(refusal) => lowering_name(refusal),
            | Self::Checking(refusal) => checking_name(refusal),
            | Self::Corpus(CorpusRefusal::ExpectationOutsideFixtureRoot { .. }) => {
                RefusalName::ExpectationOutsideFixtureRoot
            },
        }
    }

    /// Whose fact this refusal records, as its producer classifies it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the class the producing crate's own classifier gives.
    /// - provides: the class a report counts the refusal under.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one inhabitant per variant of each producer, asserted
    ///   at its pinned class, so routing one producer through another's
    ///   classifier, or pinning a class, breaks a row.
    /// - witness: `refusal::tests::every_refusal_is_named_by_its_variant`
    #[inline]
    #[must_use]
    pub const fn classify(&self) -> FailureClass
    {
        match *self {
            | Self::Lowering(ref refusal) => refusal.classify(),
            | Self::Checking(ref refusal) => refusal.classify(),
            | Self::Corpus(ref refusal) => refusal.classify(),
        }
    }
}

/// The vocabulary name of a lowering refusal.
///
/// # Specification
/// trivial.
const fn lowering_name(refusal: LoweringRefusal<'_>) -> RefusalName
{
    match refusal {
        | LoweringRefusal::UnresolvedName { .. } => RefusalName::UnresolvedName,
        | LoweringRefusal::UnresolvedTypeHead { .. } => RefusalName::UnresolvedTypeHead,
        | LoweringRefusal::DuplicateSignature { .. } => RefusalName::DuplicateSignature,
        | LoweringRefusal::DuplicateDefinition { .. } => RefusalName::DuplicateDefinition,
        | LoweringRefusal::DuplicateImportAlias { .. } => RefusalName::DuplicateImportAlias,
        | LoweringRefusal::ShadowedBuiltin { .. } => RefusalName::ShadowedBuiltin,
        | LoweringRefusal::OutOfFragment { .. } => RefusalName::OutOfFragment,
        | LoweringRefusal::MalformedLiteral { .. } => RefusalName::MalformedLiteral,
        | LoweringRefusal::MalformedForm { .. } => RefusalName::MalformedForm,
        | LoweringRefusal::UnknownAttribute { .. } => RefusalName::UnknownAttribute,
        | LoweringRefusal::DuplicateAttribute { .. } => RefusalName::DuplicateAttribute,
        | LoweringRefusal::MissingPayload { .. } => RefusalName::MissingPayload,
        | LoweringRefusal::NonValuePayload { .. } => RefusalName::NonValuePayload,
        | LoweringRefusal::IllTypedPayload { .. } => RefusalName::IllTypedPayload,
        | LoweringRefusal::BudgetExceeded { .. } => RefusalName::BudgetExceeded,
        | LoweringRefusal::GrammarMismatch { .. } => RefusalName::GrammarMismatch,
        | LoweringRefusal::UnknownMold { .. } => RefusalName::UnknownMold,
    }
}

/// The vocabulary name of a checker refusal.
///
/// # Specification
/// trivial.
const fn checking_name(refusal: CheckRefusal) -> RefusalName
{
    match refusal {
        | CheckRefusal::TypeMismatch(_) => RefusalName::TypeMismatch,
        | CheckRefusal::ShapeMismatch { .. } => RefusalName::ShapeMismatch,
        | CheckRefusal::NotSynthesisable { .. } => RefusalName::NotSynthesisable,
        | CheckRefusal::UnknownConstant { .. } => RefusalName::UnknownConstant,
        | CheckRefusal::OutOfFragment { .. } => RefusalName::OutOfFragment,
        | CheckRefusal::UnboundIndex { .. } => RefusalName::UnboundIndex,
        | CheckRefusal::BudgetExceeded { .. } => RefusalName::BudgetExceeded,
        | CheckRefusal::DanglingNode { .. } => RefusalName::DanglingNode,
        | CheckRefusal::AdmissionOrder { .. } => RefusalName::AdmissionOrder,
        | CheckRefusal::MachineInvariant => RefusalName::MachineInvariant,
        | CheckRefusal::SortMismatch { .. } => RefusalName::SortMismatch,
        | CheckRefusal::LevelMismatch { .. } => RefusalName::LevelMismatch,
        | CheckRefusal::DependentBind { .. } => RefusalName::DependentBind,
        | CheckRefusal::Undecided { .. } => RefusalName::Undecided,
    }
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;
    use alloc::vec::Vec;

    use gandr_core_checker::CheckBudget;
    use gandr_core_checker::CheckRefusal;
    use gandr_core_checker::CheckingForm;
    use gandr_core_checker::CoreNode;
    use gandr_core_checker::ExpectedShape;
    use gandr_core_checker::Mismatch;
    use gandr_core_checker::TermNode;
    use gandr_core_checker::TypeNode;
    use gandr_core_checker::UnadmittedFormer;
    use gandr_core_term::BinderDepth;
    use gandr_core_term::CoreArena;
    use gandr_core_term::FailureClass;
    use gandr_core_term::Zone;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::StringLiteral;
    use gandr_surface_grammar::NamedKind;
    use gandr_surface_lowering::AttributeRegistry;
    use gandr_surface_lowering::AttributeSchema;
    use gandr_surface_lowering::FormFault;
    use gandr_surface_lowering::FormName;
    use gandr_surface_lowering::FragmentBoundary;
    use gandr_surface_lowering::FragmentSort;
    use gandr_surface_lowering::HeadArity;
    use gandr_surface_lowering::LoweringBudget;
    use gandr_surface_lowering::LoweringRefusal;
    use gandr_surface_lowering::PayloadForm;
    use gandr_surface_lowering::SurfaceName;
    use gandr_surface_syntax::GrammarFingerprint;
    use gandr_surface_syntax::MoldId;
    use quenchant_shape::shape::Maybe;

    use super::CorpusRefusal;
    use super::Refusal;
    use super::RefusalName;
    use super::RefusalSpelling;
    use super::refusal_name;
    use crate::expectation::ExpectationSchema;
    use crate::fixture::empty_span;

    /// One inhabitant of every refusal variant of every producer, beside the
    /// spelling its name must have and the class it must carry.
    ///
    /// # Specification
    /// trivial.
    fn vocabulary() -> Vec<(Refusal<'static>, RefusalSpelling, FailureClass)>
    {
        let empty = empty_span();
        let Maybe::Present((owes, _schema)) = AttributeRegistry::lookup(SurfaceName::from("owes"))
        else {
            panic!("`owes` is registered");
        };
        let mut arena = CoreArena::new();
        let value = arena.value_unit();
        let value_type = arena.value_type_unit();
        let integer = arena.value_type_base(BaseType::Integer);
        let computation = arena.computation_return(value);
        let comp_type = arena.comp_type_returner(value_type);
        let zero = ConstantIndex::from(0_usize);
        let lowering = [
            (
                LoweringRefusal::UnresolvedName {
                    span: empty,
                    name: SurfaceName::from("x"),
                },
                "UnresolvedName",
                FailureClass::MalformedSource,
            ),
            (
                LoweringRefusal::UnresolvedTypeHead {
                    span: empty,
                    name: SurfaceName::from("Intgr"),
                    arity: HeadArity::Nullary,
                },
                "UnresolvedTypeHead",
                FailureClass::MalformedSource,
            ),
            (
                LoweringRefusal::DuplicateSignature {
                    span: empty,
                    name: SurfaceName::from("x"),
                    first: empty,
                },
                "DuplicateSignature",
                FailureClass::MalformedSource,
            ),
            (
                LoweringRefusal::DuplicateDefinition {
                    span: empty,
                    name: SurfaceName::from("x"),
                    first: empty,
                },
                "DuplicateDefinition",
                FailureClass::MalformedSource,
            ),
            (
                LoweringRefusal::DuplicateImportAlias {
                    span: empty,
                    alias: SurfaceName::from("parse"),
                    first: empty,
                },
                "DuplicateImportAlias",
                FailureClass::MalformedSource,
            ),
            (
                LoweringRefusal::ShadowedBuiltin {
                    span: empty,
                    name: SurfaceName::from("list"),
                },
                "ShadowedBuiltin",
                FailureClass::MalformedSource,
            ),
            (
                LoweringRefusal::OutOfFragment {
                    span: empty,
                    form: FormName::from(NamedKind("product_type")),
                    sort: FragmentSort::ValueType,
                    boundary: FragmentBoundary::Reserved,
                },
                "OutOfFragment",
                FailureClass::Unrepresentable,
            ),
            (
                LoweringRefusal::MalformedLiteral {
                    span: empty,
                    form: FormName::from(NamedKind("number")),
                },
                "MalformedLiteral",
                FailureClass::MalformedSource,
            ),
            (
                LoweringRefusal::MalformedForm {
                    span: empty,
                    form: FormName::DECLARATION,
                    fault: FormFault::ExtraOperand,
                },
                "MalformedForm",
                FailureClass::MalformedSource,
            ),
            (
                LoweringRefusal::UnknownAttribute {
                    span: empty,
                    name: SurfaceName::from("check"),
                    suggestion: AttributeRegistry::suggestion(SurfaceName::from("check")),
                },
                "UnknownAttribute",
                FailureClass::MalformedSource,
            ),
            (
                LoweringRefusal::DuplicateAttribute {
                    span: empty,
                    name: SurfaceName::from("checks"),
                    first: empty,
                },
                "DuplicateAttribute",
                FailureClass::MalformedSource,
            ),
            (
                LoweringRefusal::MissingPayload {
                    span: empty,
                    name: owes,
                    expected: AttributeSchema::Integer,
                },
                "MissingPayload",
                FailureClass::MalformedSource,
            ),
            (
                LoweringRefusal::NonValuePayload {
                    span: empty,
                    name: owes,
                    form: FormName::from(NamedKind("ret_expression")),
                },
                "NonValuePayload",
                FailureClass::MalformedSource,
            ),
            (
                LoweringRefusal::IllTypedPayload {
                    span: empty,
                    name: owes,
                    expected: AttributeSchema::Integer,
                    written: PayloadForm::Text,
                },
                "IllTypedPayload",
                FailureClass::MalformedSource,
            ),
            (
                LoweringRefusal::BudgetExceeded {
                    budget: LoweringBudget::from(0_usize),
                },
                "BudgetExceeded",
                FailureClass::EngineFault,
            ),
            (
                LoweringRefusal::GrammarMismatch {
                    tree: GrammarFingerprint::from(0_u64),
                    grammar: GrammarFingerprint::from(1_u64),
                },
                "GrammarMismatch",
                FailureClass::EngineFault,
            ),
            (
                LoweringRefusal::UnknownMold {
                    span: empty,
                    mold: MoldId::from(0_u32),
                },
                "UnknownMold",
                FailureClass::EngineFault,
            ),
        ];
        let checking = [
            (
                CheckRefusal::TypeMismatch(Mismatch::Value {
                    at: value,
                    synthesised: value_type,
                    expected: integer,
                }),
                "TypeMismatch",
                FailureClass::MalformedSource,
            ),
            (
                CheckRefusal::ShapeMismatch {
                    at: TermNode::Value(value),
                    wanted: ExpectedShape::Thunk,
                    found: TypeNode::Value(value_type),
                },
                "ShapeMismatch",
                FailureClass::MalformedSource,
            ),
            (
                CheckRefusal::NotSynthesisable {
                    form: CheckingForm::Hole(zero),
                },
                "NotSynthesisable",
                FailureClass::MalformedSource,
            ),
            (
                CheckRefusal::UnknownConstant {
                    at: value,
                    constant: zero,
                },
                "UnknownConstant",
                FailureClass::MalformedSource,
            ),
            (
                CheckRefusal::OutOfFragment {
                    at: CoreNode::Term(TermNode::Value(value)),
                    former: UnadmittedFormer::Pair,
                },
                "OutOfFragment",
                FailureClass::Unrepresentable,
            ),
            (
                CheckRefusal::UnboundIndex {
                    at: value,
                    zone: Zone::Intuitionistic,
                    index: DeBruijnIndex::from(0_u32),
                    depth: BinderDepth::from(0_usize),
                },
                "UnboundIndex",
                FailureClass::EngineFault,
            ),
            (
                CheckRefusal::BudgetExceeded {
                    budget: CheckBudget::DEFAULT,
                },
                "BudgetExceeded",
                FailureClass::EngineFault,
            ),
            (
                CheckRefusal::DanglingNode {
                    node: CoreNode::Type(TypeNode::Value(value_type)),
                },
                "DanglingNode",
                FailureClass::EngineFault,
            ),
            (
                CheckRefusal::AdmissionOrder {
                    constant: zero,
                    admitted: zero,
                },
                "AdmissionOrder",
                FailureClass::EngineFault,
            ),
            (
                CheckRefusal::MachineInvariant,
                "MachineInvariant",
                FailureClass::EngineFault,
            ),
            (
                CheckRefusal::SortMismatch {
                    at: value,
                    synthesised: value_type,
                    expected: integer,
                },
                "SortMismatch",
                FailureClass::MalformedSource,
            ),
            (
                CheckRefusal::LevelMismatch {
                    at: value,
                    synthesised: value_type,
                    expected: integer,
                },
                "LevelMismatch",
                FailureClass::MalformedSource,
            ),
            (
                CheckRefusal::DependentBind {
                    at: computation,
                    synthesised: comp_type,
                },
                "DependentBind",
                FailureClass::MalformedSource,
            ),
            (
                CheckRefusal::Undecided { at: value },
                "Undecided",
                FailureClass::EngineFault,
            ),
        ];
        let corpus = (
            CorpusRefusal::ExpectationOutsideFixtureRoot {
                schema: ExpectationSchema::Owes,
                span: empty,
            },
            "ExpectationOutsideFixtureRoot",
            FailureClass::MalformedSource,
        );

        let mut rows = Vec::new();
        rows.extend(lowering.into_iter().map(|(refusal, spelled, class)| {
            (Refusal::Lowering(refusal), RefusalSpelling(spelled), class)
        }));
        rows.extend(checking.into_iter().map(|(refusal, spelled, class)| {
            (Refusal::Checking(refusal), RefusalSpelling(spelled), class)
        }));
        rows.push((
            Refusal::Corpus(corpus.0),
            RefusalSpelling(corpus.1),
            corpus.2,
        ));
        rows
    }

    #[test]
    fn every_refusal_is_named_by_its_variant()
    {
        let rows = vocabulary();

        for &(refusal, spelled, class) in &rows {
            let name = refusal.name();
            assert_eq!(
                name.spelling(),
                spelled,
                "a refusal's name is spelled as its own variant"
            );
            assert_eq!(
                RefusalName::named_by(&StringLiteral::new(String::from(spelled.as_ref()))),
                Maybe::Present(name),
                "the spelling `{spelled}` names the refusal back"
            );
            assert_eq!(
                refusal.classify(),
                class,
                "`{spelled}` carries its producer's class"
            );
        }
        let mut named: Vec<RefusalName> =
            rows.iter().map(|&(refusal, ..)| refusal.name()).collect();
        named.sort_unstable();
        named.dedup();
        assert_eq!(
            named,
            RefusalName::VOCABULARY.to_vec(),
            "the producers' refusals reach every name of the vocabulary, and nothing else"
        );
    }

    #[test]
    fn a_near_miss_names_no_refusal()
    {
        for written in [
            "TypeMismatc",
            "typemismatch",
            " TypeMismatch",
            "TypeMismatch ",
            "TypeMismatches",
            "",
        ] {
            assert_eq!(
                RefusalName::named_by(&StringLiteral::new(String::from(written))),
                Maybe::Absent(refusal_name::Absent::Unnamed),
                "`{written}` is not the spelling of any refusal"
            );
        }
    }
}
