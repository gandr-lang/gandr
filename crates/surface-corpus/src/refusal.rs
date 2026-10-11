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

use anodized::spec;
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
///
/// # Specification
/// - requires: the producer establishes correspondence with the source or
///   vocabulary it represents.
/// - ensures: Records an expectation rejected by root admission, preserving its
///   schema and source span.
/// - panics: none.
/// - executable: none — The enum carries neither its root nor source text;
///   `CorpusRoot::admit` establishes refusal policy and the formatting witness
///   observes the retained location.
///
/// # Adequacy
/// - hypothesis: L3 — source-level refusal settlement retains exact identities
///   and locations; a strict-root refusal retains its admitted alternatives.
///   These witnesses cover reachable cases, not every producer variant.
/// - witness: `root::tests::the_admission_table_is_pinned`
/// - witness: `refusal::tests::root_refusal_names_every_admitted_schema`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum CorpusRefusal
{
    /// An `owes` or `refuses` attribute on a declaration under the strict
    /// root, which admits `checks` and `runs`.
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
    /// - hypothesis: L3 — the strict-root admission refusal retains both
    ///   admitted alternatives and its source position.
    /// - witness: `refusal::tests::root_refusal_names_every_admitted_schema`
    #[spec(
        ensures: |ret| matches!(ret, FailureClass::MalformedSource),
    )]
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
    /// - requires: nothing.
    /// - ensures: writes the rejected schema and source span, and names both
    ///   schemas admitted by the strict root.
    /// - fails: propagates a refusing sink as `fmt::Error`.
    /// - panics: none.
    /// - executable: none — the formatter exposes neither emitted text nor
    ///   readable sink state; the witnesses observe semantic text and a
    ///   refusing sink instead of writing twice.
    ///
    /// # Errors
    /// Returns `fmt::Error` when the sink refuses a write.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a strict-root refusal at a nonempty span retains its
    ///   exact identifier, admitted alternatives and source range, without
    ///   fixing English sentence wording.
    /// - witness: `refusal::tests::root_refusal_names_every_admitted_schema`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            | Self::ExpectationOutsideFixtureRoot { schema, span } => write!(
                f,
                "`{schema}` at {span} states an expectation the strict root refuses; only `checks` and `runs` are admitted outside the fixture root"
            ),
        }
    }
}

impl Error for CorpusRefusal
{
}

/// The spelling of a refusal name, as a `refuses` payload writes it.
///
/// # Specification
/// - requires: the producer establishes correspondence with the source or
///   vocabulary it represents.
/// - ensures: Values supplied by `RefusalName::spelling` name exactly one
///   member of the closed vocabulary, byte for byte.
/// - panics: none.
/// - executable: none — The carrier has no invocation; `RefusalName::spelling`
///   establishes its closed-name invariant with a const byte-pattern predicate.
///
/// # Adequacy
/// - hypothesis: L3 — source-reachable refusal identifiers settle their named
///   expectations; changing a name or source position changes settlement.
/// - witness: `settle::tests::every_refusal_a_source_reaches_settles_the_fixture_naming_it`
/// - witness: `refusal::tests::a_near_miss_names_no_refusal`
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
    /// - requires: nothing.
    /// - ensures: writes the canonical refusal spelling unchanged.
    /// - fails: propagates a refusing sink as `fmt::Error`.
    /// - panics: none.
    /// - executable: none — the formatter exposes neither emitted text nor
    ///   readable sink state; the witnesses observe semantic text and a
    ///   refusing sink instead of writing twice.
    ///
    /// # Errors
    /// Returns `fmt::Error` when the sink refuses a write.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — source-reachable refusal identifiers settle
    ///   expectations under their producing stage, without fixing report
    ///   sentence wording.
    /// - witness: `settle::tests::every_refusal_a_source_reaches_settles_the_fixture_naming_it`
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
///
/// # Specification
/// - requires: the producer establishes correspondence with the source or
///   vocabulary it represents.
/// - ensures: Distinguishes the closed refusal names; producer variants share a
///   name only where the vocabulary identifies them.
/// - panics: none.
/// - executable: none — The enum alone has no producer or spelling input;
///   naming, spelling and parsing methods carry the executable correspondences.
///
/// # Adequacy
/// - hypothesis: L3 — source-reachable refusals retain their exact identities
///   and locations through settlement. This is not exhaustive variant coverage.
/// - witness: `settle::tests::every_refusal_a_source_reaches_settles_the_fixture_naming_it`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum RefusalName
{
    /// The checker reports `NotADataType`.
    NotADataType,
    /// The checker reports `DataKindNotUniverse`.
    DataKindNotUniverse,
    /// The checker reports `DataFieldLevel`.
    DataFieldLevel,
    /// The checker reports `DataArgumentArity`.
    DataArgumentArity,
    /// The checker reports `UnknownConstructor`.
    UnknownConstructor,
    /// The checker reports `ConstructorArity`.
    ConstructorArity,
    /// The checker reports `NonExhaustiveDataCase`.
    NonExhaustiveDataCase,
    /// The checker reports `AbsentRecordField`.
    AbsentRecordField,
    /// The checker reports `MissingRecordField`.
    MissingRecordField,
    /// A native path endpoint is not a closed first-order code.
    PathCode,
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
    /// A bridge graded other than the default the fragment admits.
    GradedBridge,
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
    /// A module member named at or after the member naming it.
    ForwardMemberReference,
    /// A selection or a signature component a module does not supply.
    UnknownMember,
    /// A module ascription form the fragment does not read yet.
    UnreadAscription,
    /// A top-level module named with a lowercase initial.
    LowercaseModuleName,
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
    /// A static application at more arguments than its head takes.
    FamilyArity,
    /// A static application's argument at a classifier other than its domain.
    FamilyArgumentClassifier,
    /// A type operator passed where a dynamic parameter needs a value.
    StaticLambdaArgument,
    /// A static Pi over a type that classifies no codes.
    StaticClassifierExpected,
    /// An expectation the strict root refuses.
    ExpectationOutsideFixtureRoot,
}

impl RefusalName
{
    /// Every name of the vocabulary, in declaration order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: contains each closed refusal name exactly once.
    /// - panics: none.
    ///
    /// The constant has no invocation for a specification attribute; its
    /// bounded consumer evidence is stated below.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — source-reachable names remain available to
    ///   expectation settlement; this does not establish completeness or
    ///   uniqueness of the enumeration independently of its implementation.
    /// - witness: `settle::tests::every_refusal_a_source_reaches_settles_the_fixture_naming_it`
    pub const VOCABULARY: [Self; 49_usize] = [
        Self::NotADataType,
        Self::DataKindNotUniverse,
        Self::DataFieldLevel,
        Self::DataArgumentArity,
        Self::UnknownConstructor,
        Self::ConstructorArity,
        Self::NonExhaustiveDataCase,
        Self::AbsentRecordField,
        Self::MissingRecordField,
        Self::PathCode,
        Self::UnresolvedName,
        Self::UnresolvedTypeHead,
        Self::DuplicateSignature,
        Self::DuplicateDefinition,
        Self::DuplicateImportAlias,
        Self::ShadowedBuiltin,
        Self::OutOfFragment,
        Self::GradedBridge,
        Self::MalformedLiteral,
        Self::MalformedForm,
        Self::UnknownAttribute,
        Self::DuplicateAttribute,
        Self::MissingPayload,
        Self::NonValuePayload,
        Self::IllTypedPayload,
        Self::ForwardMemberReference,
        Self::UnknownMember,
        Self::UnreadAscription,
        Self::LowercaseModuleName,
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
        Self::FamilyArity,
        Self::FamilyArgumentClassifier,
        Self::StaticLambdaArgument,
        Self::StaticClassifierExpected,
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
    /// - hypothesis: L3 — source fixtures name the exact refusal they reach;
    ///   altered identifiers or sibling substitutions change their settlement.
    ///   The witness does not enumerate every producer variant.
    /// - witness: `settle::tests::every_refusal_a_source_reaches_settles_the_fixture_naming_it`
    #[spec(
        ensures: |ret| {
    matches!(
        (self, ret.0.as_bytes()), (Self::UnresolvedName, b"UnresolvedName") |
        (Self::UnresolvedTypeHead, b"UnresolvedTypeHead") | (Self::DuplicateSignature,
        b"DuplicateSignature") | (Self::DuplicateDefinition, b"DuplicateDefinition") |
        (Self::DuplicateImportAlias, b"DuplicateImportAlias") | (Self::ShadowedBuiltin,
        b"ShadowedBuiltin") | (Self::OutOfFragment, b"OutOfFragment") |
        (Self::GradedBridge, b"GradedBridge") | (Self::MalformedLiteral,
        b"MalformedLiteral") | (Self::MalformedForm, b"MalformedForm") |
        (Self::UnknownAttribute, b"UnknownAttribute") | (Self::DuplicateAttribute,
        b"DuplicateAttribute") | (Self::MissingPayload, b"MissingPayload") |
        (Self::NonValuePayload, b"NonValuePayload") | (Self::IllTypedPayload,
        b"IllTypedPayload") | (Self::ForwardMemberReference, b"ForwardMemberReference") |
        (Self::UnknownMember, b"UnknownMember") | (Self::UnreadAscription,
        b"UnreadAscription") | (Self::LowercaseModuleName, b"LowercaseModuleName") |
        (Self::BudgetExceeded, b"BudgetExceeded") | (Self::GrammarMismatch,
        b"GrammarMismatch") | (Self::UnknownMold, b"UnknownMold") | (Self::TypeMismatch,
        b"TypeMismatch") | (Self::ShapeMismatch, b"ShapeMismatch") |
        (Self::NotSynthesisable, b"NotSynthesisable") | (Self::UnknownConstant,
        b"UnknownConstant") | (Self::UnboundIndex, b"UnboundIndex") |
        (Self::DanglingNode, b"DanglingNode") | (Self::AdmissionOrder, b"AdmissionOrder")
        | (Self::MachineInvariant, b"MachineInvariant") | (Self::SortMismatch,
        b"SortMismatch") | (Self::LevelMismatch, b"LevelMismatch") |
        (Self::DependentBind, b"DependentBind") | (Self::Undecided, b"Undecided") |
        (Self::FamilyArity, b"FamilyArity") | (Self::FamilyArgumentClassifier,
        b"FamilyArgumentClassifier") | (Self::StaticLambdaArgument,
        b"StaticLambdaArgument") | (Self::StaticClassifierExpected,
        b"StaticClassifierExpected") | (Self::ExpectationOutsideFixtureRoot,
        b"ExpectationOutsideFixtureRoot") | (Self::PathCode, b"PathCode")
        | (Self::NotADataType, b"NotADataType")
        | (Self::DataKindNotUniverse, b"DataKindNotUniverse")
        | (Self::DataFieldLevel, b"DataFieldLevel")
        | (Self::DataArgumentArity, b"DataArgumentArity")
        | (Self::UnknownConstructor, b"UnknownConstructor")
        | (Self::ConstructorArity, b"ConstructorArity")
        | (Self::NonExhaustiveDataCase, b"NonExhaustiveDataCase")
        | (Self::AbsentRecordField, b"AbsentRecordField")
        | (Self::MissingRecordField, b"MissingRecordField")
    )
},
    )]
    #[inline]
    #[must_use]
    pub const fn spelling(self) -> RefusalSpelling
    {
        RefusalSpelling(match self {
            | Self::NotADataType => "NotADataType",
            | Self::DataKindNotUniverse => "DataKindNotUniverse",
            | Self::DataFieldLevel => "DataFieldLevel",
            | Self::DataArgumentArity => "DataArgumentArity",
            | Self::UnknownConstructor => "UnknownConstructor",
            | Self::ConstructorArity => "ConstructorArity",
            | Self::NonExhaustiveDataCase => "NonExhaustiveDataCase",
            | Self::AbsentRecordField => "AbsentRecordField",
            | Self::MissingRecordField => "MissingRecordField",
            | Self::UnresolvedName => "UnresolvedName",
            | Self::UnresolvedTypeHead => "UnresolvedTypeHead",
            | Self::DuplicateSignature => "DuplicateSignature",
            | Self::DuplicateDefinition => "DuplicateDefinition",
            | Self::DuplicateImportAlias => "DuplicateImportAlias",
            | Self::PathCode => "PathCode",
            | Self::ShadowedBuiltin => "ShadowedBuiltin",
            | Self::OutOfFragment => "OutOfFragment",
            | Self::GradedBridge => "GradedBridge",
            | Self::MalformedLiteral => "MalformedLiteral",
            | Self::MalformedForm => "MalformedForm",
            | Self::UnknownAttribute => "UnknownAttribute",
            | Self::DuplicateAttribute => "DuplicateAttribute",
            | Self::MissingPayload => "MissingPayload",
            | Self::NonValuePayload => "NonValuePayload",
            | Self::IllTypedPayload => "IllTypedPayload",
            | Self::ForwardMemberReference => "ForwardMemberReference",
            | Self::UnknownMember => "UnknownMember",
            | Self::UnreadAscription => "UnreadAscription",
            | Self::LowercaseModuleName => "LowercaseModuleName",
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
            | Self::FamilyArity => "FamilyArity",
            | Self::FamilyArgumentClassifier => "FamilyArgumentClassifier",
            | Self::StaticLambdaArgument => "StaticLambdaArgument",
            | Self::StaticClassifierExpected => "StaticClassifierExpected",
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
    /// - hypothesis: L3 — changed case, dropped letters, surrounding
    ///   whitespace, suffixes and empty text are refused rather than matched
    ///   permissively. Source fixtures exercise the corresponding exact
    ///   identifiers.
    /// - witness: `settle::tests::every_refusal_a_source_reaches_settles_the_fixture_naming_it`
    /// - witness: `refusal::tests::a_near_miss_names_no_refusal`
    #[spec(
        ensures: |ret| match ret {
    Maybe::Present(name) => name.spelling().0 == literal.as_ref(),
    Maybe::Absent(refusal_name::Absent::Unnamed) => {
        Self::VOCABULARY.iter().all(|name| name.spelling().0 != literal.as_ref())
    }
},
    )]
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
    /// - requires: nothing.
    /// - ensures: writes the canonical refusal spelling unchanged.
    /// - fails: propagates a refusing sink as `fmt::Error`.
    /// - panics: none.
    /// - executable: none — the formatter exposes neither emitted text nor
    ///   readable sink state; the witnesses observe semantic text and a
    ///   refusing sink instead of writing twice.
    ///
    /// # Errors
    /// Returns `fmt::Error` when the sink refuses a write.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — source-reachable refusal identifiers settle
    ///   expectations under their producing stage, without fixing report
    ///   sentence wording.
    /// - witness: `settle::tests::every_refusal_a_source_reaches_settles_the_fixture_naming_it`
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
///
/// # Specification
/// - requires: the producer establishes correspondence with the source or
///   vocabulary it represents.
/// - ensures: Retains the producing stage and its refusal; naming and
///   classification preserve that producer’s interpretation.
/// - panics: none.
/// - executable: none — The carrier has no invocation or original declaration
///   to validate; `name` and `classify` state the observable interpretation at
///   call boundaries.
///
/// # Adequacy
/// - hypothesis: L3 — source-level refusal settlement retains the producing
///   stage and exact identity for the cases the fixtures reach.
/// - witness: `settle::tests::every_refusal_a_source_reaches_settles_the_fixture_naming_it`
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
    /// - hypothesis: L3 — source-reachable refusals settle the fixture naming
    ///   them; sibling substitutions or a wrong producer change that
    ///   observation.
    /// - witness: `settle::tests::every_refusal_a_source_reaches_settles_the_fixture_naming_it`
    #[spec(
        ensures: |ret| {
    matches!(
        (* self, ret), (Self::Lowering(LoweringRefusal::UnresolvedName { .. }),
        RefusalName::UnresolvedName) |
        (Self::Lowering(LoweringRefusal::UnresolvedTypeHead { .. }),
        RefusalName::UnresolvedTypeHead) |
        (Self::Lowering(LoweringRefusal::DuplicateSignature { .. }),
        RefusalName::DuplicateSignature) |
        (Self::Lowering(LoweringRefusal::DuplicateDefinition { .. }),
        RefusalName::DuplicateDefinition) |
        (Self::Lowering(LoweringRefusal::DuplicateImportAlias { .. }),
        RefusalName::DuplicateImportAlias) |
        (Self::Lowering(LoweringRefusal::ShadowedBuiltin { .. }),
        RefusalName::ShadowedBuiltin) | (Self::Lowering(LoweringRefusal::OutOfFragment {
        .. }) | Self::Checking(CheckRefusal::OutOfFragment { .. }),
        RefusalName::OutOfFragment) | (Self::Lowering(LoweringRefusal::GradedBridge { ..
        }), RefusalName::GradedBridge) |
        (Self::Lowering(LoweringRefusal::MalformedLiteral { .. }),
        RefusalName::MalformedLiteral) | (Self::Lowering(LoweringRefusal::MalformedForm {
        .. }), RefusalName::MalformedForm) |
        (Self::Lowering(LoweringRefusal::UnknownAttribute { .. }),
        RefusalName::UnknownAttribute) |
        (Self::Lowering(LoweringRefusal::DuplicateAttribute { .. }),
        RefusalName::DuplicateAttribute) |
        (Self::Lowering(LoweringRefusal::MissingPayload { .. }),
        RefusalName::MissingPayload) | (Self::Lowering(LoweringRefusal::NonValuePayload {
        .. }), RefusalName::NonValuePayload) |
        (Self::Lowering(LoweringRefusal::IllTypedPayload { .. }),
        RefusalName::IllTypedPayload) |
        (Self::Lowering(LoweringRefusal::ForwardMemberReference { .. }),
        RefusalName::ForwardMemberReference) |
        (Self::Lowering(LoweringRefusal::UnknownMember { .. }),
        RefusalName::UnknownMember) | (Self::Lowering(LoweringRefusal::UnreadAscription {
        .. }), RefusalName::UnreadAscription) |
        (Self::Lowering(LoweringRefusal::LowercaseModuleName { .. }),
        RefusalName::LowercaseModuleName) |
        (Self::Lowering(LoweringRefusal::BudgetExceeded { .. }) |
        Self::Checking(CheckRefusal::BudgetExceeded { .. }), RefusalName::BudgetExceeded)
        | (Self::Lowering(LoweringRefusal::GrammarMismatch { .. }),
        RefusalName::GrammarMismatch) | (Self::Lowering(LoweringRefusal::UnknownMold { ..
        }), RefusalName::UnknownMold) | (Self::Checking(CheckRefusal::PathCode(_)), RefusalName::PathCode) | (Self::Checking(CheckRefusal::TypeMismatch(_)),
        RefusalName::TypeMismatch) | (Self::Checking(CheckRefusal::ShapeMismatch { .. }),
        RefusalName::ShapeMismatch) | (Self::Checking(CheckRefusal::NotSynthesisable { ..
        }), RefusalName::NotSynthesisable) |
        (Self::Checking(CheckRefusal::UnknownConstant { .. }),
        RefusalName::UnknownConstant) | (Self::Checking(CheckRefusal::UnboundIndex { ..
        }), RefusalName::UnboundIndex) | (Self::Checking(CheckRefusal::DanglingNode { ..
        }), RefusalName::DanglingNode) | (Self::Checking(CheckRefusal::AdmissionOrder {
        .. }), RefusalName::AdmissionOrder) |
        (Self::Checking(CheckRefusal::MachineInvariant), RefusalName::MachineInvariant) |
        (Self::Checking(CheckRefusal::SortMismatch { .. }), RefusalName::SortMismatch) |
        (Self::Checking(CheckRefusal::LevelMismatch { .. }), RefusalName::LevelMismatch)
        | (Self::Checking(CheckRefusal::DependentBind { .. }),
        RefusalName::DependentBind) | (Self::Checking(CheckRefusal::Undecided { .. }),
        RefusalName::Undecided) | (Self::Checking(CheckRefusal::FamilyArity { .. }),
        RefusalName::FamilyArity) |
        (Self::Checking(CheckRefusal::FamilyArgumentClassifier { .. }),
        RefusalName::FamilyArgumentClassifier) |
        (Self::Checking(CheckRefusal::StaticLambdaArgument { .. }),
        RefusalName::StaticLambdaArgument) |
        (Self::Checking(CheckRefusal::StaticClassifierExpected { .. }),
        RefusalName::StaticClassifierExpected) |
        (Self::Corpus(CorpusRefusal::ExpectationOutsideFixtureRoot { .. }),
        RefusalName::ExpectationOutsideFixtureRoot)
    )
},
    )]
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
    /// - hypothesis: L3 — source-reachable refusals retain their producer class
    ///   through settlement. The predicate preserves the owning classifier for
    ///   arbitrary payloads; the witnesses do not cover every variant.
    /// - witness: `settle::tests::every_refusal_a_source_reaches_settles_the_fixture_naming_it`
    #[spec(
        ensures: |ret| {
    let expected = match *self {
        Self::Lowering(ref refusal) => refusal.classify(),
        Self::Checking(ref refusal) => refusal.classify(),
        Self::Corpus(ref refusal) => refusal.classify(),
    };
    matches!(
        (expected, ret), (FailureClass::UserAbsence, FailureClass::UserAbsence) |
        (FailureClass::Unrepresentable, FailureClass::Unrepresentable) |
        (FailureClass::MalformedSource, FailureClass::MalformedSource) |
        (FailureClass::EngineFault, FailureClass::EngineFault)
    )
},
    )]
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
/// - requires: nothing.
/// - ensures: returns the vocabulary name of the producer variant,
///   independently of its payload.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — source-reachable lowering refusals retain their exact
///   identifiers through expectation settlement.
/// - witness: `settle::tests::every_refusal_a_source_reaches_settles_the_fixture_naming_it`
#[spec(
    ensures: |ret| {
    matches!(
        (refusal, ret), (LoweringRefusal::UnresolvedName { .. },
        RefusalName::UnresolvedName) | (LoweringRefusal::UnresolvedTypeHead { .. },
        RefusalName::UnresolvedTypeHead) | (LoweringRefusal::DuplicateSignature { .. },
        RefusalName::DuplicateSignature) | (LoweringRefusal::DuplicateDefinition { .. },
        RefusalName::DuplicateDefinition) | (LoweringRefusal::DuplicateImportAlias { ..
        }, RefusalName::DuplicateImportAlias) | (LoweringRefusal::ShadowedBuiltin { .. },
        RefusalName::ShadowedBuiltin) | (LoweringRefusal::OutOfFragment { .. },
        RefusalName::OutOfFragment) | (LoweringRefusal::GradedBridge { .. },
        RefusalName::GradedBridge) | (LoweringRefusal::MalformedLiteral { .. },
        RefusalName::MalformedLiteral) | (LoweringRefusal::MalformedForm { .. },
        RefusalName::MalformedForm) | (LoweringRefusal::UnknownAttribute { .. },
        RefusalName::UnknownAttribute) | (LoweringRefusal::DuplicateAttribute { .. },
        RefusalName::DuplicateAttribute) | (LoweringRefusal::MissingPayload { .. },
        RefusalName::MissingPayload) | (LoweringRefusal::NonValuePayload { .. },
        RefusalName::NonValuePayload) | (LoweringRefusal::IllTypedPayload { .. },
        RefusalName::IllTypedPayload) | (LoweringRefusal::ForwardMemberReference { .. },
        RefusalName::ForwardMemberReference) | (LoweringRefusal::UnknownMember { .. },
        RefusalName::UnknownMember) | (LoweringRefusal::UnreadAscription { .. },
        RefusalName::UnreadAscription) | (LoweringRefusal::LowercaseModuleName { .. },
        RefusalName::LowercaseModuleName) | (LoweringRefusal::BudgetExceeded { .. },
        RefusalName::BudgetExceeded) | (LoweringRefusal::GrammarMismatch { .. },
        RefusalName::GrammarMismatch) | (LoweringRefusal::UnknownMold { .. },
        RefusalName::UnknownMold)
    )
},
)]
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
        | LoweringRefusal::GradedBridge { .. } => RefusalName::GradedBridge,
        | LoweringRefusal::MalformedLiteral { .. } => RefusalName::MalformedLiteral,
        | LoweringRefusal::MalformedForm { .. } => RefusalName::MalformedForm,
        | LoweringRefusal::UnknownAttribute { .. } => RefusalName::UnknownAttribute,
        | LoweringRefusal::DuplicateAttribute { .. } => RefusalName::DuplicateAttribute,
        | LoweringRefusal::MissingPayload { .. } => RefusalName::MissingPayload,
        | LoweringRefusal::NonValuePayload { .. } => RefusalName::NonValuePayload,
        | LoweringRefusal::IllTypedPayload { .. } => RefusalName::IllTypedPayload,
        | LoweringRefusal::ForwardMemberReference { .. } => RefusalName::ForwardMemberReference,
        | LoweringRefusal::UnknownMember { .. } => RefusalName::UnknownMember,
        | LoweringRefusal::UnreadAscription { .. } => RefusalName::UnreadAscription,
        | LoweringRefusal::LowercaseModuleName { .. } => RefusalName::LowercaseModuleName,
        | LoweringRefusal::BudgetExceeded { .. } => RefusalName::BudgetExceeded,
        | LoweringRefusal::GrammarMismatch { .. } => RefusalName::GrammarMismatch,
        | LoweringRefusal::UnknownMold { .. } => RefusalName::UnknownMold,
    }
}

/// The vocabulary name of a checker refusal.
///
/// # Specification
/// - requires: nothing.
/// - ensures: returns the vocabulary name of the producer variant,
///   independently of its payload.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — source-reachable checker refusals retain their exact
///   identifiers through expectation settlement.
/// - witness: `settle::tests::every_refusal_a_source_reaches_settles_the_fixture_naming_it`
#[spec(
    ensures: |ret| {
    matches!(
        (refusal, ret), (CheckRefusal::TypeMismatch(_), RefusalName::TypeMismatch) |
        (CheckRefusal::ShapeMismatch { .. }, RefusalName::ShapeMismatch) |
        (CheckRefusal::NotSynthesisable { .. }, RefusalName::NotSynthesisable) |
        (CheckRefusal::UnknownConstant { .. }, RefusalName::UnknownConstant) |
        (CheckRefusal::OutOfFragment { .. }, RefusalName::OutOfFragment) |
        (CheckRefusal::UnboundIndex { .. }, RefusalName::UnboundIndex) |
        (CheckRefusal::BudgetExceeded { .. }, RefusalName::BudgetExceeded) |
        (CheckRefusal::DanglingNode { .. }, RefusalName::DanglingNode) |
        (CheckRefusal::AdmissionOrder { .. }, RefusalName::AdmissionOrder) |
        (CheckRefusal::MachineInvariant, RefusalName::MachineInvariant) |
        (CheckRefusal::SortMismatch { .. }, RefusalName::SortMismatch) |
        (CheckRefusal::LevelMismatch { .. }, RefusalName::LevelMismatch) |
        (CheckRefusal::DependentBind { .. }, RefusalName::DependentBind) |
        (CheckRefusal::Undecided { .. }, RefusalName::Undecided) |
        (CheckRefusal::FamilyArity { .. }, RefusalName::FamilyArity) |
        (CheckRefusal::FamilyArgumentClassifier { .. },
        RefusalName::FamilyArgumentClassifier) | (CheckRefusal::StaticLambdaArgument { ..
        }, RefusalName::StaticLambdaArgument) | (CheckRefusal::StaticClassifierExpected {
        .. }, RefusalName::StaticClassifierExpected) | (CheckRefusal::PathCode(_), RefusalName::PathCode)
        | (CheckRefusal::NotADataType(_), RefusalName::NotADataType)
        | (CheckRefusal::DataKindNotUniverse(_), RefusalName::DataKindNotUniverse)
        | (CheckRefusal::DataFieldLevel { .. }, RefusalName::DataFieldLevel)
        | (CheckRefusal::DataArgumentArity(_), RefusalName::DataArgumentArity)
        | (CheckRefusal::UnknownConstructor { .. }, RefusalName::UnknownConstructor)
        | (CheckRefusal::ConstructorArity(_), RefusalName::ConstructorArity)
        | (CheckRefusal::NonExhaustiveDataCase(_), RefusalName::NonExhaustiveDataCase)
        | (CheckRefusal::AbsentRecordField(_), RefusalName::AbsentRecordField)
        | (CheckRefusal::MissingRecordField { .. }, RefusalName::MissingRecordField)
    )
},
)]
const fn checking_name(refusal: CheckRefusal) -> RefusalName
{
    match refusal {
        | CheckRefusal::NotADataType(_) => RefusalName::NotADataType,
        | CheckRefusal::DataKindNotUniverse(_) => RefusalName::DataKindNotUniverse,
        | CheckRefusal::DataFieldLevel { .. } => RefusalName::DataFieldLevel,
        | CheckRefusal::DataArgumentArity(_) => RefusalName::DataArgumentArity,
        | CheckRefusal::UnknownConstructor { .. } => RefusalName::UnknownConstructor,
        | CheckRefusal::ConstructorArity(_) => RefusalName::ConstructorArity,
        | CheckRefusal::NonExhaustiveDataCase(_) => RefusalName::NonExhaustiveDataCase,
        | CheckRefusal::AbsentRecordField(_) => RefusalName::AbsentRecordField,
        | CheckRefusal::MissingRecordField { .. } => RefusalName::MissingRecordField,
        | CheckRefusal::PathCode(_) => RefusalName::PathCode,
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
        | CheckRefusal::FamilyArity { .. } => RefusalName::FamilyArity,
        | CheckRefusal::FamilyArgumentClassifier { .. } => RefusalName::FamilyArgumentClassifier,
        | CheckRefusal::StaticLambdaArgument { .. } => RefusalName::StaticLambdaArgument,
        | CheckRefusal::StaticClassifierExpected { .. } => RefusalName::StaticClassifierExpected,
    }
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;
    use alloc::string::ToString as _;
    use core::fmt;

    use gandr_kernel_term::StringLiteral;
    use gandr_surface_syntax::ByteOffset;
    use quenchant_shape::shape::Maybe;

    use super::RefusalName;
    use super::refusal_name;
    use crate::expectation::ExpectationSchema;
    use crate::fixture::RefusingWriter;
    use crate::fixture::span;
    use crate::root::CorpusRoot;

    #[test]
    fn root_refusal_names_every_admitted_schema()
    {
        let at = span(ByteOffset::from(11_usize), ByteOffset::from(29_usize));
        let refusal = CorpusRoot::Strict
            .admit(ExpectationSchema::Owes, at)
            .expect_err("owes is forbidden under the strict root");
        let rendered = refusal.to_string();
        for admitted in [ExpectationSchema::Checks, ExpectationSchema::Runs] {
            assert_eq!(CorpusRoot::Strict.admit(admitted, at), Ok(()));
            assert!(
                rendered.contains(&admitted.to_string()),
                "the diagnostic must name each admitted schema: {admitted}"
            );
        }
        assert!(rendered.contains(&at.to_string()));
        assert_eq!(
            fmt::Write::write_fmt(&mut RefusingWriter, format_args!("{refusal}")),
            Err(fmt::Error)
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
