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
//! A `refuses` payload names a refusal by its variant: `RefusalName` holds one
//! name per refusal the lowering, the checker and this crate raise, spelled as
//! the variant is, and a payload is matched byte for byte — no case folding,
//! trimming or prefix match — so a near miss names nothing and the fixture
//! fails with `ExpectationFault::UnknownRefusal` rather than settling on a
//! guess. The maps from each producer's refusal type to its name are exhaustive
//! matches without a fallback arm, so a refusal added upstream fails to compile
//! here until it is named. The lowering's `OutOfFragment` and the checker's
//! `OutOfFragment` are one name, as are the two `BudgetExceeded`: an
//! expectation states which refusal a declaration carries, not which pass
//! noticed it, and the produced class distinguishes nothing the name would need
//! to.
//!
//! The alternatives were free text matched against a refusal's rendering, which
//! breaks whenever a message is reworded, and a name per producer and variant,
//! which makes a fixture restate the pipeline's pass order. The choice reverses
//! if two producers' same-named refusals come to mean different things, at
//! which point the names split.
//!
//! # The vocabulary follows the producers
//!
//! The maps from each producer's refusals to their names are exhaustive,
//! wildcard-free matches, so a refusal variant added upstream fails to compile
//! here until it is named.
//!
//! # Native universe-path refusals
//!
//! `PathCode` is the closed vocabulary name for a malformed native
//! universe-path endpoint. The refusal table includes its producer variant,
//! spelling and malformed-source class; it is not renamed to a generic
//! unsupported-form error. Sums, injections and case are admitted by the
//! checker and do not appear as `UnadmittedFormer` alternatives.
//!
//! **Choice.** Preserve the checker’s refusal identity through settlement
//! instead of matching rendered prose. Native `Path_U` forms are programmatic
//! core inputs, not new source grammar, so a vocabulary witness is distinct
//! from a source-reachability claim. **Reversal.** Source fixtures for paths
//! enter when the parser and lowering acquire their syntax; the kernel’s code,
//! bridge, higher-field, funext, Flow and List rule-language witnesses remain
//! at their owning boundaries.

use core::error::Error;
use core::fmt;

use anodized::spec;
use gandr_core_checker::CheckRefusal;
use gandr_core_checker::access::AccessDefect;
use gandr_core_checker::codata::CodataFault;
use gandr_core_checker::session::LinearityDefect;
use gandr_core_checker::session::ProtocolDefect;
use gandr_core_checker::ua::StratumDefect;
use gandr_core_checker::ua::UaDefect;
use gandr_core_checker::worlds::LocatedDefect;
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
    /// root, which admits `checks`, `runs` and `normalizes`.
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
            Self::ExpectationOutsideFixtureRoot { .. } => FailureClass::MalformedSource,
        }
    }
}

impl fmt::Display for CorpusRefusal
{
    /// Writes the refusal and the schema it refuses.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the rejected schema and names every schema admitted by
    ///   the strict root; the source span is the diagnostic's locus and never
    ///   appears in the text.
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
    ///   exact identifier and admitted alternatives and omits the source range,
    ///   without fixing English sentence wording.
    /// - witness: `refusal::tests::root_refusal_names_every_admitted_schema`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::ExpectationOutsideFixtureRoot { schema, .. } => write!(
                f,
                "`{schema}` states an expectation the strict root refuses; only `checks`, `runs` and `normalizes` are admitted outside the fixture root"
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
/// - witness: `refusal::tests::every_refusal_spelling_reads_as_the_text_that_names_it`
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
    /// The checker reports `RuleNotPresentable`.
    RuleNotPresentable,
    /// The checker reports `RuleNotRespected`.
    RuleNotRespected,
    /// The checker reports `NotApart`.
    NotApart,
    /// The checker reports `LoopNotRespected`.
    LoopNotRespected,
    /// The checker reports `LoopUndecided`.
    LoopUndecided,
    /// The checker reports `AbstractKindNotUniverse`.
    AbstractKindNotUniverse,
    /// The checker reports `RepresentationAboveKind`.
    RepresentationAboveKind,
    /// The checker reports `NotAnAbstractType`.
    NotAnAbstractType,
    /// The checker reports `SealSiteRepeated`.
    SealSiteRepeated,
    /// The checker reports `DataArgumentArity`.
    DataArgumentArity,
    /// The checker reports `UnknownConstructor`.
    UnknownConstructor,
    /// The checker reports `ConstructorArity`.
    ConstructorArity,
    /// The checker reports `IndexedCase`.
    IndexedCase,
    /// The checker reports `NonExhaustiveDataCase`.
    NonExhaustiveDataCase,
    /// The checker reports `UndecidedCoverage`.
    UndecidedCoverage,
    /// The checker reports `AbsentRecordField`.
    AbsentRecordField,
    /// The checker reports `AbsentTupleComponent`.
    AbsentTupleComponent,
    /// The checker reports `MissingRecordField`.
    MissingRecordField,
    /// A data declaration's own family occurs under a function's domain where
    /// no stage reaches it.
    NegativeOccurrence,
    /// A data declaration's own family occurs nested where no stage reaches it.
    NestedOccurrence,
    /// A data declaration's own family occurs inside a term a type reads.
    IndexOccurrence,
    /// A data declaration's own family is applied off its parameters.
    NonUniformOccurrence,
    /// A data declaration names a position after its own.
    CrossBlockReference,
    /// A value does not stand below the stage its structural recursion wants.
    StageNotBelow,
    /// An operation absent from its interface.
    UnknownOperation,
    /// Handler clauses do not cover their interface exactly.
    HandlerCoverage,
    /// A capture without an answer delimiter.
    ShiftWithoutReset,
    /// A stack frame's result depends on its discharged binder.
    DependentStack,
    /// A native path endpoint is not a closed first-order code.
    PathCode,
    /// Reflexivity met a path type whose endpoints its point does not both
    /// convert to.
    EndpointMismatch,
    /// A compound endpoint whose computation returns no pure value.
    CompoundEndpoint,
    /// A function extensionality past the first-order boundary, where no
    /// finite coverage decides it.
    FunextUnsupported,
    /// A function extensionality whose functions disagree at some covering
    /// input: the rule's verdict.
    PointwiseDistinct,
    /// A universe equivalence the rule does not decide.
    EquivUnsupported,
    /// A universe equivalence over a recursive code.
    UncertifiedStratum,
    /// A universe equivalence whose round trip does not return its input.
    RoundTripDistinct,
    /// A telescope transport's second identity that does not lie over its
    /// path.
    NotOver,
    /// A term standing at a capability type that is no capability
    /// hypothesis.
    CapabilityForged,
    /// A capability standing where one granting more is expected.
    CapabilityAmplified,
    /// An operation exercised through a capability that does not grant it.
    CapabilityOutsideAuthority,
    /// A scoped capability that would outlive its region.
    CapabilityEscaped,
    /// A capability of the consumable grade.
    CapabilityConsumable,
    /// A held capability claiming authority the host did not grant.
    CapabilityUngranted,
    /// A `bisim` relating two protocols that are not bisimilar.
    SessionNotEquivalent,
    /// A `sim` whose source does not simulate its target.
    SessionNotSubtype,
    /// A session statement or flow over something other than a session code.
    SessionCodeExpected,
    /// A ride whose motive uses the moving endpoint other than covariantly.
    NonCovariantMotive,
    /// A ride whose motive the checker cannot move.
    RideUnsupported,
    /// A recorded run the protocol does not admit.
    RunNotAdmitted,
    /// A `forward` whose translator the rule cannot image.
    ForwardUnsupported,
    /// A function flow's boundary that runs against its variance.
    Boundary,
    /// Univalence at a degree no shape of the catalogue reaches.
    UncertifiedDegree,
    /// Univalence over a catalogue whose site fails the corolla or the Segal
    /// condition.
    UncertifiedCondition,
    /// Univalence over a catalogue past the one the checker enumerates.
    UncertifiedAllowance,
    /// A translator record naming a generator its description does not
    /// declare.
    UnknownGenerator,
    /// A generator whose corolla is past the catalogue's bound.
    PastTheBound,
    /// Two species with different numbers of elements at a corolla.
    CorollaCardinality,
    /// A corolla whose translators are missing on one side or given twice.
    CorollaTables,
    /// Translator tables that are not mutually inverse.
    NotInverse,
    /// Translator tables that do not commute with a corolla's automorphisms.
    NotNatural,
    /// A translator that returns no element of its target code.
    TranslatorStuck,
    /// A run with no computation enclosing it to run before.
    UnenclosedRun,
    /// A term name no binder or earlier declaration answers.
    UnresolvedName,
    /// A documentation link to a name nothing declares.
    UnresolvedDocLink,
    /// A type head no table entry answers.
    UnresolvedTypeHead,
    /// A second signature for one name.
    DuplicateSignature,
    /// A second definition for one name.
    DuplicateDefinition,
    /// A second import of one alias.
    DuplicateImportAlias,
    /// A declaration of a source whose path import resolves to no source.
    ImportUnresolved,
    /// A declaration of a source whose imports lead back to it.
    ImportCycle,
    /// A name an import binds and another binding of the source binds too.
    ImportShadows,
    /// A name an import answers with a declaration its source does not export.
    UnexportedName,
    /// A declared name or binder over a builtin, under the reject policy; a
    /// family named as a builtin type the grammar spells as a tile, always.
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
    /// A module binding applying a name that is not a functor.
    NotAFunctor,
    /// A path read off a functor application rather than off its binding.
    ProjectionFromApplication,
    /// A module ascription form the fragment does not read yet.
    UnreadAscription,
    /// A model signature component the derivation cannot state.
    UnstatedComponent,
    /// A type family whose parameters disagree with the indices its kind
    /// states.
    FamilyTelescope,
    /// A top-level module named with a lowercase initial.
    LowercaseModuleName,
    /// A match some scrutinee value reaches no arm of.
    NonExhaustiveMatch,
    /// A recursive definition's own name written without a descent claim.
    UnmarkedSelfReference,
    /// A recursive definition whose claims descend on two parameters.
    DescentOnSeveralParameters,
    /// Code after a statement every path of which exits.
    Unreachable,
    /// A `break` or a `continue` on no path through a loop's body.
    OutsideLoop,
    /// A `become` in a handled subject, or a `break` or a `continue` there
    /// whose loop holds the scope.
    AcrossHandler,
    /// A path matched against reflexivity, `here`: axiom K.
    WithoutK,
    /// A directed cell `-->` between two terms of a `data` block.
    DirectedCell,
    /// A cell `<->` of a `data` block between two distinct terms.
    CellNotALoop,
    /// A rule of a block's rules the path order does not orient, so the
    /// rules may not end.
    RulesUnoriented,
    /// Two rules of a block rewriting one term to two normal forms.
    RulesDiverge,
    /// A critical pair of a block's rules its step budget left undecided.
    RulesUndecided,
    /// A work allowance ran out, the lowering's or the checker's.
    BudgetExceeded,
    /// A tree lowered under another grammar than it was molded under.
    GrammarMismatch,
    /// A mold the grammar's table does not hold.
    UnknownMold,
    /// A declaration the lowering minted neither a type nor a body for, and
    /// refused nothing in.
    Unminted,
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
    /// Two rows disagree on the operation types of a shared interface.
    EffectSignatureConflict,
    /// An action the endpoint's session type does not admit.
    SessionMismatch,
    /// A selection of a label the endpoint's state does not offer.
    UnofferedLabel,
    /// An offer whose arms are not exactly the labels its state offers.
    OfferArms,
    /// A half of a fork that finished with an endpoint unconsumed.
    LinearResidue,
    /// An endpoint acted on after it was closed.
    UsedAfterClose,
    /// An endpoint named twice in one action.
    EndpointUsedTwice,
    /// An endpoint named where its use may run other than once.
    CapturedEndpoint,
    /// An endpoint, or a session type, sent as a payload.
    Delegation,
    /// An endpoint read as a value outside an action.
    EndpointAsValue,
    /// Two arms of an offer leaving an endpoint in different states.
    ArmsDisagree,
    /// A declaration whose type is a session type.
    UnrestrictedEndpoint,
    /// An action naming a linear index no fork bound.
    UnboundEndpoint,
    /// An access naming a linear slot that holds no value.
    NotHeld,
    /// A held value read, or accessed again, while an access lends it.
    HeldLent,
    /// A held value named where its holding may run other than once.
    HeldCaptured,
    /// A view named where it would outlive its access's body.
    ViewEscaped,
    /// An access's body ending with its view neither resumed nor aborted.
    ViewUnended,
    /// A view used after its resume or abort.
    ViewSpent,
    /// A resume or an abort naming a linear slot that is no view.
    NotAView,
    /// An access's unwind performing an effect.
    UnwindEffect,
    /// A codata application whose head names no admitted codata declaration.
    CodataUndeclared,
    /// A codata declaration whose kind is not a computation universe.
    CodataKindNotUniverse,
    /// A codata declaration that states no observation.
    CodataWithoutObservations,
    /// A codata declaration naming itself other than at an observation's
    /// result at its parameter variables.
    CodataOccurrence,
    /// A codata observation above the declared universe.
    CodataObservationLevel,
    /// A codata application at another arity than its declaration's
    /// telescope.
    CodataArity,
    /// A value crossing to a world its type does not reach.
    Immobile,
    /// A migration with no capability for its world.
    CapabilityMissing,
    /// A migration under a former that may run it other than once.
    CapabilityCaptured,
    /// A hypothesis or a resident used at a world other than its own.
    Elsewhere,
    /// A hold checked against a handle at another world.
    HoldElsewhere,
    /// A hold or a `leta` at the host's world.
    Unlocated,
    /// A world position no world declaration holds.
    UndeclaredWorld,
    /// A host entry naming a world the source declares nowhere.
    HostWorldUndeclared,
    /// A `mobile` mark over a representation that does not cross.
    MarkUnfounded,
    /// An entry named from another declaration.
    EntryNamed,
    /// A stated entry the host's does not hold.
    EntryUngranted,
    /// A `leta` of a value whose type is no handle.
    NotAHandle,
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
    pub const VOCABULARY: [Self; 165_usize] = [
        Self::NotADataType,
        Self::DataKindNotUniverse,
        Self::DataFieldLevel,
        Self::RuleNotPresentable,
        Self::RuleNotRespected,
        Self::NotApart,
        Self::LoopNotRespected,
        Self::LoopUndecided,
        Self::AbstractKindNotUniverse,
        Self::RepresentationAboveKind,
        Self::NotAnAbstractType,
        Self::SealSiteRepeated,
        Self::DataArgumentArity,
        Self::UnknownConstructor,
        Self::ConstructorArity,
        Self::IndexedCase,
        Self::NonExhaustiveDataCase,
        Self::UndecidedCoverage,
        Self::AbsentRecordField,
        Self::AbsentTupleComponent,
        Self::MissingRecordField,
        Self::NegativeOccurrence,
        Self::NestedOccurrence,
        Self::IndexOccurrence,
        Self::NonUniformOccurrence,
        Self::CrossBlockReference,
        Self::StageNotBelow,
        Self::PathCode,
        Self::EndpointMismatch,
        Self::CompoundEndpoint,
        Self::FunextUnsupported,
        Self::PointwiseDistinct,
        Self::EquivUnsupported,
        Self::UncertifiedStratum,
        Self::RoundTripDistinct,
        Self::NotOver,
        Self::UncertifiedDegree,
        Self::UncertifiedCondition,
        Self::UncertifiedAllowance,
        Self::UnknownGenerator,
        Self::PastTheBound,
        Self::CorollaCardinality,
        Self::CorollaTables,
        Self::NotInverse,
        Self::NotNatural,
        Self::TranslatorStuck,
        Self::UnenclosedRun,
        Self::CapabilityForged,
        Self::CapabilityAmplified,
        Self::CapabilityOutsideAuthority,
        Self::CapabilityEscaped,
        Self::CapabilityConsumable,
        Self::CapabilityUngranted,
        Self::SessionNotEquivalent,
        Self::SessionNotSubtype,
        Self::SessionCodeExpected,
        Self::NonCovariantMotive,
        Self::RideUnsupported,
        Self::RunNotAdmitted,
        Self::ForwardUnsupported,
        Self::Boundary,
        Self::UnresolvedName,
        Self::UnresolvedDocLink,
        Self::UnresolvedTypeHead,
        Self::DuplicateSignature,
        Self::DuplicateDefinition,
        Self::DuplicateImportAlias,
        Self::ImportUnresolved,
        Self::ImportCycle,
        Self::ImportShadows,
        Self::UnexportedName,
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
        Self::NotAFunctor,
        Self::ProjectionFromApplication,
        Self::UnreadAscription,
        Self::UnstatedComponent,
        Self::FamilyTelescope,
        Self::LowercaseModuleName,
        Self::NonExhaustiveMatch,
        Self::UnmarkedSelfReference,
        Self::DescentOnSeveralParameters,
        Self::Unreachable,
        Self::OutsideLoop,
        Self::AcrossHandler,
        Self::WithoutK,
        Self::DirectedCell,
        Self::CellNotALoop,
        Self::RulesUnoriented,
        Self::RulesDiverge,
        Self::RulesUndecided,
        Self::BudgetExceeded,
        Self::GrammarMismatch,
        Self::UnknownMold,
        Self::Unminted,
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
        Self::EffectSignatureConflict,
        Self::UnknownOperation,
        Self::HandlerCoverage,
        Self::ShiftWithoutReset,
        Self::DependentStack,
        Self::SessionMismatch,
        Self::UnofferedLabel,
        Self::OfferArms,
        Self::LinearResidue,
        Self::UsedAfterClose,
        Self::EndpointUsedTwice,
        Self::CapturedEndpoint,
        Self::Delegation,
        Self::EndpointAsValue,
        Self::ArmsDisagree,
        Self::UnrestrictedEndpoint,
        Self::UnboundEndpoint,
        Self::NotHeld,
        Self::HeldLent,
        Self::HeldCaptured,
        Self::ViewEscaped,
        Self::ViewUnended,
        Self::ViewSpent,
        Self::NotAView,
        Self::UnwindEffect,
        Self::CodataUndeclared,
        Self::CodataKindNotUniverse,
        Self::CodataWithoutObservations,
        Self::CodataOccurrence,
        Self::CodataObservationLevel,
        Self::CodataArity,
        Self::Immobile,
        Self::CapabilityMissing,
        Self::CapabilityCaptured,
        Self::Elsewhere,
        Self::HoldElsewhere,
        Self::Unlocated,
        Self::UndeclaredWorld,
        Self::HostWorldUndeclared,
        Self::MarkUnfounded,
        Self::EntryNamed,
        Self::EntryUngranted,
        Self::NotAHandle,
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
        (Self::UnresolvedDocLink, b"UnresolvedDocLink") |
        (Self::UnresolvedTypeHead, b"UnresolvedTypeHead") | (Self::DuplicateSignature,
        b"DuplicateSignature") | (Self::DuplicateDefinition, b"DuplicateDefinition") |
        (Self::DuplicateImportAlias, b"DuplicateImportAlias") | (Self::ImportUnresolved,
        b"ImportUnresolved") | (Self::ImportCycle, b"ImportCycle") | (Self::ImportShadows,
        b"ImportShadows") | (Self::UnexportedName, b"UnexportedName") | (Self::ShadowedBuiltin,
        b"ShadowedBuiltin") | (Self::OutOfFragment, b"OutOfFragment") |
        (Self::GradedBridge, b"GradedBridge") | (Self::MalformedLiteral,
        b"MalformedLiteral") | (Self::MalformedForm, b"MalformedForm") |
        (Self::UnknownAttribute, b"UnknownAttribute") | (Self::DuplicateAttribute,
        b"DuplicateAttribute") | (Self::MissingPayload, b"MissingPayload") |
        (Self::NonValuePayload, b"NonValuePayload") | (Self::IllTypedPayload,
        b"IllTypedPayload") | (Self::ForwardMemberReference, b"ForwardMemberReference") |
        (Self::UnknownMember, b"UnknownMember") | (Self::NotAFunctor, b"NotAFunctor")
        | (Self::ProjectionFromApplication, b"ProjectionFromApplication")
        | (Self::UnreadAscription,
        b"UnreadAscription") | (Self::UnstatedComponent, b"UnstatedComponent") |
        (Self::FamilyTelescope, b"FamilyTelescope") | (Self::LowercaseModuleName,
        b"LowercaseModuleName") |
        (Self::NonExhaustiveMatch, b"NonExhaustiveMatch") |
        (Self::UnmarkedSelfReference, b"UnmarkedSelfReference") |
        (Self::DescentOnSeveralParameters, b"DescentOnSeveralParameters") |
        (Self::Unreachable, b"Unreachable") |
        (Self::OutsideLoop, b"OutsideLoop") |
        (Self::AcrossHandler, b"AcrossHandler") |
        (Self::WithoutK, b"WithoutK") |
        (Self::DirectedCell, b"DirectedCell") |
        (Self::CellNotALoop, b"CellNotALoop") |
        (Self::RulesUnoriented, b"RulesUnoriented") |
        (Self::RulesDiverge, b"RulesDiverge") |
        (Self::RulesUndecided, b"RulesUndecided") |
        (Self::BudgetExceeded, b"BudgetExceeded") | (Self::GrammarMismatch,
        b"GrammarMismatch") | (Self::UnknownMold, b"UnknownMold") | (Self::Unminted, b"Unminted") | (Self::TypeMismatch,
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
        | (Self::RuleNotPresentable, b"RuleNotPresentable")
        | (Self::RuleNotRespected, b"RuleNotRespected")
        | (Self::NotApart, b"NotApart")
        | (Self::LoopNotRespected, b"LoopNotRespected")
        | (Self::LoopUndecided, b"LoopUndecided")
        | (Self::AbstractKindNotUniverse, b"AbstractKindNotUniverse")
        | (Self::RepresentationAboveKind, b"RepresentationAboveKind")
        | (Self::NotAnAbstractType, b"NotAnAbstractType")
        | (Self::SealSiteRepeated, b"SealSiteRepeated")
        | (Self::DataArgumentArity, b"DataArgumentArity")
        | (Self::UnknownConstructor, b"UnknownConstructor")
        | (Self::ConstructorArity, b"ConstructorArity")
        | (Self::IndexedCase, b"IndexedCase")
        | (Self::NonExhaustiveDataCase, b"NonExhaustiveDataCase")
        | (Self::UndecidedCoverage, b"UndecidedCoverage")
        | (Self::AbsentRecordField, b"AbsentRecordField")
        | (Self::AbsentTupleComponent, b"AbsentTupleComponent")
        | (Self::MissingRecordField, b"MissingRecordField")
        | (Self::NegativeOccurrence, b"NegativeOccurrence")
        | (Self::NestedOccurrence, b"NestedOccurrence")
        | (Self::IndexOccurrence, b"IndexOccurrence")
        | (Self::NonUniformOccurrence, b"NonUniformOccurrence")
        | (Self::CrossBlockReference, b"CrossBlockReference")
        | (Self::StageNotBelow, b"StageNotBelow")
        | (Self::EffectSignatureConflict, b"EffectSignatureConflict")
        | (Self::UnknownOperation, b"UnknownOperation") | (Self::HandlerCoverage, b"HandlerCoverage")
        | (Self::ShiftWithoutReset, b"ShiftWithoutReset") | (Self::DependentStack, b"DependentStack")
        | (Self::EndpointMismatch, b"EndpointMismatch")
        | (Self::CompoundEndpoint, b"CompoundEndpoint")
        | (Self::FunextUnsupported, b"FunextUnsupported")
        | (Self::PointwiseDistinct, b"PointwiseDistinct")
        | (Self::EquivUnsupported, b"EquivUnsupported")
        | (Self::UncertifiedStratum, b"UncertifiedStratum")
        | (Self::RoundTripDistinct, b"RoundTripDistinct")
        | (Self::NotOver, b"NotOver")
        | (Self::UncertifiedDegree, b"UncertifiedDegree")
        | (Self::UncertifiedCondition, b"UncertifiedCondition")
        | (Self::UncertifiedAllowance, b"UncertifiedAllowance")
        | (Self::UnknownGenerator, b"UnknownGenerator")
        | (Self::PastTheBound, b"PastTheBound")
        | (Self::CorollaCardinality, b"CorollaCardinality")
        | (Self::CorollaTables, b"CorollaTables")
        | (Self::NotInverse, b"NotInverse")
        | (Self::NotNatural, b"NotNatural")
        | (Self::TranslatorStuck, b"TranslatorStuck")
        | (Self::UnenclosedRun, b"UnenclosedRun")
        | (Self::SessionMismatch, b"SessionMismatch")
        | (Self::UnofferedLabel, b"UnofferedLabel")
        | (Self::OfferArms, b"OfferArms")
        | (Self::LinearResidue, b"LinearResidue")
        | (Self::UsedAfterClose, b"UsedAfterClose")
        | (Self::EndpointUsedTwice, b"EndpointUsedTwice")
        | (Self::CapturedEndpoint, b"CapturedEndpoint")
        | (Self::Delegation, b"Delegation")
        | (Self::EndpointAsValue, b"EndpointAsValue")
        | (Self::ArmsDisagree, b"ArmsDisagree")
        | (Self::UnrestrictedEndpoint, b"UnrestrictedEndpoint")
        | (Self::UnboundEndpoint, b"UnboundEndpoint")
        | (Self::NotHeld, b"NotHeld")
        | (Self::HeldLent, b"HeldLent")
        | (Self::HeldCaptured, b"HeldCaptured")
        | (Self::ViewEscaped, b"ViewEscaped")
        | (Self::ViewUnended, b"ViewUnended")
        | (Self::ViewSpent, b"ViewSpent")
        | (Self::NotAView, b"NotAView")
        | (Self::UnwindEffect, b"UnwindEffect")
        | (Self::CodataUndeclared, b"CodataUndeclared")
        | (Self::CodataKindNotUniverse, b"CodataKindNotUniverse")
        | (Self::CodataWithoutObservations, b"CodataWithoutObservations")
        | (Self::CodataOccurrence, b"CodataOccurrence")
        | (Self::CodataObservationLevel, b"CodataObservationLevel")
        | (Self::CodataArity, b"CodataArity")
        | (Self::Immobile, b"Immobile")
        | (Self::CapabilityMissing, b"CapabilityMissing")
        | (Self::CapabilityCaptured, b"CapabilityCaptured")
        | (Self::Elsewhere, b"Elsewhere")
        | (Self::HoldElsewhere, b"HoldElsewhere")
        | (Self::Unlocated, b"Unlocated")
        | (Self::UndeclaredWorld, b"UndeclaredWorld")
        | (Self::HostWorldUndeclared, b"HostWorldUndeclared")
        | (Self::MarkUnfounded, b"MarkUnfounded")
        | (Self::EntryNamed, b"EntryNamed")
        | (Self::EntryUngranted, b"EntryUngranted")
        | (Self::NotAHandle, b"NotAHandle")
        | (Self::CapabilityForged, b"CapabilityForged")
        | (Self::CapabilityAmplified, b"CapabilityAmplified")
        | (Self::CapabilityOutsideAuthority, b"CapabilityOutsideAuthority")
        | (Self::CapabilityEscaped, b"CapabilityEscaped")
        | (Self::CapabilityConsumable, b"CapabilityConsumable")
        | (Self::CapabilityUngranted, b"CapabilityUngranted")
        | (Self::SessionNotEquivalent, b"SessionNotEquivalent")
        | (Self::SessionNotSubtype, b"SessionNotSubtype")
        | (Self::SessionCodeExpected, b"SessionCodeExpected")
        | (Self::NonCovariantMotive, b"NonCovariantMotive")
        | (Self::RideUnsupported, b"RideUnsupported")
        | (Self::RunNotAdmitted, b"RunNotAdmitted")
        | (Self::ForwardUnsupported, b"ForwardUnsupported")
        | (Self::Boundary, b"Boundary")
    )
},
    )]
    #[inline]
    #[must_use]
    pub const fn spelling(self) -> RefusalSpelling
    {
        RefusalSpelling(match self {
            Self::NotADataType => "NotADataType",
            Self::DataKindNotUniverse => "DataKindNotUniverse",
            Self::DataFieldLevel => "DataFieldLevel",
            Self::RuleNotPresentable => "RuleNotPresentable",
            Self::RuleNotRespected => "RuleNotRespected",
            Self::NotApart => "NotApart",
            Self::LoopNotRespected => "LoopNotRespected",
            Self::LoopUndecided => "LoopUndecided",
            Self::AbstractKindNotUniverse => "AbstractKindNotUniverse",
            Self::RepresentationAboveKind => "RepresentationAboveKind",
            Self::NotAnAbstractType => "NotAnAbstractType",
            Self::SealSiteRepeated => "SealSiteRepeated",
            Self::DataArgumentArity => "DataArgumentArity",
            Self::UnknownConstructor => "UnknownConstructor",
            Self::ConstructorArity => "ConstructorArity",
            Self::IndexedCase => "IndexedCase",
            Self::NonExhaustiveDataCase => "NonExhaustiveDataCase",
            Self::UndecidedCoverage => "UndecidedCoverage",
            Self::AbsentRecordField => "AbsentRecordField",
            Self::AbsentTupleComponent => "AbsentTupleComponent",
            Self::MissingRecordField => "MissingRecordField",
            Self::NegativeOccurrence => "NegativeOccurrence",
            Self::NestedOccurrence => "NestedOccurrence",
            Self::IndexOccurrence => "IndexOccurrence",
            Self::NonUniformOccurrence => "NonUniformOccurrence",
            Self::CrossBlockReference => "CrossBlockReference",
            Self::StageNotBelow => "StageNotBelow",
            Self::UnknownOperation => "UnknownOperation",
            Self::HandlerCoverage => "HandlerCoverage",
            Self::ShiftWithoutReset => "ShiftWithoutReset",
            Self::DependentStack => "DependentStack",
            Self::EffectSignatureConflict => "EffectSignatureConflict",
            Self::UnresolvedName => "UnresolvedName",
            Self::UnresolvedDocLink => "UnresolvedDocLink",
            Self::UnresolvedTypeHead => "UnresolvedTypeHead",
            Self::DuplicateSignature => "DuplicateSignature",
            Self::DuplicateDefinition => "DuplicateDefinition",
            Self::DuplicateImportAlias => "DuplicateImportAlias",
            Self::ImportUnresolved => "ImportUnresolved",
            Self::ImportCycle => "ImportCycle",
            Self::ImportShadows => "ImportShadows",
            Self::UnexportedName => "UnexportedName",
            Self::PathCode => "PathCode",
            Self::EndpointMismatch => "EndpointMismatch",
            Self::CompoundEndpoint => "CompoundEndpoint",
            Self::FunextUnsupported => "FunextUnsupported",
            Self::PointwiseDistinct => "PointwiseDistinct",
            Self::EquivUnsupported => "EquivUnsupported",
            Self::UncertifiedStratum => "UncertifiedStratum",
            Self::RoundTripDistinct => "RoundTripDistinct",
            Self::NotOver => "NotOver",
            Self::UncertifiedDegree => "UncertifiedDegree",
            Self::UncertifiedCondition => "UncertifiedCondition",
            Self::UncertifiedAllowance => "UncertifiedAllowance",
            Self::UnknownGenerator => "UnknownGenerator",
            Self::PastTheBound => "PastTheBound",
            Self::CorollaCardinality => "CorollaCardinality",
            Self::CorollaTables => "CorollaTables",
            Self::NotInverse => "NotInverse",
            Self::NotNatural => "NotNatural",
            Self::TranslatorStuck => "TranslatorStuck",
            Self::UnenclosedRun => "UnenclosedRun",
            Self::SessionMismatch => "SessionMismatch",
            Self::UnofferedLabel => "UnofferedLabel",
            Self::OfferArms => "OfferArms",
            Self::LinearResidue => "LinearResidue",
            Self::UsedAfterClose => "UsedAfterClose",
            Self::EndpointUsedTwice => "EndpointUsedTwice",
            Self::CapturedEndpoint => "CapturedEndpoint",
            Self::Delegation => "Delegation",
            Self::EndpointAsValue => "EndpointAsValue",
            Self::ArmsDisagree => "ArmsDisagree",
            Self::UnrestrictedEndpoint => "UnrestrictedEndpoint",
            Self::UnboundEndpoint => "UnboundEndpoint",
            Self::NotHeld => "NotHeld",
            Self::HeldLent => "HeldLent",
            Self::HeldCaptured => "HeldCaptured",
            Self::ViewEscaped => "ViewEscaped",
            Self::ViewUnended => "ViewUnended",
            Self::ViewSpent => "ViewSpent",
            Self::NotAView => "NotAView",
            Self::UnwindEffect => "UnwindEffect",
            Self::CodataUndeclared => "CodataUndeclared",
            Self::CodataKindNotUniverse => "CodataKindNotUniverse",
            Self::CodataWithoutObservations => "CodataWithoutObservations",
            Self::CodataOccurrence => "CodataOccurrence",
            Self::CodataObservationLevel => "CodataObservationLevel",
            Self::CodataArity => "CodataArity",
            Self::Immobile => "Immobile",
            Self::CapabilityMissing => "CapabilityMissing",
            Self::CapabilityCaptured => "CapabilityCaptured",
            Self::Elsewhere => "Elsewhere",
            Self::HoldElsewhere => "HoldElsewhere",
            Self::Unlocated => "Unlocated",
            Self::UndeclaredWorld => "UndeclaredWorld",
            Self::HostWorldUndeclared => "HostWorldUndeclared",
            Self::MarkUnfounded => "MarkUnfounded",
            Self::EntryNamed => "EntryNamed",
            Self::EntryUngranted => "EntryUngranted",
            Self::NotAHandle => "NotAHandle",
            Self::CapabilityForged => "CapabilityForged",
            Self::CapabilityAmplified => "CapabilityAmplified",
            Self::CapabilityOutsideAuthority => "CapabilityOutsideAuthority",
            Self::CapabilityEscaped => "CapabilityEscaped",
            Self::CapabilityConsumable => "CapabilityConsumable",
            Self::CapabilityUngranted => "CapabilityUngranted",
            Self::SessionNotEquivalent => "SessionNotEquivalent",
            Self::SessionNotSubtype => "SessionNotSubtype",
            Self::SessionCodeExpected => "SessionCodeExpected",
            Self::NonCovariantMotive => "NonCovariantMotive",
            Self::RideUnsupported => "RideUnsupported",
            Self::RunNotAdmitted => "RunNotAdmitted",
            Self::ForwardUnsupported => "ForwardUnsupported",
            Self::Boundary => "Boundary",
            Self::ShadowedBuiltin => "ShadowedBuiltin",
            Self::OutOfFragment => "OutOfFragment",
            Self::GradedBridge => "GradedBridge",
            Self::MalformedLiteral => "MalformedLiteral",
            Self::MalformedForm => "MalformedForm",
            Self::UnknownAttribute => "UnknownAttribute",
            Self::DuplicateAttribute => "DuplicateAttribute",
            Self::MissingPayload => "MissingPayload",
            Self::NonValuePayload => "NonValuePayload",
            Self::IllTypedPayload => "IllTypedPayload",
            Self::ForwardMemberReference => "ForwardMemberReference",
            Self::UnknownMember => "UnknownMember",
            Self::NotAFunctor => "NotAFunctor",
            Self::ProjectionFromApplication => "ProjectionFromApplication",
            Self::UnreadAscription => "UnreadAscription",
            Self::UnstatedComponent => "UnstatedComponent",
            Self::FamilyTelescope => "FamilyTelescope",
            Self::LowercaseModuleName => "LowercaseModuleName",
            Self::NonExhaustiveMatch => "NonExhaustiveMatch",
            Self::UnmarkedSelfReference => "UnmarkedSelfReference",
            Self::DescentOnSeveralParameters => "DescentOnSeveralParameters",
            Self::Unreachable => "Unreachable",
            Self::OutsideLoop => "OutsideLoop",
            Self::AcrossHandler => "AcrossHandler",
            Self::WithoutK => "WithoutK",
            Self::DirectedCell => "DirectedCell",
            Self::CellNotALoop => "CellNotALoop",
            Self::RulesUnoriented => "RulesUnoriented",
            Self::RulesDiverge => "RulesDiverge",
            Self::RulesUndecided => "RulesUndecided",
            Self::BudgetExceeded => "BudgetExceeded",
            Self::GrammarMismatch => "GrammarMismatch",
            Self::UnknownMold => "UnknownMold",
            Self::Unminted => "Unminted",
            Self::TypeMismatch => "TypeMismatch",
            Self::ShapeMismatch => "ShapeMismatch",
            Self::NotSynthesisable => "NotSynthesisable",
            Self::UnknownConstant => "UnknownConstant",
            Self::UnboundIndex => "UnboundIndex",
            Self::DanglingNode => "DanglingNode",
            Self::AdmissionOrder => "AdmissionOrder",
            Self::MachineInvariant => "MachineInvariant",
            Self::SortMismatch => "SortMismatch",
            Self::LevelMismatch => "LevelMismatch",
            Self::DependentBind => "DependentBind",
            Self::Undecided => "Undecided",
            Self::FamilyArity => "FamilyArity",
            Self::FamilyArgumentClassifier => "FamilyArgumentClassifier",
            Self::StaticLambdaArgument => "StaticLambdaArgument",
            Self::StaticClassifierExpected => "StaticClassifierExpected",
            Self::ExpectationOutsideFixtureRoot => "ExpectationOutsideFixtureRoot",
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
        (Self::Lowering(LoweringRefusal::UnresolvedDocLink { .. }),
        RefusalName::UnresolvedDocLink) |
        (Self::Lowering(LoweringRefusal::UnresolvedTypeHead { .. }),
        RefusalName::UnresolvedTypeHead) |
        (Self::Lowering(LoweringRefusal::DuplicateSignature { .. }),
        RefusalName::DuplicateSignature) |
        (Self::Lowering(LoweringRefusal::DuplicateDefinition { .. }),
        RefusalName::DuplicateDefinition) |
        (Self::Lowering(LoweringRefusal::DuplicateImportAlias { .. }),
        RefusalName::DuplicateImportAlias) |
        (Self::Lowering(LoweringRefusal::ImportUnresolved { .. }),
        RefusalName::ImportUnresolved) |
        (Self::Lowering(LoweringRefusal::ImportCycle { .. }), RefusalName::ImportCycle) |
        (Self::Lowering(LoweringRefusal::ImportShadows { .. }), RefusalName::ImportShadows) |
        (Self::Lowering(LoweringRefusal::UnexportedName { .. }),
        RefusalName::UnexportedName) |
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
        RefusalName::UnknownMember) | (Self::Lowering(LoweringRefusal::NotAFunctor { .. }),
        RefusalName::NotAFunctor) |
        (Self::Lowering(LoweringRefusal::ProjectionFromApplication { .. }),
        RefusalName::ProjectionFromApplication) |
        (Self::Lowering(LoweringRefusal::UnreadAscription {
        .. }), RefusalName::UnreadAscription) |
        (Self::Lowering(LoweringRefusal::UnstatedComponent { .. }),
        RefusalName::UnstatedComponent) |
        (Self::Lowering(LoweringRefusal::FamilyTelescope { .. }),
        RefusalName::FamilyTelescope) |
        (Self::Lowering(LoweringRefusal::LowercaseModuleName { .. }),
        RefusalName::LowercaseModuleName) |
        (Self::Lowering(LoweringRefusal::NonExhaustiveMatch { .. }),
        RefusalName::NonExhaustiveMatch) |
        (Self::Lowering(LoweringRefusal::UnmarkedSelfReference { .. }),
        RefusalName::UnmarkedSelfReference) |
        (Self::Lowering(LoweringRefusal::DescentOnSeveralParameters { .. }),
        RefusalName::DescentOnSeveralParameters) |
        (Self::Lowering(LoweringRefusal::Unreachable { .. }),
        RefusalName::Unreachable) |
        (Self::Lowering(LoweringRefusal::OutsideLoop { .. }),
        RefusalName::OutsideLoop) |
        (Self::Lowering(LoweringRefusal::AcrossHandler { .. }),
        RefusalName::AcrossHandler) |
        (Self::Lowering(LoweringRefusal::WithoutK { .. }),
        RefusalName::WithoutK) |
        (Self::Lowering(LoweringRefusal::DirectedCell { .. }),
        RefusalName::DirectedCell) |
        (Self::Lowering(LoweringRefusal::CellNotALoop { .. }),
        RefusalName::CellNotALoop) |
        (Self::Lowering(LoweringRefusal::RulesUnoriented { .. }),
        RefusalName::RulesUnoriented) |
        (Self::Lowering(LoweringRefusal::RulesDiverge { .. }),
        RefusalName::RulesDiverge) |
        (Self::Lowering(LoweringRefusal::RulesUndecided { .. }),
        RefusalName::RulesUndecided) |
        (Self::Lowering(LoweringRefusal::BudgetExceeded { .. }) |
        Self::Checking(CheckRefusal::BudgetExceeded { .. }), RefusalName::BudgetExceeded)
        | (Self::Lowering(LoweringRefusal::GrammarMismatch { .. }),
        RefusalName::GrammarMismatch) | (Self::Lowering(LoweringRefusal::UnknownMold { ..
        }), RefusalName::UnknownMold) | (Self::Lowering(LoweringRefusal::Unminted { .. }), RefusalName::Unminted) | (Self::Checking(CheckRefusal::PathCode(_)), RefusalName::PathCode) | (Self::Checking(CheckRefusal::TypeMismatch(_)),
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
        (Self::Checking(CheckRefusal::NotADataType(_)), RefusalName::NotADataType)
        | (Self::Checking(CheckRefusal::DataKindNotUniverse(_)), RefusalName::DataKindNotUniverse)
        | (Self::Checking(CheckRefusal::DataFieldLevel { .. }), RefusalName::DataFieldLevel)
        | (Self::Checking(CheckRefusal::RuleNotPresentable { .. }), RefusalName::RuleNotPresentable)
        | (Self::Checking(CheckRefusal::RuleNotRespected { .. }), RefusalName::RuleNotRespected)
        | (Self::Checking(CheckRefusal::NotApart { .. }), RefusalName::NotApart)
        | (Self::Checking(CheckRefusal::LoopNotRespected { .. }), RefusalName::LoopNotRespected)
        | (Self::Checking(CheckRefusal::LoopUndecided { .. }), RefusalName::LoopUndecided)
        | (Self::Checking(CheckRefusal::AbstractKindNotUniverse(_)), RefusalName::AbstractKindNotUniverse)
        | (Self::Checking(CheckRefusal::RepresentationAboveKind { .. }), RefusalName::RepresentationAboveKind)
        | (Self::Checking(CheckRefusal::NotAnAbstractType(_)), RefusalName::NotAnAbstractType)
        | (Self::Checking(CheckRefusal::SealSiteRepeated(_)), RefusalName::SealSiteRepeated)
        | (Self::Checking(CheckRefusal::DataArgumentArity(_)), RefusalName::DataArgumentArity)
        | (Self::Checking(CheckRefusal::UnknownConstructor { .. }), RefusalName::UnknownConstructor)
        | (Self::Checking(CheckRefusal::ConstructorArity(_)), RefusalName::ConstructorArity)
        | (Self::Checking(CheckRefusal::IndexedCase(_)), RefusalName::IndexedCase)
        | (Self::Checking(CheckRefusal::NonExhaustiveDataCase(_)), RefusalName::NonExhaustiveDataCase)
        | (Self::Checking(CheckRefusal::UndecidedCoverage(_)), RefusalName::UndecidedCoverage)
        | (Self::Checking(CheckRefusal::AbsentRecordField(_)), RefusalName::AbsentRecordField)
        | (Self::Checking(CheckRefusal::AbsentTupleComponent(_)), RefusalName::AbsentTupleComponent)
        | (Self::Checking(CheckRefusal::MissingRecordField { .. }), RefusalName::MissingRecordField)
        | (Self::Checking(CheckRefusal::NegativeOccurrence(_)), RefusalName::NegativeOccurrence)
        | (Self::Checking(CheckRefusal::NestedOccurrence(_)), RefusalName::NestedOccurrence)
        | (Self::Checking(CheckRefusal::IndexOccurrence(_)), RefusalName::IndexOccurrence)
        | (Self::Checking(CheckRefusal::NonUniformOccurrence(_)), RefusalName::NonUniformOccurrence)
        | (Self::Checking(CheckRefusal::CrossBlockReference { .. }), RefusalName::CrossBlockReference)
        | (Self::Checking(CheckRefusal::StageNotBelow { .. }), RefusalName::StageNotBelow) |
        (Self::Corpus(CorpusRefusal::ExpectationOutsideFixtureRoot { .. }),
        RefusalName::ExpectationOutsideFixtureRoot)
        | (Self::Checking(CheckRefusal::EffectSignatureConflict { .. }), RefusalName::EffectSignatureConflict)
        | (Self::Checking(CheckRefusal::UnknownOperation { .. }), RefusalName::UnknownOperation)
        | (Self::Checking(CheckRefusal::HandlerCoverage { .. }), RefusalName::HandlerCoverage)
        | (Self::Checking(CheckRefusal::ShiftWithoutReset { .. }), RefusalName::ShiftWithoutReset)
        | (Self::Checking(CheckRefusal::DependentStack { .. }), RefusalName::DependentStack)
        | (Self::Checking(CheckRefusal::EndpointMismatch { .. }), RefusalName::EndpointMismatch)
        | (Self::Checking(CheckRefusal::CompoundEndpoint { .. }), RefusalName::CompoundEndpoint)
        | (Self::Checking(CheckRefusal::FunextUnsupported { .. }), RefusalName::FunextUnsupported)
        | (Self::Checking(CheckRefusal::PointwiseDistinct { .. }), RefusalName::PointwiseDistinct)
        | (Self::Checking(CheckRefusal::EquivUnsupported { .. }), RefusalName::EquivUnsupported)
        | (Self::Checking(CheckRefusal::UncertifiedStratum { .. }), RefusalName::UncertifiedStratum)
        | (Self::Checking(CheckRefusal::RoundTripDistinct { .. }), RefusalName::RoundTripDistinct)
        | (Self::Checking(CheckRefusal::NotOver { .. }), RefusalName::NotOver)
        | (Self::Checking(CheckRefusal::UaUncertified { .. }), RefusalName::UncertifiedDegree | RefusalName::UncertifiedCondition | RefusalName::UncertifiedAllowance)
        | (Self::Checking(CheckRefusal::UaInequivalent { .. }), RefusalName::UnknownGenerator | RefusalName::PastTheBound | RefusalName::CorollaCardinality | RefusalName::CorollaTables | RefusalName::NotInverse | RefusalName::NotNatural | RefusalName::TranslatorStuck)
        | (Self::Checking(CheckRefusal::UnenclosedRun { .. }), RefusalName::UnenclosedRun)
        | (Self::Checking(CheckRefusal::SessionMismatch { .. }), RefusalName::SessionMismatch | RefusalName::UnofferedLabel | RefusalName::OfferArms)
        | (Self::Checking(CheckRefusal::Linearity { .. }), RefusalName::LinearResidue | RefusalName::UsedAfterClose | RefusalName::EndpointUsedTwice | RefusalName::CapturedEndpoint | RefusalName::Delegation | RefusalName::EndpointAsValue | RefusalName::ArmsDisagree | RefusalName::UnrestrictedEndpoint | RefusalName::UnboundEndpoint)
        | (Self::Checking(CheckRefusal::Access { .. }), RefusalName::NotHeld | RefusalName::HeldLent | RefusalName::HeldCaptured | RefusalName::ViewEscaped | RefusalName::ViewUnended | RefusalName::ViewSpent | RefusalName::NotAView | RefusalName::UnwindEffect)
        | (Self::Checking(CheckRefusal::Codata { .. }), RefusalName::CodataUndeclared | RefusalName::CodataKindNotUniverse | RefusalName::CodataWithoutObservations | RefusalName::CodataOccurrence | RefusalName::CodataObservationLevel | RefusalName::CodataArity)
        | (Self::Checking(CheckRefusal::Located { .. }), RefusalName::Immobile | RefusalName::CapabilityMissing | RefusalName::CapabilityCaptured | RefusalName::Elsewhere | RefusalName::HoldElsewhere | RefusalName::Unlocated | RefusalName::UndeclaredWorld | RefusalName::HostWorldUndeclared | RefusalName::MarkUnfounded | RefusalName::EntryNamed | RefusalName::EntryUngranted | RefusalName::NotAHandle)
        | (Self::Checking(CheckRefusal::CapabilityForged { .. }), RefusalName::CapabilityForged)
        | (Self::Checking(CheckRefusal::CapabilityAmplified(_)), RefusalName::CapabilityAmplified)
        | (Self::Checking(CheckRefusal::CapabilityOutsideAuthority { .. }), RefusalName::CapabilityOutsideAuthority)
        | (Self::Checking(CheckRefusal::CapabilityEscaped { .. }), RefusalName::CapabilityEscaped)
        | (Self::Checking(CheckRefusal::CapabilityConsumable(_)), RefusalName::CapabilityConsumable)
        | (Self::Checking(CheckRefusal::CapabilityUngranted { .. }), RefusalName::CapabilityUngranted)
        | (Self::Checking(CheckRefusal::SessionNotEquivalent { .. }), RefusalName::SessionNotEquivalent)
        | (Self::Checking(CheckRefusal::SessionNotSubtype { .. }), RefusalName::SessionNotSubtype)
        | (Self::Checking(CheckRefusal::SessionCodeExpected { .. }), RefusalName::SessionCodeExpected)
        | (Self::Checking(CheckRefusal::NonCovariantMotive { .. }), RefusalName::NonCovariantMotive)
        | (Self::Checking(CheckRefusal::RideUnsupported { .. }), RefusalName::RideUnsupported)
        | (Self::Checking(CheckRefusal::RunNotAdmitted { .. }), RefusalName::RunNotAdmitted)
        | (Self::Checking(CheckRefusal::ForwardUnsupported { .. }), RefusalName::ForwardUnsupported)
        | (Self::Checking(CheckRefusal::Boundary { .. }), RefusalName::Boundary)
    )
},
    )]
    #[inline]
    #[must_use]
    pub const fn name(&self) -> RefusalName
    {
        match *self {
            Self::Lowering(refusal) => lowering_name(refusal),
            Self::Checking(refusal) => checking_name(refusal),
            Self::Corpus(CorpusRefusal::ExpectationOutsideFixtureRoot { .. }) => {
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
            Self::Lowering(ref refusal) => refusal.classify(),
            Self::Checking(ref refusal) => refusal.classify(),
            Self::Corpus(ref refusal) => refusal.classify(),
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
        RefusalName::UnresolvedName) | (LoweringRefusal::UnresolvedDocLink { .. },
        RefusalName::UnresolvedDocLink) | (LoweringRefusal::UnresolvedTypeHead { .. },
        RefusalName::UnresolvedTypeHead) | (LoweringRefusal::DuplicateSignature { .. },
        RefusalName::DuplicateSignature) | (LoweringRefusal::DuplicateDefinition { .. },
        RefusalName::DuplicateDefinition) | (LoweringRefusal::DuplicateImportAlias { ..
        }, RefusalName::DuplicateImportAlias) | (LoweringRefusal::ImportUnresolved { .. },
        RefusalName::ImportUnresolved) | (LoweringRefusal::ImportCycle { .. },
        RefusalName::ImportCycle) | (LoweringRefusal::ImportShadows { .. },
        RefusalName::ImportShadows) | (LoweringRefusal::UnexportedName { .. },
        RefusalName::UnexportedName) | (LoweringRefusal::ShadowedBuiltin { .. },
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
        RefusalName::UnknownMember) | (LoweringRefusal::NotAFunctor { .. },
        RefusalName::NotAFunctor) | (LoweringRefusal::ProjectionFromApplication { .. },
        RefusalName::ProjectionFromApplication) | (LoweringRefusal::UnreadAscription { .. },
        RefusalName::UnreadAscription) | (LoweringRefusal::UnstatedComponent { .. },
        RefusalName::UnstatedComponent) | (LoweringRefusal::FamilyTelescope { .. },
        RefusalName::FamilyTelescope) | (LoweringRefusal::LowercaseModuleName { .. },
        RefusalName::LowercaseModuleName) | (LoweringRefusal::NonExhaustiveMatch { .. },
        RefusalName::NonExhaustiveMatch) | (LoweringRefusal::UnmarkedSelfReference { .. },
        RefusalName::UnmarkedSelfReference) | (LoweringRefusal::DescentOnSeveralParameters { .. },
        RefusalName::DescentOnSeveralParameters) | (LoweringRefusal::Unreachable { .. },
        RefusalName::Unreachable) | (LoweringRefusal::OutsideLoop { .. },
        RefusalName::OutsideLoop) | (LoweringRefusal::AcrossHandler { .. },
        RefusalName::AcrossHandler) | (LoweringRefusal::WithoutK { .. },
        RefusalName::WithoutK) | (LoweringRefusal::DirectedCell { .. },
        RefusalName::DirectedCell) | (LoweringRefusal::CellNotALoop { .. },
        RefusalName::CellNotALoop) | (LoweringRefusal::RulesUnoriented { .. },
        RefusalName::RulesUnoriented) | (LoweringRefusal::RulesDiverge { .. },
        RefusalName::RulesDiverge) | (LoweringRefusal::RulesUndecided { .. },
        RefusalName::RulesUndecided) | (LoweringRefusal::BudgetExceeded { .. },
        RefusalName::BudgetExceeded) | (LoweringRefusal::GrammarMismatch { .. },
        RefusalName::GrammarMismatch) | (LoweringRefusal::UnknownMold { .. },
        RefusalName::UnknownMold) | (LoweringRefusal::Unminted { .. },
        RefusalName::Unminted)
    )
},
)]
const fn lowering_name(refusal: LoweringRefusal<'_>) -> RefusalName
{
    match refusal {
        LoweringRefusal::UnresolvedName { .. } => RefusalName::UnresolvedName,
        LoweringRefusal::UnresolvedDocLink { .. } => RefusalName::UnresolvedDocLink,
        LoweringRefusal::UnresolvedTypeHead { .. } => RefusalName::UnresolvedTypeHead,
        LoweringRefusal::DuplicateSignature { .. } => RefusalName::DuplicateSignature,
        LoweringRefusal::DuplicateDefinition { .. } => RefusalName::DuplicateDefinition,
        LoweringRefusal::DuplicateImportAlias { .. } => RefusalName::DuplicateImportAlias,
        LoweringRefusal::ImportUnresolved { .. } => RefusalName::ImportUnresolved,
        LoweringRefusal::ImportCycle { .. } => RefusalName::ImportCycle,
        LoweringRefusal::ImportShadows { .. } => RefusalName::ImportShadows,
        LoweringRefusal::UnexportedName { .. } => RefusalName::UnexportedName,
        LoweringRefusal::ShadowedBuiltin { .. } => RefusalName::ShadowedBuiltin,
        LoweringRefusal::OutOfFragment { .. } => RefusalName::OutOfFragment,
        LoweringRefusal::GradedBridge { .. } => RefusalName::GradedBridge,
        LoweringRefusal::MalformedLiteral { .. } => RefusalName::MalformedLiteral,
        LoweringRefusal::MalformedForm { .. } => RefusalName::MalformedForm,
        LoweringRefusal::UnknownAttribute { .. } => RefusalName::UnknownAttribute,
        LoweringRefusal::DuplicateAttribute { .. } => RefusalName::DuplicateAttribute,
        LoweringRefusal::MissingPayload { .. } => RefusalName::MissingPayload,
        LoweringRefusal::NonValuePayload { .. } => RefusalName::NonValuePayload,
        LoweringRefusal::IllTypedPayload { .. } => RefusalName::IllTypedPayload,
        LoweringRefusal::ForwardMemberReference { .. } => RefusalName::ForwardMemberReference,
        LoweringRefusal::UnknownMember { .. } => RefusalName::UnknownMember,
        LoweringRefusal::NotAFunctor { .. } => RefusalName::NotAFunctor,
        LoweringRefusal::ProjectionFromApplication { .. } => RefusalName::ProjectionFromApplication,
        LoweringRefusal::UnreadAscription { .. } => RefusalName::UnreadAscription,
        LoweringRefusal::UnstatedComponent { .. } => RefusalName::UnstatedComponent,
        LoweringRefusal::FamilyTelescope { .. } => RefusalName::FamilyTelescope,
        LoweringRefusal::LowercaseModuleName { .. } => RefusalName::LowercaseModuleName,
        LoweringRefusal::NonExhaustiveMatch { .. } => RefusalName::NonExhaustiveMatch,
        LoweringRefusal::UnmarkedSelfReference { .. } => RefusalName::UnmarkedSelfReference,
        LoweringRefusal::DescentOnSeveralParameters { .. } => {
            RefusalName::DescentOnSeveralParameters
        },
        LoweringRefusal::Unreachable { .. } => RefusalName::Unreachable,
        LoweringRefusal::OutsideLoop { .. } => RefusalName::OutsideLoop,
        LoweringRefusal::AcrossHandler { .. } => RefusalName::AcrossHandler,
        LoweringRefusal::WithoutK { .. } => RefusalName::WithoutK,
        LoweringRefusal::DirectedCell { .. } => RefusalName::DirectedCell,
        LoweringRefusal::CellNotALoop { .. } => RefusalName::CellNotALoop,
        LoweringRefusal::RulesUnoriented { .. } => RefusalName::RulesUnoriented,
        LoweringRefusal::RulesDiverge { .. } => RefusalName::RulesDiverge,
        LoweringRefusal::RulesUndecided { .. } => RefusalName::RulesUndecided,
        LoweringRefusal::BudgetExceeded { .. } => RefusalName::BudgetExceeded,
        LoweringRefusal::GrammarMismatch { .. } => RefusalName::GrammarMismatch,
        LoweringRefusal::UnknownMold { .. } => RefusalName::UnknownMold,
        LoweringRefusal::Unminted { .. } => RefusalName::Unminted,
    }
}

/// The vocabulary name of a checker refusal.
///
/// # Specification
/// - ensures: returns the vocabulary name of the producer variant,
///   independently of its payload, except that univalence at a stratum is named
///   by the defect it carries.
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
        | (CheckRefusal::RuleNotPresentable { .. }, RefusalName::RuleNotPresentable)
        | (CheckRefusal::RuleNotRespected { .. }, RefusalName::RuleNotRespected)
        | (CheckRefusal::NotApart { .. }, RefusalName::NotApart)
        | (CheckRefusal::LoopNotRespected { .. }, RefusalName::LoopNotRespected)
        | (CheckRefusal::LoopUndecided { .. }, RefusalName::LoopUndecided)
        | (CheckRefusal::AbstractKindNotUniverse(_), RefusalName::AbstractKindNotUniverse)
        | (CheckRefusal::RepresentationAboveKind { .. }, RefusalName::RepresentationAboveKind)
        | (CheckRefusal::NotAnAbstractType(_), RefusalName::NotAnAbstractType)
        | (CheckRefusal::SealSiteRepeated(_), RefusalName::SealSiteRepeated)
        | (CheckRefusal::DataArgumentArity(_), RefusalName::DataArgumentArity)
        | (CheckRefusal::UnknownConstructor { .. }, RefusalName::UnknownConstructor)
        | (CheckRefusal::ConstructorArity(_), RefusalName::ConstructorArity)
        | (CheckRefusal::IndexedCase(_), RefusalName::IndexedCase)
        | (CheckRefusal::NonExhaustiveDataCase(_), RefusalName::NonExhaustiveDataCase)
        | (CheckRefusal::UndecidedCoverage(_), RefusalName::UndecidedCoverage)
        | (CheckRefusal::AbsentRecordField(_), RefusalName::AbsentRecordField)
        | (CheckRefusal::AbsentTupleComponent(_), RefusalName::AbsentTupleComponent)
        | (CheckRefusal::MissingRecordField { .. }, RefusalName::MissingRecordField)
        | (CheckRefusal::NegativeOccurrence(_), RefusalName::NegativeOccurrence)
        | (CheckRefusal::NestedOccurrence(_), RefusalName::NestedOccurrence)
        | (CheckRefusal::IndexOccurrence(_), RefusalName::IndexOccurrence)
        | (CheckRefusal::NonUniformOccurrence(_), RefusalName::NonUniformOccurrence)
        | (CheckRefusal::CrossBlockReference { .. }, RefusalName::CrossBlockReference)
        | (CheckRefusal::StageNotBelow { .. }, RefusalName::StageNotBelow)
        | (CheckRefusal::EffectSignatureConflict { .. }, RefusalName::EffectSignatureConflict)
        | (CheckRefusal::UnknownOperation { .. }, RefusalName::UnknownOperation)
        | (CheckRefusal::HandlerCoverage { .. }, RefusalName::HandlerCoverage)
        | (CheckRefusal::ShiftWithoutReset { .. }, RefusalName::ShiftWithoutReset)
        | (CheckRefusal::DependentStack { .. }, RefusalName::DependentStack)
        | (CheckRefusal::EndpointMismatch { .. }, RefusalName::EndpointMismatch)
        | (CheckRefusal::CompoundEndpoint { .. }, RefusalName::CompoundEndpoint)
        | (CheckRefusal::FunextUnsupported { .. }, RefusalName::FunextUnsupported)
        | (CheckRefusal::PointwiseDistinct { .. }, RefusalName::PointwiseDistinct)
        | (CheckRefusal::EquivUnsupported { .. }, RefusalName::EquivUnsupported)
        | (CheckRefusal::UncertifiedStratum { .. }, RefusalName::UncertifiedStratum)
        | (CheckRefusal::RoundTripDistinct { .. }, RefusalName::RoundTripDistinct)
        | (CheckRefusal::NotOver { .. }, RefusalName::NotOver)
        | (CheckRefusal::UaUncertified { stratum: StratumDefect::Degree { .. }, .. }, RefusalName::UncertifiedDegree)
        | (CheckRefusal::UaUncertified { stratum: StratumDefect::Condition { .. }, .. }, RefusalName::UncertifiedCondition)
        | (CheckRefusal::UaUncertified { stratum: StratumDefect::Allowance { .. }, .. }, RefusalName::UncertifiedAllowance)
        | (CheckRefusal::UaInequivalent { defect: UaDefect::UnknownGenerator { .. }, .. }, RefusalName::UnknownGenerator)
        | (CheckRefusal::UaInequivalent { defect: UaDefect::PastTheBound { .. }, .. }, RefusalName::PastTheBound)
        | (CheckRefusal::UaInequivalent { defect: UaDefect::Cardinality { .. }, .. }, RefusalName::CorollaCardinality)
        | (CheckRefusal::UaInequivalent { defect: UaDefect::Tables { .. }, .. }, RefusalName::CorollaTables)
        | (CheckRefusal::UaInequivalent { defect: UaDefect::NotInverse { .. }, .. }, RefusalName::NotInverse)
        | (CheckRefusal::UaInequivalent { defect: UaDefect::NotNatural { .. }, .. }, RefusalName::NotNatural)
        | (CheckRefusal::UaInequivalent { defect: UaDefect::Stuck { .. }, .. }, RefusalName::TranslatorStuck)
        | (CheckRefusal::UnenclosedRun { .. }, RefusalName::UnenclosedRun)
        | (CheckRefusal::SessionMismatch { defect: ProtocolDefect::Action { .. }, .. }, RefusalName::SessionMismatch)
        | (CheckRefusal::SessionMismatch { defect: ProtocolDefect::Label, .. }, RefusalName::UnofferedLabel)
        | (CheckRefusal::SessionMismatch { defect: ProtocolDefect::Arms, .. }, RefusalName::OfferArms)
        | (CheckRefusal::Linearity { defect: LinearityDefect::Residue { .. }, .. }, RefusalName::LinearResidue)
        | (CheckRefusal::Linearity { defect: LinearityDefect::Closed { .. }, .. }, RefusalName::UsedAfterClose)
        | (CheckRefusal::Linearity { defect: LinearityDefect::UsedTwice { .. }, .. }, RefusalName::EndpointUsedTwice)
        | (CheckRefusal::Linearity { defect: LinearityDefect::Captured { .. }, .. }, RefusalName::CapturedEndpoint)
        | (CheckRefusal::Linearity { defect: LinearityDefect::Delegated, .. }, RefusalName::Delegation)
        | (CheckRefusal::Linearity { defect: LinearityDefect::AsValue { .. }, .. }, RefusalName::EndpointAsValue)
        | (CheckRefusal::Linearity { defect: LinearityDefect::ArmsDisagree { .. }, .. }, RefusalName::ArmsDisagree)
        | (CheckRefusal::Linearity { defect: LinearityDefect::Unrestricted, .. }, RefusalName::UnrestrictedEndpoint)
        | (CheckRefusal::Linearity { defect: LinearityDefect::Unbound { .. }, .. }, RefusalName::UnboundEndpoint)
        | (CheckRefusal::Access { defect: AccessDefect::NotHeld, .. }, RefusalName::NotHeld)
        | (CheckRefusal::Access { defect: AccessDefect::Lent, .. }, RefusalName::HeldLent)
        | (CheckRefusal::Access { defect: AccessDefect::HeldCaptured { .. }, .. }, RefusalName::HeldCaptured)
        | (CheckRefusal::Access { defect: AccessDefect::Escaped { .. }, .. }, RefusalName::ViewEscaped)
        | (CheckRefusal::Access { defect: AccessDefect::Unended, .. }, RefusalName::ViewUnended)
        | (CheckRefusal::Access { defect: AccessDefect::Spent, .. }, RefusalName::ViewSpent)
        | (CheckRefusal::Access { defect: AccessDefect::NotAView, .. }, RefusalName::NotAView)
        | (CheckRefusal::Access { defect: AccessDefect::UnwindEffect, .. }, RefusalName::UnwindEffect)
        | (CheckRefusal::Codata { fault: CodataFault::Undeclared, .. }, RefusalName::CodataUndeclared)
        | (CheckRefusal::Codata { fault: CodataFault::KindNotUniverse, .. }, RefusalName::CodataKindNotUniverse)
        | (CheckRefusal::Codata { fault: CodataFault::WithoutObservations, .. }, RefusalName::CodataWithoutObservations)
        | (CheckRefusal::Codata { fault: CodataFault::Occurrence, .. }, RefusalName::CodataOccurrence)
        | (CheckRefusal::Codata { fault: CodataFault::ObservationLevel, .. }, RefusalName::CodataObservationLevel)
        | (CheckRefusal::Codata { fault: CodataFault::Arity, .. }, RefusalName::CodataArity)
        | (CheckRefusal::Located { defect: LocatedDefect::Immobile { .. }, .. }, RefusalName::Immobile)
        | (CheckRefusal::Located { defect: LocatedDefect::CapabilityMissing { .. }, .. }, RefusalName::CapabilityMissing)
        | (CheckRefusal::Located { defect: LocatedDefect::CapabilityCaptured { .. }, .. }, RefusalName::CapabilityCaptured)
        | (CheckRefusal::Located { defect: LocatedDefect::Elsewhere { .. }, .. }, RefusalName::Elsewhere)
        | (CheckRefusal::Located { defect: LocatedDefect::HoldElsewhere { .. }, .. }, RefusalName::HoldElsewhere)
        | (CheckRefusal::Located { defect: LocatedDefect::Unlocated, .. }, RefusalName::Unlocated)
        | (CheckRefusal::Located { defect: LocatedDefect::UndeclaredWorld { .. }, .. }, RefusalName::UndeclaredWorld)
        | (CheckRefusal::Located { defect: LocatedDefect::HostWorldUndeclared, .. }, RefusalName::HostWorldUndeclared)
        | (CheckRefusal::Located { defect: LocatedDefect::MarkUnfounded { .. }, .. }, RefusalName::MarkUnfounded)
        | (CheckRefusal::Located { defect: LocatedDefect::EntryNamed { .. }, .. }, RefusalName::EntryNamed)
        | (CheckRefusal::Located { defect: LocatedDefect::EntryUngranted { .. }, .. }, RefusalName::EntryUngranted)
        | (CheckRefusal::Located { defect: LocatedDefect::NotAHandle { .. }, .. }, RefusalName::NotAHandle)
        | (CheckRefusal::CapabilityForged { .. }, RefusalName::CapabilityForged)
        | (CheckRefusal::CapabilityAmplified(_), RefusalName::CapabilityAmplified)
        | (CheckRefusal::CapabilityOutsideAuthority { .. }, RefusalName::CapabilityOutsideAuthority)
        | (CheckRefusal::CapabilityEscaped { .. }, RefusalName::CapabilityEscaped)
        | (CheckRefusal::CapabilityConsumable(_), RefusalName::CapabilityConsumable)
        | (CheckRefusal::CapabilityUngranted { .. }, RefusalName::CapabilityUngranted)
        | (CheckRefusal::SessionNotEquivalent { .. }, RefusalName::SessionNotEquivalent)
        | (CheckRefusal::SessionNotSubtype { .. }, RefusalName::SessionNotSubtype)
        | (CheckRefusal::SessionCodeExpected { .. }, RefusalName::SessionCodeExpected)
        | (CheckRefusal::NonCovariantMotive { .. }, RefusalName::NonCovariantMotive)
        | (CheckRefusal::RideUnsupported { .. }, RefusalName::RideUnsupported)
        | (CheckRefusal::RunNotAdmitted { .. }, RefusalName::RunNotAdmitted)
        | (CheckRefusal::ForwardUnsupported { .. }, RefusalName::ForwardUnsupported)
        | (CheckRefusal::Boundary { .. }, RefusalName::Boundary)
    )
},
)]
const fn checking_name(refusal: CheckRefusal) -> RefusalName
{
    match refusal {
        CheckRefusal::NotADataType(_) => RefusalName::NotADataType,
        CheckRefusal::DataKindNotUniverse(_) => RefusalName::DataKindNotUniverse,
        CheckRefusal::DataFieldLevel { .. } => RefusalName::DataFieldLevel,
        CheckRefusal::RuleNotPresentable { .. } => RefusalName::RuleNotPresentable,
        CheckRefusal::RuleNotRespected { .. } => RefusalName::RuleNotRespected,
        CheckRefusal::NotApart { .. } => RefusalName::NotApart,
        CheckRefusal::LoopNotRespected { .. } => RefusalName::LoopNotRespected,
        CheckRefusal::LoopUndecided { .. } => RefusalName::LoopUndecided,
        CheckRefusal::AbstractKindNotUniverse(_) => RefusalName::AbstractKindNotUniverse,
        CheckRefusal::RepresentationAboveKind { .. } => RefusalName::RepresentationAboveKind,
        CheckRefusal::NotAnAbstractType(_) => RefusalName::NotAnAbstractType,
        CheckRefusal::SealSiteRepeated(_) => RefusalName::SealSiteRepeated,
        CheckRefusal::DataArgumentArity(_) => RefusalName::DataArgumentArity,
        CheckRefusal::UnknownConstructor { .. } => RefusalName::UnknownConstructor,
        CheckRefusal::ConstructorArity(_) => RefusalName::ConstructorArity,
        CheckRefusal::IndexedCase(_) => RefusalName::IndexedCase,
        CheckRefusal::NonExhaustiveDataCase(_) => RefusalName::NonExhaustiveDataCase,
        CheckRefusal::UndecidedCoverage(_) => RefusalName::UndecidedCoverage,
        CheckRefusal::AbsentRecordField(_) => RefusalName::AbsentRecordField,
        CheckRefusal::AbsentTupleComponent(_) => RefusalName::AbsentTupleComponent,
        CheckRefusal::MissingRecordField { .. } => RefusalName::MissingRecordField,
        CheckRefusal::UnknownOperation { .. } => RefusalName::UnknownOperation,
        CheckRefusal::HandlerCoverage { .. } => RefusalName::HandlerCoverage,
        CheckRefusal::ShiftWithoutReset { .. } => RefusalName::ShiftWithoutReset,
        CheckRefusal::DependentStack { .. } => RefusalName::DependentStack,
        CheckRefusal::EffectSignatureConflict { .. } => RefusalName::EffectSignatureConflict,
        CheckRefusal::PathCode(_) => RefusalName::PathCode,
        CheckRefusal::EndpointMismatch { .. } => RefusalName::EndpointMismatch,
        CheckRefusal::CompoundEndpoint { .. } => RefusalName::CompoundEndpoint,
        CheckRefusal::FunextUnsupported { .. } => RefusalName::FunextUnsupported,
        CheckRefusal::PointwiseDistinct { .. } => RefusalName::PointwiseDistinct,
        CheckRefusal::EquivUnsupported { .. } => RefusalName::EquivUnsupported,
        CheckRefusal::UncertifiedStratum { .. } => RefusalName::UncertifiedStratum,
        CheckRefusal::RoundTripDistinct { .. } => RefusalName::RoundTripDistinct,
        CheckRefusal::NotOver { .. } => RefusalName::NotOver,
        CheckRefusal::UaUncertified { stratum, .. } => match stratum {
            StratumDefect::Degree { .. } => RefusalName::UncertifiedDegree,
            StratumDefect::Condition { .. } => RefusalName::UncertifiedCondition,
            StratumDefect::Allowance { .. } => RefusalName::UncertifiedAllowance,
        },
        CheckRefusal::UaInequivalent { defect, .. } => match defect {
            UaDefect::UnknownGenerator { .. } => RefusalName::UnknownGenerator,
            UaDefect::PastTheBound { .. } => RefusalName::PastTheBound,
            UaDefect::Cardinality { .. } => RefusalName::CorollaCardinality,
            UaDefect::Tables { .. } => RefusalName::CorollaTables,
            UaDefect::NotInverse { .. } => RefusalName::NotInverse,
            UaDefect::NotNatural { .. } => RefusalName::NotNatural,
            UaDefect::Stuck { .. } => RefusalName::TranslatorStuck,
        },
        CheckRefusal::UnenclosedRun { .. } => RefusalName::UnenclosedRun,
        CheckRefusal::SessionMismatch { defect, .. } => match defect {
            ProtocolDefect::Action { .. } => RefusalName::SessionMismatch,
            ProtocolDefect::Label => RefusalName::UnofferedLabel,
            ProtocolDefect::Arms => RefusalName::OfferArms,
        },
        CheckRefusal::CapabilityForged { .. } => RefusalName::CapabilityForged,
        CheckRefusal::CapabilityAmplified(_) => RefusalName::CapabilityAmplified,
        CheckRefusal::CapabilityOutsideAuthority { .. } => RefusalName::CapabilityOutsideAuthority,
        CheckRefusal::Linearity { defect, .. } => match defect {
            LinearityDefect::Residue { .. } => RefusalName::LinearResidue,
            LinearityDefect::Closed { .. } => RefusalName::UsedAfterClose,
            LinearityDefect::UsedTwice { .. } => RefusalName::EndpointUsedTwice,
            LinearityDefect::Captured { .. } => RefusalName::CapturedEndpoint,
            LinearityDefect::Delegated => RefusalName::Delegation,
            LinearityDefect::AsValue { .. } => RefusalName::EndpointAsValue,
            LinearityDefect::ArmsDisagree { .. } => RefusalName::ArmsDisagree,
            LinearityDefect::Unrestricted => RefusalName::UnrestrictedEndpoint,
            LinearityDefect::Unbound { .. } => RefusalName::UnboundEndpoint,
        },
        CheckRefusal::Access { defect, .. } => match defect {
            AccessDefect::NotHeld => RefusalName::NotHeld,
            AccessDefect::Lent => RefusalName::HeldLent,
            AccessDefect::HeldCaptured { .. } => RefusalName::HeldCaptured,
            AccessDefect::Escaped { .. } => RefusalName::ViewEscaped,
            AccessDefect::Unended => RefusalName::ViewUnended,
            AccessDefect::Spent => RefusalName::ViewSpent,
            AccessDefect::NotAView => RefusalName::NotAView,
            AccessDefect::UnwindEffect => RefusalName::UnwindEffect,
        },
        CheckRefusal::Codata { fault, .. } => match fault {
            CodataFault::Undeclared => RefusalName::CodataUndeclared,
            CodataFault::KindNotUniverse => RefusalName::CodataKindNotUniverse,
            CodataFault::WithoutObservations => RefusalName::CodataWithoutObservations,
            CodataFault::Occurrence => RefusalName::CodataOccurrence,
            CodataFault::ObservationLevel => RefusalName::CodataObservationLevel,
            CodataFault::Arity => RefusalName::CodataArity,
        },
        CheckRefusal::Located { defect, .. } => match defect {
            LocatedDefect::Immobile { .. } => RefusalName::Immobile,
            LocatedDefect::CapabilityMissing { .. } => RefusalName::CapabilityMissing,
            LocatedDefect::CapabilityCaptured { .. } => RefusalName::CapabilityCaptured,
            LocatedDefect::Elsewhere { .. } => RefusalName::Elsewhere,
            LocatedDefect::HoldElsewhere { .. } => RefusalName::HoldElsewhere,
            LocatedDefect::Unlocated => RefusalName::Unlocated,
            LocatedDefect::UndeclaredWorld { .. } => RefusalName::UndeclaredWorld,
            LocatedDefect::HostWorldUndeclared => RefusalName::HostWorldUndeclared,
            LocatedDefect::MarkUnfounded { .. } => RefusalName::MarkUnfounded,
            LocatedDefect::EntryNamed { .. } => RefusalName::EntryNamed,
            LocatedDefect::EntryUngranted { .. } => RefusalName::EntryUngranted,
            LocatedDefect::NotAHandle { .. } => RefusalName::NotAHandle,
        },
        CheckRefusal::CapabilityEscaped { .. } => RefusalName::CapabilityEscaped,
        CheckRefusal::CapabilityConsumable(_) => RefusalName::CapabilityConsumable,
        CheckRefusal::CapabilityUngranted { .. } => RefusalName::CapabilityUngranted,
        CheckRefusal::SessionNotEquivalent { .. } => RefusalName::SessionNotEquivalent,
        CheckRefusal::SessionNotSubtype { .. } => RefusalName::SessionNotSubtype,
        CheckRefusal::SessionCodeExpected { .. } => RefusalName::SessionCodeExpected,
        CheckRefusal::NonCovariantMotive { .. } => RefusalName::NonCovariantMotive,
        CheckRefusal::RideUnsupported { .. } => RefusalName::RideUnsupported,
        CheckRefusal::RunNotAdmitted { .. } => RefusalName::RunNotAdmitted,
        CheckRefusal::ForwardUnsupported { .. } => RefusalName::ForwardUnsupported,
        CheckRefusal::Boundary { .. } => RefusalName::Boundary,
        CheckRefusal::TypeMismatch(_) => RefusalName::TypeMismatch,
        CheckRefusal::ShapeMismatch { .. } => RefusalName::ShapeMismatch,
        CheckRefusal::NotSynthesisable { .. } => RefusalName::NotSynthesisable,
        CheckRefusal::UnknownConstant { .. } => RefusalName::UnknownConstant,
        CheckRefusal::OutOfFragment { .. } => RefusalName::OutOfFragment,
        CheckRefusal::UnboundIndex { .. } => RefusalName::UnboundIndex,
        CheckRefusal::BudgetExceeded { .. } => RefusalName::BudgetExceeded,
        CheckRefusal::DanglingNode { .. } => RefusalName::DanglingNode,
        CheckRefusal::AdmissionOrder { .. } => RefusalName::AdmissionOrder,
        CheckRefusal::MachineInvariant => RefusalName::MachineInvariant,
        CheckRefusal::SortMismatch { .. } => RefusalName::SortMismatch,
        CheckRefusal::LevelMismatch { .. } => RefusalName::LevelMismatch,
        CheckRefusal::DependentBind { .. } => RefusalName::DependentBind,
        CheckRefusal::Undecided { .. } => RefusalName::Undecided,
        CheckRefusal::FamilyArity { .. } => RefusalName::FamilyArity,
        CheckRefusal::FamilyArgumentClassifier { .. } => RefusalName::FamilyArgumentClassifier,
        CheckRefusal::StaticLambdaArgument { .. } => RefusalName::StaticLambdaArgument,
        CheckRefusal::StaticClassifierExpected { .. } => RefusalName::StaticClassifierExpected,
        CheckRefusal::NegativeOccurrence(_) => RefusalName::NegativeOccurrence,
        CheckRefusal::NestedOccurrence(_) => RefusalName::NestedOccurrence,
        CheckRefusal::IndexOccurrence(_) => RefusalName::IndexOccurrence,
        CheckRefusal::NonUniformOccurrence(_) => RefusalName::NonUniformOccurrence,
        CheckRefusal::CrossBlockReference { .. } => RefusalName::CrossBlockReference,
        CheckRefusal::StageNotBelow { .. } => RefusalName::StageNotBelow,
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
        for admitted in [
            ExpectationSchema::Checks,
            ExpectationSchema::Runs,
            ExpectationSchema::Normalizes,
        ] {
            assert_eq!(CorpusRoot::Strict.admit(admitted, at), Ok(()));
            assert!(
                rendered.contains(&admitted.to_string()),
                "the diagnostic must name each admitted schema: {admitted}"
            );
        }
        assert!(
            !rendered.contains(&at.to_string()),
            "the span is the report's locus, not part of its message"
        );
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

    #[test]
    fn every_refusal_spelling_reads_as_the_text_that_names_it()
    {
        for name in RefusalName::VOCABULARY {
            let spelling = name.spelling();
            let text: &str = spelling.as_ref();
            assert_eq!(text, name.to_string(), "{name:?} spells as it prints");
            assert_eq!(
                RefusalName::named_by(&StringLiteral::new(String::from(text))),
                Maybe::Present(name),
                "`{text}` names {name:?}"
            );
        }
    }
}
