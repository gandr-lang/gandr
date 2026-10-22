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
//! # A refusal that names several features is qualified by one
//!
//! Three variants each cover several features, so their name carries the
//! one it refuses after a dot: a form out of the fragment the feature its
//! producer classifies it by — `OutOfFragment.projection_expression`, a form
//! at the sort that decides its issue as
//! `OutOfFragment.instantiation_expression.computation`, the run target as
//! `OutOfFragment.WrongSort.declaration`, another boundary by its name
//! (`OutOfFragment.Arity`, without the operand count), a checker former by
//! its name (`OutOfFragment.Stage`) — and an unstated model component and an
//! undescribed member their fault (`UndescribedMember.HigherCell`). The
//! lowering's key is `FragmentFeature`, whose witness checks that one key
//! classifies alike, so a name covers one feature and one issue. A payload
//! is still read byte for byte: a qualifier no refusal carries — a misspelt
//! form, a sort that decides nothing, the bare variant — names nothing.
//! **Choice.** The qualifier on the one refusal; the alternative, a variant
//! per feature, multiplied the vocabulary for the distinction the qualifier
//! makes. **Reversal.** A feature whose refusals need their own payload or
//! message becomes its own variant.
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

use alloc::string::ToString as _;
use alloc::vec::Vec;
use core::error::Error;
use core::fmt;

use anodized::spec;
use gandr_core_checker::CheckRefusal;
use gandr_core_checker::UnadmittedFormer;
use gandr_core_checker::access::AccessDefect;
use gandr_core_checker::codata::CodataFault;
use gandr_core_checker::session::LinearityDefect;
use gandr_core_checker::session::ProtocolDefect;
use gandr_core_checker::ua::StratumDefect;
use gandr_core_checker::ua::UaDefect;
use gandr_core_checker::worlds::LocatedDefect;
use gandr_core_term::FailureClass;
use gandr_kernel_term::StringLiteral;
use gandr_surface_grammar::NamedKind;
use gandr_surface_grammar::PBG_ONLY_KINDS;
use gandr_surface_grammar::TREE_SITTER_NAMED_KINDS;
use gandr_surface_lowering::FormName;
use gandr_surface_lowering::FragmentBoundary;
use gandr_surface_lowering::FragmentFeature;
use gandr_surface_lowering::FragmentSort;
use gandr_surface_lowering::LoweringRefusal;
use gandr_surface_lowering::OperandCount;
use gandr_surface_lowering::description::MemberFault;
use gandr_surface_lowering::model::ModelFault;
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

/// The text of one reading a qualifier names: a boundary, the run target, a
/// sort, a checker former, a member's or a model component's fault.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Tag(&'static str);

impl fmt::Display for Tag
{
    /// Writes the tag's text.
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

/// What a refusal named by the feature it refuses is qualified by, after its
/// variant and a dot: the key its producer classifies the refusal by, so the
/// name covers one feature.
///
/// # Specification
/// - requires: built from a producer's key ([`RefusalName`]'s maps) or read
///   from a payload ([`RefusalName::named_by`]).
/// - ensures: a form is written as the grammar names it, a form at a sort as
///   the form, a dot and the sort, a tag as its text.
/// - panics: none.
/// - executable: none — this data type has no call boundary; the maps and the
///   reader carry the predicates.
///
/// # Adequacy
/// - hypothesis: L3 — every qualified name a fixture writes settles against the
///   refusal its declaration reaches; a qualifier for another feature leaves
///   the fixture unsettled.
/// - witness: `settle::tests::every_refusal_a_source_reaches_settles_the_fixture_naming_it`
/// - witness: `refusal::tests::every_qualified_spelling_reads_as_the_text_that_names_it`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Qualifier
{
    /// A form out of the fragment named by itself: `projection_expression`.
    Form(FormName),
    /// A form out of the fragment at the sort that decides its issue:
    /// `instantiation_expression.value`.
    FormAt(FormName, Tag),
    /// A named reading: a boundary, the run target, or a checker former.
    Named(Tag),
}

impl fmt::Display for Qualifier
{
    /// Writes the qualifier as a payload writes it after the variant's dot.
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
            Self::Form(form) => f.write_str(form.as_ref()),
            Self::FormAt(form, sort) => write!(f, "{}.{sort}", form.as_ref()),
            Self::Named(tag) => fmt::Display::fmt(&tag, f),
        }
    }
}

/// The spelling of a refusal name, as a `refuses` payload writes it: the
/// refusal's variant, then, for a refusal named by the feature it refuses, a
/// dot and the qualifier.
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
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RefusalSpelling
{
    /// The refusal's variant.
    head: &'static str,
    /// The feature, for a refusal named by the feature it refuses.
    qualifier: Option<Qualifier>,
}

impl fmt::Display for RefusalSpelling
{
    /// Writes the spelling.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the variant, then a dot and the qualifier when there
    ///   is one.
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
    /// - witness: `refusal::tests::every_qualified_spelling_reads_as_the_text_that_names_it`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(self.head)?;
        self.qualifier
            .map_or(Ok(()), |qualifier| write!(f, ".{qualifier}"))
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
    /// Two arguments of a call show stages for one stage binder that no stage
    /// satisfies together.
    StagesDisagree,
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
    /// A universe equivalence whose round trip at a list cell does not return
    /// it with the tail unread.
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
    /// A session type whose payload reads a binder outside it, outside a
    /// run's protocol.
    OpenSessionPayload,
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
    /// A form the fragment does not admit, from the lowering or the checker,
    /// qualified by the feature it refuses.
    OutOfFragment(Qualifier),
    /// A circuit rule's fed-back port read under no observation.
    BareFeedback,
    /// A description the description check refuses: its sorts, ports, shape
    /// or rules are not well formed.
    IllFormedDescription,
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
    /// A type member, or a type a signature states, reading a value.
    PhaseDependence,
    /// A selection or a signature component a module does not supply.
    UnknownMember,
    /// A module binding applying a name that is not a functor.
    NotAFunctor,
    /// A path read off a functor application rather than off its binding.
    ProjectionFromApplication,
    /// A module ascription form the fragment does not read yet.
    UnreadAscription,
    /// A model signature component the derivation cannot state, qualified by
    /// the fault.
    UnstatedComponent(Tag),
    /// A member of a description declaration the description route or its
    /// cell layer does not read, qualified by the fault.
    UndescribedMember(Tag),
    /// A type family whose parameters disagree with the indices its kind
    /// states.
    FamilyTelescope,
    /// A top-level module named with a lowercase initial.
    LowercaseModuleName,
    /// A declaration binding parameters in an implicit telescope `@[…]`.
    ImplicitTelescope,
    /// A function's merged telescope with two parameters each mentioning the
    /// other.
    TelescopeCycle,
    /// A use of a function leaving one of its implicits unsupplied.
    ImplicitUnsupplied,
    /// A call writing a function's implicit arguments among its parentheses.
    ImplicitInParentheses,
    /// A definition's region binder named as a value.
    RegionAsValue,
    /// A receiver mode word on a parameter that is no method's receiver.
    StrayReceiverMode,
    /// A method call whose name more than one module's receivers declare.
    AmbiguousMethod,
    /// A method at a deduced mode whose result is no view of its receiver's
    /// mode or whose body is no place of its receiver, or a view type off such
    /// a method's result.
    ViewNotPlace,
    /// A view block after a call of no method answering a place.
    ViewOfNoPlace,
    /// A match some scrutinee value reaches no arm of.
    NonExhaustiveMatch,
    /// A recursive definition's own name written without a descent claim.
    UnmarkedSelfReference,
    /// A productivity claim standing outside a copattern arm.
    UnguardedCorecursion,
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
    /// A rule of a block whose left side names one variable twice.
    RulesNonLinear,
    /// Two rules of a block rewriting one term to two constructor terms.
    RulesDiverge,
    /// Two rules of a block whose left sides overlap, one of which
    /// instantiates a variable a binding port binds.
    RulesOverlapSecondOrder,
    /// Two rules of a block rewriting one term to two normal forms no rule
    /// the path order orients joins.
    RulesUncompleted,
    /// Two rules of a block whose completion never ends: each rule it derives
    /// wraps the one before where no rule rewrites the wrapping.
    RulesNeverComplete,
    /// A critical pair of a block's rules the coincidence check's budget left
    /// undecided.
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
    /// An endpoint read as a value outside an action.
    EndpointAsValue,
    /// Two arms of an offer leaving an endpoint in different states.
    ArmsDisagree,
    /// A declaration whose type is a session type.
    UnrestrictedEndpoint,
    /// An action naming a linear index no fork or receive bound.
    UnboundEndpoint,
    /// A receive or an allocation ending with the buffer it placed live never
    /// handed back.
    BufferUnreturned,
    /// A placed buffer handed back a second time.
    BufferReturnedTwice,
    /// A placed buffer read other than by the send, the operation or the
    /// resumption that returns it.
    BufferRead,
    /// An operation clause owing its continuation, which holds an obligation,
    /// finishing without resuming or abandoning it.
    ContinuationUnspent,
    /// A continuation holding an obligation resumed or abandoned a second
    /// time.
    ContinuationUsedTwice,
    /// A continuation holding an obligation named where its end may run other
    /// than once.
    ContinuationCaptured,
    /// A continuation holding an obligation read as a value, other than as
    /// what a resumption or an abandonment ends.
    ContinuationAsValue,
    /// An access naming a linear slot that holds no value.
    NotHeld,
    /// A held value read while an access lends it exclusively, or accessed
    /// again where its lending excludes the access.
    HeldLent,
    /// A held value named where its holding may run other than once.
    HeldCaptured,
    /// A view named where it would outlive its access's body.
    ViewEscaped,
    /// An exclusive access's body ending with its view neither resumed nor
    /// aborted.
    ViewUnended,
    /// A view used after its resume or abort.
    ViewSpent,
    /// A resume or an abort naming a linear slot that is no view.
    NotAView,
    /// A resume or an abort naming a shared view.
    ViewReadOnly,
    /// An access's unwind performing an effect.
    UnwindEffect,
    /// An access at a place naming a held value whose type is no list.
    PlaceUnindexed,
    /// A hold at grade one entering a value not made in place.
    HeldShared,
    /// A value held at grade one copied: its held slot or a shared view of
    /// it read, or its exclusive view read twice.
    HeldCopied,
    /// An abort of a view whose value held at grade one a read moved out.
    ViewMoved,
    /// An exclusive access of a held slot a view of which is kept in a live
    /// region.
    HeldKept,
    /// A capability scope's answer naming a value kept in the scope's region.
    KeptEscaped,
    /// A held slot read, accessed or consumed after a consumed receiver ended
    /// its hold, or consumed on one arm of an offer and not on another.
    HeldConsumed,
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
    /// Every name of the vocabulary a variant spells alone, in declaration
    /// order; the names a qualifier completes are read by
    /// [`Self::named_by`].
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: contains each unqualified refusal name exactly once.
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
    pub const VOCABULARY: [Self; 196_usize] = [
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
        Self::StagesDisagree,
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
        Self::OpenSessionPayload,
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
        Self::BareFeedback,
        Self::IllFormedDescription,
        Self::GradedBridge,
        Self::MalformedLiteral,
        Self::MalformedForm,
        Self::UnknownAttribute,
        Self::DuplicateAttribute,
        Self::MissingPayload,
        Self::NonValuePayload,
        Self::IllTypedPayload,
        Self::ForwardMemberReference,
        Self::PhaseDependence,
        Self::UnknownMember,
        Self::NotAFunctor,
        Self::ProjectionFromApplication,
        Self::UnreadAscription,
        Self::FamilyTelescope,
        Self::LowercaseModuleName,
        Self::ImplicitTelescope,
        Self::TelescopeCycle,
        Self::ImplicitUnsupplied,
        Self::ImplicitInParentheses,
        Self::RegionAsValue,
        Self::StrayReceiverMode,
        Self::AmbiguousMethod,
        Self::ViewNotPlace,
        Self::ViewOfNoPlace,
        Self::NonExhaustiveMatch,
        Self::UnmarkedSelfReference,
        Self::UnguardedCorecursion,
        Self::DescentOnSeveralParameters,
        Self::Unreachable,
        Self::OutsideLoop,
        Self::AcrossHandler,
        Self::WithoutK,
        Self::DirectedCell,
        Self::CellNotALoop,
        Self::RulesUnoriented,
        Self::RulesNonLinear,
        Self::RulesDiverge,
        Self::RulesOverlapSecondOrder,
        Self::RulesUncompleted,
        Self::RulesNeverComplete,
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
        Self::EndpointAsValue,
        Self::ArmsDisagree,
        Self::UnrestrictedEndpoint,
        Self::UnboundEndpoint,
        Self::BufferUnreturned,
        Self::BufferReturnedTwice,
        Self::BufferRead,
        Self::ContinuationUnspent,
        Self::ContinuationUsedTwice,
        Self::ContinuationCaptured,
        Self::ContinuationAsValue,
        Self::NotHeld,
        Self::HeldLent,
        Self::HeldCaptured,
        Self::ViewEscaped,
        Self::ViewUnended,
        Self::ViewSpent,
        Self::NotAView,
        Self::ViewReadOnly,
        Self::UnwindEffect,
        Self::PlaceUnindexed,
        Self::HeldShared,
        Self::HeldCopied,
        Self::ViewMoved,
        Self::HeldKept,
        Self::KeptEscaped,
        Self::HeldConsumed,
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

    /// Every name no form qualifies: the vocabulary, in its order, then each
    /// `OutOfFragment` name qualified by a named reading, each model
    /// component's fault and each member's. A name qualified by a form is not
    /// among them: the forms are the grammar's, and the syntax ledger lists
    /// them.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the vocabulary first, in its order; then the named readings;
    ///   no name twice.
    /// - provides: the names the diagnostics ledger pairs with exemplars.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every name read back from its spelling is the name; a
    ///   lost family or reading is a name the diagnostics ledger cannot pair.
    /// - witness: `refusal::tests::every_qualified_spelling_reads_as_the_text_that_names_it`
    #[spec(ensures: |ret| ret.starts_with(&Self::VOCABULARY) && ret.iter().enumerate().all(|(at, name)| !ret.get(.. at).is_some_and(|before| before.contains(name))))]
    #[inline]
    #[must_use]
    pub fn closed() -> Vec<Self>
    {
        Self::VOCABULARY
            .into_iter()
            .chain(
                readings()
                    .into_iter()
                    .map(|tag| Self::OutOfFragment(Qualifier::Named(tag))),
            )
            .chain(MODEL_FAULTS.map(|fault| Self::UnstatedComponent(model_tag(fault))))
            .chain(MEMBER_FAULTS.map(|fault| Self::UndescribedMember(member_tag(fault))))
            .collect()
    }

    /// The name as a `refuses` payload spells it: the name of the variant it
    /// names, and the qualifier of one named by the feature it refuses.
    ///
    /// # Specification
    /// - requires: nothing; the function is total over the vocabulary.
    /// - ensures: each name's spelling is its own variant's identifier, with
    ///   the qualifier exactly when the variant carries one, and no two names
    ///   share one.
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
        (self, ret.head.as_bytes()), (Self::UnresolvedName, b"UnresolvedName") |
        (Self::UnresolvedDocLink, b"UnresolvedDocLink") |
        (Self::UnresolvedTypeHead, b"UnresolvedTypeHead") | (Self::DuplicateSignature,
        b"DuplicateSignature") | (Self::DuplicateDefinition, b"DuplicateDefinition") |
        (Self::DuplicateImportAlias, b"DuplicateImportAlias") | (Self::ImportUnresolved,
        b"ImportUnresolved") | (Self::ImportCycle, b"ImportCycle") | (Self::ImportShadows,
        b"ImportShadows") | (Self::UnexportedName, b"UnexportedName") | (Self::ShadowedBuiltin,
        b"ShadowedBuiltin") | (Self::OutOfFragment(_), b"OutOfFragment") |
        (Self::BareFeedback, b"BareFeedback") |
        (Self::IllFormedDescription, b"IllFormedDescription") |
        (Self::GradedBridge, b"GradedBridge") | (Self::MalformedLiteral,
        b"MalformedLiteral") | (Self::MalformedForm, b"MalformedForm") |
        (Self::UnknownAttribute, b"UnknownAttribute") | (Self::DuplicateAttribute,
        b"DuplicateAttribute") | (Self::MissingPayload, b"MissingPayload") |
        (Self::NonValuePayload, b"NonValuePayload") | (Self::IllTypedPayload,
        b"IllTypedPayload") | (Self::ForwardMemberReference, b"ForwardMemberReference") |
        (Self::PhaseDependence, b"PhaseDependence") |
        (Self::UnknownMember, b"UnknownMember") | (Self::NotAFunctor, b"NotAFunctor")
        | (Self::ProjectionFromApplication, b"ProjectionFromApplication")
        | (Self::UnreadAscription,
        b"UnreadAscription") | (Self::UnstatedComponent(_), b"UnstatedComponent") |
        (Self::UndescribedMember(_), b"UndescribedMember") |
        (Self::FamilyTelescope, b"FamilyTelescope") | (Self::LowercaseModuleName,
        b"LowercaseModuleName") |
        (Self::ImplicitTelescope, b"ImplicitTelescope") |
        (Self::TelescopeCycle, b"TelescopeCycle") |
        (Self::ImplicitUnsupplied, b"ImplicitUnsupplied") |
        (Self::ImplicitInParentheses, b"ImplicitInParentheses") |
        (Self::RegionAsValue, b"RegionAsValue") |
        (Self::StrayReceiverMode, b"StrayReceiverMode") |
        (Self::AmbiguousMethod, b"AmbiguousMethod") |
        (Self::ViewNotPlace, b"ViewNotPlace") |
        (Self::ViewOfNoPlace, b"ViewOfNoPlace") |
        (Self::NonExhaustiveMatch, b"NonExhaustiveMatch") |
        (Self::UnmarkedSelfReference, b"UnmarkedSelfReference") |
        (Self::UnguardedCorecursion, b"UnguardedCorecursion") |
        (Self::DescentOnSeveralParameters, b"DescentOnSeveralParameters") |
        (Self::Unreachable, b"Unreachable") |
        (Self::OutsideLoop, b"OutsideLoop") |
        (Self::AcrossHandler, b"AcrossHandler") |
        (Self::WithoutK, b"WithoutK") |
        (Self::DirectedCell, b"DirectedCell") |
        (Self::CellNotALoop, b"CellNotALoop") |
        (Self::RulesUnoriented, b"RulesUnoriented") |
        (Self::RulesNonLinear, b"RulesNonLinear") |
        (Self::RulesDiverge, b"RulesDiverge") |
        (Self::RulesOverlapSecondOrder, b"RulesOverlapSecondOrder") |
        (Self::RulesUncompleted, b"RulesUncompleted") |
        (Self::RulesNeverComplete, b"RulesNeverComplete") |
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
        | (Self::StagesDisagree, b"StagesDisagree")
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
        | (Self::EndpointAsValue, b"EndpointAsValue")
        | (Self::ArmsDisagree, b"ArmsDisagree")
        | (Self::UnrestrictedEndpoint, b"UnrestrictedEndpoint")
        | (Self::UnboundEndpoint, b"UnboundEndpoint")
        | (Self::BufferUnreturned, b"BufferUnreturned")
        | (Self::BufferReturnedTwice, b"BufferReturnedTwice")
        | (Self::BufferRead, b"BufferRead")
        | (Self::ContinuationUnspent, b"ContinuationUnspent")
        | (Self::ContinuationUsedTwice, b"ContinuationUsedTwice")
        | (Self::ContinuationCaptured, b"ContinuationCaptured")
        | (Self::ContinuationAsValue, b"ContinuationAsValue")
        | (Self::NotHeld, b"NotHeld")
        | (Self::HeldLent, b"HeldLent")
        | (Self::HeldCaptured, b"HeldCaptured")
        | (Self::ViewEscaped, b"ViewEscaped")
        | (Self::ViewUnended, b"ViewUnended")
        | (Self::ViewSpent, b"ViewSpent")
        | (Self::NotAView, b"NotAView")
        | (Self::ViewReadOnly, b"ViewReadOnly")
        | (Self::UnwindEffect, b"UnwindEffect")
        | (Self::PlaceUnindexed, b"PlaceUnindexed")
        | (Self::HeldShared, b"HeldShared")
        | (Self::HeldCopied, b"HeldCopied")
        | (Self::ViewMoved, b"ViewMoved")
        | (Self::HeldKept, b"HeldKept")
        | (Self::KeptEscaped, b"KeptEscaped")
        | (Self::HeldConsumed, b"HeldConsumed")
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
        | (Self::OpenSessionPayload, b"OpenSessionPayload")
        | (Self::NonCovariantMotive, b"NonCovariantMotive")
        | (Self::RideUnsupported, b"RideUnsupported")
        | (Self::RunNotAdmitted, b"RunNotAdmitted")
        | (Self::ForwardUnsupported, b"ForwardUnsupported")
        | (Self::Boundary, b"Boundary")
    ) && matches!(self, Self::OutOfFragment(_) | Self::UnstatedComponent(_) | Self::UndescribedMember(_))
        == ret.qualifier.is_some()
},
    )]
    #[inline]
    #[must_use]
    pub const fn spelling(self) -> RefusalSpelling
    {
        let head = match self {
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
            Self::StagesDisagree => "StagesDisagree",
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
            Self::EndpointAsValue => "EndpointAsValue",
            Self::ArmsDisagree => "ArmsDisagree",
            Self::UnrestrictedEndpoint => "UnrestrictedEndpoint",
            Self::UnboundEndpoint => "UnboundEndpoint",
            Self::BufferUnreturned => "BufferUnreturned",
            Self::BufferReturnedTwice => "BufferReturnedTwice",
            Self::BufferRead => "BufferRead",
            Self::ContinuationUnspent => "ContinuationUnspent",
            Self::ContinuationUsedTwice => "ContinuationUsedTwice",
            Self::ContinuationCaptured => "ContinuationCaptured",
            Self::ContinuationAsValue => "ContinuationAsValue",
            Self::NotHeld => "NotHeld",
            Self::HeldLent => "HeldLent",
            Self::HeldCaptured => "HeldCaptured",
            Self::ViewEscaped => "ViewEscaped",
            Self::ViewUnended => "ViewUnended",
            Self::ViewSpent => "ViewSpent",
            Self::NotAView => "NotAView",
            Self::ViewReadOnly => "ViewReadOnly",
            Self::UnwindEffect => "UnwindEffect",
            Self::PlaceUnindexed => "PlaceUnindexed",
            Self::HeldShared => "HeldShared",
            Self::HeldCopied => "HeldCopied",
            Self::ViewMoved => "ViewMoved",
            Self::HeldKept => "HeldKept",
            Self::KeptEscaped => "KeptEscaped",
            Self::HeldConsumed => "HeldConsumed",
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
            Self::OpenSessionPayload => "OpenSessionPayload",
            Self::NonCovariantMotive => "NonCovariantMotive",
            Self::RideUnsupported => "RideUnsupported",
            Self::RunNotAdmitted => "RunNotAdmitted",
            Self::ForwardUnsupported => "ForwardUnsupported",
            Self::Boundary => "Boundary",
            Self::ShadowedBuiltin => "ShadowedBuiltin",
            Self::OutOfFragment(_) => "OutOfFragment",
            Self::BareFeedback => "BareFeedback",
            Self::IllFormedDescription => "IllFormedDescription",
            Self::GradedBridge => "GradedBridge",
            Self::MalformedLiteral => "MalformedLiteral",
            Self::MalformedForm => "MalformedForm",
            Self::UnknownAttribute => "UnknownAttribute",
            Self::DuplicateAttribute => "DuplicateAttribute",
            Self::MissingPayload => "MissingPayload",
            Self::NonValuePayload => "NonValuePayload",
            Self::IllTypedPayload => "IllTypedPayload",
            Self::ForwardMemberReference => "ForwardMemberReference",
            Self::PhaseDependence => "PhaseDependence",
            Self::UnknownMember => "UnknownMember",
            Self::NotAFunctor => "NotAFunctor",
            Self::ProjectionFromApplication => "ProjectionFromApplication",
            Self::UnreadAscription => "UnreadAscription",
            Self::UnstatedComponent(_) => "UnstatedComponent",
            Self::UndescribedMember(_) => "UndescribedMember",
            Self::FamilyTelescope => "FamilyTelescope",
            Self::LowercaseModuleName => "LowercaseModuleName",
            Self::ImplicitTelescope => "ImplicitTelescope",
            Self::TelescopeCycle => "TelescopeCycle",
            Self::ImplicitUnsupplied => "ImplicitUnsupplied",
            Self::ImplicitInParentheses => "ImplicitInParentheses",
            Self::RegionAsValue => "RegionAsValue",
            Self::StrayReceiverMode => "StrayReceiverMode",
            Self::AmbiguousMethod => "AmbiguousMethod",
            Self::ViewNotPlace => "ViewNotPlace",
            Self::ViewOfNoPlace => "ViewOfNoPlace",
            Self::NonExhaustiveMatch => "NonExhaustiveMatch",
            Self::UnmarkedSelfReference => "UnmarkedSelfReference",
            Self::UnguardedCorecursion => "UnguardedCorecursion",
            Self::DescentOnSeveralParameters => "DescentOnSeveralParameters",
            Self::Unreachable => "Unreachable",
            Self::OutsideLoop => "OutsideLoop",
            Self::AcrossHandler => "AcrossHandler",
            Self::WithoutK => "WithoutK",
            Self::DirectedCell => "DirectedCell",
            Self::CellNotALoop => "CellNotALoop",
            Self::RulesUnoriented => "RulesUnoriented",
            Self::RulesNonLinear => "RulesNonLinear",
            Self::RulesDiverge => "RulesDiverge",
            Self::RulesOverlapSecondOrder => "RulesOverlapSecondOrder",
            Self::RulesUncompleted => "RulesUncompleted",
            Self::RulesNeverComplete => "RulesNeverComplete",
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
        };
        let qualifier = if let Self::OutOfFragment(qualifier) = self {
            Some(qualifier)
        }
        else if let Self::UnstatedComponent(fault) | Self::UndescribedMember(fault) = self {
            Some(Qualifier::Named(fault))
        }
        else {
            None
        };
        RefusalSpelling { head, qualifier }
    }

    /// The name `literal` spells, when the vocabulary holds it.
    ///
    /// # Specification
    /// - requires: nothing — any text is admissible input.
    /// - ensures: the name whose spelling equals the literal's content byte for
    ///   byte; no case folding, trimming or prefix match. A qualified name is
    ///   read only with a qualifier some refusal carries: a form the grammar
    ///   names, at a sort only where the sort decides its issue; a boundary
    ///   other than reserved and unadmitted; the run target; a checker former;
    ///   a model component's or a member's fault.
    /// - provides: the reading of a `refuses` payload.
    /// - fails: never; text naming nothing is the [`refusal_name::Absent`]
    ///   absence, which the expectation reader turns into a fixture failure.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — changed case, dropped letters, surrounding
    ///   whitespace, suffixes, empty text, a bare qualified variant and a
    ///   qualifier no refusal carries are refused rather than matched
    ///   permissively. Source fixtures exercise the corresponding exact
    ///   identifiers.
    /// - witness: `settle::tests::every_refusal_a_source_reaches_settles_the_fixture_naming_it`
    /// - witness: `refusal::tests::a_near_miss_names_no_refusal`
    /// - witness: `refusal::tests::every_qualified_spelling_reads_as_the_text_that_names_it`
    #[spec(
        ensures: |ret| match ret {
    Maybe::Present(name) => name.spelling().to_string() == literal.as_ref(),
    Maybe::Absent(refusal_name::Absent::Unnamed) => {
        Self::VOCABULARY.iter().all(|name| name.spelling().to_string() != literal.as_ref())
    }
},
    )]
    #[inline]
    pub fn named_by(literal: &StringLiteral) -> Maybe<Self, refusal_name::Absent>
    {
        let written: &str = literal.as_ref();
        let unqualified = Self::VOCABULARY
            .into_iter()
            .find(|name| name.spelling().head == written);
        let qualified = || {
            let (head, rest) = written.split_once('.')?;
            let tagged = |tags: &[Tag]| tags.iter().copied().find(|tag| tag.0 == rest);
            match head {
                "OutOfFragment" => tagged(&readings())
                    .map(Qualifier::Named)
                    .or_else(|| {
                        let (form, at) = rest
                            .split_once('.')
                            .map_or((rest, None), |(form, at)| (form, Some(at)));
                        let form = TREE_SITTER_NAMED_KINDS
                            .iter()
                            .chain(PBG_ONLY_KINDS)
                            .find(|&&kind| kind == form)
                            .map(|&kind| FormName::from(NamedKind(kind)))?;
                        at.map_or_else(
                            || {
                                (FragmentFeature::of(
                                    form,
                                    FragmentSort::Value,
                                    FragmentBoundary::Unadmitted,
                                ) == FragmentFeature::Form(form))
                                .then_some(Qualifier::Form(form))
                            },
                            |at| {
                                SORTS
                                    .into_iter()
                                    .find(|&sort| {
                                        sort_tag(sort).0 == at
                                            && FragmentFeature::of(
                                                form,
                                                sort,
                                                FragmentBoundary::Unadmitted,
                                            ) == FragmentFeature::FormAt(form, sort)
                                    })
                                    .map(|sort| Qualifier::FormAt(form, sort_tag(sort)))
                            },
                        )
                    })
                    .map(Self::OutOfFragment),
                "UnstatedComponent" => {
                    tagged(&MODEL_FAULTS.map(model_tag)).map(Self::UnstatedComponent)
                },
                "UndescribedMember" => {
                    tagged(&MEMBER_FAULTS.map(member_tag)).map(Self::UndescribedMember)
                },
                _ => None,
            }
        };
        unqualified
            .or_else(qualified)
            .map_or(Maybe::Absent(refusal_name::Absent::Unnamed), Maybe::Present)
    }
}

/// The tag the run target is qualified by: a form of the wrong sort where a
/// declaration is read.
const RUN_TARGET: Tag = Tag("WrongSort.declaration");

/// Every sort a form out of the fragment is read at.
const SORTS: [FragmentSort; 8_usize] = [
    FragmentSort::Module,
    FragmentSort::Declaration,
    FragmentSort::ValueType,
    FragmentSort::CompType,
    FragmentSort::Value,
    FragmentSort::Computation,
    FragmentSort::Pattern,
    FragmentSort::Continuation,
];

/// Every former the checker's judgement has no rule for.
const FORMERS: [UnadmittedFormer; 25_usize] = [
    UnadmittedFormer::ValueLift,
    UnadmittedFormer::NumericLiteral,
    UnadmittedFormer::NumericAtom,
    UnadmittedFormer::TypeLift,
    UnadmittedFormer::Abstract,
    UnadmittedFormer::SortParameter,
    UnadmittedFormer::TopUniverse,
    UnadmittedFormer::StaticLambda,
    UnadmittedFormer::EffectRow,
    UnadmittedFormer::Reify,
    UnadmittedFormer::Stack,
    UnadmittedFormer::Perform,
    UnadmittedFormer::Handle,
    UnadmittedFormer::Resume,
    UnadmittedFormer::Reset,
    UnadmittedFormer::Shift,
    UnadmittedFormer::Capability,
    UnadmittedFormer::Exercise,
    UnadmittedFormer::Scope,
    UnadmittedFormer::Run,
    UnadmittedFormer::HigherFlow,
    UnadmittedFormer::Memory,
    UnadmittedFormer::Stage,
    UnadmittedFormer::Buffer,
    UnadmittedFormer::Abandon,
];

/// Every fault a model component the derivation cannot state carries.
const MODEL_FAULTS: [ModelFault; 10_usize] = [
    ModelFault::UnknownHead,
    ModelFault::Arity,
    ModelFault::IllSorted,
    ModelFault::Unsorted,
    ModelFault::ManyOut,
    ModelFault::Circuit,
    ModelFault::Constructor,
    ModelFault::Inherited,
    ModelFault::Binding,
    ModelFault::Abstraction,
];

/// Every fault a member the description does not read carries.
const MEMBER_FAULTS: [MemberFault; 19_usize] = [
    MemberFault::HigherOrderField,
    MemberFault::DependentField,
    MemberFault::TypeShape,
    MemberFault::NativeDecode,
    MemberFault::OperationFiller,
    MemberFault::HigherCell,
    MemberFault::Reversible,
    MemberFault::NoOutput,
    MemberFault::AggregatedOutput,
    MemberFault::LhsNotOperation,
    MemberFault::EmptyOperation,
    MemberFault::NestedOperation,
    MemberFault::UnrepresentableOperation,
    MemberFault::ResultArity,
    MemberFault::MixedPolarity,
    MemberFault::UnderivedWiring,
    MemberFault::ParallelRedexes,
    MemberFault::OffBoundary,
    MemberFault::AtomOccurrence,
];

/// Every boundary a form out of the fragment crosses and is named by: every
/// boundary but reserved and unadmitted, which name the form instead, an
/// arity standing for every operand count.
///
/// # Specification
/// trivial.
fn crossed() -> [FragmentBoundary; 14_usize]
{
    [
        FragmentBoundary::WrongSort,
        FragmentBoundary::Arity(OperandCount::from(0_usize)),
        FragmentBoundary::Indexed,
        FragmentBoundary::Unannotated,
        FragmentBoundary::NonUniform,
        FragmentBoundary::ForeignClaim,
        FragmentBoundary::NotAFunction,
        FragmentBoundary::NotInTail,
        FragmentBoundary::JoinsBlock,
        FragmentBoundary::EmptyList,
        FragmentBoundary::Endpoint,
        FragmentBoundary::NonContractive,
        FragmentBoundary::Held,
        FragmentBoundary::View,
    ]
}

/// The tags an `OutOfFragment` name is qualified by when no form qualifies it:
/// each boundary a form crosses, the run target and each former the checker
/// declines.
///
/// # Specification
/// - requires: nothing.
/// - ensures: each crossed boundary's tag, in order, then the run target, then
///   each former's tag.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — every qualified spelling of these tags reads back as its
///   name, and every closed name is among them; a lost tag is a name no payload
///   spells.
/// - witness: `refusal::tests::every_qualified_spelling_reads_as_the_text_that_names_it`
#[spec(ensures: |ret| ret.len() == crossed().len().saturating_add(1).saturating_add(FORMERS.len()) && ret.get(crossed().len()) == Some(&RUN_TARGET))]
fn readings() -> Vec<Tag>
{
    crossed()
        .into_iter()
        .map(boundary_tag)
        .chain([RUN_TARGET])
        .chain(FORMERS.into_iter().map(former_tag))
        .collect()
}

/// The qualifier of the feature a form out of the fragment refuses.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a form is the form; a form at a sort the form and the sort's tag;
///   the run target [`RUN_TARGET`]; a crossing the boundary's tag.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`RefusalName::named_by`]: each qualifier a source
///   reaches reads back as the name it spells.
/// - witness: `refusal::tests::every_qualified_spelling_reads_as_the_text_that_names_it`
#[spec(ensures: |ret| match feature {
    | FragmentFeature::Form(form) => ret == Qualifier::Form(form),
    | FragmentFeature::FormAt(form, sort) => ret == Qualifier::FormAt(form, sort_tag(sort)),
    | FragmentFeature::RunTarget => ret == Qualifier::Named(RUN_TARGET),
    | FragmentFeature::Crossed(boundary) => ret == Qualifier::Named(boundary_tag(boundary)),
})]
fn fragment(feature: FragmentFeature) -> Qualifier
{
    match feature {
        FragmentFeature::Form(form) => Qualifier::Form(form),
        FragmentFeature::FormAt(form, sort) => Qualifier::FormAt(form, sort_tag(sort)),
        FragmentFeature::RunTarget => Qualifier::Named(RUN_TARGET),
        FragmentFeature::Crossed(boundary) => Qualifier::Named(boundary_tag(boundary)),
    }
}

/// The tag a boundary is named by: its variant, an arity's without the
/// operand count.
///
/// # Specification
/// trivial.
const fn boundary_tag(boundary: FragmentBoundary) -> Tag
{
    Tag(match boundary {
        FragmentBoundary::Reserved => "Reserved",
        FragmentBoundary::Unadmitted => "Unadmitted",
        FragmentBoundary::WrongSort => "WrongSort",
        FragmentBoundary::Arity(_) => "Arity",
        FragmentBoundary::Indexed => "Indexed",
        FragmentBoundary::Unannotated => "Unannotated",
        FragmentBoundary::NonUniform => "NonUniform",
        FragmentBoundary::ForeignClaim => "ForeignClaim",
        FragmentBoundary::NotAFunction => "NotAFunction",
        FragmentBoundary::NotInTail => "NotInTail",
        FragmentBoundary::JoinsBlock => "JoinsBlock",
        FragmentBoundary::EmptyList => "EmptyList",
        FragmentBoundary::Endpoint => "Endpoint",
        FragmentBoundary::NonContractive => "NonContractive",
        FragmentBoundary::Held => "Held",
        FragmentBoundary::View => "View",
    })
}

/// The tag a sort is named by, snake case as a form is.
///
/// # Specification
/// trivial.
const fn sort_tag(sort: FragmentSort) -> Tag
{
    Tag(match sort {
        FragmentSort::Module => "module",
        FragmentSort::Declaration => "declaration",
        FragmentSort::ValueType => "value_type",
        FragmentSort::CompType => "comp_type",
        FragmentSort::Value => "value",
        FragmentSort::Computation => "computation",
        FragmentSort::Pattern => "pattern",
        FragmentSort::Continuation => "continuation",
    })
}

/// The tag a checker former is named by: its variant.
///
/// # Specification
/// trivial.
const fn former_tag(former: UnadmittedFormer) -> Tag
{
    Tag(match former {
        UnadmittedFormer::ValueLift => "ValueLift",
        UnadmittedFormer::NumericLiteral => "NumericLiteral",
        UnadmittedFormer::NumericAtom => "NumericAtom",
        UnadmittedFormer::TypeLift => "TypeLift",
        UnadmittedFormer::Abstract => "Abstract",
        UnadmittedFormer::SortParameter => "SortParameter",
        UnadmittedFormer::TopUniverse => "TopUniverse",
        UnadmittedFormer::StaticLambda => "StaticLambda",
        UnadmittedFormer::EffectRow => "EffectRow",
        UnadmittedFormer::Reify => "Reify",
        UnadmittedFormer::Stack => "Stack",
        UnadmittedFormer::Perform => "Perform",
        UnadmittedFormer::Handle => "Handle",
        UnadmittedFormer::Resume => "Resume",
        UnadmittedFormer::Reset => "Reset",
        UnadmittedFormer::Shift => "Shift",
        UnadmittedFormer::Capability => "Capability",
        UnadmittedFormer::Exercise => "Exercise",
        UnadmittedFormer::Scope => "Scope",
        UnadmittedFormer::Run => "Run",
        UnadmittedFormer::HigherFlow => "HigherFlow",
        UnadmittedFormer::Memory => "Memory",
        UnadmittedFormer::Stage => "Stage",
        UnadmittedFormer::Buffer => "Buffer",
        UnadmittedFormer::Abandon => "Abandon",
    })
}

/// The tag a model component's fault is named by: its variant.
///
/// # Specification
/// trivial.
const fn model_tag(fault: ModelFault) -> Tag
{
    Tag(match fault {
        ModelFault::UnknownHead => "UnknownHead",
        ModelFault::Arity => "Arity",
        ModelFault::IllSorted => "IllSorted",
        ModelFault::Unsorted => "Unsorted",
        ModelFault::ManyOut => "ManyOut",
        ModelFault::Circuit => "Circuit",
        ModelFault::Constructor => "Constructor",
        ModelFault::Inherited => "Inherited",
        ModelFault::Binding => "Binding",
        ModelFault::Abstraction => "Abstraction",
    })
}

/// The tag a description member's fault is named by: its variant.
///
/// # Specification
/// trivial.
const fn member_tag(fault: MemberFault) -> Tag
{
    Tag(match fault {
        MemberFault::HigherOrderField => "HigherOrderField",
        MemberFault::DependentField => "DependentField",
        MemberFault::TypeShape => "TypeShape",
        MemberFault::NativeDecode => "NativeDecode",
        MemberFault::OperationFiller => "OperationFiller",
        MemberFault::HigherCell => "HigherCell",
        MemberFault::Reversible => "Reversible",
        MemberFault::NoOutput => "NoOutput",
        MemberFault::AggregatedOutput => "AggregatedOutput",
        MemberFault::LhsNotOperation => "LhsNotOperation",
        MemberFault::EmptyOperation => "EmptyOperation",
        MemberFault::NestedOperation => "NestedOperation",
        MemberFault::UnrepresentableOperation => "UnrepresentableOperation",
        MemberFault::ResultArity => "ResultArity",
        MemberFault::MixedPolarity => "MixedPolarity",
        MemberFault::UnderivedWiring => "UnderivedWiring",
        MemberFault::ParallelRedexes => "ParallelRedexes",
        MemberFault::OffBoundary => "OffBoundary",
        MemberFault::AtomOccurrence => "AtomOccurrence",
    })
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
        RefusalName::OutOfFragment(_)) | (Self::Lowering(LoweringRefusal::BareFeedback { .. }),
        RefusalName::BareFeedback) |
        (Self::Lowering(LoweringRefusal::IllFormedDescription { .. }),
        RefusalName::IllFormedDescription) | (Self::Lowering(LoweringRefusal::GradedBridge { ..
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
        (Self::Lowering(LoweringRefusal::PhaseDependence { .. }),
        RefusalName::PhaseDependence) |
        (Self::Lowering(LoweringRefusal::UnknownMember { .. }),
        RefusalName::UnknownMember) | (Self::Lowering(LoweringRefusal::NotAFunctor { .. }),
        RefusalName::NotAFunctor) |
        (Self::Lowering(LoweringRefusal::ProjectionFromApplication { .. }),
        RefusalName::ProjectionFromApplication) |
        (Self::Lowering(LoweringRefusal::UnreadAscription {
        .. }), RefusalName::UnreadAscription) |
        (Self::Lowering(LoweringRefusal::UnstatedComponent { .. }),
        RefusalName::UnstatedComponent(_)) |
        (Self::Lowering(LoweringRefusal::UndescribedMember { .. }),
        RefusalName::UndescribedMember(_)) |
        (Self::Lowering(LoweringRefusal::FamilyTelescope { .. }),
        RefusalName::FamilyTelescope) |
        (Self::Lowering(LoweringRefusal::LowercaseModuleName { .. }),
        RefusalName::LowercaseModuleName) |
        (Self::Lowering(LoweringRefusal::ImplicitTelescope { .. }),
        RefusalName::ImplicitTelescope) |
        (Self::Lowering(LoweringRefusal::TelescopeCycle { .. }),
        RefusalName::TelescopeCycle) |
        (Self::Lowering(LoweringRefusal::ImplicitUnsupplied { .. }),
        RefusalName::ImplicitUnsupplied) |
        (Self::Lowering(LoweringRefusal::ImplicitInParentheses { .. }),
        RefusalName::ImplicitInParentheses) |
        (Self::Lowering(LoweringRefusal::RegionAsValue { .. }),
        RefusalName::RegionAsValue) |
        (Self::Lowering(LoweringRefusal::StrayReceiverMode { .. }),
        RefusalName::StrayReceiverMode) |
        (Self::Lowering(LoweringRefusal::AmbiguousMethod { .. }),
        RefusalName::AmbiguousMethod) |
        (Self::Lowering(LoweringRefusal::ViewNotPlace { .. }),
        RefusalName::ViewNotPlace) |
        (Self::Lowering(LoweringRefusal::ViewOfNoPlace { .. }),
        RefusalName::ViewOfNoPlace) |
        (Self::Lowering(LoweringRefusal::NonExhaustiveMatch { .. }),
        RefusalName::NonExhaustiveMatch) |
        (Self::Lowering(LoweringRefusal::UnmarkedSelfReference { .. }),
        RefusalName::UnmarkedSelfReference) |
        (Self::Lowering(LoweringRefusal::UnguardedCorecursion { .. }),
        RefusalName::UnguardedCorecursion) |
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
        (Self::Lowering(LoweringRefusal::RulesNonLinear { .. }),
        RefusalName::RulesNonLinear) |
        (Self::Lowering(LoweringRefusal::RulesDiverge { .. }),
        RefusalName::RulesDiverge) |
        (Self::Lowering(LoweringRefusal::RulesOverlapSecondOrder { .. }),
        RefusalName::RulesOverlapSecondOrder) |
        (Self::Lowering(LoweringRefusal::RulesUncompleted { .. }),
        RefusalName::RulesUncompleted) |
        (Self::Lowering(LoweringRefusal::RulesNeverComplete { .. }),
        RefusalName::RulesNeverComplete) |
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
        | (Self::Checking(CheckRefusal::StageNotBelow { .. }), RefusalName::StageNotBelow)
        | (Self::Checking(CheckRefusal::StagesDisagree { .. }), RefusalName::StagesDisagree) |
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
        | (Self::Checking(CheckRefusal::Linearity { .. }), RefusalName::LinearResidue | RefusalName::UsedAfterClose | RefusalName::EndpointUsedTwice | RefusalName::CapturedEndpoint | RefusalName::EndpointAsValue | RefusalName::ArmsDisagree | RefusalName::UnrestrictedEndpoint | RefusalName::UnboundEndpoint | RefusalName::BufferUnreturned | RefusalName::BufferReturnedTwice | RefusalName::BufferRead | RefusalName::ContinuationUnspent | RefusalName::ContinuationUsedTwice | RefusalName::ContinuationCaptured | RefusalName::ContinuationAsValue)
        | (Self::Checking(CheckRefusal::Access { .. }), RefusalName::NotHeld | RefusalName::HeldLent | RefusalName::HeldCaptured | RefusalName::ViewEscaped | RefusalName::ViewUnended | RefusalName::ViewSpent | RefusalName::NotAView | RefusalName::ViewReadOnly | RefusalName::UnwindEffect | RefusalName::PlaceUnindexed | RefusalName::HeldShared | RefusalName::HeldCopied | RefusalName::ViewMoved | RefusalName::HeldKept | RefusalName::KeptEscaped | RefusalName::HeldConsumed)
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
        | (Self::Checking(CheckRefusal::OpenSessionPayload { .. }), RefusalName::OpenSessionPayload)
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
    pub fn name(&self) -> RefusalName
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
    expected == ret
},
    )]
    #[inline]
    #[must_use]
    pub fn classify(&self) -> FailureClass
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
///   independently of its payload, except that a form out of the fragment is
///   qualified by the feature [`FragmentFeature::of`] reads off its form, sort
///   and boundary, and an unstated component and an undescribed member by their
///   fault.
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
        RefusalName::OutOfFragment(_)) | (LoweringRefusal::BareFeedback { .. },
        RefusalName::BareFeedback) | (LoweringRefusal::IllFormedDescription { .. },
        RefusalName::IllFormedDescription) | (LoweringRefusal::GradedBridge { .. },
        RefusalName::GradedBridge) | (LoweringRefusal::MalformedLiteral { .. },
        RefusalName::MalformedLiteral) | (LoweringRefusal::MalformedForm { .. },
        RefusalName::MalformedForm) | (LoweringRefusal::UnknownAttribute { .. },
        RefusalName::UnknownAttribute) | (LoweringRefusal::DuplicateAttribute { .. },
        RefusalName::DuplicateAttribute) | (LoweringRefusal::MissingPayload { .. },
        RefusalName::MissingPayload) | (LoweringRefusal::NonValuePayload { .. },
        RefusalName::NonValuePayload) | (LoweringRefusal::IllTypedPayload { .. },
        RefusalName::IllTypedPayload) | (LoweringRefusal::ForwardMemberReference { .. },
        RefusalName::ForwardMemberReference) | (LoweringRefusal::PhaseDependence { .. },
        RefusalName::PhaseDependence) | (LoweringRefusal::UnknownMember { .. },
        RefusalName::UnknownMember) | (LoweringRefusal::NotAFunctor { .. },
        RefusalName::NotAFunctor) | (LoweringRefusal::ProjectionFromApplication { .. },
        RefusalName::ProjectionFromApplication) | (LoweringRefusal::UnreadAscription { .. },
        RefusalName::UnreadAscription) | (LoweringRefusal::UnstatedComponent { .. },
        RefusalName::UnstatedComponent(_)) | (LoweringRefusal::UndescribedMember { .. },
        RefusalName::UndescribedMember(_)) | (LoweringRefusal::FamilyTelescope { .. },
        RefusalName::FamilyTelescope) | (LoweringRefusal::LowercaseModuleName { .. },
        RefusalName::LowercaseModuleName) | (LoweringRefusal::ImplicitTelescope { .. },
        RefusalName::ImplicitTelescope) | (LoweringRefusal::TelescopeCycle { .. },
        RefusalName::TelescopeCycle) | (LoweringRefusal::ImplicitUnsupplied { .. },
        RefusalName::ImplicitUnsupplied) | (LoweringRefusal::ImplicitInParentheses { .. },
        RefusalName::ImplicitInParentheses) | (LoweringRefusal::RegionAsValue { .. },
        RefusalName::RegionAsValue) | (LoweringRefusal::StrayReceiverMode { .. },
        RefusalName::StrayReceiverMode) | (LoweringRefusal::AmbiguousMethod { .. },
        RefusalName::AmbiguousMethod) | (LoweringRefusal::ViewNotPlace { .. },
        RefusalName::ViewNotPlace) | (LoweringRefusal::ViewOfNoPlace { .. },
        RefusalName::ViewOfNoPlace) | (LoweringRefusal::NonExhaustiveMatch { .. },
        RefusalName::NonExhaustiveMatch) | (LoweringRefusal::UnmarkedSelfReference { .. },
        RefusalName::UnmarkedSelfReference) | (LoweringRefusal::UnguardedCorecursion { .. },
        RefusalName::UnguardedCorecursion) | (LoweringRefusal::DescentOnSeveralParameters { .. },
        RefusalName::DescentOnSeveralParameters) | (LoweringRefusal::Unreachable { .. },
        RefusalName::Unreachable) | (LoweringRefusal::OutsideLoop { .. },
        RefusalName::OutsideLoop) | (LoweringRefusal::AcrossHandler { .. },
        RefusalName::AcrossHandler) | (LoweringRefusal::WithoutK { .. },
        RefusalName::WithoutK) | (LoweringRefusal::DirectedCell { .. },
        RefusalName::DirectedCell) | (LoweringRefusal::CellNotALoop { .. },
        RefusalName::CellNotALoop) | (LoweringRefusal::RulesUnoriented { .. },
        RefusalName::RulesUnoriented) | (LoweringRefusal::RulesNonLinear { .. },
        RefusalName::RulesNonLinear) | (LoweringRefusal::RulesDiverge { .. },
        RefusalName::RulesDiverge) | (LoweringRefusal::RulesOverlapSecondOrder { .. },
        RefusalName::RulesOverlapSecondOrder) | (LoweringRefusal::RulesUncompleted { .. },
        RefusalName::RulesUncompleted) | (LoweringRefusal::RulesNeverComplete { .. },
        RefusalName::RulesNeverComplete) | (LoweringRefusal::RulesUndecided { .. },
        RefusalName::RulesUndecided) | (LoweringRefusal::BudgetExceeded { .. },
        RefusalName::BudgetExceeded) | (LoweringRefusal::GrammarMismatch { .. },
        RefusalName::GrammarMismatch) | (LoweringRefusal::UnknownMold { .. },
        RefusalName::UnknownMold) | (LoweringRefusal::Unminted { .. },
        RefusalName::Unminted)
    ) && if let LoweringRefusal::OutOfFragment { form, sort, boundary, .. } = refusal {
        ret == RefusalName::OutOfFragment(fragment(FragmentFeature::of(form, sort, boundary)))
    } else if let LoweringRefusal::UnstatedComponent { fault, .. } = refusal {
        ret == RefusalName::UnstatedComponent(model_tag(fault))
    } else if let LoweringRefusal::UndescribedMember { fault, .. } = refusal {
        ret == RefusalName::UndescribedMember(member_tag(fault))
    } else {
        true
    }
},
)]
fn lowering_name(refusal: LoweringRefusal<'_>) -> RefusalName
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
        LoweringRefusal::OutOfFragment {
            form,
            sort,
            boundary,
            ..
        } => RefusalName::OutOfFragment(fragment(FragmentFeature::of(form, sort, boundary))),
        LoweringRefusal::BareFeedback { .. } => RefusalName::BareFeedback,
        LoweringRefusal::IllFormedDescription { .. } => RefusalName::IllFormedDescription,
        LoweringRefusal::GradedBridge { .. } => RefusalName::GradedBridge,
        LoweringRefusal::MalformedLiteral { .. } => RefusalName::MalformedLiteral,
        LoweringRefusal::MalformedForm { .. } => RefusalName::MalformedForm,
        LoweringRefusal::UnknownAttribute { .. } => RefusalName::UnknownAttribute,
        LoweringRefusal::DuplicateAttribute { .. } => RefusalName::DuplicateAttribute,
        LoweringRefusal::MissingPayload { .. } => RefusalName::MissingPayload,
        LoweringRefusal::NonValuePayload { .. } => RefusalName::NonValuePayload,
        LoweringRefusal::IllTypedPayload { .. } => RefusalName::IllTypedPayload,
        LoweringRefusal::ForwardMemberReference { .. } => RefusalName::ForwardMemberReference,
        LoweringRefusal::PhaseDependence { .. } => RefusalName::PhaseDependence,
        LoweringRefusal::UnknownMember { .. } => RefusalName::UnknownMember,
        LoweringRefusal::NotAFunctor { .. } => RefusalName::NotAFunctor,
        LoweringRefusal::ProjectionFromApplication { .. } => RefusalName::ProjectionFromApplication,
        LoweringRefusal::UnreadAscription { .. } => RefusalName::UnreadAscription,
        LoweringRefusal::UnstatedComponent { fault, .. } => {
            RefusalName::UnstatedComponent(model_tag(fault))
        },
        LoweringRefusal::UndescribedMember { fault, .. } => {
            RefusalName::UndescribedMember(member_tag(fault))
        },
        LoweringRefusal::FamilyTelescope { .. } => RefusalName::FamilyTelescope,
        LoweringRefusal::LowercaseModuleName { .. } => RefusalName::LowercaseModuleName,
        LoweringRefusal::ImplicitTelescope { .. } => RefusalName::ImplicitTelescope,
        LoweringRefusal::TelescopeCycle { .. } => RefusalName::TelescopeCycle,
        LoweringRefusal::ImplicitUnsupplied { .. } => RefusalName::ImplicitUnsupplied,
        LoweringRefusal::ImplicitInParentheses { .. } => RefusalName::ImplicitInParentheses,
        LoweringRefusal::RegionAsValue { .. } => RefusalName::RegionAsValue,
        LoweringRefusal::StrayReceiverMode { .. } => RefusalName::StrayReceiverMode,
        LoweringRefusal::AmbiguousMethod { .. } => RefusalName::AmbiguousMethod,
        LoweringRefusal::ViewNotPlace { .. } => RefusalName::ViewNotPlace,
        LoweringRefusal::ViewOfNoPlace { .. } => RefusalName::ViewOfNoPlace,
        LoweringRefusal::NonExhaustiveMatch { .. } => RefusalName::NonExhaustiveMatch,
        LoweringRefusal::UnmarkedSelfReference { .. } => RefusalName::UnmarkedSelfReference,
        LoweringRefusal::UnguardedCorecursion { .. } => RefusalName::UnguardedCorecursion,
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
        LoweringRefusal::RulesNonLinear { .. } => RefusalName::RulesNonLinear,
        LoweringRefusal::RulesDiverge { .. } => RefusalName::RulesDiverge,
        LoweringRefusal::RulesOverlapSecondOrder { .. } => RefusalName::RulesOverlapSecondOrder,
        LoweringRefusal::RulesUncompleted { .. } => RefusalName::RulesUncompleted,
        LoweringRefusal::RulesNeverComplete { .. } => RefusalName::RulesNeverComplete,
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
///   by the defect it carries and a former out of the fragment is qualified by
///   the former.
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
        (CheckRefusal::OutOfFragment { .. }, RefusalName::OutOfFragment(_)) |
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
        | (CheckRefusal::StagesDisagree { .. }, RefusalName::StagesDisagree)
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
        | (CheckRefusal::Linearity { defect: LinearityDefect::AsValue { .. }, .. }, RefusalName::EndpointAsValue)
        | (CheckRefusal::Linearity { defect: LinearityDefect::ArmsDisagree { .. }, .. }, RefusalName::ArmsDisagree)
        | (CheckRefusal::Linearity { defect: LinearityDefect::Unrestricted, .. }, RefusalName::UnrestrictedEndpoint)
        | (CheckRefusal::Linearity { defect: LinearityDefect::Unbound { .. }, .. }, RefusalName::UnboundEndpoint)
        | (CheckRefusal::Linearity { defect: LinearityDefect::BufferUnreturned { .. }, .. }, RefusalName::BufferUnreturned)
        | (CheckRefusal::Linearity { defect: LinearityDefect::BufferReturnedTwice { .. }, .. }, RefusalName::BufferReturnedTwice)
        | (CheckRefusal::Linearity { defect: LinearityDefect::BufferRead { .. }, .. }, RefusalName::BufferRead)
        | (CheckRefusal::Linearity { defect: LinearityDefect::ContinuationUnspent { .. }, .. }, RefusalName::ContinuationUnspent)
        | (CheckRefusal::Linearity { defect: LinearityDefect::ContinuationUsedTwice { .. }, .. }, RefusalName::ContinuationUsedTwice)
        | (CheckRefusal::Linearity { defect: LinearityDefect::ContinuationCaptured { .. }, .. }, RefusalName::ContinuationCaptured)
        | (CheckRefusal::Linearity { defect: LinearityDefect::ContinuationAsValue { .. }, .. }, RefusalName::ContinuationAsValue)
        | (CheckRefusal::Access { defect: AccessDefect::NotHeld, .. }, RefusalName::NotHeld)
        | (CheckRefusal::Access { defect: AccessDefect::Lent, .. }, RefusalName::HeldLent)
        | (CheckRefusal::Access { defect: AccessDefect::HeldCaptured { .. }, .. }, RefusalName::HeldCaptured)
        | (CheckRefusal::Access { defect: AccessDefect::Escaped { .. }, .. }, RefusalName::ViewEscaped)
        | (CheckRefusal::Access { defect: AccessDefect::Unended, .. }, RefusalName::ViewUnended)
        | (CheckRefusal::Access { defect: AccessDefect::Spent, .. }, RefusalName::ViewSpent)
        | (CheckRefusal::Access { defect: AccessDefect::NotAView, .. }, RefusalName::NotAView)
        | (CheckRefusal::Access { defect: AccessDefect::ReadOnly, .. }, RefusalName::ViewReadOnly)
        | (CheckRefusal::Access { defect: AccessDefect::UnwindEffect, .. }, RefusalName::UnwindEffect)
        | (CheckRefusal::Access { defect: AccessDefect::Unindexed, .. }, RefusalName::PlaceUnindexed)
        | (CheckRefusal::Access { defect: AccessDefect::HeldShared, .. }, RefusalName::HeldShared)
        | (CheckRefusal::Access { defect: AccessDefect::HeldCopied, .. }, RefusalName::HeldCopied)
        | (CheckRefusal::Access { defect: AccessDefect::Moved, .. }, RefusalName::ViewMoved)
        | (CheckRefusal::Access { defect: AccessDefect::Kept, .. }, RefusalName::HeldKept)
        | (CheckRefusal::Access { defect: AccessDefect::KeptEscaped, .. }, RefusalName::KeptEscaped)
        | (CheckRefusal::Access { defect: AccessDefect::Consumed, .. }, RefusalName::HeldConsumed)
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
        | (CheckRefusal::OpenSessionPayload { .. }, RefusalName::OpenSessionPayload)
        | (CheckRefusal::NonCovariantMotive { .. }, RefusalName::NonCovariantMotive)
        | (CheckRefusal::RideUnsupported { .. }, RefusalName::RideUnsupported)
        | (CheckRefusal::RunNotAdmitted { .. }, RefusalName::RunNotAdmitted)
        | (CheckRefusal::ForwardUnsupported { .. }, RefusalName::ForwardUnsupported)
        | (CheckRefusal::Boundary { .. }, RefusalName::Boundary)
    ) && (!matches!(refusal, CheckRefusal::OutOfFragment { .. })
        || matches!((refusal, ret), (CheckRefusal::OutOfFragment { former, .. },
            RefusalName::OutOfFragment(Qualifier::Named(tag))) if tag.0 == former_tag(former).0))
},
)]
fn checking_name(refusal: CheckRefusal) -> RefusalName
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
            LinearityDefect::AsValue { .. } => RefusalName::EndpointAsValue,
            LinearityDefect::ArmsDisagree { .. } => RefusalName::ArmsDisagree,
            LinearityDefect::Unrestricted => RefusalName::UnrestrictedEndpoint,
            LinearityDefect::Unbound { .. } => RefusalName::UnboundEndpoint,
            LinearityDefect::BufferUnreturned { .. } => RefusalName::BufferUnreturned,
            LinearityDefect::BufferReturnedTwice { .. } => RefusalName::BufferReturnedTwice,
            LinearityDefect::BufferRead { .. } => RefusalName::BufferRead,
            LinearityDefect::ContinuationUnspent { .. } => RefusalName::ContinuationUnspent,
            LinearityDefect::ContinuationUsedTwice { .. } => RefusalName::ContinuationUsedTwice,
            LinearityDefect::ContinuationCaptured { .. } => RefusalName::ContinuationCaptured,
            LinearityDefect::ContinuationAsValue { .. } => RefusalName::ContinuationAsValue,
        },
        CheckRefusal::Access { defect, .. } => match defect {
            AccessDefect::NotHeld => RefusalName::NotHeld,
            AccessDefect::Lent => RefusalName::HeldLent,
            AccessDefect::HeldCaptured { .. } => RefusalName::HeldCaptured,
            AccessDefect::Escaped { .. } => RefusalName::ViewEscaped,
            AccessDefect::Unended => RefusalName::ViewUnended,
            AccessDefect::Spent => RefusalName::ViewSpent,
            AccessDefect::NotAView => RefusalName::NotAView,
            AccessDefect::ReadOnly => RefusalName::ViewReadOnly,
            AccessDefect::UnwindEffect => RefusalName::UnwindEffect,
            AccessDefect::Unindexed => RefusalName::PlaceUnindexed,
            AccessDefect::HeldShared => RefusalName::HeldShared,
            AccessDefect::HeldCopied => RefusalName::HeldCopied,
            AccessDefect::Moved => RefusalName::ViewMoved,
            AccessDefect::Kept => RefusalName::HeldKept,
            AccessDefect::KeptEscaped => RefusalName::KeptEscaped,
            AccessDefect::Consumed => RefusalName::HeldConsumed,
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
        CheckRefusal::OpenSessionPayload { .. } => RefusalName::OpenSessionPayload,
        CheckRefusal::NonCovariantMotive { .. } => RefusalName::NonCovariantMotive,
        CheckRefusal::RideUnsupported { .. } => RefusalName::RideUnsupported,
        CheckRefusal::RunNotAdmitted { .. } => RefusalName::RunNotAdmitted,
        CheckRefusal::ForwardUnsupported { .. } => RefusalName::ForwardUnsupported,
        CheckRefusal::Boundary { .. } => RefusalName::Boundary,
        CheckRefusal::TypeMismatch(_) => RefusalName::TypeMismatch,
        CheckRefusal::ShapeMismatch { .. } => RefusalName::ShapeMismatch,
        CheckRefusal::NotSynthesisable { .. } => RefusalName::NotSynthesisable,
        CheckRefusal::UnknownConstant { .. } => RefusalName::UnknownConstant,
        CheckRefusal::OutOfFragment { former, .. } => {
            RefusalName::OutOfFragment(Qualifier::Named(former_tag(former)))
        },
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
        CheckRefusal::StagesDisagree { .. } => RefusalName::StagesDisagree,
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
            "TypeMismatch.WrongSort",
            "OutOfFragment",
            "OutOfFragment.",
            "OutOfFragment.projection_expressions",
            "OutOfFragment.projection_expression.value",
            "OutOfFragment.instantiation_expression",
            "OutOfFragment.instantiation_expression.nowhere",
            "OutOfFragment.Reserved",
            "OutOfFragment.Arity(2)",
            "OutOfFragment.wrongsort",
            "UndescribedMember",
            "UndescribedMember.Bogus",
            "UnstatedComponent.HigherCell",
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
            let text = name.spelling().to_string();
            assert_eq!(text, name.to_string(), "{name:?} spells as it prints");
            assert_eq!(
                RefusalName::named_by(&StringLiteral::new(text.clone())),
                Maybe::Present(name),
                "`{text}` names {name:?}"
            );
        }
    }

    /// Every qualified name a producer mints reads back as itself, and the
    /// spellings are the variant, a dot and the feature (#1200).
    #[test]
    fn every_qualified_spelling_reads_as_the_text_that_names_it()
    {
        use gandr_surface_grammar::NamedKind;
        use gandr_surface_grammar::PBG_ONLY_KINDS;
        use gandr_surface_grammar::TREE_SITTER_NAMED_KINDS;
        use gandr_surface_lowering::FormName;
        use gandr_surface_lowering::FragmentBoundary;
        use gandr_surface_lowering::LoweringRefusal;
        use gandr_surface_lowering::OperandCount;

        use super::FORMERS;
        use super::MEMBER_FAULTS;
        use super::MODEL_FAULTS;
        use super::Qualifier;
        use super::RUN_TARGET;
        use super::Refusal;
        use super::SORTS;
        use super::boundary_tag;
        use super::crossed;
        use super::former_tag;
        use super::member_tag;
        use super::model_tag;

        let empty = span(ByteOffset::from(0_usize), ByteOffset::from(0_usize));
        let boundaries = [
            FragmentBoundary::Reserved,
            FragmentBoundary::Unadmitted,
            FragmentBoundary::Arity(OperandCount::from(3_usize)),
        ]
        .into_iter()
        .chain(crossed());
        let mut minted: alloc::vec::Vec<RefusalName> = alloc::vec::Vec::new();
        for boundary in boundaries {
            for &kind in TREE_SITTER_NAMED_KINDS.iter().chain(PBG_ONLY_KINDS) {
                for sort in SORTS {
                    minted.push(
                        Refusal::Lowering(LoweringRefusal::OutOfFragment {
                            span: empty,
                            form: FormName::from(NamedKind(kind)),
                            sort,
                            boundary,
                        })
                        .name(),
                    );
                }
            }
        }
        let closed: alloc::collections::BTreeSet<RefusalName> =
            RefusalName::closed().into_iter().collect();
        let families = FORMERS
            .map(|former| RefusalName::OutOfFragment(Qualifier::Named(former_tag(former))))
            .into_iter()
            .chain(MODEL_FAULTS.map(|fault| RefusalName::UnstatedComponent(model_tag(fault))))
            .chain(MEMBER_FAULTS.map(|fault| RefusalName::UndescribedMember(member_tag(fault))))
            .chain(
                crossed()
                    .into_iter()
                    .map(boundary_tag)
                    .chain([RUN_TARGET])
                    .map(|tag| RefusalName::OutOfFragment(Qualifier::Named(tag))),
            );
        for name in families {
            assert!(closed.contains(&name), "the closed names hold {name}");
        }
        minted.extend(RefusalName::closed());
        let literals: alloc::vec::Vec<StringLiteral> = minted
            .iter()
            .map(|name| StringLiteral::new(name.to_string()))
            .collect();
        for (name, literal) in minted.iter().zip(&literals) {
            assert_eq!(
                RefusalName::named_by(literal),
                Maybe::Present(*name),
                "`{}` names {name:?}",
                literal.as_ref()
            );
        }
        for text in [
            "OutOfFragment.projection_expression",
            "OutOfFragment.instantiation_expression.value",
            "OutOfFragment.grade.declaration",
            "OutOfFragment.operator_declaration",
            "OutOfFragment.WrongSort.declaration",
            "OutOfFragment.WrongSort",
            "OutOfFragment.Arity",
            "OutOfFragment.Endpoint",
            "OutOfFragment.Perform",
            "UnstatedComponent.ManyOut",
            "UndescribedMember.HigherCell",
        ] {
            assert!(
                literals.iter().any(|literal| literal.as_ref() == text),
                "a producer mints `{text}`"
            );
        }
    }
}
