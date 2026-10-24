//! What the primary locus of a refusal is: the label its underline carries.
//!
//! # The label says what the bytes are, not whose fact the refusal is
//!
//! A report's title already names the refusal and its class sorts it, so the
//! underline spends its space on the locus itself: the name nothing binds, the
//! term whose type does not convert, the closer the source never wrote. Two
//! refusals of one class at two different kinds of locus therefore carry two
//! different labels.
//!
//! The title names the refusal and the class sorts it, so the primary label
//! spends the underline on the bytes themselves: `not found in this scope`
//! under a name nothing binds, `its type does not convert` under a mismatched
//! term, `missing }` where a closer was never written. `Culprit` holds one
//! label per refusal variant, chosen by an exhaustive match, so a new refusal
//! cannot render until it says what its locus is. `Report::label` exposes the
//! primary label as a `PrimaryLabel` and `Report::note` the declaration note,
//! so a face that lays out its own message — the language server's — composes
//! the same parts the terminal prints.
//!
//! The alternative was the failure class as the label, which repeats what the
//! title already sorted and gives every malformed-source refusal one underline
//! whatever its cause. Reversal: when refusals carry their own per-site labels,
//! the table gives way to them.
//!
//! # A label names the types its refusal compares
//!
//! A checker refusal that sets a type against another — a type, sort, level or
//! family-argument mismatch — or meets a type of the wrong shape names those
//! types as nodes, and a type the checker synthesised has no origin to mark.
//! The primary label therefore carries them after its text: ``its type does not
//! convert: expected `Integer`, found `String` ``, ``its type is not of the
//! required shape: found `Integer` ``. The types are the ones the dispatcher
//! spelled at the judgement, through the printer the REPL and the language
//! server's hover share, and `Report::comparison` exposes them as a
//! `Comparison` of an expected and a found side, each absent when the refusal
//! names no type there or none could be spelled on one line. A refusal that
//! compares nothing keeps its label as it was.
//!
//! The alternatives were a note after the snippet, which the reader meets after
//! the underline it explains, and the types in the title, which the checker's
//! `Display` words without the spellings. Each nested reason (the `locus`
//! module) spells the type its own judgement was checked against, so the
//! primary label keeps only the failing comparison. Reversal: a type whose
//! spelling needs more than one line, left unspelled, moves to a note under the
//! snippet.

use core::fmt;

use anodized::spec;
use gandr_core_checker::CheckRefusal;
use gandr_core_checker::CheckingForm;
use gandr_core_checker::Mismatch;
use gandr_core_checker::RunFault;
use gandr_core_checker::access::AccessDefect;
use gandr_core_checker::codata::CodataFault;
use gandr_core_checker::session::LinearityDefect;
use gandr_core_checker::session::ProtocolDefect;
use gandr_core_checker::ua::StratumDefect;
use gandr_core_checker::ua::UaDefect;
use gandr_core_checker::worlds::LocatedDefect;
use gandr_surface_corpus::CorpusRefusal;
use gandr_surface_corpus::Refusal;
use gandr_surface_lowering::Ending;
use gandr_surface_lowering::FormFault;
use gandr_surface_lowering::FragmentBoundary;
use gandr_surface_lowering::LoweringRefusal;
use gandr_surface_lowering::Repair;
use gandr_surface_syntax::ClosingClass;
use gandr_surface_syntax::GroutShape;

/// What the bytes a refusal's primary locus covers are, as its underline
/// says it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Culprit(&'static str);

impl Culprit
{
    /// The label of the primary locus of `refusal`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a nonempty, single-line label naming what the refused bytes
    ///   are, chosen by the refusal's variant and, for a malformed form or a
    ///   form outside the fragment, by the fault or boundary it carries; never
    ///   the refusal's failure class.
    /// - provides: the primary label of every refusal report.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a type mismatch and an unresolved type head, both
    ///   malformed source, render different labels, and neither is the class;
    ///   each repair a malformed form carries renders its own label. Other
    ///   variants' wording is not pinned.
    /// - witness: `tests::diagnostics::refusals_of_one_class_label_what_their_locus_is`
    /// - witness: `culprit::tests::every_repair_labels_what_is_missing`
    #[spec(ensures: |ret| !ret.0.is_empty() && !ret.0.contains(['\r', '\n']))]
    #[inline]
    #[must_use]
    pub fn of(refusal: Refusal<'_>) -> Self
    {
        match refusal {
            Refusal::Lowering(lowering) => lowered(lowering),
            Refusal::Corpus(CorpusRefusal::ExpectationOutsideFixtureRoot { .. }) => {
                Self("an expectation the strict root refuses")
            },
            Refusal::Checking(checking) => checked(checking),
        }
    }
}

impl fmt::Display for Culprit
{
    /// Writes the label.
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

/// The label of a lowering refusal's primary locus.
///
/// # Specification
/// trivial.
const fn lowered(refusal: LoweringRefusal<'_>) -> Culprit
{
    Culprit(match refusal {
        LoweringRefusal::UnresolvedName { .. } => "not found in this scope",
        LoweringRefusal::UnresolvedDocLink { .. } => "links to no declared name",
        LoweringRefusal::UnresolvedTypeHead { .. } => "no type head of this name and arity",
        LoweringRefusal::DuplicateSignature { .. }
        | LoweringRefusal::DuplicateDefinition { .. }
        | LoweringRefusal::DuplicateImportAlias { .. }
        | LoweringRefusal::DuplicateAttribute { .. } => "written again here",
        LoweringRefusal::ShadowedBuiltin { .. } => "shadows a builtin",
        LoweringRefusal::ImportUnresolved { .. } => "names no source this root holds",
        LoweringRefusal::ImportCycle { .. } => "leads back to this source",
        LoweringRefusal::ImportShadows { .. } => "bound here and by an import",
        LoweringRefusal::UnexportedName { .. } => "declared without a definition",
        LoweringRefusal::OutOfFragment { boundary, .. } => match boundary {
            FragmentBoundary::Reserved(_) => "a reserved form",
            FragmentBoundary::Unadmitted(_) => "a form the fragment does not admit",
            FragmentBoundary::Misplaced => "a form admitted only as a theory's sort member",
            FragmentBoundary::NotAtResult => "a row admitted only at a definition's result",
            FragmentBoundary::WrongSort => "a form of another sort than this position takes",
            FragmentBoundary::Arity(_) => "the wrong number of operands",
            FragmentBoundary::Indexed => "a family applied to an index",
            FragmentBoundary::Unannotated => "needs a stated type",
            FragmentBoundary::NonUniform => "not the parameter itself",
            FragmentBoundary::ForeignClaim => "not the recursive function this claim is in",
            FragmentBoundary::NotAFunction => "a constructor, not a function",
            FragmentBoundary::NotInTail => "not on a path through a body",
            FragmentBoundary::JoinsBlock => "an answer the arms do not give",
            FragmentBoundary::EmptyList => "an empty list, not the unit",
            FragmentBoundary::Endpoint => "not an endpoint a fork or a receive binds",
            FragmentBoundary::NonContractive => "recurses before any action",
            FragmentBoundary::Held => "not a value a hold holds",
            FragmentBoundary::View => "not a view an access binds",
        },
        LoweringRefusal::BareFeedback { .. } => "fed back, and read under no observation",
        LoweringRefusal::IllFormedDescription { .. } => "what the description check refuses",
        LoweringRefusal::GradedBridge { .. } => "a grade other than `ω`",
        LoweringRefusal::MalformedLiteral { .. } => "not this literal's lexeme",
        LoweringRefusal::MalformedForm { fault, .. } => match fault {
            FormFault::Repaired(Repair::Grout(GroutShape::Convex)) => "a term is missing here",
            FormFault::Repaired(Repair::Grout(GroutShape::Prefix | GroutShape::Postfix))
            | FormFault::MissingOperand => "an operand is missing here",
            FormFault::Repaired(Repair::Grout(GroutShape::Infix)) => "an operator is missing here",
            FormFault::Repaired(Repair::Keyword(_)) => "a keyword where a term belongs",
            FormFault::Repaired(Repair::GhostClose(ClosingClass::Paren)) => "missing `)`",
            FormFault::Repaired(Repair::GhostClose(ClosingClass::Bracket)) => "missing `]`",
            FormFault::Repaired(Repair::GhostClose(ClosingClass::Brace)) => "missing `}`",
            FormFault::Repaired(Repair::Unended(Ending::Tile(_))) => {
                "its closing tile belongs here"
            },
            FormFault::Repaired(Repair::Unended(Ending::Unnamed)) => "the form stops here",
            FormFault::Repaired(Repair::Diverged(Ending::Tile(_))) => {
                "a tile of the form belongs here"
            },
            FormFault::Repaired(Repair::Diverged(Ending::Unnamed)) => {
                "the form leaves its shape here"
            },
            FormFault::ExtraOperand => "an operand the form does not take",
            FormFault::MisplacedTile => "out of place",
            FormFault::ExtraClose(ClosingClass::Paren) => "one `)` too many",
            FormFault::ExtraClose(ClosingClass::Bracket) => "one `]` too many",
            FormFault::ExtraClose(ClosingClass::Brace) => "one `}` too many",
            FormFault::ExtraOpen(ClosingClass::Paren) => "one `(` too many",
            FormFault::ExtraOpen(ClosingClass::Bracket) => "one `[` too many",
            FormFault::ExtraOpen(ClosingClass::Brace) => "one `{` too many",
            FormFault::MissingOpen(ClosingClass::Paren) => "missing `(`",
            FormFault::MissingOpen(ClosingClass::Bracket) => "missing `[`",
            FormFault::MissingOpen(ClosingClass::Brace) => "missing `{`",
        },
        LoweringRefusal::UnknownAttribute { .. } => "unknown attribute",
        LoweringRefusal::MissingPayload { .. } => "takes a payload",
        LoweringRefusal::NonValuePayload { .. } => "a payload that is not a value",
        LoweringRefusal::IllTypedPayload { .. } => "a payload of another schema",
        LoweringRefusal::ForwardMemberReference { .. } => "named before it is declared",
        LoweringRefusal::PhaseDependence { .. } => "a value a type depends on",
        LoweringRefusal::UnknownMember { .. } => "no member of this name",
        LoweringRefusal::UnprovenLaw { .. } => "a law this module does not prove",
        LoweringRefusal::PartialField { .. } => "a field some constructor lacks",
        LoweringRefusal::NotAFunctor { .. } => "not a functor",
        LoweringRefusal::ProjectionFromApplication { .. } => {
            "an application read before it is bound"
        },
        LoweringRefusal::UnreadAscription { .. } => "not read by the fragment yet",
        LoweringRefusal::UnstatedComponent { .. } => "the signature this model derives",
        LoweringRefusal::UndescribedMember { .. } => "a member the description does not read",
        LoweringRefusal::FamilyTelescope { .. } => "parameters its kind does not state",
        LoweringRefusal::LowercaseModuleName { .. } => "a lowercase initial",
        LoweringRefusal::ImplicitTelescope { .. } => "an implicit out of shape",
        LoweringRefusal::TelescopeCycle { .. } => "parameters mentioning each other",
        LoweringRefusal::ImplicitUnsupplied { .. } => "an implicit left unsupplied",
        LoweringRefusal::ImplicitInParentheses { .. } => "an implicit among the arguments",
        LoweringRefusal::ModelImplicitValue { .. } => "a model implicit as a value",
        LoweringRefusal::RegionAsValue { .. } => "a region named as a value",
        LoweringRefusal::EntryType { .. } => "an entry of another type",
        LoweringRefusal::StrayReceiverMode { .. } => "a mode off a receiver",
        LoweringRefusal::AmbiguousMethod { .. } => "a method of several modules",
        LoweringRefusal::ViewNotPlace { .. } => "no place of the receiver",
        LoweringRefusal::ViewOfNoPlace { .. } => "a call answering no place",
        LoweringRefusal::NonExhaustiveMatch { .. } => "some value matches no arm",
        LoweringRefusal::MismatchedPattern { .. } => "a pattern of another type",
        LoweringRefusal::UnmarkedSelfReference { .. } => "recursion without a claim",
        LoweringRefusal::UnguardedCorecursion { .. } => "not the whole arm of a copattern",
        LoweringRefusal::DescentOnSeveralParameters { .. } => "descends on another parameter",
        LoweringRefusal::Unreachable { .. } => "no path reaches this",
        LoweringRefusal::OutsideLoop { .. } => "no loop to leave",
        LoweringRefusal::AcrossHandler { .. } => "an exit across a live handler",
        LoweringRefusal::WithoutK { .. } => "a path matched against reflexivity",
        LoweringRefusal::DirectedCell { .. } => "a directed cell between terms",
        LoweringRefusal::CellNotALoop { .. } => "a cell between two distinct terms",
        LoweringRefusal::RulesUnoriented { .. } => "a rule that may not end",
        LoweringRefusal::RulesNonLinear { .. } => "a rule matching one variable twice",
        LoweringRefusal::RulesDiverge { .. } => "rewrites a term to another constructor term",
        LoweringRefusal::RulesOverlapSecondOrder { .. } => "parts from a rule that substitutes",
        LoweringRefusal::RulesOverlapCondition { .. } => {
            "overlaps a rule firing on a freshness condition"
        },
        LoweringRefusal::RulesUncompleted { .. } => "rewrites a term two ways no rule joins",
        LoweringRefusal::RulesNeverComplete { .. } => "rules whose completion never ends",
        LoweringRefusal::RulesUndecided { .. } => "a pair the check's budget left undecided",
        LoweringRefusal::UnderivedRule { .. } => "a rule its theory does not derive",
        LoweringRefusal::GenericMisplaced { .. } => "a generic program read off its place",
        LoweringRefusal::GenericUncovered { .. } => "a type with no derived equality",
        LoweringRefusal::BudgetExceeded { .. } => "the lowering's allowance ran out",
        LoweringRefusal::GrammarMismatch { .. } => "molded under another grammar",
        LoweringRefusal::UnknownMold { .. } => "a mold the grammar does not hold",
        LoweringRefusal::Unminted { .. } => "a declaration the lowering dropped",
    })
}

/// The label of a checker refusal's primary locus.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a nonempty, single-line label naming what the refused bytes are,
///   chosen by the refusal's variant and, where it carries a defect, a fault or
///   the form it could not synthesise, by that.
/// - provides: [`Culprit::of`] for a checker refusal.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a type mismatch renders its own label, neither empty nor
///   its failure class. Other variants' wording is not pinned.
/// - witness: `tests::diagnostics::refusals_of_one_class_label_what_their_locus_is`
#[spec(ensures: |ret| !ret.0.is_empty())]
const fn checked(refusal: CheckRefusal) -> Culprit
{
    Culprit(match refusal {
        CheckRefusal::NotADataType(_) => "not an admitted datatype",
        CheckRefusal::DataKindNotUniverse(_) | CheckRefusal::AbstractKindNotUniverse(_) => {
            "not a value universe"
        },
        CheckRefusal::DataFieldLevel { .. } => "above the declared universe",
        CheckRefusal::RuleNotPresentable { .. } => "rules that do not present the datatype",
        CheckRefusal::RuleNotRespected { .. } => "a case its datatype's rules do not admit",
        CheckRefusal::NotApart { .. } => "a path whose endpoints are not apart",
        CheckRefusal::LoopNotRespected { .. } => "a case its sort's loops do not admit",
        CheckRefusal::LoopUndecided { .. } => "a case whose loop obligation ran past its budget",
        CheckRefusal::RepresentationAboveKind { .. } => "above the abstract type's universe",
        CheckRefusal::NotAnAbstractType(_) => "not an abstract type",
        CheckRefusal::AtomTransport { .. } => "an identity of an atom stating no transport law",
        CheckRefusal::SealSiteRepeated(_) => "a component sealed twice",
        CheckRefusal::DataArgumentArity(_) => "the wrong number of parameters",
        CheckRefusal::UnknownConstructor { .. } => "no constructor of the datatype",
        CheckRefusal::ConstructorArity(_) => "the wrong number of fields",
        CheckRefusal::NonExhaustiveDataCase(_) => "not every constructor once",
        CheckRefusal::UndecidedCoverage(_) => "an arm left to a pattern hole",
        CheckRefusal::AbsentRecordField(_) => "no field of the record type",
        CheckRefusal::AbsentTupleComponent(_) => "no component of the product type",
        CheckRefusal::MissingRecordField { .. } => "a required field is missing",
        CheckRefusal::UnknownOperation { .. } => "not an operation of the interface",
        CheckRefusal::HandlerCoverage { .. } => "not every operation once",
        CheckRefusal::ShiftWithoutReset { .. } => "no enclosing reset",
        CheckRefusal::DependentStack { .. } => "its result type mentions the discharged value",
        CheckRefusal::EffectSignatureConflict { .. } => "effect rows that disagree",
        CheckRefusal::PathCode(_) => "not a quoted closed first-order code",
        CheckRefusal::EndpointMismatch { .. } => "not both endpoints of the path",
        CheckRefusal::CompoundEndpoint { .. } => "an endpoint that returns no pure value",
        CheckRefusal::FunextUnsupported { .. } => "functions past the first-order boundary",
        CheckRefusal::PointwiseDistinct { .. } => "functions that differ at some input",
        CheckRefusal::EquivUnsupported { .. } => "translators outside the rule's fragment",
        CheckRefusal::UncertifiedStratum { .. } => "a list cell its round trip does not return",
        CheckRefusal::RoundTripDistinct { .. } => "translators that are not inverse",
        CheckRefusal::NotOver { .. } => "an identity not over the path",
        CheckRefusal::UaUncertified { stratum, .. } => match stratum {
            StratumDefect::Degree { .. } => "a degree no shape of the catalogue reaches",
            StratumDefect::Condition { .. } => "a catalogue failing the corolla or Segal condition",
            StratumDefect::Allowance { .. } => "a catalogue past the checker's allowance",
        },
        CheckRefusal::UaInequivalent { defect, .. } => match defect {
            UaDefect::UnknownGenerator { .. } => "no generator of the description",
            UaDefect::PastTheBound { .. } => "a generator past the catalogue's bound",
            UaDefect::Cardinality { .. } => "species of different sizes at a corolla",
            UaDefect::Tables { .. } => "a corolla translated other than once",
            UaDefect::NotInverse { .. } => "translators that are not inverse",
            UaDefect::NotNatural { .. } => "translators that break the corolla's symmetry",
            UaDefect::Stuck { .. } => "a translator that returns no element",
        },
        CheckRefusal::UnenclosedRun { .. } => "a run with no computation to run before",
        CheckRefusal::ImplicitUnsolved { .. } => "an implicit left unsolved",
        CheckRefusal::ModelUnanswered { .. } => "a model implicit no module answers",
        CheckRefusal::ModelAmbiguous { .. } => "a model implicit more than one module answers",
        CheckRefusal::TypeMismatch(Mismatch::Value { .. } | Mismatch::Computation { .. }) => {
            "its type does not convert"
        },
        CheckRefusal::ShapeMismatch { .. } => "its type is not of the required shape",
        CheckRefusal::NotSynthesisable {
            form: CheckingForm::Hole(_),
        } => "an unfilled hole",
        CheckRefusal::NotSynthesisable { .. } => "needs a type to be checked against",
        CheckRefusal::UnknownConstant { .. } => "no declaration with a type",
        CheckRefusal::OutOfFragment { .. } => "no rule for this former",
        CheckRefusal::UnboundIndex { .. } => "an unbound variable",
        CheckRefusal::BudgetExceeded { .. } => "the judgement's allowance ran out",
        CheckRefusal::DanglingNode { .. } => "a node the arena does not hold",
        CheckRefusal::AdmissionOrder { .. } => "admitted out of order",
        CheckRefusal::MachineInvariant => "the checking machine disagreed with itself",
        CheckRefusal::SortMismatch { .. } => "a universe of the other sort",
        CheckRefusal::LevelMismatch { .. } => "a universe at a level not admitted",
        CheckRefusal::DependentBind { .. } => "its type mentions the bound value",
        CheckRefusal::Undecided { .. } => "an unfolding not certified",
        CheckRefusal::FamilyArity { .. } => "the wrong number of arguments",
        CheckRefusal::FamilyArgumentClassifier { .. } => "outside its parameter's domain",
        CheckRefusal::StaticLambdaArgument { .. } => "a type operator where a value is needed",
        CheckRefusal::StaticClassifierExpected { .. } => "a type that classifies no codes",
        CheckRefusal::NegativeOccurrence(_) => {
            "the declared type under a function's domain, where no stage reaches it"
        },
        CheckRefusal::NestedOccurrence(_) => {
            "the declared type inside another former, at a place it does not hold strictly positively"
        },
        CheckRefusal::IndexOccurrence(_) => "the declared type inside an index",
        CheckRefusal::NonUniformOccurrence(_) => "the declared type at other arguments",
        CheckRefusal::CrossBlockReference { .. } => "names a later declaration",
        CheckRefusal::StageNotBelow { .. } => "not below the stage its recursion wants",
        CheckRefusal::StagesDisagree { .. } => "a stage the call's earlier arguments exclude",
        CheckRefusal::SessionMismatch { defect, .. } => match defect {
            ProtocolDefect::Action { .. } => "an action the endpoint's state does not admit",
            ProtocolDefect::Label => "a label the endpoint's state does not offer",
            ProtocolDefect::Arms => "not every offered label once",
        },
        CheckRefusal::Linearity { defect, .. } => match defect {
            LinearityDefect::Residue { .. } => "an endpoint left unconsumed",
            LinearityDefect::Closed { .. } => "an endpoint already closed",
            LinearityDefect::UsedTwice { .. } => "an endpoint used twice in one action",
            LinearityDefect::Captured { .. } => "an endpoint that may be used other than once",
            LinearityDefect::AsValue { .. } => "an endpoint read as a value",
            LinearityDefect::ArmsDisagree { .. } => "an arm that leaves the endpoints otherwise",
            LinearityDefect::Unrestricted => "an endpoint outside a fork or a receive",
            LinearityDefect::Unbound { .. } => "no endpoint bound here",
            LinearityDefect::BufferUnreturned { .. } => "a buffer never handed back",
            LinearityDefect::BufferReturnedTwice { .. } => "a buffer already handed back",
            LinearityDefect::BufferRead { .. } => "a buffer read other than by its return",
            LinearityDefect::ContinuationUnspent { .. } => {
                "a continuation never resumed or abandoned"
            },
            LinearityDefect::ContinuationUsedTwice { .. } => "a continuation already ended",
            LinearityDefect::ContinuationCaptured { .. } => {
                "a continuation that may be ended other than once"
            },
            LinearityDefect::ContinuationAsValue { .. } => "a continuation read as a value",
        },
        CheckRefusal::Access { defect, .. } => match defect {
            AccessDefect::NotHeld => "no held value here",
            AccessDefect::Lent => "a held value lent to an access",
            AccessDefect::HeldCaptured { .. } => "a held value that may be held other than once",
            AccessDefect::Escaped { .. } => "a view outliving its access",
            AccessDefect::Unended => "a view neither resumed nor aborted",
            AccessDefect::Spent => "a view already ended",
            AccessDefect::NotAView => "no view here",
            AccessDefect::ReadOnly => "a shared view, which is read-only",
            AccessDefect::UnwindEffect => "an effect in an unwind",
            AccessDefect::Unindexed => "a held value with no elements to index",
            AccessDefect::HeldShared => "a value that may have another holder",
            AccessDefect::HeldCopied => "a copy of a value held at grade one",
            AccessDefect::Moved => "an abort after the value was moved out",
            AccessDefect::Kept => "a write to a value a live region keeps a view of",
            AccessDefect::KeptEscaped => "a value kept in the scope's own region",
            AccessDefect::Consumed => "a held value a consumed receiver already took",
        },
        CheckRefusal::Codata { fault, .. } => match fault {
            CodataFault::Undeclared => "no codata declaration here",
            CodataFault::KindNotUniverse => "a codata kind that is no computation universe",
            CodataFault::WithoutObservations => "a codata declaration with no observation",
            CodataFault::Occurrence => "the codata type named off an observation's result",
            CodataFault::ObservationLevel => "an observation above the declared universe",
            CodataFault::Arity => "a codata type at another arity than its declaration",
        },
        CheckRefusal::Located { defect, .. } => match defect {
            LocatedDefect::Immobile { .. } => "a value whose type does not cross",
            LocatedDefect::CapabilityMissing { .. } => "no capability for the world",
            LocatedDefect::CapabilityCaptured { .. } => "a migration that may run other than once",
            LocatedDefect::Elsewhere { .. } => "a value bound at another world",
            LocatedDefect::HoldElsewhere { .. } => "a hold wanted at another world",
            LocatedDefect::Unlocated => "a handle made or opened at the host's own world",
            LocatedDefect::UndeclaredWorld { .. } => "no world declaration",
            LocatedDefect::HostWorldUndeclared => "a world the source does not declare",
            LocatedDefect::MarkUnfounded { .. } => "a representation that does not cross",
            LocatedDefect::EntryNamed { .. } => "an entry named from another declaration",
            LocatedDefect::EntryUngranted { .. } => "an entry the host did not grant",
            LocatedDefect::NotAHandle { .. } => "not a handle at a world",
        },
        CheckRefusal::CapabilityForged { .. } => "no capability hypothesis",
        CheckRefusal::CapabilityAmplified(_) => "a capability granting less",
        CheckRefusal::CapabilityOutsideAuthority { .. } => "an operation its capability withholds",
        CheckRefusal::CapabilityEscaped { .. } => "a capability outliving its scope",
        CheckRefusal::CapabilityConsumable(_) => "a consumable capability",
        CheckRefusal::OpenSessionPayload { .. } => "a session payload open over a binder",
        CheckRefusal::CapabilityUngranted { .. } => "authority the host did not grant",
        CheckRefusal::SessionNotEquivalent { .. } => "protocols that are not bisimilar",
        CheckRefusal::SessionNotSubtype { .. } => "a protocol that does not simulate the target",
        CheckRefusal::SessionCodeExpected { .. } => "not a session code",
        CheckRefusal::NonCovariantMotive { .. } => "the moving endpoint other than covariantly",
        CheckRefusal::RideUnsupported { .. } => "a motive the ride cannot move",
        CheckRefusal::RunNotAdmitted { fault, .. } => match fault {
            RunFault::WrongDirection(_) => "a move in the other direction",
            RunFault::WrongLabel(_) => "a label the protocol does not admit here",
            RunFault::ResumeAfterEnd(_) => "a move after the run closed",
            RunFault::Incomplete(_) => "a run that stops before the protocol ends",
            RunFault::OfferNarrowed => "a run that may take an offer the target drops",
        },
        CheckRefusal::DialogueUnmatched { .. } => "a move the other endpoint does not match",
        CheckRefusal::DialogueInverted { .. } => "a move logged before the move it follows",
        CheckRefusal::ForwardUnsupported { .. } => "a translator the rule cannot image",
        CheckRefusal::Boundary { .. } => "a boundary flow running against its variance",
    })
}

/// The labels of malformed forms.
#[cfg(test)]
mod tests
{
    use gandr_surface_corpus::Refusal;
    use gandr_surface_lowering::AscriptionForm;
    use gandr_surface_lowering::AttributeSchema;
    use gandr_surface_lowering::CandidateCount;
    use gandr_surface_lowering::CrossedExit;
    use gandr_surface_lowering::Ending;
    use gandr_surface_lowering::FormFault;
    use gandr_surface_lowering::FormName;
    use gandr_surface_lowering::FragmentBoundary;
    use gandr_surface_lowering::FragmentSort;
    use gandr_surface_lowering::HeadArity;
    use gandr_surface_lowering::LoopExit;
    use gandr_surface_lowering::LoweringBudget;
    use gandr_surface_lowering::LoweringRefusal;
    use gandr_surface_lowering::Offer;
    use gandr_surface_lowering::OperandCount;
    use gandr_surface_lowering::PayloadForm;
    use gandr_surface_lowering::RegisteredAttribute;
    use gandr_surface_lowering::Repair;
    use gandr_surface_lowering::StrayKeyword;
    use gandr_surface_lowering::SurfaceName;
    use gandr_surface_lowering::TelescopeFault;
    use gandr_surface_lowering::TileName;
    use gandr_surface_lowering::Unbuilt;
    use gandr_surface_lowering::model::ModelFault;
    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::ByteSpan;
    use gandr_surface_syntax::ClosingClass;
    use gandr_surface_syntax::GrammarFingerprint;
    use gandr_surface_syntax::GroutShape;
    use gandr_surface_syntax::MoldId;

    use super::Culprit;

    #[test]
    fn every_repair_labels_what_is_missing()
    {
        let at = ByteSpan::new(ByteOffset::from(3_usize), ByteOffset::from(3_usize))
            .expect("an empty span is ordered");
        let mut labels: Vec<String> = [
            Repair::Grout(GroutShape::Convex),
            Repair::Grout(GroutShape::Postfix),
            Repair::Grout(GroutShape::Infix),
            Repair::GhostClose(ClosingClass::Paren),
            Repair::GhostClose(ClosingClass::Bracket),
            Repair::GhostClose(ClosingClass::Brace),
            Repair::Unended(Ending::Tile(TileName::SEMICOLON)),
            Repair::Unended(Ending::Unnamed),
            Repair::Diverged(Ending::Tile(TileName::SEMICOLON)),
            Repair::Diverged(Ending::Unnamed),
            Repair::Keyword(StrayKeyword {
                written: TileName::SEMICOLON,
                offer: Offer::Unspelled,
            }),
        ]
        .into_iter()
        .map(|repair| {
            Culprit::of(Refusal::Lowering(LoweringRefusal::MalformedForm {
                span: at,
                form: FormName::DECLARATION,
                fault: FormFault::Repaired(repair),
            }))
            .to_string()
        })
        .collect();
        labels.sort_unstable();
        labels.dedup();
        assert_eq!(
            labels.len(),
            11_usize,
            "each repair names what the source left out"
        );
    }

    /// The label of a lowering refusal's primary locus, as the witness reads
    /// it: the match mirrors `lowered`'s arms one for one, so a label that
    /// changes in `lowered` changes here too and the witness fails.
    ///
    /// # Specification
    /// trivial.
    const fn label(refusal: LoweringRefusal<'_>) -> Culprit
    {
        Culprit(match refusal {
            LoweringRefusal::UnresolvedName { .. } => "not found in this scope",
            LoweringRefusal::UnresolvedDocLink { .. } => "links to no declared name",
            LoweringRefusal::UnresolvedTypeHead { .. } => "no type head of this name and arity",
            LoweringRefusal::DuplicateSignature { .. }
            | LoweringRefusal::DuplicateDefinition { .. }
            | LoweringRefusal::DuplicateImportAlias { .. }
            | LoweringRefusal::DuplicateAttribute { .. } => "written again here",
            LoweringRefusal::ShadowedBuiltin { .. } => "shadows a builtin",
            LoweringRefusal::ImportUnresolved { .. } => "names no source this root holds",
            LoweringRefusal::ImportCycle { .. } => "leads back to this source",
            LoweringRefusal::ImportShadows { .. } => "bound here and by an import",
            LoweringRefusal::UnexportedName { .. } => "declared without a definition",
            LoweringRefusal::OutOfFragment { boundary, .. } => match boundary {
                FragmentBoundary::Reserved(_) => "a reserved form",
                FragmentBoundary::Unadmitted(_) => "a form the fragment does not admit",
                FragmentBoundary::Misplaced => "a form admitted only as a theory's sort member",
                FragmentBoundary::NotAtResult => "a row admitted only at a definition's result",
                FragmentBoundary::WrongSort => "a form of another sort than this position takes",
                FragmentBoundary::Arity(_) => "the wrong number of operands",
                FragmentBoundary::Indexed => "a family applied to an index",
                FragmentBoundary::Unannotated => "needs a stated type",
                FragmentBoundary::NonUniform => "not the parameter itself",
                FragmentBoundary::ForeignClaim => "not the recursive function this claim is in",
                FragmentBoundary::NotAFunction => "a constructor, not a function",
                FragmentBoundary::NotInTail => "not on a path through a body",
                FragmentBoundary::JoinsBlock => "an answer the arms do not give",
                FragmentBoundary::EmptyList => "an empty list, not the unit",
                FragmentBoundary::Endpoint => "not an endpoint a fork or a receive binds",
                FragmentBoundary::NonContractive => "recurses before any action",
                FragmentBoundary::Held => "not a value a hold holds",
                FragmentBoundary::View => "not a view an access binds",
            },
            LoweringRefusal::BareFeedback { .. } => "fed back, and read under no observation",
            LoweringRefusal::IllFormedDescription { .. } => "what the description check refuses",
            LoweringRefusal::GradedBridge { .. } => "a grade other than `ω`",
            LoweringRefusal::MalformedLiteral { .. } => "not this literal's lexeme",
            LoweringRefusal::MalformedForm { fault, .. } => match fault {
                FormFault::Repaired(Repair::Grout(GroutShape::Convex)) => "a term is missing here",
                FormFault::Repaired(Repair::Grout(GroutShape::Prefix | GroutShape::Postfix))
                | FormFault::MissingOperand => "an operand is missing here",
                FormFault::Repaired(Repair::Grout(GroutShape::Infix)) => {
                    "an operator is missing here"
                },
                FormFault::Repaired(Repair::Keyword(_)) => "a keyword where a term belongs",
                FormFault::Repaired(Repair::GhostClose(ClosingClass::Paren)) => "missing `)`",
                FormFault::Repaired(Repair::GhostClose(ClosingClass::Bracket)) => "missing `]`",
                FormFault::Repaired(Repair::GhostClose(ClosingClass::Brace)) => "missing `}`",
                FormFault::Repaired(Repair::Unended(Ending::Tile(_))) => {
                    "its closing tile belongs here"
                },
                FormFault::Repaired(Repair::Unended(Ending::Unnamed)) => "the form stops here",
                FormFault::Repaired(Repair::Diverged(Ending::Tile(_))) => {
                    "a tile of the form belongs here"
                },
                FormFault::Repaired(Repair::Diverged(Ending::Unnamed)) => {
                    "the form leaves its shape here"
                },
                FormFault::ExtraOperand => "an operand the form does not take",
                FormFault::MisplacedTile => "out of place",
                FormFault::ExtraClose(ClosingClass::Paren) => "one `)` too many",
                FormFault::ExtraClose(ClosingClass::Bracket) => "one `]` too many",
                FormFault::ExtraClose(ClosingClass::Brace) => "one `}` too many",
                FormFault::ExtraOpen(ClosingClass::Paren) => "one `(` too many",
                FormFault::ExtraOpen(ClosingClass::Bracket) => "one `[` too many",
                FormFault::ExtraOpen(ClosingClass::Brace) => "one `{` too many",
                FormFault::MissingOpen(ClosingClass::Paren) => "missing `(`",
                FormFault::MissingOpen(ClosingClass::Bracket) => "missing `[`",
                FormFault::MissingOpen(ClosingClass::Brace) => "missing `{`",
            },
            LoweringRefusal::UnknownAttribute { .. } => "unknown attribute",
            LoweringRefusal::MissingPayload { .. } => "takes a payload",
            LoweringRefusal::NonValuePayload { .. } => "a payload that is not a value",
            LoweringRefusal::IllTypedPayload { .. } => "a payload of another schema",
            LoweringRefusal::ForwardMemberReference { .. } => "named before it is declared",
            LoweringRefusal::PhaseDependence { .. } => "a value a type depends on",
            LoweringRefusal::UnknownMember { .. } => "no member of this name",
            LoweringRefusal::UnprovenLaw { .. } => "a law this module does not prove",
            LoweringRefusal::PartialField { .. } => "a field some constructor lacks",
            LoweringRefusal::NotAFunctor { .. } => "not a functor",
            LoweringRefusal::ProjectionFromApplication { .. } => {
                "an application read before it is bound"
            },
            LoweringRefusal::UnreadAscription { .. } => "not read by the fragment yet",
            LoweringRefusal::UnstatedComponent { .. } => "the signature this model derives",
            LoweringRefusal::UndescribedMember { .. } => "a member the description does not read",
            LoweringRefusal::FamilyTelescope { .. } => "parameters its kind does not state",
            LoweringRefusal::LowercaseModuleName { .. } => "a lowercase initial",
            LoweringRefusal::ImplicitTelescope { .. } => "an implicit out of shape",
            LoweringRefusal::TelescopeCycle { .. } => "parameters mentioning each other",
            LoweringRefusal::ImplicitUnsupplied { .. } => "an implicit left unsupplied",
            LoweringRefusal::ImplicitInParentheses { .. } => "an implicit among the arguments",
            LoweringRefusal::ModelImplicitValue { .. } => "a model implicit as a value",
            LoweringRefusal::RegionAsValue { .. } => "a region named as a value",
            LoweringRefusal::EntryType { .. } => "an entry of another type",
            LoweringRefusal::StrayReceiverMode { .. } => "a mode off a receiver",
            LoweringRefusal::AmbiguousMethod { .. } => "a method of several modules",
            LoweringRefusal::ViewNotPlace { .. } => "no place of the receiver",
            LoweringRefusal::ViewOfNoPlace { .. } => "a call answering no place",
            LoweringRefusal::NonExhaustiveMatch { .. } => "some value matches no arm",
            LoweringRefusal::MismatchedPattern { .. } => "a pattern of another type",
            LoweringRefusal::UnmarkedSelfReference { .. } => "recursion without a claim",
            LoweringRefusal::UnguardedCorecursion { .. } => "not the whole arm of a copattern",
            LoweringRefusal::DescentOnSeveralParameters { .. } => "descends on another parameter",
            LoweringRefusal::Unreachable { .. } => "no path reaches this",
            LoweringRefusal::OutsideLoop { .. } => "no loop to leave",
            LoweringRefusal::AcrossHandler { .. } => "an exit across a live handler",
            LoweringRefusal::WithoutK { .. } => "a path matched against reflexivity",
            LoweringRefusal::DirectedCell { .. } => "a directed cell between terms",
            LoweringRefusal::CellNotALoop { .. } => "a cell between two distinct terms",
            LoweringRefusal::RulesUnoriented { .. } => "a rule that may not end",
            LoweringRefusal::RulesNonLinear { .. } => "a rule matching one variable twice",
            LoweringRefusal::RulesDiverge { .. } => "rewrites a term to another constructor term",
            LoweringRefusal::RulesOverlapSecondOrder { .. } => "parts from a rule that substitutes",
            LoweringRefusal::RulesOverlapCondition { .. } => {
                "overlaps a rule firing on a freshness condition"
            },
            LoweringRefusal::RulesUncompleted { .. } => "rewrites a term two ways no rule joins",
            LoweringRefusal::RulesNeverComplete { .. } => "rules whose completion never ends",
            LoweringRefusal::RulesUndecided { .. } => "a pair the check's budget left undecided",
            LoweringRefusal::UnderivedRule { .. } => "a rule its theory does not derive",
            LoweringRefusal::GenericMisplaced { .. } => "a generic program read off its place",
            LoweringRefusal::GenericUncovered { .. } => "a type with no derived equality",
            LoweringRefusal::BudgetExceeded { .. } => "the lowering's allowance ran out",
            LoweringRefusal::GrammarMismatch { .. } => "molded under another grammar",
            LoweringRefusal::UnknownMold { .. } => "a mold the grammar does not hold",
            LoweringRefusal::Unminted { .. } => "a declaration the lowering dropped",
        })
    }

    #[test]
    fn every_lowering_refusal_labels_what_its_bytes_are()
    {
        let at = ByteSpan::new(ByteOffset::from(3_usize), ByteOffset::from(3_usize))
            .expect("an empty span is ordered");
        let name = SurfaceName::from("name");
        let refusals = [
            LoweringRefusal::UnresolvedName { span: at, name },
            LoweringRefusal::UnresolvedDocLink { span: at, name },
            LoweringRefusal::UnresolvedTypeHead {
                span: at,
                name,
                arity: HeadArity::Nullary,
            },
            LoweringRefusal::DuplicateSignature {
                span: at,
                name,
                first: at,
            },
            LoweringRefusal::DuplicateDefinition {
                span: at,
                name,
                first: at,
            },
            LoweringRefusal::DuplicateImportAlias {
                span: at,
                alias: name,
                first: at,
            },
            LoweringRefusal::DuplicateAttribute {
                span: at,
                name,
                first: at,
            },
            LoweringRefusal::ShadowedBuiltin { span: at, name },
            LoweringRefusal::ImportUnresolved {
                span: at,
                refused: at,
            },
            LoweringRefusal::ImportCycle {
                span: at,
                refused: at,
            },
            LoweringRefusal::ImportShadows {
                span: at,
                name,
                import: at,
                other: at,
            },
            LoweringRefusal::UnexportedName {
                span: at,
                name,
                declared: at,
            },
            LoweringRefusal::OutOfFragment {
                span: at,
                form: FormName::DECLARATION,
                sort: FragmentSort::Value,
                boundary: FragmentBoundary::Reserved(Unbuilt::Dup),
            },
            LoweringRefusal::OutOfFragment {
                span: at,
                form: FormName::DECLARATION,
                sort: FragmentSort::Value,
                boundary: FragmentBoundary::Unadmitted(Unbuilt::Projection),
            },
            LoweringRefusal::OutOfFragment {
                span: at,
                form: FormName::DECLARATION,
                sort: FragmentSort::Value,
                boundary: FragmentBoundary::Misplaced,
            },
            LoweringRefusal::OutOfFragment {
                span: at,
                form: FormName::DECLARATION,
                sort: FragmentSort::Value,
                boundary: FragmentBoundary::WrongSort,
            },
            LoweringRefusal::OutOfFragment {
                span: at,
                form: FormName::DECLARATION,
                sort: FragmentSort::Value,
                boundary: FragmentBoundary::Arity(OperandCount::from(2_usize)),
            },
            LoweringRefusal::OutOfFragment {
                span: at,
                form: FormName::DECLARATION,
                sort: FragmentSort::Value,
                boundary: FragmentBoundary::Indexed,
            },
            LoweringRefusal::OutOfFragment {
                span: at,
                form: FormName::DECLARATION,
                sort: FragmentSort::Value,
                boundary: FragmentBoundary::Unannotated,
            },
            LoweringRefusal::OutOfFragment {
                span: at,
                form: FormName::DECLARATION,
                sort: FragmentSort::Value,
                boundary: FragmentBoundary::NonUniform,
            },
            LoweringRefusal::OutOfFragment {
                span: at,
                form: FormName::DECLARATION,
                sort: FragmentSort::Value,
                boundary: FragmentBoundary::NotAFunction,
            },
            LoweringRefusal::OutOfFragment {
                span: at,
                form: FormName::DECLARATION,
                sort: FragmentSort::Value,
                boundary: FragmentBoundary::NotInTail,
            },
            LoweringRefusal::OutOfFragment {
                span: at,
                form: FormName::DECLARATION,
                sort: FragmentSort::Value,
                boundary: FragmentBoundary::JoinsBlock,
            },
            LoweringRefusal::OutOfFragment {
                span: at,
                form: FormName::DECLARATION,
                sort: FragmentSort::Value,
                boundary: FragmentBoundary::EmptyList,
            },
            LoweringRefusal::OutOfFragment {
                span: at,
                form: FormName::DECLARATION,
                sort: FragmentSort::Value,
                boundary: FragmentBoundary::Endpoint,
            },
            LoweringRefusal::OutOfFragment {
                span: at,
                form: FormName::DECLARATION,
                sort: FragmentSort::Value,
                boundary: FragmentBoundary::NonContractive,
            },
            LoweringRefusal::OutOfFragment {
                span: at,
                form: FormName::DECLARATION,
                sort: FragmentSort::Value,
                boundary: FragmentBoundary::Held,
            },
            LoweringRefusal::OutOfFragment {
                span: at,
                form: FormName::DECLARATION,
                sort: FragmentSort::Value,
                boundary: FragmentBoundary::View,
            },
            LoweringRefusal::BareFeedback { span: at, rule: at },
            LoweringRefusal::IllFormedDescription {
                span: at,
                kind: gandr_surface_lowering::WfKind::DuplicateSortName,
                subjects: [
                    quenchant_shape::shape::Maybe::Present(name),
                    quenchant_shape::shape::Maybe::Absent(
                        gandr_surface_lowering::description_subject::Absent::Unnamed,
                    ),
                ],
            },
            LoweringRefusal::GradedBridge {
                span: at,
                grade: name,
            },
            LoweringRefusal::MalformedLiteral {
                span: at,
                form: FormName::DECLARATION,
            },
            LoweringRefusal::MalformedForm {
                span: at,
                form: FormName::DECLARATION,
                fault: FormFault::ExtraOperand,
            },
            LoweringRefusal::MalformedForm {
                span: at,
                form: FormName::DECLARATION,
                fault: FormFault::MisplacedTile,
            },
            LoweringRefusal::MissingPayload {
                span: at,
                name: RegisteredAttribute::DOC,
                expected: AttributeSchema::Marker,
            },
            LoweringRefusal::NonValuePayload {
                span: at,
                name: RegisteredAttribute::DOC,
                form: FormName::DECLARATION,
            },
            LoweringRefusal::IllTypedPayload {
                span: at,
                name: RegisteredAttribute::DOC,
                expected: AttributeSchema::Marker,
                written: PayloadForm::Integer,
            },
            LoweringRefusal::ForwardMemberReference {
                span: at,
                name,
                declared: at,
            },
            LoweringRefusal::PhaseDependence {
                span: at,
                member: name,
                reached: name,
            },
            LoweringRefusal::UnknownMember {
                span: at,
                module: name,
                member: name,
            },
            LoweringRefusal::PartialField {
                span: at,
                field: name,
                constructor: name,
            },
            LoweringRefusal::NotAFunctor { span: at, name },
            LoweringRefusal::ProjectionFromApplication {
                span: at,
                functor: name,
            },
            LoweringRefusal::UnreadAscription {
                span: at,
                name,
                form: AscriptionForm::Kinded,
            },
            LoweringRefusal::UnstatedComponent {
                span: at,
                name,
                fault: ModelFault::UnknownHead,
            },
            LoweringRefusal::FamilyTelescope {
                span: at,
                name,
                fault: TelescopeFault::Index(OperandCount::from(1_usize)),
            },
            LoweringRefusal::LowercaseModuleName { span: at, name },
            LoweringRefusal::ImplicitTelescope { span: at },
            LoweringRefusal::TelescopeCycle {
                span: at,
                first: name,
                second: name,
            },
            LoweringRefusal::ImplicitUnsupplied {
                span: at,
                function: name,
                implicit: name,
            },
            LoweringRefusal::ImplicitInParentheses {
                span: at,
                function: name,
                implicit: name,
            },
            LoweringRefusal::ModelImplicitValue {
                span: at,
                implicit: name,
            },
            LoweringRefusal::RegionAsValue { span: at, name },
            LoweringRefusal::EntryType { span: at },
            LoweringRefusal::StrayReceiverMode {
                span: at,
                mode: name,
            },
            LoweringRefusal::AmbiguousMethod {
                span: at,
                method: name,
                first: name,
                second: name,
                more: CandidateCount::from(0_usize),
            },
            LoweringRefusal::ViewNotPlace { span: at },
            LoweringRefusal::ViewOfNoPlace { span: at },
            LoweringRefusal::NonExhaustiveMatch { span: at },
            LoweringRefusal::MismatchedPattern {
                span: at,
                first: at,
            },
            LoweringRefusal::UnmarkedSelfReference { span: at, name },
            LoweringRefusal::UnguardedCorecursion { span: at, name },
            LoweringRefusal::DescentOnSeveralParameters {
                span: at,
                staged: name,
                claimed: name,
            },
            LoweringRefusal::Unreachable { span: at },
            LoweringRefusal::OutsideLoop {
                span: at,
                exit: LoopExit::Break,
            },
            LoweringRefusal::AcrossHandler {
                span: at,
                exit: CrossedExit::Become,
            },
            LoweringRefusal::WithoutK { span: at },
            LoweringRefusal::DirectedCell { span: at },
            LoweringRefusal::CellNotALoop { span: at },
            LoweringRefusal::RulesUnoriented { span: at },
            LoweringRefusal::RulesNonLinear { span: at, copy: at },
            LoweringRefusal::RulesDiverge {
                span: at,
                first: at,
            },
            LoweringRefusal::RulesUncompleted {
                span: at,
                first: at,
            },
            LoweringRefusal::RulesNeverComplete {
                span: at,
                first: at,
            },
            LoweringRefusal::RulesUndecided {
                span: at,
                first: at,
            },
            LoweringRefusal::UnderivedRule {
                span: at,
                rule: name,
                theory: name,
                fault: gandr_surface_lowering::derive::DeriveFault::Apart,
            },
            LoweringRefusal::BudgetExceeded {
                budget: LoweringBudget::from(1_usize),
            },
            LoweringRefusal::GrammarMismatch {
                tree: GrammarFingerprint::from(1_u64),
                grammar: GrammarFingerprint::from(2_u64),
            },
            LoweringRefusal::UnknownMold {
                span: at,
                mold: MoldId::from(1_u32),
            },
            LoweringRefusal::Unminted { span: at, name },
        ];
        for refusal in refusals {
            assert_eq!(
                Culprit::of(Refusal::Lowering(refusal)),
                label(refusal),
                "the label names what the bytes are"
            );
        }
    }
}
