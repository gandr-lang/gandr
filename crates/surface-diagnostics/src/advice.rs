//! What a reader does about a refusal: the third part of the procedural form.
//!
//! # A refusal reads as a procedure
//!
//! A diagnostic states what is wrong in its message, where in its primary
//! label, and what to do in its help: one imperative sentence, the technical
//! vocabulary unrestricted. [`advice`] writes the help, one arm per refusal
//! name, from the refusal alone. A face shows it as the diagnostic's `help:`
//! line. A refusal tracked by an issue already ends with the issue that tracks
//! it.
//!
//! A refusal whose name has no help yet is [`help::Absent::Unworded`]: the
//! names are worded most-seen first, ten at a time, and the prose check's
//! ledger holds each unworded golden until its name is worded.
//!
//! The alternative was a help slot on each producer's refusal, which would put
//! a reader's advice beside the producer's own wording, where no face reads
//! it. Reversal: a producer whose refusal alone cannot word the help, because
//! the advice needs a fact the diagnostic does not hold, moves that name's
//! help to the producer.
//!
//! # References
//!
//! - `vault:01a178aa-9a6d-7c20-a9c5-131d35beda06` — background: the
//!   directed-univalence design (§ The surface family) — `NotATranslation`'s
//!   help declares the flow its `via` names.
//! - `vault:01a178ab-289d-7702-b010-1c47ae9fd427` — background: the univalence
//!   design (§ The trust story) — that help names who supplies a translation:
//!   the importer, declaring the flow, or the source, publishing it.
//! - `vault:01a17f02-42f0-7920-bede-5615d3bade8c` — background: the compilation
//!   ruling (§ compilation-recipe-zero-cost) — a member a flow's codomain lacks
//!   is one declaration to write, as `SignatureMismatch.Missing`'s help says.

use alloc::format;
use alloc::string::String;

use gandr_core_checker::CheckRefusal;
use gandr_core_checker::EndpointMiss;
use gandr_core_checker::access::AccessDefect;
use gandr_core_checker::session::LinearityDefect;
use gandr_core_checker::worlds::Crossed;
use gandr_core_checker::worlds::LocatedDefect;
use gandr_core_checker::worlds::Predicate;
use gandr_surface_corpus::Refusal;
use gandr_surface_lowering::Ending;
use gandr_surface_lowering::FormFault;
use gandr_surface_lowering::FragmentBoundary;
use gandr_surface_lowering::LoweringRefusal;
use gandr_surface_lowering::MatchFault;
use gandr_surface_lowering::Offer;
use gandr_surface_lowering::Repair;
use gandr_surface_lowering::WfKind;
use gandr_surface_syntax::ClosingClass;
use gandr_surface_syntax::GroutShape;
use quenchant_shape::shape::Maybe;

use crate::locus::Captor;
use crate::message::Spoken;

quenchant_shape::reason_enum! {
    /// Why a diagnostic tells its reader nothing to do.
    pub mod help {
        /// The reason a diagnostic has no help.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The diagnostic reports no refusal: a goal, an unsettled
            /// declaration or a ledger line.
            Statement,
            /// A warning: the edit it proposes, when it proposes one, is its
            /// help.
            Warning,
            /// The refusal is another declaration's: its help is on that
            /// declaration's diagnostic.
            Upstream,
            /// The refusal's name has no help worded yet.
            Unworded,
        }
    }
}

/// The help of `refusal`: what its reader does about it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one imperative sentence for each worded refusal name, naming the
///   source's own names where the refusal holds them; absent as unworded for
///   every other name.
/// - provides: the `help` of every refusal's diagnostic.
/// - fails: never.
/// - panics: none.
/// - executable: none — the sentence's mood is the prose check's to judge.
///
/// # Adequacy
/// - hypothesis: L3 — one refusal of every vocabulary name is either worded,
///   with a one-line help, or unworded; the most-seen names are worded.
/// - witness: `advice::tests::the_most_seen_names_are_worded_on_one_line`
#[inline]
pub fn advice(refusal: Refusal<'_>) -> Maybe<String, help::Absent>
{
    match refusal {
        Refusal::Lowering(refusal) => lowered(refusal),
        Refusal::Checking(refusal) => checked(refusal),
        Refusal::Corpus(_) => Maybe::Absent(help::Absent::Unworded),
    }
}

/// The help of a lowering refusal.
///
/// # Specification
/// trivial.
fn lowered(refusal: LoweringRefusal<'_>) -> Maybe<String, help::Absent>
{
    Maybe::Present(match refusal {
        LoweringRefusal::UnresolvedName { name, .. } => {
            format!("define `{name}`, or import the module that exports it")
        },
        LoweringRefusal::DuplicateDefinition { name, .. } => {
            format!("give each definition of `{name}` its own name, or delete one of them")
        },
        LoweringRefusal::UnknownMember { module, member, .. } => {
            format!("use a member that `{module}` declares, or add `{member}` to `{module}`")
        },
        LoweringRefusal::OutOfFragment {
            sort,
            boundary: FragmentBoundary::WrongSort,
            ..
        } => format!("write {sort} in this position"),
        LoweringRefusal::MalformedForm { form, fault, .. } => malformed(Spoken(form), fault),
        LoweringRefusal::IllFormedDescription { kind, .. } => ill_formed(kind),
        LoweringRefusal::RulesUncompleted { .. } => String::from(
            "add a rule that joins the two normal forms, or remove one of the two rules",
        ),
        LoweringRefusal::NotATranslation { name, .. } => {
            format!(
                "declare `flow {name}` before this import, or import a source that publishes it"
            )
        },
        LoweringRefusal::SignatureMismatch {
            signature,
            member,
            fault,
            ..
        } => match fault {
            MatchFault::Missing => format!(
                "drop `{member}` from `{signature}`, or declare `pub {member}` where the import reads it"
            ),
            MatchFault::Sort => {
                format!("give `{member}` one type in `{signature}` and where the import reads it")
            },
            MatchFault::Unstated => format!(
                "give the source's `{member}` a signature, or state only operations in `{signature}`"
            ),
        },
        LoweringRefusal::UnlabelledRequirement { name, .. } => {
            format!("write a label before it, `l : {name} with …`, and perform through `l`")
        },
        // Unworded: a later slice words each, most-seen first.
        LoweringRefusal::UnresolvedDocLink { .. }
        | LoweringRefusal::UnresolvedTypeHead { .. }
        | LoweringRefusal::DuplicateSignature { .. }
        | LoweringRefusal::DuplicateImportAlias { .. }
        | LoweringRefusal::ImportUnresolved { .. }
        | LoweringRefusal::ImportCycle { .. }
        | LoweringRefusal::UnlockedDependency { .. }
        | LoweringRefusal::ImportShadows { .. }
        | LoweringRefusal::UnexportedName { .. }
        | LoweringRefusal::ShadowedBuiltin { .. }
        | LoweringRefusal::OutOfFragment { .. }
        | LoweringRefusal::BareFeedback { .. }
        | LoweringRefusal::GradedBridge { .. }
        | LoweringRefusal::MalformedLiteral { .. }
        | LoweringRefusal::NoUniverseAbove { .. }
        | LoweringRefusal::UnknownAttribute { .. }
        | LoweringRefusal::DuplicateAttribute { .. }
        | LoweringRefusal::MissingPayload { .. }
        | LoweringRefusal::NonValuePayload { .. }
        | LoweringRefusal::IllTypedPayload { .. }
        | LoweringRefusal::ForwardMemberReference { .. }
        | LoweringRefusal::PhaseDependence { .. }
        | LoweringRefusal::InertRead { .. }
        | LoweringRefusal::UnprovenLaw { .. }
        | LoweringRefusal::PartialField { .. }
        | LoweringRefusal::NotAFunctor { .. }
        | LoweringRefusal::ProjectionFromApplication { .. }
        | LoweringRefusal::UnreadAscription { .. }
        | LoweringRefusal::UnstatedComponent { .. }
        | LoweringRefusal::UninterfacedMember { .. }
        | LoweringRefusal::UndescribedMember { .. }
        | LoweringRefusal::FamilyTelescope { .. }
        | LoweringRefusal::LowercaseModuleName { .. }
        | LoweringRefusal::ImplicitTelescope { .. }
        | LoweringRefusal::TelescopeCycle { .. }
        | LoweringRefusal::ImplicitUnsupplied { .. }
        | LoweringRefusal::ImplicitInParentheses { .. }
        | LoweringRefusal::InstanceUnanswered { .. }
        | LoweringRefusal::InstanceAmbiguous { .. }
        | LoweringRefusal::ModelImplicitValue { .. }
        | LoweringRefusal::RegionAsValue { .. }
        | LoweringRefusal::EntryType { .. }
        | LoweringRefusal::StrayReceiverMode { .. }
        | LoweringRefusal::AmbiguousMethod { .. }
        | LoweringRefusal::ViewNotPlace { .. }
        | LoweringRefusal::ViewOfNoPlace { .. }
        | LoweringRefusal::NonExhaustiveMatch { .. }
        | LoweringRefusal::MismatchedPattern { .. }
        | LoweringRefusal::UnmarkedSelfReference { .. }
        | LoweringRefusal::UnguardedCorecursion { .. }
        | LoweringRefusal::DescentOnSeveralParameters { .. }
        | LoweringRefusal::Unreachable { .. }
        | LoweringRefusal::OutsideLoop { .. }
        | LoweringRefusal::AcrossHandler { .. }
        | LoweringRefusal::WithoutK { .. }
        | LoweringRefusal::DirectedCell { .. }
        | LoweringRefusal::CellNotALoop { .. }
        | LoweringRefusal::RulesUnoriented { .. }
        | LoweringRefusal::RulesNonLinear { .. }
        | LoweringRefusal::RulesOverlapSecondOrder { .. }
        | LoweringRefusal::RulesOverlapCondition { .. }
        | LoweringRefusal::RulesDiverge { .. }
        | LoweringRefusal::RulesNeverComplete { .. }
        | LoweringRefusal::RulesUndecided { .. }
        | LoweringRefusal::UnderivedRule { .. }
        | LoweringRefusal::GenericMisplaced { .. }
        | LoweringRefusal::GenericUncovered { .. }
        | LoweringRefusal::UnknownTactic { .. }
        | LoweringRefusal::BudgetExceeded { .. }
        | LoweringRefusal::GrammarMismatch { .. }
        | LoweringRefusal::UnknownMold { .. }
        | LoweringRefusal::HostConflict { .. }
        | LoweringRefusal::Unminted { .. } => return Maybe::Absent(help::Absent::Unworded),
    })
}

/// The help of a malformed form, by its fault.
///
/// # Specification
/// trivial.
fn malformed(
    form: Spoken,
    fault: FormFault,
) -> String
{
    let opening = |close: ClosingClass| match close {
        ClosingClass::Paren => "(",
        ClosingClass::Bracket => "[",
        ClosingClass::Brace => "{",
    };
    let closing = |close: ClosingClass| match close {
        ClosingClass::Paren => ")",
        ClosingClass::Bracket => "]",
        ClosingClass::Brace => "}",
    };
    match fault {
        FormFault::Repaired(Repair::Grout(GroutShape::Convex)) => {
            String::from("write the missing term")
        },
        FormFault::Repaired(Repair::Grout(GroutShape::Prefix | GroutShape::Postfix))
        | FormFault::MissingOperand => String::from("write the missing operand"),
        FormFault::Repaired(Repair::Grout(GroutShape::Infix)) => {
            String::from("write an operator between the two terms")
        },
        FormFault::Repaired(Repair::Keyword(stray)) => match stray.offer {
            Offer::Capitalised(offer) => format!("write `{}` instead", offer.as_ref()),
            Offer::Unspelled => {
                format!("write a term in place of `{}`", stray.written.as_ref())
            },
        },
        FormFault::Repaired(Repair::GhostClose(close)) => {
            format!("add the closing `{}`", closing(close))
        },
        FormFault::Repaired(Repair::Unended(Ending::Tile(tile))) => {
            format!("add the closing `{}`", tile.as_ref())
        },
        FormFault::Repaired(Repair::Unended(Ending::Unnamed)) => format!("finish the {form}"),
        FormFault::Repaired(Repair::Diverged(Ending::Tile(tile))) => {
            format!("write `{}` here", tile.as_ref())
        },
        FormFault::Repaired(Repair::Diverged(Ending::Unnamed)) | FormFault::ExtraOperand => {
            String::from("remove the extra operand")
        },
        FormFault::MisplacedTile => {
            format!("move the keyword or symbol to its place in the {form}")
        },
        FormFault::ExtraClose(close) => format!("remove the extra `{}`", closing(close)),
        FormFault::ExtraOpen(close) => {
            format!("remove the extra `{}`, or close it", opening(close))
        },
        FormFault::Misspelt(keyword) => {
            format!(
                "write the keyword `{}` in place of this word",
                keyword.as_ref()
            )
        },
        FormFault::MissingOpen(close) => {
            format!(
                "add the `{}` that this `{}` closes",
                opening(close),
                closing(close)
            )
        },
    }
}

/// The help of an ill-formed description, by its kind.
///
/// # Specification
/// trivial.
fn ill_formed(kind: WfKind) -> String
{
    String::from(match kind {
        WfKind::OutOfSignatureRule => {
            "declare the operation in the signature, or write the rule over operations it declares"
        },
        WfKind::UnboundRhsVariable => {
            "bind the variable on the rule's left-hand side, or remove it from the right-hand side"
        },
        WfKind::ArityDoesNotCompose => "make each map of the bridge arity compose with the next",
        WfKind::DeclaresDerivedMetadata => "remove the declaration, which the rules derive",
        WfKind::DerivedBoundaryMismatch => {
            "make the declared sphere fix the boundary that the wiring derives"
        },
        WfKind::CyclicCircuitWiring => "wire the rule so that no port reaches itself",
        WfKind::UnknownRewritePort => {
            "declare the rewrite in the rule's telescope, or apply a rewrite that it declares"
        },
        WfKind::CircuitDerivationBudget => "split the rule's wiring into smaller rules",
        WfKind::DuplicateSortName => "give each sort its own name",
        WfKind::UnknownResultSort => {
            "declare the sort, or target a sort that the signature declares"
        },
        WfKind::UnknownVarSort => {
            "declare the sort, or recurse at a sort that the signature declares"
        },
        WfKind::UnknownPortSort => {
            "declare the sort in the signature, or put a builtin type at the port"
        },
        WfKind::SortPolarityDisagreement => "give the sort the polarity of its declaration",
        WfKind::MisplacedResults => {
            "move the results tuple to the root of the rule's right-hand side"
        },
        WfKind::NonRepresentableBinder => "bind the variable over a declared, representable sort",
        WfKind::SplitCircuitOutputs => "read all the outputs of the many-out node together",
        WfKind::DuplicateFaceName => "give each face of the shape its own name",
        WfKind::FaceOutsideShape => "put in the face only points that the shape holds",
        WfKind::UnsortedBinding => {
            "use the variable where a port binds it over the same sorts, with one argument for \
             each variable it binds"
        },
        WfKind::MisplacedAbstraction => {
            "abstract names only in an argument at a port that binds as many"
        },
        WfKind::AtomResult => "return a sort that is not an atom sort",
        WfKind::NonAtomAbstraction => {
            "abstract over an atom sort, or bind the variable with `pi+` instead"
        },
        WfKind::UnknownFreshness => {
            "name in the condition an atom that the rule abstracts and a variable that its left \
             side binds"
        },
        WfKind::Capture => "state the atom fresh for the variable with `where a # q`",
        WfKind::MisplacedAtom => {
            "name the atom only inside `bind a . t`, at a port of the sort that it abstracts"
        },
        WfKind::UndecidedCondition => {
            "put the variable under the same abstractions at each of its occurrences"
        },
    })
}

/// The help of a checker refusal.
///
/// # Specification
/// trivial.
fn checked(refusal: CheckRefusal) -> Maybe<String, help::Absent>
{
    Maybe::Present(match refusal {
        CheckRefusal::TypeMismatch(_) => String::from(
            "change the term or the type it is checked against, so that the two types agree",
        ),
        CheckRefusal::EndpointMismatch {
            miss: EndpointMiss::Unshown,
            ..
        } => String::from(
            "give `here` a point that both endpoints convert to, or change the endpoints",
        ),
        CheckRefusal::EndpointMismatch {
            miss: EndpointMiss::Budget,
            ..
        } => String::from(
            "state the equation through lemmas that each unfold less, or split the computation \
             into steps the conversion settles one at a time",
        ),
        CheckRefusal::StageNotBelow { .. } => String::from(
            "recurse on a field of the parameter, which a match takes apart, and not on the \
             parameter itself",
        ),
        CheckRefusal::Access {
            defect: AccessDefect::Escaped { by },
            ..
        } => format!(
            "use the view outside {}, or open the `access` inside it",
            Captor(by)
        ),
        CheckRefusal::Access {
            defect: AccessDefect::Lent,
            ..
        } => String::from("use the held value only after the `access` that lends it ends"),
        CheckRefusal::Access {
            defect: AccessDefect::KeptEscaped,
            ..
        } => String::from("return a value that the scope's own region does not keep"),
        CheckRefusal::Linearity {
            defect: LinearityDefect::Residue { .. },
            ..
        } => String::from(
            "close the endpoint before the fork half or receive body that bound it ends",
        ),
        CheckRefusal::RuleNotRespected { .. } => String::from(
            "give the arms equal results on the terms that each of the datatype's rules \
             identifies",
        ),
        CheckRefusal::NotApart { .. } => {
            String::from("write an arm for the path, because its endpoints can be equal")
        },
        CheckRefusal::NegativeOccurrence(_) => String::from(
            "apply the datatype there only to its own parameters, one stage below its \
             constructor",
        ),
        CheckRefusal::RunNotAdmitted { .. } => String::from(
            "change the run so that each move is one that the protocol admits at that point",
        ),
        CheckRefusal::UndecidedCoverage(_) => {
            String::from("replace the pattern hole with a pattern")
        },
        CheckRefusal::ImplicitUnsolved { .. } => {
            String::from("supply the implicit by name in brackets before the parentheses")
        },
        CheckRefusal::Located {
            defect:
                LocatedDefect::Immobile {
                    crossed: Crossed::Result | Crossed::Constant,
                    predicate: Predicate::Mobile,
                    ..
                },
            ..
        } => String::from(
            "return data or a handle from the migration, or mark the abstract type `mobile` in \
             its signature",
        ),
        CheckRefusal::Located {
            defect:
                LocatedDefect::Immobile {
                    crossed: Crossed::Result | Crossed::Constant,
                    predicate: Predicate::Open,
                    ..
                },
            ..
        } => String::from(
            "hold data in the handle, or an abstract type that its signature marks `mobile`",
        ),
        CheckRefusal::Located {
            defect:
                LocatedDefect::Immobile {
                    crossed: Crossed::Capture,
                    ..
                },
            ..
        } => String::from(
            "capture only data in a thunk the migration returns, or mark the abstract type \
             `mobile` in its signature",
        ),
        CheckRefusal::Located {
            defect:
                LocatedDefect::Immobile {
                    crossed: Crossed::Homed,
                    ..
                },
            ..
        } => String::from(
            "call the declaration before the migration returns, and return what it answers",
        ),
        CheckRefusal::BridgeAtSealedType { .. } => String::from(
            "give the abstract type an `identity` attribute that names its relation, or relate \
             points of a type that is not sealed",
        ),
        CheckRefusal::ComposeNotAShape {
            pasting: gandr_core_term::compose::Pasting::Chain { .. },
            ..
        } => String::from(
            "write a stratum of degree at least 2m - 1 and bound at least 2m + 1 for a chain of m \
             cells",
        ),
        CheckRefusal::ComposeNotAShape {
            pasting: gandr_core_term::compose::Pasting::Columns { .. },
            ..
        } => String::from(
            "write a stratum whose bound holds the level-two shape and whose degree reaches its \
             degree",
        ),
        CheckRefusal::ComposeDoesNotFill {
            seam: gandr_core_term::compose::Seam::Outer,
            ..
        } => String::from("start each cell at the point where the cell before it ends"),
        CheckRefusal::ComposeDoesNotFill {
            seam: gandr_core_term::compose::Seam::Column(_),
            ..
        } => String::from(
            "start each 2-cell of a column at the 1-cell where the 2-cell before it ends",
        ),
        CheckRefusal::NoFiller { .. } => String::from(
            "ask for the square the generator makes, with its sides composites of the cells and \
             at least one cell a path of paths",
        ),
        // Unworded: a later slice words each, most-seen first.
        CheckRefusal::NotADataType(_)
        | CheckRefusal::DataKindNotUniverse(_)
        | CheckRefusal::DataFieldLevel { .. }
        | CheckRefusal::RuleNotPresentable { .. }
        | CheckRefusal::LoopNotRespected { .. }
        | CheckRefusal::LoopUndecided { .. }
        | CheckRefusal::AbstractKindNotUniverse(_)
        | CheckRefusal::RepresentationAboveKind { .. }
        | CheckRefusal::NotAnAbstractType(_)
        | CheckRefusal::AtomTransport { .. }
        | CheckRefusal::SealSiteRepeated(_)
        | CheckRefusal::DataArgumentArity(_)
        | CheckRefusal::UnknownConstructor { .. }
        | CheckRefusal::ConstructorArity(_)
        | CheckRefusal::NonExhaustiveDataCase(_)
        | CheckRefusal::AbsentRecordField(_)
        | CheckRefusal::AbsentTupleComponent(_)
        | CheckRefusal::MissingRecordField { .. }
        | CheckRefusal::UnknownOperation { .. }
        | CheckRefusal::HandlerCoverage { .. }
        | CheckRefusal::HandlerUnlawful { .. }
        | CheckRefusal::ShiftWithoutReset { .. }
        | CheckRefusal::DependentStack { .. }
        | CheckRefusal::PathCode(_)
        | CheckRefusal::CompoundEndpoint { .. }
        | CheckRefusal::FunextUnsupported { .. }
        | CheckRefusal::PointwiseDistinct { .. }
        | CheckRefusal::EquivUnsupported { .. }
        | CheckRefusal::UncertifiedStratum { .. }
        | CheckRefusal::OutsideFold { .. }
        | CheckRefusal::RoundTripDistinct { .. }
        | CheckRefusal::NotOver { .. }
        | CheckRefusal::UaUncertified { .. }
        | CheckRefusal::UaInequivalent { .. }
        | CheckRefusal::ComposeUncertified { .. }
        | CheckRefusal::FillUncertified { .. }
        | CheckRefusal::GeneratorFamilyUnsupported { .. }
        | CheckRefusal::EffectSignatureConflict { .. }
        | CheckRefusal::ShapeMismatch { .. }
        | CheckRefusal::NotSynthesisable { .. }
        | CheckRefusal::UnknownConstant { .. }
        | CheckRefusal::OutOfFragment { .. }
        | CheckRefusal::UnboundIndex { .. }
        | CheckRefusal::BudgetExceeded { .. }
        | CheckRefusal::DanglingNode { .. }
        | CheckRefusal::AdmissionOrder { .. }
        | CheckRefusal::MachineInvariant
        | CheckRefusal::SortMismatch { .. }
        | CheckRefusal::LevelMismatch { .. }
        | CheckRefusal::DependentBind { .. }
        | CheckRefusal::Undecided { .. }
        | CheckRefusal::FamilyArity { .. }
        | CheckRefusal::FamilyArgumentClassifier { .. }
        | CheckRefusal::StaticLambdaArgument { .. }
        | CheckRefusal::StaticClassifierExpected { .. }
        | CheckRefusal::NestedOccurrence(_)
        | CheckRefusal::IndexOccurrence(_)
        | CheckRefusal::NonUniformOccurrence(_)
        | CheckRefusal::CrossBlockReference { .. }
        | CheckRefusal::StagesDisagree { .. }
        | CheckRefusal::StageNotCarried { .. }
        | CheckRefusal::SessionMismatch { .. }
        | CheckRefusal::Linearity { .. }
        | CheckRefusal::Access { .. }
        | CheckRefusal::Codata { .. }
        | CheckRefusal::Located { .. }
        | CheckRefusal::UnenclosedRun { .. }
        | CheckRefusal::ModelUnanswered { .. }
        | CheckRefusal::ModelAmbiguous { .. }
        | CheckRefusal::TacticRefused { .. }
        | CheckRefusal::CapabilityForged { .. }
        | CheckRefusal::CapabilityAmplified(_)
        | CheckRefusal::CapabilityOutsideAuthority { .. }
        | CheckRefusal::CapabilityEscaped { .. }
        | CheckRefusal::CapabilityConsumable(_)
        | CheckRefusal::CapabilityUngranted { .. }
        | CheckRefusal::FootprintsOverlap { .. }
        | CheckRefusal::SessionNotEquivalent { .. }
        | CheckRefusal::SessionNotSubtype { .. }
        | CheckRefusal::SessionCodeExpected { .. }
        | CheckRefusal::OpenSessionPayload { .. }
        | CheckRefusal::UnassertedLaw { .. }
        | CheckRefusal::NonCovariantMotive { .. }
        | CheckRefusal::RideUnsupported { .. }
        | CheckRefusal::DialogueUnmatched { .. }
        | CheckRefusal::DialogueInverted { .. }
        | CheckRefusal::ForwardUnsupported { .. }
        | CheckRefusal::Boundary { .. } => return Maybe::Absent(help::Absent::Unworded),
    })
}

/// The refusal names the procedural rewrite has worded, each on one line.
#[cfg(test)]
mod tests
{
    use quenchant_shape::shape::Maybe;

    use super::advice;
    use super::help;
    use crate::message::tests::one_of_every_name;

    /// The names the procedural rewrite has worded: the most-seen first,
    /// then the names worded as their goldens regenerated.
    const WORDED: [&str; 33] = [
        "TypeMismatch",
        "MalformedForm",
        "EndpointMismatch",
        "IllFormedDescription",
        "StageNotBelow",
        "UnresolvedName",
        "OutOfFragment.WrongSort",
        "ViewEscaped",
        "UnknownMember",
        "DuplicateDefinition",
        "HeldLent",
        "ImplicitUnsolved",
        "NegativeOccurrence",
        "NotApart",
        "RuleNotRespected",
        "RunNotAdmitted",
        "UndecidedCoverage",
        "KeptEscaped",
        "LinearResidue",
        "RulesUncompleted",
        "Immobile",
        "NotOpen",
        "Immobile.Capture",
        "Immobile.Homed",
        "NotOpen.Capture",
        "NotOpen.Homed",
        "NotATranslation",
        "SignatureMismatch.Sort",
        "BridgeAtSealedType",
        "UnlabelledRequirement",
        "ComposeNotAShape",
        "ComposeDoesNotFill",
        "NoFiller",
    ];

    /// Every worded name's refusal has a one-line help that opens with a
    /// lowercase verb; every other name's is unworded, and a corpus refusal
    /// is too.
    #[test]
    fn the_most_seen_names_are_worded_on_one_line()
    {
        let mut seen: alloc::vec::Vec<alloc::string::String> = alloc::vec::Vec::new();
        for refusal in one_of_every_name() {
            let name = alloc::format!("{}", refusal.name());
            match advice(refusal) {
                Maybe::Present(help) => {
                    assert!(WORDED.contains(&name.as_str()), "{name} is worded: {help}");
                    assert!(!help.contains('\n'), "{name}'s help is one line: {help}");
                    assert!(
                        help.starts_with(|first: char| first.is_ascii_lowercase()),
                        "{name}'s help opens with its verb: {help}"
                    );
                    seen.push(name);
                },
                Maybe::Absent(reason) => {
                    assert_eq!(reason, help::Absent::Unworded, "{name}");
                    assert!(!WORDED.contains(&name.as_str()), "{name} has no help");
                },
            }
        }
        for name in WORDED {
            assert!(
                seen.iter().any(|held| held == name),
                "{name} is reached by a refusal of the vocabulary"
            );
        }
    }
}
