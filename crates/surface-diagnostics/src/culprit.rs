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
    /// - witness: `diagnostics::diagnostics::refusals_of_one_class_label_what_their_locus_is`
    /// - witness: `culprit::tests::every_repair_labels_what_is_missing`
    #[spec(ensures: |ret| !ret.0.is_empty() && !ret.0.contains(['\r', '\n']))]
    #[inline]
    #[must_use]
    pub fn of(refusal: Refusal<'_>) -> Self
    {
        match refusal {
            | Refusal::Lowering(lowering) => lowered(lowering),
            | Refusal::Corpus(CorpusRefusal::ExpectationOutsideFixtureRoot { .. }) => {
                Self("an expectation the strict root refuses")
            },
            | Refusal::Checking(checking) => checked(checking),
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
        | LoweringRefusal::UnresolvedName { .. } => "not found in this scope",
        | LoweringRefusal::UnresolvedDocLink { .. } => "links to no declared name",
        | LoweringRefusal::UnresolvedTypeHead { .. } => "no type head of this name and arity",
        | LoweringRefusal::DuplicateSignature { .. }
        | LoweringRefusal::DuplicateDefinition { .. }
        | LoweringRefusal::DuplicateImportAlias { .. }
        | LoweringRefusal::DuplicateAttribute { .. } => "written again here",
        | LoweringRefusal::ShadowedBuiltin { .. } => "shadows a builtin",
        | LoweringRefusal::OutOfFragment { boundary, .. } => match boundary {
            | FragmentBoundary::Reserved => "a reserved form",
            | FragmentBoundary::Unadmitted => "a form the fragment does not admit",
            | FragmentBoundary::WrongSort => "a form of another sort than this position takes",
            | FragmentBoundary::Arity(_) => "the wrong number of operands",
            | FragmentBoundary::Indexed => "a family applied to an index",
            | FragmentBoundary::Unannotated => "needs a stated type",
            | FragmentBoundary::NonUniform => "not the parameter itself",
            | FragmentBoundary::NotInTail => "not on a path through a body",
            | FragmentBoundary::JoinsBlock => "an answer the arms do not give",
            | FragmentBoundary::EmptyList => "an empty list, not the unit",
        },
        | LoweringRefusal::GradedBridge { .. } => "a grade other than `ω`",
        | LoweringRefusal::MalformedLiteral { .. } => "not this literal's lexeme",
        | LoweringRefusal::MalformedForm { fault, .. } => match fault {
            | FormFault::Repaired(Repair::Grout(GroutShape::Convex)) => "a term is missing here",
            | FormFault::Repaired(Repair::Grout(GroutShape::Prefix | GroutShape::Postfix))
            | FormFault::MissingOperand => "an operand is missing here",
            | FormFault::Repaired(Repair::Grout(GroutShape::Infix)) => {
                "an operator is missing here"
            },
            | FormFault::Repaired(Repair::GhostClose(ClosingClass::Paren)) => "missing `)`",
            | FormFault::Repaired(Repair::GhostClose(ClosingClass::Bracket)) => "missing `]`",
            | FormFault::Repaired(Repair::GhostClose(ClosingClass::Brace)) => "missing `}`",
            | FormFault::Repaired(Repair::Unended(Ending::Tile(_))) => {
                "its closing tile belongs here"
            },
            | FormFault::Repaired(Repair::Unended(Ending::Unnamed)) => "the form stops here",
            | FormFault::ExtraOperand => "an operand the form does not take",
            | FormFault::MisplacedTile => "out of place",
        },
        | LoweringRefusal::UnknownAttribute { .. } => "unknown attribute",
        | LoweringRefusal::MissingPayload { .. } => "takes a payload",
        | LoweringRefusal::NonValuePayload { .. } => "a payload that is not a value",
        | LoweringRefusal::IllTypedPayload { .. } => "a payload of another schema",
        | LoweringRefusal::ForwardMemberReference { .. } => "named before it is declared",
        | LoweringRefusal::UnknownMember { .. } => "no member of this name",
        | LoweringRefusal::UnreadAscription { .. } => "not read by the fragment yet",
        | LoweringRefusal::LowercaseModuleName { .. } => "a lowercase initial",
        | LoweringRefusal::NonExhaustiveMatch { .. } => "some value matches no arm",
        | LoweringRefusal::UnmarkedSelfReference { .. } => "recursion without a claim",
        | LoweringRefusal::MissingExit { .. } => "the body ends here without an exit",
        | LoweringRefusal::Unreachable { .. } => "no path reaches this",
        | LoweringRefusal::WithoutK { .. } => "a path matched against reflexivity",
        | LoweringRefusal::BudgetExceeded { .. } => "the lowering's allowance ran out",
        | LoweringRefusal::GrammarMismatch { .. } => "molded under another grammar",
        | LoweringRefusal::UnknownMold { .. } => "a mold the grammar does not hold",
    })
}

/// The label of a checker refusal's primary locus.
///
/// # Specification
/// trivial.
const fn checked(refusal: CheckRefusal) -> Culprit
{
    Culprit(match refusal {
        | CheckRefusal::NotADataType(_) => "not an admitted datatype",
        | CheckRefusal::DataKindNotUniverse(_) => "not a value universe",
        | CheckRefusal::DataFieldLevel { .. } => "above the declared universe",
        | CheckRefusal::DataArgumentArity(_) => "the wrong number of parameters",
        | CheckRefusal::UnknownConstructor { .. } => "no constructor of the datatype",
        | CheckRefusal::ConstructorArity(_) => "the wrong number of fields",
        | CheckRefusal::NonExhaustiveDataCase(_) => "not every constructor once",
        | CheckRefusal::AbsentRecordField(_) => "no field of the record type",
        | CheckRefusal::AbsentTupleComponent(_) => "no component of the product type",
        | CheckRefusal::MissingRecordField { .. } => "a required field is missing",
        | CheckRefusal::UnknownOperation { .. } => "not an operation of the interface",
        | CheckRefusal::HandlerCoverage { .. } => "not every operation once",
        | CheckRefusal::ShiftWithoutReset { .. } => "no enclosing reset",
        | CheckRefusal::DependentStack { .. } => "its result type mentions the discharged value",
        | CheckRefusal::EffectSignatureConflict { .. } => "effect rows that disagree",
        | CheckRefusal::PathCode(_) => "not a quoted closed first-order code",
        | CheckRefusal::EndpointMismatch { .. } => "not both endpoints of the path",
        | CheckRefusal::CompoundEndpoint { .. } => "an endpoint that returns no pure value",
        | CheckRefusal::FunextUnsupported { .. } => "functions outside the rule's fragment",
        | CheckRefusal::PointwiseDistinct { .. } => "functions that differ at some input",
        | CheckRefusal::TypeMismatch(Mismatch::Value { .. } | Mismatch::Computation { .. }) => {
            "its type does not convert"
        },
        | CheckRefusal::ShapeMismatch { .. } => "its type is not of the required shape",
        | CheckRefusal::NotSynthesisable {
            form: CheckingForm::Hole(_),
        } => "an unfilled hole",
        | CheckRefusal::NotSynthesisable { .. } => "needs a type to be checked against",
        | CheckRefusal::UnknownConstant { .. } => "no declaration with a type",
        | CheckRefusal::OutOfFragment { .. } => "no rule for this former",
        | CheckRefusal::UnboundIndex { .. } => "an unbound variable",
        | CheckRefusal::BudgetExceeded { .. } => "the judgement's allowance ran out",
        | CheckRefusal::DanglingNode { .. } => "a node the arena does not hold",
        | CheckRefusal::AdmissionOrder { .. } => "admitted out of order",
        | CheckRefusal::MachineInvariant => "the checking machine disagreed with itself",
        | CheckRefusal::SortMismatch { .. } => "a universe of the other sort",
        | CheckRefusal::LevelMismatch { .. } => "a universe at a level not admitted",
        | CheckRefusal::DependentBind { .. } => "its type mentions the bound value",
        | CheckRefusal::Undecided { .. } => "an unfolding not certified",
        | CheckRefusal::FamilyArity { .. } => "the wrong number of arguments",
        | CheckRefusal::FamilyArgumentClassifier { .. } => "outside its parameter's domain",
        | CheckRefusal::StaticLambdaArgument { .. } => "a type operator where a value is needed",
        | CheckRefusal::StaticClassifierExpected { .. } => "a type that classifies no codes",
        | CheckRefusal::NegativeOccurrence(_) => "the declared type under a function's domain",
        | CheckRefusal::NestedOccurrence(_) => "the declared type inside another former",
        | CheckRefusal::IndexOccurrence(_) => "the declared type inside an index",
        | CheckRefusal::NonUniformOccurrence(_) => "the declared type at other arguments",
        | CheckRefusal::CrossBlockReference { .. } => "names a later declaration",
        | CheckRefusal::DescentNotReplayed { .. } => "a descent claim that does not replay",
    })
}

/// The labels of malformed forms.
#[cfg(test)]
mod tests
{
    use gandr_surface_corpus::Refusal;
    use gandr_surface_lowering::Ending;
    use gandr_surface_lowering::FormFault;
    use gandr_surface_lowering::FormName;
    use gandr_surface_lowering::LoweringRefusal;
    use gandr_surface_lowering::Repair;
    use gandr_surface_lowering::TileName;
    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::ByteSpan;
    use gandr_surface_syntax::ClosingClass;
    use gandr_surface_syntax::GroutShape;

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
            8_usize,
            "each repair names what the source left out"
        );
    }
}
