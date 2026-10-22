//! The diagnostics exemplars: one source per refusal name, or the reason it
//! has none.
//!
//! # One exemplar per closed name
//!
//! Every name a `refuses` payload can spell without naming a form
//! (`RefusalName::closed`: the vocabulary, each `OutOfFragment` name a
//! boundary, the run target or a checker former qualifies, each model
//! component's fault and each member's) has an exemplar,
//! `diagnostics/<name>.gandr`, or a row of [`OWED`]. So have the two
//! boundaries no name carries, `OutOfFragment.Reserved` and
//! `OutOfFragment.Unadmitted`: a form past either is named by the form, so
//! their exemplars are named for the boundary.
//!
//! An exemplar opens with a `///` comment naming its subject in backticks and
//! holds a declaration stating `refuses` with the subject's name, beside the
//! context declarations it needs; a boundary's exemplar holds a declaration
//! the lowering refuses at that boundary, whatever form it names. The source
//! may leave parse obligations: a repaired form is one of the refusals shown.
//! `mise run check:exemplars` settles every exemplar, so a stated refusal is a
//! produced one.
//!
//! - Choice: hold the stated name here and leave its production to the settle
//!   gate, as the syntax exemplars do; read a boundary off the lowering, since
//!   its name carries the form instead.
//! - Alternatives: settling each exemplar here, which repeats `gandr test`'s
//!   composition in a second place that would drift from it; one exemplar per
//!   form past each boundary, which is the syntax ledger's per-form admission.
//! - Reversal: a stated name the settle gate stops reading as produced moves
//!   the production check here.
//!
//! # The owed table
//!
//! A name without an exemplar is a row of [`OWED`]: unreachable, with the
//! reason no source produces it, or unwritten, with the issue that writes its
//! exemplar. A name with neither, a row naming no subject, and a subject with
//! both are findings, so the vocabulary cannot grow a name nothing shows.
//!
//! The exemplars were harvested from the fixture corpus: for each name, the
//! smallest fixture declaration refusing with it, cut to the context it needs
//! with `gandr test` deciding each cut. A name the corpus reaches only through
//! an import of a sibling fixture is unwritten: an exemplar cannot carry the
//! sibling.

use alloc::collections::BTreeMap;
use std::path::Path;

use anodized::spec;
use gandr_core_term::CoreArena;
use gandr_surface_corpus::CorpusRoot;
use gandr_surface_corpus::Outcome;
use gandr_surface_corpus::RefusalName;
use gandr_surface_corpus::Stated;
use gandr_surface_corpus::expected;
use gandr_surface_grammar::Pbg;
use gandr_surface_lowering::DeclarationOutcome;
use gandr_surface_lowering::FragmentBoundary;
use gandr_surface_lowering::LoweringBudget;
use gandr_surface_lowering::LoweringRefusal;
use gandr_surface_lowering::lower_module;
use gandr_surface_lowering::namespace::Recognition;
use gandr_surface_parser::parse;
use gandr_surface_syntax::SourceText;

use super::EXTENSION;
use super::ExemplarFault;
use super::ExemplarFinding;
use super::ExemplarReport;
use super::listed;
use crate::ledger::LedgerFault;

/// The directory of diagnostics exemplars under the exemplar directory.
pub(super) const DIAGNOSTICS: &str = "diagnostics";

/// The issue writing the exemplars of the lowering's unshown names.
const LOWERING: Issue = Issue(1788);

/// The issue writing the exemplars of the checker's unshown names.
const CHECKER: Issue = Issue(1789);

/// A tracker issue, by number.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Issue(u16);

/// Why no source produces a refusal.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Reason(&'static str);

/// Why a name has no exemplar.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Owed
{
    /// No source produces it, for the reason stated.
    Unreachable(Reason),
    /// A source produces it, and the issue writes its exemplar.
    Unwritten(Issue),
}

/// Every name without an exemplar, by its spelling, and why.
const OWED: [(&str, Owed); 147_usize] = [
    (
        "AdmissionOrder",
        Owed::Unreachable(Reason("the driver offers declarations in admission order")),
    ),
    (
        "DanglingNode",
        Owed::Unreachable(Reason(
            "the lowering mints every node it names into the arena it hands the checker",
        )),
    ),
    (
        "ExpectationOutsideFixtureRoot",
        Owed::Unreachable(Reason(
            "raised only under the strict root, and the ledger is a fixture root",
        )),
    ),
    (
        "GrammarMismatch",
        Owed::Unreachable(Reason(
            "the driver lowers each tree under the grammar that parsed it",
        )),
    ),
    (
        "MachineInvariant",
        Owed::Unreachable(Reason(
            "the checking machine disagreeing with its own bookkeeping, which no source arranges",
        )),
    ),
    (
        "UnboundIndex",
        Owed::Unreachable(Reason("the lowering binds every variable it emits")),
    ),
    (
        "UnknownMold",
        Owed::Unreachable(Reason(
            "a parsed tree holds only molds of the grammar that built it",
        )),
    ),
    ("UnresolvedDocLink", Owed::Unwritten(LOWERING)),
    ("DuplicateSignature", Owed::Unwritten(LOWERING)),
    ("DuplicateImportAlias", Owed::Unwritten(LOWERING)),
    ("ImportCycle", Owed::Unwritten(LOWERING)),
    ("ImportShadows", Owed::Unwritten(LOWERING)),
    ("UnexportedName", Owed::Unwritten(LOWERING)),
    ("MalformedLiteral", Owed::Unwritten(LOWERING)),
    ("DuplicateAttribute", Owed::Unwritten(LOWERING)),
    ("PhaseDependence", Owed::Unwritten(LOWERING)),
    ("UnknownMember", Owed::Unwritten(LOWERING)),
    ("NotAFunctor", Owed::Unwritten(LOWERING)),
    ("UnreadAscription", Owed::Unwritten(LOWERING)),
    ("FamilyTelescope", Owed::Unwritten(LOWERING)),
    ("LowercaseModuleName", Owed::Unwritten(LOWERING)),
    ("ImplicitTelescope", Owed::Unwritten(LOWERING)),
    ("ImplicitUnsupplied", Owed::Unwritten(LOWERING)),
    ("ImplicitInParentheses", Owed::Unwritten(LOWERING)),
    ("AmbiguousMethod", Owed::Unwritten(LOWERING)),
    ("ViewOfNoPlace", Owed::Unwritten(LOWERING)),
    ("RulesUndecided", Owed::Unwritten(LOWERING)),
    ("Unminted", Owed::Unwritten(LOWERING)),
    ("OutOfFragment.Indexed", Owed::Unwritten(LOWERING)),
    ("OutOfFragment.NonUniform", Owed::Unwritten(LOWERING)),
    ("OutOfFragment.EmptyList", Owed::Unwritten(LOWERING)),
    ("OutOfFragment.Held", Owed::Unwritten(LOWERING)),
    ("OutOfFragment.View", Owed::Unwritten(LOWERING)),
    ("UnstatedComponent.UnknownHead", Owed::Unwritten(LOWERING)),
    ("UnstatedComponent.Arity", Owed::Unwritten(LOWERING)),
    ("UnstatedComponent.IllSorted", Owed::Unwritten(LOWERING)),
    ("UnstatedComponent.Unsorted", Owed::Unwritten(LOWERING)),
    ("UnstatedComponent.ManyOut", Owed::Unwritten(LOWERING)),
    ("UnstatedComponent.Circuit", Owed::Unwritten(LOWERING)),
    ("UnstatedComponent.Constructor", Owed::Unwritten(LOWERING)),
    ("UnstatedComponent.Inherited", Owed::Unwritten(LOWERING)),
    ("UnstatedComponent.Binding", Owed::Unwritten(LOWERING)),
    ("UnstatedComponent.Abstraction", Owed::Unwritten(LOWERING)),
    (
        "UndescribedMember.HigherOrderField",
        Owed::Unwritten(LOWERING),
    ),
    (
        "UndescribedMember.DependentField",
        Owed::Unwritten(LOWERING),
    ),
    ("UndescribedMember.TypeShape", Owed::Unwritten(LOWERING)),
    ("UndescribedMember.NativeDecode", Owed::Unwritten(LOWERING)),
    ("UndescribedMember.NoOutput", Owed::Unwritten(LOWERING)),
    (
        "UndescribedMember.AggregatedOutput",
        Owed::Unwritten(LOWERING),
    ),
    (
        "UndescribedMember.EmptyOperation",
        Owed::Unwritten(LOWERING),
    ),
    (
        "UndescribedMember.UnrepresentableOperation",
        Owed::Unwritten(LOWERING),
    ),
    ("UndescribedMember.ResultArity", Owed::Unwritten(LOWERING)),
    ("UndescribedMember.MixedPolarity", Owed::Unwritten(LOWERING)),
    (
        "UndescribedMember.UnderivedWiring",
        Owed::Unwritten(LOWERING),
    ),
    ("UndescribedMember.OffBoundary", Owed::Unwritten(LOWERING)),
    ("NotADataType", Owed::Unwritten(CHECKER)),
    ("DataKindNotUniverse", Owed::Unwritten(CHECKER)),
    ("LoopUndecided", Owed::Unwritten(CHECKER)),
    ("AbstractKindNotUniverse", Owed::Unwritten(CHECKER)),
    ("RepresentationAboveKind", Owed::Unwritten(CHECKER)),
    ("NotAnAbstractType", Owed::Unwritten(CHECKER)),
    ("SealSiteRepeated", Owed::Unwritten(CHECKER)),
    ("DataArgumentArity", Owed::Unwritten(CHECKER)),
    ("UnknownConstructor", Owed::Unwritten(CHECKER)),
    ("ConstructorArity", Owed::Unwritten(CHECKER)),
    ("IndexedCase", Owed::Unwritten(CHECKER)),
    ("NonExhaustiveDataCase", Owed::Unwritten(CHECKER)),
    ("AbsentTupleComponent", Owed::Unwritten(CHECKER)),
    ("MissingRecordField", Owed::Unwritten(CHECKER)),
    ("IndexOccurrence", Owed::Unwritten(CHECKER)),
    ("NonUniformOccurrence", Owed::Unwritten(CHECKER)),
    ("CrossBlockReference", Owed::Unwritten(CHECKER)),
    ("StagesDisagree", Owed::Unwritten(CHECKER)),
    ("PathCode", Owed::Unwritten(CHECKER)),
    ("EquivUnsupported", Owed::Unwritten(CHECKER)),
    ("UncertifiedStratum", Owed::Unwritten(CHECKER)),
    ("RoundTripDistinct", Owed::Unwritten(CHECKER)),
    ("NotOver", Owed::Unwritten(CHECKER)),
    ("UncertifiedDegree", Owed::Unwritten(CHECKER)),
    ("UncertifiedCondition", Owed::Unwritten(CHECKER)),
    ("UncertifiedAllowance", Owed::Unwritten(CHECKER)),
    ("UnknownGenerator", Owed::Unwritten(CHECKER)),
    ("PastTheBound", Owed::Unwritten(CHECKER)),
    ("NotInverse", Owed::Unwritten(CHECKER)),
    ("TranslatorStuck", Owed::Unwritten(CHECKER)),
    ("CapabilityUngranted", Owed::Unwritten(CHECKER)),
    ("SessionCodeExpected", Owed::Unwritten(CHECKER)),
    ("RideUnsupported", Owed::Unwritten(CHECKER)),
    ("BudgetExceeded", Owed::Unwritten(CHECKER)),
    ("DependentBind", Owed::Unwritten(CHECKER)),
    ("Undecided", Owed::Unwritten(CHECKER)),
    ("FamilyArity", Owed::Unwritten(CHECKER)),
    ("FamilyArgumentClassifier", Owed::Unwritten(CHECKER)),
    ("EffectSignatureConflict", Owed::Unwritten(CHECKER)),
    ("UnknownOperation", Owed::Unwritten(CHECKER)),
    ("HandlerCoverage", Owed::Unwritten(CHECKER)),
    ("ShiftWithoutReset", Owed::Unwritten(CHECKER)),
    ("DependentStack", Owed::Unwritten(CHECKER)),
    ("UnboundEndpoint", Owed::Unwritten(CHECKER)),
    ("ContinuationUnspent", Owed::Unwritten(CHECKER)),
    ("ContinuationUsedTwice", Owed::Unwritten(CHECKER)),
    ("ContinuationCaptured", Owed::Unwritten(CHECKER)),
    ("ContinuationAsValue", Owed::Unwritten(CHECKER)),
    ("NotHeld", Owed::Unwritten(CHECKER)),
    ("NotAView", Owed::Unwritten(CHECKER)),
    ("HeldConsumed", Owed::Unwritten(CHECKER)),
    ("CodataUndeclared", Owed::Unwritten(CHECKER)),
    ("CodataWithoutObservations", Owed::Unwritten(CHECKER)),
    ("CodataOccurrence", Owed::Unwritten(CHECKER)),
    ("CodataObservationLevel", Owed::Unwritten(CHECKER)),
    ("CodataArity", Owed::Unwritten(CHECKER)),
    ("Immobile", Owed::Unwritten(CHECKER)),
    ("CapabilityMissing", Owed::Unwritten(CHECKER)),
    ("CapabilityCaptured", Owed::Unwritten(CHECKER)),
    ("Elsewhere", Owed::Unwritten(CHECKER)),
    ("HoldElsewhere", Owed::Unwritten(CHECKER)),
    ("Unlocated", Owed::Unwritten(CHECKER)),
    ("UndeclaredWorld", Owed::Unwritten(CHECKER)),
    ("HostWorldUndeclared", Owed::Unwritten(CHECKER)),
    ("MarkUnfounded", Owed::Unwritten(CHECKER)),
    ("EntryNamed", Owed::Unwritten(CHECKER)),
    ("EntryUngranted", Owed::Unwritten(CHECKER)),
    ("NotAHandle", Owed::Unwritten(CHECKER)),
    ("OutOfFragment.ValueLift", Owed::Unwritten(CHECKER)),
    ("OutOfFragment.NumericLiteral", Owed::Unwritten(CHECKER)),
    ("OutOfFragment.NumericAtom", Owed::Unwritten(CHECKER)),
    ("OutOfFragment.TypeLift", Owed::Unwritten(CHECKER)),
    ("OutOfFragment.Abstract", Owed::Unwritten(CHECKER)),
    ("OutOfFragment.SortParameter", Owed::Unwritten(CHECKER)),
    ("OutOfFragment.TopUniverse", Owed::Unwritten(CHECKER)),
    ("OutOfFragment.StaticLambda", Owed::Unwritten(CHECKER)),
    ("OutOfFragment.EffectRow", Owed::Unwritten(CHECKER)),
    ("OutOfFragment.Reify", Owed::Unwritten(CHECKER)),
    ("OutOfFragment.Stack", Owed::Unwritten(CHECKER)),
    ("OutOfFragment.Perform", Owed::Unwritten(CHECKER)),
    ("OutOfFragment.Handle", Owed::Unwritten(CHECKER)),
    ("OutOfFragment.Resume", Owed::Unwritten(CHECKER)),
    ("OutOfFragment.Reset", Owed::Unwritten(CHECKER)),
    ("OutOfFragment.Shift", Owed::Unwritten(CHECKER)),
    ("OutOfFragment.Capability", Owed::Unwritten(CHECKER)),
    ("OutOfFragment.Exercise", Owed::Unwritten(CHECKER)),
    ("OutOfFragment.Scope", Owed::Unwritten(CHECKER)),
    ("OutOfFragment.Run", Owed::Unwritten(CHECKER)),
    ("OutOfFragment.HigherFlow", Owed::Unwritten(CHECKER)),
    ("OutOfFragment.Memory", Owed::Unwritten(CHECKER)),
    ("OutOfFragment.Buffer", Owed::Unwritten(CHECKER)),
    ("OutOfFragment.Abandon", Owed::Unwritten(CHECKER)),
];

/// What a diagnostics exemplar shows.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Subject
{
    /// A name no form qualifies.
    Named(RefusalName),
    /// A boundary whose refusals are named by their form.
    Boundary(FragmentBoundary),
}

impl Subject
{
    /// Every subject: each closed name, then the reserved and the unadmitted
    /// boundary.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one subject per closed name, in the vocabulary's order, then
    ///   the two boundaries.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the committed exemplars and rows pair every subject;
    ///   a lost subject leaves its exemplar stray.
    /// - witness: `ledger::exemplars::tests::the_committed_exemplars_verify`
    /// - witness: `ledger::exemplars::diagnostics::tests::each_subject_pairs_with_one_exemplar_or_one_row`
    #[spec(ensures: |ret| ret.len() == RefusalName::closed().len().saturating_add(2))]
    fn every() -> Vec<Self>
    {
        RefusalName::closed()
            .into_iter()
            .map(Self::Named)
            .chain([
                Self::Boundary(FragmentBoundary::Reserved),
                Self::Boundary(FragmentBoundary::Unadmitted),
            ])
            .collect()
    }

    /// The name the subject's file, comment and owed row carry: a name's
    /// spelling, or `OutOfFragment.` and the boundary.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the spelling of a name; `OutOfFragment.Reserved` or
    ///   `OutOfFragment.Unadmitted` for a boundary.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every committed exemplar is found by the name and
    ///   opens with it; another name leaves the subject missing.
    /// - witness: `ledger::exemplars::tests::the_committed_exemplars_verify`
    /// - witness: `ledger::exemplars::diagnostics::tests::an_exemplar_refuses_with_its_own_name`
    #[spec(ensures: |ret| !ret.is_empty())]
    fn name(self) -> String
    {
        match self {
            Self::Named(name) => name.spelling().to_string(),
            Self::Boundary(FragmentBoundary::Reserved) => String::from("OutOfFragment.Reserved"),
            Self::Boundary(_) => String::from("OutOfFragment.Unadmitted"),
        }
    }
}

impl core::fmt::Display for Subject
{
    /// Writes `refusal `name`` or `boundary `name``.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the kind of subject, then its name in backticks.
    /// - fails: a failed write.
    /// - panics: none.
    /// - executable: none — the text is written into a formatter no predicate
    ///   reads back.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a missing subject's finding is printed whole and
    ///   compared.
    /// - witness: `ledger::exemplars::diagnostics::tests::each_subject_pairs_with_one_exemplar_or_one_row`
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            Self::Named(_) => write!(f, "refusal `{}`", self.name()),
            Self::Boundary(_) => write!(f, "boundary `{}`", self.name()),
        }
    }
}

/// Verify the diagnostics exemplars under `folder` against the closed names,
/// the two named boundaries and [`OWED`], filing what holds and what does not
/// in `report`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: each subject with a file and no row is verified and counted, or a
///   finding; each with a row and no file is counted owed; each with both, or
///   neither, is a finding; so is each row naming no subject and each file
///   naming none. A missing folder reads as empty.
/// - provides: the diagnostics part of `gandr ledger exemplars <directory>`.
/// - fails: a folder that exists and cannot be listed.
/// - panics: none.
///
/// # Errors
/// [`LedgerFault::Unreadable`] naming the folder.
///
/// # Adequacy
/// - hypothesis: L3 — the committed exemplars and table pair every subject; a
///   renamed exemplar is its subject missing and its file stray; an exemplar
///   beside its row, a row for no name, and an exemplar refusing with another
///   name are findings by name.
/// - witness: `ledger::exemplars::tests::the_committed_exemplars_verify`
/// - witness: `ledger::exemplars::diagnostics::tests::each_subject_pairs_with_one_exemplar_or_one_row`
/// - witness: `ledger::exemplars::diagnostics::tests::an_exemplar_refuses_with_its_own_name`
#[spec(ensures: |ref ret| ret.is_err() || report.diagnosed.saturating_add(report.owed) <= Subject::every().len())]
pub(super) fn verify(
    pbg: &Pbg,
    folder: &Path,
    report: &mut ExemplarReport,
) -> Result<(), LedgerFault>
{
    let mut present = listed(folder)?;
    let mut rows: BTreeMap<&str, Owed> = OWED.into_iter().collect();
    for subject in Subject::every() {
        let name = subject.name();
        let path = folder.join(format!("{name}.{EXTENSION}"));
        let written = present.remove(&path);
        let owed = rows.remove(name.as_str());
        let fault = match (written, owed) {
            (true, Some(_)) => Some(ExemplarFault::Owed {
                subject: subject.to_string(),
            }),
            (true, None) => refused(pbg, &path, subject).err(),
            (false, Some(_)) => {
                report.owed = report.owed.saturating_add(1);
                continue;
            },
            (false, None) => Some(ExemplarFault::Missing {
                subject: subject.to_string(),
            }),
        };
        match fault {
            Some(fault) => report.findings.push(ExemplarFinding { path, fault }),
            None => report.diagnosed = report.diagnosed.saturating_add(1),
        }
    }
    report
        .findings
        .extend(rows.into_keys().map(|spelled| ExemplarFinding {
            path: folder.join(format!("{spelled}.{EXTENSION}")),
            fault: ExemplarFault::Unowed,
        }));
    report
        .findings
        .extend(present.into_iter().map(|path| ExemplarFinding {
            path,
            fault: ExemplarFault::Stray,
        }));
    Ok(())
}

/// Verify the diagnostics exemplar at `path` refuses with `subject`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Ok` exactly when the file reads, opens with a `///` comment
///   naming the subject, parses, lowers, and a declaration of it states
///   `refuses` with the subject's name or, for a boundary, is refused by the
///   lowering at that boundary.
/// - fails: the first check that does not hold.
/// - panics: none.
///
/// # Errors
/// [`ExemplarFault::Unreadable`], [`ExemplarFault::Uncommented`],
/// [`ExemplarFault::Unparsed`], [`ExemplarFault::Refused`] for a source the
/// lowering refuses whole, or [`ExemplarFault::Unrefused`].
///
/// # Adequacy
/// - hypothesis: L3 — every committed exemplar holds; one stating another name,
///   and one whose boundary declaration is not refused there, are unrefused.
/// - witness: `ledger::exemplars::tests::the_committed_exemplars_verify`
/// - witness: `ledger::exemplars::diagnostics::tests::an_exemplar_refuses_with_its_own_name`
#[spec(ensures: |ref ret| ret.is_ok() || matches!(*ret, Err(ExemplarFault::Unreadable(_) | ExemplarFault::Uncommented { .. } | ExemplarFault::Unparsed { .. } | ExemplarFault::Refused { .. } | ExemplarFault::Unrefused { .. })))]
fn refused(
    pbg: &Pbg,
    path: &Path,
    subject: Subject,
) -> Result<(), ExemplarFault>
{
    let text = std::fs::read_to_string(path).map_err(ExemplarFault::Unreadable)?;
    let named = format!("`{}`", subject.name());
    if !text
        .lines()
        .next()
        .is_some_and(|first| first.starts_with("///") && first.contains(&named))
    {
        return Err(ExemplarFault::Uncommented {
            subject: subject.to_string(),
        });
    }
    let parsed =
        parse(pbg, SourceText::from(text.as_str())).map_err(|error| ExemplarFault::Unparsed {
            error: error.to_string(),
        })?;
    let mut arena = CoreArena::new();
    let module = lower_module(
        pbg,
        parsed.tree(),
        &mut arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
    )
    .map_err(|refusal| ExemplarFault::Refused {
        refusal: refusal.to_string(),
    })?;
    let shown =
        module.declarations().iter().any(|declaration| {
            match subject {
        Subject::Named(name) => expected(CorpusRoot::Fixture, &arena, &module, declaration)
            .is_ok_and(|expectations| {
                matches!(
                    expectations.stated,
                    Stated::Verdict(Outcome::Refuses(stated) | Outcome::RefusesRunning(stated, _))
                        if stated == name
                )
            }),
        Subject::Boundary(wanted) => matches!(
            declaration.outcome(),
            DeclarationOutcome::Refused(LoweringRefusal::OutOfFragment { boundary, .. })
                if boundary == wanted
        ),
    }
        });
    if shown {
        Ok(())
    }
    else {
        Err(ExemplarFault::Unrefused {
            subject: subject.to_string(),
        })
    }
}

#[cfg(test)]
mod tests
{
    use std::path::Path;

    use super::DIAGNOSTICS;
    use super::Subject;
    use super::refused;
    use crate::ledger::exemplars::ExemplarFault;
    use crate::ledger::exemplars::tests::copied;
    use crate::ledger::exemplars::tests::named;
    use crate::ledger::exemplars::tests::verified;

    #[test]
    fn each_subject_pairs_with_one_exemplar_or_one_row()
    {
        let directory = copied(Path::new("diagnostics-paired"));
        let folder = directory.join(DIAGNOSTICS);
        std::fs::rename(
            folder.join("MissingPayload.gandr"),
            folder.join("MissingPayloads.gandr"),
        )
        .expect("the exemplar renames");
        std::fs::write(
            folder.join("UnknownMold.gandr"),
            "/// `UnknownMold`: owed and written.\n@[ refuses(\"UnknownMold\") ] def a = 1 ;\n",
        )
        .expect("the exemplar writes");
        let report = verified(&directory);
        assert_eq!(named(&report), [
            "MissingPayload.gandr: no exemplar for refusal `MissingPayload`",
            "UnknownMold.gandr: the owed table lists refusal `UnknownMold`, which has an exemplar",
            "MissingPayloads.gandr: names nothing the ledger lists",
        ]);
    }

    #[test]
    fn an_exemplar_refuses_with_its_own_name()
    {
        let pbg = gandr_surface_grammar::built_in().expect("the grammar builds");
        let directory = copied(Path::new("diagnostics-refused"));
        let folder = directory.join(DIAGNOSTICS);
        let written = |name: &str, text: &str| {
            let path = folder.join(name);
            std::fs::write(&path, text).expect("the exemplar writes");
            path
        };
        let other = written(
            "other.gandr",
            "/// `MissingPayload`: states another.\n@[ refuses(\"UnresolvedName\") ] def a = b ;\n",
        );
        let admitted = written(
            "admitted.gandr",
            "/// `OutOfFragment.Reserved`: refused at another boundary.\n@[ refuses(\"OutOfFragment.case_expression\") ]\ndef stated(x : Void) -> -F Integer { case x -> -F Integer {} }\n",
        );
        let unnamed = written(
            "unnamed.gandr",
            "/// Names nothing.\n@[ refuses(\"MissingPayload\") ]\n@[doc]\ndef f = 42;\n",
        );
        let subject = |name: &str| {
            Subject::every()
                .into_iter()
                .find(|subject| subject.name() == name)
                .expect("a subject")
        };

        assert!(matches!(
            refused(&pbg, &other, subject("MissingPayload")),
            Err(ExemplarFault::Unrefused { .. })
        ));
        assert!(matches!(
            refused(&pbg, &admitted, subject("OutOfFragment.Reserved")),
            Err(ExemplarFault::Unrefused { .. })
        ));
        assert!(matches!(
            refused(&pbg, &unnamed, subject("MissingPayload")),
            Err(ExemplarFault::Uncommented { .. })
        ));
    }
}
