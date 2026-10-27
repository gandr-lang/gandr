//! What one step prints, in order: its diagnostics and its ledger lines.
//!
//! # The verb decides, `shown` decides it
//!
//! Which declaration a verb prints, and whether as a goal, is [`shown`]; this
//! module reads it and nothing else. A declaration a verb prints that is
//! unsettled becomes a diagnostic built through
//! `gandr_surface_diagnostics::diagnose`; a settled fixture `test` prints, a
//! pending source's refusal and a pending source the lowering read are ledger
//! lines, diagnostics of severity `Ledger`, because they record a source's
//! standing rather than a fault in it.
//!
//! The walk owns this order because it owns the step: the diagnostics model
//! builds one diagnostic from one subject and names no verb. The alternative
//! was the walk in the model, which made the model depend on the dispatcher
//! and every face on both; reversal: a second walker, beside this one, that
//! prints steps in another order would move the selection beside the model.

use alloc::string::String;
use core::slice;
use std::path::Path;

use anodized::spec;
use gandr_core_checker::CheckRefusal;
use gandr_core_term::effect::Purity;
use gandr_surface_corpus::DeclarationReport;
use gandr_surface_corpus::Outcome;
use gandr_surface_corpus::Refusal;
use gandr_surface_corpus::Settlement;
use gandr_surface_corpus::Stated;
use gandr_surface_corpus::produced_refusal;
use gandr_surface_diagnostics::Diagnostic;
use gandr_surface_diagnostics::Failures;
use gandr_surface_diagnostics::Severity;
use gandr_surface_diagnostics::SourceStart;
use gandr_surface_diagnostics::Subject;
use gandr_surface_diagnostics::TypeSpellings;
use gandr_surface_diagnostics::Unsettlement;
use gandr_surface_diagnostics::diagnose;
use gandr_surface_diagnostics::report_span;
use gandr_surface_diagnostics::upstream;
use gandr_surface_lowering::AskedRuns;
use gandr_surface_lowering::DeprecatedUse;
use gandr_surface_lowering::Explicitness;
use gandr_surface_lowering::FragmentBoundary;
use gandr_surface_lowering::InferredExit;
use gandr_surface_lowering::InferredRun;
use gandr_surface_lowering::LoweringRefusal;
use gandr_surface_lowering::OriginTable;
use gandr_surface_lowering::namespace::ShadowedBuiltin;
use gandr_surface_pretty::Spelling;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::compose::Composed;
use crate::report::Lints;
use crate::report::Reach;
use crate::report::Shown;
use crate::report::Verb;
use crate::report::shown;
use crate::walk::Standing;
use crate::walk::Step;

quenchant_shape::reason_enum! {
    /// Why a declaration has no entry.
    mod unshown {
        /// The reason a declaration prints nothing.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The verb counts the declaration and prints no line for it.
            Counted,
        }
    }
}

/// What a ledger line records.
#[derive(Clone, Copy, Debug)]
enum Line<'step>
{
    /// A fixture that settled, printed by `test`.
    Fixture(&'step DeclarationReport<'step>),
    /// A refusal a pending source carries, printed by `test`.
    Pending(LoweringRefusal<'step>),
    /// A pending source the lowering read, carrying no refusal an expectation
    /// cannot state.
    Lowered,
}

impl Line<'_>
{
    /// The line as a ledger diagnostic of the source at `path`, which starts
    /// at `start` in `text`.
    ///
    /// # Specification
    /// - requires: `start` was taken of `text`.
    /// - ensures: a [`Severity::Ledger`] diagnostic whose message is the
    ///   settled fixture's report, the pending refusal with the bytes it stands
    ///   at, or the note that a pending source belongs under the fixture root,
    ///   each byte range in the message measured from `start`; the fixture and
    ///   the located refusal are annotated at their bytes in `text`.
    /// - provides: the ledger representation beside located diagnostics.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — fixture and pending-source lines expose their record
    ///   category and span through real walks, and an importer's fixture line
    ///   names bytes inside its own file.
    /// - witness: `entry::tests::each_verb_prints_its_entries`
    /// - witness: `entry::tests::an_importer_s_ledger_line_names_its_own_bytes`
    #[spec(ensures: |ref ret| ret.severity == Severity::Ledger)]
    fn diagnostic(
        self,
        path: &Path,
        text: SourceText<'_>,
        start: SourceStart,
    ) -> Diagnostic
    {
        let own = |span: ByteSpan| match start.measure(span) {
            Maybe::Present(own) => own,
            Maybe::Absent(_) => span,
        };
        let (line, at) = match self {
            Line::Fixture(declaration) => (
                alloc::format!("{}", declaration.at(own(declaration.span()))),
                Maybe::Present(declaration.span()),
            ),
            Line::Pending(refusal) => match refusal.span() {
                Maybe::Present(span) => (
                    alloc::format!("pending: {refusal} at {}", own(span)),
                    Maybe::Present(span),
                ),
                Maybe::Absent(_) => (
                    alloc::format!("pending: {refusal}"),
                    Maybe::Absent(report_span::Absent::Standing),
                ),
            },
            Line::Lowered => (
                String::from(
                    "unsettled: a pending source whose every expectation can be stated; it \
                     belongs under the fixture root",
                ),
                Maybe::Absent(report_span::Absent::Standing),
            ),
        };
        diagnose(path, text, Subject::Ledger { line: &line, at })
    }
}

/// What remains of one step to print.
#[derive(Clone, Debug)]
enum Cursor<'step>
{
    /// Nothing.
    Done,
    /// One last entry: a source refused as a whole, or a pending source's
    /// refusal of it as a whole.
    Last(Last<'step>),
    /// The note on a pending source the lowering read, then its declarations.
    Lowered(Remaining<'step>),
    /// The shadowing warnings, the lint findings and then the declarations
    /// still to visit.
    Declarations(Remaining<'step>),
    /// The refusals of a pending source still to print.
    Pending
    {
        /// The refusals no expectation can state.
        unstatable: slice::Iter<'step, LoweringRefusal<'step>>,
    },
}

/// The one entry a source refused as a whole prints.
#[derive(Clone, Copy, Debug)]
enum Last<'step>
{
    /// A pending source's refusal, as a ledger line.
    Line(LoweringRefusal<'step>),
    /// A source refused where its root expects declarations, as a refusal.
    Source(LoweringRefusal<'step>),
}

/// Which of a step's refusals its declarations print.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Refusals
{
    /// The refusals that leave their declaration unsettled: what a verb prints.
    #[default]
    Unsettling,
    /// Every refusal a declaration produced, one its expectation states too,
    /// as it would print unexpected: the text a rendered golden pins.
    Every,
}

/// The warnings and declarations of a settled composition still to visit.
#[derive(Clone, Debug)]
struct Remaining<'step>
{
    /// The builtins the source shadowed, warned of before its declarations;
    /// none under `test`.
    shadowed: slice::Iter<'step, ShadowedBuiltin>,
    /// The exits the lowering inferred, each a finding where a lint reaches,
    /// printed after the warnings; none under `test`.
    inferred: slice::Iter<'step, InferredExit>,
    /// The runs the checker inferred, each a finding where a lint reaches,
    /// printed after the exits; none under `test`.
    runs: slice::Iter<'step, InferredRun>,
    /// The uses of deprecated declarations, each a finding, printed after
    /// the runs; none under `test`.
    deprecated: slice::Iter<'step, DeprecatedUse<'step>>,
    /// How many declarations refused for their form are still to print
    /// before the rest; none under `test`.
    leading: usize,
    /// Where the last of them printed stands: its refusal's start, then its
    /// admission position. The next one printed stands after it.
    led: Option<(ByteOffset, usize)>,
    /// The declarations visited after the leading ones, in admission order:
    /// each one not refused for its form.
    declarations: slice::Iter<'step, DeclarationReport<'step>>,
    /// Every declaration of the source, visited or not: what a refusal naming
    /// an admission position is read against.
    admitted: &'step [DeclarationReport<'step>],
    /// The table their core nodes are located through.
    origins: &'step OriginTable,
    /// The spellings of the types their checker failures name, in each
    /// spelling.
    spellings: &'step TypeSpellings,
    /// The failures the checking machine kept, by admission position.
    failures: &'step Failures,
}

/// The diagnostics of one step, in the order its verb prints them.
#[derive(Clone, Debug)]
pub struct Entries<'step>
{
    /// The source's path.
    path: &'step Path,
    /// The text the step's spans are measured against.
    text: SourceText<'step>,
    /// Where the source's own text starts in `text`.
    start: SourceStart,
    /// The verb the walk runs under.
    verb: Verb,
    /// Where each lint reports its findings.
    lints: Lints,
    /// Which refusals the declarations print.
    refusals: Refusals,
    /// The spelling the types a diagnostic names are read in.
    spelling: Spelling,
    /// What remains.
    cursor: Cursor<'step>,
}

/// What `step` prints under `verb`, in order.
///
/// # Specification
/// - requires: nothing; every step is admissible.
/// - ensures: a fault prints nothing here: its line is the caller's. A source
///   the lowering refused as a whole where its root expects declarations is one
///   refusal diagnostic. A pending source prints its refusals under `test`, as
///   ledger lines, and nothing under `check`. A pending source the lowering
///   read prints its ledger line, then its declarations as any source does.
///   Under `check`, a source the lowering read first prints a warning for each
///   builtin it shadowed, in the order shadowed, then a finding for each exit
///   the lowering inferred where an attribute asks for it, then one for each
///   run the checker inferred where an attribute asks for it, then one for each
///   use of a deprecated declaration, each in source order
///   ([`Entries::linting`] widens where a lint reaches); `test` prints none.
///   Each declaration is printed as [`shown`] decides under `verb`: nothing
///   when it is counted; a goal when it is a goal; when it has a line, a ledger
///   line if it settled, a refusal if it produced one, and an unsettled
///   diagnostic otherwise. Under `check`, the declarations refused for their
///   form ([`lead`]) print first, in the order their refusals stand in the
///   source, then the rest in admission order; under `test`, declarations keep
///   admission order.
/// - provides: the one pass a face prints a step through, so no refusal a step
///   carries can reach the walk without reaching a face.
/// - fails: never.
/// - panics: none.
/// - intension: borrows the step; builds each diagnostic as it is reached.
///
/// # Adequacy
/// - hypothesis: L3 — finite real steps under every verb expose entry category
///   and admission order. Interleaved counted declarations and an empty source
///   exercise progress and exhaustion; an empty-path fault exercises silence.
///   Other malformed step/standing combinations are not enumerated by these
///   fixtures.
/// - witness: `entry::tests::each_verb_prints_its_entries`
/// - witness: `entry::tests::a_refusal_of_form_prints_before_one_resting_on_it_2875`
/// - witness: `entry::tests::a_shadowed_builtin_is_warned_of_under_check_alone`
/// - witness: `entry::tests::an_inferred_exit_is_reported_where_a_lint_reaches`
/// - witness: `entry::tests::an_inferred_run_is_reported_where_a_lint_reaches`
/// - witness: `entry::tests::each_use_of_a_deprecated_declaration_is_a_finding`
/// - witness: `entry::tests::counted_declarations_preserve_visible_order_and_exhaustion`
/// - witness: `entry::tests::faults_and_empty_sources_stay_exhausted`
#[spec(ensures: |ref ret| ret.verb == verb && ret.lints == Lints::default() && ret.refusals == Refusals::Unsettling && ret.spelling == Spelling::Unicode && match *step {
    Step::Fault { path, .. } => core::ptr::eq(core::ptr::from_ref(ret.path), core::ptr::from_ref(path))
        && ret.text.as_ref().is_empty() && matches!(ret.cursor, Cursor::Done),
    Step::Source { path, text, .. } => core::ptr::eq(core::ptr::from_ref(ret.path), core::ptr::from_ref(path)) && core::ptr::eq(core::ptr::from_ref(ret.text.as_ref()), core::ptr::from_ref(text.as_ref())),
})]
#[inline]
#[must_use]
pub fn entries<'step>(
    step: &'step Step<'step>,
    verb: Verb,
) -> Entries<'step>
{
    let (path, text, base, cursor) = match *step {
        Step::Fault { path, .. } => (
            path,
            SourceText::from(""),
            ByteOffset::from(0_usize),
            Cursor::Done,
        ),
        Step::Source {
            path,
            text,
            base,
            ref composed,
            standing,
            ..
        } => (path, text, base, cursor(verb, standing, composed)),
    };
    Entries {
        path,
        text,
        start: SourceStart::of(text, base),
        verb,
        lints: Lints::default(),
        refusals: Refusals::Unsettling,
        spelling: Spelling::Unicode,
        cursor,
    }
}

/// The first cursor over a source that became `composed`.
///
/// # Specification
/// - requires: nothing; any standing and composition are admissible.
/// - ensures: pending refusals are ledger lines only under test; other
///   whole-source refusals are refusals. A lowered source starts with its
///   ledger line; other settled compositions start at their declarations, after
///   their shadowing warnings, inferred exits, inferred runs and deprecated
///   uses under `check`. Borrowed declaration, warning, inferred-exit,
///   inferred-run, deprecated-use and refusal slices retain their complete
///   order.
/// - provides: the first state of a lazy entry traversal.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — finite source roots under every verb distinguish
///   ledger/report selection and declaration admission. Empty settled
///   compositions expose the zero-length slice boundary. Contradictory
///   standing/composition pairs are outside the produced-step witnesses.
/// - witness: `entry::tests::each_verb_prints_its_entries`
/// - witness: `entry::tests::faults_and_empty_sources_stay_exhausted`
/// - witness: `entry::tests::a_shadowed_builtin_is_warned_of_under_check_alone`
#[spec(ensures: |ref ret| match (standing, composed, ret) {
    (Standing::Pending, _, &Cursor::Done) => matches!(verb, Verb::Check(_)),
    (Standing::Pending, &Composed::Refused(expected), &Cursor::Last(Last::Line(refusal))) =>
        verb == Verb::Test && refusal == expected,
    (Standing::Pending, expected, actual) => {
        let Composed::Settled { ref unstatable, .. } = *expected else { return false; };
        let Cursor::Pending { unstatable: ref held } = *actual else { return false; };
        verb == Verb::Test && core::ptr::eq(core::ptr::from_ref(held.as_slice()), core::ptr::from_ref(unstatable.as_slice()))
    },
    (Standing::Settled | Standing::Unsettled | Standing::Refused | Standing::Lowered,
        &Composed::Refused(expected), &Cursor::Last(Last::Source(refusal))) => refusal == expected,
    (Standing::Lowered, &Composed::Settled { ref report, ref origins, ref spellings, ref failures, ref shadowed, ref inferred, ref runs, ref deprecated, .. },
        &Cursor::Lowered(ref held))
    | (Standing::Settled | Standing::Unsettled | Standing::Refused,
        &Composed::Settled { ref report, ref origins, ref spellings, ref failures, ref shadowed, ref inferred, ref runs, ref deprecated, .. },
        &Cursor::Declarations(ref held)) =>
        held.leading == report.declarations().iter().filter(|declaration| lead(verb, declaration) != Lead::Rest).count()
            && held.led.is_none()
            && core::ptr::eq(core::ptr::from_ref(held.declarations.as_slice()), core::ptr::from_ref(report.declarations()))
            && match verb {
                Verb::Check(_) => core::ptr::eq(core::ptr::from_ref(held.shadowed.as_slice()), core::ptr::from_ref(shadowed.as_slice()))
                    && core::ptr::eq(core::ptr::from_ref(held.inferred.as_slice()), core::ptr::from_ref(inferred.as_slice()))
                    && core::ptr::eq(core::ptr::from_ref(held.runs.as_slice()), core::ptr::from_ref(runs.as_slice()))
                    && core::ptr::eq(core::ptr::from_ref(held.deprecated.as_slice()), core::ptr::from_ref(deprecated.as_slice())),
                Verb::Test => held.shadowed.as_slice().is_empty() && held.inferred.as_slice().is_empty()
                    && held.runs.as_slice().is_empty() && held.deprecated.as_slice().is_empty(),
            }
            && core::ptr::eq(core::ptr::from_ref(held.origins), core::ptr::from_ref(origins))
            && core::ptr::eq(core::ptr::from_ref(held.spellings), core::ptr::from_ref(spellings))
            && core::ptr::eq(core::ptr::from_ref(held.failures), core::ptr::from_ref(failures)),
    _ => false,
})]
fn cursor<'step>(
    verb: Verb,
    standing: Standing,
    composed: &'step Composed<'step>,
) -> Cursor<'step>
{
    match (standing, composed) {
        (Standing::Pending, &Composed::Refused(refusal)) => match verb {
            Verb::Test => Cursor::Last(Last::Line(refusal)),
            Verb::Check(_) => Cursor::Done,
        },
        (Standing::Pending, &Composed::Settled { ref unstatable, .. }) => match verb {
            Verb::Test => Cursor::Pending {
                unstatable: unstatable.iter(),
            },
            Verb::Check(_) => Cursor::Done,
        },
        (
            Standing::Settled | Standing::Unsettled | Standing::Refused | Standing::Lowered,
            &Composed::Refused(refusal),
        ) => Cursor::Last(Last::Source(refusal)),
        (
            standing @ (Standing::Lowered
            | Standing::Settled
            | Standing::Unsettled
            | Standing::Refused),
            &Composed::Settled {
                ref report,
                ref origins,
                ref spellings,
                ref failures,
                ref shadowed,
                ref inferred,
                ref runs,
                ref deprecated,
                ..
            },
        ) => {
            let held = Remaining {
                shadowed: warned(verb, shadowed),
                inferred: considered(verb, inferred),
                runs: considered(verb, runs),
                deprecated: considered(verb, deprecated),
                leading: report
                    .declarations()
                    .iter()
                    .filter(|declaration| lead(verb, declaration) != Lead::Rest)
                    .count(),
                led: None,
                declarations: report.declarations().iter(),
                admitted: report.declarations(),
                origins,
                spellings,
                failures,
            };
            if standing == Standing::Lowered {
                Cursor::Lowered(held)
            }
            else {
                Cursor::Declarations(held)
            }
        },
    }
}

/// Where a declaration prints among a source's entries.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Lead
{
    /// In the leading pass, refused for its form at this byte of the source.
    Form(ByteOffset),
    /// After the leading pass, in admission order.
    Rest,
}

/// Where `declaration` prints under `verb`: under `check`, a declaration the
/// lowering refused for its form leads, at its refusal's start.
///
/// A form the parser repaired, or one written where its position takes
/// another (a form of another sort, an expression at the top level, a form
/// admitted only elsewhere), is the mistake the author made. A refusal
/// elsewhere can rest on what the repair left (a member it dropped, a name it
/// moved out of scope), and printing that one first reports the consequence
/// as the mistake (#2875).
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Lead::Form` at the refusal's start exactly when `verb` is
///   `check` and `declaration` produced a `MalformedForm` refusal or an
///   `OutOfFragment` refusal at the `WrongSort`, `TopLevel` or `Misplaced`
///   boundary; `Lead::Rest` otherwise.
/// - provides: the partition [`entries`] prints a source's declarations in, and
///   the order of its leading pass.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a source whose consequent refusal is admitted before the
///   repaired form prints the repaired form first under `check`, and the
///   refusals of form in source order.
/// - witness: `entry::tests::a_refusal_of_form_prints_before_one_resting_on_it_2875`
#[spec(ensures: |ret| matches!(ret, Lead::Form(_)) == (matches!(verb, Verb::Check(_)) && matches!(
    declaration.produced().refusal(),
    Maybe::Present(Refusal::Lowering(
        LoweringRefusal::MalformedForm { .. }
            | LoweringRefusal::OutOfFragment {
                boundary: FragmentBoundary::WrongSort | FragmentBoundary::TopLevel | FragmentBoundary::Misplaced,
                ..
            }
    ))
)))]
fn lead(
    verb: Verb,
    declaration: &DeclarationReport<'_>,
) -> Lead
{
    if !matches!(verb, Verb::Check(_)) {
        return Lead::Rest;
    }
    match declaration.produced().refusal() {
        Maybe::Present(Refusal::Lowering(
            refusal @ (LoweringRefusal::MalformedForm { .. }
            | LoweringRefusal::OutOfFragment {
                boundary:
                    FragmentBoundary::WrongSort
                    | FragmentBoundary::TopLevel
                    | FragmentBoundary::Misplaced,
                ..
            }),
        )) => match refusal.span() {
            Maybe::Present(span) => Lead::Form(span.start()),
            Maybe::Absent(_) => Lead::Rest,
        },
        Maybe::Present(_) | Maybe::Absent(_) => Lead::Rest,
    }
}

/// The unsettled declaration `refusal` names, among `admitted`: the
/// declaration a refusal of its own left unsettled, which the refusal follows
/// from.
///
/// A checker that meets a constant whose declaration was refused has no type
/// to read it at, and refuses the declaration naming it; that refusal is the
/// first one's consequence, and reporting it as a second error puts red where
/// the author has nothing to fix. It is reported as a note naming the refused
/// declaration instead. rust-analyzer draws the same line between the errors
/// a source earns and those an earlier error causes, which it does not
/// report.
///
/// # Specification
/// - requires: `admitted` is the source's declarations, by admission position.
/// - ensures: the declaration of `admitted` whose constant an `UnknownConstant`
///   refusal names, when it is unsettled; absent for every other refusal and
///   for a settled or unadmitted constant.
/// - provides: the cascade cut across declarations.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a declaration calling one the lowering refused is a note
///   naming it, not another refused before it, and one calling a declaration
///   that checks is not.
/// - witness: `entry::tests::a_declaration_naming_a_refused_one_is_a_note`
/// - witness: `entry::tests::a_note_names_the_refused_declaration_it_rests_on`
#[spec(ensures: |ret| match ret {
    Maybe::Present(found) => found.settlement() == Settlement::Unsettled,
    Maybe::Absent(_) => true,
})]
fn upstream<'step>(
    refusal: Refusal<'step>,
    admitted: &'step [DeclarationReport<'step>],
) -> Maybe<&'step DeclarationReport<'step>, upstream::Absent>
{
    let Refusal::Checking(CheckRefusal::UnknownConstant { constant, .. }) = refusal
    else {
        return Maybe::Absent(upstream::Absent::Own);
    };
    admitted
        .iter()
        .find(|declaration| {
            declaration.constant() == constant && declaration.settlement() == Settlement::Unsettled
        })
        .map_or(Maybe::Absent(upstream::Absent::Own), Maybe::Present)
}

/// The refused declaration of `declaration`'s name, among `admitted`, when
/// `declaration` is unsettled by what it owes: the half the lowering could not
/// read.
///
/// A definition written with its keyword misspelt, `de pair = …;`, does not
/// read as the half a signature `def pair : T;` pairs with: the lowering
/// refuses the form, a run of declarations one of which is named `pair`, and
/// the signature owes its body.
/// What the signature owes is that refusal's consequence, so it is a note
/// naming the refused form, and the first error is where the source went
/// wrong (#2339). A refused form of the declaration's name is the evidence
/// that ties the two; a signature owing its body beside no such form is its
/// own error.
///
/// # Specification
/// - requires: `admitted` is the source's declarations, by admission position.
/// - ensures: the first declaration of `admitted` other than `declaration` that
///   shares its name and produced a lowering refusal, when `unsettlement` is
///   [`Unsettlement::Obligations`]; absent otherwise.
/// - provides: the cascade cut between a declaration's two halves.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a signature whose definition's keyword is misspelt is a
///   note, and the misspelt keyword the first error.
/// - witness: `entry::tests::a_declaration_whose_other_half_is_refused_is_a_note_2339`
#[spec(ensures: |ret| match ret {
    Maybe::Present(found) => found.name() == declaration.name()
        && matches!(found.produced().refusal(), Maybe::Present(Refusal::Lowering(_))),
    Maybe::Absent(_) => true,
})]
fn unread_half<'step>(
    declaration: &'step DeclarationReport<'step>,
    unsettlement: Unsettlement,
    admitted: &'step [DeclarationReport<'step>],
) -> Maybe<&'step DeclarationReport<'step>, upstream::Absent>
{
    if unsettlement != Unsettlement::Obligations {
        return Maybe::Absent(upstream::Absent::Own);
    }
    admitted
        .iter()
        .find(|other| {
            !core::ptr::eq(
                core::ptr::from_ref(*other),
                core::ptr::from_ref(declaration),
            ) && other.name() == declaration.name()
                && matches!(
                    other.produced().refusal(),
                    Maybe::Present(Refusal::Lowering(_))
                )
        })
        .map_or(Maybe::Absent(upstream::Absent::Own), Maybe::Present)
}

/// The shadowing warnings `verb` prints of `shadowed`: every one under
/// `check`, none under `test`, whose ledger records settlements alone.
///
/// # Specification
/// trivial.
fn warned(
    verb: Verb,
    shadowed: &[ShadowedBuiltin],
) -> slice::Iter<'_, ShadowedBuiltin>
{
    match verb {
        Verb::Check(_) => shadowed.iter(),
        Verb::Test => [].iter(),
    }
}

/// The findings `verb` considers of `found`: every one under `check`, none
/// under `test`, whose ledger records settlements alone.
///
/// # Specification
/// trivial.
fn considered<Finding>(
    verb: Verb,
    found: &[Finding],
) -> slice::Iter<'_, Finding>
{
    match verb {
        Verb::Check(_) => found.iter(),
        Verb::Test => [].iter(),
    }
}

/// Whether an ask covers a run, so a finding is reported.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Asked(bool);

/// Whether `asked` asks for a run of `purity` to be written.
///
/// # Specification
/// - requires: nothing.
/// - ensures: no run when nothing asks, every run when every run is asked for,
///   and only an effectful one under the `effects` option.
/// - provides: the one place the `effects` option filters a finding.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a pure and an effectful run under each ask, printed or
///   not.
/// - witness: `entry::tests::an_inferred_run_is_reported_where_a_lint_reaches`
#[spec(ensures: |ret| ret.0 == (asked == AskedRuns::Every || (asked == AskedRuns::Effectful && purity == Purity::Effectful)))]
fn asks(
    asked: AskedRuns,
    purity: Purity,
) -> Asked
{
    Asked(match asked {
        AskedRuns::Unasked => false,
        AskedRuns::Effectful => purity == Purity::Effectful,
        AskedRuns::Every => true,
    })
}

/// What a declaration's diagnostic is about, when its verb prints it.
#[derive(Clone, Copy, Debug)]
enum Printed<'step>
{
    /// A ledger line.
    Line(Line<'step>),
    /// A diagnostic built from its subject.
    Subject(Subject<'step>),
}

impl<'step> Entries<'step>
{
    /// These entries, each lint reaching where `lints` says.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the same entries, printing each lint's findings where `lints`
    ///   reaches, attribute or not; [`entries`] reaches only the forms an
    ///   attribute enables a lint on, and prints the `deprecated` lint's
    ///   findings wherever they stand, which `lints` neither widens nor
    ///   narrows.
    /// - provides: the driver's `--lint` flags, read where a step is printed.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an asked and an unasked inferred exit, under the
    ///   default and under `explicit-exits` enabled, each printed or not.
    /// - witness: `entry::tests::an_inferred_exit_is_reported_where_a_lint_reaches`
    #[spec(ensures: |ref ret| ret.lints == lints)]
    #[inline]
    #[must_use]
    pub fn linting(
        mut self,
        lints: Lints,
    ) -> Self
    {
        self.lints = lints;
        self
    }

    /// These entries, each type a diagnostic names read in `spelling`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the same entries, every type a refusal compares or its
    ///   failure names spelled in `spelling`; [`entries`] reads them in
    ///   [`Spelling::Unicode`].
    /// - provides: the reader's spelling, read where a step is printed.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a mismatch between two relations, printed in each
    ///   spelling.
    /// - witness: `entry::tests::a_refusal_names_its_types_in_the_spelling_asked_782`
    #[spec(ensures: |ref ret| ret.spelling == spelling)]
    #[inline]
    #[must_use]
    pub fn spelling(
        mut self,
        spelling: Spelling,
    ) -> Self
    {
        self.spelling = spelling;
        self
    }

    /// These entries, printing the refusals `refusals` selects.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the same entries, in the same order, except that under
    ///   [`Refusals::Every`] a settled declaration that produced a refusal
    ///   prints that refusal as an unsettled one does, under every verb;
    ///   [`entries`] prints [`Refusals::Unsettling`].
    /// - provides: the rendered text of an expected refusal, which no verb
    ///   prints.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fixture whose expectation states its refusal prints
    ///   nothing under `check` and its refusal under `Refusals::Every`, the
    ///   same text an unexpected one prints.
    /// - witness: `entry::tests::an_expected_refusal_prints_as_an_unexpected_one_when_every_refusal_is_asked`
    #[spec(ensures: |ref ret| ret.refusals == refusals)]
    #[inline]
    #[must_use]
    pub fn refusals(
        mut self,
        refusals: Refusals,
    ) -> Self
    {
        self.refusals = refusals;
        self
    }

    /// What `declaration` prints, when its verb prints it.
    ///
    /// # Specification
    /// - requires: the declaration, origins, spellings and failures belong to
    ///   this entry stream.
    /// - ensures: under [`Refusals::Every`], a settled declaration that
    ///   produced a refusal is that refusal's subject, as an unsettled one is.
    ///   Otherwise counted declarations print nothing; goals are goal subjects.
    ///   A shown settled declaration is a fixture ledger line; an unsettled
    ///   declaration is a refusal subject, carrying the failure the machine
    ///   kept for it, when one was produced, otherwise an unsettled subject
    ///   naming the failed expectation.
    /// - provides: verb-directed selection without changing declaration order.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — finite real declarations distinguish counted, goal
    ///   and ledger selection from refused or unproduced expectations. Ordered
    ///   refusal spans expose skipping and substitution. Run-result mismatches
    ///   and malformed expectations are not enumerated by these fixtures.
    /// - witness: `entry::tests::each_verb_prints_its_entries`
    /// - witness: `entry::tests::counted_declarations_preserve_visible_order_and_exhaustion`
    /// - witness: `entry::tests::an_expected_refusal_prints_as_an_unexpected_one_when_every_refusal_is_asked`
    #[spec(ensures: |ref ret| match (shown(declaration, self.verb), ret) {
        (_, &Maybe::Present(Printed::Subject(Subject::Refused { refusal, .. })))
            if self.refusals == Refusals::Every && declaration.settlement() == Settlement::Settled =>
            declaration.produced().refusal() == Maybe::Present(refusal),
        (Shown::Counted, &Maybe::Absent(unshown::Absent::Counted)) => true,
        (Shown::Goal, &Maybe::Present(Printed::Subject(Subject::Goal(held)))) =>
            core::ptr::eq(core::ptr::from_ref(held), core::ptr::from_ref(declaration)),
        (Shown::Line, &Maybe::Present(Printed::Line(Line::Fixture(held)))) =>
            declaration.settlement() == Settlement::Settled
                && core::ptr::eq(core::ptr::from_ref(held), core::ptr::from_ref(declaration)),
        (Shown::Line, &Maybe::Present(Printed::Subject(Subject::Refused { refusal, .. }))) =>
            declaration.settlement() == Settlement::Unsettled
                && declaration.produced().refusal() == Maybe::Present(refusal),
        (Shown::Line, &Maybe::Present(Printed::Subject(Subject::Unsettled { .. }))) =>
            declaration.settlement() == Settlement::Unsettled
                && declaration.produced().refusal() == Maybe::Absent(produced_refusal::Absent::Unrefused),
        _ => false,
    })]
    fn declaration(
        &self,
        declaration: &'step DeclarationReport<'step>,
        held: &Remaining<'step>,
    ) -> Maybe<Printed<'step>, unshown::Absent>
    {
        if self.refusals == Refusals::Every
            && declaration.settlement() == Settlement::Settled
            && let Maybe::Present(refusal) = declaration.produced().refusal()
        {
            return Maybe::Present(Printed::Subject(self.refused(declaration, refusal, held)));
        }
        Maybe::Present(
            match (shown(declaration, self.verb), declaration.settlement()) {
                (Shown::Counted, _) => return Maybe::Absent(unshown::Absent::Counted),
                (Shown::Line, Settlement::Settled) => Printed::Line(Line::Fixture(declaration)),
                (Shown::Goal, _) => Printed::Subject(Subject::Goal(declaration)),
                (Shown::Line, Settlement::Unsettled) => {
                    Printed::Subject(match declaration.produced().refusal() {
                        Maybe::Present(refusal) => self.refused(declaration, refusal, held),
                        Maybe::Absent(produced_refusal::Absent::Unrefused) => {
                            let unsettlement = match (declaration.stated(), declaration.outcome()) {
                                (&Stated::Verdict(Outcome::Checks(_)), _)
                                | (
                                    &Stated::Verdict(
                                        Outcome::Runs(_)
                                        | Outcome::Normalizes(_)
                                        | Outcome::Decomposes(_),
                                    ),
                                    Outcome::Checks(_),
                                ) => Unsettlement::Obligations,
                                (
                                    &Stated::Verdict(
                                        Outcome::Refuses(_) | Outcome::RefusesRunning(..),
                                    ),
                                    _,
                                ) => Unsettlement::Unproduced,
                                (
                                    &Stated::Verdict(Outcome::Runs(_) | Outcome::Decomposes(_)),
                                    Outcome::Runs(_)
                                    | Outcome::Refuses(_)
                                    | Outcome::Normalizes(_)
                                    | Outcome::Decomposes(_)
                                    | Outcome::RefusesRunning(..),
                                ) => Unsettlement::RunOutcome,
                                (
                                    &Stated::Verdict(Outcome::Normalizes(_)),
                                    Outcome::Normalizes(_)
                                    | Outcome::Refuses(_)
                                    | Outcome::Runs(_)
                                    | Outcome::Decomposes(_)
                                    | Outcome::RefusesRunning(..),
                                ) => Unsettlement::NormalForm,
                                (&Stated::Malformed(_), _) => Unsettlement::Malformed,
                            };
                            Subject::Unsettled {
                                declaration,
                                unsettlement,
                                upstream: unread_half(declaration, unsettlement, held.admitted),
                            }
                        },
                    })
                },
            },
        )
    }

    /// The subject of `declaration`'s `refusal`, with what the step holds of
    /// it.
    ///
    /// # Specification
    /// trivial.
    fn refused(
        &self,
        declaration: &'step DeclarationReport<'step>,
        refusal: Refusal<'step>,
        held: &Remaining<'step>,
    ) -> Subject<'step>
    {
        Subject::Refused {
            declaration,
            refusal,
            origins: held.origins,
            spellings: held.spellings.spelled(self.spelling),
            failure: held.failures.get(declaration.constant()),
            upstream: upstream(refusal, held.admitted),
        }
    }

    /// The diagnostic `printed` makes at this step's source.
    ///
    /// # Specification
    /// trivial.
    fn build(
        &self,
        printed: Printed<'_>,
    ) -> Diagnostic
    {
        match printed {
            Printed::Line(line) => line.diagnostic(self.path, self.text, self.start),
            Printed::Subject(subject) => diagnose(self.path, self.text, subject),
        }
    }
}

impl Iterator for Entries<'_>
{
    type Item = Diagnostic;

    /// The next diagnostic, in the order [`entries`] states.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each yielded diagnostic belongs to the source and consumes at
    ///   least one remaining candidate. Hidden declarations are skipped without
    ///   ending the traversal. Exhaustion remains exhausted on every subsequent
    ///   call.
    /// - provides: declaration order (under `check`, refusals of form first),
    ///   preceded by a lowered-source ledger line when present and by the
    ///   source's warnings and lint findings; pending refusals retain their
    ///   source order.
    /// - fails: never; exhaustion is None.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — interleaved counted and refused declarations expose
    ///   premature stopping or reordering; empty sources and faults expose
    ///   false entries and resurrection after exhaustion. Finite pending
    ///   fixtures exercise ledger selection, not arbitrary long refusal
    ///   sequences.
    /// - witness: `entry::tests::each_verb_prints_its_entries`
    /// - witness: `entry::tests::counted_declarations_preserve_visible_order_and_exhaustion`
    /// - witness: `entry::tests::faults_and_empty_sources_stay_exhausted`
    /// - witness: `entry::tests::an_inferred_exit_is_reported_where_a_lint_reaches`
    #[spec(
        captures: [before = match self.cursor {
            Cursor::Done => 0_usize,
            Cursor::Last(_) => 1_usize,
            Cursor::Lowered(ref held) => held.shadowed.len().saturating_add(held.inferred.len()).saturating_add(held.runs.len()).saturating_add(held.deprecated.len()).saturating_add(held.leading).saturating_add(held.declarations.len()).saturating_add(1_usize),
            Cursor::Declarations(ref held) => held.shadowed.len().saturating_add(held.inferred.len()).saturating_add(held.runs.len()).saturating_add(held.deprecated.len()).saturating_add(held.leading).saturating_add(held.declarations.len()),
            Cursor::Pending { ref unstatable } => unstatable.len(),
        }],
        ensures: |ref ret| {
            let remaining = match self.cursor {
                Cursor::Done => 0_usize,
                Cursor::Last(_) => 1_usize,
                Cursor::Lowered(ref held) => held.shadowed.len().saturating_add(held.inferred.len()).saturating_add(held.runs.len()).saturating_add(held.deprecated.len()).saturating_add(held.leading).saturating_add(held.declarations.len()).saturating_add(1_usize),
                Cursor::Declarations(ref held) => held.shadowed.len().saturating_add(held.inferred.len()).saturating_add(held.runs.len()).saturating_add(held.deprecated.len()).saturating_add(held.leading).saturating_add(held.declarations.len()),
                Cursor::Pending { ref unstatable } => unstatable.len(),
            };
            ret.as_ref().map_or(remaining == 0_usize, |diagnostic| remaining < before && diagnostic.path.as_path() == self.path)
        },
    )]
    #[inline]
    fn next(&mut self) -> Option<Self::Item>
    {
        let start = self.start;
        self.reached().map(|diagnostic| diagnostic.rebased(start))
    }
}

impl Entries<'_>
{
    /// The next diagnostic, measured against the step's whole text.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`Entries::next`], before the diagnostic is measured from
    ///   the source's own start.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the witnesses of [`Entries::next`], and an inferred
    ///   exit and run each reported where its attribute or the run's lints
    ///   reach, and only there.
    /// - witness: `entry::tests::each_verb_prints_its_entries`
    /// - witness: `entry::tests::an_inferred_exit_is_reported_where_a_lint_reaches`
    /// - witness: `entry::tests::an_inferred_run_is_reported_where_a_lint_reaches`
    #[spec(ensures: |ref ret| ret.as_ref().is_none_or(|diagnostic| diagnostic.path.as_path() == self.path))]
    fn reached(&mut self) -> Option<Diagnostic>
    {
        match core::mem::replace(&mut self.cursor, Cursor::Done) {
            Cursor::Done => None,
            Cursor::Last(Last::Line(refusal)) => {
                Some(Line::Pending(refusal).diagnostic(self.path, self.text, self.start))
            },
            Cursor::Last(Last::Source(refusal)) => {
                Some(diagnose(self.path, self.text, Subject::Source(refusal)))
            },
            Cursor::Lowered(held) => {
                self.cursor = Cursor::Declarations(held);
                Some(Line::Lowered.diagnostic(self.path, self.text, self.start))
            },
            Cursor::Pending { mut unstatable } => {
                let line = unstatable.next().map(|&refusal| Line::Pending(refusal));
                self.cursor = Cursor::Pending { unstatable };
                line.map(|line| line.diagnostic(self.path, self.text, self.start))
            },
            Cursor::Declarations(mut held) => {
                if let Some(warned) = held.shadowed.next() {
                    self.cursor = Cursor::Declarations(held);
                    return Some(diagnose(self.path, self.text, Subject::Shadowed(warned)));
                }
                while let Some(inferred) = held.inferred.next() {
                    if inferred.explicitness == Explicitness::Asked
                        || self.lints.explicit_exits() == Reach::Everywhere
                    {
                        self.cursor = Cursor::Declarations(held);
                        return Some(diagnose(
                            self.path,
                            self.text,
                            Subject::InferredExit(inferred),
                        ));
                    }
                }
                while let Some(inferred) = held.runs.next() {
                    if asks(
                        inferred.site.asked.max(self.lints.explicit_runs()),
                        inferred.purity,
                    )
                    .0
                    {
                        self.cursor = Cursor::Declarations(held);
                        return Some(diagnose(
                            self.path,
                            self.text,
                            Subject::InferredRun(inferred),
                        ));
                    }
                }
                if let Some(used) = held.deprecated.next() {
                    self.cursor = Cursor::Declarations(held);
                    return Some(diagnose(self.path, self.text, Subject::Deprecated(used)));
                }
                let verb = self.verb;
                while held.leading > 0 {
                    held.leading = held.leading.saturating_sub(1);
                    let led = held.led;
                    let Some((place, declaration)) = held
                        .admitted
                        .iter()
                        .enumerate()
                        .filter_map(|(index, declaration)| match lead(verb, declaration) {
                            Lead::Form(at) => Some(((at, index), declaration)),
                            Lead::Rest => None,
                        })
                        .filter(|&(place, _)| led.is_none_or(|led| place > led))
                        .min_by_key(|&(place, _)| place)
                    else {
                        break;
                    };
                    held.led = Some(place);
                    if let Maybe::Present(printed) = self.declaration(declaration, &held) {
                        let diagnostic = self.build(printed);
                        self.cursor = Cursor::Declarations(held);
                        return Some(diagnostic);
                    }
                }
                while let Some(declaration) = held.declarations.next() {
                    if lead(verb, declaration) == Lead::Rest
                        && let Maybe::Present(printed) = self.declaration(declaration, &held)
                    {
                        let diagnostic = self.build(printed);
                        self.cursor = Cursor::Declarations(held);
                        return Some(diagnostic);
                    }
                }
                None
            },
        }
    }
}

/// Entry policy through real composition and the walk's fault boundary.
#[cfg(test)]
mod tests
{
    use core::convert::Infallible;
    use core::ops::ControlFlow;
    use std::path::Path;
    use std::path::PathBuf;

    use gandr_core_term::effect::Purity;
    use gandr_surface_diagnostics::Class;
    use gandr_surface_diagnostics::Lint;
    use gandr_surface_diagnostics::Severity;
    use gandr_surface_grammar::built_in;
    use gandr_surface_pretty::Spelling;
    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::ByteSpan;
    use gandr_surface_syntax::SourceText;
    use quenchant_shape::shape::Maybe;

    use super::Entries;
    use super::entries;
    use crate::Goals;
    use crate::Lints;
    use crate::LoweringCount;
    use crate::Pool;
    use crate::Refusals;
    use crate::SourceRoot;
    use crate::Standing;
    use crate::Step;
    use crate::Verb;
    use crate::Walk;
    use crate::Width;
    use crate::compose;
    use crate::walk::tests::Scratch;

    /// The step a source at `path` under `root` with `standing` makes.
    ///
    /// # Specification
    /// trivial.
    fn step<'text>(
        path: &'text Path,
        root: SourceRoot,
        text: SourceText<'text>,
        standing: Standing,
        grammar: &'text gandr_surface_grammar::Pbg,
    ) -> Step<'text>
    {
        Step::Source {
            path,
            root,
            text,
            base: ByteOffset::from(0_usize),
            composed: compose(
                grammar,
                root.corpus_root(),
                text,
                &mut LoweringCount::default(),
            )
            .expect("the source composes"),
            standing,
        }
    }

    #[test]
    fn each_verb_prints_its_entries()
    {
        let grammar = built_in().expect("the grammar builds");
        let fixture = SourceText::from(
            "def good = 1 ;\n@[ refuses(\"UnresolvedName\") ] def bad = missing ;\n",
        );
        let settled = step(
            Path::new("fixtures/pair.gandr"),
            SourceRoot::Fixture,
            fixture,
            Standing::Settled,
            &grammar,
        );
        let lines: Vec<String> = entries(&settled, Verb::Test)
            .map(|diagnostic| {
                assert_eq!(diagnostic.severity, Severity::Ledger);
                diagnostic.message.text
            })
            .collect();
        assert_eq!(
            lines,
            [
                "settled `bad` at 46..65: states refuses UnresolvedName; produced refuses \
              UnresolvedName (malformed source)"
            ],
            "test prints a line for the fixture that states a verdict, and counts the rest"
        );
        assert!(
            entries(&settled, Verb::Check(Goals::Gated))
                .next()
                .is_none(),
            "check prints nothing for a settled fixture"
        );

        let strict = SourceText::from("def bad = missing ;\n");
        let refused = step(
            Path::new("bad.gandr"),
            SourceRoot::Strict,
            strict,
            Standing::Unsettled,
            &grammar,
        );
        let printed: Vec<_> = entries(&refused, Verb::Check(Goals::Gated)).collect();
        assert_eq!(printed.len(), 1_usize);
        assert_eq!(printed[0].severity, Severity::Error);
        assert!(matches!(printed[0].detail.class, Class::Refusal(_)));
        let start = strict.as_ref().find("missing").expect("the name");
        assert_eq!(
            printed[0].span,
            Maybe::Present(
                ByteSpan::new(ByteOffset::from(start), ByteOffset::from(start + 7_usize))
                    .expect("ordered")
            )
        );

        let goal = SourceText::from("def hole : Integer ;\n");
        let owing = step(
            Path::new("owed.gandr"),
            SourceRoot::Strict,
            goal,
            Standing::Unsettled,
            &grammar,
        );
        let goals: Vec<_> = entries(&owing, Verb::Check(Goals::Reported))
            .map(|diagnostic| diagnostic.severity)
            .collect();
        assert_eq!(goals, [Severity::Goal]);

        let pending = SourceText::from("def bad = missing ;\n");
        let held = step(
            Path::new("fixtures/pending/held.gandr"),
            SourceRoot::Pending,
            pending,
            Standing::Lowered,
            &grammar,
        );
        let ledger: Vec<_> = entries(&held, Verb::Test)
            .map(|diagnostic| (diagnostic.severity, diagnostic.message.text))
            .collect();
        assert_eq!(ledger.first().map(|line| line.0), Some(Severity::Ledger));
        assert!(
            ledger
                .first()
                .is_some_and(|line| line.1.starts_with("unsettled: a pending source")),
            "{ledger:?}"
        );
    }

    #[test]
    fn an_expected_refusal_prints_as_an_unexpected_one_when_every_refusal_is_asked()
    {
        let grammar = built_in().expect("the grammar builds");
        let expected = SourceText::from(
            "def good = 1 ;\n@[ refuses(\"UnresolvedName\") ] def bad = missing ;\n",
        );
        let settled = step(
            Path::new("fixtures/pair.gandr"),
            SourceRoot::Fixture,
            expected,
            Standing::Settled,
            &grammar,
        );
        let unexpected = SourceText::from("def good = 1 ;\ndef bad = missing ;\n");
        let refused = step(
            Path::new("fixtures/pair.gandr"),
            SourceRoot::Strict,
            unexpected,
            Standing::Unsettled,
            &grammar,
        );
        let check = Verb::Check(Goals::Gated);
        assert!(
            entries(&settled, check).next().is_none(),
            "check prints no refusal its expectation states"
        );
        for verb in [check, Verb::Test] {
            let every: Vec<_> = entries(&settled, verb)
                .refusals(Refusals::Every)
                .map(|diagnostic| (diagnostic.severity, diagnostic.message.text))
                .collect();
            let printed: Vec<_> = entries(&refused, check)
                .map(|diagnostic| (diagnostic.severity, diagnostic.message.text))
                .collect();
            assert_eq!(
                every, printed,
                "{verb:?}: the expected refusal prints as the unexpected one does"
            );
        }
    }

    /// #582: a source laid after its import prints its fixture line at bytes
    /// of its own file, the bytes its diagnostic is located at.
    #[test]
    fn an_importer_s_ledger_line_names_its_own_bytes()
    {
        let scratch = Scratch::new(Path::new("ledger-own-bytes"));
        scratch.file(
            Path::new("corpus/fixture/base.gandr"),
            SourceText::from("def one = 1 ;\n"),
        );
        let importer =
            "import \"./base.gandr\" ;\n@[ refuses(\"UnresolvedName\") ] def bad = missing ;\n";
        scratch.file(
            Path::new("corpus/fixture/importer.gandr"),
            SourceText::from(importer),
        );
        let start = importer.find("def bad").expect("the declaration");
        let end = start + "def bad = missing ;".len();
        let own = ByteSpan::new(ByteOffset::from(start), ByteOffset::from(end)).expect("ordered");

        let mut printed = Vec::new();
        let ControlFlow::Continue(_report) =
            Walk::new(vec![scratch.root().join("corpus/fixture/importer.gandr")]).visit(
                &Pool::new(Width::SERIAL),
                |step| -> ControlFlow<Infallible> {
                    printed.extend(
                        entries(&step, Verb::Test)
                            .map(|diagnostic| (diagnostic.message.text, diagnostic.span)),
                    );
                    ControlFlow::Continue(())
                },
            );
        assert_eq!(
            printed,
            [(
                format!(
                    "settled `bad` at {start}..{end}: states refuses UnresolvedName; produced \
                     refuses UnresolvedName (malformed source)"
                ),
                Maybe::Present(own)
            )],
            "the line names the bytes of the importer's own file, where its diagnostic stands"
        );
    }

    #[test]
    fn a_shadowed_builtin_is_warned_of_under_check_alone()
    {
        let grammar = built_in().expect("the grammar builds");
        let text = SourceText::from("def add : Integer ;\ndef add = 1 ;\n");
        let shadowing = step(
            Path::new("shadow.gandr"),
            SourceRoot::Strict,
            text,
            Standing::Settled,
            &grammar,
        );
        let warned: Vec<_> = entries(&shadowing, Verb::Check(Goals::Gated))
            .map(|diagnostic| (diagnostic.severity, diagnostic.span))
            .collect();
        assert_eq!(warned, [(
            Severity::Warning,
            Maybe::Present(
                ByteSpan::new(ByteOffset::from(4_usize), ByteOffset::from(7_usize))
                    .expect("ordered")
            )
        )]);
        assert!(entries(&shadowing, Verb::Test).next().is_none());
    }

    #[test]
    fn each_use_of_a_deprecated_declaration_is_a_finding()
    {
        let grammar = built_in().expect("the grammar builds");
        let written = "def add : Integer ;\n@[ deprecated ] def add = 1 ;\ndef a = add ;\ndef b \
                       = missing ;\n";
        let text = SourceText::from(written);
        let at = |needle: &str, length: usize| {
            let start = written.find(needle).expect("written").saturating_add(2);
            Maybe::Present(
                ByteSpan::new(
                    ByteOffset::from(start),
                    ByteOffset::from(start.saturating_add(length)),
                )
                .expect("ordered"),
            )
        };
        let source = step(
            Path::new("deprecated.gandr"),
            SourceRoot::Strict,
            text,
            Standing::Unsettled,
            &grammar,
        );
        assert_eq!(
            entries(&source, Verb::Check(Goals::Gated))
                .map(|diagnostic| (diagnostic.detail.class, diagnostic.span))
                .collect::<Vec<_>>(),
            [
                (
                    Class::Warning,
                    Maybe::Present(
                        ByteSpan::new(ByteOffset::from(4_usize), ByteOffset::from(7_usize))
                            .expect("ordered")
                    )
                ),
                (Class::Lint(Lint::Deprecated), at("= add", 3)),
                (
                    Class::Refusal(gandr_core_term::FailureClass::MalformedSource),
                    at("= missing", 7)
                ),
            ],
            "with no lint enabled, the use is a finding after the warnings and before the \
             declarations"
        );
        assert!(
            entries(&source, Verb::Test).all(|diagnostic| diagnostic.severity != Severity::Warning),
            "`test` prints settlements alone"
        );
    }

    #[test]
    fn a_declaration_naming_a_refused_one_is_a_note()
    {
        let grammar = built_in().expect("the grammar builds");
        let text = SourceText::from(
            "def a() -> Integer {\n  return 1 ^ 2\n}\n\ndef b() -> Integer {\n  return a()\n}\n\ndef \
             c() -> Integer {\n  return 1\n}\n\ndef d() -> Integer {\n  return c()\n}\n",
        );
        let cascade = step(
            Path::new("cascade.gandr"),
            SourceRoot::Strict,
            text,
            Standing::Unsettled,
            &grammar,
        );
        let at = |needle: &str, from: usize| {
            let start = text
                .as_ref()
                .get(from ..)
                .and_then(|rest| rest.find(needle))
                .expect("the needle")
                .saturating_add(from);
            Maybe::Present(
                ByteSpan::new(
                    ByteOffset::from(start),
                    ByteOffset::from(start.saturating_add(1)),
                )
                .expect("ordered"),
            )
        };
        let body = text.as_ref().find("return a()").expect("the call");
        assert_eq!(
            entries(&cascade, Verb::Check(Goals::Gated))
                .map(|diagnostic| (diagnostic.severity, diagnostic.span))
                .collect::<Vec<_>>(),
            [
                (Severity::Error, at("^", 0)),
                (Severity::Note, at("a()", body))
            ],
            "the refused declaration is the one error; the one calling it is a note at the call, \
             and the one calling a declaration that checks prints nothing"
        );
    }

    /// A signature whose definition is written with its keyword misspelt owes
    /// its body because the lowering refused that form: it is a note, and the
    /// first error is the misspelt keyword (#2339). A signature beside no
    /// refused form of its name stays an error.
    #[test]
    fn a_declaration_whose_other_half_is_refused_is_a_note_2339()
    {
        let grammar = built_in().expect("the grammar builds");
        let written = "@[ checks ]\ndef pair : Integer ;\nde pair = 1 ;\n";
        let unread = step(
            Path::new("unread.gandr"),
            SourceRoot::Strict,
            SourceText::from(written),
            Standing::Unsettled,
            &grammar,
        );
        let printed: Vec<_> = entries(&unread, Verb::Check(Goals::Gated))
            .map(|diagnostic| {
                (
                    diagnostic.severity,
                    diagnostic.span,
                    diagnostic.message.text,
                )
            })
            .collect();
        let signature = written.find("def pair :").expect("the signature");
        assert!(
            printed.iter().any(|&(severity, span, _)| severity == Severity::Note
                && matches!(span, Maybe::Present(span) if usize::from(span.start()) == signature)),
            "the signature is a note: {printed:?}"
        );
        let first = printed
            .iter()
            .find(|&&(severity, ..)| severity == Severity::Error)
            .map(|&(_, span, _)| span);
        let at = written.find("de pair").expect("the definition");
        assert!(
            matches!(first, Some(Maybe::Present(span)) if usize::from(span.start()) == at),
            "the first error is the misspelt keyword: {printed:?}"
        );
        let text = SourceText::from("@[ checks ]\ndef lone : Integer ;\n");
        let lone = step(
            Path::new("lone.gandr"),
            SourceRoot::Strict,
            text,
            Standing::Unsettled,
            &grammar,
        );
        assert_eq!(
            entries(&lone, Verb::Check(Goals::Gated))
                .map(|diagnostic| diagnostic.severity)
                .collect::<Vec<_>>(),
            [Severity::Error],
            "a signature owing its body beside no refused form is its own error"
        );
    }

    /// A declaration whose keyword is misspelt is read as an identifier at the
    /// top level, a function type where a declaration stands and a block; the
    /// declaration admitted before it, calling the name the misspelling took
    /// out of scope, is refused because of it. Under `check` the refusals of
    /// form print first, so the first error is the misspelt keyword, and the
    /// call resting on them follows (#2875).
    #[test]
    fn a_refusal_of_form_prints_before_one_resting_on_it_2875()
    {
        let grammar = built_in().expect("the grammar builds");
        let written =
            "def f() -> Integer {\n  return g()\n}\n\nde g() -> Integer {\n  return 1\n}\n";
        let misspelt = step(
            Path::new("misspelt.gandr"),
            SourceRoot::Strict,
            SourceText::from(written),
            Standing::Unsettled,
            &grammar,
        );
        let at = |needle: &str| written.find(needle).expect("the needle");
        assert_eq!(
            entries(&misspelt, Verb::Check(Goals::Gated))
                .filter(|diagnostic| diagnostic.severity == Severity::Error)
                .map(|diagnostic| match diagnostic.span {
                    Maybe::Present(span) => usize::from(span.start()),
                    Maybe::Absent(_) => usize::MAX,
                })
                .collect::<Vec<_>>(),
            [at("de g"), at("g() ->"), at("{\n  return 1"), at("g()")],
            "the refusals of form print first in admission order, then the unresolved call \
             admitted before them"
        );
    }

    /// The note of a declaration calling a refused one names the declaration
    /// it calls, not another the lowering refused before it.
    #[test]
    fn a_note_names_the_refused_declaration_it_rests_on()
    {
        let grammar = built_in().expect("the grammar builds");
        let text = SourceText::from(
            "def a() -> Integer {\n  return 1 ~ 2\n}\n\ndef x() -> Integer {\n  return 3 ~ \
             4\n}\n\ndef b() -> Integer {\n  return x()\n}\n",
        );
        let cascade = step(
            Path::new("named.gandr"),
            SourceRoot::Strict,
            text,
            Standing::Unsettled,
            &grammar,
        );
        let notes: Vec<String> = entries(&cascade, Verb::Check(Goals::Gated))
            .filter(|diagnostic| diagnostic.severity == Severity::Note)
            .filter_map(|diagnostic| match diagnostic.note {
                Maybe::Present(note) => Some(note),
                Maybe::Absent(_) => None,
            })
            .collect();
        assert!(
            matches!(notes.as_slice(), [note] if note.contains("`x`") && !note.contains("`a`")),
            "one note, naming `x`, the declaration `b` calls: {notes:?}"
        );
    }

    /// #782: a refusal names the types it compares in the spelling its
    /// entries are asked for, Unicode unless asked otherwise.
    #[test]
    fn a_refusal_names_its_types_in_the_spelling_asked_782()
    {
        let grammar = built_in().expect("the grammar builds");
        let refused = step(
            Path::new("relation.gandr"),
            SourceRoot::Strict,
            SourceText::from("def r : Integer ≃ String ;\ndef r = 1 ;\n"),
            Standing::Unsettled,
            &grammar,
        );
        let compared = |printed: Entries<'_>| {
            printed
                .map(|diagnostic| diagnostic.detail.compared.to_string())
                .collect::<Vec<_>>()
        };
        let expected = |relation: &str| [format!("expected `{relation}`, found `Integer`")];
        assert_eq!(
            compared(entries(&refused, Verb::Check(Goals::Gated))),
            expected("Integer ≃ String"),
            "Unicode by default"
        );
        assert_eq!(
            compared(entries(&refused, Verb::Check(Goals::Gated)).spelling(Spelling::Ascii)),
            expected("Integer <~> String"),
            "ASCII when asked"
        );
    }

    #[test]
    fn an_inferred_exit_is_reported_where_a_lint_reaches()
    {
        let grammar = built_in().expect("the grammar builds");
        let text = SourceText::from(
            "def add : Integer ;\ndef add = 1 ;\n@[ explicit_exits ]\ndef asked(n: Integer) -> -F \
             Integer { n }\ndef unasked(n: Integer) -> -F Integer { n }\n",
        );
        let at = |start: usize| {
            Maybe::Present(
                ByteSpan::new(
                    ByteOffset::from(start),
                    ByteOffset::from(start.saturating_add(1_usize)),
                )
                .expect("ordered"),
            )
        };
        let shadowed = Maybe::Present(
            ByteSpan::new(ByteOffset::from(4_usize), ByteOffset::from(7_usize)).expect("ordered"),
        );
        let asked = at(text
            .as_ref()
            .find("{ n }")
            .expect("asked")
            .saturating_add(2_usize));
        let unasked = at(text
            .as_ref()
            .rfind("{ n }")
            .expect("unasked")
            .saturating_add(2_usize));
        let finding = |diagnostic: gandr_surface_diagnostics::Diagnostic| {
            (diagnostic.detail.class, diagnostic.span)
        };
        let lint = Class::Lint(Lint::ExplicitExits);
        let source = step(
            Path::new("exits.gandr"),
            SourceRoot::Strict,
            text,
            Standing::Settled,
            &grammar,
        );
        assert_eq!(
            entries(&source, Verb::Check(Goals::Gated))
                .map(finding)
                .collect::<Vec<_>>(),
            [(Class::Warning, shadowed), (lint, asked)],
            "by default a lint reaches the forms its attribute marks, after the warnings"
        );
        assert_eq!(
            entries(&source, Verb::Check(Goals::Reported))
                .linting(Lints::enabling([Lint::ExplicitExits]))
                .map(finding)
                .collect::<Vec<_>>(),
            [(Class::Warning, shadowed), (lint, asked), (lint, unasked)],
            "a lint the run enables reaches every inferred exit, in source order"
        );
        assert!(
            entries(&source, Verb::Test)
                .linting(Lints::enabling([Lint::ExplicitExits]))
                .next()
                .is_none(),
            "`test` prints settlements alone"
        );
    }

    #[test]
    fn an_inferred_run_is_reported_where_a_lint_reaches()
    {
        let grammar = built_in().expect("the grammar builds");
        let text = SourceText::from(
            "def id(n: Integer) -> -F Integer { n }\n@[ explicit_runs(\"effects\") ]\ndef \
             effects(n: Integer) -> -F Integer { id(id(n)) }\n@[ explicit_runs ]\ndef every(n: \
             Integer) -> -F Integer { id(id(n)) }\ndef unasked(n: Integer) -> -F Integer { \
             id(id(n)) }\n",
        );
        let nested = |declaration: &str| {
            let context = text.as_ref().find(declaration).expect("declared");
            let start = text
                .as_ref()
                .get(context ..)
                .and_then(|rest| rest.find("{ id(id(n)) }"))
                .expect("nested")
                .saturating_add(context)
                .saturating_add(5_usize);
            Maybe::Present(
                ByteSpan::new(
                    ByteOffset::from(start),
                    ByteOffset::from(start.saturating_add(5_usize)),
                )
                .expect("ordered"),
            )
        };
        let (effects, every, unasked) = (
            nested("def effects"),
            nested("def every"),
            nested("def unasked"),
        );
        let finding = |diagnostic: gandr_surface_diagnostics::Diagnostic| {
            (diagnostic.detail.class, diagnostic.span)
        };
        let lint = Class::Lint(Lint::ExplicitRuns);
        let mut source = step(
            Path::new("runs.gandr"),
            SourceRoot::Strict,
            text,
            Standing::Settled,
            &grammar,
        );
        assert_eq!(
            entries(&source, Verb::Check(Goals::Gated))
                .map(finding)
                .collect::<Vec<_>>(),
            [(lint, every)],
            "by default the lint reaches the forms its attribute marks, and the `effects` option \
             leaves a pure run silent"
        );
        assert_eq!(
            entries(&source, Verb::Check(Goals::Gated))
                .linting(Lints::enabling([Lint::ExplicitRuns]))
                .map(finding)
                .collect::<Vec<_>>(),
            [(lint, effects), (lint, every), (lint, unasked)],
            "the lint the run enables reaches every inferred run, in source order"
        );
        // The lowering reads no effect rows yet, so a surface source cannot
        // perform one; the run the checker decided for `unasked` is marked
        // effectful here, which is what an effectful returner decides.
        if let Step::Source {
            composed: crate::Composed::Settled { ref mut runs, .. },
            ..
        } = source
        {
            for run in runs.iter_mut() {
                if Maybe::Present(run.span) == unasked {
                    run.purity = Purity::Effectful;
                }
            }
        }
        assert_eq!(
            entries(&source, Verb::Check(Goals::Gated))
                .linting(Lints::default().asking_effects())
                .map(finding)
                .collect::<Vec<_>>(),
            [(lint, every), (lint, unasked)],
            "under the run's `effects` option an effectful run is a finding everywhere, and a \
             pure one only where an attribute asks for every run"
        );
        assert!(
            entries(&source, Verb::Test)
                .linting(Lints::enabling([Lint::ExplicitRuns]))
                .next()
                .is_none(),
            "`test` prints settlements alone"
        );
    }

    #[test]
    fn a_second_run_refusal_is_located_where_its_bound_spelling_is_380()
    {
        let grammar = built_in().expect("the grammar builds");
        let data = "data Int : Type {\n  Z : Int;\n  S : (x : Int) --> Int;\n  P : (x : Int) --> \
                    Int;\n  rule S(P(x)) ==> x;\n  rule P(S(x)) ==> x;\n}\n\n";
        let fold = |arm: &str| {
            format!(
                "{data}def rec tell(n : Int) -> -F Int {{\n  case n {{\n    Z => Z,\n    S(x) => \
                 {arm},\n    P(x) => {arm}\n  }}\n}}\n"
            )
        };
        // The nested call is judged by the second run, over the bind the
        // first run elaborated it to; the bound twin by the first run alone.
        for written in [fold("S(tell[<](x))"), fold("{ run t <- tell[<](x); S(t) }")] {
            let text = SourceText::from(written.as_str());
            let start = written.find("case n").expect("the case");
            let end = written.rfind("  }\n}").expect("the case's close") + "  }".len();
            let case = Maybe::Present(
                ByteSpan::new(ByteOffset::from(start), ByteOffset::from(end)).expect("ordered"),
            );
            let fold = step(
                Path::new("fold.gandr"),
                SourceRoot::Strict,
                text,
                Standing::Unsettled,
                &grammar,
            );
            assert_eq!(
                entries(&fold, Verb::Check(Goals::Gated))
                    .map(|diagnostic| {
                        let code = diagnostic.identifier.map(|code| code.to_string());
                        (diagnostic.severity, code, diagnostic.span)
                    })
                    .collect::<Vec<_>>(),
                [(
                    Severity::Error,
                    Maybe::Present(String::from("RuleNotRespected")),
                    case
                )],
                "the fold is refused at the case block whichever run judged it:\n{written}"
            );
        }
    }

    #[test]
    fn counted_declarations_preserve_visible_order_and_exhaustion()
    {
        let text = SourceText::from(
            "def quiet = 1 ;\ndef first = missing ;\ndef middle = 2 ;\ndef second = missing ;\ndef last = 3 ;\n",
        );
        let grammar = built_in().expect("the grammar builds");
        let step = step(
            Path::new("ordered.gandr"),
            SourceRoot::Strict,
            text,
            Standing::Unsettled,
            &grammar,
        );
        let expected = [
            text.as_ref().find("missing").expect("the first refusal"),
            text.as_ref().rfind("missing").expect("the last refusal"),
        ]
        .map(|start| {
            Maybe::Present(
                ByteSpan::new(
                    ByteOffset::from(start),
                    ByteOffset::from(start + "missing".len()),
                )
                .expect("an ordered ASCII token"),
            )
        });
        let mut stream = entries(&step, Verb::Check(Goals::Gated));
        let actual = stream
            .by_ref()
            .map(|diagnostic| {
                assert_ne!(
                    diagnostic.severity,
                    Severity::Ledger,
                    "strict counted declarations are not ledger lines"
                );
                diagnostic.span
            })
            .collect::<Vec<_>>();
        assert_eq!(actual.as_slice(), &expected);
        assert!(
            stream.next().is_none(),
            "exhaustion cannot resurrect a skipped declaration"
        );
    }

    #[test]
    fn faults_and_empty_sources_stay_exhausted()
    {
        let verbs = [
            Verb::Check(Goals::Gated),
            Verb::Check(Goals::Reported),
            Verb::Test,
        ];
        let exhausted = |step: &Step<'_>| {
            for verb in verbs {
                let mut stream = entries(step, verb);
                assert!(stream.next().is_none());
                assert!(
                    stream.next().is_none(),
                    "an exhausted stream stays exhausted"
                );
            }
        };
        let faulted = Walk::new(vec![PathBuf::new()]).visit(&Pool::new(Width::SERIAL), |fault| {
            assert!(
                matches!(fault, Step::Fault { .. }),
                "an empty path is a fault, not an empty walk"
            );
            exhausted(&fault);
            ControlFlow::Break(())
        });
        assert_eq!(faulted, ControlFlow::Break(()), "the fault is handed over");
        let text = SourceText::from("");
        let grammar = built_in().expect("the grammar builds");
        exhausted(&step(
            Path::new("empty.gandr"),
            SourceRoot::Strict,
            text,
            Standing::Unsettled,
            &grammar,
        ));
    }
}
