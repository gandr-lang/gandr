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
use core::marker::PhantomData;
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
use gandr_surface_diagnostics::Fix;
use gandr_surface_diagnostics::PartingPair;
use gandr_surface_diagnostics::Severity;
use gandr_surface_diagnostics::SourceStart;
use gandr_surface_diagnostics::Subject;
use gandr_surface_diagnostics::TypeSpellings;
use gandr_surface_diagnostics::Unsettlement;
use gandr_surface_diagnostics::diagnose;
use gandr_surface_diagnostics::obstructed;
use gandr_surface_diagnostics::parting;
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
use gandr_surface_lowering::desc_cells::CellDiagnostic;
use gandr_surface_lowering::namespace::ShadowedBuiltin;
use gandr_surface_pretty::Spelling;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::compose::Composed;
use crate::engine::Engine;
use crate::walk::Standing;
use crate::walk::Step;
use crate::workspace::stepped_alone;

pub mod answered;
pub mod console;
pub mod entered;
pub mod evaluation;
pub mod exercised;
pub mod report;
pub mod worlds;

use self::report::Lints;
use self::report::Reach;
use self::report::Shown;
use self::report::Verb;
use self::report::shown;

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
    /// A settled declaration with a line: a fixture, printed by `test`, or a
    /// declaration the kernel has no image of, printed by every verb.
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
    /// - witness: `tests::entry::each_verb_prints_its_entries`
    /// - witness: `tests::entry::an_importer_s_ledger_line_names_its_own_bytes`
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

/// Whether the repair a refusal names is checked before the refusal proposes
/// it as its fix.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Repairs
{
    /// Each repair is named and checked by nobody here: an editor checks it
    /// when its reader asks for a fix.
    #[default]
    Named,
    /// Each repair is checked as `check` checks its source, at most
    /// [`CHECKED_REPAIRS`] in one source, and proposed as the fix when its
    /// declaration settles in the source the repair writes.
    Checked,
}

/// How many repairs one source checks under [`Repairs::Checked`]: each check
/// lays out, lowers and judges the source again, so the budget bounds the
/// work a source that refuses many declarations adds to `check`.
const CHECKED_REPAIRS: usize = 4;

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
    /// The cell diagnostics that hold a parting pair, in source order: what a
    /// refusal of a block's rules reads its obstruction from.
    parted: &'step [CellDiagnostic],
}

/// The diagnostics of one step, in the order its verb prints them.
#[derive(Clone, Debug)]
pub struct Entries<'step, E>
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
    /// Whether a named repair is checked before it is proposed as a fix.
    repairs: Repairs,
    /// How many repairs this source has checked.
    checked: usize,
    /// What remains.
    cursor: Cursor<'step>,
    /// The engine that runs the settlement of a repair checked.
    engine: PhantomData<fn() -> E>,
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
/// - witness: `tests::entry::each_verb_prints_its_entries`
/// - witness: `tests::entry::a_refusal_of_form_prints_before_one_resting_on_it_2875`
/// - witness: `tests::entry::a_shadowed_builtin_is_warned_of_under_check_alone`
/// - witness: `tests::entry::an_inferred_exit_is_reported_where_a_lint_reaches`
/// - witness: `tests::entry::an_inferred_run_is_reported_where_a_lint_reaches`
/// - witness: `tests::entry::each_use_of_a_deprecated_declaration_is_a_finding`
/// - witness: `tests::entry::counted_declarations_preserve_visible_order_and_exhaustion`
/// - witness: `tests::entry::faults_and_empty_sources_stay_exhausted`
#[spec(ensures: |ref ret| ret.verb == verb && ret.lints == Lints::default() && ret.refusals == Refusals::Unsettling && ret.spelling == Spelling::Unicode && ret.repairs == Repairs::Named && ret.checked == 0_usize && match *step {
    Step::Fault { path, .. } => core::ptr::eq(core::ptr::from_ref(ret.path), core::ptr::from_ref(path))
        && ret.text.as_ref().is_empty() && matches!(ret.cursor, Cursor::Done),
    Step::Source { path, text, .. } => core::ptr::eq(core::ptr::from_ref(ret.path), core::ptr::from_ref(path)) && core::ptr::eq(core::ptr::from_ref(ret.text.as_ref()), core::ptr::from_ref(text.as_ref())),
})]
#[inline]
#[must_use]
pub fn entries<'step, E>(
    step: &'step Step<'step>,
    verb: Verb,
) -> Entries<'step, E>
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
        repairs: Repairs::Named,
        checked: 0_usize,
        cursor,
        engine: PhantomData,
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
/// - witness: `tests::entry::each_verb_prints_its_entries`
/// - witness: `tests::entry::faults_and_empty_sources_stay_exhausted`
/// - witness: `tests::entry::a_shadowed_builtin_is_warned_of_under_check_alone`
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
                ref parted,
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
                parted,
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
/// - witness: `tests::entry::a_refusal_of_form_prints_before_one_resting_on_it_2875`
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
/// - witness: `tests::entry::a_declaration_naming_a_refused_one_is_a_note`
/// - witness: `tests::entry::a_note_names_the_refused_declaration_it_rests_on`
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

/// The parting pair that a refusal of a block's rules for a critical pair
/// whose sides part names, read from the cell diagnostic `parted` holds at
/// the refusal's span.
///
/// # Specification
/// - requires: `parted` is the source's cell diagnostics that hold a parting
///   pair.
/// - ensures: present exactly for a `RulesDiverge` or `RulesUncompleted`
///   refusal whose span and earlier rule a diagnostic of `parted` holds; its
///   cells and witness are that diagnostic's, by reference.
/// - provides: the obstruction the refused declaration's message names.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a block whose unit laws part reads its pair with the peak
///   and the normal forms in order; a refusal of another kind, and a divergent
///   refusal whose pair the composition does not hold, read none.
/// - witness: `tests::entry::a_rules_refusal_reads_its_parting_pair_and_no_other_refusal_does`
#[spec(ensures: |ret| match (refusal, ret) {
    (Refusal::Lowering(LoweringRefusal::RulesDiverge { span, first } | LoweringRefusal::RulesUncompleted { span, first }), Maybe::Present(pair)) =>
        pair.cells.later == span && pair.cells.earlier == first,
    (_, Maybe::Present(_)) => false,
    (_, Maybe::Absent(_)) => true,
})]
#[inline]
pub fn obstruction<'step>(
    refusal: Refusal<'step>,
    parted: &'step [CellDiagnostic],
) -> Maybe<PartingPair<'step>, obstructed::Absent>
{
    let Refusal::Lowering(
        LoweringRefusal::RulesDiverge { span, first }
        | LoweringRefusal::RulesUncompleted { span, first },
    ) = refusal
    else {
        return Maybe::Absent(obstructed::Absent::Unparted);
    };
    parted
        .iter()
        .filter(|diagnostic| diagnostic.span == span)
        .find_map(|diagnostic| match parting(diagnostic) {
            Maybe::Present(pair) if pair.cells.earlier == first => Some(pair),
            Maybe::Present(_) | Maybe::Absent(_) => None,
        })
        .map_or(Maybe::Absent(obstructed::Absent::Unparted), Maybe::Present)
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
/// - witness: `tests::entry::a_declaration_whose_other_half_is_refused_is_a_note_2339`
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
/// - witness: `tests::entry::an_inferred_run_is_reported_where_a_lint_reaches`
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

impl<'step, E> Entries<'step, E>
where
    E: Engine,
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
    /// - witness: `tests::entry::an_inferred_exit_is_reported_where_a_lint_reaches`
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
    /// - witness: `tests::entry::a_refusal_names_its_types_in_the_spelling_asked_782`
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
    /// - witness: `tests::entry::an_expected_refusal_prints_as_an_unexpected_one_when_every_refusal_is_asked`
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

    /// These entries, each repair a refusal names checked as `repairs` says.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the same entries, in the same order. Under
    ///   [`Repairs::Checked`], each of the first [`CHECKED_REPAIRS`] repairs of
    ///   the source is checked, and a refusal proposes its repair as its fix
    ///   when the refused declaration settles in the source the repair writes;
    ///   [`entries`] checks none.
    /// - provides: the driver's `check`, which proposes only a fix it checked.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a list of two items with no `,` between them proposes
    ///   the `,` as its fix under [`Repairs::Checked`] and none under
    ///   [`Repairs::Named`]; a line that continues a `let` names its repair and
    ///   proposes none, because the source it writes still refuses.
    /// - witness: `tests::entry::a_repair_is_proposed_as_a_fix_once_it_checks_5474`
    #[spec(ensures: |ref ret| ret.repairs == repairs)]
    #[inline]
    #[must_use]
    pub fn repairing(
        mut self,
        repairs: Repairs,
    ) -> Self
    {
        self.repairs = repairs;
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
    ///   A shown settled declaration is a ledger line: a fixture, or one the
    ///   kernel has no image of; an unsettled declaration is a refusal subject,
    ///   carrying the failure the machine kept for it, when one was produced,
    ///   otherwise an unsettled subject naming the failed expectation.
    /// - provides: verb-directed selection without changing declaration order.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — finite real declarations distinguish counted, goal
    ///   and ledger selection from refused or unproduced expectations. Ordered
    ///   refusal spans expose skipping and substitution. Run-result mismatches
    ///   and malformed expectations are not enumerated by these fixtures.
    /// - witness: `tests::entry::each_verb_prints_its_entries`
    /// - witness: `tests::entry::counted_declarations_preserve_visible_order_and_exhaustion`
    /// - witness: `tests::entry::an_expected_refusal_prints_as_an_unexpected_one_when_every_refusal_is_asked`
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
                                        | Outcome::Decomposes(_)
                                        | Outcome::RunsTracing(..)
                                        | Outcome::Reads(_)
                                        | Outcome::Distributes(_),
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
                                    &Stated::Verdict(
                                        Outcome::Runs(_)
                                        | Outcome::Decomposes(_)
                                        | Outcome::RunsTracing(..)
                                        | Outcome::Distributes(_),
                                    ),
                                    Outcome::Runs(_)
                                    | Outcome::Refuses(_)
                                    | Outcome::Normalizes(_)
                                    | Outcome::Decomposes(_)
                                    | Outcome::RefusesRunning(..)
                                    | Outcome::RunsTracing(..)
                                    | Outcome::Reads(_)
                                    | Outcome::Distributes(_),
                                ) => Unsettlement::RunOutcome,
                                (
                                    &Stated::Verdict(Outcome::Normalizes(_)),
                                    Outcome::Normalizes(_)
                                    | Outcome::Refuses(_)
                                    | Outcome::Runs(_)
                                    | Outcome::Decomposes(_)
                                    | Outcome::RefusesRunning(..)
                                    | Outcome::RunsTracing(..)
                                    | Outcome::Reads(_)
                                    | Outcome::Distributes(_),
                                ) => Unsettlement::NormalForm,
                                (
                                    &Stated::Verdict(Outcome::Reads(_)),
                                    Outcome::Reads(_)
                                    | Outcome::Refuses(_)
                                    | Outcome::Runs(_)
                                    | Outcome::Normalizes(_)
                                    | Outcome::Decomposes(_)
                                    | Outcome::RefusesRunning(..)
                                    | Outcome::RunsTracing(..)
                                    | Outcome::Distributes(_),
                                ) => Unsettlement::Reads,
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
            obstruction: obstruction(refusal, held.parted),
        }
    }

    /// The diagnostic `printed` makes at this step's source.
    ///
    /// # Specification
    /// trivial.
    fn build(
        &mut self,
        printed: Printed<'_>,
    ) -> Diagnostic
    {
        match printed {
            Printed::Line(line) => line.diagnostic(self.path, self.text, self.start),
            Printed::Subject(subject) => {
                let mut diagnostic = diagnose(self.path, self.text, subject);
                if let Subject::Refused { declaration, .. } = subject
                    && let Maybe::Present(ref named) = diagnostic.repair
                    && self.repairs == Repairs::Checked
                    && self.checked < CHECKED_REPAIRS
                {
                    self.checked = self.checked.saturating_add(1);
                    if settles::<E>(self.path, self.text, self.start, declaration, named)
                        == Settlement::Settled
                    {
                        diagnostic.fix = Maybe::Present(named.clone());
                    }
                }
                diagnostic
            },
        }
    }
}

/// How `declaration` stands in the source at `path` that `repair` writes into
/// the source's own part of `text`, checked as `check` checks a source.
///
/// # Specification
/// - requires: `start` is where the source's own text starts in `text`, and
///   `repair` is measured against `text`.
/// - ensures: [`Settlement::Unsettled`] when `repair` lies before the source's
///   own text, or the source it writes does not compose; otherwise
///   [`Settlement::Settled`] exactly when a declaration of `declaration`'s name
///   settles in it.
/// - fails: never.
/// - panics: none.
/// - executable: none — the answer is the judgement of a whole source.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Entries::repairing`].
/// - witness: `tests::entry::a_repair_is_proposed_as_a_fix_once_it_checks_5474`
fn settles<E>(
    path: &Path,
    text: SourceText<'_>,
    start: SourceStart,
    declaration: &DeclarationReport<'_>,
    repair: &Fix,
) -> Settlement
where
    E: Engine,
{
    let Maybe::Present(own) = start.measure(repair.span)
    else {
        return Settlement::Unsettled;
    };
    let base = usize::from(repair.span.start()).saturating_sub(usize::from(own.start()));
    let Some((before, after)) = text.as_ref().get(base ..).and_then(|source| {
        Some((
            source.get(.. usize::from(own.start()))?,
            source.get(usize::from(own.end()) ..)?,
        ))
    })
    else {
        return Settlement::Unsettled;
    };
    let mut written = String::with_capacity(
        before
            .len()
            .saturating_add(repair.replacement.len())
            .saturating_add(after.len()),
    );
    written.push_str(before);
    written.push_str(&repair.replacement);
    written.push_str(after);
    stepped_alone::<E, _, _>(
        path,
        SourceText::from(written.as_str()),
        |step| match step {
            Step::Source {
                composed: Composed::Settled { ref report, .. },
                ..
            } if report.declarations().iter().any(|held| {
                held.name() == declaration.name() && held.settlement() == Settlement::Settled
            }) =>
            {
                Settlement::Settled
            },
            Step::Source { .. } | Step::Fault { .. } => Settlement::Unsettled,
        },
    )
    .unwrap_or(Settlement::Unsettled)
}

impl<E> Iterator for Entries<'_, E>
where
    E: Engine,
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
    /// - witness: `tests::entry::each_verb_prints_its_entries`
    /// - witness: `tests::entry::counted_declarations_preserve_visible_order_and_exhaustion`
    /// - witness: `tests::entry::faults_and_empty_sources_stay_exhausted`
    /// - witness: `tests::entry::an_inferred_exit_is_reported_where_a_lint_reaches`
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

impl<E> Entries<'_, E>
where
    E: Engine,
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
    /// - witness: `tests::entry::each_verb_prints_its_entries`
    /// - witness: `tests::entry::an_inferred_exit_is_reported_where_a_lint_reaches`
    /// - witness: `tests::entry::an_inferred_run_is_reported_where_a_lint_reaches`
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
