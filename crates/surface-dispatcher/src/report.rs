//! The runner's report: what a walk counted, and the gate it decides.
//!
//! # One predicate, three answers
//!
//! A run is settled when every declaration of every source it read settled and
//! every source was read the way its root expects; it faulted when a path
//! could not be carried through the pipeline or the engine refused a
//! declaration for a fault of its own. `--goals` changes what a reported
//! obligation does to the gate, never what settled means.

use core::fmt;

use gandr_core_term::FailureClass;
use gandr_surface_corpus::DeclarationReport;
use gandr_surface_corpus::Membership;
use gandr_surface_corpus::Outcome;
use gandr_surface_corpus::Settlement;
use gandr_surface_corpus::Stated;
use gandr_surface_corpus::Tally;
use gandr_surface_lowering::DeclarationCount;

use crate::compose::Composed;
use crate::compose::LoweringCount;
use crate::exercised::Exercised;
use crate::root::SourceRoot;
use crate::walk::Standing;

/// What `check` does with a declaration unsettled by its obligations alone.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Goals
{
    /// It fails the run, as every unsettled declaration does.
    Gated,
    /// It is printed as a goal and does not fail the run.
    Reported,
}

/// The verb a walk is run under, which decides what is printed and what
/// fails.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Verb
{
    /// `check`: every unsettled declaration has a line.
    Check(Goals),
    /// `test`: every fixture has a line, settled or not, and so does every
    /// unsettled declaration.
    Test,
}

/// Whether, and how, a verb prints one declaration.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Shown
{
    /// The declaration has no line of its own; it is only counted.
    Counted,
    /// The declaration has a line.
    Line,
    /// The declaration has a line as a goal: unsettled by its obligations
    /// alone, under `check --goals`.
    Goal,
}

/// How `verb` prints `declaration`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a declaration unsettled by its obligations alone — it states and
///   produces *checks*, owing different counts — is a [`Shown::Goal`] under
///   `check --goals`; any other unsettled declaration is a [`Shown::Line`]
///   under every verb; a settled one is a line under `test` when it is a
///   fixture, and counted otherwise.
/// - provides: the one place a verb's printing is decided, so the verbs share
///   the pass and differ only here.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the domain is three verbs by settled fixture, settled
///   plain declaration, goal-shaped and refusal-shaped unsettled declaration,
///   enumerated against a pinned table.
/// - witness: `report::tests::each_verb_shows_its_declarations`
#[inline]
#[must_use]
#[anodized::spec(ensures: |ret| match ret {
    Shown::Goal => declaration.settlement() == Settlement::Unsettled
        && unsettled_by(declaration) == Unsettled::Obligations && verb == Verb::Check(Goals::Reported),
    Shown::Line => (declaration.settlement() == Settlement::Unsettled
        && !(unsettled_by(declaration) == Unsettled::Obligations && verb == Verb::Check(Goals::Reported)))
        || (declaration.settlement() == Settlement::Settled
            && declaration.membership() == Membership::Fixture && verb == Verb::Test),
    Shown::Counted => declaration.settlement() == Settlement::Settled
        && !(declaration.membership() == Membership::Fixture && verb == Verb::Test),
})]
pub fn shown(
    declaration: &DeclarationReport<'_>,
    verb: Verb,
) -> Shown
{
    match (declaration.settlement(), unsettled_by(declaration), verb) {
        | (Settlement::Unsettled, Unsettled::Obligations, Verb::Check(Goals::Reported)) => {
            Shown::Goal
        },
        | (Settlement::Unsettled, Unsettled::Obligations | Unsettled::Verdict, _) => Shown::Line,
        | (Settlement::Settled, _, Verb::Test) if declaration.membership() == Membership::Fixture => {
            Shown::Line
        },
        | (Settlement::Settled, _, Verb::Test | Verb::Check(_)) => Shown::Counted,
    }
}

/// What a declaration's unsettlement rests on.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Unsettled
{
    /// Both sides are *checks*, owing different counts: only obligations
    /// survive.
    Obligations,
    /// Anything else: a refusal on either side, a stated run outcome, or an
    /// expectation stating no verdict.
    Verdict,
}

/// What `declaration`'s unsettlement, if any, rests on.
///
/// # Specification
/// - requires: nothing.
/// - ensures: obligations exactly when both stated and produced outcomes are
///   checks; every refusal, stated run or malformed expectation is
///   verdict-shaped.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — real settled, owed and refused declarations are observed
///   through their printing and gating decisions. These cover the ordinary
///   checks/refusal boundary, not every malformed expectation.
/// - witness: `report::tests::each_verb_shows_its_declarations`
/// - witness: `report::tests::each_count_decides_its_verdict`
#[anodized::spec(ensures: |ret| (ret == Unsettled::Obligations)
    == matches!((declaration.stated(), declaration.outcome()),
        (&Stated::Verdict(Outcome::Checks(_)), Outcome::Checks(_))))]
fn unsettled_by(declaration: &DeclarationReport<'_>) -> Unsettled
{
    match (declaration.stated(), declaration.outcome()) {
        | (&Stated::Verdict(Outcome::Checks(_)), Outcome::Checks(_)) => Unsettled::Obligations,
        | (
            &(Stated::Verdict(Outcome::Checks(_) | Outcome::Refuses(_) | Outcome::Runs(_))
            | Stated::Malformed(_)),
            _,
        ) => Unsettled::Verdict,
    }
}

/// How a run went, as the driver's exit reports it.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum RunVerdict
{
    /// Every declaration settled and every source was read as its root
    /// expects.
    Settled,
    /// At least one declaration is unsettled, or a source was not read as its
    /// root expects.
    Unsettled,
    /// A path could not be carried through the pipeline, or the engine refused
    /// a declaration for a fault of its own.
    Faulted,
}

impl fmt::Display for RunVerdict
{
    /// Writes `settled`, `unsettled` or `faulted`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            | Self::Settled => "settled",
            | Self::Unsettled => "unsettled",
            | Self::Faulted => "faulted",
        })
    }
}

/// How many sources a run read, by root, and how many it could not read as
/// their root expects.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct SourceCounts
{
    /// Sources read under the strict root.
    strict: SourceCount,
    /// Sources read under the fixture root, outside its pending set.
    fixture: SourceCount,
    /// Sources read in the pending set.
    pending: SourceCount,
    /// Sources the lowering refused as a whole where their root expects
    /// declarations.
    refused: SourceCount,
    /// Pending sources carrying no refusal an expectation cannot state.
    lowered_pending: SourceCount,
    /// Paths the run could not carry through the pipeline.
    faulted: SourceCount,
}

impl SourceCounts
{
    /// Sources read under the strict root.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn strict(&self) -> SourceCount
    {
        self.strict
    }

    /// Sources read under the fixture root, outside its pending set.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn fixture(&self) -> SourceCount
    {
        self.fixture
    }

    /// Sources read in the pending set.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn pending(&self) -> SourceCount
    {
        self.pending
    }

    /// Sources the lowering refused as a whole where their root expects
    /// declarations.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn refused(&self) -> SourceCount
    {
        self.refused
    }

    /// Pending sources carrying no refusal an expectation cannot state.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn lowered_pending(&self) -> SourceCount
    {
        self.lowered_pending
    }

    /// Paths the run could not carry through the pipeline.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn faulted(&self) -> SourceCount
    {
        self.faulted
    }

    /// Every source read, whatever its root.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the saturated sum of strict, fixture and pending sources;
    ///   refusal, lowered-pending and fault counters do not add sources.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct root counts and a sum beyond the maximum
    ///   count distinguish omitted roots, inclusion of fault/refusal counts and
    ///   wrapping arithmetic. These are finite integer boundaries.
    /// - witness: `report::tests::source_counts_saturate_without_counting_refusals`
    /// - witness: `report::tests::report_rendering_preserves_numeric_roles_and_line_boundaries`
    #[inline]
    #[must_use]
    #[anodized::spec(ensures: |ret| ret.0 == self.strict.0
        .saturating_add(self.fixture.0).saturating_add(self.pending.0))]
    pub fn read(&self) -> SourceCount
    {
        SourceCount(
            self.strict
                .0
                .saturating_add(self.fixture.0)
                .saturating_add(self.pending.0),
        )
    }
}

impl fmt::Display for SourceCounts
{
    /// Writes the sources read, by root, then those not read as their root
    /// expects and the faulted paths.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: renders the total, strict, fixture, pending, refused,
    ///   lowered-pending and fault counts in that order.
    /// - fails: propagates the formatter's write failure.
    /// - panics: none.
    /// - executable: none — write status does not expose the emitted count
    ///   sequence in the caller-owned formatter sink.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — pairwise distinct counts have an independently
    ///   expected numeric sequence in the rendered report. Dropped, repeated or
    ///   exchanged roles are distinguished without pinning English prose;
    ///   arbitrary formatter failures are outside the successful-write fixture.
    /// - witness: `report::tests::report_rendering_preserves_numeric_roles_and_line_boundaries`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(
            f,
            "{} read ({} strict, {} fixture, {} pending), {} refused as a whole, {} no longer pending, {} faulted",
            self.read(),
            self.strict,
            self.fixture,
            self.pending,
            self.refused,
            self.lowered_pending,
            self.faulted
        )
    }
}

/// How many sources, or paths, a run counted.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SourceCount(usize);

impl SourceCount
{
    /// The count and one more, saturating.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one greater, saturated at the maximum source count.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — consecutive fault transitions reach and remain at the
    ///   maximum count; ordinary path faults exercise an increment below the
    ///   boundary. These distinguish wraparound and premature saturation.
    /// - witness: `report::tests::source_counts_saturate_without_counting_refusals`
    /// - witness: `report::tests::each_count_decides_its_verdict`
    #[anodized::spec(ensures: |ret| ret.0 == self.0.saturating_add(1_usize))]
    const fn one_more(self) -> Self
    {
        Self(self.0.saturating_add(1_usize))
    }
}

impl From<usize> for SourceCount
{
    /// The count of `sources` sources.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(sources: usize) -> Self
    {
        Self(sources)
    }
}

impl From<SourceCount> for usize
{
    /// The number of sources `count` records.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: SourceCount) -> Self
    {
        count.0
    }
}

impl fmt::Display for SourceCount
{
    /// Writes the number of sources.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        fmt::Display::fmt(&self.0, f)
    }
}

/// Everything a walk counted: the runner's report.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct RunReport
{
    /// The sources, by root and by how they were read.
    sources: SourceCounts,
    /// The settle counts, absorbed over every source the lowering read.
    tally: Tally,
    /// The exercised rows the settled declarations carry.
    exercised: Exercised,
    /// The lowerings performed.
    lowerings: LoweringCount,
    /// The declarations unsettled by their obligations alone.
    goals: DeclarationCount,
}

impl RunReport
{
    /// The sources, by root and by how they were read.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn sources(&self) -> SourceCounts
    {
        self.sources
    }

    /// The settle counts over every source the lowering read.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn tally(&self) -> Tally
    {
        self.tally
    }

    /// The exercised rows the settled declarations carry.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn exercised(&self) -> Exercised
    {
        self.exercised
    }

    /// The lowerings the run performed: one per source read, the declared
    /// projection of the composition's single lowering.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn lowerings(&self) -> LoweringCount
    {
        self.lowerings
    }

    /// The declarations unsettled by their obligations alone.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn goals(&self) -> DeclarationCount
    {
        self.goals
    }

    /// The gate `verb` reads off this report.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`RunVerdict::Faulted`] when a path faulted or a declaration
    ///   produced an engine-fault refusal, whatever it states; otherwise
    ///   [`RunVerdict::Unsettled`] when a source was not read as its root
    ///   expects, or a declaration is unsettled — under `check --goals`,
    ///   unsettled by more than its obligations; otherwise
    ///   [`RunVerdict::Settled`].
    /// - provides: the predicate the driver's exit code reports.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each count that decides is set alone on an otherwise
    ///   settled report and the verdict asserted under every verb, with the
    ///   goals boundary at goals equal to and one below the unsettled count.
    /// - witness: `report::tests::each_count_decides_its_verdict`
    #[inline]
    #[must_use]
    #[anodized::spec(ensures: |ret| {
        let fault = self.sources.faulted.0 != 0
            || usize::from(self.tally.refusals().count(FailureClass::EngineFault)) != 0;
        let owed = usize::from(self.tally.declarations().unsettled());
        let unsettled = self.sources.refused.0 != 0 || self.sources.lowered_pending.0 != 0
            || match verb {
                Verb::Check(Goals::Reported) => owed > usize::from(self.goals),
                Verb::Check(Goals::Gated) | Verb::Test => owed != 0,
            };
        match ret {
            RunVerdict::Faulted => fault,
            RunVerdict::Unsettled => !fault && unsettled,
            RunVerdict::Settled => !fault && !unsettled,
        }
    })]
    pub fn verdict(
        &self,
        verb: Verb,
    ) -> RunVerdict
    {
        let engine = self.tally.refusals().count(FailureClass::EngineFault);
        let unsettled = usize::from(self.tally.declarations().unsettled());
        let gating = match verb {
            | Verb::Check(Goals::Reported) => unsettled.saturating_sub(usize::from(self.goals)),
            | Verb::Check(Goals::Gated) | Verb::Test => unsettled,
        };
        if usize::from(self.sources.faulted) > 0_usize || usize::from(engine) > 0_usize {
            RunVerdict::Faulted
        }
        else if usize::from(self.sources.refused) > 0_usize
            || usize::from(self.sources.lowered_pending) > 0_usize
            || gating > 0_usize
        {
            RunVerdict::Unsettled
        }
        else {
            RunVerdict::Settled
        }
    }

    /// Count one faulted path.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the fault count increases by one with saturation; the source
    ///   root counts, refusals and lowered-pending count are unchanged.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — ordinary faults outrank unsettlement; successive
    ///   faults at the maximum preserve the root and refusal counts. This
    ///   distinguishes wrapping and changing an unrelated source
    ///   classification.
    /// - witness: `report::tests::each_count_decides_its_verdict`
    /// - witness: `report::tests::source_counts_saturate_without_counting_refusals`
    #[anodized::spec(
        captures: [sources = self.sources],
        ensures: |_| self.sources.faulted.0 == sources.faulted.0.saturating_add(1_usize)
            && self.sources.strict == sources.strict && self.sources.fixture == sources.fixture
            && self.sources.pending == sources.pending && self.sources.refused == sources.refused
            && self.sources.lowered_pending == sources.lowered_pending,
    )]
    pub(crate) fn faulted(&mut self)
    {
        self.sources.faulted = self.sources.faulted.one_more();
    }

    /// Count one lowering.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn lowerings_mut(&mut self) -> &mut LoweringCount
    {
        &mut self.lowerings
    }

    /// Count one source read under `root`, what it became and how it stands;
    /// a pending source's declarations are not counted.
    ///
    /// # Specification
    /// - requires: nothing; the caller supplies the source's classification.
    /// - ensures: the selected root count increases with saturation; refused
    ///   and lowered standings increment their respective counters. Pending
    ///   standings contribute no declarations, exercised rows or goals;
    ///   otherwise a settled composition contributes its tally and rows, and
    ///   one goal per declaration unsettled only by obligations. Fault and
    ///   lowering counts are unchanged.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — real ordinary, pending-form and newly lowered sources
    ///   distinguish source counting from declaration/goal absorption. Existing
    ///   gating fixtures distinguish refusal and engine counts. The
    ///   observations are finite compositions, not arbitrary tally states.
    /// - witness: `report::tests::pending_sources_do_not_contribute_declarations_or_goals`
    /// - witness: `report::tests::each_count_decides_its_verdict`
    #[anodized::spec(
        captures: [sources = self.sources, goals = usize::from(self.goals), lowerings = self.lowerings],
        ensures: |_| {
            let added_goals = if standing == Standing::Pending { 0_usize }
                else { match *composed {
                    Composed::Settled { ref report, .. } => report.declarations().iter()
                        .filter(|declaration| declaration.settlement() == Settlement::Unsettled
                            && unsettled_by(declaration) == Unsettled::Obligations).count(),
                    Composed::Refused(_) => 0_usize,
                }};
            self.sources.strict.0 == sources.strict.0.saturating_add(usize::from(root == SourceRoot::Strict))
                && self.sources.fixture.0 == sources.fixture.0.saturating_add(usize::from(root == SourceRoot::Fixture))
                && self.sources.pending.0 == sources.pending.0.saturating_add(usize::from(root == SourceRoot::Pending))
                && self.sources.refused.0 == sources.refused.0.saturating_add(usize::from(standing == Standing::Refused))
                && self.sources.lowered_pending.0 == sources.lowered_pending.0.saturating_add(usize::from(standing == Standing::Lowered))
                && self.sources.faulted == sources.faulted && self.lowerings == lowerings
                && usize::from(self.goals) == goals.saturating_add(added_goals)
        },
    )]
    pub(crate) fn read(
        &mut self,
        root: SourceRoot,
        composed: &Composed<'_>,
        standing: Standing,
    )
    {
        let slot = match root {
            | SourceRoot::Strict => &mut self.sources.strict,
            | SourceRoot::Fixture => &mut self.sources.fixture,
            | SourceRoot::Pending => &mut self.sources.pending,
        };
        *slot = slot.one_more();
        match standing {
            | Standing::Refused => self.sources.refused = self.sources.refused.one_more(),
            | Standing::Lowered => {
                self.sources.lowered_pending = self.sources.lowered_pending.one_more();
            },
            | Standing::Pending => return,
            | Standing::Settled | Standing::Unsettled => {},
        }
        if let Composed::Settled {
            ref report,
            ref exercised,
            ..
        } = *composed
        {
            self.tally.absorb(&report.tally());
            self.exercised.absorb(exercised);
            for declaration in report.declarations() {
                if declaration.settlement() == Settlement::Unsettled
                    && unsettled_by(declaration) == Unsettled::Obligations
                {
                    self.goals =
                        DeclarationCount::from(usize::from(self.goals).saturating_add(1_usize));
                }
            }
        }
    }
}

impl fmt::Display for RunReport
{
    /// Writes one line each for the sources, the lowerings, the goals and the
    /// exercised rows, then the settle counts: the ledger size, the
    /// declarations and fixtures, the surviving obligations, the refusals by
    /// class, the declarations' settlement and the seal. Writes no trailing
    /// line terminator.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: sources, lowerings, goals and exercised rows precede the
    ///   settle tally on separate lines, without a trailing line terminator.
    /// - fails: propagates the formatter's write failure.
    /// - panics: none.
    /// - executable: none — the formatter exposes status but not the emitted
    ///   line sequence or its trailing boundary.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — distinct source, lowering and goal counts occupy
    ///   their expected line roles and the report has no trailing CR or LF.
    ///   This observes layout without pinning English sentences or the separate
    ///   tally formatter; arbitrary sink failures are outside the fixture.
    /// - witness: `report::tests::report_rendering_preserves_numeric_roles_and_line_boundaries`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        writeln!(f, "sources: {}", self.sources)?;
        writeln!(f, "lowerings: {}", self.lowerings)?;
        writeln!(f, "goals: {}", usize::from(self.goals))?;
        writeln!(f, "exercised: {}", self.exercised)?;
        fmt::Display::fmt(&self.tally, f)
    }
}

#[cfg(test)]
mod tests
{
    use gandr_core_checker::CheckBudget;
    use gandr_core_checker::CheckingContext;
    use gandr_core_checker::bridge;
    use gandr_core_checker::check_module;
    use gandr_core_term::CoreArena;
    use gandr_core_term::FailureClass;
    use gandr_surface_corpus::CorpusRoot;
    use gandr_surface_corpus::settle;
    use gandr_surface_grammar::built_in;
    use gandr_surface_lowering::DeclarationCount;
    use gandr_surface_lowering::LoweringBudget;
    use gandr_surface_lowering::lower_module;
    use gandr_surface_lowering::namespace::Recognition;
    use gandr_surface_parser::parse;
    use gandr_surface_syntax::SourceText;

    use super::Goals;
    use super::RunReport;
    use super::RunVerdict;
    use super::Shown;
    use super::Verb;
    use super::shown;
    use crate::compose::Composed;
    use crate::compose::LoweringCount;
    use crate::compose::adapt;
    use crate::compose::compose;
    use crate::evaluate::Program;
    use crate::exercised::Exercised;
    use crate::root::SourceRoot;
    use crate::walk::Standing;

    /// The verbs, every one.
    const VERBS: [Verb; 3_usize] = [
        Verb::Check(Goals::Gated),
        Verb::Check(Goals::Reported),
        Verb::Test,
    ];

    #[test]
    fn each_verb_shows_its_declarations()
    {
        let grammar = built_in().expect("the built-in grammar builds");
        let mut lowerings = LoweringCount::default();
        let Ok(Composed::Settled { report, .. }) = compose(
            &grammar,
            CorpusRoot::Fixture,
            SourceText::from(
                r#"@[ checks ] def fixture = 1 ;
def plain = 2 ;
def hole : Integer ;
def broken = missing ;"#,
            ),
            &mut lowerings,
        )
        else {
            panic!("the module settles");
        };
        let rows = [
            ("fixture", [Shown::Counted, Shown::Counted, Shown::Line]),
            ("plain", [Shown::Counted, Shown::Counted, Shown::Counted]),
            ("hole", [Shown::Line, Shown::Goal, Shown::Line]),
            ("broken", [Shown::Line, Shown::Line, Shown::Line]),
        ];
        for ((name, expected), declaration) in rows.into_iter().zip(report.declarations()) {
            assert_eq!(declaration.name().to_string(), name, "admission order");
            for (verb, expected) in VERBS.into_iter().zip(expected) {
                assert_eq!(shown(declaration, verb), expected, "{name} under {verb:?}");
            }
        }
    }

    #[test]
    fn each_count_decides_its_verdict()
    {
        let grammar = built_in().expect("the built-in grammar builds");
        let settled_source = |source: &'static str| {
            let mut lowerings = LoweringCount::default();
            let Ok(composed @ Composed::Settled { .. }) = compose(
                &grammar,
                CorpusRoot::Fixture,
                SourceText::from(source),
                &mut lowerings,
            )
            else {
                panic!("{source} settles");
            };
            composed
        };
        let read = |source: &'static str, standing: Standing| {
            let composed = settled_source(source);
            let mut report = RunReport::default();
            report.read(SourceRoot::Fixture, &composed, standing);
            report
        };
        let all = |report: &RunReport| VERBS.map(|verb| report.verdict(verb));

        assert_eq!(
            all(&read("def a = 1 ;", Standing::Settled)),
            [RunVerdict::Settled; 3_usize],
            "a settled run is settled under every verb"
        );
        assert_eq!(
            all(&read("def a : Integer ;", Standing::Unsettled)),
            [
                RunVerdict::Unsettled,
                RunVerdict::Settled,
                RunVerdict::Unsettled
            ],
            "an undeclared obligation is a goal under check --goals alone"
        );
        assert_eq!(
            all(&read(
                "def a : Integer ; def b = missing ;",
                Standing::Unsettled
            )),
            [RunVerdict::Unsettled; 3_usize],
            "one unsettled declaration beyond the goals fails every verb"
        );
        assert_eq!(
            all(&read("def a = 1 ;", Standing::Refused)),
            [RunVerdict::Unsettled; 3_usize],
            "a source refused as a whole fails every verb"
        );
        assert_eq!(
            all(&read("def a = 1 ;", Standing::Lowered)),
            [RunVerdict::Unsettled; 3_usize],
            "a pending source the lowering read fails every verb"
        );
        let mut faulted = read("def a : Integer ;", Standing::Unsettled);
        faulted.faulted();
        assert_eq!(
            all(&faulted),
            [RunVerdict::Faulted; 3_usize],
            "a faulted path faults every verb, over any unsettled declaration"
        );

        let source = SourceText::from(r#"@[ refuses("BudgetExceeded") ] def a = 1 ;"#);
        let tree = parse(&grammar, source).expect("parses").into_tree();
        let mut arena = CoreArena::new();
        let module = lower_module(
            &grammar,
            &tree,
            &mut arena,
            LoweringBudget::DEFAULT,
            Recognition::default(),
        )
        .expect("the module lowers");
        let verdicts = check_module(
            &mut CheckingContext::new(&mut arena, CheckBudget::from(0_usize)),
            &adapt(&module),
        );
        let kernel = bridge::readmit(&mut arena, &verdicts).export(module.structured_names());
        let mut program = Program::new(&arena, &module, &verdicts);
        let composed = Composed::Settled {
            report: settle(
                CorpusRoot::Fixture,
                &arena,
                &module,
                &verdicts,
                &mut program,
            )
            .expect("the verdicts are the module's"),
            exercised: Exercised::default(),
            unstatable: Vec::new(),
            kernel,
            origins: module.into_origins(),
            program,
        };
        let mut engine = RunReport::default();
        engine.read(SourceRoot::Fixture, &composed, Standing::Settled);
        assert_eq!(
            engine.tally().refusals().count(FailureClass::EngineFault),
            DeclarationCount::from(1_usize),
            "an exhausted allowance is the engine's fault"
        );
        assert_eq!(
            usize::from(engine.tally().declarations().unsettled()),
            0_usize,
            "the declaration states its refusal, so it settles"
        );
        assert_eq!(
            all(&engine),
            [RunVerdict::Faulted; 3_usize],
            "an engine refusal faults every verb, even one a declaration states"
        );
    }

    #[test]
    fn source_counts_saturate_without_counting_refusals()
    {
        let mut report = RunReport {
            sources: super::SourceCounts {
                strict: super::SourceCount(usize::MAX.saturating_sub(1)),
                fixture: super::SourceCount(1),
                pending: super::SourceCount(1),
                refused: super::SourceCount(7),
                lowered_pending: super::SourceCount(11),
                faulted: super::SourceCount(usize::MAX.saturating_sub(1)),
            },
            ..RunReport::default()
        };
        assert_eq!(usize::MAX, usize::from(report.sources().read()));
        let before = report.sources();
        report.faulted();
        assert_eq!(usize::MAX, usize::from(report.sources().faulted()));
        report.faulted();
        assert_eq!(usize::MAX, usize::from(report.sources().faulted()));
        assert_eq!(before.strict(), report.sources().strict());
        assert_eq!(before.fixture(), report.sources().fixture());
        assert_eq!(before.pending(), report.sources().pending());
        assert_eq!(before.refused(), report.sources().refused());
        assert_eq!(before.lowered_pending(), report.sources().lowered_pending());
    }

    #[test]
    fn pending_sources_do_not_contribute_declarations_or_goals()
    {
        let grammar = built_in().expect("the built-in grammar builds");
        let compose_source = |source: &'static str| {
            let mut lowerings = LoweringCount::default();
            compose(
                &grammar,
                CorpusRoot::Fixture,
                SourceText::from(source),
                &mut lowerings,
            )
            .expect("the fixture composes")
        };
        let ordinary = compose_source(
            "def identity : +U (Integer -> -F Integer) ; def identity = thunk { fn (x) { ret x } } ; def hole : Integer ;",
        );
        let pending = compose_source(
            "def rec f(x: Integer) -> -F Integer { ret x }\ndef identity : +U (Integer -> -F Integer) ; def identity = thunk { fn (x) { ret x } } ; def hole : Integer ;",
        );
        let mut report = RunReport::default();
        report.read(
            SourceRoot::Fixture,
            &ordinary,
            Standing::of(SourceRoot::Fixture, &ordinary),
        );
        assert_eq!(DeclarationCount::from(1_usize), report.goals());
        assert_eq!(
            DeclarationCount::from(1_usize),
            report
                .exercised()
                .count(crate::exercised::Row::LambdaChecks)
        );
        let before = report;
        let standing = Standing::of(SourceRoot::Pending, &pending);
        assert_eq!(Standing::Pending, standing);
        report.read(SourceRoot::Pending, &pending, standing);
        assert_eq!(before.tally(), report.tally());
        assert_eq!(before.exercised(), report.exercised());
        assert_eq!(before.goals(), report.goals());
        assert_eq!(super::SourceCount(1), report.sources().pending());
        let standing = Standing::of(SourceRoot::Pending, &ordinary);
        assert_eq!(Standing::Lowered, standing);
        report.read(SourceRoot::Pending, &ordinary, standing);
        assert_eq!(super::SourceCount(2), report.sources().pending());
        assert_eq!(super::SourceCount(1), report.sources().lowered_pending());
        assert_eq!(DeclarationCount::from(2_usize), report.goals());
        assert_eq!(
            DeclarationCount::from(2_usize),
            report
                .exercised()
                .count(crate::exercised::Row::LambdaChecks)
        );
    }

    #[test]
    fn report_rendering_preserves_numeric_roles_and_line_boundaries()
    {
        let report = RunReport {
            sources: super::SourceCounts {
                strict: super::SourceCount(2),
                fixture: super::SourceCount(3),
                pending: super::SourceCount(5),
                refused: super::SourceCount(7),
                lowered_pending: super::SourceCount(11),
                faulted: super::SourceCount(13),
            },
            lowerings: LoweringCount::from(23_usize),
            goals: DeclarationCount::from(29_usize),
            ..RunReport::default()
        };
        let rendered = std::format!("{report}");
        let mut lines = rendered.lines();
        let expected: [&[usize]; 3] = [&[10, 2, 3, 5, 7, 11, 13], &[23], &[29]];
        for counts in expected {
            let line = lines.next().expect("a report line for these count roles");
            assert!(
                line.split(|ch: char| !ch.is_ascii_digit())
                    .filter(|part| !part.is_empty())
                    .map(|part| part.parse::<usize>().expect("decimal digits"))
                    .eq(counts.iter().copied())
            );
        }
        assert!(!rendered.ends_with(['\r', '\n']));
    }
}
