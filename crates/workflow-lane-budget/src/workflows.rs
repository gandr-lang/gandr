//! Each workflow's completed runs timed whole, wall time and job time summed,
//! and held to the summed budget and ceiling `nightly.yml` states for a
//! workflow.
//!
//! A run's summed time is its completed jobs' times together: what the
//! hosted budget counts, since a public repository's minutes are not billed
//! and GitHub's billable timing reads zero. A budgeted workflow is over when
//! the lower median of its runs' summed times passes the budget, or when any
//! run passes the ceiling; each such run is a line naming the job furthest past
//! its own median over the window, the job that grew.
//!
//! Over is a report. The refusal is narrower: a workflow whose newest
//! completed run passed its ceiling ([`Workflows::past_ceiling`]).
//! The window keeps a run past the ceiling for ten nights, so refusing on
//! "over" would hold a workflow red for ten nights after it came back within.
//! The newest run alone turns the next run red, and the next night within
//! clears it.

extern crate alloc;

use alloc::collections::BTreeMap;
use core::fmt;
use core::str::FromStr;

use quenchant_shape::shape::Maybe;

use crate::budget::Lane;
use crate::budget::RunCount;
use crate::budget::Seconds;
use crate::error::BudgetError;
use crate::report::RunId;
use crate::report::Sample;
use crate::report::Standing;
use crate::report::Unsampled;
use crate::report::lower_median;

/// Bytes in a gibibyte, for the cache line's `10.0 GiB`.
const GIBIBYTE: u128 = 1 << 30;

/// A workflow's display name, as its `name:` spells it.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct WorkflowName(String);

impl From<&str> for WorkflowName
{
    /// Names the workflow `name`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a budget is matched to the listed workflow by name,
    ///   so an emptied name leaves the budgeted row unmeasured.
    /// - witness: `workflows::tests::a_budgeted_workflow_is_held_by_its_summed_median`
    #[inline]
    fn from(name: &str) -> Self
    {
        Self(name.to_owned())
    }
}

impl fmt::Display for WorkflowName
{
    /// Writes the workflow's name as it spells it.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each row spells its workflow, so writing nothing
    ///   changes the asserted table.
    /// - witness: `workflows::tests::a_budgeted_workflow_is_held_by_its_summed_median`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(&self.0)
    }
}

/// What a budgeted workflow's runs are held to.
///
/// # Specification
/// - provides: the two limits a summed time is compared with.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Limits
{
    /// The most the lower median of the runs' summed times may take.
    pub budget: Seconds,
    /// The most any one run's summed time may take.
    pub ceiling: Seconds,
}

/// One `--summed` argument: a workflow and its limits.
///
/// # Specification
/// - provides: a budgeted row of the workflow table.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Summed
{
    /// The workflow, by its display name.
    pub workflow: WorkflowName,
    /// What its runs are held to.
    pub limits: Limits,
}

impl FromStr for Summed
{
    type Err = BudgetError;

    /// Reads `NAME=BUDGET/CEILING`: the workflow's display name, `=`, and the
    /// whole seconds of its budget and its ceiling, `/` between them.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the name is the text before the last `=`, trimmed
    ///   and not empty, and the budget and ceiling the decimals either side of
    ///   the `/` after it, the budget at most the ceiling.
    /// - provides: the budgeted workflows from the nightly's arguments.
    /// - fails: [`BudgetError::Summed`] without an `=` or a `/`, with an empty
    ///   name, seconds that are not whole, or a budget past its ceiling.
    /// - panics: none.
    /// - executable: none — the outcome is the parse itself.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a name with a space and an `=`, a missing ceiling, a
    ///   fraction, an empty name and a budget past its ceiling; splitting at
    ///   the first `=`, swapping the two limits or accepting a budget past the
    ///   ceiling changes a parse.
    /// - witness: `workflows::tests::a_summed_budget_reads_name_budget_and_ceiling`
    #[inline]
    fn from_str(text: &str) -> Result<Self, Self::Err>
    {
        let refuse = || BudgetError::Summed {
            text: text.to_owned(),
        };
        let (name, limits) = text.rsplit_once('=').ok_or_else(refuse)?;
        let (budget, ceiling) = limits.split_once('/').ok_or_else(refuse)?;
        let name = name.trim();
        if name.is_empty() {
            return Err(refuse());
        }
        let budget = budget.trim().parse::<Seconds>().ok().ok_or_else(refuse)?;
        let ceiling = ceiling.trim().parse::<Seconds>().ok().ok_or_else(refuse)?;
        if budget > ceiling {
            return Err(refuse());
        }
        Ok(Self {
            workflow: WorkflowName::from(name),
            limits: Limits { budget, ceiling },
        })
    }
}

/// One completed run of a workflow, timed.
///
/// # Specification
/// - provides: a run's wall time and the jobs its summed time adds up.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Timed
{
    /// The run.
    pub run: RunId,
    /// From the run's start to its last update.
    pub wall: Seconds,
    /// Each completed job and its time, whatever its conclusion.
    pub jobs: Vec<Sample>,
}

impl Timed
{
    /// The run's jobs' times together.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Seconds::plus`].
    /// - witness: `workflows::tests::a_budgeted_workflow_is_held_by_its_summed_median`
    #[inline]
    #[must_use]
    pub fn summed(&self) -> Seconds
    {
        self.jobs
            .iter()
            .fold(Seconds::default(), |total, job| total.plus(job.time))
    }
}

/// What `gh api …/actions/cache/usage` reports: the active caches' bytes and
/// count.
///
/// # Specification
/// - provides: the cache line of the workflow table.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CacheUsage
{
    /// The bytes the active caches hold.
    bytes: u64,
    /// How many caches are active.
    caches: u64,
}

impl FromStr for CacheUsage
{
    type Err = NotAUsage;

    /// Reads `BYTES<TAB>COUNT`, the line the cache query prints.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the bytes are the decimal before the tab and the
    ///   count the decimal after it, surrounding whitespace ignored.
    /// - provides: the cache usage from `gh`'s output.
    /// - fails: [`NotAUsage::Shape`] without a tab or with a part that is not a
    ///   whole number.
    /// - panics: none.
    /// - executable: none — the outcome is the parse itself.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a usage read and rendered, and a line without a tab;
    ///   swapping the two parts changes the line rendered.
    /// - witness: `workflows::tests::the_cache_reads_as_gibibytes_and_caches`
    #[inline]
    fn from_str(line: &str) -> Result<Self, Self::Err>
    {
        let (bytes, caches) = line.trim().split_once('\t').ok_or(NotAUsage::Shape)?;
        Ok(Self {
            bytes: bytes.parse().ok().ok_or(NotAUsage::Shape)?,
            caches: caches.parse().ok().ok_or(NotAUsage::Shape)?,
        })
    }
}

impl fmt::Display for CacheUsage
{
    /// Writes the usage as `10.0 GiB in 144 caches`: gibibytes to one decimal,
    /// rounded down, and the count.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a usage just past ten gibibytes; dividing by a
    ///   thousand cubed or dropping the tenths changes the line.
    /// - witness: `workflows::tests::the_cache_reads_as_gibibytes_and_caches`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let tenths = u128::from(self.bytes)
            .saturating_mul(10)
            .checked_div(GIBIBYTE)
            .unwrap_or_default();
        let whole = tenths.checked_div(10).unwrap_or_default();
        let tenth = tenths.checked_rem(10).unwrap_or_default();
        let caches = if self.caches == 1 { "cache" } else { "caches" };
        write!(f, "{whole}.{tenth} GiB in {} {caches}", self.caches)
    }
}

/// Why a line is not a cache usage.
///
/// # Specification
/// - provides: the one way a cache line is refused.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NotAUsage
{
    /// The line is not two whole numbers and a tab between them.
    Shape,
}

/// Why a workflow's row is held to nothing.
///
/// # Specification
/// - provides: the one reason a row has no limits.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Unbudgeted
{
    /// No `--summed` argument names the workflow.
    NoSummedBudget,
}

/// One workflow's line of the table.
///
/// # Specification
/// - provides: the workflow, its runs timed, and its limits when budgeted.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Row
{
    /// The workflow.
    workflow: WorkflowName,
    /// Its completed runs sampled, newest first.
    runs: Vec<Timed>,
    /// What it is held to.
    limits: Maybe<Limits, Unbudgeted>,
}

impl Row
{
    /// The lower median of the runs' summed times.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`lower_median`] and [`Timed::summed`].
    /// - witness: `workflows::tests::a_budgeted_workflow_is_held_by_its_summed_median`
    fn summed(&self) -> Maybe<Seconds, Unsampled>
    {
        lower_median(self.runs.iter().map(Timed::summed).collect())
    }

    /// How many runs' summed time passes `limit`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a run at the budget and one past it; a count of runs
    ///   at or past changes the column.
    /// - witness: `workflows::tests::a_budgeted_workflow_is_held_by_its_summed_median`
    fn passing(
        &self,
        limit: Seconds,
    ) -> RunsPast
    {
        RunsPast(self.runs.iter().filter(|run| run.summed() > limit).count())
    }

    /// How the workflow stands against its limits.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Standing::Unmeasured`] without a run; for a budgeted row,
    ///   [`Standing::Over`] when the summed median passes the budget or any run
    ///   passes the ceiling, [`Standing::Within`] otherwise; an unbudgeted row
    ///   with runs is within.
    /// - provides: the row's share of the report's verdict.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the outcome is the comparison itself.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a median past the budget, a median within with one
    ///   run past the ceiling, both within, an unbudgeted row past every limit
    ///   and a row with no run; dropping either test or holding an unbudgeted
    ///   row changes a verdict.
    /// - witness: `workflows::tests::a_budgeted_workflow_is_held_by_its_summed_median`
    /// - witness: `workflows::tests::a_run_over_the_ceiling_names_the_job_that_grew`
    fn standing(&self) -> Standing
    {
        match (self.summed(), self.limits) {
            (Maybe::Absent(Unsampled::NoSuccessfulJob), _) => Standing::Unmeasured,
            (Maybe::Present(median), Maybe::Present(limits))
                if median > limits.budget
                    || self.runs.iter().any(|run| run.summed() > limits.ceiling) =>
            {
                Standing::Over
            },
            (Maybe::Present(_), _) => Standing::Within,
        }
    }

    /// Each run past the ceiling, with the job furthest past its own median
    /// over the row's runs.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: nothing for an unbudgeted row; otherwise one entry per run
    ///   whose summed time passes the ceiling, newest first, holding the run,
    ///   its summed time, the ceiling, and the job with the most time past the
    ///   lower median of its name's times in the row's runs, the first such job
    ///   on a tie, with that median.
    /// - provides: the report's account of a night that grew.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the grouping is the clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a run over the ceiling whose longest job is steady
    ///   and whose shorter job grew; naming the longest job, or a run within
    ///   the ceiling, changes the lines.
    /// - witness: `workflows::tests::a_run_over_the_ceiling_names_the_job_that_grew`
    fn grown(&self) -> Vec<Grown<'_>>
    {
        let Maybe::Present(limits) = self.limits
        else {
            return Vec::new();
        };
        let mut times: BTreeMap<&Lane, Vec<Seconds>> = BTreeMap::new();
        for job in self.runs.iter().flat_map(|run| &run.jobs) {
            times.entry(&job.lane).or_default().push(job.time);
        }
        let medians: BTreeMap<&Lane, Seconds> = times
            .into_iter()
            .filter_map(|(lane, times)| match lower_median(times) {
                Maybe::Present(median) => Some((lane, median)),
                Maybe::Absent(Unsampled::NoSuccessfulJob) => None,
            })
            .collect();
        let mut grown = Vec::new();
        for run in &self.runs {
            let summed = run.summed();
            if summed <= limits.ceiling {
                continue;
            }
            let mut most: Option<(&Sample, Seconds, Seconds)> = None;
            for job in &run.jobs {
                let median = medians.get(&job.lane).copied().unwrap_or_default();
                let past = job.time.past(median);
                if most.is_none_or(|(_, _, furthest)| past > furthest) {
                    most = Some((job, median, past));
                }
            }
            // A run past the ceiling has run some job.
            if let Some((job, median, _)) = most {
                grown.push(Grown {
                    workflow: &self.workflow,
                    run: run.run,
                    summed,
                    ceiling: limits.ceiling,
                    job,
                    median,
                });
            }
        }
        grown
    }
}

/// How many of a row's runs pass a limit.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct RunsPast(usize);

impl fmt::Display for RunsPast
{
    /// Writes the count in decimal.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each budgeted row's two counts are asserted, so
    ///   writing nothing changes both.
    /// - witness: `workflows::tests::a_budgeted_workflow_is_held_by_its_summed_median`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "{}", self.0)
    }
}

/// A run past its workflow's ceiling and the job that grew the most in it.
///
/// # Specification
/// - provides: one line of the report's account of a night that grew.
#[derive(Clone, Copy, Debug)]
struct Grown<'row>
{
    /// The workflow.
    workflow: &'row WorkflowName,
    /// The run.
    run: RunId,
    /// The run's summed time.
    summed: Seconds,
    /// The ceiling it passed.
    ceiling: Seconds,
    /// The job furthest past its median.
    job: &'row Sample,
    /// That job's median over the row's runs.
    median: Seconds,
}

impl fmt::Display for Grown<'_>
{
    /// Writes one table row: the workflow, the run, its summed time and the
    /// ceiling, then the job that grew with its time and its median.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the line of a run past its ceiling is asserted whole,
    ///   so a dropped or swapped field changes it.
    /// - witness: `workflows::tests::a_run_over_the_ceiling_names_the_job_that_grew`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(
            f,
            "| {} | {} | {} | {} | `{}` | {} | {} |",
            self.workflow,
            self.run,
            self.summed,
            self.ceiling,
            self.job.lane,
            self.job.time,
            self.median
        )
    }
}

/// A budgeted workflow whose newest completed run passed its ceiling: what
/// `lane-budget` refuses after reporting.
///
/// # Specification
/// - provides: one clause of [`BudgetError::Ceiling`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PastCeiling
{
    /// The workflow.
    workflow: WorkflowName,
    /// Its newest completed run.
    run: RunId,
    /// That run's summed time.
    summed: Seconds,
    /// The ceiling it passed.
    ceiling: Seconds,
}

impl fmt::Display for PastCeiling
{
    /// Writes the workflow, the run, its summed time and the ceiling.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the line of a newest run past its ceiling is asserted
    ///   whole, so a dropped or swapped field changes it.
    /// - witness: `workflows::tests::only_the_newest_run_past_the_ceiling_refuses`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(
            f,
            "{} run {}: {} summed, past its {} ceiling",
            self.workflow, self.run, self.summed, self.ceiling
        )
    }
}

/// The workflow table: every listed workflow's runs timed, each budgeted one
/// held to its limits, and the cache's usage.
///
/// # Specification
/// - provides: the part of the report the summed budgets give.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Workflows
{
    /// How many runs each workflow was asked for.
    asked: RunCount,
    /// One row per listed workflow, in the listing's order, then one per
    /// budgeted workflow the listing lacked.
    rows: Vec<Row>,
    /// The cache's usage.
    cache: CacheUsage,
}

impl Workflows
{
    /// The table over `timed`, each workflow's runs as listed, held to
    /// `budgets`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one row per entry of `timed`, in order, carrying the limits
    ///   of the `budgets` entry naming it, the last such on a repeat; then one
    ///   row without runs for each budgeted workflow `timed` lacks, in the
    ///   budgets' order.
    /// - provides: the workflow table.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the matching is the clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a budgeted workflow listed, an unbudgeted one listed
    ///   and a budgeted one missing from the listing; dropping the missing row
    ///   or matching a budget to the wrong workflow changes the table.
    /// - witness: `workflows::tests::a_budgeted_workflow_is_held_by_its_summed_median`
    #[inline]
    #[must_use]
    pub fn new(
        budgets: &[Summed],
        asked: RunCount,
        timed: Vec<(WorkflowName, Vec<Timed>)>,
        cache: CacheUsage,
    ) -> Self
    {
        let mut limits: BTreeMap<&WorkflowName, Limits> = budgets
            .iter()
            .map(|summed| (&summed.workflow, summed.limits))
            .collect();
        let mut rows: Vec<Row> = timed
            .into_iter()
            .map(|(workflow, runs)| Row {
                limits: limits
                    .remove(&workflow)
                    .map_or(Maybe::Absent(Unbudgeted::NoSummedBudget), Maybe::Present),
                workflow,
                runs,
            })
            .collect();
        for summed in budgets {
            if let Some(limits) = limits.remove(&summed.workflow) {
                rows.push(Row {
                    workflow: summed.workflow.clone(),
                    runs: Vec::new(),
                    limits: Maybe::Present(limits),
                });
            }
        }
        Self { asked, rows, cache }
    }

    /// How the table stands: over when any workflow is over, otherwise within.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Row::standing`].
    /// - witness: `workflows::tests::a_budgeted_workflow_is_held_by_its_summed_median`
    #[inline]
    #[must_use]
    pub fn standing(&self) -> Standing
    {
        if self.rows.iter().any(|row| row.standing() == Standing::Over) {
            Standing::Over
        }
        else {
            Standing::Within
        }
    }

    /// Each budgeted workflow whose newest completed run passed its ceiling.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one entry per budgeted row, in the table's order, whose
    ///   newest run's summed time passes the ceiling; an older run past the
    ///   ceiling, an unbudgeted row and a row without runs give none.
    /// - provides: what `lane-budget` refuses after its report, so a night past
    ///   the ceiling turns the next run red and a night within clears it, where
    ///   [`Workflows::standing`] stays over for the whole window.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the selection is the clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a newest run past the ceiling, an older one past it
    ///   under a newest within, and an unbudgeted workflow past every limit;
    ///   reading any run instead of the newest, or holding an unbudgeted row,
    ///   changes the entries.
    /// - witness: `workflows::tests::only_the_newest_run_past_the_ceiling_refuses`
    #[inline]
    #[must_use]
    pub fn past_ceiling(&self) -> Vec<PastCeiling>
    {
        self.rows
            .iter()
            .filter_map(|row| match (row.limits, row.runs.first()) {
                (Maybe::Present(limits), Some(newest)) if newest.summed() > limits.ceiling => {
                    Some(PastCeiling {
                        workflow: row.workflow.clone(),
                        run: newest.run,
                        summed: newest.summed(),
                        ceiling: limits.ceiling,
                    })
                },
                (Maybe::Present(_) | Maybe::Absent(Unbudgeted::NoSummedBudget), _) => None,
            })
            .collect()
    }
}

impl fmt::Display for Workflows
{
    /// Writes a sentence naming the window, then the table collapsed under a
    /// one-line summary, with the table of the runs past a ceiling and the
    /// cache sentence inside it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a `<details>` block whose summary counts the workflows,
    ///   states the verdict, and counts the rows over and unmeasured; inside it
    ///   one line per row: workflow, runs, wall median and maximum, summed
    ///   median, the runs past the budget and past the ceiling, `—` for an
    ///   unbudgeted row's two and for a row without runs' times, and its
    ///   standing, `unbudgeted` for a row held to nothing; then each row's
    ///   table of runs past a ceiling under its lead, then the cache sentence.
    /// - provides: the workflow part of the job summary and the issue body.
    /// - fails: propagates the formatter's own write failure.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Workflows::new`] and [`Row::grown`].
    /// - witness: `workflows::tests::a_budgeted_workflow_is_held_by_its_summed_median`
    /// - witness: `workflows::tests::a_run_over_the_ceiling_names_the_job_that_grew`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let counted = |standing: Standing| {
            self.rows
                .iter()
                .filter(|row| row.standing() == standing)
                .count()
        };
        let over = counted(Standing::Over);
        let verdict = if over > 0 { "over" } else { "within" };
        let workflows = if self.rows.len() == 1 {
            "workflow"
        }
        else {
            "workflows"
        };
        writeln!(
            f,
            "\nThe table holds each workflow's summed job time and wall time over its last {} \
             completed runs against the summed budgets in `nightly.yml`.\n",
            usize::from(self.asked)
        )?;
        writeln!(
            f,
            "<details><summary>{} {workflows} — {verdict}: {over} over, {} unmeasured</summary>\n",
            self.rows.len(),
            counted(Standing::Unmeasured)
        )?;
        writeln!(
            f,
            "| workflow | runs | wall median | wall max | summed median | past budget | past \
             ceiling | standing |"
        )?;
        writeln!(f, "| --- | ---: | ---: | ---: | ---: | ---: | ---: | --- |")?;
        let shown = |time: Maybe<Seconds, Unsampled>| match time {
            Maybe::Present(time) => time.to_string(),
            Maybe::Absent(Unsampled::NoSuccessfulJob) => "—".to_owned(),
        };
        for row in &self.rows {
            let walls: Vec<Seconds> = row.runs.iter().map(|run| run.wall).collect();
            let longest = walls
                .iter()
                .max()
                .copied()
                .map_or(Maybe::Absent(Unsampled::NoSuccessfulJob), Maybe::Present);
            let (budget, ceiling, standing) = match row.limits {
                Maybe::Present(limits) => (
                    format!("{} past {}", row.passing(limits.budget), limits.budget),
                    format!("{} past {}", row.passing(limits.ceiling), limits.ceiling),
                    row.standing().to_string(),
                ),
                Maybe::Absent(Unbudgeted::NoSummedBudget) => {
                    ("—".to_owned(), "—".to_owned(), match row.standing() {
                        Standing::Unmeasured => Standing::Unmeasured.to_string(),
                        Standing::Within | Standing::Over => "unbudgeted".to_owned(),
                    })
                },
            };
            writeln!(
                f,
                "| {} | {} | {} | {} | {} | {budget} | {ceiling} | {standing} |",
                row.workflow,
                row.runs.len(),
                shown(lower_median(walls)),
                shown(longest),
                shown(row.summed()),
            )?;
        }
        let grown: Vec<Grown<'_>> = self.rows.iter().flat_map(Row::grown).collect();
        if !grown.is_empty() {
            writeln!(
                f,
                "\nThe table gives each run past its ceiling and the job that grew the most in \
                 it.\n\n| workflow | run | summed | ceiling | job | time | median |\n| --- | ---: \
                 | ---: | ---: | --- | ---: | ---: |"
            )?;
        }
        for line in grown {
            writeln!(f, "{line}")?;
        }
        writeln!(f, "\nThe Actions cache holds {}.\n\n</details>", self.cache)
    }
}

#[cfg(test)]
mod tests
{
    use super::CacheUsage;
    use super::NotAUsage;
    use super::Summed;
    use super::Timed;
    use super::WorkflowName;
    use super::Workflows;
    use crate::budget::Lane;
    use crate::budget::RunCount;
    use crate::budget::Seconds;
    use crate::error::BudgetError;
    use crate::report::RunId;
    use crate::report::Sample;
    use crate::report::Standing;

    /// A run `$id` of `$wall` seconds whose jobs are `$jobs`, seconds and
    /// name.
    macro_rules! timed {
        ($id:literal, $wall:literal, $jobs:expr) => {
            Timed {
                run: $id.parse::<RunId>().unwrap(),
                wall: Seconds::from($wall),
                jobs: $jobs
                    .iter()
                    .map(|&(time, lane): &(u64, &str)| Sample {
                        lane: Lane::from(lane),
                        time: Seconds::from(time),
                    })
                    .collect(),
            }
        };
    }

    /// The usage a fake listing reports: just past ten gibibytes.
    macro_rules! cache {
        () => {
            "10738220202\t144".parse::<CacheUsage>().unwrap()
        };
    }

    #[test]
    fn a_summed_budget_reads_name_budget_and_ceiling()
    {
        let summed = " a = b =900/1200".parse::<Summed>().unwrap();
        assert_eq!(summed.workflow, WorkflowName::from("a = b"));
        assert_eq!(summed.limits.budget, Seconds::from(900));
        assert_eq!(summed.limits.ceiling, Seconds::from(1200));
        for text in [
            "Nightly=900",
            "Nightly=900/12.5",
            "=900/1200",
            "Nightly=1200/900",
            "Nightly",
        ] {
            assert_eq!(
                text.parse::<Summed>(),
                Err(BudgetError::Summed {
                    text: text.to_owned()
                }),
                "{text}"
            );
        }
    }

    #[test]
    fn the_cache_reads_as_gibibytes_and_caches()
    {
        assert_eq!(cache!().to_string(), "10.0 GiB in 144 caches");
        assert_eq!(
            "1610612736\t1".parse::<CacheUsage>().unwrap().to_string(),
            "1.5 GiB in 1 cache"
        );
        assert_eq!(
            "10738220202 144".parse::<CacheUsage>(),
            Err(NotAUsage::Shape)
        );
    }

    #[test]
    fn a_budgeted_workflow_is_held_by_its_summed_median()
    {
        let budgets = [
            "Nightly=500/700".parse::<Summed>().unwrap(),
            "Coverage=60/120".parse::<Summed>().unwrap(),
        ];
        let table = |nightly: &[(u64, &str)]| {
            Workflows::new(
                &budgets,
                "3".parse::<RunCount>().unwrap(),
                vec![
                    (WorkflowName::from("CI"), vec![timed!("31", 2000, [(
                        3000, "test",
                    )])]),
                    (WorkflowName::from("Nightly"), vec![
                        timed!("6", 400, nightly),
                        timed!("5", 300, [(400, "sweep"), (100, "test")]),
                        timed!("4", 200, [(300, "sweep"), (200, "test")]),
                    ]),
                ],
                cache!(),
            )
        };
        // Summed 600, 500 and 500: the median is at the budget, and one run
        // past it is within the ceiling.
        let within = table(&[(500, "sweep"), (100, "test")]);
        assert_eq!(within.standing(), Standing::Within);
        assert_eq!(
            within.to_string(),
            "\nThe table holds each workflow's summed job time and wall time over its last 3 \
             completed runs against the summed budgets in `nightly.yml`.\n\n\
             <details><summary>3 workflows — within: 0 over, 1 unmeasured</summary>\n\n\
             | workflow | runs | wall median | wall max | summed median | past budget | past \
             ceiling | standing |\n\
             | --- | ---: | ---: | ---: | ---: | ---: | ---: | --- |\n\
             | CI | 1 | 33m 20s | 33m 20s | 50m 0s | — | — | unbudgeted |\n\
             | Nightly | 3 | 5m 0s | 6m 40s | 8m 20s | 1 past 8m 20s | 0 past 11m 40s | within |\n\
             | Coverage | 0 | — | — | — | 0 past 1m 0s | 0 past 2m 0s | unmeasured |\n\
             \nThe Actions cache holds 10.0 GiB in 144 caches.\n\n</details>\n"
        );
        // Summed 700, 500 and 600 after the third run grows: the median, 600,
        // passes the budget.
        let over = Workflows::new(
            &budgets,
            "3".parse::<RunCount>().unwrap(),
            vec![(WorkflowName::from("Nightly"), vec![
                timed!("6", 400, [(600, "sweep"), (100, "test")]),
                timed!("5", 300, [(400, "sweep"), (100, "test")]),
                timed!("4", 200, [(400, "sweep"), (200, "test")]),
            ])],
            cache!(),
        );
        assert_eq!(over.standing(), Standing::Over);
        assert!(
            over.to_string()
                .contains("| Nightly | 3 | 5m 0s | 6m 40s | 10m 0s | 2 past 8m 20s | 0 past 11m 40s | **over** |"),
            "{over}"
        );
    }

    #[test]
    fn a_run_over_the_ceiling_names_the_job_that_grew()
    {
        let budgets = ["Nightly=900/1000".parse::<Summed>().unwrap()];
        // The sweep is the longest job every night and steady; the tests grew
        // on run 6, which alone passes the ceiling.
        let table = Workflows::new(
            &budgets,
            "3".parse::<RunCount>().unwrap(),
            vec![(WorkflowName::from("Nightly"), vec![
                timed!("6", 700, [(600, "sweep"), (500, "test"), (10, "file")]),
                timed!("5", 600, [(610, "sweep"), (200, "test"), (10, "file")]),
                timed!("4", 600, [(590, "sweep"), (210, "test"), (10, "file")]),
            ])],
            cache!(),
        );
        assert_eq!(table.standing(), Standing::Over);
        let text = table.to_string();
        assert!(
            text.contains(
                "| Nightly | 3 | 10m 0s | 11m 40s | 13m 40s | 1 past 15m 0s | 1 past 16m 40s | \
                 **over** |\n\
                 \nThe table gives each run past its ceiling and the job that grew the most in \
                 it.\n\n| workflow | run | summed | ceiling | job | time | median |\n\
                 | --- | ---: | ---: | ---: | --- | ---: | ---: |\n\
                 | Nightly | 6 | 18m 30s | 16m 40s | `test` | 8m 20s | 3m 30s |\n\
                 \nThe Actions cache holds"
            ),
            "{text}"
        );
    }

    #[test]
    fn only_the_newest_run_past_the_ceiling_refuses()
    {
        let budgets = [
            "Nightly=900/1200".parse::<Summed>().unwrap(),
            "Weekly=900/1200".parse::<Summed>().unwrap(),
        ];
        let runs = |newest: u64| {
            vec![
                timed!("9", 900, [(newest, "sweep"), (200, "test")]),
                timed!("8", 900, [(1300, "sweep"), (200, "test")]),
            ]
        };
        // Nightly's newest run passes the ceiling; Weekly's only an older one
        // does; Release, unbudgeted, passes every limit.
        let table = Workflows::new(
            &budgets,
            "2".parse::<RunCount>().unwrap(),
            vec![
                (WorkflowName::from("Nightly"), runs(1100)),
                (WorkflowName::from("Weekly"), runs(500)),
                (WorkflowName::from("Release"), runs(5000)),
            ],
            cache!(),
        );
        let past: Vec<String> = table
            .past_ceiling()
            .iter()
            .map(ToString::to_string)
            .collect();
        assert_eq!(past, [
            "Nightly run 9: 21m 40s summed, past its 20m 0s ceiling"
        ]);
    }
}
