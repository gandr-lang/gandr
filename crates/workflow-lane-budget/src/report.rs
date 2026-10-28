//! Each budgeted lane's median over the sampled runs, and the report that
//! compares it with the budget.

extern crate alloc;

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use core::fmt;
use core::num::ParseIntError;
use core::str::FromStr;

use quenchant_shape::shape::Maybe;

use crate::budget::Budget;
use crate::budget::Lane;
use crate::budget::Seconds;
use crate::cone::Cone;
use crate::github::Window;
use crate::workflows::Unbudgeted;
use crate::workflows::Workflows;

/// A workflow run's identifier.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RunId(u64);

impl FromStr for RunId
{
    type Err = ParseIntError;

    /// Reads a run identifier written in decimal.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — runs 3 and 2 are listed and their jobs fetched by
    ///   identifier, so every run read as zero fetches another route.
    /// - witness: `tests::cli::an_over_budget_lane_opens_the_issue`
    #[inline]
    fn from_str(text: &str) -> Result<Self, Self::Err>
    {
        text.parse().map(Self)
    }
}

impl fmt::Display for RunId
{
    /// Writes the identifier in decimal.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each run's jobs are fetched at a route naming it, and
    ///   the report lists the runs read.
    /// - witness: `tests::cli::an_over_budget_lane_opens_the_issue`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "{}", self.0)
    }
}

/// One successful job of a sampled run: its name and how long it ran.
///
/// # Specification
/// - provides: one sample of a lane's job time.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Sample
{
    /// The job's display name.
    pub lane: Lane,
    /// From the job's start to its completion.
    pub time: Seconds,
}

/// Why a sample line could not be read.
///
/// # Specification
/// - provides: the one way a line is not a sample.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NotASample
{
    /// The line is not whole seconds, a tab, and a name.
    Shape,
}

impl FromStr for Sample
{
    type Err = NotASample;

    /// Reads `SECONDS<TAB>NAME`, the line the job query prints.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the time is the decimal before the first tab and
    ///   the lane the rest of the line, which may hold spaces and tabs.
    /// - provides: a job's sample from `gh`'s output.
    /// - fails: [`NotASample::Shape`] without a tab, with an empty name, or
    ///   when the seconds are not a whole number.
    /// - panics: none.
    /// - executable: none — the outcome is the parse itself.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a name with spaces and parentheses, a missing tab, a
    ///   fraction and an empty name; splitting at the last tab or accepting a
    ///   fraction changes a parse.
    /// - witness: `report::tests::a_sample_reads_seconds_then_name`
    #[inline]
    fn from_str(line: &str) -> Result<Self, Self::Err>
    {
        let (seconds, name) = line.split_once('\t').ok_or(NotASample::Shape)?;
        if name.is_empty() {
            return Err(NotASample::Shape);
        }
        let time = seconds.parse::<Seconds>().ok().ok_or(NotASample::Shape)?;
        Ok(Self {
            lane: Lane::from(name),
            time,
        })
    }
}

/// Why a lane has no median.
///
/// # Specification
/// - provides: the one reason a budgeted lane goes unmeasured.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Unsampled
{
    /// No sampled run holds a successful job of the lane.
    NoSuccessfulJob,
}

/// How a lane, or the whole report, stands against its budget.
///
/// # Specification
/// - provides: the verdict the issue is filed or closed by.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Standing
{
    /// The median is at or under the budget.
    Within,
    /// The median exceeds the budget.
    Over,
    /// No sample: neither within nor over.
    Unmeasured,
}

impl fmt::Display for Standing
{
    /// Writes the standing as the report's last column: `within`, `over` or
    /// `unmeasured`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a row within and a row over are asserted, so writing
    ///   nothing changes both.
    /// - witness: `tests::cli::a_run_is_classified_by_the_cone_it_touched`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            Self::Within => "within",
            Self::Over => "**over**",
            Self::Unmeasured => "unmeasured",
        })
    }
}

/// How many samples a row's median comes from.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct SampleCount(usize);

impl fmt::Display for SampleCount
{
    /// Writes the count in decimal.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each row's job count is asserted, so writing nothing
    ///   changes it.
    /// - witness: `tests::cli::a_run_is_classified_by_the_cone_it_touched`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "{}", self.0)
    }
}

/// One budgeted lane's line of the report.
///
/// # Specification
/// - provides: the lane, its cone, its median over the samples of that cone,
///   how many there were, and its budget.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Row
{
    /// The lane, by its job's name.
    pub lane: Lane,
    /// The cone this row holds; a lane without a deep budget is not
    /// cone-classified and its single row is held to its one budget.
    pub cone: Cone,
    /// The lower median of its samples.
    pub median: Maybe<Seconds, Unsampled>,
    /// How many samples the median comes from.
    pub samples: SampleCount,
    /// The budget it is held to.
    pub limit: Seconds,
}

impl Row
{
    /// How the lane stands against its budget.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Standing::Over`] when the median exceeds the limit,
    ///   [`Standing::Within`] when it does not, [`Standing::Unmeasured`]
    ///   without a median.
    /// - provides: the row's verdict.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the outcome is the comparison itself.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a median one second over, one exactly at and none; a
    ///   strict comparison flipped or an unmeasured lane counted over changes
    ///   the verdict.
    /// - witness: `report::tests::a_lane_over_its_budget_puts_the_report_over`
    #[inline]
    #[must_use]
    pub fn standing(&self) -> Standing
    {
        match self.median {
            Maybe::Present(median) if median > self.limit => Standing::Over,
            Maybe::Present(_) => Standing::Within,
            Maybe::Absent(Unsampled::NoSuccessfulJob) => Standing::Unmeasured,
        }
    }
}

/// The lower median of `samples`: the sample at position ⌊(n − 1) / 2⌋ in
/// ascending order, a time some job actually took.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`Maybe::Present`] holding that sample when any exists.
/// - provides: a lane's summary, robust to the slowest runs of a window.
/// - fails: [`Unsampled::NoSuccessfulJob`] for no samples.
/// - panics: none.
/// - executable: none — the sort is the clause.
///
/// # Adequacy
/// - hypothesis: L3 — odd and even counts in shuffled order and none; the upper
///   median, the mean or an unsorted pick changes the value.
/// - witness: `report::tests::the_median_is_a_time_some_job_took`
#[inline]
pub fn lower_median(mut samples: Vec<Seconds>) -> Maybe<Seconds, Unsampled>
{
    samples.sort_unstable();
    let middle = samples
        .len()
        .saturating_sub(1)
        .checked_div(2)
        .unwrap_or_default();
    samples
        .get(middle)
        .copied()
        .map_or(Maybe::Absent(Unsampled::NoSuccessfulJob), Maybe::Present)
}

/// One row per budget, in the budget table's order, over `samples`, each in
/// the cone its run touched.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one row per budget, in order, whose median is the lower median of
///   the samples of its lane and whose count is theirs: the samples in its own
///   cone when the lane has a deep budget, and those of both cones when it has
///   only the one; samples of lanes without a budget are ignored.
/// - provides: the rows of either table.
/// - fails: never.
/// - panics: none.
/// - executable: none — the grouping is the clause.
///
/// # Adequacy
/// - hypothesis: L3 — a cone-classified lane sampled in both cones beside a
///   single-budget lane sampled in both, one sampled three times and one never;
///   grouping by the lane alone, keying a single-budget lane's samples by cone,
///   or dropping the unsampled row changes the rendered report.
/// - witness: `report::tests::the_report_lists_every_budget_in_order`
/// - witness: `report::tests::a_cone_classified_lane_holds_each_cone_to_its_own_budget`
/// - witness: `report::tests::a_single_budget_lane_counts_both_cones`
fn rows(
    budgets: &[Budget],
    samples: Vec<(Cone, Sample)>,
) -> Vec<Row>
{
    let classified: BTreeSet<&Lane> = budgets
        .iter()
        .filter(|budget| budget.cone == Cone::Deep)
        .map(|budget| &budget.lane)
        .collect();
    let mut by_lane: BTreeMap<(Lane, Cone), Vec<Seconds>> = BTreeMap::new();
    for (cone, sample) in samples {
        let cone = if classified.contains(&sample.lane) {
            cone
        }
        else {
            Cone::Surface
        };
        by_lane
            .entry((sample.lane, cone))
            .or_default()
            .push(sample.time);
    }
    budgets
        .iter()
        .map(|budget| {
            let times = by_lane
                .remove(&(budget.lane.clone(), budget.cone))
                .unwrap_or_default();
            Row {
                lane: budget.lane.clone(),
                cone: budget.cone,
                samples: SampleCount(times.len()),
                median: lower_median(times),
                limit: budget.limit,
            }
        })
        .collect()
}

/// The lanes a scheduled window alone holds: the runs sampled and one row
/// per such lane.
///
/// # Specification
/// - provides: one scheduled table of the report.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Scheduled
{
    /// The window the runs were drawn from: never [`Window::Landing`].
    window: Window,
    /// The runs sampled, newest first.
    runs: Vec<RunId>,
    /// One row per budget, in order.
    rows: Vec<Row>,
}

/// The report: the landing runs sampled and one row per budgeted lane, then,
/// for each scheduled window holding lanes of its own, its runs sampled and
/// one row per such lane.
///
/// # Specification
/// - provides: what the nightly run prints and files.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Report
{
    /// The landing runs sampled, newest first.
    runs: Vec<RunId>,
    /// One row per budget, in the budget table's order.
    rows: Vec<Row>,
    /// One table per scheduled window given budgets, in the order given.
    scheduled: Vec<Scheduled>,
    /// The workflow table, when a workflow was given a summed budget.
    workflows: Maybe<Workflows, Unbudgeted>,
}

impl Report
{
    /// Each budget's lane summarised over `samples`, each in the cone its run
    /// touched.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the rows [`rows`] gives for `budgets` and `samples`, and no
    ///   scheduled table.
    /// - provides: the report.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the construction is the clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`rows`].
    /// - witness: `report::tests::the_report_lists_every_budget_in_order`
    #[inline]
    #[must_use]
    pub fn new(
        budgets: &[Budget],
        runs: Vec<RunId>,
        samples: Vec<(Cone, Sample)>,
    ) -> Self
    {
        Self {
            runs,
            rows: rows(budgets, samples),
            scheduled: Vec::new(),
            workflows: Maybe::Absent(Unbudgeted::NoSummedBudget),
        }
    }

    /// The report with the lanes only the scheduled `window` holds: each of
    /// `budgets` summarised over `samples`, the jobs of that window's `runs`.
    ///
    /// # Specification
    /// - requires: `window` is a scheduled window, never [`Window::Landing`].
    /// - ensures: the landing rows and earlier tables unchanged; one more table
    ///   after them, of `window`, with one row per budget, in order, whose
    ///   median is the lower median of the samples of its lane, none
    ///   cone-classified, and whose count is theirs; samples of lanes without a
    ///   budget here are ignored.
    /// - provides: a scheduled table and its share of the standing.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the grouping is the clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a daily lane over budget in the scheduled runs beside
    ///   a landing lane whose job those runs also hold, and a nightly lane held
    ///   over the nightly runs beside both; a scheduled sample counted in
    ///   another table's row, or a scheduled row left out of the standing,
    ///   changes the report.
    /// - witness: `report::tests::a_daily_lane_is_held_over_the_scheduled_runs`
    /// - witness: `report::tests::a_nightly_lane_is_held_over_the_nightly_runs`
    #[inline]
    #[must_use]
    pub fn with_scheduled(
        mut self,
        window: Window,
        budgets: &[Budget],
        runs: Vec<RunId>,
        samples: Vec<Sample>,
    ) -> Self
    {
        let samples = samples
            .into_iter()
            .map(|sample| (Cone::Surface, sample))
            .collect();
        self.scheduled.push(Scheduled {
            window,
            runs,
            rows: rows(budgets, samples),
        });
        self
    }

    /// The report with the workflow table `workflows` after its lane tables.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the lane tables unchanged, and `workflows` written after them
    ///   and counted in the standing.
    /// - provides: the summed budgets' share of the report.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the construction is the clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a workflow over beside lanes within puts the report
    ///   over and its table after theirs; a table dropped or left out of the
    ///   standing changes the filing.
    /// - witness: `tests::cli::a_summed_budget_tables_every_workflow`
    #[inline]
    #[must_use]
    pub fn with_workflows(
        mut self,
        workflows: Workflows,
    ) -> Self
    {
        self.workflows = Maybe::Present(workflows);
        self
    }

    /// How the report stands: over when any lane or workflow is over,
    /// otherwise within.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Standing::Over`] exactly when some row, landing or
    ///   scheduled, is over, or the workflow table is; [`Standing::Within`]
    ///   otherwise, unmeasured rows included.
    /// - provides: whether the issue is opened or closed.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clause would walk every row, the body itself.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Row::standing`], a daily or a nightly row over
    ///   beside landing rows within, and a workflow over beside lanes within.
    /// - witness: `report::tests::a_lane_over_its_budget_puts_the_report_over`
    /// - witness: `report::tests::a_daily_lane_is_held_over_the_scheduled_runs`
    /// - witness: `report::tests::a_nightly_lane_is_held_over_the_nightly_runs`
    /// - witness: `tests::cli::a_summed_budget_tables_every_workflow`
    #[inline]
    #[must_use]
    pub fn standing(&self) -> Standing
    {
        let workflows = match self.workflows {
            Maybe::Present(ref workflows) => workflows.standing(),
            Maybe::Absent(Unbudgeted::NoSummedBudget) => Standing::Within,
        };
        if workflows == Standing::Over
            || self
                .rows
                .iter()
                .chain(self.scheduled.iter().flat_map(|table| &table.rows))
                .any(|row| row.standing() == Standing::Over)
        {
            Standing::Over
        }
        else {
            Standing::Within
        }
    }
}

/// Writes `rows`, sampled over `window` from `runs`, as the report's Markdown
/// table collapsed under a one-line summary: lane, class, median, budget,
/// sample count and standing, the class `daily` for a row of the CI workflow's
/// scheduled window and `nightly` for one of the nightly workflow's, then the
/// runs.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a `<details>` block whose summary counts the lanes, states the
///   table's verdict — over when any row is over, within otherwise — and counts
///   the rows over and unmeasured; inside it the header, one line per row, in
///   order, with an unmeasured median written as `—`, and the runs line.
/// - provides: either table of the report.
/// - fails: propagates the formatter's own write failure.
/// - panics: none.
/// - executable: none — the formatter exposes no readable output buffer.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Report::new`] and [`Report::with_scheduled`].
/// - witness: `report::tests::the_report_lists_every_budget_in_order`
/// - witness: `report::tests::a_daily_lane_is_held_over_the_scheduled_runs`
/// - witness: `report::tests::a_nightly_lane_is_held_over_the_nightly_runs`
fn table(
    f: &mut fmt::Formatter<'_>,
    rows: &[Row],
    window: Window,
    runs: &[RunId],
) -> fmt::Result
{
    let counted = |standing: Standing| rows.iter().filter(|row| row.standing() == standing).count();
    let over = counted(Standing::Over);
    let verdict = if over > 0 { "over" } else { "within" };
    let lanes = if rows.len() == 1 { "lane" } else { "lanes" };
    writeln!(
        f,
        "<details><summary>{} {lanes} — {verdict}: {over} over, {} unmeasured</summary>\n",
        rows.len(),
        counted(Standing::Unmeasured)
    )?;
    writeln!(f, "| lane | class | median | budget | jobs | standing |")?;
    writeln!(f, "| --- | --- | ---: | ---: | ---: | --- |")?;
    for row in rows {
        let median = match row.median {
            Maybe::Present(median) => median.to_string(),
            Maybe::Absent(Unsampled::NoSuccessfulJob) => "—".to_owned(),
        };
        let class: &dyn fmt::Display = match window {
            Window::Landing => &row.cone,
            Window::Scheduled => &"daily",
            Window::Nightly => &"nightly",
        };
        writeln!(
            f,
            "| {} | {class} | {median} | {} | {} | {} |",
            row.lane,
            row.limit,
            row.samples,
            row.standing()
        )?;
    }
    writeln!(f, "\nThe table reads runs {}.\n\n</details>", listed(runs))
}

/// The runs a table sampled, as the line after it lists them.
///
/// # Specification
/// trivial.
///
/// # Adequacy
/// - hypothesis: L3 — one run and two, each run's id in the order sampled; an
///   empty or fixed list, or another separator, changes the runs line.
/// - witness: `report::tests::the_report_lists_every_budget_in_order`
/// - witness: `report::tests::a_daily_lane_is_held_over_the_scheduled_runs`
fn listed(runs: &[RunId]) -> String
{
    runs.iter()
        .map(RunId::to_string)
        .collect::<Vec<_>>()
        .join(", ")
}

impl fmt::Display for Report
{
    /// Writes the report as Markdown: a sentence naming the window, then a
    /// table of lane, class, median, budget, sample count and standing with
    /// the runs, collapsed under its summary; then the same for each scheduled
    /// window given budgets.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one table row per budget, in order, the class beside each
    ///   row, and an unmeasured median written as `—`; a scheduled window's
    ///   table only when budgets were given for it.
    /// - provides: the job summary and the issue body.
    /// - fails: propagates the formatter's own write failure.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Report::new`] and [`Report::with_scheduled`].
    /// - witness: `report::tests::the_report_lists_every_budget_in_order`
    /// - witness: `report::tests::a_daily_lane_is_held_over_the_scheduled_runs`
    /// - witness: `report::tests::a_nightly_lane_is_held_over_the_nightly_runs`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        writeln!(
            f,
            "This report holds each CI lane's median job time against its budget in \
             `nightly.yml`.\n\nThe table holds each lane's median over the last {} merge-queue \
             and pull-request runs of `ci.yml`. The cone a landing touches gives each lane its \
             class.\n",
            self.runs.len()
        )?;
        table(f, &self.rows, Window::Landing, &self.runs)?;
        for scheduled in &self.scheduled {
            let (lanes, workflow) = match scheduled.window {
                Window::Landing | Window::Scheduled => ("daily", "ci.yml"),
                Window::Nightly => ("nightly", "nightly.yml"),
            };
            writeln!(
                f,
                "\nThe table holds the {lanes} lanes' medians over the last {} scheduled runs of \
                 `{workflow}`.\n",
                scheduled.runs.len()
            )?;
            table(f, &scheduled.rows, scheduled.window, &scheduled.runs)?;
        }
        match self.workflows {
            Maybe::Present(ref workflows) => write!(f, "{workflows}"),
            Maybe::Absent(Unbudgeted::NoSummedBudget) => Ok(()),
        }
    }
}

#[cfg(test)]
mod tests
{
    use quenchant_shape::shape::Maybe;

    use super::NotASample;
    use super::Report;
    use super::RunId;
    use super::Sample;
    use super::Standing;
    use super::Unsampled;
    use super::lower_median;
    use crate::budget::Budget;
    use crate::budget::Lane;
    use crate::budget::Seconds;
    use crate::cone::Cone;
    use crate::github::Window;

    #[test]
    fn a_sample_reads_seconds_then_name()
    {
        assert_eq!(
            "581\ttest enforcing targets (linux)".parse::<Sample>(),
            Ok(Sample {
                lane: Lane::from("test enforcing targets (linux)"),
                time: Seconds::from(581),
            })
        );
        assert_eq!(
            "7\ta\tb".parse::<Sample>().map(|sample| sample.lane),
            Ok(Lane::from("a\tb"))
        );
        for line in ["581 check", "1.5\tcheck", "7\t", ""] {
            assert_eq!(line.parse::<Sample>(), Err(NotASample::Shape), "{line:?}");
        }
    }

    #[test]
    fn the_median_is_a_time_some_job_took()
    {
        let times = |seconds: &[u64]| seconds.iter().copied().map(Seconds::from).collect();
        assert_eq!(
            lower_median(times(&[9, 1, 5])),
            Maybe::Present(Seconds::from(5))
        );
        assert_eq!(
            lower_median(times(&[9, 1, 5, 7])),
            Maybe::Present(Seconds::from(5))
        );
        assert_eq!(
            lower_median(Vec::new()),
            Maybe::Absent(Unsampled::NoSuccessfulJob)
        );
    }

    #[test]
    fn the_report_lists_every_budget_in_order()
    {
        let budgets = [
            "check Clippy wall=300".parse::<Budget>().unwrap(),
            "test enforcing targets (macos-arm64)=900".parse().unwrap(),
        ];
        let sample = |time: u64, lane: &str| {
            (Cone::Surface, Sample {
                lane: Lane::from(lane),
                time: Seconds::from(time),
            })
        };
        let report = Report::new(
            &budgets,
            vec!["12".parse::<RunId>().unwrap(), "11".parse().unwrap()],
            vec![
                sample(200, "check Clippy wall"),
                sample(5, "detect changed-file categories"),
                sample(240, "check Clippy wall"),
                sample(181, "check Clippy wall"),
            ],
        );
        assert_eq!(
            report.to_string(),
            "This report holds each CI lane's median job time against its budget in \
             `nightly.yml`.\n\nThe table holds each lane's median over the last 2 merge-queue \
             and pull-request runs of `ci.yml`. The cone a landing touches gives each lane its \
             class.\n\n\
             <details><summary>2 lanes — within: 0 over, 1 unmeasured</summary>\n\n\
             | lane | class | median | budget | jobs | standing |\n\
             | --- | --- | ---: | ---: | ---: | --- |\n\
             | check Clippy wall | surface | 3m 20s | 5m 0s | 3 | within |\n\
             | test enforcing targets (macos-arm64) | surface | — | 15m 0s | 0 | unmeasured |\n\
             \nThe table reads runs 12, 11.\n\n</details>\n"
        );
        assert_eq!(report.standing(), Standing::Within);
    }

    #[test]
    fn a_cone_classified_lane_holds_each_cone_to_its_own_budget()
    {
        let budgets = [
            "test enforcing targets (linux)=360"
                .parse::<Budget>()
                .unwrap(),
            "test enforcing targets (linux):deep=540".parse().unwrap(),
        ];
        let sample = |cone: Cone, time: u64| {
            (cone, Sample {
                lane: Lane::from("test enforcing targets (linux)"),
                time: Seconds::from(time),
            })
        };
        let report = Report::new(
            &budgets,
            vec!["12".parse::<RunId>().unwrap(), "11".parse().unwrap()],
            vec![
                sample(Cone::Surface, 300),
                sample(Cone::Surface, 350),
                sample(Cone::Deep, 500),
                sample(Cone::Deep, 530),
            ],
        );
        assert_eq!(
            report.to_string(),
            "This report holds each CI lane's median job time against its budget in \
             `nightly.yml`.\n\nThe table holds each lane's median over the last 2 merge-queue \
             and pull-request runs of `ci.yml`. The cone a landing touches gives each lane its \
             class.\n\n\
             <details><summary>2 lanes — within: 0 over, 0 unmeasured</summary>\n\n\
             | lane | class | median | budget | jobs | standing |\n\
             | --- | --- | ---: | ---: | ---: | --- |\n\
             | test enforcing targets (linux) | surface | 5m 0s | 6m 0s | 2 | within |\n\
             | test enforcing targets (linux) | deep | 8m 20s | 9m 0s | 2 | within |\n\
             \nThe table reads runs 12, 11.\n\n</details>\n"
        );
        assert_eq!(report.standing(), Standing::Within);
    }

    #[test]
    fn a_single_budget_lane_counts_both_cones()
    {
        let budgets = [
            "join the enforcing shards (linux)=120"
                .parse::<Budget>()
                .unwrap(),
            "test enforcing targets (linux)=360".parse().unwrap(),
            "test enforcing targets (linux):deep=540".parse().unwrap(),
        ];
        let sample = |cone: Cone, lane: &str, time: u64| {
            (cone, Sample {
                lane: Lane::from(lane),
                time: Seconds::from(time),
            })
        };
        let report = Report::new(
            &budgets,
            vec!["12".parse::<RunId>().unwrap(), "11".parse().unwrap()],
            vec![
                sample(Cone::Surface, "join the enforcing shards (linux)", 60),
                sample(Cone::Deep, "join the enforcing shards (linux)", 150),
                sample(Cone::Surface, "test enforcing targets (linux)", 300),
                sample(Cone::Deep, "test enforcing targets (linux)", 500),
            ],
        );
        // The join has one budget, so its deep landing's 150 s counts beside
        // the surface 60 s; the enforcing lane keeps its cones apart.
        let text = report.to_string();
        assert!(
            text.contains(
                "| join the enforcing shards (linux) | surface | 1m 0s | 2m 0s | 2 | within |"
            ),
            "{text}"
        );
        assert!(
            text.contains(
                "| test enforcing targets (linux) | surface | 5m 0s | 6m 0s | 1 | within |"
            ),
            "{text}"
        );
        assert!(
            text.contains(
                "| test enforcing targets (linux) | deep | 8m 20s | 9m 0s | 1 | within |"
            ),
            "{text}"
        );
    }

    #[test]
    fn a_lane_over_its_budget_puts_the_report_over()
    {
        let budgets = ["a=100".parse::<Budget>().unwrap(), "b=100".parse().unwrap()];
        let report = |a: u64, b: u64| {
            Report::new(&budgets, Vec::new(), vec![
                (Cone::Surface, Sample {
                    lane: Lane::from("a"),
                    time: Seconds::from(a),
                }),
                (Cone::Surface, Sample {
                    lane: Lane::from("b"),
                    time: Seconds::from(b),
                }),
            ])
        };
        assert_eq!(report(100, 100).standing(), Standing::Within);
        assert_eq!(report(100, 101).standing(), Standing::Over);
        let unmeasured = Report::new(&budgets, Vec::new(), Vec::new());
        assert_eq!(unmeasured.standing(), Standing::Within);
        assert!(
            unmeasured
                .to_string()
                .contains("| a | surface | — | 1m 40s | 0 | unmeasured |")
        );
    }

    #[test]
    fn a_daily_lane_is_held_over_the_scheduled_runs()
    {
        let sample = |time: u64, lane: &str| Sample {
            lane: Lane::from(lane),
            time: Seconds::from(time),
        };
        let landing = ["check Clippy wall=300".parse::<Budget>().unwrap()];
        let daily = ["mutate the night's crate (linux)=840"
            .parse::<Budget>()
            .unwrap()];
        let report = Report::new(&landing, vec!["12".parse::<RunId>().unwrap()], vec![(
            Cone::Surface,
            sample(200, "check Clippy wall"),
        )]);
        assert_eq!(report.standing(), Standing::Within);
        // The scheduled runs hold a Clippy job too, far over its budget; only
        // the landing runs measure it.
        let report = report.with_scheduled(
            Window::Scheduled,
            &daily,
            vec!["9".parse::<RunId>().unwrap(), "8".parse().unwrap()],
            vec![
                sample(900, "check Clippy wall"),
                sample(850, "mutate the night's crate (linux)"),
                sample(900, "check Clippy wall"),
                sample(880, "mutate the night's crate (linux)"),
            ],
        );
        assert_eq!(
            report.to_string(),
            "This report holds each CI lane's median job time against its budget in \
             `nightly.yml`.\n\nThe table holds each lane's median over the last 1 merge-queue \
             and pull-request runs of `ci.yml`. The cone a landing touches gives each lane its \
             class.\n\n\
             <details><summary>1 lane — within: 0 over, 0 unmeasured</summary>\n\n\
             | lane | class | median | budget | jobs | standing |\n\
             | --- | --- | ---: | ---: | ---: | --- |\n\
             | check Clippy wall | surface | 3m 20s | 5m 0s | 1 | within |\n\
             \nThe table reads runs 12.\n\n</details>\n\
             \nThe table holds the daily lanes' medians over the last 2 scheduled runs of \
             `ci.yml`.\n\n\
             <details><summary>1 lane — over: 1 over, 0 unmeasured</summary>\n\n\
             | lane | class | median | budget | jobs | standing |\n\
             | --- | --- | ---: | ---: | ---: | --- |\n\
             | mutate the night's crate (linux) | daily | 14m 10s | 14m 0s | 2 | **over** |\n\
             \nThe table reads runs 9, 8.\n\n</details>\n"
        );
        assert_eq!(report.standing(), Standing::Over);
    }

    #[test]
    fn a_nightly_lane_is_held_over_the_nightly_runs()
    {
        let sample = |time: u64, lane: &str| Sample {
            lane: Lane::from(lane),
            time: Seconds::from(time),
        };
        let landing = ["check Clippy wall=300".parse::<Budget>().unwrap()];
        let daily = ["mutate the night's crate (linux)=840"
            .parse::<Budget>()
            .unwrap()];
        let nightly = ["test every crate with every feature on=240"
            .parse::<Budget>()
            .unwrap()];
        let report = Report::new(&landing, vec!["12".parse::<RunId>().unwrap()], vec![(
            Cone::Surface,
            sample(200, "check Clippy wall"),
        )])
        .with_scheduled(
            Window::Scheduled,
            &daily,
            vec!["9".parse::<RunId>().unwrap()],
            vec![
                sample(800, "mutate the night's crate (linux)"),
                sample(900, "test every crate with every feature on"),
            ],
        );
        assert_eq!(report.standing(), Standing::Within);
        // The daily runs' all-features job, far over, is not the nightly
        // lane's; the nightly runs alone measure it.
        let report = report.with_scheduled(
            Window::Nightly,
            &nightly,
            vec!["6".parse::<RunId>().unwrap(), "5".parse().unwrap()],
            vec![
                sample(250, "test every crate with every feature on"),
                sample(260, "test every crate with every feature on"),
            ],
        );
        let text = report.to_string();
        assert!(
            text.ends_with(
                "| mutate the night's crate (linux) | daily | 13m 20s | 14m 0s | 1 | within |\n\
                 \nThe table reads runs 9.\n\n</details>\n\
                 \nThe table holds the nightly lanes' medians over the last 2 scheduled runs of \
                 `nightly.yml`.\n\n\
                 <details><summary>1 lane — over: 1 over, 0 unmeasured</summary>\n\n\
                 | lane | class | median | budget | jobs | standing |\n\
                 | --- | --- | ---: | ---: | ---: | --- |\n\
                 | test every crate with every feature on | nightly | 4m 10s | 4m 0s | 2 | **over** |\n\
                 \nThe table reads runs 6, 5.\n\n</details>\n"
            ),
            "{text}"
        );
        assert_eq!(report.standing(), Standing::Over);
    }
}
