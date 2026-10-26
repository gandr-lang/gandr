//! A regressed function's issue, whose body indexes its regressions.
//!
//! One table row per pull request (or bare commit) and benchmark: the
//! commit, the series, the metric, the delta, the status and the report's
//! links. The table is written collapsed in a `<details>` block whose summary
//! counts the rows and the open ones. The guard rewrites only the rows and
//! that summary; the prose, the `## Lint` obligation (owed once per function,
//! not per row) and anything a person wrote around the table stay as written,
//! so a hand-folded row in the same columns is read like the guard's own.
//!
//! Each pull request (or bare commit) has one report comment on the issue,
//! found by its marker (`<!-- hotpath: pr=<n> -->`) and linked from its
//! rows: its first regression posts it, and every later run of the same
//! pull request edits it in place — a later regression, a passing run, a
//! shift or an acceptance — so a rerun or a restack never adds a comment.
//!
//! A row is `open`; `fixed` when a later run of its pull request passes its
//! benchmark; `runner shift`; or `accepted`, written when the pull request's
//! body carries a settled `hotpath: accepted` verdict for the benchmark (the
//! verdict a red hotpath check owes before it queues). The issue closes when
//! no row is open and reopens on the next open row.

use core::fmt;
use core::str::FromStr;

use quenchant_shape::shape::Maybe;
use serde::Deserialize;

use crate::check::Benchmark;
use crate::check::CommitSha;
use crate::check::CrateDir;
use crate::check::Repository;
use crate::check::RunUrl;
use crate::check::SiteName;
use crate::check::Unstated;
use crate::report::Regression;
use crate::report::Subject;

/// The opening of every title the guard files, before the function.
pub const TITLE_PREFIX: &str = "perf: ";

/// The label every issue the guard files carries.
pub const KIND: &str = "kind:performance";

/// The label marking an issue the guard keeps: its body indexes rows, its
/// open rows are its work, and settling every row closes it.
pub const COLLECTOR: &str = "collector";

/// The index table's heading row.
const HEADER: &str = "| pull request | commit | series | metric | delta | status | report |";

/// The index table's alignment row.
const SEPARATOR: &str = "| --- | --- | --- | --- | --- | --- | --- |";

/// The opening of the collapsed block the index table stands in, before its
/// summary.
const DETAILS_OPEN: &str = "<details><summary>";

/// The closing of the collapsed block the index table stands in.
const DETAILS_CLOSE: &str = "</details>";

/// The opening of a report cell's comment link.
const COMMENT: &str = "[comment](";

/// An issue's title.
#[repr(transparent)]
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
pub struct IssueTitle(String);

impl IssueTitle
{
    /// The title of `function`'s issue: `perf: ` and its profiled name.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an opened issue's title; a lost name changes the `gh`
    ///   invocation.
    /// - witness: `tests::cli::a_failed_check_opens_one_issue_per_function`
    #[must_use]
    #[inline]
    pub fn of(function: &SiteName) -> Self
    {
        Self(format!("{TITLE_PREFIX}{function}"))
    }

    /// The function a guard-kept title names: the part after `perf: `.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the title after [`TITLE_PREFIX`] when it opens with it and
    ///   the rest does not open with `#`, so a per-pull-request title of the
    ///   earlier shape, `perf: #<n> regresses <site>`, names no function.
    /// - provides: the function whose index a passing run may fix.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the prefix is the clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `perf: gandr_core_checker::module::decide` and `perf:
    ///   #<n> regresses module::decide`; reading the second as a function, or
    ///   the first as none, changes the issues a pass touches.
    /// - witness: `tests::cli::a_passing_run_edits_its_comment_and_marks_its_row_fixed`
    #[must_use]
    #[inline]
    pub fn function(&self) -> Option<SiteName>
    {
        let rest = self
            .0
            .strip_prefix(TITLE_PREFIX)
            .filter(|rest| !rest.starts_with('#'))?;
        rest.parse::<SiteName>().ok()
    }
}

impl fmt::Display for IssueTitle
{
    /// Writes the title.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an opened issue's title; an empty write changes the
    ///   `gh` invocation.
    /// - witness: `tests::cli::a_failed_check_opens_one_issue_per_function`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(&self.0)
    }
}

/// An issue's Markdown body, as `gh` prints it.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq)]
#[serde(transparent)]
pub struct IssueBody(String);

/// A row's standing.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Status
{
    /// The regression stands.
    Open,
    /// A later run of the pull request passed the series.
    Fixed,
    /// The pull request settled the regression as accepted.
    Accepted,
    /// The run moved every function alike: the runner, not the code.
    RunnerShift,
}

/// One row of the index, cell by cell.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
struct Row
{
    /// The seven cells, trimmed: pull request, commit, series, metric,
    /// delta, status, report.
    cells: Vec<String>,
}

/// What a row is found by: its pull request cell and its series cell.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct RowKey<'key>
{
    /// The pull request cell: `#1358`, or a bare commit's short form.
    subject: &'key str,
    /// The series cell: `` `gandr` ``.
    series: &'key str,
}

/// A row key as this run writes it.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Key
{
    /// The pull request cell.
    subject: String,
    /// The series cell.
    series: String,
}

impl Key
{
    /// The key of `subject`'s row in `series`.
    ///
    /// # Specification
    /// trivial.
    fn new(
        subject: &Subject,
        series: &Benchmark,
    ) -> Self
    {
        Self {
            subject: subject.to_string(),
            series: format!("`{series}`"),
        }
    }

    /// The key, borrowed for comparison with a row's.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a later run of the same pull request finds its row;
    ///   an empty key appends a second one.
    /// - witness: `tests::cli::a_later_run_edits_its_comment_and_row`
    fn borrowed(&self) -> RowKey<'_>
    {
        RowKey {
            subject: &self.subject,
            series: &self.series,
        }
    }
}

impl Row
{
    /// The row's key: its first and third cells.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a later run of the same pull request finds its row;
    ///   an empty key appends a second one.
    /// - witness: `tests::cli::a_later_run_edits_its_comment_and_row`
    fn key(&self) -> RowKey<'_>
    {
        RowKey {
            subject: self.cells.first().map_or("", String::as_str),
            series: self.cells.get(2).map_or("", String::as_str),
        }
    }

    /// The row's status, read from its status cell's first words.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `fixed`, `accepted` and `runner shift` openings read as their
    ///   status; every other cell, `open` included, reads open, so an
    ///   unreadable row keeps the issue open.
    /// - provides: the standing the issue is closed or reopened by.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the table is the clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the hand-folded `fixed — …` and `runner shift — …`
    ///   rows, and an `accepted — …` row beside an `open` one; reading prose
    ///   after the dash, a settled word as open, or an unknown cell as settled,
    ///   changes whether the issue closes.
    /// - witness: `index::tests::a_hand_folded_index_keeps_its_rows`
    /// - witness: `index::tests::an_open_row_keeps_the_issue_open_and_an_accepted_one_settles`
    fn status(&self) -> Status
    {
        let cell = self.cells.get(5).map_or("", String::as_str);
        let word = cell.split(" — ").next().unwrap_or(cell).trim();
        match word {
            "fixed" => Status::Fixed,
            "accepted" => Status::Accepted,
            "runner shift" => Status::RunnerShift,
            _ => Status::Open,
        }
    }

    /// The report cell's comment link, as written.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a later run keeps its row's comment link; a lost link
    ///   changes the row.
    /// - witness: `tests::cli::a_later_run_edits_its_comment_and_row`
    fn comment(&self) -> Maybe<String, Unstated>
    {
        let cell = self.cells.get(6).map_or("", String::as_str);
        cell.find(COMMENT).map_or(Maybe::Absent(Unstated), |start| {
            Maybe::Present(cell.get(start ..).unwrap_or_default().to_owned())
        })
    }
}

/// What a run does to its subject's report comment on a function's issue.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Comment
{
    /// A regression standing unaccepted and unshifted: the subject's
    /// comment is edited to this run's report, or posted when it has none.
    Owed,
    /// A passing run, a runner shift or an accepted regression: the
    /// subject's comment is edited to this run's report when it has one, and
    /// none is posted.
    Unowed,
}

impl Comment
{
    /// What recording `regression` does to its subject's comment.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Comment::Unowed`] for a runner shift or a regression its
    ///   pull request's body accepts; [`Comment::Owed`] otherwise.
    /// - provides: whether this run may post the subject's first comment.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the cases are the clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a first regression, a shift and an accepted
    ///   regression; a comment posted for the shift or the acceptance, or none
    ///   for the regression, changes the comments.
    /// - witness: `tests::cli::a_failed_check_opens_one_issue_per_function`
    /// - witness: `tests::cli::a_runner_shift_is_read_over_every_function`
    /// - witness: `tests::cli::an_accepted_landing_settles_its_issue_without_a_comment`
    #[must_use]
    #[inline]
    pub const fn of(regression: &Regression) -> Self
    {
        if matches!(regression.shift, Maybe::Present(_))
            || matches!(regression.accepted, Maybe::Present(_))
        {
            Self::Unowed
        }
        else {
            Self::Owed
        }
    }
}

/// Whether the issue stands open or settled.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Standing
{
    /// Some row is open.
    Open,
    /// Every row is fixed, accepted or a runner shift.
    Settled,
}

/// The index a function's issue body holds: the body before the table's
/// rows, the rows, and the body after them.
///
/// The table is written collapsed in a `<details>` block whose summary counts
/// the rows and the open ones.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Index
{
    /// The body's lines through the table's alignment row, without the
    /// collapsed block's opening.
    head: Vec<String>,
    /// The table's rows.
    rows: Vec<Row>,
    /// The body's lines after the table, without the collapsed block's
    /// closing.
    tail: Vec<String>,
}

impl Index
{
    /// The index of a function with no issue yet.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a paragraph naming the function and its crate, an empty `##
    ///   Index` table, the `## Lint` obligation once for the function, and the
    ///   `## Close` rule.
    /// - provides: the body a new issue is opened with.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the text is the clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a function's first regression; a lost section or
    ///   table changes the opened body.
    /// - witness: `tests::cli::a_failed_check_opens_one_issue_per_function`
    #[must_use]
    #[inline]
    pub fn new(
        function: &SiteName,
        krate: &Maybe<CrateDir, Unstated>,
    ) -> Self
    {
        let place = match *krate {
            Maybe::Present(ref krate) => format!(" (`crates/{krate}`)"),
            Maybe::Absent(_) => String::new(),
        };
        let lines = |text: &str| text.split('\n').map(str::to_owned).collect::<Vec<_>>();
        Self {
            head: lines(&format!(
                "The hotpath guard's regressions of `{function}`{place}, as the `hotpath / \
                 <series>` checks measure it: this body is the index, one row per pull request \
                 and series; each pull request's report is one comment below, edited by its \
                 later runs. The guard rewrites the rows and keeps the rest of this body as \
                 written.\n\n## \
                 Index\n\n{HEADER}\n{SEPARATOR}"
            )),
            rows: Vec::new(),
            tail: lines(
                "\n## Lint\n\nOwed once for the function, by the first fix that lands under this \
                 issue: whether a quenchant dylint could have refused the pattern that \
                 regressed, as the rule it would check.\n\n## Close\n\nThe guard closes this \
                 issue when every row is `fixed`, `accepted` or `runner shift`, and reopens it \
                 on the next `open` row. A `runner shift` row states the run's global shift: \
                 the median move of every function both timing reports measure, and how many \
                 they are.\n",
            ),
        }
    }

    /// The index `body` holds.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the heading row is the first line opening with the first six
    ///   columns of [`HEADER`], whatever the seventh is named; the rows are the
    ///   lines starting `|` after it and the line after it, each split into its
    ///   cells; the lines before and after them are kept verbatim, less the
    ///   `<details><summary>` line and blank line just before the heading row
    ///   and the blank line and `</details>` just after the rows, which the
    ///   rendering writes afresh. A body without a heading row keeps all of
    ///   itself, its trailing blank lines dropped, and gains an `## Index`
    ///   table after it.
    /// - provides: the rows the run reads and rewrites; a hand-written row of
    ///   the same columns is a row like any other.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — rendering the read index gives back the body.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the hand-folded index of `decide`'s regressions with
    ///   its prose, lint and close sections and a seventh column named `was`, a
    ///   body without a table, and a table with an open row; a lost line, a row
    ///   read as prose, prose read as a row or a second table changes the
    ///   rewritten body or the standing.
    /// - witness: `index::tests::a_hand_folded_index_keeps_its_rows`
    /// - witness: `index::tests::an_open_row_keeps_the_issue_open_and_an_accepted_one_settles`
    #[must_use]
    #[inline]
    pub fn read(body: &IssueBody) -> Self
    {
        let lines: Vec<String> = body
            .0
            .split('\n')
            .map(|line| line.strip_suffix('\r').unwrap_or(line).to_owned())
            .collect();
        let key = HEADER.rsplitn(3, '|').last().unwrap_or(HEADER);
        let Some(header) = lines.iter().position(|line| line.trim().starts_with(key))
        else {
            let mut head = lines;
            while head.last().is_some_and(|line| line.trim().is_empty()) {
                head.pop();
            }
            head.extend(["", "## Index", "", HEADER, SEPARATOR].map(str::to_owned));
            return Self {
                head,
                rows: Vec::new(),
                tail: vec![String::new()],
            };
        };
        let first = header.saturating_add(2).min(lines.len());
        let end = lines
            .iter()
            .skip(first)
            .position(|line| !line.trim_start().starts_with('|'))
            .map_or(lines.len(), |offset| first.saturating_add(offset));
        let mut lines = lines;
        let mut tail = lines.split_off(end);
        if tail.first().is_some_and(|blank| blank.trim().is_empty())
            && tail
                .get(1)
                .is_some_and(|closing| closing.trim() == DETAILS_CLOSE)
        {
            tail.drain(.. 2);
        }
        let rows = lines
            .split_off(first)
            .into_iter()
            .map(|line| Row {
                cells: line
                    .trim()
                    .trim_matches('|')
                    .split(" | ")
                    .map(|cell| cell.trim().to_owned())
                    .collect(),
            })
            .collect();
        let opening = header.checked_sub(2).filter(|&at| {
            matches!(
                lines.get(at .. header),
                Some([summary, blank])
                    if summary.trim_start().starts_with(DETAILS_OPEN) && blank.trim().is_empty()
            )
        });
        if let Some(at) = opening {
            lines.drain(at .. header);
        }
        Self {
            head: lines,
            rows,
            tail: if tail.is_empty() {
                vec![String::new()]
            }
            else {
                tail
            },
        }
    }

    /// Records `regression` as `subject`'s row in its series.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the subject's row in the series, appended when it had none,
    ///   states the commit, the series, the metric, the delta, `accepted` with
    ///   the body's verdict when the pull request accepts the growth, else
    ///   `runner shift` with the global shift and the functions it is read
    ///   over, else `open`, and the run; its comment is `comment` when this run
    ///   posted or edited one, otherwise the row's earlier comment as written.
    /// - provides: the index after a failed run.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the rendered row is the clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a first regression, a rerun, a shift and an accepted
    ///   regression; a second row for the rerun, a lost comment link, an `open`
    ///   shift, a shift without its median or count, or an `open` acceptance
    ///   changes the index.
    /// - witness: `tests::cli::a_failed_check_opens_one_issue_per_function`
    /// - witness: `tests::cli::a_later_run_edits_its_comment_and_row`
    /// - witness: `tests::cli::a_runner_shift_is_read_over_every_function`
    /// - witness: `tests::cli::an_accepted_landing_settles_its_issue_without_a_comment`
    #[inline]
    pub fn record(
        &mut self,
        regression: &Regression,
        at: &Run<'_>,
        comment: &Maybe<CommentUrl, Unposted>,
    )
    {
        let status = match (&regression.accepted, regression.shift) {
            (&Maybe::Present(ref acceptance), _) => format!("accepted — {acceptance}"),
            (&Maybe::Absent(_), Maybe::Present(shift)) => format!(
                "runner shift — the {} functions both reports time moved {} % at the median, and \
                 none moved past the policy's threshold beside it",
                shift.functions, shift.ratio
            ),
            (&Maybe::Absent(_), Maybe::Absent(_)) => "open".to_owned(),
        };
        let key = Key::new(at.subject, &regression.series);
        let found = self.rows.iter().position(|row| row.key() == key.borrowed());
        let earlier = found
            .and_then(|index| self.rows.get(index))
            .map_or(Maybe::Absent(Unstated), Row::comment);
        let report = match (comment, earlier) {
            (&Maybe::Present(ref url), _) => {
                format!("[run]({}), {COMMENT}{url})", regression.run)
            },
            (&Maybe::Absent(_), Maybe::Present(earlier)) => {
                format!("[run]({}), {earlier}", regression.run)
            },
            (&Maybe::Absent(_), Maybe::Absent(_)) => format!("[run]({})", regression.run),
        };
        let row = Row {
            cells: vec![
                at.subject.to_string(),
                at.commit(),
                format!("`{}`", regression.series),
                regression.metric.to_string(),
                regression.delta.to_string(),
                status,
                report,
            ],
        };
        match found.and_then(|index| self.rows.get_mut(index)) {
            Some(slot) => *slot = row,
            None => self.rows.push(row),
        }
    }

    /// Whether `subject` has an open row in `series`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a hand-folded index's open row, its settled rows and
    ///   a series it has no row in; matching another subject or series, or a
    ///   settled row, changes the standing.
    /// - witness: `index::tests::an_open_row_keeps_the_issue_open_and_an_accepted_one_settles`
    #[must_use]
    #[inline]
    pub fn standing_in(
        &self,
        subject: &Subject,
        series: &Benchmark,
    ) -> Standing
    {
        let key = Key::new(subject, series);
        if self
            .rows
            .iter()
            .any(|row| row.key() == key.borrowed() && row.status() == Status::Open)
        {
            Standing::Open
        }
        else {
            Standing::Settled
        }
    }

    /// Marks `subject`'s open row in `series` fixed by the passing `run`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the subject's open row in the series reads `fixed`, naming
    ///   the series and the passing commit linked to its run; every other row
    ///   is unchanged.
    /// - provides: the index after a passing run.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the rendered row is the clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a pull request's open rows in two series, one of
    ///   which passes; fixing both, or neither, changes the index.
    /// - witness: `tests::cli::a_passing_run_edits_its_comment_and_marks_its_row_fixed`
    #[inline]
    pub fn fix(
        &mut self,
        series: &Benchmark,
        run: &RunUrl,
        at: &Run<'_>,
    )
    {
        let key = Key::new(at.subject, series);
        for row in &mut self.rows {
            if row.key() == key.borrowed()
                && row.status() == Status::Open
                && let Some(cell) = row.cells.get_mut(5)
            {
                *cell = format!(
                    "fixed — `hotpath / {series}` passed at [`{}`]({run})",
                    at.sha.short()
                );
            }
        }
    }

    /// Whether the issue stands open: some row is open.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Standing::Open`] exactly when some row reads open.
    /// - provides: whether the guard closes or reopens the issue.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clause would walk the rows the body walks.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an index whose last open row is fixed, and one
    ///   gaining an open row; leaving either as it stood changes the state.
    /// - witness: `tests::cli::a_passing_run_edits_its_comment_and_marks_its_row_fixed`
    /// - witness: `tests::cli::a_new_regression_reopens_a_settled_issue`
    #[must_use]
    #[inline]
    pub fn standing(&self) -> Standing
    {
        if self.rows.iter().any(|row| row.status() == Status::Open) {
            Standing::Open
        }
        else {
            Standing::Settled
        }
    }
}

impl fmt::Display for Index
{
    /// Writes the body: the lines before the table, the table collapsed in a
    /// `<details>` block, and the lines after it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the head's lines before its heading row; a `<details>` line
    ///   whose summary counts the rows and states the index's standing — the
    ///   count of open rows when any is open, `settled` otherwise — then a
    ///   blank line; the heading and alignment rows; each row; a blank line and
    ///   `</details>`; then the tail.
    /// - fails: propagates the formatter's own write failure.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a hand-folded index written back collapsed, and the
    ///   collapsed body read and written back unchanged; an empty write, a
    ///   second block or a stale summary changes it.
    /// - witness: `index::tests::a_hand_folded_index_keeps_its_rows`
    /// - witness: `index::tests::an_open_row_keeps_the_issue_open_and_an_accepted_one_settles`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let open = self
            .rows
            .iter()
            .filter(|row| row.status() == Status::Open)
            .count();
        let standing = if open > 0 {
            format!("{open} open")
        }
        else {
            String::from("settled")
        };
        let regressions = if self.rows.len() == 1 {
            "regression"
        }
        else {
            "regressions"
        };
        let summary = format!(
            "{DETAILS_OPEN}{} {regressions} — {standing}</summary>",
            self.rows.len()
        );
        let split = self.head.len().saturating_sub(2);
        let (prose, heading) = self.head.split_at(split);
        let rows = self
            .rows
            .iter()
            .map(|row| format!("| {} |", row.cells.join(" | ")));
        let lines: Vec<String> = prose
            .iter()
            .cloned()
            .chain([summary, String::new()])
            .chain(heading.iter().cloned())
            .chain(rows)
            .chain([String::new(), DETAILS_CLOSE.to_owned()])
            .chain(self.tail.iter().cloned())
            .collect();
        f.write_str(&lines.join("\n"))
    }
}

/// The run a row is written for: its subject and commit.
#[derive(Clone, Copy, Debug)]
pub struct Run<'run>
{
    /// The repository.
    pub repository: &'run Repository,
    /// The commit.
    pub sha: &'run CommitSha,
    /// The row's key.
    pub subject: &'run Subject,
}

impl Run<'_>
{
    /// The commit cell: its short form linked to the commit.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a new row's commit cell; another or an empty cell
    ///   changes the row.
    /// - witness: `tests::cli::a_failed_check_opens_one_issue_per_function`
    fn commit(&self) -> String
    {
        format!(
            "[`{}`](https://github.com/{}/commit/{})",
            self.sha.short(),
            self.repository,
            self.sha
        )
    }
}

/// A posted comment's address.
#[repr(transparent)]
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[serde(transparent)]
pub struct CommentUrl(String);

impl FromStr for CommentUrl
{
    type Err = core::convert::Infallible;

    /// Reads a comment's address as written.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the address `gh` prints for a posted comment lands in
    ///   the row's report cell; a lost address changes the row.
    /// - witness: `tests::cli::a_failed_check_opens_one_issue_per_function`
    #[inline]
    fn from_str(text: &str) -> Result<Self, Self::Err>
    {
        Ok(Self(text.to_owned()))
    }
}

impl fmt::Display for CommentUrl
{
    /// Writes the address.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the row's report cell links the posted comment; an
    ///   empty write changes the row.
    /// - witness: `tests::cli::a_failed_check_opens_one_issue_per_function`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(&self.0)
    }
}

/// Why a row records no comment of this run: none was posted or edited.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Unposted;

#[cfg(test)]
mod tests
{
    use super::Index;
    use super::IssueBody;
    use super::Standing;
    use crate::check::Benchmark;
    use crate::report::Subject;

    /// The hand-folded index of `decide`, trimmed to two of its rows.
    const FOLDED: &str = "The hotpath guard's regressions of `gandr_core_checker::module::decide`, folded by hand.

## Index

| pull request | commit | series | metric | delta | status | was |
| --- | --- | --- | --- | --- | --- | --- |
| #1490 | `a71172e2` | `gandr` | allocations avg | 879 → 917, +4.3 % | fixed — its revision took the keystroke 43.7 MB → 7.4 MB | #1493 |
| #1496 | `e6f58bf9` | `gandr-timing` | wall avg | 179 → 235 µs, +31 % | runner shift — every function +25 to +31 % together | #1516 |

## Lint

Owed once for the function.
";

    /// [`FOLDED`] as the guard writes it back: its table collapsed.
    const COLLAPSED: &str = "The hotpath guard's regressions of `gandr_core_checker::module::decide`, folded by hand.

## Index

<details><summary>2 regressions — settled</summary>

| pull request | commit | series | metric | delta | status | was |
| --- | --- | --- | --- | --- | --- | --- |
| #1490 | `a71172e2` | `gandr` | allocations avg | 879 → 917, +4.3 % | fixed — its revision took the keystroke 43.7 MB → 7.4 MB | #1493 |
| #1496 | `e6f58bf9` | `gandr-timing` | wall avg | 179 → 235 µs, +31 % | runner shift — every function +25 to +31 % together | #1516 |

</details>

## Lint

Owed once for the function.
";

    #[test]
    fn a_hand_folded_index_keeps_its_rows()
    {
        let index = Index::read(&IssueBody(FOLDED.to_owned()));
        assert_eq!(index.to_string(), COLLAPSED, "written back collapsed");
        assert_eq!(
            Index::read(&IssueBody(COLLAPSED.to_owned())).to_string(),
            COLLAPSED,
            "a collapsed body is read and written back unchanged"
        );
        assert_eq!(index.standing(), Standing::Settled);
        assert_eq!(
            index.standing_in(
                &"#1496".parse::<Subject>().unwrap(),
                &"gandr-timing".parse::<Benchmark>().unwrap()
            ),
            Standing::Settled
        );
        let bare = Index::read(&IssueBody("A note.\n\n".to_owned())).to_string();
        assert_eq!(
            bare,
            "A note.\n\n## Index\n\n<details><summary>0 regressions — settled</summary>\n\n\
             | pull request | commit | series | metric | delta | status | report |\n| --- | --- | \
             --- | --- | --- | --- | --- |\n\n</details>\n"
        );
    }

    #[test]
    fn an_open_row_keeps_the_issue_open_and_an_accepted_one_settles()
    {
        let body = FOLDED.replace(
            "| #1496 | `e6f58bf9` | `gandr-timing` | wall avg | 179 → 235 µs, +31 % | runner shift \
             — every function +25 to +31 % together | #1516 |",
            "| #1496 | `e6f58bf9` | `gandr-timing` | wall avg | 179 → 235 µs, +31 % | accepted — \
             records cost 31 allocations each | #1516 |\n| #1500 | `0a1b2c3d` | `gandr` | \
             allocations avg | 917 → 950, +3.6 % | open | #1520 |",
        );
        let index = Index::read(&IssueBody(body));
        let written = index.to_string();
        assert!(
            written.contains("<details><summary>3 regressions — 1 open</summary>\n\n"),
            "{written}"
        );
        assert_eq!(
            Index::read(&IssueBody(written.clone())).to_string(),
            written,
            "read and written back unchanged"
        );
        let standing = |subject: &str, series: &str| {
            index.standing_in(
                &subject.parse::<Subject>().unwrap(),
                &series.parse::<Benchmark>().unwrap(),
            )
        };
        assert_eq!(
            standing("#1496", "gandr-timing"),
            Standing::Settled,
            "an accepted row is settled"
        );
        assert_eq!(standing("#1500", "gandr"), Standing::Open);
        assert_eq!(
            index.standing(),
            Standing::Open,
            "the open row keeps the issue open"
        );
    }
}
