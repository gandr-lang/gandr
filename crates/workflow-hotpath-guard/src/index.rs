//! A regressed function's issue, whose body indexes its regressions.
//!
//! One table row per pull request (or bare commit) and benchmark: the
//! commit, the series, the metric, the delta, the status and the report's
//! links. The guard rewrites only the rows; the prose, the `## Lint`
//! obligation (owed once per function, not per row) and anything a person
//! wrote around the table stay as written, so a hand-folded row in the same
//! columns is read like the guard's own.
//!
//! A new regression's report is a comment its row links. A later run of the
//! same pull request and benchmark rewrites the row and adds no comment,
//! unless the set of functions the run regressed changed (the row records
//! the set its comment named) or the row had settled.
//!
//! A row is `open`; `fixed` when a later run of its pull request passes its
//! benchmark; `runner shift`; or `accepted`, written when the pull request's
//! body carries a settled `hotpath: accepted` verdict for the benchmark (the
//! verdict a red hotpath check owes before it queues). The issue closes when
//! no row is open and reopens on the next open row.

extern crate alloc;

use alloc::collections::BTreeSet;
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

/// The index table's heading row.
const HEADER: &str = "| pull request | commit | series | metric | delta | status | report |";

/// The index table's alignment row.
const SEPARATOR: &str = "| --- | --- | --- | --- | --- | --- | --- |";

/// The opening of a report cell's record of its comment's functions.
const WITH: &str = "<!-- with: ";

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
    /// - witness: `tests::cli::a_passing_run_marks_its_row_fixed_without_a_comment`
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

    /// The report cell's comment link and its record of the comment's
    /// functions, as written.
    ///
    /// # Specification
    /// trivial.
    fn comment(&self) -> Maybe<String, Unstated>
    {
        let cell = self.cells.get(6).map_or("", String::as_str);
        cell.find(COMMENT).map_or(Maybe::Absent(Unstated), |start| {
            Maybe::Present(cell.get(start ..).unwrap_or_default().to_owned())
        })
    }
}

/// Whether recording a regression owes its issue a comment.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Comment
{
    /// A new regression: the report is appended as a comment.
    Owed,
    /// A later run of a standing regression, or a runner shift: the row
    /// changes, no comment is added.
    Unowed,
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
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Index
{
    /// The body's lines through the table's alignment row.
    head: Vec<String>,
    /// The table's rows.
    rows: Vec<Row>,
    /// The body's lines after the table.
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
                 and series; each new regression's report is a comment below. The guard \
                 rewrites the rows and keeps the rest of this body as written.\n\n## \
                 Index\n\n{HEADER}\n{SEPARATOR}"
            )),
            rows: Vec::new(),
            tail: lines(
                "\n## Lint\n\nOwed once for the function, by the first fix that lands under this \
                 issue: whether a quenchant dylint could have refused the pattern that \
                 regressed, as the rule it would check.\n\n## Close\n\nThe guard closes this \
                 issue when every row is `fixed`, `accepted` or `runner shift`, and reopens it \
                 on the next `open` row. A `runner shift` row proposes a policy change to the \
                 owner; the guard never applies one.\n",
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
    ///   cells; the lines before and after them are kept verbatim. A body
    ///   without a heading row keeps all of itself, its trailing blank lines
    ///   dropped, and gains an `## Index` table after it.
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
        let tail = lines.split_off(end);
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

    /// Whether recording `regression` for `subject` owes a comment.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Comment::Unowed`] for a runner shift or a regression its
    ///   pull request's body accepts; otherwise [`Comment::Owed`] when the
    ///   subject has no row in the series, its row is not open, or its row's
    ///   comment named other functions than `regressed`; [`Comment::Unowed`]
    ///   for a later run of an open row with the same functions.
    /// - provides: one comment per regression event, none per rerun.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the cases are the clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a first regression, a rerun naming the same
    ///   functions, a rerun naming one more, a shift, and an accepted
    ///   regression; a comment per rerun, none for the changed set, or one for
    ///   the shift or the acceptance changes the comments.
    /// - witness: `tests::cli::a_later_run_updates_its_row_without_a_comment`
    /// - witness: `index::tests::a_changed_set_of_functions_owes_a_comment`
    /// - witness: `tests::cli::an_accepted_landing_settles_its_issue_without_a_comment`
    #[must_use]
    #[inline]
    pub fn owes(
        &self,
        subject: &Subject,
        regression: &Regression,
        regressed: &BTreeSet<SiteName>,
    ) -> Comment
    {
        if matches!(regression.shift, Maybe::Present(_))
            || matches!(regression.accepted, Maybe::Present(_))
        {
            return Comment::Unowed;
        }
        let key = Key::new(subject, &regression.series);
        let Some(row) = self.rows.iter().find(|row| row.key() == key.borrowed())
        else {
            return Comment::Owed;
        };
        let named = match row.comment() {
            Maybe::Present(cell) => cell.contains(&format!("{WITH}{} -->", With(regressed))),
            Maybe::Absent(_) => false,
        };
        if row.status() == Status::Open && named {
            Comment::Unowed
        }
        else {
            Comment::Owed
        }
    }

    /// Records `regression` as `subject`'s row in its series.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the subject's row in the series, appended when it had none,
    ///   states the commit, the series, the metric, the delta, `accepted` with
    ///   the body's verdict when the pull request accepts the growth, else the
    ///   `runner shift` with its proposal, else `open`, and the run; its
    ///   comment is `comment` with `regressed` recorded when one was posted,
    ///   otherwise the row's earlier comment as written.
    /// - provides: the index after a failed run.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the rendered row is the clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a first regression, a rerun, a shift and an accepted
    ///   regression; a second row for the rerun, a lost comment link, an `open`
    ///   shift or an `open` acceptance changes the index.
    /// - witness: `tests::cli::a_failed_check_opens_one_issue_per_function`
    /// - witness: `tests::cli::a_later_run_updates_its_row_without_a_comment`
    /// - witness: `tests::cli::a_uniform_shift_is_a_runner_shift_row_without_a_comment`
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
                "runner shift — the wall time and every regressed function moved {} to {} % \
                 together, calls unchanged, allocations clean; proposed to the owner: raise the \
                 policy's `min_percent_change` by 2.5",
                shift.low, shift.high
            ),
            (&Maybe::Absent(_), Maybe::Absent(_)) => "open".to_owned(),
        };
        let key = Key::new(at.subject, &regression.series);
        let found = self.rows.iter().position(|row| row.key() == key.borrowed());
        let earlier = found
            .and_then(|index| self.rows.get(index))
            .map_or(Maybe::Absent(Unstated), Row::comment);
        let report = match (comment, earlier) {
            (&Maybe::Present(ref url), _) => format!(
                "[run]({}), {COMMENT}{url}) {WITH}{} -->",
                regression.run,
                With(at.regressed)
            ),
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
    /// - witness: `tests::cli::a_passing_run_marks_its_row_fixed_without_a_comment`
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
    /// - witness: `tests::cli::a_passing_run_marks_its_row_fixed_without_a_comment`
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
    /// Writes the body: the lines before the rows, each row, and the lines
    /// after them.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let rows = self
            .rows
            .iter()
            .map(|row| format!("| {} |", row.cells.join(" | ")));
        let lines: Vec<String> = self
            .head
            .iter()
            .cloned()
            .chain(rows)
            .chain(self.tail.iter().cloned())
            .collect();
        f.write_str(&lines.join("\n"))
    }
}

/// The run a row is written for: its subject, commit and regressed set.
#[derive(Clone, Copy, Debug)]
pub struct Run<'run>
{
    /// The repository.
    pub repository: &'run Repository,
    /// The commit.
    pub sha: &'run CommitSha,
    /// The row's key.
    pub subject: &'run Subject,
    /// Every function the run's failed checks regressed.
    pub regressed: &'run BTreeSet<SiteName>,
}

impl Run<'_>
{
    /// The commit cell: its short form linked to the commit.
    ///
    /// # Specification
    /// trivial.
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
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CommentUrl(String);

impl FromStr for CommentUrl
{
    type Err = core::convert::Infallible;

    /// Reads a comment's address as written.
    ///
    /// # Specification
    /// trivial.
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
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(&self.0)
    }
}

/// Why a row records no new comment: none was owed.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Unposted;

/// A set of functions as a report cell records it: comma-separated names.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct With<'set>(&'set BTreeSet<SiteName>);

impl fmt::Display for With<'_>
{
    /// Writes the names, sorted, comma-separated.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let names: Vec<String> = self.0.iter().map(ToString::to_string).collect();
        f.write_str(&names.join(", "))
    }
}

#[cfg(test)]
mod tests
{
    extern crate alloc;

    use alloc::collections::BTreeSet;

    use quenchant_shape::shape::Maybe;

    use super::Comment;
    use super::CommentUrl;
    use super::Index;
    use super::IssueBody;
    use super::Run;
    use super::Standing;
    use crate::check::Benchmark;
    use crate::check::RunUrl;
    use crate::check::SiteName;
    use crate::report::Regression;
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

    #[test]
    fn a_hand_folded_index_keeps_its_rows()
    {
        let index = Index::read(&IssueBody(FOLDED.to_owned()));
        assert_eq!(index.to_string(), FOLDED, "read and written back unchanged");
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
            "A note.\n\n## Index\n\n| pull request | commit | series | metric | delta | status | \
             report |\n| --- | --- | --- | --- | --- | --- | --- |\n"
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
        let index = Index::read(&IssueBody(body.clone()));
        assert_eq!(index.to_string(), body, "read and written back unchanged");
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

    #[test]
    fn a_changed_set_of_functions_owes_a_comment()
    {
        let repository = "gandr-lang/gandr".parse().unwrap();
        let sha = "914a768".parse().unwrap();
        let subject = "#1358".parse::<Subject>().unwrap();
        let decide = "gandr_core_checker::module::decide"
            .parse::<SiteName>()
            .unwrap();
        let one: BTreeSet<SiteName> = [decide.clone()].into();
        let two: BTreeSet<SiteName> =
            [decide.clone(), "lsp keystroke".parse::<SiteName>().unwrap()].into();
        let regression = Regression {
            function: decide.clone(),
            krate: Maybe::Absent(crate::check::Unstated),
            series: "gandr".parse::<Benchmark>().unwrap(),
            run: "https://github.com/gandr-lang/gandr/runs/1"
                .parse::<RunUrl>()
                .unwrap(),
            metric: "allocations".parse().unwrap(),
            delta: "avg `1444 → 2558` **+77%**".parse().unwrap(),
            shift: Maybe::Absent(crate::check::Unshifted),
            accepted: Maybe::Absent(crate::report::Unaccepted),
        };
        let mut index = Index::new(&decide, &Maybe::Absent(crate::check::Unstated));
        assert_eq!(index.owes(&subject, &regression, &one), Comment::Owed);
        index.record(
            &regression,
            &Run {
                repository: &repository,
                sha: &sha,
                subject: &subject,
                regressed: &one,
            },
            &Maybe::Present("https://example.invalid/c/1".parse::<CommentUrl>().unwrap()),
        );
        assert_eq!(index.owes(&subject, &regression, &one), Comment::Unowed);
        assert_eq!(index.owes(&subject, &regression, &two), Comment::Owed);
    }
}
