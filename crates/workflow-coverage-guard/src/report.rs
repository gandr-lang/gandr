//! One upload of `main` against the one before it: the drop the threshold is
//! held against, the files each covers, and each crate's coverage on both
//! sides.

extern crate alloc;

use alloc::collections::BTreeMap;
use core::cmp::Ordering;
use core::fmt;

use anodized::spec;
use quenchant_shape::shape::Maybe;

use crate::codecov::CrateName;
use crate::codecov::MeasuredFile;
use crate::codecov::Repository;
use crate::codecov::Upload;
use crate::measure::Change;
use crate::measure::Coverage;
use crate::measure::Lines;
use crate::measure::Points;

/// The prefix every title the guard files starts with, by which it finds
/// the one open issue.
pub const TITLE_PREFIX: &str = "coverage: main dropped from ";

/// Why a crate has no lines on one side of the comparison.
///
/// # Specification
/// - provides: the one reason a side is empty.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Absent
{
    /// The upload covers no file of the crate.
    NotUploaded,
}

/// What became of a crate between the two uploads.
///
/// # Specification
/// - provides: the change column, ordered worst first: crates gone from the
///   later upload, then moves from the largest fall, then crates new in it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Fate
{
    /// The later upload covers none of its files.
    Vanished,
    /// Both uploads cover it; its coverage moved by this much.
    Moved(Change),
    /// Only the later upload covers it.
    Arrived,
}

impl Ord for Fate
{
    /// Orders vanished crates first, then moves worst first, then arrivals.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Fate::Vanished`] before every [`Fate::Moved`], ordered as
    ///   their changes, before [`Fate::Arrived`].
    /// - provides: the report's row order.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the four rows of the drop witness in their printed
    ///   order; a vanished crate sorted last, or moves sorted best first,
    ///   changes the table.
    /// - witness: `tests::cli::a_drop_opens_the_issue`
    #[spec(ensures: |ret| matches!(ret, Ordering::Equal) == (self == other))]
    #[inline]
    fn cmp(
        &self,
        other: &Self,
    ) -> Ordering
    {
        match (*self, *other) {
            (Self::Vanished, Self::Vanished) | (Self::Arrived, Self::Arrived) => Ordering::Equal,
            (Self::Moved(left), Self::Moved(right)) => left.cmp(&right),
            (Self::Vanished, _) | (Self::Moved(_), Self::Arrived) => Ordering::Less,
            (_, Self::Vanished) | (Self::Arrived, Self::Moved(_)) => Ordering::Greater,
        }
    }
}

impl PartialOrd for Fate
{
    /// As [`Ord::cmp`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn partial_cmp(
        &self,
        other: &Self,
    ) -> Option<Ordering>
    {
        Some(self.cmp(other))
    }
}

/// One crate's line of the table.
///
/// # Specification
/// - provides: the crate, its lines in each upload, and what became of it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Row
{
    /// The crate.
    pub name: CrateName,
    /// Its lines in the earlier upload.
    pub before: Maybe<Lines, Absent>,
    /// Its lines in the later upload.
    pub after: Maybe<Lines, Absent>,
    /// What became of it.
    pub fate: Fate,
}

/// Whether the later upload calls for the issue.
///
/// # Specification
/// - provides: the verdict the issue is filed by.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Standing
{
    /// The coverage fell by more than the threshold, the upload covers fewer
    /// files than the one before, or both.
    Dropped,
    /// Neither.
    Steady,
}

/// The comparison of one upload of `main` with the one before it.
///
/// # Specification
/// - provides: what the guard prints and files.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Comparison
{
    /// The repository both uploads belong to.
    repository: Repository,
    /// The earlier upload.
    before: Upload,
    /// The later upload.
    after: Upload,
    /// How far the coverage may fall before the guard files.
    threshold: Points,
    /// How the coverage moved.
    change: Change,
    /// Every crate whose coverage or missed lines moved, or that one upload
    /// lacks, worst first.
    rows: Vec<Row>,
}

/// The whole of an upload's coverage; an upload with no lines covers
/// nothing.
///
/// # Specification
/// trivial.
fn overall(upload: &Upload) -> Coverage
{
    match upload.totals.lines.coverage() {
        Maybe::Present(coverage) => coverage,
        Maybe::Absent(_) => Coverage::ZERO,
    }
}

/// Each crate's lines summed from `files`.
///
/// # Specification
/// trivial.
fn by_crate(files: Vec<MeasuredFile>) -> BTreeMap<CrateName, Lines>
{
    let mut crates = BTreeMap::new();
    for file in files {
        let lines: &mut Lines = crates.entry(file.path.crate_name()).or_default();
        *lines = lines.plus(file.totals);
    }
    crates
}

impl Comparison
{
    /// Compares `after` with `before`, each crate summed from its upload's
    /// files, the drop held against `threshold`.
    ///
    /// # Specification
    /// - requires: `before_files` and `after_files` are the files of `before`
    ///   and `after`.
    /// - ensures: the change runs from `before`'s coverage to `after`'s; a row
    ///   stands for every crate either upload covers whose coverage or missed
    ///   lines differ, or that one of them lacks, sorted by [`Fate`] then name.
    /// - provides: the comparison the guard prints and files.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clause would rebuild every row, the body
    ///   itself.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two uploads with a crate that fell, one that rose,
    ///   one unchanged, one gone and one new; an unchanged crate listed, a gone
    ///   or new one dropped, or the sides swapped changes the table.
    /// - witness: `report::tests::a_crate_sums_its_files`
    /// - witness: `tests::cli::a_drop_opens_the_issue`
    #[must_use]
    #[inline]
    pub fn new(
        repository: Repository,
        before: Upload,
        before_files: Vec<MeasuredFile>,
        after: Upload,
        after_files: Vec<MeasuredFile>,
        threshold: Points,
    ) -> Self
    {
        let change = overall(&before).change_to(overall(&after));
        let mut earlier = by_crate(before_files);
        let later = by_crate(after_files);
        let mut rows = Vec::new();
        for (name, lines) in later {
            let row = match earlier.remove(&name) {
                Some(previous) => {
                    let fate = match (previous.coverage(), lines.coverage()) {
                        (Maybe::Present(from), Maybe::Present(to)) => {
                            Fate::Moved(from.change_to(to))
                        },
                        _ => Fate::Moved(Change::Held),
                    };
                    if fate == Fate::Moved(Change::Held) && previous.missed() == lines.missed() {
                        continue;
                    }
                    Row {
                        name,
                        before: Maybe::Present(previous),
                        after: Maybe::Present(lines),
                        fate,
                    }
                },
                None => Row {
                    name,
                    before: Maybe::Absent(Absent::NotUploaded),
                    after: Maybe::Present(lines),
                    fate: Fate::Arrived,
                },
            };
            rows.push(row);
        }
        rows.extend(earlier.into_iter().map(|(name, lines)| Row {
            name,
            before: Maybe::Present(lines),
            after: Maybe::Absent(Absent::NotUploaded),
            fate: Fate::Vanished,
        }));
        rows.sort_by(|left, right| {
            left.fate
                .cmp(&right.fate)
                .then_with(|| left.name.cmp(&right.name))
        });
        Self {
            repository,
            before,
            after,
            threshold,
            change,
            rows,
        }
    }

    /// Whether the later upload calls for the issue.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Standing::Dropped`] when the coverage fell by strictly more
    ///   than the threshold or the later upload covers fewer files;
    ///   [`Standing::Steady`] otherwise.
    /// - provides: the verdict the issue is filed by.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clause would restate the body's two tests.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fall over, at and under the threshold, a rise, and
    ///   fewer files with a rise; filing at the threshold, ignoring the file
    ///   count or filing on a rise changes the verdict.
    /// - witness: `report::tests::the_threshold_is_exceeded_not_met`
    #[must_use]
    #[inline]
    pub fn standing(&self) -> Standing
    {
        let fell = matches!(self.change, Change::Fell(points) if points > self.threshold);
        if fell || self.after.totals.files < self.before.totals.files {
            Standing::Dropped
        }
        else {
            Standing::Steady
        }
    }

    /// The issue's title: `coverage: main dropped from X to Y (<sha>)`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`TITLE_PREFIX`], the earlier coverage, ` to `, the later,
    ///   and the later commit's short form in parentheses.
    /// - provides: the title the issue is opened or retitled with.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the 10-20 drop's title; swapped coverages or the
    ///   earlier commit change it.
    /// - witness: `tests::cli::a_drop_opens_the_issue`
    #[spec(ensures: |ret| ret.0.starts_with(TITLE_PREFIX))]
    #[must_use]
    #[inline]
    pub fn title(&self) -> IssueTitle
    {
        IssueTitle(format!(
            "{TITLE_PREFIX}{} to {} ({})",
            overall(&self.before),
            overall(&self.after),
            self.after.sha.short()
        ))
    }
}

/// An issue's title.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IssueTitle(String);

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

/// A cell of the table: a side's coverage, or `—` when it has none.
#[repr(transparent)]
struct CoverageCell(Maybe<Lines, Absent>);

impl fmt::Display for CoverageCell
{
    /// Writes the coverage and ` %`, or `—`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match self.0 {
            Maybe::Present(lines) => match lines.coverage() {
                Maybe::Present(coverage) => write!(f, "{coverage} %"),
                Maybe::Absent(_) => f.write_str("—"),
            },
            Maybe::Absent(_) => f.write_str("—"),
        }
    }
}

/// A cell of the table: a side's missed lines, or `—` when it has none.
#[repr(transparent)]
struct MissedCell(Maybe<Lines, Absent>);

impl fmt::Display for MissedCell
{
    /// Writes the missed lines, or `—`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match self.0 {
            Maybe::Present(lines) => write!(f, "{}", lines.missed()),
            Maybe::Absent(_) => f.write_str("—"),
        }
    }
}

impl fmt::Display for Fate
{
    /// Writes the signed change, `gone` or `new`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Vanished => f.write_str("gone"),
            Self::Moved(change) => change.fmt(f),
            Self::Arrived => f.write_str("new"),
        }
    }
}

impl fmt::Display for Comparison
{
    /// Writes the report as Markdown: the movement, the file counts, the
    /// verdict, and one table row per crate that moved, collapsed under a
    /// summary.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a sentence naming both coverages, both commits linked to
    ///   Codecov, the change and the threshold; a sentence naming both file
    ///   counts; the verdict; the table inside a `<details>` block whose
    ///   summary counts the crates that moved and repeats the verdict, or a
    ///   line saying no crate moved.
    /// - provides: the job summary and the issue's body.
    /// - fails: propagates the formatter's own write failure.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a drop with every row kind and a steady upload; a
    ///   lost row, a swapped column or a wrong verdict line changes the text.
    /// - witness: `tests::cli::a_drop_opens_the_issue`
    /// - witness: `tests::cli::a_steady_upload_files_nothing`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let commit = |upload: &Upload| {
            format!(
                "[{}](https://app.codecov.io/github/{}/commit/{})",
                upload.sha.short(),
                self.repository,
                upload.sha
            )
        };
        writeln!(
            f,
            "Main's coverage moved from {} % at {} to {} % at {}: {} points, against a threshold of {}.",
            overall(&self.before),
            commit(&self.before),
            overall(&self.after),
            commit(&self.after),
            self.change,
            self.threshold
        )?;
        writeln!(
            f,
            "The upload covers {} files; the one before covered {}.\n",
            self.after.totals.files, self.before.totals.files
        )?;
        match self.standing() {
            Standing::Dropped => writeln!(
                f,
                "**Dropped**: a fall over the threshold or fewer files. A second drop updates this issue.\n"
            )?,
            Standing::Steady => writeln!(f, "Steady: within the threshold, no file lost.\n")?,
        }
        if self.rows.is_empty() {
            return writeln!(f, "No crate's coverage moved.");
        }
        let verdict = match self.standing() {
            Standing::Dropped => "dropped",
            Standing::Steady => "steady",
        };
        let crates = if self.rows.len() == 1 {
            "crate"
        }
        else {
            "crates"
        };
        writeln!(
            f,
            "<details><summary>{} {crates} moved — {verdict}</summary>\n",
            self.rows.len()
        )?;
        writeln!(
            f,
            "| crate | before | after | change | missed before | missed after |"
        )?;
        writeln!(f, "| --- | ---: | ---: | ---: | ---: | ---: |")?;
        for row in &self.rows {
            writeln!(
                f,
                "| {} | {} | {} | {} | {} | {} |",
                row.name,
                CoverageCell(row.before),
                CoverageCell(row.after),
                row.fate,
                MissedCell(row.before),
                MissedCell(row.after)
            )?;
        }
        writeln!(f, "\n</details>")
    }
}

#[cfg(test)]
mod tests
{
    use super::Comparison;
    use super::Standing;
    use crate::codecov::MeasuredFile;
    use crate::codecov::Upload;

    /// An upload of commit `$sha` covering `$files` files, `$hits` of
    /// `$lines`.
    macro_rules! upload {
        ($sha:literal, $files:expr, $lines:expr, $hits:expr) => {{
            let (files, lines, hits): (u64, u64, u64) = ($files, $lines, $hits);
            Upload {
                sha: $sha.parse().unwrap(),
                totals: serde_json::from_str(&format!(
                    r#"{{"files":{files},"lines":{lines},"hits":{hits}}}"#
                ))
                .unwrap(),
            }
        }};
    }

    /// A file at `$path` with `$hits` of `$lines` covered.
    macro_rules! measured {
        ($path:literal, $lines:expr, $hits:expr) => {{
            let (lines, hits): (u64, u64) = ($lines, $hits);
            serde_json::from_str::<MeasuredFile>(&format!(
                r#"{{"name":"{}","totals":{{"lines":{lines},"hits":{hits}}}}}"#,
                $path
            ))
            .unwrap()
        }};
    }

    #[test]
    fn a_crate_sums_its_files()
    {
        let comparison = Comparison::new(
            "gandr-lang/gandr".parse().unwrap(),
            upload!("aaaaaaa", 2, 20, 10),
            vec![
                measured!("crates/a/src/x.rs", 10, 5),
                measured!("crates/a/src/y.rs", 10, 5),
            ],
            upload!("bbbbbbb", 2, 20, 15),
            vec![
                measured!("crates/a/src/x.rs", 10, 10),
                measured!("crates/a/src/y.rs", 10, 5),
            ],
            "0.5".parse().unwrap(),
        );
        let text = comparison.to_string();
        assert!(
            text.contains("| a | 50.00 % | 75.00 % | +25.00 | 10 | 5 |"),
            "{text}"
        );
    }

    #[test]
    fn the_threshold_is_exceeded_not_met()
    {
        let compare = |files: u64, hits: u64| {
            Comparison::new(
                "gandr-lang/gandr".parse().unwrap(),
                upload!("aaaaaaa", 10, 10_000, 9_000),
                Vec::new(),
                upload!("bbbbbbb", files, 10_000, hits),
                Vec::new(),
                "0.5".parse().unwrap(),
            )
            .standing()
        };
        assert_eq!(compare(10, 8_949), Standing::Dropped, "0.51 points");
        assert_eq!(compare(10, 8_950), Standing::Steady, "0.50 points");
        assert_eq!(compare(10, 8_951), Standing::Steady, "0.49 points");
        assert_eq!(compare(10, 9_100), Standing::Steady, "a rise");
        assert_eq!(compare(9, 9_100), Standing::Dropped, "a file lost");
    }
}
