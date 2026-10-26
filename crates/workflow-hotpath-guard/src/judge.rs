//! The judgement hotpath Cloud cannot make, written as a check's summary.
//!
//! A commit's runs of one benchmark are judged against its base's, several
//! a side, under the benchmark's policy, and the summary keeps hotpath
//! Cloud's shape ([`crate::check::Failure::read`]), so the guard files it
//! like the Cloud's own.
//!
//! **Rows under the share floor: disjoint runs, not one.**
//! `Store::delete_part`, 0.65 % of the `store` series, fell under
//! `min_percent_total`, which hotpath Cloud never judges, and its 9 % slowdown
//! landed unseen. Dropping the floor would judge such a row on one run a side,
//! where the runner's noise is a larger share of a small row. The floor falls
//! to [`SHARE_FLOOR`] instead, and a row under the policy's floor regresses
//! only when its median moved past `min_percent_change` and every run of the
//! commit lies past every run of the base: three runs on a pull request
//! against the five main's push keeps. A row at or over the floor regresses
//! on its median, as hotpath Cloud judges it on one report a side.
//! **Reversal**: more than one false flag in a day under the floor raises it
//! back toward 1 %; a disjoint flag that proves noise on re-measure means
//! more runs, not a higher floor.

extern crate alloc;

use alloc::collections::BTreeMap;
use core::fmt;

use serde::Deserialize;

use crate::check::CommitSha;
use crate::check::Repository;
use crate::error::GuardError;

pub mod shift;

/// The smallest share of the run a row is judged at: 0.1 %.
pub const SHARE_FLOOR: Share = Share(10);

/// Picoseconds in each unit a timing report writes.
const TIME_UNITS: [(&str, Scale); 5] = [
    ("ns", Scale(1_000)),
    ("µs", Scale(1_000_000)),
    ("us", Scale(1_000_000)),
    ("ms", Scale(1_000_000_000)),
    ("s", Scale(1_000_000_000_000)),
];

/// Thousandths in one allocation count.
const COUNT_SCALE: Scale = Scale(1_000);

/// Hundredths in one percent.
const PERCENT_SCALE: Scale = Scale(100);

/// Each family's policy table and hotpath's default `min_percent_change`.
const FAMILIES: [(Family, &str, Share); 2] = [
    (Family::Timing, "timing", Share(5_000)),
    (Family::Alloc, "alloc", Share(2_000)),
];

/// A share of the run, or a change, in hundredths of a percent.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Share(u128);

/// A measured amount in thousandths of its unit: picoseconds for timing,
/// thousandths of an allocation for counts.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Amount(u128);

/// A decimal number read at a scale.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Fixed(u128);

/// How many of a fixed number's units make one of what it counts.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Scale(u128);

/// The digits of a decimal number, as written.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Digits<'text>(&'text str);

/// A number as a report or a policy writes it: `8.237559 ms`, `73.43%`.
#[repr(transparent)]
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[serde(transparent)]
pub struct Written(String);

/// A row's profiled name.
#[repr(transparent)]
#[derive(Clone, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd)]
#[serde(transparent)]
pub struct RowName(String);

impl fmt::Display for RowName
{
    /// Writes the name.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a summary's site names its function; an empty write
    ///   changes the site the guard reads.
    /// - witness: `judge::tests::a_summary_reads_back_into_its_sites`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(&self.0)
    }
}

/// An `ignore` pattern: `*` matches any run of characters.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
struct Pattern(String);

/// A file the judge reads, and its text.
#[derive(Clone, Copy, Debug)]
pub struct Input<'input>
{
    /// The path, as given; a refusal names it.
    pub path: &'input str,
    /// The file's text.
    pub text: &'input str,
}

impl Input<'_>
{
    /// A refusal naming this file.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a malformed report's refusal names its path; a lost
    ///   path changes the message.
    /// - witness: `judge::tests::a_malformed_report_is_refused_by_its_path`
    fn refuse(
        self,
        message: String,
    ) -> GuardError
    {
        GuardError::Input {
            path: self.path.to_owned(),
            message,
        }
    }
}

/// What a report measures in a section.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Family
{
    /// Wall-clock time per function.
    Timing,
    /// Allocations per function.
    Alloc,
}

impl fmt::Display for Family
{
    /// Writes the family's summary heading, in hotpath Cloud's words.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a timing summary read back as a timing section; the
    ///   allocation heading changes the guard's runner-shift reading.
    /// - witness: `judge::tests::a_summary_reads_back_into_its_sites`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            Self::Timing => "**Functions · timing**",
            Self::Alloc => "**Functions · allocations**",
        })
    }
}

impl Family
{
    /// Reads an amount as this family's report writes it: `8.237559 ms`,
    /// `420 ns`, `92368`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a timing amount is a decimal and one of the units of
    ///   [`TIME_UNITS`], in picoseconds; a count is a bare decimal, in
    ///   thousandths; digits past the unit's resolution are dropped.
    /// - provides: the numbers a row is judged on.
    /// - fails: none — any other text is absent.
    /// - panics: none.
    /// - executable: none — the parse is the clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — milliseconds with six decimals, microseconds with
    ///   two, whole nanoseconds, a count, a count with a unit and a unit
    ///   without a number; a wrong scale or an accepted malformed amount
    ///   changes a reading.
    /// - witness: `judge::tests::an_amount_reads_in_its_unit`
    fn amount(
        self,
        text: &Written,
    ) -> Option<Amount>
    {
        let mut words = text.0.split_whitespace();
        let number = Digits(words.next()?);
        let unit = words.next();
        if words.next().is_some() {
            return None;
        }
        let scale = match (self, unit) {
            (Self::Timing, Some(unit)) => TIME_UNITS
                .iter()
                .find(|&&(name, _)| name == unit)
                .map(|&(_, scale)| scale)?,
            (Self::Alloc, None) => COUNT_SCALE,
            (Self::Timing, None) | (Self::Alloc, Some(_)) => return None,
        };
        decimal(number, scale).map(|Fixed(value)| Amount(value))
    }
}

/// Reads a decimal number at `scale`, dropping digits past one unit.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `8.237559` at 10⁹ is `8_237_559_000`; an empty part either side
///   of the point is refused, as is any character but digits and one point.
/// - provides: every amount, share and threshold the judge compares.
/// - fails: none — malformed text or overflow is absent.
/// - panics: none.
/// - executable: none — the parse is the clause.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Family::amount`].
/// - witness: `judge::tests::an_amount_reads_in_its_unit`
fn decimal(
    number: Digits<'_>,
    scale: Scale,
) -> Option<Fixed>
{
    let (whole, fraction) = number.0.split_once('.').unwrap_or((number.0, ""));
    let digits = |part: &str| !part.is_empty() && part.bytes().all(|byte| byte.is_ascii_digit());
    if !digits(whole) || (number.0.contains('.') && !digits(fraction)) {
        return None;
    }
    let mut value = whole.parse::<u128>().ok()?.checked_mul(scale.0)?;
    let mut place = scale.0;
    for byte in fraction.bytes() {
        place = place.checked_div(10)?;
        let digit = u128::from(byte.checked_sub(b'0')?);
        value = value.checked_add(digit.checked_mul(place)?)?;
    }
    Some(Fixed(value))
}

/// Reads a percentage, a report's `73.43%` or a policy's `7.5`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the number before an optional trailing `%`, in hundredths of a
///   percent; a third decimal is dropped.
/// - provides: a row's share and the policy's thresholds.
/// - fails: none — malformed text is absent.
/// - panics: none.
/// - executable: none — the parse is the clause.
///
/// # Adequacy
/// - hypothesis: L3 — a report's share and a policy's whole and decimal
///   thresholds; a dropped decimal or a scale off by ten changes a reading.
/// - witness: `judge::tests::an_amount_reads_in_its_unit`
fn percent(text: &Written) -> Option<Share>
{
    let number = Digits(text.0.strip_suffix('%').unwrap_or(&text.0));
    decimal(number, PERCENT_SCALE).map(|Fixed(value)| Share(value))
}

/// A row's place in its source.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
struct Location
{
    /// The file, from the repository's root.
    file: String,
    /// The line of the function's attribute.
    line: u64,
}

/// One function's row as a report writes it.
#[derive(Clone, Debug, Deserialize)]
struct RawRow
{
    /// The profiled name.
    name: RowName,
    /// The calls the run made.
    calls: u64,
    /// The average, written with its unit.
    avg: Written,
    /// The sum over the calls, written with its unit.
    total: Written,
    /// The row's share of the run: `73.43%`.
    percent_total: Written,
    /// Where the function is defined; absent for a bench's block.
    location: Option<Location>,
}

/// One section of a report.
#[derive(Clone, Debug, Deserialize)]
struct RawSection
{
    /// The run's wall time, in a timing section.
    total_elapsed_ns: Option<u64>,
    /// The rows.
    data: Vec<RawRow>,
}

/// A report as hotpath writes it, the sections the judge reads.
#[derive(Clone, Debug, Deserialize)]
struct RawReport
{
    /// Time per function.
    functions_timing: Option<RawSection>,
    /// Allocations per function.
    functions_alloc: Option<RawSection>,
}

/// One function's row, its numbers read.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Row
{
    /// The calls the run made.
    calls: u64,
    /// The average.
    avg: Amount,
    /// The sum over the calls.
    total: Amount,
    /// The row's share of the run.
    share: Share,
    /// Where the function is defined.
    location: Option<Location>,
}

/// What a row's spread over a side's runs is taken of.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Reading
{
    /// The calls the run made.
    Calls,
    /// The row's share of the run.
    Share,
    /// A judged metric.
    Metric(Metric),
}

impl Reading
{
    /// The reading's value in a row.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a row judged on its average, its calls and its share;
    ///   reading another field changes the judgement.
    /// - witness: `judge::tests::a_sub_floor_row_regresses_only_over_disjoint_runs`
    /// - witness: `judge::tests::an_ignored_or_rare_row_is_not_judged`
    fn of(
        self,
        row: &Row,
    ) -> Amount
    {
        match self {
            Self::Calls => Amount(u128::from(row.calls)),
            Self::Share => Amount(row.share.0),
            Self::Metric(Metric::Avg) => row.avg,
            Self::Metric(Metric::Total) => row.total,
        }
    }
}

/// One run of a benchmark: its rows per family and its wall time.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Run
{
    /// The wall time, in picoseconds.
    wall: Option<Amount>,
    /// Each family's rows, by profiled name.
    rows: BTreeMap<(Family, RowName), Row>,
}

impl Run
{
    /// Reads one run's JSON report.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: every row of the timing and allocation sections, by family
    ///   and name, with its numbers read in its family's unit; the wall time is
    ///   the timing section's `total_elapsed_ns`.
    /// - provides: one side's runs.
    /// - fails: [`GuardError::Input`] naming the file for text that is not a
    ///   hotpath report or a row whose numbers do not read.
    /// - panics: none.
    /// - executable: none — the parse is the clause.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a report's timing and allocation rows, and a row
    ///   whose average carries no unit; a dropped family or an accepted
    ///   malformed row changes the judgement.
    /// - witness: `judge::tests::a_sub_floor_row_regresses_only_over_disjoint_runs`
    /// - witness: `judge::tests::a_malformed_report_is_refused_by_its_path`
    #[inline]
    pub fn read(input: Input<'_>) -> Result<Self, GuardError>
    {
        let report: RawReport =
            serde_json::from_str(input.text).map_err(|error| input.refuse(error.to_string()))?;
        let mut run = Self {
            wall: report
                .functions_timing
                .as_ref()
                .and_then(|section| section.total_elapsed_ns)
                .and_then(|ns| u128::from(ns).checked_mul(1_000))
                .map(Amount),
            rows: BTreeMap::new(),
        };
        for (family, section) in [
            (Family::Timing, report.functions_timing),
            (Family::Alloc, report.functions_alloc),
        ] {
            for raw in section.map(|section| section.data).unwrap_or_default() {
                let number = |text: &Written| {
                    family.amount(text).ok_or_else(|| {
                        input.refuse(format!("`{}` reads no amount from `{}`", raw.name, text.0))
                    })
                };
                let row = Row {
                    calls: raw.calls,
                    avg: number(&raw.avg)?,
                    total: number(&raw.total)?,
                    share: percent(&raw.percent_total).ok_or_else(|| {
                        input.refuse(format!(
                            "`{}` reads no share from `{}`",
                            raw.name, raw.percent_total.0
                        ))
                    })?,
                    location: raw.location,
                };
                drop(run.rows.insert((family, raw.name), row));
            }
        }
        Ok(run)
    }
}

/// A metric a family is judged on.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Metric
{
    /// The average per call.
    Avg,
    /// The sum over the calls.
    Total,
}

impl fmt::Display for Metric
{
    /// Writes the metric's name, as a policy and a summary write it.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a site line names its metric; a swapped name changes
    ///   the line.
    /// - witness: `judge::tests::a_summary_reads_back_into_its_sites`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            Self::Avg => "avg",
            Self::Total => "total",
        })
    }
}

/// How a family is judged: the policy's block, when it fails the check.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Judged
{
    /// The smallest change that counts.
    change: Share,
    /// The metrics judged.
    metrics: Vec<Metric>,
    /// Rows with fewer calls on both sides are not judged.
    min_calls: Amount,
}

/// Whether a policy judges a row.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Coverage
{
    /// The policy judges it.
    Judged,
    /// An `ignore` pattern matches it.
    Ignored,
}

/// A benchmark's regression policy, the keys the judge reads.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Policy
{
    /// The share at and over which a single median decides
    /// (`min_percent_total`).
    floor: Share,
    /// Names never judged.
    ignore: Vec<Pattern>,
    /// Each family that fails the check, with its block.
    families: Vec<(Family, Judged)>,
}

impl Policy
{
    /// Reads a policy file as hotpath Cloud does, the keys the judge uses.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the `[functions]` table's `min_percent_total` (0 when absent)
    ///   and `ignore`; each of `[functions.timing]` and `[functions.alloc]`
    ///   that sets `judged` and `fail_check`, with its `min_percent_change`,
    ///   `metrics` and `min_calls` or hotpath's defaults for them (timing 50,
    ///   alloc 20; avg and total; 1).
    /// - provides: the thresholds the judgement applies.
    /// - fails: [`GuardError::Input`] naming the file for text that is not
    ///   TOML, a key of another type, or a metric other than `avg` and `total`,
    ///   which the judge would otherwise skip in silence.
    /// - panics: none.
    /// - executable: none — the parse is the clause.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the repository's allocation and timing policies, one
    ///   naming `p95`; a family read without `fail_check`, a lost threshold or
    ///   an accepted unknown metric changes the policy.
    /// - witness: `judge::tests::a_policy_reads_only_the_families_that_fail_the_check`
    #[inline]
    pub fn read(input: Input<'_>) -> Result<Self, GuardError>
    {
        let table: toml::Table =
            toml::from_str(input.text).map_err(|error| input.refuse(error.to_string()))?;
        let empty = toml::Table::new();
        let functions = match table.get("functions") {
            None => &empty,
            Some(&toml::Value::Table(ref functions)) => functions,
            Some(_) => return Err(input.refuse("`functions` is not a table".to_owned())),
        };
        let number = |value: &toml::Value, key| {
            let text = match *value {
                toml::Value::Integer(integer) => integer.to_string(),
                toml::Value::Float(float) => float.to_string(),
                toml::Value::String(_)
                | toml::Value::Boolean(_)
                | toml::Value::Datetime(_)
                | toml::Value::Array(_)
                | toml::Value::Table(_) => String::new(),
            };
            percent(&Written(text))
                .ok_or_else(|| input.refuse(format!("`{key}` is not a percentage")))
        };
        let strings = |value: &toml::Value, key| match *value {
            toml::Value::Array(ref items) => items
                .iter()
                .map(|item| {
                    item.as_str()
                        .map(str::to_owned)
                        .ok_or_else(|| input.refuse(format!("`{key}` holds a non-string")))
                })
                .collect::<Result<Vec<_>, _>>(),
            toml::Value::String(_)
            | toml::Value::Integer(_)
            | toml::Value::Float(_)
            | toml::Value::Boolean(_)
            | toml::Value::Datetime(_)
            | toml::Value::Table(_) => Err(input.refuse(format!("`{key}` is not an array"))),
        };
        let floor = functions
            .get("min_percent_total")
            .map_or(Ok(Share(0)), |value| number(value, "min_percent_total"))?;
        let ignore = functions
            .get("ignore")
            .map_or(Ok(Vec::new()), |value| strings(value, "ignore"))?
            .into_iter()
            .map(Pattern)
            .collect();
        let mut families = Vec::new();
        for (family, name, default_change) in FAMILIES {
            let Some(value) = functions.get(name)
            else {
                continue;
            };
            let toml::Value::Table(ref block) = *value
            else {
                return Err(input.refuse(format!("`functions.{name}` is not a table")));
            };
            let flag = |key| {
                block
                    .get(key)
                    .and_then(toml::Value::as_bool)
                    .unwrap_or(false)
            };
            if !(flag("judged") && flag("fail_check")) {
                continue;
            }
            let change = block
                .get("min_percent_change")
                .map_or(Ok(default_change), |value| {
                    number(value, "min_percent_change")
                })?;
            let metrics = block
                .get("metrics")
                .map_or_else(
                    || Ok(vec!["avg".to_owned(), "total".to_owned()]),
                    |value| strings(value, "metrics"),
                )?
                .iter()
                .map(|metric| match metric.as_str() {
                    "avg" => Ok(Metric::Avg),
                    "total" => Ok(Metric::Total),
                    other => Err(input.refuse(format!("the judge reads no metric `{other}`"))),
                })
                .collect::<Result<Vec<_>, _>>()?;
            let min_calls = match block.get("min_calls") {
                None => 1,
                Some(&toml::Value::Integer(calls)) => u128::try_from(calls)
                    .map_err(|error| input.refuse(format!("`min_calls`: {error}")))?,
                Some(_) => return Err(input.refuse("`min_calls` is not an integer".to_owned())),
            };
            families.push((family, Judged {
                change,
                metrics,
                min_calls: Amount(min_calls),
            }));
        }
        Ok(Self {
            floor,
            ignore,
            families,
        })
    }

    /// Whether the policy judges a name.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: ignored when an `ignore` pattern matches the whole name, each
    ///   `*` standing for any run of characters; judged otherwise.
    /// - provides: the timing report's closure: crates the change does not
    ///   reach are ignored.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the match is the clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a `crate::*module::fn` pattern and a prefix that does
    ///   not match the whole name; a partial match or a literal `*` changes the
    ///   verdict.
    /// - witness: `judge::tests::an_ignored_or_rare_row_is_not_judged`
    fn covers(
        &self,
        name: &RowName,
    ) -> Coverage
    {
        if self
            .ignore
            .iter()
            .any(|pattern| glob(pattern, name) == Coverage::Ignored)
        {
            Coverage::Ignored
        }
        else {
            Coverage::Judged
        }
    }
}

/// Whether `pattern`, each `*` any run of characters, matches all of `name`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: ignored when the literal parts appear in order, the first at the
///   start and the last at the end unless a `*` surrounds them.
/// - provides: [`Policy::covers`].
/// - fails: never.
/// - panics: none.
/// - executable: none — the match is the clause.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Policy::covers`].
/// - witness: `judge::tests::an_ignored_or_rare_row_is_not_judged`
fn glob(
    pattern: &Pattern,
    name: &RowName,
) -> Coverage
{
    let mut parts = pattern.0.split('*');
    let first = parts.next().unwrap_or_default();
    let Some(mut rest) = name.0.strip_prefix(first)
    else {
        return Coverage::Judged;
    };
    let mut last = None;
    for part in parts {
        if let Some(previous) = last.replace(part) {
            match rest.find(previous) {
                Some(at) => {
                    rest = rest
                        .get(at.saturating_add(previous.len()) ..)
                        .unwrap_or_default();
                },
                None => return Coverage::Judged,
            }
        }
    }
    let matched = last.map_or(rest.is_empty(), |last| rest.ends_with(last));
    if matched {
        Coverage::Ignored
    }
    else {
        Coverage::Judged
    }
}

/// Which rows a judgement covers.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Scope
{
    /// Only the rows under the policy's floor: a pull request, whose rows at
    /// and over it hotpath Cloud judges.
    Band,
    /// Every row: a push, which hotpath Cloud does not judge.
    All,
}

/// The least, the median and the greatest of one reading over a side's runs.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Spread
{
    /// The smallest run.
    low: Amount,
    /// The middle run; the lower middle of an even count.
    median: Amount,
    /// The largest run.
    high: Amount,
}

impl Spread
{
    /// The spread of a side's values.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: absent for no values; otherwise the least, the median (the
    ///   lower middle for an even count) and the greatest.
    /// - provides: what a row's move is judged on.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the sort is the clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — three runs a side of a measured regression; the upper
    ///   middle or a mean changes the median and the verdict.
    /// - witness: `judge::tests::a_sub_floor_row_regresses_only_over_disjoint_runs`
    fn of(mut values: Vec<Amount>) -> Option<Self>
    {
        values.sort_unstable();
        let middle = values.len().saturating_sub(1).checked_div(2)?;
        Some(Self {
            low: *values.first()?,
            median: *values.get(middle)?,
            high: *values.last()?,
        })
    }

    /// The spread of one reading over a side's rows.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Spread::of`].
    /// - witness: `judge::tests::a_sub_floor_row_regresses_only_over_disjoint_runs`
    fn over(
        rows: &[&Row],
        reading: Reading,
    ) -> Option<Self>
    {
        Self::of(rows.iter().map(|&row| reading.of(row)).collect())
    }
}

/// How far `after` grew from `before`, in hundredths of a percent.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `(after − before) × 10 000 ÷ before`, rounded down; absent when
///   `after` is not larger or `before` is zero.
/// - provides: the change a threshold is compared with.
/// - fails: never.
/// - panics: none.
/// - executable: none — the arithmetic is the clause.
///
/// # Adequacy
/// - hypothesis: L3 — medians of 81 ns and 89 ns (+9.87 %) and an unchanged
///   median; a swapped side or a lost factor changes the change.
/// - witness: `judge::tests::a_sub_floor_row_regresses_only_over_disjoint_runs`
fn growth(
    before: Amount,
    after: Amount,
) -> Option<Share>
{
    let grown = after.0.checked_sub(before.0).filter(|&grown| grown > 0)?;
    grown.checked_mul(10_000)?.checked_div(before.0).map(Share)
}

/// One metric that moved past its threshold.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Move
{
    /// The metric.
    metric: Metric,
    /// The base's runs.
    before: Spread,
    /// The commit's runs.
    after: Spread,
    /// The median's growth.
    growth: Share,
}

/// A row that regressed.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Finding
{
    /// The family it regressed in.
    family: Family,
    /// Its profiled name.
    name: RowName,
    /// Where it is defined.
    location: Option<Location>,
    /// The metrics past their threshold.
    moves: Vec<Move>,
}

/// A check run's conclusion.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Conclusion
{
    /// No row regressed.
    Success,
    /// A row regressed.
    Failure,
}

impl fmt::Display for Conclusion
{
    /// Writes the conclusion as the check runs API takes it.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a regressed band and a clear one; a swapped word
    ///   posts the other check.
    /// - witness: `tests::judge::a_regressed_band_writes_a_failed_check`
    /// - witness: `tests::judge::a_clear_band_writes_a_passed_check`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            Self::Success => "success",
            Self::Failure => "failure",
        })
    }
}

/// A judgement: each regressed row, and the wall time either side.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Verdict
{
    /// The rows that regressed, in family and name order.
    findings: Vec<Finding>,
    /// The wall time of the base's runs and the commit's.
    wall: Option<(Spread, Spread)>,
    /// The runs a side, the fewer of the two.
    runs: usize,
}

impl Verdict
{
    /// The check's conclusion: a failure exactly when a row regressed.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a regressed judgement and a clear one; a constant
    ///   answer changes one check's conclusion.
    /// - witness: `judge::tests::a_sub_floor_row_regresses_only_over_disjoint_runs`
    #[must_use]
    #[inline]
    pub fn conclusion(&self) -> Conclusion
    {
        if self.findings.is_empty() {
            Conclusion::Success
        }
        else {
            Conclusion::Failure
        }
    }
}

/// A row's reading in every run of one side.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the row of every run, in run order; absent when any run lacks it
///   or there are no runs.
/// - provides: one side of a row's judgement.
/// - fails: never.
/// - panics: none.
/// - executable: none — the lookup is the clause.
///
/// # Adequacy
/// - hypothesis: L3 — as [`judge`].
/// - witness: `judge::tests::a_sub_floor_row_regresses_only_over_disjoint_runs`
fn rows_of<'runs>(
    runs: &'runs [Run],
    key: &(Family, RowName),
) -> Option<Vec<&'runs Row>>
{
    runs.iter()
        .map(|run| run.rows.get(key))
        .collect::<Option<Vec<_>>>()
        .filter(|rows| !rows.is_empty())
}

/// Judges a commit's runs against its base's under a policy.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a row is judged in each family the policy fails the check on when
///   every run of both sides carries it, the policy does not ignore it, either
///   side's median calls reach `min_calls`, and the larger median share reaches
///   [`SHARE_FLOOR`]; under [`Scope::Band`] only a row under the policy's floor
///   is judged. It regresses on each judged metric whose median grew by at
///   least `min_percent_change`, and, under the floor, whose least run on the
///   commit exceeds the greatest on the base.
/// - provides: the check's verdict.
/// - fails: never.
/// - panics: none.
/// - executable: none — the verdict is the clause.
///
/// # Adequacy
/// - hypothesis: L3 — a measured regression of a row under the floor over
///   disjoint runs, an equal one over overlapping runs, a row over the floor
///   under both scopes, an ignored row, a rare row and a row under 0.1 %;
///   dropping the disjointness, the floor, the scope, the ignore or the call
///   floor changes a verdict.
/// - witness: `judge::tests::a_sub_floor_row_regresses_only_over_disjoint_runs`
/// - witness: `judge::tests::a_row_over_the_floor_is_the_clouds_on_a_pull_request`
/// - witness: `judge::tests::an_ignored_or_rare_row_is_not_judged`
#[must_use]
#[inline]
pub fn judge(
    policy: &Policy,
    scope: Scope,
    base: &[Run],
    head: &[Run],
) -> Verdict
{
    let walls = |runs: &[Run]| {
        Spread::of(
            runs.iter()
                .map(|run| run.wall)
                .collect::<Option<Vec<_>>>()?,
        )
    };
    let mut findings = Vec::new();
    let first = head.first().map(|run| &run.rows);
    for &(family, ref judged) in &policy.families {
        for key in first
            .into_iter()
            .flat_map(BTreeMap::keys)
            .filter(|key| key.0 == family)
        {
            if policy.covers(&key.1) == Coverage::Ignored {
                continue;
            }
            let (Some(before), Some(after)) = (rows_of(base, key), rows_of(head, key))
            else {
                continue;
            };
            let median =
                |rows: &[&Row], reading| Spread::over(rows, reading).map(|spread| spread.median);
            if median(&before, Reading::Calls) < Some(judged.min_calls)
                && median(&after, Reading::Calls) < Some(judged.min_calls)
            {
                continue;
            }
            let share = median(&before, Reading::Share)
                .max(median(&after, Reading::Share))
                .map_or(Share(0), |Amount(share)| Share(share));
            let banded = share < policy.floor;
            if share < SHARE_FLOOR || (scope == Scope::Band && !banded) {
                continue;
            }
            let moves: Vec<Move> = judged
                .metrics
                .iter()
                .filter_map(|&metric| {
                    let was = Spread::over(&before, Reading::Metric(metric))?;
                    let is = Spread::over(&after, Reading::Metric(metric))?;
                    let grew = growth(was.median, is.median)?;
                    (grew >= judged.change && (!banded || is.low > was.high)).then_some(Move {
                        metric,
                        before: was,
                        after: is,
                        growth: grew,
                    })
                })
                .collect();
            if !moves.is_empty() {
                findings.push(Finding {
                    family,
                    name: key.1.clone(),
                    location: after.first().and_then(|row| row.location.clone()),
                    moves,
                });
            }
        }
    }
    findings.sort_by(|left, right| (left.family, &left.name).cmp(&(right.family, &right.name)));
    Verdict {
        findings,
        wall: walls(base).zip(walls(head)),
        runs: base.len().min(head.len()),
    }
}

/// An amount as a summary writes it, in its family's unit.
#[derive(Clone, Copy, Debug)]
struct Shown(Family, Amount);

impl fmt::Display for Shown
{
    /// Writes the amount: a time in the largest unit it reaches, to two
    /// decimals, or a count to one when it has a fraction.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: 81 500 ps is `81.50 ns`, 5 144 385 000 ps `5.14 ms`, a count
    ///   of 92 368 `92368`, half a count `0.5`.
    /// - provides: the before and after numbers of a site line.
    /// - fails: propagates the formatter's write failure.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Errors
    /// Propagates the formatter's write failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a summary's site and wall lines; a wrong unit or
    ///   scale changes the written numbers.
    /// - witness: `judge::tests::a_summary_reads_back_into_its_sites`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let Self(family, Amount(value)) = *self;
        let (Scale(scale), unit, places) = match family {
            Family::Alloc => (COUNT_SCALE, "", 10),
            Family::Timing => TIME_UNITS
                .iter()
                .rev()
                .find(|&&(unit, Scale(scale))| unit != "us" && value >= scale)
                .map_or((Scale(1_000), "ns", 100), |&(unit, scale)| {
                    (scale, unit, 100)
                }),
        };
        let whole = value.checked_div(scale).unwrap_or_default();
        let part = value
            .checked_rem(scale)
            .and_then(|rest| rest.checked_mul(places))
            .and_then(|rest| rest.checked_div(scale))
            .unwrap_or_default();
        match (family, part) {
            (Family::Alloc, 0) => write!(f, "{whole}"),
            (Family::Alloc, _) => write!(f, "{whole}.{part}"),
            (Family::Timing, _) => write!(f, "{whole}.{part:02} {unit}"),
        }
    }
}

/// Which way an amount moved.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Direction
{
    /// It grew or stayed.
    Up,
    /// It fell.
    Down,
}

/// A change as a summary writes it: `**+9.8%**`, `**-1.5%**`.
#[derive(Clone, Copy, Debug)]
struct Delta
{
    /// Which way the amount moved.
    direction: Direction,
    /// The size of the change.
    size: Share,
}

impl Delta
{
    /// The change from `before` to `after`, either way.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the difference × 10 000 ÷ `before`, rounded down, and whether
    ///   `after` is the smaller; no change for a zero `before`.
    /// - provides: the wall line's delta, which may fall.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the arithmetic is the clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an unchanged wall time; a swapped side or sign
    ///   changes the wall line.
    /// - witness: `judge::tests::a_summary_reads_back_into_its_sites`
    fn between(
        before: Amount,
        after: Amount,
    ) -> Self
    {
        let direction = if after < before {
            Direction::Down
        }
        else {
            Direction::Up
        };
        let size = before
            .0
            .abs_diff(after.0)
            .checked_mul(10_000)
            .and_then(|scaled| scaled.checked_div(before.0))
            .map_or(Share(0), Share);
        Self { direction, size }
    }
}

impl fmt::Display for Delta
{
    /// Writes the change to one decimal, bold, with its sign.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a growth of 987 hundredths is `**+9.8%**`, of 1 000
    ///   `**+10%**`; a fall of 150 `**-1.5%**`; none `**+0%**`.
    /// - provides: a site line's delta, which the guard writes into its row
    ///   ([`crate::check::SummaryLine::delta`]).
    /// - fails: propagates the formatter's write failure.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Errors
    /// Propagates the formatter's write failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Shown`].
    /// - witness: `judge::tests::a_summary_reads_back_into_its_sites`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let sign = match self.direction {
            Direction::Up => '+',
            Direction::Down => '-',
        };
        let tenths = self.size.0.checked_div(10).unwrap_or_default();
        let whole = tenths.checked_div(10).unwrap_or_default();
        match tenths.checked_rem(10).unwrap_or_default() {
            0 => write!(f, "**{sign}{whole}%**"),
            tenth => write!(f, "**{sign}{whole}.{tenth}%**"),
        }
    }
}

/// What a check's summary names: the repository, the two commits and the
/// benchmark.
#[derive(Clone, Copy, Debug)]
pub struct Subject<'subject>
{
    /// The repository the links point into.
    pub repository: &'subject Repository,
    /// The commit judged.
    pub head: &'subject CommitSha,
    /// The commit it was judged against.
    pub base: &'subject CommitSha,
    /// The check's benchmark: `store-timing-band`.
    pub benchmark: &'subject str,
}

/// A verdict written as a `hotpath / <benchmark>` check's summary.
#[derive(Clone, Copy, Debug)]
pub struct Summary<'verdict>
{
    /// What the check names.
    pub subject: Subject<'verdict>,
    /// The judgement.
    pub verdict: &'verdict Verdict,
}

impl fmt::Display for Summary<'_>
{
    /// Writes the summary in hotpath Cloud's shape.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a ``### `<benchmark>` · <verdict>`` heading, the commits, the
    ///   wall-time line, then each family's heading and one line per finding:
    ///   the warning marker, the linked name, each metric's medians and growth
    ///   and its runs' ranges, and `· fails the check`.
    /// - provides: the text [`crate::check::Failure::read`] reads back.
    /// - fails: propagates the formatter's write failure.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Errors
    /// Propagates the formatter's write failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a regressed timing summary read back by the guard
    ///   into its site, crate and delta, and a clear one; a lost marker,
    ///   suffix, link or heading changes the reading.
    /// - witness: `judge::tests::a_summary_reads_back_into_its_sites`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let Subject {
            repository,
            head,
            base,
            benchmark,
        } = self.subject;
        let count = self.verdict.findings.len();
        writeln!(f, "<!-- hotpath:benchmark={benchmark} -->")?;
        match count {
            0 => writeln!(f, "### `{benchmark}` · ✅ no regression")?,
            1 => writeln!(f, "### `{benchmark}` · ⚠️ 1 regression")?,
            _ => writeln!(f, "### `{benchmark}` · ⚠️ {count} regressions")?,
        }
        writeln!(
            f,
            "[`{}`](https://github.com/{repository}/commit/{head}) vs [`{}`](https://github.com/{repository}/commit/{base}), {} runs a side",
            head.short(),
            base.short(),
            self.verdict.runs
        )?;
        if let Some((before, after)) = self.verdict.wall {
            writeln!(
                f,
                "Wall time `{} → {}` {}",
                Shown(Family::Timing, before.median),
                Shown(Family::Timing, after.median),
                Delta::between(before.median, after.median)
            )?;
        }
        let mut open = None;
        for finding in &self.verdict.findings {
            if open != Some(finding.family) {
                write!(f, "\n{}\n", finding.family)?;
                open = Some(finding.family);
            }
            match finding.location {
                Some(ref location) => write!(
                    f,
                    "⚠️ [`{}`](https://github.com/{repository}/blob/{}/{}#L{})",
                    finding.name,
                    head.short(),
                    location.file,
                    location.line
                )?,
                None => write!(
                    f,
                    "⚠️ [`{}`](https://github.com/{repository}/commit/{head})",
                    finding.name
                )?,
            }
            let shown = |amount| Shown(finding.family, amount);
            for (index, step) in finding.moves.iter().enumerate() {
                write!(
                    f,
                    "{} {} `{} → {}` {}, runs `{}–{} → {}–{}`",
                    if index == 0 { ":" } else { "," },
                    step.metric,
                    shown(step.before.median),
                    shown(step.after.median),
                    Delta {
                        direction: Direction::Up,
                        size: step.growth,
                    },
                    shown(step.before.low),
                    shown(step.before.high),
                    shown(step.after.low),
                    shown(step.after.high)
                )?;
            }
            writeln!(f, " · fails the check")?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests
{
    use super::Amount;
    use super::Conclusion;
    use super::Family;
    use super::Input;
    use super::Policy;
    use super::Run;
    use super::Scope;
    use super::Share;
    use super::Subject;
    use super::Summary;
    use super::Verdict;
    use super::Written;
    use super::judge;
    use crate::check::Benchmark;
    use crate::check::Failure;
    use crate::check::RunUrl;

    /// The repository's `store-timing` policy, as `ci:hotpath` writes it.
    const TIMING: &str = "pr_check = \"fail\"\n\n[functions]\nmin_percent_total = 1\n\n[functions.timing]\njudged = true\nfail_check = true\nmin_percent_change = 5\nmetrics = [\"avg\"]\nmin_calls = 20\n";

    /// One run's averages, in nanoseconds: `delete_part` over 384 calls and
    /// 0.65 % of the run, `preimage` over 256 and 0.13 %, `add_part` over
    /// 19 584 calls and 72 %.
    #[derive(Clone, Copy)]
    struct Averages
    {
        /// `Store::delete_part`'s.
        delete: &'static str,
        /// `Store::preimage`'s.
        pre: &'static str,
        /// `Store::add_part`'s.
        add: &'static str,
    }

    /// The averages of one run: `delete_part`'s, `preimage`'s, `add_part`'s.
    macro_rules! at {
        ($delete:literal, $pre:literal, $add:literal) => {
            Averages {
                delete: $delete,
                pre: $pre,
                add: $add,
            }
        };
    }

    /// A number as a report writes it.
    macro_rules! written {
        ($text:expr) => {
            Written(String::from($text))
        };
    }

    /// A run of the `store` series at its averages.
    ///
    /// # Specification
    /// trivial.
    fn run(averages: Averages) -> Run
    {
        let Averages { delete, pre, add } = averages;
        let text = format!(
            r#"{{"functions_timing": {{"total_elapsed_ns": 5144385, "data": [
              {{"name": "gandr_storage_schema::store::edit::Store::delete_part", "calls": 384, "avg": "{delete} ns", "total": "31.2 µs", "percent_total": "0.65%", "location": {{"file": "crates/storage-schema/src/store/edit.rs", "line": 212}}}},
              {{"name": "gandr_storage_schema::store::Store::preimage", "calls": 256, "avg": "{pre} ns", "total": "6.4 µs", "percent_total": "0.13%", "location": {{"file": "crates/storage-schema/src/store.rs", "line": 90}}}},
              {{"name": "gandr_storage_schema::store::edit::Store::add_part", "calls": 19584, "avg": "{add} ns", "total": "3.7 ms", "percent_total": "72.26%", "location": {{"file": "crates/storage-schema/src/store/edit.rs", "line": 155}}}}
            ]}},
            "functions_alloc": {{"data": [
              {{"name": "gandr_storage_schema::store::edit::Store::add_part", "calls": 19584, "avg": "4", "total": "92368", "percent_total": "89.09%"}}
            ]}}}}"#
        );
        Run::read(Input {
            path: "run.json",
            text: &text,
        })
        .unwrap()
    }

    /// The runs of one side.
    ///
    /// # Specification
    /// trivial.
    fn side(runs: &[Averages]) -> Vec<Run>
    {
        runs.iter().map(|&averages| run(averages)).collect()
    }

    /// A measured regression, three runs a side: `delete_part` 78–83 ns to
    /// 88–90 ns, `preimage` 23–27 ns to 25–26 ns, `add_part` steady.
    ///
    /// # Specification
    /// trivial.
    fn measured() -> (Vec<Run>, Vec<Run>)
    {
        (
            side(&[
                at!("81", "25", "189"),
                at!("78", "23", "190"),
                at!("83", "27", "188"),
            ]),
            side(&[
                at!("89", "26", "190"),
                at!("88", "25", "191"),
                at!("90", "25", "189"),
            ]),
        )
    }

    /// A policy from its text.
    macro_rules! policy {
        ($text:expr) => {
            Policy::read(Input {
                path: "policy.toml",
                text: &$text,
            })
            .unwrap()
        };
    }

    /// The names a verdict regressed.
    ///
    /// # Specification
    /// trivial.
    fn names(verdict: &Verdict) -> Vec<String>
    {
        verdict
            .findings
            .iter()
            .map(|finding| finding.name.to_string())
            .collect()
    }

    #[test]
    fn an_amount_reads_in_its_unit()
    {
        assert_eq!(
            Family::Timing.amount(&written!("8.237559 ms")),
            Some(Amount(8_237_559_000))
        );
        assert_eq!(
            Family::Timing.amount(&written!("179.28 µs")),
            Some(Amount(179_280_000))
        );
        assert_eq!(
            Family::Timing.amount(&written!("420 ns")),
            Some(Amount(420_000))
        );
        assert_eq!(
            Family::Alloc.amount(&written!("92368")),
            Some(Amount(92_368_000))
        );
        for (family, text) in [
            (Family::Alloc, "4 ns"),
            (Family::Timing, "420"),
            (Family::Timing, "ms"),
            (Family::Timing, "1. ms"),
            (Family::Timing, "4 2 ns"),
        ] {
            assert_eq!(
                family.amount(&written!(text)),
                None,
                "{text} reads no {family:?} amount"
            );
        }
        assert_eq!(super::percent(&written!("73.43%")), Some(Share(7_343)));
        assert_eq!(super::percent(&written!("7.5")), Some(Share(750)));
        assert_eq!(super::percent(&written!("2")), Some(Share(200)));
    }

    #[test]
    fn a_policy_reads_only_the_families_that_fail_the_check()
    {
        let timing = policy!(TIMING);
        assert_eq!(timing.floor, Share(100));
        let [(family, ref judged)] = *timing.families.as_slice()
        else {
            panic!("one family fails the check: {:?}", timing.families);
        };
        assert_eq!(
            (family, judged.change, judged.min_calls),
            (Family::Timing, Share(500), Amount(20))
        );
        let alloc = policy!(
            "[functions]\nmin_percent_total = 1\n\n[functions.alloc]\njudged = true\nfail_check = true\nmin_percent_change = 2\n\n[functions.timing]\njudged = false\n"
        );
        assert!(
            matches!(*alloc.families.as_slice(), [(Family::Alloc, _)]),
            "a judged block that does not fail the check is not the judge's: {alloc:?}"
        );
        let p95 = TIMING.replace("[\"avg\"]", "[\"avg\", \"p95\"]");
        let refused = Policy::read(Input {
            path: "p95.toml",
            text: &p95,
        })
        .map(|_| ())
        .map_err(|error| error.to_string());
        assert_eq!(
            refused,
            Err("`p95.toml`: the judge reads no metric `p95`".to_owned())
        );
    }

    #[test]
    fn a_sub_floor_row_regresses_only_over_disjoint_runs()
    {
        let (base, head) = measured();
        let verdict = judge(&policy!(TIMING), Scope::Band, &base, &head);
        assert_eq!(
            names(&verdict),
            ["gandr_storage_schema::store::edit::Store::delete_part"],
            "delete_part's runs part; preimage's medians do not move"
        );
        assert_eq!(
            verdict.conclusion(),
            Conclusion::Failure,
            "a finding fails the check"
        );
        let overlapping = side(&[
            at!("81", "25", "189"),
            at!("78", "23", "190"),
            at!("91", "27", "188"),
        ]);
        let verdict = judge(&policy!(TIMING), Scope::Band, &overlapping, &head);
        assert_eq!(
            names(&verdict),
            Vec::<String>::new(),
            "a base run at 91 ns overlaps the commit's, so +9 % on the medians is not enough under the floor"
        );
        assert_eq!(
            verdict.conclusion(),
            Conclusion::Success,
            "no finding, no failure"
        );
    }

    #[test]
    fn a_row_over_the_floor_is_the_clouds_on_a_pull_request()
    {
        let (base, _) = measured();
        let slower = side(&[
            at!("81", "25", "205"),
            at!("80", "25", "207"),
            at!("82", "25", "186"),
        ]);
        assert_eq!(
            names(&judge(&policy!(TIMING), Scope::Band, &base, &slower)),
            Vec::<String>::new(),
            "hotpath Cloud judges a row over the floor on a pull request"
        );
        assert_eq!(
            names(&judge(&policy!(TIMING), Scope::All, &base, &slower)),
            ["gandr_storage_schema::store::edit::Store::add_part"],
            "on a push the judge decides it on its median alone, the ranges overlapping"
        );
    }

    #[test]
    fn an_ignored_or_rare_row_is_not_judged()
    {
        let (base, head) = measured();
        let ignoring = policy!(TIMING.replace(
            "min_percent_total = 1\n",
            "min_percent_total = 1\nignore = [\"gandr_storage_schema::*edit::Store::delete_part\"]\n",
        ));
        assert_eq!(
            names(&judge(&ignoring, Scope::Band, &base, &head)),
            Vec::<String>::new()
        );
        let prefix = policy!(TIMING.replace(
            "min_percent_total = 1\n",
            "min_percent_total = 1\nignore = [\"gandr_storage_schema::store::edit\"]\n",
        ));
        assert_eq!(
            names(&judge(&prefix, Scope::Band, &base, &head)).len(),
            1,
            "a pattern matches the whole name"
        );
        let rare = policy!(TIMING.replace("min_calls = 20", "min_calls = 400"));
        assert_eq!(
            names(&judge(&rare, Scope::Band, &base, &head)),
            Vec::<String>::new(),
            "384 calls a side is under 400"
        );
        let small = |runs: Vec<Run>| {
            runs.into_iter()
                .map(|mut run| {
                    for row in run.rows.values_mut() {
                        row.share = Share(row.share.0.min(9));
                    }
                    run
                })
                .collect::<Vec<_>>()
        };
        assert_eq!(
            names(&judge(
                &policy!(TIMING),
                Scope::All,
                &small(base),
                &small(head)
            )),
            Vec::<String>::new(),
            "a row under 0.1 % of the run is never judged"
        );
    }

    #[test]
    fn a_summary_reads_back_into_its_sites()
    {
        let (base, head) = measured();
        let repository = "gandr-lang/gandr".parse().unwrap();
        let commit = "17756fc17aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".parse().unwrap();
        let below = "8d13f30c8bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb".parse().unwrap();
        let subject = Subject {
            repository: &repository,
            head: &commit,
            base: &below,
            benchmark: "store-timing-band",
        };
        let verdict = judge(&policy!(TIMING), Scope::Band, &base, &head);
        let summary = Summary {
            subject,
            verdict: &verdict,
        }
        .to_string();
        let text: crate::check::Summary =
            serde_json::from_value(serde_json::Value::String(summary.clone())).unwrap();
        let Ok(benchmark) = "store-timing-band".parse::<Benchmark>();
        let Ok(run) = "https://github.com/gandr-lang/gandr/runs/3".parse::<RunUrl>();
        let failure = Failure::read(benchmark, run, &text);
        let [ref section] = *failure.sections.as_slice()
        else {
            panic!("one section: {summary}");
        };
        assert_eq!(
            section.metric.to_string(),
            "Functions · timing",
            "{summary}"
        );
        let [ref site] = *section.sites.as_slice()
        else {
            panic!("one site: {summary}");
        };
        assert_eq!(
            site.name.to_string(),
            "gandr_storage_schema::store::edit::Store::delete_part",
            "{summary}"
        );
        assert!(
            matches!(site.krate, quenchant_shape::shape::Maybe::Present(ref dir) if dir.to_string() == "storage-schema"),
            "{summary}"
        );
        assert_eq!(
            site.line.to_string(),
            "[`gandr_storage_schema::store::edit::Store::delete_part`](https://github.com/gandr-lang/gandr/blob/17756fc/crates/storage-schema/src/store/edit.rs#L212): avg `81.00 ns → 89.00 ns` **+9.8%**, runs `78.00 ns–83.00 ns → 88.00 ns–90.00 ns`",
            "{summary}"
        );
        assert!(
            summary.contains("Wall time `5.14 ms → 5.14 ms` **+0%**"),
            "the wall line: {summary}"
        );
        let clear = judge(&policy!(TIMING), Scope::Band, &base, &base);
        let written = Summary {
            subject,
            verdict: &clear,
        }
        .to_string();
        assert!(
            written.contains("### `store-timing-band` · ✅ no regression"),
            "{written}"
        );
    }

    #[test]
    fn a_malformed_report_is_refused_by_its_path()
    {
        let read = Run::read(Input {
            path: "runs/store-2.json",
            text: r#"{"functions_timing": {"data": [{"name": "f", "calls": 1, "avg": "4", "total": "4 ns", "percent_total": "1%"}]}}"#,
        })
        .map(|_| ())
        .map_err(|error| error.to_string());
        assert_eq!(
            read,
            Err("`runs/store-2.json`: `f` reads no amount from `4`".to_owned())
        );
    }
}
