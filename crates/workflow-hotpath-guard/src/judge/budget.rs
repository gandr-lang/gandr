//! The budgets of a series: absolute limits on what a function allocates,
//! judged on one run in bytes, with no base.
//!
//! A report of counts gives no byte, so a budget in bytes needs a run of its
//! own, with `HOTPATH_ALLOC_METRIC=bytes`, and a policy of its own,
//! `hotpath/<series>-bytes-policy.toml`. The rules are hotpath's
//! `[[functions.budgets]]` (<https://hotpath.rs/performance_budgets>): `match`
//! names the functions, `alloc` limits their `avg` and `total` in bytes, and
//! `calls` bounds their calls. Each rule checks that a function that it
//! matches ran, unless its `calls.min` is 0. [`super::Policy::read`] refuses a
//! budget, so a policy of counts holds none.

extern crate alloc;

use alloc::collections::BTreeMap;
use core::fmt;

use serde::Deserialize;

use super::Digits;
use super::Fixed;
use super::Input;
use super::Metric;
use super::Pattern;
use super::RowName;
use super::Scale;
use super::Written;
use super::decimal;
use super::glob;
use crate::error::GuardError;

/// The bytes in each unit that a budget or a report writes: 1 KB is 1024 B.
const UNITS: [(&str, u128); 5] = [
    ("B", 1),
    ("KB", 1_024),
    ("MB", 0x0010_0000),
    ("GB", 0x4000_0000),
    ("TB", 0x0100_0000_0000),
];

/// The profiling mode of an allocation section in bytes.
const MODE: &str = "alloc-bytes";

/// Thousandths in one: the precision at which an amount's decimal is read.
const THOUSANDTHS: u128 = 1_000;

/// The bytes in one kilobyte, the unit in which an amount is written.
const KILOBYTE: u128 = 1_024;

/// An amount of bytes.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Bytes(u128);

impl Bytes
{
    /// Reads an amount as a budget or a report writes it: `512 B`, `1186 KB`,
    /// `1090.3 KB`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a decimal and one unit of [`UNITS`], in bytes: the decimal
    ///   read in thousandths, times the unit, the part past one byte dropped.
    /// - provides: each limit of a budget and each amount of a run in bytes.
    /// - fails: none — any other text, such as a bare count, is absent.
    /// - panics: none.
    /// - executable: none — the parse is the clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a whole and a decimal amount in kilobytes, bytes, a
    ///   bare count and a unit in other case; a unit of 1000 or an accepted
    ///   count changes a reading.
    /// - witness: `judge::budget::tests::an_amount_reads_in_bytes`
    fn read(text: &str) -> Option<Self>
    {
        let mut words = text.split_whitespace();
        let number = Digits(words.next()?);
        let unit = words.next()?;
        if words.next().is_some() {
            return None;
        }
        let &(_, bytes) = UNITS.iter().find(|&&(name, _)| name == unit)?;
        let Fixed(thousandths) = decimal(number, Scale(THOUSANDTHS))?;
        thousandths
            .checked_mul(bytes)?
            .checked_div(THOUSANDTHS)
            .map(Self)
    }
}

impl fmt::Display for Bytes
{
    /// Writes the amount in whole bytes under 1 KB, else in kilobytes with one
    /// decimal, so that an amount and its limit compare in one unit:
    /// `1090.3 KB, over budget 1024.0 KB`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — bytes, kilobytes with a decimal and a whole megabyte;
    ///   a unit of 1000 or a lost decimal changes the text.
    /// - witness: `judge::budget::tests::an_amount_reads_in_bytes`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        if self.0 < KILOBYTE {
            return write!(f, "{} B", self.0);
        }
        let tenths = self
            .0
            .saturating_mul(10)
            .saturating_add(KILOBYTE.checked_div(2).unwrap_or_default())
            .checked_div(KILOBYTE)
            .unwrap_or_default();
        let whole = tenths.checked_div(10).unwrap_or_default();
        let tenth = tenths.checked_rem(10).unwrap_or_default();
        write!(f, "{whole}.{tenth} KB")
    }
}

/// One function's row as a report in bytes writes it.
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
}

/// The allocation section of a report.
#[derive(Clone, Debug, Deserialize)]
struct RawSection
{
    /// What the section measures: `alloc-bytes` or `alloc-count`.
    profiling_mode: String,
    /// The rows.
    data: Vec<RawRow>,
}

/// A report as hotpath writes it, the section a budget reads.
#[derive(Clone, Debug, Deserialize)]
struct RawReport
{
    /// Allocations per function.
    functions_alloc: Option<RawSection>,
}

/// One function's row, its amounts read.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Row
{
    /// The calls the run made.
    calls: u64,
    /// The average.
    avg: Bytes,
    /// The sum over the calls.
    total: Bytes,
}

impl Row
{
    /// The row's amount of a metric.
    ///
    /// # Specification
    /// trivial.
    fn of(
        &self,
        metric: Metric,
    ) -> Bytes
    {
        match metric {
            Metric::Avg => self.avg,
            Metric::Total => self.total,
        }
    }
}

/// One run of a series in bytes: what each function allocated.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Run
{
    /// Each row, by profiled name.
    rows: BTreeMap<RowName, Row>,
}

impl Run
{
    /// Reads one run's JSON report.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each row of the allocation section, with its calls and its
    ///   amounts in bytes.
    /// - provides: the run that each budget is judged on.
    /// - fails: [`GuardError::Input`] naming the file for text that is not a
    ///   hotpath report, a report with no allocation section, a section that
    ///   does not measure bytes, or a row whose amounts do not read.
    /// - panics: none.
    /// - executable: none — the parse is the clause.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a report in bytes and a report of counts; an accepted
    ///   report of counts judges counts as bytes.
    /// - witness: `judge::budget::tests::a_report_of_counts_is_refused`
    #[inline]
    pub fn read(input: Input<'_>) -> Result<Self, GuardError>
    {
        let report: RawReport =
            serde_json::from_str(input.text).map_err(|error| input.refuse(error.to_string()))?;
        let Some(section) = report.functions_alloc
        else {
            return Err(input.refuse("the report has no section `functions_alloc`".to_owned()));
        };
        if section.profiling_mode != MODE {
            return Err(input.refuse(format!(
                "the section `functions_alloc` measures `{}`, and a budget reads `{MODE}`",
                section.profiling_mode
            )));
        }
        let rows = section
            .data
            .into_iter()
            .map(|raw| {
                let amount = |text: &Written| {
                    Bytes::read(&text.0).ok_or_else(|| {
                        input.refuse(format!("`{}` reads no bytes from `{}`", raw.name, text.0))
                    })
                };
                let row = Row {
                    calls: raw.calls,
                    avg: amount(&raw.avg)?,
                    total: amount(&raw.total)?,
                };
                Ok((raw.name, row))
            })
            .collect::<Result<_, GuardError>>()?;
        Ok(Self { rows })
    }
}

/// One rule of `[[functions.budgets]]`.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Rule
{
    /// The functions it limits.
    pattern: Pattern,
    /// Each limited metric, with its limit.
    limits: Vec<(Metric, Bytes)>,
    /// The fewest calls of each function that it matches.
    min_calls: u64,
    /// The most calls of each function that it matches.
    max_calls: Option<u64>,
    /// The text shown beside a broken rule.
    message: Option<String>,
    /// Whether a broken rule fails the series.
    fails: bool,
}

/// The budgets of a series: each rule of its policy in bytes.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Budgets
{
    /// The rules, in the order of the file.
    rules: Vec<Rule>,
}

/// How a function breaks a rule.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Breach
{
    /// No function that the rule matches ran.
    Absent,
    /// The calls fall outside the rule's bounds.
    Calls(u64),
    /// A metric is over its limit.
    Over
    {
        /// The metric.
        metric: Metric,
        /// The run's amount.
        amount: Bytes,
        /// The rule's limit.
        limit: Bytes,
    },
}

/// A rule that a run breaks, for one function.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Broken
{
    /// The function, or the rule's pattern when no function ran.
    name: String,
    /// How it breaks the rule.
    breach: Breach,
    /// The calls that the rule admits: its least and its most.
    calls: (u64, Option<u64>),
    /// The rule's text.
    message: Option<String>,
    /// Whether it fails the series.
    fails: bool,
}

impl Broken
{
    /// Whether the broken rule fails the series.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn fails(&self) -> bool
    {
        self.fails
    }
}

impl fmt::Display for Broken
{
    /// Writes the broken rule as hotpath's comment writes it:
    /// `⛔ parse: alloc.avg 1.4 KB, over budget 1.0 KB: <message> · fails the
    /// check`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a limit over its budget, a function that did not run
    ///   and calls past their bound, each with and without the failure of the
    ///   check; a lost amount, limit or message changes the line.
    /// - witness: `judge::budget::tests::a_rule_checks_each_row_that_it_matches`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let sign = if self.fails { "⛔" } else { "⚠️" };
        write!(f, "{sign} {}: ", self.name)?;
        match self.breach {
            Breach::Absent => f.write_str("not called")?,
            Breach::Calls(calls) => {
                write!(f, "calls {calls}, outside {} ..", self.calls.0)?;
                if let Some(max) = self.calls.1 {
                    write!(f, "= {max}")?;
                }
            },
            Breach::Over {
                metric,
                amount,
                limit,
            } => write!(f, "alloc.{metric} {amount}, over budget {limit}")?,
        }
        if let Some(ref message) = self.message {
            write!(f, ": {message}")?;
        }
        if self.fails {
            f.write_str(" · fails the check")?;
        }
        Ok(())
    }
}

impl Budgets
{
    /// Reads the budgets of a policy in bytes.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each table of `[[functions.budgets]]`, in order: its `match`,
    ///   its `alloc` limits `avg` and `total` in bytes, its `calls` bounds
    ///   (`min` 1 when absent), its `message`, and its `fail_check` (true when
    ///   absent); no rule when the policy has no budget.
    /// - provides: the rules that [`Budgets::judge`] applies.
    /// - fails: [`GuardError::Input`] naming the file for text that is not
    ///   TOML, a rule with no `match`, a key of another type, an amount that
    ///   reads no bytes, or a key that the judge does not read, such as
    ///   `timing` or a percentile, which it would otherwise skip in silence.
    /// - panics: none.
    /// - executable: none — the parse is the clause.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the repository's policy of `gandr` in bytes, a rule
    ///   of timing and a rule with no `match`; a lost limit or an accepted
    ///   unread key changes the budgets.
    /// - witness: `judge::budget::tests::the_policy_in_bytes_reads_each_rule`
    #[inline]
    pub fn read(input: Input<'_>) -> Result<Self, GuardError>
    {
        let table: toml::Table =
            toml::from_str(input.text).map_err(|error| input.refuse(error.to_string()))?;
        let rules = match table
            .get("functions")
            .and_then(|value| value.get("budgets"))
        {
            None => return Ok(Self::default()),
            Some(&toml::Value::Array(ref rules)) => rules,
            Some(_) => return Err(input.refuse("`functions.budgets` is not an array".to_owned())),
        };
        let mut budgets = Self::default();
        for value in rules {
            let toml::Value::Table(ref rule) = *value
            else {
                return Err(input.refuse("a budget is not a table".to_owned()));
            };
            budgets.rules.push(read_rule(input, rule)?);
        }
        Ok(budgets)
    }

    /// Each rule that a run breaks.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: for each rule, in order: one [`Broken`] naming its pattern
    ///   when no row that it matches ran and its `calls.min` is not 0; else for
    ///   each row that it matches, by name, one [`Broken`] when the calls fall
    ///   outside its bounds, and one for each metric over its limit.
    /// - provides: the budgets' verdict of a series.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the verdict is the clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a row over one limit and under the other, a pattern
    ///   with `*` over two rows, a rule that matches no row with and without
    ///   `calls.min = 0`, and calls past `max`; a lost row, limit or call check
    ///   changes the list.
    /// - witness: `judge::budget::tests::a_rule_checks_each_row_that_it_matches`
    #[must_use]
    #[inline]
    pub fn judge(
        &self,
        run: &Run,
    ) -> Vec<Broken>
    {
        let mut broken = Vec::new();
        for rule in &self.rules {
            let broke = |name: &str, breach| Broken {
                name: name.to_owned(),
                breach,
                calls: (rule.min_calls, rule.max_calls),
                message: rule.message.clone(),
                fails: rule.fails,
            };
            let mut matched = run
                .rows
                .iter()
                .filter(|&(name, _)| glob(&rule.pattern, name))
                .peekable();
            if matched.peek().is_none() {
                if rule.min_calls > 0 {
                    broken.push(broke(&rule.pattern.0, Breach::Absent));
                }
                continue;
            }
            for (name, row) in matched {
                if row.calls < rule.min_calls || rule.max_calls.is_some_and(|max| row.calls > max) {
                    broken.push(broke(&name.0, Breach::Calls(row.calls)));
                }
                for &(metric, limit) in &rule.limits {
                    let amount = row.of(metric);
                    if amount > limit {
                        broken.push(broke(&name.0, Breach::Over {
                            metric,
                            amount,
                            limit,
                        }));
                    }
                }
            }
        }
        broken
    }

    /// How many rules the budgets hold.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn len(&self) -> usize
    {
        self.rules.len()
    }

    /// Whether the budgets hold no rule.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn is_empty(&self) -> bool
    {
        self.rules.is_empty()
    }
}

/// Reads one rule of `[[functions.budgets]]`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: as [`Budgets::read`] states for one rule.
/// - provides: each rule of [`Budgets::read`].
/// - fails: as [`Budgets::read`].
/// - panics: none.
/// - executable: none — the parse is the clause.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — as [`Budgets::read`].
/// - witness: `judge::budget::tests::the_policy_in_bytes_reads_each_rule`
fn read_rule(
    input: Input<'_>,
    rule: &toml::Table,
) -> Result<Rule, GuardError>
{
    let Some(pattern) = rule.get("match").and_then(toml::Value::as_str)
    else {
        return Err(input.refuse("a budget has no string `match`".to_owned()));
    };
    let mut read = Rule {
        pattern: Pattern(pattern.to_owned()),
        limits: Vec::new(),
        min_calls: 1,
        max_calls: None,
        message: None,
        fails: true,
    };
    let count = |key: &str, value: &toml::Value| {
        value
            .as_integer()
            .and_then(|count| u64::try_from(count).ok())
            .ok_or_else(|| input.refuse(format!("`{pattern}`: `calls.{key}` is not a count")))
    };
    for (key, value) in rule {
        match (key.as_str(), value) {
            ("match", _) => {},
            ("message", &toml::Value::String(ref message)) => read.message = Some(message.clone()),
            ("fail_check", &toml::Value::Boolean(fails)) => read.fails = fails,
            ("alloc", &toml::Value::Table(ref limits)) => {
                for (metric, limit) in limits {
                    let metric = match metric.as_str() {
                        "avg" => Metric::Avg,
                        "total" => Metric::Total,
                        other => {
                            return Err(input.refuse(format!(
                                "`{pattern}`: the judge reads no budget `alloc.{other}`"
                            )));
                        },
                    };
                    let bytes = limit.as_str().and_then(Bytes::read).ok_or_else(|| {
                        input.refuse(format!("`{pattern}`: `alloc.{metric}` reads no bytes"))
                    })?;
                    read.limits.push((metric, bytes));
                }
            },
            ("calls", &toml::Value::Table(ref bounds)) => {
                for (bound, value) in bounds {
                    match bound.as_str() {
                        "min" => read.min_calls = count(bound, value)?,
                        "max" => read.max_calls = Some(count(bound, value)?),
                        other => {
                            return Err(input.refuse(format!(
                                "`{pattern}`: the judge reads no budget `calls.{other}`"
                            )));
                        },
                    }
                }
            },
            (other, _) => {
                return Err(input.refuse(format!(
                    "`{pattern}`: the judge reads no budget key `{other}` of this type"
                )));
            },
        }
    }
    Ok(read)
}

#[cfg(test)]
mod tests
{
    use super::super::Input;
    use super::Budgets;
    use super::Bytes;
    use super::Run;

    /// The repository's policy of `gandr` in bytes.
    const POLICY: &str = include_str!("../../../../hotpath/gandr-bytes-policy.toml");

    /// A report of one run, its allocation section in `mode`, with two rows of
    /// `gandr_core` and one of `gandr_kernel`.
    ///
    /// # Specification
    /// trivial.
    fn report(mode: &str) -> String
    {
        format!(
            r#"{{"functions_alloc": {{"profiling_mode": "{mode}", "data": [
                {{"name": "gandr_core::first", "calls": 2, "avg": "1.5 KB", "total": "3.0 KB", "percent_total": "50.00%"}},
                {{"name": "gandr_core::second", "calls": 1, "avg": "512 B", "total": "512 B", "percent_total": "10.00%"}},
                {{"name": "gandr_kernel::third", "calls": 9, "avg": "1.0 MB", "total": "9.0 MB", "percent_total": "40.00%"}}
            ]}}}}"#
        )
    }

    /// The budgets of a policy's text.
    ///
    /// # Specification
    /// trivial.
    fn budgets(text: &str) -> Result<Budgets, String>
    {
        Budgets::read(Input {
            path: "policy.toml",
            text,
        })
        .map_err(|error| error.to_string())
    }

    #[test]
    fn an_amount_reads_in_bytes()
    {
        assert_eq!(Bytes::read("1186 KB"), Some(Bytes(1_214_464)));
        assert_eq!(Bytes::read("1090.3 KB"), Some(Bytes(1_116_467)));
        assert_eq!(Bytes::read("1116467 B"), Some(Bytes(1_116_467)));
        assert_eq!(Bytes::read("1 MB"), Some(Bytes(0x0010_0000)));
        assert_eq!(Bytes::read("92368"), None, "a count is no amount of bytes");
        assert_eq!(Bytes::read("1 kB"), None);
        assert_eq!(Bytes::read("N/A"), None);
        assert_eq!(Bytes(512).to_string(), "512 B");
        assert_eq!(Bytes(1_214_464).to_string(), "1186.0 KB");
        assert_eq!(Bytes(1_116_467).to_string(), "1090.3 KB");
        assert_eq!(Bytes(0x0010_0000).to_string(), "1024.0 KB");
    }

    #[test]
    fn the_policy_in_bytes_reads_each_rule()
    {
        let read = budgets(POLICY).unwrap();
        assert_eq!(read.len(), 3);
        assert_eq!(
            budgets("[[functions.budgets]]\nmatch = \"f\"\ntiming = { avg = \"1 ms\" }\n"),
            Err(
                "`policy.toml`: `f`: the judge reads no budget key `timing` of this type"
                    .to_owned()
            )
        );
        assert_eq!(
            budgets("[[functions.budgets]]\nmatch = \"f\"\nalloc = { p95 = \"1 KB\" }\n"),
            Err("`policy.toml`: `f`: the judge reads no budget `alloc.p95`".to_owned())
        );
        assert_eq!(
            budgets("[[functions.budgets]]\nalloc = { avg = \"1 KB\" }\n"),
            Err("`policy.toml`: a budget has no string `match`".to_owned())
        );
        assert_eq!(
            budgets("[[functions.budgets]]\nmatch = \"f\"\nalloc = { avg = \"1024\" }\n"),
            Err("`policy.toml`: `f`: `alloc.avg` reads no bytes".to_owned())
        );
        assert!(
            budgets("[functions.alloc]\njudged = false\n")
                .unwrap()
                .is_empty()
        );
    }

    #[test]
    fn a_report_of_counts_is_refused()
    {
        let run = |text: &str| {
            Run::read(Input {
                path: "gandr-bytes.json",
                text,
            })
            .map_err(|error| error.to_string())
        };
        assert_eq!(run(&report("alloc-bytes")).map(|run| run.rows.len()), Ok(3));
        assert_eq!(
            run(&report("alloc-count")),
            Err(
                "`gandr-bytes.json`: the section `functions_alloc` measures `alloc-count`, and a \
                 budget reads `alloc-bytes`"
                    .to_owned()
            )
        );
        assert_eq!(
            run("{}"),
            Err("`gandr-bytes.json`: the report has no section `functions_alloc`".to_owned())
        );
    }

    #[test]
    fn a_rule_checks_each_row_that_it_matches()
    {
        let run = Run::read(Input {
            path: "gandr-bytes.json",
            text: &report("alloc-bytes"),
        })
        .unwrap();
        let read = budgets(
            "[[functions.budgets]]\nmatch = \"gandr_core::*\"\nalloc = { avg = \"1 KB\", total = \"4 KB\" }\nmessage = \"a core function stays small\"\n\n[[functions.budgets]]\nmatch = \"gandr_kernel::third\"\ncalls = { max = 8 }\nfail_check = false\n\n[[functions.budgets]]\nmatch = \"gandr_core::renamed\"\n\n[[functions.budgets]]\nmatch = \"gandr_core::optional\"\ncalls = { min = 0 }\n",
        )
        .unwrap();
        let lines: Vec<String> = read.judge(&run).iter().map(ToString::to_string).collect();
        assert_eq!(lines, [
            "⛔ gandr_core::first: alloc.avg 1.5 KB, over budget 1.0 KB: a core function stays \
             small · fails the check",
            "⚠️ gandr_kernel::third: calls 9, outside 1 ..= 8",
            "⛔ gandr_core::renamed: not called · fails the check",
        ]);
        assert_eq!(
            read.judge(&run)
                .iter()
                .filter(|broken| broken.fails())
                .count(),
            2
        );
    }
}
