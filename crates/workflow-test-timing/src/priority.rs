//! nextest priority levels: the ones the configuration sets now, the ones
//! the measured medians propose, and the tables a reviewer commits.
//!
//! nextest starts higher priorities first and runs a test without an override
//! at 0. For each setting the first override whose filter matches applies, so
//! a test's current priority is the priority of the first matching override
//! that sets one.

extern crate alloc;

use alloc::borrow::ToOwned as _;
use core::fmt;
use core::time::Duration;
use std::path::Path;

use anodized::spec;

use crate::error::ConfigDefect;
use crate::error::TimingError;
use crate::report::Containment;
use crate::report::Stability;
use crate::report::TestName;
use crate::report::Timing;

/// A nextest scheduling priority, from -100 to 100; higher starts first.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Priority(i8);

impl Priority
{
    /// The priority of a test no override names.
    pub const DEFAULT: Self = Self(0);
}

impl TryFrom<i64> for Priority
{
    type Error = OutOfRange;

    /// Reads a configured priority.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the priority `value` names when it lies in -100..=100.
    /// - provides: the range nextest accepts.
    /// - fails: [`OutOfRange`] outside it.
    /// - panics: none.
    ///
    /// # Errors
    /// [`OutOfRange`] — `value` is below -100 or above 100.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — both ends of the range and the first value past each;
    ///   an off-by-one bound or an `i8`-wide range changes the verdict.
    /// - witness: `priority::tests::a_priority_lies_within_nextest_range`
    #[inline]
    #[spec(ensures: |ret| ret.is_ok() == (-100_i64..=100_i64).contains(&value))]
    fn try_from(value: i64) -> Result<Self, Self::Error>
    {
        if (-100_i64 ..= 100_i64).contains(&value) {
            i8::try_from(value).ok().map(Self).ok_or(OutOfRange)
        }
        else {
            Err(OutOfRange)
        }
    }
}

/// A configured priority outside -100..=100.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct OutOfRange;

impl fmt::Display for Priority
{
    /// Writes the priority as a decimal number.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the carried number through `i8`'s rendering.
    /// - provides: the priority columns and the generated `priority` keys.
    /// - fails: propagates the formatter's own write failure.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the generated table writes `priority = 100`.
    /// - witness: `priority::tests::overrides_render_one_table_per_level`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        fmt::Display::fmt(&self.0, f)
    }
}

/// One priority level and the medians that move a test into or out of it.
///
/// # Specification
/// - provides: `enter` above and `leave` below the level's boundary, a quarter
///   of the boundary each way, so a median that wanders across the boundary
///   between runs does not move the test back and forth.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Level
{
    /// The priority the level assigns.
    priority: Priority,
    /// The median at or above which a test below the level enters it.
    enter: Duration,
    /// The median below which a test at or above the level leaves it.
    leave: Duration,
}

/// The levels, highest first: boundaries at 120, 60, 30 and 15 seconds.
const LEVELS: [Level; 4] = [
    Level {
        priority: Priority(100),
        enter: Duration::from_secs(150),
        leave: Duration::from_secs(96),
    },
    Level {
        priority: Priority(90),
        enter: Duration::from_secs(75),
        leave: Duration::from_secs(48),
    },
    Level {
        priority: Priority(80),
        enter: Duration::from_millis(37_500),
        leave: Duration::from_secs(24),
    },
    Level {
        priority: Priority(70),
        enter: Duration::from_millis(18_750),
        leave: Duration::from_secs(12),
    },
];

/// The level a test with `median` belongs at, given where it is now.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the highest level whose threshold `median` reaches, where a level
///   at or below `current` is held down to its `leave` median and a level above
///   `current` needs its `enter` median; [`Priority::DEFAULT`] when no level is
///   reached.
/// - provides: the proposed priority, stable against medians that wander across
///   a boundary.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — for a test at the default, medians just below and at a
///   level's `enter`; for a test at a level, medians just below and at its
///   `leave`; and a median that skips a level. A threshold read from the wrong
///   side, an inclusive `leave`, or a first-match from the lowest level changes
///   the asserted priority.
/// - witness: `priority::tests::a_median_moves_a_level_only_past_its_margin`
#[must_use]
#[spec(ensures: |ret| ret == Priority::DEFAULT
    || LEVELS.iter().any(|level| level.priority == ret
        && median >= if level.priority <= current { level.leave } else { level.enter }))]
#[inline]
pub fn propose(
    current: Priority,
    median: Duration,
) -> Priority
{
    for level in &LEVELS {
        let threshold = if level.priority <= current {
            level.leave
        }
        else {
            level.enter
        };
        if median >= threshold {
            return level.priority;
        }
    }
    Priority::DEFAULT
}

/// One term of an override filter.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Term
{
    /// `test(=NAME)`: the test named exactly so.
    Exact(TestName),
    /// `test(TEXT)`: every test whose name contains the text.
    Contains(TestName),
}

/// One override that sets a priority.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Rule
{
    /// The priority it sets.
    priority: Priority,
    /// Its filter: the union of the terms.
    terms: Vec<Term>,
}

/// The text of a nextest configuration file.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct ConfigText<'text>(&'text str);

impl<'text> From<&'text str> for ConfigText<'text>
{
    /// Adopts `text` as a configuration's contents.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(text: &'text str) -> Self
    {
        Self(text)
    }
}

/// The priority overrides of nextest's default profile, in file order.
///
/// # Specification
/// - provides: each override that sets a priority, with a filter read as a
///   union of `test(=NAME)` and `test(TEXT)` terms; overrides that set no
///   priority are left out, since they never decide one.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Overrides(Vec<Rule>);

impl Overrides
{
    /// Reads the priority overrides of `profile.default`.
    ///
    /// # Specification
    /// - requires: nothing — any text is admissible input.
    /// - ensures: one rule per `[[profile.default.overrides]]` table that sets
    ///   `priority`, in file order; a file with no such table reads as no
    ///   rules.
    /// - provides: the current priorities a proposal is compared with.
    /// - fails: [`TimingError::Config`], naming `path`, when the text is not
    ///   TOML, the overrides are not an array of tables, a prioritized
    ///   override's `filter` is not a string, a term is neither form, or a
    ///   priority is not an integer from -100 to 100.
    /// - panics: none.
    ///
    /// # Errors
    /// [`TimingError::Config`] — as `fails` lists, with the defect.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a file with a prioritized override, an unprioritized
    ///   one and a two-term filter reads two terms in order; each defect is
    ///   refused with its own variant; a skipped override, a reordered rule or
    ///   a swallowed refusal changes the asserted value.
    /// - witness: `priority::tests::the_configured_overrides_read_in_order`
    /// - witness: `priority::tests::an_unreadable_override_is_refused_by_name`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |overrides| overrides.0.iter().all(|rule| !rule.terms.is_empty())))]
    #[inline]
    pub fn parse(
        text: ConfigText<'_>,
        path: &Path,
    ) -> Result<Self, TimingError>
    {
        let refuse = |defect| TimingError::Config {
            path: path.to_owned(),
            defect,
        };
        let table = toml::from_str::<toml::Table>(text.0)
            .map_err(|error| refuse(ConfigDefect::Toml(error.message().to_owned())))?;
        let Some(overrides) = table
            .get("profile")
            .and_then(|profile| profile.get("default"))
            .and_then(|default| default.get("overrides"))
        else {
            return Ok(Self::default());
        };
        let overrides = overrides
            .as_array()
            .ok_or_else(|| refuse(ConfigDefect::Overrides))?;
        let mut rules = Vec::new();
        for entry in overrides {
            let entry = entry
                .as_table()
                .ok_or_else(|| refuse(ConfigDefect::Overrides))?;
            let Some(priority) = entry.get("priority")
            else {
                continue;
            };
            let described = || match *priority {
                | toml::Value::Integer(value) => format!("`{value}`"),
                | ref other => format!("a {}", other.type_str()),
            };
            let priority = priority
                .as_integer()
                .and_then(|value| Priority::try_from(value).ok())
                .ok_or_else(|| refuse(ConfigDefect::Priority(described())))?;
            let filter = entry
                .get("filter")
                .and_then(toml::Value::as_str)
                .ok_or_else(|| refuse(ConfigDefect::Filter))?;
            let mut terms = Vec::new();
            for term in filter.split(" or ") {
                let term = term.trim();
                let inner = term
                    .strip_prefix("test(")
                    .and_then(|rest| rest.strip_suffix(')'))
                    .filter(|inner| !inner.contains(['(', ')', ' ']))
                    .ok_or_else(|| refuse(ConfigDefect::Term(term.to_owned())))?;
                terms.push(match inner.strip_prefix('=') {
                    | Some(name) => Term::Exact(TestName::from(name)),
                    | None => Term::Contains(TestName::from(inner)),
                });
            }
            rules.push(Rule { priority, terms });
        }
        Ok(Self(rules))
    }

    /// The priority the configuration gives `test` now.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the priority of the first rule with a term matching `test`,
    ///   or [`Priority::DEFAULT`] when none matches.
    /// - provides: the current column a proposal is compared with.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a test matched by an exact term, one matched only by
    ///   containment, one matched by two rules, and one matched by none; a
    ///   last-match rule, an exact term read as containment, or a missing
    ///   default changes the asserted priority.
    /// - witness: `priority::tests::a_filter_matches_exactly_or_by_containment`
    #[must_use]
    #[spec(ensures: |ret| ret == Priority::DEFAULT || self.0.iter().any(|rule| rule.priority == ret))]
    #[inline]
    pub fn current(
        &self,
        test: &TestName,
    ) -> Priority
    {
        for rule in &self.0 {
            let matches = rule.terms.iter().any(|term| match *term {
                | Term::Exact(ref name) => name == test,
                | Term::Contains(ref text) => test.contains(text) == Containment::Contains,
            });
            if matches {
                return rule.priority;
            }
        }
        Priority::DEFAULT
    }
}

/// A test's measured time, its current priority and the proposed one.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Proposal
{
    /// The test.
    pub test: TestName,
    /// Its summary in the lane it holds longest.
    pub timing: Timing,
    /// The priority the configuration gives it now.
    pub current: Priority,
    /// The priority its median proposes.
    pub proposed: Priority,
}

/// Every test that has a priority now or would have one.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one [`Proposal`] per timing whose current or proposed priority is
///   not the default, slowest median first, ties by name.
/// - provides: the rows of the report.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a fast unprioritized test is left out, a fast prioritized
///   one and a slow unprioritized one are kept, and the order follows the
///   median; keeping every test or sorting by name changes the asserted rows.
/// - witness: `priority::tests::the_table_lists_every_prioritized_test`
#[must_use]
#[spec(ensures: |ref ret| ret.iter().all(|proposal| proposal.current != Priority::DEFAULT || proposal.proposed != Priority::DEFAULT)
    && ret.is_sorted_by(|left, right| left.timing.median >= right.timing.median))]
#[inline]
pub fn proposals(
    timings: Vec<(TestName, Timing)>,
    overrides: &Overrides,
) -> Vec<Proposal>
{
    let mut proposals: Vec<Proposal> = timings
        .into_iter()
        .filter_map(|(test, timing)| {
            let current = overrides.current(&test);
            let proposed = propose(current, timing.median);
            (current != Priority::DEFAULT || proposed != Priority::DEFAULT).then_some(Proposal {
                test,
                timing,
                current,
                proposed,
            })
        })
        .collect();
    proposals.sort_by(|left, right| {
        right
            .timing
            .median
            .cmp(&left.timing.median)
            .then_with(|| left.test.cmp(&right.test))
    });
    proposals
}

/// The report table: one row per proposal.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Table<'proposals>(pub &'proposals [Proposal]);

impl fmt::Display for Table<'_>
{
    /// Writes a header and one aligned row per proposal.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each row names the test, its median, fastest and slowest
    ///   seconds, its run count and lane, its current and proposed priority,
    ///   and `unsteady` when its spread exceeds half its median.
    /// - provides: what a reviewer reads before accepting a proposal.
    /// - fails: propagates the formatter's own write failure.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a steady row and an unsteady row render every column
    ///   exactly; a dropped column or a misplaced flag changes the asserted
    ///   text.
    /// - witness: `priority::tests::the_table_lists_every_prioritized_test`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let width = self
            .0
            .iter()
            .map(|proposal| proposal.test.to_string().len())
            .chain([4_usize])
            .max()
            .unwrap_or(4_usize);
        writeln!(
            f,
            "{:<width$}  median  fastest  slowest  runs  current  proposed  lane",
            "test"
        )?;
        for proposal in self.0 {
            let timing = &proposal.timing;
            let flag = match timing.stability() {
                | Stability::Steady => "",
                | Stability::Unsteady => "  unsteady",
            };
            writeln!(
                f,
                "{:<width$}  {:>6.1}  {:>7.1}  {:>7.1}  {:>4}  {:>7}  {:>8}  {}{flag}",
                proposal.test.to_string(),
                timing.median.as_secs_f64(),
                timing.fastest.as_secs_f64(),
                timing.slowest.as_secs_f64(),
                timing.runs,
                proposal.current,
                proposal.proposed,
                timing.lane,
            )?;
        }
        Ok(())
    }
}

/// The proposed overrides, one table per level, for `.config/nextest.toml`.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct Generated<'proposals>(pub &'proposals [Proposal]);

impl fmt::Display for Generated<'_>
{
    /// Writes one `[[profile.default.overrides]]` table per proposed level.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the levels in descending order, each with a `filter` that
    ///   names its tests by exact term in name order and its `priority`; a
    ///   level no test is proposed for writes nothing.
    /// - provides: the tables a reviewer commits in place of the current
    ///   priority overrides.
    /// - fails: propagates the formatter's own write failure.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — proposals at two levels and at the default render two
    ///   tables in descending order with names sorted; a level written for the
    ///   default, an unsorted filter or a missing `or` changes the asserted
    ///   text.
    /// - witness: `priority::tests::overrides_render_one_table_per_level`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        for level in &LEVELS {
            let mut names: Vec<&TestName> = self
                .0
                .iter()
                .filter(|proposal| proposal.proposed == level.priority)
                .map(|proposal| &proposal.test)
                .collect();
            if names.is_empty() {
                continue;
            }
            names.sort_unstable();
            f.write_str("[[profile.default.overrides]]\nfilter = \"")?;
            for (position, name) in names.iter().enumerate() {
                if position != 0_usize {
                    f.write_str(" or ")?;
                }
                write!(f, "test(={name})")?;
            }
            writeln!(f, "\"\npriority = {}\n", level.priority)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests
{
    use core::time::Duration;
    use std::path::Path;

    use super::ConfigText;
    use super::Generated;
    use super::Overrides;
    use super::Priority;
    use super::Proposal;
    use super::Rule;
    use super::Table;
    use super::Term;
    use super::proposals;
    use super::propose;
    use crate::error::ConfigDefect;
    use crate::error::TimingError;
    use crate::report::BinaryId;
    use crate::report::Lane;
    use crate::report::TestName;
    use crate::report::Timing;

    #[test]
    fn a_priority_lies_within_nextest_range()
    {
        assert_eq!(Priority::try_from(100_i64), Ok(Priority(100)), "the top");
        assert_eq!(
            Priority::try_from(-100_i64),
            Ok(Priority(-100)),
            "the bottom"
        );
        assert!(Priority::try_from(101_i64).is_err(), "one past the top");
        assert!(Priority::try_from(-101_i64).is_err(), "one past the bottom");
        assert!(
            Priority::try_from(127_i64).is_err(),
            "inside i8, outside nextest"
        );
    }

    #[test]
    fn a_median_moves_a_level_only_past_its_margin()
    {
        let secs = Duration::from_secs;
        let millis = Duration::from_millis;
        assert_eq!(
            propose(Priority::DEFAULT, millis(18_749)),
            Priority::DEFAULT,
            "below 70's entry"
        );
        assert_eq!(
            propose(Priority::DEFAULT, millis(18_750)),
            Priority(70),
            "at 70's entry"
        );
        assert_eq!(
            propose(Priority(70), millis(11_999)),
            Priority::DEFAULT,
            "below 70's exit"
        );
        assert_eq!(
            propose(Priority(70), secs(12)),
            Priority(70),
            "at 70's exit"
        );
        assert_eq!(
            propose(Priority(70), secs(74)),
            Priority(80),
            "past 80's entry, short of 90's"
        );
        assert_eq!(
            propose(Priority(100), secs(96)),
            Priority(100),
            "at 100's exit"
        );
        assert_eq!(
            propose(Priority(100), millis(95_999)),
            Priority(90),
            "below 100's exit"
        );
        assert_eq!(
            propose(Priority::DEFAULT, secs(175)),
            Priority(100),
            "skips every lower level"
        );
    }

    #[test]
    fn the_configured_overrides_read_in_order()
    {
        let text = "[profile.default]\nstatus-level = \"pass\"\n\n\
                    [[profile.default.overrides]]\nfilter = \"test(=a::slow) or test(corpus)\"\npriority = 90\n\n\
                    [[profile.default.overrides]]\nfilter = \"test(=b)\"\nslow-timeout = \"1m\"\n\n\
                    [[profile.default.overrides]]\nfilter = \"test(=c)\"\npriority = -5\n\n\
                    [profile.ci]\nfail-fast = false\n";
        assert_eq!(
            Overrides::parse(ConfigText::from(text), Path::new("n.toml")),
            Ok(Overrides(vec![
                Rule {
                    priority: Priority(90),
                    terms: vec![
                        Term::Exact(TestName::from("a::slow")),
                        Term::Contains(TestName::from("corpus")),
                    ],
                },
                Rule {
                    priority: Priority(-5),
                    terms: vec![Term::Exact(TestName::from("c"))],
                },
            ])),
            "two prioritized overrides in file order; the timeout override sets no priority"
        );
        assert_eq!(
            Overrides::parse(ConfigText::from("[profile.ci]\n"), Path::new("n.toml")),
            Ok(Overrides::default()),
            "no overrides at all"
        );
    }

    #[test]
    fn an_unreadable_override_is_refused_by_name()
    {
        let path = Path::new("n.toml");
        let refused = |text: &str| Overrides::parse(ConfigText::from(text), path);
        let defect = |defect| {
            Err(TimingError::Config {
                path: path.to_owned(),
                defect,
            })
        };
        assert!(
            matches!(
                refused("[profile"),
                Err(TimingError::Config {
                    defect: ConfigDefect::Toml(_),
                    ..
                })
            ),
            "not TOML"
        );
        assert_eq!(
            refused("[profile.default]\noverrides = 1\n"),
            defect(ConfigDefect::Overrides),
            "not an array"
        );
        assert_eq!(
            refused("[profile.default]\noverrides = [1]\n"),
            defect(ConfigDefect::Overrides),
            "not an array of tables"
        );
        assert_eq!(
            refused("[[profile.default.overrides]]\npriority = 1\n"),
            defect(ConfigDefect::Filter),
            "no filter"
        );
        assert_eq!(
            refused("[[profile.default.overrides]]\nfilter = \"package(x)\"\npriority = 1\n"),
            defect(ConfigDefect::Term("package(x)".into())),
            "another predicate"
        );
        assert_eq!(
            refused(
                "[[profile.default.overrides]]\nfilter = \"test(a) and test(b)\"\npriority = 1\n"
            ),
            defect(ConfigDefect::Term("test(a) and test(b)".into())),
            "another operator"
        );
        assert_eq!(
            refused("[[profile.default.overrides]]\nfilter = \"test(=a)\"\npriority = 101\n"),
            defect(ConfigDefect::Priority("`101`".into())),
            "out of range"
        );
        assert_eq!(
            refused("[[profile.default.overrides]]\nfilter = \"test(=a)\"\npriority = \"high\"\n"),
            defect(ConfigDefect::Priority("a string".into())),
            "not an integer"
        );
    }

    #[test]
    fn a_filter_matches_exactly_or_by_containment()
    {
        let overrides = Overrides(vec![
            Rule {
                priority: Priority(100),
                terms: vec![Term::Exact(TestName::from("corpus::every_source"))],
            },
            Rule {
                priority: Priority(80),
                terms: vec![Term::Contains(TestName::from("corpus"))],
            },
            Rule {
                priority: Priority(70),
                terms: vec![Term::Exact(TestName::from("corpus::every"))],
            },
        ]);
        let current = |name: &str| overrides.current(&TestName::from(name));
        assert_eq!(
            current("corpus::every_source"),
            Priority(100),
            "an exact term, first of two matches"
        );
        assert_eq!(
            current("corpus::every"),
            Priority(80),
            "containment matches before a later exact term"
        );
        assert_eq!(
            current("a::corpus_b"),
            Priority(80),
            "containment inside the name"
        );
        assert_eq!(current("corpu"), Priority::DEFAULT, "a near miss");
        assert_eq!(
            TestName::from("corpus::every_source")
                .contains(&TestName::from("corpus::every_source")),
            super::Containment::Contains,
            "a name contains itself"
        );
    }

    #[test]
    fn the_table_lists_every_prioritized_test()
    {
        let timing = |median: Duration, fastest: Duration, slowest: Duration| Timing {
            lane: Lane::from("junit-cargo-test-enforcing"),
            binary: BinaryId::from("b"),
            median,
            fastest,
            slowest,
            runs: crate::report::RunCount::from(3_usize),
        };
        let secs = Duration::from_secs;
        let overrides = Overrides(vec![Rule {
            priority: Priority(90),
            terms: vec![Term::Exact(TestName::from("was_slow"))],
        }]);
        let rows = proposals(
            vec![
                (TestName::from("fast"), timing(secs(1), secs(1), secs(1))),
                (
                    TestName::from("now_slow"),
                    timing(secs(160), secs(100), secs(200)),
                ),
                (
                    TestName::from("was_slow"),
                    timing(secs(2), secs(2), secs(2)),
                ),
            ],
            &overrides,
        );
        assert_eq!(
            rows.iter()
                .map(|row| (row.test.clone(), row.current, row.proposed))
                .collect::<Vec<_>>(),
            vec![
                (TestName::from("now_slow"), Priority::DEFAULT, Priority(100)),
                (TestName::from("was_slow"), Priority(90), Priority::DEFAULT),
            ],
            "the unprioritized fast test is left out; slowest first"
        );
        assert_eq!(
            Table(&rows).to_string(),
            "test      median  fastest  slowest  runs  current  proposed  lane\n\
             now_slow   160.0    100.0    200.0     3        0       100  junit-cargo-test-enforcing  unsteady\n\
             was_slow     2.0      2.0      2.0     3       90         0  junit-cargo-test-enforcing\n",
            "every column, and the flag on the wide spread"
        );
    }

    #[test]
    fn overrides_render_one_table_per_level()
    {
        let row = |name: &str, proposed| Proposal {
            test: TestName::from(name),
            timing: Timing {
                lane: Lane::from("l"),
                binary: BinaryId::from("b"),
                median: Duration::ZERO,
                fastest: Duration::ZERO,
                slowest: Duration::ZERO,
                runs: crate::report::RunCount::from(1_usize),
            },
            current: Priority::DEFAULT,
            proposed,
        };
        let rows = [
            row("z::late", Priority(80)),
            row("a::top", Priority(100)),
            row("m::mid", Priority(80)),
            row("gone", Priority::DEFAULT),
        ];
        assert_eq!(
            Generated(&rows).to_string(),
            "[[profile.default.overrides]]\nfilter = \"test(=a::top)\"\npriority = 100\n\n\
             [[profile.default.overrides]]\nfilter = \"test(=m::mid) or test(=z::late)\"\npriority = 80\n\n",
            "levels descending, names sorted, nothing for the default"
        );
    }
}
