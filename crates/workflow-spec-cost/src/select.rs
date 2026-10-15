//! The tests a ranking profiles: named on the command line, or the slowest
//! enforcing tests of the stored merge-queue runs.

use core::fmt;
use core::num::NonZeroUsize;
use core::str::FromStr;
use std::path::Path;

use gandr_workflow_test_timing::History;
use gandr_workflow_test_timing::RunLimit;
use gandr_workflow_test_timing::read_run;
use gandr_workflow_test_timing::report::BinaryId;
use gandr_workflow_test_timing::report::TestName;
use gandr_workflow_test_timing::stored_runs;

use crate::error::CostError;

/// One test in one binary, as nextest names them.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Workload
{
    /// The binary, as nextest's binary id.
    pub binary: BinaryId,
    /// The test's path inside the binary.
    pub test: TestName,
}

impl FromStr for Workload
{
    type Err = CostError;

    /// Reads `BINARY TEST`, the form nextest prints a test in.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the binary before the first space and the test after it.
    /// - provides: the `--test` argument.
    /// - fails: [`CostError::Workload`] when either part is empty.
    /// - panics: none.
    /// - executable: none — the parts are the split itself.
    ///
    /// # Errors
    /// [`CostError::Workload`] — no space, or an empty side.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a binary id and a test path, both holding `::`, and
    ///   arguments without a space or with an empty side; a split on `::` or at
    ///   the last space changes the parsed workload.
    /// - witness: `select::tests::a_workload_reads_as_nextest_prints_it`
    #[inline]
    fn from_str(text: &str) -> Result<Self, Self::Err>
    {
        match text.split_once(' ') {
            Some((binary, test)) if !binary.is_empty() && !test.is_empty() => Ok(Self {
                binary: BinaryId::from(binary),
                test: TestName::from(test),
            }),
            Some(_) | None => Err(CostError::Workload {
                text: text.to_owned(),
            }),
        }
    }
}

impl fmt::Display for Workload
{
    /// Writes `BINARY TEST`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the binary, a space and the test, which
    ///   [`Workload::from_str`] reads back.
    /// - provides: the name the progress lines and the report print.
    /// - fails: propagates the formatter's own write failure.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a workload renders as nextest prints it and parses
    ///   back to itself.
    /// - witness: `select::tests::a_workload_reads_as_nextest_prints_it`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "{} {}", self.binary, self.test)
    }
}

/// How many tests a ranking profiles; never zero.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct WorkloadCount(NonZeroUsize);

impl FromStr for WorkloadCount
{
    type Err = core::num::ParseIntError;

    /// Reads a positive decimal count.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the count `text` spells, when it is a positive integer.
    /// - provides: the `--tests` argument.
    /// - fails: the parse error of a non-number or of zero.
    /// - panics: none.
    /// - executable: none — the outcome is `NonZeroUsize`'s own parse.
    ///
    /// # Errors
    /// A [`core::num::ParseIntError`] for anything but a positive integer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `--tests 0` exits 2 and `--tests 2` profiles two
    ///   tests; a count that admitted zero or ignored the number changes
    ///   either.
    /// - witness: `cli::cli::a_malformed_invocation_exits_two`
    /// - witness: `select::tests::the_slowest_enforcing_tests_are_chosen`
    #[inline]
    fn from_str(text: &str) -> Result<Self, Self::Err>
    {
        text.parse().map(Self)
    }
}

/// The `count` tests of the newest `runs` stored runs whose summary is longest
/// in an enforcing lane, slowest first.
///
/// # Specification
/// - requires: nothing.
/// - ensures: at most `count` workloads, each summarised in a lane whose name
///   holds `enforcing`, in descending order of that summary's median.
/// - provides: the default set a ranking profiles.
/// - fails: every refusal of [`stored_runs`] and [`read_run`];
///   [`CostError::NoWorkloads`] when no stored run names an enforcing test.
/// - panics: none.
/// - executable: none — the outcome depends on the store on disk.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — a store whose slowest test is plain and whose two
///   enforcing tests differ in median; choosing by plain time, ascending or
///   past the count changes the selection.
/// - witness: `select::tests::the_slowest_enforcing_tests_are_chosen`
#[inline]
pub fn slowest_enforcing(
    store: &Path,
    runs: RunLimit,
    count: WorkloadCount,
) -> Result<Vec<Workload>, CostError>
{
    let mut history = History::default();
    for run in stored_runs(store)?.into_iter().take(runs.into()) {
        read_run(store, run, &mut history)?;
    }
    let mut enforcing: Vec<_> = history
        .timings()
        .into_iter()
        .filter(|entry| entry.1.lane.to_string().contains("enforcing"))
        .collect();
    enforcing.sort_by_key(|entry| core::cmp::Reverse(entry.1.median));
    let chosen: Vec<Workload> = enforcing
        .into_iter()
        .take(count.0.get())
        .map(|(test, timing)| Workload {
            binary: timing.binary,
            test,
        })
        .collect();
    if chosen.is_empty() {
        return Err(CostError::NoWorkloads {
            dir: store.to_path_buf(),
        });
    }
    Ok(chosen)
}

#[cfg(test)]
mod tests
{
    use std::path::Path;

    use gandr_workflow_test_timing::report::BinaryId;
    use gandr_workflow_test_timing::report::TestName;

    use super::Workload;
    use super::slowest_enforcing;
    use crate::error::CostError;

    #[test]
    fn a_workload_reads_as_nextest_prints_it()
    {
        let parsed: Workload = "gandr-surface-parser::tests acceptance::corpus_parses_totally"
            .parse()
            .unwrap();
        assert_eq!(
            parsed,
            Workload {
                binary: BinaryId::from("gandr-surface-parser::tests"),
                test: TestName::from("acceptance::corpus_parses_totally"),
            },
            "split at the first space"
        );
        assert_eq!(
            parsed.to_string(),
            "gandr-surface-parser::tests acceptance::corpus_parses_totally",
            "rendered back as given"
        );
        for text in ["acceptance::corpus_parses_totally", " t", "b ", ""] {
            assert_eq!(
                text.parse::<Workload>(),
                Err(CostError::Workload {
                    text: text.to_owned(),
                }),
                "{text:?} names no binary and test"
            );
        }
    }

    #[test]
    fn the_slowest_enforcing_tests_are_chosen()
    {
        let store = std::env::temp_dir().join(format!("spec-cost-{}-select", std::process::id()));
        if store.exists() {
            std::fs::remove_dir_all(&store).unwrap();
        }
        let report = |lane: &str, cases: &[(&str, &str)]| {
            let dir = store.join("7").join(lane);
            std::fs::create_dir_all(&dir).unwrap();
            let body = cases
                .iter()
                .map(|&(name, time)| {
                    format!("<testcase classname=\"gandr-a\" name=\"{name}\" time=\"{time}\"/>")
                })
                .collect::<Vec<_>>()
                .concat();
            std::fs::write(
                dir.join("junit.xml"),
                format!("<testsuites>{body}</testsuites>"),
            )
            .unwrap();
        };
        report("junit-cargo-test-plain", &[("plain::slowest", "900.0")]);
        report("junit-cargo-test-enforcing", &[
            ("plain::slowest", "1.0"),
            ("e::fast", "2.0"),
            ("e::slow", "30.0"),
            ("e::mid", "9.0"),
        ]);
        let pick = |count: &str| {
            slowest_enforcing(&store, "5".parse().unwrap(), count.parse().unwrap()).map(|chosen| {
                chosen
                    .into_iter()
                    .map(|workload| workload.to_string())
                    .collect::<Vec<_>>()
            })
        };
        assert_eq!(
            pick("2"),
            Ok(vec![
                "gandr-a e::slow".to_owned(),
                "gandr-a e::mid".to_owned()
            ]),
            "enforcing summaries only, slowest first, two of them"
        );
        std::fs::remove_dir_all(&store).unwrap();
        assert_eq!(
            pick("2"),
            Err(CostError::NoWorkloads {
                dir: Path::new(&store).to_path_buf(),
            }),
            "an empty store names nothing to profile"
        );
    }
}
