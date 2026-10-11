//! A test's profile: its binary built for sampling, a `perf record` of one run
//! of it, and the samples `perf script` reads back.
//!
//! The binaries are built with specifications enforced, frame pointers kept
//! and line tables on, into `target/spec-cost`, so profiling never disturbs
//! the build state of the test gates.

extern crate alloc;

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use std::io::BufReader;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command;
use std::process::Stdio;

use anodized::spec;
use gandr_workflow_test_timing::report::BinaryId;
use gandr_workflow_test_timing::report::TestName;
use quenchant_shape::shape::Maybe;
use serde::Deserialize;

use crate::error::CostError;
use crate::ledger::Frequency;
use crate::ledger::Ledger;
use crate::ledger::charge;
use crate::region::Regions;
use crate::select::Workload;
use crate::stack::Stacks;

/// The flags a profiled build compiles under: enforcement, as the enforcing
/// test gate builds, and frame pointers, which `perf` unwinds by.
const PROFILE_RUSTFLAGS: &str = "--cfg anodized_panic -C force-frame-pointers=yes";

/// nextest's machine-readable test list, as far as a profile reads it.
#[repr(transparent)]
#[derive(Debug, Deserialize)]
struct Listing
{
    /// Every test binary, by binary id.
    #[serde(rename = "rust-suites")]
    suites: BTreeMap<String, ListedSuite>,
}

/// One binary of the list.
#[derive(Debug, Deserialize)]
struct ListedSuite
{
    /// The executable.
    #[serde(rename = "binary-path")]
    binary_path: String,
    /// The directory nextest runs it in: its package's.
    cwd: String,
    /// Its tests, by name.
    testcases: BTreeMap<String, ListedCase>,
}

/// One test of a listed binary.
#[repr(transparent)]
#[derive(Debug, Deserialize)]
struct ListedCase
{
    /// Whether the test is `#[ignore]`d, which a plain run skips.
    ignored: bool,
}

/// A built test binary.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Suite
{
    /// The executable.
    pub binary: PathBuf,
    /// The directory it runs in.
    pub cwd: PathBuf,
    /// Its tests.
    tests: BTreeSet<TestName>,
}

/// The binaries a set of workloads runs in, built for profiling.
///
/// # Specification
/// - provides: a workload's executable and directory, or the refusal naming a
///   test its binary lacks.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Suites(BTreeMap<BinaryId, Suite>);

impl Suites
{
    /// Builds and lists the test binaries of every package `workloads` name.
    ///
    /// # Specification
    /// - requires: `cargo nextest` on the path; `root` the workspace root.
    /// - ensures: one suite per binary nextest listed for the packages, each
    ///   named before the first `::` of a workload's binary.
    /// - provides: the executables a profile runs.
    /// - fails: [`CostError::Command`] when the build or the listing fails;
    ///   [`CostError::Listing`] when the list is not the JSON this crate reads.
    /// - panics: none.
    /// - executable: none — the outcome is the build's, outside the call.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fake `cargo` that records its flags and lists one
    ///   binary; a build without enforcement, frame pointers or line tables, or
    ///   a lost listing, changes what the fake records or the report.
    /// - witness: `cli::cli::a_profile_is_charged_to_its_outermost_specification`
    #[inline]
    pub fn build(
        workloads: &[Workload],
        root: &Path,
    ) -> Result<Self, CostError>
    {
        let packages: BTreeSet<String> = workloads
            .iter()
            .map(|workload| {
                let binary = workload.binary.to_string();
                binary
                    .split_once("::")
                    .map_or_else(|| binary.clone(), |(package, _)| package.to_owned())
            })
            .collect();
        let mut command = Command::new("cargo");
        command
            .args(["nextest", "list", "--locked", "--message-format", "json"])
            .args(
                packages
                    .iter()
                    .flat_map(|package| ["--package", package.as_str()]),
            )
            .current_dir(root)
            .env("RUSTFLAGS", PROFILE_RUSTFLAGS)
            .env("CARGO_TARGET_DIR", root.join("target").join("spec-cost"))
            .env("CARGO_PROFILE_TEST_DEBUG", "line-tables-only")
            .stderr(Stdio::inherit());
        let listed = output(&mut command)?;
        let listing: Listing =
            serde_json::from_slice(&listed.stdout).map_err(|error| CostError::Listing {
                message: error.to_string(),
            })?;
        Ok(Self(
            listing
                .suites
                .into_iter()
                .map(|(binary, suite)| {
                    (BinaryId::from(binary), Suite {
                        binary: PathBuf::from(suite.binary_path),
                        cwd: PathBuf::from(suite.cwd),
                        tests: suite
                            .testcases
                            .into_iter()
                            .filter(|entry| !entry.1.ignored)
                            .map(|(name, _)| TestName::from(name))
                            .collect(),
                    })
                })
                .collect(),
        ))
    }

    /// The suite `workload` runs in.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the listed suite of the workload's binary, which lists its
    ///   test.
    /// - provides: the check that a profile runs a test that exists: a libtest
    ///   filter matching nothing succeeds silently.
    /// - fails: [`CostError::UnknownTest`] when the binary is unlisted or lacks
    ///   the test.
    /// - panics: none.
    ///
    /// # Errors
    /// [`CostError::UnknownTest`] — no such binary, or no such test in it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a listed test is profiled and an unlisted one is
    ///   refused by name; a lookup by binary alone profiles nothing silently.
    /// - witness: `cli::cli::an_unknown_test_is_refused_by_name`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |suite| suite.tests.contains(&workload.test)))]
    #[inline]
    pub fn get(
        &self,
        workload: &Workload,
    ) -> Result<&Suite, CostError>
    {
        self.0
            .get(&workload.binary)
            .filter(|suite| suite.tests.contains(&workload.test))
            .ok_or_else(|| CostError::UnknownTest {
                binary: workload.binary.to_string(),
                test: workload.test.to_string(),
            })
    }
}

/// Runs `workload` alone under `perf record`, writing the samples to `data`.
///
/// # Specification
/// - requires: `perf` on the path and allowed to sample user space.
/// - ensures: one run of the test, single-threaded, in its suite's directory,
///   sampled at `frequency` with frame-pointer call stacks into `data`.
/// - provides: the profile [`read_samples`] charges.
/// - fails: [`CostError::Command`] when `perf` cannot start or the run fails, a
///   failing test included.
/// - panics: none.
/// - executable: none — the outcome is the file `perf` writes.
///
/// # Errors
/// [`CostError::Command`] — `perf` or the test failed.
///
/// # Adequacy
/// - hypothesis: L3 — a fake `perf` records its arguments and directory; a lost
///   rate, test name, thread limit or directory changes what it records.
/// - witness: `cli::cli::a_profile_is_charged_to_its_outermost_specification`
#[inline]
pub fn record(
    suite: &Suite,
    workload: &Workload,
    frequency: Frequency,
    data: &Path,
) -> Result<(), CostError>
{
    let mut command = Command::new("perf");
    command
        .args([
            "record",
            "-q",
            "-F",
            &frequency.to_string(),
            "--call-graph",
            "fp",
            "-o",
        ])
        .arg(data)
        .arg("--")
        .arg(&suite.binary)
        .args([
            "--exact",
            &workload.test.to_string(),
            "--test-threads",
            "1",
            "-q",
        ])
        .current_dir(&suite.cwd)
        .env("CARGO_MANIFEST_DIR", &suite.cwd)
        .stdout(Stdio::null())
        .stderr(Stdio::inherit());
    output(&mut command).map(drop)
}

/// Charges every sample of `data` to `workload` in `ledger`.
///
/// # Specification
/// - requires: `perf` on the path; `data` written by [`record`].
/// - ensures: every sample `perf script` prints is recorded once, charged by
///   [`charge`] against `regions` with locations resolved against `root`.
/// - provides: the ledger a ranking prints.
/// - fails: [`CostError::Command`] when `perf script` cannot start or fails;
///   [`CostError::Io`] when its output cannot be read.
/// - panics: none.
/// - executable: none — the outcome is the ledger's private counts.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — a fake `perf script` printing three samples, one nested,
///   one in a body and one in a check, yields the asserted ranking.
/// - witness: `cli::cli::a_profile_is_charged_to_its_outermost_specification`
#[inline]
pub fn read_samples(
    data: &Path,
    root: &Path,
    regions: &Regions,
    workload: &Workload,
    ledger: &mut Ledger,
) -> Result<(), CostError>
{
    let mut command = Command::new("perf");
    command
        .args(["script", "-i"])
        .arg(data)
        .args(["-F", "ip,sym,srcline", "--inline", "--full-source-path"])
        .stdout(Stdio::piped())
        .stderr(Stdio::inherit());
    let invocation = invocation_of(&command);
    let failed = |message: String| CostError::Command {
        command: invocation.clone(),
        message,
    };
    let mut child = command.spawn().map_err(|error| failed(error.to_string()))?;
    let Some(script) = child.stdout.take()
    else {
        return Err(failed("no standard output".to_owned()));
    };
    let mut stacks = Stacks::new(BufReader::new(script), root);
    while let Maybe::Present(frames) = stacks.next_sample()? {
        ledger.record(workload, charge(&frames, regions));
    }
    let status = child.wait().map_err(|error| failed(error.to_string()))?;
    if status.success() {
        Ok(())
    }
    else {
        Err(failed(status.to_string()))
    }
}

/// The command as typed.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the program and its arguments, separated by spaces.
/// - provides: the invocation a refusal names.
/// - panics: none.
/// - executable: none — the text is the joined arguments.
///
/// # Adequacy
/// - hypothesis: L3 — a failing fake names its invocation in the refusal; a
///   lost program or argument changes the message.
/// - witness: `cli::cli::a_failing_profile_is_refused_with_its_invocation`
fn invocation_of(command: &Command) -> String
{
    core::iter::once(command.get_program())
        .chain(command.get_args())
        .map(|part| part.to_string_lossy().into_owned())
        .collect::<Vec<_>>()
        .join(" ")
}

/// Runs `command` and returns what it wrote.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the command's output, its exit status a success.
/// - provides: the one place a `cargo` or `perf` failure becomes a refusal.
/// - fails: [`CostError::Command`], naming the invocation, when the command
///   cannot start or exits unsuccessfully.
/// - panics: none.
/// - executable: none — the outcome is the external process's.
///
/// # Errors
/// [`CostError::Command`] — the command did not start or did not succeed.
///
/// # Adequacy
/// - hypothesis: L3 — a fake that succeeds and one that fails; a swallowed exit
///   status lets the failing profile print a ranking.
/// - witness: `cli::cli::a_failing_profile_is_refused_with_its_invocation`
fn output(command: &mut Command) -> Result<std::process::Output, CostError>
{
    let invocation = invocation_of(command);
    let output = command.output().map_err(|error| CostError::Command {
        command: invocation.clone(),
        message: error.to_string(),
    })?;
    if output.status.success() {
        Ok(output)
    }
    else {
        Err(CostError::Command {
            command: invocation,
            message: output.status.to_string(),
        })
    }
}
