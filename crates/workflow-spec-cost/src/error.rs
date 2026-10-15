//! The refusals a ranking can meet, each naming what it refused.

use core::fmt;
use std::path::PathBuf;

use gandr_workflow_test_timing::TimingError;

/// Why a specification-cost ranking could not be produced.
///
/// # Specification
/// - provides: one variant per refusal; each carries the file, the command or
///   the test it refused, so the message points at what must change.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CostError
{
    /// A file or a directory could not be read or written.
    Io
    {
        /// The path the operation named.
        path: PathBuf,
        /// The operating system's description of the failure.
        message: String,
    },
    /// A source file is not Rust the parser reads.
    Source
    {
        /// The file.
        path: PathBuf,
        /// The parser's description of the defect.
        message: String,
    },
    /// A `cargo` or `perf` invocation could not run, or exited unsuccessfully.
    Command
    {
        /// The invocation, as typed.
        command: String,
        /// Why it did not start, or how it exited.
        message: String,
    },
    /// nextest's test list is not the JSON this crate reads.
    Listing
    {
        /// The parser's description of the defect.
        message: String,
    },
    /// A requested test is not in the binary nextest listed.
    UnknownTest
    {
        /// The binary, as nextest names it.
        binary: String,
        /// The test.
        test: String,
    },
    /// A `--test` argument is not a binary and a test separated by a space.
    Workload
    {
        /// The argument.
        text: String,
    },
    /// A `--threshold` argument is not a ratio written with at most two
    /// decimals.
    Factor
    {
        /// The argument.
        text: String,
    },
    /// A `--floor` argument is not a non-negative number of seconds.
    Seconds
    {
        /// The argument.
        text: String,
    },
    /// No stored run names an enforcing test to profile.
    NoWorkloads
    {
        /// The store searched.
        dir: PathBuf,
    },
    /// The stored timing reports could not be read.
    Timing(TimingError),
    /// Standard output could not be written.
    Output
    {
        /// The writer's description of the failure.
        message: String,
    },
}

impl fmt::Display for CostError
{
    /// Describes the refusal and names its input.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes one line naming the variant's path, command, binary,
    ///   test or store, and its detail.
    /// - provides: the message the binary prints before exiting with status 2.
    /// - fails: propagates the formatter's own write failure.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every variant's rendering names its input and its
    ///   detail; a dropped field or a swapped variant changes the asserted
    ///   line.
    /// - witness: `error::tests::every_refusal_names_its_input`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Io {
                ref path,
                ref message,
            } => write!(f, "{}: {message}", path.display()),
            Self::Source {
                ref path,
                ref message,
            } => write!(
                f,
                "{}: not Rust the parser reads: {message}",
                path.display()
            ),
            Self::Command {
                ref command,
                ref message,
            } => write!(f, "`{command}` failed: {message}"),
            Self::Listing { ref message } => {
                write!(f, "nextest's test list is not readable: {message}")
            },
            Self::UnknownTest {
                ref binary,
                ref test,
            } => write!(f, "`{binary}` lists no test `{test}`"),
            Self::Workload { ref text } => {
                write!(
                    f,
                    "`{text}` is not a test binary and a test separated by a space"
                )
            },
            Self::Factor { ref text } => {
                write!(f, "`{text}` is not a ratio with at most two decimals")
            },
            Self::Seconds { ref text } => {
                write!(f, "`{text}` is not a non-negative number of seconds")
            },
            Self::NoWorkloads { ref dir } => write!(
                f,
                "{}: no stored run names an enforcing test; run `mise run ci:timing` first",
                dir.display()
            ),
            Self::Timing(ref error) => fmt::Display::fmt(error, f),
            Self::Output { ref message } => write!(f, "standard output: {message}"),
        }
    }
}

/// A refusal is an error value, so clap can report a malformed `--test`.
impl core::error::Error for CostError
{
}

impl From<TimingError> for CostError
{
    /// Carries a timing report's refusal unchanged.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(error: TimingError) -> Self
    {
        Self::Timing(error)
    }
}

#[cfg(test)]
mod tests
{
    use std::path::PathBuf;

    use gandr_workflow_test_timing::TimingError;

    use super::CostError;

    #[test]
    fn every_refusal_names_its_input()
    {
        let path = PathBuf::from;
        let cases = [
            (
                CostError::Io {
                    path: path("target/spec-cost/profiles/0.data"),
                    message: "denied".into(),
                },
                "target/spec-cost/profiles/0.data: denied",
            ),
            (
                CostError::Source {
                    path: path("crates/a/src/lib.rs"),
                    message: "expected `;`".into(),
                },
                "crates/a/src/lib.rs: not Rust the parser reads: expected `;`",
            ),
            (
                CostError::Command {
                    command: "perf record".into(),
                    message: "exit status: 255".into(),
                },
                "`perf record` failed: exit status: 255",
            ),
            (
                CostError::Listing {
                    message: "missing field `cwd`".into(),
                },
                "nextest's test list is not readable: missing field `cwd`",
            ),
            (
                CostError::UnknownTest {
                    binary: "gandr-a::tests".into(),
                    test: "slow::t".into(),
                },
                "`gandr-a::tests` lists no test `slow::t`",
            ),
            (
                CostError::Workload {
                    text: "slow::t".into(),
                },
                "`slow::t` is not a test binary and a test separated by a space",
            ),
            (
                CostError::Factor {
                    text: "2.505".into(),
                },
                "`2.505` is not a ratio with at most two decimals",
            ),
            (
                CostError::Seconds { text: "-1".into() },
                "`-1` is not a non-negative number of seconds",
            ),
            (
                CostError::NoWorkloads {
                    dir: path("target/test-timing"),
                },
                "target/test-timing: no stored run names an enforcing test; run `mise run \
                 ci:timing` first",
            ),
            (
                CostError::from(TimingError::NoRuns {
                    dir: path("target/test-timing"),
                }),
                "target/test-timing: no stored run to report on",
            ),
            (
                CostError::Output {
                    message: "broken pipe".into(),
                },
                "standard output: broken pipe",
            ),
        ];
        for (error, expected) in cases {
            assert_eq!(error.to_string(), expected, "{error:?}");
        }
    }
}
