//! The refusals a timing report can meet, each naming what it refused.

use core::fmt;
use std::path::PathBuf;

use gandr_workflow_github::GitHubError;

/// Why a timing report could not be produced.
///
/// # Specification
/// - provides: one variant per refusal; each carries the file, the command or
///   the configuration term it refused, so the message points at what must
///   change.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TimingError
{
    /// A file or a directory could not be read or written.
    Io
    {
        /// The path the operation named.
        path: PathBuf,
        /// The operating system's description of the failure.
        message: String,
    },
    /// A report is not well-formed XML.
    Xml
    {
        /// The report.
        path: PathBuf,
        /// The parser's description of the defect.
        message: String,
    },
    /// A `<testcase>` element cannot be read as a timed test.
    TestCase
    {
        /// The report holding the element.
        path: PathBuf,
        /// What the element lacks.
        defect: TestCaseDefect,
    },
    /// The nextest configuration cannot be read as a priority table.
    Config
    {
        /// The configuration file.
        path: PathBuf,
        /// What the file holds that the report cannot read.
        defect: ConfigDefect,
    },
    /// A `gh` invocation could not run, exited unsuccessfully, or printed
    /// what this crate does not read.
    Gh(GitHubError),
    /// The report directory holds no stored run.
    NoRuns
    {
        /// The directory searched.
        dir: PathBuf,
    },
    /// Standard output could not be written.
    Output
    {
        /// The writer's description of the failure.
        message: String,
    },
}

/// What a `<testcase>` element lacks.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TestCaseDefect
{
    /// The element has no `name` attribute.
    MissingName,
    /// The element has no `classname` attribute, which names its binary.
    MissingBinary,
    /// The element has no `time` attribute.
    MissingTime,
    /// The `time` attribute is not a finite, non-negative number of seconds.
    Time(String),
}

/// What a nextest configuration holds that the report cannot read.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ConfigDefect
{
    /// The file is not TOML.
    Toml(String),
    /// `profile.default.overrides` is not an array of tables.
    Overrides,
    /// An override's `filter` is not a string.
    Filter,
    /// A filter term is neither `test(=NAME)` nor `test(TEXT)`.
    Term(String),
    /// An override's `priority` is not an integer from -100 to 100: the
    /// integer in backticks, or the kind of value it is.
    Priority(String),
}

impl fmt::Display for TimingError
{
    /// Describes the refusal and names its input.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes one line naming the variant's path, command or
    ///   directory and its detail.
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
            Self::Xml {
                ref path,
                ref message,
            } => write!(f, "{}: not a JUnit report: {message}", path.display()),
            Self::TestCase {
                ref path,
                ref defect,
            } => write!(f, "{}: {defect}", path.display()),
            Self::Config {
                ref path,
                ref defect,
            } => write!(f, "{}: {defect}", path.display()),
            Self::Gh(ref error) => error.fmt(f),
            Self::NoRuns { ref dir } => {
                write!(f, "{}: no stored run to report on", dir.display())
            },
            Self::Output { ref message } => write!(f, "standard output: {message}"),
        }
    }
}

impl fmt::Display for TestCaseDefect
{
    /// Describes what the element lacks.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the missing attribute, or the unreadable time as
    ///   given.
    /// - provides: the detail of [`TimingError::TestCase`].
    /// - fails: propagates the formatter's own write failure.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each defect renders its own attribute name or text.
    /// - witness: `error::tests::every_refusal_names_its_input`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::MissingName => f.write_str("a testcase has no `name`"),
            Self::MissingBinary => f.write_str("a testcase has no `classname`"),
            Self::MissingTime => f.write_str("a testcase has no `time`"),
            Self::Time(ref text) => write!(f, "a testcase time `{text}` is not seconds"),
        }
    }
}

impl fmt::Display for ConfigDefect
{
    /// Describes what the configuration holds that cannot be read.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the unreadable key, term or value as given.
    /// - provides: the detail of [`TimingError::Config`].
    /// - fails: propagates the formatter's own write failure.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each defect renders its own key, term or value.
    /// - witness: `error::tests::every_refusal_names_its_input`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Toml(ref message) => write!(f, "not TOML: {message}"),
            Self::Overrides => f.write_str("`profile.default.overrides` is not an array of tables"),
            Self::Filter => f.write_str("an override's `filter` is not a string"),
            Self::Term(ref term) => {
                write!(
                    f,
                    "filter term `{term}` is neither `test(=NAME)` nor `test(TEXT)`"
                )
            },
            Self::Priority(ref value) => {
                write!(f, "priority {value} is not an integer from -100 to 100")
            },
        }
    }
}

impl core::error::Error for TimingError
{
}

impl From<GitHubError> for TimingError
{
    /// The refusal of a failed `gh` invocation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(error: GitHubError) -> Self
    {
        Self::Gh(error)
    }
}

#[cfg(test)]
mod tests
{
    use std::path::PathBuf;

    use super::ConfigDefect;
    use super::TestCaseDefect;
    use super::TimingError;

    #[test]
    fn every_refusal_names_its_input()
    {
        let path = PathBuf::from("reports/junit.xml");
        let config = PathBuf::from(".config/nextest.toml");
        let cases = [
            (
                TimingError::Io {
                    path: path.clone(),
                    message: "denied".into(),
                },
                "reports/junit.xml: denied",
            ),
            (
                TimingError::Xml {
                    path: path.clone(),
                    message: "unexpected end".into(),
                },
                "reports/junit.xml: not a JUnit report: unexpected end",
            ),
            (
                TimingError::TestCase {
                    path: path.clone(),
                    defect: TestCaseDefect::MissingName,
                },
                "reports/junit.xml: a testcase has no `name`",
            ),
            (
                TimingError::TestCase {
                    path: path.clone(),
                    defect: TestCaseDefect::MissingBinary,
                },
                "reports/junit.xml: a testcase has no `classname`",
            ),
            (
                TimingError::TestCase {
                    path: path.clone(),
                    defect: TestCaseDefect::MissingTime,
                },
                "reports/junit.xml: a testcase has no `time`",
            ),
            (
                TimingError::TestCase {
                    path,
                    defect: TestCaseDefect::Time("-1".into()),
                },
                "reports/junit.xml: a testcase time `-1` is not seconds",
            ),
            (
                TimingError::Config {
                    path: config.clone(),
                    defect: ConfigDefect::Toml("expected `=`".into()),
                },
                ".config/nextest.toml: not TOML: expected `=`",
            ),
            (
                TimingError::Config {
                    path: config.clone(),
                    defect: ConfigDefect::Overrides,
                },
                ".config/nextest.toml: `profile.default.overrides` is not an array of tables",
            ),
            (
                TimingError::Config {
                    path: config.clone(),
                    defect: ConfigDefect::Filter,
                },
                ".config/nextest.toml: an override's `filter` is not a string",
            ),
            (
                TimingError::Config {
                    path: config.clone(),
                    defect: ConfigDefect::Term("package(x)".into()),
                },
                ".config/nextest.toml: filter term `package(x)` is neither `test(=NAME)` nor \
                 `test(TEXT)`",
            ),
            (
                TimingError::Config {
                    path: config,
                    defect: ConfigDefect::Priority("`101`".into()),
                },
                ".config/nextest.toml: priority `101` is not an integer from -100 to 100",
            ),
            (
                TimingError::NoRuns {
                    dir: PathBuf::from("target/test-timing"),
                },
                "target/test-timing: no stored run to report on",
            ),
            (
                TimingError::Output {
                    message: "broken pipe".into(),
                },
                "standard output: broken pipe",
            ),
        ];
        for (error, expected) in cases {
            assert_eq!(error.to_string(), expected, "rendering of {error:?}");
        }
    }
}
