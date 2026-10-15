//! The refusals a prune can meet, each naming what it refused.

use core::fmt;
use std::path::PathBuf;

/// Why a target directory could not be pruned.
///
/// # Specification
/// - provides: one variant per refusal; each carries the file it refused and
///   the detail, so the message points at what must change. Every refusal
///   happens before the first removal except [`BuildStateError::Io`] during
///   removal, which leaves the entries not yet visited in place.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum BuildStateError
{
    /// A file or a directory could not be read or removed.
    Io
    {
        /// The path the operation named.
        path: PathBuf,
        /// The operating system's description of the failure.
        message: String,
    },
    /// A line of a message file is not a JSON message.
    Json
    {
        /// The message file.
        path: PathBuf,
        /// The line, counted from one.
        line: usize,
        /// The parser's description of the defect.
        message: String,
    },
    /// A message file ends without Cargo's `build-finished` message, so it
    /// may name only part of the build.
    Unfinished
    {
        /// The message file.
        path: PathBuf,
    },
    /// A message file records a build that failed, so the units it names
    /// are not a build's complete set.
    Failed
    {
        /// The message file.
        path: PathBuf,
    },
    /// Standard output could not be written.
    Output
    {
        /// The writer's description of the failure.
        message: String,
    },
}

impl fmt::Display for BuildStateError
{
    /// Describes the refusal and names its input.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes one line naming the variant's path and its detail.
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
            Self::Json {
                ref path,
                line,
                ref message,
            } => write!(
                f,
                "{}:{line}: not a Cargo JSON message: {message}",
                path.display()
            ),
            Self::Unfinished { ref path } => write!(
                f,
                "{}: no `build-finished` message, so the build's units may be incomplete",
                path.display()
            ),
            Self::Failed { ref path } => write!(
                f,
                "{}: the build failed, so its units are not a complete set",
                path.display()
            ),
            Self::Output { ref message } => write!(f, "standard output: {message}"),
        }
    }
}

#[cfg(test)]
mod tests
{
    use std::path::PathBuf;

    use super::BuildStateError;

    #[test]
    fn every_refusal_names_its_input()
    {
        let path = PathBuf::from;
        let cases = [
            (
                BuildStateError::Io {
                    path: path("target/enforcing/debug/deps"),
                    message: "denied".into(),
                },
                "target/enforcing/debug/deps: denied",
            ),
            (
                BuildStateError::Json {
                    path: path("target/build-units.jsonl"),
                    line: 7,
                    message: "expected value".into(),
                },
                "target/build-units.jsonl:7: not a Cargo JSON message: expected value",
            ),
            (
                BuildStateError::Unfinished {
                    path: path("target/build-units.jsonl"),
                },
                "target/build-units.jsonl: no `build-finished` message, so the build's units \
                 may be incomplete",
            ),
            (
                BuildStateError::Failed {
                    path: path("target/build-units.jsonl"),
                },
                "target/build-units.jsonl: the build failed, so its units are not a complete set",
            ),
            (
                BuildStateError::Output {
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
