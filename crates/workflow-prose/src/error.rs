//! The refusals the prose check can meet, each naming what it refused.

use core::fmt;
use std::path::PathBuf;

/// Why the prose check could not run.
///
/// # Specification
/// - provides: one variant per refusal; each carries the path or the command it
///   refused, so the message points at what must change.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProseError
{
    /// A file the check reads or writes could not be read or written.
    Io
    {
        /// The file.
        path: PathBuf,
        /// The system's description of the failure.
        message: String,
    },
    /// The glossary is not a table of words, each a part of speech the check
    /// knows.
    Glossary
    {
        /// What the reader found.
        message: String,
    },
    /// A ledger line is not a path, a rule and a digest.
    Ledger
    {
        /// The line.
        line: String,
    },
    /// The parse script could not run, exited unsuccessfully, or printed what
    /// this crate does not read.
    Parse
    {
        /// The invocation, as typed.
        command: String,
        /// Why it did not start, how it exited, or what it printed.
        message: String,
    },
}

impl fmt::Display for ProseError
{
    /// Describes the refusal and names its input.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes one line naming the variant's input and its detail.
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
            Self::Glossary { ref message } => write!(f, "corpus/glossary.toml: {message}"),
            Self::Ledger { ref line } => write!(
                f,
                "corpus/prose.ledger: `{line}` is not a path, a rule and a digest"
            ),
            Self::Parse {
                ref command,
                ref message,
            } => write!(f, "`{command}` failed: {message}"),
        }
    }
}

/// A refusal is an error value, so the binary reports it as one.
impl core::error::Error for ProseError
{
}

#[cfg(test)]
mod tests
{
    use std::path::PathBuf;

    use super::ProseError;

    #[test]
    fn every_refusal_names_its_input()
    {
        let cases = [
            (
                ProseError::Io {
                    path: PathBuf::from("corpus/prose.ledger"),
                    message: "permission denied".into(),
                },
                "corpus/prose.ledger: permission denied",
            ),
            (
                ProseError::Glossary {
                    message: "`refuse` is `verbal`, not a part of speech".into(),
                },
                "corpus/glossary.toml: `refuse` is `verbal`, not a part of speech",
            ),
            (
                ProseError::Ledger {
                    line: "corpus/a.gandr Passive".into(),
                },
                "corpus/prose.ledger: `corpus/a.gandr Passive` is not a path, a rule and a \
                 digest",
            ),
            (
                ProseError::Parse {
                    command: "python parse.py".into(),
                    message: "exit status: 1: No module named 'spacy'".into(),
                },
                "`python parse.py` failed: exit status: 1: No module named 'spacy'",
            ),
        ];
        for (error, expected) in cases {
            assert_eq!(error.to_string(), expected, "{error:?}");
        }
    }
}
