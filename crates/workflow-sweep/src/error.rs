//! The refusals a sweep can meet, each naming what it refused.

use core::fmt;
use std::path::PathBuf;

/// Why a sweep could not decide what it visits.
///
/// # Specification
/// - provides: one variant per refusal; each carries the path or the command it
///   refused, so the message points at what must change.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SweepError
{
    /// A corpus directory or entry could not be read.
    Walk
    {
        /// The directory or entry.
        path: PathBuf,
        /// What reading it reported.
        detail: String,
    },
    /// A `git` invocation could not run, exited unsuccessfully, or printed
    /// what is not UTF-8.
    Git
    {
        /// The invocation, as a shell would spell it.
        command: String,
        /// What it reported.
        detail: String,
    },
    /// The built-in grammar the layout comparison parses with did not build.
    Grammar
    {
        /// What building it reported.
        detail: String,
    },
}

impl fmt::Display for SweepError
{
    /// Describes the refusal and names its input.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes one line naming the variant's input and its detail.
    /// - provides: the message a sweep test fails with.
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
            Self::Walk {
                ref path,
                ref detail,
            } => write!(f, "cannot read corpus entry {}: {detail}", path.display()),
            Self::Git {
                ref command,
                ref detail,
            } => write!(
                f,
                "`{command}` failed: {detail}; set GANDR_SWEEP_BASE to the revision the change is measured against"
            ),
            Self::Grammar { ref detail } => {
                write!(f, "the built-in grammar does not build: {detail}")
            },
        }
    }
}

/// A refusal is an error value, so a test can return it.
impl core::error::Error for SweepError
{
}

#[cfg(test)]
mod tests
{
    use std::path::PathBuf;

    use super::SweepError;

    #[test]
    fn every_refusal_names_its_input()
    {
        assert_eq!(
            SweepError::Walk {
                path: PathBuf::from("fixture/model"),
                detail: String::from("denied"),
            }
            .to_string(),
            "cannot read corpus entry fixture/model: denied"
        );
        assert_eq!(
            SweepError::Git {
                command: String::from("git merge-base origin/main HEAD"),
                detail: String::from("no such ref"),
            }
            .to_string(),
            "`git merge-base origin/main HEAD` failed: no such ref; set GANDR_SWEEP_BASE to the \
             revision the change is measured against"
        );
        assert_eq!(
            SweepError::Grammar {
                detail: String::from("a cycle"),
            }
            .to_string(),
            "the built-in grammar does not build: a cycle"
        );
    }
}
