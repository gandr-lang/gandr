//! The refusals of a run, each naming what it refused.

use core::fmt;

use crate::name::Check;

/// Why a run gave no answer.
///
/// # Specification
/// - provides: one variant per refusal; each carries the command, the file or
///   the check that it refused, so the message points at what must change.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum GateError
{
    /// A program did not start, or it ended with a failure.
    Command
    {
        /// The program and its arguments.
        command: String,
        /// What the program wrote to standard error, or why it did not start.
        reason: String,
    },
    /// A table of the gate, or the answer of a program, is not what this
    /// crate reads.
    Read
    {
        /// The file or the answer.
        what: String,
        /// Why it does not read.
        reason: String,
    },
    /// `mise` lists no task of the check's name.
    Unlisted
    {
        /// The check.
        check: Check,
    },
    /// A thread of the run stopped with no result.
    Thread
    {
        /// The part that the thread ran.
        part: String,
    },
}

impl fmt::Display for GateError
{
    /// Describes the refusal and names its input.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes one line that names the variant's input and its
    ///   detail.
    /// - provides: the message that the binary prints before it exits with
    ///   status 2.
    /// - fails: propagates the formatter's own write failure.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the rendering of each variant names its input and its
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
            Self::Command {
                ref command,
                ref reason,
            } => write!(f, "{command} failed: {reason}"),
            Self::Read {
                ref what,
                ref reason,
            } => write!(f, "{what} does not read: {reason}"),
            Self::Unlisted { ref check } => write!(f, "mise holds no task `{check}`"),
            Self::Thread { ref part } => write!(f, "the thread of {part} stopped with no result"),
        }
    }
}

/// A refusal is an error value, so a caller can carry it as one.
impl core::error::Error for GateError
{
}

#[cfg(test)]
mod tests
{
    use super::GateError;
    use crate::name::Check;

    #[test]
    fn every_refusal_names_its_input()
    {
        let command = GateError::Command {
            command: "git show".to_owned(),
            reason: "no object".to_owned(),
        };
        assert_eq!(command.to_string(), "git show failed: no object");
        let read = GateError::Read {
            what: "verdicts.json".to_owned(),
            reason: "expected a map".to_owned(),
        };
        assert_eq!(
            read.to_string(),
            "verdicts.json does not read: expected a map"
        );
        let unlisted = GateError::Unlisted {
            check: Check::from("check:other"),
        };
        assert_eq!(unlisted.to_string(), "mise holds no task `check:other`");
        let thread = GateError::Thread {
            part: "mise tasks ls".to_owned(),
        };
        assert_eq!(
            thread.to_string(),
            "the thread of mise tasks ls stopped with no result"
        );
    }
}
