//! Routes a driver invocation into the gandr surface pipeline.
//!
//! The driver (`gandr-lang`) owns the argument surface; this crate owns what
//! happens after an invocation is understood. Interaction modes and pipeline
//! entries arrive here as [`Invocation`] variants and leave as [`Outcome`]
//! values the driver renders.

/// One understood driver invocation, ready to route.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Invocation
{
    /// A bare invocation: report the toolchain-management status.
    Status,
}

/// What an invocation routed to, for the driver to render.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Outcome
{
    /// The toolchain-management status report.
    Status(StatusReport),
}

/// The toolchain-management status, rendered by the driver.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StatusReport;

impl core::fmt::Display for StatusReport
{
    /// Render the status line's message body.
    ///
    /// # Specification
    /// - requires: nothing; the report carries no state to render.
    /// - ensures: writes one sentence and no line terminator, so the driver
    ///   owns the line the message sits on.
    /// - provides: the placeholder body the driver prints until toolchain
    ///   management lands.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.write_str(
            "toolchain management is not yet implemented; see https://github.com/gandr-lang/gandr",
        )
    }
}

/// Route one invocation to its outcome.
///
/// # Specification
/// - requires: nothing; every [`Invocation`] variant routes.
/// - ensures: each variant maps to exactly one [`Outcome`] variant; routing
///   performs no I/O and touches no process state.
/// - provides: the outcome the driver renders. The postcondition stays prose.
///   Its effect half — no I/O, no process state touched — is not a predicate
///   over values, and `anodized`'s effect qualifiers are parsed declarations
///   rather than checks. Its routing half is a one-variant match whose whole
///   input domain the witness below enumerates, so a runtime clause would
///   restate an exhaustive enumeration.
/// - fails: never; routing is total over the invocation vocabulary.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 only — the decision surface is a one-variant match,
///   enumerated exhaustively with the exact outcome asserted.
/// - witness: `tests::status_routes_to_the_status_report`
#[inline]
#[must_use]
pub fn dispatch(invocation: Invocation) -> Outcome
{
    match invocation {
        | Invocation::Status => Outcome::Status(StatusReport),
    }
}

#[cfg(test)]
mod tests
{
    /// The routing table, enumerated exhaustively: one variant, one outcome.
    #[test]
    fn status_routes_to_the_status_report()
    {
        let outcome = super::dispatch(super::Invocation::Status);
        assert_eq!(outcome, super::Outcome::Status(super::StatusReport));
    }
}
