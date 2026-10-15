//! The lints: findings about a form the source may write either way, each
//! reported where an attribute in the source asks for it, or everywhere the
//! driver enables it.
//!
//! # A lint names itself, not a refusal
//!
//! A finding is a [`Severity::Warning`](crate::Severity::Warning): it settles
//! nothing, so `gandr check` still exits zero on a source whose only
//! diagnostics are findings. Its identifier is the lint's own spelling,
//! `explicit-exits` or `explicit-runs`, where a shadowed builtin's is the
//! refusal the reject policy files for the same bytes, because no policy
//! turns a finding into a refusal: an elided exit or run is a form the
//! language admits, and the lint is a house style a module chooses. The
//! alternative was naming a finding as a refusal it is not, which would let a
//! `refuses` expectation name it. Reversal: a lint some policy makes refusing
//! takes that refusal's name, as the shadowing warning does.
//!
//! A finding carries the fix that settles it, the keyword written before the
//! tail or the nested computation, so applying the fix and checking again
//! reports nothing.

use core::fmt;

/// A lint the toolchain knows.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one variant per lint, each spelled as its driver flag and its
///   diagnostics' identifier spell it.
/// - provides: the lint vocabulary every face and the driver share.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a finding of each lint is identified by its spelling in
///   the JSON image and on the terminal.
/// - witness: `diagnostics::diagnostics::an_inferred_exit_is_a_finding_whose_fix_writes_its_keyword`
/// - witness: `diagnostics::diagnostics::an_inferred_run_is_a_finding_whose_fix_writes_its_keyword`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Lint
{
    /// `explicit-exits`: every exit the lowering inferred where a path
    /// through a body ends, which the source could write.
    ExplicitExits,
    /// `explicit-runs`: every run the checker inferred where a computation
    /// stands in a position that reads a value, which the source could
    /// write; with its `effects` option, only the runs that perform an
    /// effect.
    ExplicitRuns,
}

impl AsRef<str> for Lint
{
    /// The lint's spelling: `explicit-exits` or `explicit-runs`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        match *self {
            Self::ExplicitExits => "explicit-exits",
            Self::ExplicitRuns => "explicit-runs",
        }
    }
}

impl fmt::Display for Lint
{
    /// Writes the lint's spelling.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(self.as_ref())
    }
}
