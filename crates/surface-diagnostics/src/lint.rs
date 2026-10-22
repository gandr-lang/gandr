//! The lints: findings about a form the source may write either way, each
//! reported where an attribute in the source asks for it, or everywhere the
//! driver enables it, and the `deprecated` lint, reported at every use of a
//! declaration its author marked.
//!
//! # A lint names itself, not a refusal
//!
//! A finding is a [`Severity::Warning`](crate::Severity::Warning): it settles
//! nothing, so `gandr check` still exits zero on a source whose only
//! diagnostics are findings. Its identifier is the lint's own spelling,
//! `explicit-exits`, `explicit-runs` or `deprecated`, where a shadowed
//! builtin's is the refusal the reject policy files for the same bytes,
//! because no policy turns a finding into a refusal: an elided exit or run is
//! a form the language admits, and the lint is a house style a module
//! chooses. The alternative was naming a finding as a refusal it is not,
//! which would let a `refuses` expectation name it. Reversal: a lint some
//! policy makes refusing takes that refusal's name, as the shadowing warning
//! does.
//!
//! An `explicit-exits` or `explicit-runs` finding carries the fix that
//! settles it, the keyword written before the tail or the nested
//! computation, so applying the fix and checking again reports nothing.
//!
//! # A use of a deprecated declaration is a lint's finding everywhere
//!
//! A `@[ deprecated ]` declaration still checks and runs; each written name
//! that resolves to it is a finding of the `deprecated` lint, naming the
//! version and the note the attribute states. No attribute or flag is needed
//! for it to reach: the author of the declaration asked for it, and the user
//! of the name is the one it tells. It proposes no fix, because what to use
//! instead is prose in the note. The alternative was a warning named as a
//! refusal, as a shadowed builtin is, and no policy refuses a deprecated use.
//! Reversal: a policy that refuses deprecated uses names the refusal.

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
/// - witness: `tests::diagnostics::an_inferred_exit_is_a_finding_whose_fix_writes_its_keyword`
/// - witness: `tests::diagnostics::an_inferred_run_is_a_finding_whose_fix_writes_its_keyword`
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
    /// `deprecated`: every use of a declaration a `deprecated` attribute
    /// marks, wherever it is written.
    Deprecated,
}

impl AsRef<str> for Lint
{
    /// The lint's spelling: `explicit-exits`, `explicit-runs` or
    /// `deprecated`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        match *self {
            Self::ExplicitExits => "explicit-exits",
            Self::ExplicitRuns => "explicit-runs",
            Self::Deprecated => "deprecated",
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
