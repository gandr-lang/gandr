//! The run outcome a `runs` expectation states, and what settling one asks of
//! the caller.
//!
//! # The comparison is over spellings
//!
//! This crate holds no machine. A `runs` payload is the outcome's spelling,
//! and the caller that composes the pipeline runs the declaration and spells
//! what the run produced; the two compare byte for byte. The spelling is the
//! one the toolchain prints a run's outcome in, so a stated outcome reads as
//! what `gandr run` prints.

use alloc::string::String;
use core::fmt;

use gandr_kernel_term::ConstantIndex;

/// A run outcome, spelled: what a `runs` payload states, and what a run
/// produced.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RunSpelling(String);

impl From<String> for RunSpelling
{
    /// The outcome `spelled` spells.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(spelled: String) -> Self
    {
        Self(spelled)
    }
}

impl AsRef<str> for RunSpelling
{
    /// The spelling's text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        &self.0
    }
}

impl fmt::Display for RunSpelling
{
    /// Writes the spelling.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the supplied outcome spelling unchanged.
    /// - fails: returns the formatting refusal when the sink rejects the
    ///   spelling.
    /// - panics: none.
    /// - executable: none — the formatter does not expose emitted text or
    ///   readable sink state; the report consumer and a refusing sink observe
    ///   these effects.
    ///
    /// # Errors
    /// Returns `fmt::Error` when the sink refuses the spelling.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a parsed run expectation and a different non-ASCII
    ///   produced spelling; the unsettled report retains both payloads, and
    ///   formatting the produced spelling returns the exact sink error. Losing
    ///   either payload or swallowing a write refusal changes the observation;
    ///   sentence wording remains unconstrained.
    /// - witness: `run::tests::run_mismatches_expose_both_spellings_and_preserve_sink_refusal`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(&self.0)
    }
}

/// What settling a `runs` expectation asks of the caller: run one declaration
/// and spell its outcome.
///
/// # Specification
/// - requires: an implementation owns the module and execution context for the
///   declarations it runs.
/// - ensures: each supplied outcome uses the spelling its toolchain gives that
///   declaration, including a run that stops short of a value.
/// - panics: none for an implementation satisfying the interface.
/// - executable: none — the trait holds neither the module nor a machine or
///   renderer. The implementing execution context supplies those observations;
///   settlement checks when it asks for an outcome and compares the supplied
///   spelling exactly.
///
/// # Adequacy
/// - hypothesis: L3 — accepted, owed, refused and guarded declarations, with
///   matching and mismatching run expectations; settlement and callback
///   positions distinguish an unrequested run, a skipped requested run and a
///   changed spelling. The external implementation owns correctness of
///   execution and rendering.
/// - witness: `settle::tests::a_run_outcome_settles_under_either_root`
/// - witness: `run::tests::run_mismatches_expose_both_spellings_and_preserve_sink_refusal`
pub trait Runner
{
    /// The spelling of what running the declaration at `constant` produced.
    ///
    /// # Specification
    /// - requires: `constant` is the admission position of a declaration of the
    ///   module being settled that the checker accepted.
    /// - ensures: the spelling the toolchain prints that declaration's run
    ///   outcome in, a run that stops short of a value included.
    /// - provides: the produced side of a `runs` comparison.
    /// - fails: never; a run that cannot be carried out is an outcome of its
    ///   own, spelled.
    /// - panics: none.
    /// - executable: none — the required method has no body and carries no
    ///   module, machine or renderer with which to validate admission or
    ///   execution. Its implementing context must establish those premises.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — accepted, owed, refused and guarded declarations with
    ///   or without a run expectation; the requested admission positions and
    ///   exact settlement separate extra or missing calls and spelling
    ///   mismatches. These consumer witnesses assume a conforming execution
    ///   context rather than proving its machine semantics.
    /// - witness: `settle::tests::a_run_outcome_settles_under_either_root`
    /// - witness: `run::tests::run_mismatches_expose_both_spellings_and_preserve_sink_refusal`
    fn run(
        &mut self,
        constant: ConstantIndex,
    ) -> RunSpelling;
}

impl<Run> Runner for Run
where
    Run: FnMut(ConstantIndex) -> RunSpelling,
{
    /// Calls the closure.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn run(
        &mut self,
        constant: ConstantIndex,
    ) -> RunSpelling
    {
        self(constant)
    }
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;
    use alloc::string::ToString as _;
    use core::fmt;

    use gandr_kernel_term::ConstantIndex;
    use gandr_surface_syntax::SourceText;

    use super::RunSpelling;
    use crate::expectation::Outcome;
    use crate::fixture::RefusingWriter;
    use crate::fixture::checked;
    use crate::root::CorpusRoot;
    use crate::settle::Settlement;
    use crate::settle::settle;

    #[test]
    fn run_mismatches_expose_both_spellings_and_preserve_sink_refusal()
    {
        let checked = checked(SourceText::from("@[ runs(\"expected\") ] def value = 3 ;"));
        let mut runner = |_constant: ConstantIndex| RunSpelling::from(String::from("λ actual"));
        let report = settle(
            CorpusRoot::Fixture,
            &checked.arena,
            &checked.module,
            &checked.verdicts,
            &mut runner,
        )
        .expect("the fixture owns its verdicts");
        let declaration = report.declarations().first().expect("one declared value");
        assert_eq!(declaration.settlement(), Settlement::Unsettled);
        let rendered = report.to_string();
        assert!(
            rendered.contains("expected"),
            "a mismatch retains its expectation"
        );
        assert!(
            rendered.contains("λ actual"),
            "a mismatch retains its produced output"
        );
        let Outcome::Runs(spelled) = declaration.outcome()
        else {
            panic!("the accepted declaration was run");
        };
        assert_eq!(
            fmt::Write::write_fmt(&mut RefusingWriter, format_args!("{spelled}")),
            Err(fmt::Error),
            "rendering the produced output propagates a failed write"
        );
    }
}
