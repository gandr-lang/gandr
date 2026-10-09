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
    /// trivial.
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
