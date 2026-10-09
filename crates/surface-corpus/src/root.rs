//! The two corpus roots and which expectations each admits.
//!
//! # Membership is location
//!
//! A source is a fixture or a gate by where it sits, never by what it says
//! about itself. The strict root gates: every declaration must check owing
//! nothing, and the expectations it admits are `checks`, which asserts exactly
//! that, and `runs`, which asserts that and a run outcome besides. An `owes` or
//! `refuses` attribute there could describe a red declaration as green, so it
//! is refused as a source error instead of read.

use core::fmt;

use gandr_surface_syntax::ByteSpan;

use crate::expectation::ExpectationSchema;
use crate::refusal::CorpusRefusal;

/// Which corpus root a source sits under.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum CorpusRoot
{
    /// The gating root: every declaration is held to *checks, owing nothing*,
    /// and an `owes` or `refuses` attribute is refused outright.
    Strict,
    /// The fixture root: all four schemas are admitted, so a source here
    /// asserts what the checker refuses and what it owes.
    Fixture,
}

impl CorpusRoot
{
    /// Admit an expectation of `schema`, written at `span`, under this root.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the fixture root admits every schema; the strict root admits
    ///   `checks` and `runs`, the schemas that assert at least what the root
    ///   already requires.
    /// - provides: the guard that keeps a gating source from describing itself
    ///   green.
    /// - fails: [`CorpusRefusal::ExpectationOutsideFixtureRoot`], naming the
    ///   schema and its span, for `owes` or `refuses` under the strict root.
    /// - panics: none.
    ///
    /// # Errors
    /// [`CorpusRefusal::ExpectationOutsideFixtureRoot`] when the strict root
    /// meets an `owes` or `refuses` expectation.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the domain is two roots by four schemas, enumerated
    ///   against a pinned eight-row table, so a widened or narrowed arm breaks
    ///   its row; the guard's effect on a whole declaration is settled end to
    ///   end.
    /// - witness: `root::tests::the_admission_table_is_pinned`
    /// - witness: `settle::tests::the_strict_root_refuses_an_expectation_outside_the_fixture_root`
    #[inline]
    pub const fn admit(
        self,
        schema: ExpectationSchema,
        span: ByteSpan,
    ) -> Result<(), CorpusRefusal>
    {
        match (self, schema) {
            | (
                Self::Fixture,
                ExpectationSchema::Checks
                | ExpectationSchema::Owes
                | ExpectationSchema::Refuses
                | ExpectationSchema::Runs,
            )
            | (Self::Strict, ExpectationSchema::Checks | ExpectationSchema::Runs) => Ok(()),
            | (Self::Strict, ExpectationSchema::Owes | ExpectationSchema::Refuses) => {
                Err(CorpusRefusal::ExpectationOutsideFixtureRoot { schema, span })
            },
        }
    }
}

impl fmt::Display for CorpusRoot
{
    /// Writes the root's name: `strict` or `fixture`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            | Self::Strict => "strict",
            | Self::Fixture => "fixture",
        })
    }
}

#[cfg(test)]
mod tests
{
    use super::CorpusRoot;
    use crate::expectation::ExpectationSchema;
    use crate::fixture::empty_span;
    use crate::refusal::CorpusRefusal;

    #[test]
    fn the_admission_table_is_pinned()
    {
        let span = empty_span();
        let refused = |schema| Err(CorpusRefusal::ExpectationOutsideFixtureRoot { schema, span });
        let table = [
            (CorpusRoot::Strict, ExpectationSchema::Checks, Ok(())),
            (
                CorpusRoot::Strict,
                ExpectationSchema::Owes,
                refused(ExpectationSchema::Owes),
            ),
            (
                CorpusRoot::Strict,
                ExpectationSchema::Refuses,
                refused(ExpectationSchema::Refuses),
            ),
            (CorpusRoot::Strict, ExpectationSchema::Runs, Ok(())),
            (CorpusRoot::Fixture, ExpectationSchema::Checks, Ok(())),
            (CorpusRoot::Fixture, ExpectationSchema::Owes, Ok(())),
            (CorpusRoot::Fixture, ExpectationSchema::Refuses, Ok(())),
            (CorpusRoot::Fixture, ExpectationSchema::Runs, Ok(())),
        ];

        for (root, schema, admitted) in table {
            assert_eq!(
                root.admit(schema, span),
                admitted,
                "the {root} root's admission of `{schema}` is pinned"
            );
        }
    }
}
