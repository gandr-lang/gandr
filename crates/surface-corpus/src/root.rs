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

use anodized::spec;
use gandr_surface_syntax::ByteSpan;

use crate::expectation::ExpectationSchema;
use crate::refusal::CorpusRefusal;

/// Which corpus root a source sits under.
///
/// # Specification
/// - requires: the caller selects the root by source location rather than
///   source attributes.
/// - ensures: strict admission rejects self-description as owing or refusing;
///   fixture admission permits each expectation schema.
/// - panics: none.
/// - executable: none — the tag carries no source path or filesystem
///   membership. Its caller supplies that provenance; `admit` checks the
///   selected policy.
///
/// # Adequacy
/// - hypothesis: L3 — both roots and all four schemas; exact admission variants
///   and a nonempty refusal span distinguish widened or narrowed policy arms.
///   End-to-end settlement distinguishes an expectation interpreted under the
///   wrong root; directory provenance remains a caller premise.
/// - witness: `root::tests::the_admission_table_is_pinned`
/// - witness: `settle::tests::the_strict_root_refuses_an_expectation_outside_the_fixture_root`
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
    /// - hypothesis: L3 — both roots crossed with all four schemas at a
    ///   nonempty byte span; exact results distinguish widened or narrowed
    ///   admissions, swapped refused schemas and lost source spans. The
    ///   end-to-end strict-root witness observes guarded settlement, not merely
    ///   the admission tag.
    /// - witness: `root::tests::the_admission_table_is_pinned`
    /// - witness: `settle::tests::the_strict_root_refuses_an_expectation_outside_the_fixture_root`
    #[spec(
        ensures: |ret| {
    matches!(
        (self, schema, ret), (Self::Fixture, _, Ok(())) | (Self::Strict,
        ExpectationSchema::Checks | ExpectationSchema::Runs, Ok(())) | (Self::Strict,
        ExpectationSchema::Owes, Err(CorpusRefusal::ExpectationOutsideFixtureRoot {
        schema : ExpectationSchema::Owes, .. })) | (Self::Strict,
        ExpectationSchema::Refuses, Err(CorpusRefusal::ExpectationOutsideFixtureRoot {
        schema : ExpectationSchema::Refuses, .. }))
    )
},
    )]
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
    /// - requires: nothing.
    /// - ensures: writes a label distinguishing the selected corpus root.
    /// - fails: returns the formatter sink refusal without swallowing it.
    /// - panics: none.
    /// - executable: none — the formatter exposes neither previously emitted
    ///   text nor the sink state; these effects are observed by the caller.
    ///
    /// # Errors
    /// Returns `fmt::Error` when the sink refuses the label.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — both root tags and a refusing sink; distinct rendered
    ///   labels and the exact formatting refusal distinguish collapsed root
    ///   names and discarded write failures. The English wording is not pinned.
    /// - witness: `root::tests::root_labels_are_distinct_and_propagate_sink_refusal`
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
    use alloc::string::ToString as _;
    use core::fmt;

    use gandr_surface_syntax::ByteOffset;

    use super::CorpusRoot;
    use crate::expectation::ExpectationSchema;
    use crate::fixture::RefusingWriter;
    use crate::fixture::span;
    use crate::refusal::CorpusRefusal;

    #[test]
    fn root_labels_are_distinct_and_propagate_sink_refusal()
    {
        assert_ne!(
            CorpusRoot::Strict.to_string(),
            CorpusRoot::Fixture.to_string()
        );
        assert_eq!(
            fmt::Write::write_fmt(&mut RefusingWriter, format_args!("{}", CorpusRoot::Strict)),
            Err(fmt::Error),
            "the root formatter propagates a failed write"
        );
    }

    #[test]
    fn the_admission_table_is_pinned()
    {
        let span = span(ByteOffset::from(11_usize), ByteOffset::from(29_usize));
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
