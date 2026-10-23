//! The two corpus roots and which expectations each admits.
//!
//! # Membership is location
//!
//! A source is a fixture or a gate by where it sits, never by what it says
//! about itself. The strict root gates: every declaration must check owing
//! nothing, and the expectations it admits are `checks`, which asserts exactly
//! that, `runs`, which asserts that and a run outcome besides, and
//! `normalizes`, which asserts that and a block's normal form. An `owes` or
//! `refuses` attribute there could describe a red declaration as green, so it
//! is refused as a source error instead of read.
//!
//! A source is a fixture or a gate by the root it sits under, never by what it
//! says about itself. `CorpusRoot::Strict` is the gating root: every
//! declaration is held to _checks, owing 0_, or to the stricter _runs to_ or
//! _normalizes_ line it states. `CorpusRoot::Fixture` is the root where the
//! checker's refusals and obligations are asserted, and all five schemas are
//! admitted
//! there. Inside a root, a declaration carrying an expectation attribute is a
//! fixture (`Membership::Fixture`) and gets its own line in the report; one
//! carrying none is counted.
//!
//! The alternative was an attribute or a file header marking a source as a
//! fixture, which hands the classification to the source being classified. The
//! choice reverses only together with the guard below: if self-description were
//! made safe some other way, membership could move into the source.
//!
//! # The corpus
//!
//! The language's sources live beside the library that settles them, under the
//! two roots `settle` names. `gandr check crates/surface-corpus/strict` and
//! `gandr test corpus` run them, and `mise run check:corpus` runs both as a
//! gate; a red root fails it.
//!
//! | Directory | Holds | Expectations |
//! | --------- | ----- | ------------ |
//! | `strict/` | sources in the fragment: signatures and definitions, literals and the unit value, thunks, lambdas, returns, forces and applications; under `classifier/`, both universes, quotes, a code constant unfolding, a polymorphic function at several instances, and the relative-monad witness — a type operator over a computation-valued carrier, written with every universe spelled out and with the defaults left off, instantiated, and equated with its instance spelled by hand through `=>`; under `pathological/`, the dependent instantiations whose codomains could capture | none, or `runs` on each declaration the fragment runs: every declaration checks, owing nothing |
//! | `corpus/fragment/` | one source per refusal the fragment's checker and lowering can raise at a declaration, one owed signature, and a run blamed on the goal it reaches | `refuses`, `checks`, `owes` or `runs` on each declaration |
//! | `corpus/classifier/` | the universe families' refusals: a level too large, a sort mismatch, a graded bridge, and a bind whose body's type needs its binder; the relative-monad witness's sort errors beside the forms that repair them; a static abstraction at a static parameter, normalized away, and at a dynamic one, refused; implicit parameters supplied by name, in any order | `refuses` on each refused declaration, `checks` on each that forms, `runs` on each run |
//! | `corpus/model/`, `corpus/pathological/`, `corpus/surface/` | the language's own surface programs whose declarations the lowering reads, each verdict stated | `refuses`, `checks` or `runs` on each declaration |
//! | `corpus/pending/` | the language's own surface programs the fragment does not yet cover | none: membership by location (§ The pending set) |
//!
//! The language's own surface programs — the model programs, the pathological
//! cases and the surface families — are kept in their own subdirectories with
//! their commentary removed. The parser reads every source here as its
//! zero-obligation gate — a pathological source whose point is a parse error
//! is pinned there to exactly the obligations it owes — and the highlighter's
//! role golden in `gandr-surface-grammar` mirrors every source: a source added,
//! moved between roots or removed is followed by `UPDATE_EXPECT=1 cargo
//! nextest run -p gandr-surface-grammar`, which rewrites the golden to match.
//! The parser's recovery record mirrors every `strict/` and `fixture/` source
//! the same way: `UPDATE_EXPECT=1 GANDR_RECOVERY_SOURCE=<path here> mise run
//! ci:recovery` re-records one source, and the diff is read for recovery
//! regressions.
//!
//! No count is pinned. The runner's report says how many sources each root
//! holds, how many declarations settled, the ledger size and the seal, and its
//! tests assert that each root holds declarations and that every row of the
//! fragment's exercised table is carried. Adding a source changes a count and
//! reddens no root; a source that stops settling reddens its root.
//!
//! A bind written in a block is always checked, because a block stands only in
//! a thunk, a lambda or a function's tail, and each of those is checked against
//! its declared type. The expected type is read outside the binder, so a body
//! whose type needs the binder fails to convert with it and the fixture states
//! `TypeMismatch`; the checker's `DependentBind` names the same mistake only
//! where a bind synthesises its type, which no surface form reaches yet. The
//! alternative was spelling the fixture around a synthesising bind, which the
//! surface has no form for. The fixture's expectation changes to
//! `DependentBind` when an ascription or a synthesising block lets a bind's
//! type come from its body.
//!
//! A `runs` outcome is written on every declaration the fragment runs to a
//! value or to blame: the literals, copies, functions and applications of
//! `strict/`, the classifier's values and polymorphic functions, the
//! pathological compositions, the model's unit, every module member whose body
//! checks, and the blamed run. A declaration the machine carries no image of —
//! a code, or a value that reaches one — states no run, because nothing runs
//! it; the run verb reports it as never reaching the machine.
//!
//! `pathological/module-forward-member-reference` names a later member inside
//! `second + 1`. The fragment does not read the infix operator, and a form is
//! refused before any name under it is read, so the fixture states
//! `OutOfFragment`; the forward-member refusal itself is witnessed by
//! `gandr-surface-lowering`'s module tests. The expectation becomes
//! `ForwardMemberReference` when the fragment reads infix operators.
//!
//! # One walk registers every source
//!
//! A source is registered by where it sits: the dispatcher's one walk over
//! `strict/` and `fixture/` reaches it, and nothing else decides what the
//! corpus holds. The kernel export suite here lists the two roots by the walk's
//! own rule — `.gandr` files, links not followed — because this crate does not
//! depend on the dispatcher; it reads what the walk reaches and registers
//! nothing of its own. An orphan is a `.gandr` file the walk does not reach —
//! one outside both roots, or behind a symbolic link, which the walk does not
//! follow — and the registration witness finds every such file by listing the
//! crate's directories, links followed, and fails naming each one:
//! `tests::corpus::every_corpus_source_is_registered` in
//! `gandr-surface-dispatcher`, its positive control
//! `tests::corpus::a_planted_orphan_is_not_registered`, which plants an orphan
//! outside the roots and one behind a link and expects exactly those two. No
//! count is pinned, so a source added where the walk reaches it moves a count
//! and reddens nothing, and one added where it does not reddens the witness,
//! which names the file.
//!
//! Two registration mechanisms would fail in opposite directions: a test file
//! not named in the test target's module list is never compiled, silently, and
//! a source added to the corpus moves a pinned count in a test the author has
//! not opened. Neither is here: this crate's suite is its modules' own
//! `cfg(test)` modules, compiled with the library, and the corpus has the one
//! walk and no pinned count.
//!
//! # The pending set
//!
//! A source under `fixture/pending/` carries a refusal no expectation can
//! state: the lowering refuses it as a whole — its root is not a list of
//! declarations — or refuses one of its declarations at the declaration's own
//! form, which files no half for an attribute to be read off. The runner counts
//! such a source as pending and settles none of its declarations; `test` prints
//! each such refusal, naming the form the fragment lacks — a call or an
//! operator, a record update, a data declaration, a module, an effect — which
//! is the former the source waits for, and its run outcomes are written when it
//! moves. A pending source that carries none — the fragment grew, and every
//! expectation it needs can be stated — is unsettled, and moves to the fixture
//! root with its expectations written.
//!
//! Three module sources stay pending for the second reason.
//! `pathological/module-malformed-recovery` writes a member whose definition
//! leaves its operand unwritten, refused at the member's own form;
//! `pathological/modules/module-missing-component` and
//! `pathological/modules/module-abstract-type-component` write a value
//! component and an abstract type component the body supplies no member for,
//! each refused at the component, which declares nothing. A refusal at the
//! declaration form itself has no half to carry an expectation. A type
//! component whose body supplies the member does: the check of the member at
//! the component's kind reads its expectation off the attributes written
//! before the member, `@[ refuses("…") ] type T = τ ;`, so
//! `surface/kinded-type-component` states its refusal and settles.
//!
//! The alternatives were leaving these sources out, which loses them, and
//! stating each one's refusal in an attribute, which the lowering cannot read
//! for either kind of refusal. The choice reverses when the lowering files an
//! attribute for a declaration refused at its form and a refusal of the whole
//! module can carry an expectation; the pending set then empties into the
//! fixture root.

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
/// - hypothesis: L3 — both roots and all five schemas; exact admission variants
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
    /// The fixture root: all five schemas are admitted, so a source here
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
    ///   `checks`, `runs` and `normalizes`, the schemas that assert at least
    ///   what the root already requires.
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
    /// - hypothesis: L3 — both roots crossed with all five schemas at a
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
        ExpectationSchema::Checks | ExpectationSchema::Runs | ExpectationSchema::Normalizes, Ok(())) | (Self::Strict,
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
            (
                Self::Fixture,
                ExpectationSchema::Checks
                | ExpectationSchema::Owes
                | ExpectationSchema::Refuses
                | ExpectationSchema::Runs
                | ExpectationSchema::Normalizes,
            )
            | (
                Self::Strict,
                ExpectationSchema::Checks | ExpectationSchema::Runs | ExpectationSchema::Normalizes,
            ) => Ok(()),
            (Self::Strict, ExpectationSchema::Owes | ExpectationSchema::Refuses) => {
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
    /// - executable: none — the formatter exposes neither the emitted text nor
    ///   the sink state; these effects are observed by the caller.
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
            Self::Strict => "strict",
            Self::Fixture => "fixture",
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
            (CorpusRoot::Strict, ExpectationSchema::Normalizes, Ok(())),
            (CorpusRoot::Fixture, ExpectationSchema::Checks, Ok(())),
            (CorpusRoot::Fixture, ExpectationSchema::Owes, Ok(())),
            (CorpusRoot::Fixture, ExpectationSchema::Refuses, Ok(())),
            (CorpusRoot::Fixture, ExpectationSchema::Runs, Ok(())),
            (CorpusRoot::Fixture, ExpectationSchema::Normalizes, Ok(())),
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
