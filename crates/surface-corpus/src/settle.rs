//! The settle comparison: each declaration's stated verdict against the one it
//! produced, and the obligations that survive between them.
//!
//! # Lockstep with the checker
//!
//! A driver hands the checker every declaration the lowering did not refuse,
//! in admission order. The comparison walks the module's declarations in the
//! same order, pairs each such declaration with the next verdict by its
//! admission position, and refuses verdicts that do not line up — one
//! missing, one for another position, one left over — because settling a
//! module against another module's verdicts is a caller fault, never a
//! verdict.
//!
//! # A declaration's own obligations
//!
//! A declaration produces one obligation when its verdict is owed and none
//! otherwise: the checker records exactly one ledger entry per owed verdict,
//! so the count is read off the verdict, and the ledger size off the ledger.

use alloc::vec::Vec;
use core::error::Error;
use core::fmt;

use gandr_core_checker::ModuleReport;
use gandr_core_checker::ObligationCount;
use gandr_core_checker::Verdict;
use gandr_core_term::CoreArena;
use gandr_kernel_term::ConstantIndex;
use gandr_surface_lowering::AttributeEntry;
use gandr_surface_lowering::AttributeTable;
use gandr_surface_lowering::DeclarationOutcome;
use gandr_surface_lowering::LoweredDeclaration;
use gandr_surface_lowering::LoweredModule;
use gandr_surface_lowering::LoweringRefusal;
use gandr_surface_lowering::SurfaceName;
use gandr_surface_syntax::ByteSpan;
use quenchant_shape::shape::Maybe;

use crate::expectation;
use crate::expectation::Membership;
use crate::expectation::Outcome;
use crate::expectation::Stated;
use crate::refusal::CorpusRefusal;
use crate::refusal::Refusal;
use crate::report::SettleReport;
use crate::root::CorpusRoot;

quenchant_shape::reason_enum! {
    /// Why a declaration produced no refusal.
    pub mod produced_refusal {
        /// The declaration was not refused.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The checker judged the declaration checked, synthesised or
            /// owed.
            Unrefused,
        }
    }
}

/// Whether what was stated was produced.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Settlement
{
    /// The produced verdict is the stated one.
    Settled,
    /// The produced verdict differs from the stated one, or nothing was
    /// stated that a production could meet.
    Unsettled,
}

impl fmt::Display for Settlement
{
    /// Writes `settled` or `unsettled`.
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
            | Self::Settled => "settled",
            | Self::Unsettled => "unsettled",
        })
    }
}

/// What a declaration produced.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Produced<'source>
{
    /// The checker's verdict.
    Judged(Verdict),
    /// The lowering refused the declaration, so the checker never saw it.
    Unlowered(LoweringRefusal<'source>),
    /// The root refused an expectation the declaration carries; this stands
    /// in place of whatever the declaration produced.
    Guarded(CorpusRefusal),
}

impl<'source> Produced<'source>
{
    /// The refusal produced, when the declaration was refused.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a refused verdict, a lowering refusal and a corpus refusal
    ///   are each the refusal of their producer; a checked, synthesised or owed
    ///   verdict is no refusal.
    /// - provides: the produced side of a `refuses` comparison.
    /// - fails: never; an unrefused declaration is the
    ///   [`produced_refusal::Absent::Unrefused`] absence.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every producer's refusal is settled against a fixture
    ///   naming it, and every unrefused verdict kind against a fixture stating
    ///   a refusal, which a misrouted arm would settle.
    /// - witness: `settle::tests::every_refusal_a_source_reaches_settles_the_fixture_naming_it`
    /// - witness: `settle::tests::a_wrong_stated_verdict_is_unsettled_either_way`
    #[inline]
    pub const fn refusal(&self) -> Maybe<Refusal<'source>, produced_refusal::Absent>
    {
        match *self {
            | Self::Judged(Verdict::Refused(refusal)) => Maybe::Present(Refusal::Checking(refusal)),
            | Self::Judged(
                Verdict::Checked { .. } | Verdict::Synthesised { .. } | Verdict::Owed(_),
            ) => Maybe::Absent(produced_refusal::Absent::Unrefused),
            | Self::Unlowered(refusal) => Maybe::Present(Refusal::Lowering(refusal)),
            | Self::Guarded(refusal) => Maybe::Present(Refusal::Corpus(refusal)),
        }
    }
}

/// The obligations one declaration leaves unsettled.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Surviving
{
    /// Produced obligations nothing declares.
    undeclared: ObligationCount,
    /// Declared obligations nothing produces.
    unproduced: ObligationCount,
}

impl Surviving
{
    /// `undeclared` obligations produced with nothing declaring them, beside
    /// `unproduced` declared with nothing producing them.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        undeclared: ObligationCount,
        unproduced: ObligationCount,
    ) -> Self
    {
        Self {
            undeclared,
            unproduced,
        }
    }

    /// Produced obligations nothing declares.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn undeclared(&self) -> ObligationCount
    {
        self.undeclared
    }

    /// Declared obligations nothing produces.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn unproduced(&self) -> ObligationCount
    {
        self.unproduced
    }
}

impl fmt::Display for Surviving
{
    /// Writes both counts.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(
            f,
            "{} undeclared, {} unproduced",
            self.undeclared, self.unproduced
        )
    }
}

/// One declared name, settled: what it states beside what it produced.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct DeclarationReport<'source>
{
    /// The declared name.
    name: SurfaceName<'source>,
    /// The bytes of the declaration that introduced the name.
    span: ByteSpan,
    /// The name's admission position.
    constant: ConstantIndex,
    /// Whether the name carries an expectation.
    membership: Membership,
    /// The verdict the name states.
    stated: Stated,
    /// What the name produced.
    produced: Produced<'source>,
    /// The obligations its verdict left in the ledger.
    owed: ObligationCount,
}

impl<'source> DeclarationReport<'source>
{
    /// The declared name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn name(&self) -> SurfaceName<'source>
    {
        self.name
    }

    /// The bytes of the declaration that introduced the name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn span(&self) -> ByteSpan
    {
        self.span
    }

    /// The name's admission position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn constant(&self) -> ConstantIndex
    {
        self.constant
    }

    /// Whether the name carries an expectation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn membership(&self) -> Membership
    {
        self.membership
    }

    /// The verdict the name states.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn stated(&self) -> Stated
    {
        self.stated
    }

    /// What the name produced.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn produced(&self) -> Produced<'source>
    {
        self.produced
    }

    /// The obligations the name's verdict left in the ledger.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn owed(&self) -> ObligationCount
    {
        self.owed
    }

    /// The produced verdict, read in the stated verdict's shape.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the produced refusal's name when one was produced, else
    ///   checks owing the declaration's own obligations.
    /// - provides: the side the settle comparison holds the stated verdict
    ///   against.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — both arms are driven against a stated verdict of the
    ///   other arm and of their own, so a swapped arm or a constant count
    ///   unsettles a control row or settles a mismatched one.
    /// - witness: `settle::tests::a_wrong_stated_verdict_is_unsettled_either_way`
    #[inline]
    #[must_use]
    pub const fn outcome(&self) -> Outcome
    {
        match self.produced.refusal() {
            | Maybe::Present(refusal) => Outcome::Refuses(refusal.name()),
            | Maybe::Absent(produced_refusal::Absent::Unrefused) => Outcome::Checks(self.owed),
        }
    }

    /// Whether the name produced what it states.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: settled exactly when a verdict is stated and equals
    ///   [`Self::outcome`]; a malformed expectation never settles.
    /// - provides: the per-declaration half of the run predicate.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each axis is driven wrong in both directions beside a
    ///   corrected control: a refusal stated and none produced, one produced
    ///   and none stated, another refusal produced than stated, more and fewer
    ///   obligations than stated, and a malformed expectation.
    /// - witness: `settle::tests::a_wrong_stated_verdict_is_unsettled_either_way`
    /// - witness: `settle::tests::a_refusal_outside_the_vocabulary_fails_the_fixture`
    #[inline]
    #[must_use]
    pub fn settlement(&self) -> Settlement
    {
        match self.stated {
            | Stated::Verdict(stated) if stated == self.outcome() => Settlement::Settled,
            | Stated::Verdict(_) | Stated::Malformed(_) => Settlement::Unsettled,
        }
    }

    /// The obligations the name leaves unsettled.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: with `declared` the count a stated `checks` verdict names,
    ///   and zero for a stated refusal or a malformed expectation, the owed
    ///   obligations past `declared` are undeclared and the declared ones past
    ///   the owed are unproduced; at most one of the two is nonzero.
    /// - provides: the surviving count a report sums.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an owed hole with no declaration, a declared
    ///   obligation with no hole, and a declared hole are asserted at their
    ///   exact counts.
    /// - witness: `settle::tests::a_wrong_stated_verdict_is_unsettled_either_way`
    #[inline]
    #[must_use]
    pub fn surviving(&self) -> Surviving
    {
        let declared = match self.stated {
            | Stated::Verdict(Outcome::Checks(declared)) => usize::from(declared),
            | Stated::Verdict(Outcome::Refuses(_)) | Stated::Malformed(_) => 0_usize,
        };
        let owed = usize::from(self.owed);
        Surviving::new(
            ObligationCount::from(owed.saturating_sub(declared)),
            ObligationCount::from(declared.saturating_sub(owed)),
        )
    }
}

impl fmt::Display for DeclarationReport<'_>
{
    /// Writes one line: the settlement, the name and its span, what it
    /// states, what it produced with the refusal's class, and the obligations
    /// that survive when any do.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(
            f,
            "{} `{}` at {}: states {}; produced {}",
            self.settlement(),
            self.name,
            self.span,
            self.stated,
            self.outcome()
        )?;
        if let Maybe::Present(refusal) = self.produced.refusal() {
            write!(f, " ({})", refusal.classify())?;
        }
        let surviving = self.surviving();
        if surviving != Surviving::default() {
            write!(f, "; surviving obligations: {surviving}")?;
        }
        Ok(())
    }
}

/// Why verdicts cannot be settled against a module.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum SettleFault
{
    /// The verdicts ran out before a declaration the lowering did not refuse.
    MissingVerdict
    {
        /// The declaration's admission position.
        constant: ConstantIndex,
    },
    /// The next verdict answers another declaration than the next one due.
    MisalignedVerdict
    {
        /// The admission position of the declaration due.
        declared: ConstantIndex,
        /// The admission position the verdict answers.
        judged: ConstantIndex,
    },
    /// A verdict is left once every declaration is answered.
    SurplusVerdict
    {
        /// The admission position the verdict answers.
        constant: ConstantIndex,
    },
    /// An expectation's payload is not its schema's literal in the arena
    /// given.
    UnreadablePayload
    {
        /// The bytes the attribute covers.
        span: ByteSpan,
    },
}

impl fmt::Display for SettleFault
{
    /// Writes the fault and the positions or bytes it names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            | Self::MissingVerdict { constant } => write!(
                f,
                "no verdict answers the declaration at admission position {}",
                usize::from(constant)
            ),
            | Self::MisalignedVerdict { declared, judged } => write!(
                f,
                "the verdict for admission position {} stands where position {} is due",
                usize::from(judged),
                usize::from(declared)
            ),
            | Self::SurplusVerdict { constant } => write!(
                f,
                "the verdict for admission position {} answers no declaration of the module",
                usize::from(constant)
            ),
            | Self::UnreadablePayload { span } => write!(
                f,
                "the payload of the attribute at {span} is not its schema's literal in the arena given"
            ),
        }
    }
}

impl Error for SettleFault
{
}

/// Settle `verdicts` against `module` under `root`, reading expectation
/// payloads out of `arena`.
///
/// # Specification
/// - requires: `verdicts` are the checker's report for the declarations of
///   `module` the lowering did not refuse, in admission order, and `arena` is
///   the arena the lowering minted `module` into.
/// - ensures: one report per declared name, in admission order: what the name's
///   attributes state under `root`, beside the verdict paired with it by
///   admission position, its lowering refusal, or — overriding both — the
///   root's refusal of an expectation it does not admit; the report's ledger
///   size is the size of `verdicts`' ledger.
/// - provides: the settle comparison a corpus run is gated on.
/// - fails: [`SettleFault`] when a verdict is missing, misaligned or left over,
///   or an expectation payload is unreadable in `arena`.
/// - panics: none.
///
/// # Errors
/// [`SettleFault::MissingVerdict`], [`SettleFault::MisalignedVerdict`] and
/// [`SettleFault::SurplusVerdict`] when `verdicts` are not the module's own;
/// [`SettleFault::UnreadablePayload`] when `arena` does not hold an
/// expectation's payload.
///
/// # Adequacy
/// - hypothesis: L3 — every fault is driven by verdicts or an arena from
///   another module beside the module's own, and the pairing is exercised
///   across a lowering-refused declaration, whose missing verdict a consumer
///   that paired by list position would misalign.
/// - witness: `settle::tests::verdicts_that_are_not_the_modules_own_are_refused`
/// - witness: `settle::tests::a_lowering_refused_declaration_consumes_no_verdict`
/// - witness: `settle::tests::the_strict_root_refuses_an_expectation_outside_the_fixture_root`
/// - witness: `settle::tests::every_refusal_a_source_reaches_settles_the_fixture_naming_it`
#[inline]
pub fn settle<'source>(
    root: CorpusRoot,
    arena: &CoreArena,
    module: &LoweredModule<'source>,
    verdicts: &ModuleReport,
) -> Result<SettleReport<'source>, SettleFault>
{
    let mut judged = verdicts.judged().iter();
    let mut declarations = Vec::with_capacity(module.declarations().len());
    for lowered in module.declarations() {
        let expectations =
            expectation::read(root, attributes(module.attributes(), lowered), arena)?;
        let (produced, owed) = match lowered.outcome() {
            | DeclarationOutcome::Refused(refusal) => {
                (Produced::Unlowered(refusal), ObligationCount::from(0_usize))
            },
            | DeclarationOutcome::Completed { .. }
            | DeclarationOutcome::Uncompleted { .. }
            | DeclarationOutcome::Bodied { .. } => {
                let constant = lowered.constant();
                let Some(answer) = judged.next()
                else {
                    return Err(SettleFault::MissingVerdict { constant });
                };
                if answer.constant() != constant {
                    return Err(SettleFault::MisalignedVerdict {
                        declared: constant,
                        judged: answer.constant(),
                    });
                }
                let verdict = answer.verdict();
                let owed = match verdict {
                    | Verdict::Owed(_) => 1_usize,
                    | Verdict::Checked { .. }
                    | Verdict::Synthesised { .. }
                    | Verdict::Refused(_) => 0_usize,
                };
                (Produced::Judged(verdict), ObligationCount::from(owed))
            },
        };
        let produced = match expectations.guard {
            | Maybe::Present(refusal) => Produced::Guarded(refusal),
            | Maybe::Absent(expectation::guard::Absent::Admitted) => produced,
        };
        declarations.push(DeclarationReport {
            name: lowered.name(),
            span: lowered.span(),
            constant: lowered.constant(),
            membership: expectations.membership,
            stated: expectations.stated,
            produced,
            owed,
        });
    }
    if let Some(surplus) = judged.next() {
        return Err(SettleFault::SurplusVerdict {
            constant: surplus.constant(),
        });
    }

    Ok(SettleReport::new(
        root,
        declarations,
        verdicts.ledger().count(),
    ))
}

/// The attributes filed under `lowered`'s halves in `table`: the signature's,
/// then the definition's.
///
/// # Specification
/// trivial.
fn attributes<'table>(
    table: &'table AttributeTable,
    lowered: &LoweredDeclaration<'_>,
) -> impl Iterator<Item = &'table AttributeEntry>
{
    [lowered.signature(), lowered.definition()]
        .into_iter()
        .filter_map(|half| match half {
            | Maybe::Present(digest) => Some(digest),
            | Maybe::Absent(_) => None,
        })
        .flat_map(move |digest| table.entries(digest))
}

#[cfg(test)]
mod tests
{
    use gandr_core_checker::ObligationCount;
    use gandr_core_term::CoreArena;
    use gandr_core_term::FailureClass;
    use gandr_kernel_term::ConstantIndex;
    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::SourceText;
    use quenchant_shape::shape::Maybe;

    use super::DeclarationReport;
    use super::Produced;
    use super::SettleFault;
    use super::Settlement;
    use super::Surviving;
    use super::settle;
    use crate::expectation::ExpectationFault;
    use crate::expectation::ExpectationSchema;
    use crate::expectation::Membership;
    use crate::expectation::Outcome;
    use crate::expectation::Stated;
    use crate::expectation::owing_nothing;
    use crate::fixture::checked;
    use crate::fixture::settled;
    use crate::fixture::span;
    use crate::refusal::CorpusRefusal;
    use crate::refusal::RefusalName;
    use crate::report::SettleReport;
    use crate::root::CorpusRoot;

    /// The one declaration `report` holds.
    ///
    /// # Specification
    /// trivial.
    fn only<'report, 'source>(
        report: &'report SettleReport<'source>
    ) -> &'report DeclarationReport<'source>
    {
        let [ref declaration] = *report.declarations()
        else {
            panic!("the fixture declares one name");
        };
        declaration
    }

    #[test]
    fn a_refusal_outside_the_vocabulary_fails_the_fixture()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let near = settled(
            CorpusRoot::Fixture,
            SourceText::from(r#"@[ refuses("UnresolvedNames") ] def a = b ;"#),
        );
        let named = settled(
            CorpusRoot::Fixture,
            SourceText::from(r#"@[ refuses("UnresolvedName") ] def a = b ;"#),
        );

        assert_eq!(
            only(&near).stated(),
            Stated::Malformed(ExpectationFault::UnknownRefusal { span: at(3, 29) }),
            "a near miss names no refusal, and the fault names the attribute"
        );
        assert_eq!(
            only(&near).settlement(),
            Settlement::Unsettled,
            "an expectation naming no refusal fails the fixture"
        );
        assert_eq!(
            only(&named).settlement(),
            Settlement::Settled,
            "the exact name settles the same declaration"
        );
    }

    #[test]
    fn a_wrong_stated_verdict_is_unsettled_either_way()
    {
        let rows = [
            (
                r#"@[ owes(1) ] def a : Integer ;"#,
                Settlement::Settled,
                (0_usize, 0_usize),
            ),
            (
                r#"@[ owes(1) ] def a : Integer ; def a = 3 ;"#,
                Settlement::Unsettled,
                (0_usize, 1_usize),
            ),
            (
                r#"@[ owes(2) ] def a : Integer ;"#,
                Settlement::Unsettled,
                (0_usize, 1_usize),
            ),
            (
                r#"def a : Integer ;"#,
                Settlement::Unsettled,
                (1_usize, 0_usize),
            ),
            (
                r#"@[ checks ] def a : Integer ;"#,
                Settlement::Unsettled,
                (1_usize, 0_usize),
            ),
            (
                r#"@[ checks ] def a : Integer ; def a = 3 ;"#,
                Settlement::Settled,
                (0_usize, 0_usize),
            ),
            (
                r#"@[ refuses("TypeMismatch") ] def a : Integer ; def a = "three" ;"#,
                Settlement::Settled,
                (0_usize, 0_usize),
            ),
            (
                r#"@[ refuses("TypeMismatch") ] def a : Integer ; def a = 3 ;"#,
                Settlement::Unsettled,
                (0_usize, 0_usize),
            ),
            (
                r#"def a : Integer ; def a = "three" ;"#,
                Settlement::Unsettled,
                (0_usize, 0_usize),
            ),
            (
                r#"@[ refuses("ShapeMismatch") ] def a : Integer ; def a = "three" ;"#,
                Settlement::Unsettled,
                (0_usize, 0_usize),
            ),
            (
                r#"@[ refuses("TypeMismatch") ] def a : Integer ;"#,
                Settlement::Unsettled,
                (1_usize, 0_usize),
            ),
        ];

        for (source, settlement, (undeclared, unproduced)) in rows {
            let report = settled(CorpusRoot::Fixture, SourceText::from(source));
            let declaration = only(&report);
            assert_eq!(
                declaration.settlement(),
                settlement,
                "`{source}` settles as pinned"
            );
            assert_eq!(
                declaration.surviving(),
                Surviving::new(
                    ObligationCount::from(undeclared),
                    ObligationCount::from(unproduced)
                ),
                "`{source}` leaves its pinned obligations surviving"
            );
        }
    }

    #[test]
    fn a_name_carrying_two_expectations_states_none()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let rows = [
            (
                r#"@[ checks, owes(1) ] def a : Integer ;"#,
                Stated::Malformed(ExpectationFault::ConflictingExpectations {
                    first: at(3, 9),
                    second: at(11, 18),
                }),
            ),
            (
                r#"@[ owes(1) ] def a : Integer ; @[ checks ] def a = 3 ;"#,
                Stated::Malformed(ExpectationFault::ConflictingExpectations {
                    first: at(3, 10),
                    second: at(34, 40),
                }),
            ),
            (
                r#"@[ checks ] def a : Integer ; def a = 3 ;"#,
                owing_nothing(),
            ),
        ];

        for (source, stated) in rows {
            let report = settled(CorpusRoot::Fixture, SourceText::from(source));
            assert_eq!(
                only(&report).stated(),
                stated,
                "`{source}` states its pinned verdict"
            );
        }
        let report = settled(
            CorpusRoot::Fixture,
            SourceText::from(r#"@[ checks, owes(1) ] def a : Integer ;"#),
        );
        assert_eq!(
            only(&report).settlement(),
            Settlement::Unsettled,
            "two expectations settle nothing, even when one of them holds"
        );
    }

    #[test]
    fn the_strict_root_refuses_an_expectation_outside_the_fixture_root()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let owed = settled(
            CorpusRoot::Strict,
            SourceText::from(r#"@[ owes(1) ] def a : Integer ;"#),
        );
        let declaration = only(&owed);
        let guard = CorpusRefusal::ExpectationOutsideFixtureRoot {
            schema: ExpectationSchema::Owes,
            span: at(3, 10),
        };
        assert_eq!(
            declaration.produced(),
            Produced::Guarded(guard),
            "an `owes` under the strict root is the corpus refusal"
        );
        assert_eq!(
            declaration.stated(),
            owing_nothing(),
            "the strict root holds the declaration to checks owing nothing"
        );
        assert_eq!(
            declaration.settlement(),
            Settlement::Unsettled,
            "the guarded declaration is unsettled"
        );
        assert_eq!(
            usize::from(declaration.owed()),
            1_usize,
            "the guard keeps the obligation the verdict owes"
        );
        assert_eq!(
            usize::from(owed.ledger()),
            1_usize,
            "the ledger still records it"
        );

        let rows = [
            (
                CorpusRoot::Strict,
                r#"@[ refuses("ExpectationOutsideFixtureRoot") ] def a = 3 ;"#,
                Settlement::Unsettled,
            ),
            (
                CorpusRoot::Strict,
                r#"@[ refuses("UnresolvedName") ] def a = b ;"#,
                Settlement::Unsettled,
            ),
            (
                CorpusRoot::Strict,
                r#"@[ checks ] def a = 3 ;"#,
                Settlement::Settled,
            ),
            (
                CorpusRoot::Fixture,
                r#"@[ owes(1) ] def a : Integer ;"#,
                Settlement::Settled,
            ),
            (
                CorpusRoot::Fixture,
                r#"@[ refuses("UnresolvedName") ] def a = b ;"#,
                Settlement::Settled,
            ),
        ];
        for (root, source, settlement) in rows {
            let report = settled(root, SourceText::from(source));
            assert_eq!(
                only(&report).settlement(),
                settlement,
                "`{source}` under the {root} root settles as pinned"
            );
        }
        let named = settled(
            CorpusRoot::Strict,
            SourceText::from(r#"@[ refuses("ExpectationOutsideFixtureRoot") ] def a = 3 ;"#),
        );
        assert_eq!(
            only(&named).outcome(),
            Outcome::Refuses(RefusalName::ExpectationOutsideFixtureRoot),
            "naming the guard's own refusal produces it, and still states checks"
        );
    }

    #[test]
    fn every_refusal_a_source_reaches_settles_the_fixture_naming_it()
    {
        let rows = [
            (
                r#"@[ refuses("UnresolvedName") ] def a = b ;"#,
                RefusalName::UnresolvedName,
                FailureClass::MalformedSource,
            ),
            (
                r#"@[ refuses("UnresolvedTypeHead") ] def a : Intgr ;"#,
                RefusalName::UnresolvedTypeHead,
                FailureClass::MalformedSource,
            ),
            (
                r#"@[ refuses("DuplicateSignature") ] def a : Integer ; def a : Integer ;"#,
                RefusalName::DuplicateSignature,
                FailureClass::MalformedSource,
            ),
            (
                r#"@[ refuses("DuplicateDefinition") ] def a = 3 ; def a = 4 ;"#,
                RefusalName::DuplicateDefinition,
                FailureClass::MalformedSource,
            ),
            (
                r#"@[ refuses("OutOfFragment") ] def a : Integer * Integer ;"#,
                RefusalName::OutOfFragment,
                FailureClass::Unrepresentable,
            ),
            (
                r#"@[ refuses("UnknownAttribute"), check ] def a = 3 ;"#,
                RefusalName::UnknownAttribute,
                FailureClass::MalformedSource,
            ),
            (
                r#"@[ refuses("DuplicateAttribute"), refuses("DuplicateAttribute") ] def a = 3 ;"#,
                RefusalName::DuplicateAttribute,
                FailureClass::MalformedSource,
            ),
            (
                r#"@[ refuses("MissingPayload"), owes ] def a = 3 ;"#,
                RefusalName::MissingPayload,
                FailureClass::MalformedSource,
            ),
            (
                r#"@[ refuses("IllTypedPayload"), owes("one") ] def a = 3 ;"#,
                RefusalName::IllTypedPayload,
                FailureClass::MalformedSource,
            ),
            (
                r#"@[ refuses("TypeMismatch") ] def a : Integer ; def a = "three" ;"#,
                RefusalName::TypeMismatch,
                FailureClass::MalformedSource,
            ),
            (
                r#"@[ refuses("ShapeMismatch") ] def a : U (Integer -> F Integer) ; def a = thunk { ret 3 } ;"#,
                RefusalName::ShapeMismatch,
                FailureClass::MalformedSource,
            ),
            (
                r#"@[ refuses("NotSynthesisable") ] def a = thunk { ret 3 } ;"#,
                RefusalName::NotSynthesisable,
                FailureClass::MalformedSource,
            ),
            (
                r#"def b = c ; @[ refuses("UnknownConstant") ] def a = b ;"#,
                RefusalName::UnknownConstant,
                FailureClass::MalformedSource,
            ),
        ];

        for (source, name, class) in rows {
            let report = settled(CorpusRoot::Fixture, SourceText::from(source));
            let fixture = report
                .declarations()
                .iter()
                .find(|declaration| declaration.membership() == Membership::Fixture)
                .expect("the source carries one fixture");
            let Maybe::Present(refusal) = fixture.produced().refusal()
            else {
                panic!("`{source}` produces a refusal");
            };
            assert_eq!(refusal.name(), name, "`{source}` produces {name}");
            assert_eq!(refusal.classify(), class, "{name} is {class}");
            assert_eq!(
                fixture.settlement(),
                Settlement::Settled,
                "the fixture naming {name} settles"
            );
        }
    }

    #[test]
    fn a_lowering_refused_declaration_consumes_no_verdict()
    {
        let report = settled(
            CorpusRoot::Fixture,
            SourceText::from(
                r#"@[ refuses("UnresolvedName") ] def a = b ; @[ owes(1) ] def c : Integer ; def d = 3 ;"#,
            ),
        );

        let [ref refused, ref owed, ref checked] = *report.declarations()
        else {
            panic!("the module declares three names");
        };
        assert!(
            matches!(refused.produced(), Produced::Unlowered(_)),
            "the lowering-refused name carries the lowering's refusal"
        );
        assert_eq!(
            (owed.constant(), owed.outcome()),
            (
                ConstantIndex::from(1_usize),
                Outcome::Checks(ObligationCount::from(1_usize))
            ),
            "the first verdict answers the second name"
        );
        assert_eq!(
            (checked.constant(), checked.outcome()),
            (
                ConstantIndex::from(2_usize),
                Outcome::Checks(ObligationCount::from(0_usize))
            ),
            "the second verdict answers the third name"
        );
        assert_eq!(
            report.tally().settlement(),
            Settlement::Settled,
            "every name settles"
        );
    }

    #[test]
    fn verdicts_that_are_not_the_modules_own_are_refused()
    {
        let at = |start: usize, end: usize| span(ByteOffset::from(start), ByteOffset::from(end));
        let two = checked(SourceText::from(r#"def a = 3 ; def b = 4 ;"#));
        let one = checked(SourceText::from(r#"def a = 3 ;"#));
        let shifted = checked(SourceText::from(r#"def a = b ; def c = 3 ;"#));
        let owed = checked(SourceText::from(r#"@[ owes(1) ] def a : Integer ;"#));
        let rows = [
            (
                settle(CorpusRoot::Fixture, &two.arena, &two.module, &one.verdicts),
                SettleFault::MissingVerdict {
                    constant: ConstantIndex::from(1_usize),
                },
            ),
            (
                settle(CorpusRoot::Fixture, &one.arena, &one.module, &two.verdicts),
                SettleFault::SurplusVerdict {
                    constant: ConstantIndex::from(1_usize),
                },
            ),
            (
                settle(
                    CorpusRoot::Fixture,
                    &shifted.arena,
                    &shifted.module,
                    &one.verdicts,
                ),
                SettleFault::MisalignedVerdict {
                    declared: ConstantIndex::from(1_usize),
                    judged: ConstantIndex::from(0_usize),
                },
            ),
            (
                settle(
                    CorpusRoot::Fixture,
                    &CoreArena::new(),
                    &owed.module,
                    &owed.verdicts,
                ),
                SettleFault::UnreadablePayload { span: at(3, 10) },
            ),
        ];

        for (result, fault) in rows {
            assert_eq!(result, Err(fault), "the mismatch is refused: {fault}");
        }
        for own in [&two, &one, &shifted, &owed] {
            assert!(
                settle(CorpusRoot::Fixture, &own.arena, &own.module, &own.verdicts).is_ok(),
                "a module's own verdicts and arena settle"
            );
        }
    }
}
