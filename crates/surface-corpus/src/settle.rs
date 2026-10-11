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

use anodized::spec;
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
use crate::run::RunSpelling;
use crate::run::Runner;

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

quenchant_shape::reason_enum! {
    /// Why a declaration carries no run outcome.
    pub mod ran {
        /// The declaration was not run.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// It states no run outcome, so nothing asked for one.
            Unstated,
            /// It states one, but was refused or owes its body, so there is
            /// nothing to run.
            Unaccepted,
        }
    }
}

/// Whether what was stated was produced.
///
/// # Specification
/// - requires: the producer establishes correspondence with the source or
///   counts represented.
/// - ensures: A declaration settles exactly when it states a verdict equal to
///   its produced outcome; malformed expectations do not settle.
/// - panics: none.
/// - executable: none — The state carries no compared declarations;
///   `DeclarationReport::settlement` supplies the executable comparison.
///
/// # Adequacy
/// - hypothesis: L3 — matched and mismatched source expectations, missing or
///   shifted verdicts, and guarded and run-producing declarations. Exact
///   classifications, identities, counts and fault positions distinguish lost
///   or swapped fields at their consuming boundaries.
/// - witness: `settle::tests::a_wrong_stated_verdict_is_unsettled_either_way`
/// - witness: `settle::tests::a_refusal_outside_the_vocabulary_fails_the_fixture`
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
    /// - requires: nothing.
    /// - ensures: writes distinct settled and unsettled states.
    /// - fails: propagates a refusing sink as `fmt::Error`.
    /// - panics: none.
    /// - executable: none — the formatter exposes neither emitted text nor
    ///   readable sink state; output payloads and a refusing sink are observed
    ///   by the witness.
    ///
    /// # Errors
    /// Returns `fmt::Error` when the sink refuses a write.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — both settlement states, distinct residual counts,
    ///   every alignment/payload fault, and owed, refused and checked source
    ///   declarations. Required semantic fields and exact sink refusals
    ///   distinguish erased metadata and swallowed failures without fixing
    ///   sentences.
    /// - witness: `settle::tests::settlement_formatters_retain_fields_and_sink_refusals`
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
///
/// # Specification
/// - requires: the producer establishes correspondence with the source or
///   counts represented.
/// - ensures: Retains the checker verdict, lowering refusal or overriding
///   corpus guard with its producing stage.
/// - panics: none.
/// - executable: none — The carrier has no original source or arena to
///   validate; `settle` establishes correspondence and `refusal` specifies
///   stage selection.
///
/// # Adequacy
/// - hypothesis: L3 — matched and mismatched source expectations, missing or
///   shifted verdicts, and guarded and run-producing declarations. Exact
///   classifications, identities, counts and fault positions distinguish lost
///   or swapped fields at their consuming boundaries.
/// - witness: `settle::tests::every_refusal_a_source_reaches_settles_the_fixture_naming_it`
/// - witness: `settle::tests::the_strict_root_refuses_an_expectation_outside_the_fixture_root`
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
    /// - hypothesis: L3 — source-reached refusals from every producing stage,
    ///   and checked, synthesised and owed controls. Exact names, classes and
    ///   the strict guard’s nonempty span distinguish wrong routing, fabricated
    ///   refusals and lost guard metadata. The const predicate observes tags;
    ///   source witnesses observe payloads.
    /// - witness: `settle::tests::every_refusal_a_source_reaches_settles_the_fixture_naming_it`
    /// - witness: `settle::tests::a_wrong_stated_verdict_is_unsettled_either_way`
    /// - witness: `settle::tests::the_strict_root_refuses_an_expectation_outside_the_fixture_root`
    #[spec(
        ensures: |ret| {
    matches!(
        (* self, ret), (Self::Judged(Verdict::Refused(_)),
        Maybe::Present(Refusal::Checking(_))) | (Self::Judged(Verdict::Checked { .. } |
        Verdict::Data | Verdict::Synthesised { .. } | Verdict::Owed(_)),
        Maybe::Absent(produced_refusal::Absent::Unrefused)) | (Self::Unlowered(_),
        Maybe::Present(Refusal::Lowering(_))) | (Self::Guarded(_),
        Maybe::Present(Refusal::Corpus(_)))
    )
},
    )]
    #[inline]
    pub const fn refusal(&self) -> Maybe<Refusal<'source>, produced_refusal::Absent>
    {
        match *self {
            | Self::Judged(Verdict::Refused(refusal)) => Maybe::Present(Refusal::Checking(refusal)),
            | Self::Judged(
                Verdict::Data
                | Verdict::Checked { .. }
                | Verdict::Synthesised { .. }
                | Verdict::Owed(_),
            ) => Maybe::Absent(produced_refusal::Absent::Unrefused),
            | Self::Unlowered(refusal) => Maybe::Present(Refusal::Lowering(refusal)),
            | Self::Guarded(refusal) => Maybe::Present(Refusal::Corpus(refusal)),
        }
    }
}

/// The obligations one declaration leaves unsettled.
///
/// # Specification
/// - requires: the producer establishes correspondence with the source or
///   counts represented.
/// - ensures: Keeps undeclared production and unproduced declarations in
///   separate count channels. Per-declaration residuals have at most one
///   nonzero channel; aggregated residuals may have both.
/// - panics: none.
/// - executable: none — The counts do not retain original stated and owed
///   obligations; the per-declaration predicate and tally aggregation establish
///   their arithmetic interpretation.
///
/// # Adequacy
/// - hypothesis: L3 — matched and mismatched source expectations, missing or
///   shifted verdicts, and guarded and run-producing declarations. Exact
///   classifications, identities, counts and fault positions distinguish lost
///   or swapped fields at their consuming boundaries.
/// - witness: `settle::tests::a_wrong_stated_verdict_is_unsettled_either_way`
/// - witness: `report::tests::absorbing_a_tally_sums_every_count`
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
    /// - requires: nothing.
    /// - ensures: writes both residual count channels.
    /// - fails: propagates a refusing sink as `fmt::Error`.
    /// - panics: none.
    /// - executable: none — the formatter exposes neither emitted text nor
    ///   readable sink state; output payloads and a refusing sink are observed
    ///   by the witness.
    ///
    /// # Errors
    /// Returns `fmt::Error` when the sink refuses a write.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — both settlement states, distinct residual counts,
    ///   every alignment/payload fault, and owed, refused and checked source
    ///   declarations. Required semantic fields and exact sink refusals
    ///   distinguish erased metadata and swallowed failures without fixing
    ///   sentences.
    /// - witness: `settle::tests::settlement_formatters_retain_fields_and_sink_refusals`
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
///
/// # Specification
/// - requires: the producer establishes correspondence with the source or
///   counts represented.
/// - ensures: A settlement-produced report retains source identity, admission
///   position, stated and produced outcomes, owed obligations and the requested
///   run outcome.
/// - panics: none.
/// - executable: none — The record has no module, original attributes or
///   checker report; `settle` and the report’s comparison methods carry the
///   executable relationships.
///
/// # Adequacy
/// - hypothesis: L3 — matched and mismatched source expectations, missing or
///   shifted verdicts, and guarded and run-producing declarations. Exact
///   classifications, identities, counts and fault positions distinguish lost
///   or swapped fields at their consuming boundaries.
/// - witness: `settle::tests::a_lowering_refused_declaration_consumes_no_verdict`
/// - witness: `settle::tests::a_run_outcome_settles_under_either_root`
/// - witness: `settle::tests::the_strict_root_refuses_an_expectation_outside_the_fixture_root`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
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
    /// The outcome its run produced, when it states one and was run.
    ran: Maybe<RunSpelling, ran::Absent>,
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
    pub const fn stated(&self) -> &Stated
    {
        &self.stated
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
    /// - ensures: the produced refusal's name when one was produced; else the
    ///   outcome its run produced, when it states one and was run; else checks
    ///   owing the declaration's own obligations.
    /// - provides: the side the settle comparison holds the stated verdict
    ///   against.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — checked, owed, refused, guarded and requested-run
    ///   declarations beside mismatching expectations. Exact outcome variants,
    ///   counts and text distinguish changed precedence, erased obligations and
    ///   altered run spelling; the predicate borrows text rather than cloning a
    ///   second outcome.
    /// - witness: `settle::tests::a_wrong_stated_verdict_is_unsettled_either_way`
    /// - witness: `settle::tests::a_run_outcome_settles_under_either_root`
    /// - witness: `settle::tests::the_strict_root_refuses_an_expectation_outside_the_fixture_root`
    #[spec(
        ensures: |ret| match self.produced.refusal() {
    Maybe::Present(refusal) => ret == Outcome::Refuses(refusal.name()),
    Maybe::Absent(produced_refusal::Absent::Unrefused) => {
        match self.ran {
            Maybe::Present(ref spelled) => {
                matches!(ret, Outcome::Runs(ref actual) if actual == spelled)
            }
            Maybe::Absent(_) => ret == Outcome::Checks(self.owed),
        }
    }
},
    )]
    #[inline]
    #[must_use]
    pub fn outcome(&self) -> Outcome
    {
        match (self.produced.refusal(), &self.ran) {
            | (Maybe::Present(refusal), _) => Outcome::Refuses(refusal.name()),
            | (
                Maybe::Absent(produced_refusal::Absent::Unrefused),
                &Maybe::Present(ref spelled),
            ) => Outcome::Runs(spelled.clone()),
            | (Maybe::Absent(produced_refusal::Absent::Unrefused), &Maybe::Absent(_)) => {
                Outcome::Checks(self.owed)
            },
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
    /// - hypothesis: L3 — refusals and obligation counts mismatched in either
    ///   direction, matching and mismatching run spellings, and malformed
    ///   expectations. Exact settlement distinguishes variant-only comparison,
    ///   ignored payloads and accepting a malformed expectation; the predicate
    ///   compares borrowed text without another allocation.
    /// - witness: `settle::tests::a_wrong_stated_verdict_is_unsettled_either_way`
    /// - witness: `settle::tests::a_refusal_outside_the_vocabulary_fails_the_fixture`
    /// - witness: `settle::tests::a_name_carrying_two_expectations_states_none`
    /// - witness: `settle::tests::a_run_outcome_settles_under_either_root`
    #[spec(
        ensures: |ret| {
    (ret == Settlement::Settled)
        == match self.stated {
            Stated::Malformed(_) => false,
            Stated::Verdict(Outcome::Refuses(name)) => {
                matches!(
                    self.produced.refusal(), Maybe::Present(refusal) if refusal.name() ==
                    name
                )
            }
            Stated::Verdict(Outcome::Checks(count)) => {
                matches!(self.produced.refusal(), Maybe::Absent(_))
                    && matches!(self.ran, Maybe::Absent(_)) && count == self.owed
            }
            Stated::Verdict(Outcome::Runs(ref expected)) => {
                matches!(self.produced.refusal(), Maybe::Absent(_))
                    && matches!(
                        self.ran, Maybe::Present(ref actual) if actual == expected
                    )
            }
        }
},
    )]
    #[inline]
    #[must_use]
    pub fn settlement(&self) -> Settlement
    {
        let agrees = match self.stated {
            | Stated::Malformed(_) => false,
            | Stated::Verdict(Outcome::Refuses(name)) => matches!(
                self.produced.refusal(),
                Maybe::Present(refusal) if refusal.name() == name
            ),
            | Stated::Verdict(Outcome::Checks(count)) => {
                matches!(self.produced.refusal(), Maybe::Absent(_))
                    && matches!(self.ran, Maybe::Absent(_))
                    && count == self.owed
            },
            | Stated::Verdict(Outcome::Runs(ref expected)) => {
                matches!(self.produced.refusal(), Maybe::Absent(_))
                    && matches!(self.ran, Maybe::Present(ref actual) if actual == expected)
            },
        };
        if agrees {
            Settlement::Settled
        }
        else {
            Settlement::Unsettled
        }
    }

    /// The obligations the name leaves unsettled.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: with `declared` the count a stated `checks` verdict names,
    ///   and zero for a stated refusal, a stated run outcome or a malformed
    ///   expectation, the owed obligations past `declared` are undeclared and
    ///   the declared ones past the owed are unproduced; at most one of the two
    ///   is nonzero.
    /// - provides: the surviving count a report sums.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — owed and declared counts equal, below and above one
    ///   another, with checked, refused and run outcomes. Exact directional
    ///   residuals distinguish swapped channels, unsaturated subtraction and
    ///   counting a non-count expectation as obligations.
    /// - witness: `settle::tests::a_wrong_stated_verdict_is_unsettled_either_way`
    /// - witness: `settle::tests::a_run_outcome_settles_under_either_root`
    #[spec(
        ensures: |ret| {
    let declared = match self.stated {
        Stated::Verdict(Outcome::Checks(count)) => usize::from(count),
        _ => 0_usize,
    };
    let owed = usize::from(self.owed);
    usize::from(ret.undeclared) == owed.saturating_sub(declared)
        && usize::from(ret.unproduced) == declared.saturating_sub(owed)
        && (usize::from(ret.undeclared) == 0_usize
            || usize::from(ret.unproduced) == 0_usize)
},
    )]
    #[inline]
    #[must_use]
    pub fn surviving(&self) -> Surviving
    {
        let declared = match self.stated {
            | Stated::Verdict(Outcome::Checks(declared)) => usize::from(declared),
            | Stated::Verdict(Outcome::Refuses(_) | Outcome::Runs(_)) | Stated::Malformed(_) => {
                0_usize
            },
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
    /// - requires: nothing.
    /// - ensures: writes the declaration’s settlement, name, span, stated and
    ///   produced outcomes, refusal class when present, and nonzero residual
    ///   obligations.
    /// - fails: propagates a refusing sink as `fmt::Error`.
    /// - panics: none.
    /// - executable: none — the formatter exposes neither emitted text nor
    ///   readable sink state; output payloads and a refusing sink are observed
    ///   by the witness.
    ///
    /// # Errors
    /// Returns `fmt::Error` when the sink refuses a write.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — both settlement states, distinct residual counts,
    ///   every alignment/payload fault, and owed, refused and checked source
    ///   declarations. Required semantic fields and exact sink refusals
    ///   distinguish erased metadata and swallowed failures without fixing
    ///   sentences.
    /// - witness: `settle::tests::settlement_formatters_retain_fields_and_sink_refusals`
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
///
/// # Specification
/// - requires: the producer establishes correspondence with the source or
///   counts represented.
/// - ensures: Distinguishes missing, misaligned and surplus checker verdicts
///   from unreadable expectation payloads, retaining the admission positions or
///   source span of the fault.
/// - panics: none.
/// - executable: none — The enum does not retain the attempted module, verdict
///   sequence or arena; `settle` establishes the fault relation at its call
///   boundary.
///
/// # Adequacy
/// - hypothesis: L3 — matched and mismatched source expectations, missing or
///   shifted verdicts, and guarded and run-producing declarations. Exact
///   classifications, identities, counts and fault positions distinguish lost
///   or swapped fields at their consuming boundaries.
/// - witness: `settle::tests::verdicts_that_are_not_the_modules_own_are_refused`
/// - witness: `settle::tests::settlement_formatters_retain_fields_and_sink_refusals`
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
    /// - requires: nothing.
    /// - ensures: writes the fault kind and every admission position or source
    ///   span it carries.
    /// - fails: propagates a refusing sink as `fmt::Error`.
    /// - panics: none.
    /// - executable: none — the formatter exposes neither emitted text nor
    ///   readable sink state; output payloads and a refusing sink are observed
    ///   by the witness.
    ///
    /// # Errors
    /// Returns `fmt::Error` when the sink refuses a write.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — both settlement states, distinct residual counts,
    ///   every alignment/payload fault, and owed, refused and checked source
    ///   declarations. Required semantic fields and exact sink refusals
    ///   distinguish erased metadata and swallowed failures without fixing
    ///   sentences.
    /// - witness: `settle::tests::settlement_formatters_retain_fields_and_sink_refusals`
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
/// payloads out of `arena` and asking `runner` for each run outcome stated.
///
/// # Specification
/// - requires: `runner` supplies the toolchain outcome for each requested
///   accepted declaration. The caller owns source provenance: module and
///   verdict identifiers are interpreted in the supplied arena; structural
///   checks do not establish arena or source identity.
/// - ensures: on success, one report per declaration in module order, retaining
///   its name, span and admission position. A lowering refusal consumes no
///   checker verdict; other declarations pair with the checker by admission
///   position. Root guards override produced verdicts without dropping their
///   owed obligations. Only accepted declarations stating a run outcome call
///   `runner`, once each in order; the report preserves the checker ledger
///   count.
/// - fails: `SettleFault` for the first missing or misaligned verdict, an
///   unreadable expectation payload, or a verdict left after the module ends.
///   Calls made to the runner before a later fault are not rolled back.
/// - panics: none for a conforming runner.
///
/// # Errors
/// [`SettleFault::MissingVerdict`], [`SettleFault::MisalignedVerdict`] and
/// [`SettleFault::SurplusVerdict`] when `verdicts` are not the module's own;
/// [`SettleFault::UnreadablePayload`] when `arena` does not hold an
/// expectation's payload.
///
/// # Adequacy
/// - hypothesis: L3 — aligned, missing, shifted and surplus checker reports;
///   unreadable payloads; a lowering refusal before checked names; strict
///   guards retaining obligations; and accepted versus unaccepted run requests.
///   Exact records and typed fault positions distinguish pairing, precedence
///   and ledger errors. Callback positions are observed by the witnesses; the
///   postcondition never calls or replays the runner.
/// - witness: `settle::tests::verdicts_that_are_not_the_modules_own_are_refused`
/// - witness: `settle::tests::a_lowering_refused_declaration_consumes_no_verdict`
/// - witness: `settle::tests::the_strict_root_refuses_an_expectation_outside_the_fixture_root`
/// - witness: `settle::tests::a_run_outcome_settles_under_either_root`
/// - witness: `settle::tests::a_later_alignment_fault_does_not_replay_or_extend_runner_calls`
#[spec(
    ensures: |ret| match ret {
    Ok(ref report) => {
        report.root() == root && report.ledger() == verdicts.ledger().count()
            && report.declarations().len() == module.declarations().len()
            && report
                .declarations()
                .iter()
                .zip(module.declarations())
                .all(|(declaration, lowered)| {
                    declaration.name == lowered.name()
                        && declaration.span == lowered.span()
                        && declaration.constant == lowered.constant()
                        && match declaration.produced {
                            Produced::Guarded(
                                CorpusRefusal::ExpectationOutsideFixtureRoot { schema, .. },
                            ) => {
                                root == CorpusRoot::Strict
                                    && matches!(
                                        schema, expectation::ExpectationSchema::Owes |
                                        expectation::ExpectationSchema::Refuses
                                    ) && declaration.stated == expectation::owing_nothing()
                            }
                            Produced::Unlowered(refusal) => {
                                matches!(
                                    lowered.outcome(), DeclarationOutcome::Refused(expected) if
                                    expected == refusal
                                ) && usize::from(declaration.owed) == 0_usize
                            }
                            Produced::Judged(_) => {
                                !matches!(lowered.outcome(), DeclarationOutcome::Refused(_))
                            }
                        }
                        && match declaration.ran {
                            Maybe::Present(_) => {
                                matches!(
                                    declaration.stated, Stated::Verdict(Outcome::Runs(_))
                                )
                                    && matches!(
                                        declaration.produced, Produced::Judged(Verdict::Checked { ..
                                        } | Verdict::Synthesised { .. })
                                    )
                            }
                            Maybe::Absent(ran::Absent::Unaccepted) => {
                                matches!(
                                    declaration.stated, Stated::Verdict(Outcome::Runs(_))
                                )
                                    && !matches!(
                                        declaration.produced, Produced::Judged(Verdict::Checked { ..
                                        } | Verdict::Synthesised { .. })
                                    )
                            }
                            Maybe::Absent(ran::Absent::Unstated) => {
                                !matches!(
                                    declaration.stated, Stated::Verdict(Outcome::Runs(_))
                                )
                            }
                        }
                })
            && module
                .declarations()
                .iter()
                .filter(|lowered| {
                    !matches!(lowered.outcome(), DeclarationOutcome::Refused(_))
                })
                .count() == verdicts.judged().len()
            && report
                .declarations()
                .iter()
                .zip(module.declarations())
                .filter(|&(_, lowered)| {
                    !matches!(lowered.outcome(), DeclarationOutcome::Refused(_))
                })
                .zip(verdicts.judged())
                .all(|((declaration, lowered), answer)| {
                    lowered.constant() == answer.constant()
                        && usize::from(declaration.owed)
                            == usize::from(matches!(answer.verdict(), Verdict::Owed(_)))
                        && (declaration.produced == Produced::Judged(answer.verdict())
                            || matches!(declaration.produced, Produced::Guarded(_)))
                })
    }
    Err(SettleFault::MissingVerdict { constant }) => {
        module
            .declarations()
            .iter()
            .filter(|lowered| {
                !matches!(lowered.outcome(), DeclarationOutcome::Refused(_))
            })
            .nth(verdicts.judged().len())
            .is_some_and(|lowered| lowered.constant() == constant)
    }
    Err(SettleFault::MisalignedVerdict { declared, judged }) => {
        module
            .declarations()
            .iter()
            .filter(|lowered| {
                !matches!(lowered.outcome(), DeclarationOutcome::Refused(_))
            })
            .zip(verdicts.judged())
            .find(|&(lowered, answer)| lowered.constant() != answer.constant())
            .is_some_and(|(lowered, answer)| {
                lowered.constant() == declared && answer.constant() == judged
            })
    }
    Err(SettleFault::SurplusVerdict { constant }) => {
        verdicts
            .judged()
            .get(
                module
                    .declarations()
                    .iter()
                    .filter(|lowered| {
                        !matches!(lowered.outcome(), DeclarationOutcome::Refused(_))
                    })
                    .count(),
            )
            .is_some_and(|answer| answer.constant() == constant)
    }
    Err(SettleFault::UnreadablePayload { span }) => {
        module
            .declarations()
            .iter()
            .any(|lowered| {
                attributes(module.attributes(), lowered)
                    .any(|entry| entry.span() == span)
            })
    }
},
)]
#[inline]
pub fn settle<'source>(
    root: CorpusRoot,
    arena: &CoreArena,
    module: &LoweredModule<'source>,
    verdicts: &ModuleReport,
    runner: &mut dyn Runner,
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
                    | Verdict::Data
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
        let ran = match (&expectations.stated, produced) {
            | (
                &Stated::Verdict(Outcome::Runs(_)),
                Produced::Judged(Verdict::Checked { .. } | Verdict::Synthesised { .. }),
            ) => Maybe::Present(runner.run(lowered.constant())),
            | (
                &Stated::Verdict(Outcome::Runs(_)),
                Produced::Judged(Verdict::Data | Verdict::Owed(_) | Verdict::Refused(_))
                | Produced::Unlowered(_)
                | Produced::Guarded(_),
            ) => Maybe::Absent(ran::Absent::Unaccepted),
            | (
                &Stated::Verdict(Outcome::Checks(_) | Outcome::Refuses(_)) | &Stated::Malformed(_),
                _,
            ) => Maybe::Absent(ran::Absent::Unstated),
        };
        declarations.push(DeclarationReport {
            name: lowered.name(),
            span: lowered.span(),
            constant: lowered.constant(),
            membership: expectations.membership,
            stated: expectations.stated,
            produced,
            owed,
            ran,
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
/// then the definition's; a form that wrote both halves, a signed function
/// tail, has its attributes read once.
///
/// # Specification
/// - requires: nothing; a declaration half with no table entry contributes no
///   attributes.
/// - ensures: yields the signature’s entries followed by the definition’s
///   entries in their stored order, but reads a shared signature/definition
///   origin only once.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — separate signature and definition expectations produce a
///   conflict with ordered spans; a single attributed signed function settles
///   without a duplicated expectation; an unattributed declaration has no
///   entries. The predicate traverses a cheap clone of the private iterator,
///   leaving the returned iterator unconsumed.
/// - witness: `settle::tests::a_name_carrying_two_expectations_states_none`
/// - witness: `settle::tests::a_wrong_stated_verdict_is_unsettled_either_way`
#[spec(
    ensures: |ret| {
    let signature = lowered.signature();
    let definition = lowered.definition();
    let first = match signature {
        Maybe::Present(digest) => table.entries(digest),
        Maybe::Absent(_) => &[],
    };
    let second = if signature == definition {
        &[][..]
    } else {
        match definition {
            Maybe::Present(digest) => table.entries(digest),
            Maybe::Absent(_) => &[],
        }
    };
    ret.clone().eq(first.iter().chain(second.iter()))
},
)]
fn attributes<'table>(
    table: &'table AttributeTable,
    lowered: &LoweredDeclaration<'_>,
) -> core::iter::Chain<
    core::slice::Iter<'table, AttributeEntry>,
    core::slice::Iter<'table, AttributeEntry>,
>
{
    let signature = lowered.signature();
    let definition = lowered.definition();
    let first = match signature {
        | Maybe::Present(digest) => table.entries(digest),
        | Maybe::Absent(_) => &[],
    };
    let second = if signature == definition {
        &[][..]
    }
    else {
        match definition {
            | Maybe::Present(digest) => table.entries(digest),
            | Maybe::Absent(_) => &[],
        }
    };
    first.iter().chain(second.iter())
}

#[cfg(test)]
mod tests
{
    use alloc::collections::BTreeSet;
    use alloc::format;
    use alloc::string::ToString as _;
    use alloc::vec::Vec;
    use core::fmt;

    use anodized::spec;
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
    use crate::fixture::RefusingWriter;
    use crate::fixture::checked;
    use crate::fixture::ran_at;
    use crate::fixture::settled;
    use crate::fixture::span;
    use crate::refusal::CorpusRefusal;
    use crate::refusal::RefusalName;
    use crate::report::SettleReport;
    use crate::root::CorpusRoot;
    use crate::run::RunSpelling;

    /// The one declaration `report` holds.
    ///
    /// # Specification
    /// - requires: the fixture report contains exactly one declaration.
    /// - ensures: returns that declaration by reference.
    /// - panics: when the fixture violates the one-declaration premise.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the same-suite single-declaration source fixtures
    ///   observe exact stated verdicts, refusals, counts and spans through the
    ///   borrowed declaration. The predicate states cardinality and reference
    ///   identity; invalid fixture shapes are outside its domain.
    /// - witness: `settle::tests::a_wrong_stated_verdict_is_unsettled_either_way`
    /// - witness: `settle::tests::the_strict_root_refuses_an_expectation_outside_the_fixture_root`
    #[spec(
        requires: report.declarations().len() == 1_usize,
        ensures: |ret| {
    report
        .declarations()
        .first()
        .is_some_and(|first| core::ptr::eq(
            core::ptr::from_ref(ret),
            core::ptr::from_ref(first),
        ))
},
    )]
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
            &Stated::Malformed(ExpectationFault::UnknownRefusal { span: at(3, 29) }),
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
                r#"@[ checks ] def f(x: Integer) -> -F Integer { ret x }"#,
                Settlement::Settled,
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
                &stated,
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
            &owing_nothing(),
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
    fn a_run_outcome_settles_under_either_root()
    {
        let ran = |position: &str| Outcome::Runs(RunSpelling::from(format!("ran at {position}")));
        let rows = [
            (
                CorpusRoot::Strict,
                r#"@[ runs("ran at 0") ] def a = 3 ;"#,
                ran("0"),
                Settlement::Settled,
            ),
            (
                CorpusRoot::Fixture,
                r#"@[ runs("ran at 0") ] def a = 3 ;"#,
                ran("0"),
                Settlement::Settled,
            ),
            (
                CorpusRoot::Fixture,
                r#"@[ runs("ran at 1") ] def a = 3 ;"#,
                ran("0"),
                Settlement::Unsettled,
            ),
            (
                CorpusRoot::Fixture,
                r#"@[ runs("ran at 0") ] def a : Integer ;"#,
                Outcome::Checks(ObligationCount::from(1_usize)),
                Settlement::Unsettled,
            ),
            (
                CorpusRoot::Fixture,
                r#"@[ runs("ran at 0") ] def a : Integer ; def a = "three" ;"#,
                Outcome::Refuses(RefusalName::TypeMismatch),
                Settlement::Unsettled,
            ),
            (
                CorpusRoot::Strict,
                r#"@[ runs("ran at 0"), owes(1) ] def a : Integer ;"#,
                Outcome::Refuses(RefusalName::ExpectationOutsideFixtureRoot),
                Settlement::Unsettled,
            ),
            (
                CorpusRoot::Fixture,
                r#"@[ checks, runs("ran at 0") ] def a = 3 ;"#,
                Outcome::Checks(ObligationCount::from(0_usize)),
                Settlement::Unsettled,
            ),
        ];
        for (root, source, outcome, settlement) in rows {
            let report = settled(root, SourceText::from(source));
            assert_eq!(
                (only(&report).outcome(), only(&report).settlement()),
                (outcome, settlement),
                "`{source}` under the {root} root produces and settles as pinned"
            );
        }

        let module = checked(SourceText::from(
            r#"def a : Integer ; @[ runs("ran at 1") ] def b = 3 ; @[ runs("ran at 2") ] def c : Integer ; @[ checks ] def d = 4 ; @[ runs("ran at 4") ] def e : Integer ; def e = "four" ;"#,
        ));
        let mut asked = Vec::new();
        let mut runner = |constant: ConstantIndex| {
            asked.push(usize::from(constant));
            ran_at(constant)
        };
        let report = settle(
            CorpusRoot::Fixture,
            &module.arena,
            &module.module,
            &module.verdicts,
            &mut runner,
        )
        .expect("the verdicts are the module's own");
        assert_eq!(
            asked,
            [1_usize],
            "only the accepted declaration stating a run outcome is run"
        );
        assert_eq!(
            report.declarations().len(),
            5_usize,
            "every name is reported, run or not"
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
                r#"@[ refuses("OutOfFragment") ] def a : -F Integer & -F Integer ;"#,
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
                r#"@[ refuses("ShapeMismatch") ] def a : +U (Integer -> -F Integer) ; def a = thunk { ret 3 } ;"#,
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
    fn a_later_alignment_fault_does_not_replay_or_extend_runner_calls()
    {
        let all = checked(SourceText::from(
            r#"@[ runs("ran at 0") ] def a = 3 ; @[ runs("ran at 1") ] def b = 4 ;"#,
        ));
        let one = checked(SourceText::from(r#"@[ runs("ran at 0") ] def a = 3 ;"#));
        let shifted = checked(SourceText::from("def a = absent ; def b = 4 ;"));
        let zero = ConstantIndex::from(0_usize);
        let one_position = ConstantIndex::from(1_usize);
        for (module, verdicts, fault, expected_calls) in [
            (
                &all,
                &one.verdicts,
                SettleFault::MissingVerdict {
                    constant: one_position,
                },
                &[zero][..],
            ),
            (
                &one,
                &all.verdicts,
                SettleFault::SurplusVerdict {
                    constant: one_position,
                },
                &[zero][..],
            ),
            (
                &all,
                &shifted.verdicts,
                SettleFault::MisalignedVerdict {
                    declared: zero,
                    judged: one_position,
                },
                &[][..],
            ),
        ] {
            let mut calls = Vec::new();
            let mut runner = |constant| {
                calls.push(constant);
                ran_at(constant)
            };
            let result = settle(
                CorpusRoot::Fixture,
                &module.arena,
                &module.module,
                verdicts,
                &mut runner,
            );
            assert_eq!(result, Err(fault));
            assert_eq!(
                calls, expected_calls,
                "failed settlement must neither replay earlier work nor run later declarations"
            );
        }
    }

    #[test]
    fn settlement_formatters_retain_fields_and_sink_refusals()
    {
        assert_ne!(
            Settlement::Settled.to_string(),
            Settlement::Unsettled.to_string()
        );
        for settlement in [Settlement::Settled, Settlement::Unsettled] {
            assert_eq!(
                fmt::Write::write_fmt(&mut RefusingWriter, format_args!("{settlement}")),
                Err(fmt::Error)
            );
        }
        let residual = Surviving::new(
            ObligationCount::from(17_usize),
            ObligationCount::from(29_usize),
        );
        let rendered = residual.to_string();
        assert!(rendered.contains("17") && rendered.contains("29"));
        assert_eq!(
            fmt::Write::write_fmt(&mut RefusingWriter, format_args!("{residual}")),
            Err(fmt::Error)
        );
        let at = span(ByteOffset::from(43_usize), ByteOffset::from(61_usize));
        let at_spelled = at.to_string();
        let mut distinct = BTreeSet::new();
        for (fault, payloads) in [
            (
                SettleFault::MissingVerdict {
                    constant: ConstantIndex::from(17_usize),
                },
                &["17"][..],
            ),
            (
                SettleFault::MisalignedVerdict {
                    declared: ConstantIndex::from(17_usize),
                    judged: ConstantIndex::from(29_usize),
                },
                &["17", "29"][..],
            ),
            (
                SettleFault::SurplusVerdict {
                    constant: ConstantIndex::from(17_usize),
                },
                &["17"][..],
            ),
            (
                SettleFault::UnreadablePayload { span: at },
                &[at_spelled.as_str()][..],
            ),
        ] {
            let rendered = fault.to_string();
            for payload in payloads {
                assert!(rendered.contains(payload));
            }
            assert!(
                distinct.insert(rendered),
                "distinct faults remain distinguishable"
            );
            assert_eq!(
                fmt::Write::write_fmt(&mut RefusingWriter, format_args!("{fault}")),
                Err(fmt::Error)
            );
        }
        for source in [
            "@[ owes(17) ] def owing_record : Integer ;",
            r#"@[ refuses("UnresolvedName") ] def refused_record = absent_record ;"#,
            "def unmarked_record = 3 ;",
        ] {
            let report = settled(CorpusRoot::Fixture, SourceText::from(source));
            let declaration = only(&report);
            let rendered = declaration.to_string();
            assert!(rendered.contains(declaration.name().as_ref()));
            assert!(rendered.contains(&declaration.span().to_string()));
            assert!(rendered.contains(&declaration.stated().to_string()));
            assert!(rendered.contains(&declaration.outcome().to_string()));
            if let Maybe::Present(refusal) = declaration.produced().refusal() {
                assert!(rendered.contains(&refusal.classify().to_string()));
            }
            if declaration.surviving() != Surviving::default() {
                assert!(rendered.contains(&declaration.surviving().to_string()));
            }
            assert_eq!(
                fmt::Write::write_fmt(&mut RefusingWriter, format_args!("{declaration}")),
                Err(fmt::Error)
            );
        }
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
                settle(
                    CorpusRoot::Fixture,
                    &two.arena,
                    &two.module,
                    &one.verdicts,
                    &mut ran_at,
                ),
                SettleFault::MissingVerdict {
                    constant: ConstantIndex::from(1_usize),
                },
            ),
            (
                settle(
                    CorpusRoot::Fixture,
                    &one.arena,
                    &one.module,
                    &two.verdicts,
                    &mut ran_at,
                ),
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
                    &mut ran_at,
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
                    &mut ran_at,
                ),
                SettleFault::UnreadablePayload { span: at(3, 10) },
            ),
        ];

        for (result, fault) in rows {
            assert_eq!(result, Err(fault), "the mismatch is refused: {fault}");
        }
        for own in [&two, &one, &shifted, &owed] {
            assert!(
                settle(
                    CorpusRoot::Fixture,
                    &own.arena,
                    &own.module,
                    &own.verdicts,
                    &mut ran_at,
                )
                .is_ok(),
                "a module's own verdicts and arena settle"
            );
        }
    }
}
