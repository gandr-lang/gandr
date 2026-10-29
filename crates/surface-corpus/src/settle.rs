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
//! The checker judges the declarations a driver hands it — every declaration
//! the lowering did not refuse, in admission order — and returns one verdict
//! for each, in the same order. `settle` walks the module's declarations in
//! that order, pairs each unrefused declaration with the next verdict, and
//! checks the pairing by admission position: a verdict missing, a verdict for
//! another position, or a verdict left over is `SettleFault`, a caller fault
//! rather than a verdict, as is a payload the arena given does not hold. A
//! declaration's own obligations are read off its verdict — one for an owed
//! verdict, one per blocker for a suspended one, none otherwise — because the
//! checker records exactly one ledger entry per owed verdict and a suspension
//! per suspended one; the run's ledger size is read off the ledger.
//!
//! The alternative was pairing by origin token, which the driver issues and
//! could issue in any scheme; the admission position is the one index both the
//! lowering and the checker define. The choice reverses if the checker ever
//! returns verdicts out of admission order, at which point the pairing becomes
//! a lookup by position.
//!
//! # A declaration's own obligations
//!
//! A declaration produces one obligation when its verdict is owed, one per
//! hole it waits on when its verdict is suspended, and none otherwise: the
//! checker records exactly one ledger entry per owed verdict and the blockers
//! of each suspension, so the count is read off the verdict, and the ledger
//! size off the ledger.
//!
//! # One predicate: settled
//!
//! A declaration is settled when the verdict it produced equals the verdict it
//! states. A verdict is one of three shapes: _checks, owing n_ — checked,
//! synthesised, owed or suspended, with n the obligations its verdict left in
//! the ledger, the holes a suspension waits on, or for a fold the owed laws it
//! rests on — _runs to_ a spelled value, or
//! _refuses_ a named refusal. `checks` states _checks, owing 0_; `owes(n)`
//! states _checks, owing n_; `runs("spelling")` states _runs to_ the spelling;
//! `refuses("Name")` states the named refusal; a declaration carrying none of
//! the four states _checks, owing 0_. A run is settled when every declaration
//! in it is, which is the predicate a corpus run is gated on.
//!
//! An obligation survives when it is unsettled, in either direction: produced
//! with nothing declaring it (an unannotated hole), or declared with nothing
//! producing it (an `owes` on a declaration that completes). Each declaration
//! reports both counts and the tally sums them. A wrong stated verdict
//! therefore fails both ways: a refusal stated and not produced, a refusal
//! produced and not stated, another refusal produced than the one stated, more
//! obligations than stated and fewer.
//!
//! The alternative was a pass/fail bit per fixture with the obligation count as
//! an informative extra; it lets an `owes(2)` over a single hole pass. The
//! choice reverses if an expectation needs a looser relation than equality — an
//! obligation count bounded rather than exact — which would arrive as a fifth
//! schema rather than a change to this one.

use alloc::format;
use alloc::string::String;
use alloc::string::ToString as _;
use alloc::vec::Vec;
use core::error::Error;
use core::fmt;

use anodized::spec;
use gandr_core_checker::Judged;
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
use gandr_surface_lowering::RegisteredAttribute;
use gandr_surface_lowering::Role;
use gandr_surface_lowering::SurfaceName;
use gandr_surface_lowering::UnitKey;
use gandr_surface_lowering::coincide::CallText;
use gandr_surface_syntax::ByteSpan;
use quenchant_shape::shape::Maybe;

use crate::expectation;
use crate::expectation::Expectations;
use crate::expectation::Membership;
use crate::expectation::Outcome;
use crate::expectation::Stated;
use crate::expectation::reads_as_stated;
use crate::expectation::web_as_stated;
use crate::refusal::CorpusRefusal;
use crate::refusal::Refusal;
use crate::report::SettleReport;
use crate::root::CorpusRoot;
use crate::root::Rooted;
use crate::run::Channel;
use crate::run::RunSpelling;
use crate::run::Runner;
use crate::run::TracedRun;

/// How a stated channel the run never forked reads.
const UNPLAYED: &str = "unplayed";

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
    /// Why a declaration carries no run outcome or normal form.
    pub mod ran {
        /// The declaration was not run, and no call was read under it.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// It states no run outcome or normal form, so nothing asked for
            /// one.
            Unstated,
            /// It states one, but was refused, owes its body, or is not of
            /// the verdict that has one, so there is nothing to run or read.
            Unaccepted,
            /// It states a run beside a refusal, but the checker did not
            /// refuse it: it checked, owes, or the lowering or the root refused
            /// it first, so there is no checker-refused body to run.
            Unrefused,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a declaration names no admission.
    pub mod admitted {
        /// The declaration is no law the host admits.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// It is no admitted law, or the admission did not cross as the
            /// owed axiom it is.
            Unadmitted,
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
            Self::Settled => "settled",
            Self::Unsettled => "unsettled",
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
    /// This crate refused the declaration, and the refusal stands in place of
    /// whatever it produced: the root, an expectation it carries; or a
    /// boundary check's run, the clause the block's members break.
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
        Verdict::Data | Verdict::Synthesised { .. } | Verdict::Owed(_) | Verdict::Suspended(_)),
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
            Self::Judged(Verdict::Refused(refusal)) => Maybe::Present(Refusal::Checking(refusal)),
            Self::Judged(
                Verdict::Data
                | Verdict::Checked { .. }
                | Verdict::Synthesised { .. }
                | Verdict::Owed(_)
                | Verdict::Suspended(_),
            ) => Maybe::Absent(produced_refusal::Absent::Unrefused),
            Self::Unlowered(refusal) => Maybe::Present(Refusal::Lowering(refusal)),
            Self::Guarded(refusal) => Maybe::Present(Refusal::Corpus(refusal)),
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
///   position, stated and produced outcomes, owed obligations, the requested
///   run outcome and the path of a law the host admits.
/// - panics: none.
/// - executable: none — The record has no module, original attributes or
///   checker report; `settle` and the report’s comparison methods carry the
///   executable relationships.
///
/// # Adequacy
/// - hypothesis: L3 — matched and mismatched source expectations, missing or
///   shifted verdicts, guarded and run-producing declarations, and an admitted
///   law. Exact classifications, identities, counts and fault positions
///   distinguish lost or swapped fields at their consuming boundaries.
/// - witness: `settle::tests::a_lowering_refused_declaration_consumes_no_verdict`
/// - witness: `settle::tests::a_run_outcome_settles_under_either_root`
/// - witness: `settle::tests::the_strict_root_refuses_an_expectation_outside_the_fixture_root`
/// - witness: `settle::tests::an_admitted_law_settles_as_checks_and_lists_its_admission_2356`
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
    /// The owed holes a suspended verdict waits on, by name, in admission
    /// order; empty for every other verdict.
    waits: Vec<SurfaceName<'source>>,
    /// The outcome its run produced, or the line its block's normal form
    /// produced, when it states one and was accepted.
    ran: Maybe<RunSpelling, ran::Absent>,
    /// Each channel its `traces` entries state, as its traced run played it
    /// ([`played`]); empty unless it states its run's channels and was
    /// accepted.
    traced: Vec<Channel>,
    /// The structured name of the law, when the declaration is one its module
    /// admits at a primitive carrier and it crossed as the axiom it is: the
    /// audit row the report lists in place of an obligation.
    admitted: Maybe<Vec<SurfaceName<'source>>, admitted::Absent>,
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

    /// The same report with its declaration at `span`: the bytes a face
    /// measures from the start of the file it names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn at(
        &self,
        span: ByteSpan,
    ) -> Self
    {
        Self {
            span,
            ..self.clone()
        }
    }

    /// The structured name of the law the declaration admits, when it is one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn admitted(&self) -> &Maybe<Vec<SurfaceName<'source>>, admitted::Absent>
    {
        &self.admitted
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

    /// The owed holes the name's suspended verdict waits on, by name, in
    /// admission order; empty unless the verdict is suspended.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn waits(&self) -> &[SurfaceName<'source>]
    {
        &self.waits
    }

    /// The produced verdict, read in the stated verdict's shape.
    ///
    /// # Specification
    /// - ensures: the produced refusal's name when one was produced, beside the
    ///   run's spelling when a run beside the refusal is stated and was run;
    ///   else the outcome its run or its normal form produced, in the stated
    ///   schema, when it states one and was accepted, a web read as its prime
    ///   count when the stated one is a count, and each stated channel as the
    ///   run played it ([`played`]); else checks owing the declaration's own
    ///   obligations.
    /// - provides: the side the settle comparison holds the stated verdict
    ///   against.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — checked, owed, refused, guarded and requested-run
    ///   declarations beside mismatching expectations, and a refused one run
    ///   beside its refusal. Exact outcome variants, counts and text
    ///   distinguish changed precedence, erased obligations and altered run
    ///   spelling; the predicate borrows text rather than cloning a second
    ///   outcome.
    /// - witness: `settle::tests::a_wrong_stated_verdict_is_unsettled_either_way`
    /// - witness: `settle::tests::a_run_outcome_settles_under_either_root`
    /// - witness: `settle::tests::the_strict_root_refuses_an_expectation_outside_the_fixture_root`
    /// - witness: `settle::tests::a_run_beside_a_refusal_settles_only_when_both_hold`
    /// - witness: `settle::tests::a_channel_settles_against_the_web_its_play_decomposes_to_3338`
    #[spec(
        ensures: |ret| match self.produced.refusal() {
    Maybe::Present(refusal) => match (&self.stated, &self.ran) {
        (&Stated::Verdict(Outcome::RefusesRunning(..)), &Maybe::Present(ref spelled)) => {
            matches!(ret, Outcome::RefusesRunning(name, ref actual) if name == refusal.name() && actual == spelled)
        }
        (&Stated::Verdict(Outcome::RefusesRunning(..)), &Maybe::Absent(_))
        | (&(Stated::Verdict(Outcome::Checks(_) | Outcome::Refuses(_) | Outcome::Runs(_) | Outcome::Normalizes(_) | Outcome::Decomposes(_) | Outcome::RunsTracing(..) | Outcome::Reads(_)) | Stated::Malformed(_)), _) => {
            ret == Outcome::Refuses(refusal.name())
        }
    },
    Maybe::Absent(produced_refusal::Absent::Unrefused) => {
        match self.ran {
            Maybe::Present(ref spelled) => match self.stated {
                Stated::Verdict(Outcome::Normalizes(_)) => {
                    matches!(ret, Outcome::Normalizes(ref actual) if actual == spelled)
                }
                Stated::Verdict(Outcome::Decomposes(ref stated)) => {
                    matches!(ret, Outcome::Decomposes(ref actual) if *actual == web_as_stated(stated, spelled))
                }
                Stated::Verdict(Outcome::Reads(ref stated)) => {
                    matches!(ret, Outcome::Reads(ref actual) if *actual == reads_as_stated(stated, spelled))
                }
                Stated::Verdict(Outcome::RunsTracing(..)) => {
                    matches!(ret, Outcome::RunsTracing(ref actual, ref channels) if actual == spelled && channels_settle(channels, &self.traced) == Settlement::Settled)
                }
                Stated::Verdict(_) | Stated::Malformed(_) => matches!(ret, Outcome::Runs(ref actual) if actual == spelled),
            },
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
            (Maybe::Present(refusal), &Maybe::Present(ref spelled))
                if matches!(self.stated, Stated::Verdict(Outcome::RefusesRunning(..))) =>
            {
                Outcome::RefusesRunning(refusal.name(), spelled.clone())
            },
            (Maybe::Present(refusal), _) => Outcome::Refuses(refusal.name()),
            (Maybe::Absent(produced_refusal::Absent::Unrefused), &Maybe::Present(ref spelled)) => {
                match self.stated {
                    Stated::Verdict(Outcome::Normalizes(_)) => Outcome::Normalizes(spelled.clone()),
                    Stated::Verdict(Outcome::Decomposes(ref stated)) => {
                        Outcome::Decomposes(web_as_stated(stated, spelled))
                    },
                    Stated::Verdict(Outcome::Reads(ref stated)) => {
                        Outcome::Reads(reads_as_stated(stated, spelled))
                    },
                    Stated::Verdict(Outcome::RunsTracing(..)) => {
                        Outcome::RunsTracing(spelled.clone(), self.traced.clone())
                    },
                    Stated::Verdict(
                        Outcome::Checks(_)
                        | Outcome::Refuses(_)
                        | Outcome::Runs(_)
                        | Outcome::RefusesRunning(..),
                    )
                    | Stated::Malformed(_) => Outcome::Runs(spelled.clone()),
                }
            },
            (Maybe::Absent(produced_refusal::Absent::Unrefused), &Maybe::Absent(_)) => {
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
    ///   compares borrowed text without another allocation, but for a web read
    ///   as the prime count a stated count names.
    /// - witness: `settle::tests::a_wrong_stated_verdict_is_unsettled_either_way`
    /// - witness: `settle::tests::a_refusal_outside_the_vocabulary_fails_the_fixture`
    /// - witness: `settle::tests::a_name_carrying_two_expectations_states_none`
    /// - witness: `settle::tests::a_run_outcome_settles_under_either_root`
    /// - witness: `settle::tests::a_run_beside_a_refusal_settles_only_when_both_hold`
    /// - witness: `settle::tests::a_channel_settles_against_the_web_its_play_decomposes_to_3338`
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
            Stated::Verdict(Outcome::Runs(ref expected) | Outcome::Normalizes(ref expected)) => {
                matches!(self.produced.refusal(), Maybe::Absent(_))
                    && matches!(
                        self.ran, Maybe::Present(ref actual) if actual == expected
                    )
            }
            Stated::Verdict(Outcome::Decomposes(ref expected)) => {
                matches!(self.produced.refusal(), Maybe::Absent(_))
                    && matches!(
                        self.ran, Maybe::Present(ref actual) if web_as_stated(expected, actual) == *expected
                    )
            }
            Stated::Verdict(Outcome::Reads(ref expected)) => {
                matches!(self.produced.refusal(), Maybe::Absent(_))
                    && matches!(
                        self.ran, Maybe::Present(ref actual) if reads_as_stated(expected, actual) == *expected
                    )
            }
            Stated::Verdict(Outcome::RefusesRunning(name, ref expected)) => {
                matches!(self.produced.refusal(), Maybe::Present(refusal) if refusal.name() == name)
                    && matches!(self.ran, Maybe::Present(ref actual) if actual == expected)
            }
            Stated::Verdict(Outcome::RunsTracing(ref expected, ref stated)) => {
                matches!(self.produced.refusal(), Maybe::Absent(_))
                    && matches!(self.ran, Maybe::Present(ref actual) if actual == expected)
                    && channels_settle(&self.traced, stated) == Settlement::Settled
            }
        }
},
    )]
    #[inline]
    #[must_use]
    pub fn settlement(&self) -> Settlement
    {
        let agrees = match self.stated {
            Stated::Malformed(_) => false,
            Stated::Verdict(Outcome::Refuses(name)) => matches!(
                self.produced.refusal(),
                Maybe::Present(refusal) if refusal.name() == name
            ),
            Stated::Verdict(Outcome::Checks(count)) => {
                matches!(self.produced.refusal(), Maybe::Absent(_))
                    && matches!(self.ran, Maybe::Absent(_))
                    && count == self.owed
            },
            Stated::Verdict(Outcome::Runs(ref expected) | Outcome::Normalizes(ref expected)) => {
                matches!(self.produced.refusal(), Maybe::Absent(_))
                    && matches!(self.ran, Maybe::Present(ref actual) if actual == expected)
            },
            Stated::Verdict(Outcome::Decomposes(ref expected)) => {
                matches!(self.produced.refusal(), Maybe::Absent(_))
                    && matches!(self.ran, Maybe::Present(ref actual) if web_as_stated(expected, actual) == *expected)
            },
            Stated::Verdict(Outcome::Reads(ref expected)) => {
                matches!(self.produced.refusal(), Maybe::Absent(_))
                    && matches!(self.ran, Maybe::Present(ref actual) if reads_as_stated(expected, actual) == *expected)
            },
            Stated::Verdict(Outcome::RefusesRunning(name, ref expected)) => {
                matches!(self.produced.refusal(), Maybe::Present(refusal) if refusal.name() == name)
                    && matches!(self.ran, Maybe::Present(ref actual) if actual == expected)
            },
            Stated::Verdict(Outcome::RunsTracing(ref expected, ref stated)) => {
                matches!(self.produced.refusal(), Maybe::Absent(_))
                    && matches!(self.ran, Maybe::Present(ref actual) if actual == expected)
                    && channels_settle(&self.traced, stated) == Settlement::Settled
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
    ///   and zero for a stated refusal, a stated run outcome, normal form,
    ///   decomposition or run with its channels, a run beside a refusal, or a
    ///   malformed expectation, the owed obligations past `declared` are
    ///   undeclared and the declared ones past the owed are unproduced; at most
    ///   one of the two is nonzero.
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
        Stated::Verdict(_) | Stated::Malformed(_) => 0_usize,
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
            Stated::Verdict(Outcome::Checks(declared)) => usize::from(declared),
            Stated::Verdict(
                Outcome::Refuses(_)
                | Outcome::Runs(_)
                | Outcome::Normalizes(_)
                | Outcome::Decomposes(_)
                | Outcome::RefusesRunning(..)
                | Outcome::RunsTracing(..)
                | Outcome::Reads(_),
            )
            | Stated::Malformed(_) => 0_usize,
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
    /// states, what it produced with the refusal's class, the obligations
    /// that survive when any do, and the audit row of a law the host admits.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the declaration’s settlement, name, span, stated and
    ///   produced outcomes, refusal class when present, nonzero residual
    ///   obligations, and `audit: M.law admitted` for an admitted law.
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
    /// - witness: `settle::tests::an_admitted_law_settles_as_checks_and_lists_its_admission_2356`
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
        let mut waits = self.waits.iter();
        if let Some(first) = waits.next() {
            write!(f, "; waits on `{first}`")?;
            for hole in waits {
                write!(f, ", `{hole}`")?;
            }
        }
        if let Maybe::Present(refusal) = self.produced.refusal() {
            write!(f, " ({})", refusal.classify())?;
        }
        let surviving = self.surviving();
        if surviving != Surviving::default() {
            write!(f, "; surviving obligations: {surviving}")?;
        }
        if let Maybe::Present(ref path) = self.admitted {
            f.write_str("; audit: ")?;
            let mut segments = path.iter();
            if let Some(first) = segments.next() {
                write!(f, "{first}")?;
            }
            for segment in segments {
                write!(f, ".{segment}")?;
            }
            f.write_str(" admitted")?;
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
            Self::MissingVerdict { constant } => write!(
                f,
                "no verdict answers the declaration at admission position {}",
                usize::from(constant)
            ),
            Self::MisalignedVerdict { declared, judged } => write!(
                f,
                "the verdict for admission position {} stands where position {} is due",
                usize::from(judged),
                usize::from(declared)
            ),
            Self::SurplusVerdict { constant } => write!(
                f,
                "the verdict for admission position {} answers no declaration of the module",
                usize::from(constant)
            ),
            Self::UnreadablePayload { span } => write!(
                f,
                "the payload of the attribute at {span} is not its schema's literal in the arena given"
            ),
        }
    }
}

impl Error for SettleFault
{
}

/// Settle `verdicts` against `module`, each declaration under the root
/// `roots` names for where its bytes start.
///
/// Expectation payloads are read out of `arena`, `runner` is asked for each
/// run outcome stated, and each normal form stated is read under its block's
/// rules.
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
///   owed obligations. An accepted declaration carrying `boundary` calls
///   `runner`'s run, and a clause the run names stands in place of its verdict.
///   Only accepted declarations stating a run outcome, a web or a run with its
///   channels call `runner`'s run, its decomposition or its traced run, and
///   only checker-refused declarations stating a run beside their refusal call
///   its refused run, once each in order; a report holds played channels only
///   for a traced run; only accepted declarations stating a normal form read
///   one, through [`LoweredModule::normal_form`], under the rules of the block
///   that holds them; an admitted law the checker owes is owed nothing; the
///   report preserves the checker ledger count.
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
/// - witness: `settle::tests::a_normal_form_settles_against_the_engines_reading`
/// - witness: `settle::tests::a_run_beside_a_refusal_settles_only_when_both_hold`
/// - witness: `settle::tests::a_web_settles_against_the_dialogue_s_decomposition_2077`
/// - witness: `settle::tests::an_admitted_law_settles_as_checks_and_lists_its_admission_2356`
/// - witness: `settle::tests::a_boundary_check_stands_as_its_run_answers_2901`
/// - witness: `settle::tests::a_channel_settles_against_the_web_its_play_decomposes_to_3338`
#[spec(
    ensures: |ret| match ret {
    Ok(ref report) => {
        report.ledger() == verdicts.ledger().count()
            && report.declarations().len() == module.declarations().iter().len()
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
                                roots.root_at(lowered.span().start()) == CorpusRoot::Strict
                                    && matches!(
                                        schema, expectation::ExpectationSchema::Owes |
                                        expectation::ExpectationSchema::Refuses
                                    ) && declaration.stated == expectation::owing_nothing()
                            }
                            Produced::Guarded(CorpusRefusal::BoundaryUnrealised { .. }) => {
                                !matches!(lowered.outcome(), DeclarationOutcome::Refused(_))
                                    && boundary_at(module.attributes(), lowered).is_some()
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
                                (matches!(
                                    declaration.stated, Stated::Verdict(Outcome::Runs(_) | Outcome::Decomposes(_) | Outcome::RunsTracing(..))
                                )
                                    && matches!(
                                        declaration.produced, Produced::Judged(Verdict::Checked { ..
                                        } | Verdict::Synthesised { .. })
                                    ))
                                    || (matches!(
                                        declaration.stated, Stated::Verdict(Outcome::Normalizes(_) | Outcome::Reads(_))
                                    ) && matches!(
                                        declaration.produced, Produced::Judged(Verdict::Data
                                        | Verdict::Checked { .. } | Verdict::Synthesised { .. })
                                    ))
                                    || (matches!(
                                        declaration.stated, Stated::Verdict(Outcome::RefusesRunning(..))
                                    ) && matches!(
                                        declaration.produced, Produced::Judged(Verdict::Refused(_))
                                    ))
                            }
                            Maybe::Absent(ran::Absent::Unaccepted) => {
                                (matches!(
                                    declaration.stated, Stated::Verdict(Outcome::Runs(_) | Outcome::Decomposes(_) | Outcome::RunsTracing(..))
                                )
                                    && !matches!(
                                        declaration.produced, Produced::Judged(Verdict::Checked { ..
                                        } | Verdict::Synthesised { .. })
                                    ))
                                    || (matches!(
                                        declaration.stated, Stated::Verdict(Outcome::Normalizes(_) | Outcome::Reads(_))
                                    ) && !matches!(
                                        declaration.produced, Produced::Judged(Verdict::Data
                                        | Verdict::Checked { .. } | Verdict::Synthesised { .. })
                                    ))
                            }
                            Maybe::Absent(ran::Absent::Unrefused) => {
                                matches!(
                                    declaration.stated, Stated::Verdict(Outcome::RefusesRunning(..))
                                ) && !matches!(
                                    declaration.produced, Produced::Judged(Verdict::Refused(_))
                                )
                            }
                            Maybe::Absent(ran::Absent::Unstated) => {
                                !matches!(
                                    declaration.stated, Stated::Verdict(Outcome::Runs(_) | Outcome::Normalizes(_) | Outcome::Decomposes(_) | Outcome::RefusesRunning(..) | Outcome::RunsTracing(..) | Outcome::Reads(_))
                                )
                            }
                        }
                        && (declaration.traced.is_empty()
                            || matches!(
                                (&declaration.stated, &declaration.ran),
                                (&Stated::Verdict(Outcome::RunsTracing(..)), &Maybe::Present(_))
                            ))
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
                        && (usize::from(declaration.owed) == usize::from(owed_by(verdicts, answer))
                            || (lowered.role() == Role::Admitted
                                && matches!(answer.verdict(), Verdict::Owed(_))
                                && usize::from(declaration.owed) == 0_usize))
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
                    .chain(header(module.attributes(), lowered))
                    .any(|entry| entry.span() == span)
            })
    }
},
)]
#[inline]
pub fn settle<'source, Roots>(
    roots: Roots,
    arena: &CoreArena,
    module: &LoweredModule<'source>,
    verdicts: &ModuleReport,
    runner: &mut dyn Runner,
) -> Result<SettleReport<'source>, SettleFault>
where
    Roots: Rooted + Copy,
{
    settle_after(roots, arena, module, verdicts, runner, &[])
}

/// [`settle`], the reports of `module`'s leading declarations given as
/// `earlier`: only the declarations after them are settled, and their reports
/// lead the report.
///
/// # Specification
/// - requires: as [`settle`]; `earlier` is the report [`settle`] answered under
///   `roots` for a module whose declarations lead `module`'s, its verdicts
///   leading `verdicts` and its arena one `arena` extends.
/// - ensures: what [`settle`] answers of `module`, `earlier` leading its
///   reports, the runner called only for the declarations after `earlier`'s.
/// - provides: a document's settlement at the cost of its own declarations.
/// - fails: as [`settle`], over the declarations after `earlier`'s.
/// - panics: none for a conforming runner.
///
/// # Errors
/// As [`settle`].
///
/// # Adequacy
/// - hypothesis: L3 — a module settled after its leading declarations' report
///   answers what settling it whole answers; a refused name an application
///   binds reads the application's attribute, and a refused declaration writing
///   its own halves keeps its own; a witness that checks beside its refused
///   function keeps the default.
/// - witness: `settle::tests::a_module_settled_after_its_leading_report_settles_as_a_whole_one_776`
/// - witness: `settle::tests::an_application_s_attribute_states_its_refused_names_1274`
/// - witness: `settle::tests::a_witness_that_checks_keeps_the_default_beside_its_refused_function_3706`
#[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|report|
    report.declarations().get(.. earlier.len()) == Some(earlier)))]
#[inline]
pub fn settle_after<'source, Roots>(
    roots: Roots,
    arena: &CoreArena,
    module: &LoweredModule<'source>,
    verdicts: &ModuleReport,
    runner: &mut dyn Runner,
    earlier: &[DeclarationReport<'source>],
) -> Result<SettleReport<'source>, SettleFault>
where
    Roots: Rooted + Copy,
{
    // The declarations the earlier report settled lead the module's, the
    // closure's; the rest are settled here.
    let mut later = module.declarations().iter();
    // A lowering refusal consumes no verdict.
    let consumed = later
        .by_ref()
        .take(earlier.len())
        .filter(|lowered| !matches!(lowered.outcome(), DeclarationOutcome::Refused(_)))
        .count();
    let mut judged = verdicts.judged().iter().skip(consumed);
    let mut declarations = Vec::with_capacity(module.declarations().iter().len());
    declarations.extend_from_slice(earlier);
    for lowered in later {
        let root = roots.root_at(lowered.span().start());
        let expectations = expected(root, arena, module, lowered)?;
        let (produced, owed) = match lowered.outcome() {
            DeclarationOutcome::Refused(refusal) => {
                (Produced::Unlowered(refusal), ObligationCount::from(0_usize))
            },
            DeclarationOutcome::Completed { .. }
            | DeclarationOutcome::Uncompleted { .. }
            | DeclarationOutcome::Bodied { .. }
            | DeclarationOutcome::Data(_)
            | DeclarationOutcome::Codata(_)
            | DeclarationOutcome::Abstract(_)
            | DeclarationOutcome::World => {
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
                (Produced::Judged(verdict), owed_by(verdicts, answer))
            },
        };
        // A name an application or a module's header binds writes no half:
        // when it is refused, the attributes before that form state its
        // expectation, and a witness that checks keeps the default. A witness
        // of a written signature reads its function's form, and when it
        // checks the function alone states that form's expectation.
        let expectations = match produced {
            Produced::Unlowered(_) | Produced::Judged(Verdict::Refused(_))
                if !header(module.attributes(), lowered).is_empty() =>
            {
                refused_expected(root, arena, module, lowered)?
            },
            Produced::Judged(Verdict::Checked { .. } | Verdict::Synthesised { .. })
                if expectations.membership == Membership::Fixture
                    && function_s_form(module, lowered).is_some() =>
            {
                Expectations::unattributed()
            },
            Produced::Unlowered(_)
            | Produced::Judged(
                Verdict::Data
                | Verdict::Checked { .. }
                | Verdict::Synthesised { .. }
                | Verdict::Owed(_)
                | Verdict::Suspended(_)
                | Verdict::Refused(_),
            )
            | Produced::Guarded(_) => expectations,
        };
        let produced = match expectations.guard {
            Maybe::Present(refusal) => Produced::Guarded(refusal),
            Maybe::Absent(expectation::guard::Absent::Admitted) => produced,
        };
        // A boundary check stands as its run answers: a clause its members
        // break refuses the block in place of the checker's verdict.
        let produced = match (boundary_at(module.attributes(), lowered), produced) {
            (
                Some(span),
                Produced::Judged(Verdict::Checked { .. } | Verdict::Synthesised { .. }),
            ) => match CorpusRefusal::unrealised(&runner.run(lowered.constant()), span) {
                Maybe::Present(refusal) => Produced::Guarded(refusal),
                Maybe::Absent(_) => produced,
            },
            (Some(_) | None, _) => produced,
        };
        let mut traced = Vec::new();
        let ran = match (&expectations.stated, produced) {
            (
                &Stated::Verdict(Outcome::RunsTracing(_, ref stated)),
                Produced::Judged(Verdict::Checked { .. } | Verdict::Synthesised { .. }),
            ) => {
                let TracedRun { run, channels } = runner.run_traced(lowered.constant());
                traced = played(stated, &channels);
                Maybe::Present(run)
            },
            (
                &Stated::Verdict(Outcome::Runs(_)),
                Produced::Judged(Verdict::Checked { .. } | Verdict::Synthesised { .. }),
            ) => Maybe::Present(runner.run(lowered.constant())),
            (
                &Stated::Verdict(Outcome::Decomposes(_)),
                Produced::Judged(Verdict::Checked { .. } | Verdict::Synthesised { .. }),
            ) => Maybe::Present(runner.decompose(lowered.constant())),
            (
                &Stated::Verdict(Outcome::RefusesRunning(..)),
                Produced::Judged(Verdict::Refused(_)),
            ) => Maybe::Present(runner.run_refused(lowered.constant())),
            (
                &Stated::Verdict(Outcome::RefusesRunning(..)),
                Produced::Judged(
                    Verdict::Data
                    | Verdict::Checked { .. }
                    | Verdict::Synthesised { .. }
                    | Verdict::Owed(_)
                    | Verdict::Suspended(_),
                )
                | Produced::Unlowered(_)
                | Produced::Guarded(_),
            ) => Maybe::Absent(ran::Absent::Unrefused),
            (
                &Stated::Verdict(Outcome::Normalizes(ref line)),
                Produced::Judged(
                    Verdict::Data | Verdict::Checked { .. } | Verdict::Synthesised { .. },
                ),
            ) => Maybe::Present(normalized(module, lowered, line)),
            (
                &Stated::Verdict(Outcome::Reads(_)),
                Produced::Judged(
                    Verdict::Data | Verdict::Checked { .. } | Verdict::Synthesised { .. },
                ),
            ) => Maybe::Present(runner.reads(lowered.constant())),
            (
                &Stated::Verdict(
                    Outcome::Runs(_) | Outcome::Decomposes(_) | Outcome::RunsTracing(..),
                ),
                Produced::Judged(
                    Verdict::Data | Verdict::Owed(_) | Verdict::Suspended(_) | Verdict::Refused(_),
                )
                | Produced::Unlowered(_)
                | Produced::Guarded(_),
            )
            | (
                &Stated::Verdict(Outcome::Normalizes(_) | Outcome::Reads(_)),
                Produced::Judged(Verdict::Owed(_) | Verdict::Suspended(_) | Verdict::Refused(_))
                | Produced::Unlowered(_)
                | Produced::Guarded(_),
            ) => Maybe::Absent(ran::Absent::Unaccepted),
            (
                &Stated::Verdict(Outcome::Checks(_) | Outcome::Refuses(_)) | &Stated::Malformed(_),
                _,
            ) => Maybe::Absent(ran::Absent::Unstated),
        };
        let waits = match produced {
            Produced::Judged(Verdict::Suspended(_)) => waits(module, verdicts, lowered.constant()),
            Produced::Judged(
                Verdict::Data
                | Verdict::Checked { .. }
                | Verdict::Synthesised { .. }
                | Verdict::Owed(_)
                | Verdict::Refused(_),
            )
            | Produced::Unlowered(_)
            | Produced::Guarded(_) => Vec::new(),
        };
        // A law the host admits crosses as the axiom it is: the audit lists
        // it in place of an obligation.
        let (owed, admitted) = match produced {
            Produced::Judged(Verdict::Owed(_)) if lowered.role() == Role::Admitted => (
                ObligationCount::from(0_usize),
                Maybe::Present(module.path_of(lowered)),
            ),
            Produced::Judged(
                Verdict::Data
                | Verdict::Checked { .. }
                | Verdict::Synthesised { .. }
                | Verdict::Owed(_)
                | Verdict::Suspended(_)
                | Verdict::Refused(_),
            )
            | Produced::Unlowered(_)
            | Produced::Guarded(_) => (owed, Maybe::Absent(admitted::Absent::Unadmitted)),
        };
        declarations.push(DeclarationReport {
            name: lowered.name(),
            span: lowered.span(),
            constant: lowered.constant(),
            membership: expectations.membership,
            stated: expectations.stated,
            produced,
            owed,
            waits,
            ran,
            traced,
            admitted,
        });
    }
    if let Some(surplus) = judged.next() {
        return Err(SettleFault::SurplusVerdict {
            constant: surplus.constant(),
        });
    }

    Ok(SettleReport::new(declarations, verdicts.ledger().count()))
}

/// The names of the owed holes the suspended declaration at `constant` waits
/// on, in admission order.
///
/// # Specification
/// - requires: `verdicts` judged `module`.
/// - ensures: one name per blocker of the suspension `verdicts` keeps at
///   `constant` that names a declaration of `module`, in admission order; empty
///   when it keeps none.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a declaration decoding an owed code hole names that hole,
///   and the same declaration after its hole is filled names none.
/// - witness: `settle::tests::a_suspended_declaration_owes_its_blockers`
#[spec(ensures: |ret| ret.len() <= verdicts.suspensions().get(&constant).map_or(0, |waiting| waiting.blockers().len()))]
fn waits<'source>(
    module: &LoweredModule<'source>,
    verdicts: &ModuleReport,
    constant: ConstantIndex,
) -> Vec<SurfaceName<'source>>
{
    let Some(waiting) = verdicts.suspensions().get(&constant)
    else {
        return Vec::new();
    };
    let declarations = module.declarations();
    waiting
        .blockers()
        .iter()
        .filter_map(
            |&hole| match declarations.search(&hole, LoweredDeclaration::constant) {
                Maybe::Present(declaration) => Some(declaration.name()),
                Maybe::Absent(_) => None,
            },
        )
        .collect()
}

/// The obligations `answer` owes: one for an owed declaration, one per
/// blocker for a suspended one, and for a checked fold one per law it rests
/// on that is itself owed. A fold's laws are its evidence, and a suspension's
/// blockers the holes its judgement waits on, so what they still owe is owed
/// by what rests on them; the ledger holds each hole's obligation once, under
/// the hole.
///
/// # Specification
/// - requires: `answer` is one of `verdicts`' judgements, whose constants
///   ascend in admission order.
/// - ensures: `1` for an owed verdict; for a suspended one, the number of holes
///   its suspension is blocked on; for a checked or synthesised one, the number
///   of laws `verdicts` records for its constant whose own judgement is owed;
///   `0` otherwise.
/// - fails: never.
/// - panics: none.
///
/// # Termination
/// - reason: one pass over the declaration's finite laws, each looked up by
///   binary search, not recursion.
/// - measure: the laws left.
///
/// # Adequacy
/// - hypothesis: L3 — the circle's winding number into the native integers owes
///   its two laws and each law owes itself; a declaration decoding an owed code
///   hole owes that hole.
/// - witness: `kernel_export::kernel_corpus_partition::corpus_partition_matches_the_manifest_in_shard_0`
/// - witness: `settle::tests::a_suspended_declaration_owes_its_blockers`
#[spec(ensures: |ret| match answer.verdict() {
    | Verdict::Owed(_) => usize::from(ret) == 1,
    | Verdict::Suspended(_) => {
        usize::from(ret) == verdicts.suspensions().get(&answer.constant()).map_or(0, |waiting| waiting.blockers().len())
    },
    | Verdict::Checked { .. } | Verdict::Synthesised { .. } => {
        usize::from(ret) <= verdicts.laws().get(&answer.constant()).map_or(0, Vec::len)
    },
    | Verdict::Data | Verdict::Refused(_) => usize::from(ret) == 0,
})]
fn owed_by(
    verdicts: &ModuleReport,
    answer: &Judged,
) -> ObligationCount
{
    let owed = match answer.verdict() {
        Verdict::Owed(_) => 1_usize,
        Verdict::Suspended(_) => verdicts
            .suspensions()
            .get(&answer.constant())
            .map_or(0_usize, |waiting| waiting.blockers().len()),
        Verdict::Checked { .. } | Verdict::Synthesised { .. } => {
            let judged = verdicts.judged();
            verdicts
                .laws()
                .get(&answer.constant())
                .map_or(0_usize, |laws| {
                    laws.iter()
                        .filter(|&&law| {
                            judged
                                .binary_search_by_key(&law, Judged::constant)
                                .ok()
                                .and_then(|at| judged.get(at))
                                .is_some_and(|held| matches!(held.verdict(), Verdict::Owed(_)))
                        })
                        .count()
                })
        },
        Verdict::Data | Verdict::Refused(_) => 0_usize,
    };
    ObligationCount::from(owed)
}

/// The line `lowered`'s block reads the call `line` states to: the call as
/// stated, trimmed, then `~>`, then the engine's normal form, or why it has
/// none.
///
/// # Specification
/// - requires: `line` was read as a `normalizes` payload, so it writes `~>`.
/// - ensures: the call before the first `~>`, trimmed, a space, `~>`, a space,
///   and either the spelling of [`LoweredModule::normal_form`]'s answer or the
///   reason it gives.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a stated normal form the engine reaches settles, one it
///   does not shows the engine's spelling, and a call into a refused block
///   shows the refusal.
/// - witness: `settle::tests::a_normal_form_settles_against_the_engines_reading`
#[spec(ensures: |ret| match expectation::normalized_call(line) {
    Maybe::Present(call) => ret.as_ref().starts_with(call.as_ref()),
    Maybe::Absent(_) => true,
})]
fn normalized(
    module: &LoweredModule<'_>,
    lowered: &LoweredDeclaration<'_>,
    line: &RunSpelling,
) -> RunSpelling
{
    let call = match expectation::normalized_call(line) {
        Maybe::Present(call) => call,
        Maybe::Absent(expectation::normalized_call::Absent::Unwritten) => CallText::from(""),
    };
    let reached = match module.normal_form(lowered, call) {
        Ok(normal) => normal.spelling(),
        Err(fault) => fault.to_string(),
    };
    RunSpelling::from(format!(
        "{call} {arrow} {reached}",
        call = call.as_ref(),
        arrow = expectation::NORMAL_FORM_ARROW
    ))
}

/// The attributes filed under `lowered`'s halves in `table`: the signature's,
/// then the definition's, or, where no definition is written, those of the
/// form refused while it was collected; a form that wrote both halves, a
/// signed function tail, has its attributes read once.
///
/// # Specification
/// - requires: nothing; a declaration half with no table entry contributes no
///   attributes.
/// - ensures: yields the signature’s entries followed by the definition’s
///   entries in their stored order, the refused form's standing in for the
///   definition's when it has none, but reads a shared signature/definition
///   origin only once.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — separate signature and definition expectations produce a
///   conflict with ordered spans; a single attributed signed function settles
///   without a duplicated expectation; an unattributed declaration has no
///   entries; a declaration refused at its form before it wrote a half states
///   its refusal. The predicate traverses a cheap clone of the private
///   iterator, leaving the returned iterator unconsumed.
/// - witness: `settle::tests::a_name_carrying_two_expectations_states_none`
/// - witness: `settle::tests::a_wrong_stated_verdict_is_unsettled_either_way`
/// - witness: `settle::tests::a_form_refused_at_collection_states_its_refusal_1798`
#[spec(
    ensures: |ret| {
    let signature = lowered.signature();
    let definition = match lowered.definition() {
        Maybe::Present(key) => Maybe::Present(key),
        Maybe::Absent(_) => lowered.refused_form(),
    };
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
    let definition = match lowered.definition() {
        Maybe::Present(key) => Maybe::Present(key),
        Maybe::Absent(_) => lowered.refused_form(),
    };
    let first = match signature {
        Maybe::Present(digest) => table.entries(digest),
        Maybe::Absent(_) => &[],
    };
    let second = if signature == definition {
        &[][..]
    }
    else {
        match definition {
            Maybe::Present(digest) => table.entries(digest),
            Maybe::Absent(_) => &[],
        }
    };
    first.iter().chain(second.iter())
}

/// The bytes of the `boundary` attribute `lowered` carries, when it carries
/// one: the block it introduces is checked by its run.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the span of the first `boundary` entry among `lowered`'s
///   attributes; none when it carries none.
/// - provides: what settlement reads a boundary check by.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a checked block and a plain declaration separate the
///   answers.
/// - witness: `settle::tests::a_boundary_check_stands_as_its_run_answers_2901`
#[spec(ensures: |ret| ret == attributes(table, lowered)
    .find(|entry| entry.name() == RegisteredAttribute::BOUNDARY)
    .map(AttributeEntry::span))]
fn boundary_at(
    table: &AttributeTable,
    lowered: &LoweredDeclaration<'_>,
) -> Option<ByteSpan>
{
    attributes(table, lowered)
        .find(|entry| entry.name() == RegisteredAttribute::BOUNDARY)
        .map(AttributeEntry::span)
}

/// The admission positions of `module`'s declarations that state the items
/// they read, in declaration order.
///
/// # Specification
/// - requires: nothing.
/// - ensures: each declaration one of whose attributes, read as [`settle`]
///   reads them, is `reads`, and no other.
/// - provides: whether a runner needs any footprint before the module is
///   settled.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — sources stating `reads` with a written, an empty and a
///   malformed payload, each declaration asked what it reads named, and one
///   declaration of two stating none.
/// - witness: `settle::tests::a_reads_claim_settles_against_the_items_read_2520`
#[spec(ensures: |ret| ret.iter().all(|constant| module.declarations().iter().any(|lowered| lowered.constant() == *constant
    && attributes(module.attributes(), lowered).any(|entry| entry.name() == RegisteredAttribute::READS))))]
#[inline]
#[must_use]
pub fn stating_reads(module: &LoweredModule<'_>) -> Vec<ConstantIndex>
{
    module
        .declarations()
        .iter()
        .filter(|lowered| {
            attributes(module.attributes(), lowered)
                .any(|entry| entry.name() == RegisteredAttribute::READS)
        })
        .map(LoweredDeclaration::constant)
        .collect()
}

/// The entries filed under the form that introduced `lowered` when it writes
/// no half of its own: the attributes written before the application or the
/// module whose header bound it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the entries under [`LoweredDeclaration::introduced`] when the
///   declaration has no signature, no definition and no refused form; none
///   otherwise.
/// - provides: the expectation of a refused name an application or a header
///   binds.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an application refused at its binding and one refused at
///   a witness each settle the attribute written before them, and the witnesses
///   that check settle the default.
/// - witness: `settle::tests::every_refusal_a_source_reaches_settles_the_fixture_naming_it`
#[spec(ensures: |ret| ret == match (lowered.signature(), lowered.definition(), lowered.refused_form()) {
    (Maybe::Absent(_), Maybe::Absent(_), Maybe::Absent(_)) => table.entries(lowered.introduced()),
    _ => &[],
})]
fn header<'table>(
    table: &'table AttributeTable,
    lowered: &LoweredDeclaration<'_>,
) -> &'table [AttributeEntry]
{
    match (
        lowered.signature(),
        lowered.definition(),
        lowered.refused_form(),
    ) {
        (Maybe::Absent(_), Maybe::Absent(_), Maybe::Absent(_)) => {
            table.entries(lowered.introduced())
        },
        _ => &[],
    }
}

/// The form whose attributes the witness `lowered` reads and another
/// declaration of `module` reads as its own: the witness that checks a
/// function's written signature against the one another form states reads the
/// form the function is defined by.
///
/// # Specification
/// - requires: nothing.
/// - ensures: present only when `lowered` is a [`Role::Witness`]: then the
///   first of its signature, definition and refused-form keys that files an
///   entry and is a signature, definition or refused-form key of a declaration
///   at another admission position.
/// - provides: which witness that checks keeps the default beside its refused
///   function.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a function signed twice and a model's law component each
///   settle their refusal beside the witness that checks, and a component's one
///   witness keeps its member's expectation.
/// - witness: `settle::tests::a_witness_that_checks_keeps_the_default_beside_its_refused_function_3706`
#[spec(ensures: |ret| ret.is_none() || lowered.role() == Role::Witness)]
fn function_s_form(
    module: &LoweredModule<'_>,
    lowered: &LoweredDeclaration<'_>,
) -> Option<UnitKey>
{
    let keys = |declaration: &LoweredDeclaration<'_>| {
        [
            declaration.signature(),
            declaration.definition(),
            declaration.refused_form(),
        ]
        .into_iter()
        .filter_map(|key| match key {
            Maybe::Present(key) => Some(key),
            Maybe::Absent(_) => None,
        })
    };
    if lowered.role() != Role::Witness {
        return None;
    }
    keys(lowered)
        .filter(|&key| !module.attributes().entries(key).is_empty())
        .find(|&key| {
            module.declarations().iter().any(|other| {
                other.constant() != lowered.constant() && keys(other).any(|held| held == key)
            })
        })
}

/// What the declaration `lowered` of `module` states under `root`: the
/// expectations among the attributes filed on its signature and its
/// definition, their payloads read out of `arena`.
///
/// # Specification
/// - requires: `lowered` is a declaration of `module`, and `arena` the arena
///   its lowering minted the payloads into.
/// - ensures: the expectation reader's reading of the declaration's entries,
///   the signature's before the definition's.
/// - provides: the stated side of the settle comparison, for a reader that
///   settles nothing.
/// - fails: as the expectation reader.
/// - panics: none.
///
/// # Errors
/// [`SettleFault::UnreadablePayload`] when a payload is not its schema's
/// literal of `arena`.
///
/// # Adequacy
/// - hypothesis: L3 — every settled fixture reads its expectations here; a lost
///   entry or a payload read out of another arena unsettles them.
/// - witness: `settle::tests::a_name_carrying_two_expectations_states_none`
/// - witness: `settle::tests::every_refusal_a_source_reaches_settles_the_fixture_naming_it`
#[spec(ensures: |ref ret| ret.as_ref().map_or_else(|fault| matches!(*fault, SettleFault::UnreadablePayload { .. }), |_| true))]
#[inline]
pub fn expected(
    root: CorpusRoot,
    arena: &CoreArena,
    module: &LoweredModule<'_>,
    lowered: &LoweredDeclaration<'_>,
) -> Result<Expectations, SettleFault>
{
    expectation::read(
        root,
        attributes(module.attributes(), lowered),
        arena,
        |entry| spelled(module.attributes(), lowered, entry),
    )
}

/// What the declaration `lowered` of `module` states under `root` once it is
/// refused.
///
/// A name an application or a module's header binds writes no half, so the
/// attributes before the form that introduced it state its refusal; a
/// witness of it that checks keeps [`expected`]'s default.
///
/// # Specification
/// - requires: as [`expected`].
/// - ensures: the expectation reader's reading of [`header`]'s entries when
///   there are any, and [`expected`]'s reading otherwise.
/// - provides: the stated side of a refused declaration's settle comparison,
///   for [`settle`] and for a reader that settles nothing.
/// - fails: as the expectation reader.
/// - panics: none.
///
/// # Errors
/// [`SettleFault::UnreadablePayload`] when a payload is not its schema's
/// literal of `arena`.
///
/// # Adequacy
/// - hypothesis: L3 — an application refused at its binding and one refused at
///   a witness each settle the attribute written before them, and the witnesses
///   that check settle the default.
/// - witness: `settle::tests::every_refusal_a_source_reaches_settles_the_fixture_naming_it`
#[spec(ensures: |ref ret| ret.as_ref().map_or_else(|fault| matches!(*fault, SettleFault::UnreadablePayload { .. }), |_| true))]
#[inline]
pub fn refused_expected(
    root: CorpusRoot,
    arena: &CoreArena,
    module: &LoweredModule<'_>,
    lowered: &LoweredDeclaration<'_>,
) -> Result<Expectations, SettleFault>
{
    let introduced = header(module.attributes(), lowered);
    if introduced.is_empty() {
        return expected(root, arena, module, lowered);
    }
    expectation::read(root, introduced.iter(), arena, |entry| {
        spelled(module.attributes(), lowered, entry)
    })
}

/// The spelling the lowering filed beside `entry`, an attribute of the
/// declaration `lowered` whose payload it read unquoted.
///
/// # Specification
/// - requires: `entry` is filed in `table` under one of `lowered`'s keys.
/// - ensures: the spelling filed under the first of `lowered`'s signature,
///   definition, refused form and introduced keys that holds one for the
///   entry's span; absent when none does.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a `decomposes` written before a dialogue's signature is
///   read from the signature's key, and each of two `traces` reads its own.
/// - witness: `settle::tests::a_web_settles_against_the_dialogue_s_decomposition_2077`
/// - witness: `settle::tests::a_channel_settles_against_the_web_its_play_decomposes_to_3338`
#[spec(ensures: |ret| ret.as_ref().is_none_or(|web| {
    [lowered.signature(), lowered.definition(), lowered.refused_form(), Maybe::Present(lowered.introduced())]
        .into_iter()
        .any(|key| matches!(key, Maybe::Present(key) if table.spelled(key, entry.span()).is_some_and(|filed| filed.as_str() == web.as_ref())))
}))]
fn spelled(
    table: &AttributeTable,
    lowered: &LoweredDeclaration<'_>,
    entry: &AttributeEntry,
) -> Option<RunSpelling>
{
    let present = |key| match key {
        Maybe::Present(key) => Some(key),
        Maybe::Absent(_) => None,
    };
    [
        present(lowered.signature()),
        present(lowered.definition()),
        present(lowered.refused_form()),
        Some(lowered.introduced()),
    ]
    .into_iter()
    .flatten()
    .find_map(|key| table.spelled(key, entry.span()))
    .map(|web| RunSpelling::from(web.clone()))
}

/// Each channel of `stated` as the run played it: the web of every play of
/// that name among `plays`, read as the stated web reads it
/// ([`web_as_stated`]), in the order played and joined by ` then `;
/// `unplayed` for a channel the run never forked.
///
/// # Specification
/// - ensures: one channel per stated one, named alike, in order.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a channel played as stated, played otherwise, stated by
///   its prime count and never forked, alone and beside another.
/// - witness: `settle::tests::a_channel_settles_against_the_web_its_play_decomposes_to_3338`
#[spec(ensures: |ref ret| ret.len() == stated.len()
    && ret.iter().zip(stated).all(|(played, written)| played.name == written.name))]
fn played(
    stated: &[Channel],
    plays: &[Channel],
) -> Vec<Channel>
{
    stated
        .iter()
        .map(|written| {
            let mut web = String::new();
            for play in plays.iter().filter(|play| play.name == written.name) {
                if !web.is_empty() {
                    web.push_str(" then ");
                }
                web.push_str(web_as_stated(&written.web, &play.web).as_ref());
            }
            if web.is_empty() {
                web.push_str(UNPLAYED);
            }
            Channel {
                name: written.name.clone(),
                web: RunSpelling::from(web),
            }
        })
        .collect()
}

/// Whether the channels `played` holds are the ones `stated` states, in
/// order.
///
/// # Specification
/// - ensures: settled exactly when both hold the same channels in the same
///   order.
/// - panics: none.
///
/// # Clause cost
/// - bound: one name and one web comparison per stated channel, one entry per
///   channel a declaration's run forks.
///
/// # Adequacy
/// - hypothesis: L3 — as [`played`].
/// - witness: `settle::tests::a_channel_settles_against_the_web_its_play_decomposes_to_3338`
#[spec(ensures: |ret| (ret == Settlement::Settled) == (played == stated))]
fn channels_settle(
    played: &[Channel],
    stated: &[Channel],
) -> Settlement
{
    if played == stated {
        Settlement::Settled
    }
    else {
        Settlement::Unsettled
    }
}

#[cfg(test)]
mod tests
{
    use alloc::collections::BTreeSet;
    use alloc::format;
    use alloc::string::String;
    use alloc::string::ToString as _;
    use alloc::vec::Vec;
    use core::fmt;

    use anodized::spec;
    use gandr_core_checker::ObligationCount;
    use gandr_core_checker::Verdict;
    use gandr_core_term::CoreArena;
    use gandr_core_term::FailureClass;
    use gandr_kernel_term::ConstantIndex;
    use gandr_surface_lowering::SurfaceName;
    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::SourceText;
    use quenchant_shape::shape::Maybe;

    use super::DeclarationReport;
    use super::Produced;
    use super::SettleFault;
    use super::Settlement;
    use super::Surviving;
    use super::settle;
    use super::settle_after;
    use super::stating_reads;
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
    use crate::run::Channel;
    use crate::run::RunSpelling;
    use crate::run::Runner;
    use crate::run::TracedRun;

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
                r#"@[ checks ] def f(x: Integer) -> -F Integer { return x }"#,
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

    /// #1798: a declaration refused at its own form while it was collected —
    /// an implicit telescope before no function's parameters — wrote no half,
    /// so its attribute block was read nowhere and it stayed expected to
    /// check. The block is filed under the refused form, which stands in for
    /// the definition the form did not write.
    #[test]
    fn a_form_refused_at_collection_states_its_refusal_1798()
    {
        let rows = [
            (
                r#"@[ refuses("ImplicitTelescope") ] def f @[a : Type] = 1 ;"#,
                Settlement::Settled,
            ),
            (
                r#"@[ refuses("TypeMismatch") ] def f @[a : Type] = 1 ;"#,
                Settlement::Unsettled,
            ),
            (r#"def f @[a : Type] = 1 ;"#, Settlement::Unsettled),
            (
                r#"def f : Integer ; @[ refuses("ImplicitTelescope") ] def f @[a : Type] = 1 ;"#,
                Settlement::Settled,
            ),
        ];
        for (source, settlement) in rows {
            let report = settled(CorpusRoot::Fixture, SourceText::from(source));
            assert_eq!(
                only(&report).settlement(),
                settlement,
                "`{source}` settles as pinned"
            );
        }
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

    /// #3100: a unit laid from a strict source and a fixture settled its
    /// expectations under the root of whichever path was given first; each
    /// declaration settles under the root its own bytes start in.
    #[test]
    fn each_declaration_settles_under_the_root_its_bytes_start_in_3100()
    {
        use crate::root::Rooted;

        /// `before` up to `at`, `after` from it.
        ///
        /// # Specification
        /// trivial.
        #[derive(Clone, Copy)]
        struct Split
        {
            /// Where the second root starts.
            at: ByteOffset,
            /// The root before `at`.
            before: CorpusRoot,
            /// The root from `at`.
            after: CorpusRoot,
        }

        impl Rooted for Split
        {
            /// `before` up to `at`, `after` from it.
            ///
            /// # Specification
            /// trivial.
            fn root_at(
                &self,
                start: ByteOffset,
            ) -> CorpusRoot
            {
                if start < self.at {
                    self.before
                }
                else {
                    self.after
                }
            }
        }

        let source = r#"@[ refuses("UnresolvedName") ] def a = z ; @[ refuses("UnresolvedName") ] def b = y ;"#;
        let at = ByteOffset::from(source.find(" @[").expect("two declarations are written"));
        for (before, after, settlements) in [
            (CorpusRoot::Strict, CorpusRoot::Fixture, [
                Settlement::Unsettled,
                Settlement::Settled,
            ]),
            (CorpusRoot::Fixture, CorpusRoot::Strict, [
                Settlement::Settled,
                Settlement::Unsettled,
            ]),
        ] {
            let report = settled(Split { at, before, after }, SourceText::from(source));
            let read: Vec<Settlement> = report
                .declarations()
                .iter()
                .map(DeclarationReport::settlement)
                .collect();
            assert_eq!(
                read, settlements,
                "under {before} then {after}, the strict `refuses` is refused and the fixture's \
                 settles"
            );
            assert!(
                report.declarations().iter().any(|declaration| matches!(
                    declaration.produced(),
                    Produced::Guarded(CorpusRefusal::ExpectationOutsideFixtureRoot {
                        schema: ExpectationSchema::Refuses,
                        ..
                    })
                )),
                "the strict declaration's `refuses` is the corpus refusal"
            );
        }
    }

    #[test]
    fn a_suspended_declaration_owes_its_blockers()
    {
        let report = settled(
            CorpusRoot::Fixture,
            SourceText::from(
                "def code : Type ; def three : code ; def three = 3 ; def filled : Type ; \
                 def filled = Integer ; def resumed : filled ; def resumed = 3 ;",
            ),
        );
        let &[ref code, ref three, _, ref resumed] = report.declarations()
        else {
            panic!("four declarations: {:?}", report.declarations());
        };
        assert!(
            matches!(three.produced(), Produced::Judged(Verdict::Suspended(_))),
            "a value at an owed code's decode waits: {:?}",
            three.produced()
        );
        assert_eq!(
            usize::from(three.owed()),
            1_usize,
            "it owes the one hole it waits on"
        );
        assert_eq!(three.waits(), [code.name()], "and names that hole");
        assert_eq!(
            usize::from(report.ledger()),
            1_usize,
            "the ledger holds the hole once, under the hole"
        );
        assert!(
            matches!(
                resumed.produced(),
                Produced::Judged(Verdict::Checked { .. })
            ),
            "the same value at a filled code's decode checks: {:?}",
            resumed.produced()
        );
        assert_eq!(usize::from(resumed.owed()), 0_usize);
        assert!(resumed.waits().is_empty());
    }

    /// #2356: a law a module admits at a primitive carrier crosses as the
    /// owed axiom it is, settles `checks` owing nothing and lists its
    /// admission on its line; the checker's ledger still holds it.
    #[test]
    fn an_admitted_law_settles_as_checks_and_lists_its_admission_2356()
    {
        let report = settled(
            CorpusRoot::Fixture,
            SourceText::from(
                "theory Same {\n  sort Carrier : Type;\n  oper same : (a : Carrier, b : Carrier) --> Bool;\n  law refl : (a : Carrier) => Path(Bool, same(a, a), true);\n}\nmodule SameInteger : Model(Same) with sort Carrier = Integer {\n  def same(a : Integer, b : Integer) -> Bool { int.eq(a, b) }\n  law refl admitted;\n}\n",
            ),
        );
        let refl = report
            .declarations()
            .iter()
            .find(|declaration| declaration.name() == SurfaceName::from("refl"))
            .unwrap_or_else(|| panic!("`refl` is declared: {:?}", report.declarations()));
        assert!(
            matches!(refl.produced(), Produced::Judged(Verdict::Owed(_))),
            "the admission is owed to the checker: {:?}",
            refl.produced()
        );
        assert_eq!(
            (refl.settlement(), usize::from(refl.owed())),
            (Settlement::Settled, 0_usize),
            "and settles `checks`, owing nothing"
        );
        assert!(
            refl.to_string()
                .ends_with("; audit: SameInteger.refl admitted"),
            "its line names the admission: {refl}"
        );
        assert_eq!(
            usize::from(report.ledger()),
            1_usize,
            "the ledger holds the axiom the kernel takes"
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

    /// #2901: a block carrying `boundary` stands as its check's run answers.
    /// An admission keeps the checker's verdict, so the block checks; a
    /// clause refuses the block at its attribute in place of that verdict,
    /// and settles only the block that states it. The check alone is run.
    #[test]
    fn a_boundary_check_stands_as_its_run_answers_2901()
    {
        let declared = concat!(
            "data Scalar : Type { U32 : Scalar; }\n",
            "data Code : Type { Plain : (s : Scalar) --> Code; }\n",
            "data Coded : Type { NoCoded : Coded; Coded : (name : String, c : Code, rest : Coded) --> Coded; }\n",
            "data Signature : Type { Signature : (params : Coded, result : Code) --> Signature; }\n",
            "data Signatures : Type { NoSignature : Signatures; Member : (s : Signature, rest : Signatures) --> Signatures; }\n",
            "data Row : Type { Row : (result : Code) --> Row; }\n",
            "data Rows : Type { NoRow : Rows; Named : (r : Row, rest : Rows) --> Rows; }\n",
            "data Admission : Type { Admitted : Admission; }\n",
            "def admitBlock(ss : Signatures, rs : Rows) -> Admission { Admitted }\n",
            "def addRow : Row = Row(Plain(U32));\n",
        );
        let size = RefusalName::BoundaryUnrealised(crate::refusal::BoundaryClause::Size.tag());
        let rows = [
            (
                "",
                "Admitted",
                Outcome::Checks(ObligationCount::from(0_usize)),
                Settlement::Settled,
            ),
            (
                "",
                "Unrealised(Size(Argument(1)))",
                Outcome::Refuses(size),
                Settlement::Unsettled,
            ),
            (
                r#", refuses("BoundaryUnrealised.Size")"#,
                "Unrealised(Size(Argument(1)))",
                Outcome::Refuses(size),
                Settlement::Settled,
            ),
            (
                r#", refuses("BoundaryUnrealised.Size")"#,
                "Unrealised(Members)",
                Outcome::Refuses(RefusalName::BoundaryUnrealised(
                    crate::refusal::BoundaryClause::Members.tag(),
                )),
                Settlement::Unsettled,
            ),
            (
                "",
                "stopped short",
                Outcome::Refuses(RefusalName::BoundaryUnrealised(
                    crate::refusal::BoundaryClause::Unanswered.tag(),
                )),
                Settlement::Unsettled,
            ),
        ];
        for (stated, ran, outcome, settlement) in rows {
            let text = format!(
                "{declared}@[ boundary(addRow){stated} ]\nextern \"rust\" from \"b\" as B {{ def add(x : u32) -> u32; }}\n"
            );
            let module = checked(SourceText::from(text.as_str()));
            let mut asked = Vec::new();
            let mut runner = |constant: ConstantIndex| {
                asked.push(usize::from(constant));
                RunSpelling::from(String::from(ran))
            };
            let report = settle(
                CorpusRoot::Fixture,
                &module.arena,
                &module.module,
                &module.verdicts,
                &mut runner,
            )
            .expect("the verdicts are the module's own");
            let Some(check) = report
                .declarations()
                .iter()
                .find(|declaration| declaration.name == SurfaceName::from("B"))
            else {
                panic!("the block takes its check's slot");
            };
            assert_eq!(
                (check.outcome(), check.settlement()),
                (outcome, settlement),
                "`{ran}` against `{stated}` produces and settles as pinned"
            );
            assert_eq!(
                asked,
                [usize::from(check.constant)],
                "`{ran}`: the check alone is run"
            );
            if let Produced::Guarded(CorpusRefusal::BoundaryUnrealised { span, .. }) =
                check.produced
            {
                assert_eq!(
                    text.get(usize::from(span.start()) .. usize::from(span.end())),
                    Some("boundary(addRow)"),
                    "`{ran}` is refused at the attribute"
                );
            }
        }
    }

    /// A runner recording which of its runs each position asked for.
    ///
    /// # Specification
    /// trivial.
    #[repr(transparent)]
    #[derive(Default)]
    struct Asked(Vec<(&'static str, usize)>);

    impl Runner for Asked
    {
        /// Records an accepted run and spells it by position.
        ///
        /// # Specification
        /// trivial.
        fn run(
            &mut self,
            constant: ConstantIndex,
        ) -> RunSpelling
        {
            self.0.push(("run", usize::from(constant)));
            ran_at(constant)
        }

        /// Records a refused run and spells it by position.
        ///
        /// # Specification
        /// trivial.
        fn run_refused(
            &mut self,
            constant: ConstantIndex,
        ) -> RunSpelling
        {
            self.0.push(("refused", usize::from(constant)));
            ran_at(constant)
        }

        /// Records a decomposition and spells it as a one-event web at the
        /// position.
        ///
        /// # Specification
        /// trivial.
        fn decompose(
            &mut self,
            constant: ConstantIndex,
        ) -> RunSpelling
        {
            self.0.push(("decompose", usize::from(constant)));
            RunSpelling::from(format!("event(left, {})", usize::from(constant)))
        }

        /// Records a traced run, spells it by position, and plays one
        /// channel, `c`, as a one-event web at the position.
        ///
        /// # Specification
        /// trivial.
        fn run_traced(
            &mut self,
            constant: ConstantIndex,
        ) -> TracedRun
        {
            self.0.push(("traced", usize::from(constant)));
            TracedRun {
                run: ran_at(constant),
                channels: Vec::from([Channel {
                    name: String::from("c"),
                    web: RunSpelling::from(format!("event(left, {})", usize::from(constant))),
                }]),
            }
        }

        /// Records what a declaration reads and spells it as `(Nat, side)`
        /// whatever the position.
        ///
        /// # Specification
        /// trivial.
        fn reads(
            &mut self,
            constant: ConstantIndex,
        ) -> RunSpelling
        {
            self.0.push(("reads", usize::from(constant)));
            RunSpelling::from(String::from("(Nat, side)"))
        }
    }

    /// #2077: a `decomposes` payload is the web's tree, unquoted; an accepted
    /// dialogue settles when the web `decompose` reads back is the one it
    /// states, however the tree is laid out, and a payload that is no web
    /// node is a malformed expectation that asks for nothing.
    #[test]
    fn a_web_settles_against_the_dialogue_s_decomposition_2077()
    {
        let web = |at: &str| Outcome::Decomposes(RunSpelling::from(format!("event(left, {at})")));
        let rows = [
            (
                CorpusRoot::Strict,
                "@[ decomposes(event(left, 0)) ] def a = 3 ;",
                web("0"),
                Settlement::Settled,
                &[("decompose", 0_usize)][..],
            ),
            (
                CorpusRoot::Fixture,
                "@[ decomposes(\n  event(\n    left,\n    0\n  )\n) ] def a = 3 ;",
                web("0"),
                Settlement::Settled,
                &[("decompose", 0_usize)][..],
            ),
            (
                CorpusRoot::Fixture,
                "@[ decomposes(event(left, 1)) ] def a = 3 ;",
                web("0"),
                Settlement::Unsettled,
                &[("decompose", 0_usize)][..],
            ),
            (
                CorpusRoot::Fixture,
                "@[ decomposes(series) ] def a = 3 ;",
                Outcome::Checks(ObligationCount::from(0_usize)),
                Settlement::Unsettled,
                &[][..],
            ),
            (
                CorpusRoot::Fixture,
                "@[ decomposes(event(left, 0)) ] def a : Integer ;",
                Outcome::Checks(ObligationCount::from(1_usize)),
                Settlement::Unsettled,
                &[][..],
            ),
        ];
        for (root, source, outcome, settlement, runs) in rows {
            let module = checked(SourceText::from(source));
            let mut asked = Asked::default();
            let report = settle(
                root,
                &module.arena,
                &module.module,
                &module.verdicts,
                &mut asked,
            )
            .expect("the verdicts are the module's own");
            assert_eq!(
                (
                    only(&report).outcome(),
                    only(&report).settlement(),
                    asked.0.as_slice()
                ),
                (outcome, settlement, runs),
                "`{source}` under the {root} root decomposes and settles as pinned"
            );
        }
    }

    /// #2520: a `reads` payload names the items a declaration mentions; it
    /// settles when the runner names the same items in any order, a data
    /// declaration's included, and a payload that names no items is a
    /// malformed expectation that asks for nothing. Every declaration asked
    /// what it reads is one [`stating_reads`] names, and a declaration that
    /// states no `reads` is not.
    #[test]
    fn a_reads_claim_settles_against_the_items_read_2520()
    {
        let read = |spelled: &str| Outcome::Reads(RunSpelling::from(String::from(spelled)));
        let rows = [
            (
                CorpusRoot::Strict,
                "@[ reads((side, Nat)) ] def a = 3 ;",
                read("(side, Nat)"),
                Settlement::Settled,
                &[("reads", 0_usize)][..],
            ),
            (
                CorpusRoot::Fixture,
                "@[ reads(Nat) ] def a = 3 ;",
                read("(Nat, side)"),
                Settlement::Unsettled,
                &[("reads", 0_usize)][..],
            ),
            (
                CorpusRoot::Fixture,
                "@[ reads((Nat, side, Nat)) ] data D : Type { E : D; }",
                read("(Nat, side, Nat)"),
                Settlement::Settled,
                &[("reads", 0_usize)][..],
            ),
            (
                CorpusRoot::Fixture,
                "@[ reads(()) ] def a = 3 ;",
                read("(Nat, side)"),
                Settlement::Unsettled,
                &[("reads", 0_usize)][..],
            ),
            (
                CorpusRoot::Fixture,
                "@[ reads(f(x)) ] def a = 3 ;",
                Outcome::Checks(ObligationCount::from(0_usize)),
                Settlement::Unsettled,
                &[][..],
            ),
            (
                CorpusRoot::Fixture,
                "@[ reads(Nat) ] def a : Integer ;",
                Outcome::Checks(ObligationCount::from(1_usize)),
                Settlement::Unsettled,
                &[][..],
            ),
        ];
        for (root, source, outcome, settlement, asks) in rows {
            let module = checked(SourceText::from(source));
            let stating: BTreeSet<ConstantIndex> =
                stating_reads(&module.module).into_iter().collect();
            let mut asked = Asked::default();
            let report = settle(
                root,
                &module.arena,
                &module.module,
                &module.verdicts,
                &mut asked,
            )
            .expect("the verdicts are the module's own");
            assert_eq!(
                (
                    only(&report).outcome(),
                    only(&report).settlement(),
                    asked.0.as_slice()
                ),
                (outcome, settlement, asks),
                "`{source}` under the {root} root reads and settles as pinned"
            );
            assert!(
                asked
                    .0
                    .iter()
                    .all(|&(_, position)| stating.contains(&ConstantIndex::from(position))),
                "`{source}`: each declaration asked what it reads states it"
            );
        }
        let module = checked(SourceText::from("def b = 3 ; @[ reads(Nat) ] def a = 3 ;"));
        assert_eq!(
            stating_reads(&module.module),
            [ConstantIndex::from(1_usize)],
            "only the declaration stating `reads` is named"
        );
    }

    /// #3338: a `traces` entry beside `runs` states one channel's web; the
    /// declaration settles when the run is the stated one and each stated
    /// channel's play decomposes to its web, or to its stated count of prime
    /// nodes. A channel the run never forked reads `unplayed`.
    #[test]
    fn a_channel_settles_against_the_web_its_play_decomposes_to_3338()
    {
        let tracing = |ran: &str, channels: &[(&str, &str)]| {
            Outcome::RunsTracing(
                RunSpelling::from(String::from(ran)),
                channels
                    .iter()
                    .map(|&(name, web)| Channel {
                        name: String::from(name),
                        web: RunSpelling::from(String::from(web)),
                    })
                    .collect(),
            )
        };
        let rows = [
            (
                CorpusRoot::Strict,
                "@[ runs(\"ran at 0\"), traces(decomposes(c, event(left, 0))) ] def a = 3 ;",
                tracing("ran at 0", &[("c", "event(left, 0)")]),
                Settlement::Settled,
            ),
            (
                CorpusRoot::Fixture,
                "@[ runs(\"ran at 0\"), traces(primes(c, 0)) ] def a = 3 ;",
                tracing("ran at 0", &[("c", "primes = 0")]),
                Settlement::Settled,
            ),
            (
                CorpusRoot::Fixture,
                "@[ runs(\"ran at 0\"), traces(decomposes(c, event(left, 1))) ] def a = 3 ;",
                tracing("ran at 0", &[("c", "event(left, 0)")]),
                Settlement::Unsettled,
            ),
            (
                CorpusRoot::Fixture,
                "@[ runs(\"ran at 0\"), traces(decomposes(d, event(left, 0))) ] def a = 3 ;",
                tracing("ran at 0", &[("d", "unplayed")]),
                Settlement::Unsettled,
            ),
            (
                CorpusRoot::Fixture,
                "@[ runs(\"ran at 1\"), traces(decomposes(c, event(left, 0))) ] def a = 3 ;",
                tracing("ran at 0", &[("c", "event(left, 0)")]),
                Settlement::Unsettled,
            ),
            (
                CorpusRoot::Fixture,
                "@[ runs(\"ran at 0\"), traces(decomposes(c, event(left, 0))), traces(primes(d, 0)) \
                 ] def a = 3 ;",
                tracing("ran at 0", &[("c", "event(left, 0)"), ("d", "unplayed")]),
                Settlement::Unsettled,
            ),
        ];
        for (root, source, outcome, settlement) in rows {
            let module = checked(SourceText::from(source));
            let mut asked = Asked::default();
            let report = settle(
                root,
                &module.arena,
                &module.module,
                &module.verdicts,
                &mut asked,
            )
            .expect("the verdicts are the module's own");
            assert_eq!(
                (
                    only(&report).outcome(),
                    only(&report).settlement(),
                    asked.0.as_slice()
                ),
                (outcome, settlement, &[("traced", 0_usize)][..]),
                "`{source}` under the {root} root traces and settles as pinned"
            );
        }
    }

    #[test]
    fn a_run_beside_a_refusal_settles_only_when_both_hold()
    {
        let both = |name, position: &str| {
            Outcome::RefusesRunning(name, RunSpelling::from(format!("ran at {position}")))
        };
        let rows = [
            (
                CorpusRoot::Fixture,
                r#"@[ runs("ran at 0"), refuses("TypeMismatch") ] def a : Integer ; def a = "three" ;"#,
                both(RefusalName::TypeMismatch, "0"),
                Settlement::Settled,
            ),
            (
                CorpusRoot::Fixture,
                r#"@[ refuses("TypeMismatch"), runs("ran at 1") ] def a : Integer ; def a = "three" ;"#,
                both(RefusalName::TypeMismatch, "0"),
                Settlement::Unsettled,
            ),
            (
                CorpusRoot::Fixture,
                r#"@[ runs("ran at 0"), refuses("UnknownConstant") ] def a : Integer ; def a = "three" ;"#,
                both(RefusalName::TypeMismatch, "0"),
                Settlement::Unsettled,
            ),
            (
                CorpusRoot::Fixture,
                r#"@[ runs("ran at 0"), refuses("TypeMismatch") ] def a = 3 ;"#,
                Outcome::Checks(ObligationCount::from(0_usize)),
                Settlement::Unsettled,
            ),
            (
                CorpusRoot::Strict,
                r#"@[ runs("ran at 0"), refuses("TypeMismatch") ] def a : Integer ; def a = "three" ;"#,
                Outcome::Refuses(RefusalName::ExpectationOutsideFixtureRoot),
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
            r#"@[ runs("ran at 0") ] def a = 3 ; @[ runs("ran at 1"), refuses("TypeMismatch") ] def b : Integer ; def b = "three" ; @[ refuses("TypeMismatch") ] def c : Integer ; def c = "four" ; @[ runs("ran at 3"), refuses("TypeMismatch") ] def d = 4 ;"#,
        ));
        let mut asked = Asked::default();
        let report = settle(
            CorpusRoot::Fixture,
            &module.arena,
            &module.module,
            &module.verdicts,
            &mut asked,
        )
        .expect("the verdicts are the module's own");
        assert_eq!(
            asked.0,
            [("run", 0_usize), ("refused", 1_usize)],
            "an accepted run is asked as one, a refused run beside its refusal as the other, and nothing else"
        );
        assert_eq!(
            report
                .declarations()
                .iter()
                .map(DeclarationReport::settlement)
                .collect::<Vec<_>>(),
            [
                Settlement::Settled,
                Settlement::Settled,
                Settlement::Settled,
                Settlement::Unsettled
            ],
            "each settles on its own verdict; the checked one stating a refusal does not"
        );
    }

    #[test]
    fn a_normal_form_settles_against_the_engines_reading()
    {
        let family = |rules: &str, line: &str| {
            format!(
                r#"@[ normalizes("{line}") ]
data NatUnits : Type {{
    Zero : NatUnits;
    Succ : (n : NatUnits) --> NatUnits;
    oper add(m : NatUnits, n : NatUnits) -> NatUnits;
    rule add(Zero, n) ==> n;
    {rules}
    rule add(Succ(m), n) ==> Succ(add(m, n));
}}"#
            )
        };
        let joins = "rule add(m, Zero) ==> m;";
        let parts = "rule add(m, Zero) ==> Succ(m);";
        let normalizes = |line: &str| Outcome::Normalizes(RunSpelling::from(String::from(line)));
        let rows = [
            (
                CorpusRoot::Strict,
                family(joins, "add(Succ(Zero), Zero) ~> Succ(Zero)"),
                normalizes("add(Succ(Zero), Zero) ~> Succ(Zero)"),
                Settlement::Settled,
            ),
            (
                CorpusRoot::Fixture,
                family(joins, " add(Zero, Zero)   ~> Zero"),
                normalizes("add(Zero, Zero) ~> Zero"),
                Settlement::Unsettled,
            ),
            (
                CorpusRoot::Fixture,
                family(joins, "add(Zero, Zero) ~> Succ(Zero)"),
                normalizes("add(Zero, Zero) ~> Zero"),
                Settlement::Unsettled,
            ),
            (
                CorpusRoot::Fixture,
                family(joins, "add(Zero, Zero) ~> nonsense("),
                normalizes("add(Zero, Zero) ~> Zero"),
                Settlement::Unsettled,
            ),
            (
                CorpusRoot::Fixture,
                family(joins, "add(Zero, Zero)"),
                Outcome::Checks(ObligationCount::from(0_usize)),
                Settlement::Unsettled,
            ),
            (
                CorpusRoot::Fixture,
                family(parts, "add(Zero, Zero) ~> Zero"),
                Outcome::Refuses(RefusalName::RulesDiverge),
                Settlement::Unsettled,
            ),
        ];
        for (root, source, outcome, settlement) in rows {
            let report = settled(root, SourceText::from(source.as_str()));
            for declaration in report.declarations() {
                assert_eq!(
                    (declaration.outcome(), declaration.settlement()),
                    (outcome.clone(), settlement),
                    "`{source}` under the {root} root produces and settles as pinned at `{}`, \
                     the family and its operation alike",
                    declaration.name()
                );
            }
        }

        let unwritten_source = family(joins, "add(Zero, Zero)");
        let unwritten = settled(
            CorpusRoot::Fixture,
            SourceText::from(unwritten_source.as_str()),
        );
        assert!(matches!(
            unwritten.declarations()[0].stated(),
            Stated::Malformed(ExpectationFault::UnwrittenNormalForm { .. })
        ));
        let function = settled(
            CorpusRoot::Fixture,
            SourceText::from(r#"@[ normalizes("a ~> 3") ] def a = 3 ;"#),
        );
        assert_eq!(
            (only(&function).outcome(), only(&function).settlement()),
            (
                normalizes("a ~> no normal form: the declaration has no rules"),
                Settlement::Unsettled
            ),
            "a definition holds no rules to read a call under"
        );
    }

    #[test]
    fn every_refusal_a_source_reaches_settles_the_fixture_naming_it()
    {
        let named = |text: &str| match RefusalName::named_by(
            &gandr_kernel_term::StringLiteral::new(alloc::string::String::from(text)),
        ) {
            Maybe::Present(name) => name,
            Maybe::Absent(_) => panic!("`{text}` names a refusal"),
        };
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
                r#"@[ refuses("OutOfFragment.WrongSort") ] def a : -F Integer & -F Integer ;"#,
                named("OutOfFragment.WrongSort"),
                FailureClass::MalformedSource,
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
                r#"@[ refuses("ShapeMismatch") ] def a : +U (Integer -> -F Integer) ; def a = thunk { return 3 } ;"#,
                RefusalName::ShapeMismatch,
                FailureClass::MalformedSource,
            ),
            (
                r#"@[ refuses("NotSynthesisable") ] def a = thunk { return 3 } ;"#,
                RefusalName::NotSynthesisable,
                FailureClass::MalformedSource,
            ),
            (
                r#"@[ refuses("UnenclosedRun") ] def a : Integer ; def a = 1 + 2 ;"#,
                RefusalName::UnenclosedRun,
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

    /// #1274: a name an application binds and refuses settles under the
    /// attribute before the application, and a refused declaration that
    /// writes its own halves keeps the expectation written before it.
    #[test]
    fn an_application_s_attribute_states_its_refused_names_1274()
    {
        let report = settled(
            CorpusRoot::Fixture,
            SourceText::from(
                r#"module Mk(C : #{ zero : Integer }) { @[ checks ] def seed = C.zero ; } module Bare { @[ checks ] def other = 1 ; } @[ refuses("UnknownMember") ] module Applied = Mk(Bare) ; @[ refuses("UnresolvedName") ] def b = z ;"#,
            ),
        );
        let unsettled: Vec<_> = report
            .declarations()
            .iter()
            .filter(|declaration| declaration.settlement() != Settlement::Settled)
            .map(DeclarationReport::name)
            .collect();
        assert!(
            unsettled.is_empty(),
            "the applied `seed` settles under its application's attribute and `b` under its \
             own, got {unsettled:?} unsettled in {:?}",
            report.declarations()
        );
        assert!(
            report
                .declarations()
                .iter()
                .any(|declaration| matches!(declaration.produced().refusal(), Maybe::Present(refusal) if refusal.name() == RefusalName::UnknownMember)),
            "the application refuses its binding by name"
        );
    }

    /// #3706: an expectation written before a signed function whose signature
    /// another form states settles the refusal the function meets. The
    /// witness checking the function's written signature against the stated
    /// one keeps the default when it checks: a model's law component and a
    /// function signed twice alike.
    #[test]
    fn a_witness_that_checks_keeps_the_default_beside_its_refused_function_3706()
    {
        let rows = [
            (
                r#"def g : +U (Bool -> -F Integer) ; @[ refuses("TypeMismatch") ] def g(x : Bool) -> Integer { "s" }"#,
                RefusalName::TypeMismatch,
            ),
            (
                r#"theory Idem {
                  sort T : Type;
                  oper f : (x : T) --> T;
                  rule idem : f(f(x)) <=> f(x);
                }
                module Bad : Model(Idem) {
                  type T = Bool;
                  def f(x : Bool) -> Bool { case x { true => false, false => true } }
                  @[ refuses("EndpointMismatch") ]
                  def idem(x : Bool) -> Path(Bool, f(f(x)), f(x)) { here(f(x)) }
                }"#,
                RefusalName::EndpointMismatch,
            ),
        ];
        for (source, name) in rows {
            let report = settled(CorpusRoot::Fixture, SourceText::from(source));
            let fixtures: Vec<_> = report
                .declarations()
                .iter()
                .filter(|declaration| declaration.membership() == Membership::Fixture)
                .collect();
            let [fixture] = *fixtures
            else {
                panic!(
                    "the refused function alone states the expectation, got {:?}",
                    report.declarations()
                );
            };
            assert!(
                matches!(fixture.produced().refusal(), Maybe::Present(refusal) if refusal.name() == name),
                "the fixture is the function refused {name}, got {fixture:?}"
            );
            let unsettled: Vec<_> = report
                .declarations()
                .iter()
                .filter(|declaration| declaration.settlement() != Settlement::Settled)
                .map(DeclarationReport::name)
                .collect();
            assert!(
                unsettled.is_empty(),
                "the refused function settles under its expectation and the witness that checks \
                 under the default, got {unsettled:?} unsettled in {:?}",
                report.declarations()
            );
        }
    }

    /// #776: a module settled after its leading declarations' report — a
    /// lowering refusal among them, which consumes no verdict — settles to the
    /// report settling it whole gives, every split alike, running only the
    /// declarations after the leading ones.
    #[test]
    fn a_module_settled_after_its_leading_report_settles_as_a_whole_one_776()
    {
        let module = checked(SourceText::from(
            r#"@[ runs("ran at 0") ] def a = 3 ; @[ refuses("UnresolvedName") ] def b = z ; @[ owes(1) ] def c : Integer ; @[ runs("ran at 3") ] def d = a ; def e = 5 ;"#,
        ));
        let whole = settle(
            CorpusRoot::Fixture,
            &module.arena,
            &module.module,
            &module.verdicts,
            &mut ran_at,
        )
        .expect("the verdicts are the module's own");
        assert_eq!(whole.declarations().len(), 5_usize, "five names");
        for leading in 0_usize ..= 5_usize {
            let earlier = whole.declarations().get(.. leading).unwrap_or_default();
            let mut asked = Vec::new();
            let mut runner = |constant: ConstantIndex| {
                asked.push(usize::from(constant));
                ran_at(constant)
            };
            let after = settle_after(
                CorpusRoot::Fixture,
                &module.arena,
                &module.module,
                &module.verdicts,
                &mut runner,
                earlier,
            )
            .expect("the verdicts are the module's own");
            assert_eq!(
                after, whole,
                "after {leading} leading names, the whole report"
            );
            let expected: Vec<usize> = [0_usize, 3_usize]
                .into_iter()
                .filter(|&ran| ran >= leading)
                .collect();
            assert_eq!(asked, expected, "only the later names run");
        }
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
