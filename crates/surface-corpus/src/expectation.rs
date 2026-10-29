//! The seven expectation schemas, the verdict a declaration states, and the
//! reading of a declared name's attributes into it.
//!
//! # A name states one verdict or none
//!
//! A declared name carries one expectation, a `runs` beside a `refuses`, or a
//! `runs` beside `traces` (see below). Any other two on one name — `checks`
//! beside `owes`, or one on the signature and another on the definition —
//! state no verdict:
//! [`ExpectationFault::ConflictingExpectations`] names the first two, and the
//! name is unsettled even when one of them would hold. A form that writes both
//! halves, a signed function tail, is one form with one set of attributes, read
//! once. A payload outside its schema's range — a negative `owes`, or one past
//! every ledger size — likewise states nothing, with the bytes it covers. The
//! lowering already refuses one attribute written twice; this crate refuses
//! two different expectations.
//!
//! # A run beside a refusal states both
//!
//! `@[ runs("v"), refuses("Name") ]` states that the checker refuses the
//! declaration with `Name` and that running it anyway comes to `v`: a program
//! that runs while the checker refuses it, as a loop with no measure does. The
//! two read as their conjunction, [`Outcome::RefusesRunning`], in either order.
//! The declaration settles only when both hold: the produced refusal is `Name`
//! and the runner, asked to run the refused declaration, spells `v`. It is a
//! `refuses`, so the strict root guards it as it guards any.
//!
//! # A run states its channels' webs
//!
//! `@[ runs("v"), traces(decomposes(c, web)) ]` states that running the
//! declaration comes to `v` and that the channel its fork names `c` — the
//! binder the fork writes at its protocol — plays a dialogue whose causal web
//! decomposes to `web`; `traces(primes(c, n))` states only the web's prime
//! count, as `decomposes(primes = n)` does. A `runs` beside one or more
//! `traces` reads as [`Outcome::RunsTracing`], the channels in the order
//! written. The runner is asked for a traced run, and the declaration settles
//! when the run spells `v` and each stated channel's play decomposes as
//! stated. A channel the run never forks reads `unplayed`; one forked more
//! than once reads each play's web in turn. A `traces` with no `runs` beside
//! it states no verdict ([`ExpectationFault::TraceWithoutRun`]), and one
//! whose payload is neither form states none either
//! ([`ExpectationFault::UnwrittenTrace`]).
//!
//! # A run outcome refines *checks*
//!
//! `runs("…")` states that the declaration checks, owing nothing, and that
//! running it produces the outcome the payload spells. It refines `checks`
//! rather than contradicting it, so the strict root admits it.
//!
//! `runs("spelling")` states that the declaration checks, owing nothing, and
//! that running it comes to `spelling`: the one spelling `gandr run` prints,
//! compared byte for byte. A declaration the checker accepted is run through
//! the `Runner` the caller passes to `settle`, and its outcome is _runs to_
//! what the runner spelled; one the checker did not accept keeps its produced
//! verdict — a refusal, or an obligation — so a `runs` stated over it is
//! unsettled against that verdict. Nothing is run for a declaration that states
//! no run outcome. The runner is a trait so this crate stays free of the
//! machine: the dispatcher's program implements it, and the suite here spells
//! runs by position.
//!
//! The alternative was outcome snapshots: one sidecar file per source,
//! recording each item's outcome under a digest of the source's bytes,
//! rewritten by a generator behind an environment switch. The expectation here
//! rides the declaration it is about, as `refuses` does: there is no digest to
//! refresh and no generator to run, an outcome changed by a change to the
//! language shows in the diff of the source it changes, and one name carries
//! one expectation. The choice reverses if an outcome outgrows one spelled line
//! — a structured value compared up to sharing, say — when a file of outcomes
//! beside the source would return with its own comparison.
//!
//! # A normal form refines *checks* for a rule-bearing block
//!
//! `normalizes("call ~> normal form")` on a `data` family or a `theory` block
//! states that the block checks, owing nothing, and that the engine reads
//! `call` to `normal form` under the block's rules: the reading
//! `LoweredModule::normal_form` certifies, spelled as `gandr run` spells a
//! value. The block's attributes are its operations' too, and an operation
//! reads the call under the rules of the block that holds it, so the family
//! and its operations settle together. The produced side writes the call as
//! stated, trimmed, then ` ~> `, then the engine's spelling or the reason it
//! has none, and compares the line byte for byte, so a stated normal form
//! that differs from the engine's shows both. A payload with no `~>` states no
//! verdict ([`ExpectationFault::UnwrittenNormalForm`]); a declaration refused
//! or owing has nothing to read, and one outside every rule-bearing block
//! reads that it has no rules, so either stays unsettled. Like `runs`, it
//! refines `checks`, so the strict root admits it. It is the stated half of
//! the coincidence the lowering decides: a block whose rules part is refused
//! there and reads no normal form here.
//!
//! # Under the strict root
//!
//! The strict root holds every declaration to *checks, owing nothing*. An
//! `owes` or `refuses` attribute there is not read: its first occurrence in
//! reading order is the corpus refusal the declaration produces instead of its
//! verdict. A declaration carrying neither is read as under the fixture root,
//! where the three schemas it can carry — `checks`, `runs` and `normalizes` —
//! all state that it checks, owing nothing.
//!
//! Under the strict root an `owes` or `refuses` attribute is itself a refusal:
//! `CorpusRefusal::ExpectationOutsideFixtureRoot`, classed `MalformedSource`,
//! naming the schema and the bytes it covers. The first such attribute in
//! reading order — the signature's attributes, then the definition's — stands
//! in place of whatever the declaration produced, and the declaration still
//! states _checks, owing 0_, so it is unsettled. Naming the guard's own refusal
//! in a `refuses` payload therefore settles nothing under the strict root: the
//! stated verdict there is never read from an attribute. The verdict's
//! obligations are kept, so the ledger size is unchanged by the guard.
//!
//! The refusal is owned here because this crate sits below the driver and the
//! dispatcher and is the first that knows what a root is. The alternatives were
//! reading strict-root expectations like fixture ones, which lets a regression
//! migrate into the gate by describing itself as expected, and ignoring them,
//! which leaves a misleading annotation in a gating source. The choice reverses
//! if the strict root grows an expectation that asserts something stricter than
//! _checks, owing 0_; that schema is admitted beside `checks`, as `runs` and
//! `normalizes` are.

use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_core_checker::ObligationCount;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Sign;
use gandr_surface_lowering::AttributeEntry;
use gandr_surface_lowering::RegisteredAttribute;
use gandr_surface_lowering::coincide::CallText;
use gandr_surface_syntax::ByteSpan;
use quenchant_shape::shape::Maybe;

use crate::refusal::CorpusRefusal;
use crate::refusal::RefusalName;
use crate::refusal::refusal_name;
use crate::root::CorpusRoot;
use crate::run::Channel;
use crate::run::RunSpelling;
use crate::settle::SettleFault;

quenchant_shape::reason_enum! {
    /// Why a registered attribute is no expectation schema.
    pub mod expectation_schema {
        /// The attribute states something other than a verdict.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The registry holds the attribute for another purpose.
            Unrelated,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a declaration's expectations raise no corpus refusal.
    pub mod guard {
        /// The root admits what the declaration writes.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// Every expectation the declaration carries is one its root
            /// admits.
            Admitted,
        }
    }
}

quenchant_shape::reason_enum! {
    /// Why a `normalizes` line reads no call.
    pub mod normalized_call {
        /// The line separates no call from a normal form.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// The line writes no `~>`.
            Unwritten,
        }
    }
}

/// One of the eight expectation schemas.
///
/// # Specification
/// - requires: nothing; source correspondence is established by the reader or
///   producer.
/// - ensures: A schema selects whether the declaration expects zero
///   obligations, a stated count, a named refusal, an exact run spelling or the
///   items it reads.
/// - panics: none.
/// - executable: none — The enum has no invocation at which to read a
///   registered name or declaration; `of`, `read` and `CorpusRoot::admit` carry
///   the executable observations.
///
/// # Adequacy
/// - hypothesis: L3 — source-level and payload-boundary fixtures observe the
///   interpretation at the consuming operation. Exact variants, counts,
///   membership and spans distinguish changed classifications, erased payloads
///   and inappropriate settlement; this is not a predicate over arbitrary
///   user-constructed records.
/// - witness: `expectation::tests::registered_names_select_schemas_without_order_assumptions`
/// - witness: `root::tests::the_admission_table_is_pinned`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ExpectationSchema
{
    /// `checks`: the declaration checks, owing nothing.
    Checks,
    /// `owes(n)`: the declaration checks, leaving `n` obligations.
    Owes,
    /// `refuses("Name")`: the declaration is refused with the named refusal.
    Refuses,
    /// `runs("outcome")`: the declaration checks, owing nothing, and running
    /// it produces the outcome spelled.
    Runs,
    /// `normalizes("call ~> normal form")`: the block checks, owing nothing,
    /// and its rules read the call to the normal form spelled.
    Normalizes,
    /// `decomposes(web)`: the dialogue checks, owing nothing, and its causal
    /// web decomposes to the web written.
    Decomposes,
    /// `traces(decomposes(c, web))`: beside a `runs`, the channel the run's
    /// fork names `c` plays a dialogue whose web decomposes to the web
    /// written.
    Traces,
    /// `reads(names)`: the declaration checks, owing nothing, and mentions
    /// exactly the items named, `()` when it mentions none.
    Reads,
}

impl ExpectationSchema
{
    /// The schema `attribute` names, when it names one.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `checks`, `owes`, `refuses`, `runs`, `normalizes`,
    ///   `decomposes`, `traces` and `reads` name their schemas; any other
    ///   registered attribute names none.
    /// - provides: the filter that decides which attributes state a verdict.
    /// - fails: never; an attribute stating something else is the
    ///   [`expectation_schema::Absent::Unrelated`] absence.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each registered expectation name resolves
    ///   independently of registry ordering, and each formatted schema resolves
    ///   back to the same schema. Swapped names and altered case or spelling
    ///   change the observation. The registry currently exposes no unrelated
    ///   name, so that future branch has a predicate but no reachable witness.
    /// - witness: `expectation::tests::registered_names_select_schemas_without_order_assumptions`
    #[spec(
        ensures: |ret| match (attribute.as_ref(), ret) {
    ("checks", Maybe::Present(Self::Checks))
    | ("owes", Maybe::Present(Self::Owes))
    | ("refuses", Maybe::Present(Self::Refuses))
    | ("runs", Maybe::Present(Self::Runs))
    | ("normalizes", Maybe::Present(Self::Normalizes))
    | ("decomposes", Maybe::Present(Self::Decomposes))
    | ("traces", Maybe::Present(Self::Traces))
    | ("reads", Maybe::Present(Self::Reads)) => true,
    (name, Maybe::Absent(expectation_schema::Absent::Unrelated)) => {
        !matches!(name, "checks" | "owes" | "refuses" | "runs" | "normalizes" | "decomposes" | "traces" | "reads")
    }
    _ => false,
},
    )]
    #[inline]
    pub fn of(attribute: RegisteredAttribute) -> Maybe<Self, expectation_schema::Absent>
    {
        let spelled: &str = attribute.as_ref();
        match spelled {
            "checks" => Maybe::Present(Self::Checks),
            "owes" => Maybe::Present(Self::Owes),
            "refuses" => Maybe::Present(Self::Refuses),
            "runs" => Maybe::Present(Self::Runs),
            "normalizes" => Maybe::Present(Self::Normalizes),
            "decomposes" => Maybe::Present(Self::Decomposes),
            "traces" => Maybe::Present(Self::Traces),
            "reads" => Maybe::Present(Self::Reads),
            _ => Maybe::Absent(expectation_schema::Absent::Unrelated),
        }
    }
}

impl fmt::Display for ExpectationSchema
{
    /// Writes the attribute name the schema is registered under.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the canonical registered name for the schema.
    /// - fails: propagates a refusing output sink as `fmt::Error`.
    /// - panics: none.
    /// - executable: none — the formatter exposes neither emitted text nor
    ///   readable sink state; successful output and a refusing sink are
    ///   observed by the witnesses.
    ///
    /// # Errors
    /// Returns `fmt::Error` when the output sink refuses a write.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each variant with distinct nonempty spans, counts or
    ///   a non-ASCII spelling. The observation retains semantic payloads and
    ///   distinguishes fault kinds without pinning sentence wording; every
    ///   branch propagates an exact sink refusal.
    /// - witness: `expectation::tests::registered_names_select_schemas_without_order_assumptions`
    /// - witness: `expectation::tests::expectation_formatters_retain_payloads_and_sink_failures`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            Self::Checks => "checks",
            Self::Owes => "owes",
            Self::Refuses => "refuses",
            Self::Runs => "runs",
            Self::Normalizes => "normalizes",
            Self::Decomposes => "decomposes",
            Self::Traces => "traces",
            Self::Reads => "reads",
        })
    }
}

/// A verdict as the settle comparison reads it: what a declaration states,
/// and what it produced, in one shape.
///
/// # Specification
/// - requires: nothing; source correspondence is established by the reader or
///   producer.
/// - ensures: Verdict equality distinguishes the outcome variant and its exact
///   count, refusal name or run spelling.
/// - panics: none.
/// - executable: none — The enum carries a comparison value, not the checker,
///   declaration or execution context that produced it; settlement specifies
///   the comparison at its call boundary.
///
/// # Adequacy
/// - hypothesis: L3 — source-level and payload-boundary fixtures observe the
///   interpretation at the consuming operation. Exact variants, counts,
///   membership and spans distinguish changed classifications, erased payloads
///   and inappropriate settlement; this is not a predicate over arbitrary
///   user-constructed records.
/// - witness: `settle::tests::a_wrong_stated_verdict_is_unsettled_either_way`
/// - witness: `settle::tests::a_run_outcome_settles_under_either_root`
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Outcome
{
    /// The declaration checks, leaving this many obligations in the ledger.
    Checks(ObligationCount),
    /// The declaration is refused with the named refusal.
    Refuses(RefusalName),
    /// The declaration checks, owing nothing, and running it produces the
    /// outcome spelled.
    Runs(RunSpelling),
    /// The block checks, owing nothing, and its rules read a call to a normal
    /// form: the line `call ~> normal form`.
    Normalizes(RunSpelling),
    /// The dialogue checks, owing nothing, and its causal web decomposes to
    /// the web spelled.
    Decomposes(RunSpelling),
    /// The declaration is refused with the named refusal, and running it
    /// anyway produces the outcome spelled: a program that runs while the
    /// checker refuses it.
    RefusesRunning(RefusalName, RunSpelling),
    /// The declaration checks, owing nothing, running it produces the outcome
    /// spelled, and each channel named plays a dialogue whose web decomposes
    /// to the web spelled beside it.
    RunsTracing(RunSpelling, Vec<Channel>),
    /// The declaration checks, owing nothing, and mentions exactly the items
    /// spelled: `()`, one name, or a tuple of names.
    Reads(RunSpelling),
}

impl fmt::Display for Outcome
{
    /// Writes `checks owing n`, `refuses Name`, `runs to outcome`,
    /// `normalizes call ~> normal form`, `decomposes to web`,
    /// `refuses Name and runs to outcome`, `runs to outcome tracing c to
    /// web, …` or `reads names`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the verdict kind and its count, refusal name, run
    ///   spelling or normalization line, or the refusal name and the run
    ///   spelling together.
    /// - fails: propagates a refusing output sink as `fmt::Error`.
    /// - panics: none.
    /// - executable: none — the formatter exposes neither emitted text nor
    ///   readable sink state; successful output and a refusing sink are
    ///   observed by the witnesses.
    ///
    /// # Errors
    /// Returns `fmt::Error` when the output sink refuses a write.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each variant with distinct nonempty spans, counts or
    ///   a non-ASCII spelling. The observation retains semantic payloads and
    ///   distinguishes fault kinds without pinning sentence wording; every
    ///   branch propagates an exact sink refusal.
    /// - witness: `expectation::tests::expectation_formatters_retain_payloads_and_sink_failures`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Checks(owed) => write!(f, "checks owing {owed}"),
            Self::Refuses(name) => write!(f, "refuses {name}"),
            Self::Runs(ref spelled) => write!(f, "runs to {spelled}"),
            Self::Normalizes(ref spelled) => write!(f, "normalizes {spelled}"),
            Self::Decomposes(ref spelled) => write!(f, "decomposes to {spelled}"),
            Self::RefusesRunning(name, ref spelled) => {
                write!(f, "refuses {name} and runs to {spelled}")
            },
            Self::RunsTracing(ref spelled, ref channels) => {
                write!(f, "runs to {spelled} tracing")?;
                let mut separator = " ";
                for channel in channels {
                    write!(f, "{separator}{} to {}", channel.name, channel.web)?;
                    separator = ", ";
                }
                Ok(())
            },
            Self::Reads(ref spelled) => write!(f, "reads {spelled}"),
        }
    }
}

/// What a declaration states.
///
/// # Specification
/// - requires: nothing; source correspondence is established by the reader or
///   producer.
/// - ensures: A malformed expectation states no verdict and cannot settle
///   against a produced outcome.
/// - panics: none.
/// - executable: none — There is no produced outcome at this enum declaration;
///   `DeclarationReport::settlement` expresses the comparison as a predicate.
///
/// # Adequacy
/// - hypothesis: L3 — source-level and payload-boundary fixtures observe the
///   interpretation at the consuming operation. Exact variants, counts,
///   membership and spans distinguish changed classifications, erased payloads
///   and inappropriate settlement; this is not a predicate over arbitrary
///   user-constructed records.
/// - witness: `settle::tests::a_refusal_outside_the_vocabulary_fails_the_fixture`
/// - witness: `settle::tests::a_name_carrying_two_expectations_states_none`
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Stated
{
    /// A verdict: the one its expectation writes, or checks owing nothing when
    /// it writes none.
    Verdict(Outcome),
    /// An expectation naming no verdict, which no production settles.
    Malformed(ExpectationFault),
}

impl fmt::Display for Stated
{
    /// Writes the stated verdict, or why the expectation states none.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the verdict or the reason no verdict is stated.
    /// - fails: propagates a refusing output sink as `fmt::Error`.
    /// - panics: none.
    /// - executable: none — the formatter exposes neither emitted text nor
    ///   readable sink state; successful output and a refusing sink are
    ///   observed by the witnesses.
    ///
    /// # Errors
    /// Returns `fmt::Error` when the output sink refuses a write.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each variant with distinct nonempty spans, counts or
    ///   a non-ASCII spelling. The observation retains semantic payloads and
    ///   distinguishes fault kinds without pinning sentence wording; every
    ///   branch propagates an exact sink refusal.
    /// - witness: `expectation::tests::expectation_formatters_retain_payloads_and_sink_failures`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Verdict(ref outcome) => fmt::Display::fmt(outcome, f),
            Self::Malformed(fault) => write!(f, "no verdict, {fault}"),
        }
    }
}

/// Why an expectation names no verdict.
///
/// # Specification
/// - requires: nothing; source correspondence is established by the reader or
///   producer.
/// - ensures: Distinguishes unknown refusal names, negative counts,
///   unrepresentable counts, unwritten normal forms and conflicting
///   expectations, preserving the source positions of each cause.
/// - panics: none.
/// - executable: none — The source and attempted interpretation are not stored
///   in this enum; the reader predicates and source fixtures establish the
///   cause and provenance.
///
/// # Adequacy
/// - hypothesis: L3 — source-level and payload-boundary fixtures observe the
///   interpretation at the consuming operation. Exact variants, counts,
///   membership and spans distinguish changed classifications, erased payloads
///   and inappropriate settlement; this is not a predicate over arbitrary
///   user-constructed records.
/// - witness: `expectation::tests::an_owes_payload_outside_the_counts_states_no_verdict`
/// - witness: `expectation::tests::guard_and_conflict_precedence_preserve_the_first_spans`
/// - witness: `settle::tests::a_refusal_outside_the_vocabulary_fails_the_fixture`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ExpectationFault
{
    /// A `refuses` payload spelling no name of the closed refusal vocabulary.
    UnknownRefusal
    {
        /// The bytes the attribute covers.
        span: ByteSpan,
    },
    /// An `owes` payload below zero.
    NegativeObligations
    {
        /// The bytes the attribute covers.
        span: ByteSpan,
    },
    /// An `owes` payload past every count a ledger can hold.
    ObligationsBeyondRange
    {
        /// The bytes the attribute covers.
        span: ByteSpan,
    },
    /// A second expectation on a name that already carries one.
    ConflictingExpectations
    {
        /// The bytes the first expectation covers.
        first: ByteSpan,
        /// The bytes the second expectation covers.
        second: ByteSpan,
    },
    /// A `normalizes` payload writing no `~>` between a call and its normal
    /// form.
    UnwrittenNormalForm
    {
        /// The bytes the attribute covers.
        span: ByteSpan,
    },
    /// A `decomposes` payload that is no web: no `series`, `parallel`,
    /// `prime` or `event` node.
    UnwrittenWeb
    {
        /// The bytes the attribute covers.
        span: ByteSpan,
    },
    /// A `traces` payload that is neither `decomposes(c, web)` over a web
    /// node nor `primes(c, n)` over a count.
    UnwrittenTrace
    {
        /// The bytes the attribute covers.
        span: ByteSpan,
    },
    /// A `traces` with no `runs` beside it: a channel of no stated run.
    TraceWithoutRun
    {
        /// The bytes the first `traces` covers.
        span: ByteSpan,
    },
    /// A `reads` payload that is neither `()`, one name, nor a tuple of
    /// names.
    UnwrittenReads
    {
        /// The bytes the attribute covers.
        span: ByteSpan,
    },
}

impl fmt::Display for ExpectationFault
{
    /// Writes the fault without the bytes it names: a diagnostic locates the
    /// attribute through the fault's spans instead.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the fault kind and no source span.
    /// - fails: propagates a refusing output sink as `fmt::Error`.
    /// - panics: none.
    /// - executable: none — the formatter exposes neither emitted text nor
    ///   readable sink state; successful output and a refusing sink are
    ///   observed by the witnesses.
    ///
    /// # Errors
    /// Returns `fmt::Error` when the output sink refuses a write.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each variant with distinct nonempty spans, counts or
    ///   a non-ASCII spelling. The observation distinguishes fault kinds and
    ///   omits every span without pinning sentence wording; every branch
    ///   propagates an exact sink refusal.
    /// - witness: `expectation::tests::expectation_formatters_retain_payloads_and_sink_failures`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::UnknownRefusal { .. } => f.write_str("the `refuses` payload names no refusal"),
            Self::NegativeObligations { .. } => f.write_str("the `owes` payload is below zero"),
            Self::ObligationsBeyondRange { .. } => {
                f.write_str("the `owes` payload is past every ledger size")
            },
            Self::ConflictingExpectations { .. } => {
                f.write_str("the expectation contradicts an earlier one")
            },
            Self::UnwrittenNormalForm { .. } => {
                f.write_str("the `normalizes` payload writes no `~>` before a normal form")
            },
            Self::UnwrittenWeb { .. } => f.write_str(
                "the `decomposes` payload is no `series`, `parallel`, `prime` or `event` node",
            ),
            Self::UnwrittenTrace { .. } => f.write_str(
                "the `traces` payload is no `decomposes(channel, web)` or `primes(channel, n)`",
            ),
            Self::TraceWithoutRun { .. } => {
                f.write_str("the `traces` states a channel of no run: it needs a `runs` beside it")
            },
            Self::UnwrittenReads { .. } => {
                f.write_str("the `reads` payload is no `()`, name or tuple of names")
            },
        }
    }
}

/// Whether a declaration is a fixture.
///
/// # Specification
/// - requires: nothing; source correspondence is established by the reader or
///   producer.
/// - ensures: A reader-produced fixture has an expectation attribute; an
///   unattributed declaration states checks owing nothing.
/// - panics: none.
/// - executable: none — An enum value has neither attributes nor a stated
///   verdict to inspect; `read` establishes the relationship at its call
///   boundary.
///
/// # Adequacy
/// - hypothesis: L3 — source-level and payload-boundary fixtures observe the
///   interpretation at the consuming operation. Exact variants, counts,
///   membership and spans distinguish changed classifications, erased payloads
///   and inappropriate settlement; this is not a predicate over arbitrary
///   user-constructed records.
/// - witness: `expectation::tests::missing_and_nonliteral_payloads_fail_but_checks_needs_none`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Membership
{
    /// It carries an expectation attribute, so the report gives it a line of
    /// its own.
    Fixture,
    /// It carries none, and states checks owing nothing.
    Unattributed,
}

/// What one declared name's expectation attributes amount to under a root.
///
/// # Specification
/// - requires: nothing; source correspondence is established by the reader or
///   producer.
/// - ensures: For a reader-produced record, root guards precede conflict and
///   payload interpretation; unattributed and guarded declarations state checks
///   owing nothing.
/// - panics: none.
/// - executable: none — The record exposes fields but holds no original
///   attributes, iterator or root; `read` supplies executable result invariants
///   and the fixtures observe input correspondence.
///
/// # Adequacy
/// - hypothesis: L3 — source-level and payload-boundary fixtures observe the
///   interpretation at the consuming operation. Exact variants, counts,
///   membership and spans distinguish changed classifications, erased payloads
///   and inappropriate settlement; this is not a predicate over arbitrary
///   user-constructed records.
/// - witness: `expectation::tests::guard_and_conflict_precedence_preserve_the_first_spans`
/// - witness: `expectation::tests::missing_and_nonliteral_payloads_fail_but_checks_needs_none`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Expectations
{
    /// Whether the name carries an expectation attribute.
    pub membership: Membership,
    /// The verdict the name states.
    pub stated: Stated,
    /// The refusal the root raises against an expectation it does not admit.
    pub guard: Maybe<CorpusRefusal, guard::Absent>,
}

impl Expectations
{
    /// What a name carrying no expectation states: unattributed, checks owing
    /// nothing, unguarded.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn unattributed() -> Self
    {
        Self {
            membership: Membership::Unattributed,
            stated: owing_nothing(),
            guard: Maybe::Absent(guard::Absent::Admitted),
        }
    }
}

/// Read the expectations among `attributes` under `root`, their payloads out
/// of `arena` or, for a payload written unquoted, out of `spelled`.
///
/// # Specification
/// - requires: `attributes` are the entries filed under one declared name, the
///   signature's before the definition's; `arena` is the arena the lowering
///   minted their payloads into, and `spelled` answers the spelling the
///   lowering filed beside an entry whose payload it read unquoted.
/// - ensures: with no expectation, an unattributed name stating checks owing
///   nothing, unguarded. Otherwise a fixture: guarded by the first expectation
///   in reading order its root does not admit — under the strict root an `owes`
///   or a `refuses` — and then stating checks owing nothing with no payload
///   read; unguarded, stating its one expectation's verdict, the two together
///   when it carries exactly a `runs` and a `refuses`, in either order, the run
///   and its channels when it carries `traces` as [`traced`] reads them, or
///   [`ExpectationFault::ConflictingExpectations`] naming the first two when it
///   carries any other pair or more than two.
/// - provides: the stated side of the settle comparison.
/// - fails: [`SettleFault::UnreadablePayload`] when the one payload read is
///   absent from `arena`, or is not its schema's literal, or a `decomposes`
///   entry has no spelling.
/// - panics: none.
///
/// # Errors
/// [`SettleFault::UnreadablePayload`] when an `owes`, `refuses`, `runs` or
/// `normalizes` payload is not an integer or a text literal of `arena`, or a
/// `decomposes` payload was filed with no spelling.
///
/// # Adequacy
/// - hypothesis: L3 — all six schemas under both roots; negative, zero, maximal
///   and overflowing obligation counts; missing and wrong-kind payloads;
///   absent, single, composed and conflicting expectations. Exact membership,
///   verdict, guard and source spans distinguish changed defaults, wrong schema
///   readings and error-precedence changes. The iterator is consumed once, so
///   its original sequence is observed by the fixtures, not replayed in the
///   postcondition.
/// - witness: `expectation::tests::an_owes_payload_outside_the_counts_states_no_verdict`
/// - witness: `expectation::tests::a_payload_the_arena_does_not_hold_is_unreadable`
/// - witness: `expectation::tests::guard_and_conflict_precedence_preserve_the_first_spans`
/// - witness: `expectation::tests::missing_and_nonliteral_payloads_fail_but_checks_needs_none`
/// - witness: `settle::tests::a_refusal_outside_the_vocabulary_fails_the_fixture`
/// - witness: `settle::tests::a_name_carrying_two_expectations_states_none`
/// - witness: `settle::tests::a_run_outcome_settles_under_either_root`
/// - witness: `expectation::tests::a_run_beside_a_refusal_states_both`
#[spec(
    ensures: |ret| match ret {
    Ok(ref expectations) => {
        match expectations.guard {
            Maybe::Present(
                CorpusRefusal::ExpectationOutsideFixtureRoot { schema, .. },
            ) => {
                root == CorpusRoot::Strict
                    && matches!(
                        schema, ExpectationSchema::Owes | ExpectationSchema::Refuses
                    ) && expectations.membership == Membership::Fixture
                    && expectations.stated == owing_nothing()
            }
            Maybe::Absent(guard::Absent::Admitted) => {
                (expectations.membership != Membership::Unattributed
                    || expectations.stated == owing_nothing())
                    && (root != CorpusRoot::Strict
                        || !matches!(
                            expectations.stated,
                            Stated::Verdict(Outcome::Refuses(_) | Outcome::RefusesRunning(..))
                        ))
                    && (root != CorpusRoot::Strict
                        || !matches!(
                            expectations.stated, Stated::Verdict(Outcome::Checks(count))
                            if usize::from(count) != 0_usize
                        ))
            }
            Maybe::Present(CorpusRefusal::BoundaryUnrealised { .. }) => false,
        }
    }
    Err(fault) => matches!(fault, SettleFault::UnreadablePayload { .. }),
},
)]
#[inline]
pub fn read<'entry, Entries, Spell>(
    root: CorpusRoot,
    attributes: Entries,
    arena: &CoreArena,
    spelled: Spell,
) -> Result<Expectations, SettleFault>
where
    Entries: Iterator<Item = &'entry AttributeEntry>,
    Spell: Fn(&AttributeEntry) -> Option<RunSpelling>,
{
    let written: Vec<(ExpectationSchema, &AttributeEntry)> = attributes
        .filter_map(|entry| match ExpectationSchema::of(entry.name()) {
            Maybe::Present(schema) => Some((schema, entry)),
            Maybe::Absent(expectation_schema::Absent::Unrelated) => None,
        })
        .collect();
    let Some(&(schema, entry)) = written.first()
    else {
        return Ok(Expectations::unattributed());
    };
    if let Some(refusal) = written
        .iter()
        .find_map(|&(schema, entry)| root.admit(schema, entry.span()).err())
    {
        return Ok(Expectations {
            membership: Membership::Fixture,
            stated: owing_nothing(),
            guard: Maybe::Present(refusal),
        });
    }
    let stated = if written
        .iter()
        .any(|&(schema, _)| schema == ExpectationSchema::Traces)
    {
        traced(&written, arena, &spelled)?
    }
    else {
        match *written.as_slice() {
            [
                (ExpectationSchema::Runs, ran),
                (ExpectationSchema::Refuses, refused),
            ]
            | [
                (ExpectationSchema::Refuses, refused),
                (ExpectationSchema::Runs, ran),
            ] => {
                let spelled = run_spelled(ran, arena)?;
                match refusal_named(refused, arena)? {
                    Maybe::Present(name) => Stated::Verdict(Outcome::RefusesRunning(name, spelled)),
                    Maybe::Absent(refusal_name::Absent::Unnamed) => {
                        Stated::Malformed(ExpectationFault::UnknownRefusal {
                            span: refused.span(),
                        })
                    },
                }
            },
            [_, (_, second), ..] => Stated::Malformed(ExpectationFault::ConflictingExpectations {
                first: entry.span(),
                second: second.span(),
            }),
            [_] | [] => stated_by(schema, entry, arena, spelled(entry).as_ref())?,
        }
    };
    Ok(Expectations {
        membership: Membership::Fixture,
        stated,
        guard: Maybe::Absent(guard::Absent::Admitted),
    })
}

/// The verdict one expectation of `schema` states, its payload read out of
/// `arena`, or `spelled` for a payload written unquoted.
///
/// # Specification
/// - requires: `entry` belongs to the declaration being read; the caller
///   supplies its payload arena and the spelling filed beside it.
/// - ensures: `checks` states zero obligations without a payload; `owes` reads
///   an integer count; `refuses` resolves an exact vocabulary spelling or
///   reports its unknown name; `runs` preserves the text payload; `normalizes`
///   preserves a text payload that writes `~>` and reports one that does not;
///   `decomposes` preserves a spelling that is a `series`, `parallel`, `prime`
///   or `event` node, or a prime count `primes = n`, and reports one that is
///   neither; `reads` preserves a spelling that is `()`, a name or a tuple of
///   names, and reports one that is none of them; a `traces` read alone states
///   no verdict, a channel of no run. Malformed counts, names, lines, webs and
///   reads retain the attribute span.
/// - fails: `UnreadablePayload` at the attribute span for an absent or
///   wrong-kind payload required by the schema, or a `decomposes` or `reads`
///   with no spelling.
/// - panics: none.
///
/// # Errors
/// [`SettleFault::UnreadablePayload`] when the payload is not the schema's
/// literal of `arena`, or a `decomposes` or `reads` payload has no spelling.
///
/// # Adequacy
/// - hypothesis: L3 — integer boundaries, exact refusal names and a near miss,
///   and differing run spellings, beside absent and wrong-kind literal
///   payloads. Exact verdicts and fault spans distinguish schema swaps, payload
///   loss and treating malformed input as a verdict.
/// - witness: `expectation::tests::an_owes_payload_outside_the_counts_states_no_verdict`
/// - witness: `expectation::tests::missing_and_nonliteral_payloads_fail_but_checks_needs_none`
/// - witness: `settle::tests::a_refusal_outside_the_vocabulary_fails_the_fixture`
/// - witness: `settle::tests::a_normal_form_settles_against_the_engines_reading`
/// - witness: `run::tests::run_mismatches_expose_both_spellings_and_preserve_sink_refusal`
/// - witness: `settle::tests::a_web_settles_against_the_dialogue_s_decomposition_2077`
/// - witness: `settle::tests::a_reads_claim_settles_against_the_items_read_2520`
#[spec(
    ensures: |ret| {
    let unreadable = SettleFault::UnreadablePayload {
        span: entry.span(),
    };
    if schema == ExpectationSchema::Checks {
        ret == Ok(owing_nothing())
    } else if schema == ExpectationSchema::Decomposes {
        match spelled {
            None => ret == Err(unreadable),
            Some(web) if (WEB_NODES.iter().any(|node| web.as_ref().starts_with(node)) && web.as_ref().ends_with(')'))
                || web.as_ref().strip_prefix(PRIMES).is_some_and(|count| !count.is_empty() && count.bytes().all(|digit| digit.is_ascii_digit())) => {
                matches!(ret, Ok(Stated::Verdict(Outcome::Decomposes(ref stated))) if stated == web)
            }
            Some(_) => ret == Ok(Stated::Malformed(ExpectationFault::UnwrittenWeb { span: entry.span() })),
        }
    } else if schema == ExpectationSchema::Reads {
        match spelled {
            None => ret == Err(unreadable),
            Some(names) if matches!(read_names(names), Maybe::Present(_)) => {
                matches!(ret, Ok(Stated::Verdict(Outcome::Reads(ref stated))) if stated == names)
            }
            Some(_) => ret == Ok(Stated::Malformed(ExpectationFault::UnwrittenReads { span: entry.span() })),
        }
    } else if schema == ExpectationSchema::Traces {
        ret == Ok(Stated::Malformed(ExpectationFault::TraceWithoutRun { span: entry.span() }))
    } else {
        payload(entry, arena)
            .map_or_else(
                |_| ret == Err(unreadable),
                |literal| match *literal {
                    Literal::Integer(
                        ref integer,
                    ) if schema == ExpectationSchema::Owes => {
                        ret == Ok(obligations(integer, entry.span()))
                    }
                    Literal::Text(ref text) if schema == ExpectationSchema::Refuses => {
                        match ret {
                            Ok(Stated::Verdict(Outcome::Refuses(name))) => {
                                RefusalName::named_by(text) == Maybe::Present(name)
                            }
                            Ok(
                                Stated::Malformed(ExpectationFault::UnknownRefusal { span }),
                            ) => {
                                span == entry.span()
                                    && matches!(
                                        RefusalName::named_by(text),
                                        Maybe::Absent(refusal_name::Absent::Unnamed)
                                    )
                            }
                            _ => false,
                        }
                    }
                    Literal::Text(ref text) if schema == ExpectationSchema::Runs => {
                        matches!(
                            ret, Ok(Stated::Verdict(Outcome::Runs(ref spelled))) if
                            spelled.as_ref() == text.as_ref()
                        )
                    }
                    Literal::Text(ref text) if schema == ExpectationSchema::Normalizes => {
                        match ret {
                            Ok(Stated::Verdict(Outcome::Normalizes(ref spelled))) => {
                                spelled.as_ref() == text.as_ref()
                                    && matches!(normalized_call(text), Maybe::Present(_))
                            }
                            Ok(Stated::Malformed(ExpectationFault::UnwrittenNormalForm { span })) => {
                                span == entry.span()
                                    && matches!(normalized_call(text), Maybe::Absent(_))
                            }
                            _ => false,
                        }
                    }
                    Literal::Integer(_) | Literal::Text(_) | Literal::Numeric(_) | Literal::Character(_) | Literal::Float64(_) | Literal::Fixed(_) => ret == Err(unreadable),
                },
            )
    }
},
)]
fn stated_by(
    schema: ExpectationSchema,
    entry: &AttributeEntry,
    arena: &CoreArena,
    spelled: Option<&RunSpelling>,
) -> Result<Stated, SettleFault>
{
    let span = entry.span();
    let unreadable = SettleFault::UnreadablePayload { span };
    match schema {
        ExpectationSchema::Checks => Ok(owing_nothing()),
        ExpectationSchema::Owes => {
            let literal = payload(entry, arena)?;
            let Literal::Integer(ref integer) = *literal
            else {
                return Err(unreadable);
            };
            Ok(obligations(integer, span))
        },
        ExpectationSchema::Refuses => Ok(match refusal_named(entry, arena)? {
            Maybe::Present(name) => Stated::Verdict(Outcome::Refuses(name)),
            Maybe::Absent(refusal_name::Absent::Unnamed) => {
                Stated::Malformed(ExpectationFault::UnknownRefusal { span })
            },
        }),
        ExpectationSchema::Runs => Ok(Stated::Verdict(Outcome::Runs(run_spelled(entry, arena)?))),
        ExpectationSchema::Normalizes => {
            let literal = payload(entry, arena)?;
            let Literal::Text(ref text) = *literal
            else {
                return Err(unreadable);
            };
            Ok(match normalized_call(text) {
                Maybe::Present(_) => Stated::Verdict(Outcome::Normalizes(RunSpelling::from(
                    String::from(text.as_ref()),
                ))),
                Maybe::Absent(normalized_call::Absent::Unwritten) => {
                    Stated::Malformed(ExpectationFault::UnwrittenNormalForm { span })
                },
            })
        },
        ExpectationSchema::Decomposes => {
            let web = spelled.ok_or(unreadable)?;
            let written = WEB_NODES.iter().any(|node| web.as_ref().starts_with(node))
                && web.as_ref().ends_with(')');
            let counted = web.as_ref().strip_prefix(PRIMES).is_some_and(|count| {
                !count.is_empty() && count.bytes().all(|digit| digit.is_ascii_digit())
            });
            Ok(if written || counted {
                Stated::Verdict(Outcome::Decomposes(web.clone()))
            }
            else {
                Stated::Malformed(ExpectationFault::UnwrittenWeb { span })
            })
        },
        ExpectationSchema::Reads => {
            let names = spelled.ok_or(unreadable)?;
            Ok(match read_names(names) {
                Maybe::Present(_) => Stated::Verdict(Outcome::Reads(names.clone())),
                Maybe::Absent(read_names::Absent::Unwritten) => {
                    Stated::Malformed(ExpectationFault::UnwrittenReads { span })
                },
            })
        },
        ExpectationSchema::Traces => Ok(Stated::Malformed(ExpectationFault::TraceWithoutRun {
            span,
        })),
    }
}

/// The node openings a `decomposes` payload begins with: the modular
/// decomposition's series, parallel and prime nodes, and a leaf event.
const WEB_NODES: [&str; 4] = ["series(", "parallel(", "prime(", "event("];

/// The opening of a `decomposes` payload that states only the web's prime
/// count, `primes = 2`.
const PRIMES: &str = "primes = ";

quenchant_shape::reason_enum! {
    /// Why a `reads` spelling names no items.
    mod read_names {
        /// The spelling is no `()`, name or tuple of names.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// It is none of the three forms.
            Unwritten,
        }
    }
}

/// The items a `reads` spelling names, each once.
#[derive(Clone, Debug, Eq, PartialEq)]
#[repr(transparent)]
struct ReadNames<'spelled>(BTreeSet<&'spelled str>);

/// The items `spelled` names, read as a `reads` payload writes them: none
/// for `()`, the one a bare name writes, and each component of a tuple of
/// names.
///
/// # Specification
/// - requires: nothing.
/// - ensures: present exactly when `spelled` is `()`, one name, or names
///   between parentheses separated by commas, each name nonempty and holding no
///   white space, comma or parenthesis; each name written is held once.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the three forms and a repeated name read, and an empty
///   component, a nested tuple and a phrase refused.
/// - witness: `expectation::tests::a_reads_payload_names_each_item_once_2520`
#[spec(ensures: |ret| match ret {
    Maybe::Present(ref names) => names.0.iter().all(|name| !name.is_empty() && name.chars().all(|glyph| !glyph.is_whitespace() && !matches!(glyph, ',' | '(' | ')'))),
    Maybe::Absent(_) => true,
})]
fn read_names(spelled: &RunSpelling) -> Maybe<ReadNames<'_>, read_names::Absent>
{
    let text: &str = spelled.as_ref();
    let components: Vec<&str> = match text
        .strip_prefix('(')
        .and_then(|rest| rest.strip_suffix(')'))
    {
        Some("") => Vec::new(),
        Some(inner) => inner.split(',').map(str::trim).collect(),
        None => Vec::from([text]),
    };
    let named = components.iter().all(|name| {
        !name.is_empty()
            && name
                .chars()
                .all(|glyph| !glyph.is_whitespace() && !matches!(glyph, ',' | '(' | ')'))
    });
    if named {
        Maybe::Present(ReadNames(components.into_iter().collect()))
    }
    else {
        Maybe::Absent(read_names::Absent::Unwritten)
    }
}

/// `produced` as the `reads` payload `stated` reads it: `stated` itself when
/// both name the same items, in whatever order and however often, and
/// `produced` otherwise.
///
/// # Specification
/// - requires: `produced` is a spelling the runner gave for what a declaration
///   reads.
/// - ensures: `stated` when both spellings read as names and the two sets are
///   equal; `produced` otherwise.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the same items in another order, one item fewer and a
///   produced spelling that names no items.
/// - witness: `expectation::tests::a_reads_payload_names_each_item_once_2520`
/// - witness: `settle::tests::a_reads_claim_settles_against_the_items_read_2520`
#[spec(ensures: |ret| ret == *stated || ret == *produced)]
#[must_use]
pub fn reads_as_stated(
    stated: &RunSpelling,
    produced: &RunSpelling,
) -> RunSpelling
{
    match (read_names(stated), read_names(produced)) {
        (Maybe::Present(written), Maybe::Present(read)) if written == read => stated.clone(),
        (Maybe::Present(_) | Maybe::Absent(_), _) => produced.clone(),
    }
}

/// The `reads` spelling of `names`: `()` for none, the name itself for one,
/// and the names between parentheses, in ascending order and each once,
/// separated by `, ` for more.
///
/// # Specification
/// - requires: no name is empty or holds white space, a comma or a parenthesis.
/// - ensures: a spelling a `reads` payload writes, naming exactly `names`.
/// - provides: the produced side of a `reads` comparison, spelled as the
///   payload is written.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — none, one and several names, one of them repeated, read
///   back.
/// - witness: `expectation::tests::a_reads_payload_names_each_item_once_2520`
#[spec(ensures: |ref ret| matches!(read_names(ret), Maybe::Present(_)))]
#[inline]
#[must_use]
pub fn reads_spelled<Names, Name>(names: Names) -> RunSpelling
where
    Names: IntoIterator<Item = Name>,
    Name: AsRef<str>,
{
    let held: Vec<Name> = names.into_iter().collect();
    let sorted: BTreeSet<&str> = held.iter().map(AsRef::as_ref).collect();
    let mut spelled = String::new();
    if sorted.len() == 1_usize {
        spelled.extend(sorted.first().copied());
    }
    else {
        spelled.push('(');
        for (index, name) in sorted.iter().enumerate() {
            if index > 0_usize {
                spelled.push_str(", ");
            }
            spelled.push_str(name);
        }
        spelled.push(')');
    }
    RunSpelling::from(spelled)
}

/// What a name carrying `traces` among `written` states: the run its one
/// `runs` spells, and each channel a `traces` names, in the order written.
///
/// # Specification
/// - requires: `written` holds a `traces`, its entries in reading order;
///   `spelled` answers the spelling the lowering filed beside each.
/// - ensures: [`ExpectationFault::ConflictingExpectations`] naming the first
///   two entries when one is neither a `runs` nor a `traces`, or there are two
///   `runs`; else [`ExpectationFault::UnwrittenTrace`] at the first `traces`
///   whose payload names no channel; else [`ExpectationFault::TraceWithoutRun`]
///   at the first `traces` when no `runs` stands beside them; else
///   [`Outcome::RunsTracing`] of the run and the channels.
/// - fails: as [`run_spelled`].
/// - panics: none.
/// - executable: none — the clause is the body's walk.
///
/// # Errors
/// [`SettleFault::UnreadablePayload`] when the `runs` payload is no text
/// literal of `arena`.
///
/// # Adequacy
/// - hypothesis: L3 — a run beside two channels, one stated by its prime count;
///   a `traces` alone; one beside a `checks`; a payload of neither form.
/// - witness: `expectation::tests::a_run_beside_traces_states_its_channels_3338`
fn traced<Spell>(
    written: &[(ExpectationSchema, &AttributeEntry)],
    arena: &CoreArena,
    spelled: &Spell,
) -> Result<Stated, SettleFault>
where
    Spell: Fn(&AttributeEntry) -> Option<RunSpelling>,
{
    let runs: Vec<&AttributeEntry> = written
        .iter()
        .filter(|&&(schema, _)| schema == ExpectationSchema::Runs)
        .map(|&(_, entry)| entry)
        .collect();
    let foreign = written
        .iter()
        .any(|&(schema, _)| !matches!(schema, ExpectationSchema::Runs | ExpectationSchema::Traces));
    if (foreign || runs.len() > 1)
        && let [(_, first), (_, second), ..] = *written
    {
        return Ok(Stated::Malformed(
            ExpectationFault::ConflictingExpectations {
                first: first.span(),
                second: second.span(),
            },
        ));
    }
    let mut channels = Vec::new();
    let mut first = None;
    for &(schema, entry) in written {
        if schema != ExpectationSchema::Traces {
            continue;
        }
        first = first.or_else(|| Some(entry.span()));
        let channel = spelled(entry).map_or(
            Maybe::Absent(channel_stated::Absent::Unwritten),
            |spelling| channel_stated(&spelling),
        );
        match channel {
            Maybe::Present(channel) => channels.push(channel),
            Maybe::Absent(channel_stated::Absent::Unwritten) => {
                return Ok(Stated::Malformed(ExpectationFault::UnwrittenTrace {
                    span: entry.span(),
                }));
            },
        }
    }
    match (runs.first(), first) {
        (Some(&ran), _) => Ok(Stated::Verdict(Outcome::RunsTracing(
            run_spelled(ran, arena)?,
            channels,
        ))),
        (None, Some(span)) => Ok(Stated::Malformed(ExpectationFault::TraceWithoutRun {
            span,
        })),
        (None, None) => Ok(owing_nothing()),
    }
}

quenchant_shape::reason_enum! {
    /// Why a `traces` payload names no channel.
    mod channel_stated {
        /// The payload is neither form.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// It is no `decomposes(c, web)` over a web node and no
            /// `primes(c, n)` over a count.
            Unwritten,
        }
    }
}

/// The channel a `traces` payload spelled `spelled` states: `decomposes(c,
/// web)` names `c` with `web`, and `primes(c, n)` names `c` with the prime
/// count `primes = n`, as a `decomposes` payload states one.
///
/// # Specification
/// - ensures: a channel named by an identifier, whose web is a `series`,
///   `parallel`, `prime` or `event` node or a prime count; unwritten for a
///   payload of neither form, or an empty or spaced name.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`traced`].
/// - witness: `expectation::tests::a_run_beside_traces_states_its_channels_3338`
#[spec(ensures: |ref ret| match *ret {
    Maybe::Present(ref channel) => !channel.name.is_empty()
        && (WEB_NODES.iter().any(|node| channel.web.as_ref().starts_with(node))
            || channel.web.as_ref().starts_with(PRIMES)),
    Maybe::Absent(_) => true,
})]
fn channel_stated(spelled: &RunSpelling) -> Maybe<Channel, channel_stated::Absent>
{
    let unwritten = Maybe::Absent(channel_stated::Absent::Unwritten);
    let text: &str = spelled.as_ref();
    let read = |opening: &str| {
        text.strip_prefix(opening)
            .and_then(|rest| rest.strip_suffix(')'))
            .and_then(|inner| inner.split_once(','))
            .map(|(name, rest)| (name, rest.trim_start()))
    };
    let named = |name: &str| {
        !name.is_empty()
            && name
                .chars()
                .all(|glyph| glyph.is_alphanumeric() || glyph == '_' || glyph == '\'')
    };
    if let Some((name, web)) = read("decomposes(")
        && named(name)
        && WEB_NODES.iter().any(|node| web.starts_with(node))
        && web.ends_with(')')
    {
        return Maybe::Present(Channel {
            name: String::from(name),
            web: RunSpelling::from(String::from(web)),
        });
    }
    if let Some((name, count)) = read("primes(")
        && named(name)
        && !count.is_empty()
        && count.bytes().all(|digit| digit.is_ascii_digit())
    {
        return Maybe::Present(Channel {
            name: String::from(name),
            web: RunSpelling::from(alloc::format!("{PRIMES}{count}")),
        });
    }
    unwritten
}

/// `web` as the `decomposes` payload `stated` reads it: the count of its
/// prime nodes, `primes = k`, when the payload states a count, and its whole
/// spelling otherwise.
///
/// # Specification
/// - requires: `web` is a spelling the runner printed for a web.
/// - ensures: `primes = k` for a `stated` opening `primes = `, `k` the number
///   of `prime(` nodes in `web`, each a `prime(` that begins a name rather than
///   ending a longer one; `web` itself otherwise.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a counted payload against a web with and without a prime
///   node, and a written web, each read back.
/// - witness: `expectation::tests::a_counted_web_reads_its_prime_nodes_2077`
#[spec(ensures: |ret| if stated.as_ref().starts_with(PRIMES) { ret.as_ref().starts_with(PRIMES) } else { ret == *web })]
#[must_use]
pub fn web_as_stated(
    stated: &RunSpelling,
    web: &RunSpelling,
) -> RunSpelling
{
    if !stated.as_ref().starts_with(PRIMES) {
        return web.clone();
    }
    let spelled = web.as_ref();
    let primes = spelled
        .match_indices("prime(")
        .filter(|&(at, _)| {
            spelled
                .get(.. at)
                .and_then(|before| before.chars().next_back())
                .is_none_or(|before| !before.is_alphanumeric() && before != '_')
        })
        .count();

    RunSpelling::from(alloc::format!("{PRIMES}{primes}"))
}

/// The refusal a `refuses` entry names, read out of `arena`.
///
/// # Specification
/// - requires: `entry` is a `refuses` entry of the declaration being read.
/// - ensures: the refusal its text payload spells exactly, or the unnamed
///   absence for text outside the vocabulary.
/// - fails: `UnreadablePayload` at the entry's span for an absent or non-text
///   payload.
/// - panics: none.
///
/// # Errors
/// [`SettleFault::UnreadablePayload`] when the payload is not a text literal
/// of `arena`.
///
/// # Adequacy
/// - hypothesis: L3 — a named refusal and a near miss, alone and beside a run.
/// - witness: `settle::tests::a_refusal_outside_the_vocabulary_fails_the_fixture`
/// - witness: `expectation::tests::a_run_beside_a_refusal_states_both`
#[spec(ensures: |ret| match ret {
    | Ok(Maybe::Present(name)) => payload(entry, arena).is_ok_and(|literal| matches!(*literal, Literal::Text(ref text) if RefusalName::named_by(text) == Maybe::Present(name))),
    | Ok(Maybe::Absent(refusal_name::Absent::Unnamed)) => payload(entry, arena).is_ok_and(|literal| matches!(*literal, Literal::Text(_))),
    | Err(fault) => fault == SettleFault::UnreadablePayload { span: entry.span() },
})]
fn refusal_named(
    entry: &AttributeEntry,
    arena: &CoreArena,
) -> Result<Maybe<RefusalName, refusal_name::Absent>, SettleFault>
{
    let literal = payload(entry, arena)?;
    let Literal::Text(ref text) = *literal
    else {
        return Err(SettleFault::UnreadablePayload { span: entry.span() });
    };
    Ok(RefusalName::named_by(text))
}

/// The run outcome a `runs` entry spells, read out of `arena`.
///
/// # Specification
/// - requires: `entry` is a `runs` entry of the declaration being read.
/// - ensures: its text payload, unchanged.
/// - fails: `UnreadablePayload` at the entry's span for an absent or non-text
///   payload.
/// - panics: none.
///
/// # Errors
/// [`SettleFault::UnreadablePayload`] when the payload is not a text literal
/// of `arena`.
///
/// # Adequacy
/// - hypothesis: L3 — a run alone and beside a refusal.
/// - witness: `settle::tests::a_run_outcome_settles_under_either_root`
/// - witness: `expectation::tests::a_run_beside_a_refusal_states_both`
#[spec(ensures: |ret| match ret {
    | Ok(ref spelled) => payload(entry, arena).is_ok_and(|literal| matches!(*literal, Literal::Text(ref text) if spelled.as_ref() == text.as_ref())),
    | Err(fault) => fault == SettleFault::UnreadablePayload { span: entry.span() },
})]
fn run_spelled(
    entry: &AttributeEntry,
    arena: &CoreArena,
) -> Result<RunSpelling, SettleFault>
{
    let literal = payload(entry, arena)?;
    let Literal::Text(ref text) = *literal
    else {
        return Err(SettleFault::UnreadablePayload { span: entry.span() });
    };
    Ok(RunSpelling::from(String::from(text.as_ref())))
}

/// The call a `normalizes` line reads: the text before its first `~>`,
/// trimmed.
///
/// # Specification
/// - ensures: absent exactly when `line` writes no `~>`; otherwise the text
///   before the first one, without surrounding white space.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a line with an arrow and one without, through
///   [`stated_by`]'s witness.
/// - witness: `settle::tests::a_normal_form_settles_against_the_engines_reading`
#[spec(ensures: |ret| matches!(ret, Maybe::Present(_)) == line.as_ref().contains(NORMAL_FORM_ARROW))]
#[inline]
pub fn normalized_call<L>(line: &L) -> Maybe<CallText<'_>, normalized_call::Absent>
where
    L: AsRef<str>,
{
    match line.as_ref().split_once(NORMAL_FORM_ARROW) {
        Some((call, _normal)) => Maybe::Present(CallText::from(call.trim())),
        None => Maybe::Absent(normalized_call::Absent::Unwritten),
    }
}

/// What separates a call from its normal form in a `normalizes` line.
pub const NORMAL_FORM_ARROW: &str = "~>";

/// The literal `entry`'s payload is in `arena`.
///
/// # Specification
/// - requires: nothing; identifiers are interpreted within the supplied arena,
///   whose provenance remains the caller’s responsibility.
/// - ensures: returns the borrowed literal at the entry’s identifier, without
///   manufacturing a replacement.
/// - fails: `UnreadablePayload` preserving the attribute span when the payload
///   is missing, dangling or a nonliteral node.
/// - panics: none.
///
/// # Errors
/// [`SettleFault::UnreadablePayload`] when the entry has no payload, or the
/// arena holds no literal at its id.
///
/// # Adequacy
/// - hypothesis: L3 — held integer and text literals, an identifier absent from
///   the supplied arena, a missing payload and a held unit node. Exact values
///   and refusal spans distinguish wrong-node selection, fabricated defaults
///   and erased positions; pointer equality additionally states borrowing in
///   the predicate. Arena ownership is not encoded in a value identifier.
/// - witness: `expectation::tests::a_payload_the_arena_does_not_hold_is_unreadable`
/// - witness: `expectation::tests::missing_and_nonliteral_payloads_fail_but_checks_needs_none`
#[spec(
    ensures: |ret| match entry.payload() {
    Maybe::Present(value) => {
        arena
            .value(value)
            .map_or_else(
                || {
                    ret
                        == Err(SettleFault::UnreadablePayload {
                            span: entry.span(),
                        })
                },
                |node| match *node {
                    Value::Literal(ref literal) => {
                        matches!(
                            ret, Ok(found) if core::ptr::eq(core::ptr::from_ref(found),
                            core::ptr::from_ref(literal))
                        )
                    }
                    Value::Univalence(..) | Value::Dialogue(_) | Value::Web(_) | Value::RecordUpdate { .. } | Value::Row(_) |
                    Value::Primitive { .. } | Value::PathRefl(_) | Value::PathProduct(..) | Value::PathEquiv { .. } | Value::Here(_) | Value::Funext(..) | Value::Equiv(..) | Value::Ua { .. } | Value::SessionRelated { .. } | Value::Stay(_) | Value::Then(..) | Value::FlowProduct(..) | Value::Forward(_) | Value::FunctionFlow(..) | Value::Recorded(_) | Value::Returned(_) | Value::Nested(_) | Value::Run(_) | Value::Variable { .. } | Value::Constant(_) | Value::Tuple(_) | Value::Injection(..) | Value::ListNil | Value::ListCons(..) | Value::Thunk(_) | Value::Ascribe { .. } | Value::Lift { .. } | Value::Quote(_) | Value::QuoteComputation(_) | Value::StaticLambda(_) | Value::StaticApplication(..) | Value::Constructor { .. } | Value::Record(_) | Value::Hole(_) | Value::Mark { .. } | Value::Reify(_) => {
                        ret
                            == Err(SettleFault::UnreadablePayload {
                                span: entry.span(),
                            })
                    }
                },
            )
    }
    Maybe::Absent(_) => {
        ret
            == Err(SettleFault::UnreadablePayload {
                span: entry.span(),
            })
    }
},
)]
fn payload<'arena>(
    entry: &AttributeEntry,
    arena: &'arena CoreArena,
) -> Result<&'arena Literal, SettleFault>
{
    let unreadable = SettleFault::UnreadablePayload { span: entry.span() };
    let Maybe::Present(value) = entry.payload()
    else {
        return Err(unreadable);
    };
    let Some(node) = arena.value(value)
    else {
        return Err(unreadable);
    };
    let Value::Literal(ref literal) = *node
    else {
        return Err(unreadable);
    };
    Ok(literal)
}

/// What a declaration stating nothing states: it checks, owing nothing.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub fn owing_nothing() -> Stated
{
    Stated::Verdict(Outcome::Checks(ObligationCount::from(0_usize)))
}

/// The verdict an `owes` payload of `integer`, covering `span`, states.
///
/// # Specification
/// - requires: nothing; `IntegerLiteral` supplies a canonical sign and
///   magnitude.
/// - ensures: nonnegative magnitudes representable by a ledger count state that
///   exact count. A negative integer states `NegativeObligations`; a larger
///   nonnegative magnitude states `ObligationsBeyondRange`; both faults
///   preserve `span`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — negative and positive two, zero, the largest ledger count
///   and its immediate successor. Exact counts and nonempty fault spans
///   distinguish sign loss, off-by-one overflow, saturation and erased
///   location.
/// - witness: `expectation::tests::an_owes_payload_outside_the_counts_states_no_verdict`
#[spec(
    ensures: |ret| match integer.sign() {
    Sign::Negative => {
        ret
            == Stated::Malformed(ExpectationFault::NegativeObligations {
                span,
            })
    }
    Sign::NonNegative => {
        match (integer.magnitude().as_ref().parse::<usize>(), &ret) {
            (Ok(count), &Stated::Verdict(Outcome::Checks(owed))) => {
                usize::from(owed) == count
            }
            (
                Err(_),
                &Stated::Malformed(
                    ExpectationFault::ObligationsBeyondRange { span: reported },
                ),
            ) => reported == span,
            _ => false,
        }
    }
},
)]
fn obligations(
    integer: &IntegerLiteral,
    span: ByteSpan,
) -> Stated
{
    match integer.sign() {
        Sign::Negative => Stated::Malformed(ExpectationFault::NegativeObligations { span }),
        Sign::NonNegative => {
            let digits: &str = integer.magnitude().as_ref();
            digits.parse::<usize>().map_or(
                Stated::Malformed(ExpectationFault::ObligationsBeyondRange { span }),
                |owed| Stated::Verdict(Outcome::Checks(ObligationCount::from(owed))),
            )
        },
    }
}

#[cfg(test)]
mod tests
{
    use alloc::collections::BTreeSet;
    use alloc::string::String;
    use alloc::string::ToString as _;
    use alloc::vec::Vec;
    use core::fmt;
    use core::iter;

    use gandr_core_checker::ObligationCount;
    use gandr_core_term::CoreArena;
    use gandr_kernel_term::IntegerLiteral;
    use gandr_kernel_term::Literal;
    use gandr_kernel_term::Magnitude;
    use gandr_kernel_term::Sign;
    use gandr_kernel_term::StringLiteral;
    use gandr_surface_lowering::AttributeEntry;
    use gandr_surface_lowering::AttributeSchema;
    use gandr_surface_lowering::SurfaceName;
    use gandr_surface_syntax::ByteOffset;
    use gandr_surface_syntax::SourceText;
    use quenchant_shape::shape::Maybe;

    use super::ExpectationFault;
    use super::ExpectationSchema;
    use super::Membership;
    use super::Outcome;
    use super::Stated;
    use super::guard;
    use super::owing_nothing;
    use super::read;
    use crate::fixture::RefusingWriter;
    use crate::fixture::checked;
    use crate::fixture::empty_span;
    use crate::fixture::registered;
    use crate::fixture::span;
    use crate::refusal::CorpusRefusal;
    use crate::refusal::RefusalName;
    use crate::root::CorpusRoot;
    use crate::run::Channel;
    use crate::run::RunSpelling;
    use crate::settle::SettleFault;

    #[test]
    fn registered_names_select_schemas_without_order_assumptions()
    {
        for (spelled, schema) in [
            ("runs", ExpectationSchema::Runs),
            ("checks", ExpectationSchema::Checks),
            ("refuses", ExpectationSchema::Refuses),
            ("owes", ExpectationSchema::Owes),
            ("normalizes", ExpectationSchema::Normalizes),
            ("traces", ExpectationSchema::Traces),
            ("reads", ExpectationSchema::Reads),
        ] {
            assert_eq!(
                ExpectationSchema::of(registered(SurfaceName::from(spelled))),
                Maybe::Present(schema)
            );
            let rendered = schema.to_string();
            assert_eq!(
                ExpectationSchema::of(registered(SurfaceName::from(rendered.as_str()))),
                Maybe::Present(schema)
            );
        }
    }

    #[test]
    fn an_owes_payload_outside_the_counts_states_no_verdict()
    {
        let span = span(ByteOffset::from(11_usize), ByteOffset::from(29_usize));
        let magnitude = |digits: &str| {
            Magnitude::from_decimal_text(String::from(digits))
                .expect("the fixture spells decimal digits")
        };
        let owes = registered(SurfaceName::from("owes"));
        let widest = usize::MAX.to_string();
        let beyond = u128::try_from(usize::MAX)
            .expect("the target count fits u128")
            .checked_add(1_u128)
            .expect("u128 is wider than the target count")
            .to_string();
        let rows = [
            (
                IntegerLiteral::new(Sign::NonNegative, magnitude("0")),
                owing_nothing(),
            ),
            (
                IntegerLiteral::new(Sign::NonNegative, magnitude("2")),
                Stated::Verdict(Outcome::Checks(ObligationCount::from(2_usize))),
            ),
            (
                IntegerLiteral::new(Sign::Negative, magnitude("2")),
                Stated::Malformed(ExpectationFault::NegativeObligations { span }),
            ),
            (
                IntegerLiteral::new(Sign::NonNegative, magnitude(&widest)),
                Stated::Verdict(Outcome::Checks(ObligationCount::from(usize::MAX))),
            ),
            (
                IntegerLiteral::new(Sign::NonNegative, magnitude(&beyond)),
                Stated::Malformed(ExpectationFault::ObligationsBeyondRange { span }),
            ),
        ];

        for (integer, stated) in rows {
            let mut arena = CoreArena::new();
            let payload = arena.value_literal(Literal::Integer(integer));
            let entry = AttributeEntry::new(
                owes,
                AttributeSchema::Integer,
                Maybe::Present(payload),
                span,
            );
            let expectations = read(CorpusRoot::Fixture, iter::once(&entry), &arena, |_| None)
                .expect("the payload is an integer of the arena");
            assert_eq!(
                expectations.membership,
                Membership::Fixture,
                "an `owes` name is a fixture"
            );
            assert_eq!(
                expectations.stated, stated,
                "the payload states its count, or why it states none"
            );
        }
    }

    #[test]
    fn a_payload_the_arena_does_not_hold_is_unreadable()
    {
        let span = empty_span();
        let owes = registered(SurfaceName::from("owes"));
        let mut holding = CoreArena::new();
        let count = holding.value_literal(Literal::Integer(IntegerLiteral::new(
            Sign::NonNegative,
            Magnitude::zero(),
        )));
        let text = holding.value_literal(Literal::Text(StringLiteral::new(String::from(
            "TypeMismatch",
        ))));
        let owed = AttributeEntry::new(owes, AttributeSchema::Integer, Maybe::Present(count), span);
        let refused = AttributeEntry::new(
            registered(SurfaceName::from("refuses")),
            AttributeSchema::Text,
            Maybe::Present(text),
            span,
        );
        let misread =
            AttributeEntry::new(owes, AttributeSchema::Integer, Maybe::Present(text), span);
        let stated = |root: CorpusRoot, entry: AttributeEntry, arena: &CoreArena| {
            read(root, iter::once(&entry), arena, |_| None).map(|expectations| expectations.stated)
        };

        assert_eq!(
            stated(CorpusRoot::Fixture, owed, &holding),
            Ok(owing_nothing()),
            "the arena holding the payload reads it"
        );
        assert!(
            matches!(
                stated(CorpusRoot::Fixture, refused, &holding),
                Ok(Stated::Verdict(Outcome::Refuses(_)))
            ),
            "the arena holding a text payload reads it"
        );
        let empty = CoreArena::new();
        for entry in [owed, refused] {
            assert_eq!(
                stated(CorpusRoot::Fixture, entry, &empty),
                Err(SettleFault::UnreadablePayload { span }),
                "an arena without the payload reads nothing"
            );
        }
        assert_eq!(
            stated(CorpusRoot::Fixture, misread, &holding),
            Err(SettleFault::UnreadablePayload { span }),
            "a payload of another literal kind reads nothing"
        );
        assert_eq!(
            stated(CorpusRoot::Strict, misread, &empty),
            Ok(owing_nothing()),
            "the strict root reads no payload"
        );
    }

    #[test]
    fn a_run_beside_a_refusal_states_both()
    {
        let first = span(ByteOffset::from(3_usize), ByteOffset::from(12_usize));
        let second = span(ByteOffset::from(14_usize), ByteOffset::from(40_usize));
        let mut arena = CoreArena::new();
        let text = |arena: &mut CoreArena, spelled: &str| {
            Maybe::Present(
                arena.value_literal(Literal::Text(StringLiteral::new(String::from(spelled)))),
            )
        };
        let ran = text(&mut arena, "5");
        let named = text(&mut arena, "HeldCaptured");
        let unnamed = text(&mut arena, "HeldCapture");
        let runs = AttributeEntry::new(
            registered(SurfaceName::from("runs")),
            AttributeSchema::Text,
            ran,
            first,
        );
        let refuses = AttributeEntry::new(
            registered(SurfaceName::from("refuses")),
            AttributeSchema::Text,
            named,
            second,
        );
        let misnamed = AttributeEntry::new(
            registered(SurfaceName::from("refuses")),
            AttributeSchema::Text,
            unnamed,
            second,
        );
        let normalizes = AttributeEntry::new(
            registered(SurfaceName::from("normalizes")),
            AttributeSchema::Text,
            ran,
            second,
        );
        let both = Stated::Verdict(Outcome::RefusesRunning(
            RefusalName::HeldCaptured,
            RunSpelling::from(String::from("5")),
        ));
        let stated = |root: CorpusRoot, entries: &[&AttributeEntry]| {
            read(root, entries.iter().copied(), &arena, |_| None)
                .map(|expectations| (expectations.stated, expectations.guard))
        };

        for entries in [[&runs, &refuses], [&refuses, &runs]] {
            assert_eq!(
                stated(CorpusRoot::Fixture, &entries),
                Ok((both.clone(), Maybe::Absent(guard::Absent::Admitted))),
                "a run beside a refusal states both, in either order"
            );
            assert!(
                matches!(
                    stated(CorpusRoot::Strict, &entries),
                    Ok((_, Maybe::Present(_)))
                ),
                "the strict root guards the refusal half"
            );
        }
        assert_eq!(
            stated(CorpusRoot::Fixture, &[&runs, &misnamed]),
            Ok((
                Stated::Malformed(ExpectationFault::UnknownRefusal { span: second }),
                Maybe::Absent(guard::Absent::Admitted)
            )),
            "a refusal outside the vocabulary states nothing, beside a run as alone"
        );
        assert_eq!(
            stated(CorpusRoot::Fixture, &[&runs, &normalizes]),
            Ok((
                Stated::Malformed(ExpectationFault::ConflictingExpectations { first, second }),
                Maybe::Absent(guard::Absent::Admitted)
            )),
            "a run beside any other expectation still conflicts"
        );
        assert_eq!(
            stated(CorpusRoot::Fixture, &[&runs, &refuses, &refuses]),
            Ok((
                Stated::Malformed(ExpectationFault::ConflictingExpectations { first, second }),
                Maybe::Absent(guard::Absent::Admitted)
            )),
            "a third expectation beside the pair conflicts"
        );
    }

    #[test]
    fn guard_and_conflict_precedence_preserve_the_first_spans()
    {
        let arena = CoreArena::new();
        let first = span(ByteOffset::from(11_usize), ByteOffset::from(29_usize));
        let second = span(ByteOffset::from(43_usize), ByteOffset::from(61_usize));
        let lowered = checked(SourceText::from("@[ checks ] def marker = 0 ;"));
        let declaration = lowered
            .module
            .declarations()
            .iter()
            .next()
            .expect("one marker declaration");
        let Maybe::Present(digest) = declaration.definition()
        else {
            panic!("the declaration has a definition")
        };
        let marker = lowered
            .module
            .attributes()
            .entries(digest)
            .first()
            .expect("one marker attribute");
        let absent = marker.payload();
        let runs = AttributeEntry::new(
            registered(SurfaceName::from("runs")),
            AttributeSchema::Text,
            absent,
            first,
        );
        let owes = AttributeEntry::new(
            registered(SurfaceName::from("owes")),
            AttributeSchema::Integer,
            absent,
            second,
        );
        let refuses = AttributeEntry::new(
            registered(SurfaceName::from("refuses")),
            AttributeSchema::Text,
            absent,
            first,
        );
        for (entries, schema, at) in [
            ([runs, owes], ExpectationSchema::Owes, second),
            ([owes, refuses], ExpectationSchema::Owes, second),
            ([refuses, owes], ExpectationSchema::Refuses, first),
        ] {
            let strict = read(CorpusRoot::Strict, entries.iter(), &arena, |_| None)
                .expect("the guard precedes missing payloads");
            assert_eq!(strict.membership, Membership::Fixture);
            assert_eq!(strict.stated, owing_nothing());
            assert_eq!(
                strict.guard,
                Maybe::Present(CorpusRefusal::ExpectationOutsideFixtureRoot { schema, span: at })
            );
            let fixture = read(CorpusRoot::Fixture, entries.iter(), &arena, |_| None)
                .expect("the conflict precedes missing payloads");
            let [left, right] = entries;
            assert_eq!(fixture.membership, Membership::Fixture);
            assert_eq!(
                fixture.stated,
                Stated::Malformed(ExpectationFault::ConflictingExpectations {
                    first: left.span(),
                    second: right.span()
                })
            );
            assert_eq!(fixture.guard, Maybe::Absent(super::guard::Absent::Admitted));
        }
    }

    #[test]
    fn missing_and_nonliteral_payloads_fail_but_checks_needs_none()
    {
        let mut arena = CoreArena::new();
        let at = span(ByteOffset::from(17_usize), ByteOffset::from(39_usize));
        let unit = arena.value_unit();
        let lowered = checked(SourceText::from("@[ checks ] def marker = 0 ;"));
        let declaration = lowered
            .module
            .declarations()
            .iter()
            .next()
            .expect("one marker declaration");
        let Maybe::Present(digest) = declaration.definition()
        else {
            panic!("the declaration has a definition")
        };
        let marker = lowered
            .module
            .attributes()
            .entries(digest)
            .first()
            .expect("one marker attribute");
        let absent = marker.payload();
        for (name, schema) in [
            ("owes", AttributeSchema::Integer),
            ("refuses", AttributeSchema::Text),
            ("runs", AttributeSchema::Text),
        ] {
            for payload in [absent, Maybe::Present(unit)] {
                let entry =
                    AttributeEntry::new(registered(SurfaceName::from(name)), schema, payload, at);
                assert_eq!(
                    read(CorpusRoot::Fixture, iter::once(&entry), &arena, |_| None),
                    Err(SettleFault::UnreadablePayload { span: at })
                );
            }
        }
        let checks = AttributeEntry::new(
            registered(SurfaceName::from("checks")),
            marker.schema(),
            absent,
            at,
        );
        for root in [CorpusRoot::Strict, CorpusRoot::Fixture] {
            let empty = read(root, iter::empty(), &arena, |_| None)
                .expect("no expectation needs no payload");
            assert_eq!(empty.membership, Membership::Unattributed);
            assert_eq!(empty.stated, owing_nothing());
            assert_eq!(empty.guard, Maybe::Absent(super::guard::Absent::Admitted));
            let marked =
                read(root, iter::once(&checks), &arena, |_| None).expect("checks is a marker");
            assert_eq!(marked.membership, Membership::Fixture);
            assert_eq!(marked.stated, owing_nothing());
            assert_eq!(marked.guard, Maybe::Absent(super::guard::Absent::Admitted));
        }
    }

    #[test]
    fn expectation_formatters_retain_payloads_and_sink_failures()
    {
        for schema in [
            ExpectationSchema::Checks,
            ExpectationSchema::Owes,
            ExpectationSchema::Refuses,
            ExpectationSchema::Runs,
            ExpectationSchema::Normalizes,
            ExpectationSchema::Decomposes,
            ExpectationSchema::Traces,
            ExpectationSchema::Reads,
        ] {
            assert_eq!(
                fmt::Write::write_fmt(&mut RefusingWriter, format_args!("{schema}")),
                Err(fmt::Error)
            );
        }
        for (outcome, payload) in [
            (Outcome::Checks(ObligationCount::from(37_usize)), "37"),
            (Outcome::Refuses(RefusalName::TypeMismatch), "TypeMismatch"),
            (
                Outcome::Runs(RunSpelling::from(String::from("λ actual"))),
                "λ actual",
            ),
            (
                Outcome::Normalizes(RunSpelling::from(String::from("f(λ) ~> λ"))),
                "f(λ) ~> λ",
            ),
            (
                Outcome::Decomposes(RunSpelling::from(String::from("series(event(left, 0))"))),
                "series(event(left, 0))",
            ),
            (
                Outcome::RunsTracing(
                    RunSpelling::from(String::from("unit")),
                    Vec::from([Channel {
                        name: String::from("seat"),
                        web: RunSpelling::from(String::from("event(left, 0)")),
                    }]),
                ),
                "seat to event(left, 0)",
            ),
            (
                Outcome::Reads(RunSpelling::from(String::from("(Nat, λ)"))),
                "(Nat, λ)",
            ),
        ] {
            let stated = Stated::Verdict(outcome);
            assert!(stated.to_string().contains(payload));
            assert_eq!(
                fmt::Write::write_fmt(&mut RefusingWriter, format_args!("{stated}")),
                Err(fmt::Error)
            );
        }
        let first = span(ByteOffset::from(11_usize), ByteOffset::from(29_usize));
        let second = span(ByteOffset::from(43_usize), ByteOffset::from(61_usize));
        let first_spelled = first.to_string();
        let second_spelled = second.to_string();
        let mut distinct = BTreeSet::new();
        for fault in [
            ExpectationFault::UnknownRefusal { span: first },
            ExpectationFault::NegativeObligations { span: first },
            ExpectationFault::ObligationsBeyondRange { span: first },
            ExpectationFault::ConflictingExpectations { first, second },
            ExpectationFault::UnwrittenNormalForm { span: first },
            ExpectationFault::UnwrittenWeb { span: first },
            ExpectationFault::UnwrittenTrace { span: first },
            ExpectationFault::TraceWithoutRun { span: first },
            ExpectationFault::UnwrittenReads { span: first },
        ] {
            let stated = Stated::Malformed(fault);
            let rendered = stated.to_string();
            assert!(!rendered.contains(&first_spelled));
            assert!(!rendered.contains(&second_spelled));
            assert!(
                distinct.insert(rendered),
                "distinct faults must remain distinguishable"
            );
            assert_eq!(
                fmt::Write::write_fmt(&mut RefusingWriter, format_args!("{stated}")),
                Err(fmt::Error)
            );
        }
    }

    /// #2077: `decomposes(primes = n)` holds a web to its prime count, a
    /// prime node counted wherever it stands and a name ending in `prime`
    /// not counted; a written web is held to its whole spelling.
    #[test]
    fn a_counted_web_reads_its_prime_nodes_2077()
    {
        let spelling = |text: &str| RunSpelling::from(String::from(text));
        let counted = spelling("primes = 1");
        let web = spelling(
            "series(event(left, 0), prime(event(left, 1), event(right, 0), subprime(x), series(event(right, 1), prime(event(left, 2)))))",
        );
        let series = spelling("series(event(left, 0), parallel(event(left, 1), event(right, 0)))");
        assert_eq!(super::web_as_stated(&counted, &web), spelling("primes = 2"));
        assert_eq!(
            super::web_as_stated(&counted, &series),
            spelling("primes = 0")
        );
        assert_eq!(super::web_as_stated(&series, &web), web);
    }

    /// #2520: a `reads` payload reads as the set of items it names, `()` for
    /// none, a bare name or a tuple, each name once and in any order; an
    /// empty component, a nested tuple and a phrase name nothing. A set the
    /// runner spells reads back as itself, and a stated set settles against a
    /// produced one only when the two are equal.
    #[test]
    fn a_reads_payload_names_each_item_once_2520()
    {
        let spelling = |text: &str| RunSpelling::from(String::from(text));
        let named = |text: &str| match super::read_names(&spelling(text)) {
            Maybe::Present(names) => {
                Some(names.0.into_iter().map(String::from).collect::<Vec<_>>())
            },
            Maybe::Absent(_) => None,
        };
        let names = |written: &[&str]| Some(written.iter().copied().map(String::from).collect());
        assert_eq!(named("()"), names(&[]));
        assert_eq!(named("Nat"), names(&["Nat"]));
        assert_eq!(named("Inner.leaf"), names(&["Inner.leaf"]));
        assert_eq!(named("(side, Nat, side)"), names(&["Nat", "side"]));
        for unwritten in [
            "",
            "(Nat,, side)",
            "((Nat, side))",
            "f(x)",
            "no footprint: opaque",
        ] {
            assert_eq!(named(unwritten), None, "`{unwritten}` names nothing");
        }
        assert_eq!(
            super::reads_spelled(["side", "Nat", "side"]),
            spelling("(Nat, side)")
        );
        assert_eq!(super::reads_spelled(["Nat"]), spelling("Nat"));
        assert_eq!(super::reads_spelled(Vec::<&str>::new()), spelling("()"));
        let produced = spelling("(Nat, side)");
        let reordered = spelling("(side, Nat)");
        assert_eq!(super::reads_as_stated(&reordered, &produced), reordered);
        assert_eq!(
            super::reads_as_stated(&spelling("Nat"), &produced),
            produced
        );
        let opaque = spelling("no footprint: opaque");
        assert_eq!(super::reads_as_stated(&spelling("()"), &opaque), opaque);
    }

    /// #3338: `runs` beside `traces` states the run and each channel in the
    /// order written, a channel by its web or by its prime count; a `traces`
    /// with no `runs`, beside another expectation, or naming no channel states
    /// no verdict.
    #[test]
    fn a_run_beside_traces_states_its_channels_3338()
    {
        let at = |start: usize| span(ByteOffset::from(start), ByteOffset::from(start + 1_usize));
        let mut arena = CoreArena::new();
        let ran = Maybe::Present(
            arena.value_literal(Literal::Text(StringLiteral::new(String::from("unit")))),
        );
        let entry = |name: &str, schema, start| {
            AttributeEntry::new(registered(SurfaceName::from(name)), schema, ran, at(start))
        };
        let runs = entry("runs", AttributeSchema::Text, 0_usize);
        let webbed = entry("traces", AttributeSchema::Spelled, 2_usize);
        let counted = entry("traces", AttributeSchema::Spelled, 4_usize);
        let spaced = entry("traces", AttributeSchema::Spelled, 6_usize);
        let bare = entry("traces", AttributeSchema::Spelled, 8_usize);
        let checks = entry("checks", AttributeSchema::Marker, 10_usize);
        let spellings = [
            (
                2_usize,
                "decomposes(seat, series(event(left, 0), event(right, 0)))",
            ),
            (4_usize, "primes(other, 1)"),
            (6_usize, "decomposes(a b, event(left, 0))"),
            (8_usize, "decomposes(seat, 3)"),
        ];
        let spelled = |written: &AttributeEntry| {
            spellings
                .iter()
                .find(|&&(start, _)| at(start) == written.span())
                .map(|&(_, text)| RunSpelling::from(String::from(text)))
        };
        let channel = |name: &str, web: &str| Channel {
            name: String::from(name),
            web: RunSpelling::from(String::from(web)),
        };
        let both = Stated::Verdict(Outcome::RunsTracing(
            RunSpelling::from(String::from("unit")),
            Vec::from([
                channel("seat", "series(event(left, 0), event(right, 0))"),
                channel("other", "primes = 1"),
            ]),
        ));
        let malformed = |fault| {
            Ok((
                Stated::Malformed(fault),
                Maybe::Absent(guard::Absent::Admitted),
            ))
        };
        let rows = [
            (
                CorpusRoot::Strict,
                Vec::from([&runs, &webbed, &counted]),
                Ok((both.clone(), Maybe::Absent(guard::Absent::Admitted))),
            ),
            (
                CorpusRoot::Fixture,
                Vec::from([&webbed, &counted, &runs]),
                Ok((both, Maybe::Absent(guard::Absent::Admitted))),
            ),
            (
                CorpusRoot::Fixture,
                Vec::from([&webbed]),
                malformed(ExpectationFault::TraceWithoutRun { span: at(2_usize) }),
            ),
            (
                CorpusRoot::Fixture,
                Vec::from([&checks, &webbed, &runs]),
                malformed(ExpectationFault::ConflictingExpectations {
                    first: at(10_usize),
                    second: at(2_usize),
                }),
            ),
            (
                CorpusRoot::Fixture,
                Vec::from([&runs, &webbed, &runs]),
                malformed(ExpectationFault::ConflictingExpectations {
                    first: at(0_usize),
                    second: at(2_usize),
                }),
            ),
            (
                CorpusRoot::Fixture,
                Vec::from([&runs, &webbed, &spaced]),
                malformed(ExpectationFault::UnwrittenTrace { span: at(6_usize) }),
            ),
            (
                CorpusRoot::Fixture,
                Vec::from([&runs, &bare]),
                malformed(ExpectationFault::UnwrittenTrace { span: at(8_usize) }),
            ),
        ];
        for (root, entries, expected) in rows {
            assert_eq!(
                read(root, entries.iter().copied(), &arena, spelled)
                    .map(|expectations| (expectations.stated, expectations.guard)),
                expected,
                "{entries:?} under the {root} root states as pinned"
            );
        }
    }
}
