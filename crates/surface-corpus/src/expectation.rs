//! The five expectation schemas, the verdict a declaration states, and the
//! reading of a declared name's attributes into it.
//!
//! # A name states one verdict or none
//!
//! A declared name carries one expectation, or a `runs` beside a `refuses`
//! (see below). Any other two on one name — `checks` beside `owes`, or one on
//! the signature and another on the definition — state no verdict:
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

/// One of the five expectation schemas.
///
/// # Specification
/// - requires: nothing; source correspondence is established by the reader or
///   producer.
/// - ensures: A schema selects whether the declaration expects zero
///   obligations, a stated count, a named refusal or an exact run spelling.
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
}

impl ExpectationSchema
{
    /// The schema `attribute` names, when it names one.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `checks`, `owes`, `refuses`, `runs`, `normalizes` and
    ///   `decomposes` name their schemas; any other registered attribute names
    ///   none.
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
    | ("decomposes", Maybe::Present(Self::Decomposes)) => true,
    (name, Maybe::Absent(expectation_schema::Absent::Unrelated)) => {
        !matches!(name, "checks" | "owes" | "refuses" | "runs" | "normalizes" | "decomposes")
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
}

impl fmt::Display for Outcome
{
    /// Writes `checks owing n`, `refuses Name`, `runs to outcome`,
    /// `normalizes call ~> normal form`, `decomposes to web` or
    /// `refuses Name and runs to outcome`.
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
///   when it carries exactly a `runs` and a `refuses`, in either order, or
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
        return Ok(Expectations {
            membership: Membership::Unattributed,
            stated: owing_nothing(),
            guard: Maybe::Absent(guard::Absent::Admitted),
        });
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
    let stated = match *written.as_slice() {
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
///   or `event` node and reports one that is not. Malformed counts, names,
///   lines and webs retain the attribute span.
/// - fails: `UnreadablePayload` at the attribute span for an absent or
///   wrong-kind payload required by the schema, or a `decomposes` with no
///   spelling.
/// - panics: none.
///
/// # Errors
/// [`SettleFault::UnreadablePayload`] when the payload is not the schema's
/// literal of `arena`, or a `decomposes` payload has no spelling.
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
            Some(web) if WEB_NODES.iter().any(|node| web.as_ref().starts_with(node)) && web.as_ref().ends_with(')') => {
                matches!(ret, Ok(Stated::Verdict(Outcome::Decomposes(ref stated))) if stated == web)
            }
            Some(_) => ret == Ok(Stated::Malformed(ExpectationFault::UnwrittenWeb { span: entry.span() })),
        }
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
                    Literal::Integer(_) | Literal::Text(_) | Literal::Numeric(_) => ret == Err(unreadable),
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
            Ok(if written {
                Stated::Verdict(Outcome::Decomposes(web.clone()))
            }
            else {
                Stated::Malformed(ExpectationFault::UnwrittenWeb { span })
            })
        },
    }
}

/// The node openings a `decomposes` payload begins with: the modular
/// decomposition's series, parallel and prime nodes, and a leaf event.
const WEB_NODES: [&str; 4] = ["series(", "parallel(", "prime(", "event("];

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
                    Value::Univalence(..) | Value::Dialogue(_) | Value::Web(_) |
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
            .first()
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
            .first()
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
}
