//! The four expectation schemas, the verdict a declaration states, and the
//! reading of a declared name's attributes into it.
//!
//! # A name states one verdict or none
//!
//! A declared name carries at most one expectation. Two on one name — `checks`
//! beside `owes`, or one on the signature and another on the definition —
//! state no verdict: the name is unsettled with
//! [`ExpectationFault::ConflictingExpectations`], never resolved by picking
//! one. A payload outside its schema's range states no verdict either, and
//! is reported with the bytes it covers.
//!
//! # A run outcome refines *checks*
//!
//! `runs("…")` states that the declaration checks, owing nothing, and that
//! running it produces the outcome the payload spells. It refines `checks`
//! rather than contradicting it, so the strict root admits it.
//!
//! # Under the strict root
//!
//! The strict root holds every declaration to *checks, owing nothing*. An
//! `owes` or `refuses` attribute there is not read: its first occurrence in
//! reading order is the corpus refusal the declaration produces instead of its
//! verdict. A declaration carrying neither is read as under the fixture root,
//! where the two schemas it can carry — `checks` and `runs` — both state that
//! it checks, owing nothing.

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

/// One of the four expectation schemas.
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
}

impl ExpectationSchema
{
    /// The schema `attribute` names, when it names one.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `checks`, `owes`, `refuses` and `runs` name their schemas;
    ///   any other registered attribute names none.
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
    | ("runs", Maybe::Present(Self::Runs)) => true,
    (name, Maybe::Absent(expectation_schema::Absent::Unrelated)) => {
        !matches!(name, "checks" | "owes" | "refuses" | "runs")
    }
    _ => false,
},
    )]
    #[inline]
    pub fn of(attribute: RegisteredAttribute) -> Maybe<Self, expectation_schema::Absent>
    {
        let spelled: &str = attribute.as_ref();
        match spelled {
            | "checks" => Maybe::Present(Self::Checks),
            | "owes" => Maybe::Present(Self::Owes),
            | "refuses" => Maybe::Present(Self::Refuses),
            | "runs" => Maybe::Present(Self::Runs),
            | _ => Maybe::Absent(expectation_schema::Absent::Unrelated),
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
            | Self::Checks => "checks",
            | Self::Owes => "owes",
            | Self::Refuses => "refuses",
            | Self::Runs => "runs",
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
}

impl fmt::Display for Outcome
{
    /// Writes `checks owing n`, `refuses Name` or `runs to outcome`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the verdict kind and its count, refusal name or run
    ///   spelling.
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
            | Self::Checks(owed) => write!(f, "checks owing {owed}"),
            | Self::Refuses(name) => write!(f, "refuses {name}"),
            | Self::Runs(ref spelled) => write!(f, "runs to {spelled}"),
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
            | Self::Verdict(ref outcome) => fmt::Display::fmt(outcome, f),
            | Self::Malformed(fault) => write!(f, "no verdict, {fault}"),
        }
    }
}

/// Why an expectation names no verdict.
///
/// # Specification
/// - requires: nothing; source correspondence is established by the reader or
///   producer.
/// - ensures: Distinguishes unknown refusal names, negative counts,
///   unrepresentable counts and conflicting expectations, preserving the source
///   positions of each cause.
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
}

impl fmt::Display for ExpectationFault
{
    /// Writes the fault and the bytes it names.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the fault kind and every source span it carries.
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
            | Self::UnknownRefusal { span } => {
                write!(f, "the `refuses` payload at {span} names no refusal")
            },
            | Self::NegativeObligations { span } => {
                write!(f, "the `owes` payload at {span} is below zero")
            },
            | Self::ObligationsBeyondRange { span } => {
                write!(f, "the `owes` payload at {span} is past every ledger size")
            },
            | Self::ConflictingExpectations { first, second } => write!(
                f,
                "the expectation at {second} contradicts the one at {first}"
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
/// of `arena`.
///
/// # Specification
/// - requires: `attributes` are the entries filed under one declared name, the
///   signature's before the definition's, and `arena` is the arena the lowering
///   minted their payloads into.
/// - ensures: with no expectation, an unattributed name stating checks owing
///   nothing, unguarded. Otherwise a fixture: guarded by the first expectation
///   in reading order its root does not admit — under the strict root an `owes`
///   or a `refuses` — and then stating checks owing nothing with no payload
///   read; unguarded, stating its one expectation's verdict, or
///   [`ExpectationFault::ConflictingExpectations`] naming the first two when it
///   carries more than one.
/// - provides: the stated side of the settle comparison.
/// - fails: [`SettleFault::UnreadablePayload`] when the one payload read is
///   absent from `arena`, or is not its schema's literal.
/// - panics: none.
///
/// # Errors
/// [`SettleFault::UnreadablePayload`] when an `owes`, `refuses` or `runs`
/// payload is not an integer or a text literal of `arena`.
///
/// # Adequacy
/// - hypothesis: L3 — all four schemas under both roots; negative, zero,
///   maximal and overflowing obligation counts; missing and wrong-kind
///   payloads; absent, single and conflicting expectations. Exact membership,
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
                            expectations.stated, Stated::Verdict(Outcome::Refuses(_))
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
pub fn read<'entry, Entries>(
    root: CorpusRoot,
    attributes: Entries,
    arena: &CoreArena,
) -> Result<Expectations, SettleFault>
where
    Entries: Iterator<Item = &'entry AttributeEntry>,
{
    let written: Vec<(ExpectationSchema, &AttributeEntry)> = attributes
        .filter_map(|entry| match ExpectationSchema::of(entry.name()) {
            | Maybe::Present(schema) => Some((schema, entry)),
            | Maybe::Absent(expectation_schema::Absent::Unrelated) => None,
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
    let stated = match written.get(1_usize) {
        | Some(&(_schema, second)) => {
            Stated::Malformed(ExpectationFault::ConflictingExpectations {
                first: entry.span(),
                second: second.span(),
            })
        },
        | None => stated_by(schema, entry, arena)?,
    };
    Ok(Expectations {
        membership: Membership::Fixture,
        stated,
        guard: Maybe::Absent(guard::Absent::Admitted),
    })
}

/// The verdict one expectation of `schema` states, its payload read out of
/// `arena`.
///
/// # Specification
/// - requires: `entry` belongs to the declaration being read; the caller
///   supplies its payload arena.
/// - ensures: `checks` states zero obligations without a payload; `owes` reads
///   an integer count; `refuses` resolves an exact vocabulary spelling or
///   reports its unknown name; `runs` preserves the text payload. Malformed
///   counts and names retain the attribute span.
/// - fails: `UnreadablePayload` at the attribute span for an absent or
///   wrong-kind payload required by the schema.
/// - panics: none.
///
/// # Errors
/// [`SettleFault::UnreadablePayload`] when the payload is not the schema's
/// literal of `arena`.
///
/// # Adequacy
/// - hypothesis: L3 — integer boundaries, exact refusal names and a near miss,
///   and differing run spellings, beside absent and wrong-kind literal
///   payloads. Exact verdicts and fault spans distinguish schema swaps, payload
///   loss and treating malformed input as a verdict.
/// - witness: `expectation::tests::an_owes_payload_outside_the_counts_states_no_verdict`
/// - witness: `expectation::tests::missing_and_nonliteral_payloads_fail_but_checks_needs_none`
/// - witness: `settle::tests::a_refusal_outside_the_vocabulary_fails_the_fixture`
/// - witness: `run::tests::run_mismatches_expose_both_spellings_and_preserve_sink_refusal`
#[spec(
    ensures: |ret| {
    let unreadable = SettleFault::UnreadablePayload {
        span: entry.span(),
    };
    if schema == ExpectationSchema::Checks {
        ret == Ok(owing_nothing())
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
                                name.spelling().as_ref() == text.as_ref()
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
                    _ => ret == Err(unreadable),
                },
            )
    }
},
)]
fn stated_by(
    schema: ExpectationSchema,
    entry: &AttributeEntry,
    arena: &CoreArena,
) -> Result<Stated, SettleFault>
{
    let span = entry.span();
    let unreadable = SettleFault::UnreadablePayload { span };
    match schema {
        | ExpectationSchema::Checks => Ok(owing_nothing()),
        | ExpectationSchema::Owes => {
            let literal = payload(entry, arena)?;
            let Literal::Integer(ref integer) = *literal
            else {
                return Err(unreadable);
            };
            Ok(obligations(integer, span))
        },
        | ExpectationSchema::Refuses => {
            let literal = payload(entry, arena)?;
            let Literal::Text(ref text) = *literal
            else {
                return Err(unreadable);
            };
            Ok(match RefusalName::named_by(text) {
                | Maybe::Present(name) => Stated::Verdict(Outcome::Refuses(name)),
                | Maybe::Absent(refusal_name::Absent::Unnamed) => {
                    Stated::Malformed(ExpectationFault::UnknownRefusal { span })
                },
            })
        },
        | ExpectationSchema::Runs => {
            let literal = payload(entry, arena)?;
            let Literal::Text(ref text) = *literal
            else {
                return Err(unreadable);
            };
            Ok(Stated::Verdict(Outcome::Runs(RunSpelling::from(
                String::from(text.as_ref()),
            ))))
        },
    }
}

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
                    _ => {
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
        | Sign::Negative => Stated::Malformed(ExpectationFault::NegativeObligations { span }),
        | Sign::NonNegative => {
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
            let expectations = read(CorpusRoot::Fixture, iter::once(&entry), &arena)
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
            read(root, iter::once(&entry), arena).map(|expectations| expectations.stated)
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
            let strict = read(CorpusRoot::Strict, entries.iter(), &arena)
                .expect("the guard precedes missing payloads");
            assert_eq!(strict.membership, Membership::Fixture);
            assert_eq!(strict.stated, owing_nothing());
            assert_eq!(
                strict.guard,
                Maybe::Present(CorpusRefusal::ExpectationOutsideFixtureRoot { schema, span: at })
            );
            let fixture = read(CorpusRoot::Fixture, entries.iter(), &arena)
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
                    read(CorpusRoot::Fixture, iter::once(&entry), &arena),
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
            let empty = read(root, iter::empty(), &arena).expect("no expectation needs no payload");
            assert_eq!(empty.membership, Membership::Unattributed);
            assert_eq!(empty.stated, owing_nothing());
            assert_eq!(empty.guard, Maybe::Absent(super::guard::Absent::Admitted));
            let marked = read(root, iter::once(&checks), &arena).expect("checks is a marker");
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
        ] {
            let stated = Stated::Malformed(fault);
            let rendered = stated.to_string();
            assert!(rendered.contains(&first_spelled));
            if matches!(fault, ExpectationFault::ConflictingExpectations { .. }) {
                assert!(rendered.contains(&second_spelled));
            }
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
