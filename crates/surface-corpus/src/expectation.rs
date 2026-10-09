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
    /// - hypothesis: L3 — the registry is a finite class; every registered name
    ///   is read and asserted at its pinned schema, and each schema's own
    ///   spelling reads back to it.
    /// - witness: `expectation::tests::every_registered_attribute_is_an_expectation_schema`
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
    /// trivial.
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
    /// trivial.
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
    /// trivial.
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
    /// trivial.
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
/// - hypothesis: L3 — each branch is driven by a source naming it and asserted
///   at its exact reading, beside a control one change away: a payload in and
///   out of range, a vocabulary name and a near miss, one expectation and two,
///   the same expectation under both roots, a run outcome under the strict
///   root, and a payload read from an arena that does not hold it.
/// - witness: `expectation::tests::an_owes_payload_outside_the_counts_states_no_verdict`
/// - witness: `expectation::tests::a_payload_the_arena_does_not_hold_is_unreadable`
/// - witness: `settle::tests::a_refusal_outside_the_vocabulary_fails_the_fixture`
/// - witness: `settle::tests::a_name_carrying_two_expectations_states_none`
/// - witness: `settle::tests::the_strict_root_refuses_an_expectation_outside_the_fixture_root`
/// - witness: `settle::tests::a_run_outcome_settles_under_either_root`
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
/// trivial.
///
/// # Errors
/// [`SettleFault::UnreadablePayload`] when the payload is not the schema's
/// literal of `arena`.
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
/// trivial.
///
/// # Errors
/// [`SettleFault::UnreadablePayload`] when the entry has no payload, or the
/// arena holds no literal at its id.
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
/// trivial.
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
    use alloc::string::String;
    use alloc::string::ToString as _;
    use core::iter;

    use gandr_core_checker::ObligationCount;
    use gandr_core_term::CoreArena;
    use gandr_kernel_term::IntegerLiteral;
    use gandr_kernel_term::Literal;
    use gandr_kernel_term::Magnitude;
    use gandr_kernel_term::Sign;
    use gandr_kernel_term::StringLiteral;
    use gandr_surface_lowering::AttributeEntry;
    use gandr_surface_lowering::AttributeRegistry;
    use gandr_surface_lowering::AttributeSchema;
    use gandr_surface_lowering::SurfaceName;
    use quenchant_shape::shape::Maybe;

    use super::ExpectationFault;
    use super::ExpectationSchema;
    use super::Membership;
    use super::Outcome;
    use super::Stated;
    use super::owing_nothing;
    use super::read;
    use crate::fixture::empty_span;
    use crate::fixture::registered;
    use crate::root::CorpusRoot;
    use crate::settle::SettleFault;

    #[test]
    fn every_registered_attribute_is_an_expectation_schema()
    {
        let pinned = [
            ("checks", ExpectationSchema::Checks),
            ("owes", ExpectationSchema::Owes),
            ("refuses", ExpectationSchema::Refuses),
            ("runs", ExpectationSchema::Runs),
        ];

        let names = AttributeRegistry::names();
        assert_eq!(
            names.len(),
            pinned.len(),
            "the registry holds the four schemas"
        );
        for (name, (spelled, schema)) in names.into_iter().zip(pinned) {
            assert_eq!(name.as_ref(), spelled, "the registry order is pinned");
            assert_eq!(
                ExpectationSchema::of(name),
                Maybe::Present(schema),
                "`{spelled}` names its schema"
            );
            assert_eq!(
                schema.to_string(),
                spelled,
                "the schema writes the name it is registered under"
            );
        }
    }

    #[test]
    fn an_owes_payload_outside_the_counts_states_no_verdict()
    {
        let span = empty_span();
        let magnitude = |digits: &str| {
            Magnitude::from_decimal_text(String::from(digits))
                .expect("the fixture spells decimal digits")
        };
        let owes = registered(SurfaceName::from("owes"));
        let widest = usize::MAX.to_string();
        let rows = [
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
                IntegerLiteral::new(Sign::NonNegative, magnitude("99999999999999999999999999")),
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
}
