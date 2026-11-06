//! The exact reals a run reaches: where the operations of `Reals` go.
//!
//! The host at a program's entry holds the run's [`Plans`]: each one a plan
//! of `theory-exact-reals` that the validation pass admits. `admit` reads
//! its string as the canonical bytes of a plan in lowercase hexadecimal. It
//! validates them under the default quotas, against the registered cut of
//! stage A, and replies the place of the plan in the table. So a plan is an
//! integer that names a plan this host holds, and it never crosses. `enclose`
//! takes a plan and a precision `k`. It runs the refinement machine on the
//! root of the plan until the machine certifies an enclosure no wider than
//! `2^-k`. The checker replays the certificate, and the host replies the two
//! ends, each spelled `<mantissa>p<exponent>` for `mantissa · 2^exponent`.
//!
//! An operation that fails is declined, and the run is stuck at it. Before
//! the decline, the host writes one line to standard error. The line names
//! the operation and the cause: the site and the check of a refused plan, or
//! the other cause of the decline.
//!
//! # References
//!
//! - `vault:01a178aa-a419-7ab1-82e7-40a4f95938c6` — anchor: the first adapter
//!   of the decision register, a handle that names a plan the host holds, and §
//!   The architecture, where the host validates each value that crosses.
//! - `vault:01a1aa2d-a69c-7030-91e0-337d68d88151` — anchor: §
//!   presented-spaces-crates puts the host adapter of stage C in the
//!   dispatcher.

use alloc::boxed::Box;
use alloc::format;
use alloc::string::String;
use alloc::string::ToString as _;
use alloc::vec::Vec;
use core::fmt;
use core::num::NonZeroU32;

use anodized::spec;
use gandr_core_sequent::ConstructorTag;
use gandr_core_sequent::HeapValue;
use gandr_core_sequent::HeapValueId;
use gandr_core_sequent::ProducerArity;
use gandr_core_term::effect::OperationName;
use gandr_core_term::effect::host::REALS;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Sign;
use gandr_kernel_term::StringLiteral;
use gandr_runtime_emitter::HostReply;
use gandr_runtime_emitter::HostRequest;
use gandr_runtime_emitter::HostValues;
use gandr_theory_exact_reals::Answer;
use gandr_theory_exact_reals::Budget;
use gandr_theory_exact_reals::CertificateRefusal;
use gandr_theory_exact_reals::CheckerQuotas;
use gandr_theory_exact_reals::Conclusion;
use gandr_theory_exact_reals::Demand;
use gandr_theory_exact_reals::Dovetail;
use gandr_theory_exact_reals::Dyadic;
use gandr_theory_exact_reals::EncodedPlan;
use gandr_theory_exact_reals::Endpoint;
use gandr_theory_exact_reals::Evidence;
use gandr_theory_exact_reals::EvidenceTable;
use gandr_theory_exact_reals::Exponent;
use gandr_theory_exact_reals::Judgement;
use gandr_theory_exact_reals::Obligation;
use gandr_theory_exact_reals::Outcome;
use gandr_theory_exact_reals::Position;
use gandr_theory_exact_reals::Quantum;
use gandr_theory_exact_reals::Quotas;
use gandr_theory_exact_reals::Refusal;
use gandr_theory_exact_reals::Rounds;
use gandr_theory_exact_reals::SuspendReason;
use gandr_theory_exact_reals::ValidatedPlan;
use gandr_theory_exact_reals::check;
use gandr_theory_exact_reals::validate;

use super::Console;
use super::Printed;
use super::console::Line;

/// The operation of [`REALS`] that validates a plan.
const ADMIT: &str = "admit";
/// The operation of [`REALS`] that encloses the root of a plan.
const ENCLOSE: &str = "enclose";

/// The most plans that one run holds.
const PLANS: usize = 64;

/// The finest precision that `enclose` takes: an enclosure no wider than
/// `2^-4096`.
const PRECISION: i32 = 1 << 12;

/// The most certificate steps that one `enclose` does: the step quota of the
/// checker.
const STEPS: u64 = 1 << 16;

/// The plans that a run holds, each at the place that its handle names.
///
/// The table is empty until the first `admit`, so a run that performs no
/// `Reals` operation allocates nothing for it.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(super) struct Plans
{
    /// The validated plans, in the order of their `admit`.
    held: Vec<ValidatedPlan>,
}

/// The handle of a plan: its place in the table of the run.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Handle(usize);

/// The bytes that the hexadecimal text of an `admit` spells.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
struct Decoded(Vec<u8>);

/// What the payload of a `Reals` operation asks, read out of the store of the
/// run.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Asked<'values>
{
    /// Validate the plan that the text spells.
    Admit(&'values StringLiteral),
    /// Enclose the root of the plan at the handle no wider than `2^width`.
    Enclose
    {
        /// The place of the plan in the table.
        handle: Handle,
        /// The power of two that bounds the width, from `-PRECISION` to zero.
        width: Exponent,
    },
}

/// What a `Reals` operation answers, to be allocated as its reply.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Answered
{
    /// The handle of a plan that the table now holds.
    Plan(Handle),
    /// The lower end and the upper end of an enclosure, each spelled.
    Enclosure(String, String),
}

/// Why a run of the machine stops short of an enclosure.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Stopped
{
    /// The run stops at its limit of rounds with the obligation live.
    Pending,
    /// The run spends its budget of steps.
    Exhausted,
    /// The run stops at a cancellation.
    Cancelled,
    /// The machine cannot go on, for the stated reason.
    Suspended(SuspendReason),
}

/// Why the host declines a `Reals` operation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Declined
{
    /// The payload is not what `Reals` declares.
    Payload,
    /// The text is not the lowercase hexadecimal of a byte string.
    Hexadecimal,
    /// The run holds [`PLANS`] plans already.
    Full,
    /// The validation pass refuses the plan.
    Refused(Refusal),
    /// The run holds no plan at the handle.
    Unknown,
    /// The precision is below zero or past [`PRECISION`].
    Precision,
    /// The root of the plan is no real.
    Proposition,
    /// The machine stops short of an enclosure.
    Unsettled(Stopped),
    /// The checker refuses the certificate.
    Replay(CertificateRefusal),
    /// The certificate concludes another judgement than the enclosure asked.
    Mismatch,
    /// The store refuses the reply.
    Store,
}

impl fmt::Display for Declined
{
    /// Write the cause as one line.
    ///
    /// # Specification
    /// - ensures: writes one phrase per variant, no two alike, with the refusal
    ///   of the validation pass or of the checker after its phrase.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Errors
    /// Propagates the formatter's write failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — text that is not hexadecimal, a forged plan, an
    ///   unknown handle and a precision past the quota, each named on standard
    ///   error.
    /// - witness: `tests::run::a_script_encloses_the_square_root_of_two_5700`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Payload => f.write_str("the payload is not what `Reals` declares"),
            Self::Hexadecimal => {
                f.write_str("the text is not the lowercase hexadecimal of a byte string")
            },
            Self::Full => write!(f, "the run holds {PLANS} plans already"),
            Self::Refused(refusal) => write!(f, "the plan is refused at {refusal}"),
            Self::Unknown => f.write_str("the run holds no plan at the handle"),
            Self::Precision => write!(f, "the precision is not from 0 to {PRECISION}"),
            Self::Proposition => f.write_str("the root of the plan is no real"),
            Self::Unsettled(stopped) => {
                f.write_str("the machine stops short of an enclosure: ")?;
                f.write_str(match stopped {
                    Stopped::Pending => "the run is pending",
                    Stopped::Exhausted => "the run spends its budget of steps",
                    Stopped::Cancelled => "the run is cancelled",
                    Stopped::Suspended(SuspendReason::NoRule) => {
                        "the certificate format has no rule for the form of the root"
                    },
                    Stopped::Suspended(SuspendReason::Quota) => {
                        "the next step puts the certificate past the quotas of the checker"
                    },
                    Stopped::Suspended(SuspendReason::Opposed) => "a step concludes the other pole",
                })
            },
            Self::Replay(refusal) => write!(f, "the certificate does not replay: {refusal}"),
            Self::Mismatch => {
                f.write_str("the certificate concludes another judgement than the enclosure asked")
            },
            Self::Store => f.write_str("the store refuses the reply"),
        }
    }
}

/// Serve the `Reals` operation that `request` offers on `plans`: the reply
/// that the host gives, or nothing when the request is another interface's.
///
/// # Specification
/// - requires: nothing.
/// - ensures: for `admit`, the plan that the hexadecimal text spells, validated
///   and held, and its handle as the reply; for `enclose`, the two ends of a
///   certified enclosure of the root no wider than `2^-k`, which the checker
///   replays before the reply. A decline when the payload is not what `Reals`
///   declares, the text is not hexadecimal, the table is full, the plan is
///   refused, the handle names no plan, the precision is past the quota, the
///   machine stops short, the checker refuses, or the store refuses the reply;
///   one line on `console`'s standard error names the cause first. Nothing for
///   any other interface.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the exemplar admits the square root of two and encloses
///   it at `2^-64`; text that is not hexadecimal, a forged plan, an unknown
///   handle and a precision past the quota are each declined with their cause
///   on standard error.
/// - witness: `tests::run::a_script_encloses_the_square_root_of_two_5700`
#[spec(
    captures: [real = request.signature.name().as_ref() == REALS],
    ensures: |ret| ret.is_none() != real,
)]
pub(super) fn served<Abort>(
    plans: &mut Plans,
    console: &mut dyn Console,
    request: HostRequest<'_>,
    values: &mut HostValues<'_>,
) -> Option<HostReply<Abort>>
{
    if request.signature.name().as_ref() != REALS {
        return None;
    }
    let answered = asked(request.operation, request.payload, values)
        .and_then(|asked| plans.answer(asked))
        .and_then(|answer| reply(answer, values).ok_or(Declined::Store));
    Some(match answered {
        Ok(reply) => HostReply::Resume(reply),
        Err(declined) => {
            let line = format!("{REALS}.{}: {declined}", request.operation.as_ref());
            match console.eprint(Line::from(line.as_str())) {
                Printed::Written | Printed::Failed => {},
            }
            HostReply::Decline
        },
    })
}

impl Plans
{
    /// Answer `asked` over the plans of the run.
    ///
    /// # Specification
    /// trivial.
    fn answer(
        &mut self,
        asked: Asked<'_>,
    ) -> Result<Answered, Declined>
    {
        match asked {
            Asked::Admit(text) => self.admit(text).map(Answered::Plan),
            Asked::Enclose { handle, width } => self
                .enclose(handle, width)
                .map(|(lower, upper)| Answered::Enclosure(lower, upper)),
        }
    }

    /// Validate the plan that `text` spells and hold it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the handle of the plan, the place where the table now holds
    ///   it; the table holds no plan that fails validation.
    /// - fails: a full table, text that is not lowercase hexadecimal, and a
    ///   plan that the validation pass refuses, each with the table unchanged.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Declined::Full`], [`Declined::Hexadecimal`] or
    /// [`Declined::Refused`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`served`].
    /// - witness: `tests::run::a_script_encloses_the_square_root_of_two_5700`
    #[spec(
        captures: [before = self.held.len()],
        ensures: |ret| ret.as_ref().map_or(self.held.len() == before, |&handle| handle.0 == before && self.held.len() == before.saturating_add(1)),
    )]
    fn admit(
        &mut self,
        text: &StringLiteral,
    ) -> Result<Handle, Declined>
    {
        if self.held.len() >= PLANS {
            return Err(Declined::Full);
        }
        let bytes = hexadecimal(text).ok_or(Declined::Hexadecimal)?;
        let plan = validate(
            EncodedPlan::from(bytes.0.as_slice()),
            &Quotas::default(),
            &evidence(),
        )
        .map_err(Declined::Refused)?;
        let handle = Handle(self.held.len());
        self.held.push(plan);
        Ok(handle)
    }

    /// The two ends of a certified enclosure of the root of the plan at
    /// `handle`, no wider than `2^width`.
    ///
    /// # Specification
    /// - requires: `width` from `-PRECISION` to zero.
    /// - ensures: the lower end and the upper end of the enclosure that the
    ///   checker replays from the certificate of the machine, the conclusion
    ///   about the root at the width asked.
    /// - fails: a handle that names no plan, a root that is no real, a run of
    ///   the machine that stops short, and a certificate that the checker
    ///   refuses or that concludes another judgement.
    /// - panics: none.
    /// - executable: none — the clause speaks of the machine's certificate and
    ///   its replay, which the function makes.
    ///
    /// # Errors
    /// [`Declined::Unknown`], [`Declined::Proposition`],
    /// [`Declined::Unsettled`], [`Declined::Replay`] or
    /// [`Declined::Mismatch`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`served`].
    /// - witness: `tests::run::a_script_encloses_the_square_root_of_two_5700`
    fn enclose(
        &self,
        handle: Handle,
        width: Exponent,
    ) -> Result<(String, String), Declined>
    {
        let plan = self.held.get(handle.0).ok_or(Declined::Unknown)?;
        let obligation =
            Obligation::new(plan, plan.plan().root().node(), Demand::Encloses { width })
                .ok()
                .ok_or(Declined::Proposition)?;
        let quotas = CheckerQuotas::default();
        let mut machine = Dovetail::new(plan, [obligation], Quantum::from(NonZeroU32::MAX), quotas);
        let report = machine.run(Budget::from(STEPS), Rounds::from(1_u64), || false);
        let stopped = match report.outcome(Position::from(0_usize)) {
            Some(Outcome::Certified(certificate)) => Ok(certificate),
            Some(Outcome::Pending) | None => Err(Stopped::Pending),
            Some(Outcome::Exhausted) => Err(Stopped::Exhausted),
            Some(Outcome::Cancelled) => Err(Stopped::Cancelled),
            Some(Outcome::Suspended(reason)) => Err(Stopped::Suspended(reason)),
        };
        let certificate = stopped.map_err(Declined::Unsettled)?;
        let checked = check(plan, certificate, &quotas).map_err(Declined::Replay)?;
        match obligation.answered_by(checked.conclusion()) {
            Answer::Answers => {},
            Answer::Misses => return Err(Declined::Mismatch),
        }
        match *checked.conclusion() {
            Conclusion::Encloses { ref interval, .. } => {
                match (&interval.lower().endpoint, &interval.upper().endpoint) {
                    (&Endpoint::Finite(ref lower), &Endpoint::Finite(ref upper)) => {
                        Ok((spelled(lower), spelled(upper)))
                    },
                    (
                        &(Endpoint::NegInf | Endpoint::Finite(_) | Endpoint::PosInf),
                        &(Endpoint::NegInf | Endpoint::Finite(_) | Endpoint::PosInf),
                    ) => Err(Declined::Mismatch),
                }
            },
            Conclusion::Holds { .. } | Conclusion::Fails { .. } => Err(Declined::Mismatch),
        }
    }
}

/// The evidence that a plan may reference: the registered cut of stage A,
/// whose laws stand at the reference zero.
///
/// # Specification
/// trivial.
fn evidence() -> EvidenceTable
{
    let mut table = EvidenceTable::new();
    // A fresh table holds no judgement that the registration conflicts with,
    // and a table without it refuses every cut, so neither answer admits more.
    match table.register(Evidence::from(0_u32), Judgement::CutLaws) {
        Ok(()) | Err(_) => table,
    }
}

/// `value` spelled `<mantissa>p<exponent>`, for `mantissa · 2^exponent`.
///
/// # Specification
/// trivial.
fn spelled(value: &Dyadic) -> String
{
    format!("{}p{}", value.mantissa(), i32::from(value.exponent()))
}

/// The bytes that `text` spells in lowercase hexadecimal, two digits a byte.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the byte string whose digits, each pair high first, are `text`;
///   nothing for text of odd length or with a character other than `0`–`9` and
///   `a`–`f`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the plan of the exemplar, and text with a character that
///   is not a digit.
/// - witness: `tests::run::a_script_encloses_the_square_root_of_two_5700`
#[spec(ensures: |ret| ret.as_ref().is_none_or(|bytes| bytes.0.len().checked_mul(2) == Some(AsRef::<str>::as_ref(text).len())))]
fn hexadecimal(text: &StringLiteral) -> Option<Decoded>
{
    let text: &str = text.as_ref();
    let (pairs, odd) = text.as_bytes().as_chunks::<2>();
    if !odd.is_empty() {
        return None;
    }
    let nibble = |digit: u8| match digit {
        b'0' ..= b'9' => digit.checked_sub(b'0'),
        b'a' ..= b'f' => digit.checked_sub(b'a')?.checked_add(10),
        _ => None,
    };
    let mut bytes = Vec::with_capacity(pairs.len());
    for &[high, low] in pairs {
        bytes.push(nibble(high)?.checked_shl(4)? | nibble(low)?);
    }
    Some(Decoded(bytes))
}

/// What `operation` asks of the plans, its payload `payload` read out of
/// `values`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `admit` with its text, and `enclose` with its handle and the
///   width that its precision bounds.
/// - fails: a payload that is not what `Reals` declares, or an operation that
///   `Reals` does not declare, and a precision below zero or past
///   [`PRECISION`].
/// - panics: none.
/// - executable: none — the clause restates the reading of the payload.
///
/// # Errors
/// [`Declined::Payload`], [`Declined::Unknown`] for a handle below zero or
/// past the places of a table, or [`Declined::Precision`].
///
/// # Adequacy
/// - hypothesis: L3 — as [`served`].
/// - witness: `tests::run::a_script_encloses_the_square_root_of_two_5700`
fn asked<'values>(
    operation: &OperationName,
    payload: HeapValueId,
    values: &'values HostValues<'_>,
) -> Result<Asked<'values>, Declined>
{
    match operation.as_ref() {
        ADMIT => match values.value(payload) {
            Some(&HeapValue::Literal(Literal::Text(ref text))) => Ok(Asked::Admit(text)),
            Some(_) | None => Err(Declined::Payload),
        },
        ENCLOSE => {
            let Some(&HeapValue::Constructed {
                tag: ConstructorTag::Tuple(ProducerArity::TWO),
                ref fields,
            }) = values.value(payload)
            else {
                return Err(Declined::Payload);
            };
            let (&handle, &precision) =
                fields.first().zip(fields.get(1)).ok_or(Declined::Payload)?;
            let handle = natural(values, handle)?
                .as_ref()
                .parse::<usize>()
                .ok()
                .map(Handle)
                .ok_or(Declined::Unknown)?;
            let width = natural(values, precision)
                .ok()
                .and_then(|digits| digits.as_ref().parse::<i32>().ok())
                .filter(|&precision| precision <= PRECISION)
                .map(|precision| Exponent::from(precision.saturating_neg()))
                .ok_or(Declined::Precision)?;
            Ok(Asked::Enclose { handle, width })
        },
        _ => Err(Declined::Payload),
    }
}

/// The magnitude of the non-negative integer that `value` holds.
///
/// # Specification
/// trivial.
fn natural<'values>(
    values: &'values HostValues<'_>,
    value: HeapValueId,
) -> Result<&'values Magnitude, Declined>
{
    match values.value(value) {
        Some(&HeapValue::Literal(Literal::Integer(ref integer))) => match integer.sign() {
            Sign::NonNegative => Ok(integer.magnitude()),
            Sign::Negative => Err(Declined::Unknown),
        },
        Some(_) | None => Err(Declined::Payload),
    }
}

/// `answer` allocated in `values`: a handle as an integer, and an enclosure
/// as a pair of strings.
///
/// # Specification
/// trivial.
fn reply(
    answer: Answered,
    values: &mut HostValues<'_>,
) -> Option<HeapValueId>
{
    match answer {
        Answered::Plan(handle) => {
            let magnitude = Magnitude::from_decimal_text(handle.0.to_string())?;
            values
                .allocate(HeapValue::Literal(Literal::Integer(IntegerLiteral::new(
                    Sign::NonNegative,
                    magnitude,
                ))))
                .ok()
        },
        Answered::Enclosure(lower, upper) => {
            let lower = values
                .allocate(HeapValue::Literal(Literal::Text(StringLiteral::new(lower))))
                .ok()?;
            let upper = values
                .allocate(HeapValue::Literal(Literal::Text(StringLiteral::new(upper))))
                .ok()?;
            values
                .allocate(HeapValue::Constructed {
                    tag: ConstructorTag::Tuple(ProducerArity::TWO),
                    fields: Box::new([lower, upper]),
                })
                .ok()
        },
    }
}
