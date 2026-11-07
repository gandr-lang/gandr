//! The randomness a run reaches: where the operation of `Rand` goes.
//!
//! `draw` takes a width `n` with `1 ≤ n ≤ 64`. The host reads eight bytes
//! from the entropy source of the operating system, keeps the high `n` bits
//! of their word, and replies that integer, uniform over `[0, 2^n)`. The host
//! holds no state between draws, and a run that performs no `draw` never
//! reads the entropy source.
//!
//! A width outside that range, a width that is not an integer, and an entropy
//! source that fails are declines, and the run is stuck at the draw. Before
//! the decline, the host writes one line to standard error. The line names
//! the operation and the cause.
//!
//! # References
//!
//! - `vault:01a178aa-a7bd-7d03-a728-feae5af9d1a8` — anchor: §
//!   ffi-design-effect-safety-model. A handler of the source shadows the native
//!   handler, so a model of the draws runs with no entropy read, and a native
//!   handler resumes exactly once.
//! - `vault:01a1aa2d-a69c-7030-91e0-337d68d88151` — anchor: §
//!   presented-spaces-quantities-probability. A draw is the operation of a
//!   probability effect, whose exact model `theory-probability` gives.

use alloc::format;
use alloc::string::String;
use alloc::string::ToString as _;
use core::fmt;

use anodized::spec;
use gandr_core_sequent::HeapValue;
use gandr_core_sequent::HeapValueId;
use gandr_core_term::effect::OperationName;
use gandr_core_term::effect::host::RAND;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Sign;
use gandr_runtime_emitter::HostReply;
use gandr_runtime_emitter::HostRequest;
use gandr_runtime_emitter::HostValues;

use super::Console;
use super::Printed;
use super::console::Line;

#[cfg(test)]
mod tests;

/// The operation of [`RAND`] that draws fair bits.
const DRAW: &str = "draw";

/// The widest draw, in bits: one word of the entropy source.
const WIDEST: u32 = 64;

/// The width of a draw in bits, from one to [`WIDEST`].
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Width(u32);

/// An integer drawn uniform over `[0, 2^n)` for a width `n`.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Drawn(u64);

/// Why the host declines an operation of [`RAND`].
#[derive(Clone, Debug, Eq, PartialEq)]
enum Declined
{
    /// The operation is not `draw`.
    Operation,
    /// The width is not an integer.
    Payload,
    /// The width, as the program spells it, lies outside one to [`WIDEST`].
    Width(String),
    /// The entropy source of the operating system failed.
    Entropy(getrandom::Error),
    /// The run's values hold no room for the drawn integer.
    Store,
}

impl fmt::Display for Declined
{
    /// Writes the cause of the decline as one clause.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Operation => f.write_str("the interface has no such operation"),
            Self::Payload => f.write_str("the width is not an integer"),
            Self::Width(ref spelled) => {
                write!(f, "a width of {spelled} bits lies outside 1 to {WIDEST}")
            },
            Self::Entropy(error) => {
                write!(
                    f,
                    "the entropy source of the operating system failed: {error}"
                )
            },
            Self::Store => f.write_str("the run holds no room for the drawn integer"),
        }
    }
}

/// Serve the `Rand` operation that `request` offers: the reply that the host
/// gives, or nothing when the request is another interface's.
///
/// # Specification
/// - requires: nothing.
/// - ensures: for `draw`, an integer uniform over `[0, 2^n)` for the width `n`
///   of the payload. A decline when the width is not an integer from one to 64,
///   or when the entropy source fails; one line on `console`'s standard error
///   names the cause first. Nothing for any other interface.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the exemplar sums two draws of two bits and exits with a
///   sum from 0 to 6; the widths 0, 65 and -1 are each declined with their
///   cause on standard error, and the run is stuck at the draw.
/// - witness: `tests::run::a_script_draws_fair_bits_5707`
#[spec(
    captures: [random = request.signature.name().as_ref() == RAND],
    ensures: |ret| ret.is_none() != random,
)]
pub(super) fn served<Abort>(
    console: &mut dyn Console,
    request: HostRequest<'_>,
    values: &mut HostValues<'_>,
) -> Option<HostReply<Abort>>
{
    if request.signature.name().as_ref() != RAND {
        return None;
    }
    let answered = width(request.operation, request.payload, values)
        .and_then(draw)
        .and_then(|drawn| reply(drawn, values).ok_or(Declined::Store));
    Some(match answered {
        Ok(reply) => HostReply::Resume(reply),
        Err(declined) => {
            let line = format!("{RAND}.{}: {declined}", request.operation.as_ref());
            match console.eprint(Line::from(line.as_str())) {
                Printed::Written | Printed::Failed => {},
            }
            HostReply::Decline
        },
    })
}

/// The width that the payload of `operation` gives a draw.
///
/// # Specification
/// - ensures: the width, from one to [`WIDEST`], when `operation` is `draw` and
///   its payload is such an integer.
/// - fails: another operation, a payload that is not an integer, and an integer
///   outside the range are each refused by name.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the widths 0, 65 and -1 are each refused, and 1 and 64
///   are each taken.
/// - witness: `evaluate::rand::tests::a_draw_lies_below_two_to_its_width_at_each_width`
/// - witness: `tests::run::a_script_draws_fair_bits_5707`
#[spec(ensures: |ref ret| ret.as_ref().map_or(true, |width| (1 ..= WIDEST).contains(&width.0)))]
fn width(
    operation: &OperationName,
    payload: HeapValueId,
    values: &HostValues<'_>,
) -> Result<Width, Declined>
{
    if operation.as_ref() != DRAW {
        return Err(Declined::Operation);
    }
    let Some(&HeapValue::Literal(Literal::Integer(ref integer))) = values.value(payload)
    else {
        return Err(Declined::Payload);
    };
    let digits = integer.magnitude().as_ref();
    match integer.sign() {
        Sign::Negative => Err(Declined::Width(format!("-{digits}"))),
        Sign::NonNegative => digits
            .parse::<u32>()
            .ok()
            .filter(|bits| (1 ..= WIDEST).contains(bits))
            .map(Width)
            .ok_or_else(|| Declined::Width(digits.to_owned())),
    }
}

/// Draw `width` fair bits from the entropy source of the operating system:
/// the high bits of one word of eight bytes.
///
/// # Specification
/// - ensures: an integer below `2^width`.
/// - fails: a source that fails is refused with its error.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — at each width from one to 64, each draw lies below
///   `2^width`; 256 draws of two bits give each of the four values.
/// - witness: `evaluate::rand::tests::a_draw_lies_below_two_to_its_width_at_each_width`
/// - witness: `evaluate::rand::tests::draws_of_two_bits_give_each_of_the_four_values`
#[spec(ensures: |ref ret| ret.as_ref().map_or(true, |drawn| drawn.0.checked_shr(width.0).is_none_or(|above| above == 0)))]
fn draw(width: Width) -> Result<Drawn, Declined>
{
    let mut bytes = [0_u8; 8];
    getrandom::fill(&mut bytes).map_err(Declined::Entropy)?;
    let word = u64::from_le_bytes(bytes);
    let unused = WIDEST.saturating_sub(width.0);
    Ok(Drawn(word.checked_shr(unused).unwrap_or(0)))
}

/// `drawn` allocated in `values` as a non-negative integer.
///
/// # Specification
/// trivial.
fn reply(
    drawn: Drawn,
    values: &mut HostValues<'_>,
) -> Option<HeapValueId>
{
    let magnitude = Magnitude::from_decimal_text(drawn.0.to_string())?;
    values
        .allocate(HeapValue::Literal(Literal::Integer(IntegerLiteral::new(
            Sign::NonNegative,
            magnitude,
        ))))
        .ok()
}
