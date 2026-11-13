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
//! The exact model answers the draws from a path instead ([`Draws`]): the
//! corpus runs a `distributes` declaration once for each sequence of answers,
//! depth first, and reads no entropy. A path that draws past its quota stops
//! at the draw that passes it, and the path is marked so the corpus refuses
//! it by name.
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
use alloc::vec::Vec;
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
use gandr_surface_corpus::Bits;
use gandr_surface_dispatcher::Console;
use gandr_surface_dispatcher::Line;
use gandr_surface_dispatcher::Printed;

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
pub(super) enum Declined
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
    /// The exact model's path draws past its quota: the bits it would take
    /// with this draw.
    PastQuota(u32),
    /// The exact model's run draws another width than its path recorded at
    /// this draw.
    Unreplayed,
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
            Self::PastQuota(bits) => {
                write!(
                    f,
                    "the draws take {bits} bits, past the quota of the exact model"
                )
            },
            Self::Unreplayed => {
                f.write_str("the draw has another width than the path the exact model recorded")
            },
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

/// Whether a path follows: what [`Draws::advance`] answers.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Advanced
{
    /// The draws hold the next path.
    Next,
    /// Every path ran.
    Done,
}

/// The answers of the draws of one path of a run, for the exact model.
///
/// The path's leading draws are answered as recorded, and each draw past
/// them is answered 0 and recorded. [`Self::advance`] then drops the trailing
/// draws at their greatest answer and raises the last one that can rise, so
/// the runs walk every sequence of answers depth first, each once. The first
/// draw a run declines is kept, so the corpus names its cause.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct Draws
{
    /// Each draw of the path, in order: its width and its answer.
    path: Vec<(Width, Drawn)>,
    /// How many leading draws of the path this run answers as recorded.
    fixed: usize,
    /// How many draws this run has answered.
    taken: usize,
    /// The bits this run's draws take.
    bits: u32,
    /// The most bits one path may draw.
    quota: u32,
    /// The bits a draw past the quota would take, when one was asked.
    past: Option<u32>,
    /// Why the first draw this run declined was declined, when one was.
    declined: Option<Declined>,
}

impl Draws
{
    /// The draws of the first path: none recorded yet, each answered 0.
    ///
    /// # Specification
    /// trivial.
    pub(super) fn new(quota: Bits) -> Self
    {
        Self {
            path: Vec::new(),
            fixed: 0,
            taken: 0,
            bits: 0,
            quota: u32::from(quota),
            past: None,
            declined: None,
        }
    }

    /// The bits the draws of the last run take.
    ///
    /// # Specification
    /// trivial.
    pub(super) fn bits(&self) -> Bits
    {
        Bits::from(self.bits)
    }

    /// The bits of the first draw past the quota, when the last run asked
    /// one.
    ///
    /// # Specification
    /// trivial.
    pub(super) fn past(&self) -> Option<Bits>
    {
        self.past.map(Bits::from)
    }

    /// Why the first draw the last run declined was declined, when one was.
    ///
    /// # Specification
    /// trivial.
    pub(super) const fn declined(&self) -> Option<&Declined>
    {
        self.declined.as_ref()
    }

    /// The answer to a draw of `width` bits: the path's recorded answer while
    /// the run is within its leading draws, else 0, recorded.
    ///
    /// # Specification
    /// - ensures: an answer below `2^width`; the draw counted with its width.
    /// - fails: a draw past the quota, marked in [`Self::past`], and a width
    ///   other than the one the path recorded, are refused by name.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two draws of two bits walk 16 paths in order, and a
    ///   draw of 17 bits is past the quota.
    /// - witness: `evaluate::rand::tests::two_draws_of_two_bits_walk_sixteen_paths_in_order`
    /// - witness: `evaluate::rand::tests::a_draw_past_the_quota_is_marked`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |drawn| drawn.0.checked_shr(width.0).is_none_or(|above| above == 0)))]
    fn answer(
        &mut self,
        width: Width,
    ) -> Result<Drawn, Declined>
    {
        let bits = self.bits.saturating_add(width.0);
        if bits > self.quota {
            self.past = Some(bits);
            return Err(Declined::PastQuota(bits));
        }
        let drawn = if self.taken < self.fixed {
            match self.path.get(self.taken) {
                Some(&(recorded, drawn)) if recorded == width => drawn,
                Some(_) | None => return Err(Declined::Unreplayed),
            }
        }
        else {
            self.path.push((width, Drawn(0)));
            Drawn(0)
        };
        self.taken = self.taken.saturating_add(1);
        self.bits = bits;
        Ok(drawn)
    }

    /// Move to the next path, depth first: drop the trailing draws at their
    /// greatest answer, and raise the last one that can rise.
    ///
    /// # Specification
    /// - ensures: [`Advanced::Next`] with the next path's leading draws fixed
    ///   and the count of bits reset; [`Advanced::Done`] when every draw of the
    ///   path is at its greatest answer.
    /// - panics: none.
    ///
    /// # Termination
    /// - reason: each pass drops one draw of the finite path or returns.
    /// - measure: the draws left in the path.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::answer`].
    /// - witness: `evaluate::rand::tests::two_draws_of_two_bits_walk_sixteen_paths_in_order`
    #[spec(ensures: |ret| ret == Advanced::Done || self.fixed == self.path.len())]
    pub(super) fn advance(&mut self) -> Advanced
    {
        self.taken = 0;
        self.bits = 0;
        self.past = None;
        self.declined = None;
        while let Some(&mut (width, ref mut drawn)) = self.path.last_mut() {
            let greatest = u64::MAX
                .checked_shr(WIDEST.saturating_sub(width.0))
                .unwrap_or(0);
            if drawn.0 < greatest {
                *drawn = Drawn(drawn.0.saturating_add(1));
                self.fixed = self.path.len();
                return Advanced::Next;
            }
            let _greatest = self.path.pop();
        }
        self.fixed = 0;
        Advanced::Done
    }
}

/// Serve the `Rand` operation that `request` offers from `draws`, the exact
/// model: the reply the path gives, or nothing when the request is another
/// interface's.
///
/// # Specification
/// - requires: nothing.
/// - ensures: for `draw`, the answer [`Draws::answer`] gives. A decline when
///   the width is not an integer from one to 64, when the path draws past its
///   quota, or when the run draws another width than the path recorded; one
///   line on `console`'s standard error names the cause first, and `draws`
///   keeps the cause of the run's first decline. Nothing for any other
///   interface.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the exemplar's two draws of two bits settle their stated
///   distribution, and a draw of 17 bits is refused past the quota.
/// - witness: `tests::corpus::a_distribution_settles_over_every_answer_of_its_draws_5710`
#[spec(
    captures: [random = request.signature.name().as_ref() == RAND],
    ensures: |ret| ret.is_none() != random,
)]
pub(super) fn answered<Abort, Printer>(
    console: &mut Printer,
    draws: &mut Draws,
    request: HostRequest<'_>,
    values: &mut HostValues<'_>,
) -> Option<HostReply<Abort>>
where
    Printer: Console + ?Sized,
{
    if request.signature.name().as_ref() != RAND {
        return None;
    }
    let answered = width(request.operation, request.payload, values)
        .and_then(|width| draws.answer(width))
        .and_then(|drawn| reply(drawn, values).ok_or(Declined::Store));
    Some(match answered {
        Ok(reply) => HostReply::Resume(reply),
        Err(declined) => {
            let line = format!("{RAND}.{}: {declined}", request.operation.as_ref());
            match console.eprint(Line::from(line.as_str())) {
                Printed::Written | Printed::Failed => {},
            }
            if draws.declined.is_none() {
                draws.declined = Some(declined);
            }
            HostReply::Decline
        },
    })
}
