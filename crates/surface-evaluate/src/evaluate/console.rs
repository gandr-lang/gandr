//! The standard streams of a run, served on its console: the lines that
//! `Console.print` and `Stderr.eprint` perform and the bytes that
//! `Console.write_bytes` performs go to the run's [`Streams`], and
//! `Stdin.read_line` and `Stdin.read_bytes` read from them.
//!
//! The host at a program's entry hands each line to the console. The closed
//! set of the consoles lives in [`gandr_surface_dispatcher::Streams`], below
//! the run stage. A program runs unchanged under each console of the set.

use alloc::boxed::Box;
use alloc::string::ToString as _;
use alloc::vec::Vec;
use core::convert::Infallible;

use anodized::spec;
use gandr_core_sequent::ConstructorTag;
use gandr_core_sequent::HeapValue;
use gandr_core_sequent::HeapValueId;
use gandr_core_sequent::ProducerArity;
use gandr_core_term::effect::host::CONSOLE;
use gandr_core_term::effect::host::STDERR;
use gandr_core_term::effect::host::STDIN;
use gandr_kernel_term::FixedInteger;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Sign;
use gandr_kernel_term::StringLiteral;
use gandr_runtime_emitter::HostHandler;
use gandr_runtime_emitter::HostReply;
use gandr_runtime_emitter::HostRequest;
use gandr_runtime_emitter::HostValues;
use gandr_runtime_emitter::TaskOrder;
use gandr_surface_dispatcher::Bytes;
use gandr_surface_dispatcher::Console as _;
use gandr_surface_dispatcher::Input;
use gandr_surface_dispatcher::Line;
use gandr_surface_dispatcher::Printed;
use gandr_surface_dispatcher::Streams;
use gandr_surface_dispatcher::Wrote;

use super::rand::Draws;
use super::rand::answered;

/// The operation of [`CONSOLE`] that writes a line.
const PRINT: &str = "print";

/// The operation of [`STDERR`] that writes a line.
const EPRINT: &str = "eprint";

/// The operation of [`STDIN`] that reads a line.
const READ_LINE: &str = "read_line";

/// The operation of [`CONSOLE`] that writes bytes.
const WRITE_BYTES: &str = "write_bytes";

/// The operation of [`STDIN`] that reads bytes.
const READ_BYTES: &str = "read_bytes";

/// The error number that `read_bytes` replies for a count below 1, `EINVAL`.
const INVALID: i32 = 22;

/// The standard stream a host operation meets, and how.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Stream
{
    /// Standard output, `Console.print`.
    Out,
    /// Standard error, `Stderr.eprint`.
    Err,
    /// Standard input, `Stdin.read_line`.
    In,
    /// Standard output, `Console.write_bytes`.
    OutBytes,
    /// Standard input, `Stdin.read_bytes`.
    InBytes,
}

/// The standard stream `request` meets, or none for any other operation.
///
/// # Specification
/// trivial.
fn stream(request: &HostRequest<'_>) -> Option<Stream>
{
    match (
        request.signature.name().as_ref(),
        request.operation.as_ref(),
    ) {
        (CONSOLE, PRINT) => Some(Stream::Out),
        (STDERR, EPRINT) => Some(Stream::Err),
        (STDIN, READ_LINE) => Some(Stream::In),
        (CONSOLE, WRITE_BYTES) => Some(Stream::OutBytes),
        (STDIN, READ_BYTES) => Some(Stream::InBytes),
        _ => None,
    }
}

/// Serve the standard-stream `request` offers on `console`: the reply the host
/// gives, or nothing when the request is another operation.
///
/// # Specification
/// - requires: nothing.
/// - ensures: for `Console.print` and `Stderr.eprint` with a string payload,
///   the line handed to `console` on its stream and the unit allocated as the
///   reply; for `Stdin.read_line`, the line `console` reads allocated as the
///   reply. For `Console.write_bytes` with a list of `u8`, the bytes handed to
///   `console` and their count as the reply, or the negative error number of
///   the console. For `Stdin.read_bytes` with an integer `n`, the pair of the
///   count of the bytes of one read of at most `n` and those bytes as a list,
///   or of a negative error number and the empty list; a count below 1 replies
///   `-22`. A decline when a payload has another form, a line could not be read
///   or written, or the store refused the reply; nothing for any other
///   operation.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — as [`gandr_surface_dispatcher::Console::print`],
///   [`gandr_surface_dispatcher::Console::eprint`] and
///   [`gandr_surface_dispatcher::Console::read_line`].
/// - witness: `evaluate::entry::tests::an_entry_prints_through_its_console_2279`
/// - witness: `evaluate::entry::tests::an_entry_reads_and_writes_the_three_streams_2970`
/// - witness: `evaluate::entry::tests::an_entry_reads_and_writes_bytes`
///
/// # Cost
/// - allocation: the reply in the store, the line that the console reads, and
///   the bytes that it reads or writes, growth within the run's store
#[spec(
    captures: [streaming = stream(&request).is_some()],
    ensures: |ret| ret.is_none() || streaming,
)]
pub(super) fn served<Abort>(
    console: &mut Streams<'_>,
    request: HostRequest<'_>,
    values: &mut HostValues<'_>,
) -> Option<HostReply<Abort>>
{
    let met = stream(&request)?;
    match met {
        Stream::In => {
            let Input::Line(line) = console.read_line()
            else {
                return Some(HostReply::Decline);
            };
            return Some(
                values
                    .allocate(HeapValue::Literal(Literal::Text(StringLiteral::new(line))))
                    .map_or(HostReply::Decline, HostReply::Resume),
            );
        },
        Stream::InBytes => return Some(read_bytes(console, request.payload, values)),
        Stream::OutBytes => return Some(write_bytes(console, request.payload, values)),
        Stream::Out | Stream::Err => {},
    }
    let Some(&HeapValue::Literal(Literal::Text(ref text))) = values.value(request.payload)
    else {
        return Some(HostReply::Decline);
    };
    let line = Line::from(text.as_ref());
    let written = if met == Stream::Err {
        console.eprint(line)
    }
    else {
        console.print(line)
    };
    if written == Printed::Failed {
        return Some(HostReply::Decline);
    }
    Some(
        values
            .allocate(HeapValue::Constructed {
                tag: ConstructorTag::Tuple(ProducerArity::ZERO),
                fields: Box::new([]),
            })
            .map_or(HostReply::Decline, HostReply::Resume),
    )
}

/// `Stdin.read_bytes` with the payload `payload` served on `console`.
///
/// # Specification
/// trivial.
///
/// # Cost
/// - allocation: the bytes read and their list in the store, growth within the
///   run's store
fn read_bytes<Abort>(
    console: &mut Streams<'_>,
    payload: HeapValueId,
    values: &mut HostValues<'_>,
) -> HostReply<Abort>
{
    let Some(&HeapValue::Literal(Literal::Integer(ref count))) = values.value(payload)
    else {
        return HostReply::Decline;
    };
    let limit = if count.sign() == Sign::Negative {
        0
    }
    else {
        count
            .magnitude()
            .as_ref()
            .parse::<usize>()
            .unwrap_or(usize::MAX)
    };
    let (count, bytes) = if limit == 0 {
        (i64::from(INVALID).saturating_neg(), Vec::new())
    }
    else {
        match console.read_bytes(limit) {
            Bytes::Read(bytes) => (i64::try_from(bytes.len()).unwrap_or(i64::MAX), bytes),
            Bytes::Failed(number) => (i64::from(i32::from(number)).saturating_neg(), Vec::new()),
        }
    };
    let Some(count) = integer(values, count)
    else {
        return HostReply::Decline;
    };
    let Some(list) = byte_list(values, &bytes)
    else {
        return HostReply::Decline;
    };
    values
        .allocate(HeapValue::Constructed {
            tag: ConstructorTag::Tuple(ProducerArity::TWO),
            fields: Box::new([count, list]),
        })
        .map_or(HostReply::Decline, HostReply::Resume)
}

/// `Console.write_bytes` with the payload `payload` served on `console`.
///
/// # Specification
/// trivial.
///
/// # Cost
/// - allocation: the bytes of the payload and the reply in the store, growth
///   within the run's store
fn write_bytes<Abort>(
    console: &mut Streams<'_>,
    payload: HeapValueId,
    values: &mut HostValues<'_>,
) -> HostReply<Abort>
{
    let mut bytes = Vec::new();
    let mut cell = payload;
    loop {
        match values.value(cell) {
            Some(&HeapValue::Constructed {
                tag: ConstructorTag::ListNil,
                ..
            }) => break,
            Some(&HeapValue::Constructed {
                tag: ConstructorTag::ListCons,
                ref fields,
            }) => {
                let [head, tail] = **fields
                else {
                    return HostReply::Decline;
                };
                let Some(&HeapValue::Literal(Literal::Fixed(FixedInteger::U8(byte)))) =
                    values.value(head)
                else {
                    return HostReply::Decline;
                };
                bytes.push(byte);
                cell = tail;
            },
            Some(_) | None => return HostReply::Decline,
        }
    }
    let count = match console.write_bytes(&bytes) {
        Wrote::Written => i64::try_from(bytes.len()).unwrap_or(i64::MAX),
        Wrote::Failed(number) => i64::from(i32::from(number)).saturating_neg(),
    };
    integer(values, count).map_or(HostReply::Decline, HostReply::Resume)
}

/// The integer `value`, allocated in `values`.
///
/// # Specification
/// trivial.
fn integer(
    values: &mut HostValues<'_>,
    value: i64,
) -> Option<HeapValueId>
{
    let sign = if value < 0 {
        Sign::Negative
    }
    else {
        Sign::NonNegative
    };
    let magnitude = Magnitude::from_decimal_text(value.unsigned_abs().to_string())?;
    values
        .allocate(HeapValue::Literal(Literal::Integer(IntegerLiteral::new(
            sign, magnitude,
        ))))
        .ok()
}

/// The list of the bytes `bytes`, each a `u8`, allocated in `values`.
///
/// # Specification
/// trivial.
fn byte_list(
    values: &mut HostValues<'_>,
    bytes: &[u8],
) -> Option<HeapValueId>
{
    let mut list = values
        .allocate(HeapValue::Constructed {
            tag: ConstructorTag::ListNil,
            fields: Box::new([]),
        })
        .ok()?;
    // The list is built from its last byte.
    for &byte in bytes.iter().rev() {
        let head = values
            .allocate(HeapValue::Literal(Literal::Fixed(FixedInteger::U8(byte))))
            .ok()?;
        list = values
            .allocate(HeapValue::Constructed {
                tag: ConstructorTag::ListCons,
                fields: Box::new([head, list]),
            })
            .ok()?;
    }
    Some(list)
}

/// The host of a run that only meets the standard streams: each of their
/// operations is served on its console, and every other one is declined. The
/// host crosses threads as its console does, so a concurrent run's reader may
/// hold it. Given the draws of the exact model, it also answers each
/// `Rand.draw` from them, and switches between ready tasks in the order it is
/// given.
pub(super) struct PrintingHost<'console>
{
    /// Where the run's printed lines go.
    console: Streams<'console>,
    /// The answers of the exact model, when the run takes them.
    draws: Option<&'console mut Draws>,
    /// The order in which the run's ready tasks take their turns.
    order: TaskOrder,
}

impl<'console> PrintingHost<'console>
{
    /// The host writing to `console`.
    ///
    /// # Specification
    /// trivial.
    pub(super) const fn new(console: Streams<'console>) -> Self
    {
        Self {
            console,
            draws: None,
            order: TaskOrder::Oldest,
        }
    }

    /// The host writing to `console`, answering each draw from `draws`, and
    /// switching between ready tasks in `order`.
    ///
    /// # Specification
    /// trivial.
    pub(super) const fn drawing(
        console: Streams<'console>,
        draws: &'console mut Draws,
        order: TaskOrder,
    ) -> Self
    {
        Self {
            console,
            draws: Some(draws),
            order,
        }
    }
}

impl HostHandler for PrintingHost<'_>
{
    type Abort = Infallible;

    /// Serve a standard-stream operation on the console, and a draw from the
    /// exact model's answers when the host holds them; decline every other
    /// operation.
    ///
    /// # Specification
    /// trivial.
    fn handle(
        &mut self,
        request: HostRequest<'_>,
        values: &mut HostValues<'_>,
    ) -> HostReply<Self::Abort>
    {
        if let Some(reply) = served(&mut self.console, request, values) {
            return reply;
        }
        match self.draws {
            Some(ref mut draws) => {
                answered(&mut self.console, draws, request, values).unwrap_or(HostReply::Decline)
            },
            None => HostReply::Decline,
        }
    }

    /// The order the host was given.
    ///
    /// # Specification
    /// trivial.
    fn task_order(&mut self) -> TaskOrder
    {
        self.order
    }
}
