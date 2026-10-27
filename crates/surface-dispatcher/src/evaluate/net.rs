//! The network a run reaches: where the operations of `Net` go.
//!
//! The host at a program's entry hands each `Net` operation to the run's
//! [`Net`]: `connect` dials the peer its string spells, `accept` waits for a
//! dialer and replies its key and the stream, `transmit` and `receive` carry
//! one frame, and `disconnect` closes a stream. A stream is the integer the
//! network minted for it, held by this host alone. A frame is a string sent
//! as its UTF-8 bytes, so a frame received that is not UTF-8 is refused. An
//! operation the network refuses, or whose payload is not what `Net`
//! declares, is declined, and the run is stuck at it.

use alloc::boxed::Box;
use alloc::string::String;
use alloc::string::ToString as _;
use alloc::vec::Vec;
use core::str::FromStr as _;

use anodized::spec;
use gandr_core_sequent::ConstructorTag;
use gandr_core_sequent::HeapValue;
use gandr_core_sequent::HeapValueId;
use gandr_core_sequent::ProducerArity;
use gandr_core_term::effect::OperationName;
use gandr_core_term::effect::host::NET;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Sign;
use gandr_kernel_term::StringLiteral;
use gandr_runtime_emitter::HostReply;
use gandr_runtime_emitter::HostRequest;
use gandr_runtime_emitter::HostValues;
use gandr_runtime_net::Frame;
use gandr_runtime_net::Net;
use gandr_runtime_net::Peer;
use gandr_runtime_net::StreamId;

/// The operation of [`NET`] that dials a peer.
const CONNECT: &str = "connect";
/// The operation of [`NET`] that waits for a dialer.
const ACCEPT: &str = "accept";
/// The operation of [`NET`] that sends a frame.
const TRANSMIT: &str = "transmit";
/// The operation of [`NET`] that receives a frame.
const RECEIVE: &str = "receive";
/// The operation of [`NET`] that closes a stream.
const DISCONNECT: &str = "disconnect";

/// What a `Net` operation's payload asks, read out of the run's store.
#[derive(Clone, Debug)]
enum Asked
{
    /// Dial the peer.
    Connect(Peer),
    /// Wait for a dialer.
    Accept,
    /// Send the frame on the stream.
    Transmit(StreamId, Frame),
    /// Receive a frame on the stream.
    Receive(StreamId),
    /// Close the stream.
    Disconnect(StreamId),
}

/// What a `Net` operation answered, to be allocated as its reply.
#[derive(Clone, Debug)]
enum Answered
{
    /// A stream.
    Stream(StreamId),
    /// A dialer's key and its stream.
    Accepted(String, StreamId),
    /// A frame.
    Frame(String),
    /// The unit.
    Done,
}

/// Serve the `Net` operation `request` offers on `net`: the reply the host
/// gives, or nothing when the request is another interface's.
///
/// # Specification
/// - requires: nothing.
/// - ensures: for a `Net` operation whose payload is what `Net` declares, the
///   operation performed on `net` and its answer allocated as the reply:
///   `connect` a stream, `accept` the dialer's key spelled in hex beside a
///   stream, `transmit` and `disconnect` the unit, `receive` the frame as a
///   string. A decline when the payload is not what `Net` declares, names no
///   stream or no peer, the network refuses, a received frame is not UTF-8, or
///   the store refuses the reply; nothing for any other interface.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the ping exemplar dials an endpoint on loopback and
///   drives `connect`, `transmit`, `receive` and `disconnect`, the endpoint
///   answering; a `transmit` on a stream no network minted is declined.
///   `accept` is driven by the driver's two-process case.
/// - witness: `tests::run::a_script_pings_over_its_network_3186`
#[spec(
    captures: [networked = request.signature.name().as_ref() == NET],
    ensures: |ret| ret.is_none() != networked,
)]
pub(super) fn served<Abort>(
    net: &mut Net,
    request: HostRequest<'_>,
    values: &mut HostValues<'_>,
) -> Option<HostReply<Abort>>
{
    if request.signature.name().as_ref() != NET {
        return None;
    }
    let Some(asked) = asked(request.operation, request.payload, values)
    else {
        return Some(HostReply::Decline);
    };
    let answered = match asked {
        Asked::Connect(peer) => net.connect(&peer).ok().map(Answered::Stream),
        Asked::Accept => net
            .accept()
            .ok()
            .map(|(peer, stream)| Answered::Accepted(peer.to_string(), stream)),
        Asked::Transmit(stream, frame) => net.send(stream, frame).ok().map(|()| Answered::Done),
        Asked::Receive(stream) => net
            .recv(stream)
            .ok()
            .and_then(|frame| String::from_utf8(Vec::from(frame)).ok())
            .map(Answered::Frame),
        Asked::Disconnect(stream) => net.close(stream).ok().map(|()| Answered::Done),
    };
    Some(
        answered
            .and_then(|answer| reply(answer, values))
            .map_or(HostReply::Decline, HostReply::Resume),
    )
}

/// What `operation` asks of the network, its payload `payload` read out of
/// `values`; nothing when the operation is no `Net` operation or the payload
/// is not what it declares.
///
/// # Specification
/// trivial.
fn asked(
    operation: &OperationName,
    payload: HeapValueId,
    values: &HostValues<'_>,
) -> Option<Asked>
{
    match operation.as_ref() {
        CONNECT => Peer::from_str(text(values, payload)?.as_ref())
            .ok()
            .map(Asked::Connect),
        ACCEPT => Some(Asked::Accept),
        TRANSMIT => {
            let Some(&HeapValue::Constructed {
                tag: ConstructorTag::Tuple(ProducerArity::TWO),
                ref fields,
            }) = values.value(payload)
            else {
                return None;
            };
            let (&stream, &frame) = fields.first().zip(fields.get(1))?;
            let frame: &str = text(values, frame)?.as_ref();
            Some(Asked::Transmit(
                stream_of(values, stream)?,
                Frame::from(frame.as_bytes().to_vec()),
            ))
        },
        RECEIVE => stream_of(values, payload).map(Asked::Receive),
        DISCONNECT => stream_of(values, payload).map(Asked::Disconnect),
        _ => None,
    }
}

/// The string `value` holds.
///
/// # Specification
/// trivial.
fn text<'values>(
    values: &'values HostValues<'_>,
    value: HeapValueId,
) -> Option<&'values StringLiteral>
{
    match values.value(value) {
        Some(&HeapValue::Literal(Literal::Text(ref text))) => Some(text),
        Some(_) | None => None,
    }
}

/// The stream the integer `value` holds names: a non-negative integer that
/// fits 64 bits.
///
/// # Specification
/// trivial.
fn stream_of(
    values: &HostValues<'_>,
    value: HeapValueId,
) -> Option<StreamId>
{
    match values.value(value) {
        Some(&HeapValue::Literal(Literal::Integer(ref integer)))
            if integer.sign() == Sign::NonNegative =>
        {
            integer
                .magnitude()
                .as_ref()
                .parse::<u64>()
                .ok()
                .map(StreamId::from)
        },
        Some(_) | None => None,
    }
}

/// `answer` allocated in `values`: a stream as an integer, a frame as a
/// string, the dialer's key and stream as a pair, and the unit.
///
/// # Specification
/// trivial.
fn reply(
    answer: Answered,
    values: &mut HostValues<'_>,
) -> Option<HeapValueId>
{
    match answer {
        Answered::Stream(stream) => integer(stream, values),
        Answered::Accepted(peer, stream) => {
            let peer = values
                .allocate(HeapValue::Literal(Literal::Text(StringLiteral::new(peer))))
                .ok()?;
            let stream = integer(stream, values)?;
            values
                .allocate(HeapValue::Constructed {
                    tag: ConstructorTag::Tuple(ProducerArity::TWO),
                    fields: Box::new([peer, stream]),
                })
                .ok()
        },
        Answered::Frame(frame) => values
            .allocate(HeapValue::Literal(Literal::Text(StringLiteral::new(frame))))
            .ok(),
        Answered::Done => values
            .allocate(HeapValue::Constructed {
                tag: ConstructorTag::Tuple(ProducerArity::ZERO),
                fields: Box::new([]),
            })
            .ok(),
    }
}

/// `stream` allocated in `values` as the integer naming it.
///
/// # Specification
/// trivial.
fn integer(
    stream: StreamId,
    values: &mut HostValues<'_>,
) -> Option<HeapValueId>
{
    let magnitude = Magnitude::from_decimal_text(u64::from(stream).to_string())?;
    values
        .allocate(HeapValue::Literal(Literal::Integer(IntegerLiteral::new(
            Sign::NonNegative,
            magnitude,
        ))))
        .ok()
}
