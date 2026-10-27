//! The endpoint's thread: a single-threaded runtime that binds the iroh
//! endpoint, then answers each request in the order it arrives, holding every
//! stream the endpoint opened or accepted until it is closed. Beside the
//! requests, a task accepts every connection the endpoint is offered: a
//! dialer's stream waits for the owner's `accept`, and a fetch is answered
//! from the endpoint's chunks at once, whatever the owner is waiting on.

use alloc::collections::BTreeMap;
use core::net::SocketAddr;
use core::time::Duration;
use std::sync::mpsc;

use gandr_storage_values::ValueManifest;
use iroh::endpoint::ApplicationClose;
use iroh::endpoint::Connection;
use iroh::endpoint::ConnectionError;
use iroh::endpoint::Incoming;
use iroh::endpoint::ReadError;
use iroh::endpoint::ReadExactError;
use iroh::endpoint::RecvStream;
use iroh::endpoint::SendStream;
use iroh::endpoint::StoppedError;
use iroh::endpoint::VarInt;

use super::ALPN;
use super::Binding;
use super::Fault;
use super::Frame;
use super::Lookup;
use super::MAX_FRAME;
use super::StreamId;
use crate::chunks::CHUNKS_ALPN;
use crate::chunks::Chunks;
use crate::chunks::Fetched;
use crate::chunks::Framed;
use crate::peer::NodeId;

/// The code a connection closes with once both ends closed their stream.
const CLOSED: u32 = 0;

/// The code a connection closes with when a frame announced is oversized.
const REFUSED: u32 = 1;

/// How long a dropped endpoint waits for its connections to close.
const GRACE: Duration = Duration::from_secs(2);

/// The most bytes a fetch's request holds: a frame's 16 MiB.
const MAX_REQUEST: usize = 0x0100_0000_usize;

/// The most bytes a fetch's answer holds: 256 MiB.
const MAX_ANSWER: usize = 0x1000_0000_usize;

/// Where the thread answers one request.
pub(super) type Reply<Answered> = mpsc::SyncSender<Result<Answered, Fault>>;

/// Where the accepting task hands a dialer's stream, with the key it proved.
type Arriving = tokio::sync::mpsc::UnboundedSender<(NodeId, Held)>;

/// Where the owner's `accept` takes the next dialer's stream.
type Arrivals = tokio::sync::mpsc::UnboundedReceiver<(NodeId, Held)>;

/// What the endpoint's owner asks of its thread.
#[derive(Debug)]
pub(super) enum Request
{
    /// Dial a peer and open a stream to it.
    Connect(NodeId, iroh::EndpointAddr, Reply<StreamId>),
    /// Wait for a dialer's stream.
    Accept(Reply<(NodeId, StreamId)>),
    /// Send a frame on a stream.
    Send(StreamId, Frame, Reply<()>),
    /// Receive a frame on a stream.
    Recv(StreamId, Reply<Frame>),
    /// Close a stream.
    Close(StreamId, Reply<()>),
    /// Fetch a value's chunks from a peer: the value, and the request naming
    /// it and the values held.
    Fetch(
        NodeId,
        iroh::EndpointAddr,
        (ValueManifest, Framed),
        Reply<Fetched>,
    ),
    /// Close the endpoint and end the thread.
    Shutdown,
}

/// A stream the endpoint holds, with the connection it alone runs on.
#[derive(Debug)]
struct Held
{
    /// The connection.
    connection: Connection,
    /// This end's half.
    send: SendStream,
    /// The peer's half.
    recv: RecvStream,
}

/// The streams the endpoint holds, the next name it mints, and the dialers'
/// streams not yet accepted.
#[derive(Debug)]
struct Streams
{
    /// The next name.
    next: u64,
    /// Each held stream, by name.
    held: BTreeMap<StreamId, Held>,
    /// The dialers' streams, in the order their first bytes arrived.
    arrivals: Arrivals,
}

/// Run the endpoint `binding` describes on this thread: answer `ready` with
/// its sockets once bound, or with why it did not bind, then serve `inbox`
/// until it asks for shutdown or closes.
///
/// # Specification
/// trivial.
pub(super) fn run(
    binding: &Binding,
    inbox: tokio::sync::mpsc::UnboundedReceiver<Request>,
    ready: &mpsc::SyncSender<Result<Vec<SocketAddr>, Fault>>,
)
{
    match tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
    {
        Ok(runtime) => runtime.block_on(serve(binding, inbox, ready)),
        Err(refused) => answer(
            ready,
            Err(Fault::Bind {
                reason: refused.to_string(),
            }),
        ),
    }
}

/// Bind, report, and answer requests until shutdown.
///
/// # Specification
/// trivial.
async fn serve(
    binding: &Binding,
    mut inbox: tokio::sync::mpsc::UnboundedReceiver<Request>,
    ready: &mpsc::SyncSender<Result<Vec<SocketAddr>, Fault>>,
)
{
    let endpoint = match bind(binding).await {
        Ok(endpoint) => endpoint,
        Err(fault) => {
            answer(ready, Err(fault));
            return;
        },
    };
    answer(ready, Ok(endpoint.bound_sockets()));
    let (arriving, arrivals) = tokio::sync::mpsc::unbounded_channel();
    let accepting = tokio::spawn(admit(endpoint.clone(), arriving, binding.chunks.clone()));
    let mut streams = Streams {
        next: 0,
        held: BTreeMap::new(),
        arrivals,
    };
    while let Some(request) = inbox.recv().await {
        match request {
            Request::Connect(peer, dialed, reply) => {
                answer(&reply, streams.connect(&endpoint, peer, dialed).await);
            },
            Request::Accept(reply) => answer(&reply, streams.accept().await),
            Request::Send(stream, frame, reply) => {
                answer(&reply, streams.send(stream, &frame).await);
            },
            Request::Recv(stream, reply) => answer(&reply, streams.recv(stream).await),
            Request::Close(stream, reply) => answer(&reply, streams.close(stream).await),
            Request::Fetch(peer, dialed, (wanted, request), reply) => {
                let fetched = fetch(
                    &endpoint,
                    &binding.chunks,
                    (peer, dialed),
                    (&wanted, &request),
                );
                answer(&reply, fetched.await);
            },
            Request::Shutdown => break,
        }
    }
    accepting.abort();
    tokio::time::timeout(GRACE, endpoint.close())
        .await
        .unwrap_or_default();
}

/// The iroh endpoint `binding` describes, bound.
///
/// # Specification
/// trivial.
async fn bind(binding: &Binding) -> Result<iroh::Endpoint, Fault>
{
    let refused = |reason: String| Fault::Bind { reason };
    let mut builder = iroh::Endpoint::builder(iroh::endpoint::presets::Minimal)
        .secret_key(binding.secret.key())
        .alpns(Vec::from([ALPN.to_vec(), CHUNKS_ALPN.to_vec()]))
        .relay_mode(iroh::RelayMode::Disabled);
    for &socket in &binding.sockets {
        builder = builder
            .bind_addr(socket)
            .map_err(|invalid| refused(invalid.to_string()))?;
    }
    if binding.lookup == Lookup::Mdns {
        builder = builder.address_lookup(iroh_mdns_address_lookup::MdnsAddressLookup::builder());
    }
    builder
        .bind()
        .await
        .map_err(|unbound| refused(unbound.to_string()))
}

/// Hand `answered` to whoever asked; one who stopped waiting is not told.
///
/// # Specification
/// trivial.
fn answer<Answered>(
    reply: &mpsc::SyncSender<Answered>,
    answered: Answered,
)
{
    match reply.send(answered) {
        Ok(()) | Err(mpsc::SendError(_)) => {},
    }
}

/// Accept every connection the endpoint is offered until it closes, each
/// handshake on a task of its own.
///
/// # Specification
/// trivial.
async fn admit(
    endpoint: iroh::Endpoint,
    arriving: Arriving,
    chunks: Chunks,
)
{
    while let Some(incoming) = endpoint.accept().await {
        tokio::spawn(handshake(incoming, arriving.clone(), chunks.clone()));
    }
}

/// Finish the handshake `incoming` began: answer a fetch from `chunks`, or
/// hand a dialer's stream to `arriving` once its first bytes arrive. A
/// handshake that fails is dropped unanswered.
///
/// # Specification
/// trivial.
async fn handshake(
    incoming: Incoming,
    arriving: Arriving,
    chunks: Chunks,
)
{
    let Ok(connection) = incoming.await
    else {
        return;
    };
    if connection.alpn() == CHUNKS_ALPN {
        serve_chunks(&connection, &chunks).await;
        return;
    }
    let Ok((send, recv)) = connection.accept_bi().await
    else {
        return;
    };
    let peer = NodeId::from(connection.remote_id());
    // An owner gone has dropped its arrivals; the stream goes with the
    // endpoint.
    match arriving.send((peer, Held {
        connection,
        send,
        recv,
    })) {
        Ok(()) | Err(_) => {},
    }
}

/// Answer the fetch `connection` carries from `chunks`: read the request to
/// its end, write the answer and finish, then wait until the asker holds
/// every byte. A request that does not read or is refused closes the
/// connection refused, unanswered.
///
/// # Specification
/// trivial.
async fn serve_chunks(
    connection: &Connection,
    chunks: &Chunks,
)
{
    let Ok((mut send, mut recv)) = connection.accept_bi().await
    else {
        return;
    };
    let answered = recv
        .read_to_end(MAX_REQUEST)
        .await
        .ok()
        .and_then(|request| chunks.answer(&Framed::from(request)).ok());
    let Some(answered) = answered
    else {
        connection.close(VarInt::from_u32(REFUSED), b"refused");
        return;
    };
    if send.write_all(answered.as_ref()).await.is_err() || send.finish().is_err() {
        return;
    }
    // The asker closes the connection once it holds every byte.
    match send.stopped().await {
        Ok(Some(_) | None) | Err(_) => {},
    }
}

/// Fetch `wanted` from `peer` at `dialed` into `chunks` with `request`, on a
/// connection of its own closed before this returns.
///
/// # Specification
/// trivial.
async fn fetch(
    endpoint: &iroh::Endpoint,
    chunks: &Chunks,
    (peer, dialed): (NodeId, iroh::EndpointAddr),
    (wanted, request): (&ValueManifest, &Framed),
) -> Result<Fetched, Fault>
{
    let failed = |reason: String| Fault::Fetch { peer, reason };
    let connection = endpoint
        .connect(dialed, CHUNKS_ALPN)
        .await
        .map_err(|unreached| failed(unreached.to_string()))?;
    let (mut send, mut recv) = connection
        .open_bi()
        .await
        .map_err(|unopened| failed(unopened.to_string()))?;
    send.write_all(request.as_ref())
        .await
        .map_err(|unwritten| failed(unwritten.to_string()))?;
    send.finish()
        .map_err(|unfinished| failed(unfinished.to_string()))?;
    let answer = recv
        .read_to_end(MAX_ANSWER)
        .await
        .map_err(|unread| failed(unread.to_string()));
    connection.close(VarInt::from_u32(CLOSED), b"fetched");
    let answer = answer?;
    chunks.admit(peer, wanted, &Framed::from(answer))
}

/// Whether a connection was lost to the peer closing after its own close,
/// which leaves nothing of this end's unsent.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(transparent)]
struct Clean(bool);

/// Whether `error` is the peer closing after its own close.
///
/// # Specification
/// trivial.
fn closed_cleanly(error: &ConnectionError) -> Clean
{
    Clean(
        matches!(*error, ConnectionError::ApplicationClosed(ApplicationClose { error_code, .. }) if error_code == VarInt::from_u32(CLOSED)),
    )
}

impl Streams
{
    /// Hold `held` under a fresh name.
    ///
    /// # Specification
    /// trivial.
    fn hold(
        &mut self,
        held: Held,
    ) -> Result<StreamId, Fault>
    {
        let stream = StreamId(self.next);
        self.next = self.next.checked_add(1).ok_or(Fault::Exhausted)?;
        self.held.insert(stream, held);
        Ok(stream)
    }

    /// The stream named `stream`.
    ///
    /// # Specification
    /// trivial.
    fn held(
        &mut self,
        stream: StreamId,
    ) -> Result<&mut Held, Fault>
    {
        self.held.get_mut(&stream).ok_or(Fault::Unknown(stream))
    }

    /// Dial `peer` at `dialed` and open a stream.
    ///
    /// # Specification
    /// trivial.
    async fn connect(
        &mut self,
        endpoint: &iroh::Endpoint,
        peer: NodeId,
        dialed: iroh::EndpointAddr,
    ) -> Result<StreamId, Fault>
    {
        let refused = |reason: String| Fault::Connect { peer, reason };
        let connection = endpoint
            .connect(dialed, ALPN)
            .await
            .map_err(|unreached| refused(unreached.to_string()))?;
        let (send, recv) = connection
            .open_bi()
            .await
            .map_err(|unopened| refused(unopened.to_string()))?;
        self.hold(Held {
            connection,
            send,
            recv,
        })
    }

    /// Take the next dialer's stream, waiting for one.
    ///
    /// # Specification
    /// trivial.
    async fn accept(&mut self) -> Result<(NodeId, StreamId), Fault>
    {
        let (peer, held) = self.arrivals.recv().await.ok_or(Fault::Accept)?;
        let stream = self.hold(held)?;
        Ok((peer, stream))
    }

    /// Send `frame` on `stream`, its length first.
    ///
    /// # Specification
    /// trivial.
    async fn send(
        &mut self,
        stream: StreamId,
        frame: &Frame,
    ) -> Result<(), Fault>
    {
        let bytes = frame.as_ref();
        let length = u32::try_from(bytes.len())
            .ok()
            .filter(|&length| length <= MAX_FRAME)
            .ok_or_else(|| Fault::Oversized {
                length: u64::try_from(bytes.len()).unwrap_or(u64::MAX),
            })?;
        let held = self.held(stream)?;
        let failed = |reason: String| Fault::Stream { stream, reason };
        held.send
            .write_all(&length.to_le_bytes())
            .await
            .map_err(|unwritten| failed(unwritten.to_string()))?;
        held.send
            .write_all(bytes)
            .await
            .map_err(|unwritten| failed(unwritten.to_string()))
    }

    /// Receive the next frame on `stream`.
    ///
    /// # Specification
    /// trivial.
    async fn recv(
        &mut self,
        stream: StreamId,
    ) -> Result<Frame, Fault>
    {
        let unread = |error: ReadExactError| match error {
            ReadExactError::FinishedEarly(_) => Fault::Ended(stream),
            ReadExactError::ReadError(ReadError::ConnectionLost(ref lost))
                if closed_cleanly(lost).0 =>
            {
                Fault::Ended(stream)
            },
            ReadExactError::ReadError(failed) => Fault::Stream {
                stream,
                reason: failed.to_string(),
            },
        };
        let held = self.held(stream)?;
        let mut prefix = [0_u8; 4];
        held.recv.read_exact(&mut prefix).await.map_err(unread)?;
        let length = u32::from_le_bytes(prefix);
        if length > MAX_FRAME {
            if let Some(refused) = self.held.remove(&stream) {
                refused
                    .connection
                    .close(VarInt::from_u32(REFUSED), b"oversized frame");
            }
            return Err(Fault::Oversized {
                length: u64::from(length),
            });
        }
        let mut frame = vec![0_u8; usize::try_from(length).unwrap_or(usize::MAX)];
        held.recv.read_exact(&mut frame).await.map_err(unread)?;
        Ok(Frame::from(frame))
    }

    /// Close `stream`: finish this end, drain the peer's until it finishes,
    /// wait for the peer to hold every byte sent, then close the connection.
    ///
    /// # Specification
    /// trivial.
    async fn close(
        &mut self,
        stream: StreamId,
    ) -> Result<(), Fault>
    {
        let Held {
            connection,
            mut send,
            mut recv,
        } = self.held.remove(&stream).ok_or(Fault::Unknown(stream))?;
        let failed = |reason: String| Fault::Stream { stream, reason };
        // A stream the peer reset is finished already.
        match send.finish() {
            Ok(()) | Err(_) => {},
        }
        loop {
            match recv.read_chunk(usize::MAX).await {
                Ok(Some(_)) => {},
                Ok(None) | Err(ReadError::Reset(_) | ReadError::ClosedStream) => break,
                Err(ReadError::ConnectionLost(ref lost)) if closed_cleanly(lost).0 => break,
                Err(unread @ (ReadError::ConnectionLost(_) | ReadError::ZeroRttRejected)) => {
                    return Err(failed(unread.to_string()));
                },
            }
        }
        match send.stopped().await {
            Ok(Some(_) | None) => {},
            Err(StoppedError::ConnectionLost(ref lost)) if closed_cleanly(lost).0 => {},
            Err(unsettled @ (StoppedError::ConnectionLost(_) | StoppedError::ZeroRttRejected)) => {
                return Err(failed(unsettled.to_string()));
            },
        }
        connection.close(VarInt::from_u32(CLOSED), b"closed");
        Ok(())
    }
}
