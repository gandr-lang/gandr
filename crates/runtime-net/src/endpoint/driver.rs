//! The endpoint's thread: a single-threaded runtime that binds the iroh
//! endpoint, then answers each request in the order it arrives, holding every
//! stream the endpoint opened or accepted until it is closed.

use alloc::collections::BTreeMap;
use core::net::SocketAddr;
use core::time::Duration;
use std::sync::mpsc;

use iroh::endpoint::ApplicationClose;
use iroh::endpoint::Connection;
use iroh::endpoint::ConnectionError;
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
use crate::peer::NodeId;

/// The code a connection closes with once both ends closed their stream.
const CLOSED: u32 = 0;

/// The code a connection closes with when a frame announced is oversized.
const REFUSED: u32 = 1;

/// How long a dropped endpoint waits for its connections to close.
const GRACE: Duration = Duration::from_secs(2);

/// Where the thread answers one request.
pub(super) type Reply<Answered> = mpsc::SyncSender<Result<Answered, Fault>>;

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

/// The streams the endpoint holds, and the next name it mints.
#[derive(Debug, Default)]
struct Streams
{
    /// The next name.
    next: u64,
    /// Each held stream, by name.
    held: BTreeMap<StreamId, Held>,
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
    let mut streams = Streams::default();
    while let Some(request) = inbox.recv().await {
        match request {
            Request::Connect(peer, dialed, reply) => {
                answer(&reply, streams.connect(&endpoint, peer, dialed).await);
            },
            Request::Accept(reply) => answer(&reply, streams.accept(&endpoint).await),
            Request::Send(stream, frame, reply) => {
                answer(&reply, streams.send(stream, &frame).await);
            },
            Request::Recv(stream, reply) => answer(&reply, streams.recv(stream).await),
            Request::Close(stream, reply) => answer(&reply, streams.close(stream).await),
            Request::Shutdown => break,
        }
    }
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
        .alpns(Vec::from([ALPN.to_vec()]))
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

    /// Wait for a dialer's stream, skipping any handshake that fails.
    ///
    /// # Specification
    /// trivial.
    async fn accept(
        &mut self,
        endpoint: &iroh::Endpoint,
    ) -> Result<(NodeId, StreamId), Fault>
    {
        loop {
            let incoming = endpoint.accept().await.ok_or(Fault::Accept)?;
            let Ok(connection) = incoming.await
            else {
                continue;
            };
            let Ok((send, recv)) = connection.accept_bi().await
            else {
                continue;
            };
            let peer = NodeId::from(connection.remote_id());
            let stream = self.hold(Held {
                connection,
                send,
                recv,
            })?;
            return Ok((peer, stream));
        }
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
