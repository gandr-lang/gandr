//! The endpoint's thread: a single-threaded runtime that binds the iroh
//! endpoint, then answers each request in the order it arrives, holding every
//! stream the endpoint opened or accepted until it is closed. Beside the
//! requests, a task accepts every connection the endpoint is offered: a
//! dialer's stream waits for the owner's `accept`, a migration for the owner's
//! `arrive`, and a fetch is answered from the endpoint's chunks at once,
//! whatever the owner is waiting on.

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
use super::PREFIX;
use super::Prefix;
use super::StreamId;
use crate::chunks::CHUNKS_ALPN;
use crate::chunks::Chunks;
use crate::chunks::Fetched;
use crate::chunks::Framed;
use crate::chunks::Malformed;
use crate::peer::NodeId;
use crate::worlds::Answer;
use crate::worlds::Arrival;
use crate::worlds::ArrivalId;
use crate::worlds::Configuration;
use crate::worlds::WORLDS_ALPN;

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

/// Where the accepting task hands a migration once its configuration read.
type Migrating = tokio::sync::mpsc::UnboundedSender<(Configuration, Pending)>;

/// Where the owner's `arrive` takes the next migration.
type Migrations = tokio::sync::mpsc::UnboundedReceiver<(Configuration, Pending)>;

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
    /// Ship a migration to a peer: the configuration framed, and its
    /// captures, named held when the answer is fetched.
    Migrate(
        NodeId,
        iroh::EndpointAddr,
        (Framed, Vec<ValueManifest>),
        Reply<Answer>,
    ),
    /// Wait for a migration.
    Arrive(Reply<Arrival>),
    /// Fetch a value's chunks from an arrival's asker: the value, and the
    /// request naming it and the values held.
    FetchArrived(ArrivalId, (ValueManifest, Framed), Reply<Fetched>),
    /// Answer an arrival with the answer framed.
    Answer(ArrivalId, Framed, Reply<()>),
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

/// A migration waiting for its answer: the asker, its connection, and this
/// end's half of the stream the configuration came on.
#[derive(Debug)]
struct Pending
{
    /// The asker.
    peer: NodeId,
    /// The connection.
    connection: Connection,
    /// The half the answer is written on.
    send: SendStream,
}

/// The migrations the owner holds until it answers them, the next name it
/// mints, the migrations not yet taken, and the answered ones whose askers
/// may still fetch.
#[derive(Debug)]
struct Worlds
{
    /// The next name.
    next: u64,
    /// Each held migration, by name.
    pending: BTreeMap<ArrivalId, Pending>,
    /// The migrations in the order their configurations read.
    migrations: Migrations,
    /// The fetches served on each answered connection, each task ending when
    /// its asker closes the connection.
    answered: tokio::task::JoinSet<()>,
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
    let (migrating, migrations) = tokio::sync::mpsc::unbounded_channel();
    let accepting = tokio::spawn(admit(
        endpoint.clone(),
        (arriving, migrating),
        binding.chunks.clone(),
    ));
    let mut streams = Streams {
        next: 0,
        held: BTreeMap::new(),
        arrivals,
    };
    let mut worlds = Worlds {
        next: 0,
        pending: BTreeMap::new(),
        migrations,
        answered: tokio::task::JoinSet::new(),
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
            Request::Migrate(peer, dialed, (framed, captures), reply) => {
                let migrated = migrate(
                    &endpoint,
                    &binding.chunks,
                    (peer, dialed),
                    (&framed, &captures),
                );
                answer(&reply, migrated.await);
            },
            Request::Arrive(reply) => answer(&reply, worlds.arrive().await),
            Request::FetchArrived(arrival, (wanted, request), reply) => {
                let fetched = worlds.fetch(arrival, &binding.chunks, (&wanted, &request));
                answer(&reply, fetched.await);
            },
            Request::Answer(arrival, framed, reply) => {
                let answered = worlds.answer(arrival, &binding.chunks, &framed);
                answer(&reply, answered.await);
            },
            Request::Shutdown => break,
        }
    }
    accepting.abort();
    // An asker fetches an answer's chunks after the answer is sent, so the
    // connections answered stay open until their askers close them.
    let answered = async { while worlds.answered.join_next().await.is_some() {} };
    tokio::time::timeout(GRACE, answered)
        .await
        .unwrap_or_default();
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
        .alpns(Vec::from([
            ALPN.to_vec(),
            CHUNKS_ALPN.to_vec(),
            WORLDS_ALPN.to_vec(),
        ]))
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
    (arriving, migrating): (Arriving, Migrating),
    chunks: Chunks,
)
{
    while let Some(incoming) = endpoint.accept().await {
        tokio::spawn(handshake(
            incoming,
            (arriving.clone(), migrating.clone()),
            chunks.clone(),
        ));
    }
}

/// Finish the handshake `incoming` began: answer a fetch from `chunks`, hand
/// a migration to `migrating` once its configuration reads, or hand a
/// dialer's stream to `arriving` once its first bytes arrive. A handshake
/// that fails is dropped unanswered.
///
/// # Specification
/// trivial.
async fn handshake(
    incoming: Incoming,
    (arriving, migrating): (Arriving, Migrating),
    chunks: Chunks,
)
{
    let Ok(connection) = incoming.await
    else {
        return;
    };
    if connection.alpn() == CHUNKS_ALPN {
        if let Ok((send, recv)) = connection.accept_bi().await {
            serve_fetch(&connection, (send, recv), &chunks).await;
        }
        return;
    }
    let Ok((send, mut recv)) = connection.accept_bi().await
    else {
        return;
    };
    let peer = NodeId::from(connection.remote_id());
    if connection.alpn() == WORLDS_ALPN {
        let configuration = recv
            .read_to_end(MAX_REQUEST)
            .await
            .ok()
            .and_then(|framed| Configuration::read(&Framed::from(framed)).ok());
        let Some(configuration) = configuration
        else {
            connection.close(VarInt::from_u32(REFUSED), b"refused");
            return;
        };
        // An owner gone has dropped its migrations; the connection goes with
        // the endpoint.
        match migrating.send((configuration, Pending {
            peer,
            connection,
            send,
        })) {
            Ok(()) | Err(_) => {},
        }
        return;
    }
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

/// Answer the fetch on `stream` from `chunks`: read the request to its end,
/// write the answer and finish, then wait until the asker holds every byte.
/// A request that does not read or is refused closes `connection` refused,
/// unanswered. Whether the connection still serves.
///
/// # Specification
/// trivial.
async fn serve_fetch(
    connection: &Connection,
    (mut send, mut recv): (SendStream, RecvStream),
    chunks: &Chunks,
) -> Serving
{
    let answered = recv
        .read_to_end(MAX_REQUEST)
        .await
        .ok()
        .and_then(|request| chunks.answer(&Framed::from(request)).ok());
    let Some(answered) = answered
    else {
        connection.close(VarInt::from_u32(REFUSED), b"refused");
        return Serving(false);
    };
    if send.write_all(answered.as_ref()).await.is_err() || send.finish().is_err() {
        return Serving(false);
    }
    // The asker closes the connection, or reads the answer whole.
    match send.stopped().await {
        Ok(Some(_) | None) => Serving(true),
        Err(_) => Serving(false),
    }
}

/// Whether a connection still serves fetches.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(transparent)]
struct Serving(bool);

/// Answer every fetch the peer opens on `connection` from `chunks`, one after
/// another, until the connection closes or a fetch is refused.
///
/// # Specification
/// trivial.
async fn serve_fetches(
    connection: Connection,
    chunks: Chunks,
)
{
    while let Ok(stream) = connection.accept_bi().await {
        if !serve_fetch(&connection, stream, &chunks).await.0 {
            return;
        }
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
    let connection = endpoint
        .connect(dialed, CHUNKS_ALPN)
        .await
        .map_err(|unreached| Fault::Fetch {
            peer,
            reason: unreached.to_string(),
        })?;
    let fetched = fetch_on(&connection, chunks, peer, (wanted, request)).await;
    connection.close(VarInt::from_u32(CLOSED), b"fetched");
    fetched
}

/// Fetch `wanted` from `peer` into `chunks` with `request`, on a stream of
/// `connection` of its own.
///
/// # Specification
/// trivial.
async fn fetch_on(
    connection: &Connection,
    chunks: &Chunks,
    peer: NodeId,
    (wanted, request): (&ValueManifest, &Framed),
) -> Result<Fetched, Fault>
{
    let failed = |reason: String| Fault::Fetch { peer, reason };
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
        .map_err(|unread| failed(unread.to_string()))?;
    chunks.admit(peer, wanted, &Framed::from(answer))
}

/// Ship the configuration `framed` to `peer` at `dialed`, serving from
/// `chunks` each fetch it makes until it answers, then fetch an answered
/// value's chunks into `chunks`, naming `captures` held; the connection is
/// closed before this returns.
///
/// # Specification
/// trivial.
async fn migrate(
    endpoint: &iroh::Endpoint,
    chunks: &Chunks,
    (peer, dialed): (NodeId, iroh::EndpointAddr),
    (framed, captures): (&Framed, &[ValueManifest]),
) -> Result<Answer, Fault>
{
    let failed = |reason: String| Fault::Migrate { peer, reason };
    let connection = endpoint
        .connect(dialed, WORLDS_ALPN)
        .await
        .map_err(|unreached| failed(unreached.to_string()))?;
    let migrated = ship(&connection, chunks, peer, (framed, captures)).await;
    connection.close(VarInt::from_u32(CLOSED), b"migrated");
    migrated
}

/// [`migrate`] over `connection`, which the caller closes.
///
/// # Specification
/// trivial.
async fn ship(
    connection: &Connection,
    chunks: &Chunks,
    peer: NodeId,
    (framed, captures): (&Framed, &[ValueManifest]),
) -> Result<Answer, Fault>
{
    let failed = |reason: String| Fault::Migrate { peer, reason };
    let (mut send, mut recv) = connection
        .open_bi()
        .await
        .map_err(|unopened| failed(unopened.to_string()))?;
    send.write_all(framed.as_ref())
        .await
        .map_err(|unwritten| failed(unwritten.to_string()))?;
    send.finish()
        .map_err(|unfinished| failed(unfinished.to_string()))?;
    // The far host fetches each capture before it answers, so no fetch is
    // under way once the answer has read.
    let serving = tokio::spawn(serve_fetches(connection.clone(), chunks.clone()));
    let answered = recv.read_to_end(MAX_REQUEST).await;
    serving.abort();
    let answered = answered.map_err(|unread| failed(unread.to_string()))?;
    let answer =
        Answer::read(&Framed::from(answered)).map_err(|Malformed| Fault::Malformed { peer })?;
    if let Answer::Answered(manifest) = answer {
        let request = Framed::request(&manifest, captures)?;
        fetch_on(connection, chunks, peer, (&manifest, &request)).await?;
    }
    Ok(answer)
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

impl Worlds
{
    /// Take the next migration, waiting for one, and hold it under a fresh
    /// name.
    ///
    /// # Specification
    /// trivial.
    async fn arrive(&mut self) -> Result<Arrival, Fault>
    {
        let (configuration, pending) = self.migrations.recv().await.ok_or(Fault::Accept)?;
        let id = ArrivalId::from(self.next);
        self.next = self.next.checked_add(1).ok_or(Fault::Exhausted)?;
        let from = pending.peer;
        self.pending.insert(id, pending);
        Ok(Arrival {
            from,
            configuration,
            id,
        })
    }

    /// Fetch `wanted` into `chunks` from the asker of `arrival`, over its
    /// connection.
    ///
    /// # Specification
    /// trivial.
    async fn fetch(
        &self,
        arrival: ArrivalId,
        chunks: &Chunks,
        (wanted, request): (&ValueManifest, &Framed),
    ) -> Result<Fetched, Fault>
    {
        let pending = self
            .pending
            .get(&arrival)
            .ok_or(Fault::Unarrived(arrival))?;
        fetch_on(&pending.connection, chunks, pending.peer, (wanted, request)).await
    }

    /// Answer `arrival` with `framed`, and serve its asker's fetches from
    /// `chunks` on a task [`Worlds::answered`] holds until the asker closes
    /// the connection.
    ///
    /// # Specification
    /// trivial.
    async fn answer(
        &mut self,
        arrival: ArrivalId,
        chunks: &Chunks,
        framed: &Framed,
    ) -> Result<(), Fault>
    {
        let Pending {
            peer,
            connection,
            mut send,
        } = self
            .pending
            .remove(&arrival)
            .ok_or(Fault::Unarrived(arrival))?;
        let failed = |reason: String| Fault::Migrate { peer, reason };
        send.write_all(framed.as_ref())
            .await
            .map_err(|unwritten| failed(unwritten.to_string()))?;
        send.finish()
            .map_err(|unfinished| failed(unfinished.to_string()))?;
        while self.answered.try_join_next().is_some() {}
        self.answered
            .spawn(serve_fetches(connection, chunks.clone()));
        Ok(())
    }
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
        let prefix = Prefix::try_from(bytes.len())?;
        let held = self.held(stream)?;
        let failed = |reason: String| Fault::Stream { stream, reason };
        held.send
            .write_all(&<[u8; PREFIX]>::from(prefix))
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
        let mut prefix = [0_u8; PREFIX];
        held.recv.read_exact(&mut prefix).await.map_err(unread)?;
        let length = match Prefix::try_from(prefix) {
            Ok(length) => length,
            Err(oversized) => {
                if let Some(refused) = self.held.remove(&stream) {
                    refused
                        .connection
                        .close(VarInt::from_u32(REFUSED), b"oversized frame");
                }
                return Err(Fault::from(oversized));
            },
        };
        let mut frame = vec![0_u8; usize::from(length)];
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
