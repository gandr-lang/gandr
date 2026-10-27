//! An iroh endpoint on its own thread: [`Endpoint::bind`] starts one thread
//! running a single-threaded runtime, and each operation hands that thread a
//! request and waits for its answer, so the caller's thread never runs async
//! code. One operation runs at a time, in the order the caller makes them.
//!
//! A stream is a bidirectional QUIC stream on a connection of its own, named
//! by a [`StreamId`] this endpoint mints and holds; the name means nothing to
//! another endpoint. A frame is a little-endian `u32` length, then that many
//! bytes, at most [`MAX_FRAME`].
//!
//! # Boundaries
//!
//! - `accept` returns once the dialer has sent its first frame, or closed: a
//!   QUIC stream reaches its peer with its first bytes.
//! - `close` finishes this end, reads and drops what the peer sent until the
//!   peer finishes too, and waits until the peer has every byte this end sent;
//!   then it closes the connection. Both ends closing is a rendezvous.
//! - A frame longer than [`MAX_FRAME`] is refused before it is sent, and one
//!   announced longer than it closes the stream it arrived on.
//! - The endpoint serves its [`Chunks`] under [`CHUNKS_ALPN`] whatever its
//!   owner is doing, and [`Endpoint::fetch`] asks a peer for a value's chunks
//!   on a connection of its own; neither touches a stream the owner holds.
//!
//! [`CHUNKS_ALPN`]: crate::CHUNKS_ALPN

mod driver;

use core::error::Error;
use core::fmt;
use core::net::SocketAddr;
use core::str::FromStr;
use std::sync::mpsc;
use std::thread;

use anodized::spec;
use gandr_storage_values::ValueError;
use gandr_storage_values::ValueManifest;

use crate::chunks::Chunks;
use crate::chunks::Fetched;
use crate::chunks::Framed;
use crate::peer::NodeId;
use crate::peer::Peer;
use crate::peer::Secret;

/// The protocol name an endpoint offers and dials: a peer that speaks
/// another refuses the handshake.
pub const ALPN: &[u8] = b"gandr/net/0";

/// The longest frame, in bytes, either end sends or accepts: 16 MiB.
pub const MAX_FRAME: u32 = 0x0100_0000;

/// A stream an endpoint holds, by the name it minted.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct StreamId(u64);

impl From<u64> for StreamId
{
    /// The stream named `name`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(name: u64) -> Self
    {
        Self(name)
    }
}

impl From<StreamId> for u64
{
    /// The stream's name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(stream: StreamId) -> Self
    {
        stream.0
    }
}

impl fmt::Display for StreamId
{
    /// The stream's name in decimal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "stream {}", self.0)
    }
}

/// The bytes one send carries, at most [`MAX_FRAME`] of them.
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
#[repr(transparent)]
pub struct Frame(Vec<u8>);

impl From<Vec<u8>> for Frame
{
    /// The frame of `bytes`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: Vec<u8>) -> Self
    {
        Self(bytes)
    }
}

impl From<Frame> for Vec<u8>
{
    /// The frame's bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(frame: Frame) -> Self
    {
        frame.0
    }
}

impl AsRef<[u8]> for Frame
{
    /// The frame's bytes, borrowed.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        &self.0
    }
}

/// How an endpoint finds a peer it is asked to dial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Lookup
{
    /// Only at the addresses the peer's spelling names.
    Explicit,
    /// Also by multicast DNS on the local network.
    Mdns,
}

impl FromStr for Lookup
{
    type Err = LookupError;

    /// `explicit` or `mdns`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from_str(text: &str) -> Result<Self, LookupError>
    {
        match text {
            "explicit" => Ok(Self::Explicit),
            "mdns" => Ok(Self::Mdns),
            other => Err(LookupError(String::from(other))),
        }
    }
}

/// A lookup spelled neither `explicit` nor `mdns`.
#[derive(Clone, Debug, Eq, PartialEq)]
#[repr(transparent)]
pub struct LookupError(String);

impl fmt::Display for LookupError
{
    /// The spelling refused and the two that read.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "`{}` is no lookup: `explicit` or `mdns`", self.0)
    }
}

impl Error for LookupError
{
}

/// What an endpoint binds with: the secret it proves, the sockets it binds,
/// how it finds peers, and the chunks it serves.
#[derive(Clone, Debug)]
pub struct Binding
{
    /// The secret the endpoint proves its key with.
    secret: Secret,
    /// The sockets it binds; none binds iroh's defaults, every interface on
    /// an ephemeral port.
    sockets: Vec<SocketAddr>,
    /// How it finds a peer.
    lookup: Lookup,
    /// The chunks it serves and fetches into.
    chunks: Chunks,
}

impl Binding
{
    /// Bind with `secret` on every interface, on an ephemeral port, finding
    /// peers only at the addresses their spellings name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new(secret: Secret) -> Self
    {
        Self {
            secret,
            sockets: Vec::new(),
            lookup: Lookup::Explicit,
            chunks: Chunks::new(),
        }
    }

    /// Bind `socket` in place of the default for its address family; port 0
    /// picks a free one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn at(
        mut self,
        socket: SocketAddr,
    ) -> Self
    {
        self.sockets.push(socket);
        self
    }

    /// Find peers by `lookup`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn lookup(
        mut self,
        lookup: Lookup,
    ) -> Self
    {
        self.lookup = lookup;
        self
    }

    /// Serve `chunks`, and fetch into them, in place of a store of its own.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn serving(
        mut self,
        chunks: Chunks,
    ) -> Self
    {
        self.chunks = chunks;
        self
    }

    /// The key the endpoint will prove.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn node_id(&self) -> NodeId
    {
        self.secret.node_id()
    }
}

/// Why an operation on an endpoint did not complete.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Fault
{
    /// The endpoint did not bind, or its thread did not start.
    Bind
    {
        /// What refused.
        reason: String,
    },
    /// The peer was not reached, refused the connection, or opened no stream.
    Connect
    {
        /// The peer dialed.
        peer: NodeId,
        /// What refused.
        reason: String,
    },
    /// The endpoint closed while waiting for a dialer.
    Accept,
    /// The endpoint holds no stream by this name.
    Unknown(StreamId),
    /// A frame longer than [`MAX_FRAME`], sent or announced.
    Oversized
    {
        /// The frame's length in bytes.
        length: u64,
    },
    /// The peer finished the stream before a whole frame.
    Ended(StreamId),
    /// The stream or its connection failed.
    Stream
    {
        /// The stream.
        stream: StreamId,
        /// What failed.
        reason: String,
    },
    /// The endpoint has minted every stream name.
    Exhausted,
    /// A fetch's connection failed, or the holder closed it unanswered.
    Fetch
    {
        /// The holder asked.
        peer: NodeId,
        /// What failed.
        reason: String,
    },
    /// A holder's answer this protocol does not frame.
    Malformed
    {
        /// The holder.
        peer: NodeId,
    },
    /// A fetched chunk did not verify against its digest, or the value's
    /// closure is not held whole.
    Refused
    {
        /// The holder.
        peer: NodeId,
        /// The value plane's refusal, naming the chunk.
        refusal: ValueError,
    },
    /// The endpoint's thread is gone.
    Driver,
}

impl fmt::Display for Fault
{
    /// What failed, in a sentence fragment.
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
            Self::Bind { ref reason } => write!(f, "the endpoint did not bind: {reason}"),
            Self::Connect { peer, ref reason } => {
                write!(f, "peer {peer} was not reached: {reason}")
            },
            Self::Accept => write!(f, "the endpoint closed while accepting"),
            Self::Unknown(stream) => write!(f, "no {stream} is held"),
            Self::Oversized { length } => {
                write!(f, "a frame of {length} bytes exceeds {MAX_FRAME}")
            },
            Self::Ended(stream) => write!(f, "the peer finished {stream}"),
            Self::Stream { stream, ref reason } => write!(f, "{stream} failed: {reason}"),
            Self::Exhausted => write!(f, "every stream name is spent"),
            Self::Fetch { peer, ref reason } => {
                write!(f, "the fetch from {peer} failed: {reason}")
            },
            Self::Malformed { peer } => write!(f, "{peer} answered a fetch unframed"),
            Self::Refused { peer, refusal } => {
                write!(f, "the value fetched from {peer} was refused: {refusal}")
            },
            Self::Driver => write!(f, "the endpoint's thread is gone"),
        }
    }
}

impl Error for Fault
{
}

/// A bound endpoint and the thread that runs it.
#[derive(Debug)]
pub struct Endpoint
{
    /// Where requests go.
    requests: tokio::sync::mpsc::UnboundedSender<driver::Request>,
    /// The thread, joined when the endpoint drops.
    thread: Option<thread::JoinHandle<()>>,
    /// The key it proves.
    node: NodeId,
    /// The sockets it bound.
    sockets: Vec<SocketAddr>,
}

impl Endpoint
{
    /// Bind an endpoint as `binding` says, on a thread of its own.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: an endpoint proving `binding`'s key, bound to the sockets
    ///   [`Self::sockets`] reports.
    /// - fails: [`Fault::Bind`] when the thread, its runtime or a socket is
    ///   refused.
    /// - panics: none.
    ///
    /// # Errors
    /// [`Fault::Bind`], naming what refused.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two endpoints bound on loopback reach each other at
    ///   the sockets each reports, and a socket another holds is refused.
    /// - witness: `tests::endpoint::two_endpoints_exchange_frames_on_loopback`
    /// - witness: `tests::endpoint::a_socket_another_holds_is_refused`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |bound| bound.node == binding.node_id()))]
    #[inline]
    pub fn bind(binding: &Binding) -> Result<Self, Fault>
    {
        let (requests, inbox) = tokio::sync::mpsc::unbounded_channel();
        let (ready, bound) = mpsc::sync_channel(1);
        let configured = binding.clone();
        let thread = thread::Builder::new()
            .name(String::from("gandr-net"))
            .spawn(move || driver::run(&configured, inbox, &ready))
            .map_err(|refused| Fault::Bind {
                reason: refused.to_string(),
            })?;
        match bound.recv() {
            Ok(Ok(sockets)) => Ok(Self {
                requests,
                thread: Some(thread),
                node: binding.node_id(),
                sockets,
            }),
            Ok(Err(fault)) => {
                joined(thread);
                Err(fault)
            },
            Err(mpsc::RecvError) => {
                joined(thread);
                Err(Fault::Driver)
            },
        }
    }

    /// The key this endpoint proves.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn node_id(&self) -> NodeId
    {
        self.node
    }

    /// The sockets this endpoint bound.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn sockets(&self) -> &[SocketAddr]
    {
        &self.sockets
    }

    /// Dial `peer` and open a stream to it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a stream this endpoint holds, on a connection to an endpoint
    ///   that proved `peer`'s key; the peer's `accept` answers it once this end
    ///   sends.
    /// - fails: [`Fault::Connect`] when iroh gives up the dial: no endpoint at
    ///   `peer`'s addresses proved its key and spoke [`ALPN`] within iroh's
    ///   handshake timeout; [`Fault::Driver`].
    /// - panics: none.
    /// - executable: none — the outcome is the peer's, across the network.
    ///
    /// # Errors
    /// [`Fault::Connect`], [`Fault::Exhausted`] or [`Fault::Driver`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a dial on loopback reaches the endpoint whose key it
    ///   names. A dial naming another key retries until iroh's timeout, so no
    ///   witness waits for its refusal.
    /// - witness: `tests::endpoint::two_endpoints_exchange_frames_on_loopback`
    #[inline]
    pub fn connect(
        &mut self,
        peer: &Peer,
    ) -> Result<StreamId, Fault>
    {
        let (id, dialed) = (peer.id(), peer.endpoint_addr());
        self.ask(|reply| driver::Request::Connect(id, dialed, reply))
    }

    /// Wait for a peer to open a stream to this endpoint.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the key the dialer proved and a stream this endpoint holds to
    ///   it; a handshake that fails is skipped, not answered.
    /// - fails: [`Fault::Accept`] when the endpoint closes; [`Fault::Driver`].
    /// - panics: none.
    /// - executable: none — the outcome is the dialer's, across the network.
    ///
    /// # Errors
    /// [`Fault::Accept`], [`Fault::Exhausted`] or [`Fault::Driver`].
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the acceptor reads the dialer's key and its frames.
    /// - witness: `tests::endpoint::two_endpoints_exchange_frames_on_loopback`
    #[inline]
    pub fn accept(&mut self) -> Result<(NodeId, StreamId), Fault>
    {
        self.ask(driver::Request::Accept)
    }

    /// Send `frame` on `stream`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the frame is queued on the stream, behind every frame sent on
    ///   it before.
    /// - fails: [`Fault::Oversized`] for a frame longer than [`MAX_FRAME`],
    ///   [`Fault::Unknown`] for a stream this endpoint does not hold,
    ///   [`Fault::Stream`] when the stream is reset or its connection lost;
    ///   [`Fault::Driver`].
    /// - panics: none.
    /// - executable: none — the outcome is the peer's, across the network.
    ///
    /// # Errors
    /// As the failures above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — frames arrive whole and in order, an empty frame
    ///   among them; an oversized frame and an unknown stream are refused.
    /// - witness: `tests::endpoint::two_endpoints_exchange_frames_on_loopback`
    /// - witness: `tests::endpoint::an_oversized_frame_and_an_unknown_stream_are_refused`
    #[inline]
    pub fn send(
        &mut self,
        stream: StreamId,
        frame: Frame,
    ) -> Result<(), Fault>
    {
        self.ask(|reply| driver::Request::Send(stream, frame, reply))
    }

    /// Receive the next frame on `stream`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the oldest frame the peer sent on the stream and this end has
    ///   not received.
    /// - fails: [`Fault::Ended`] when the peer finished the stream first,
    ///   [`Fault::Oversized`] for a frame announced longer than [`MAX_FRAME`],
    ///   which closes the stream, [`Fault::Unknown`], [`Fault::Stream`] and
    ///   [`Fault::Driver`].
    /// - panics: none.
    /// - executable: none — the outcome is the peer's, across the network.
    ///
    /// # Errors
    /// As the failures above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — frames arrive whole and in order; a stream the peer
    ///   closed ends.
    /// - witness: `tests::endpoint::two_endpoints_exchange_frames_on_loopback`
    #[inline]
    pub fn recv(
        &mut self,
        stream: StreamId,
    ) -> Result<Frame, Fault>
    {
        self.ask(|reply| driver::Request::Recv(stream, reply))
    }

    /// Close `stream`, once the peer closes its end too.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: this endpoint holds the stream no more; the peer has every
    ///   frame this end sent on it, and what the peer sent and this end did not
    ///   receive is dropped.
    /// - fails: [`Fault::Unknown`]; [`Fault::Stream`] when the connection is
    ///   lost before the peer has every frame; [`Fault::Driver`].
    /// - panics: none.
    /// - executable: none — the outcome is the peer's, across the network.
    ///
    /// # Errors
    /// As the failures above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — both ends close after the exchange, and a stream
    ///   closed is unknown after.
    /// - witness: `tests::endpoint::two_endpoints_exchange_frames_on_loopback`
    #[inline]
    pub fn close(
        &mut self,
        stream: StreamId,
    ) -> Result<(), Fault>
    {
        self.ask(|reply| driver::Request::Close(stream, reply))
    }

    /// Fetch the chunks of `wanted` that this endpoint's store lacks from
    /// `peer`, naming each of `held` as a value whose chunks it holds whole.
    ///
    /// # Specification
    /// - requires: nothing; a value named held whose closure the store lacks
    ///   leaves the walk to refuse the chunk missing.
    /// - ensures: the store holds `wanted`'s whole closure, and the count is of
    ///   the chunks the answer carried: the wanted closure less the held
    ///   closures `peer` holds whole. One request and one answer, on a
    ///   connection under [`CHUNKS_ALPN`] closed before this returns.
    /// - fails: [`Fault::Fetch`] when the dial or the connection fails;
    ///   [`Fault::Malformed`] for an answer that does not frame;
    ///   [`Fault::Refused`] for a chunk that does not verify, with nothing
    ///   inserted, or for the first chunk of the closure neither end holds;
    ///   [`Fault::Oversized`] for a manifest longer than a frame;
    ///   [`Fault::Driver`].
    /// - panics: none.
    ///
    /// # Errors
    /// As the failures above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a list of 888 integers fetched whole, then with one
    ///   element edited and the first named held, carries exactly the chunks
    ///   the edit added, inside the locality bound, and both read back equal; a
    ///   tampered chunk and an unframed part are refused with nothing kept; a
    ///   value the holder lacks is refused by its root chunk.
    /// - witness: `tests::chunks::a_second_fetch_carries_only_the_chunks_an_edit_changed`
    /// - witness: `tests::chunks::an_answer_that_does_not_verify_or_frame_is_refused_before_any_chunk_is_kept`
    /// - witness: `tests::chunks::a_value_the_holder_lacks_is_refused_by_its_first_chunk`
    ///
    /// [`CHUNKS_ALPN`]: crate::CHUNKS_ALPN
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |fetched| fetched.bytes >= u64::try_from(usize::from(fetched.chunks)).unwrap_or(u64::MAX)))]
    #[inline]
    pub fn fetch(
        &mut self,
        peer: &Peer,
        wanted: &ValueManifest,
        held: &[ValueManifest],
    ) -> Result<Fetched, Fault>
    {
        let request = Framed::request(wanted, held)?;
        let (id, dialed, wanted) = (peer.id(), peer.endpoint_addr(), *wanted);
        self.ask(|reply| driver::Request::Fetch(id, dialed, (wanted, request), reply))
    }

    /// Hand the thread the request `make` builds around a reply channel, and
    /// wait for the answer on it.
    ///
    /// # Specification
    /// trivial.
    fn ask<Answered, Make>(
        &self,
        make: Make,
    ) -> Result<Answered, Fault>
    where
        Make: FnOnce(driver::Reply<Answered>) -> driver::Request,
    {
        let (reply, answer) = mpsc::sync_channel(1);
        self.requests
            .send(make(reply))
            .map_err(|tokio::sync::mpsc::error::SendError(_)| Fault::Driver)?;
        match answer.recv() {
            Ok(answered) => answered,
            Err(mpsc::RecvError) => Err(Fault::Driver),
        }
    }
}

impl Drop for Endpoint
{
    /// Close the endpoint and join its thread.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the thread has closed every connection, within its grace, and
    ///   ended.
    /// - panics: none.
    /// - executable: none — the thread's end is observed only by joining it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — endpoints dropped at the end of each witness leave no
    ///   thread behind for the next.
    /// - witness: `tests::endpoint::two_endpoints_exchange_frames_on_loopback`
    #[inline]
    fn drop(&mut self)
    {
        match self.requests.send(driver::Request::Shutdown) {
            // A thread already gone has closed its endpoint as it ended.
            Ok(()) | Err(_) => {},
        }
        if let Some(thread) = self.thread.take() {
            joined(thread);
        }
    }
}

/// Wait for `thread` to end, whether it returned or panicked.
///
/// # Specification
/// trivial.
fn joined(thread: thread::JoinHandle<()>)
{
    match thread.join() {
        Ok(()) | Err(_) => {},
    }
}
