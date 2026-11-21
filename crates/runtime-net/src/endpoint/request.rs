//! What the endpoint's owner asks of its thread, and where the thread
//! answers. Both drivers read this one vocabulary: the QUIC driver serves it,
//! and on a target with no transport the absent driver refuses the bind.

use std::sync::mpsc;

use gandr_storage_values::ValueManifest;

use super::Fault;
use super::Frame;
use super::StreamId;
use crate::chunks::Fetched;
use crate::frame::Framed;
use crate::peer::NodeId;
use crate::worlds::Answer;
use crate::worlds::Arrival;
use crate::worlds::ArrivalId;

/// Where the thread answers one request.
pub(super) type Reply<Answered> = mpsc::SyncSender<Result<Answered, Fault>>;

/// What the endpoint's owner asks of its thread.
#[derive(Debug)]
pub(super) enum Request
{
    /// Dial a peer and open a stream to it.
    Connect(NodeId, iroh_base::EndpointAddr, Reply<StreamId>),
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
        iroh_base::EndpointAddr,
        (ValueManifest, Framed),
        Reply<Fetched>,
    ),
    /// Ship a migration to a peer: the configuration framed, and its
    /// captures, named held when the answer is fetched.
    Migrate(
        NodeId,
        iroh_base::EndpointAddr,
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
