//! **The network a host holds** for its `Net` interface: streams to peers
//! named by their keys, over QUIC through iroh, and the chunk wire that
//! fetches a committed value's chunks by content. In the storage picture of
//! `Rainey-2026-localmem_typedirected_adaptive_serialization_location_contentaddressable_memory`
//! this crate is a LAM-side driver: a stream is a location the host holds,
//! named to the program by an integer that never crosses to another host, and
//! a frame is the bytes one `send` carried. Its wall is integrity: TLS 1.3
//! under QUIC binds every stream to the key its dialer named and authenticates
//! each frame on it, and every fetched chunk is verified against its digest.
//! It decides nothing about validity: a frame is bytes.
//!
//! A [`Net`] binds an [`Endpoint`] on its first operation; the endpoint runs
//! on one thread of its own beside the program, and the program's thread
//! waits on each operation. A [`Peer`] is a key, the identity, with the
//! socket addresses a dialer may try for it; the addresses never enter
//! identity. A [`Secret`] is what an endpoint proves its key with; that key
//! names one process here and is the key a located world will carry. The
//! endpoint serves its [`Chunks`] to any peer that asks under
//! [`CHUNKS_ALPN`], and [`Endpoint::fetch`] asks a peer for the chunks of a
//! value it lacks, naming the values it holds, in one round trip.
//!
//! # References
//!
//! - `Rainey-2026-localmem_typedirected_adaptive_serialization_location_contentaddressable_memory` — lineage: the
//!   location a stream is, held by its host and never moved, beside the
//!   content-addressed values that do cross.

extern crate alloc;

mod chunks;
mod endpoint;
mod net;
mod peer;

pub use crate::chunks::CHUNKS_ALPN;
pub use crate::chunks::Chunks;
pub use crate::chunks::Fetched;
pub use crate::endpoint::ALPN;
pub use crate::endpoint::Binding;
pub use crate::endpoint::Endpoint;
pub use crate::endpoint::Fault;
pub use crate::endpoint::Frame;
pub use crate::endpoint::Lookup;
pub use crate::endpoint::LookupError;
pub use crate::endpoint::MAX_FRAME;
pub use crate::endpoint::StreamId;
pub use crate::net::Net;
pub use crate::peer::NodeId;
pub use crate::peer::Peer;
pub use crate::peer::PeerError;
pub use crate::peer::Secret;
