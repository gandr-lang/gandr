//! The endpoint's thread on a target with no QUIC transport: WASI 0.3
//! offers no UDP socket iroh can bind. The thread answers its bind with
//! [`Fault::Bind`] and ends, so a run that never reaches the network runs
//! as it does on a host with one. A run that does reach it stops with the
//! same refusal a host whose sockets are taken gives.

use core::net::SocketAddr;
use std::sync::mpsc;

use super::Binding;
use super::Fault;
use super::request::Request;

/// Refuse the bind `ready` waits for: this target binds no endpoint.
///
/// # Specification
/// trivial.
pub(super) fn run(
    _binding: &Binding,
    _inbox: tokio::sync::mpsc::UnboundedReceiver<Request>,
    ready: &mpsc::SyncSender<Result<Vec<SocketAddr>, Fault>>,
)
{
    match ready.send(Err(Fault::Bind {
        reason: String::from("this target has no QUIC transport"),
    })) {
        Ok(()) | Err(mpsc::SendError(_)) => {},
    }
}
