//! A network created unbound binds on its first operation, at the socket its
//! binding names.

use core::net::Ipv4Addr;
use core::net::SocketAddr;
use std::net::UdpSocket;
use std::thread;

use gandr_runtime_net::Binding;
use gandr_runtime_net::Endpoint;
use gandr_runtime_net::Frame;
use gandr_runtime_net::Net;
use gandr_runtime_net::Peer;
use gandr_runtime_net::Secret;

/// The first port of the lowest default range of ephemeral ports: Linux's,
/// from 32768. macOS's starts at 49152.
const EPHEMERAL: u16 = 0x8000;

/// A loopback port free a moment ago, below each default range of ephemeral
/// ports. A bind to port 0 in a test that runs beside the caller never takes
/// it between the probe and the caller's own bind (#7665). The process's id
/// spreads the start, so two runs probe apart.
///
/// # Specification
/// trivial.
fn a_port_below_the_ephemeral_range() -> SocketAddr
{
    let start = 20_000_u16.saturating_add(u16::try_from(std::process::id() % 10_000).unwrap_or(0));
    (start .. EPHEMERAL)
        .find_map(|port| {
            UdpSocket::bind(SocketAddr::from((Ipv4Addr::LOCALHOST, port)))
                .and_then(|probe| probe.local_addr())
                .ok()
        })
        .expect("a loopback port below the ephemeral range is free")
}

#[test]
fn the_probed_port_lies_below_each_ephemeral_range_7665()
{
    let port = a_port_below_the_ephemeral_range().port();
    assert!(port < EPHEMERAL, "port {port} lies in an ephemeral range");
}

#[test]
fn a_network_binds_on_its_first_operation()
{
    // A port for the network to bind when it first accepts.
    let socket = a_port_below_the_ephemeral_range();
    let secret = Secret::generate();
    let mut net = Net::new(Binding::new(secret.clone()).at(socket));
    assert_eq!(net.node_id(), secret.node_id(), "the key is known unbound");
    let mut dialer = Endpoint::bind(
        &Binding::new(Secret::generate()).at(SocketAddr::from((Ipv4Addr::LOCALHOST, 0))),
    )
    .expect("loopback binds");
    let reached = Peer::new(secret.node_id()).at(socket);
    thread::scope(|scope| {
        let accepting = scope.spawn(move || {
            let (_, stream) = net.accept().expect("the dialer's stream arrives");
            let frame = net.recv(stream).expect("a frame arrives");
            net.close(stream).expect("both ends close");
            frame
        });
        let stream = dialer
            .connect(&reached)
            .expect("the network bound and is reached");
        dialer
            .send(stream, Frame::from(b"hello".to_vec()))
            .expect("a frame is sent");
        dialer.close(stream).expect("both ends close");
        assert_eq!(
            accepting.join().expect("the acceptor ends"),
            Frame::from(b"hello".to_vec())
        );
    });
}
