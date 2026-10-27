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

#[test]
fn a_network_binds_on_its_first_operation()
{
    // A port free a moment ago, for the network to bind when it first
    // accepts.
    let socket = UdpSocket::bind(SocketAddr::from((Ipv4Addr::LOCALHOST, 0)))
        .and_then(|probe| probe.local_addr())
        .expect("a loopback port is free");
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
