//! Two endpoints on loopback: a dial reaches the key it names, frames arrive
//! whole and in order, both ends close, and what an endpoint does not hold or
//! cannot send is refused.

use core::net::IpAddr;
use core::net::Ipv4Addr;
use core::net::SocketAddr;
use std::thread;

use gandr_runtime_net::Binding;
use gandr_runtime_net::Endpoint;
use gandr_runtime_net::Fault;
use gandr_runtime_net::Frame;
use gandr_runtime_net::MAX_FRAME;
use gandr_runtime_net::Peer;
use gandr_runtime_net::Secret;
use gandr_runtime_net::StreamId;

/// An endpoint bound on loopback at an ephemeral port.
///
/// # Specification
/// trivial.
fn on_loopback() -> Endpoint
{
    Endpoint::bind(&Binding::new(Secret::generate()).at(SocketAddr::from((Ipv4Addr::LOCALHOST, 0))))
        .expect("loopback binds")
}

/// The IPv4 socket `endpoint` bound.
///
/// # Specification
/// trivial.
fn socket_of(endpoint: &Endpoint) -> SocketAddr
{
    endpoint
        .sockets()
        .iter()
        .copied()
        .find(|socket| socket.ip() == IpAddr::V4(Ipv4Addr::LOCALHOST))
        .expect("an endpoint bound on loopback reports the socket")
}

#[test]
fn two_endpoints_exchange_frames_on_loopback()
{
    let mut acceptor = on_loopback();
    let mut dialer = on_loopback();
    let reached = Peer::new(acceptor.node_id()).at(socket_of(&acceptor));
    let dialer_id = dialer.node_id();
    thread::scope(|scope| {
        let accepting = scope.spawn(move || {
            let (peer, stream) = acceptor.accept().expect("the dialer's stream arrives");
            let frames = [(); 3].map(|()| acceptor.recv(stream).expect("a frame arrives"));
            acceptor
                .send(stream, Frame::from(b"pong".to_vec()))
                .expect("the answer is sent");
            acceptor.close(stream).expect("both ends close");
            assert_eq!(
                acceptor.send(stream, Frame::default()),
                Err(Fault::Unknown(stream)),
                "a closed stream is unknown after"
            );
            (peer, frames)
        });
        let stream = dialer.connect(&reached).expect("the acceptor is reached");
        for frame in [&b"ping"[..], b"", b"three"] {
            dialer
                .send(stream, Frame::from(frame.to_vec()))
                .expect("a frame is sent");
        }
        assert_eq!(
            dialer.recv(stream),
            Ok(Frame::from(b"pong".to_vec())),
            "the answer arrives"
        );
        assert_eq!(
            dialer.recv(stream),
            Err(Fault::Ended(stream)),
            "a stream the acceptor finished ends"
        );
        dialer.close(stream).expect("both ends close");
        let (peer, frames) = accepting.join().expect("the acceptor ends");
        assert_eq!(
            peer, dialer_id,
            "the acceptor reads the key the dialer proved"
        );
        assert_eq!(
            frames,
            [&b"ping"[..], b"", b"three"].map(|bytes| Frame::from(bytes.to_vec())),
            "frames arrive whole and in order, the empty one among them"
        );
    });
}

#[test]
fn a_socket_another_holds_is_refused()
{
    let holder = on_loopback();
    let held = socket_of(&holder);
    assert!(
        matches!(
            Endpoint::bind(&Binding::new(Secret::generate()).at(held)),
            Err(Fault::Bind { .. })
        ),
        "{held} is held"
    );
}

#[test]
fn an_oversized_frame_and_an_unknown_stream_are_refused()
{
    let mut endpoint = on_loopback();
    let unknown = StreamId::from(7_u64);
    assert_eq!(
        endpoint.send(unknown, Frame::default()),
        Err(Fault::Unknown(unknown))
    );
    assert_eq!(endpoint.recv(unknown), Err(Fault::Unknown(unknown)));
    assert_eq!(endpoint.close(unknown), Err(Fault::Unknown(unknown)));
    let over = usize::try_from(MAX_FRAME).expect("the cap fits a usize") + 1;
    assert_eq!(
        endpoint.send(unknown, Frame::from(vec![0; over])),
        Err(Fault::Oversized {
            length: u64::try_from(over).expect("the length fits a u64")
        }),
        "an oversized frame is refused before its stream is looked up"
    );
}
