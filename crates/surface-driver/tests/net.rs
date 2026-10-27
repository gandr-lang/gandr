//! Two `gandr run` processes on one host, one serving the ping exemplar and
//! one pinging it over `Net`.

use core::net::Ipv4Addr;
use core::net::SocketAddr;
use core::str::FromStr as _;
use std::net::UdpSocket;
use std::path::Path;
use std::process::Command;
use std::process::Stdio;

use gandr_runtime_net::Peer;
use gandr_runtime_net::Secret;

/// The serving process's secret, fixed so the pinger can name its key.
const SERVER_SECRET: &str = "0202020202020202020202020202020202020202020202020202020202020202";

/// #3186: `gandr run` of the ping exemplar with no argument serves on the
/// socket `--net-bind` names, under the key `GANDR_NET_SECRET` holds; a
/// second `gandr run` given that key and socket dials it. The pinger prints
/// the `pong` it reads back, the server the `ping`, and both exit 0.
#[test]
fn two_processes_exchange_a_ping_3186()
{
    let exemplar =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/model/distribution/ping.gandr");
    let socket = UdpSocket::bind(SocketAddr::from((Ipv4Addr::LOCALHOST, 0)))
        .and_then(|probe| probe.local_addr())
        .expect("a free loopback port");
    let key = Secret::from_str(SERVER_SECRET)
        .expect("the secret is hex")
        .node_id();
    let peer = Peer::new(key).at(socket);
    let unconfigured = std::env::temp_dir().join("gandr-driver-unconfigured");
    let mut serving = Command::new(env!("CARGO_BIN_EXE_gandr"));
    serving
        .arg("run")
        .arg("--net-bind")
        .arg(socket.to_string())
        .arg(&exemplar)
        .env("GANDR_NET_SECRET", SERVER_SECRET)
        .env("XDG_CONFIG_HOME", &unconfigured)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let mut server = serving.spawn().expect("the server starts");
    let pinged = Command::new(env!("CARGO_BIN_EXE_gandr"))
        .arg("run")
        .arg("--net-bind")
        .arg(SocketAddr::from((Ipv4Addr::LOCALHOST, 0)).to_string())
        .arg(&exemplar)
        .arg(peer.to_string())
        .env("XDG_CONFIG_HOME", &unconfigured)
        .output()
        .expect("the pinger runs");
    if !pinged.status.success() {
        server.kill().expect("a failed ping stops the server");
    }
    let served = server.wait_with_output().expect("the server ends");
    assert_eq!(
        (
            pinged.status.code(),
            String::from_utf8_lossy(&pinged.stdout)
        ),
        (Some(0_i32), "pong\n".into()),
        "the pinger prints the answer: {}",
        String::from_utf8_lossy(&pinged.stderr)
    );
    assert_eq!(
        (
            served.status.code(),
            String::from_utf8_lossy(&served.stdout)
        ),
        (Some(0_i32), "ping\n".into()),
        "the server prints the ping: {}",
        String::from_utf8_lossy(&served.stderr)
    );
}
