//! Two `gandr` processes on one host: one serving the ping exemplar and one
//! pinging it over `Net`, and one hosting the migration model's far world and
//! one running it.

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

/// The hosting process's secret, fixed so the runner can bind the far world
/// to its key.
const HOST_SECRET: &str = "0303030303030303030303030303030303030303030303030303030303030303";

/// `gandr host` of the migration model hosts its world `far` on the socket
/// `--net-bind` names, under the key `GANDR_NET_SECRET` holds; `gandr run`
/// binding `far` to that key and socket ships it both migrations. The run
/// exits 42, as the same source run in one process does, and the host prints
/// a line for each migration it ran, the second fetching nothing: its capture
/// is the value the first held there. A run with no world binding naming
/// `far` is refused before it runs, naming it.
#[test]
fn two_processes_run_the_far_world_s_migrations_there()
{
    let model =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/model/worlds/two-processes.gandr");
    let socket = UdpSocket::bind(SocketAddr::from((Ipv4Addr::LOCALHOST, 0)))
        .and_then(|probe| probe.local_addr())
        .expect("a free loopback port");
    let key = Secret::from_str(HOST_SECRET)
        .expect("the secret is hex")
        .node_id();
    let far = format!("far={}", Peer::new(key).at(socket));
    let unconfigured = std::env::temp_dir().join("gandr-driver-unconfigured");
    let alone = Command::new(env!("CARGO_BIN_EXE_gandr"))
        .arg("run")
        .arg(&model)
        .env("XDG_CONFIG_HOME", &unconfigured)
        .output()
        .expect("the model runs alone");
    assert_eq!(
        alone.status.code(),
        Some(42_i32),
        "in one process the model answers 42: {}",
        String::from_utf8_lossy(&alone.stderr)
    );
    let mut hosting = Command::new(env!("CARGO_BIN_EXE_gandr"));
    hosting
        .arg("host")
        .arg("--net-bind")
        .arg(socket.to_string())
        .arg("--world")
        .arg(&far)
        .arg("--migrations")
        .arg("2")
        .arg(&model)
        .env("GANDR_NET_SECRET", HOST_SECRET)
        .env("XDG_CONFIG_HOME", &unconfigured)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let mut host = hosting.spawn().expect("the host starts");
    let ran = Command::new(env!("CARGO_BIN_EXE_gandr"))
        .arg("run")
        .arg("--net-bind")
        .arg(SocketAddr::from((Ipv4Addr::LOCALHOST, 0)).to_string())
        .arg("--world")
        .arg(&far)
        .arg(&model)
        .env("XDG_CONFIG_HOME", &unconfigured)
        .output()
        .expect("the runner runs");
    if ran.status.code() != Some(42_i32) {
        host.kill().expect("a failed run stops the host");
    }
    let hosted = host.wait_with_output().expect("the host ends");
    assert_eq!(
        ran.status.code(),
        Some(42_i32),
        "across two processes the model answers 42: {}",
        String::from_utf8_lossy(&ran.stderr)
    );
    assert_eq!(
        (
            hosted.status.code(),
            String::from_utf8_lossy(&hosted.stdout)
        ),
        (
            Some(0_i32),
            "ran a migration at far, fetching 0 chunks\nran a migration at far, fetching 0 \
             chunks\n"
                .into()
        ),
        "the host ran both migrations: {}",
        String::from_utf8_lossy(&hosted.stderr)
    );
    let unbound = Command::new(env!("CARGO_BIN_EXE_gandr"))
        .arg("run")
        .arg("--world")
        .arg(format!("near={}", Peer::new(key).at(socket)))
        .arg(&model)
        .env("XDG_CONFIG_HOME", &unconfigured)
        .output()
        .expect("the unbound run runs");
    let refusal = String::from_utf8_lossy(&unbound.stderr);
    assert_eq!(
        unbound.status.code(),
        Some(2_i32),
        "a world no host is bound to never runs: {refusal}"
    );
    assert!(
        refusal.contains("UnboundWorld") && refusal.contains("`far`"),
        "the refusal names the world: {refusal}"
    );
}
