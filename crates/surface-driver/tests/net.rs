//! Two `gandr` processes on one host: one serving the ping exemplar and one
//! pinging it over `Net`, and one hosting the migration model's far world and
//! one running it, bound by flags and by the site and manifold they desugar
//! from; and a host reading its site's secret by name.

use core::net::Ipv4Addr;
use core::net::SocketAddr;
use core::str::FromStr as _;
use std::ffi::OsStr;
use std::io::BufRead as _;
use std::io::BufReader;
use std::net::UdpSocket;
use std::path::Path;
use std::process::Command;
use std::process::Stdio;

use gandr_runtime_net::Peer;
use gandr_runtime_net::Secret;

use super::cli::Scratch;
use super::cli::Text;

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

/// #3374: the same two processes bound by files. `gandr host --site` binds
/// the socket the corpus site names under its key, which the secret
/// `GANDR_SECRET_FAR` holds proves (#3375), and prints that peer first on
/// standard error; `gandr run --manifold` ships both migrations to the site
/// the manifold places `far` at. The run exits 42 and the host prints a line
/// for each migration, as with the flags. The corpus files are laid in a
/// scratch tree as the corpus holds them, the site's socket a free one. Each
/// refusal exits 2 before anything runs: a run given `--world` beside the
/// manifold, naming both; and a run of another source than the manifold
/// deploys, naming both paths.
#[test]
fn two_processes_run_the_far_world_from_their_site_and_manifold_3374()
{
    let corpus = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let read = |relative: &str| {
        std::fs::read_to_string(corpus.join(relative)).expect("the corpus file reads")
    };
    let socket = UdpSocket::bind(SocketAddr::from((Ipv4Addr::LOCALHOST, 0)))
        .and_then(|probe| probe.local_addr())
        .expect("a free loopback port");
    let scratch = Scratch::new(Path::new("net-manifold-3374"));
    let lay = |relative: &str, text: &str| scratch.file(Path::new(relative), Text::from(text));
    lay(
        "library/std/src/manifold.gandr",
        &read("library/std/src/manifold.gandr"),
    );
    let model = lay(
        "corpus/model/worlds/two-processes.gandr",
        &read("corpus/model/worlds/two-processes.gandr"),
    );
    let site = lay(
        "corpus/model/worlds/two-processes.site.gandr",
        &read("corpus/model/worlds/two-processes.site.gandr")
            .replace("127.0.0.1:7433", &socket.to_string()),
    );
    let manifold = lay(
        "corpus/model/worlds/two-processes.manifold.gandr",
        &read("corpus/model/worlds/two-processes.manifold.gandr"),
    );
    let key = Secret::from_str(HOST_SECRET)
        .expect("the secret is hex")
        .node_id();
    let unconfigured = std::env::temp_dir().join("gandr-driver-unconfigured");
    let mut hosting = Command::new(env!("CARGO_BIN_EXE_gandr"));
    hosting
        .arg("host")
        .arg("--site")
        .arg(&site)
        .arg("--manifold")
        .arg(&manifold)
        .arg("--migrations")
        .arg("2")
        .arg(&model)
        .env("GANDR_SECRET_FAR", HOST_SECRET)
        .env_remove("GANDR_NET_SECRET")
        .env("XDG_CONFIG_HOME", &unconfigured)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let mut host = hosting.spawn().expect("the host starts");
    let ran = Command::new(env!("CARGO_BIN_EXE_gandr"))
        .arg("run")
        .arg("--manifold")
        .arg(&manifold)
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
        "across two processes bound by files the model answers 42: {}",
        String::from_utf8_lossy(&ran.stderr)
    );
    let named = String::from_utf8_lossy(&hosted.stderr);
    let peer = Peer::new(key).at(socket).to_string();
    assert!(
        named
            .lines()
            .find(|line| Line(line).writer() == Writer::Host)
            .is_some_and(|first| { first == peer || first.starts_with(&format!("{peer}@")) }),
        "the host's first line past its diagnostics is the peer the site names, before any \
         other socket it bound: {named}"
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
        "the host ran both migrations: {named}"
    );
    let refused = |arguments: &[&OsStr]| {
        let output = Command::new(env!("CARGO_BIN_EXE_gandr"))
            .args(arguments)
            .env_remove("GANDR_NET_SECRET")
            .env("XDG_CONFIG_HOME", &unconfigured)
            .output()
            .expect("the refused command runs");
        (
            output.status.code(),
            String::from_utf8_lossy(&output.stderr).into_owned(),
        )
    };
    let bound = format!("far={peer}");
    let (code, refusal) = refused(&[
        OsStr::new("run"),
        OsStr::new("--manifold"),
        manifold.as_os_str(),
        OsStr::new("--world"),
        OsStr::new(&bound),
        model.as_os_str(),
    ]);
    assert!(
        code == Some(2_i32) && refusal.contains("`--world`") && refusal.contains("`--manifold`"),
        "a run bound by both a flag and a manifold never runs, naming both: {refusal}"
    );
    let (code, refusal) = refused(&[
        OsStr::new("run"),
        OsStr::new("--manifold"),
        manifold.as_os_str(),
        site.as_os_str(),
    ]);
    assert!(
        code == Some(2_i32) && refusal.contains("the manifold deploys"),
        "a run of a source the manifold does not deploy never runs, naming both: {refusal}"
    );
}

/// #3375: a host reads its site's secret by the name the site gives it.
/// Given the corpus secrets model, `gandr host --site` binds the site's peer
/// and prints it first on standard error. Each refusal exits 2 before
/// anything binds: a secret in `GANDR_SECRET_FAR` proving another key, naming
/// both keys and the variable; the variable unset, naming it; a secret
/// spelling no key, never spelling it; and `GANDR_NET_SECRET` given beside the
/// site, naming `--net-secret` and `--site`.
#[test]
fn a_host_reads_its_site_s_secret_by_name_3375()
{
    let corpus = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let read = |relative: &str| {
        std::fs::read_to_string(corpus.join(relative)).expect("the corpus file reads")
    };
    let socket = UdpSocket::bind(SocketAddr::from((Ipv4Addr::LOCALHOST, 0)))
        .and_then(|probe| probe.local_addr())
        .expect("a free loopback port");
    let scratch = Scratch::new(Path::new("net-secrets-3375"));
    let lay = |relative: &str, text: &str| scratch.file(Path::new(relative), Text::from(text));
    for module in ["manifold", "secret"] {
        let relative = format!("library/std/src/{module}.gandr");
        lay(&relative, &read(&relative));
    }
    let model = lay(
        "corpus/model/worlds/two-processes.gandr",
        &read("corpus/model/worlds/two-processes.gandr"),
    );
    let site = lay(
        "corpus/model/worlds/two-processes.site.gandr",
        &read("corpus/model/worlds/two-processes.site.gandr")
            .replace("127.0.0.1:7433", &socket.to_string()),
    );
    let secrets = lay(
        "corpus/model/worlds/two-processes.secrets.gandr",
        &read("corpus/model/worlds/two-processes.secrets.gandr"),
    );
    let key = Secret::from_str(HOST_SECRET)
        .expect("the secret is hex")
        .node_id();
    let unconfigured = std::env::temp_dir().join("gandr-driver-unconfigured");
    let hosting = |variables: &[(&str, &str)]| {
        let mut command = Command::new(env!("CARGO_BIN_EXE_gandr"));
        command
            .arg("host")
            .arg("--site")
            .arg(&site)
            .env_remove("GANDR_NET_SECRET")
            .env_remove("GANDR_SECRET_FAR")
            .env("XDG_CONFIG_HOME", &unconfigured);
        for &(name, value) in variables {
            command.env(name, value);
        }
        command
    };
    let mut host = hosting(&[])
        .arg("--secrets")
        .arg(&secrets)
        .arg(&model)
        .stdout(Stdio::null())
        .stderr(Stdio::piped())
        .spawn()
        .expect("the host starts");
    let mut first = String::new();
    let mut lines = BufReader::new(host.stderr.take().expect("the host's standard error"));
    let read_first = loop {
        first.clear();
        match lines.read_line(&mut first) {
            Ok(read) if read > 0 && Line(first.trim_end()).writer() == Writer::Subscriber => {},
            read => break read,
        }
    };
    host.kill().expect("the bound host stops");
    let _ended = host.wait();
    read_first.expect("the host's first line reads");
    let first = first.trim_end();
    let peer = Peer::new(key).at(socket).to_string();
    assert!(
        first == peer || first.starts_with(&format!("{peer}@")),
        "a host given the corpus secrets model binds the site's peer: {first}"
    );
    let refused = |variables: &[(&str, &str)]| {
        let output = hosting(variables)
            .arg(&model)
            .output()
            .expect("the refused host runs");
        (
            output.status.code(),
            String::from_utf8_lossy(&output.stderr).into_owned(),
        )
    };
    let (code, refusal) = refused(&[("GANDR_SECRET_FAR", SERVER_SECRET)]);
    let proving = Secret::from_str(SERVER_SECRET)
        .expect("the secret is hex")
        .node_id()
        .to_string();
    assert!(
        code == Some(2_i32)
            && refusal.contains(&key.to_string())
            && refusal.contains(&proving)
            && refusal.contains("`GANDR_SECRET_FAR`"),
        "a host whose secret proves another key than its site's never binds, naming both and \
         the variable: {refusal}"
    );
    let (code, refusal) = refused(&[]);
    assert!(
        code == Some(2_i32)
            && refusal.contains("no secret is given")
            && refusal.contains("`GANDR_SECRET_FAR`"),
        "a host given no secret never binds, naming the variable: {refusal}"
    );
    let (code, refusal) = refused(&[("GANDR_SECRET_FAR", "hunter2")]);
    assert!(
        code == Some(2_i32) && refusal.contains("spells no key") && !refusal.contains("hunter2"),
        "a secret spelling no key is refused without being spelled: {refusal}"
    );
    let (code, refusal) = refused(&[("GANDR_NET_SECRET", HOST_SECRET)]);
    assert!(
        code == Some(2_i32) && refusal.contains("`--net-secret`") && refusal.contains("`--site`"),
        "a network secret beside a site is refused, naming both: {refusal}"
    );
}

/// Who wrote a line of the host's standard error (#4006).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Writer
{
    /// The `tracing` feature's subscriber, which shares the stream.
    Subscriber,
    /// The host itself: its peer, its migrations, its refusals.
    Host,
}

/// A line of the host's standard error.
#[derive(Clone, Copy)]
#[repr(transparent)]
struct Line<'line>(&'line str);

impl Line<'_>
{
    /// Who wrote this line: the subscriber's lines open with a timestamp,
    /// then a level, so a host's first line is read past them.
    ///
    /// # Specification
    /// trivial.
    fn writer(self) -> Writer
    {
        let mut fields = self.0.split_whitespace();
        let stamped = fields
            .next()
            .is_some_and(|stamp| stamp.ends_with('Z') && stamp.contains('T'));
        let levelled = fields
            .next()
            .is_some_and(|level| ["TRACE", "DEBUG", "INFO", "WARN", "ERROR"].contains(&level));
        if stamped && levelled {
            Writer::Subscriber
        }
        else {
            Writer::Host
        }
    }
}

/// #4006: with every feature on, the host's standard error opens with the
/// subscriber's close of the dispatch span, then the peer. The peer is read
/// past the subscriber's lines, and the peer line is none of them.
#[test]
fn a_host_s_peer_is_read_past_its_diagnostics_4006()
{
    let peer = "ed4928c628d1c2c6eae90338905995612959273a5c63f93636c14614ac8737d1@127.0.0.1:39684";
    let named = format!(
        "2026-10-30T00:05:38.237291Z  INFO driver:dispatch: gandr_surface_dispatcher: close \
         time.busy=1.48ms time.idle=3.26µs\n{peer}@[::]:38070\n2026-10-30T00:05:38.307738Z  INFO \
         driver: gandr: output flushed\n"
    );
    assert_eq!(
        named
            .lines()
            .find(|line| Line(line).writer() == Writer::Host),
        Some(format!("{peer}@[::]:38070").as_str()),
        "the first line the subscriber did not write is the peer"
    );
    assert_eq!(
        named.lines().next().map(|line| Line(line).writer()),
        Some(Writer::Subscriber),
        "the dispatch span's close is the subscriber's"
    );
}
