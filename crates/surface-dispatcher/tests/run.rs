//! The run verb's source and script faces.
//!
//! [`run_source`] runs source text and [`Script`] the file `gandr run` names.
//! These cases pin what the file face separates — a path it cannot read, a
//! source that never reaches the machine, and a completed run — and the
//! shebang line an executable script opens with, each against the same text
//! run with no file.
//!
//! The run cases, in a `cfg(test)` module so the crate's lint wall reads them
//! as test code rather than as shipping code.

use core::net::Ipv4Addr;
use core::net::SocketAddr;
use core::str::FromStr as _;
use core::time::Duration;
use std::net::UdpSocket;
use std::path::Path;
use std::path::PathBuf;
use std::thread;

use anodized::spec;
use gandr_runtime_net::Binding;
use gandr_runtime_net::Endpoint;
use gandr_runtime_net::Frame;
use gandr_runtime_net::Net;
use gandr_runtime_net::Peer;
use gandr_runtime_net::Secret;
use gandr_runtime_net::WorldName;
use gandr_storage_values::ChunkCount;
use gandr_surface_dispatcher::Captured;
use gandr_surface_dispatcher::Composed;
use gandr_surface_dispatcher::Entered;
use gandr_surface_dispatcher::Evaluation;
use gandr_surface_dispatcher::ExitStatus;
use gandr_surface_dispatcher::Hosted;
use gandr_surface_dispatcher::LoweringCount;
use gandr_surface_dispatcher::MigrationCount;
use gandr_surface_dispatcher::Ran;
use gandr_surface_dispatcher::RunStatus;
use gandr_surface_dispatcher::Script;
use gandr_surface_dispatcher::ScriptRun;
use gandr_surface_dispatcher::SourceFault;
use gandr_surface_dispatcher::Step;
use gandr_surface_dispatcher::Unrunnable;
use gandr_surface_dispatcher::WorldBinding;
use gandr_surface_dispatcher::WorldBindingError;
use gandr_surface_dispatcher::WorldBindings;
use gandr_surface_dispatcher::run_source;
use gandr_surface_grammar::built_in;
use gandr_surface_syntax::SourceText;

/// A program whose `main` returns forty-two.
const ANSWER: &str = "def answer = 42 ;\ndef main() -> -F Integer { return answer }\n";

/// The hosting endpoint's secret, fixed so a run can bind the seat to its
/// key.
const HOST_SECRET: &str = "0505050505050505050505050505050505050505050505050505050505050505";

/// How many integers the descent case's list holds: enough for its image to
/// span many chunks.
const LISTED: u16 = 300;

/// How long the descent case's first host stays bound after its last
/// answer: a host whose endpoint is slow to close, which the run's next
/// migration to the seat must not reach.
const LINGER: Duration = Duration::from_millis(100);

/// A scratch source file, removed when dropped.
#[repr(transparent)]
struct Scratch(PathBuf);

impl Scratch
{
    /// `text` written to a file named for `test` and this process.
    ///
    /// # Specification
    /// - requires: the derived path has a writable parent and belongs only to
    ///   this fixture for its lifetime.
    /// - ensures: the returned path names a regular file containing `text`.
    /// - fails: never.
    /// - panics: if the file cannot be written.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — isolated value, shebang and refusal files are read
    ///   back through the script's source step and compared byte-for-byte with
    ///   their supplied text. These cases detect truncation or a wrong source,
    ///   not external interference or every filesystem failure.
    /// - witness: `tests::run::run_source_file_runs_a_script_file`
    /// - witness: `tests::run::run_source_file_accepts_an_executable_shebang_line`
    /// - witness: `tests::run::run_source_file_surfaces_a_source_failure_unchanged`
    #[spec(ensures: |ref ret| ret.0.metadata().is_ok_and(|metadata|
            metadata.is_file() && u64::try_from(text.as_ref().len())
                .is_ok_and(|offered| metadata.len() == offered)))]
    fn write(
        test: &Path,
        text: SourceText<'_>,
    ) -> Self
    {
        let path = std::env::temp_dir().join(format!(
            "gandr-dispatcher-run-{}-{}.gandr",
            test.display(),
            std::process::id()
        ));
        std::fs::write(&path, text.as_ref()).expect("the scratch source is written");
        Self(path)
    }
}

impl Drop for Scratch
{
    /// Remove the file.
    ///
    /// # Specification
    /// - requires: the fixture still exclusively owns its removable file.
    /// - ensures: the fixture's path no longer names a file.
    /// - fails: never.
    /// - panics: if the file cannot be removed.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the value-file case retains its path across drop and
    ///   independently observes its absence afterward, detecting a skipped
    ///   removal on normal exit. Unwinding and external filesystem changes are
    ///   outside this witness.
    /// - witness: `tests::run::run_source_file_runs_a_script_file`
    #[spec(ensures: self.0.try_exists().is_ok_and(|exists| !exists))]
    fn drop(&mut self)
    {
        let removed = std::fs::remove_file(&self.0);
        assert!(removed.is_ok(), "the scratch source is removed");
    }
}

/// What running `text` with no file comes to.
///
/// # Specification
/// - requires: the built-in grammar builds and the fixture composes.
/// - ensures: returns the source's execution outcome; any entry run is named in
///   the supplied source.
/// - fails: never.
/// - panics: if grammar construction or composition fails.
///
/// # Adequacy
/// - hypothesis: L3 — an explicit forty-two program asserts its entry and
///   status, while empty and refused sources assert their distinct outcomes.
///   This detects losing the entry or collapsing those outcomes, not arbitrary
///   evaluation errors or parser recovery.
/// - witness: `tests::run::run_source_runs_source_text`
/// - witness: `tests::run::run_source_file_surfaces_a_source_failure_unchanged`
#[spec(ensures: |ref ret| match *ret {
        Ran::Entered { target, .. } => text.as_ref().contains(target.as_ref()),
        Ran::Refused | Ran::NoProgram => true,
        Ran::Hosted(_) => false,
    })]
fn ran_text(text: SourceText<'_>) -> Ran<'_>
{
    let grammar = built_in().expect("the built-in grammar builds");
    let mut lowerings = LoweringCount::default();
    let (_composed, ran) = run_source(&grammar, text, &mut lowerings, &mut Captured::default())
        .expect("the source composes");
    ran
}

/// Assert the file's complete source, path, execution and status.
///
/// # Specification
/// - requires: the fixture file is readable and composes as a module;
///   `expected_status` is the status of `expected`.
/// - ensures: returning establishes that the source step preserves `path` and
///   holds `expected_text` from its base, after the prelude, and its execution
///   equals both expectations.
/// - fails: never.
/// - panics: if the script does not produce that source and execution.
///
/// # Adequacy
/// - hypothesis: L3 literal status and source observations distinguish an
///   entry, refusal and empty programs and preserve the shebang's bytes; L2
///   comparison with in-memory execution checks the two entry paths agree.
///   Neither is an independent evaluator for arbitrary programs.
/// - witness: `tests::run::run_source_file_runs_a_script_file`
/// - witness: `tests::run::run_source_file_accepts_an_executable_shebang_line`
/// - witness: `tests::run::run_source_file_surfaces_a_source_failure_unchanged`
#[spec(requires: expected.status() == expected_status)]
fn assert_runs_to(
    path: &Path,
    expected_text: SourceText<'_>,
    expected: &Ran<'_>,
    expected_status: RunStatus,
)
{
    let mut script = Script::new(path.to_path_buf());
    let actual = script.run(&mut Captured::default());
    assert_eq!(
        actual.status(),
        expected_status,
        "the script's status is preserved"
    );
    match actual {
        ScriptRun::Source {
            step:
                Step::Source {
                    path: observed_path,
                    text,
                    base,
                    composed: Composed::Settled { .. },
                    ..
                },
            ran,
        } => {
            assert_eq!(
                observed_path, path,
                "the source step names the supplied path"
            );
            assert_eq!(
                text.as_ref().get(usize::from(base) ..),
                Some(expected_text.as_ref()),
                "the complete file is retained as source, after the prelude"
            );
            assert_eq!(ran, *expected, "the file face runs as its text does");
        },
        other @ (ScriptRun::Fault { .. } | ScriptRun::Source { .. }) => {
            panic!("the script composes: {other:?}")
        },
    }
}

#[test]
fn run_source_runs_source_text()
{
    let ran = ran_text(SourceText::from(ANSWER));
    assert!(
        matches!(
            ran,
            Ran::Entered {
                target,
                entered: Entered::Exited(status),
            } if target.as_ref() == "main" && status == ExitStatus::from(42_u8)
        ),
        "a completed run exits with what its entry returns: {ran:?}"
    );
}

/// A script file runs exactly as its source text does.
#[test]
fn run_source_file_runs_a_script_file()
{
    let script = Scratch::write(Path::new("value"), SourceText::from(ANSWER));
    assert_runs_to(
        &script.0,
        SourceText::from(ANSWER),
        &ran_text(SourceText::from(ANSWER)),
        RunStatus::Value,
    );
    let removed_path = script.0.clone();
    drop(script);
    assert!(removed_path.try_exists().is_ok_and(|exists| !exists));
}

/// A shebang line does not change what a script computes.
#[test]
fn run_source_file_accepts_an_executable_shebang_line()
{
    let shebang = format!("#!/usr/bin/env gandr\n{ANSWER}");
    let script = Scratch::write(Path::new("shebang"), SourceText::from(shebang.as_str()));
    assert_runs_to(
        &script.0,
        SourceText::from(shebang.as_str()),
        &ran_text(SourceText::from(ANSWER)),
        RunStatus::Value,
    );
}

/// #2302: a script is laid after the prelude, so `==` between two strings
/// resolves the prelude's `EqString` and runs to whether they are the same
/// text; bare, `==` would be the integer primitive and refuse them.
#[test]
fn a_script_compares_through_the_prelude_s_eq_2302()
{
    for (test, compared, status) in [
        ("same", r#""types" == "types""#, 0_u8),
        ("different", r#""types" == "machines""#, 1_u8),
    ] {
        let text = format!(
            "def main() -> -F Integer {{\n  if {compared} {{ return 0 }} else {{ return 1 }}\n}}\n"
        );
        let file = Scratch::write(
            Path::new(&format!("eq-2302-{test}")),
            SourceText::from(text.as_str()),
        );
        let mut script = Script::new(file.0.clone());
        let run = script.run(&mut Captured::default());
        assert!(
            matches!(
                run,
                ScriptRun::Source {
                    ran: Ran::Entered {
                        entered: Entered::Exited(exited),
                        ..
                    },
                    ..
                } if exited == ExitStatus::from(status)
            ),
            "`{compared}` decides the status: {run:?}"
        );
    }
}

/// #1881: a script's arguments reach its entry, which exits with their
/// number.
#[test]
fn a_script_passes_its_arguments_to_its_entry_1881()
{
    let counted = "def rec count(xs : List(String)) -> -F Integer {\n  case xs {\n    [] => 0,\n    \
                   [x, ..rest] => { run n <- count[<](rest); n + 1 }\n  }\n}\ndef main(args : \
                   List(String)) -> -F Integer { become count(args) }\n";
    let file = Scratch::write(Path::new("arguments"), SourceText::from(counted));
    for arguments in [vec![], vec![String::from("one"), String::from("two")]] {
        let mut script = Script::new(file.0.clone());
        let count = u8::try_from(arguments.len()).expect("a few arguments");
        script.pass(arguments);
        let run = script.run(&mut Captured::default());
        assert!(
            matches!(
                run,
                ScriptRun::Source {
                    ran: Ran::Entered {
                        entered: Entered::Exited(status),
                        ..
                    },
                    ..
                } if u8::from(status) == count
            ),
            "the entry exits with the number of its arguments: {run:?}"
        );
    }
}

#[test]
fn run_source_file_reports_the_path_of_an_absent_file()
{
    let absent = std::env::temp_dir().join(format!(
        "gandr-dispatcher-run-absent-{}.gandr",
        std::process::id()
    ));
    drop(std::fs::remove_file(&absent));
    let mut script = Script::new(absent.clone());
    let run = script.run(&mut Captured::default());
    assert_eq!(
        run.status(),
        RunStatus::Unreached,
        "an absent file never reaches the machine"
    );
    assert!(
        matches!(
            run,
            ScriptRun::Fault {
                path,
                fault: SourceFault::Unreadable(_),
            } if path == absent
        ),
        "an unreadable file is a read fault naming the path it could not read: {run:?}"
    );
}

/// The script face surfaces the source's failure unchanged.
#[test]
fn run_source_file_surfaces_a_source_failure_unchanged()
{
    for (test, text, failure) in [
        ("no-program", "// declares nothing\n", Ran::NoProgram),
        (
            "no-main",
            "def answer : +U (-F Integer) ;\ndef answer = thunk { return 42 } ;\n",
            Ran::NoProgram,
        ),
        (
            "refused",
            "def only : Integer ;\ndef only = \"one\" ;\n",
            Ran::Refused,
        ),
    ] {
        assert_eq!(
            ran_text(SourceText::from(text)),
            failure,
            "`{text}` fails before the machine"
        );
        let script = Scratch::write(Path::new(test), SourceText::from(text));
        assert_runs_to(
            &script.0,
            SourceText::from(text),
            &failure,
            RunStatus::Unreached,
        );
    }
}

/// #3186: the ping exemplar run as a script with a network dials an endpoint
/// on loopback, sends `ping`, prints the `pong` it reads back and exits 0;
/// a `transmit` on a stream no network minted is declined, and the run is
/// stuck at it.
#[test]
fn a_script_pings_over_its_network_3186()
{
    let loopback = SocketAddr::from((Ipv4Addr::LOCALHOST, 0));
    let mut server =
        Endpoint::bind(&Binding::new(Secret::generate()).at(loopback)).expect("loopback binds");
    let socket = server
        .sockets()
        .iter()
        .copied()
        .find(SocketAddr::is_ipv4)
        .expect("the server reports its loopback socket");
    let peer = Peer::new(server.node_id()).at(socket);
    let exemplar =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/model/distribution/ping.gandr");
    thread::scope(|scope| {
        let serving = scope.spawn(move || {
            let (_, stream) = server.accept().expect("the script dials");
            let ping = server.recv(stream).expect("the script sends");
            server
                .send(stream, Frame::from(b"pong".to_vec()))
                .expect("the answer is sent");
            server.close(stream).expect("both ends close");
            ping
        });
        let mut script = Script::new(exemplar.clone());
        script.pass(vec![peer.to_string()]);
        script.network(Net::new(Binding::new(Secret::generate()).at(loopback)));
        let mut console = Captured::default();
        let run = script.run(&mut console);
        assert!(
            matches!(
                run,
                ScriptRun::Source {
                    ran: Ran::Entered {
                        entered: Entered::Exited(status),
                        ..
                    },
                    ..
                } if status == ExitStatus::from(0_u8)
            ),
            "the pinger exits 0: {run:?}"
        );
        assert_eq!(console.lines(), ["pong"], "the answer is printed");
        assert_eq!(
            serving.join().expect("the server ends"),
            Frame::from(b"ping".to_vec())
        );
    });

    let stray = Scratch::write(
        Path::new("net-stray-3186"),
        SourceText::from("def main() -> -F [Net] Integer { Net.transmit(7, \"lost\"); 0 }\n"),
    );
    let mut script = Script::new(stray.0.clone());
    script.network(Net::new(Binding::new(Secret::generate()).at(loopback)));
    let run = script.run(&mut Captured::default());
    assert!(
        matches!(run, ScriptRun::Source {
            ran: Ran::Entered {
                entered: Entered::Ended(Evaluation::Stuck(_)),
                ..
            },
            ..
        }),
        "a stream no network minted is declined: {run:?}"
    );
}

/// The migration model: two migrations to the seat, answering 42.
///
/// # Specification
/// trivial.
fn model() -> PathBuf
{
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/model/worlds/two-processes.gandr")
}

/// The world bindings binding `world` to `peer`.
///
/// # Specification
/// trivial.
fn bindings(
    world: &WorldName,
    peer: &Peer,
) -> WorldBindings
{
    WorldBindings::new(vec![binding(world, peer)])
}

/// The binding of `world` to `peer`.
///
/// # Specification
/// trivial.
fn binding(
    world: &WorldName,
    peer: &Peer,
) -> WorldBinding
{
    WorldBinding::from_str(&format!("{world}={peer}")).expect("the binding reads")
}

/// What `script` exited with, when its entry exited.
///
/// # Specification
/// trivial.
fn exited(script: &mut Script) -> Option<ExitStatus>
{
    match script.run(&mut Captured::default()) {
        ScriptRun::Source {
            ran:
                Ran::Entered {
                    entered: Entered::Exited(status),
                    ..
                },
            ..
        } => Some(status),
        ScriptRun::Source { .. } | ScriptRun::Fault { .. } => None,
    }
}

#[test]
fn a_world_binding_reads_its_name_and_its_peer()
{
    let peer =
        Peer::new(Secret::generate().node_id()).at(SocketAddr::from((Ipv4Addr::LOCALHOST, 4433)));
    let bound = bindings(&WorldName::from("seat"), &peer);
    assert_eq!(
        bound
            .peer(&WorldName::from("seat"))
            .map(ToString::to_string),
        Some(peer.to_string()),
        "the world names the peer after its `=`"
    );
    assert!(
        bound.peer(&WorldName::from("operator")).is_none(),
        "a world no binding names has no host"
    );
    for (text, refusal) in [
        ("seat", "Unbound"),
        (&*format!("={peer}"), "Unnamed"),
        ("seat=not-a-key", "Peer"),
    ] {
        let read = WorldBinding::from_str(text);
        assert!(
            matches!(
                (&read, refusal),
                (Err(WorldBindingError::Unbound(_)), "Unbound")
                    | (Err(WorldBindingError::Unnamed(_)), "Unnamed")
                    | (Err(WorldBindingError::Peer(_)), "Peer")
            ),
            "`{text}` is refused {refusal}: {read:?}"
        );
    }
}

#[test]
fn a_world_bound_to_this_host_runs_here()
{
    let loopback = SocketAddr::from((Ipv4Addr::LOCALHOST, 0));
    let secret = Secret::from_str(HOST_SECRET).expect("the secret is hex");
    let here = Peer::new(secret.node_id()).at(loopback);
    let mut script = Script::new(model());
    script.network(Net::new(Binding::new(secret).at(loopback)));
    script.bindings(bindings(&WorldName::from("far"), &here));
    assert_eq!(
        exited(&mut script),
        Some(ExitStatus::from(42_u8)),
        "a world bound to this host's key runs here, and no host elsewhere is asked"
    );
}

#[test]
fn a_world_no_binding_names_is_refused_before_the_run()
{
    let elsewhere =
        Peer::new(Secret::generate().node_id()).at(SocketAddr::from((Ipv4Addr::LOCALHOST, 4433)));
    let mut script = Script::new(model());
    script.bindings(bindings(&WorldName::from("near"), &elsewhere));
    let run = script.run(&mut Captured::default());
    assert!(
        matches!(
            run,
            ScriptRun::Source {
                ran: Ran::Entered {
                    entered: Entered::Ended(Evaluation::Unrunnable(Unrunnable::UnboundWorld(world))),
                    ..
                },
                ..
            } if world.as_ref() == "far"
        ),
        "an entry that may migrate to a world no binding names never runs: {run:?}"
    );
}

/// A network bound at `socket` under `secret`, bound again while a host that
/// just ended there still holds the socket.
///
/// # Specification
/// trivial.
fn bound(
    secret: &Secret,
    socket: SocketAddr,
) -> Net
{
    let mut net = Net::new(Binding::new(secret.clone()).at(socket));
    let mut attempts = 0_u32;
    while net.endpoint().is_err() {
        attempts = attempts.saturating_add(1);
        assert!(attempts < 100, "the host binds its socket");
        thread::sleep(Duration::from_millis(50));
    }
    net
}

/// The lines a host on `net` prints hosting `migrations` of the source at
/// `path`, `world` bound to `peer`, the host itself. The host keeps `net`
/// bound for `linger` after its last answer.
///
/// # Specification
/// trivial.
fn hosted(
    path: &Path,
    (net, world, peer): (Net, &WorldName, &Peer),
    (migrations, linger): (MigrationCount, Duration),
) -> Vec<String>
{
    let mut script = Script::new(path.to_path_buf());
    script.network(net);
    script.bindings(bindings(world, peer));
    script.hosting(migrations);
    let mut console = Captured::default();
    let run = script.run(&mut console);
    assert!(
        matches!(
            run,
            ScriptRun::Source {
                ran: Ran::Hosted(Hosted::Answered(answered)),
                ..
            } if answered == migrations
        ),
        "the host answers each migration: {run:?}"
    );
    thread::sleep(linger);
    console.lines().to_vec()
}

/// The chunks each of a host's `lines` says its migration's captures
/// fetched.
///
/// # Specification
/// trivial.
fn fetched(lines: &[String]) -> Vec<ChunkCount>
{
    lines
        .iter()
        .map(|line| {
            line.strip_prefix("ran a migration at seat, fetching ")
                .and_then(|rest| rest.strip_suffix(" chunks"))
                .and_then(|count| count.parse::<usize>().ok())
                .map(ChunkCount::from)
                .expect("a line naming the chunks fetched")
        })
        .collect()
}

/// A host that held a list and its edit at the seat ends, and another under
/// its key takes its place. The run's next migration reads the list there:
/// the new host fetches all of it from the runner. The one after reads the
/// edit: naming the list it holds, the host fetches only the chunks the edit
/// changed. The run answers as it would in one process.
///
/// Between the edit and the read the run migrates to a gate, which opens
/// only once the second host holds the seat's socket. The first host stays
/// bound for [`LINGER`] after its last answer, so a run that reached for the
/// seat before the gate answered would find the host that ended and stop
/// unreached. The hosts take their turns on a thread of their own, which a
/// run that stops is not held for.
#[test]
fn a_second_migration_of_an_edited_list_fetches_what_changed_3365()
{
    let listed = (1 ..= LISTED)
        .map(|element| element.to_string())
        .collect::<Vec<_>>()
        .join(", ");
    let text = format!(
        "pub world operator;\npub world seat;\npub world gate;\n\ndef rec size(xs : \
         List(Integer)) -> Integer {{\n  case xs {{\n    [] => 0,\n    [x, ..rest] => 1 + \
         size[<](rest)\n  }}\n}}\n\n@[ entry((operator, seat, seat, gate, seat, seat)) ]\ndef \
         main() -> Integer {{\n  run listed : List(Integer) at seat <- migrate [seat] {{ (hold \
         [{listed}]) }};\n  leta xs = listed;\n  run edited : List(Integer) at seat <- migrate \
         [seat] {{ (hold cons(0, xs)) }};\n  leta ys = edited;\n  run opened <- migrate [gate] \
         {{ pure 0 }};\n  run before <- migrate [seat] {{ size(xs) }};\n  run after <- migrate \
         [seat] {{ size(ys) }};\n  pure (after - before + 41 + opened)\n}}\n"
    );
    let file = Scratch::write(Path::new("descent"), SourceText::from(text.as_str()));
    let alone = exited(&mut Script::new(file.0.clone()));
    assert_eq!(
        alone,
        Some(ExitStatus::from(42_u8)),
        "in one process the run answers 42"
    );
    let free = || {
        UdpSocket::bind(SocketAddr::from((Ipv4Addr::LOCALHOST, 0))).expect("a free loopback port")
    };
    let (socket, door) = {
        let (seat, gate) = (free(), free());
        (
            seat.local_addr().expect("the seat's probe has an address"),
            gate.local_addr().expect("the gate's probe has an address"),
        )
    };
    let host = Secret::from_str(HOST_SECRET).expect("the secret is hex");
    let peer = Peer::new(host.node_id()).at(socket);
    let keeper = Secret::generate();
    let gatekeeper = Peer::new(keeper.node_id()).at(door);
    let hosts = thread::spawn({
        let (path, peer, gatekeeper) = (file.0.clone(), peer.clone(), gatekeeper.clone());
        move || {
            let (seat, gate) = (WorldName::from("seat"), WorldName::from("gate"));
            let two = MigrationCount::from(2_usize);
            thread::scope(|scope| {
                let first = hosted(&path, (bound(&host, socket), &seat, &peer), (two, LINGER));
                let net = bound(&host, socket);
                let (path, seat, peer) = (&path, &seat, &peer);
                let second =
                    scope.spawn(move || hosted(path, (net, seat, peer), (two, Duration::ZERO)));
                hosted(
                    path,
                    (bound(&keeper, door), &gate, &gatekeeper),
                    (MigrationCount::from(1_usize), Duration::ZERO),
                );
                (first, second.join().expect("the second host ends"))
            })
        }
    });
    let mut script = Script::new(file.0.clone());
    script.network(Net::new(
        Binding::new(Secret::generate()).at(SocketAddr::from((Ipv4Addr::LOCALHOST, 0))),
    ));
    script.bindings(WorldBindings::new(vec![
        binding(&WorldName::from("seat"), &peer),
        binding(&WorldName::from("gate"), &gatekeeper),
    ]));
    let run = script.run(&mut Captured::default());
    let ScriptRun::Source { ref ran, .. } = run
    else {
        panic!("the source runs: {run:?}");
    };
    assert!(
        matches!(ran, Ran::Entered { entered: Entered::Exited(status), .. } if *status == ExitStatus::from(42_u8)),
        "across hosts the run answers 42: {ran:?}"
    );
    let (first, second) = hosts.join().expect("the hosts end");
    assert_eq!(
        fetched(&first),
        [ChunkCount::from(0_usize); 2],
        "the first host made both values it read"
    );
    let second = fetched(&second);
    assert!(
        matches!(*second, [whole, edit] if ChunkCount::from(0_usize) < edit && edit < whole),
        "the second host fetches the list whole, then fewer chunks for its edit: {second:?}"
    );
}
