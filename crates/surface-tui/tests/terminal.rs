//! The faces that claim the process's terminal, each run as a child test of
//! this binary on a pseudo-terminal: `script` gives the child one, and the
//! parent types its keys once the face has entered the alternate screen, which
//! it does after the terminal is raw. Linux's `script` is util-linux's, and
//! macOS's is the BSD one, which spells the child differently ([`script`]).

use std::io::IsTerminal as _;
#[cfg(any(target_os = "linux", target_os = "macos"))]
use std::io::Read as _;
#[cfg(any(target_os = "linux", target_os = "macos"))]
use std::io::Write as _;
use std::process::Command;
use std::process::Stdio;

#[cfg(any(target_os = "linux", target_os = "macos"))]
use anodized::spec;
use gandr_surface_render_remote::RenderFrame;
use gandr_surface_repl::Ended;
use gandr_surface_tui::Following;
use gandr_surface_tui::Heard;
use gandr_surface_tui::follow;

/// The escape sequence a face writes on entering the alternate screen.
#[cfg(any(target_os = "linux", target_os = "macos"))]
const ALTERNATE_SCREEN: &[u8] = b"\x1b[?1049h";

/// One test of this binary, by its path.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
#[cfg(any(target_os = "linux", target_os = "macos"))]
struct Child(&'static str);

/// The bytes typed on the child's terminal once its face is up.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
#[cfg(any(target_os = "linux", target_os = "macos"))]
struct Keys(&'static [u8]);

/// The terminal's settings, as `stty -g` prints them.
#[repr(transparent)]
#[derive(Debug, Eq, PartialEq)]
struct Settings(Vec<u8>);

/// The settings of the terminal on standard input.
///
/// # Specification
/// trivial.
fn settings() -> Settings
{
    let read = Command::new("stty")
        .arg("-g")
        .stdin(Stdio::inherit())
        .output()
        .expect("terminal settings can be read");
    assert!(read.status.success());
    Settings(read.stdout)
}

/// The side view's process: on a terminal, over a bus the hub has already
/// closed, the view completes, sends the hub one detach line, and leaves the
/// terminal's settings as it found them.
#[test]
#[ignore = "requires an attached terminal; run by `the_side_view_claims_and_restores_a_terminal`"]
fn the_side_view_completes_and_restores_its_settings()
{
    assert!(std::io::stdin().is_terminal() && std::io::stdout().is_terminal());
    let before = settings();
    let mut written = Vec::new();
    let closed: &[u8] = b"";
    let ended = follow(closed, &mut written).expect("the side view runs");
    assert_eq!(
        settings(),
        before,
        "the original terminal settings are restored"
    );
    assert!(matches!(ended, Ended::Completed));
    let line = String::from_utf8(written).expect("the line is text");
    let frame: RenderFrame = serde_json::from_str(line.strip_suffix('\n').expect("one line"))
        .expect("the line is a frame");
    assert_eq!(Following::default().hear(&frame), Heard::Detached);
}

/// util-linux's `script`, set to run `child` of this binary on a fresh
/// pseudo-terminal, keeping no typescript and exiting with the child's status
/// (`--return`). It takes the child as one shell command after `--command`,
/// before the typescript's file.
///
/// # Specification
/// trivial.
#[cfg(target_os = "linux")]
fn script(child: Child) -> Command
{
    let binary = std::env::current_exe().expect("the test binary is named");
    let command = format!(
        "'{}' --exact {} --ignored --test-threads=1 --color=never",
        binary.display(),
        child.0
    );
    let mut script = Command::new("script");
    let _set = script.args([
        "--quiet",
        "--return",
        "--command",
        command.as_str(),
        "/dev/null",
    ]);
    script
}

/// The BSD `script` macOS ships, set to run `child` of this binary on a fresh
/// pseudo-terminal, keeping no typescript. It takes the child as the words
/// after the typescript's file, run without a shell, and always exits with the
/// child's status.
///
/// # Specification
/// trivial.
#[cfg(target_os = "macos")]
fn script(child: Child) -> Command
{
    let binary = std::env::current_exe().expect("the test binary is named");
    let mut script = Command::new("script");
    let _set = script.args(["-q", "/dev/null"]).arg(binary).args([
        "--exact",
        child.0,
        "--ignored",
        "--test-threads=1",
        "--color=never",
    ]);
    script
}

/// What the test harness reports when `child` runs on a pseudo-terminal and
/// `keys` are typed once the face has entered the alternate screen.
///
/// # Specification
/// - requires: `script` is on the path, util-linux's on Linux and the BSD one
///   on macOS; the test binary can be started again.
/// - ensures: the child's whole terminal output, escape sequences included,
///   holding the harness's report of the one test it ran.
/// - provides: the pseudo-terminal observer of the faces that claim a terminal.
/// - fails: never.
/// - panics: if `script` cannot start, if the face never enters the alternate
///   screen, or if the child fails.
///
/// # Adequacy
/// - hypothesis: L3 — the face's own witness, which compares the terminal's
///   settings before and after, passes only when the keys reach it and it ends
///   completed; a lost key leaves the run waiting and a wrong ending fails it.
/// - witness: `tests::terminal::the_terminal_face_reads_its_keys_and_restores_a_terminal`
/// - witness: `tests::terminal::the_side_view_claims_and_restores_a_terminal`
#[cfg(any(target_os = "linux", target_os = "macos"))]
#[spec(ensures: |ref ret| ret.contains("1 passed"))]
fn on_a_terminal(
    child: Child,
    keys: Keys,
) -> String
{
    let mut script = script(child)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("script starts");
    let mut typing = script.stdin.take().expect("standard input is piped");
    let mut output = script.stdout.take().expect("standard output is piped");
    let mut seen = Vec::new();
    let mut chunk = [0_u8; 4096];
    while !seen
        .windows(ALTERNATE_SCREEN.len())
        .any(|window| window == ALTERNATE_SCREEN)
    {
        let read = output.read(&mut chunk).expect("the terminal is read");
        assert_ne!(
            read,
            0,
            "the face never entered the alternate screen: {}",
            String::from_utf8_lossy(&seen)
        );
        seen.extend_from_slice(chunk.get(.. read).unwrap_or_default());
    }
    typing.write_all(keys.0).expect("the keys are typed");
    typing.flush().expect("the keys are sent");
    let _rest = output
        .read_to_end(&mut seen)
        .expect("the terminal is read to its end");
    let ran = script.wait_with_output().expect("script ends");
    drop(typing);
    let report = String::from_utf8_lossy(&seen).into_owned();
    assert!(
        ran.status.success(),
        "{report}\n{}",
        String::from_utf8_lossy(&ran.stderr)
    );
    report
}

/// The terminal face claims a real terminal: keys typed on it reach the loop
/// through the keyboard, `:quit` ends the run completed, and the terminal's
/// settings are restored.
#[cfg(any(target_os = "linux", target_os = "macos"))]
#[test]
fn the_terminal_face_reads_its_keys_and_restores_a_terminal()
{
    let report = on_a_terminal(
        Child("launch::the_terminal_face_completes_and_restores_its_settings"),
        Keys(b":quit\r"),
    );
    assert!(
        report.contains("test launch::the_terminal_face_completes_and_restores_its_settings ... ")
            && report.contains("test result: ok. 1 passed"),
        "{report}"
    );
}

/// The side view claims a real terminal, completes when the hub's stream
/// ends, detaches, and restores the terminal's settings.
#[cfg(any(target_os = "linux", target_os = "macos"))]
#[test]
fn the_side_view_claims_and_restores_a_terminal()
{
    let report = on_a_terminal(
        Child("terminal::the_side_view_completes_and_restores_its_settings"),
        Keys(b""),
    );
    assert!(
        report.contains("test terminal::the_side_view_completes_and_restores_its_settings ... ")
            && report.contains("test result: ok. 1 passed"),
        "{report}"
    );
}
