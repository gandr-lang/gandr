//! The terminal face run as its own process, its standard input piped: the
//! line editor reads the lines it is given, the loop answers each, and the
//! watch that needs a terminal is said to be off.

use std::io::Write as _;
use std::process::Command;
use std::process::Stdio;

use anodized::spec;
use gandr_surface_grammar::Spelling;
use gandr_surface_render_terminal::RenderStyle;
use gandr_surface_repl::Ended;
use gandr_surface_repl::run_interactive;

/// The variable that tells the child to run the face.
const CHILD: &str = "GANDR_REPL_TERMINAL_CHILD";

/// The face's process: run only when the parent test starts this binary for
/// it, writing the transcript and then the ending to standard output.
#[test]
#[ignore = "run by `the_terminal_face_reads_its_input_through_the_editor` as a child process"]
fn terminal_face_child()
{
    if std::env::var_os(CHILD).is_none() {
        return;
    }
    let mut output = std::io::stdout().lock();
    let ended = run_interactive(&mut output, RenderStyle::Plain, Spelling::Unicode)
        .expect("the transcript is written");
    writeln!(output, "ended: {}", match ended {
        Ended::Completed => "completed",
        Ended::Faulted(_) => "faulted",
    })
    .expect("the ending is written");
}

/// What the face writes after its watch notice when run as a child process
/// over `input` piped to its standard input, up to the test harness's own
/// verdict line.
///
/// # Specification
/// - requires: the test binary can be started again.
/// - ensures: the transcript the face wrote, the ending line last, without the
///   notice that the watch is off or the harness's lines around it.
/// - provides: the child-process observer of the terminal face.
/// - fails: never.
/// - panics: if the child cannot start or fails, or if it does not report its
///   watch as off.
///
/// # Adequacy
/// - hypothesis: L3 — exact transcripts of a quit run, an end-of-input run and
///   a faulted run distinguish a lost line, a lost prompt and a wrong ending.
/// - witness: `tests::terminal::the_terminal_face_reads_its_input_through_the_editor`
/// - witness: `tests::terminal::the_terminal_face_ends_at_the_end_of_input_and_faults_on_unreadable_input`
#[spec(ensures: |ref ret| ret.ends_with("ended: completed") || ret.ends_with("ended: faulted"))]
fn face<Input>(input: Input) -> String
where
    Input: AsRef<[u8]>,
{
    let mut child = Command::new(std::env::current_exe().expect("the test binary is named"))
        .args([
            "--exact",
            "terminal::terminal_face_child",
            "--ignored",
            "--nocapture",
            "--test-threads=1",
        ])
        .env(CHILD, "1")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("the face starts");
    child
        .stdin
        .take()
        .expect("standard input is piped")
        .write_all(input.as_ref())
        .expect("the lines are written");
    let ran = child.wait_with_output().expect("the face ends");
    let transcript = String::from_utf8(ran.stdout).expect("the transcript is UTF-8");
    assert!(
        ran.status.success(),
        "{transcript}\n{}",
        String::from_utf8_lossy(&ran.stderr)
    );
    let Some((_, watch)) = transcript.split_once("loaded files are not watched for changes")
    else {
        panic!("the watch is reported as off: {transcript}");
    };
    let session = watch
        .split_once('\n')
        .map(|(_, rest)| rest)
        .unwrap_or_default();
    String::from(
        session
            .split_once("\nok\n")
            .map_or(session, |(written, _)| written),
    )
}

/// Piped lines reach the loop through the line editor: a definition is
/// answered with its type and value under the fresh prompt, an open form
/// waits under the continuing prompt, a later line reads both, `:quit` ends
/// the run completed before the line after it, and the watch, which needs a
/// terminal, is reported as off.
#[test]
fn the_terminal_face_reads_its_input_through_the_editor()
{
    assert_eq!(
        face("def a = 41 ;\ndef b = (\na) ;\ndef c = b ;\n:quit\ndef never = 0 ;\n"),
        "gandr> ▸ def a = 41 ;\na : Integer\n= 41\ngandr>   ...> ▸ def b = (\n  a) ;\nb : \
         Integer\n= 41\ngandr> ▸ def c = b ;\nc : Integer\n= 41\ngandr> ended: completed",
    );
}

/// The end of input ends the run completed, submitting the buffer still
/// open; input the editor cannot read ends it faulted.
#[test]
fn the_terminal_face_ends_at_the_end_of_input_and_faults_on_unreadable_input()
{
    let ended = face("def a = (\n1 ;\n");
    assert!(
        ended.starts_with("gandr>   ...>   ...> ▸ def a = (\n  1 ;\n")
            && ended.contains("warning[W0012]: parse repaired")
            && ended.ends_with("\nended: completed"),
        "the open buffer is submitted at the end of input: {ended}"
    );
    assert_eq!(
        face(b"def a = 1 ;\n\xff\xfe\n".as_slice()),
        "gandr> ▸ def a = 1 ;\na : Integer\n= 1\ngandr> ended: faulted",
        "the line before the unreadable one is answered, and the run ends faulted"
    );
}
