//! Session traces replayed against a fresh server: a scene recorded through
//! `gandr lsp` replays whole, a trace whose answer was altered parts at that
//! line, and a session that asks for a trace writes one its replay holds.

use std::path::PathBuf;

use gandr_surface_lsp::Body;
use gandr_surface_lsp::Parted;
use gandr_surface_lsp::Pool;
use gandr_surface_lsp::Served;
use gandr_surface_lsp::Spelling;
use gandr_surface_lsp::Width;
use gandr_surface_lsp::Workspace;
use gandr_surface_lsp::replay;
use gandr_surface_lsp::serve;
use gandr_surface_lsp::write_frame;
use serde_json::Value;
use serde_json::json;

/// The pool a replay runs on: one thread, so each judgement and admission
/// runs where it is submitted.
static SERIAL: Pool = Pool::new(Width::SERIAL);

/// The scene `fixing_a_mismatch_clears_its_diagnostic` types, recorded through
/// `gandr lsp --standalone` with a trace asked for: a document opened, a
/// string typed where an integer is declared, a hover over the declaration,
/// the integer typed back and a hover over it, each step a second apart.
const SCENE: &str = include_str!("replay/fixing-a-mismatch.trace");

/// A trace file under the system's temporary directory, named for this
/// process, removed when dropped.
#[repr(transparent)]
struct Scratch(PathBuf);

impl Scratch
{
    /// A path no file is at, named for this process.
    ///
    /// # Specification
    /// trivial.
    fn new() -> Self
    {
        let path =
            std::env::temp_dir().join(format!("gandr-lsp-trace-{}.trace", std::process::id()));
        let _cleared = std::fs::remove_file(&path);
        Self(path)
    }
}

impl Drop for Scratch
{
    /// Remove the file.
    ///
    /// # Specification
    /// trivial.
    fn drop(&mut self)
    {
        let _removed = std::fs::remove_file(&self.0);
    }
}

#[test]
fn a_recorded_scene_replays_against_a_fresh_server()
{
    let replayed =
        replay(SCENE.as_bytes(), &SERIAL).unwrap_or_else(|divergence| panic!("{divergence}"));
    assert_eq!(
        usize::from(replayed),
        SCENE.lines().count(),
        "every line of the scene is met"
    );
}

#[test]
fn a_replay_parting_from_its_trace_names_the_line()
{
    let hover = SCENE
        .lines()
        .position(|line| line.contains(r#""id":2,"result""#))
        .expect("the scene answers its first hover");
    let altered: String = SCENE
        .lines()
        .enumerate()
        .map(|(index, line)| {
            if index == hover {
                line.replacen("a : Integer", "a : String", 1)
            }
            else {
                line.to_owned()
            }
        })
        .flat_map(|line| [line, String::from("\n")])
        .collect();
    let divergence = replay(altered.as_bytes(), &SERIAL).expect_err("the altered answer parts");
    assert_eq!(
        usize::from(divergence.line),
        hover + 1,
        "the replay parts at the altered answer's line: {divergence}"
    );
    let Parted::Wrote {
        ref replayed,
        ref recorded,
    } = divergence.parted
    else {
        panic!("the replay wrote another answer: {divergence}");
    };
    assert_eq!(
        replayed.pointer("/result/contents/value"),
        Some(&json!(
            "```gandr\na : Integer\n```\n\nrefused: the type this term synthesises does not convert to the type it is checked against"
        )),
        "the replay wrote the server's answer"
    );
    assert_eq!(
        replayed.get("id"),
        recorded.get("id"),
        "the answers answer one request"
    );
    let truncated: String = SCENE
        .lines()
        .take(hover)
        .chain(SCENE.lines().skip(hover.saturating_add(1)))
        .flat_map(|line| [line, "\n"])
        .collect();
    let divergence =
        replay(truncated.as_bytes(), &SERIAL).expect_err("an answer missing from the trace parts");
    assert!(
        matches!(divergence.parted, Parted::Unrecorded(_)),
        "the replay wrote what the trace lacks: {divergence}"
    );
}

#[test]
fn a_session_asking_for_a_trace_writes_one_its_replay_holds()
{
    let scratch = Scratch::new();
    let uri = "file:///trace/asked.gandr";
    let mut input = Vec::new();
    for message in [
        json!({ "jsonrpc": "2.0", "id": 1_i32, "method": "initialize", "params": {
            "capabilities": {},
            "initializationOptions": {
                "diagnostics": { "quiet": 0_i32 },
                "sessionTrace": scratch.0.to_string_lossy(),
            },
        }}),
        json!({ "jsonrpc": "2.0", "method": "initialized", "params": {} }),
        json!({ "jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
            "textDocument": {
                "uri": uri, "languageId": "gandr", "version": 1_i32, "text": "def a = 1 ;\n",
            },
        }}),
        json!({ "jsonrpc": "2.0", "id": 2_i32, "method": "textDocument/hover", "params": {
            "textDocument": { "uri": uri }, "position": { "line": 0_i32, "character": 4_i32 },
        }}),
        json!({ "jsonrpc": "2.0", "method": "textDocument/didChange", "params": {
            "textDocument": { "uri": uri, "version": 2_i32 },
            "contentChanges": [{ "text": "def a = 2 ;\n" }],
        }}),
        json!({ "jsonrpc": "2.0", "id": 3_i32, "method": "textDocument/hover", "params": {
            "textDocument": { "uri": uri }, "position": { "line": 0_i32, "character": 4_i32 },
        }}),
        json!({ "jsonrpc": "2.0", "id": 4_i32, "method": "shutdown" }),
        json!({ "jsonrpc": "2.0", "method": "exit" }),
    ] {
        write_frame(&mut input, &Body::from(message.to_string().into_bytes()))
            .expect("a vector takes every frame");
    }
    let served = serve(
        &mut input.as_slice(),
        &mut Vec::new(),
        &mut Vec::new(),
        (Workspace::spelled(Spelling::Unicode), &SERIAL),
    )
    .expect("the session's streams carry every frame");
    assert_eq!(served, Served::Clean, "the session ends cleanly");
    let trace = std::fs::read_to_string(&scratch.0).expect("the session wrote its trace");
    let first: Value = serde_json::from_str(trace.lines().next().unwrap_or_default())
        .expect("the trace's first line is JSON");
    assert_eq!(
        first.pointer("/read/method"),
        Some(&json!("initialize")),
        "the trace starts at the initialize asking for it"
    );
    let replayed =
        replay(trace.as_bytes(), &SERIAL).unwrap_or_else(|divergence| panic!("{divergence}"));
    assert_eq!(
        usize::from(replayed),
        trace.lines().count(),
        "the replay meets every line the session wrote"
    );
}
