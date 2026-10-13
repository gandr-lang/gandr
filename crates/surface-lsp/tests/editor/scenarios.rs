//! The scenarios: the corpus typed and erased, scripted edits that break and
//! fix a document, and random edit scripts undone to where they started.

use alloc::string::String;
use alloc::vec::Vec;
use core::num::NonZeroUsize;
use core::sync::atomic::AtomicUsize;
use core::sync::atomic::Ordering;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use percent_encoding::AsciiSet;
use percent_encoding::NON_ALPHANUMERIC;
use percent_encoding::utf8_percent_encode;
use proptest::prelude::Just;
use proptest::prelude::ProptestConfig;
use proptest::prelude::Strategy;
use proptest::prelude::any;
use proptest::prop_assert_eq;
use proptest::prop_oneof;
use proptest::proptest;
use proptest::sample::select;
use serde_json::Value;
use serde_json::json;

use super::buffer::Buffer;
use super::buffer::History;
use super::buffer::Key;
use super::buffer::Offset;
use super::buffer::Position;
use super::buffer::Text;
use super::buffer::Typing;
use super::editing::Oracle;
use super::editing::Session;

/// The random edit scripts each run generates.
const CASES: u32 = 32;

/// The texts a random edit script starts from.
const SEEDS: [&str; 4] = [
    "",
    "def a : Integer ;\ndef a = 1 ;\n",
    "def f(x : Integer) -> -F Integer {\n  return x\n}\n",
    "data Nat : Type {\n  Zero : Nat;\n  Succ : (n : Nat) --> Nat;\n}\n\ndef rec down(n : Nat) -> -F Nat {\n  case n {\n    Zero => return n,\n    Succ(p) => become down[<](p)\n  }\n}\n",
];

/// What a random script types, one token per step.
const TOKENS: [&str; 34] = [
    "def", " ", "a", "x", "1", "\"", "(", ")", "{", "}", "[", "]", ":", ";", ",", "=", "->", "=>",
    "<-", "-F", "+U", "Integer", "return", "become", "case", "thunk", "force", "run", "fn", "data",
    "Type", "//", "é", "😀",
];

/// What a random script pastes.
const SNIPPETS: [&str; 4] = [
    "def b = a ;\n",
    "case n {\n  Zero => return n\n}",
    "\"text\"",
    "thunk { return 1 }",
];

/// The bytes a `file` URI's path keeps unescaped: RFC 3986's unreserved
/// characters and the separator.
const PATH: &AsciiSet = &NON_ALPHANUMERIC
    .remove(b'-')
    .remove(b'.')
    .remove(b'_')
    .remove(b'~')
    .remove(b'/');

/// One corpus source as an editor opens it.
struct Source
{
    /// Its `file` URI.
    uri: String,
    /// Its text.
    text: String,
}

/// Every corpus source, in path order, under its canonical path so it
/// classifies as the walk classifies it.
///
/// # Specification
/// - requires: the corpus crate sits beside this one.
/// - ensures: one source per `.gandr` file under the corpus's `strict` and
///   `fixture` roots, in path order, each with its percent-escaped `file` URI.
/// - provides: the texts the corpus scenarios type and erase.
/// - panics: the corpus cannot be read.
///
/// # Adequacy
/// - hypothesis: L3 — the corpus scenarios assert they reached more than a
///   hundred sources; an empty or truncated walk fails that floor.
/// - witness: `editor::editor::scenarios::typing_each_corpus_source_keeps_every_answer_faithful`
#[spec(ensures: |ret| ret.len() > 100 && ret.iter().all(|source|
    source.uri.starts_with("file://")
        && Path::new(&source.uri).extension().is_some_and(|extension| extension == "gandr")))]
fn corpus() -> Vec<Source>
{
    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../surface-corpus")
        .canonicalize()
        .expect("the corpus sits beside the language server");
    let mut pending = vec![root.join("strict"), root.join("fixture")];
    let mut paths: Vec<PathBuf> = Vec::new();
    while let Some(directory) = pending.pop() {
        for entry in std::fs::read_dir(&directory).expect("a corpus directory reads") {
            let path = entry.expect("a corpus entry reads").path();
            if path.is_dir() {
                pending.push(path);
            }
            else if path
                .extension()
                .is_some_and(|extension| extension == "gandr")
            {
                paths.push(path);
            }
        }
    }
    paths.sort();
    paths
        .into_iter()
        .map(|path| {
            let text = std::fs::read_to_string(&path).expect("a corpus source reads");
            let spelled = path.to_str().expect("a corpus path is UTF-8");
            Source {
                uri: format!("file://{}", utf8_percent_encode(spelled, PATH)),
                text,
            }
        })
        .collect()
}

#[test]
fn positions_count_utf16_code_units()
{
    let text = Text("é😀x\ny");
    assert_eq!(
        Position::of(text, Offset(0)),
        Position {
            line: 0,
            character: 0
        },
        "the origin"
    );
    assert_eq!(
        Position::of(text, Offset("é".len())),
        Position {
            line: 0,
            character: 1
        },
        "a two-byte character is one code unit"
    );
    assert_eq!(
        Position::of(text, Offset("é😀".len())),
        Position {
            line: 0,
            character: 3
        },
        "an astral character is two code units"
    );
    assert_eq!(
        Position::of(text, Offset("é😀x\n".len())),
        Position {
            line: 1,
            character: 0
        },
        "a newline starts the next line"
    );
}

#[test]
fn assisted_typing_closes_and_steps_over_pairs()
{
    let mut buffer = Buffer::holding(Text(""), Typing::Assisted);
    let _typed: Vec<_> = "f("
        .chars()
        .map(|typed| buffer.type_char(Key(typed)))
        .collect();
    assert_eq!(
        (buffer.text(), buffer.cursor()),
        (Text("f()"), Offset(2)),
        "an opener closes itself"
    );
    assert!(
        buffer.type_char(Key(')')).is_empty(),
        "a typed closer steps over the inserted one"
    );
    assert_eq!(buffer.cursor(), Offset(3), "the cursor passes the closer");
    let _space = buffer.type_char(Key(' '));
    let _brace = buffer.type_char(Key('{'));
    let _enter = buffer.enter();
    assert_eq!(
        (buffer.text(), buffer.cursor()),
        (Text("f() {\n  \n}"), Offset(8)),
        "Enter between braces opens an indented line"
    );
    let _undone = buffer.undo();
    assert_eq!(
        (buffer.text(), buffer.cursor()),
        (Text("f() {}"), Offset(5)),
        "undo restores the pair"
    );
    let _deleted = buffer.backspace();
    assert_eq!(
        buffer.text(),
        Text("f() "),
        "backspace inside an empty pair deletes both"
    );
    let mut quoted = Buffer::holding(Text(""), Typing::Assisted);
    let _opened = quoted.type_char(Key('"'));
    let _letter = quoted.type_char(Key('a'));
    assert!(
        quoted.type_char(Key('"')).is_empty(),
        "a closing quote steps over"
    );
    assert_eq!(quoted.text(), Text("\"a\""), "the string is closed once");
    let mut nested = Buffer::holding(Text("  "), Typing::Assisted);
    let _outdented = nested.type_char(Key('}'));
    assert_eq!(
        nested.text(),
        Text("}"),
        "a closer first on a line outdents"
    );
}

/// One step of a random edit script.
#[derive(Clone, Copy, Debug)]
enum Edit
{
    /// Type a token, one keystroke per character.
    Type(&'static str),
    /// Press Enter.
    Enter,
    /// Press backspace.
    Backspace,
    /// Press delete.
    Delete,
    /// Move the cursor to this many thousandths of the text.
    Move(usize),
    /// Delete the cursor's line.
    DeleteLine,
    /// Paste a snippet at the cursor.
    Paste(&'static str),
    /// Undo the latest edit.
    Undo,
}

/// The edits a random script draws from, weighted towards typing.
///
/// # Specification
/// trivial.
fn edit() -> impl Strategy<Value = Edit>
{
    prop_oneof![
        6 => select(TOKENS.as_slice()).prop_map(Edit::Type),
        2 => Just(Edit::Enter),
        3 => Just(Edit::Backspace),
        1 => Just(Edit::Delete),
        3 => (0_usize ..= 1000_usize).prop_map(Edit::Move),
        1 => Just(Edit::DeleteLine),
        1 => select(SNIPPETS.as_slice()).prop_map(Edit::Paste),
        2 => Just(Edit::Undo),
    ]
}

/// Apply `edit` to `session`, keystroke by keystroke.
///
/// # Specification
/// trivial.
fn apply(
    session: &mut Session,
    edit: Edit,
)
{
    match edit {
        | Edit::Type(token) => token
            .chars()
            .for_each(|typed| session.type_char(Key(typed))),
        | Edit::Enter => session.enter(),
        | Edit::Backspace => session.backspace(),
        | Edit::Delete => session.delete(),
        | Edit::Move(thousandths) => {
            let text = session.buffer().text().0;
            let at = text
                .len()
                .saturating_mul(thousandths)
                .checked_div(1000_usize)
                .expect("a thousandth divides");
            let at = text.floor_char_boundary(at);
            session.move_to(Offset(at));
        },
        | Edit::DeleteLine => {
            let text = session.buffer().text().0;
            let cursor = session.buffer().cursor().0;
            let start = text
                .get(.. cursor)
                .and_then(|before| before.rfind('\n'))
                .map_or(0_usize, |newline| newline.saturating_add(1));
            let end = text
                .get(cursor ..)
                .and_then(|after| after.find('\n'))
                .map_or(text.len(), |newline| {
                    cursor.saturating_add(newline).saturating_add(1)
                });
            session.replace(Offset(start), Offset(end), Text(""));
        },
        | Edit::Paste(snippet) => {
            let cursor = session.buffer().cursor();
            session.replace(cursor, cursor, Text(snippet));
        },
        | Edit::Undo => session.undo(),
    }
}

/// Visit every source, spread over the machine's cores, the longest first so
/// no core is left with a long source at the end.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `visit` ran once on each source; a panic in any visit fails the
///   caller once every worker has stopped.
/// - provides: the corpus scenarios' wall time divided by the cores.
/// - panics: a visit panics.
/// - executable: none — the visits' effects are their own assertions, made on
///   worker threads; the call returns nothing that records them.
///
/// # Adequacy
/// - hypothesis: L3 — the corpus scenarios visit through here; one shared index
///   hands each source to exactly one worker, and a panic in a worker fails the
///   scope, so a failing source fails the scenario.
/// - witness: `editor::editor::scenarios::typing_each_corpus_source_keeps_every_answer_faithful`
fn each_in_parallel(
    sources: &[Source],
    visit: impl Fn(&Source) + Sync,
)
{
    let mut ordered: Vec<&Source> = sources.iter().collect();
    ordered.sort_by_key(|source| core::cmp::Reverse(source.text.len()));
    let next = AtomicUsize::new(0_usize);
    let workers = std::thread::available_parallelism().map_or(1_usize, NonZeroUsize::get);
    std::thread::scope(|scope| {
        for _ in 0_usize .. workers {
            let _worker = scope.spawn(|| {
                while let Some(source) = ordered.get(next.fetch_add(1_usize, Ordering::Relaxed)) {
                    visit(source);
                }
            });
        }
    });
}

#[test]
fn typing_each_corpus_source_keeps_every_answer_faithful()
{
    let sources = corpus();
    assert!(
        sources.len() > 100,
        "the corpus is walked whole: {}",
        sources.len()
    );
    each_in_parallel(&sources, |source| {
        let mut session =
            Session::open(source.uri.clone(), Text(""), Typing::Assisted, Oracle::Line);
        session.type_in(Text(&source.text));
        session.replays_over_streams();
    });
}

#[test]
fn erasing_each_corpus_source_line_by_line_keeps_every_answer_faithful()
{
    let sources = corpus();
    assert!(
        sources.len() > 100,
        "the corpus is walked whole: {}",
        sources.len()
    );
    each_in_parallel(&sources, |source| {
        let mut session = Session::open(
            source.uri.clone(),
            Text(&source.text),
            Typing::Assisted,
            Oracle::Keystroke,
        );
        session.erase_lines();
        assert!(
            session.buffer().text().0.is_empty(),
            "the document is erased"
        );
        session.replays_over_streams();
    });
}

#[test]
fn fixing_a_mismatch_clears_its_diagnostic()
{
    let text = "def a : Integer ;\ndef a = 1 ;\n";
    let mut session = Session::open(
        String::from("file:///strict/mismatch.gandr"),
        Text(text),
        Typing::Assisted,
        Oracle::Keystroke,
    );
    assert_eq!(session.codes(), Vec::<Value>::new(), "the document checks");
    let one = text.rfind('1').expect("the value is written");
    session.move_to(Offset(one.saturating_add(1)));
    session.backspace();
    session.type_in(Text("\"text\""));
    assert_eq!(
        session.codes(),
        [json!("TypeMismatch")],
        "a string is not an integer"
    );
    for _ in 0_u8 .. 6_u8 {
        session.backspace();
    }
    session.type_in(Text("1"));
    assert_eq!(
        session.codes(),
        Vec::<Value>::new(),
        "the fix clears the diagnostic"
    );
    session.replays_over_streams();
}

#[test]
fn defining_a_missing_name_clears_its_diagnostic()
{
    let mut session = Session::open(
        String::from("file:///strict/missing.gandr"),
        Text("def b = a ;\n"),
        Typing::Assisted,
        Oracle::Keystroke,
    );
    assert_eq!(
        session.codes(),
        [json!("UnresolvedName")],
        "`a` is not defined"
    );
    session.move_to(Offset(0));
    session.type_in(Text("def a = 1 ;\n"));
    assert_eq!(
        session.codes(),
        Vec::<Value>::new(),
        "defining `a` clears the diagnostic"
    );
    session.replays_over_streams();
}

#[test]
fn restoring_a_semicolon_clears_its_diagnostic()
{
    let text = "def a = 1 ;\ndef b = a ;\n";
    let mut session = Session::open(
        String::from("file:///strict/semicolon.gandr"),
        Text(text),
        Typing::Assisted,
        Oracle::Keystroke,
    );
    let semicolon = text.find(';').expect("the first definition ends");
    session.move_to(Offset(semicolon.saturating_add(1)));
    session.backspace();
    assert!(
        !session.codes().is_empty(),
        "a definition without its `;` is refused"
    );
    session.type_char(Key(';'));
    assert_eq!(
        session.codes(),
        Vec::<Value>::new(),
        "the `;` clears the diagnostic"
    );
    session.replays_over_streams();
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(CASES))]

    #[test]
    fn random_edits_keep_every_answer_faithful(
        seed in select(SEEDS.as_slice()),
        assisted in any::<bool>(),
        script in proptest::collection::vec(edit(), 1_usize .. 24_usize),
    ) {
        let typing = if assisted { Typing::Assisted } else { Typing::Plain };
        let mut session = Session::open(
            String::from("file:///strict/random.gandr"),
            Text(seed),
            typing,
            Oracle::Keystroke,
        );
        let opened = session.published().clone();
        for &step in &script {
            apply(&mut session, step);
        }
        while session.buffer().history() == History::Undoable {
            session.undo();
        }
        prop_assert_eq!(session.buffer().text(), Text(seed), "undoing every edit restores the text");
        prop_assert_eq!(session.published(), &opened, "and the diagnostics it opened with");
    }
}
