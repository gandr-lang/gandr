//! The scenarios: the corpus typed and erased, scripted edits that break and
//! fix a document, and random edit scripts undone to where they started.
//!
//! The gate types and erases a sample of the corpus and generates a share of
//! the random scripts; `GANDR_SWEEPS_WHOLE=1` (`mise run ci:sweeps`, the
//! daily lane) visits every source and runs every script. A source that fails
//! in the sample fails the gate, and one outside it fails the daily lane.

use alloc::string::String;
use alloc::vec::Vec;
use core::num::NonZeroUsize;
use core::panic::AssertUnwindSafe;
use core::sync::atomic::AtomicUsize;
use core::sync::atomic::Ordering;
use std::panic::catch_unwind;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use gandr_surface_lsp::DocumentUri;
use gandr_surface_parser::Lexeme;
use gandr_surface_parser::label;
use gandr_surface_syntax::SourceFragment;
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
use super::client::Client;
use super::client::Method;
use super::client::Quiet;
use super::client::Record;
use super::editing::Oracle;
use super::editing::Session;
use super::editing::panic_message;

/// The share of corpus positions a hover answers, in thousandths, below
/// which hovering has regressed: the share measured when it was last
/// changed. A change that answers more positions raises it; a position inside
/// a declaration's body that no entry holds answers nothing, so the
/// declaration's own answer is not counted there. A position inside a comment
/// is hovered but not counted: a comment is no hover target, and corpus items
/// carry comments saying what they demonstrate, so counting them would lower
/// the share for documentation alone.
const ANSWERED_FLOOR: usize = 773;

/// The random edit scripts each scenario generates in a whole run.
const CASES: u32 = 32;

/// The random edit scripts each scenario generates in the gate's run: a
/// quarter of the whole's. Their cost is the scripts' keystrokes: the whole's
/// 32 took the random-edit scenario 40 s and the two-editor scenarios 22 s
/// and 19 s on the enforcing lane (medians of five merge-queue runs).
const SAMPLED_CASES: u32 = 8;

/// The gate's erasure: every fourth corpus source by index after the length
/// sort, the longest in, every keystroke held to the oracle. On four cores
/// with specifications enforced the sample erases in 29 s against the whole
/// corpus's 48 s, the longest source setting both.
const ERASED: Sample = Sample {
    stride: Stride(4),
    ceiling: Ceiling(usize::MAX),
};

/// The gate's typing, a smoke: every eighth corpus source no longer than a
/// kibibyte, by index after the length sort. On four cores with
/// specifications enforced the whole corpus types in 88 s, 66 s of it the
/// longest source alone, which no sample that keeps that source can shorten;
/// the sources past the ceiling are typed by the whole run, and the erasure's
/// sample still holds the longest to the oracle at every keystroke. The smoke
/// types in 4 s.
const TYPED: Sample = Sample {
    stride: Stride(8),
    ceiling: Ceiling(1024),
};

/// What part of the corpus a sweep visits under the gate; the whole run,
/// `GANDR_SWEEPS_WHOLE=1` (`mise run ci:sweeps`), visits every source.
#[derive(Clone, Copy, Debug)]
struct Sample
{
    /// The step between the sources it visits.
    stride: Stride,
    /// The longest source it visits.
    ceiling: Ceiling,
}

/// A sample's step: it visits the sources whose index after the length sort
/// this divides.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Stride(usize);

/// The length in bytes past which a source is left to the whole run.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Ceiling(usize);

/// How much a run of the corpus sweeps covers.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Sweep
{
    /// Every source and every random script: `mise run ci:sweeps`, the
    /// daily lane.
    Whole,
    /// The gate's samples and its share of random scripts: `mise run check`.
    Sampled,
}

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

impl Sweep
{
    /// The coverage the environment asks for: the whole when
    /// `GANDR_SWEEPS_WHOLE` is set, the gate's samples otherwise.
    ///
    /// # Specification
    /// trivial.
    fn asked() -> Self
    {
        if std::env::var_os("GANDR_SWEEPS_WHOLE").is_some() {
            Self::Whole
        }
        else {
            Self::Sampled
        }
    }

    /// The corpus sources a sweep visits, the longest first: every source in
    /// a whole run, and `sample`'s share in the gate's.
    ///
    /// # Specification
    /// - requires: the corpus crate sits beside this one.
    /// - ensures: the walk reached more than a hundred sources. A whole run
    ///   returns every one; a sampled run returns, of those no longer than the
    ///   sample's ceiling, the ones whose index after the length sort its
    ///   stride divides, standing for more than a hundred sources. Either way
    ///   longest first, sources of one length in path order.
    /// - provides: the sources the typing and the erasure visit.
    /// - panics: the corpus cannot be read, the walk reaches a hundred sources
    ///   or fewer, or the sample stands for a hundred or fewer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a truncated walk fails the whole run's floor, and a
    ///   sample whose ceiling or stride left too few sources fails the sampled
    ///   run's; the order is the predicate's.
    /// - witness: `editor::editor::scenarios::typing_each_corpus_source_keeps_every_answer_faithful`
    /// - witness: `editor::editor::scenarios::erasing_each_corpus_source_line_by_line_keeps_every_answer_faithful`
    #[spec(ensures: |ret| ret.is_sorted_by(|longer, shorter| longer.text.len() >= shorter.text.len()))]
    fn visited(
        self,
        sample: Sample,
    ) -> Vec<Source>
    {
        let mut sources = corpus();
        assert!(
            sources.len() > 100,
            "the corpus is walked whole: {}",
            sources.len()
        );
        sources.sort_by_key(|source| core::cmp::Reverse(source.text.len()));
        if self == Self::Whole {
            return sources;
        }
        let Sample {
            stride: Stride(stride),
            ceiling: Ceiling(ceiling),
        } = sample;
        let sampled: Vec<Source> = sources
            .into_iter()
            .filter(|source| source.text.len() <= ceiling)
            .step_by(stride)
            .collect();
        assert!(
            sampled.len().saturating_mul(stride) > 100,
            "every {stride}th source of at most {ceiling} bytes stands for a hundred or more: {}",
            sampled.len()
        );
        sampled
    }

    /// The random edit scripts each scenario generates.
    ///
    /// # Specification
    /// trivial.
    fn scripts(self) -> ProptestConfig
    {
        ProptestConfig::with_cases(match self {
            | Self::Whole => CASES,
            | Self::Sampled => SAMPLED_CASES,
        })
    }
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
///   caller once every worker has stopped, its message naming the source the
///   visit was given.
/// - provides: the corpus scenarios' wall time divided by the cores.
/// - panics: a visit panics.
/// - executable: none — the visits' effects are their own assertions, made on
///   worker threads; the call returns nothing that records them.
///
/// # Adequacy
/// - hypothesis: L3 — the corpus scenarios visit through here; one shared index
///   hands each source to exactly one worker, and a panic in a worker fails the
///   scope, so a failing source fails the scenario, and the daily lane's log
///   names it.
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
                    if let Err(payload) = catch_unwind(AssertUnwindSafe(|| visit(source))) {
                        panic!("visiting {}: {}", source.uri, panic_message(&*payload).0);
                    }
                }
            });
        }
    });
}

#[test]
fn typing_each_corpus_source_keeps_every_answer_faithful()
{
    let sources = Sweep::asked().visited(TYPED);
    each_in_parallel(&sources, |source| {
        let mut session =
            Session::open(source.uri.clone(), Text(""), Typing::Assisted, Oracle::Line);
        session.type_in(Text(&source.text));
        session.closes_over_streams();
    });
}

#[test]
fn erasing_each_corpus_source_line_by_line_keeps_every_answer_faithful()
{
    let sources = Sweep::asked().visited(ERASED);
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
        session.closes_over_streams();
    });
}

#[test]
fn hovering_every_position_of_each_corpus_source_answers_without_fault()
{
    let sources = corpus();
    assert!(
        sources.len() > 100,
        "the corpus is walked whole: {}",
        sources.len()
    );
    let positions = AtomicUsize::new(0_usize);
    let answered = AtomicUsize::new(0_usize);
    each_in_parallel(&sources, |source| {
        let mut client = Client::initialized(Record::Dropped, Quiet::Unheld);
        let _opened = client.notify(
            Method("textDocument/didOpen"),
            &json!({ "textDocument": {
                "uri": source.uri, "languageId": "gandr", "version": 1_i32, "text": source.text,
            }}),
        );
        let text = Text(&source.text);
        let comments: Vec<(usize, usize)> = label(SourceFragment::from(source.text.as_str()))
            .into_iter()
            .filter(|token| token.lexeme == Lexeme::Space)
            .filter_map(|token| {
                let start = usize::try_from(token.start).ok()?;
                let end = usize::try_from(token.end).ok()?;
                let layout = source.text.get(start .. end)?;
                (layout.starts_with("//") || layout.starts_with("/*")).then_some((start, end))
            })
            .collect();
        let offsets = source
            .text
            .char_indices()
            .map(|(offset, _)| offset)
            .chain([source.text.len()]);
        for offset in offsets {
            let at = Position::of(text, Offset(offset));
            let shown = client.request(
                Method("textDocument/hover"),
                &json!({ "textDocument": { "uri": source.uri }, "position": at.json() }),
            );
            if comments
                .iter()
                .any(|&(start, end)| (start .. end).contains(&offset))
            {
                continue;
            }
            let _counted = positions.fetch_add(1_usize, Ordering::Relaxed);
            if !shown.is_null() {
                let _counted = answered.fetch_add(1_usize, Ordering::Relaxed);
            }
        }
    });
    let positions = positions.into_inner();
    let answered = answered.into_inner();
    let share = answered
        .saturating_mul(1000_usize)
        .checked_div(positions)
        .unwrap_or_default();
    assert!(
        share >= ANSWERED_FLOOR,
        "hovers answer {answered} of {positions} corpus positions, {share}‰, below the floor of \
         {ANSWERED_FLOOR}‰"
    );
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
    session.closes_over_streams();
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
    session.closes_over_streams();
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
    session.closes_over_streams();
}

/// The document the quiet scenario types into: three declarations, the last
/// naming the first.
const QUIET_SEED: &str = "def one = 1 ;\ndef mid = 2 ;\ndef two = one ;\n";

/// The document's URI.
const QUIET_URI: &str = "file:///strict/quiet.gandr";

/// The declaration the quiet scenario types on the line after the seed's.
const QUIET_DECLARATION: &str = "def three = two ;";

/// Each diagnostic notification among `messages`, as the `[code, line]` of
/// each diagnostic it publishes.
///
/// # Specification
/// trivial.
fn publications(messages: &[Value]) -> Vec<Vec<Value>>
{
    messages
        .iter()
        .filter(|message| message.get("method") == Some(&json!("textDocument/publishDiagnostics")))
        .map(|message| {
            message
                .pointer("/params/diagnostics")
                .and_then(Value::as_array)
                .map(|diagnostics| {
                    diagnostics
                        .iter()
                        .map(|diagnostic| {
                            json!([
                                diagnostic.get("code"),
                                diagnostic.pointer("/range/start/line")
                            ])
                        })
                        .collect()
                })
                .unwrap_or_default()
        })
        .collect()
}

/// A connection with [`QUIET_SEED`] open at [`QUIET_URI`], changed one
/// ranged change at a time, each at the next version.
struct Typist
{
    /// The connection.
    client: Client,
    /// The version the latest change carried.
    version: i32,
}

impl Typist
{
    /// A connection at the quiet interval `quiet`, the seed open at version 1.
    ///
    /// # Specification
    /// trivial.
    fn opened(quiet: Quiet) -> Self
    {
        let mut client = Client::initialized(Record::Dropped, quiet);
        let _opened = client.notify(
            Method("textDocument/didOpen"),
            &json!({ "textDocument": {
                "uri": QUIET_URI, "languageId": "gandr", "version": 1_i32, "text": QUIET_SEED,
            } }),
        );
        Self {
            client,
            version: 1_i32,
        }
    }

    /// Replace what lies from `start` to `end` with `text` in one ranged
    /// change, and return its publications.
    ///
    /// # Specification
    /// trivial.
    fn replace(
        &mut self,
        start: Position,
        end: Position,
        Text(text): Text<'_>,
    ) -> Vec<Vec<Value>>
    {
        self.version = self.version.saturating_add(1_i32);
        publications(&self.client.notify(
            Method("textDocument/didChange"),
            &json!({
                "textDocument": { "uri": QUIET_URI, "version": self.version },
                "contentChanges": [{
                    "range": {
                        "start": { "line": start.line, "character": start.character },
                        "end": { "line": end.line, "character": end.character },
                    },
                    "text": text,
                }],
            }),
        ))
    }

    /// Type `text` at `at`, one character a change, and return each
    /// keystroke's publications.
    ///
    /// # Specification
    /// trivial.
    fn type_at(
        &mut self,
        at: Position,
        Text(text): Text<'_>,
    ) -> Vec<Vec<Vec<Value>>>
    {
        let mut caret = at;
        text.chars()
            .map(|typed| {
                let published = self.replace(caret, caret, Text(typed.encode_utf8(&mut [0_u8; 4])));
                caret.character = caret
                    .character
                    .saturating_add(u32::try_from(typed.len_utf16()).unwrap_or(u32::MAX));
                published
            })
            .collect()
    }

    /// Let the document's quiet interval pass, and return what that
    /// publishes.
    ///
    /// # Specification
    /// trivial.
    fn lapse(&mut self) -> Vec<Vec<Value>>
    {
        publications(&self.client.lapse(&DocumentUri::from(QUIET_URI)))
    }
}

#[test]
fn typing_a_declaration_holds_its_diagnostics_until_its_terminator()
{
    let at = |line: u32, character: u32| Position { line, character };
    let seed_lines = u32::try_from(QUIET_SEED.lines().count()).expect("the seed is short");
    let declared = u32::try_from(QUIET_DECLARATION.len()).expect("the declaration is short");

    // With a zero interval, each keystroke publishes what a fresh connection
    // opening the same text does: the unfinished declaration is red from its
    // first character to its last.
    let mut unheld = Typist::opened(Quiet::Unheld);
    let today = unheld.type_at(at(seed_lines, 0), Text(QUIET_DECLARATION));
    for (cut, publications) in QUIET_DECLARATION
        .char_indices()
        .map(|(offset, typed)| offset.saturating_add(typed.len_utf8()))
        .zip(&today)
    {
        let mut fresh = Client::initialized(Record::Dropped, Quiet::Default);
        let typed = QUIET_DECLARATION.get(.. cut).unwrap_or_default();
        let text = format!("{QUIET_SEED}{typed}");
        let opened = fresh.notify(
            Method("textDocument/didOpen"),
            &json!({ "textDocument": {
                "uri": QUIET_URI, "languageId": "gandr", "version": 1_i32, "text": text,
            } }),
        );
        assert_eq!(
            *publications,
            self::publications(&opened),
            "with a zero interval, typing `{text}` publishes what opening it does"
        );
    }
    let unfinished = |code: &str| vec![vec![json!([code, seed_lines])]];
    let mut expected = vec![unfinished("OutOfFragment"); 2];
    expected.extend(vec![
        unfinished("MalformedForm");
        QUIET_DECLARATION.len().saturating_sub(3)
    ]);
    expected.push(vec![Vec::new()]);
    assert_eq!(
        today, expected,
        "each keystroke of the declaration is red until its `;`"
    );

    // Under the interval, nothing of the declaration under the caret
    // publishes; the `;` that ends it leaves nothing held.
    let mut quiet = Typist::opened(Quiet::Default);
    assert_eq!(
        quiet.type_at(at(seed_lines, 0), Text(QUIET_DECLARATION)),
        vec![vec![Vec::<Value>::new()]; QUIET_DECLARATION.len()],
        "the declaration under the caret publishes nothing while it is typed"
    );
    assert_eq!(
        quiet.lapse(),
        Vec::<Vec<Value>>::new(),
        "and its `;` leaves nothing held"
    );

    // A declaration left unfinished is held while the caret is in it.
    let line = seed_lines.saturating_add(1);
    assert_eq!(
        quiet.type_at(at(seed_lines, declared), Text("\n")),
        [vec![Vec::<Value>::new()]],
        "a new line after the `;` publishes nothing"
    );
    assert_eq!(
        quiet.type_at(at(line, 0), Text("def four =")),
        vec![vec![Vec::<Value>::new()]; 10],
        "an unfinished declaration under the caret publishes nothing"
    );

    // An edit two declarations above `two` refuses it on that keystroke, and
    // the caret leaving the unfinished declaration publishes its refusal.
    // `three`, which names `two`, is noted as unsettled by that refusal.
    assert_eq!(
        quiet.replace(at(0, 7), at(0, 7), Text("s")),
        [vec![
            json!(["UnresolvedName", 2_i32]),
            json!(["UnknownConstant", seed_lines]),
            json!(["MalformedForm", line]),
        ]],
        "the refusal the edit causes below publishes at once, and the declaration the caret left publishes"
    );
    assert_eq!(
        quiet.replace(at(0, 7), at(0, 8), Text("")),
        [vec![json!(["MalformedForm", line])]],
        "undoing the edit clears its refusal"
    );

    // Back in the unfinished declaration, its refusal is held again until
    // the document is quiet for the interval.
    assert_eq!(
        quiet.type_at(at(line, 10), Text(" 4")),
        vec![vec![Vec::<Value>::new()]; 2],
        "typing in the unfinished declaration holds its refusal again"
    );
    assert_eq!(
        quiet.lapse(),
        [vec![json!(["MalformedForm", line])]],
        "the interval passing publishes the held refusal"
    );
    assert_eq!(
        quiet.lapse(),
        Vec::<Vec<Value>>::new(),
        "a released refusal is published once"
    );
    assert_eq!(
        quiet.type_at(at(line, 12), Text(" ;")),
        [vec![Vec::<Value>::new()], vec![Vec::new()]],
        "typing in the declaration again holds its refusal again, and the `;` clears it"
    );
    assert_eq!(
        quiet.lapse(),
        Vec::<Vec<Value>>::new(),
        "the finished declaration holds nothing"
    );
}

proptest! {
    #![proptest_config(Sweep::asked().scripts())]

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

    #[test]
    fn two_editors_on_one_buffer_each_keep_their_answers(
        seed in select(SEEDS.as_slice()),
        script in proptest::collection::vec(edit(), 1_usize .. 16_usize),
    ) {
        let mut first = Session::open_shared(
            String::from("file:///strict/shared.gandr"),
            Text(seed),
            Typing::Assisted,
            Oracle::Keystroke,
        );
        let mut second = first.beside(Typing::Assisted);
        for &step in &script {
            apply(&mut first, step);
            apply(&mut second, step);
            prop_assert_eq!(first.buffer().text(), second.buffer().text(), "one buffer, two clients");
        }
        first.replays_over_streams();
        second.replays_over_streams();
    }

    #[test]
    fn two_editors_on_their_own_buffers_each_keep_their_answers(
        seed in select(SEEDS.as_slice()),
        script in proptest::collection::vec((any::<bool>(), edit()), 1_usize .. 16_usize),
    ) {
        let mut first = Session::open_shared(
            String::from("file:///strict/diverged.gandr"),
            Text(seed),
            Typing::Assisted,
            Oracle::Keystroke,
        );
        let mut second = first.beside(Typing::Plain);
        for &(in_first, step) in &script {
            apply(if in_first { &mut first } else { &mut second }, step);
            first.verify();
            second.verify();
        }
        first.replays_over_streams();
        second.replays_over_streams();
    }
}
