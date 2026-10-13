//! A document open in an editor, synchronised one keystroke at a time and
//! held to what a fresh connection answers for the same text.
//!
//! The server answers each change before it reads the next message, so the
//! session runs in lockstep: every keystroke is followed by its publication,
//! and every assertion is made at the keystroke that broke it. The oracle is
//! external to the incremental path: a fresh connection opening the same text
//! whole. Whatever the server derives from the text alone — the diagnostics,
//! the semantic tokens, the outline, the folding, the selection ranges and the
//! inline completion — must agree between the two, so a text the server holds
//! differently from the editor, or an incremental answer that differs from a
//! whole one, fails where it diverged. A hover reads the session's latest
//! accepted revision, which a fresh connection does not have, so it is held
//! to answering, not to agreeing.
//!
//! Every keystroke checks its publication and asks for the inline completion
//! at the cursor. The oracle, the hover and the selection ranges — each of
//! which parses the whole document again — run at every keystroke under
//! [`Oracle::Keystroke`], and under [`Oracle::Line`] at every keystroke that
//! adds or removes a line, at the opening and at the end of a typing. The
//! corpus replay takes the line cadence: with specifications enforced, a
//! whole parse per keystroke across fifty thousand keystrokes costs minutes,
//! while the incremental path the line cadence still drives at every
//! keystroke is what the replay is for; the scripted and random sessions, on
//! short texts, keep the keystroke cadence.

use alloc::string::String;
use alloc::vec::Vec;

use anodized::spec;
use serde_json::Value;
use serde_json::json;

use super::buffer::Buffer;
use super::buffer::Change;
use super::buffer::Key;
use super::buffer::Offset;
use super::buffer::Text;
use super::buffer::Typing;
use super::client::Client;
use super::client::Method;
use super::client::Record;

/// The requests over the whole document whose answers depend on its text
/// alone.
const WHOLE: [Method; 3] = [
    Method("textDocument/semanticTokens/full"),
    Method("textDocument/documentSymbol"),
    Method("textDocument/foldingRange"),
];

/// When a session consults the oracle.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Oracle
{
    /// At every keystroke.
    Keystroke,
    /// At every keystroke that adds or removes a line, and when asked.
    Line,
}

/// A document open in an editor and its server, synchronised keystroke by
/// keystroke.
pub struct Session
{
    /// The document's URI.
    uri: String,
    /// The editor's buffer.
    buffer: Buffer,
    /// The connection.
    client: Client,
    /// When the oracle is consulted.
    oracle: Oracle,
    /// The version the latest synchronisation carried.
    version: i32,
    /// How many keystrokes have been checked.
    keystrokes: usize,
    /// The diagnostics last published.
    published: Value,
}

impl Session
{
    /// Open `text` at `uri` under `typing`, the cursor at its end, consulting
    /// the oracle at the cadence `oracle` names.
    ///
    /// # Specification
    /// - requires: `uri` is a `file` URI.
    /// - ensures: the document is open at version 1 and its publication was
    ///   held to the fresh connection's.
    /// - provides: a session ready for keystrokes.
    /// - panics: the opening publication is missing, or disagrees with a fresh
    ///   connection's.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every scenario opens here; the opening publication is
    ///   compared exactly as a keystroke's is.
    /// - witness: `editor::editor::scenarios::typing_each_corpus_source_keeps_every_answer_faithful`
    #[spec(requires: uri.starts_with("file://"),
        ensures: |ret| ret.version == 1_i32 && ret.buffer.text() == text && ret.uri.starts_with("file://"))]
    pub fn open(
        uri: String,
        text: Text<'_>,
        typing: Typing,
        oracle: Oracle,
    ) -> Self
    {
        let mut client = Client::initialized(Record::Kept);
        let opened = client.notify(
            Method("textDocument/didOpen"),
            &json!({ "textDocument": {
                "uri": uri, "languageId": "gandr", "version": 1_i32, "text": text.0,
            }}),
        );
        let mut session = Self {
            uri,
            buffer: Buffer::holding(text, typing),
            client,
            oracle,
            version: 1_i32,
            keystrokes: 0_usize,
            published: Value::Null,
        };
        session.published = session.publication(&opened);
        session.check(Oracle::Keystroke);
        session
    }

    /// Hold the current text to the oracle, whatever the session's cadence.
    ///
    /// # Specification
    /// trivial.
    pub fn verify(&mut self)
    {
        self.check(Oracle::Keystroke);
    }

    /// The editor's buffer.
    ///
    /// # Specification
    /// trivial.
    pub const fn buffer(&self) -> &Buffer
    {
        &self.buffer
    }

    /// The diagnostics last published.
    ///
    /// # Specification
    /// trivial.
    pub const fn published(&self) -> &Value
    {
        &self.published
    }

    /// The codes of the diagnostics last published, in order, each `null`
    /// when the diagnostic carries none.
    ///
    /// # Specification
    /// trivial.
    pub fn codes(&self) -> Vec<Value>
    {
        self.published
            .as_array()
            .map(|diagnostics| {
                diagnostics
                    .iter()
                    .map(|diagnostic| diagnostic.get("code").cloned().unwrap_or(Value::Null))
                    .collect()
            })
            .unwrap_or_default()
    }

    /// Type `typed`, one keystroke.
    ///
    /// # Specification
    /// trivial.
    pub fn type_char(
        &mut self,
        typed: Key,
    )
    {
        let changes = self.buffer.type_char(typed);
        self.keystroke(&changes);
    }

    /// Press Enter, one keystroke.
    ///
    /// # Specification
    /// trivial.
    pub fn enter(&mut self)
    {
        let change = self.buffer.enter();
        self.keystroke(&[change]);
    }

    /// Press backspace, one keystroke.
    ///
    /// # Specification
    /// trivial.
    pub fn backspace(&mut self)
    {
        let changes = self.buffer.backspace();
        self.keystroke(&changes);
    }

    /// Press delete, one keystroke.
    ///
    /// # Specification
    /// trivial.
    pub fn delete(&mut self)
    {
        let changes = self.buffer.delete();
        self.keystroke(&changes);
    }

    /// Replace `start .. end` with `text`, one keystroke.
    ///
    /// # Specification
    /// trivial.
    pub fn replace(
        &mut self,
        start: Offset,
        end: Offset,
        text: Text<'_>,
    )
    {
        let change = self.buffer.replace(start, end, text);
        self.keystroke(&[change]);
    }

    /// Undo the latest edit, one keystroke.
    ///
    /// # Specification
    /// trivial.
    pub fn undo(&mut self)
    {
        let changes = self.buffer.undo();
        self.keystroke(&changes);
    }

    /// Move the cursor to `at`, one keystroke that edits nothing.
    ///
    /// # Specification
    /// trivial.
    pub fn move_to(
        &mut self,
        at: Offset,
    )
    {
        self.buffer.move_to(at);
        self.keystroke(&[]);
    }

    /// Replay the session's whole exchange over framed streams.
    ///
    /// # Specification
    /// trivial.
    pub fn replays_over_streams(&self)
    {
        self.client.replays_over_streams();
    }

    /// Send `changes` as one synchronisation, then check the keystroke.
    ///
    /// # Specification
    /// - requires: `changes` are the edits the buffer just applied, in order,
    ///   each counted in the text before it.
    /// - ensures: with changes, the server published once for the new version
    ///   last; either way, the keystroke was checked, against the oracle when
    ///   the session's cadence or a change that adds or removes a line asks.
    /// - provides: one lockstep step.
    /// - panics: the publication is missing or stale, or a check fails.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every keystroke of every scenario passes here; a
    ///   server that skipped a publication, published a stale version or held a
    ///   different text fails at that keystroke.
    /// - witness: `editor::editor::scenarios::typing_each_corpus_source_keeps_every_answer_faithful`
    /// - witness: `editor::editor::scenarios::random_edits_keep_every_answer_faithful`
    #[spec(captures: [keystrokes = self.keystrokes, version = self.version],
        ensures: self.keystrokes == keystrokes.saturating_add(1)
            && self.version == if changes.is_empty() { version } else { version.saturating_add(1) })]
    fn keystroke(
        &mut self,
        changes: &[Change],
    )
    {
        self.keystrokes = self.keystrokes.saturating_add(1);
        if !changes.is_empty() {
            self.version = self.version.saturating_add(1);
            let messages = self.client.notify(
                Method("textDocument/didChange"),
                &json!({
                    "textDocument": { "uri": self.uri, "version": self.version },
                    "contentChanges": changes.iter().map(Change::json).collect::<Vec<_>>(),
                }),
            );
            self.published = self.publication(&messages);
        }
        let lines = changes
            .iter()
            .any(|change| change.start.line != change.end.line || change.text.contains('\n'));
        self.check(if lines {
            Oracle::Keystroke
        }
        else {
            self.oracle
        });
    }

    /// The diagnostics of the latest publication for the document among
    /// `messages`, at the session's version.
    ///
    /// # Specification
    /// trivial.
    fn publication(
        &self,
        messages: &[Value],
    ) -> Value
    {
        let publication = messages
            .iter()
            .rev()
            .find(|message| {
                message.get("method").and_then(Value::as_str)
                    == Some("textDocument/publishDiagnostics")
                    && message.pointer("/params/uri").and_then(Value::as_str)
                        == Some(self.uri.as_str())
            })
            .unwrap_or_else(|| panic!("a publication follows the synchronisation{}", self.scene()));
        assert_eq!(
            publication.pointer("/params/version"),
            Some(&json!(self.version)),
            "the publication carries the latest version{}",
            self.scene()
        );
        publication
            .pointer("/params/diagnostics")
            .cloned()
            .unwrap_or(Value::Null)
    }

    /// Check the current keystroke, against the oracle when `cadence` is
    /// [`Oracle::Keystroke`].
    ///
    /// # Specification
    /// - requires: the latest publication is in `published`.
    /// - ensures: the inline completion at the cursor answers without an error,
    ///   once. Against the oracle, the hover and selection ranges at the cursor
    ///   answer likewise, and the published diagnostics, the whole-document
    ///   answers and the inline completion and selection ranges at the cursor
    ///   equal a fresh connection's for the buffer's text.
    /// - provides: the per-keystroke invariants.
    /// - panics: a query is refused or answered twice, or an answer disagrees.
    /// - executable: none — the answers compared are the two connections'
    ///   replies, read and asserted inside the call; it returns nothing and
    ///   keeps no record of them.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the oracle is a fresh connection opening the text
    ///   whole, external to the incremental path; an incremental reparse, a
    ///   stale form or a text applied differently changes some text-derived
    ///   answer at the keystroke that caused it, or by the next line.
    /// - witness: `editor::editor::scenarios::typing_each_corpus_source_keeps_every_answer_faithful`
    /// - witness: `editor::editor::scenarios::random_edits_keep_every_answer_faithful`
    fn check(
        &mut self,
        cadence: Oracle,
    )
    {
        let document = json!({ "uri": self.uri });
        let at = json!({ "textDocument": document, "position": self.buffer.position().json() });
        let inline = json!({
            "textDocument": document,
            "position": self.buffer.position().json(),
            "context": { "triggerKind": 2_i32 },
        });
        let selection = json!({
            "textDocument": document,
            "positions": [self.buffer.position().json()],
        });
        let ghost = self
            .client
            .request(Method("textDocument/inlineCompletion"), &inline);
        if cadence == Oracle::Line {
            return;
        }
        let _hover = self.client.request(Method("textDocument/hover"), &at);
        let ranges = self
            .client
            .request(Method("textDocument/selectionRange"), &selection);
        let mut fresh = Client::initialized(Record::Dropped);
        let opened = fresh.notify(
            Method("textDocument/didOpen"),
            &json!({ "textDocument": {
                "uri": self.uri, "languageId": "gandr", "version": self.version,
                "text": self.buffer.text().0,
            }}),
        );
        let whole = opened
            .iter()
            .rev()
            .find_map(|message| message.pointer("/params/diagnostics"))
            .cloned()
            .unwrap_or(Value::Null);
        assert_eq!(
            self.published,
            whole,
            "the published diagnostics are a fresh connection's{}",
            self.scene()
        );
        for method in WHOLE {
            let params = json!({ "textDocument": document });
            assert_eq!(
                self.client.request(method, &params),
                fresh.request(method, &params),
                "{} answers as a fresh connection does{}",
                method.0,
                self.scene()
            );
        }
        assert_eq!(
            ghost,
            fresh.request(Method("textDocument/inlineCompletion"), &inline),
            "the inline completion is a fresh connection's{}",
            self.scene()
        );
        assert_eq!(
            ranges,
            fresh.request(Method("textDocument/selectionRange"), &selection),
            "the selection ranges are a fresh connection's{}",
            self.scene()
        );
    }

    /// Where the session stands, for a failure message.
    ///
    /// # Specification
    /// trivial.
    fn scene(&self) -> String
    {
        let text = self.buffer.text().0;
        let (before, after) = text.split_at(self.buffer.cursor().0);
        format!(
            "\n  at {} keystroke {} version {}\n  text: {before}⸢cursor⸣{after}",
            self.uri, self.keystrokes, self.version
        )
    }
}
