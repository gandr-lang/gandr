//! A session's trace: each message a connection reads and writes, and each
//! other thing its loop meets.
//!
//! The trace holds one JSON object a line, in the order the loop meets them.
//! Its replay meets each recorded thing again on a fresh connection and holds
//! every message that connection writes to the one the trace recorded, so a
//! report from an editor becomes a test.
//!
//! A client asks for a trace at `initialize`, naming a file in its
//! `initializationOptions.sessionTrace`; a relative name resolves against the
//! server's working directory, the hub's under `gandr lsp`. The server
//! creates or empties the file and writes each line as the loop meets its
//! thing, so a session that breaks leaves its trace up to the break. A line
//! holds one entry: `read`, a message as the server classified it, with
//! `later` counting the messages already read behind it, which can withdraw
//! it; `unparsed`, a body that is not JSON; `wrote`, a message the server
//! wrote; `quiet`, the URI of a document whose quiet interval lapsed;
//! `admitted`, judgements or admissions that ended; `changed`, `edited` and
//! `proposed`, which only the hub meets; and `closed`, the stream's end. A
//! change names its document's version in its own parameters, so the trace
//! names the version of every text the server judged.
//!
//! The replay, which runs a fresh server, stays in `gandr-surface-lsp`.

use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;
use std::fs::File;
use std::io;
use std::io::LineWriter;
use std::io::Write;
use std::path::PathBuf;

use anodized::spec;
use serde::Serialize;
use serde_json::Value;
use serde_json::json;

use crate::quiet::Met;
use crate::rpc::Classified;
use crate::rpc::Incoming;
use crate::rpc::Malformed;
use crate::rpc::Outgoing;
use crate::rpc::classify;
use crate::transport::Body;

/// Where the `initialize` parameters name the file a trace is written to.
const OPTION: &str = "/initializationOptions/sessionTrace";

/// Where a connection's trace stands.
///
/// # Specification
/// - executable: none — the file is opaque; [`SessionTrace::met`] and
///   [`SessionTrace::wrote`] carry the clauses.
///
/// # Adequacy
/// - hypothesis: L3 — a session that asks for a trace writes one its replay
///   holds to every message, and one that asks for none writes nothing.
/// - witness: `gandr-surface-lsp::tests::replay::a_session_asking_for_a_trace_writes_one_its_replay_holds`
#[repr(transparent)]
#[derive(Debug)]
pub struct SessionTrace(State);

/// The states of a trace.
#[derive(Debug)]
enum State
{
    /// Before `initialize`: the client may still ask for one.
    Awaiting,
    /// Written to its file.
    Writing(Writing),
    /// The file refused a line, which the loop has not logged yet.
    Failed(Unwritten),
    /// None: the client asked for none, its file was refused, or the session
    /// is a replay.
    Off,
}

/// A trace's file.
#[derive(Debug)]
struct Writing
{
    /// The file, as the client named it.
    path: PathBuf,
    /// The file, written a line at a time.
    file: LineWriter<File>,
}

/// A trace the server stopped writing: its file, and why.
#[derive(Debug)]
pub struct Unwritten
{
    /// The file, as the client named it.
    path: PathBuf,
    /// Why it was not written.
    error: io::Error,
}

impl fmt::Display for Unwritten
{
    /// Name the file and why it was not written.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(
            f,
            "gandr: the session trace {} is not written: {}",
            self.path.display(),
            self.error
        )
    }
}

/// One line the trace writes for a message the server wrote.
#[repr(transparent)]
#[derive(Serialize)]
struct Wrote<'message>
{
    /// The message.
    wrote: &'message Outgoing,
}

impl SessionTrace
{
    /// A trace the client may ask for at `initialize`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn asked() -> Self
    {
        Self(State::Awaiting)
    }

    /// No trace, whatever the client asks: a replay's.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn never() -> Self
    {
        Self(State::Off)
    }

    /// Note what the loop met, opening the trace first when `met` is the
    /// `initialize` naming its file; a file refused is said on `log`.
    ///
    /// # Specification
    /// - requires: `met` is what the loop meets next, before it handles it.
    /// - ensures: a trace still awaiting its client, met by an `initialize`
    ///   whose options name a file, writes to that file, created or emptied,
    ///   and by any other `initialize` writes nothing from then on; a trace
    ///   writing appends `met`'s line. A file that refuses its creation or a
    ///   line, now or at an earlier [`SessionTrace::wrote`], is said on `log`
    ///   once and written no more.
    /// - provides: every line but `wrote`, in the order the loop meets them.
    /// - fails: never; a refused file is said and dropped, and the session goes
    ///   on.
    /// - panics: none.
    /// - executable: none — the file and the log are opaque.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a traced session's file replays whole from its
    ///   `initialize` on.
    /// - witness: `gandr-surface-lsp::tests::replay::a_session_asking_for_a_trace_writes_one_its_replay_holds`
    #[inline]
    pub fn met<Log>(
        &mut self,
        met: &Met<'_>,
        log: &mut Log,
    ) where
        Log: Write,
    {
        if matches!(self.0, State::Awaiting)
            && let Met::Frame {
                message:
                    Ok(Incoming::Request {
                        ref method,
                        ref params,
                        ..
                    }),
                ..
            } = *met
            && method.as_ref() == "initialize"
        {
            self.0 = params
                .pointer(OPTION)
                .and_then(Value::as_str)
                .map_or(State::Off, |path| opened(PathBuf::from(path)));
        }
        if let State::Writing(ref mut writing) = self.0
            && let Err(error) = written(&mut writing.file, &line(met))
        {
            self.fail(error);
        }
        if let State::Failed(_) = self.0
            && let State::Failed(unwritten) = core::mem::replace(&mut self.0, State::Off)
        {
            let _unlogged = writeln!(log, "{unwritten}");
        }
    }

    /// Note `message`, which the server wrote.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a trace writing appends `{"wrote": message}`; a line its file
    ///   refuses leaves the trace failed, to be said at the next
    ///   [`SessionTrace::met`].
    /// - provides: the `wrote` lines, each after the line of what the loop met
    ///   that wrote it.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the file is opaque.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`SessionTrace::met`].
    /// - witness: `gandr-surface-lsp::tests::replay::a_session_asking_for_a_trace_writes_one_its_replay_holds`
    #[inline]
    pub fn wrote(
        &mut self,
        message: &Outgoing,
    )
    {
        if let State::Writing(ref mut writing) = self.0
            && let Err(error) = written(&mut writing.file, &Wrote { wrote: message })
        {
            self.fail(error);
        }
    }

    /// Stop writing after `error`, keeping it to be said.
    ///
    /// # Specification
    /// trivial.
    fn fail(
        &mut self,
        error: io::Error,
    )
    {
        if let State::Writing(Writing { path, .. }) = core::mem::replace(&mut self.0, State::Off) {
            self.0 = State::Failed(Unwritten { path, error });
        }
    }
}

/// A trace writing to the file at `path`, created or emptied, or failed with
/// the reason the file could not be.
///
/// # Specification
/// trivial.
fn opened(path: PathBuf) -> State
{
    match File::create(&path) {
        Ok(file) => State::Writing(Writing {
            path,
            file: LineWriter::new(file),
        }),
        Err(error) => State::Failed(Unwritten { path, error }),
    }
}

/// Write `entry` to `file` as one line.
///
/// # Specification
/// trivial.
fn written<Entry>(
    file: &mut LineWriter<File>,
    entry: &Entry,
) -> io::Result<()>
where
    Entry: Serialize,
{
    let mut line = serde_json::to_vec(entry).map_err(io::Error::other)?;
    line.push(b'\n');
    file.write_all(&line)
}

/// The line that records `met`.
///
/// # Specification
/// trivial.
fn line(met: &Met<'_>) -> Value
{
    match *met {
        Met::Frame {
            message: Err(Malformed::Parse),
            ..
        } => json!({ "unparsed": null }),
        Met::Frame {
            ref message,
            later: &[],
        } => {
            json!({ "read": spelled(message) })
        },
        Met::Frame { ref message, later } => {
            json!({ "read": spelled(message), "later": later.len() })
        },
        Met::Quiet(ref uri) => json!({ "quiet": uri }),
        Met::Changed(ref paths) => json!({ "changed": lossy(paths) }),
        Met::Edited(ref paths) => json!({ "edited": lossy(paths) }),
        Met::Proposed => json!({ "proposed": null }),
        Met::Admitted => json!({ "admitted": null }),
        Met::Traced => json!({ "traced": null }),
        Met::Closed => json!({ "closed": null }),
    }
}

/// Each of `paths` as text, a byte that is not UTF-8 replaced.
///
/// # Specification
/// trivial.
fn lossy(paths: &[PathBuf]) -> Vec<String>
{
    paths
        .iter()
        .map(|path| path.to_string_lossy().into_owned())
        .collect()
}

/// `message` as a body that [`classify`] reads back as `message`: an
/// envelope for a request, notification or response, and an invalid
/// message's identifier alone, which names no version.
///
/// # Specification
/// - requires: `message` is not [`Malformed::Parse`], which no JSON body is.
/// - ensures: [`classify`] of the value's text is `message`.
/// - provides: the `read` entry, which the replay classifies again.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — each kind of message read back as itself.
/// - witness: `session_trace::tests::a_read_entry_classifies_back_as_its_message`
#[spec(ensures: |ret| matches!(*message, Err(Malformed::Parse))
    || classify(&Body::from(ret.to_string().into_bytes())) == *message)]
fn spelled(message: &Classified) -> Value
{
    match *message {
        Ok(Incoming::Request {
            ref id,
            ref method,
            ref params,
        }) => {
            let mut spelled = json!({ "jsonrpc": "2.0", "id": id, "method": method.as_ref() });
            if !params.is_null()
                && let Value::Object(ref mut envelope) = spelled
            {
                let _unheld = envelope.insert("params".to_owned(), params.clone());
            }
            spelled
        },
        Ok(Incoming::Notification {
            ref method,
            ref params,
        }) => {
            let mut spelled = json!({ "jsonrpc": "2.0", "method": method.as_ref() });
            if !params.is_null()
                && let Value::Object(ref mut envelope) = spelled
            {
                let _unheld = envelope.insert("params".to_owned(), params.clone());
            }
            spelled
        },
        Ok(Incoming::Response {
            ref id,
            result: Some(ref result),
        }) => json!({ "jsonrpc": "2.0", "id": id, "result": result }),
        Ok(Incoming::Response {
            ref id,
            result: None,
        }) => {
            json!({ "jsonrpc": "2.0", "id": id, "error": null })
        },
        Err(Malformed::Invalid(ref id)) => json!({ "id": id }),
        Err(Malformed::Parse) => Value::Null,
    }
}

/// A line of a trace, counted from one.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct TraceLine(pub usize);

impl From<TraceLine> for usize
{
    /// The line's number, counted from one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(line: TraceLine) -> Self
    {
        line.0
    }
}

impl fmt::Display for TraceLine
{
    /// The line's number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "{}", self.0)
    }
}

/// Where a replay first parted from its trace, and how.
///
/// # Specification
/// - executable: none — a report; the replay of `gandr-surface-lsp` carries the
///   clauses.
///
/// # Adequacy
/// - hypothesis: L3 — a trace whose answer was altered parts at its line.
/// - witness: `gandr-surface-lsp::tests::replay::a_replay_parting_from_its_trace_names_the_line`
#[derive(Debug)]
pub struct Divergence
{
    /// The line it parted at.
    pub line: TraceLine,
    /// How.
    pub parted: Parted,
}

/// How a replay parted from its trace.
#[derive(Debug)]
pub enum Parted
{
    /// The trace could not be read there.
    Unread(io::Error),
    /// The line is no entry of a trace.
    Unreadable,
    /// The line records what only the hub meets, which another connection
    /// caused.
    Unreplayable,
    /// The replay wrote a message where the trace holds another.
    Wrote
    {
        /// What the replay wrote.
        replayed: Value,
        /// What the trace holds.
        recorded: Value,
    },
    /// The replay wrote nothing more where the trace holds a message.
    Unwritten(Value),
    /// The replay wrote a message where the trace holds none.
    Unrecorded(Value),
    /// The session had ended before the line.
    Ended,
    /// The replay could not encode a message.
    Fault(crate::transport::TransportFault),
}

impl fmt::Display for Divergence
{
    /// Name the line and how the replay parted there.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let line = self.line;
        match self.parted {
            Parted::Unread(ref error) => write!(f, "line {line}: unread: {error}"),
            Parted::Unreadable => write!(f, "line {line}: no entry of a trace"),
            Parted::Unreplayable => write!(
                f,
                "line {line}: what another connection caused, which no replay meets"
            ),
            Parted::Wrote {
                ref replayed,
                ref recorded,
            } => write!(
                f,
                "line {line}: the replay wrote {replayed} where the trace wrote {recorded}"
            ),
            Parted::Unwritten(ref recorded) => write!(
                f,
                "line {line}: the replay wrote nothing where the trace wrote {recorded}"
            ),
            Parted::Unrecorded(ref replayed) => write!(
                f,
                "line {line}: the replay wrote {replayed} where the trace wrote nothing"
            ),
            Parted::Ended => write!(f, "line {line}: the session had ended"),
            Parted::Fault(ref fault) => write!(f, "line {line}: {fault}"),
        }
    }
}

/// How much of a trace a replay met.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Replayed(pub usize);

impl From<Replayed> for usize
{
    /// The number of lines replayed.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(replayed: Replayed) -> Self
    {
        replayed.0
    }
}

#[cfg(test)]
mod tests
{
    use serde_json::json;

    use super::spelled;
    use crate::rpc::Malformed;
    use crate::rpc::classify;
    use crate::transport::Body;

    /// Every kind of message the loop reads is spelled as a body that
    /// classifies back as it: a request and a notification with and without
    /// parameters, a response with a result and with an error, and an invalid
    /// message with and without an identifier.
    #[test]
    fn a_read_entry_classifies_back_as_its_message()
    {
        for body in [
            r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"capabilities":{}}}"#,
            r#"{"jsonrpc":"2.0","id":"s","method":"shutdown"}"#,
            r#"{"jsonrpc":"2.0","method":"exit"}"#,
            r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///a.gandr","version":3},"contentChanges":[]}}"#,
            r#"{"jsonrpc":"2.0","id":4,"result":[1,2]}"#,
            r#"{"jsonrpc":"2.0","id":5,"error":{"code":-32601,"message":"no"}}"#,
            r#"{"jsonrpc":"1.0","id":6,"method":"m"}"#,
            r#"[1]"#,
        ] {
            let message = classify(&Body::from(body.as_bytes().to_vec()));
            assert!(!matches!(message, Err(Malformed::Parse)), "{body} is JSON");
            let read = spelled(&message);
            assert_eq!(
                classify(&Body::from(read.to_string().into_bytes())),
                message,
                "{body} reads back from {read}"
            );
        }
        assert_eq!(
            spelled(&classify(&Body::from(b"{}".to_vec()))),
            json!({ "id": null }),
            "an invalid message with no identifier is spelled by its unread one"
        );
    }
}
