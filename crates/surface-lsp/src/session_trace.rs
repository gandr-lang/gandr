//! A session's trace: each message a connection reads and writes, and each
//! other thing its loop meets, one JSON object a line in the order the loop
//! meets them; and its replay, which meets each recorded thing again on a
//! fresh connection and holds every message that connection writes to the
//! one the trace recorded, so a report from an editor becomes a test.
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
//! [`replay`] runs each judgement and admission where it is submitted, so an
//! admission the traced session settled only after a later message settles
//! at the first `admitted` line after it was submitted, and the replay parts
//! there. It refuses an entry only the hub meets, since another connection's
//! edit is not in the trace. Its workspace spells types as the default does:
//! an editor's presentation settings travel in `initialize`, a user's
//! configured spelling does not. A `$/logTrace` is held to its message alone,
//! since its `verbose` part times the work.

use core::fmt;
use core::ops::ControlFlow;
use std::fs::File;
use std::io;
use std::io::BufRead;
use std::io::LineWriter;
use std::io::Write;
use std::path::PathBuf;

use anodized::spec;
use quenchant_shape::shape::Maybe;
use serde::Serialize;
use serde_json::Value;
use serde_json::json;

use crate::protocol::DocumentUri;
use crate::quiet::Deadlines;
use crate::quiet::Inbox;
use crate::quiet::Met;
use crate::rpc::Classified;
use crate::rpc::Incoming;
use crate::rpc::Malformed;
use crate::rpc::Outgoing;
use crate::rpc::classify;
use crate::server::Drive;
use crate::server::Workspace;
use crate::transport::Body;
use crate::transport::read_frame;

/// Where the `initialize` parameters name the file a trace is written to.
const OPTION: &str = "/initializationOptions/sessionTrace";

/// The method whose `verbose` part times the work it traces.
const LOG_TRACE: &str = "$/logTrace";

/// Where a connection's trace stands.
///
/// # Specification
/// - executable: none — the file is opaque; [`SessionTrace::met`] and
///   [`SessionTrace::wrote`] carry the clauses.
///
/// # Adequacy
/// - hypothesis: L3 — a session that asks for a trace writes one its replay
///   holds to every message, and one that asks for none writes nothing.
/// - witness: `tests::replay::a_session_asking_for_a_trace_writes_one_its_replay_holds`
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
    /// - witness: `tests::replay::a_session_asking_for_a_trace_writes_one_its_replay_holds`
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
    /// - witness: `tests::replay::a_session_asking_for_a_trace_writes_one_its_replay_holds`
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
pub struct TraceLine(usize);

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
/// - executable: none — a report; [`replay`] carries the clauses.
///
/// # Adequacy
/// - hypothesis: L3 — a trace whose answer was altered parts at its line.
/// - witness: `tests::replay::a_replay_parting_from_its_trace_names_the_line`
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
pub struct Replayed(usize);

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

/// One entry of a trace, read.
#[derive(Debug)]
enum Entry
{
    /// A message the loop met, at its place among those read, with how many
    /// were read behind it.
    Read
    {
        /// Its place among the messages read.
        at: usize,
        /// How many were read behind it.
        later: usize,
    },
    /// A message the server wrote.
    Wrote(Value),
    /// A document whose quiet interval lapsed.
    Quiet(DocumentUri),
    /// Judgements or admissions that ended.
    Admitted,
    /// The stream's end.
    Closed,
}

/// A trace's entries, each with its line, and the messages it read, in order.
struct Recorded
{
    /// Each entry, with its line.
    entries: Vec<(TraceLine, Entry)>,
    /// The messages read, each at the place its entry names.
    reads: Vec<Classified>,
}

/// Hold a fresh connection to `trace`, a session's recorded trace.
///
/// The connection serves the default workspace, its judgements and admissions
/// running on that workspace's serial pool; the replay meets each thing the
/// trace records, in order, and holds what the connection writes after each to
/// the `wrote` lines that follow it.
///
/// # Specification
/// - requires: nothing; the default workspace's pool runs each job where it is
///   submitted, so the replay settles where the trace did.
/// - ensures: `Ok` with the lines met when every message the replay wrote, in
///   order, is the one the trace's next `wrote` line holds, a `$/logTrace` held
///   to its message alone, and every `wrote` line was written; otherwise the
///   first line at which the replay parted, as [`Parted`] names. A replay
///   writes no trace of its own.
/// - provides: the oracle of a recorded session: the server it runs is the one
///   `serve` runs.
/// - fails: as [`Parted`] names.
/// - panics: resumes a judgement's or an admission's panic.
/// - executable: none — the replay's server is opaque; its writes are compared
///   inside the call.
///
/// # Errors
/// [`Divergence`], as above.
///
/// # Adequacy
/// - hypothesis: L3 — a recorded scene replays whole, an altered answer parts
///   at its line, and a session's own trace replays.
/// - witness: `tests::replay::a_recorded_scene_replays_against_a_fresh_server`
/// - witness: `tests::replay::a_replay_parting_from_its_trace_names_the_line`
/// - witness: `tests::replay::a_session_asking_for_a_trace_writes_one_its_replay_holds`
#[inline]
pub fn replay<Trace>(trace: Trace) -> Result<Replayed, Divergence>
where
    Trace: BufRead,
{
    let Recorded { entries, reads } = recorded(trace)?;
    let inbox = Inbox::default();
    let mut drive = Drive::new(Workspace::default(), inbox.changes(), SessionTrace::never());
    let mut deadlines = Deadlines::default();
    let mut ended = false;
    let mut at = 0_usize;
    let mut output = Vec::new();
    while let Some(&(line, ref entry)) = entries.get(at) {
        at = at.saturating_add(1);
        let met = match *entry {
            Entry::Wrote(ref recorded) => {
                return Err(Divergence {
                    line,
                    parted: Parted::Unwritten(recorded.clone()),
                });
            },
            _ if ended => {
                return Err(Divergence {
                    line,
                    parted: Parted::Ended,
                });
            },
            Entry::Read { at: read, later } => Met::Frame {
                message: reads.get(read).cloned().unwrap_or(Err(Malformed::Parse)),
                later: reads
                    .get(read.saturating_add(1) .. read.saturating_add(1).saturating_add(later))
                    .unwrap_or_default(),
            },
            Entry::Quiet(ref uri) => Met::Quiet(uri.clone()),
            Entry::Admitted => Met::Admitted,
            Entry::Closed => Met::Closed,
        };
        output.clear();
        let flow = drive
            .met(met, &mut deadlines, (&mut output, &mut io::sink()))
            .map_err(|fault| Divergence {
                line,
                parted: Parted::Fault(fault),
            })?;
        ended = matches!(flow, ControlFlow::Break(_));
        let mut written = output.as_slice();
        while let Ok(Maybe::Present(body)) = read_frame(&mut written) {
            let replayed = serde_json::from_slice::<Value>(body.as_ref()).unwrap_or(Value::Null);
            let Some(&(recorded_line, Entry::Wrote(ref recorded))) = entries.get(at)
            else {
                return Err(Divergence {
                    line: entries.get(at).map_or(line, |&(next, _)| next),
                    parted: Parted::Unrecorded(replayed),
                });
            };
            at = at.saturating_add(1);
            if comparable(&replayed) != comparable(recorded) {
                return Err(Divergence {
                    line: recorded_line,
                    parted: Parted::Wrote {
                        replayed,
                        recorded: recorded.clone(),
                    },
                });
            }
        }
    }
    Ok(Replayed(entries.len()))
}

/// `message` as a replay compares it: a `$/logTrace` without the `verbose`
/// part that times the work.
///
/// # Specification
/// trivial.
fn comparable(message: &Value) -> Value
{
    let mut held = message.clone();
    if held.get("method").and_then(Value::as_str) == Some(LOG_TRACE)
        && let Some(&mut Value::Object(ref mut params)) = held.get_mut("params")
    {
        let _timed = params.remove("verbose");
    }
    held
}

/// Every entry of `trace`, each with its line, and the messages read, in
/// order.
///
/// # Specification
/// trivial.
fn recorded<Trace>(trace: Trace) -> Result<Recorded, Divergence>
where
    Trace: BufRead,
{
    let mut entries = Vec::new();
    let mut reads = Vec::new();
    for (index, text) in trace.lines().enumerate() {
        let line = TraceLine(index.saturating_add(1));
        let text = text.map_err(|error| Divergence {
            line,
            parted: Parted::Unread(error),
        })?;
        let unreadable = || Divergence {
            line,
            parted: Parted::Unreadable,
        };
        let Ok(Value::Object(object)) = serde_json::from_str::<Value>(&text)
        else {
            return Err(unreadable());
        };
        let later = object
            .get("later")
            .and_then(Value::as_u64)
            .and_then(|later| usize::try_from(later).ok())
            .unwrap_or(0_usize);
        let entry = if let Some(read) = object.get("read") {
            reads.push(classify(&Body::from(read.to_string().into_bytes())));
            Entry::Read {
                at: reads.len().saturating_sub(1),
                later,
            }
        }
        else if object.contains_key("unparsed") {
            reads.push(Err(Malformed::Parse));
            Entry::Read {
                at: reads.len().saturating_sub(1),
                later,
            }
        }
        else if let Some(wrote) = object.get("wrote") {
            Entry::Wrote(wrote.clone())
        }
        else if let Some(uri) = object.get("quiet").and_then(Value::as_str) {
            Entry::Quiet(DocumentUri::from(uri))
        }
        else if object.contains_key("admitted") {
            Entry::Admitted
        }
        else if object.contains_key("closed") {
            Entry::Closed
        }
        else if ["changed", "edited", "proposed"]
            .iter()
            .any(|key| object.contains_key(*key))
        {
            return Err(Divergence {
                line,
                parted: Parted::Unreplayable,
            });
        }
        else {
            return Err(unreadable());
        };
        entries.push((line, entry));
    }
    Ok(Recorded { entries, reads })
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
