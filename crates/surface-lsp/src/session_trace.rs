//! The replay of a session's trace, which meets each recorded thing again on
//! a fresh connection and holds every message that connection writes to the
//! one the trace recorded, so a report from an editor becomes a test.
//!
//! The trace itself, its lines and the result of a replay are in
//! `gandr-surface-lsp-base`.
//!
//! [`replay`] runs each judgement and admission where it is submitted, so an
//! admission the traced session settled only after a later message settles
//! at the first `admitted` line after it was submitted, and the replay parts
//! there. It refuses an entry only the hub meets, since another connection's
//! edit is not in the trace. Its workspace spells types as the default does:
//! an editor's presentation settings travel in `initialize`, a user's
//! configured spelling does not. A `$/logTrace` is held to its message alone,
//! since its `verbose` part times the work.

use core::ops::ControlFlow;
use std::io;
use std::io::BufRead;

use gandr_surface_lsp_base::quiet::Met;
use gandr_surface_lsp_base::session_trace::Divergence;
use gandr_surface_lsp_base::session_trace::Parted;
use gandr_surface_lsp_base::session_trace::Replayed;
use gandr_surface_lsp_base::session_trace::SessionTrace;
use gandr_surface_lsp_base::session_trace::TraceLine;
use quenchant_shape::shape::Maybe;
use serde_json::Value;

use crate::inbox::Inbox;
use crate::protocol::DocumentUri;
use crate::quiet::Deadlines;
use crate::rpc::Classified;
use crate::rpc::Malformed;
use crate::rpc::classify;
use crate::server::Drive;
use crate::server::Workspace;
use crate::transport::Body;
use crate::transport::read_frame;

/// The method whose `verbose` part times the work it traces.
const LOG_TRACE: &str = "$/logTrace";

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
