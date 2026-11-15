//! The parts of the engine hub that read neither the dispatcher nor the
//! session.
//!
//! These parts are the relay, which carries an editor's frames to the hub's
//! socket, the workspace's name, the listener's bind, and the hub's linger.
//!
//! The hub itself, its connections and the socket each build names stay in
//! `gandr-surface-lsp`, whose `hub` module states the design.

use alloc::sync::Arc;
use core::sync::atomic::AtomicUsize;
use core::sync::atomic::Ordering;
use core::time::Duration;
use std::fs::DirBuilder;
use std::io;
use std::io::BufReader;
use std::io::Read;
use std::io::Write;
use std::os::unix::fs::DirBuilderExt as _;
use std::os::unix::net::UnixListener;
use std::os::unix::net::UnixStream;
use std::path::Path;
use std::sync::Mutex;
use std::sync::MutexGuard;
use std::sync::PoisonError;
use std::sync::mpsc::channel;
use std::thread;

use anodized::spec;
use quenchant_shape::shape::Maybe;
use serde_json::Value;

use crate::handover::Carried;
use crate::handover::Handover;
use crate::handover::REPLAY;
use crate::protocol::Served;
use crate::rpc::Incoming;
use crate::rpc::classify;
use crate::transport::Body;
use crate::transport::TransportFault;
use crate::transport::read_frame;
use crate::transport::write_frame;

/// How long a hub with no connection waits for one before it exits, unless
/// its caller names another.
///
/// economy: one minute. An editor restarted within it finds its documents'
/// sessions still warm; a hub nobody returns to gives its memory back soon
/// after.
pub const LINGER: Duration = Duration::from_secs(60);

/// The hex digits of the build and workspace digest a socket is named by.
///
/// economy: 16 digits, 64 bits. Collisions between one user's workspaces and
/// builds are out of reach, and the name keeps a socket path under the 104
/// bytes the smallest platform limit allows, inside a long per-user temporary
/// directory.
pub const NAME_DIGITS: usize = 16;

quenchant_shape::reason_enum! {
    /// Why no listener was bound.
    pub mod bind {
        /// The reason the hub does not listen.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// Another hub already listens on the socket.
            Served,
        }
    }
}

/// Lock `mutex`, taking its state as it is when a holder panicked.
///
/// # Specification
/// trivial.
#[inline]
pub fn lock<Held>(mutex: &Mutex<Held>) -> MutexGuard<'_, Held>
{
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

/// The name of the workspace rooted at `root`, the same for every build.
///
/// # Specification
/// - requires: nothing; `root` is resolved through the file system.
/// - ensures: the first sixteen hex digits of the BLAKE3 hash of the canonical
///   root. Every spelling of one directory names one workspace, and the build
///   does not change the name.
/// - provides: the key of what a hub keeps for its workspace across builds: the
///   calls its toolset acknowledged and did not answer.
/// - fails: when `root` cannot be canonicalised.
/// - panics: none.
///
/// # Errors
/// The error canonicalising `root`.
///
/// # Adequacy
/// - hypothesis: L3 — a directory named directly and through a `..` detour
///   names one workspace; a sibling directory names another.
/// - witness: `gandr-surface-lsp::hub::tests::a_workspace_names_one_socket`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |name| name.len() == NAME_DIGITS))]
#[inline]
pub fn workspace_name(root: &Path) -> io::Result<String>
{
    let root = std::fs::canonicalize(root)?;
    Ok(blake3::hash(root.as_os_str().as_encoded_bytes())
        .to_hex()
        .chars()
        .take(NAME_DIGITS)
        .collect())
}

/// Listen on `socket`, unless another hub already does.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the socket's directory exists, created readable by its owner
///   alone when this call made it. A socket a listener accepts on is
///   [`bind::Absent::Served`] and left alone, whichever process holds that
///   listener. A socket file nothing accepts on is stale, removed and bound
///   afresh.
/// - provides: the one hub per socket a client's start relies on.
/// - fails: when the directory cannot be made or the socket bound.
/// - panics: none.
///
/// # Errors
/// The error creating the directory, removing a stale socket or binding.
///
/// # Adequacy
/// - hypothesis: L3 — binding a live hub's socket answers Served; binding a
///   socket whose listener a child process still holds answers Served; binding
///   a socket file nothing accepts on succeeds.
/// - witness: `gandr-surface-lsp::hub::tests::a_socket_has_one_hub`
/// - witness: `gandr-surface-lsp::hub::tests::a_listener_a_child_holds_is_served_5332`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |bound|
    !matches!(*bound, Maybe::Present(_)) || socket.exists()))]
#[inline]
pub fn bind(socket: &Path) -> Result<Maybe<UnixListener, bind::Absent>, io::Error>
{
    if let Some(directory) = socket.parent() {
        DirBuilder::new()
            .recursive(true)
            .mode(0o700)
            .create(directory)?;
    }
    match UnixListener::bind(socket) {
        Ok(listener) => Ok(Maybe::Present(listener)),
        Err(error) if error.kind() == io::ErrorKind::AddrInUse => {
            if UnixStream::connect(socket).is_ok() {
                return Ok(Maybe::Absent(bind::Absent::Served));
            }
            std::fs::remove_file(socket)?;
            UnixListener::bind(socket).map(Maybe::Present)
        },
        Err(error) => Err(error),
    }
}

/// How a relayed session ended.
#[derive(Debug, Eq, PartialEq)]
pub enum Relayed
{
    /// The session ended, as the client's frames decide.
    Ended(Served),
    /// The selection moved to another build: the session goes on in that
    /// build's image, which takes the handover.
    Switched(Handover),
}

/// What a relay's input thread tells the thread reading the hub.
enum Ending
{
    /// The input ended, faulted or carried `exit`: the session's verdict.
    Served(Result<Served, TransportFault>),
    /// The input thread asked the hub for the replay: the client's bytes it
    /// read and did not forward, the frame it held back first.
    Switching(Vec<u8>),
}

/// How a frame from the hub reads to a relay.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Answered
{
    /// A response under the identifier [`REPLAY`].
    Replay,
    /// A response under another identifier.
    Other,
    /// A request or a notification, or no message.
    Unanswered,
}

/// The envelope of a message from the hub, its payload skipped unread.
#[derive(serde::Deserialize)]
struct Envelope
{
    /// The identifier, when the message carries one.
    #[serde(default)]
    id: Option<Value>,
    /// The method, when the message calls one.
    #[serde(default)]
    method: Option<serde::de::IgnoredAny>,
}

/// Whether the frame `body` from the hub answers a request, and which.
///
/// # Specification
/// - requires: nothing.
/// - ensures: [`Answered::Replay`] for a message carrying the identifier
///   [`REPLAY`] and no method, [`Answered::Other`] for any other identifier and
///   no method, [`Answered::Unanswered`] otherwise.
/// - panics: none.
/// - executable: none — a predicate would read the body's envelope a second
///   time, which is the whole of the function.
///
/// # Adequacy
/// - hypothesis: L3 — a response to a request held before a switch is counted,
///   and the replay's answer is told apart.
/// - witness: `gandr-surface-lsp::hub::tests::a_relay_switches_once_nothing_is_pending`
fn answered(body: &Body) -> Answered
{
    match serde_json::from_slice::<Envelope>(body.as_ref()) {
        Ok(Envelope {
            id: Some(id),
            method: None,
        }) if id.as_str() == Some(REPLAY) => Answered::Replay,
        Ok(Envelope {
            id: Some(_),
            method: None,
        }) => Answered::Other,
        Ok(_) | Err(_) => Answered::Unanswered,
    }
}

/// The replay the hub's answer `body` to [`REPLAY`] carries, one body per
/// message.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the answer's `result` array, each message encoded again.
/// - fails: when the answer carries no array of messages.
/// - panics: none.
/// - executable: none — a predicate would parse the answer a second time to
///   compare its messages, which is the whole of the function.
///
/// # Errors
/// [`TransportFault::Io`] of kind `InvalidData` when the answer carries no
/// array.
///
/// # Adequacy
/// - hypothesis: L3 — as [`relay`]'s switch.
/// - witness: `gandr-surface-lsp::hub::tests::a_relay_switches_once_nothing_is_pending`
fn replayed(body: &Body) -> Result<Vec<Body>, TransportFault>
{
    /// The answer to [`REPLAY`].
    #[repr(transparent)]
    #[derive(serde::Deserialize)]
    struct Answer
    {
        /// The replay's messages.
        result: Vec<Value>,
    }
    let answer: Answer = serde_json::from_slice(body.as_ref())
        .map_err(|error| TransportFault::Io(io::Error::new(io::ErrorKind::InvalidData, error)))?;
    answer
        .result
        .iter()
        .map(|message| serde_json::to_vec(message).map(Body::from))
        .collect::<Result<Vec<Body>, serde_json::Error>>()
        .map_err(TransportFault::Encode)
}

/// Carry frames between a client and the hub at the other end of `hub`,
/// until the hub closes the connection or the session moves to another build.
///
/// `opening` goes to the hub first. Then each frame `input` holds goes to the
/// hub, and each frame the hub sends goes to `output`, until the hub closes or
/// `moved` answers that the session belongs to another build.
///
/// # Specification
/// - requires: nothing.
/// - ensures: frames pass unchanged and in order both ways, but for the hub's
///   answers to the requests in `opening`, which are dropped. Once `input`
///   ends, faults or carries `exit`, the hub's end is shut for writing. The
///   session is [`Served::Clean`] when `input` carried a `shutdown` request
///   before `exit`, the fault when `input` broke inside a frame, and
///   [`Served::Abrupt`] otherwise. `moved` is asked before each frame from
///   `input` while none of the client's requests waits for its answer; once it
///   answers `true`, that frame and every byte read past it are held, the hub
///   is asked for [`REPLAY`], and the session ends [`Relayed::Switched`] with
///   the hub's replay and the held bytes.
/// - provides: a client's whole session with a hub, across builds.
/// - fails: when `input` breaks, a frame from the hub cannot be read or written
///   to `output`, or the hub's replay is no array of messages.
/// - panics: none.
/// - executable: none — the frames go to a socket and to `output`, which the
///   call consumes or writes but cannot read back.
///
/// # Errors
/// [`TransportFault`] reading `input` or the hub's frames, writing to
/// `output`, or reading the replay.
///
/// # Adequacy
/// - hypothesis: L3 — a session of initialize, shutdown and exit is carried
///   whole and ends clean; one closed before shutdown ends abrupt; a truncated
///   frame is a fault; a switch waits for the client's pending request and
///   hands over the frame it held with the hub's replay.
/// - witness: `gandr-surface-lsp::hub::tests::a_relay_carries_a_session_and_its_ending`
/// - witness: `gandr-surface-lsp::hub::tests::a_relay_switches_once_nothing_is_pending`
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        pool_only_threads,
        reason = "io: the relay's input thread blocks on the editor's frames for the session's life"
    )
)]
#[inline]
pub fn relay<Input, Output, Moved>(
    input: Input,
    output: &mut Output,
    hub: UnixStream,
    opening: &[Body],
    mut moved: Moved,
) -> Result<Relayed, TransportFault>
where
    Input: Read + Send + 'static,
    Output: Write,
    Moved: FnMut() -> bool + Send + 'static,
{
    let mut forward = hub.try_clone().map_err(TransportFault::Io)?;
    let mut replayed_requests = 0_usize;
    for body in opening {
        if let Ok(Incoming::Request { .. }) = classify(body) {
            replayed_requests = replayed_requests.saturating_add(1);
        }
        write_frame(&mut forward, body)?;
    }
    let pending = Arc::new(AtomicUsize::new(replayed_requests));
    let waiting = Arc::clone(&pending);
    let (verdict, verdicts) = channel();
    drop(thread::spawn(move || {
        let mut input = BufReader::new(input);
        let mut shut = false;
        let served = loop {
            let body = match read_frame(&mut input) {
                Ok(Maybe::Present(body)) => body,
                Ok(Maybe::Absent(_closed)) => break Ok(Served::Abrupt),
                Err(fault) => break Err(fault),
            };
            let (exit, request) = match classify(&body) {
                Ok(Incoming::Request { ref method, .. }) => {
                    shut |= method.as_ref() == "shutdown";
                    (false, true)
                },
                Ok(Incoming::Notification { ref method, .. }) => (method.as_ref() == "exit", false),
                Ok(Incoming::Response { .. }) | Err(_) => (false, false),
            };
            if exit {
                // The verdict is sent before the hub can read `exit`, so it
                // is waiting when the hub's end closes.
                drop(verdict.send(Ending::Served(Ok(if shut {
                    Served::Clean
                }
                else {
                    Served::Abrupt
                }))));
                drop(write_frame(&mut forward, &body));
                break Ok(Served::Abrupt);
            }
            if waiting.load(Ordering::Acquire) == 0 && moved() {
                let mut carried = Vec::new();
                if let Err(fault) = write_frame(&mut carried, &body) {
                    break Err(fault);
                }
                carried.extend_from_slice(input.buffer());
                // The held bytes are waiting before the hub can answer the
                // replay, so the reader finds them with the answer.
                drop(verdict.send(Ending::Switching(carried)));
                let asked = format!(r#"{{"jsonrpc":"2.0","id":"{REPLAY}","method":"{REPLAY}"}}"#);
                drop(write_frame(&mut forward, &Body::from(asked.into_bytes())));
                return;
            }
            if request {
                let _counted = waiting.fetch_add(1, Ordering::AcqRel);
            }
            if let Err(fault) = write_frame(&mut forward, &body) {
                break Err(fault);
            }
        };
        drop(verdict.send(Ending::Served(served)));
        drop(forward.shutdown(std::net::Shutdown::Write));
    }));
    let mut reading = BufReader::new(hub);
    while let Maybe::Present(body) = read_frame(&mut reading)? {
        let answer = answered(&body);
        if answer != Answered::Unanswered {
            let _answered = pending.try_update(Ordering::AcqRel, Ordering::Acquire, |count| {
                Some(count.saturating_sub(1))
            });
        }
        if answer == Answered::Replay {
            if replayed_requests > 0 {
                replayed_requests = replayed_requests.saturating_sub(1);
                continue;
            }
            let replay = replayed(&body)?;
            return match verdicts.recv() {
                Ok(Ending::Switching(carried)) => {
                    Ok(Relayed::Switched(Handover::new(replay, Carried(carried))))
                },
                Ok(Ending::Served(served)) => served.map(Relayed::Ended),
                Err(_gone) => Ok(Relayed::Ended(Served::Abrupt)),
            };
        }
        write_frame(output, &body)?;
    }
    match verdicts.try_recv() {
        Ok(Ending::Served(served)) => served.map(Relayed::Ended),
        Ok(Ending::Switching(_)) | Err(_) => Ok(Relayed::Ended(Served::Abrupt)),
    }
}
