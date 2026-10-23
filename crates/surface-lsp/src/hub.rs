//! The engine hub: one process serving every connection to a workspace over
//! a Unix domain socket, the connections sharing the documents they open.
//!
//! The hub accepts connections until none has been open for its linger, then
//! removes its socket and returns. Each connection runs on a reader thread,
//! which handles the frames it reads over the one [`Workspace`] and publishes
//! what a quiet document held back, as the `quiet` module states, and a writer
//! thread, which drains the connection's outbox of its answers and
//! publications. A relay is the client's end: it carries frames between an
//! editor's standard streams and the hub's socket.
//!
//! # One hub serves a workspace's clients
//!
//! **Choice.** On Unix, `gandr lsp` is a relay: it connects to the engine hub
//! listening on the current directory's workspace socket, starting `gandr
//! serve` detached when nothing answers, and carries frames between its
//! standard streams and the socket unchanged. The hub, `run_hub`, accepts every
//! connection the socket takes and serves each with a reader thread and a
//! writer thread over one `Workspace`: the open documents, each with every
//! holding connection's own copy of its text and session. Each connection's
//! changes apply to its own copy and it is answered from that copy, so two
//! editors over one file are each answered for the text they hold, and the
//! faces beside them read the copy that synchronised last. A connection that
//! ends, cleanly or killed, lets go of what it held; a document no connection
//! holds is forgotten with its sessions. The hub removes its socket and exits
//! once no client has connected for its linger, a minute unless `--linger-ms`
//! names another.
//!
//! **Discovery.** The socket is `$XDG_RUNTIME_DIR/gandr/<digest>.sock`, or
//! `<temporary directory>/gandr-$USER/<digest>.sock` without that variable,
//! where the digest is the first sixteen hex digits of the canonical workspace
//! path's BLAKE3 hash; the directory is created readable by its owner alone.
//! Sixteen digits keep the path under the 104 bytes the smallest platform limit
//! allows inside a long per-user temporary directory. `bind` answers `Served`
//! when a hub accepts on the socket, and removes and rebinds a socket file
//! nothing accepts on, so a hub that died leaves no lock behind. The socket
//! file is the lock: no second file says who owns it.
//!
//! **Serialisation.** One mutex guards the workspace; a connection holds it
//! while it handles a frame and runs the admission that frame left, and sends
//! what it made to its outbox inside it, so every face reads a document's
//! copies in the order the hub changed them. The relay decides its exit code
//! from the frames it carries: a `shutdown` request before `exit` is clean,
//! anything else abrupt, a broken client stream a fault, as `serve` decides
//! them.
//!
//! **A second face.** The hub reads each connection's first byte: a frame
//! begins with its `Content-Length` header, so a connection beginning with `{`
//! is handed to the `Face` `run_hub` was given, which serves it over the same
//! locked workspace; the driver gives it the Model Context Protocol server.
//! Each publication keeps its diagnostics beside the document and tells every
//! watcher the document changed, so another face reads diagnostics without
//! judging the text again. The face is a parameter so this crate does not
//! depend on the protocols served beside it.
//!
//! **Alternatives.** A hub per document would keep a judgement per process
//! that a face beside the editors could not read; one workspace per hub
//! holds every copy where every face reads it. A lock file beside the socket
//! would name the owner's process, at the cost of a second file whose staleness
//! needs the same probe the socket answers directly. A hub that exits with its
//! last client would cost the next editor start a cold session; the linger
//! keeps a restart warm and returns the memory soon after. Per-document locks
//! would let two clients' edits to different documents run at once; the one
//! lock is simpler and no measurement shows contention. Making the relay read
//! the hub's answers to learn whether `shutdown` succeeded would cost a parse
//! per frame both ways for a case only a client that sends `shutdown` before
//! `initialize` reaches. The read-evaluate loop as a client is not in this
//! crate yet; a client speaking another protocol than the Language Server
//! Protocol is a second face over the same `Workspace`.
//!
//! **Reversal.** Measured contention on the workspace lock moves it per
//! document; a platform without Unix domain sockets gains a transport there,
//! its clients serving standalone until it does; a client that needs the hub's
//! own judgement of its session's ending replaces the relay's reading of its
//! input with one of the hub's answers.

use alloc::collections::BTreeSet;
use alloc::sync::Arc;
use core::ops::ControlFlow;
use core::sync::atomic::AtomicU64;
use core::sync::atomic::Ordering;
use core::time::Duration;
use std::fs::DirBuilder;
use std::io;
use std::io::BufRead as _;
use std::io::BufReader;
use std::io::Read;
use std::io::Write;
use std::os::unix::fs::DirBuilderExt as _;
use std::os::unix::net::UnixListener;
use std::os::unix::net::UnixStream;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Mutex;
use std::sync::MutexGuard;
use std::sync::PoisonError;
use std::sync::mpsc::Sender;
use std::sync::mpsc::channel;
use std::thread;
use std::time::Instant;

use anodized::spec;
use gandr_surface_dispatcher::Pool;
use gandr_surface_pretty::Spelling;
use quenchant_shape::shape::Maybe;

use crate::disk::Disk;
use crate::quiet::Inbox;
use crate::quiet::Met;
use crate::quiet::paced;
use crate::rpc::Incoming;
use crate::rpc::Outgoing;
use crate::rpc::classify;
use crate::server::Admissions;
use crate::server::Awaiting;
use crate::server::Flow;
use crate::server::Logged;
use crate::server::Peer;
use crate::server::Served;
use crate::server::Server;
use crate::server::Workspace;
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

/// How often a hub with nothing to accept looks again.
///
/// economy: 20 ms. A connection waits at most this long to be accepted; an
/// idle hub wakes fifty times a second, a cost no profile has found.
const POLL: Duration = Duration::from_millis(20);

/// The hex digits of the workspace digest a socket is named by.
///
/// economy: 16 digits, 64 bits. Collisions between one user's workspaces are
/// out of reach, and the name keeps a socket path under the 104 bytes the
/// smallest platform limit allows, inside a long per-user temporary directory.
const NAME_DIGITS: usize = 16;

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
pub fn lock<Held>(mutex: &Mutex<Held>) -> MutexGuard<'_, Held>
{
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

/// The socket the hub serving the workspace rooted at `root` listens on.
///
/// # Specification
/// - requires: nothing; `root` is resolved through the file system.
/// - ensures: the path is `$XDG_RUNTIME_DIR/gandr/<digest>.sock` when that
///   variable is set, `<temporary directory>/gandr-$USER/<digest>.sock`
///   otherwise, where the digest is the first sixteen hex digits of the BLAKE3
///   hash of the canonical root. Every spelling of one directory names one
///   socket.
/// - provides: discovery: a client and the hub it starts agree on the socket
///   without exchanging it.
/// - fails: when `root` cannot be canonicalised.
/// - panics: none.
///
/// # Errors
/// The error canonicalising `root` returned.
///
/// # Adequacy
/// - hypothesis: L3 — a directory named directly and through a `..` detour
///   names one socket; a sibling directory names another.
/// - witness: `hub::tests::a_workspace_names_one_socket`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |socket|
    socket.extension().is_some_and(|extension| extension == "sock")))]
#[inline]
pub fn socket_for(root: &Path) -> Result<PathBuf, io::Error>
{
    let root = std::fs::canonicalize(root)?;
    let directory = std::env::var_os("XDG_RUNTIME_DIR").map_or_else(
        || {
            let mut name = std::ffi::OsString::from("gandr-");
            name.push(std::env::var_os("USER").unwrap_or_default());
            std::env::temp_dir().join(name)
        },
        |runtime| PathBuf::from(runtime).join("gandr"),
    );
    let digest = blake3::hash(root.as_os_str().as_encoded_bytes()).to_hex();
    let name: String = digest
        .chars()
        .take(NAME_DIGITS)
        .chain(".sock".chars())
        .collect();
    Ok(directory.join(name))
}

/// Listen on `socket`, unless another hub already does.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the socket's directory exists, created readable by its owner
///   alone when this call made it. A socket another hub accepts on is
///   [`bind::Absent::Served`] and left alone; a socket file nothing accepts on
///   is stale, removed and bound afresh.
/// - provides: the one hub per socket a client's start relies on.
/// - fails: when the directory cannot be made or the socket bound.
/// - panics: none.
///
/// # Errors
/// The error creating the directory, removing a stale socket or binding.
///
/// # Adequacy
/// - hypothesis: L3 — binding a live hub's socket answers Served; binding the
///   socket a dropped listener left behind succeeds.
/// - witness: `hub::tests::a_socket_has_one_hub`
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

/// A face that serves a connection speaking newline-delimited JSON.
///
/// The Model Context Protocol speaks it. The face reads the connection
/// through the buffered stream it is given, writes to the stream under it,
/// and works over the workspace every connection shares, as the peer it is
/// given. The hub lets the peer go and shuts the stream once the face
/// returns.
pub type Face = fn(&mut BufReader<UnixStream>, Peer, &Mutex<Workspace>);

/// Serve every connection `listener`, bound to `socket`, accepts over one
/// workspace, until none has been open for `linger`.
///
/// # Specification
/// - requires: `listener` is bound to `socket`.
/// - ensures: a connection whose first byte is `{` is handed to `lines` when
///   one is given, and one whose first byte is `r` to the render-bus face,
///   [`crate::bus::serve`]. Every other accepted connection is served as
///   [`Server::handle`], [`Server::admit`] and [`Server::admitted`] state, over
///   the documents every connection shares, the workspace's configured spelling
///   `spelling`, its judgements and kernel admissions running on `pool`, each
///   connection answered from its own copy: its answers and publications reach
///   it in the order its handling made them, and each synchronisation's timing
///   line goes to `log`. For a connection whose client watches no file, the hub
///   watches the files its copies' closures name, as [`Server::followed`] reads
///   them, and a change to one on disk is handled as
///   [`Server::changed_on_disk`] states; a watch that cannot start is said once
///   in `log` and the hub serves on unwatched. A connection ends at `exit`, at
///   the end of its stream, or at a stream fault; it then holds nothing and its
///   socket is shut. The hub returns once no connection has been open for
///   `linger`, its socket file removed first so a late client starts a fresh
///   hub.
/// - provides: the engine hub's whole lifetime.
/// - fails: when accepting fails for a reason other than having nothing to
///   accept.
/// - panics: none.
/// - executable: none — the hub's effects are frames on other threads' sockets
///   and the socket file another process may bind again at once; its return
///   carries none of them.
///
/// # Errors
/// The error accepting a connection or configuring the listener returned.
///
/// # Adequacy
/// - hypothesis: L3 — two connections over one document are each answered for
///   their own copy; one leaving leaves the other served; the hub, left with
///   none, removes its socket and returns.
/// - witness: `hub::tests::two_clients_hold_their_own_copies_230`
/// - witness: `hub::tests::a_hub_left_alone_exits_after_its_linger`
/// - witness: `hub::tests::a_hub_whose_socket_is_already_gone_exits_cleanly`
/// - witness: `hub::tests::a_line_connection_reaches_the_second_face`
/// - witness: `hub::tests::an_attached_view_follows_the_editors_edits`
/// - witness: `hub::tests::an_unwatching_client_is_told_of_a_rewritten_import`
#[inline]
pub fn run_hub<Log>(
    listener: &UnixListener,
    socket: &Path,
    linger: Duration,
    mut log: Log,
    lines: Option<Face>,
    (spelling, pool): (Spelling, Pool),
) -> Result<(), io::Error>
where
    Log: Write + Send + 'static,
{
    listener.set_nonblocking(true)?;
    let workspace = Arc::new(Mutex::new(Workspace::spelled(spelling)));
    let pool = Arc::new(pool);
    let disk = match Disk::new() {
        Ok(disk) => Some(disk),
        Err(error) => {
            drop(writeln!(log, "the hub watches no file: {error}"));
            None
        },
    };
    let disk = Arc::new(Mutex::new(disk));
    let log = Arc::new(Mutex::new(log));
    let open = Arc::new(AtomicU64::new(0));
    let mut peers = 0_u64;
    let mut quiet_since = Instant::now();
    let mut start = |stream: UnixStream| -> Result<(), io::Error> {
        stream.set_nonblocking(false)?;
        peers = peers.saturating_add(1);
        let _opened = open.fetch_add(1, Ordering::SeqCst);
        let (workspace, disk, log, open, pool) = (
            Arc::clone(&workspace),
            Arc::clone(&disk),
            Arc::clone(&log),
            Arc::clone(&open),
            Arc::clone(&pool),
        );
        let peer = Peer::from(peers);
        drop(thread::spawn(move || {
            connection(stream, peer, (&workspace, &pool), &disk, &log, lines);
            let _closed = open.fetch_sub(1, Ordering::SeqCst);
        }));
        Ok(())
    };
    loop {
        match listener.accept() {
            Ok((stream, _address)) => start(stream)?,
            Err(error) if error.kind() == io::ErrorKind::WouldBlock => {
                if open.load(Ordering::SeqCst) != 0 {
                    quiet_since = Instant::now();
                }
                else if quiet_since.elapsed() >= linger {
                    break;
                }
                thread::sleep(POLL);
            },
            Err(error) => return Err(error),
        }
    }
    match std::fs::remove_file(socket) {
        Ok(()) => {},
        Err(error) if error.kind() == io::ErrorKind::NotFound => {},
        Err(error) => return Err(error),
    }
    while let Ok((stream, _address)) = listener.accept() {
        start(stream)?;
    }
    while open.load(Ordering::SeqCst) != 0 {
        thread::sleep(POLL);
    }
    Ok(())
}

/// Serve the connection `peer` over `stream` until it ends.
///
/// # Specification
/// - requires: `stream` is blocking.
/// - ensures: as [`run_hub`] states for one connection; on return `peer` has
///   departed `workspace` and `stream` is shut both ways.
/// - provides: one connection's reader and writer.
/// - fails: never; a fault ends the connection.
/// - panics: none.
/// - executable: none — the connection's effects are frames on its socket and
///   entries in a workspace other connections change concurrently.
///
/// # Adequacy
/// - hypothesis: L3 — as [`run_hub`]'s witnesses.
/// - witness: `hub::tests::two_clients_hold_their_own_copies_230`
fn connection<Log>(
    stream: UnixStream,
    peer: Peer,
    (workspace, pool): (&Mutex<Workspace>, &Pool),
    disk: &Mutex<Option<Disk>>,
    log: &Mutex<Log>,
    lines: Option<Face>,
) where
    Log: Write,
{
    let mut reading = BufReader::new(stream);
    let first = reading
        .fill_buf()
        .ok()
        .and_then(|bytes| bytes.first().copied());
    let face: Option<Face> = match (first, lines) {
        (Some(b'{'), Some(lines)) => Some(lines),
        (Some(b'r'), _) => Some(crate::bus::serve),
        _ => None,
    };
    if let Some(face) = face {
        face(&mut reading, peer, workspace);
        lock(workspace).depart(peer);
        drop(reading.get_ref().shutdown(std::net::Shutdown::Both));
        return;
    }
    let (outbox, inbox) = channel::<Outgoing>();
    let writer = reading.get_ref().try_clone().map(|mut writing| {
        thread::spawn(move || {
            for message in inbox {
                let Ok(encoded) = serde_json::to_vec(&message)
                else {
                    break;
                };
                if write_frame(&mut writing, &Body::from(encoded)).is_err() {
                    break;
                }
            }
        })
    });
    let mut server = Server::new(peer);
    let inbox = Inbox::default();
    let changes = inbox.changes();
    let mut admissions = Admissions::new(pool, inbox.changes());
    lock(workspace).hear_edits(peer, inbox.changes());
    if writer.is_ok() {
        let _ended = paced(&mut reading, inbox, |met, deadlines| {
            let mut held = lock(workspace);
            let (reported, messages, flow) = match met {
                Met::Closed => {
                    let settled = server.admitted(&mut held, &mut admissions, Awaiting::All);
                    drop(held);
                    let mut written = lock(log);
                    for line in &settled.log {
                        drop(writeln!(written, "{line}"));
                    }
                    drop(written);
                    return Ok(ControlFlow::Break(()));
                },
                Met::Quiet(uri) => {
                    for message in server.release(&mut held, &uri) {
                        drop(outbox.send(message));
                    }
                    return Ok(ControlFlow::Continue(()));
                },
                Met::Proposed => {
                    for message in server.proposed_elsewhere(&held) {
                        drop(outbox.send(message));
                    }
                    return Ok(ControlFlow::Continue(()));
                },
                Met::Admitted => {
                    let settled = server.admitted(&mut held, &mut admissions, Awaiting::Ended);
                    // The watch follows what the published judgements' closures
                    // name before the client hears them, so a change it makes on
                    // hearing one is seen.
                    if let Some(ref mut watch) = *lock(disk)
                        && let Some(watched) = watch.follow(peer, &changes, server.followed(&held))
                    {
                        held.watched_on_disk(watched);
                    }
                    drop(held);
                    for message in settled.messages {
                        drop(outbox.send(message));
                    }
                    deadlines.note(&settled.judged, server.quiet(), Instant::now());
                    deadlines.settled(&settled.log);
                    logged(&server, &settled.log, (log, &outbox));
                    return Ok(ControlFlow::Continue(()));
                },
                Met::Changed(paths) => {
                    let reported = server.reported_on_disk(&held, &paths);
                    for message in reported.begin {
                        drop(outbox.send(message));
                    }
                    server.changed_on_disk(&mut held, &paths);
                    (reported.end, Vec::new(), Flow::Continue)
                },
                Met::Edited(paths) => {
                    let reported = server.reported_elsewhere(&held, &paths);
                    for message in reported.begin {
                        drop(outbox.send(message));
                    }
                    server.edited_elsewhere(&mut held, &paths);
                    (reported.end, Vec::new(), Flow::Continue)
                },
                Met::Frame { message, later } => {
                    let reported = server.reported(&held, &message);
                    for message in reported.begin {
                        drop(outbox.send(message));
                    }
                    let outcome = server.answer(&mut held, message, later);
                    (reported.end, outcome.messages, outcome.flow)
                },
            };
            // The watch is armed before the client hears the judgement, so a
            // change it makes on hearing it is seen.
            if let Some(ref mut watch) = *lock(disk)
                && let Some(watched) = watch.follow(peer, &changes, server.followed(&held))
            {
                held.watched_on_disk(watched);
            }
            for message in messages {
                drop(outbox.send(message));
            }
            let now = server.admit(&mut held, &mut admissions);
            for message in admissions.ended(reported) {
                drop(outbox.send(message));
            }
            drop(held);
            logged(&server, &now, (log, &outbox));
            Ok(match flow {
                Flow::Exit(_) => {
                    let settled =
                        server.admitted(&mut lock(workspace), &mut admissions, Awaiting::All);
                    let mut written = lock(log);
                    for line in &settled.log {
                        drop(writeln!(written, "{line}"));
                    }
                    drop(written);
                    ControlFlow::Break(())
                },
                Flow::Continue => ControlFlow::Continue(()),
            })
        });
    }
    let watched = lock(disk)
        .as_mut()
        .and_then(|watch| watch.follow(peer, &changes, BTreeSet::new()));
    let mut held = lock(workspace);
    if let Some(watched) = watched {
        held.watched_on_disk(watched);
    }
    held.depart(peer);
    drop(held);
    drop(outbox);
    if let Ok(writer) = writer {
        drop(writer.join());
    }
    drop(reading.get_ref().shutdown(std::net::Shutdown::Both));
}

/// Write `lines` to `log`, and send the trace of them `server`'s client asked
/// for through `outbox`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: each line is written to `log` with a line terminator, a line
///   `log` refuses dropped, then each trace message `server` makes of them is
///   sent, a message the closed writer refuses dropped.
/// - fails: never.
/// - panics: none.
/// - executable: none — the log and the writer are opaque.
///
/// # Adequacy
/// - hypothesis: L3 — as [`run_hub`]'s witnesses.
/// - witness: `hub::tests::two_clients_hold_their_own_copies_230`
fn logged<Log>(
    server: &Server,
    lines: &[Logged],
    (log, outbox): (&Mutex<Log>, &Sender<Outgoing>),
) where
    Log: Write,
{
    let mut written = lock(log);
    for line in lines {
        drop(writeln!(written, "{line}"));
    }
    drop(written);
    for message in server.traced(lines) {
        drop(outbox.send(message));
    }
}

/// Carry frames between a client and the hub at the other end of `hub`:
/// each frame `input` holds to the hub, each frame the hub sends to
/// `output`, until the hub closes the connection.
///
/// # Specification
/// - requires: nothing.
/// - ensures: frames pass unchanged and in order both ways. Once `input` ends,
///   faults or carries `exit`, the hub's end is shut for writing. The session
///   is [`Served::Clean`] when `input` carried a `shutdown` request before
///   `exit`, the fault when `input` broke inside a frame, and
///   [`Served::Abrupt`] otherwise.
/// - provides: a client's whole session with a hub.
/// - fails: when `input` breaks, or a frame from the hub cannot be read or
///   written to `output`.
/// - panics: none.
/// - executable: none — the frames go to a socket and to `output`, which the
///   call consumes or writes but cannot read back.
///
/// # Errors
/// [`TransportFault`] reading `input` or the hub's frames, or writing to
/// `output`.
///
/// # Adequacy
/// - hypothesis: L3 — a session of initialize, shutdown and exit is carried
///   whole and ends clean; one closed before shutdown ends abrupt; a truncated
///   frame is a fault.
/// - witness: `hub::tests::a_relay_carries_a_session_and_its_ending`
#[inline]
pub fn relay<Input, Output>(
    input: Input,
    output: &mut Output,
    hub: UnixStream,
) -> Result<Served, TransportFault>
where
    Input: Read + Send + 'static,
    Output: Write,
{
    let mut forward = hub.try_clone().map_err(TransportFault::Io)?;
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
            let exit = match classify(&body) {
                Ok(Incoming::Request { ref method, .. }) => {
                    shut |= method.as_ref() == "shutdown";
                    false
                },
                Ok(Incoming::Notification { ref method, .. }) => method.as_ref() == "exit",
                Ok(Incoming::Response { .. }) | Err(_) => false,
            };
            if exit {
                // The verdict is sent before the hub can read `exit`, so it
                // is waiting when the hub's end closes.
                drop(verdict.send(Ok(if shut { Served::Clean } else { Served::Abrupt })));
                drop(write_frame(&mut forward, &body));
                break Ok(Served::Abrupt);
            }
            if let Err(fault) = write_frame(&mut forward, &body) {
                break Err(fault);
            }
        };
        drop(verdict.send(served));
        drop(forward.shutdown(std::net::Shutdown::Write));
    }));
    let mut reading = BufReader::new(hub);
    while let Maybe::Present(body) = read_frame(&mut reading)? {
        write_frame(output, &body)?;
    }
    verdicts.try_recv().unwrap_or(Ok(Served::Abrupt))
}

#[cfg(test)]
mod tests
{
    use core::time::Duration;
    use std::io;
    use std::io::BufRead as _;
    use std::io::BufReader;
    use std::io::Write as _;
    use std::os::unix::net::UnixStream;
    use std::path::Path;
    use std::path::PathBuf;
    use std::thread;
    use std::thread::JoinHandle;

    use anodized::spec;
    use gandr_surface_render_remote::DocId;
    use gandr_surface_render_remote::DocVersion;
    use gandr_surface_render_remote::FrameBody;
    use gandr_surface_render_remote::FrameScope;
    use gandr_surface_render_remote::RenderFrame;
    use quenchant_shape::shape::Maybe;
    use serde_json::Value;

    use super::bind;
    use super::relay;
    use super::run_hub;
    use super::socket_for;
    use crate::bus::RENDER_BUS_PREFACE;
    use crate::server::Served;
    use crate::transport::Body;
    use crate::transport::read_frame;
    use crate::transport::write_frame;

    /// A message, spelled as JSON text.
    #[repr(transparent)]
    #[derive(Clone, Copy)]
    struct Json<'text>(&'text str);

    /// A fresh scratch directory, removed when dropped.
    #[repr(transparent)]
    struct Scratch(PathBuf);

    impl Scratch
    {
        /// An empty directory named for `test` and this process, kept short:
        /// a socket path inside it must fit the platform's limit.
        ///
        /// # Specification
        /// trivial.
        fn new(test: Json<'_>) -> Self
        {
            let Json(test) = test;
            let directory = std::env::temp_dir().join(format!("gh-{}-{test}", std::process::id()));
            drop(std::fs::remove_dir_all(&directory));
            std::fs::create_dir_all(&directory).expect("the scratch directory is made");
            Self(directory)
        }

        /// The socket path inside the directory.
        ///
        /// # Specification
        /// trivial.
        fn socket(&self) -> PathBuf
        {
            self.0.join("hub.sock")
        }
    }

    impl Drop for Scratch
    {
        /// Remove the directory.
        ///
        /// # Specification
        /// trivial.
        fn drop(&mut self)
        {
            drop(std::fs::remove_dir_all(&self.0));
        }
    }

    /// A line face that answers each line it reads with the number of
    /// documents the workspace holds, then the line.
    ///
    /// # Specification
    /// trivial.
    fn echo(
        reading: &mut BufReader<UnixStream>,
        _peer: super::Peer,
        workspace: &std::sync::Mutex<super::Workspace>,
    )
    {
        let mut writing = reading.get_ref().try_clone().expect("the stream clones");
        let mut line = String::new();
        while reading.read_line(&mut line).is_ok_and(|read| read != 0) {
            let held = super::lock(workspace).held().count();
            write!(writing, "{held} {line}").expect("the client reads");
            line.clear();
        }
    }

    /// A hub serving `socket` on its own thread, lingering 100 ms, its line
    /// face [`echo`].
    ///
    /// # Specification
    /// trivial.
    fn hub(socket: &Path) -> JoinHandle<()>
    {
        let Maybe::Present(listener) = bind(socket).expect("the socket binds")
        else {
            panic!("no other hub serves a fresh socket");
        };
        let socket = socket.to_path_buf();
        thread::spawn(move || {
            run_hub(
                &listener,
                &socket,
                Duration::from_millis(100),
                io::sink(),
                Some(echo),
                (
                    super::Spelling::Unicode,
                    super::Pool::new(gandr_surface_dispatcher::Width::SERIAL),
                ),
            )
            .expect("the hub serves");
        })
    }

    /// One client's end of a hub connection.
    struct Client
    {
        /// The end it writes.
        writing: UnixStream,
        /// The end it reads, buffered across frames.
        reading: BufReader<UnixStream>,
    }

    impl Client
    {
        /// A client connected to `socket`, initialised.
        ///
        /// # Specification
        /// trivial.
        fn new(socket: &Path) -> Self
        {
            Self::initialised(socket, Json("{}"))
        }

        /// A client connected to `socket`, initialised with the `initialize`
        /// parameters `params` spells.
        ///
        /// # Specification
        /// trivial.
        fn initialised(
            socket: &Path,
            params: Json<'_>,
        ) -> Self
        {
            let writing = UnixStream::connect(socket).expect("the hub accepts");
            let reading = BufReader::new(writing.try_clone().expect("the stream clones"));
            let mut client = Self { writing, reading };
            let Json(params) = params;
            let initialize =
                format!(r#"{{"jsonrpc":"2.0","id":1,"method":"initialize","params":{params}}}"#);
            client.send(Json(&initialize));
            assert!(client.receive().pointer("/result/capabilities").is_some());
            client
        }

        /// Send the message `json` spells.
        ///
        /// # Specification
        /// trivial.
        fn send(
            &mut self,
            json: Json<'_>,
        )
        {
            let Json(text) = json;
            write_frame(&mut self.writing, &Body::from(text.as_bytes().to_vec()))
                .expect("the hub reads");
        }

        /// The next message the hub sent, parsed.
        ///
        /// # Specification
        /// - requires: the hub owes the client a message.
        /// - ensures: the value is the next frame's body, parsed as JSON.
        /// - provides: the client's view of the hub's answers.
        /// - fails: never in the valid domain.
        /// - panics: a closed connection or an unparseable body fails the
        ///   witness.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — the witnesses read exact versions and results.
        /// - witness: `hub::tests::two_clients_hold_their_own_copies_230`
        #[spec(ensures: |ret| ret.is_object())]
        fn receive(&mut self) -> Value
        {
            let Maybe::Present(body) =
                read_frame(&mut self.reading).expect("the hub frames its messages")
            else {
                panic!("the hub closed the connection");
            };
            serde_json::from_slice(body.as_ref()).expect("the hub sends JSON")
        }

        /// The version of the next message, a publication.
        ///
        /// # Specification
        /// trivial.
        fn published(&mut self) -> Option<Value>
        {
            let message = self.receive();
            assert_eq!(
                message.get("method"),
                Some(&serde_json::json!("textDocument/publishDiagnostics"))
            );
            message.pointer("/params/version").cloned()
        }
    }

    /// The frames `messages` spell, one after another.
    ///
    /// # Specification
    /// trivial.
    fn frames(messages: &[Json<'_>]) -> Body
    {
        let mut framed = Vec::new();
        for &Json(message) in messages {
            write_frame(&mut framed, &Body::from(message.as_bytes().to_vec()))
                .expect("a vector takes a frame");
        }
        Body::from(framed)
    }

    #[test]
    fn a_workspace_names_one_socket()
    {
        let scratch = Scratch::new(Json("names"));
        let (first, second) = (scratch.0.join("first"), scratch.0.join("second"));
        std::fs::create_dir_all(&first).expect("a workspace is made");
        std::fs::create_dir_all(&second).expect("a workspace is made");
        let named = socket_for(&first).expect("the workspace resolves");
        assert_eq!(
            socket_for(&second.join("..").join("first")).expect("the detour resolves"),
            named,
            "every spelling of one directory names one socket"
        );
        assert_ne!(socket_for(&second).expect("the sibling resolves"), named);
        assert!(socket_for(&scratch.0.join("absent")).is_err());
    }

    #[test]
    fn a_socket_has_one_hub()
    {
        let scratch = Scratch::new(Json("bind"));
        let socket = scratch.socket();
        let first = bind(&socket).expect("a fresh socket binds");
        assert!(matches!(first, Maybe::Present(_)));
        assert!(
            matches!(
                bind(&socket).expect("a served socket is read"),
                Maybe::Absent(super::bind::Absent::Served)
            ),
            "a socket a hub accepts on is left to it"
        );
        drop(first);
        assert!(socket.exists(), "a dropped listener leaves its file behind");
        assert!(
            matches!(
                bind(&socket).expect("a stale socket binds"),
                Maybe::Present(_)
            ),
            "a socket nothing accepts on is stale and bound afresh"
        );
    }

    #[test]
    fn two_clients_hold_their_own_copies_230()
    {
        let scratch = Scratch::new(Json("share"));
        let socket = scratch.socket();
        let hub = hub(&socket);
        let open = Json(
            r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{
                "uri":"file:///tmp/shared.gandr","version":1,"text":"def f = 42 ;\n"}}}"#,
        );
        let mut first = Client::new(&socket);
        first.send(open);
        assert_eq!(first.published(), Some(serde_json::json!(1_i32)));
        let mut second = Client::new(&socket);
        second.send(open);
        assert_eq!(second.published(), Some(serde_json::json!(1_i32)));
        first.send(Json(
            r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{
                "textDocument":{"uri":"file:///tmp/shared.gandr","version":2},
                "contentChanges":[{"text":"def g = 1 ;\n"}]}}"#,
        ));
        assert_eq!(
            first.published(),
            Some(serde_json::json!(2_i32)),
            "the first hears its own change, and nothing of the second's open"
        );
        second.send(Json(
            r#"{"jsonrpc":"2.0","id":5,"method":"textDocument/hover","params":{
                "textDocument":{"uri":"file:///tmp/shared.gandr"},"position":{"line":0,"character":4}}}"#,
        ));
        assert_eq!(
            second.receive().pointer("/result/contents/value"),
            Some(&serde_json::json!("```gandr\nf : Integer\n```")),
            "each client is answered for the text it holds, and hears nothing of the other's change"
        );
        drop(first);
        second.send(Json(
            r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{
                "textDocument":{"uri":"file:///tmp/shared.gandr","version":3},
                "contentChanges":[{"text":"def h = 2 ;\n"}]}}"#,
        ));
        assert_eq!(
            second.published(),
            Some(serde_json::json!(3_i32)),
            "a client killed mid-session leaves the other served"
        );
        drop(second);
        hub.join().expect("the hub exits");
        assert!(!socket.exists(), "the hub removes its socket");
    }

    #[test]
    fn an_html_client_hovers_in_the_roles_its_tokens_carry()
    {
        let scratch = Scratch::new(Json("html"));
        let socket = scratch.socket();
        let hub = hub(&socket);
        let mut client = Client::initialised(
            &socket,
            Json(
                r#"{"capabilities":{"general":{"markdown":{"parser":"marked",
                    "allowedTags":["p","code","pre","span","em"]}}}}"#,
            ),
        );
        let coloured = |role: &str, text: &str| {
            format!("<span style=\"color:var(--vscode-gandr-hover-{role});\">{text}</span>")
        };
        let mut hovered = |uri: &str, text: &str, (line, character): (u32, u32)| {
            let open = serde_json::json!({
                "jsonrpc": "2.0",
                "method": "textDocument/didOpen",
                "params": {"textDocument": {"uri": uri, "version": 1_i32, "text": text}},
            })
            .to_string();
            client.send(Json(&open));
            assert_eq!(client.published(), Some(serde_json::json!(1_i32)));
            let hover = serde_json::json!({
                "jsonrpc": "2.0",
                "id": 5_i32,
                "method": "textDocument/hover",
                "params": {
                    "textDocument": {"uri": uri},
                    "position": {"line": line, "character": character},
                },
            })
            .to_string();
            client.send(Json(&hover));
            client.receive().pointer("/result/contents/value").cloned()
        };
        assert_eq!(
            hovered("file:///tmp/f.gandr", "def f = 42 ;\n", (0, 4)),
            Some(serde_json::json!(format!(
                "<pre><code>{} : {}</code></pre>",
                coloured("functionDef", "f"),
                coloured("typeBuiltin", "Integer"),
            ))),
            "a client keeping `span`, `pre` and `code` reads the hover coloured by role"
        );
        // At its own path, so its import of the subject's base resolves.
        let corolla = concat!(
            "file://",
            env!("CARGO_MANIFEST_DIR"),
            "/../../corpus/model/higher-cells/ua-corolla.gandr"
        );
        assert_eq!(
            hovered(
                corolla,
                include_str!("../../../corpus/model/higher-cells/ua-corolla.gandr"),
                (49, 4),
            ),
            Some(serde_json::json!(format!(
                "<pre><code>{} : {}({} {} {}, {}, {})</code></pre>\n\nThe swap and the swap three \
                 times agree at every boolean.",
                coloured("functionDef", "agree"),
                coloured("typeBuiltin", "Path"),
                coloured("type", "Bool"),
                coloured("operator", "=&gt;"),
                coloured("type", "Bool"),
                coloured("variable", "exchange"),
                coloured("variable", "flip"),
            ))),
            "a path type in its sugared form, each role coloured, its punctuation as the editor \
             leaves it, then its documentation"
        );
        drop(client);
        hub.join().expect("the hub exits");
    }

    #[test]
    fn a_line_connection_reaches_the_second_face()
    {
        let scratch = Scratch::new(Json("lines"));
        let socket = scratch.socket();
        let hub = hub(&socket);
        let mut editor = Client::new(&socket);
        editor.send(Json(
            r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{
                "uri":"file:///tmp/lines.gandr","version":1,"text":"def f = 42 ;\n"}}}"#,
        ));
        assert_eq!(editor.published(), Some(serde_json::json!(1_i32)));
        let mut model = UnixStream::connect(&socket).expect("the hub accepts");
        model.write_all(b"{\"ping\":1}\n").expect("the hub reads");
        let mut answer = String::new();
        BufReader::new(&model)
            .read_line(&mut answer)
            .expect("the face answers");
        assert_eq!(
            answer, "1 {\"ping\":1}\n",
            "a connection opening with `{{` is served by the line face, over the shared documents"
        );
        drop(model);
        drop(editor);
        hub.join().expect("the hub exits");
    }

    /// The next frame the render bus sent on `reading`, and the line it came
    /// on.
    ///
    /// # Specification
    /// trivial.
    fn next_frame(reading: &mut BufReader<UnixStream>) -> (String, RenderFrame)
    {
        let mut line = String::new();
        assert_ne!(
            reading.read_line(&mut line).expect("the face writes lines"),
            0_usize,
            "the face owes a frame"
        );
        let frame =
            serde_json::from_str(&line).expect("each line is a frame at the schema version");
        (line, frame)
    }

    #[test]
    fn an_attached_view_follows_the_editors_edits()
    {
        let scratch = Scratch::new(Json("view"));
        let socket = scratch.socket();
        let hub = hub(&socket);
        let mut editor = Client::new(&socket);
        editor.send(Json(
            r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{
                "uri":"file:///tmp/view.gandr","version":1,"text":"def f : Integer ;\ndef f = \"one\" ;\n"}}}"#,
        ));
        assert_eq!(editor.published(), Some(serde_json::json!(1_i32)));
        let mut view = UnixStream::connect(&socket).expect("the hub accepts");
        view.write_all(RENDER_BUS_PREFACE.as_bytes())
            .expect("the hub reads");
        let mut reading = BufReader::new(view.try_clone().expect("the stream clones"));
        let document = |version: i32| DocId {
            uri: gandr_surface_render_remote::DocumentUri::from(String::from(
                "file:///tmp/view.gandr",
            )),
            version: DocVersion::from(version),
        };
        let (_line, greeting) = next_frame(&mut reading);
        assert_eq!(
            greeting,
            RenderFrame::hello(Vec::from([document(1_i32)])),
            "the view is greeted with the held document"
        );
        let report = |frame: &RenderFrame| match *frame.body() {
            FrameBody::Frame { ref report } => report.clone(),
            FrameBody::Hello { .. } | FrameBody::Resync | FrameBody::Detach => {
                panic!("a report was owed, not {frame:?}")
            },
        };
        let (line, first) = next_frame(&mut reading);
        assert!(
            line.contains("\"schema_version\":1"),
            "the served frame carries its schema version: {line}"
        );
        assert_eq!(first.scope(), &FrameScope::Document(document(1_i32)));
        assert_eq!(
            report(&first).diagnostics.len(),
            1_usize,
            "the refusal the editor shows is a card"
        );
        editor.send(Json(
            r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{
                "textDocument":{"uri":"file:///tmp/view.gandr","version":2},
                "contentChanges":[{"text":"def f : Integer ;\ndef f = 1 ;\n"}]}}"#,
        ));
        assert_eq!(editor.published(), Some(serde_json::json!(2_i32)));
        let (_line, second) = next_frame(&mut reading);
        assert_eq!(
            second.scope(),
            &FrameScope::Document(document(2_i32)),
            "the edit reaches the view within its one check"
        );
        assert_eq!(report(&second).source, "def f : Integer ;\ndef f = 1 ;\n");
        assert!(
            report(&second).diagnostics.is_empty(),
            "the repaired document carries no card"
        );
        let mut resync =
            serde_json::to_string(&RenderFrame::resync(document(1_i32))).expect("a frame encodes");
        resync.push('\n');
        view.write_all(resync.as_bytes()).expect("the hub reads");
        assert_eq!(
            next_frame(&mut reading).1,
            second,
            "a resync is answered at the current version"
        );
        let mut detach = serde_json::to_string(&RenderFrame::detach()).expect("a frame encodes");
        detach.push('\n');
        view.write_all(detach.as_bytes()).expect("the hub reads");
        assert_eq!(next_frame(&mut reading).1, RenderFrame::detach());
        let mut rest = String::new();
        assert_eq!(
            reading.read_line(&mut rest).expect("the end is read"),
            0_usize,
            "a detach closes the stream"
        );
        let mut stranger = UnixStream::connect(&socket).expect("the hub accepts");
        stranger
            .write_all(b"render-bus/9\n")
            .expect("the hub reads");
        let mut stranger = BufReader::new(stranger);
        assert_eq!(
            next_frame(&mut stranger).1,
            RenderFrame::detach(),
            "another bus version is detached at once"
        );
        drop(editor);
        hub.join().expect("the hub exits");
    }

    #[test]
    fn an_unwatching_client_is_told_of_a_rewritten_import()
    {
        let scratch = Scratch::new(Json("disk"));
        let socket = scratch.socket();
        let hub = hub(&socket);
        let importer = "import \"./base.gandr\" ;\ndef two : Integer ;\ndef two = one ;\n";
        let base = scratch.0.join("base.gandr");
        std::fs::write(&base, "def one : Integer ;\ndef one = 1 ;\n").expect("the base is written");
        let importing = scratch.0.join("importer.gandr");
        std::fs::write(&importing, importer).expect("the importer is written");
        let mut client = Client::new(&socket);
        client
            .reading
            .get_ref()
            .set_read_timeout(Some(Duration::from_secs(20)))
            .expect("the stream takes a timeout");
        let open = serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
            "textDocument": {"uri": format!("file://{}", importing.display()), "languageId": "gandr",
                "version": 1_i32, "text": importer}}});
        client.send(Json(&open.to_string()));
        let opened = client.receive();
        assert_eq!(
            opened.pointer("/params/diagnostics"),
            Some(&serde_json::json!([])),
            "the importer checks against its base"
        );
        std::fs::write(&base, "def other : Integer ;\ndef other = 1 ;\n")
            .expect("the base is rewritten");
        let rechecked = client.receive();
        assert_eq!(
            rechecked.get("method"),
            Some(&serde_json::json!("textDocument/publishDiagnostics")),
            "with nothing sent, the hub republishes the importer: {rechecked}"
        );
        assert_eq!(
            rechecked.pointer("/params/version"),
            Some(&serde_json::json!(1_i32))
        );
        assert!(
            rechecked
                .pointer("/params/diagnostics")
                .and_then(Value::as_array)
                .is_some_and(|diagnostics| !diagnostics.is_empty()),
            "the name the base no longer declares is refused: {rechecked}"
        );
        drop(client);
        hub.join().expect("the hub exits");
    }

    #[test]
    fn an_editor_s_copy_shadows_the_disk_for_every_connection()
    {
        let scratch = Scratch::new(Json("shadow"));
        let socket = scratch.socket();
        let hub = hub(&socket);
        let importer = "import \"./base.gandr\" ;\ndef two : Integer ;\ndef two = one ;\n";
        let base = scratch.0.join("base.gandr");
        std::fs::write(&base, "def one : Integer ;\ndef one = 1 ;\n").expect("the base is written");
        let importing = scratch.0.join("importer.gandr");
        std::fs::write(&importing, importer).expect("the importer is written");
        let mut reader = Client::new(&socket);
        let mut writer = Client::new(&socket);
        for client in [&reader, &writer] {
            client
                .reading
                .get_ref()
                .set_read_timeout(Some(Duration::from_secs(20)))
                .expect("the stream takes a timeout");
        }
        let open = |path: &Path, text: &str| {
            serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": format!("file://{}", path.display()), "languageId": "gandr",
                    "version": 1_i32, "text": text}}})
            .to_string()
        };
        reader.send(Json(&open(&importing, importer)));
        assert_eq!(
            reader.receive().pointer("/params/diagnostics"),
            Some(&serde_json::json!([])),
            "the importer checks against the base on disk"
        );
        writer.send(Json(&open(
            &base,
            "def other : Integer ;\ndef other = 1 ;\n",
        )));
        assert_eq!(
            writer.receive().pointer("/params/diagnostics"),
            Some(&serde_json::json!([])),
            "the editor's copy of the base checks"
        );
        let edited = reader.receive();
        assert_eq!(
            edited.pointer("/params/uri"),
            Some(&serde_json::json!(format!(
                "file://{}",
                importing.display()
            ))),
            "another editor's unsaved base republishes the importer: {edited}"
        );
        assert!(
            edited
                .pointer("/params/diagnostics")
                .and_then(Value::as_array)
                .is_some_and(|diagnostics| !diagnostics.is_empty()),
            "the name the editor's base no longer declares is refused: {edited}"
        );
        let close = serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didClose", "params": {
            "textDocument": {"uri": format!("file://{}", base.display())}}});
        writer.send(Json(&close.to_string()));
        let restored = reader.receive();
        assert_eq!(
            restored.pointer("/params/diagnostics"),
            Some(&serde_json::json!([])),
            "once no editor holds the base, the importer reads the disk again: {restored}"
        );
        drop(writer);
        drop(reader);
        hub.join().expect("the hub exits");
    }

    #[test]
    fn a_hub_left_alone_exits_after_its_linger()
    {
        let scratch = Scratch::new(Json("linger"));
        let socket = scratch.socket();
        hub(&socket).join().expect("the hub exits");
        assert!(!socket.exists(), "the hub removes its socket");
        assert!(
            matches!(
                bind(&socket).expect("the socket binds again"),
                Maybe::Present(_)
            ),
            "a later client starts a fresh hub"
        );
    }

    #[test]
    fn a_hub_whose_socket_is_already_gone_exits_cleanly()
    {
        let scratch = Scratch::new(Json("gone"));
        let socket = scratch.socket();
        let Maybe::Present(listener) = bind(&socket).expect("the socket binds")
        else {
            panic!("no other hub serves a fresh socket");
        };
        std::fs::remove_file(&socket).expect("the socket file is removed");
        assert!(
            run_hub(
                &listener,
                &socket,
                Duration::from_millis(10),
                io::sink(),
                Some(echo),
                (
                    super::Spelling::Unicode,
                    super::Pool::new(gandr_surface_dispatcher::Width::SERIAL),
                ),
            )
            .is_ok(),
            "a socket another hand removed is not a fault"
        );
    }

    #[test]
    fn a_relay_carries_a_session_and_its_ending()
    {
        let scratch = Scratch::new(Json("relay"));
        let socket = scratch.socket();
        let hub = hub(&socket);
        let initialize = Json(r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#);
        let shutdown = Json(r#"{"jsonrpc":"2.0","id":2,"method":"shutdown"}"#);
        let exit = Json(r#"{"jsonrpc":"2.0","method":"exit"}"#);
        let mut output = Vec::new();
        let served = relay(
            io::Cursor::new(frames(&[initialize, shutdown, exit]).as_ref().to_vec()),
            &mut output,
            UnixStream::connect(&socket).expect("the hub accepts"),
        )
        .expect("the relay carries the session");
        assert_eq!(served, Served::Clean, "exit after shutdown ends cleanly");
        let mut replies = output.as_slice();
        for id in [1_i32, 2_i32] {
            let Maybe::Present(body) = read_frame(&mut replies).expect("a reply is framed")
            else {
                panic!("each request is answered");
            };
            let reply: Value = serde_json::from_slice(body.as_ref()).expect("a reply is JSON");
            assert_eq!(reply.get("id"), Some(&serde_json::json!(id)));
        }
        assert!(matches!(
            read_frame(&mut replies).expect("the boundary is clean"),
            Maybe::Absent(_)
        ));
        let served = relay(
            io::Cursor::new(frames(&[initialize]).as_ref().to_vec()),
            &mut Vec::new(),
            UnixStream::connect(&socket).expect("the hub accepts"),
        )
        .expect("the relay carries the session");
        assert_eq!(
            served,
            Served::Abrupt,
            "a session closed before shutdown is abrupt"
        );
        let served = relay(
            io::Cursor::new(frames(&[initialize, exit]).as_ref().to_vec()),
            &mut Vec::new(),
            UnixStream::connect(&socket).expect("the hub accepts"),
        )
        .expect("the relay carries the session");
        assert_eq!(
            served,
            Served::Abrupt,
            "an exit no shutdown request preceded is abrupt"
        );
        assert!(
            matches!(
                relay(
                    io::Cursor::new(b"Content-Length: 9\r\n\r\n{".to_vec()),
                    &mut Vec::new(),
                    UnixStream::connect(&socket).expect("the hub accepts"),
                ),
                Err(crate::transport::TransportFault::Truncated)
            ),
            "a client stream broken inside a frame is a fault"
        );
        hub.join().expect("the hub exits");
    }
}
