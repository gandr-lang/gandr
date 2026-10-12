//! The engine hub: one process serving every connection to a workspace over
//! a Unix domain socket, the connections sharing the documents they open.
//!
//! The hub accepts connections until none has been open for its linger, then
//! removes its socket and returns. Each connection runs on a reader thread,
//! which handles the frames it reads over the one [`Workspace`], and a writer
//! thread, which drains the connection's outbox: its own answers and every
//! publication another connection's synchronisation made for a document it
//! holds open. A relay is the client's end: it carries frames between an
//! editor's standard streams and the hub's socket.

use alloc::sync::Arc;
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
use std::sync::mpsc::channel;
use std::thread;
use std::time::Instant;

use anodized::spec;
use quenchant_shape::shape::Maybe;

use crate::rpc::Incoming;
use crate::rpc::Outgoing;
use crate::rpc::classify;
use crate::server::Flow;
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
fn lock<Held>(mutex: &Mutex<Held>) -> MutexGuard<'_, Held>
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
        | Ok(listener) => Ok(Maybe::Present(listener)),
        | Err(error) if error.kind() == io::ErrorKind::AddrInUse => {
            if UnixStream::connect(socket).is_ok() {
                return Ok(Maybe::Absent(bind::Absent::Served));
            }
            std::fs::remove_file(socket)?;
            UnixListener::bind(socket).map(Maybe::Present)
        },
        | Err(error) => Err(error),
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
///   one is given. Every other accepted connection is served as
///   [`Server::handle`] and [`Server::admit`] state, over the documents every
///   connection shares: its answers and publications reach it in the order its
///   handling made them, interleaved with the publications other connections'
///   synchronisations made for documents it holds, and each synchronisation's
///   timing line goes to `log`. A connection ends at `exit`, at the end of its
///   stream, or at a stream fault; it then holds nothing and its socket is
///   shut. The hub returns once no connection has been open for `linger`, its
///   socket file removed first so a late client starts a fresh hub.
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
/// - hypothesis: L3 — two connections share one document's edits and
///   publications; one leaving leaves the other served; the hub, left with
///   none, removes its socket and returns.
/// - witness: `hub::tests::two_clients_share_one_document`
/// - witness: `hub::tests::a_hub_left_alone_exits_after_its_linger`
/// - witness: `hub::tests::a_line_connection_reaches_the_second_face`
#[inline]
pub fn run_hub<Log>(
    listener: &UnixListener,
    socket: &Path,
    linger: Duration,
    log: Log,
    lines: Option<Face>,
) -> Result<(), io::Error>
where
    Log: Write + Send + 'static,
{
    listener.set_nonblocking(true)?;
    let workspace = Arc::new(Mutex::new(Workspace::default()));
    let log = Arc::new(Mutex::new(log));
    let open = Arc::new(AtomicU64::new(0));
    let mut peers = 0_u64;
    let mut quiet_since = Instant::now();
    let mut start = |stream: UnixStream| -> Result<(), io::Error> {
        stream.set_nonblocking(false)?;
        peers = peers.saturating_add(1);
        let _opened = open.fetch_add(1, Ordering::SeqCst);
        let (workspace, log, open) = (Arc::clone(&workspace), Arc::clone(&log), Arc::clone(&open));
        let peer = Peer::from(peers);
        drop(thread::spawn(move || {
            connection(stream, peer, &workspace, &log, lines);
            let _closed = open.fetch_sub(1, Ordering::SeqCst);
        }));
        Ok(())
    };
    loop {
        match listener.accept() {
            | Ok((stream, _address)) => start(stream)?,
            | Err(error) if error.kind() == io::ErrorKind::WouldBlock => {
                if open.load(Ordering::SeqCst) != 0 {
                    quiet_since = Instant::now();
                }
                else if quiet_since.elapsed() >= linger {
                    break;
                }
                thread::sleep(POLL);
            },
            | Err(error) => return Err(error),
        }
    }
    match std::fs::remove_file(socket) {
        | Ok(()) => {},
        | Err(error) if error.kind() == io::ErrorKind::NotFound => {},
        | Err(error) => return Err(error),
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
/// - witness: `hub::tests::two_clients_share_one_document`
fn connection<Log>(
    stream: UnixStream,
    peer: Peer,
    workspace: &Mutex<Workspace>,
    log: &Mutex<Log>,
    lines: Option<Face>,
) where
    Log: Write,
{
    let mut reading = BufReader::new(stream);
    if let Some(face) = lines
        && reading
            .fill_buf()
            .is_ok_and(|bytes| bytes.first() == Some(&b'{'))
    {
        face(&mut reading, peer, workspace);
        lock(workspace).depart(peer);
        drop(reading.get_ref().shutdown(std::net::Shutdown::Both));
        return;
    }
    let (outbox, inbox) = channel::<Outgoing>();
    lock(workspace).join(peer, outbox.clone());
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
    if writer.is_ok() {
        while let Ok(Maybe::Present(body)) = read_frame(&mut reading) {
            let mut held = lock(workspace);
            let mut outcome = server.handle(&mut held, &body);
            for message in outcome.messages {
                drop(outbox.send(message));
            }
            for message in server.admit(&mut held, &mut outcome.log) {
                drop(outbox.send(message));
            }
            drop(held);
            let mut written = lock(log);
            for line in &outcome.log {
                drop(writeln!(written, "{line}"));
            }
            drop(written);
            if matches!(outcome.flow, Flow::Exit(_)) {
                break;
            }
        }
    }
    lock(workspace).depart(peer);
    drop(outbox);
    if let Ok(writer) = writer {
        drop(writer.join());
    }
    drop(reading.get_ref().shutdown(std::net::Shutdown::Both));
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
                | Ok(Maybe::Present(body)) => body,
                | Ok(Maybe::Absent(_closed)) => break Ok(Served::Abrupt),
                | Err(fault) => break Err(fault),
            };
            let exit = match classify(&body) {
                | Ok(Incoming::Request { ref method, .. }) => {
                    shut |= method.as_ref() == "shutdown";
                    false
                },
                | Ok(Incoming::Notification { ref method, .. }) => method.as_ref() == "exit",
                | Ok(Incoming::Response) | Err(_) => false,
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
    use quenchant_shape::shape::Maybe;
    use serde_json::Value;

    use super::bind;
    use super::relay;
    use super::run_hub;
    use super::socket_for;
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
            let writing = UnixStream::connect(socket).expect("the hub accepts");
            let reading = BufReader::new(writing.try_clone().expect("the stream clones"));
            let mut client = Self { writing, reading };
            client.send(Json(
                r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#,
            ));
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
        /// - witness: `hub::tests::two_clients_share_one_document`
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
    fn two_clients_share_one_document()
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
        assert_eq!(
            first.published(),
            Some(serde_json::json!(1_i32)),
            "the other holder hears the second open"
        );
        first.send(Json(
            r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{
                "textDocument":{"uri":"file:///tmp/shared.gandr","version":2},
                "contentChanges":[{"text":"def g = 1 ;\n"}]}}"#,
        ));
        assert_eq!(first.published(), Some(serde_json::json!(2_i32)));
        assert_eq!(second.published(), Some(serde_json::json!(2_i32)));
        second.send(Json(
            r#"{"jsonrpc":"2.0","id":5,"method":"textDocument/hover","params":{
                "textDocument":{"uri":"file:///tmp/shared.gandr"},"position":{"line":0,"character":4}}}"#,
        ));
        assert_eq!(
            second.receive().pointer("/result/contents/value"),
            Some(&serde_json::json!("```gandr\ng : Integer\n```")),
            "an edit through one client is visible to the other's query"
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
