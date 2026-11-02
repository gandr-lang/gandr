//! The hub's second face: a connection speaking newline-delimited JSON,
//! served over the workspace the editors' connections share; and the relay
//! that carries a client's standard streams to it.
//!
//! # One socket, two faces
//!
//! **Choice.** The model's server is a face of the engine hub, on the hub's own
//! socket. The hub reads a connection's first byte: a language-server frame
//! begins with its `Content-Length` header, a model's message with `{`, and the
//! hub hands the second kind to the face `run_hub` was given. The face is a
//! parameter, so the language server's crate never depends on this one; the
//! driver wires `serve` into the hub it runs. `gandr mcp` reaches the hub as
//! `gandr lsp` does, starting it when none answers.
//!
//! **Alternatives.** A second socket per workspace would double the discovery
//! and the stale-socket probe for one more listener. A separate model server
//! process would hold a second workspace that the editors' edits never reach.
//!
//! **Reversal.** A third protocol whose first byte cannot be told from these
//! two moves the hub to a socket per protocol.
//!
//! # A session across builds
//!
//! **Choice.** The relay reads its client a line at a time and keeps the
//! client's `initialize` and `notifications/initialized` itself. The face holds
//! no documents per connection, so that opening is the whole replay the next
//! build needs, and the hub answers no request for it. Before a line, while
//! none of the client's requests waits for its answer, the relay asks whether
//! the selection moved; the driver then hands the opening and the held line to
//! the selected build, as `gandr lsp` does.
//!
//! **Alternatives.** A replay request to the hub, as the language server's
//! relay sends, would add a method the line face answers for one caller.
//!
//! **Reversal.** A face that keeps per-connection state on the hub moves the
//! replay to the hub, as the language server's.

use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::sync::atomic::AtomicUsize;
use core::sync::atomic::Ordering;
use std::io;
use std::io::BufRead as _;
use std::io::BufReader;
use std::io::Read;
use std::io::Write;
use std::net::Shutdown;
use std::os::unix::net::UnixStream;
use std::sync::Mutex;
use std::sync::MutexGuard;
use std::sync::PoisonError;
use std::sync::mpsc::channel;
use std::thread;

use gandr_surface_lsp::Body;
use gandr_surface_lsp::Carried;
use gandr_surface_lsp::DocumentUri;
use gandr_surface_lsp::Handover;
use gandr_surface_lsp::Peer;
use gandr_surface_lsp::REPLAY;
use gandr_surface_lsp::Workspace;
use serde_json::Value;

use crate::connection::Connection;

/// What the connection's loop acts on next.
enum Event
{
    /// A line the client sent.
    Line(String),
    /// A document a synchronisation published or the hub forgot.
    Changed(DocumentUri),
    /// The client's stream ended.
    Closed,
}

/// Lock `workspace`, taking its state as it is when a holder panicked.
///
/// # Specification
/// trivial.
fn lock(workspace: &Mutex<Workspace>) -> MutexGuard<'_, Workspace>
{
    workspace.lock().unwrap_or_else(PoisonError::into_inner)
}

/// Write `messages`, one line each, to `writing`.
///
/// # Specification
/// trivial.
fn send(
    writing: &mut UnixStream,
    messages: &[Value],
) -> io::Result<()>
{
    let mut line = String::new();
    for message in messages {
        line.clear();
        core::fmt::Write::write_fmt(&mut line, format_args!("{message}\n"))
            .map_err(io::Error::other)?;
        writing.write_all(line.as_bytes())?;
    }
    writing.flush()
}

/// Serve the Model Context Protocol on the connection `reading` buffers, as
/// `peer`, over `workspace`: the hub's line face.
///
/// # Specification
/// - requires: `reading` is the connection the hub accepted, its first byte
///   `{`.
/// - ensures: every line the client sends is answered as [`Connection::handle`]
///   states, a line that is not JSON with a parse error; every document a
///   synchronisation publishes or the hub forgets reaches the client as the
///   notifications [`Connection::changed`] owes it. Replies and notifications
///   are written one line each, in the order the connection made them. The face
///   returns when the client's stream ends or a write fails.
/// - provides: `gandr serve`'s Model Context Protocol face.
/// - fails: never; a fault ends the connection.
/// - panics: none.
/// - executable: none — the effects are lines on a socket and a watcher in a
///   workspace other connections change concurrently.
///
/// # Adequacy
/// - hypothesis: L3 — through a running hub, an edit by an editor's connection
///   notifies a subscribed model connection in both subscription styles and
///   leaves an unsubscribed resource silent, and a tool call reads the edit.
/// - witness: `face::tests::an_edit_through_the_hub_notifies_its_subscribers`
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        pool_only_threads,
        reason = "io: the change forwarder and the model's line reader each block on their channel or socket for the connection's life"
    )
)]
#[inline]
pub fn serve(
    reading: &mut BufReader<UnixStream>,
    peer: Peer,
    workspace: &Mutex<Workspace>,
)
{
    let Ok(mut writing) = reading.get_ref().try_clone()
    else {
        return;
    };
    let (events, inbox) = channel();
    let (watcher, changes) = channel::<DocumentUri>();
    lock(workspace).watch(peer, watcher);
    let forward = events.clone();
    drop(thread::spawn(move || {
        for uri in changes {
            if forward.send(Event::Changed(uri)).is_err() {
                break;
            }
        }
    }));
    thread::scope(|scope| {
        drop(scope.spawn(move || {
            let mut line = String::new();
            while reading.read_line(&mut line).is_ok_and(|read| read != 0) {
                if events
                    .send(Event::Line(core::mem::take(&mut line)))
                    .is_err()
                {
                    return;
                }
            }
            drop(events.send(Event::Closed));
        }));
        let mut connection = Connection::default();
        let mut writable = true;
        for event in &inbox {
            let messages = match event {
                Event::Closed => break,
                Event::Line(line) if line.trim().is_empty() => continue,
                Event::Line(line) => serde_json::from_str::<Value>(&line).map_or_else(
                    |_| Vec::from([Connection::unreadable()]),
                    |message| connection.handle(&mut lock(workspace), &message),
                ),
                Event::Changed(uri) => connection.changed(&uri),
            };
            if writable && send(&mut writing, &messages).is_err() {
                // The reader is woken by the shutdown and ends the loop.
                writable = false;
                drop(writing.shutdown(Shutdown::Both));
            }
        }
    });
}

/// How a relayed model session ended.
#[derive(Debug, Eq, PartialEq)]
pub enum Relayed
{
    /// The input ended, and the hub closed once it had answered it.
    Ended,
    /// The selection moved to another build: the session goes on in that
    /// build's image, which takes the handover.
    Switched(Handover),
}

/// How a line reads to a relay, its payload skipped.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Line
{
    /// The client's `initialize` request.
    Initialize,
    /// The client's `notifications/initialized`.
    Initialized,
    /// Another request.
    Request,
    /// A response under the identifier [`REPLAY`].
    Replay,
    /// A response under another identifier.
    Answer,
    /// A notification, or no message.
    Other,
}

/// The envelope of a line, its payload skipped unread.
#[derive(serde::Deserialize)]
struct Envelope<'line>
{
    /// The identifier, when the message carries one.
    #[serde(default)]
    id: Option<Value>,
    /// The method, when the message calls one.
    #[serde(default, borrow)]
    method: Option<alloc::borrow::Cow<'line, str>>,
}

/// One line of the wire, its terminator included or not.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Message<'line>(&'line [u8]);

impl Message<'_>
{
    /// How the line reads to a relay.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a message with an identifier and a method is a request, the
    ///   `initialize` one told apart; one with an identifier and no method is
    ///   an answer, the one to [`REPLAY`] told apart;
    ///   `notifications/initialized` is told apart from every other line.
    /// - panics: none.
    /// - executable: none — a predicate would read the envelope a second time,
    ///   which is the whole of the function.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the relay keeps the opening, counts the pending
    ///   requests and drops the replay's answer.
    /// - witness: `face::tests::a_relay_switches_once_nothing_is_pending`
    fn read(self) -> Line
    {
        match serde_json::from_slice::<Envelope<'_>>(self.0) {
            Ok(Envelope {
                id: Some(_),
                method: Some(method),
            }) if method == "initialize" => Line::Initialize,
            Ok(Envelope {
                id: Some(_),
                method: Some(_),
            }) => Line::Request,
            Ok(Envelope {
                id: Some(id),
                method: None,
            }) if id.as_str() == Some(REPLAY) => Line::Replay,
            Ok(Envelope {
                id: Some(_),
                method: None,
            }) => Line::Answer,
            Ok(Envelope {
                id: None,
                method: Some(method),
            }) if method == "notifications/initialized" => Line::Initialized,
            Ok(_) | Err(_) => Line::Other,
        }
    }

    /// The line as a replay keeps it, read as `read`: its terminator dropped,
    /// and an `initialize` request under the identifier [`REPLAY`].
    ///
    /// # Specification
    /// trivial.
    fn kept(
        self,
        read: Line,
    ) -> Body
    {
        let message = self.0.trim_ascii_end();
        if read != Line::Initialize {
            return Body::from(message.to_vec());
        }
        serde_json::from_slice::<Value>(message)
            .ok()
            .and_then(|mut request| {
                *request.get_mut("id")? = Value::from(REPLAY);
                serde_json::to_vec(&request).ok()
            })
            .map_or_else(|| Body::from(message.to_vec()), Body::from)
    }
}

/// Carry lines between a client and the hub at the other end of `hub`, until
/// the hub closes the connection or the session moves to another build.
///
/// `opening` goes to the hub first, a line each. Then every line `input` holds
/// goes to the hub, and each line the hub sends goes to `output`, until the hub
/// closes or `moved` answers that the session belongs to another build.
///
/// # Specification
/// - requires: nothing.
/// - ensures: lines pass unchanged and in order both ways, `output` flushed
///   after each, but for the hub's answers to the requests in `opening`, which
///   are dropped. Once `input` ends or fails, the hub's end is shut for
///   writing, and the session is [`Relayed::Ended`]. `moved` is asked before
///   each line from `input` while none of the client's requests waits for its
///   answer; once it answers `true`, that line and every byte read past it are
///   held, the hub's end is shut for writing, and the session ends
///   [`Relayed::Switched`] with the client's opening and the held bytes. The
///   opening is `opening` until `input` carries `initialize`, then that request
///   under the identifier [`REPLAY`] and the `notifications/initialized` after
///   it.
/// - provides: `gandr mcp`, a client's whole session with a hub, across builds.
/// - fails: when a line from the hub cannot be read or written to `output`.
/// - panics: none.
/// - executable: none — the bytes go to a socket and to `output`, which the
///   call consumes or writes but cannot read back.
///
/// # Errors
/// The error writing `opening` to the hub, reading the hub's lines or writing
/// them to `output`.
///
/// # Adequacy
/// - hypothesis: L3 — a session of discovery and a tool call is carried whole
///   through a running hub; a switch waits for the client's pending request and
///   hands over the line it held with the client's opening.
/// - witness: `face::tests::a_relay_carries_a_model_session`
/// - witness: `face::tests::a_relay_switches_once_nothing_is_pending`
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        pool_only_threads,
        reason = "io: the relay's input thread blocks on the model's lines for the session's life"
    )
)]
#[inline]
pub fn relay<Input, Output, Moved>(
    input: Input,
    output: &mut Output,
    hub: UnixStream,
    opening: &[Body],
    mut moved: Moved,
) -> io::Result<Relayed>
where
    Input: Read + Send + 'static,
    Output: Write,
    Moved: FnMut() -> bool + Send + 'static,
{
    let mut forward = hub.try_clone()?;
    let mut replayed = 0_usize;
    for body in opening {
        if matches!(
            Message(body.as_ref()).read(),
            Line::Initialize | Line::Request
        ) {
            replayed = replayed.saturating_add(1);
        }
        forward.write_all(body.as_ref())?;
        forward.write_all(b"\n")?;
    }
    let pending = Arc::new(AtomicUsize::new(replayed));
    let waiting = Arc::clone(&pending);
    let mut opened = opening.to_vec();
    let (switching, switched) = channel::<Handover>();
    drop(thread::spawn(move || {
        let mut input = BufReader::new(input);
        let mut held = Vec::new();
        while input
            .read_until(b'\n', &mut held)
            .is_ok_and(|read| read != 0)
        {
            if waiting.load(Ordering::Acquire) == 0 && moved() {
                let mut carried = core::mem::take(&mut held);
                carried.extend_from_slice(input.buffer());
                // The handover is waiting before the hub closes, so the
                // reader finds it at the end of the hub's lines.
                drop(switching.send(Handover::new(opened, Carried(carried))));
                break;
            }
            let read = Message(&held).read();
            match read {
                Line::Initialize => {
                    opened.clear();
                    opened.push(Message(&held).kept(read));
                },
                Line::Initialized => opened.push(Message(&held).kept(read)),
                Line::Request | Line::Replay | Line::Answer | Line::Other => {},
            }
            if matches!(read, Line::Initialize | Line::Request) {
                let _counted = waiting.fetch_add(1, Ordering::AcqRel);
            }
            if forward.write_all(&held).is_err() {
                break;
            }
            held.clear();
        }
        drop(forward.shutdown(Shutdown::Write));
    }));
    let mut reading = BufReader::new(hub);
    let mut answer = Vec::new();
    while reading.read_until(b'\n', &mut answer)? != 0 {
        let read = Message(&answer).read();
        if matches!(read, Line::Replay | Line::Answer) {
            let _answered = pending.try_update(Ordering::AcqRel, Ordering::Acquire, |count| {
                Some(count.saturating_sub(1))
            });
        }
        if read == Line::Replay && replayed > 0 {
            replayed = replayed.saturating_sub(1);
        }
        else {
            output.write_all(&answer)?;
            output.flush()?;
        }
        answer.clear();
    }
    Ok(switched
        .try_recv()
        .map_or(Relayed::Ended, Relayed::Switched))
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;
    use alloc::sync::Arc;
    use core::sync::atomic::AtomicBool;
    use core::sync::atomic::Ordering;
    use core::time::Duration;
    use std::io;
    use std::io::BufRead as _;
    use std::io::BufReader;
    use std::io::Write as _;
    use std::os::unix::net::UnixStream;
    use std::path::PathBuf;
    use std::thread;
    use std::thread::JoinHandle;

    use gandr_surface_lsp::Body;
    use gandr_surface_lsp::bind;
    use gandr_surface_lsp::read_frame;
    use gandr_surface_lsp::run_hub;
    use gandr_surface_lsp::write_frame;
    use quenchant_shape::shape::Maybe;
    use serde_json::Value;
    use serde_json::json;

    use super::Relayed;
    use super::relay;
    use super::serve;

    /// A scratch directory holding one hub's socket, removed when dropped.
    #[repr(transparent)]
    struct Scratch(PathBuf);

    impl Scratch
    {
        /// A fresh directory named for `test` and this process, kept short:
        /// a socket path inside it must fit the platform's limit.
        ///
        /// # Specification
        /// trivial.
        fn new(test: &Value) -> Self
        {
            let directory = std::env::temp_dir().join(alloc::format!(
                "gm-{}-{}",
                std::process::id(),
                test.as_str().unwrap_or_default()
            ));
            drop(std::fs::remove_dir_all(&directory));
            std::fs::create_dir_all(&directory).expect("the scratch directory is made");
            Self(directory)
        }

        /// The socket inside the directory.
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

    /// A hub serving `scratch`'s socket with this crate's line face,
    /// lingering 100 ms.
    ///
    /// # Specification
    /// trivial.
    fn hub(scratch: &Scratch) -> JoinHandle<()>
    {
        let socket = scratch.socket();
        let Maybe::Present(listener) = bind(&socket).expect("the socket binds")
        else {
            panic!("no other hub serves a fresh socket");
        };
        thread::spawn(move || {
            run_hub(
                &listener,
                &socket,
                Duration::from_millis(100),
                io::sink(),
                Some(serve),
                gandr_surface_lsp::Workspace::spelled(gandr_surface_lsp::Spelling::Unicode),
            )
            .expect("the hub serves");
        })
    }

    /// An editor's connection: Language Server Protocol frames.
    struct Editor
    {
        /// The end it writes.
        writing: UnixStream,
        /// The end it reads.
        reading: BufReader<UnixStream>,
    }

    impl Editor
    {
        /// An initialised editor connection to `scratch`'s hub.
        ///
        /// # Specification
        /// trivial.
        fn new(scratch: &Scratch) -> Self
        {
            Self::declaring(scratch, &json!({}))
        }

        /// An editor connection to `scratch`'s hub, initialised declaring
        /// `capabilities`.
        ///
        /// # Specification
        /// trivial.
        fn declaring(
            scratch: &Scratch,
            capabilities: &Value,
        ) -> Self
        {
            let writing = UnixStream::connect(scratch.socket()).expect("the hub accepts");
            let reading = BufReader::new(writing.try_clone().expect("the stream clones"));
            let mut editor = Self { writing, reading };
            editor.send(
                &json!({ "jsonrpc": "2.0", "id": 1_i32, "method": "initialize",
                "params": { "capabilities": capabilities } }),
            );
            drop(editor.receive());
            editor
        }

        /// Send `message`, framed.
        ///
        /// # Specification
        /// trivial.
        fn send(
            &mut self,
            message: &Value,
        )
        {
            write_frame(
                &mut self.writing,
                &Body::from(message.to_string().into_bytes()),
            )
            .expect("the hub reads");
        }

        /// The next frame the hub sent, parsed.
        ///
        /// # Specification
        /// trivial.
        fn receive(&mut self) -> Value
        {
            let Maybe::Present(body) = read_frame(&mut self.reading).expect("a frame")
            else {
                panic!("the hub closed the editor's connection");
            };
            serde_json::from_slice(body.as_ref()).expect("JSON")
        }

        /// Synchronise `uri` to `version` with `text`, opening it at the first
        /// version, and wait for its publication.
        ///
        /// # Specification
        /// trivial.
        fn edit(
            &mut self,
            uri: &Value,
            version: &Value,
            text: &Value,
        )
        {
            let message = if version == &json!(1_i32) {
                json!({ "jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                    "textDocument": { "uri": uri, "languageId": "gandr", "version": version, "text": text } } })
            }
            else {
                json!({ "jsonrpc": "2.0", "method": "textDocument/didChange", "params": {
                    "textDocument": { "uri": uri, "version": version },
                    "contentChanges": [{ "text": text }] } })
            };
            self.send(&message);
            assert_eq!(self.receive().pointer("/params/version"), Some(version));
        }
    }

    /// A model's connection: one JSON message per line.
    struct Model
    {
        /// The end it writes.
        writing: UnixStream,
        /// The end it reads.
        reading: BufReader<UnixStream>,
    }

    impl Model
    {
        /// A model connection to `scratch`'s hub.
        ///
        /// # Specification
        /// trivial.
        fn new(scratch: &Scratch) -> Self
        {
            let writing = UnixStream::connect(scratch.socket()).expect("the hub accepts");
            let reading = BufReader::new(writing.try_clone().expect("the stream clones"));
            Self { writing, reading }
        }

        /// The next line the hub sends after `message`, parsed.
        ///
        /// # Specification
        /// trivial.
        fn ask(
            &mut self,
            message: &Value,
        ) -> Value
        {
            writeln!(self.writing, "{message}").expect("the hub reads");
            self.receive()
        }

        /// The next line the hub sent, parsed.
        ///
        /// # Specification
        /// trivial.
        fn receive(&mut self) -> Value
        {
            let mut line = String::new();
            assert_ne!(
                self.reading.read_line(&mut line).expect("a line"),
                0_usize,
                "the hub closed the model's connection"
            );
            serde_json::from_str(&line).expect("JSON")
        }
    }

    #[test]
    fn an_edit_through_the_hub_notifies_its_subscribers()
    {
        let scratch = Scratch::new(&json!("notify"));
        let hub = hub(&scratch);
        let mut editor = Editor::new(&scratch);
        let (first, second, third) = (
            json!("file:///tmp/first.gandr"),
            json!("file:///tmp/second.gandr"),
            json!("file:///tmp/third.gandr"),
        );
        for uri in [&first, &second, &third] {
            editor.edit(uri, &json!(1_i32), &json!("def f = 42 ;\n"));
        }
        let mut model = Model::new(&scratch);
        let subscribed = model.ask(
            &json!({ "jsonrpc": "2.0", "id": 1_i32, "method": "resources/subscribe",
            "params": { "uri": "gandr:///tmp/first.gandr/diagnostics" } }),
        );
        assert_eq!(
            subscribed.pointer("/result/resultType"),
            Some(&json!("complete"))
        );
        let acknowledged = model.ask(&json!({ "jsonrpc": "2.0", "id": 2_i32, "method": "subscriptions/listen",
            "params": {
                "_meta": { "io.modelcontextprotocol/protocolVersion": crate::MODERN },
                "notifications": { "resourceSubscriptions": ["gandr:///tmp/second.gandr/diagnostics"] },
            } }));
        assert_eq!(
            acknowledged.get("method"),
            Some(&json!("notifications/subscriptions/acknowledged"))
        );
        editor.edit(&third, &json!(2_i32), &json!("def g = 1 ;\n"));
        editor.edit(&first, &json!(2_i32), &json!("def g = missing ;\n"));
        assert_eq!(
            model.receive(),
            json!({ "jsonrpc": "2.0", "method": "notifications/resources/updated",
                "params": { "uri": "gandr:///tmp/first.gandr/diagnostics" } }),
            "the legacy subscription hears its document, and the unsubscribed edit before it nothing"
        );
        editor.edit(&second, &json!(2_i32), &json!("def g = 1 ;\n"));
        assert_eq!(
            model.receive(),
            json!({ "jsonrpc": "2.0", "method": "notifications/resources/updated",
                "params": { "_meta": { "io.modelcontextprotocol/subscriptionId": 2_i32 },
                    "uri": "gandr:///tmp/second.gandr/diagnostics" } }),
            "the listening stream hears its document under its identifier"
        );
        let read = model.ask(
            &json!({ "jsonrpc": "2.0", "id": 3_i32, "method": "tools/call",
            "params": { "name": "diagnostics", "arguments": { "uri": first } } }),
        );
        assert_eq!(
            read.pointer("/result/structuredContent/version"),
            Some(&json!(2_i32))
        );
        assert_eq!(
            read.pointer("/result/structuredContent/diagnostics")
                .and_then(Value::as_array)
                .map(alloc::vec::Vec::len),
            Some(1_usize),
            "the model reads the editor's edit at its version"
        );
        drop(model);
        drop(editor);
        hub.join().expect("the hub exits");
    }

    #[test]
    fn a_kept_fill_asks_its_editor_for_lenses_again()
    {
        let scratch = Scratch::new(&json!("refresh"));
        let hub = hub(&scratch);
        let mut editor = Editor::declaring(
            &scratch,
            &json!({ "workspace": { "codeLens": { "refreshSupport": true } } }),
        );
        let uri = json!("file:///tmp/refresh.gandr");
        editor.edit(
            &uri,
            &json!(1_i32),
            &json!("def f : Integer ;\ndef f = missing ;\n"),
        );
        let mut model = Model::new(&scratch);
        let kept = model.ask(
            &json!({ "jsonrpc": "2.0", "id": 1_i32, "method": "tools/call",
            "params": { "name": "propose", "arguments": { "uri": uri, "version": 1_i32,
                "range": { "start": { "line": 1_u32, "character": 8_u32 },
                    "end": { "line": 1_u32, "character": 15_u32 } },
                "text": "42" } } }),
        );
        assert_eq!(
            kept.pointer("/result/structuredContent/kept"),
            Some(&json!(true))
        );
        assert_eq!(
            editor.receive(),
            json!({ "jsonrpc": "2.0", "id": "workspace/codeLens/refresh/1",
                "method": "workspace/codeLens/refresh" }),
            "the editor holding the document is asked for its lenses again"
        );
        drop(model);
        drop(editor);
        hub.join().expect("the hub exits");
    }

    #[test]
    fn a_relay_carries_a_model_session()
    {
        let scratch = Scratch::new(&json!("relay"));
        let hub = hub(&scratch);
        let session = alloc::format!(
            "{}\n{}\n",
            json!({ "jsonrpc": "2.0", "id": 1_i32, "method": "server/discover" }),
            json!({ "jsonrpc": "2.0", "id": 2_i32, "method": "tools/call",
                "params": { "name": "documents", "arguments": {} } }),
        );
        let mut output = alloc::vec::Vec::new();
        let relayed = relay(
            io::Cursor::new(session.into_bytes()),
            &mut output,
            UnixStream::connect(scratch.socket()).expect("the hub accepts"),
            &[],
            || false,
        )
        .expect("the relay carries the session");
        assert_eq!(relayed, Relayed::Ended);
        let replies: alloc::vec::Vec<Value> = String::from_utf8(output)
            .expect("UTF-8")
            .lines()
            .map(|line| serde_json::from_str(line).expect("JSON"))
            .collect();
        assert_eq!(replies.len(), 2_usize, "{replies:?}");
        assert_eq!(
            replies[0].pointer("/result/supportedVersions/0"),
            Some(&json!(crate::MODERN))
        );
        assert_eq!(
            replies[1].pointer("/result/structuredContent/documents"),
            Some(&json!([]))
        );
        hub.join().expect("the hub exits");
    }

    /// A relay asked to move hands over the client's opening and the line it
    /// held, and the next relay replays the opening, drops its answer, and
    /// carries the held line on.
    #[test]
    fn a_relay_switches_once_nothing_is_pending()
    {
        let scratch = Scratch::new(&json!("switch"));
        let hub = hub(&scratch);
        let (mut client, input) = UnixStream::pair().expect("a pair of sockets");
        let (output, answers) = UnixStream::pair().expect("a pair of sockets");
        let flag = Arc::new(AtomicBool::new(false));
        let asked = Arc::clone(&flag);
        let socket = scratch.socket();
        let first = thread::spawn(move || {
            let mut output = output;
            relay(
                input,
                &mut output,
                UnixStream::connect(socket).expect("the hub accepts"),
                &[],
                move || asked.load(Ordering::Acquire),
            )
        });
        let initialize = json!({ "jsonrpc": "2.0", "id": 1_i32, "method": "initialize",
            "params": { "protocolVersion": "2025-06-18", "capabilities": {} } });
        let initialized = json!({ "jsonrpc": "2.0", "method": "notifications/initialized" });
        let held = json!({ "jsonrpc": "2.0", "id": 2_i32, "method": "server/discover" });
        writeln!(client, "{initialize}\n{initialized}").expect("the opening is written");
        let mut reading = BufReader::new(answers);
        let mut opened = String::new();
        let _read = reading
            .read_line(&mut opened)
            .expect("the opening is answered");
        assert!(opened.contains(r#""id":1"#), "{opened}");
        flag.store(true, Ordering::Release);
        writeln!(client, "{held}").expect("the held line is written");
        let Relayed::Switched(handover) = first
            .join()
            .expect("the relay ends")
            .expect("the relay carries the session")
        else {
            panic!("the relay switches once asked");
        };
        let replay: alloc::vec::Vec<Value> = handover
            .replay()
            .iter()
            .map(|body| serde_json::from_slice(body.as_ref()).expect("JSON"))
            .collect();
        let mut replayed = initialize.clone();
        replayed["id"] = json!(gandr_surface_lsp::REPLAY);
        assert_eq!(replay, [replayed, initialized]);
        assert_eq!(
            handover.carried().0,
            alloc::format!("{held}\n").into_bytes()
        );
        drop(client);
        let mut output = alloc::vec::Vec::new();
        let next = relay(
            io::Cursor::new(handover.carried().0.clone()),
            &mut output,
            UnixStream::connect(scratch.socket()).expect("the hub accepts"),
            handover.replay(),
            || false,
        )
        .expect("the next relay carries the session");
        assert_eq!(next, Relayed::Ended);
        let replies: alloc::vec::Vec<Value> = String::from_utf8(output)
            .expect("UTF-8")
            .lines()
            .map(|line| serde_json::from_str(line).expect("JSON"))
            .collect();
        assert_eq!(
            replies
                .iter()
                .map(|reply| reply.get("id").cloned())
                .collect::<alloc::vec::Vec<Option<Value>>>(),
            [Some(json!(2_i32))],
            "the held line is answered, and the replay's answer dropped: {replies:?}"
        );
        drop(reading);
        hub.join().expect("the hub exits");
    }
}
