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

use alloc::string::String;
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

use gandr_surface_lsp::DocumentUri;
use gandr_surface_lsp::Peer;
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
    for message in messages {
        let mut line = message.to_string();
        line.push('\n');
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
                | Event::Closed => break,
                | Event::Line(line) if line.trim().is_empty() => continue,
                | Event::Line(line) => match serde_json::from_str::<Value>(&line) {
                    | Ok(message) => connection.handle(&mut lock(workspace), &message),
                    | Err(_) => Vec::from([Connection::unreadable()]),
                },
                | Event::Changed(uri) => connection.changed(&uri),
            };
            if writable && send(&mut writing, &messages).is_err() {
                // The reader is woken by the shutdown and ends the loop.
                writable = false;
                drop(writing.shutdown(Shutdown::Both));
            }
        }
    });
}

/// Carry lines between a client and the hub at the other end of `hub`: every
/// byte `input` holds to the hub, each line the hub sends to `output`, until
/// the hub closes the connection.
///
/// # Specification
/// - requires: nothing.
/// - ensures: bytes pass unchanged and in order both ways, `output` flushed
///   after each line. Once `input` ends or fails, the hub's end is shut for
///   writing.
/// - provides: `gandr mcp`, a client's whole session with a hub.
/// - fails: when a line from the hub cannot be read or written to `output`.
/// - panics: none.
/// - executable: none — the bytes go to a socket and to `output`, which the
///   call consumes or writes but cannot read back.
///
/// # Errors
/// The error reading the hub's lines or writing them to `output`.
///
/// # Adequacy
/// - hypothesis: L3 — a session of discovery and a tool call is carried whole
///   through a running hub.
/// - witness: `face::tests::a_relay_carries_a_model_session`
#[inline]
pub fn relay<Input, Output>(
    input: Input,
    output: &mut Output,
    hub: UnixStream,
) -> io::Result<()>
where
    Input: Read + Send + 'static,
    Output: Write,
{
    let mut forward = hub.try_clone()?;
    drop(thread::spawn(move || {
        let mut input = input;
        drop(io::copy(&mut input, &mut forward));
        drop(forward.shutdown(Shutdown::Write));
    }));
    let mut reading = BufReader::new(hub);
    let mut line = String::new();
    while reading.read_line(&mut line)? != 0 {
        output.write_all(line.as_bytes())?;
        output.flush()?;
        line.clear();
    }
    Ok(())
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;
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
            let writing = UnixStream::connect(scratch.socket()).expect("the hub accepts");
            let reading = BufReader::new(writing.try_clone().expect("the stream clones"));
            let mut editor = Self { writing, reading };
            editor.send(
                &json!({ "jsonrpc": "2.0", "id": 1_i32, "method": "initialize", "params": {} }),
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
        relay(
            io::Cursor::new(session.into_bytes()),
            &mut output,
            UnixStream::connect(scratch.socket()).expect("the hub accepts"),
        )
        .expect("the relay carries the session");
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
}
