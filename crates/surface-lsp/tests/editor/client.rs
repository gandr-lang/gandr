//! The client's side of a session: a connection an editor holds, driven one
//! message at a time. A served connection is `serve` itself, on a thread of
//! its own over in-memory framed streams, so every answer a session reads is
//! one the transport wrote. A joined connection is driven in process exactly
//! as `serve` drives one, over a workspace other connections may join, as the
//! hub's are; when kept, its exchange replays over framed streams.

use alloc::rc::Rc;
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::cell::RefCell;
use std::io;
use std::io::BufRead as _;
use std::sync::Mutex;
use std::sync::PoisonError;
use std::sync::mpsc;
use std::thread::JoinHandle;

use anodized::spec;
use gandr_surface_lsp::Body;
use gandr_surface_lsp::Peer;
use gandr_surface_lsp::Served;
use gandr_surface_lsp::Server;
use gandr_surface_lsp::TransportFault;
use gandr_surface_lsp::Workspace;
use gandr_surface_lsp::read_frame;
use gandr_surface_lsp::serve;
use gandr_surface_lsp::write_frame;
use quenchant_shape::shape::Maybe;
use serde_json::Value;
use serde_json::json;

/// The name of a protocol method.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Method(pub &'static str);

/// Whether a joined client keeps its exchange for a replay over streams.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Record
{
    /// Every message sent and received is kept.
    Kept,
    /// Nothing is kept: the client answers one question and is dropped.
    Dropped,
}

/// A workspace the connections over it share, and how many have joined it.
#[derive(Default)]
struct Shared
{
    /// The workspace.
    workspace: Workspace,
    /// How many connections have joined, each numbered by its turn.
    joined: u64,
}

/// One connection, as an editor holds one.
pub struct Client
{
    /// How the connection is reached.
    connection: Connection,
    /// The id of the latest request.
    requests: i64,
}

/// How a client reaches its connection.
enum Connection
{
    /// `serve` on a thread of its own, over in-memory framed streams.
    Served(Streams),
    /// A connection driven in process, over a workspace others may join.
    Joined(Joined),
}

/// Bytes on a framed stream: whole frames, back to back.
#[repr(transparent)]
#[derive(Default)]
struct Stream(Vec<u8>);

/// The client's ends of the in-memory framed streams a `serve` loop runs
/// over.
struct Streams
{
    /// Each frame the loop is to read, whole.
    frames: mpsc::Sender<Stream>,
    /// A signal each time the loop asks for a frame it has not been sent: by
    /// then it has written everything it owes the frames before.
    waiting: mpsc::Receiver<()>,
    /// What the loop wrote that the client has not read yet.
    written: Arc<Mutex<Stream>>,
    /// The loop, which ends at `exit` or when the client drops the frames.
    serving: JoinHandle<Result<Served, TransportFault>>,
}

/// The loop's end of the client's frames: each handed over whole, and a
/// signal sent each time the loop asks for one it does not have.
struct Inbox
{
    /// The frames the client sends.
    frames: mpsc::Receiver<Stream>,
    /// Where the loop's requests for a frame are signalled.
    waiting: mpsc::Sender<()>,
    /// The frame being read.
    frame: Stream,
    /// How many of its bytes the loop has consumed.
    read: usize,
}

/// The loop's output stream, read by the client after each frame.
#[repr(transparent)]
struct Outbox(Arc<Mutex<Stream>>);

/// A connection driven in process over a workspace other connections may
/// join, as the hub's are.
struct Joined
{
    /// The connection.
    server: Server,
    /// Its workspace, shared with every connection beside it.
    shared: Rc<RefCell<Shared>>,
    /// Whether the exchange is kept.
    record: Record,
    /// Every message sent, in order, when kept.
    sent: Vec<Value>,
    /// Every message received, in order, when kept.
    received: Vec<Value>,
}

impl Client
{
    /// A connection served by `serve` itself, on a thread of its own over
    /// in-memory framed streams, past `initialize` and `initialized`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the loop answered `initialize` without an error and waits for
    ///   the next frame.
    /// - provides: a single editor's connection, whose every answer is a frame
    ///   the transport wrote.
    /// - panics: the loop stops, or the initialization is refused.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every single-editor scenario connects here and holds
    ///   each answer to a fresh in-process connection's; a transport that
    ///   framed, reordered, dropped or added a message, or a loop that answered
    ///   other than `handle` and `admit` do, changes an answer at the keystroke
    ///   that caused it.
    /// - witness: `editor::editor::scenarios::typing_each_corpus_source_keeps_every_answer_faithful`
    /// - witness: `editor::editor::scenarios::fixing_a_mismatch_clears_its_diagnostic`
    #[spec(ensures: |ret| ret.requests == 1 && matches!(ret.connection, Connection::Served(_)))]
    pub fn served() -> Self
    {
        let (frames, inbox_frames) = mpsc::channel();
        let (inbox_waiting, waiting) = mpsc::channel();
        let written = Arc::new(Mutex::new(Stream::default()));
        let mut inbox = Inbox {
            frames: inbox_frames,
            waiting: inbox_waiting,
            frame: Stream::default(),
            read: 0_usize,
        };
        let mut outbox = Outbox(Arc::clone(&written));
        let serving = std::thread::spawn(move || serve(&mut inbox, &mut outbox, &mut io::sink()));
        waiting.recv().expect("the loop asks for its first frame");
        Self {
            connection: Connection::Served(Streams {
                frames,
                waiting,
                written,
                serving,
            }),
            requests: 0_i64,
        }
        .initialize()
    }

    /// A connection past `initialize` and `initialized`, driven in process
    /// over a workspace of its own that others may join.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the connection answered `initialize` without an error and is
    ///   running; with [`Record::Kept`] both messages and the answer are kept.
    /// - provides: a running connection, as an editor holds one.
    /// - panics: the initialization is refused.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every scenario starts here or at
    ///   [`served`](Self::served), and its requests would be refused by a
    ///   connection left waiting, which `request` asserts.
    /// - witness: `editor::editor::scenarios::two_editors_on_one_buffer_each_keep_their_answers`
    #[spec(ensures: |ret| ret.requests == 1 && matches!(ret.connection,
        Connection::Joined(ref joined) if joined.record == record
            && (record == Record::Dropped || joined.sent.len() == 2)))]
    pub fn initialized(record: Record) -> Self
    {
        Self::joining(Rc::new(RefCell::new(Shared::default())), record)
    }

    /// A second connection past `initialize` and `initialized`, over this
    /// one's workspace, as a second editor reaches the hub.
    ///
    /// # Specification
    /// - requires: this connection is joined, not served.
    /// - ensures: the connection is running over the same workspace under a
    ///   peer number no connection over it had.
    /// - provides: the second editor of the shared-workspace scenarios.
    /// - panics: this connection is served, or the initialization is refused.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the two-editor scenarios open one document from both
    ///   connections; a connection that shared no workspace would never meet
    ///   the other's document, and its answers would agree trivially.
    /// - witness: `editor::editor::scenarios::two_editors_on_one_buffer_each_keep_their_answers`
    #[spec(ensures: |ret| ret.requests == 1 && match ret.connection {
        Connection::Joined(ref joined) => match self.connection {
            Connection::Joined(ref this) => Rc::ptr_eq(&joined.shared, &this.shared),
            Connection::Served(_) => false,
        },
        Connection::Served(_) => false,
    })]
    pub fn beside(
        &self,
        record: Record,
    ) -> Self
    {
        let Connection::Joined(ref this) = self.connection
        else {
            panic!("a served connection holds its workspace alone");
        };
        Self::joining(Rc::clone(&this.shared), record)
    }

    /// A connection over `shared`, numbered by its turn, past `initialize`
    /// and `initialized`.
    ///
    /// # Specification
    /// trivial.
    fn joining(
        shared: Rc<RefCell<Shared>>,
        record: Record,
    ) -> Self
    {
        let peer = {
            let mut joined = shared.borrow_mut();
            joined.joined = joined.joined.saturating_add(1);
            Peer::from(joined.joined)
        };
        Self {
            connection: Connection::Joined(Joined {
                server: Server::new(peer),
                shared,
                record,
                sent: Vec::new(),
                received: Vec::new(),
            }),
            requests: 0_i64,
        }
        .initialize()
    }

    /// Answer `initialize`, then say `initialized`.
    ///
    /// # Specification
    /// trivial.
    fn initialize(mut self) -> Self
    {
        let _capabilities = self.request(Method("initialize"), &json!({ "capabilities": {} }));
        let _quiet = self.notify(Method("initialized"), &json!({}));
        self
    }

    /// Send the notification `method` with `params`.
    ///
    /// # Specification
    /// trivial.
    pub fn notify(
        &mut self,
        method: Method,
        params: &Value,
    ) -> Vec<Value>
    {
        self.exchange(json!({ "jsonrpc": "2.0", "method": method.0, "params": params }))
    }

    /// Send the request `method` with `params` and return its result.
    ///
    /// # Specification
    /// - requires: the connection is running.
    /// - ensures: exactly one answer carries the request's id, and it is a
    ///   success.
    /// - panics: no answer, two answers, or an error answer.
    /// - executable: none — the answers are the server's reply, which the call
    ///   asserts as it reads them and which its return, the result alone, no
    ///   longer carries.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every query at every keystroke goes through here; a
    ///   request answered twice, answered with an error or not answered fails
    ///   the scenario at that keystroke.
    /// - witness: `editor::editor::scenarios::typing_each_corpus_source_keeps_every_answer_faithful`
    pub fn request(
        &mut self,
        method: Method,
        params: &Value,
    ) -> Value
    {
        self.requests = self.requests.saturating_add(1);
        let id = json!(self.requests);
        let messages = self
            .exchange(json!({ "jsonrpc": "2.0", "id": id, "method": method.0, "params": params }));
        let answers: Vec<&Value> = messages
            .iter()
            .filter(|message| message.get("id") == Some(&id))
            .collect();
        let &[answer] = answers.as_slice()
        else {
            panic!(
                "one answer to {}, got {}: {}",
                method.0,
                answers.len(),
                Value::from(messages.clone())
            );
        };
        assert!(
            answer.get("error").is_none(),
            "{} answers without an error: {answer}",
            method.0
        );
        answer.get("result").cloned().unwrap_or(Value::Null)
    }

    /// End a served connection as an editor does: `shutdown`, answered with
    /// nothing, then `exit`, at which the loop ends cleanly.
    ///
    /// # Specification
    /// - requires: the connection is served.
    /// - ensures: the loop answered `shutdown` alone, wrote nothing for `exit`,
    ///   and ended [`Served::Clean`].
    /// - provides: the check that a session ends as the transport ends one.
    /// - panics: the connection is joined, or the loop answers otherwise, fails
    ///   a frame or ends otherwise.
    /// - executable: none — the loop's ending is its thread's result, read and
    ///   asserted inside the call, which consumes the client and returns
    ///   nothing.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the corpus sessions and the scripted sessions end
    ///   here; a loop that answered `shutdown` twice or not at all, wrote after
    ///   `exit`, or ended abruptly fails the scenario.
    /// - witness: `editor::editor::scenarios::typing_each_corpus_source_keeps_every_answer_faithful`
    /// - witness: `editor::editor::scenarios::fixing_a_mismatch_clears_its_diagnostic`
    pub fn closes_over_streams(mut self)
    {
        let shutdown =
            self.exchange(json!({ "jsonrpc": "2.0", "id": "end", "method": "shutdown" }));
        assert_eq!(
            shutdown,
            [json!({ "jsonrpc": "2.0", "id": "end", "result": null })],
            "shutdown is answered alone, with nothing"
        );
        let Connection::Served(streams) = self.connection
        else {
            panic!("only a served connection closes over its streams");
        };
        streams
            .frames
            .send(Stream::of(&json!({ "jsonrpc": "2.0", "method": "exit" })))
            .expect("the loop reads the exit");
        let served = streams
            .serving
            .join()
            .expect("the loop ends without a panic")
            .expect("the loop's streams carry every frame");
        assert_eq!(served, Served::Clean, "the session ends cleanly");
        assert!(
            lock(&streams.written).0.is_empty(),
            "the loop writes nothing for exit"
        );
    }

    /// Replay the kept exchange of a joined connection over framed streams
    /// through `serve`, and require it to write what the in-process connection
    /// wrote.
    ///
    /// # Specification
    /// - requires: the client is joined and was built with [`Record::Kept`].
    /// - ensures: `serve`, reading every kept message as a frame followed by
    ///   `shutdown` and `exit`, writes every kept received message in order,
    ///   then the answer to `shutdown`, and ends cleanly.
    /// - provides: the check that the in-process drive of a shared workspace is
    ///   the transport's.
    /// - panics: the client is served or keeps nothing, the replay writes
    ///   anything else, or a frame fails.
    /// - executable: none — the replay's streams live and die inside the call,
    ///   which asserts them and returns nothing.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the two-editor scenarios end here; a transport that
    ///   reordered, dropped or added a message, or framed one wrongly, differs
    ///   from the in-process record.
    /// - witness: `editor::editor::scenarios::two_editors_on_one_buffer_each_keep_their_answers`
    pub fn replays_over_streams(&self)
    {
        let Connection::Joined(ref joined) = self.connection
        else {
            panic!("a served connection is the transport already");
        };
        assert_eq!(joined.record, Record::Kept, "only a kept exchange replays");
        let mut input = Stream::default();
        let closing = [
            json!({ "jsonrpc": "2.0", "id": "end", "method": "shutdown" }),
            json!({ "jsonrpc": "2.0", "method": "exit" }),
        ];
        for message in joined.sent.iter().chain(&closing) {
            input.frame(message);
        }
        let mut output = Stream::default();
        let served = serve(&mut input.0.as_slice(), &mut output.0, &mut Vec::new())
            .expect("the replay serves");
        assert_eq!(served, Served::Clean, "the replay ends cleanly");
        let mut expected = joined.received.clone();
        expected.push(json!({ "jsonrpc": "2.0", "id": "end", "result": null }));
        assert_eq!(
            output.messages(),
            expected,
            "the framed replay writes what the in-process drive received"
        );
    }

    /// Send `message` to the connection and return every message it wrote in
    /// answer, before it read anything further.
    ///
    /// # Specification
    /// trivial.
    fn exchange(
        &mut self,
        message: Value,
    ) -> Vec<Value>
    {
        match self.connection {
            | Connection::Served(ref streams) => streams.exchange(&message),
            | Connection::Joined(ref mut joined) => joined.exchange(message),
        }
    }
}

impl Streams
{
    /// Send `message` to the loop as one frame, wait until it asks for the
    /// next, and read every frame it wrote meanwhile.
    ///
    /// # Specification
    /// - requires: the loop is running.
    /// - ensures: returns, in order, every message the loop wrote between
    ///   reading `message` and asking for its next frame: the frame's answers
    ///   and notifications, then the admissions its log left.
    /// - provides: one lockstep step over the transport.
    /// - panics: the loop stopped, or wrote a frame that does not read as JSON.
    /// - executable: none — the messages are the loop's writes on its own
    ///   thread; no predicate over the return alone tells them from others.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every single-editor keystroke passes here; a step
    ///   that returned before the loop's writes ended, or read another frame's,
    ///   leaves a publication stale or a request answered other than once, and
    ///   the session fails at that keystroke.
    /// - witness: `editor::editor::scenarios::typing_each_corpus_source_keeps_every_answer_faithful`
    fn exchange(
        &self,
        message: &Value,
    ) -> Vec<Value>
    {
        self.frames
            .send(Stream::of(message))
            .expect("the loop reads the frame");
        self.waiting
            .recv()
            .expect("the loop answers the frame, unless it stopped: its panic is reported above");
        core::mem::take(&mut *lock(&self.written)).messages()
    }
}

impl Joined
{
    /// Handle `message` as `serve` does — the message, then the admission
    /// its log leaves — and return every message written.
    ///
    /// # Specification
    /// trivial.
    fn exchange(
        &mut self,
        message: Value,
    ) -> Vec<Value>
    {
        let body = Body::from(serde_json::to_vec(&message).expect("a message encodes"));
        let mut shared = self.shared.borrow_mut();
        let mut outcome = self.server.handle(&mut shared.workspace, &body);
        let admitted = self.server.admit(&mut shared.workspace, &mut outcome.log);
        drop(shared);
        let messages: Vec<Value> = outcome
            .messages
            .iter()
            .map(|written| serde_json::to_value(written).expect("a written message encodes"))
            .chain(
                admitted
                    .iter()
                    .map(|written| serde_json::to_value(written).expect("an admission encodes")),
            )
            .collect();
        if self.record == Record::Kept {
            self.sent.push(message);
            self.received.extend(messages.iter().cloned());
        }
        messages
    }
}

impl io::Read for Inbox
{
    /// Copy what is left of the current frame, waiting for the next when it
    /// is spent.
    ///
    /// # Specification
    /// trivial.
    fn read(
        &mut self,
        buf: &mut [u8],
    ) -> io::Result<usize>
    {
        let copied = {
            let available = self.fill_buf()?;
            let copied = available.len().min(buf.len());
            buf.get_mut(.. copied)
                .expect("a copy fits its destination")
                .copy_from_slice(available.get(.. copied).expect("a copy fits its source"));
            copied
        };
        self.consume(copied);
        Ok(copied)
    }
}

impl io::BufRead for Inbox
{
    /// What is left of the current frame; once it is spent, the loop's ask
    /// for more is signalled and the next frame awaited, and a client that
    /// dropped its frames leaves the stream closed.
    ///
    /// # Specification
    /// trivial.
    fn fill_buf(&mut self) -> io::Result<&[u8]>
    {
        if self.read >= self.frame.0.len() {
            // A client that has gone away is not waiting for the signal.
            let _signalled = self.waiting.send(());
            self.frame = self.frames.recv().unwrap_or_default();
            self.read = 0_usize;
        }
        Ok(self.frame.0.get(self.read ..).unwrap_or_default())
    }

    /// Mark `amount` more bytes of the current frame read.
    ///
    /// # Specification
    /// trivial.
    fn consume(
        &mut self,
        amount: usize,
    )
    {
        self.read = self.read.saturating_add(amount).min(self.frame.0.len());
    }
}

impl io::Write for Outbox
{
    /// Keep `buf` for the client to read.
    ///
    /// # Specification
    /// trivial.
    fn write(
        &mut self,
        buf: &[u8],
    ) -> io::Result<usize>
    {
        lock(&self.0).0.extend_from_slice(buf);
        Ok(buf.len())
    }

    /// Nothing is buffered on this side.
    ///
    /// # Specification
    /// trivial.
    fn flush(&mut self) -> io::Result<()>
    {
        Ok(())
    }
}

impl Stream
{
    /// `message` as one frame.
    ///
    /// # Specification
    /// trivial.
    fn of(message: &Value) -> Self
    {
        let mut stream = Self::default();
        stream.frame(message);
        stream
    }

    /// Append `message` as one frame.
    ///
    /// # Specification
    /// trivial.
    fn frame(
        &mut self,
        message: &Value,
    )
    {
        let body = Body::from(serde_json::to_vec(message).expect("a message encodes"));
        write_frame(&mut self.0, &body).expect("a vector takes every write");
    }

    /// Every message framed on the stream, in order.
    ///
    /// # Specification
    /// trivial.
    fn messages(&self) -> Vec<Value>
    {
        let mut stream = self.0.as_slice();
        let mut messages = Vec::new();
        while !stream.fill_buf().expect("a slice reads").is_empty() {
            let Maybe::Present(body) = read_frame(&mut stream).expect("a written frame reads")
            else {
                break;
            };
            messages.push(
                serde_json::from_slice::<Value>(body.as_ref()).expect("a written frame is JSON"),
            );
        }
        messages
    }
}

/// The stream behind `written`, whether or not a holder panicked.
///
/// # Specification
/// trivial.
fn lock(written: &Mutex<Stream>) -> std::sync::MutexGuard<'_, Stream>
{
    written.lock().unwrap_or_else(PoisonError::into_inner)
}
