//! The client's side of a session: a connection an editor holds, driven one
//! message at a time. A served connection is `serve` itself, on a thread of
//! its own over the shared client's pipes, so every answer a session reads is
//! one the transport wrote. A joined connection is driven in process exactly
//! as `serve` drives one, over a workspace other connections may join, as the
//! hub's are; when kept, its exchange replays over framed streams.

use alloc::rc::Rc;
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::cell::RefCell;

use anodized::spec;
use gandr_surface_lsp::Admissions;
use gandr_surface_lsp::Awaiting;
use gandr_surface_lsp::Body;
use gandr_surface_lsp::DocumentUri;
use gandr_surface_lsp::Peer;
use gandr_surface_lsp::Served;
use gandr_surface_lsp::Server;
use gandr_surface_lsp::Spelling;
use gandr_surface_lsp::Workspace;
pub use gandr_surface_lsp::client::Method;
use gandr_surface_lsp::client::Serving;
use gandr_surface_lsp::client::spawned;
use serde_json::Value;
use serde_json::json;

/// Whether a joined client keeps its exchange for a replay over streams.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Record
{
    /// Every message sent and received is kept.
    Kept,
    /// Nothing is kept: the client answers one question and is dropped.
    Dropped,
}

/// The quiet interval a connection names at `initialize`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Quiet
{
    /// Zero: every diagnostic publishes with its synchronisation, as a fresh
    /// connection's does.
    Unheld,
    /// None named: the server's own interval.
    Default,
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
    /// `serve` on a thread of its own, over the shared client's pipes.
    Served(Streams),
    /// A connection driven in process, over a workspace others may join; boxed,
    /// the server it drives outweighing the streams.
    Joined(Box<Joined>),
}

/// A `serve` loop on a thread of its own, and the client of its pipes.
struct Streams
{
    /// The client of the loop's pipes.
    client: gandr_surface_lsp::client::Client,
    /// The loop, which ends at `exit` or when the client closes its stream.
    serving: Serving,
}

/// A connection driven in process over a workspace other connections may
/// join, as the hub's are.
struct Joined
{
    /// The connection.
    server: Server,
    /// Its admissions, on the shared workspace's pool.
    admissions: Admissions,
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
    /// in-memory framed streams, past `initialize` and `initialized`, holding
    /// nothing back: its oracle is a fresh connection, which has no caret.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the loop answered `initialize`, naming a quiet interval of
    ///   zero, without an error.
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
    /// - witness: `tests::editor::scenarios::sweeps::typing_each_corpus_source_keeps_every_answer_faithful`
    /// - witness: `tests::editor::scenarios::fixing_a_mismatch_clears_its_diagnostic`
    #[spec(ensures: |ret| ret.requests == 1 && matches!(ret.connection, Connection::Served(_)))]
    pub fn served() -> Self
    {
        Self {
            connection: Connection::Served(Streams::spawn()),
            requests: 0_i64,
        }
        .initialize(Quiet::Unheld)
    }

    /// A connection past `initialize` and `initialized`, driven in process
    /// over a workspace of its own that others may join, at the quiet
    /// interval `quiet` names.
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
    /// - witness: `tests::editor::scenarios::sweeps::two_editors_on_one_buffer_each_keep_their_answers`
    #[spec(ensures: |ret| ret.requests == 1 && matches!(ret.connection,
        Connection::Joined(ref joined) if joined.record == record
            && (record == Record::Dropped || joined.sent.len() == 2)))]
    pub fn initialized(
        record: Record,
        quiet: Quiet,
    ) -> Self
    {
        Self::joining(Rc::new(RefCell::new(Shared::default())), record, quiet)
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
    /// - witness: `tests::editor::scenarios::sweeps::two_editors_on_one_buffer_each_keep_their_answers`
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
        Self::joining(Rc::clone(&this.shared), record, Quiet::Unheld)
    }

    /// A connection over `shared`, numbered by its turn, past `initialize`
    /// and `initialized` at `quiet`.
    ///
    /// # Specification
    /// trivial.
    fn joining(
        shared: Rc<RefCell<Shared>>,
        record: Record,
        quiet: Quiet,
    ) -> Self
    {
        let (peer, pool) = {
            let mut joined = shared.borrow_mut();
            joined.joined = joined.joined.saturating_add(1);
            (
                Peer::from(joined.joined),
                Arc::clone(joined.workspace.pool()),
            )
        };
        Self {
            connection: Connection::Joined(Box::new(Joined {
                server: Server::new(peer),
                admissions: Admissions::new(pool, gandr_surface_lsp::Inbox::default().changes()),
                shared,
                record,
                sent: Vec::new(),
                received: Vec::new(),
            })),
            requests: 0_i64,
        }
        .initialize(quiet)
    }

    /// Answer `initialize`, naming the quiet interval `quiet` names, then say
    /// `initialized`.
    ///
    /// # Specification
    /// trivial.
    fn initialize(
        mut self,
        quiet: Quiet,
    ) -> Self
    {
        let params = match quiet {
            Quiet::Unheld => json!({
                "capabilities": {},
                "initializationOptions": { "diagnostics": { "quiet": 0_i32 } },
            }),
            Quiet::Default => json!({ "capabilities": {} }),
        };
        let _capabilities = self.request(Method("initialize"), &params);
        let _quiet = self.notify(Method("initialized"), &json!({}));
        self
    }

    /// Let the quiet interval of the document at `uri` pass, as the loop does
    /// when no frame arrives before its deadline, and return what that
    /// publishes.
    ///
    /// # Specification
    /// - requires: the connection is joined.
    /// - ensures: the messages [`Server::release`] writes for `uri`.
    /// - panics: the connection is served: its loop keeps its own time.
    /// - executable: none — the messages are the server's.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the quiet scenario stops mid-form and reads the held
    ///   diagnostics here; a release that dropped or reordered them fails it.
    /// - witness: `tests::editor::scenarios::typing_a_declaration_holds_its_diagnostics_until_its_terminator`
    pub fn lapse(
        &mut self,
        uri: &DocumentUri,
    ) -> Vec<Value>
    {
        let Connection::Joined(ref mut joined) = self.connection
        else {
            panic!("a served connection keeps its own time");
        };
        let mut shared = joined.shared.borrow_mut();
        joined
            .server
            .release(&mut shared.workspace, uri)
            .iter()
            .map(|written| serde_json::to_value(written).expect("a release encodes"))
            .collect()
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
    /// - witness: `tests::editor::scenarios::sweeps::typing_each_corpus_source_keeps_every_answer_faithful`
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
    /// - witness: `tests::editor::scenarios::sweeps::typing_each_corpus_source_keeps_every_answer_faithful`
    /// - witness: `tests::editor::scenarios::fixing_a_mismatch_clears_its_diagnostic`
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
        assert_eq!(streams.end(), Served::Clean, "the session ends cleanly");
    }

    /// Replay the kept exchange of a joined connection over framed streams
    /// through `serve`, and require it to write what the in-process connection
    /// wrote.
    ///
    /// # Specification
    /// - requires: the client is joined and was built with [`Record::Kept`].
    /// - ensures: `serve`, sent every kept message as a frame one exchange at a
    ///   time as an editor that awaits each answer sends them, then `shutdown`
    ///   and `exit`, writes every kept received message in order, then the
    ///   answer to `shutdown`, and ends cleanly.
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
    /// - witness: `tests::editor::scenarios::sweeps::two_editors_on_one_buffer_each_keep_their_answers`
    pub fn replays_over_streams(&self)
    {
        let Connection::Joined(ref joined) = self.connection
        else {
            panic!("a served connection is the transport already");
        };
        assert_eq!(joined.record, Record::Kept, "only a kept exchange replays");
        let mut streams = Streams::spawn();
        let mut written: Vec<Value> = Vec::new();
        for message in &joined.sent {
            written.extend(streams.exchange(message));
        }
        written.extend(
            streams.exchange(&json!({ "jsonrpc": "2.0", "id": "end", "method": "shutdown" })),
        );
        assert_eq!(streams.end(), Served::Clean, "the replay ends cleanly");
        let mut expected = joined.received.clone();
        expected.push(json!({ "jsonrpc": "2.0", "id": "end", "result": null }));
        assert_eq!(
            written, expected,
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
            Connection::Served(ref mut streams) => streams.exchange(&message),
            Connection::Joined(ref mut joined) => joined.exchange(message),
        }
    }
}

impl Streams
{
    /// `serve` on a thread of its own over fresh pipes.
    ///
    /// # Specification
    /// trivial.
    fn spawn() -> Self
    {
        let (client, serving) =
            spawned(Workspace::spelled(Spelling::Unicode)).expect("the loop's pipes open");
        Self { client, serving }
    }

    /// Send `message` to the loop, and read every message it wrote for it.
    ///
    /// # Specification
    /// trivial.
    fn exchange(
        &mut self,
        message: &Value,
    ) -> Vec<Value>
    {
        self.client
            .exchange(message)
            .expect("the loop answers the frame, unless it stopped: its panic is reported above")
    }

    /// Send `exit`, close the client's stream, and answer how the loop ended.
    ///
    /// # Specification
    /// - requires: the loop answered `shutdown`.
    /// - ensures: the loop wrote nothing for `exit` and ended.
    /// - panics: the loop wrote anything after `exit`, a frame failed, or the
    ///   loop panicked.
    /// - executable: none — the ending is the loop thread's result.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every served session ends here; a loop that wrote
    ///   after `exit` or ended abruptly fails the scenario.
    /// - witness: `tests::editor::scenarios::fixing_a_mismatch_clears_its_diagnostic`
    fn end(mut self) -> Served
    {
        self.client
            .send(&[json!({ "jsonrpc": "2.0", "method": "exit" })])
            .expect("the loop reads the exit");
        let after = self
            .client
            .finish()
            .expect("the loop's streams carry every frame");
        assert!(
            after.is_empty(),
            "the loop writes nothing for exit: {after:?}"
        );
        self.serving.ended().expect("the loop ends without a fault")
    }
}

impl Joined
{
    /// Handle `message` as `serve` does — the message, then the judgements and
    /// admissions it starts, settled — and return every message written.
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
        let outcome = self.server.handle(&mut shared.workspace, &body);
        let _logged = self
            .server
            .admit(&mut shared.workspace, &mut self.admissions);
        let admitted =
            self.server
                .admitted(&mut shared.workspace, &mut self.admissions, Awaiting::All);
        drop(shared);
        let messages: Vec<Value> = outcome
            .messages
            .iter()
            .chain(&admitted.messages)
            .map(|written| serde_json::to_value(written).expect("a written message encodes"))
            .collect();
        if self.record == Record::Kept {
            self.sent.push(message);
            self.received.extend(messages.iter().cloned());
        }
        messages
    }
}
