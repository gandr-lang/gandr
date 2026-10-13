//! The client's side of a session: a connection driven in process, one
//! message at a time, exactly as `serve` drives it, with every message sent
//! and received kept so the same exchange can be replayed over framed
//! streams. Connections may share one workspace, as the hub's do.

use alloc::rc::Rc;
use alloc::vec::Vec;
use core::cell::RefCell;
use std::io::BufRead as _;

use anodized::spec;
use gandr_surface_lsp::Body;
use gandr_surface_lsp::Peer;
use gandr_surface_lsp::Served;
use gandr_surface_lsp::Server;
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

/// Whether a client keeps its exchange for a replay over streams.
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

/// One connection over a workspace, driven in process.
pub struct Client
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
    /// The id of the latest request.
    requests: i64,
}

impl Client
{
    /// A connection past `initialize` and `initialized`, over a workspace of
    /// its own.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the connection answered `initialize` without an error and is
    ///   running; with [`Record::Kept`] both messages and the answer are kept.
    /// - provides: a running connection, as an editor holds one.
    /// - panics: the initialization is refused.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every scenario starts here and its requests would be
    ///   refused by a connection left waiting, which `request` asserts.
    /// - witness: `editor::editor::scenarios::typing_each_corpus_source_keeps_every_answer_faithful`
    #[spec(ensures: |ret| ret.requests == 1 && ret.record == record
        && (record == Record::Dropped || ret.sent.len() == 2))]
    pub fn initialized(record: Record) -> Self
    {
        Self::joining(Rc::new(RefCell::new(Shared::default())), record)
    }

    /// A second connection past `initialize` and `initialized`, over this
    /// one's workspace, as a second editor reaches the hub.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the connection is running over the same workspace under a
    ///   peer number no connection over it had.
    /// - provides: the second editor of the shared-workspace scenarios.
    /// - panics: the initialization is refused.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the two-editor scenarios open one document from both
    ///   connections; a connection that shared no workspace would never meet
    ///   the other's document, and its answers would agree trivially.
    /// - witness: `editor::editor::scenarios::two_editors_on_one_buffer_each_keep_their_answers`
    #[spec(ensures: |ret| Rc::ptr_eq(&ret.shared, &self.shared) && ret.requests == 1)]
    pub fn beside(
        &self,
        record: Record,
    ) -> Self
    {
        Self::joining(Rc::clone(&self.shared), record)
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
        let mut client = Self {
            server: Server::new(peer),
            shared,
            record,
            sent: Vec::new(),
            received: Vec::new(),
            requests: 0_i64,
        };
        let _capabilities = client.request(Method("initialize"), &json!({ "capabilities": {} }));
        let _quiet = client.notify(Method("initialized"), &json!({}));
        client
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

    /// Replay the kept exchange over framed streams through `serve`, and
    /// require it to write what the in-process connection wrote.
    ///
    /// # Specification
    /// - requires: the client was built with [`Record::Kept`].
    /// - ensures: `serve`, reading every kept message as a frame followed by
    ///   `shutdown` and `exit`, writes every kept received message in order,
    ///   then the answer to `shutdown`, and ends cleanly.
    /// - provides: the check that the in-process drive is the transport's.
    /// - panics: the replay writes anything else, or a frame fails.
    /// - executable: none — the replay's streams live and die inside the call,
    ///   which asserts them and returns nothing.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the corpus replay and the scripted sessions end here;
    ///   a transport that reordered, dropped or added a message, or framed one
    ///   wrongly, differs from the in-process record.
    /// - witness: `editor::editor::scenarios::typing_each_corpus_source_keeps_every_answer_faithful`
    /// - witness: `editor::editor::scenarios::fixing_a_mismatch_clears_its_diagnostic`
    pub fn replays_over_streams(&self)
    {
        assert_eq!(self.record, Record::Kept, "only a kept exchange replays");
        let mut input = Vec::new();
        let closing = [
            json!({ "jsonrpc": "2.0", "id": "end", "method": "shutdown" }),
            json!({ "jsonrpc": "2.0", "method": "exit" }),
        ];
        for message in self.sent.iter().chain(&closing) {
            let body = Body::from(serde_json::to_vec(message).expect("a message encodes"));
            write_frame(&mut input, &body).expect("a vector takes every write");
        }
        let mut output = Vec::new();
        let served =
            serve(&mut input.as_slice(), &mut output, &mut Vec::new()).expect("the replay serves");
        assert_eq!(served, Served::Clean, "the replay ends cleanly");
        let mut stream = output.as_slice();
        let mut written = Vec::new();
        while !stream.fill_buf().expect("a slice reads").is_empty() {
            let Maybe::Present(body) = read_frame(&mut stream).expect("a written frame reads")
            else {
                break;
            };
            written.push(
                serde_json::from_slice::<Value>(body.as_ref()).expect("a written frame is JSON"),
            );
        }
        let mut expected = self.received.clone();
        expected.push(json!({ "jsonrpc": "2.0", "id": "end", "result": null }));
        assert_eq!(
            written, expected,
            "the framed replay writes what the in-process drive received"
        );
    }

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
