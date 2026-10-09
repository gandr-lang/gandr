//! The server: a state machine over classified messages, and the loop that
//! drives it over a pair of byte streams.
//!
//! The lifecycle is the protocol's. Before `initialize` is answered every
//! request is refused as not initialized and every notification but `exit` is
//! dropped; a second `initialize` is an invalid request; after `shutdown`
//! every request is an invalid request. `exit` ends the session, successfully
//! after `shutdown` and abruptly before it; a stream closed without `exit`
//! ends it the same way. A notification is never answered: one whose
//! parameters the server cannot read is dropped, and `$/` notifications and
//! every other unknown one are ignored, as the protocol admits.

use alloc::collections::BTreeMap;
use std::io::BufRead;
use std::io::Write;

use gandr_surface_render_remote::LineIndex;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;
use serde_json::Value;

use crate::position::Range;
use crate::protocol::Answer;
use crate::protocol::DidChangeParams;
use crate::protocol::DidOpenParams;
use crate::protocol::DocumentParams;
use crate::protocol::DocumentUri;
use crate::protocol::DocumentVersion;
use crate::protocol::InitializeResult;
use crate::protocol::PublishParams;
use crate::protocol::RangeParams;
use crate::protocol::SemanticTokens;
use crate::recheck::highlight;
use crate::recheck::recheck;
use crate::rpc::ErrorCode;
use crate::rpc::Incoming;
use crate::rpc::Method;
use crate::rpc::Outgoing;
use crate::rpc::RequestId;
use crate::rpc::classify;
use crate::rpc::failure;
use crate::rpc::publish;
use crate::rpc::success;
use crate::tokens::encode;
use crate::tokens::overlapping;
use crate::transport::Body;
use crate::transport::TransportFault;
use crate::transport::read_frame;
use crate::transport::write_frame;

/// Where the server stands in the protocol's lifecycle.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Phase
{
    /// `initialize` has not been answered.
    Waiting,
    /// `initialize` has been answered and `shutdown` has not.
    Running,
    /// `shutdown` has been answered; only `exit` remains.
    ShuttingDown,
}

/// The tokens a request asks for.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Window
{
    /// Every token of the document.
    Whole,
    /// The tokens overlapping a range.
    Within(Range),
}

/// One open document, as the client last synchronised it.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Document
{
    /// The version of its text.
    version: DocumentVersion,
    /// Its whole text.
    text: String,
}

/// How a session ended.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Served
{
    /// `exit` arrived after `shutdown`, or the stream closed after it.
    Clean,
    /// `exit` arrived, or the stream closed, before `shutdown`.
    Abrupt,
}

/// What handling one message decided.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Flow
{
    /// The session continues.
    Continue,
    /// `exit` arrived: the session ends as stated.
    Exit(Served),
}

/// What handling one message produced: the messages to write, in order, and
/// whether the session goes on.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Outcome
{
    /// The messages to write, in order.
    pub messages: Vec<Outgoing>,
    /// Whether the session goes on.
    pub flow: Flow,
}

impl Outcome
{
    /// Nothing to write; the session goes on.
    ///
    /// # Specification
    /// trivial.
    const fn quiet() -> Self
    {
        Self {
            messages: Vec::new(),
            flow: Flow::Continue,
        }
    }

    /// One message to write; the session goes on.
    ///
    /// # Specification
    /// trivial.
    fn say(message: Outgoing) -> Self
    {
        Self {
            messages: vec![message],
            flow: Flow::Continue,
        }
    }
}

/// The server's state: where it stands in the lifecycle, and every open
/// document.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Server
{
    /// Where the server stands in the lifecycle.
    phase: Phase,
    /// Every open document, by its URI.
    documents: BTreeMap<DocumentUri, Document>,
}

impl Default for Server
{
    /// A server waiting for `initialize`, with no document open.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self {
            phase: Phase::Waiting,
            documents: BTreeMap::new(),
        }
    }
}

impl Server
{
    /// Handle one message body.
    ///
    /// # Specification
    /// - requires: nothing; any body is admissible input.
    /// - ensures: a request is answered exactly once, under its own identifier,
    ///   as the lifecycle and the method decide; a notification is never
    ///   answered, and a document synchronisation publishes the document's
    ///   diagnostics, recomputed whole — opening and changing it publish its
    ///   diagnostics at its new version, closing it publishes none and forgets
    ///   it. A body that is not a message is answered with the error the
    ///   protocol owes it. `exit` ends the session.
    /// - provides: the whole of the server's behaviour; [`serve`] only moves
    ///   bytes.
    /// - fails: never; every refusal is a message to the client.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — the capabilities and the token streams of a known
    ///   document are asserted whole; L3 — the lifecycle's decision surfaces,
    ///   each range shape, and a refused document's publication, each asserted
    ///   at its exact messages.
    /// - witness: `server::tests::initialize_advertises_the_token_legend`
    /// - witness: `server::tests::semantic_tokens_full_answers_a_known_document`
    /// - witness: `server::tests::a_range_returns_only_the_tokens_it_covers`
    /// - witness: `server::tests::a_refused_program_is_published_as_an_editor_diagnostic`
    /// - witness: `server::tests::the_lifecycle_admits_requests_in_the_protocol_order`
    /// - witness: `server::tests::synchronisation_publishes_and_close_clears`
    #[inline]
    #[must_use]
    pub fn handle(
        &mut self,
        body: &Body,
    ) -> Outcome
    {
        match classify(body) {
            | Err(malformed) => Outcome::say(malformed.response()),
            | Ok(Incoming::Response) => Outcome::quiet(),
            | Ok(Incoming::Request { id, method, params }) => {
                Outcome::say(self.request(id, &method, params))
            },
            | Ok(Incoming::Notification { method, params }) => self.notification(&method, params),
        }
    }

    /// How the session ends if the stream closes now.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Served::Clean`] once `shutdown` has been answered,
    ///   [`Served::Abrupt`] before.
    /// - provides: the ending of `exit` and of a closed stream alike.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `exit` before and after `shutdown`, each asserted at
    ///   its exact ending.
    /// - witness: `server::tests::the_lifecycle_admits_requests_in_the_protocol_order`
    #[inline]
    #[must_use]
    pub const fn closed(&self) -> Served
    {
        match self.phase {
            | Phase::ShuttingDown => Served::Clean,
            | Phase::Waiting | Phase::Running => Served::Abrupt,
        }
    }

    /// The response to the request `id` calling `method` with `params`.
    ///
    /// # Specification
    /// trivial.
    fn request(
        &mut self,
        id: RequestId,
        method: &Method,
        params: Value,
    ) -> Outgoing
    {
        let name = method.as_ref();
        match (self.phase, name) {
            | (Phase::Waiting, "initialize") => {
                self.phase = Phase::Running;
                success(
                    id,
                    Answer::Initialize(Box::new(InitializeResult::advertised())),
                )
            },
            | (Phase::Waiting, _) => failure(
                id,
                ErrorCode::SERVER_NOT_INITIALIZED,
                format!("`{name}` arrived before `initialize`"),
            ),
            | (Phase::Running, "initialize") => failure(
                id,
                ErrorCode::INVALID_REQUEST,
                "`initialize` was already answered".to_owned(),
            ),
            | (Phase::Running, "shutdown") => {
                self.phase = Phase::ShuttingDown;
                success(id, Answer::Nothing)
            },
            | (Phase::Running, "textDocument/semanticTokens/full") => {
                match serde_json::from_value::<DocumentParams>(params) {
                    | Ok(params) => {
                        success(id, self.tokens(&params.text_document.uri, Window::Whole))
                    },
                    | Err(error) => failure(id, ErrorCode::INVALID_PARAMS, error.to_string()),
                }
            },
            | (Phase::Running, "textDocument/semanticTokens/range") => {
                match serde_json::from_value::<RangeParams>(params) {
                    | Ok(params) => success(
                        id,
                        self.tokens(&params.text_document.uri, Window::Within(params.range)),
                    ),
                    | Err(error) => failure(id, ErrorCode::INVALID_PARAMS, error.to_string()),
                }
            },
            | (Phase::Running, _) => failure(
                id,
                ErrorCode::METHOD_NOT_FOUND,
                format!("`{name}` is not served"),
            ),
            | (Phase::ShuttingDown, _) => failure(
                id,
                ErrorCode::INVALID_REQUEST,
                format!("`{name}` arrived after `shutdown`"),
            ),
        }
    }

    /// What the notification calling `method` with `params` produces.
    ///
    /// # Specification
    /// trivial.
    fn notification(
        &mut self,
        method: &Method,
        params: Value,
    ) -> Outcome
    {
        match (self.phase, method.as_ref()) {
            | (_, "exit") => Outcome {
                messages: Vec::new(),
                flow: Flow::Exit(self.closed()),
            },
            | (Phase::Running, "textDocument/didOpen") => {
                let Ok(DidOpenParams { text_document }) = serde_json::from_value(params)
                else {
                    return Outcome::quiet();
                };
                let document = Document {
                    version: text_document.version,
                    text: text_document.text,
                };
                let message = published(&text_document.uri, &document);
                let _prior = self.documents.insert(text_document.uri, document);
                Outcome::say(message)
            },
            | (Phase::Running, "textDocument/didChange") => {
                let Ok(DidChangeParams {
                    text_document,
                    mut content_changes,
                }) = serde_json::from_value(params)
                else {
                    return Outcome::quiet();
                };
                let Some(document) = self.documents.get_mut(&text_document.uri)
                else {
                    return Outcome::quiet();
                };
                document.version = text_document.version;
                if let Some(change) = content_changes.pop() {
                    document.text = change.text;
                }
                Outcome::say(published(&text_document.uri, document))
            },
            | (Phase::Running, "textDocument/didClose") => {
                let Ok(DocumentParams { text_document }) = serde_json::from_value(params)
                else {
                    return Outcome::quiet();
                };
                let _closed = self.documents.remove(&text_document.uri);
                Outcome::say(publish(PublishParams {
                    uri: text_document.uri,
                    version: None,
                    diagnostics: Vec::new(),
                }))
            },
            | (Phase::Waiting | Phase::Running | Phase::ShuttingDown, _) => Outcome::quiet(),
        }
    }

    /// The tokens of the document at `uri` in `window`.
    ///
    /// # Specification
    /// trivial.
    fn tokens(
        &self,
        uri: &DocumentUri,
        window: Window,
    ) -> Answer
    {
        let Some(document) = self.documents.get(uri)
        else {
            return Answer::Nothing;
        };
        let text = document.text.as_str();
        let index = LineIndex::new(text.into());
        let spans = highlight(SourceText::from(text));
        let spans = match window {
            | Window::Whole => spans,
            | Window::Within(range) => {
                overlapping(spans, range.start.byte(&index), range.end.byte(&index))
            },
        };
        Answer::Tokens(SemanticTokens {
            data: encode(&index, &spans),
        })
    }
}

/// The notification publishing the diagnostics of `document`, open at `uri`.
///
/// # Specification
/// trivial.
fn published(
    uri: &DocumentUri,
    document: &Document,
) -> Outgoing
{
    publish(PublishParams {
        uri: uri.clone(),
        version: Some(document.version),
        diagnostics: recheck(uri, SourceText::from(document.text.as_str())),
    })
}

/// Serve the protocol over `input` and `output` until the session ends.
///
/// # Specification
/// - requires: nothing of the streams; `input` carries the client's frames and
///   `output` takes the server's.
/// - ensures: each frame read is handled by one [`Server`], and every message
///   it produces is written as one frame, in order, before the next frame is
///   read; the session ends at `exit` or at a stream closed at a frame
///   boundary, as [`Server::closed`] states.
/// - provides: the language server over any pair of streams: the driver's
///   standard input and output, or memory.
/// - fails: the first [`TransportFault`] of either stream, and
///   [`TransportFault::Encode`] for a message that does not encode.
/// - panics: none.
///
/// # Errors
/// [`TransportFault`], as above.
///
/// # Adequacy
/// - hypothesis: L2 — a whole session over in-memory streams, from `initialize`
///   to `exit`, asserted frame by frame; L3 — a session closed without `exit`,
///   and one whose stream breaks inside a frame.
/// - witness: `session::session::a_session_round_trips_over_in_memory_streams`
/// - witness: `session::session::a_stream_closed_without_exit_ends_abruptly`
#[inline]
pub fn serve<Input, Output>(
    input: &mut Input,
    output: &mut Output,
) -> Result<Served, TransportFault>
where
    Input: BufRead,
    Output: Write,
{
    let mut server = Server::default();
    loop {
        let read = read_frame(input)?;
        let Maybe::Present(body) = read
        else {
            return Ok(server.closed());
        };
        let outcome = server.handle(&body);
        for message in &outcome.messages {
            let encoded = serde_json::to_vec(message).map_err(TransportFault::Encode)?;
            write_frame(output, &Body::from(encoded))?;
        }
        if let Flow::Exit(served) = outcome.flow {
            return Ok(served);
        }
    }
}

#[cfg(test)]
mod tests
{
    use serde_json::Value;

    use super::Flow;
    use super::Served;
    use super::Server;
    use crate::transport::Body;

    /// A message or a value, spelled as JSON text.
    #[repr(transparent)]
    #[derive(Clone, Copy)]
    struct Json<'text>(&'text str);

    /// The text `json` spells, parsed.
    ///
    /// # Specification
    /// trivial.
    fn wire(Json(text): Json<'_>) -> Value
    {
        serde_json::from_str(text).expect("a test's JSON parses")
    }

    /// The messages `server` writes for the message `json` spells, as one
    /// JSON array.
    ///
    /// # Specification
    /// trivial.
    fn send(
        server: &mut Server,
        Json(text): Json<'_>,
    ) -> Value
    {
        let body = Body::from(text.as_bytes().to_vec());
        Value::Array(
            server
                .handle(&body)
                .messages
                .iter()
                .map(|outgoing| serde_json::to_value(outgoing).expect("a message encodes"))
                .collect(),
        )
    }

    /// A server that has answered `initialize`.
    ///
    /// # Specification
    /// trivial.
    fn initialized() -> Server
    {
        let mut server = Server::default();
        let answered = send(
            &mut server,
            Json(r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"capabilities":{}}}"#),
        );
        assert_eq!(
            answered.as_array().map(Vec::len),
            Some(1_usize),
            "initialize is answered once"
        );
        server
    }

    /// A server with the known document open: `def f = 42 ;`, a keyword, a
    /// declared name and a number, with `=` and `;` unclassified.
    ///
    /// # Specification
    /// trivial.
    fn server_over_the_known_document() -> Server
    {
        let mut server = initialized();
        let _published = send(
            &mut server,
            Json(
                r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":
                    {"uri":"file:///tmp/example.gandr","languageId":"gandr","version":1,
                     "text":"def f = 42 ;\n"}}}"#,
            ),
        );
        server
    }

    /// The token stream a range request over the known document answers.
    ///
    /// # Specification
    /// trivial.
    fn ranged(Json(range): Json<'_>) -> Value
    {
        let mut server = server_over_the_known_document();
        let request = format!(
            r#"{{"jsonrpc":"2.0","id":2,"method":"textDocument/semanticTokens/range",
                "params":{{"textDocument":{{"uri":"file:///tmp/example.gandr"}},"range":{range}}}}}"#
        );
        send(&mut server, Json(&request))
            .pointer("/0/result/data")
            .cloned()
            .unwrap_or(Value::Null)
    }

    #[test]
    fn initialize_advertises_the_token_legend()
    {
        let mut server = Server::default();
        assert_eq!(
            send(
                &mut server,
                Json(
                    r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"capabilities":{}}}"#
                ),
            ),
            wire(Json(concat!(
                r#"[{"jsonrpc":"2.0","id":1,"result":{
                    "capabilities":{
                        "positionEncoding":"utf-16",
                        "textDocumentSync":{"openClose":true,"change":1},
                        "semanticTokensProvider":{
                            "legend":{
                                "tokenTypes":["keyword","operator","function","variable",
                                    "parameter","property","enumMember","type","typeParameter",
                                    "number","string","comment","macro","label"],
                                "tokenModifiers":["declaration","defaultLibrary"]},
                            "full":true,
                            "range":true}},
                    "serverInfo":{"name":"gandr","version":""#,
                env!("CARGO_PKG_VERSION"),
                r#""}}}]"#
            ))),
            "the advertised capabilities, whole: no hover, no completion"
        );
    }

    #[test]
    fn semantic_tokens_full_answers_a_known_document()
    {
        let mut server = server_over_the_known_document();
        assert_eq!(
            send(
                &mut server,
                Json(
                    r#"{"jsonrpc":"2.0","id":2,"method":"textDocument/semanticTokens/full",
                        "params":{"textDocument":{"uri":"file:///tmp/example.gandr"}}}"#
                ),
            ),
            wire(Json(
                r#"[{"jsonrpc":"2.0","id":2,
                     "result":{"data":[0,0,3,0,0, 0,4,1,2,1, 0,4,2,9,0]}}]"#
            )),
            "the known document's tokens: `def`, `f` a declared function, `42`"
        );
        for (id, method) in [
            ("3", "textDocument/hover"),
            ("4", "textDocument/completion"),
        ] {
            let request = format!(
                r#"{{"jsonrpc":"2.0","id":{id},"method":"{method}","params":{{
                    "textDocument":{{"uri":"file:///tmp/example.gandr"}},
                    "position":{{"line":0,"character":4}}}}}}"#
            );
            let refusal = format!(
                r#"[{{"jsonrpc":"2.0","id":{id},
                     "error":{{"code":-32601,"message":"`{method}` is not served"}}}}]"#
            );
            assert_eq!(
                send(&mut server, Json(&request)),
                wire(Json(&refusal)),
                "{method} is not advertised, so it is not served"
            );
        }
    }

    #[test]
    fn a_range_returns_only_the_tokens_it_covers()
    {
        // Characters 8..10 of the known document are exactly `42`; its token
        // keeps the document's origin, so a stream re-based on the range
        // would read [0, 0, 2, 9, 0] and paint the number over `def`.
        assert_eq!(
            ranged(Json(
                r#"{"start":{"line":0,"character":8},"end":{"line":0,"character":10}}"#
            )),
            wire(Json("[0,8,2,9,0]")),
            "the only token in 8..10 is `42`, at line 0 column 8"
        );
    }

    #[test]
    fn a_range_over_the_whole_document_agrees_with_the_full_stream()
    {
        assert_eq!(
            ranged(Json(
                r#"{"start":{"line":0,"character":0},"end":{"line":1,"character":0}}"#
            )),
            wire(Json("[0,0,3,0,0, 0,4,1,2,1, 0,4,2,9,0]")),
            "a range over every line answers the full stream"
        );
    }

    #[test]
    fn a_token_straddling_the_range_edge_is_returned_whole()
    {
        // Characters 1..2 lie strictly inside `def` at 0..3 and touch
        // nothing else.
        assert_eq!(
            ranged(Json(
                r#"{"start":{"line":0,"character":1},"end":{"line":0,"character":2}}"#
            )),
            wire(Json("[0,0,3,0,0]")),
            "an overlapping token is sent whole, not clipped"
        );
    }

    #[test]
    fn an_inverted_range_yields_no_tokens()
    {
        // The inversion lies strictly inside `def`, so the overlap test alone
        // — `span.start < 1 && 2 < span.end` — would keep the keyword; only
        // the inversion check sends nothing.
        assert_eq!(
            ranged(Json(
                r#"{"start":{"line":0,"character":2},"end":{"line":0,"character":1}}"#
            )),
            wire(Json("[]")),
            "an inverted range classifies nothing"
        );
    }

    /// The half-open overlap test keeps no span for `start == end`, so this
    /// guards the outcome rather than separating the inversion check, which
    /// `an_inverted_range_yields_no_tokens` separates.
    #[test]
    fn an_empty_range_yields_no_tokens()
    {
        assert_eq!(
            ranged(Json(
                r#"{"start":{"line":0,"character":4},"end":{"line":0,"character":4}}"#
            )),
            wire(Json("[]")),
            "an empty range classifies nothing"
        );
    }

    #[test]
    fn a_refused_program_is_published_as_an_editor_diagnostic()
    {
        let mut server = initialized();
        assert_eq!(
            send(
                &mut server,
                Json(
                    r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":
                        {"uri":"file:///tmp/refused.gandr","languageId":"gandr","version":3,
                         "text":"def answer = 42 ;\ndef broken = missing ;\n"}}}"#
                ),
            ),
            wire(Json(
                r#"[{"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{
                    "uri":"file:///tmp/refused.gandr",
                    "version":3,
                    "diagnostics":[{
                        "range":{"start":{"line":1,"character":13},
                                 "end":{"line":1,"character":20}},
                        "severity":1,
                        "code":"UnresolvedName",
                        "source":"gandr",
                        "message":"no declaration or binder answers `missing` at 31..38"}]}}]"#
            )),
            "the refusal is one error at the name, coded with its vocabulary name"
        );
    }

    #[test]
    fn the_lifecycle_admits_requests_in_the_protocol_order()
    {
        let mut server = Server::default();
        assert_eq!(
            send(
                &mut server,
                Json(r#"{"jsonrpc":"2.0","id":1,"method":"shutdown"}"#)
            ),
            wire(Json(
                r#"[{"jsonrpc":"2.0","id":1,"error":{"code":-32002,
                     "message":"`shutdown` arrived before `initialize`"}}]"#
            )),
            "a request before initialize is refused as not initialized"
        );
        assert_eq!(
            send(
                &mut server,
                Json(r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{}}"#),
            ),
            wire(Json("[]")),
            "a notification before initialize is dropped"
        );
        let _answered = send(
            &mut server,
            Json(r#"{"jsonrpc":"2.0","id":2,"method":"initialize","params":{}}"#),
        );
        assert_eq!(
            send(
                &mut server,
                Json(r#"{"jsonrpc":"2.0","id":3,"method":"initialize","params":{}}"#),
            ),
            wire(Json(
                r#"[{"jsonrpc":"2.0","id":3,"error":{"code":-32600,
                     "message":"`initialize` was already answered"}}]"#
            )),
            "a second initialize is an invalid request"
        );
        assert_eq!(
            send(
                &mut server,
                Json(
                    r#"{"jsonrpc":"2.0","id":4,"method":"textDocument/semanticTokens/full",
                        "params":{}}"#
                ),
            ),
            wire(Json(
                r#"[{"jsonrpc":"2.0","id":4,"error":{"code":-32602,
                     "message":"missing field `textDocument`"}}]"#
            )),
            "parameters the method cannot read are invalid"
        );
        assert_eq!(
            send(
                &mut server,
                Json(r#"{"jsonrpc":"2.0","method":"$/cancelRequest","params":{"id":4}}"#),
            ),
            wire(Json("[]")),
            "a `$/` notification is ignored"
        );
        assert_eq!(
            server.closed(),
            Served::Abrupt,
            "closing before shutdown is abrupt"
        );
        assert_eq!(
            send(
                &mut server,
                Json(r#"{"jsonrpc":"2.0","id":5,"method":"shutdown","params":null}"#)
            ),
            wire(Json(r#"[{"jsonrpc":"2.0","id":5,"result":null}]"#)),
            "shutdown answers null"
        );
        assert_eq!(
            send(
                &mut server,
                Json(
                    r#"{"jsonrpc":"2.0","id":6,"method":"textDocument/semanticTokens/full",
                        "params":{}}"#
                ),
            ),
            wire(Json(
                r#"[{"jsonrpc":"2.0","id":6,"error":{"code":-32600,
                     "message":"`textDocument/semanticTokens/full` arrived after `shutdown`"}}]"#
            )),
            "a request after shutdown is an invalid request"
        );
        let exit = Body::from(br#"{"jsonrpc":"2.0","method":"exit"}"#.to_vec());
        assert_eq!(
            server.handle(&exit).flow,
            Flow::Exit(Served::Clean),
            "exit after shutdown ends the session cleanly"
        );
        assert_eq!(
            Server::default().handle(&exit).flow,
            Flow::Exit(Served::Abrupt),
            "exit before shutdown ends it abruptly"
        );
    }

    #[test]
    fn synchronisation_publishes_and_close_clears()
    {
        let mut server = server_over_the_known_document();
        let changed = send(
            &mut server,
            Json(
                r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{
                    "textDocument":{"uri":"file:///tmp/example.gandr","version":2},
                    "contentChanges":[{"text":"def g = 1 ;\n"},{"text":"def g = missing ;\n"}]}}"#,
            ),
        );
        assert_eq!(
            changed.pointer("/0/params/diagnostics/0/code"),
            Some(&wire(Json(r#""UnresolvedName""#))),
            "the last change is the document, rechecked whole: {changed}"
        );
        assert_eq!(
            changed.pointer("/0/params/version"),
            Some(&wire(Json("2"))),
            "published at the changed version"
        );
        assert_eq!(
            send(
                &mut server,
                Json(
                    r#"{"jsonrpc":"2.0","method":"textDocument/didClose",
                        "params":{"textDocument":{"uri":"file:///tmp/example.gandr"}}}"#
                ),
            ),
            wire(Json(
                r#"[{"jsonrpc":"2.0","method":"textDocument/publishDiagnostics",
                     "params":{"uri":"file:///tmp/example.gandr","diagnostics":[]}}]"#
            )),
            "closing clears the document's diagnostics"
        );
        assert_eq!(
            send(
                &mut server,
                Json(
                    r#"{"jsonrpc":"2.0","id":9,"method":"textDocument/semanticTokens/full",
                        "params":{"textDocument":{"uri":"file:///tmp/example.gandr"}}}"#
                ),
            ),
            wire(Json(r#"[{"jsonrpc":"2.0","id":9,"result":null}]"#)),
            "a closed document has no tokens"
        );
    }
}
