//! The server: a state machine over classified messages, and the loop that
//! drives it over a pair of byte streams and a log.
//!
//! The lifecycle is the protocol's. Before `initialize` is answered every
//! request is refused as not initialized and every notification but `exit` is
//! dropped; a second `initialize` is an invalid request; after `shutdown`
//! every request is an invalid request. `exit` ends the session, successfully
//! after `shutdown` and abruptly before it; a stream closed without `exit`
//! ends it the same way. A notification is never answered: one whose
//! parameters the server cannot read is dropped, and `$/` notifications and
//! every other unknown one are ignored, as the protocol admits.
//!
//! A synchronisation publishes its diagnostics off the document's judgement,
//! then [`Server::admit`] runs the kernel admission the judgement left and
//! [`serve`] logs the timing line carrying both walls: an editor reads the
//! reports before the kernel has re-derived them, and a disagreement the
//! admission finds is published in their place.

use alloc::collections::BTreeMap;
use core::fmt;
use std::io::BufRead;
use std::io::Write;

use anodized::spec;
use gandr_surface_render_remote::LineIndex;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;
use serde_json::Value;

use crate::position::Range;
use crate::protocol::Answer;
use crate::protocol::ContentChange;
use crate::protocol::DidChangeParams;
use crate::protocol::DidOpenParams;
use crate::protocol::DocumentParams;
use crate::protocol::DocumentUri;
use crate::protocol::DocumentVersion;
use crate::protocol::InitializeResult;
use crate::protocol::PublishParams;
use crate::protocol::RangeParams;
use crate::protocol::SemanticTokens;
use crate::recheck::DocumentSession;
use crate::recheck::Timing;
use crate::recheck::admit;
use crate::recheck::highlight;
use crate::recheck::open;
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

/// One open document, as the client last synchronised it, and the session
/// its revisions are submitted to.
struct Document
{
    /// The version of its text.
    version: DocumentVersion,
    /// Its whole text.
    text: String,
    /// The session holding its forms between synchronisations.
    session: DocumentSession,
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

/// One synchronisation's line in the server log: the document, the version
/// it reached, and what rechecking it cost.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Logged
{
    /// The document synchronised.
    uri: DocumentUri,
    /// The version it reached.
    version: DocumentVersion,
    /// What rechecking it cost.
    timing: Timing,
}

impl fmt::Display for Logged
{
    /// Writes the document, its version and the recheck's timing, one line.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `<uri> at version <version>: <timing>`, no terminator.
    /// - panics: none.
    /// - executable: none — the formatter exposes neither its written bytes nor
    ///   its sink's failure state.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the transcript reads each logged line back, naming
    ///   the document and the version it was synchronised to.
    /// - witness: `session::session::an_edit_to_a_large_document_rechecks_its_forms`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(
            f,
            "{} at version {}: {}",
            self.uri, self.version, self.timing
        )
    }
}

/// What handling one message produced: the messages to write, in order, the
/// lines to log, and whether the session goes on.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Outcome
{
    /// The messages to write, in order.
    pub messages: Vec<Outgoing>,
    /// The lines to log, in order.
    pub log: Vec<Logged>,
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
            log: Vec::new(),
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
            log: Vec::new(),
            flow: Flow::Continue,
        }
    }
}

/// The server's state: where it stands in the lifecycle, and every open
/// document.
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
    ///   diagnostics off its session's judgement of the whole text and logs one
    ///   timing line, its admission left for [`Server::admit`] — opening and
    ///   changing it publish its diagnostics at its new version, closing it
    ///   publishes none and forgets it. A body that is not a message is
    ///   answered with the error the protocol owes it. `exit` ends the session.
    /// - provides: the whole of the server's behaviour but the admission
    ///   [`Server::admit`] runs after it; [`serve`] only moves bytes.
    /// - fails: never; every refusal is a message to the client.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — pinned capability and token objects distinguish wrong
    ///   answers for the known document. L3 — lifecycle boundaries, range
    ///   shapes, refusal publications and ignored messages distinguish wrong
    ///   codes, extra replies and forbidden document mutations.
    /// - witness: `server::tests::initialize_advertises_the_token_legend`
    /// - witness: `server::tests::semantic_tokens_full_answers_a_known_document`
    /// - witness: `server::tests::a_range_returns_only_the_tokens_it_covers`
    /// - witness: `server::tests::a_refused_program_is_published_as_an_editor_diagnostic`
    /// - witness: `server::tests::the_lifecycle_admits_requests_in_the_protocol_order`
    /// - witness: `server::tests::synchronisation_publishes_and_close_clears`
    /// - witness: `server::tests::ignored_messages_and_empty_changes_preserve_document_text`
    #[spec(
        captures: phase = self.phase,
        ensures: |ret| ret.messages.len() <= 1 && ret.log.len() <= ret.messages.len()
            && (self.phase == phase || matches!((phase, self.phase),
                (Phase::Waiting, Phase::Running) | (Phase::Running, Phase::ShuttingDown)))
            && match ret.flow { Flow::Continue => true, Flow::Exit(ending) =>
                ret.messages.is_empty() && ending == self.closed() },
    )]
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
    #[spec(ensures: |ret| matches!((self.phase, ret),
        (Phase::ShuttingDown, Served::Clean) | (Phase::Waiting | Phase::Running, Served::Abrupt)))]
    #[inline]
    #[must_use]
    pub const fn closed(&self) -> Served
    {
        match self.phase {
            | Phase::ShuttingDown => Served::Clean,
            | Phase::Waiting | Phase::Running => Served::Abrupt,
        }
    }

    /// Run the kernel admission each synchronisation logged in `log` left, its
    /// diagnostics already published, and return what to publish in their
    /// place.
    ///
    /// # Specification
    /// - requires: `log` is the log of the outcome [`Server::handle`] returned
    ///   last, its messages already written.
    /// - ensures: each line naming a held document at its held version runs the
    ///   admission that document's session holds, as [`admit`] states, and
    ///   carries its wall; a kernel disagreement adds one diagnostic
    ///   notification at the line's URI and version whose one diagnostic names
    ///   it. Every other line is left as it was.
    /// - provides: the second half of every synchronisation; [`serve`] writes
    ///   what it returns, then logs the lines.
    /// - fails: never; a disagreement is a diagnostic.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a change's logged line gains the admission's wall and
    ///   publishes nothing more when the kernel agrees; a line naming a closed
    ///   document is left as it was.
    /// - witness: `server::tests::an_admission_follows_its_synchronisation`
    /// - witness: `session::session::an_edit_to_a_large_document_rechecks_its_forms`
    #[spec(ensures: |ret| ret.len() <= log.len() && ret.iter().all(|message| matches!(*message,
        Outgoing::Notification { method: "textDocument/publishDiagnostics", ref params, .. }
            if params.diagnostics.len() == 1 && log.iter().any(|logged|
                logged.uri == params.uri && Some(logged.version) == params.version))))]
    #[inline]
    #[must_use]
    pub fn admit(
        &mut self,
        log: &mut [Logged],
    ) -> Vec<Outgoing>
    {
        let mut corrections = Vec::new();
        for logged in &mut *log {
            let Some(document) = self
                .documents
                .get_mut(&logged.uri)
                .filter(|document| document.version == logged.version)
            else {
                continue;
            };
            let admitted = admit(&mut document.session, logged.timing);
            logged.timing = admitted.timing;
            if let Maybe::Present(fault) = admitted.fault {
                corrections.push(publish(PublishParams {
                    uri: logged.uri.clone(),
                    version: Some(logged.version),
                    diagnostics: vec![fault],
                }));
            }
        }
        corrections
    }

    /// The response to the request `id` calling `method` with `params`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: initialization and shutdown advance the lifecycle once; other
    ///   requests preserve it and every request preserves open documents. The
    ///   response echoes the identifier and carries the method result or its
    ///   lifecycle, unknown-method or invalid-parameter error.
    /// - provides: one response per request.
    /// - fails: refusals are error responses, never Rust errors.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every lifecycle boundary and invalid parameters are
    ///   observed through response identifiers, exact error codes and session
    ///   ending; L2 — token responses agree with pinned streams.
    /// - witness: `server::tests::the_lifecycle_admits_requests_in_the_protocol_order`
    /// - witness: `server::tests::semantic_tokens_full_answers_a_known_document`
    #[spec(
        captures: [phase = self.phase, documents = self.documents.len()],
        ensures: |ret| self.documents.len() == documents && match (phase, method.as_ref()) {
            (Phase::Waiting, "initialize") => self.phase == Phase::Running
                && matches!(ret, Outgoing::Success { result: Answer::Initialize(_), .. }),
            (Phase::Waiting, _) => self.phase == phase && matches!(ret,
                Outgoing::Failure { ref error, .. } if error.code == ErrorCode::SERVER_NOT_INITIALIZED),
            (Phase::Running, "shutdown") => self.phase == Phase::ShuttingDown
                && matches!(ret, Outgoing::Success { result: Answer::Nothing, .. }),
            (Phase::Running, "initialize") | (Phase::ShuttingDown, _) => self.phase == phase
                && matches!(ret, Outgoing::Failure { ref error, .. } if error.code == ErrorCode::INVALID_REQUEST),
            (Phase::Running, "textDocument/semanticTokens/full" | "textDocument/semanticTokens/range") =>
                self.phase == phase && match ret {
                    Outgoing::Success { result: Answer::Nothing | Answer::Tokens(_), .. } => true,
                    Outgoing::Failure { ref error, .. } => error.code == ErrorCode::INVALID_PARAMS,
                    _ => false,
                },
            (Phase::Running, _) => self.phase == phase && matches!(ret,
                Outgoing::Failure { ref error, .. } if error.code == ErrorCode::METHOD_NOT_FOUND),
        },
    )]
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
    /// - requires: nothing.
    /// - ensures: notifications preserve the lifecycle and never send
    ///   responses. Exit ends the session; running-state opens and changes
    ///   publish the held document at its supplied version and log one timing
    ///   line. An open starts the document's session afresh; a change applies
    ///   each content change in order, as [`apply`] states. An empty change
    ///   list preserves text. Close forgets the named document and publishes a
    ///   versionless empty diagnostic list, even for an unknown URI. Unknown,
    ///   malformed and out-of-phase notifications leave documents alone.
    /// - provides: document synchronization and termination.
    /// - fails: unreadable parameters and changes to unknown documents are
    ///   ignored.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — open/change/close, empty change lists, unknown URIs,
    ///   malformed notifications and each lifecycle phase distinguish extra
    ///   responses, wrong versions and destructive updates through exact token
    ///   streams, publications and endings.
    /// - witness: `server::tests::synchronisation_publishes_and_close_clears`
    /// - witness: `server::tests::the_lifecycle_admits_requests_in_the_protocol_order`
    /// - witness: `server::tests::ignored_messages_and_empty_changes_preserve_document_text`
    /// - witness: `server::tests::ranged_changes_edit_the_held_text_in_order`
    #[spec(
        captures: [phase = self.phase, count = self.documents.len()],
        ensures: |ret| self.phase == phase && ret.messages.len() <= 1
            && ret.log.len() == usize::from(matches!(method.as_ref(), "textDocument/didOpen" | "textDocument/didChange")
                && !ret.messages.is_empty())
            && ret.flow == if method.as_ref() == "exit" { Flow::Exit(self.closed()) } else { Flow::Continue }
            && if ret.messages.is_empty() { self.documents.len() == count } else {
                phase == Phase::Running && ret.messages.iter().all(|message| match *message {
                    Outgoing::Notification { ref params, .. } => match method.as_ref() {
                        "textDocument/didOpen" | "textDocument/didChange" =>
                            self.documents.get(&params.uri).is_some_and(|document| params.version == Some(document.version)),
                        "textDocument/didClose" => params.version.is_none() && params.diagnostics.is_empty()
                            && !self.documents.contains_key(&params.uri),
                        _ => false,
                    },
                    _ => false,
                })
            },
    )]
    fn notification(
        &mut self,
        method: &Method,
        params: Value,
    ) -> Outcome
    {
        match (self.phase, method.as_ref()) {
            | (_, "exit") => Outcome {
                messages: Vec::new(),
                log: Vec::new(),
                flow: Flow::Exit(self.closed()),
            },
            | (Phase::Running, "textDocument/didOpen") => {
                let Ok(DidOpenParams { text_document }) = serde_json::from_value(params)
                else {
                    return Outcome::quiet();
                };
                let mut document = Document {
                    version: text_document.version,
                    text: text_document.text,
                    session: open(&text_document.uri),
                };
                let outcome = synchronised(&text_document.uri, &mut document);
                let _prior = self.documents.insert(text_document.uri, document);
                outcome
            },
            | (Phase::Running, "textDocument/didChange") => {
                let Ok(DidChangeParams {
                    text_document,
                    content_changes,
                }) = serde_json::from_value(params)
                else {
                    return Outcome::quiet();
                };
                let Some(document) = self.documents.get_mut(&text_document.uri)
                else {
                    return Outcome::quiet();
                };
                document.version = text_document.version;
                for change in content_changes {
                    apply(&mut document.text, change);
                }
                synchronised(&text_document.uri, document)
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
    /// - requires: nothing; an unknown URI and any range are admitted.
    /// - ensures: an unknown document yields Nothing; a held document yields a
    ///   token stream, restricted to overlapping whole spans for a range
    ///   request. Empty and inverted ranges yield an empty stream, not Nothing.
    /// - provides: full and range token answers in document coordinates.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — known/unknown documents and empty, inverted, partial
    ///   and whole ranges distinguish null from empty, clipping and delta
    ///   shifts through exact wire streams for the known three-token document.
    /// - witness: `server::tests::semantic_tokens_full_answers_a_known_document`
    /// - witness: `server::tests::a_range_returns_only_the_tokens_it_covers`
    /// - witness: `server::tests::a_token_straddling_the_range_edge_is_returned_whole`
    /// - witness: `server::tests::an_empty_range_yields_no_tokens`
    /// - witness: `server::tests::an_inverted_range_yields_no_tokens`
    #[spec(ensures: |ret| match ret {
        Answer::Nothing => !self.documents.contains_key(uri),
        Answer::Tokens(ref tokens) => self.documents.contains_key(uri)
            && tokens.data.as_ref().len().is_multiple_of(5)
            && match window { Window::Within(range) if range.start >= range.end => tokens.data.as_ref().is_empty(), _ => true },
        Answer::Initialize(_) => false,
    })]
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

/// `text` with `change` applied.
///
/// # Specification
/// - requires: nothing; any range is admissible input.
/// - ensures: a change naming no range replaces the whole text; a ranged one
///   replaces the bytes between its two ends, each resolved through the line
///   index of the text as it stands as [`crate::position::Position::byte`]
///   states, an end before the start read as the start.
/// - provides: incremental synchronisation, with full synchronisation as the
///   change that names no range.
/// - fails: never.
/// - panics: none; a resolved end is always a character boundary.
///
/// # Adequacy
/// - hypothesis: L3 — successive ranged changes, one after a character beyond
///   the basic plane, an inverted range, and a rangeless change, each asserted
///   at the exact text it leaves.
/// - witness: `server::tests::ranged_changes_edit_the_held_text_in_order`
#[spec(
    captures: [length = text.len(), replaced = change.text.len(), whole = change.range.is_none()],
    ensures: |_| if whole { text.len() == replaced }
        else { replaced <= text.len() && text.len() <= length.saturating_add(replaced) },
)]
fn apply(
    text: &mut String,
    change: ContentChange,
)
{
    let Some(range) = change.range
    else {
        *text = change.text;
        return;
    };
    let index = LineIndex::new(text.as_str().into());
    let start = usize::from(range.start.byte(&index));
    let end = usize::from(range.end.byte(&index)).max(start);
    text.replace_range(start .. end, &change.text);
}

/// Recheck `document`, open at `uri`: the notification publishing its
/// diagnostics and the line logging what the recheck cost.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one diagnostic notification naming the supplied URI and held
///   version, with the diagnostics the document's session judges for its whole
///   text, and one log line naming the same URI and version, its admission
///   pending when the judgement left one.
/// - provides: the publication shared by open and change notifications.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — opening and changing the known document, including a
///   refusal and an empty change list, distinguish wrong URI, version and stale
///   text through exact publications and subsequent token streams.
/// - witness: `server::tests::synchronisation_publishes_and_close_clears`
/// - witness: `server::tests::ignored_messages_and_empty_changes_preserve_document_text`
/// - witness: `session::session::an_edit_to_a_large_document_rechecks_its_forms`
#[spec(ensures: |ret| ret.flow == Flow::Continue
    && matches!(*ret.messages.as_slice(), [Outgoing::Notification { method: "textDocument/publishDiagnostics", ref params, .. }]
        if params.uri == *uri && params.version == Some(document.version))
    && matches!(*ret.log.as_slice(), [ref logged] if logged.uri == *uri && logged.version == document.version))]
fn synchronised(
    uri: &DocumentUri,
    document: &mut Document,
) -> Outcome
{
    let rechecked = recheck(
        uri,
        &mut document.session,
        SourceText::from(document.text.as_str()),
    );
    Outcome {
        messages: vec![publish(PublishParams {
            uri: uri.clone(),
            version: Some(document.version),
            diagnostics: rechecked.diagnostics,
        })],
        log: vec![Logged {
            uri: uri.clone(),
            version: document.version,
            timing: rechecked.timing,
        }],
        flow: Flow::Continue,
    }
}

/// Serve the protocol over `input` and `output` until the session ends,
/// writing each synchronisation's timing line to `log`.
///
/// # Specification
/// - requires: nothing of the streams; `input` carries the client's frames,
///   `output` takes the server's, and `log` takes the operator's lines.
/// - ensures: each frame read is handled by one [`Server`], and every message
///   it produces is written as one frame, in order; then the admissions its
///   synchronisations left run, as [`Server::admit`] states, each correction
///   written as one frame, and every line logged is written to `log` with a
///   line terminator, before the next frame is read; the session ends at `exit`
///   or at a stream closed at a frame boundary, as [`Server::closed`] states. A
///   line `log` refuses is dropped: the log is the operator's, and the protocol
///   never depends on it.
/// - provides: the language server over any pair of streams and a log: the
///   driver's standard input, output and error, or memory.
/// - fails: the first [`TransportFault`] of either protocol stream, and
///   [`TransportFault::Encode`] for a message that does not encode.
/// - panics: none.
/// - executable: none — generic streams expose neither their consumed nor
///   emitted transcript; the returned ending or fault cannot reconstruct
///   lifecycle transitions, frame order or the failing stream operation.
///
/// # Errors
/// [`TransportFault`], as above.
///
/// # Adequacy
/// - hypothesis: L2 — a whole session over in-memory streams, from `initialize`
///   to `exit`, asserted frame by frame; L3 — a session closed without `exit`,
///   one whose stream breaks inside a frame, and an editor-shaped edit to a
///   large document whose log carries one timing line per synchronisation.
/// - witness: `session::session::a_session_round_trips_over_in_memory_streams`
/// - witness: `session::session::a_stream_closed_without_exit_ends_abruptly`
/// - witness: `session::session::an_edit_to_a_large_document_rechecks_its_forms`
#[inline]
pub fn serve<Input, Output, Log>(
    input: &mut Input,
    output: &mut Output,
    log: &mut Log,
) -> Result<Served, TransportFault>
where
    Input: BufRead,
    Output: Write,
    Log: Write,
{
    let mut server = Server::default();
    loop {
        let read = read_frame(input)?;
        let Maybe::Present(body) = read
        else {
            return Ok(server.closed());
        };
        let mut outcome = server.handle(&body);
        for message in &outcome.messages {
            let encoded = serde_json::to_vec(message).map_err(TransportFault::Encode)?;
            write_frame(output, &Body::from(encoded))?;
        }
        for message in &server.admit(&mut outcome.log) {
            let encoded = serde_json::to_vec(message).map_err(TransportFault::Encode)?;
            write_frame(output, &Body::from(encoded))?;
        }
        for line in &outcome.log {
            let _unlogged = writeln!(log, "{line}");
        }
        if let Flow::Exit(served) = outcome.flow {
            return Ok(served);
        }
    }
}

#[cfg(test)]
mod tests
{
    use anodized::spec;
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
    /// - requires: text is valid JSON accepted by the decoder.
    /// - ensures: the decoded value preserves its JSON kind and content.
    /// - provides: independent wire goldens for protocol assertions.
    /// - fails: never in the valid domain.
    /// - panics: rejected JSON violates the requirement.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — object and array goldens in lifecycle and token tests
    ///   distinguish wrong shapes and values; primitive fields are read
    ///   exactly.
    /// - witness: `server::tests::the_lifecycle_admits_requests_in_the_protocol_order`
    /// - witness: `server::tests::semantic_tokens_full_answers_a_known_document`
    #[spec(ensures: |ret| match text.trim_start().as_bytes().first().copied() {
        Some(b'[') => ret.is_array(), Some(b'{') => ret.is_object(),
        Some(b'"') => ret.is_string(), Some(b't' | b'f') => ret.is_boolean(),
        Some(b'n') => ret.is_null(), _ => ret.is_number(),
    })]
    fn wire(Json(text): Json<'_>) -> Value
    {
        serde_json::from_str(text).expect("a test's JSON parses")
    }

    /// The messages `server` writes for the message `json` spells, as one
    /// JSON array.
    ///
    /// # Specification
    /// - requires: nothing; malformed bodies are admitted.
    /// - ensures: serialized outgoing messages remain in order, with at most
    ///   one response or publication and JSON-RPC version 2.0.
    /// - provides: the protocol-visible result of one state-machine step.
    /// - fails: never for the current serializable outgoing variants.
    /// - panics: an unencodable outgoing value violates the serialization
    ///   premise.
    ///
    /// # Adequacy
    /// - hypothesis: L2/L3 — capability, token, lifecycle and synchronization
    ///   goldens distinguish lost, duplicate and misidentified messages.
    /// - witness: `server::tests::the_lifecycle_admits_requests_in_the_protocol_order`
    /// - witness: `server::tests::synchronisation_publishes_and_close_clears`
    #[spec(ensures: |ret| ret.as_array().is_some_and(|messages|
        messages.len() <= 1 && messages.iter().all(|message|
            message.get("jsonrpc").and_then(Value::as_str) == Some("2.0"))))]
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
    /// - requires: nothing.
    /// - ensures: the server is running with no open documents.
    /// - provides: a session ready for document operations.
    /// - fails: never.
    /// - panics: an incorrect initialization response fails the witness.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — subsequent known-document requests distinguish a
    ///   waiting or closed fixture from the required running state.
    /// - witness: `server::tests::semantic_tokens_full_answers_a_known_document`
    #[spec(ensures: |ret| ret.phase == super::Phase::Running && ret.documents.is_empty())]
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
    /// - requires: nothing.
    /// - ensures: the running server holds only the known three-token document
    ///   at its specified URI and text.
    /// - provides: a fixed source for range and synchronization witnesses.
    /// - fails: never.
    /// - panics: an initialization failure fails the fixture.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a pinned full token stream distinguishes changed text
    ///   or an unopened fixture; range goldens distinguish incorrect URI
    ///   lookup.
    /// - witness: `server::tests::semantic_tokens_full_answers_a_known_document`
    /// - witness: `server::tests::a_range_returns_only_the_tokens_it_covers`
    #[spec(ensures: |ret| ret.phase == super::Phase::Running
        && ret.documents.len() == 1
        && ret.documents.values().all(|document| document.text == "def f = 42 ;\n"))]
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
    /// - requires: range decodes as a protocol Range.
    /// - ensures: the known document answers a token array in five-integer
    ///   groups; the range selects whole overlapping spans in document
    ///   coordinates.
    /// - provides: the wire observation of a range request.
    /// - fails: never in the valid domain.
    /// - panics: a malformed range violates the requirement.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — whole, partial, touching, empty and inverted ranges
    ///   distinguish clipping, shifted deltas and null answers through exact
    ///   arrays.
    /// - witness: `server::tests::a_range_returns_only_the_tokens_it_covers`
    /// - witness: `server::tests::a_token_straddling_the_range_edge_is_returned_whole`
    /// - witness: `server::tests::an_empty_range_yields_no_tokens`
    /// - witness: `server::tests::an_inverted_range_yields_no_tokens`
    #[spec(requires: serde_json::from_str::<crate::position::Range>(range).is_ok(),
        ensures: |ret| ret.as_array().is_some_and(|integers|
            integers.len().is_multiple_of(5) && integers.iter().all(Value::is_u64)))]
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
                        "textDocumentSync":{"openClose":true,"change":2},
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
        let mut publication = send(
            &mut server,
            Json(
                r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":
                {"uri":"file:///tmp/refused.gandr","languageId":"gandr","version":3,
                 "text":"def answer = 42 ;\ndef broken = missing ;\n"}}}"#,
            ),
        );
        publication
            .pointer_mut("/0/params/diagnostics/0")
            .and_then(Value::as_object_mut)
            .expect("a diagnostic object")
            .remove("message");
        assert_eq!(
            publication,
            wire(Json(
                r#"[{"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{
                "uri":"file:///tmp/refused.gandr","version":3,"diagnostics":[{
                    "range":{"start":{"line":1,"character":13},"end":{"line":1,"character":20}},
                    "severity":1,"code":"UnresolvedName","source":"gandr"}]}}]"#,
            ))
        );
    }

    #[test]
    fn the_lifecycle_admits_requests_in_the_protocol_order()
    {
        let assert_error = |messages: Value, id: Value, code: i64| {
            assert_eq!(messages.as_array().map(Vec::len), Some(1_usize));
            assert_eq!(
                messages.pointer("/0/jsonrpc").and_then(Value::as_str),
                Some("2.0")
            );
            assert_eq!(messages.pointer("/0/id"), Some(&id));
            assert_eq!(
                messages.pointer("/0/error/code").and_then(Value::as_i64),
                Some(code)
            );
            assert!(messages.pointer("/0/result").is_none());
        };
        let mut server = Server::default();
        assert_error(
            send(
                &mut server,
                Json(r#"{"jsonrpc":"2.0","id":1,"method":"shutdown"}"#),
            ),
            serde_json::json!(1_i32),
            -32_002,
        );
        assert_eq!(
            send(
                &mut server,
                Json(r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{}}"#)
            ),
            serde_json::json!([])
        );
        let initialized = send(
            &mut server,
            Json(r#"{"jsonrpc":"2.0","id":2,"method":"initialize"}"#),
        );
        assert_eq!(
            initialized
                .pointer("/0/result/capabilities/positionEncoding")
                .and_then(Value::as_str),
            Some("utf-16")
        );
        for (request, id, code) in [
            (
                r#"{"jsonrpc":"2.0","id":3,"method":"initialize"}"#,
                serde_json::json!(3_i32),
                -32_600_i64,
            ),
            (
                r#"{"jsonrpc":"2.0","id":4,"method":"textDocument/semanticTokens/full","params":{}}"#,
                serde_json::json!(4_i32),
                -32_602,
            ),
            (
                r#"{"jsonrpc":"2.0","id":5,"method":"textDocument/semanticTokens/range","params":{}}"#,
                serde_json::json!(5_i32),
                -32_602,
            ),
            (
                r#"{"jsonrpc":"2.0","id":"correlation","method":"unknown"}"#,
                serde_json::json!("correlation"),
                -32_601,
            ),
        ] {
            assert_error(send(&mut server, Json(request)), id, code);
        }
        assert_eq!(server.closed(), Served::Abrupt);
        assert_eq!(
            send(
                &mut server,
                Json(r#"{"jsonrpc":"2.0","id":8,"method":"shutdown","params":null}"#)
            ),
            serde_json::json!([{"jsonrpc":"2.0","id":8_i32,"result":null}])
        );
        assert_error(
            send(
                &mut server,
                Json(r#"{"jsonrpc":"2.0","id":9,"method":"initialize"}"#),
            ),
            serde_json::json!(9_i32),
            -32_600,
        );
        assert_eq!(server.closed(), Served::Clean);
        let exit = Body::from(br#"{"jsonrpc":"2.0","method":"exit"}"#.to_vec());
        for (phase, expected) in [
            (super::Phase::Waiting, Served::Abrupt),
            (super::Phase::Running, Served::Abrupt),
            (super::Phase::ShuttingDown, Served::Clean),
        ] {
            let mut server = Server {
                phase,
                ..Server::default()
            };
            let outcome = server.handle(&exit);
            assert_eq!(outcome.flow, Flow::Exit(expected));
            assert!(outcome.messages.is_empty());
        }
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

    #[test]
    fn an_admission_follows_its_synchronisation()
    {
        let mut server = server_over_the_known_document();
        let body = Body::from(
            br#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{
                "textDocument":{"uri":"file:///tmp/example.gandr","version":2},
                "contentChanges":[{"text":"def g : Integer ;\ndef g = 1 ;\n"}]}}"#
                .to_vec(),
        );
        let mut outcome = server.handle(&body);
        let [ref published] = *outcome.log.as_slice()
        else {
            panic!("one timing line per synchronisation");
        };
        assert!(
            !published.to_string().contains("admitted"),
            "the diagnostics are published before the admission: {published}"
        );
        assert_eq!(
            server.admit(&mut outcome.log),
            Vec::new(),
            "the kernel agrees, so nothing replaces the published diagnostics"
        );
        let [ref admitted] = *outcome.log.as_slice()
        else {
            panic!("the admission keeps the line");
        };
        assert!(
            admitted.to_string().contains(", admitted in "),
            "the logged line carries the admission's wall: {admitted}"
        );
        let closed = Body::from(
            br#"{"jsonrpc":"2.0","method":"textDocument/didClose",
                "params":{"textDocument":{"uri":"file:///tmp/example.gandr"}}}"#
                .to_vec(),
        );
        let _cleared = server.handle(&closed);
        let mut stale = server.handle(&body).log;
        assert_eq!(
            stale,
            Vec::new(),
            "a change to a closed document logs nothing"
        );
        assert_eq!(server.admit(&mut stale), Vec::new());
    }

    #[test]
    fn ranged_changes_edit_the_held_text_in_order()
    {
        let mut server = server_over_the_known_document();
        let uri = crate::protocol::DocumentUri::from("file:///tmp/example.gandr");
        let held = |server: &Server| {
            server
                .documents
                .get(&uri)
                .map(|document| document.text.clone())
                .expect("the document is open")
        };
        let changed = send(
            &mut server,
            Json(
                r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{
                    "textDocument":{"uri":"file:///tmp/example.gandr","version":2},
                    "contentChanges":[
                        {"range":{"start":{"line":0,"character":8},"end":{"line":0,"character":10}},"text":"7"},
                        {"range":{"start":{"line":1,"character":0},"end":{"line":1,"character":0}},"text":"def g = \"𝄞\" ;\n"},
                        {"range":{"start":{"line":1,"character":11},"end":{"line":1,"character":12}},"text":"x\""},
                        {"range":{"start":{"line":0,"character":10},"end":{"line":0,"character":8}},"text":"!"}
                    ]}}"#,
            ),
        );
        assert_eq!(
            changed.pointer("/0/params/version"),
            Some(&serde_json::json!(2_i32))
        );
        assert_eq!(
            held(&server),
            "def f = 7 !;\ndef g = \"𝄞x\" ;\n",
            "each change applies to the text the ones before it left, counted in UTF-16 units, \
             an inverted range inserting at its start"
        );
        let restored = send(
            &mut server,
            Json(
                r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{
                    "textDocument":{"uri":"file:///tmp/example.gandr","version":3},
                    "contentChanges":[{"text":"def f = 42 ;\n"}]}}"#,
            ),
        );
        assert_eq!(
            held(&server),
            "def f = 42 ;\n",
            "a rangeless change replaces the whole text"
        );
        assert_eq!(
            restored.pointer("/0/params/diagnostics"),
            Some(&serde_json::json!([]))
        );
    }

    #[test]
    fn ignored_messages_and_empty_changes_preserve_document_text()
    {
        let mut server = server_over_the_known_document();
        let tokens = Json(
            r#"{"jsonrpc":"2.0","id":9,"method":"textDocument/semanticTokens/full","params":{"textDocument":{"uri":"file:///tmp/example.gandr"}}}"#,
        );
        let expected = wire(Json("[0,0,3,0,0,0,4,1,2,1,0,4,2,9,0]"));
        for ignored in [
            r#"{"jsonrpc":"2.0","id":10,"result":null}"#,
            r#"{"jsonrpc":"2.0","method":"$/cancelRequest","params":{"id":9}}"#,
            r#"{"jsonrpc":"2.0","method":"unknown"}"#,
            r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///tmp/example.gandr","version":2,"text":3}}}"#,
            r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///tmp/example.gandr","version":2},"contentChanges":3}}"#,
            r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///tmp/unknown.gandr","version":2},"contentChanges":[{"text":""}]}}"#,
            r#"{"jsonrpc":"2.0","method":"textDocument/didClose","params":{"textDocument":{"uri":3}}}"#,
        ] {
            assert_eq!(send(&mut server, Json(ignored)), serde_json::json!([]));
            assert_eq!(
                send(&mut server, tokens).pointer("/0/result/data"),
                Some(&expected)
            );
        }
        let changed = send(
            &mut server,
            Json(
                r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///tmp/example.gandr","version":17},"contentChanges":[]}}"#,
            ),
        );
        assert_eq!(
            changed.pointer("/0/params/version"),
            Some(&serde_json::json!(17_i32))
        );
        assert_eq!(
            changed.pointer("/0/params/diagnostics"),
            Some(&serde_json::json!([]))
        );
        assert_eq!(
            send(&mut server, tokens).pointer("/0/result/data"),
            Some(&expected)
        );
        let closed = send(
            &mut server,
            Json(
                r#"{"jsonrpc":"2.0","method":"textDocument/didClose","params":{"textDocument":{"uri":"file:///tmp/unknown.gandr"}}}"#,
            ),
        );
        assert_eq!(
            closed.pointer("/0/params/diagnostics"),
            Some(&serde_json::json!([]))
        );
        assert!(closed.pointer("/0/params/version").is_none());
        assert_eq!(
            send(&mut server, tokens).pointer("/0/result/data"),
            Some(&expected)
        );
        let _shutdown = send(
            &mut server,
            Json(r#"{"jsonrpc":"2.0","id":11,"method":"shutdown"}"#),
        );
        assert_eq!(
            send(
                &mut server,
                Json(
                    r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///tmp/new.gandr","version":1,"text":""}}}"#
                )
            ),
            serde_json::json!([])
        );
        assert_eq!(server.closed(), Served::Clean);
    }
}
