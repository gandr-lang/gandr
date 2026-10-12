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
use alloc::collections::BTreeSet;
use core::fmt;
use std::io::BufRead;
use std::io::Write;
use std::sync::mpsc::Sender;

use anodized::spec;
use gandr_surface_diagnostics::Verbosity;
use gandr_surface_render_remote::LineIndex;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;
use serde::Deserialize as _;
use serde_json::Value;

use crate::format::edits;
use crate::hover::hover;
use crate::inline::ghost;
use crate::outline::folds;
use crate::outline::selections;
use crate::outline::symbols;
use crate::position::Position;
use crate::position::Range;
use crate::proposal::Proposal;
use crate::proposal::ProposalRefusal;
use crate::proposal::actions;
use crate::proposal::check;
use crate::proposal::ghosts;
use crate::proposal::lenses;
use crate::proposal::notes;
use crate::protocol::Answer;
use crate::protocol::ConfigurationParams;
use crate::protocol::ContentChange;
use crate::protocol::Diagnostic;
use crate::protocol::DidChangeParams;
use crate::protocol::DidOpenParams;
use crate::protocol::DocumentParams;
use crate::protocol::DocumentUri;
use crate::protocol::DocumentVersion;
use crate::protocol::Hover;
use crate::protocol::InitializeParams;
use crate::protocol::InitializeResult;
use crate::protocol::InlineCompletionItem;
use crate::protocol::InlineCompletionList;
use crate::protocol::MarkupContent;
use crate::protocol::PositionParams;
use crate::protocol::PublishParams;
use crate::protocol::RangeParams;
use crate::protocol::SelectionRangeParams;
use crate::protocol::SemanticTokens;
use crate::protocol::Settings;
use crate::protocol::StringValue;
use crate::recheck::DocumentSession;
use crate::recheck::Timing;
use crate::recheck::Tried;
use crate::recheck::admit;
use crate::recheck::grammar;
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

/// What a token or formatting request asks about.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Window
{
    /// The whole document.
    Whole,
    /// What overlaps a range.
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
    /// The diagnostics last published at its version.
    published: Vec<Diagnostic>,
    /// The checked proposals kept for its version, in the order kept.
    proposals: Vec<Proposal>,
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

/// One connection among those a workspace serves.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Peer(u64);

impl From<u64> for Peer
{
    /// The connection numbered `number`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(number: u64) -> Self
    {
        Self(number)
    }
}

/// What every connection to one server shares.
///
/// The open documents with the diagnostics last published for each, which
/// connections hold each open, where to send a connection what another's
/// synchronisation published, and which watchers hear of each change.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a document is held while at least one connection holds it open,
///   and is forgotten with its session once none does.
/// - panics: none.
/// - executable: none — this state carrier has no call boundary; the server's
///   handling carries the executable clauses.
///
/// # Adequacy
/// - hypothesis: L3 — two connections opening, editing, querying and closing
///   one document, and one leaving while the other stays, observe one text, one
///   session and each publication at every holder.
/// - witness: `server::tests::two_connections_share_one_document`
/// - witness: `server::tests::a_departing_connection_leaves_the_others_served`
#[derive(Default)]
pub struct Workspace
{
    /// Every open document, by its URI.
    documents: BTreeMap<DocumentUri, Document>,
    /// The connections holding each open document open.
    holders: BTreeMap<DocumentUri, BTreeSet<Peer>>,
    /// Where each joined connection takes messages another's handling made.
    outboxes: BTreeMap<Peer, Sender<Outgoing>>,
    /// Where each watching connection hears which document changed.
    watchers: BTreeMap<Peer, Sender<DocumentUri>>,
}

impl Workspace
{
    /// Admit `peer`, whose messages from other connections' handling go to
    /// `outbox`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn join(
        &mut self,
        peer: Peer,
        outbox: Sender<Outgoing>,
    )
    {
        let _prior = self.outboxes.insert(peer, outbox);
    }

    /// Admit `peer` as a watcher: the URI of each document a synchronisation
    /// publishes, and of each document forgotten, goes to `watcher`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn watch(
        &mut self,
        peer: Peer,
        watcher: Sender<DocumentUri>,
    )
    {
        let _prior = self.watchers.insert(peer, watcher);
    }

    /// The open documents and the version each is at, in URI order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn held(&self) -> impl Iterator<Item = (&DocumentUri, DocumentVersion)>
    {
        self.documents
            .iter()
            .map(|(uri, document)| (uri, document.version))
    }

    /// The diagnostics last published for the document at `uri`, and the
    /// version they were published at.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `None` for a document no connection holds; otherwise the last
    ///   diagnostics published at the document's held version, empty until its
    ///   first synchronisation publishes.
    /// - provides: a cheap read of what an editor shows, for another face.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a refused change's diagnostics are read back at its
    ///   version; a closed document reads `None`.
    /// - witness: `server::tests::a_workspace_answers_queries_off_its_documents`
    #[spec(ensures: |ret| ret.is_some() == self.documents.contains_key(uri))]
    #[inline]
    #[must_use]
    pub fn published(
        &self,
        uri: &DocumentUri,
    ) -> Option<(DocumentVersion, &[Diagnostic])>
    {
        self.documents
            .get(uri)
            .map(|document| (document.version, document.published.as_slice()))
    }

    /// Judge each of `changes`, applied alone to the document at `uri` as it
    /// stands, without submitting any: the held version and each candidate's
    /// result, best first.
    ///
    /// # Specification
    /// - requires: nothing; any changes are admissible input.
    /// - ensures: `None` for a document no connection holds; otherwise one
    ///   result per change, each the [`crate::recheck::trial`] of the held text
    ///   with that change alone applied as a synchronisation applies it — a
    ///   ranged change splices its text over the range, one naming no range is
    ///   the whole text — ranked as the trial ranks them. The document, its
    ///   session and its published diagnostics are unchanged.
    /// - provides: batched candidate fills at a hole or over a declaration's
    ///   body, for another face.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fill spliced over a hole and a whole replacement
    ///   are judged and ranked, and the document reads back as it was.
    /// - witness: `server::tests::a_workspace_tries_candidate_fills`
    #[spec(ensures: |ret| ret.as_ref().is_none_or(|&(version, ref tried)|
        tried.len() == changes.len() && self.documents.get(uri).is_some_and(|document| document.version == version)))]
    #[inline]
    #[must_use]
    pub fn trial(
        &self,
        uri: &DocumentUri,
        changes: &[ContentChange],
    ) -> Option<(DocumentVersion, Vec<Tried>)>
    {
        let document = self.documents.get(uri)?;
        let texts: Vec<String> = changes
            .iter()
            .map(|change| {
                let mut text = document.text.clone();
                apply(&mut text, change.clone());
                text
            })
            .collect();
        let candidates: Vec<SourceText<'_>> = texts
            .iter()
            .map(|text| SourceText::from(text.as_str()))
            .collect();
        Some((
            document.version,
            crate::recheck::trial(uri, &document.session, &candidates),
        ))
    }

    /// Keep `proposal`, a model's fill of a range of the document at `uri`
    /// made against `version`, once it checks.
    ///
    /// # Specification
    /// - requires: nothing; any proposal is admissible input.
    /// - ensures: a document no connection holds, or one whose version is not
    ///   `version`, refuses the proposal and keeps nothing. Otherwise the
    ///   document with the fill applied is tried as [`Self::trial`] tries a
    ///   change; a fill that passes [`check`] against the published diagnostics
    ///   is kept beside the document, after those kept before, and its trial's
    ///   diagnostics answered; one that does not is refused with them. The
    ///   document's text, session and published diagnostics are unchanged.
    /// - provides: the one way a model's output reaches an editor.
    /// - fails: as above, with the reason in the refusal.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ProposalRefusal`] for a document not held, a stale version, or a
    /// fill that does not check.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fill settling a hole is kept, a fill leaving the
    ///   refusal and a fill refused whole are refused, a stale version is
    ///   refused, and the next edit withdraws what was kept.
    /// - witness: `server::tests::a_proposal_is_kept_only_once_it_checks`
    #[spec(
        captures: kept = self.documents.get(uri).map_or(0_usize, |document| document.proposals.len()),
        ensures: |ret| self.documents.get(uri).map_or(0_usize, |document| document.proposals.len())
            == kept.saturating_add(usize::from(ret.is_ok())),
    )]
    #[inline]
    pub fn propose(
        &mut self,
        uri: &DocumentUri,
        version: DocumentVersion,
        proposal: Proposal,
    ) -> Result<Vec<Diagnostic>, ProposalRefusal>
    {
        let held = self
            .documents
            .get(uri)
            .ok_or(ProposalRefusal::NotHeld)?
            .version;
        if held != version {
            return Err(ProposalRefusal::Stale { held });
        }
        let change = ContentChange {
            range: Some(proposal.range),
            text: proposal.text.clone(),
        };
        let tried = self
            .trial(uri, core::slice::from_ref(&change))
            .and_then(|(_version, mut tried)| tried.pop())
            .ok_or(ProposalRefusal::NotHeld)?;
        let document = self
            .documents
            .get_mut(uri)
            .ok_or(ProposalRefusal::NotHeld)?;
        let diagnostics = check(tried, &document.published)?;
        document.proposals.push(proposal);
        Ok(diagnostics)
    }

    /// The response a running connection gives the request `request`, read
    /// off the documents held, as JSON.
    ///
    /// # Specification
    /// - requires: nothing; any body is admitted.
    /// - ensures: a request is answered as [`Server::handle`] answers it on a
    ///   running connection, under its own identifier; `initialize` and
    ///   `shutdown` are refused as a running connection refuses or answers
    ///   them, and change nothing here. A notification or a response is
    ///   answered `null`; a body that is not a message, with the error the
    ///   protocol owes it.
    /// - provides: every read-only request of the language server, for a face
    ///   that speaks another protocol over the same documents.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a hover and an outline answer as a connection's
    ///   would; a notification answers `null`.
    /// - witness: `server::tests::a_workspace_answers_queries_off_its_documents`
    #[spec(ensures: |ret| ret.is_null() || ret.get("jsonrpc").is_some())]
    #[inline]
    #[must_use]
    pub fn query(
        &self,
        request: &Body,
    ) -> Value
    {
        let mut reader = Server {
            phase: Phase::Running,
            peer: Peer(u64::MAX),
            verbosity: Verbosity::User,
        };
        let answer = match classify(request) {
            | Err(malformed) => malformed.response(),
            | Ok(Incoming::Request { id, method, params }) => {
                reader.request(self, id, &method, params)
            },
            | Ok(Incoming::Notification { .. } | Incoming::Response) => return Value::Null,
        };
        serde_json::to_value(answer).unwrap_or(Value::Null)
    }

    /// Let `peer` go: it holds nothing open any more, takes no message, and a
    /// document no other connection holds is forgotten with its session.
    ///
    /// # Specification
    /// - requires: nothing; a peer that never joined or held nothing is
    ///   admitted.
    /// - ensures: `peer` has no outbox and holds no document; every document
    ///   left is held by another connection.
    /// - provides: a connection's end, clean or not.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one of two connections holding a document leaving,
    ///   then the other, observe the document kept, then forgotten.
    /// - witness: `server::tests::a_departing_connection_leaves_the_others_served`
    #[spec(ensures: !self.outboxes.contains_key(&peer) && !self.watchers.contains_key(&peer)
        && self.holders.values().all(|holders| !holders.contains(&peer) && !holders.is_empty())
        && self.documents.keys().all(|uri| self.holders.contains_key(uri)))]
    #[inline]
    pub fn depart(
        &mut self,
        peer: Peer,
    )
    {
        let _outbox = self.outboxes.remove(&peer);
        let _watcher = self.watchers.remove(&peer);
        let mut forgotten = Vec::new();
        self.holders.retain(|uri, holders| {
            let _held = holders.remove(&peer);
            if holders.is_empty() {
                forgotten.push(uri.clone());
                false
            }
            else {
                true
            }
        });
        for uri in forgotten {
            self.forget(&uri);
        }
    }

    /// Forget the document at `uri`, with its session, and tell every
    /// watcher.
    ///
    /// # Specification
    /// trivial.
    fn forget(
        &mut self,
        uri: &DocumentUri,
    )
    {
        let _released = self.holders.remove(uri);
        if self.documents.remove(uri).is_some() {
            for watcher in self.watchers.values() {
                let _gone = watcher.send(uri.clone());
            }
        }
    }

    /// Record `message`, a publication `peer`'s handling made, as its
    /// document's last diagnostics, send it to every connection but `peer`
    /// that holds the document open, and tell every watcher.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a diagnostic notification at a held document's held version
    ///   becomes that document's published diagnostics, is sent once to the
    ///   outbox of each other holder of its URI that has one, and its URI to
    ///   every watcher; anything else is recorded and sent nowhere. A channel
    ///   whose connection is gone takes nothing, silently.
    /// - panics: none.
    /// - executable: none — the sends land in channels whose receiving ends
    ///   this call does not hold, so nothing it can read states them.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a change by one of two holders publishes to the other
    ///   and not back to itself; the diagnostics read back are the change's.
    /// - witness: `server::tests::two_connections_share_one_document`
    /// - witness: `server::tests::a_workspace_answers_queries_off_its_documents`
    fn published_by(
        &mut self,
        peer: Peer,
        message: &Outgoing,
    )
    {
        let Outgoing::Notification { ref params, .. } = *message
        else {
            return;
        };
        let Some(document) = self
            .documents
            .get_mut(&params.uri)
            .filter(|document| params.version == Some(document.version))
        else {
            return;
        };
        document.published.clone_from(&params.diagnostics);
        if let Some(holders) = self.holders.get(&params.uri) {
            for holder in holders.iter().filter(|&&holder| holder != peer) {
                if let Some(outbox) = self.outboxes.get(holder) {
                    let _gone = outbox.send(message.clone());
                }
            }
        }
        for watcher in self.watchers.values() {
            let _gone = watcher.send(params.uri.clone());
        }
    }
}

/// One connection's state: where it stands in the lifecycle, which connection
/// it is, and how much of each report its diagnostics carry.
pub struct Server
{
    /// Where the connection stands in the lifecycle.
    phase: Phase,
    /// Which connection it is.
    peer: Peer,
    /// The level its editor's `gandr.diagnostics.verbosity` setting names:
    /// read at `initialize` and at each `workspace/didChangeConfiguration`.
    verbosity: Verbosity,
}

impl Default for Server
{
    /// The first connection, waiting for `initialize`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self::new(Peer(0))
    }
}

impl Server
{
    /// The connection `peer`, waiting for `initialize`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(peer: Peer) -> Self
    {
        Self {
            phase: Phase::Waiting,
            peer,
            verbosity: Verbosity::User,
        }
    }

    /// Handle one message body over `workspace`.
    ///
    /// # Specification
    /// - requires: nothing; any body is admissible input.
    /// - ensures: a request is answered exactly once, under its own identifier,
    ///   as the lifecycle and the method decide, from the documents `workspace`
    ///   holds, whichever connection opened them; a notification is never
    ///   answered, and a document synchronisation publishes the document's
    ///   diagnostics off its session's judgement of the whole text, at this
    ///   connection's verbosity, and logs one timing line, its admission left
    ///   for [`Server::admit`] — opening and changing it publish its
    ///   diagnostics at its new version, to this connection and to every other
    ///   holding it open, and closing it publishes none to this connection and
    ///   forgets it once no connection holds it. A configuration change that
    ///   names another verbosity republishes every document this connection
    ///   holds, to it alone. A body that is not a message is answered with the
    ///   error the protocol owes it. `exit` ends the session.
    /// - provides: the whole of a connection's behaviour but the admission
    ///   [`Server::admit`] runs after it; [`serve`] and the hub only move
    ///   bytes.
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
    /// - witness: `server::tests::a_configuration_change_republishes_at_its_verbosity`
    #[spec(
        captures: phase = self.phase,
        ensures: |ret| ret.log.len() <= ret.messages.len()
            && (self.phase == phase || matches!((phase, self.phase),
                (Phase::Waiting, Phase::Running) | (Phase::Running, Phase::ShuttingDown)))
            && match ret.flow { Flow::Continue => true, Flow::Exit(ending) =>
                ret.messages.is_empty() && ending == self.closed() },
    )]
    #[inline]
    #[must_use]
    pub fn handle(
        &mut self,
        workspace: &mut Workspace,
        body: &Body,
    ) -> Outcome
    {
        match classify(body) {
            | Err(malformed) => Outcome::say(malformed.response()),
            | Ok(Incoming::Response) => Outcome::quiet(),
            | Ok(Incoming::Request { id, method, params }) => {
                Outcome::say(self.request(workspace, id, &method, params))
            },
            | Ok(Incoming::Notification { method, params }) => {
                self.notification(workspace, &method, params)
            },
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
    /// - ensures: each line naming a document `workspace` holds at its held
    ///   version runs the admission that document's session holds, as [`admit`]
    ///   states, and carries its wall; a kernel disagreement adds one
    ///   diagnostic notification at the line's URI and version whose one
    ///   diagnostic names it, also sent to every other connection holding the
    ///   document. Every other line is left as it was.
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
        &self,
        workspace: &mut Workspace,
        log: &mut [Logged],
    ) -> Vec<Outgoing>
    {
        let mut corrections = Vec::new();
        for logged in &mut *log {
            let Some(document) = workspace
                .documents
                .get_mut(&logged.uri)
                .filter(|document| document.version == logged.version)
            else {
                continue;
            };
            let admitted = admit(&mut document.session, logged.timing);
            logged.timing = admitted.timing;
            if let Maybe::Present(fault) = admitted.fault {
                let correction = publish(PublishParams {
                    uri: logged.uri.clone(),
                    version: Some(logged.version),
                    diagnostics: vec![fault],
                });
                workspace.published_by(self.peer, &correction);
                corrections.push(correction);
            }
        }
        corrections
    }

    /// The response to the request `id` calling `method` with `params`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: initialization and shutdown advance the lifecycle once, and
    ///   initialization takes the verbosity its options name, the user level
    ///   when they name none; other requests preserve it, and no request
    ///   changes `workspace`. The response echoes the identifier and carries
    ///   the method result or its lifecycle, unknown-method or
    ///   invalid-parameter error.
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
    /// - witness: `server::tests::inline_completion_answers_the_expected_closer`
    /// - witness: `server::tests::the_outline_requests_answer_a_known_document`
    /// - witness: `server::tests::a_hover_answers_a_known_declaration`
    /// - witness: `server::tests::kept_proposals_reach_every_editor_surface`
    /// - witness: `server::tests::formatting_answers_the_edits_that_lay_a_document_out`
    /// - witness: `server::tests::a_configuration_change_republishes_at_its_verbosity`
    #[spec(
        captures: [phase = self.phase, initial = initial_verbosity(&params)],
        ensures: |ret| match (phase, method.as_ref()) {
            (Phase::Waiting, "initialize") => self.phase == Phase::Running
                && self.verbosity == initial
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
            (Phase::Running, "textDocument/inlineCompletion") =>
                self.phase == phase && match ret {
                    Outgoing::Success { result: Answer::Nothing | Answer::Inline(_), .. } => true,
                    Outgoing::Failure { ref error, .. } => error.code == ErrorCode::INVALID_PARAMS,
                    _ => false,
                },
            (Phase::Running, "textDocument/documentSymbol" | "textDocument/foldingRange" | "textDocument/selectionRange") =>
                self.phase == phase && match ret {
                    Outgoing::Success { result: Answer::Nothing | Answer::Symbols(_) | Answer::Folds(_) | Answer::Selections(_), .. } => true,
                    Outgoing::Failure { ref error, .. } => error.code == ErrorCode::INVALID_PARAMS,
                    _ => false,
                },
            (Phase::Running, "textDocument/hover") =>
                self.phase == phase && match ret {
                    Outgoing::Success { result: Answer::Nothing | Answer::Hover(_), .. } => true,
                    Outgoing::Failure { ref error, .. } => error.code == ErrorCode::INVALID_PARAMS,
                    _ => false,
                },
            (Phase::Running, "textDocument/codeLens" | "textDocument/codeAction") =>
                self.phase == phase && match ret {
                    Outgoing::Success { result: Answer::Nothing | Answer::Lenses(_) | Answer::Actions(_), .. } => true,
                    Outgoing::Failure { ref error, .. } => error.code == ErrorCode::INVALID_PARAMS,
                    _ => false,
                },
            (Phase::Running, "textDocument/formatting" | "textDocument/rangeFormatting") =>
                self.phase == phase && match ret {
                    Outgoing::Success { result: Answer::Nothing | Answer::Edits(_), .. } => true,
                    Outgoing::Failure { ref error, .. } =>
                        error.code == ErrorCode::INVALID_PARAMS || error.code == ErrorCode::REQUEST_FAILED,
                    _ => false,
                },
            (Phase::Running, _) => self.phase == phase && matches!(ret,
                Outgoing::Failure { ref error, .. } if error.code == ErrorCode::METHOD_NOT_FOUND),
        },
    )]
    fn request(
        &mut self,
        workspace: &Workspace,
        id: RequestId,
        method: &Method,
        params: Value,
    ) -> Outgoing
    {
        let name = method.as_ref();
        match (self.phase, name) {
            | (Phase::Waiting, "initialize") => {
                self.phase = Phase::Running;
                self.verbosity = initial_verbosity(&params);
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
                    | Ok(params) => success(
                        id,
                        workspace.tokens(&params.text_document.uri, Window::Whole),
                    ),
                    | Err(error) => failure(id, ErrorCode::INVALID_PARAMS, error.to_string()),
                }
            },
            | (Phase::Running, "textDocument/semanticTokens/range") => {
                match serde_json::from_value::<RangeParams>(params) {
                    | Ok(params) => success(
                        id,
                        workspace.tokens(&params.text_document.uri, Window::Within(params.range)),
                    ),
                    | Err(error) => failure(id, ErrorCode::INVALID_PARAMS, error.to_string()),
                }
            },
            | (Phase::Running, "textDocument/inlineCompletion") => {
                match serde_json::from_value::<PositionParams>(params) {
                    | Ok(params) => success(
                        id,
                        workspace.inline(&params.text_document.uri, params.position),
                    ),
                    | Err(error) => failure(id, ErrorCode::INVALID_PARAMS, error.to_string()),
                }
            },
            | (Phase::Running, "textDocument/documentSymbol") => {
                match serde_json::from_value::<DocumentParams>(params) {
                    | Ok(params) => success(
                        id,
                        workspace.outline(&params.text_document.uri, |text| {
                            Answer::Symbols(symbols(text))
                        }),
                    ),
                    | Err(error) => failure(id, ErrorCode::INVALID_PARAMS, error.to_string()),
                }
            },
            | (Phase::Running, "textDocument/foldingRange") => {
                match serde_json::from_value::<DocumentParams>(params) {
                    | Ok(params) => success(
                        id,
                        workspace
                            .outline(&params.text_document.uri, |text| Answer::Folds(folds(text))),
                    ),
                    | Err(error) => failure(id, ErrorCode::INVALID_PARAMS, error.to_string()),
                }
            },
            | (Phase::Running, "textDocument/selectionRange") => {
                match serde_json::from_value::<SelectionRangeParams>(params) {
                    | Ok(params) => success(
                        id,
                        workspace.outline(&params.text_document.uri, |text| {
                            Answer::Selections(selections(text, &params.positions))
                        }),
                    ),
                    | Err(error) => failure(id, ErrorCode::INVALID_PARAMS, error.to_string()),
                }
            },
            | (Phase::Running, "textDocument/hover") => {
                match serde_json::from_value::<PositionParams>(params) {
                    | Ok(params) => success(
                        id,
                        workspace.hover(&params.text_document.uri, params.position),
                    ),
                    | Err(error) => failure(id, ErrorCode::INVALID_PARAMS, error.to_string()),
                }
            },
            | (Phase::Running, "textDocument/codeLens") => {
                match serde_json::from_value::<DocumentParams>(params) {
                    | Ok(params) => success(
                        id,
                        workspace
                            .documents
                            .get(&params.text_document.uri)
                            .map_or(Answer::Nothing, |document| {
                                Answer::Lenses(lenses(&document.proposals))
                            }),
                    ),
                    | Err(error) => failure(id, ErrorCode::INVALID_PARAMS, error.to_string()),
                }
            },
            | (Phase::Running, "textDocument/codeAction") => {
                match serde_json::from_value::<RangeParams>(params) {
                    | Ok(params) => success(
                        id,
                        workspace.documents.get(&params.text_document.uri).map_or(
                            Answer::Nothing,
                            |document| {
                                Answer::Actions(actions(
                                    &params.text_document.uri,
                                    &document.proposals,
                                    params.range,
                                ))
                            },
                        ),
                    ),
                    | Err(error) => failure(id, ErrorCode::INVALID_PARAMS, error.to_string()),
                }
            },
            | (Phase::Running, "textDocument/formatting") => {
                match serde_json::from_value::<DocumentParams>(params) {
                    | Ok(params) => workspace.format(id, &params.text_document.uri, Window::Whole),
                    | Err(error) => failure(id, ErrorCode::INVALID_PARAMS, error.to_string()),
                }
            },
            | (Phase::Running, "textDocument/rangeFormatting") => {
                match serde_json::from_value::<RangeParams>(params) {
                    | Ok(params) => workspace.format(
                        id,
                        &params.text_document.uri,
                        Window::Within(params.range),
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
    ///   line, and send the same publication to every other connection holding
    ///   the document open. An open of a document no connection holds starts
    ///   its session; an open of one another connection holds takes the
    ///   opener's text and version into the held session. Either way this
    ///   connection then holds it. A change applies each content change in
    ///   order, as [`apply`] states; an empty change list preserves text. Close
    ///   lets this connection's hold go, forgets the document once no
    ///   connection holds it, and publishes a versionless empty diagnostic list
    ///   to this connection, even for an unknown URI. A running-state
    ///   configuration change whose `gandr` section names a verbosity other
    ///   than this connection's takes it, then republishes every document this
    ///   connection holds, in URI order, at its held version, to this
    ///   connection alone, logging one timing line each; a change naming none,
    ///   or the verbosity already held, changes nothing. Unknown, malformed and
    ///   out-of-phase notifications leave documents alone.
    /// - provides: document synchronization, configuration and termination.
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
    /// - witness: `server::tests::a_configuration_change_republishes_at_its_verbosity`
    #[spec(
        captures: [phase = self.phase, count = workspace.documents.len()],
        ensures: |ret| self.phase == phase
            && (ret.messages.len() <= 1 || method.as_ref() == "workspace/didChangeConfiguration")
            && ret.log.len() == match method.as_ref() {
                "textDocument/didOpen" | "textDocument/didChange" => usize::from(!ret.messages.is_empty()),
                "workspace/didChangeConfiguration" => ret.messages.len(),
                _ => 0_usize,
            }
            && ret.flow == if method.as_ref() == "exit" { Flow::Exit(self.closed()) } else { Flow::Continue }
            && if ret.messages.is_empty() { workspace.documents.len() == count } else {
                phase == Phase::Running && ret.messages.iter().all(|message| match *message {
                    Outgoing::Notification { ref params, .. } => match method.as_ref() {
                        "textDocument/didOpen" =>
                            workspace.documents.get(&params.uri).is_some_and(|document| params.version == Some(document.version))
                            && workspace.holders.get(&params.uri).is_some_and(|holders| holders.contains(&self.peer)),
                        "textDocument/didChange" =>
                            workspace.documents.get(&params.uri).is_some_and(|document| params.version == Some(document.version)),
                        "textDocument/didClose" => params.version.is_none() && params.diagnostics.is_empty()
                            && !workspace.holders.get(&params.uri).is_some_and(|holders| holders.contains(&self.peer))
                            && workspace.documents.contains_key(&params.uri) == workspace.holders.contains_key(&params.uri),
                        "workspace/didChangeConfiguration" =>
                            workspace.documents.get(&params.uri).is_some_and(|document| params.version == Some(document.version))
                            && workspace.holders.get(&params.uri).is_some_and(|holders| holders.contains(&self.peer)),
                        _ => false,
                    },
                    _ => false,
                })
            },
    )]
    fn notification(
        &mut self,
        workspace: &mut Workspace,
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
                let uri = text_document.uri;
                let document = workspace
                    .documents
                    .entry(uri.clone())
                    .or_insert_with(|| Document {
                        version: text_document.version,
                        text: String::new(),
                        session: open(&uri),
                        published: Vec::new(),
                        proposals: Vec::new(),
                    });
                document.version = text_document.version;
                document.text = text_document.text;
                document.proposals.clear();
                let outcome = synchronised(&uri, document, self.verbosity);
                let _first = workspace.holders.entry(uri).or_default().insert(self.peer);
                for message in &outcome.messages {
                    workspace.published_by(self.peer, message);
                }
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
                let Some(document) = workspace.documents.get_mut(&text_document.uri)
                else {
                    return Outcome::quiet();
                };
                document.version = text_document.version;
                document.proposals.clear();
                for change in content_changes {
                    apply(&mut document.text, change);
                }
                let outcome = synchronised(&text_document.uri, document, self.verbosity);
                for message in &outcome.messages {
                    workspace.published_by(self.peer, message);
                }
                outcome
            },
            | (Phase::Running, "textDocument/didClose") => {
                let Ok(DocumentParams { text_document }) = serde_json::from_value(params)
                else {
                    return Outcome::quiet();
                };
                if let Some(holders) = workspace.holders.get_mut(&text_document.uri) {
                    let _held = holders.remove(&self.peer);
                    if holders.is_empty() {
                        workspace.forget(&text_document.uri);
                    }
                }
                Outcome::say(publish(PublishParams {
                    uri: text_document.uri,
                    version: None,
                    diagnostics: Vec::new(),
                }))
            },
            | (Phase::Running, "workspace/didChangeConfiguration") => {
                let Some(verbosity) = serde_json::from_value::<ConfigurationParams>(params)
                    .ok()
                    .and_then(|params| params.settings)
                    .and_then(|sections| sections.gandr)
                    .and_then(Settings::verbosity)
                    .filter(|&verbosity| verbosity != self.verbosity)
                else {
                    return Outcome::quiet();
                };
                self.verbosity = verbosity;
                let peer = self.peer;
                let holders = &workspace.holders;
                let mut outcome = Outcome::quiet();
                for (uri, document) in workspace.documents.iter_mut().filter(|&(uri, _)| {
                    holders
                        .get(uri)
                        .is_some_and(|holders| holders.contains(&peer))
                }) {
                    let republished = synchronised(uri, document, verbosity);
                    outcome.messages.extend(republished.messages);
                    outcome.log.extend(republished.log);
                }
                outcome
            },
            | (Phase::Waiting | Phase::Running | Phase::ShuttingDown, _) => Outcome::quiet(),
        }
    }
}

impl Workspace
{
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
        Answer::Initialize(_) | Answer::Inline(_) | Answer::Symbols(_) | Answer::Folds(_) | Answer::Selections(_)
            | Answer::Hover(_) | Answer::Edits(_) | Answer::Lenses(_) | Answer::Actions(_) => false,
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

    /// The inline completion of the document at `uri` at `position`.
    ///
    /// # Specification
    /// - requires: nothing; an unknown URI and any position are admitted.
    /// - ensures: an unknown document yields Nothing; a held document yields
    ///   first the ghost text of each kept proposal whose range holds the
    ///   position, replacing that range, then one item when [`ghost()`] shows
    ///   ghost text at the position's byte, its snippet inserted at the empty
    ///   range at `position`, and none when it shows none or the grammar did
    ///   not build.
    /// - provides: the answer to `textDocument/inlineCompletion`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a known document after an open bracket, the same
    ///   document where nothing is owed, and an unknown document distinguish
    ///   the item, the empty list and null through exact wire answers; a cursor
    ///   inside a kept proposal sees it first.
    /// - witness: `server::tests::inline_completion_answers_the_expected_closer`
    /// - witness: `server::tests::kept_proposals_reach_every_editor_surface`
    #[spec(ensures: |ret| match ret {
        Answer::Nothing => !self.documents.contains_key(uri),
        Answer::Inline(ref list) => self.documents.get(uri).is_some_and(|document|
            list.items.len() <= document.proposals.len().saturating_add(1))
            && list.items.iter().all(|item| item.range.start <= position && position <= item.range.end),
        Answer::Initialize(_) | Answer::Tokens(_) | Answer::Symbols(_) | Answer::Folds(_) | Answer::Selections(_)
            | Answer::Hover(_) | Answer::Edits(_) | Answer::Lenses(_) | Answer::Actions(_) => false,
    })]
    fn inline(
        &self,
        uri: &DocumentUri,
        position: Position,
    ) -> Answer
    {
        let Some(document) = self.documents.get(uri)
        else {
            return Answer::Nothing;
        };
        let text = document.text.as_str();
        let index = LineIndex::new(text.into());
        let at = position.byte(&index);
        let mut items = ghosts(&document.proposals, position);
        if let Ok(Maybe::Present(snippet)) =
            grammar().map(|grammar| ghost(grammar, SourceText::from(text), at))
        {
            items.push(InlineCompletionItem {
                insert_text: StringValue {
                    kind: "snippet",
                    value: String::from(snippet),
                },
                range: Range {
                    start: position,
                    end: position,
                },
            });
        }
        Answer::Inline(InlineCompletionList { items })
    }

    /// What `read` answers over the text of the document at `uri`.
    ///
    /// # Specification
    /// - requires: nothing; an unknown URI is admitted.
    /// - ensures: an unknown document yields Nothing, without calling `read`; a
    ///   held document yields what `read` answers over its text.
    /// - provides: the answers to the outline requests, which read the
    ///   document's text alone.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each outline request over a held and an unknown
    ///   document is asserted at its exact wire answer.
    /// - witness: `server::tests::the_outline_requests_answer_a_known_document`
    #[spec(ensures: |ret| matches!(ret, Answer::Nothing) != self.documents.contains_key(uri))]
    fn outline(
        &self,
        uri: &DocumentUri,
        read: impl FnOnce(SourceText<'_>) -> Answer,
    ) -> Answer
    {
        self.documents.get(uri).map_or(Answer::Nothing, |document| {
            read(SourceText::from(document.text.as_str()))
        })
    }

    /// What a hover at `position` of the document at `uri` shows.
    ///
    /// # Specification
    /// - requires: nothing; an unknown URI and any position are admitted.
    /// - ensures: an unknown document yields Nothing; otherwise the hover
    ///   [`hover()`] shows read against the document's session, followed by the
    ///   notes of the kept proposals whose range holds the position and explain
    ///   themselves, or those notes alone over the first one's range when the
    ///   session shows nothing there or the grammar did not build. Nothing when
    ///   neither shows anything.
    /// - provides: the answer to `textDocument/hover`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a hover over a held document's declaration, over its
    ///   keyword and over an unknown document are asserted at their exact wire
    ///   answers; one inside an explained proposal carries its note.
    /// - witness: `server::tests::a_hover_answers_a_known_declaration`
    /// - witness: `server::tests::kept_proposals_reach_every_editor_surface`
    #[spec(ensures: |ret| matches!(ret, Answer::Nothing | Answer::Hover(_))
        && (self.documents.contains_key(uri) || matches!(ret, Answer::Nothing)))]
    fn hover(
        &self,
        uri: &DocumentUri,
        position: Position,
    ) -> Answer
    {
        let Some(document) = self.documents.get(uri)
        else {
            return Answer::Nothing;
        };
        let shown = match document.session {
            | Ok(ref session) => hover(SourceText::from(document.text.as_str()), session, position),
            | Err(_) => Maybe::Absent(crate::hover::hovered::Absent::Unparsed),
        };
        match (shown, notes(&document.proposals, position)) {
            | (Maybe::Present(mut shown), Some((_range, notes))) => {
                shown.contents.value.push_str("\n\n---\n\n");
                shown.contents.value.push_str(&notes);
                Answer::Hover(shown)
            },
            | (Maybe::Present(shown), None) => Answer::Hover(shown),
            | (Maybe::Absent(_), Some((range, notes))) => Answer::Hover(Hover {
                contents: MarkupContent {
                    kind: "markdown",
                    value: notes,
                },
                range,
            }),
            | (Maybe::Absent(_), None) => Answer::Nothing,
        }
    }

    /// The answer to a formatting request `id` over `window` of the document
    /// at `uri`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `null` for a document the server does not hold; otherwise the
    ///   edits [`edits`] answers for its text, or a request-failed refusal
    ///   carrying why it was not formatted. The document is not changed: the
    ///   client applies the edits and synchronises them back.
    /// - fails: never; a refusal is a response.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the known document out of layout, formatted whole and
    ///   over a range, a closed document and a document in layout observe the
    ///   edits, `null` and the empty list exactly.
    /// - witness: `server::tests::formatting_answers_the_edits_that_lay_a_document_out`
    #[spec(ensures: |ref ret| match *ret {
        Outgoing::Success { result: Answer::Nothing, .. } => !self.documents.contains_key(uri),
        Outgoing::Success { result: Answer::Edits(_), .. } => self.documents.contains_key(uri),
        Outgoing::Failure { ref error, .. } => error.code == ErrorCode::REQUEST_FAILED,
        _ => false,
    })]
    fn format(
        &self,
        id: RequestId,
        uri: &DocumentUri,
        window: Window,
    ) -> Outgoing
    {
        let Some(document) = self.documents.get(uri)
        else {
            return success(id, Answer::Nothing);
        };
        match edits(SourceText::from(document.text.as_str()), window) {
            | Ok(edits) => success(id, Answer::Edits(edits)),
            | Err(unformatted) => failure(id, ErrorCode::REQUEST_FAILED, unformatted.to_string()),
        }
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

/// The verbosity the `initialize` parameters `params` name: the one their
/// initialization options' `diagnostics.verbosity` names, the user level when
/// they name none or cannot be read.
///
/// # Specification
/// trivial.
fn initial_verbosity(params: &Value) -> Verbosity
{
    InitializeParams::deserialize(params)
        .ok()
        .and_then(|params| params.initialization_options)
        .and_then(Settings::verbosity)
        .unwrap_or_default()
}

/// Recheck `document`, open at `uri`, at `verbosity`: the notification
/// publishing its diagnostics and the line logging what the recheck cost.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one diagnostic notification naming the supplied URI and held
///   version, with the diagnostics the document's session judges for its whole
///   text, rendered at `verbosity`, and one log line naming the same URI and
///   version, its admission pending when the judgement left one.
/// - provides: the publication shared by open, change and configuration
///   notifications.
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
/// - witness: `server::tests::a_configuration_change_republishes_at_its_verbosity`
#[spec(ensures: |ret| ret.flow == Flow::Continue
    && matches!(*ret.messages.as_slice(), [Outgoing::Notification { method: "textDocument/publishDiagnostics", ref params, .. }]
        if params.uri == *uri && params.version == Some(document.version))
    && matches!(*ret.log.as_slice(), [ref logged] if logged.uri == *uri && logged.version == document.version))]
fn synchronised(
    uri: &DocumentUri,
    document: &mut Document,
    verbosity: Verbosity,
) -> Outcome
{
    let rechecked = recheck(
        uri,
        &mut document.session,
        SourceText::from(document.text.as_str()),
        verbosity,
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
    let mut workspace = Workspace::default();
    let mut server = Server::default();
    loop {
        let read = read_frame(input)?;
        let Maybe::Present(body) = read
        else {
            return Ok(server.closed());
        };
        let mut outcome = server.handle(&mut workspace, &body);
        for message in &outcome.messages {
            let encoded = serde_json::to_vec(message).map_err(TransportFault::Encode)?;
            write_frame(output, &Body::from(encoded))?;
        }
        for message in &server.admit(&mut workspace, &mut outcome.log) {
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
    use std::sync::mpsc::Receiver;
    use std::sync::mpsc::channel;

    use anodized::spec;
    use serde_json::Value;

    use super::Flow;
    use super::Outcome;
    use super::Peer;
    use super::Served;
    use super::Server;
    use super::Workspace;
    use crate::position::Character;
    use crate::position::Line;
    use crate::position::Position;
    use crate::position::Range;
    use crate::proposal::Proposal;
    use crate::proposal::ProposalRefusal;
    use crate::protocol::ContentChange;
    use crate::rpc::Outgoing;
    use crate::server::Logged;
    use crate::transport::Body;

    /// One connection over a workspace of its own, as [`super::serve`] runs
    /// one.
    #[derive(Default)]
    struct Connected
    {
        /// The connection.
        server: Server,
        /// Its workspace.
        workspace: Workspace,
    }

    impl Connected
    {
        /// What the connection makes of `body`.
        ///
        /// # Specification
        /// trivial.
        fn handle(
            &mut self,
            body: &Body,
        ) -> Outcome
        {
            self.server.handle(&mut self.workspace, body)
        }

        /// The admissions `log` left, run.
        ///
        /// # Specification
        /// trivial.
        fn admit(
            &mut self,
            log: &mut [Logged],
        ) -> Vec<Outgoing>
        {
            self.server.admit(&mut self.workspace, log)
        }

        /// How the connection ends if its stream closes now.
        ///
        /// # Specification
        /// trivial.
        const fn closed(&self) -> Served
        {
            self.server.closed()
        }
    }

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
        server: &mut Connected,
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
    #[spec(ensures: |ret| ret.server.phase == super::Phase::Running && ret.workspace.documents.is_empty())]
    fn initialized() -> Connected
    {
        let mut server = Connected::default();
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
    #[spec(ensures: |ret| ret.server.phase == super::Phase::Running
        && ret.workspace.documents.len() == 1
        && ret.workspace.documents.values().all(|document| document.text == "def f = 42 ;\n"))]
    fn server_over_the_known_document() -> Connected
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
        let mut server = Connected::default();
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
                            "range":true},
                        "inlineCompletionProvider":true,
                        "documentSymbolProvider":true,
                        "foldingRangeProvider":true,
                        "selectionRangeProvider":true,
                        "hoverProvider":true,
                        "documentFormattingProvider":true,
                        "documentRangeFormattingProvider":true,
                        "codeLensProvider":{"resolveProvider":false},
                        "codeActionProvider":true},
                    "serverInfo":{"name":"gandr","version":""#,
                env!("CARGO_PKG_VERSION"),
                r#""}}}]"#
            ))),
            "the advertised capabilities, whole: no completion list"
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
        let request = r#"{"jsonrpc":"2.0","id":4,"method":"textDocument/completion","params":{
            "textDocument":{"uri":"file:///tmp/example.gandr"},
            "position":{"line":0,"character":4}}}"#;
        assert_eq!(
            send(&mut server, Json(request)),
            wire(Json(
                r#"[{"jsonrpc":"2.0","id":4,
                     "error":{"code":-32601,"message":"`textDocument/completion` is not served"}}]"#
            )),
            "completion is not advertised, so it is not served"
        );
    }

    #[test]
    fn inline_completion_answers_the_expected_closer()
    {
        let mut server = initialized();
        let _published = send(
            &mut server,
            Json(
                r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":
                    {"uri":"file:///tmp/open.gandr","languageId":"gandr","version":1,
                     "text":"def x = f(1\n"}}}"#,
            ),
        );
        let ask = |server: &mut Connected, uri: &str, character: u32| {
            let request = format!(
                r#"{{"jsonrpc":"2.0","id":7,"method":"textDocument/inlineCompletion","params":{{
                    "textDocument":{{"uri":"{uri}"}},
                    "position":{{"line":0,"character":{character}}},
                    "context":{{"triggerKind":2}}}}}}"#
            );
            send(server, Json(&request))
        };
        assert_eq!(
            ask(&mut server, "file:///tmp/open.gandr", 11),
            wire(Json(
                r#"[{"jsonrpc":"2.0","id":7,"result":{"items":[{
                    "insertText":{"kind":"snippet","value":")"},
                    "range":{"start":{"line":0,"character":11},"end":{"line":0,"character":11}}}]}}]"#
            )),
            "after `f(1` the call's closer is the ghost text"
        );
        assert_eq!(
            ask(&mut server, "file:///tmp/open.gandr", 5),
            wire(Json(r#"[{"jsonrpc":"2.0","id":7,"result":{"items":[]}}]"#)),
            "text after the cursor on its line: nothing is shown"
        );
        assert_eq!(
            ask(&mut server, "file:///tmp/closed.gandr", 0),
            wire(Json(r#"[{"jsonrpc":"2.0","id":7,"result":null}]"#)),
            "a document the server does not hold answers null"
        );
    }

    #[test]
    fn the_outline_requests_answer_a_known_document()
    {
        let mut server = server_over_the_known_document();
        let ask = |server: &mut Connected, method: &str, uri: &str, extra: &str| {
            let request = format!(
                r#"{{"jsonrpc":"2.0","id":9,"method":"{method}","params":{{
                    "textDocument":{{"uri":"{uri}"}}{extra}}}}}"#
            );
            send(server, Json(&request))
        };
        let known = "file:///tmp/example.gandr";
        assert_eq!(
            ask(&mut server, "textDocument/documentSymbol", known, ""),
            wire(Json(
                r#"[{"jsonrpc":"2.0","id":9,"result":[{"name":"f","kind":12,
                    "range":{"start":{"line":0,"character":0},"end":{"line":0,"character":12}},
                    "selectionRange":{"start":{"line":0,"character":4},"end":{"line":0,"character":5}}}]}]"#
            )),
            "the one definition is a function symbol, selected at its name"
        );
        assert_eq!(
            ask(&mut server, "textDocument/foldingRange", known, ""),
            wire(Json(r#"[{"jsonrpc":"2.0","id":9,"result":[]}]"#)),
            "a one-line document folds nowhere"
        );
        assert_eq!(
            ask(
                &mut server,
                "textDocument/selectionRange",
                known,
                r#","positions":[{"line":0,"character":9}]"#
            ),
            wire(Json(
                r#"[{"jsonrpc":"2.0","id":9,"result":[{
                    "range":{"start":{"line":0,"character":8},"end":{"line":0,"character":10}},
                    "parent":{"range":{"start":{"line":0,"character":0},"end":{"line":0,"character":12}},
                    "parent":{"range":{"start":{"line":0,"character":0},"end":{"line":1,"character":0}}}}}]}]"#
            )),
            "inside `42`: the number, the definition, the document"
        );
        for method in [
            "textDocument/documentSymbol",
            "textDocument/foldingRange",
            "textDocument/selectionRange",
        ] {
            assert_eq!(
                ask(
                    &mut server,
                    method,
                    "file:///tmp/closed.gandr",
                    r#","positions":[]"#
                ),
                wire(Json(r#"[{"jsonrpc":"2.0","id":9,"result":null}]"#)),
                "{method} about a document the server does not hold answers null"
            );
        }
    }

    #[test]
    fn formatting_answers_the_edits_that_lay_a_document_out()
    {
        let mut server = initialized();
        let _published = send(
            &mut server,
            Json(
                r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":
                    {"uri":"file:///tmp/loose.gandr","languageId":"gandr","version":1,
                     "text":"def  f =  42 ;\n"}}}"#,
            ),
        );
        let ask = |server: &mut Connected, method: &str, uri: &str, range: &str| {
            let request = format!(
                r#"{{"jsonrpc":"2.0","id":7,"method":"{method}","params":{{
                    "textDocument":{{"uri":"{uri}"}},{range}
                    "options":{{"tabSize":4,"insertSpaces":true}}}}}}"#
            );
            send(server, Json(&request))
        };
        assert_eq!(
            ask(
                &mut server,
                "textDocument/formatting",
                "file:///tmp/loose.gandr",
                ""
            ),
            wire(Json(
                r#"[{"jsonrpc":"2.0","id":7,"result":[{
                    "range":{"start":{"line":0,"character":4},"end":{"line":0,"character":9}},
                    "newText":"f ="}]}]"#
            )),
            "the whole document: one edit over the span the layout changes"
        );
        assert_eq!(
            ask(
                &mut server,
                "textDocument/rangeFormatting",
                "file:///tmp/loose.gandr",
                r#""range":{"start":{"line":0,"character":5},"end":{"line":0,"character":5}},"#
            ),
            wire(Json(
                r#"[{"jsonrpc":"2.0","id":7,"result":[{
                    "range":{"start":{"line":0,"character":4},"end":{"line":0,"character":9}},
                    "newText":"f ="}]}]"#
            )),
            "a cursor: the form holding it"
        );
        assert_eq!(
            ask(
                &mut server,
                "textDocument/formatting",
                "file:///tmp/example.gandr",
                ""
            ),
            wire(Json(r#"[{"jsonrpc":"2.0","id":7,"result":null}]"#)),
            "a document the server does not hold answers null"
        );
        let mut tidy = server_over_the_known_document();
        assert_eq!(
            ask(
                &mut tidy,
                "textDocument/formatting",
                "file:///tmp/example.gandr",
                ""
            ),
            wire(Json(r#"[{"jsonrpc":"2.0","id":7,"result":[]}]"#)),
            "a document in layout answers no edit"
        );
    }

    #[test]
    fn a_hover_answers_a_known_declaration()
    {
        let mut server = server_over_the_known_document();
        let ask = |server: &mut Connected, uri: &str, character: u32| {
            let request = format!(
                r#"{{"jsonrpc":"2.0","id":5,"method":"textDocument/hover","params":{{
                    "textDocument":{{"uri":"{uri}"}},
                    "position":{{"line":0,"character":{character}}}}}}}"#
            );
            send(server, Json(&request))
        };
        assert_eq!(
            ask(&mut server, "file:///tmp/example.gandr", 4),
            wire(Json(
                r#"[{"jsonrpc":"2.0","id":5,"result":{
                    "contents":{"kind":"markdown","value":"```gandr\nf : Integer\n```"},
                    "range":{"start":{"line":0,"character":4},"end":{"line":0,"character":5}}}}]"#
            )),
            "on `f`: its synthesised type, about its name"
        );
        assert_eq!(
            ask(&mut server, "file:///tmp/example.gandr", 1),
            wire(Json(r#"[{"jsonrpc":"2.0","id":5,"result":null}]"#)),
            "on the keyword: no declaration's name, so null"
        );
        assert_eq!(
            ask(&mut server, "file:///tmp/closed.gandr", 4),
            wire(Json(r#"[{"jsonrpc":"2.0","id":5,"result":null}]"#)),
            "a document the server does not hold answers null"
        );
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
        let mut server = Connected::default();
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
            let mut server = Connected {
                server: Server {
                    phase,
                    ..Server::default()
                },
                workspace: Workspace::default(),
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
    fn a_configuration_change_republishes_at_its_verbosity()
    {
        let mut server = Connected::default();
        let _answered = send(
            &mut server,
            Json(
                r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"capabilities":{},
                    "initializationOptions":{"diagnostics":{"verbosity":"detailed"}}}}"#,
            ),
        );
        let opened = send(
            &mut server,
            Json(
                r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{
                    "uri":"file:///tmp/b.gandr","languageId":"gandr","version":3,
                    "text":"def g = missing ;\n"}}}"#,
            ),
        );
        let message = opened
            .pointer("/0/params/diagnostics/0/message")
            .and_then(Value::as_str)
            .expect("the refusal is published");
        assert!(
            message.lines().any(|line| line.starts_with("class: ")),
            "the initialization options choose the detailed level: {message}"
        );
        let _clean = send(
            &mut server,
            Json(
                r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{
                    "uri":"file:///tmp/a.gandr","languageId":"gandr","version":7,
                    "text":"def f = 42 ;\n"}}}"#,
            ),
        );
        let configure = |verbosity: &str| {
            Body::from(
                format!(
                    r#"{{"jsonrpc":"2.0","method":"workspace/didChangeConfiguration",
                        "params":{{"settings":{{"gandr":{{"diagnostics":{{"verbosity":{verbosity}}}}}}}}}}}"#
                )
                .into_bytes(),
            )
        };
        let republished = server.handle(&configure(r#""json""#));
        let published: Vec<Value> = republished
            .messages
            .iter()
            .map(|outgoing| serde_json::to_value(outgoing).expect("a message encodes"))
            .collect();
        assert_eq!(
            published
                .iter()
                .map(|message| (
                    message.pointer("/params/uri").and_then(Value::as_str),
                    message.pointer("/params/version").and_then(Value::as_i64)
                ))
                .collect::<Vec<_>>(),
            [
                (Some("file:///tmp/a.gandr"), Some(7_i64)),
                (Some("file:///tmp/b.gandr"), Some(3_i64))
            ],
            "every held document is republished at its held version, in URI order"
        );
        assert_eq!(
            republished.log.len(),
            2_usize,
            "one timing line per republication"
        );
        let image: Value = published
            .get(1)
            .and_then(|message| message.pointer("/params/diagnostics/0/message"))
            .and_then(Value::as_str)
            .and_then(|message| serde_json::from_str(message).ok())
            .expect("the json level publishes the report's JSON image");
        assert_eq!(
            image.get("name").and_then(Value::as_str),
            Some("UnresolvedName")
        );
        for (unchanged, why) in [
            (configure(r#""json""#), "the level already held"),
            (configure(r#""loud""#), "a value that names no level"),
            (configure("null"), "a section that names none"),
        ] {
            assert!(
                server.handle(&unchanged).messages.is_empty(),
                "{why} republishes nothing"
            );
        }
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
        let held = |server: &Connected| {
            server
                .workspace
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

    /// Two running connections, numbered 1 and 2, over one workspace, each
    /// joined with the receiving end of its outbox returned.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: both connections are running, both joined, no document is
    ///   open and both outboxes are empty.
    /// - provides: the fixture the shared-workspace witnesses start from.
    /// - fails: never.
    /// - panics: an unanswered `initialize` fails the witness.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the witnesses' first publications distinguish a
    ///   connection that never joined.
    /// - witness: `server::tests::two_connections_share_one_document`
    #[spec(ensures: |ret| ret.0.documents.is_empty() && ret.0.outboxes.len() == 2
        && ret.1.iter().all(|connection| connection.0.phase == super::Phase::Running))]
    fn two_connections() -> (Workspace, [(Server, Receiver<Outgoing>); 2])
    {
        let mut workspace = Workspace::default();
        let initialize =
            Body::from(br#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#.to_vec());
        let connections = [1_u64, 2_u64].map(|number| {
            let peer = Peer::from(number);
            let (outbox, inbox) = channel();
            workspace.join(peer, outbox);
            let mut server = Server::new(peer);
            assert_eq!(server.handle(&mut workspace, &initialize).messages.len(), 1);
            (server, inbox)
        });
        (workspace, connections)
    }

    /// The body of a synchronisation of `file:///tmp/shared.gandr`: `method`
    /// with the parameters `params` spells.
    ///
    /// # Specification
    /// trivial.
    fn shared(
        method: Json<'_>,
        params: Json<'_>,
    ) -> Body
    {
        let Json(method) = method;
        let Json(params) = params;
        Body::from(
            format!(
                r#"{{"jsonrpc":"2.0","method":"{method}","params":{{"textDocument":{{"uri":"file:///tmp/shared.gandr"{params}}}}}"#
            )
            .into_bytes(),
        )
    }

    /// The versions of the publications waiting in `inbox`, in order, `None`
    /// for a versionless one.
    ///
    /// # Specification
    /// trivial.
    fn published(inbox: &Receiver<Outgoing>) -> Vec<Option<Value>>
    {
        inbox
            .try_iter()
            .map(|message| {
                serde_json::to_value(message)
                    .expect("a message encodes")
                    .pointer("/params/version")
                    .cloned()
            })
            .collect()
    }

    #[test]
    fn two_connections_share_one_document()
    {
        let (mut workspace, [(mut first, first_inbox), (mut second, second_inbox)]) =
            two_connections();
        let open = Json(r#","version":1,"text":"def f = 42 ;\n"}"#);
        let opened = first.handle(&mut workspace, &shared(Json("textDocument/didOpen"), open));
        assert_eq!(opened.messages.len(), 1, "the opener hears its publication");
        assert_eq!(
            published(&second_inbox),
            Vec::new(),
            "a connection not holding the document hears nothing"
        );
        let reopened = second.handle(&mut workspace, &shared(Json("textDocument/didOpen"), open));
        let [ref logged] = *reopened.log.as_slice()
        else {
            panic!("one timing line per synchronisation");
        };
        assert!(
            logged.to_string().contains(": 0/1 forms molded"),
            "opening a held document reuses its session, molding nothing: {logged}"
        );
        assert_eq!(
            published(&first_inbox),
            vec![Some(serde_json::json!(1_i32))],
            "the other holder hears the publication"
        );
        let changed = first.handle(
            &mut workspace,
            &shared(
                Json("textDocument/didChange"),
                Json(r#","version":2},"contentChanges":[{"text":"def g = 1 ;\n"}]"#),
            ),
        );
        assert_eq!(changed.messages.len(), 1);
        assert_eq!(
            published(&first_inbox),
            Vec::new(),
            "never back to the changer"
        );
        assert_eq!(published(&second_inbox), vec![Some(serde_json::json!(
            2_i32
        ))]);
        let hover = Body::from(
            br#"{"jsonrpc":"2.0","id":5,"method":"textDocument/hover","params":{
                "textDocument":{"uri":"file:///tmp/shared.gandr"},"position":{"line":0,"character":4}}}"#
                .to_vec(),
        );
        let hovered = serde_json::to_value(&second.handle(&mut workspace, &hover).messages)
            .expect("a message encodes");
        assert_eq!(
            hovered.pointer("/0/result/contents/value"),
            Some(&serde_json::json!("```gandr\ng : Integer\n```")),
            "the second connection reads the first's change"
        );
        let close = Json("}");
        let closed = first.handle(
            &mut workspace,
            &shared(Json("textDocument/didClose"), close),
        );
        assert_eq!(closed.messages.len(), 1, "the closer hears its clearing");
        assert_eq!(
            published(&second_inbox),
            Vec::new(),
            "the other holder keeps its diagnostics"
        );
        assert_eq!(
            workspace.documents.len(),
            1,
            "the second connection still holds it"
        );
        let _closed = second.handle(
            &mut workspace,
            &shared(Json("textDocument/didClose"), close),
        );
        assert!(workspace.documents.is_empty() && workspace.holders.is_empty());
    }

    #[test]
    fn a_departing_connection_leaves_the_others_served()
    {
        let (mut workspace, [(mut first, _first_inbox), (mut second, second_inbox)]) =
            two_connections();
        let open = Json(r#","version":1,"text":"def f = 42 ;\n"}"#);
        drop(first.handle(&mut workspace, &shared(Json("textDocument/didOpen"), open)));
        drop(second.handle(&mut workspace, &shared(Json("textDocument/didOpen"), open)));
        workspace.depart(Peer::from(1_u64));
        assert_eq!(
            workspace.documents.len(),
            1,
            "the second connection still holds it"
        );
        assert!(!workspace.outboxes.contains_key(&Peer::from(1_u64)));
        let changed = second.handle(
            &mut workspace,
            &shared(
                Json("textDocument/didChange"),
                Json(r#","version":2},"contentChanges":[{"text":"def g = 1 ;\n"}]"#),
            ),
        );
        assert_eq!(changed.messages.len(), 1, "the one left is still served");
        assert_eq!(published(&second_inbox), Vec::new());
        workspace.depart(Peer::from(2_u64));
        assert!(
            workspace.documents.is_empty() && workspace.holders.is_empty(),
            "a document no connection holds is forgotten"
        );
        workspace.depart(Peer::from(3_u64));
        assert!(
            workspace.outboxes.is_empty(),
            "a stranger's departure changes nothing"
        );
    }

    #[test]
    fn a_workspace_answers_queries_off_its_documents()
    {
        let (mut workspace, [(mut first, _first_inbox), (_second, _second_inbox)]) =
            two_connections();
        let (watcher, changes) = channel();
        workspace.watch(Peer::from(9_u64), watcher);
        let uri = crate::protocol::DocumentUri::from("file:///tmp/shared.gandr");
        assert!(workspace.published(&uri).is_none(), "nothing is held yet");
        drop(first.handle(
            &mut workspace,
            &shared(
                Json("textDocument/didOpen"),
                Json(r#","version":4,"text":"def g = missing ;\n"}"#),
            ),
        ));
        let (version, diagnostics) = workspace
            .published(&uri)
            .expect("the opened document is held");
        assert_eq!(version.to_string(), "4", "read at the version published");
        assert_eq!(diagnostics.len(), 1, "the refusal is what was published");
        assert_eq!(
            changes.try_iter().collect::<Vec<_>>(),
            vec![uri.clone()],
            "a watcher hears which document changed"
        );
        let hover = Body::from(
            br#"{"jsonrpc":"2.0","id":3,"method":"textDocument/hover","params":{
                "textDocument":{"uri":"file:///tmp/shared.gandr"},"position":{"line":0,"character":4}}}"#
                .to_vec(),
        );
        let answered = workspace.query(&hover);
        assert_eq!(answered.get("id"), Some(&serde_json::json!(3_i32)));
        assert_eq!(
            Some(answered),
            serde_json::to_value(&first.handle(&mut workspace, &hover).messages)
                .expect("a message encodes")
                .get(0_usize)
                .cloned(),
            "a query answers as a connection answers"
        );
        assert!(
            workspace
                .query(&Body::from(
                    br#"{"jsonrpc":"2.0","method":"exit"}"#.to_vec()
                ))
                .is_null(),
            "a notification is answered null"
        );
        drop(first.handle(
            &mut workspace,
            &shared(Json("textDocument/didClose"), Json("}")),
        ));
        assert!(
            workspace.published(&uri).is_none(),
            "a closed document reads nothing"
        );
        assert_eq!(
            changes.try_iter().collect::<Vec<_>>(),
            vec![uri],
            "a watcher hears a document forgotten"
        );
    }

    #[test]
    fn a_workspace_tries_candidate_fills()
    {
        let (mut workspace, [(mut first, _first_inbox), (_second, _second_inbox)]) =
            two_connections();
        let uri = crate::protocol::DocumentUri::from("file:///tmp/shared.gandr");
        let text = "def f : Integer ;\ndef f = missing ;\n";
        assert!(workspace.trial(&uri, &[]).is_none(), "nothing is held yet");
        drop(first.handle(
            &mut workspace,
            &shared(
                Json("textDocument/didOpen"),
                Json(r#","version":4,"text":"def f : Integer ;\ndef f = missing ;\n"}"#),
            ),
        ));
        let published = workspace
            .published(&uri)
            .map(|(version, diagnostics)| (version.to_string(), diagnostics.to_vec()));
        let hole = Range {
            start: Position {
                line: crate::position::Line::from(1_u32),
                character: crate::position::Character::from(8_u32),
            },
            end: Position {
                line: crate::position::Line::from(1_u32),
                character: crate::position::Character::from(15_u32),
            },
        };
        let changes = [
            ContentChange {
                range: Some(hole),
                text: String::from("\"one\""),
            },
            ContentChange {
                range: Some(hole),
                text: String::from("42"),
            },
            ContentChange {
                range: None,
                text: String::from("def f : Integer ;\npure 3\n"),
            },
        ];
        let (version, tried) = workspace
            .trial(&uri, &changes)
            .expect("the document is held");
        assert_eq!(version.to_string(), "4");
        assert_eq!(
            tried
                .iter()
                .map(|tried| (
                    usize::from(tried.candidate),
                    tried.reached,
                    tried.diagnostics.len()
                ))
                .collect::<Vec<_>>(),
            [
                (1_usize, crate::recheck::Reached::Judged, 0_usize),
                (0_usize, crate::recheck::Reached::Judged, 1_usize),
                (2_usize, crate::recheck::Reached::RefusedWhole, 1_usize),
            ],
            "the fill spliced over the hole that checks ranks first"
        );
        assert_eq!(
            workspace
                .published(&uri)
                .map(|(version, diagnostics)| (version.to_string(), diagnostics.to_vec())),
            published,
            "the published diagnostics are unchanged"
        );
        assert_eq!(
            workspace
                .documents
                .get(&uri)
                .map(|document| document.text.as_str()),
            Some(text),
            "the held text is unchanged"
        );
    }

    /// The range of `line`, from `start` to `end`, on one line.
    ///
    /// # Specification
    /// trivial.
    fn on_line(
        line: crate::position::Line,
        start: crate::position::Character,
        end: crate::position::Character,
    ) -> Range
    {
        let at = |character| Position { line, character };
        Range {
            start: at(start),
            end: at(end),
        }
    }

    /// A proposal filling `range` with `text`, explained by `explanation`.
    ///
    /// # Specification
    /// trivial.
    fn fill(
        range: Range,
        text: Json<'_>,
        explanation: Option<Json<'_>>,
    ) -> Proposal
    {
        Proposal {
            range,
            text: String::from(text.0),
            explanation: explanation.map(|Json(explanation)| String::from(explanation)),
        }
    }

    /// What `workspace` answers the request `method` with `params` about the
    /// shared document.
    ///
    /// # Specification
    /// trivial.
    fn asked(
        workspace: &Workspace,
        method: Json<'_>,
        params: Json<'_>,
    ) -> Value
    {
        let (Json(method), Json(params)) = (method, params);
        workspace
            .query(&Body::from(
                format!(
                    r#"{{"jsonrpc":"2.0","id":1,"method":"{method}","params":{{"textDocument":{{"uri":"file:///tmp/shared.gandr"}}{params}}}}}"#
                )
                .into_bytes(),
            ))
            .get("result")
            .cloned()
            .unwrap_or(Value::Null)
    }

    #[test]
    fn a_proposal_is_kept_only_once_it_checks()
    {
        let (mut workspace, [(mut first, _first_inbox), (_second, _second_inbox)]) =
            two_connections();
        let uri = crate::protocol::DocumentUri::from("file:///tmp/shared.gandr");
        let hole = on_line(
            Line::from(1_u32),
            Character::from(8_u32),
            Character::from(15_u32),
        );
        let version = |workspace: &Workspace| {
            workspace
                .documents
                .get(&uri)
                .map(|document| document.version)
                .expect("the document is held")
        };
        assert_eq!(
            workspace.propose(
                &uri,
                serde_json::from_value(serde_json::json!(4_i32)).expect("a version"),
                fill(hole, Json("42"), None)
            ),
            Err(ProposalRefusal::NotHeld)
        );
        drop(first.handle(
            &mut workspace,
            &shared(
                Json("textDocument/didOpen"),
                Json(r#","version":4,"text":"def f : Integer ;\ndef f = missing ;\n"}"#),
            ),
        ));
        let held = version(&workspace);
        let stale = serde_json::from_value(serde_json::json!(3_i32)).expect("a version");
        assert_eq!(
            workspace.propose(&uri, stale, fill(hole, Json("42"), None)),
            Err(ProposalRefusal::Stale { held })
        );
        assert!(
            matches!(
                workspace.propose(&uri, held, fill(hole, Json("\"one\""), None)),
                Err(ProposalRefusal::Unchecked { ref diagnostics }) if diagnostics.len() == 1
            ),
            "a fill leaving a refusal is not kept"
        );
        assert!(
            matches!(
                workspace.propose(&uri, held, fill(hole, Json("1 ;\npure 3"), None)),
                Err(ProposalRefusal::Unchecked { .. })
            ),
            "a fill the lowering refuses whole is not kept"
        );
        assert_eq!(
            workspace.propose(&uri, held, fill(hole, Json("42"), None)),
            Ok(Vec::new()),
            "a fill that settles the document is kept"
        );
        let kept = |workspace: &Workspace| {
            workspace
                .documents
                .get(&uri)
                .map(|document| document.proposals.clone())
        };
        assert_eq!(kept(&workspace), Some(vec![fill(hole, Json("42"), None)]));
        assert_eq!(
            workspace
                .published(&uri)
                .map(|(_, diagnostics)| diagnostics.len()),
            Some(1_usize),
            "what the editor shows is unchanged"
        );
        drop(first.handle(
            &mut workspace,
            &shared(
                Json("textDocument/didChange"),
                Json(r#","version":5},"contentChanges":[{"text":"def f : Integer ;\ndef f = missing ;\n"}]"#),
            ),
        ));
        assert_eq!(
            kept(&workspace),
            Some(Vec::new()),
            "the next edit withdraws what was kept"
        );
    }

    #[test]
    fn kept_proposals_reach_every_editor_surface()
    {
        let (mut workspace, [(mut first, _first_inbox), (_second, _second_inbox)]) =
            two_connections();
        let uri = crate::protocol::DocumentUri::from("file:///tmp/shared.gandr");
        drop(first.handle(
            &mut workspace,
            &shared(
                Json("textDocument/didOpen"),
                Json(
                    r#","version":1,"text":"def f : Integer ;\ndef f = missing ;\ndef g : Integer ;\ndef g = absent ;\n"}"#,
                ),
            ),
        ));
        let held = workspace
            .documents
            .get(&uri)
            .map(|document| document.version)
            .expect("the document is held");
        let (f, g) = (
            on_line(
                Line::from(1_u32),
                Character::from(8_u32),
                Character::from(15_u32),
            ),
            on_line(
                Line::from(3_u32),
                Character::from(8_u32),
                Character::from(14_u32),
            ),
        );
        for proposal in [
            fill(f, Json("42"), Some(Json("the answer"))),
            fill(f, Json("7"), None),
            fill(g, Json("1"), None),
        ] {
            assert!(
                workspace.propose(&uri, held, proposal).is_ok(),
                "a fill repairing one refusal of two is kept"
            );
        }
        let inside = r#","position":{"line":1,"character":10}"#;
        let ghosts = asked(
            &workspace,
            Json("textDocument/inlineCompletion"),
            Json(inside),
        );
        assert_eq!(
            ghosts.pointer("/items/0"),
            Some(
                &serde_json::json!({ "insertText": { "kind": "snippet", "value": "42" },
                "range": { "start": { "line": 1_u32, "character": 8_u32 }, "end": { "line": 1_u32, "character": 15_u32 } } })
            ),
            "the cursor's proposals come first"
        );
        assert_eq!(
            ghosts.pointer("/items/1/insertText/value"),
            Some(&serde_json::json!("7"))
        );
        let outside = asked(
            &workspace,
            Json("textDocument/inlineCompletion"),
            Json(r#","position":{"line":0,"character":0}"#),
        );
        assert!(
            outside
                .pointer("/items")
                .and_then(Value::as_array)
                .is_some_and(|items| items.iter().all(
                    |item| item.pointer("/range/start/line") == Some(&serde_json::json!(0_u32))
                )),
            "a cursor outside every proposal sees none: {outside}"
        );
        let lenses = asked(&workspace, Json("textDocument/codeLens"), Json(""));
        assert_eq!(
            lenses.as_array().map(|lenses| lenses
                .iter()
                .map(|lens| lens.pointer("/command/title").cloned())
                .collect::<Vec<_>>()),
            Some(vec![
                Some(serde_json::json!("2 checked fills")),
                Some(serde_json::json!("1 checked fill"))
            ])
        );
        let actions = asked(
            &workspace,
            Json("textDocument/codeAction"),
            Json(
                r#","range":{"start":{"line":1,"character":9},"end":{"line":1,"character":9}},"context":{"diagnostics":[]}"#,
            ),
        );
        assert_eq!(
            actions.pointer("/0/edit/changes/file:~1~1~1tmp~1shared.gandr/0"),
            Some(
                &serde_json::json!({ "range": { "start": { "line": 1_u32, "character": 8_u32 },
                "end": { "line": 1_u32, "character": 15_u32 } }, "newText": "42" })
            )
        );
        assert_eq!(actions.as_array().map(Vec::len), Some(2_usize));
        assert_eq!(
            asked(
                &workspace,
                Json("textDocument/codeAction"),
                Json(
                    r#","range":{"start":{"line":0,"character":0},"end":{"line":0,"character":3}},"context":{"diagnostics":[]}"#
                ),
            ),
            serde_json::json!([]),
            "a range elsewhere is offered nothing"
        );
        let hovered = asked(&workspace, Json("textDocument/hover"), Json(inside));
        assert!(
            hovered
                .pointer("/contents/value")
                .and_then(Value::as_str)
                .is_some_and(|value| value.contains("**Checked fill** `42`: the answer")),
            "{hovered}"
        );
    }
}
