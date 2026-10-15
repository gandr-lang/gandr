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
//!
//! # The lifecycle and its error codes
//!
//! | Phase | Request | Answer |
//! | ----- | ------- | ------ |
//! | before `initialize` | any but `initialize` | `-32002` server not initialized |
//! | running | `initialize` again | `-32600` invalid request |
//! | running | a method the server does not serve | `-32601` method not found |
//! | running | a served method with parameters it cannot read | `-32602` invalid params |
//! | running | a formatting request for a document the formatter refuses | `-32803` request failed, with the reason |
//! | after `shutdown` | any | `-32600` invalid request |
//! | any | a body outside the decoder-supported JSON fragment | `-32700` parse error, under a null id |
//! | any | decoded JSON that is not a request, notification or response, a batch included | `-32600` invalid request |
//!
//! Before `initialize` every notification but `exit` is dropped. A notification
//! is never answered: one whose parameters the server cannot read is dropped, a
//! change to a document the server does not hold is dropped, and `$/`
//! notifications and every other unknown one are ignored, as the protocol
//! admits. A response from the client is read and discarded, since the server
//! sends no request.
//!
//! # Document URIs
//!
//! A document's URI is kept as the client spelled it, as the key it is
//! synchronised and published under. Its path, for the root classification
//! alone, is the `file` URI's path percent-decoded by `percent-encoding` 2.3.2
//! with `alloc` only, so `file:///x%C3%A9.gandr` names `/xé.gandr`. The
//! alternatives were `fluent-uri` 0.4.1, a full RFC 3986 parser for one
//! component, and `url` 2.5.8, whose `to_file_path` brings the WHATWG parser
//! and internationalised domain names. The choice reverses when the server
//! serves a workspace whose documents arrive under other schemes or remote
//! authorities, which needs a parser.

use alloc::collections::BTreeMap;
use core::cell::OnceCell;
use core::fmt;
use core::ops::ControlFlow;
use core::time::Duration;
use std::io::BufRead;
use std::io::Write;
use std::sync::mpsc::Sender;
use std::time::Instant;

use anodized::spec;
use gandr_surface_diagnostics::Verbosity;
use gandr_surface_pretty::Form;
use gandr_surface_render_remote::DocId;
use gandr_surface_render_remote::LineIndex;
use gandr_surface_render_remote::RenderFrame;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;
use serde::Deserialize as _;
use serde_json::Value;

use crate::format::edits;
use crate::hover::Hovering;
use crate::hover::Style;
use crate::hover::hover;
use crate::hover::hovering;
use crate::inline::ghost;
use crate::markup::Markup;
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
use crate::quiet::Holding;
use crate::quiet::Met;
use crate::quiet::QUIET;
use crate::quiet::formless;
use crate::quiet::paced;
use crate::quiet::publishable;
use crate::reading::Reading;
use crate::recheck::DocumentSession;
use crate::recheck::Timing;
use crate::recheck::Tried;
use crate::recheck::admit;
use crate::recheck::forms;
use crate::recheck::grammar;
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
use crate::transport::write_frame;
use crate::view::report;

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

quenchant_shape::reason_enum! {
    /// Why a copy has no caret.
    mod uncareted {
        /// The reason the caret is unknown.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub(super) enum Absent {
            /// The copy was opened, or its last change named no range: the
            /// whole text arrived at once, and nothing in it is being typed.
            Unranged,
        }
    }
}

/// One connection's copy of an open document, as that connection last
/// synchronised it, and the session its revisions are submitted to.
struct Document
{
    /// The version of its text.
    version: DocumentVersion,
    /// Its whole text, with the reading and the hover table the requests
    /// about it share.
    text: HeldText,
    /// The session holding its forms between synchronisations.
    session: DocumentSession,
    /// Where its last change left the caret: the end of the text the last
    /// ranged change inserted.
    caret: Maybe<ByteOffset, uncareted::Absent>,
    /// The diagnostics its session judged at its version, every one; those
    /// published and those the quiet publication holds.
    checked: Vec<Diagnostic>,
    /// The diagnostics last published at its version.
    published: Vec<Diagnostic>,
    /// The checked proposals kept for its version, in the order kept.
    proposals: Vec<Proposal>,
}

impl Document
{
    /// An empty copy of the document at `uri`, at `version`, with a session
    /// of its own.
    ///
    /// # Specification
    /// trivial.
    fn opened(
        uri: &DocumentUri,
        version: DocumentVersion,
    ) -> Self
    {
        Self {
            version,
            text: HeldText::new(),
            session: open(uri),
            caret: Maybe::Absent(uncareted::Absent::Unranged),
            checked: Vec::new(),
            published: Vec::new(),
            proposals: Vec::new(),
        }
    }
}

/// A copy's text and, once a request has asked, the one [`Reading`] of it and
/// the [`Hovering`] its hovers read.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a reading or a hover table, once made, is of the text as it
///   stands: every change to the text drops both.
/// - panics: none.
/// - executable: none — the text and what is read off it are private and change
///   only together, so the structure states the invariant and no call boundary
///   is left to check.
///
/// # Adequacy
/// - hypothesis: L2 — the editor scenarios hold every structural answer after
///   each keystroke to a fresh connection's over the same text and every hover
///   to answering; a reading kept past a change disagrees at the keystroke that
///   made it.
/// - witness: `editor::editor::scenarios::sweeps::random_edits_keep_every_answer_faithful`
/// - witness: `editor::editor::scenarios::sweeps::typing_each_corpus_source_keeps_every_answer_faithful`
struct HeldText
{
    /// The text.
    text: String,
    /// The reading of `text`, made by the first request that asks.
    reading: OnceCell<Reading>,
    /// The type table of `text`, made by the first hover after it changed.
    hovering: OnceCell<Hovering>,
}

impl HeldText
{
    /// The empty text, unread.
    ///
    /// # Specification
    /// trivial.
    const fn new() -> Self
    {
        Self {
            text: String::new(),
            reading: OnceCell::new(),
            hovering: OnceCell::new(),
        }
    }

    /// The text, as source.
    ///
    /// # Specification
    /// trivial.
    fn source(&self) -> SourceText<'_>
    {
        SourceText::from(self.text.as_str())
    }

    /// Hold `text` in place of the text held, unread.
    ///
    /// # Specification
    /// trivial.
    fn replace(
        &mut self,
        text: String,
    )
    {
        self.text = text;
        self.reading = OnceCell::new();
        self.hovering = OnceCell::new();
    }

    /// Apply `change` to the text held, as [`apply`] does, drop what was read
    /// off it, and return where the change left the caret.
    ///
    /// # Specification
    /// trivial.
    fn apply(
        &mut self,
        change: ContentChange,
    ) -> Maybe<ByteOffset, uncareted::Absent>
    {
        let caret = apply(&mut self.text, change);
        self.reading = OnceCell::new();
        self.hovering = OnceCell::new();
        caret
    }

    /// The reading of the text held, made now when no request has asked since
    /// it last changed.
    ///
    /// # Specification
    /// trivial.
    fn reading(&self) -> &Reading
    {
        self.reading.get_or_init(|| Reading::of(self.source()))
    }

    /// What the hovers of the text held read, made now when no hover has asked
    /// since it last changed.
    ///
    /// # Specification
    /// trivial.
    fn hovering(&self) -> &Hovering
    {
        self.hovering.get_or_init(|| hovering(self.source()))
    }
}

quenchant_shape::reason_enum! {
    /// Why a connection has no copy of a document.
    mod unheld {
        /// The reason no copy is there.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub(super) enum Absent {
            /// The connection never opened the document, or closed it.
            Unopened,
            /// No connection holds the document: none opened it, or its last
            /// copy was let go.
            Forgotten,
        }
    }
}

/// An open document: every holding connection's own copy, one of them the
/// latest to synchronise.
///
/// # Specification
/// - requires: nothing.
/// - ensures: every holding connection has exactly one copy, the latest is one
///   of them, and a held document has at least one.
/// - panics: none.
/// - executable: none — the latest copy is a field rather than a key, so the
///   structure states the invariant and no call boundary is left to check.
///
/// # Adequacy
/// - hypothesis: L2 — the editor simulation's two-editor scenarios edit one
///   document from two connections, mirrored and apart, and hold each
///   connection's every answer to a fresh connection's over its own text.
/// - witness: `server::tests::two_connections_hold_their_own_copies`
struct Held
{
    /// The connection whose copy synchronised last.
    latest: Peer,
    /// Its copy.
    document: Document,
    /// Every other holding connection's copy.
    others: BTreeMap<Peer, Document>,
}

impl Held
{
    /// The copy `peer` holds.
    ///
    /// # Specification
    /// trivial.
    fn own(
        &self,
        peer: Peer,
    ) -> Maybe<&Document, unheld::Absent>
    {
        if peer == self.latest {
            Maybe::Present(&self.document)
        }
        else {
            self.others
                .get(&peer)
                .map_or(Maybe::Absent(unheld::Absent::Unopened), Maybe::Present)
        }
    }

    /// The copy `peer` holds, to change.
    ///
    /// # Specification
    /// trivial.
    fn own_mut(
        &mut self,
        peer: Peer,
    ) -> Maybe<&mut Document, unheld::Absent>
    {
        if peer == self.latest {
            Maybe::Present(&mut self.document)
        }
        else {
            self.others
                .get_mut(&peer)
                .map_or(Maybe::Absent(unheld::Absent::Unopened), Maybe::Present)
        }
    }

    /// The copy `peer` is answered from: its own, or the latest when it holds
    /// none.
    ///
    /// # Specification
    /// trivial.
    fn view(
        &self,
        peer: Peer,
    ) -> &Document
    {
        match self.own(peer) {
            Maybe::Present(document) => document,
            Maybe::Absent(_) => &self.document,
        }
    }

    /// Make `peer`'s copy the latest, when it holds one.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: when `peer` holds a copy it is the latest and the copy that
    ///   was latest is kept among the others; otherwise nothing changes.
    /// - provides: the other faces' reading of whichever connection
    ///   synchronised last.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — after the second of two connections synchronises, the
    ///   workspace's published diagnostics are its copy's, and the first's copy
    ///   still answers the first.
    /// - witness: `server::tests::two_connections_hold_their_own_copies`
    #[spec(captures: [holders = self.others.len()],
        ensures: self.others.len() == holders && (self.latest == peer || !self.others.contains_key(&peer)))]
    fn promote(
        &mut self,
        peer: Peer,
    )
    {
        if let Some(document) = self.others.remove(&peer) {
            let previous = core::mem::replace(&mut self.document, document);
            let _held = self.others.insert(self.latest, previous);
            self.latest = peer;
        }
    }

    /// Give `peer` a copy, an empty one at `version` when it holds none, and
    /// make it the latest.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `peer`'s copy is the latest; a copy it already held is kept,
    ///   session and all, and every other connection's copy is unchanged.
    /// - provides: an open, which then overwrites the copy's text.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a second connection opening a held document gets a
    ///   copy of its own beside the first's, which keeps answering the first.
    /// - witness: `server::tests::two_connections_hold_their_own_copies`
    #[spec(captures: [holders = self.others.len().saturating_add(1_usize)],
        ensures: self.latest == peer && self.others.len().saturating_add(1_usize) >= holders)]
    fn take_up(
        &mut self,
        peer: Peer,
        uri: &DocumentUri,
        version: DocumentVersion,
    )
    {
        if matches!(self.own(peer), Maybe::Absent(_)) {
            let _first = self.others.insert(peer, Document::opened(uri, version));
        }
        self.promote(peer);
    }

    /// The document without `peer`'s copy.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `peer` holds no copy of what is returned, and every other
    ///   connection keeps its copy; when `peer`'s copy was the latest, the copy
    ///   of the lowest-numbered other connection becomes the latest; when it
    ///   was the only copy, nothing is returned.
    /// - provides: a connection's close, or its departure.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the latest holder closing while another still holds
    ///   the document leaves it answering the other, and the last close forgets
    ///   it.
    /// - witness: `server::tests::two_connections_hold_their_own_copies`
    /// - witness: `server::tests::a_departing_connection_leaves_the_others_served`
    #[spec(ensures: |ret| match ret {
        Maybe::Present(ref held) => held.latest != peer && !held.others.contains_key(&peer),
        Maybe::Absent(_) => true,
    })]
    fn release(
        mut self,
        peer: Peer,
    ) -> Maybe<Self, unheld::Absent>
    {
        if peer != self.latest {
            let _released = self.others.remove(&peer);
            return Maybe::Present(self);
        }
        match self.others.pop_first() {
            Some((latest, document)) => Maybe::Present(Self {
                latest,
                document,
                others: self.others,
            }),
            None => Maybe::Absent(unheld::Absent::Forgotten),
        }
    }
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
/// it reached, what rechecking it cost, and whether its publication held a
/// diagnostic back.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Logged
{
    /// The document synchronised.
    uri: DocumentUri,
    /// The version it reached.
    version: DocumentVersion,
    /// What rechecking it cost.
    timing: Timing,
    /// Whether its publication held a diagnostic back.
    holding: Holding,
}

impl Logged
{
    /// The document synchronised.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn uri(&self) -> &DocumentUri
    {
        &self.uri
    }

    /// Whether the synchronisation's publication held a diagnostic back.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn holding(&self) -> Holding
    {
        self.holding
    }
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
/// The open documents, each with every holding connection's own copy, and
/// which watchers hear of each change.
///
/// Each connection's changes apply to its own copy and each connection is
/// answered from it, so two editors over one document are each answered for
/// the text they hold: two clients of one editor buffer, which both send
/// every change, keep two equal copies, and two editors with buffers of
/// their own keep two that differ. The latest copy to synchronise is the one
/// the other faces read — the render bus, the agent face's queries, trials
/// and proposals — and the one a connection holding no copy is answered
/// from.
///
/// The recorded design held one text and one session per document, applied
/// every holder's changes to it, and forwarded each publication to every
/// other holder, so a second connection's open molded nothing. Two clients of
/// one buffer then applied each edit twice. One text with a change applied
/// only when its version passes the held one was the other repair; clients
/// number versions independently, so two whose numbering drifted apart would
/// lose each other's edits. A copy costs a session per holding connection and
/// a cold check at its open; a session that forks, sharing its form store and
/// checkpoints between copies, is the lever if that cost is ever measured.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a document is held while at least one connection holds a copy,
///   and is forgotten with its sessions once none does.
/// - panics: none.
/// - executable: none — this state carrier has no call boundary; the server's
///   handling carries the executable clauses.
///
/// # Adequacy
/// - hypothesis: L3 — two connections opening, editing, querying and closing
///   one document, and one leaving while the other stays, are each answered for
///   their own copy.
/// - witness: `server::tests::two_connections_hold_their_own_copies`
/// - witness: `server::tests::a_departing_connection_leaves_the_others_served`
#[derive(Default)]
pub struct Workspace
{
    /// Every open document, by its URI.
    documents: BTreeMap<DocumentUri, Held>,
    /// Where each watching connection hears which document changed.
    watchers: BTreeMap<Peer, Sender<DocumentUri>>,
}

impl Workspace
{
    /// Admit `peer` as a watcher: the URI of each document a synchronisation
    /// publishes, of each whose latest copy is let go, and of each forgotten,
    /// goes to `watcher`.
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

    /// The open documents and the version each one's latest copy is at, in
    /// URI order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn held(&self) -> impl Iterator<Item = (&DocumentUri, DocumentVersion)>
    {
        self.documents
            .iter()
            .map(|(uri, held)| (uri, held.document.version))
    }

    /// The diagnostics last published for the document at `uri`, and the
    /// version they were published at.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `None` for a document no connection holds; otherwise the last
    ///   diagnostics published at its latest copy's version, empty until that
    ///   copy's first synchronisation publishes.
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
            .map(|held| (held.document.version, held.document.published.as_slice()))
    }

    /// The render bus's greeting: every open document, at the version its
    /// latest copy is at, in URI order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn greeting(&self) -> RenderFrame
    {
        RenderFrame::hello(
            self.documents
                .iter()
                .map(|(uri, held)| DocId {
                    uri: uri.into(),
                    version: held.document.version.into(),
                })
                .collect(),
        )
    }

    /// The render bus's report of the document at `uri`, as its latest copy's
    /// last synchronisation published it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `None` for a document no connection holds; otherwise a frame
    ///   scoped to the document at its latest copy's version, carrying the
    ///   [`crate::view::report`] of that copy's text and published diagnostics.
    /// - provides: what the render-bus face sends after each publication.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a client attached to a hub receives a held document's
    ///   frame at its version, then the next version's after an edit, and a
    ///   resync answered at the current version.
    /// - witness: `hub::tests::an_attached_view_follows_the_editors_edits`
    #[spec(ensures: |ret| ret.is_some() == self.documents.contains_key(uri))]
    #[inline]
    #[must_use]
    pub fn rendered(
        &self,
        uri: &DocumentUri,
    ) -> Option<RenderFrame>
    {
        self.documents.get(uri).map(|held| {
            let document = &held.document;
            RenderFrame::frame(
                DocId {
                    uri: uri.into(),
                    version: document.version.into(),
                },
                report(
                    document.text.source(),
                    document.text.reading(),
                    &document.published,
                ),
            )
        })
    }

    /// Judge each of `changes`, applied alone to the latest copy of the
    /// document at `uri` as it stands, without submitting any: that copy's
    /// version and each candidate's result, best first.
    ///
    /// # Specification
    /// - requires: nothing; any changes are admissible input.
    /// - ensures: `None` for a document no connection holds; otherwise one
    ///   result per change, each the [`crate::recheck::trial`] of the latest
    ///   copy's text with that change alone applied as a synchronisation
    ///   applies it — a ranged change splices its text over the range, one
    ///   naming no range is the whole text — ranked as the trial ranks them.
    ///   Every copy, its session and its published diagnostics are unchanged.
    /// - provides: batched candidate fills at a hole or over a declaration's
    ///   body, for another face.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a fill spliced over a hole and a whole replacement
    ///   are judged and ranked, and the document reads back as it was.
    /// - witness: `server::tests::a_workspace_tries_candidate_fills`
    #[spec(ensures: |ret| ret.as_ref().is_none_or(|&(version, ref tried)|
        tried.len() == changes.len() && self.documents.get(uri).is_some_and(|held| held.document.version == version)))]
    #[inline]
    #[must_use]
    pub fn trial(
        &self,
        uri: &DocumentUri,
        changes: &[ContentChange],
    ) -> Option<(DocumentVersion, Vec<Tried>)>
    {
        let document = &self.documents.get(uri)?.document;
        let texts: Vec<String> = changes
            .iter()
            .map(|change| {
                let mut text = String::from(document.text.source().as_ref());
                let _caret = apply(&mut text, change.clone());
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

    /// Keep `proposal`, a model's fill of a range of the latest copy of the
    /// document at `uri` made against `version`, once it checks.
    ///
    /// # Specification
    /// - requires: nothing; any proposal is admissible input.
    /// - ensures: a document no connection holds, or one whose latest copy's
    ///   version is not `version`, refuses the proposal and keeps nothing.
    ///   Otherwise that copy with the fill applied is tried as [`Self::trial`]
    ///   tries a change; a fill that passes [`check`] against the copy's
    ///   published diagnostics is kept beside it, after those kept before, and
    ///   its trial's diagnostics answered; one that does not is refused with
    ///   them. Every copy's text, session and published diagnostics are
    ///   unchanged.
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
        captures: kept = self.documents.get(uri).map_or(0_usize, |held| held.document.proposals.len()),
        ensures: |ret| self.documents.get(uri).map_or(0_usize, |held| held.document.proposals.len())
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
            .document
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
        let document = &mut self
            .documents
            .get_mut(uri)
            .ok_or(ProposalRefusal::NotHeld)?
            .document;
        let diagnostics = check(tried, &document.published)?;
        document.proposals.push(proposal);
        Ok(diagnostics)
    }

    /// The response a running connection holding no copy gives the request
    /// `request`, read off each document's latest copy, as JSON.
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
            quiet: QUIET,
            style: STYLE,
        };
        let answer = match classify(request) {
            Err(malformed) => malformed.response(),
            Ok(Incoming::Request { id, method, params }) => {
                reader.request(self, id, &method, params)
            },
            Ok(Incoming::Notification { .. } | Incoming::Response) => return Value::Null,
        };
        serde_json::to_value(answer).unwrap_or(Value::Null)
    }

    /// Let `peer` go: it holds no copy any more and watches nothing, and a
    /// document no other connection holds is forgotten with its sessions.
    ///
    /// # Specification
    /// - requires: nothing; a peer that never connected or held nothing is
    ///   admitted.
    /// - ensures: `peer` watches nothing and holds no copy of any document;
    ///   every document left is held by another connection.
    /// - provides: a connection's end, clean or not.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one of two connections holding a document leaving,
    ///   then the other, observe the document kept, then forgotten.
    /// - witness: `server::tests::a_departing_connection_leaves_the_others_served`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body lets go of every document once; the check reads each document once"
        )
    )]
    #[spec(ensures: !self.watchers.contains_key(&peer)
        && self.documents.values().all(|held| matches!(held.own(peer), Maybe::Absent(_))))]
    #[inline]
    pub fn depart(
        &mut self,
        peer: Peer,
    )
    {
        let _watcher = self.watchers.remove(&peer);
        for (uri, held) in core::mem::take(&mut self.documents) {
            self.let_go(uri, held, peer);
        }
    }

    /// Keep `held`, the document at `uri`, without `peer`'s copy, forgetting
    /// it when that copy was the last, and tell every watcher when the copy
    /// let go was the latest.
    ///
    /// # Specification
    /// trivial.
    fn let_go(
        &mut self,
        uri: DocumentUri,
        held: Held,
        peer: Peer,
    )
    {
        if held.latest == peer {
            for watcher in self.watchers.values() {
                let _gone = watcher.send(uri.clone());
            }
        }
        if let Maybe::Present(held) = held.release(peer) {
            let _kept = self.documents.insert(uri, held);
        }
    }

    /// Record `message`, a publication `peer`'s handling made, as the last
    /// diagnostics of `peer`'s copy, and tell every watcher.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a diagnostic notification at the version of `peer`'s copy of
    ///   a held document becomes that copy's published diagnostics, and its URI
    ///   is sent to every watcher; anything else is recorded nowhere and sent
    ///   nowhere. A watcher whose connection is gone takes nothing, silently.
    ///   No other connection is sent the publication: each holder's copy
    ///   publishes its own.
    /// - panics: none.
    /// - executable: none — the sends land in channels whose receiving ends
    ///   this call does not hold, so nothing it can read states them.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an open's diagnostics are read back at its version,
    ///   and a watcher hears which document changed.
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
        let Some(held) = self.documents.get_mut(&params.uri)
        else {
            return;
        };
        let Maybe::Present(document) = held.own_mut(peer)
        else {
            return;
        };
        if params.version != Some(document.version) {
            return;
        }
        document.published.clone_from(&params.diagnostics);
        for watcher in self.watchers.values() {
            let _gone = watcher.send(params.uri.clone());
        }
    }
}

/// One connection's state.
///
/// Where it stands in the lifecycle, which connection it is, how much of
/// each report its diagnostics carry, how long a diagnostic of the form under
/// the caret waits, and how its hovers spell types and are written.
pub struct Server
{
    /// Where the connection stands in the lifecycle.
    phase: Phase,
    /// Which connection it is.
    peer: Peer,
    /// The level its editor's `gandr.diagnostics.verbosity` setting names:
    /// read at `initialize` and at each `workspace/didChangeConfiguration`.
    verbosity: Verbosity,
    /// The interval its editor's `gandr.diagnostics.quiet` setting names, read
    /// as the verbosity is; zero holds nothing.
    quiet: Duration,
    /// The form its editor's `gandr.presentation.form` setting names, read as
    /// the verbosity is, and the markup its client's markdown renderer reads,
    /// read at `initialize`.
    style: Style,
}

/// The style a connection hovers in until `initialize` says otherwise: the
/// sugared form, in markdown.
const STYLE: Style = Style {
    form: Form::Sugared,
    markup: Markup::Markdown,
};

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
            quiet: QUIET,
            style: STYLE,
        }
    }

    /// How long a document goes without a change before the diagnostics held
    /// for the form under its caret publish; zero when nothing is held.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn quiet(&self) -> Duration
    {
        self.quiet
    }

    /// Publish whatever this connection's copy of `uri` holds back: every
    /// diagnostic its session judged at its version, when its last
    /// publication left any out.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: when this connection holds a copy of `uri` whose published
    ///   diagnostics are fewer than it checked, one diagnostic notification at
    ///   `uri` and the copy's version carrying all of them, recorded as the
    ///   copy's publication; nothing otherwise.
    /// - provides: the promotion a passed deadline makes, and the one a
    ///   configuration that holds nothing makes.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a held diagnostic publishes at the copy's version
    ///   when released, and a copy holding nothing publishes nothing.
    /// - witness: `editor::editor::scenarios::typing_a_declaration_holds_its_diagnostics_until_its_terminator`
    /// - witness: `session::session::a_held_diagnostic_publishes_once_the_document_is_quiet`
    #[spec(ensures: |ret| ret.len() <= 1)]
    #[inline]
    #[must_use]
    pub fn release(
        &self,
        workspace: &mut Workspace,
        uri: &DocumentUri,
    ) -> Vec<Outgoing>
    {
        let Some(held) = workspace.documents.get(uri)
        else {
            return Vec::new();
        };
        let Maybe::Present(document) = held.own(self.peer)
        else {
            return Vec::new();
        };
        if document.published.len() >= document.checked.len() {
            return Vec::new();
        }
        let release = publish(PublishParams {
            uri: uri.clone(),
            version: Some(document.version),
            diagnostics: document.checked.clone(),
        });
        workspace.published_by(self.peer, &release);
        vec![release]
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
            Err(malformed) => Outcome::say(malformed.response()),
            Ok(Incoming::Response) => Outcome::quiet(),
            Ok(Incoming::Request { id, method, params }) => {
                Outcome::say(self.request(workspace, id, &method, params))
            },
            Ok(Incoming::Notification { method, params }) => {
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
            Phase::ShuttingDown => Served::Clean,
            Phase::Waiting | Phase::Running => Served::Abrupt,
        }
    }

    /// Run the kernel admission each synchronisation logged in `log` left, its
    /// diagnostics already published, and return what to publish in their
    /// place.
    ///
    /// # Specification
    /// - requires: `log` is the log of the outcome [`Server::handle`] returned
    ///   last, its messages already written.
    /// - ensures: each line naming a document of which this connection holds a
    ///   copy at the line's version runs the admission that copy's session
    ///   holds, as [`admit`] states, and carries its wall; a kernel
    ///   disagreement adds one diagnostic notification at the line's URI and
    ///   version whose one diagnostic names it, recorded as the copy's
    ///   publication and as all it checked, and the line holds nothing. Every
    ///   other line is left as it was.
    /// - provides: the second half of every synchronisation; [`serve`] writes
    ///   what it returns, then logs the lines.
    /// - fails: never; a disagreement is a diagnostic.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a change's logged line gains the admission's wall and
    ///   publishes nothing more when the kernel agrees; a line naming a closed
    ///   document is left as it was. Corrections are made in log order, so the
    ///   predicate matches them against the log in one ordered pass.
    /// - witness: `server::tests::an_admission_follows_its_synchronisation`
    /// - witness: `session::session::an_edit_to_a_large_document_rechecks_its_forms`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body walks every logged line once; the check walks them once more in order beside the corrections"
        )
    )]
    #[spec(ensures: |ret| ret.len() <= log.len() && {
        let mut lines = log.iter();
        ret.iter().all(|message| matches!(*message,
            Outgoing::Notification { method: "textDocument/publishDiagnostics", ref params, .. }
                if params.diagnostics.len() == 1 && lines.any(|logged|
                    logged.uri == params.uri && Some(logged.version) == params.version)))
    })]
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
            let Some(held) = workspace.documents.get_mut(&logged.uri)
            else {
                continue;
            };
            let Maybe::Present(document) = held.own_mut(self.peer)
            else {
                continue;
            };
            if document.version != logged.version {
                continue;
            }
            let admitted = admit(&mut document.session, logged.timing);
            logged.timing = admitted.timing;
            if let Maybe::Present(fault) = admitted.fault {
                document.checked = vec![fault.clone()];
                logged.holding = Holding(false);
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
    ///   initialization takes the verbosity, the quiet interval and the
    ///   presentation form its options name, the user level, [`QUIET`] and the
    ///   sugared form when they name none, and the markup its client's
    ///   capabilities name; other requests preserve them, and no request
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
        captures: [phase = self.phase, initial = initial_settings(&params), markup = initial_markup(&params)],
        ensures: |ret| match (phase, method.as_ref()) {
            (Phase::Waiting, "initialize") => self.phase == Phase::Running
                && self.verbosity == initial.verbosity().unwrap_or_default()
                && self.quiet == initial.quiet().unwrap_or(QUIET)
                && self.style == Style { form: initial.form().unwrap_or(Form::Sugared), markup }
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
                    Outgoing::Success { .. } | Outgoing::Notification { .. } => false,
                },
            (Phase::Running, "textDocument/inlineCompletion") =>
                self.phase == phase && match ret {
                    Outgoing::Success { result: Answer::Nothing | Answer::Inline(_), .. } => true,
                    Outgoing::Failure { ref error, .. } => error.code == ErrorCode::INVALID_PARAMS,
                    Outgoing::Success { .. } | Outgoing::Notification { .. } => false,
                },
            (Phase::Running, "textDocument/documentSymbol" | "textDocument/foldingRange" | "textDocument/selectionRange") =>
                self.phase == phase && match ret {
                    Outgoing::Success { result: Answer::Nothing | Answer::Symbols(_) | Answer::Folds(_) | Answer::Selections(_), .. } => true,
                    Outgoing::Failure { ref error, .. } => error.code == ErrorCode::INVALID_PARAMS,
                    Outgoing::Success { .. } | Outgoing::Notification { .. } => false,
                },
            (Phase::Running, "textDocument/hover") =>
                self.phase == phase && match ret {
                    Outgoing::Success { result: Answer::Nothing | Answer::Hover(_), .. } => true,
                    Outgoing::Failure { ref error, .. } => error.code == ErrorCode::INVALID_PARAMS,
                    Outgoing::Success { .. } | Outgoing::Notification { .. } => false,
                },
            (Phase::Running, "textDocument/codeLens" | "textDocument/codeAction") =>
                self.phase == phase && match ret {
                    Outgoing::Success { result: Answer::Nothing | Answer::Lenses(_) | Answer::Actions(_), .. } => true,
                    Outgoing::Failure { ref error, .. } => error.code == ErrorCode::INVALID_PARAMS,
                    Outgoing::Success { .. } | Outgoing::Notification { .. } => false,
                },
            (Phase::Running, "textDocument/formatting" | "textDocument/rangeFormatting") =>
                self.phase == phase && match ret {
                    Outgoing::Success { result: Answer::Nothing | Answer::Edits(_), .. } => true,
                    Outgoing::Failure { ref error, .. } =>
                        error.code == ErrorCode::INVALID_PARAMS || error.code == ErrorCode::REQUEST_FAILED,
                    Outgoing::Success { .. } | Outgoing::Notification { .. } => false,
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
            (Phase::Waiting, "initialize") => {
                self.phase = Phase::Running;
                let settings = initial_settings(&params);
                self.verbosity = settings.verbosity().unwrap_or_default();
                self.quiet = settings.quiet().unwrap_or(QUIET);
                self.style = Style {
                    form: settings.form().unwrap_or(Form::Sugared),
                    markup: initial_markup(&params),
                };
                success(
                    id,
                    Answer::Initialize(Box::new(InitializeResult::advertised())),
                )
            },
            (Phase::Waiting, _) => failure(
                id,
                ErrorCode::SERVER_NOT_INITIALIZED,
                format!("`{name}` arrived before `initialize`"),
            ),
            (Phase::Running, "initialize") => failure(
                id,
                ErrorCode::INVALID_REQUEST,
                "`initialize` was already answered".to_owned(),
            ),
            (Phase::Running, "shutdown") => {
                self.phase = Phase::ShuttingDown;
                success(id, Answer::Nothing)
            },
            (Phase::Running, "textDocument/semanticTokens/full") => {
                match serde_json::from_value::<DocumentParams>(params) {
                    Ok(params) => success(
                        id,
                        workspace.tokens(&params.text_document.uri, self.peer, Window::Whole),
                    ),
                    Err(error) => failure(id, ErrorCode::INVALID_PARAMS, error.to_string()),
                }
            },
            (Phase::Running, "textDocument/semanticTokens/range") => {
                match serde_json::from_value::<RangeParams>(params) {
                    Ok(params) => success(
                        id,
                        workspace.tokens(
                            &params.text_document.uri,
                            self.peer,
                            Window::Within(params.range),
                        ),
                    ),
                    Err(error) => failure(id, ErrorCode::INVALID_PARAMS, error.to_string()),
                }
            },
            (Phase::Running, "textDocument/inlineCompletion") => {
                match serde_json::from_value::<PositionParams>(params) {
                    Ok(params) => success(
                        id,
                        workspace.inline(&params.text_document.uri, self.peer, params.position),
                    ),
                    Err(error) => failure(id, ErrorCode::INVALID_PARAMS, error.to_string()),
                }
            },
            (Phase::Running, "textDocument/documentSymbol") => {
                match serde_json::from_value::<DocumentParams>(params) {
                    Ok(params) => success(
                        id,
                        workspace.outline(&params.text_document.uri, self.peer, |reading, _| {
                            Answer::Symbols(reading.symbols())
                        }),
                    ),
                    Err(error) => failure(id, ErrorCode::INVALID_PARAMS, error.to_string()),
                }
            },
            (Phase::Running, "textDocument/foldingRange") => {
                match serde_json::from_value::<DocumentParams>(params) {
                    Ok(params) => success(
                        id,
                        workspace.outline(&params.text_document.uri, self.peer, |reading, _| {
                            Answer::Folds(reading.folds().to_vec())
                        }),
                    ),
                    Err(error) => failure(id, ErrorCode::INVALID_PARAMS, error.to_string()),
                }
            },
            (Phase::Running, "textDocument/selectionRange") => {
                match serde_json::from_value::<SelectionRangeParams>(params) {
                    Ok(params) => success(
                        id,
                        workspace.outline(&params.text_document.uri, self.peer, |reading, text| {
                            Answer::Selections(reading.selections(
                                &LineIndex::new(text.as_ref().into()),
                                &params.positions,
                            ))
                        }),
                    ),
                    Err(error) => failure(id, ErrorCode::INVALID_PARAMS, error.to_string()),
                }
            },
            (Phase::Running, "textDocument/hover") => {
                match serde_json::from_value::<PositionParams>(params) {
                    Ok(params) => success(
                        id,
                        workspace.hover(
                            &params.text_document.uri,
                            self.peer,
                            params.position,
                            self.style,
                        ),
                    ),
                    Err(error) => failure(id, ErrorCode::INVALID_PARAMS, error.to_string()),
                }
            },
            (Phase::Running, "textDocument/codeLens") => {
                match serde_json::from_value::<DocumentParams>(params) {
                    Ok(params) => success(
                        id,
                        match workspace.view(&params.text_document.uri, self.peer) {
                            Maybe::Present(document) => Answer::Lenses(lenses(&document.proposals)),
                            Maybe::Absent(_) => Answer::Nothing,
                        },
                    ),
                    Err(error) => failure(id, ErrorCode::INVALID_PARAMS, error.to_string()),
                }
            },
            (Phase::Running, "textDocument/codeAction") => {
                match serde_json::from_value::<RangeParams>(params) {
                    Ok(params) => success(
                        id,
                        match workspace.view(&params.text_document.uri, self.peer) {
                            Maybe::Present(document) => Answer::Actions(actions(
                                &params.text_document.uri,
                                &document.proposals,
                                params.range,
                            )),
                            Maybe::Absent(_) => Answer::Nothing,
                        },
                    ),
                    Err(error) => failure(id, ErrorCode::INVALID_PARAMS, error.to_string()),
                }
            },
            (Phase::Running, "textDocument/formatting") => {
                match serde_json::from_value::<DocumentParams>(params) {
                    Ok(params) => {
                        workspace.format(id, &params.text_document.uri, self.peer, Window::Whole)
                    },
                    Err(error) => failure(id, ErrorCode::INVALID_PARAMS, error.to_string()),
                }
            },
            (Phase::Running, "textDocument/rangeFormatting") => {
                match serde_json::from_value::<RangeParams>(params) {
                    Ok(params) => workspace.format(
                        id,
                        &params.text_document.uri,
                        self.peer,
                        Window::Within(params.range),
                    ),
                    Err(error) => failure(id, ErrorCode::INVALID_PARAMS, error.to_string()),
                }
            },
            (Phase::Running, _) => failure(
                id,
                ErrorCode::METHOD_NOT_FOUND,
                format!("`{name}` is not served"),
            ),
            (Phase::ShuttingDown, _) => failure(
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
    ///   publish this connection's copy of the document at its supplied version
    ///   to this connection alone, log one timing line, and make that copy the
    ///   latest; a change holds back the diagnostics of the form under the
    ///   caret it leaves, as [`publishable`] states, while the quiet interval
    ///   is not zero. An open gives this connection a copy with a session of
    ///   its own when it holds none, then sets the copy's text and version;
    ///   every other connection's copy is untouched. A change applies each
    ///   content change in order to this connection's copy, as [`apply`]
    ///   states; an empty change list preserves text. Close lets this
    ///   connection's copy go, forgets the document once no connection holds a
    ///   copy, and publishes a versionless empty diagnostic list to this
    ///   connection, even for an unknown URI. A running-state configuration
    ///   change whose `gandr` section names a quiet interval takes it, and one
    ///   naming a presentation form takes it for every later hover. One that
    ///   names a verbosity other than this connection's takes it, then
    ///   republishes every copy this connection holds, in URI order, at its
    ///   version, to this connection alone, logging one timing line each;
    ///   otherwise, one that names a zero interval publishes what each copy
    ///   holds back, as [`Server::release`] states, and one naming neither
    ///   changes nothing. Unknown, malformed and out-of-phase notifications
    ///   leave documents alone.
    /// - provides: document synchronization, configuration and termination.
    /// - fails: unreadable parameters and changes to documents this connection
    ///   holds no copy of are ignored.
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
    /// - witness: `server::tests::a_configuration_change_reanswers_hovers_in_its_form`
    /// - witness: `server::tests::two_connections_hold_their_own_copies`
    #[spec(
        captures: [phase = self.phase, count = workspace.documents.len()],
        ensures: |ret| self.phase == phase
            && (ret.messages.len() <= 1 || method.as_ref() == "workspace/didChangeConfiguration")
            && match method.as_ref() {
                "textDocument/didOpen" | "textDocument/didChange" => ret.log.len() == usize::from(!ret.messages.is_empty()),
                "workspace/didChangeConfiguration" => ret.log.len() <= ret.messages.len(),
                _ => ret.log.is_empty(),
            }
            && ret.flow == if method.as_ref() == "exit" { Flow::Exit(self.closed()) } else { Flow::Continue }
            && if ret.messages.is_empty() { workspace.documents.len() == count } else {
                phase == Phase::Running && ret.messages.iter().all(|message| match *message {
                    Outgoing::Notification { ref params, .. } => match method.as_ref() {
                        "textDocument/didOpen" | "textDocument/didChange" | "workspace/didChangeConfiguration" =>
                            workspace.documents.get(&params.uri).is_some_and(|held| matches!(held.own(self.peer),
                                Maybe::Present(document) if params.version == Some(document.version))),
                        "textDocument/didClose" => params.version.is_none() && params.diagnostics.is_empty()
                            && workspace.documents.get(&params.uri)
                                .is_none_or(|held| matches!(held.own(self.peer), Maybe::Absent(_))),
                        _ => false,
                    },
                    Outgoing::Success { .. } | Outgoing::Failure { .. } => false,
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
            (_, "exit") => Outcome {
                messages: Vec::new(),
                log: Vec::new(),
                flow: Flow::Exit(self.closed()),
            },
            (Phase::Running, "textDocument/didOpen") => {
                let Ok(DidOpenParams { text_document }) = serde_json::from_value(params)
                else {
                    return Outcome::quiet();
                };
                let uri = text_document.uri;
                let held = workspace
                    .documents
                    .entry(uri.clone())
                    .or_insert_with(|| Held {
                        latest: self.peer,
                        document: Document::opened(&uri, text_document.version),
                        others: BTreeMap::new(),
                    });
                held.take_up(self.peer, &uri, text_document.version);
                let document = &mut held.document;
                document.version = text_document.version;
                document.text.replace(text_document.text);
                document.caret = Maybe::Absent(uncareted::Absent::Unranged);
                document.proposals.clear();
                let outcome = synchronised(&uri, document, self.verbosity, self.quiet);
                for message in &outcome.messages {
                    workspace.published_by(self.peer, message);
                }
                outcome
            },
            (Phase::Running, "textDocument/didChange") => {
                let Ok(DidChangeParams {
                    text_document,
                    content_changes,
                }) = serde_json::from_value(params)
                else {
                    return Outcome::quiet();
                };
                let Some(held) = workspace.documents.get_mut(&text_document.uri)
                else {
                    return Outcome::quiet();
                };
                held.promote(self.peer);
                let Maybe::Present(document) = held.own_mut(self.peer)
                else {
                    return Outcome::quiet();
                };
                document.version = text_document.version;
                document.proposals.clear();
                for change in content_changes {
                    document.caret = document.text.apply(change);
                }
                let outcome =
                    synchronised(&text_document.uri, document, self.verbosity, self.quiet);
                for message in &outcome.messages {
                    workspace.published_by(self.peer, message);
                }
                outcome
            },
            (Phase::Running, "textDocument/didClose") => {
                let Ok(DocumentParams { text_document }) = serde_json::from_value(params)
                else {
                    return Outcome::quiet();
                };
                if let Some(held) = workspace.documents.remove(&text_document.uri) {
                    workspace.let_go(text_document.uri.clone(), held, self.peer);
                }
                Outcome::say(publish(PublishParams {
                    uri: text_document.uri,
                    version: None,
                    diagnostics: Vec::new(),
                }))
            },
            (Phase::Running, "workspace/didChangeConfiguration") => {
                let Some(settings) = serde_json::from_value::<ConfigurationParams>(params)
                    .ok()
                    .and_then(|params| params.settings)
                    .and_then(|sections| sections.gandr)
                else {
                    return Outcome::quiet();
                };
                if let Some(quiet) = settings.quiet() {
                    self.quiet = quiet;
                }
                if let Some(form) = settings.form() {
                    self.style.form = form;
                }
                let mut outcome = Outcome::quiet();
                let Some(verbosity) = settings
                    .verbosity()
                    .filter(|&verbosity| verbosity != self.verbosity)
                else {
                    if settings.quiet().is_some_and(|quiet| quiet.is_zero()) {
                        let uris: Vec<DocumentUri> = workspace.documents.keys().cloned().collect();
                        for uri in &uris {
                            outcome.messages.extend(self.release(workspace, uri));
                        }
                    }
                    return outcome;
                };
                self.verbosity = verbosity;
                let peer = self.peer;
                for (uri, held) in &mut workspace.documents {
                    let Maybe::Present(document) = held.own_mut(peer)
                    else {
                        continue;
                    };
                    let republished = synchronised(uri, document, verbosity, self.quiet);
                    outcome.messages.extend(republished.messages);
                    outcome.log.extend(republished.log);
                }
                for message in &outcome.messages {
                    workspace.published_by(peer, message);
                }
                outcome
            },
            (Phase::Waiting | Phase::Running | Phase::ShuttingDown, _) => Outcome::quiet(),
        }
    }
}

impl Workspace
{
    /// The copy of the document at `uri` that `peer` is answered from: its
    /// own, or the latest when it holds none.
    ///
    /// # Specification
    /// trivial.
    fn view(
        &self,
        uri: &DocumentUri,
        peer: Peer,
    ) -> Maybe<&Document, unheld::Absent>
    {
        self.documents
            .get(uri)
            .map_or(Maybe::Absent(unheld::Absent::Forgotten), |held| {
                Maybe::Present(held.view(peer))
            })
    }

    /// The tokens of the copy of the document at `uri` that `peer` is
    /// answered from, in `window`.
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
            && match window { Window::Within(range) if range.start >= range.end => tokens.data.as_ref().is_empty(), Window::Whole | Window::Within(_) => true },
        Answer::Initialize(_) | Answer::Inline(_) | Answer::Symbols(_) | Answer::Folds(_) | Answer::Selections(_)
            | Answer::Hover(_) | Answer::Edits(_) | Answer::Lenses(_) | Answer::Actions(_) => false,
    })]
    fn tokens(
        &self,
        uri: &DocumentUri,
        peer: Peer,
        window: Window,
    ) -> Answer
    {
        let Maybe::Present(document) = self.view(uri, peer)
        else {
            return Answer::Nothing;
        };
        let index = LineIndex::new(<&str>::from(document.text.source()).into());
        let spans = document.text.reading().spans();
        let spans = match window {
            Window::Whole => spans.to_vec(),
            Window::Within(range) => {
                overlapping(spans, range.start.byte(&index), range.end.byte(&index))
            },
        };
        Answer::Tokens(SemanticTokens {
            data: encode(&index, &spans),
        })
    }

    /// The inline completion of the copy of the document at `uri` that `peer`
    /// is answered from, at `position`.
    ///
    /// # Specification
    /// - requires: nothing; an unknown URI and any position are admitted.
    /// - ensures: an unknown document yields Nothing; a held document yields
    ///   first the ghost text of each kept proposal whose range holds the
    ///   position, replacing that range, then each ghost text [`ghost()`] ranks
    ///   at the position's byte, best first, its snippet inserted at the empty
    ///   range at `position`; none of those when the grammar did not build.
    /// - provides: the answer to `textDocument/inlineCompletion`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a known document after an open bracket, the same
    ///   document before written text, and an unknown document distinguish the
    ///   ranked items and null through exact wire answers; a cursor inside a
    ///   kept proposal sees it first.
    /// - witness: `server::tests::inline_completion_answers_the_expected_closer`
    /// - witness: `server::tests::kept_proposals_reach_every_editor_surface`
    #[spec(ensures: |ret| match ret {
        Answer::Nothing => !self.documents.contains_key(uri),
        Answer::Inline(ref list) => self.documents.get(uri).is_some_and(|held|
            list.items.len() <= held.view(peer).proposals.len().saturating_add(8))
            && list.items.iter().all(|item| item.range.start <= position && position <= item.range.end),
        Answer::Initialize(_) | Answer::Tokens(_) | Answer::Symbols(_) | Answer::Folds(_) | Answer::Selections(_)
            | Answer::Hover(_) | Answer::Edits(_) | Answer::Lenses(_) | Answer::Actions(_) => false,
    })]
    fn inline(
        &self,
        uri: &DocumentUri,
        peer: Peer,
        position: Position,
    ) -> Answer
    {
        let Maybe::Present(document) = self.view(uri, peer)
        else {
            return Answer::Nothing;
        };
        let text = document.text.source();
        let index = LineIndex::new(text.as_ref().into());
        let at = position.byte(&index);
        let mut items = ghosts(&document.proposals, position);
        if let (Ok(grammar), Ok(forms)) = (grammar(), forms()) {
            items.extend(ghost(grammar, forms, text, at).into_iter().map(|snippet| {
                InlineCompletionItem {
                    insert_text: StringValue {
                        kind: "snippet",
                        value: String::from(snippet),
                    },
                    range: Range {
                        start: position,
                        end: position,
                    },
                }
            }));
        }
        Answer::Inline(InlineCompletionList { items })
    }

    /// What `read` answers over the reading and the text of the copy of the
    /// document at `uri` that `peer` is answered from.
    ///
    /// # Specification
    /// - requires: nothing; an unknown URI is admitted.
    /// - ensures: an unknown document yields Nothing, without calling `read`; a
    ///   held document yields what `read` answers over its text's reading and
    ///   its text.
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
        peer: Peer,
        read: impl FnOnce(&Reading, SourceText<'_>) -> Answer,
    ) -> Answer
    {
        match self.view(uri, peer) {
            Maybe::Present(document) => read(document.text.reading(), document.text.source()),
            Maybe::Absent(_) => Answer::Nothing,
        }
    }

    /// What a hover at `position` of the copy of the document at `uri` that
    /// `peer` is answered from shows, in `style`.
    ///
    /// # Specification
    /// - requires: nothing; an unknown URI and any position are admitted.
    /// - ensures: an unknown document yields Nothing; otherwise the hover
    ///   [`hover()`] shows in `style`, read against the text's reading, what
    ///   the copy keeps for its hovers and its session, followed by the notes
    ///   of the kept proposals whose range holds the position and explain
    ///   themselves, in `style`'s markup, or those notes alone over the first
    ///   one's range when the hover shows nothing there or the grammar did not
    ///   build. Nothing when neither shows anything.
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
        peer: Peer,
        position: Position,
        style: Style,
    ) -> Answer
    {
        let Maybe::Present(document) = self.view(uri, peer)
        else {
            return Answer::Nothing;
        };
        let shown = document.session.as_ref().map_or(
            Maybe::Absent(crate::hover::hovered::Absent::Unparsed),
            |session| {
                hover(
                    document.text.source(),
                    session,
                    document.text.reading(),
                    document.text.hovering(),
                    position,
                    style,
                )
            },
        );
        match (shown, notes(&document.proposals, position, style.markup)) {
            (Maybe::Present(mut shown), Some((_range, notes))) => {
                shown.contents.value.push_str("\n\n---\n\n");
                shown.contents.value.push_str(&notes);
                Answer::Hover(shown)
            },
            (Maybe::Present(shown), None) => Answer::Hover(shown),
            (Maybe::Absent(_), Some((range, notes))) => Answer::Hover(Hover {
                contents: MarkupContent {
                    kind: "markdown",
                    value: notes,
                },
                range,
            }),
            (Maybe::Absent(_), None) => Answer::Nothing,
        }
    }

    /// The answer to a formatting request `id` over `window` of the copy of
    /// the document at `uri` that `peer` is answered from.
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
        Outgoing::Success { .. } | Outgoing::Notification { .. } => false,
    })]
    fn format(
        &self,
        id: RequestId,
        uri: &DocumentUri,
        peer: Peer,
        window: Window,
    ) -> Outgoing
    {
        let Maybe::Present(document) = self.view(uri, peer)
        else {
            return success(id, Answer::Nothing);
        };
        match edits(document.text.source(), window) {
            Ok(edits) => success(id, Answer::Edits(edits)),
            Err(unformatted) => failure(id, ErrorCode::REQUEST_FAILED, unformatted.to_string()),
        }
    }
}

/// `text` with `change` applied, and where the change left the caret.
///
/// # Specification
/// - requires: nothing; any range is admissible input.
/// - ensures: a change naming no range replaces the whole text and leaves no
///   caret; a ranged one replaces the bytes between its two ends, each resolved
///   through the line index of the text as it stands as
///   [`crate::position::Position::byte`] states, an end before the start read
///   as the start, and leaves the caret at the end of the text it inserted.
/// - provides: incremental synchronisation, with full synchronisation as the
///   change that names no range; the caret the quiet publication reads.
/// - fails: never.
/// - panics: none; a resolved end is always a character boundary.
///
/// # Adequacy
/// - hypothesis: L3 — successive ranged changes, one after a character beyond
///   the basic plane, an inverted range, and a rangeless change, each asserted
///   at the exact text it leaves and the caret it leaves.
/// - witness: `server::tests::ranged_changes_edit_the_held_text_in_order`
#[spec(
    captures: [length = text.len(), replaced = change.text.len(), whole = change.range.is_none()],
    ensures: |ret| if whole { text.len() == replaced && matches!(ret, Maybe::Absent(_)) }
        else { replaced <= text.len() && text.len() <= length.saturating_add(replaced)
            && matches!(ret, Maybe::Present(caret) if usize::from(caret) <= text.len()) },
)]
fn apply(
    text: &mut String,
    change: ContentChange,
) -> Maybe<ByteOffset, uncareted::Absent>
{
    let Some(range) = change.range
    else {
        *text = change.text;
        return Maybe::Absent(uncareted::Absent::Unranged);
    };
    let index = LineIndex::new(text.as_str().into());
    let start = usize::from(range.start.byte(&index));
    let end = usize::from(range.end.byte(&index)).max(start);
    text.replace_range(start .. end, &change.text);
    Maybe::Present(ByteOffset::from(start.saturating_add(change.text.len())))
}

/// The settings the `initialize` parameters `params` name in their
/// initialization options, none when they name none or cannot be read.
///
/// # Specification
/// trivial.
fn initial_settings(params: &Value) -> Settings
{
    InitializeParams::deserialize(params)
        .ok()
        .and_then(|params| params.initialization_options)
        .unwrap_or_default()
}

/// The markup the client sending the `initialize` parameters `params` reads
/// a hover in, markdown when they cannot be read.
///
/// # Specification
/// trivial.
fn initial_markup(params: &Value) -> Markup
{
    InitializeParams::deserialize(params)
        .map(|params| params.markup())
        .unwrap_or_default()
}

/// The range of `form`, the form under `document`'s caret in the revision
/// its session judged.
///
/// # Specification
/// trivial.
fn caret_range(
    document: &Document,
    form: Maybe<ByteSpan, formless::Absent>,
) -> Maybe<Range, formless::Absent>
{
    let span = match form {
        Maybe::Present(span) => span,
        Maybe::Absent(reason) => return Maybe::Absent(reason),
    };
    let index = LineIndex::new(document.text.text.as_str().into());
    Range::of_bytes(
        &index,
        gandr_surface_render_remote::ByteOffset::from(usize::from(span.start())),
        gandr_surface_render_remote::ByteOffset::from(usize::from(span.end())),
    )
    .map_or(Maybe::Absent(formless::Absent::Between), Maybe::Present)
}

/// Recheck `document`, open at `uri`, at `verbosity`, holding back for
/// `quiet` the diagnostics of the form under its caret: the notification
/// publishing the rest and the line logging what the recheck cost.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one diagnostic notification naming the supplied URI and held
///   version, with the diagnostics the document's session judges for its whole
///   text, rendered at `verbosity`, less those [`publishable`] holds for the
///   form under the document's caret while `quiet` is not zero; the copy
///   records every judged diagnostic as checked. One log line names the same
///   URI and version, its admission pending when the judgement left one, and
///   whether the publication held any.
/// - provides: the publication shared by open, change and configuration
///   notifications.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — opening and changing the known document, including a
///   refusal and an empty change list, distinguish wrong URI, version and stale
///   text through exact publications and subsequent token streams; typing a
///   declaration distinguishes a held diagnostic from a published one.
/// - witness: `server::tests::synchronisation_publishes_and_close_clears`
/// - witness: `server::tests::ignored_messages_and_empty_changes_preserve_document_text`
/// - witness: `session::session::an_edit_to_a_large_document_rechecks_its_forms`
/// - witness: `server::tests::a_configuration_change_republishes_at_its_verbosity`
/// - witness: `editor::editor::scenarios::typing_a_declaration_holds_its_diagnostics_until_its_terminator`
#[spec(ensures: |ret| ret.flow == Flow::Continue
    && matches!(*ret.messages.as_slice(), [Outgoing::Notification { method: "textDocument/publishDiagnostics", ref params, .. }]
        if params.uri == *uri && params.version == Some(document.version)
            && params.diagnostics.len() <= document.checked.len())
    && matches!(*ret.log.as_slice(), [ref logged] if logged.uri == *uri && logged.version == document.version))]
fn synchronised(
    uri: &DocumentUri,
    document: &mut Document,
    verbosity: Verbosity,
    quiet: Duration,
) -> Outcome
{
    let caret = match document.caret {
        Maybe::Present(caret) if !quiet.is_zero() => Maybe::Present(caret),
        Maybe::Present(_) | Maybe::Absent(_) => Maybe::Absent(formless::Absent::Uncareted),
    };
    let rechecked = recheck(
        uri,
        &mut document.session,
        document.text.source(),
        verbosity,
        caret,
    );
    let form = caret_range(document, rechecked.form);
    let (published, holding) = publishable(&rechecked.diagnostics, &form);
    document.checked = rechecked.diagnostics;
    Outcome {
        messages: vec![publish(PublishParams {
            uri: uri.clone(),
            version: Some(document.version),
            diagnostics: published,
        })],
        log: vec![Logged {
            uri: uri.clone(),
            version: document.version,
            timing: rechecked.timing,
            holding,
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
///   line terminator, before the next frame is read. A synchronisation whose
///   publication held a diagnostic back arms its document's deadline the
///   server's quiet interval later, and one that held nothing disarms it; a
///   deadline that passes with no frame read publishes what the document holds
///   back, as [`Server::release`] states. The session ends at `exit` or at a
///   stream closed at a frame boundary, as [`Server::closed`] states. A line
///   `log` refuses is dropped: the log is the operator's, and the protocol
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
///   one whose stream breaks inside a frame, an editor-shaped edit to a large
///   document whose log carries one timing line per synchronisation, and a held
///   diagnostic published once the document is quiet.
/// - witness: `session::session::a_session_round_trips_over_in_memory_streams`
/// - witness: `session::session::a_stream_closed_without_exit_ends_abruptly`
/// - witness: `session::session::an_edit_to_a_large_document_rechecks_its_forms`
/// - witness: `session::session::a_held_diagnostic_publishes_once_the_document_is_quiet`
#[inline]
pub fn serve<Input, Output, Log>(
    input: &mut Input,
    output: &mut Output,
    log: &mut Log,
) -> Result<Served, TransportFault>
where
    Input: BufRead + Send,
    Output: Write,
    Log: Write,
{
    let mut workspace = Workspace::default();
    let mut server = Server::default();
    paced(input, |met, deadlines| {
        let body = match met {
            Met::Closed => return Ok(ControlFlow::Break(server.closed())),
            Met::Quiet(uri) => {
                for message in &server.release(&mut workspace, &uri) {
                    written(output, message)?;
                }
                return Ok(ControlFlow::Continue(()));
            },
            Met::Frame(body) => body,
        };
        let mut outcome = server.handle(&mut workspace, &body);
        for message in &outcome.messages {
            written(output, message)?;
        }
        for message in &server.admit(&mut workspace, &mut outcome.log) {
            written(output, message)?;
        }
        deadlines.note(&outcome.log, server.quiet(), Instant::now());
        for line in &outcome.log {
            let _unlogged = writeln!(log, "{line}");
        }
        Ok(match outcome.flow {
            Flow::Exit(served) => ControlFlow::Break(served),
            Flow::Continue => ControlFlow::Continue(()),
        })
    })
}

/// Write `message` to `output` as one frame.
///
/// # Specification
/// - requires: nothing of the stream.
/// - ensures: the message's JSON encoding is written as one frame.
/// - fails: [`TransportFault::Encode`] for a message that does not encode, and
///   the stream's fault for a frame it refuses.
/// - panics: none.
/// - executable: none — the stream is opaque.
///
/// # Errors
/// [`TransportFault`], as above.
///
/// # Adequacy
/// - hypothesis: L2 — every frame a served session writes passes here.
/// - witness: `session::session::a_session_round_trips_over_in_memory_streams`
fn written<Output>(
    output: &mut Output,
    message: &Outgoing,
) -> Result<(), TransportFault>
where
    Output: Write,
{
    let encoded = serde_json::to_vec(message).map_err(TransportFault::Encode)?;
    write_frame(output, &Body::from(encoded))
}

#[cfg(test)]
mod tests
{
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
        && ret.workspace.documents.values().all(|held| held.document.text.source().as_ref() == "def f = 42 ;\n"))]
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
        let after_call = ask(&mut server, "file:///tmp/open.gandr", 11);
        assert_eq!(
            after_call.pointer("/0/result/items/0"),
            Some(&wire(Json(
                r#"{"insertText":{"kind":"snippet","value":")"},
                    "range":{"start":{"line":0,"character":11},"end":{"line":0,"character":11}}}"#
            ))),
            "after `f(1` the call's closer is the first ghost text: {after_call}"
        );
        // Text after the cursor on its line is input, never a refusal: the
        // ranked ghost texts are inserted at the cursor.
        let before_text = ask(&mut server, "file:///tmp/open.gandr", 5);
        let items = before_text
            .pointer("/0/result/items")
            .and_then(Value::as_array)
            .expect("a held document answers a list");
        assert!(
            (1 ..= 8).contains(&items.len())
                && items.iter().all(|item| {
                    item.pointer("/range")
                        == Some(&wire(Json(
                            r#"{"start":{"line":0,"character":5},"end":{"line":0,"character":5}}"#,
                        )))
                }),
            "text after the cursor on its line: ghost texts at the cursor: {before_text}"
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
            wire(Json(
                r#"[{"jsonrpc":"2.0","id":5,"result":{
                    "contents":{"kind":"markdown","value":"```gandr\nf : Integer\n```"},
                    "range":{"start":{"line":0,"character":0},"end":{"line":0,"character":12}}}}]"#
            )),
            "on the keyword: the declaration it introduces, about the declaration"
        );
        assert_eq!(
            ask(&mut server, "file:///tmp/example.gandr", 8),
            wire(Json(
                r#"[{"jsonrpc":"2.0","id":5,"result":{
                    "contents":{"kind":"markdown","value":"```gandr\nInteger\n```"},
                    "range":{"start":{"line":0,"character":8},"end":{"line":0,"character":10}}}}]"#
            )),
            "on the literal: its type, about the literal"
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
    fn a_configuration_change_reanswers_hovers_in_its_form()
    {
        let mut server = Connected::default();
        let _answered = send(
            &mut server,
            Json(
                r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"capabilities":{},
                    "initializationOptions":{"presentation":{"form":"explicit"}}}}"#,
            ),
        );
        let _opened = send(
            &mut server,
            Json(
                r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{
                    "uri":"file:///tmp/f.gandr","languageId":"gandr","version":1,
                    "text":"def f(x: Integer) -> -F Integer { return x }\n"}}}"#,
            ),
        );
        let hovered = |server: &mut Connected| {
            send(
                server,
                Json(
                    r#"{"jsonrpc":"2.0","id":5,"method":"textDocument/hover","params":{
                        "textDocument":{"uri":"file:///tmp/f.gandr"},
                        "position":{"line":0,"character":4}}}"#,
                ),
            )
            .pointer("/0/result/contents/value")
            .and_then(Value::as_str)
            .map(str::to_owned)
        };
        let configure = |form: &str| {
            Body::from(
                format!(
                    r#"{{"jsonrpc":"2.0","method":"workspace/didChangeConfiguration",
                        "params":{{"settings":{{"gandr":{{"presentation":{{"form":{form}}}}}}}}}}}"#
                )
                .into_bytes(),
            )
        };
        let explicit = Some(String::from(
            "```gandr\nf : +U (Integer -> -F Integer)\n```",
        ));
        let sugared = Some(String::from("```gandr\nf : Integer => Integer\n```"));
        assert_eq!(
            hovered(&mut server),
            explicit,
            "the initialization options choose the form"
        );
        assert!(
            server
                .handle(&configure(r#""sugared""#))
                .messages
                .is_empty(),
            "a form republishes nothing"
        );
        assert_eq!(
            hovered(&mut server),
            sugared,
            "the next hover answers in the form configured"
        );
        for (unchanged, why) in [
            (configure(r#""loose""#), "a value that names no form"),
            (configure("null"), "a section that names none"),
        ] {
            let _ignored = server.handle(&unchanged);
            assert_eq!(hovered(&mut server), sugared, "{why} keeps the form held");
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
                .map(|held| String::from(held.document.text.source().as_ref()))
                .expect("the document is open")
        };
        let caret = |server: &Connected| {
            server
                .workspace
                .documents
                .get(&uri)
                .map(|held| held.document.caret)
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
        assert_eq!(
            caret(&server),
            super::Maybe::Present(gandr_surface_syntax::ByteOffset::from(11_usize)),
            "the caret is where the last change's text ends: after its `!`"
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
            caret(&server),
            super::Maybe::Absent(super::uncareted::Absent::Unranged),
            "a rangeless change leaves no caret"
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

    /// Two running connections, numbered 1 and 2, over one workspace.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: both connections are running and no document is open.
    /// - provides: the fixture the shared-workspace witnesses start from.
    /// - fails: never.
    /// - panics: an unanswered `initialize` fails the witness.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the witnesses' first publications distinguish a
    ///   connection left waiting.
    /// - witness: `server::tests::two_connections_hold_their_own_copies`
    #[spec(ensures: |ret| ret.0.documents.is_empty()
        && ret.1.iter().all(|connection| connection.phase == super::Phase::Running))]
    fn two_connections() -> (Workspace, [Server; 2])
    {
        let mut workspace = Workspace::default();
        let initialize =
            Body::from(br#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#.to_vec());
        let connections = [1_u64, 2_u64].map(|number| {
            let mut server = Server::new(Peer::from(number));
            assert_eq!(server.handle(&mut workspace, &initialize).messages.len(), 1);
            server
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

    /// What a hover at the first line's fifth character of
    /// `file:///tmp/shared.gandr` shows `server`, `null` when nothing.
    ///
    /// # Specification
    /// trivial.
    fn hovered(
        server: &mut Server,
        workspace: &mut Workspace,
    ) -> Value
    {
        let hover = Body::from(
            br#"{"jsonrpc":"2.0","id":5,"method":"textDocument/hover","params":{
                "textDocument":{"uri":"file:///tmp/shared.gandr"},"position":{"line":0,"character":4}}}"#
                .to_vec(),
        );
        serde_json::to_value(&server.handle(workspace, &hover).messages)
            .expect("a message encodes")
            .pointer("/0/result/contents/value")
            .cloned()
            .unwrap_or(Value::Null)
    }

    #[test]
    fn two_connections_hold_their_own_copies()
    {
        let (mut workspace, [mut first, mut second]) = two_connections();
        let uri = crate::protocol::DocumentUri::from("file:///tmp/shared.gandr");
        let open = shared(
            Json("textDocument/didOpen"),
            Json(r#","version":1,"text":"def f = 42 ;\n"}"#),
        );
        let insert = |version: Json<'_>, character: Json<'_>, text: Json<'_>| {
            let (Json(version), Json(character), Json(text)) = (version, character, text);
            shared(
                Json("textDocument/didChange"),
                Json(&format!(
                    r#","version":{version}}},"contentChanges":[{{"range":{{"start":{{"line":0,"character":{character}}},"end":{{"line":0,"character":{character}}}}},"text":"{text}"}}]"#
                )),
            )
        };
        let shown = |name: Json<'_>| {
            let Json(name) = name;
            serde_json::json!(format!("```gandr\n{name} : Integer\n```"))
        };
        assert_eq!(first.handle(&mut workspace, &open).messages.len(), 1);
        assert_eq!(
            second.handle(&mut workspace, &open).messages.len(),
            1,
            "the second opener hears the publication of its own copy"
        );
        let renamed = insert(Json("2"), Json("5"), Json("g"));
        let changed = first.handle(&mut workspace, &renamed);
        assert_eq!(
            changed.messages.len(),
            1,
            "a change publishes to its connection alone"
        );
        assert_eq!(hovered(&mut first, &mut workspace), shown(Json("fg")));
        assert_eq!(
            hovered(&mut second, &mut workspace),
            shown(Json("f")),
            "the second connection is answered for the text it holds"
        );
        drop(second.handle(&mut workspace, &renamed));
        assert_eq!(
            hovered(&mut second, &mut workspace),
            shown(Json("fg")),
            "one edit sent by both connections applies once to each copy"
        );
        drop(second.handle(&mut workspace, &insert(Json("3"), Json("6"), Json("h"))));
        assert_eq!(
            workspace
                .published(&uri)
                .map(|(version, _)| version.to_string()),
            Some("3".to_owned()),
            "the other faces read the copy that synchronised last"
        );
        assert_eq!(hovered(&mut first, &mut workspace), shown(Json("fg")));
        let close = shared(Json("textDocument/didClose"), Json("}"));
        assert_eq!(
            first.handle(&mut workspace, &close).messages.len(),
            1,
            "the closer hears its clearing"
        );
        assert_eq!(
            hovered(&mut first, &mut workspace),
            shown(Json("fgh")),
            "a connection holding no copy is answered from the latest"
        );
        drop(second.handle(&mut workspace, &close));
        assert!(workspace.documents.is_empty(), "the last close forgets it");
    }

    #[test]
    fn a_departing_connection_leaves_the_others_served()
    {
        let (mut workspace, [mut first, mut second]) = two_connections();
        let open = Json(r#","version":1,"text":"def f = 42 ;\n"}"#);
        drop(first.handle(&mut workspace, &shared(Json("textDocument/didOpen"), open)));
        drop(second.handle(&mut workspace, &shared(Json("textDocument/didOpen"), open)));
        workspace.depart(Peer::from(1_u64));
        assert_eq!(
            workspace.documents.len(),
            1,
            "the second connection still holds it"
        );
        let change = shared(
            Json("textDocument/didChange"),
            Json(r#","version":2},"contentChanges":[{"text":"def g = 1 ;\n"}]"#),
        );
        assert!(
            first.handle(&mut workspace, &change).messages.is_empty(),
            "a departed connection's change touches nothing"
        );
        assert_eq!(
            second.handle(&mut workspace, &change).messages.len(),
            1,
            "the one left is still served"
        );
        workspace.depart(Peer::from(2_u64));
        assert!(
            workspace.documents.is_empty(),
            "a document no connection holds is forgotten"
        );
        workspace.depart(Peer::from(3_u64));
        assert!(
            workspace.documents.is_empty(),
            "a stranger's departure changes nothing"
        );
    }

    #[test]
    fn a_workspace_answers_queries_off_its_documents()
    {
        let (mut workspace, [mut first, _second]) = two_connections();
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
        let (mut workspace, [mut first, _second]) = two_connections();
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
                .map(|held| <&str>::from(held.document.text.source())),
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
        let (mut workspace, [mut first, _second]) = two_connections();
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
                .map(|held| held.document.version)
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
                .map(|held| held.document.proposals.clone())
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
        let (mut workspace, [mut first, _second]) = two_connections();
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
            .map(|held| held.document.version)
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
