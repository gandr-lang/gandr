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
use alloc::collections::BTreeSet;
use core::cell::OnceCell;
use core::cell::RefCell;
use core::convert::Infallible;
use core::fmt;
use core::ops::ControlFlow;
use core::time::Duration;
use std::io::BufRead;
use std::io::Write;
use std::path::Path;
use std::path::PathBuf;
use std::sync::mpsc::Sender;
use std::time::Instant;

use anodized::spec;
use gandr_surface_diagnostics::Verbosity;
use gandr_surface_dispatcher::Shadows;
use gandr_surface_dispatcher::imports_named;
use gandr_surface_dispatcher::named_path;
use gandr_surface_pretty::Form;
use gandr_surface_pretty::Spelling;
use gandr_surface_render_remote::DocId;
use gandr_surface_render_remote::LineIndex;
use gandr_surface_render_remote::RenderFrame;
use gandr_surface_session::Session;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;
use serde::Deserialize as _;
use serde_json::Value;

use crate::complete::completions;
use crate::complete::resolved;
use crate::files::Files;
use crate::fix::repairs;
use crate::format::Scope;
use crate::format::edits;
use crate::goto::Goto;
use crate::goto::targets;
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
use crate::proposal::applied;
use crate::proposal::check;
use crate::proposal::ghosts;
use crate::proposal::lenses;
use crate::proposal::notes;
use crate::proposal::settles;
use crate::protocol::APPLY_FILL;
use crate::protocol::Answer;
use crate::protocol::AppliedEdit;
use crate::protocol::AppliesEdits;
use crate::protocol::ApplyEditParams;
use crate::protocol::CancelProgressParams;
use crate::protocol::ChoiceParams;
use crate::protocol::CodeAction;
use crate::protocol::CodeActionParams;
use crate::protocol::CodeLens;
use crate::protocol::Command;
use crate::protocol::CompletionItem;
use crate::protocol::ConfigurationParams;
use crate::protocol::ContentChange;
use crate::protocol::ContentParams;
use crate::protocol::ContentResult;
use crate::protocol::DeltaParams;
use crate::protocol::Diagnostic;
use crate::protocol::DidChangeParams;
use crate::protocol::DidOpenParams;
use crate::protocol::DocumentParams;
use crate::protocol::DocumentUri;
use crate::protocol::DocumentVersion;
use crate::protocol::EditsShaped;
use crate::protocol::ExecuteCommandParams;
use crate::protocol::FORM_CLOSER;
use crate::protocol::FileEvent;
use crate::protocol::FileRename;
use crate::protocol::FilesParams;
use crate::protocol::FoldersChangedParams;
use crate::protocol::FoldsCollapsed;
use crate::protocol::Hover;
use crate::protocol::ImportFilesParams;
use crate::protocol::InitializeParams;
use crate::protocol::InitializeResult;
use crate::protocol::InlineCompletionItem;
use crate::protocol::InlineCompletionList;
use crate::protocol::LabelOffsets;
use crate::protocol::LabelsDetailed;
use crate::protocol::LensData;
use crate::protocol::LensResolution;
use crate::protocol::Linked;
use crate::protocol::ListsFolders;
use crate::protocol::Location;
use crate::protocol::MarkupContent;
use crate::protocol::MessageAction;
use crate::protocol::MessageParams;
use crate::protocol::MessageType;
use crate::protocol::PositionParams;
use crate::protocol::ProgressToken;
use crate::protocol::PublishParams;
use crate::protocol::PullsConfiguration;
use crate::protocol::RangeParams;
use crate::protocol::RangesParams;
use crate::protocol::ReferenceContext;
use crate::protocol::ReferenceParams;
use crate::protocol::Refreshing;
use crate::protocol::RegistrationParams;
use crate::protocol::RenameFilesParams;
use crate::protocol::RenameParams;
use crate::protocol::SHOW_REFERENCES;
use crate::protocol::Sections;
use crate::protocol::SelectionRangeParams;
use crate::protocol::SemanticTokens;
use crate::protocol::SemanticTokensDelta;
use crate::protocol::SetTraceParams;
use crate::protocol::Settings;
use crate::protocol::Severity;
use crate::protocol::ShowDocumentParams;
use crate::protocol::ShowsDocuments;
use crate::protocol::ShowsProgress;
use crate::protocol::StringValue;
use crate::protocol::SymbolInformation;
use crate::protocol::TakesSnippets;
use crate::protocol::TextEdit;
use crate::protocol::Trace;
use crate::protocol::TraceParams;
use crate::protocol::TypedParams;
use crate::protocol::UnregistrationParams;
use crate::protocol::Unresolved;
use crate::protocol::ViewsContent;
use crate::protocol::WatchedFilesParams;
use crate::protocol::WatchesFiles;
use crate::protocol::WorkTitle;
use crate::protocol::WorkspaceEdit;
use crate::protocol::WorkspaceFolder;
use crate::protocol::WorkspaceSymbolParams;
use crate::protocol::folder_roots;
use crate::quiet::Changes;
use crate::quiet::Holding;
use crate::quiet::Inbox;
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
use crate::recheck::trial;
use crate::relocate::Moves;
use crate::rename::NewName;
use crate::rename::Unrenamed;
use crate::rename::prepared;
use crate::rename::sites;
use crate::rename::spliced;
use crate::rename::text_edits;
use crate::rpc::Answered;
use crate::rpc::Classified;
use crate::rpc::ErrorCode;
use crate::rpc::Incoming;
use crate::rpc::Method;
use crate::rpc::Notified;
use crate::rpc::Outgoing;
use crate::rpc::Refreshed;
use crate::rpc::RequestId;
use crate::rpc::Requests;
use crate::rpc::Told;
use crate::rpc::Withdrawn;
use crate::rpc::apply_edit;
use crate::rpc::choose;
use crate::rpc::classify;
use crate::rpc::failure;
use crate::rpc::list_folders;
use crate::rpc::progress_begun;
use crate::rpc::progress_ended;
use crate::rpc::publish;
use crate::rpc::pull;
use crate::rpc::refresh;
use crate::rpc::refresh_content;
use crate::rpc::register;
use crate::rpc::show;
use crate::rpc::success;
use crate::rpc::tell;
use crate::rpc::trace;
use crate::rpc::unregister;
use crate::search::FOUND_HELD;
use crate::signature::help;
use crate::syntax::printed;
use crate::tokens::Resolved;
use crate::tokens::ResultId;
use crate::tokens::TokenStream;
use crate::tokens::classified;
use crate::tokens::encode;
use crate::tokens::overlapping;
use crate::transport::Body;
use crate::transport::TransportFault;
use crate::transport::write_frame;
use crate::uses::Written;
use crate::uses::declared;
use crate::uses::highlights;
use crate::uses::located;
use crate::uses::mirrored;
use crate::uses::placed;
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

/// What a token request asks about.
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

/// Where a change to a file was made.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Origin
{
    /// On disk: a file an editor holds reads as the editor's copy, so the
    /// change is not read.
    Disk,
    /// In an editor's copy.
    Editor,
}

/// Which of a connection's copies a recheck picks.
#[derive(Clone, Copy, Debug)]
enum Picks<'changed>
{
    /// Every copy.
    Every,
    /// Those whose closures, at their last judgement, named a file of these,
    /// sorted, changed where the origin says.
    Naming(&'changed [PathBuf], Origin),
    /// Those whose closures named this file, changed in an editor's copy.
    File(&'changed Path),
    /// Those whose closures, at their last judgement, named a file of these
    /// or under a folder of these, created, deleted or renamed on disk.
    Under(&'changed [PathBuf]),
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
    /// Every path its closure's imports named at its last judgement, as
    /// `lay_out` names them, sorted: a change to one of those files changes
    /// the judgement.
    named: Vec<PathBuf>,
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
            named: Vec::new(),
            published: Vec::new(),
            proposals: Vec::new(),
        }
    }
}

/// A copy's text and, once a request has asked, the one [`Reading`] of it, its
/// printed syntax tree and the [`Hovering`] its hovers read.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a reading, a printed tree or a hover table, once made, is of the
///   text as it stands: every change to the text drops all three.
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
/// - witness: `tests::editor::scenarios::sweeps::random_edits_keep_every_answer_faithful`
/// - witness: `tests::editor::scenarios::sweeps::typing_each_corpus_source_keeps_every_answer_faithful`
struct HeldText
{
    /// The text.
    text: String,
    /// The reading of `text`, made by the first request that asks.
    reading: OnceCell<Reading>,
    /// The syntax tree of `text`, printed by the first request that asks.
    tree: OnceCell<ContentResult>,
    /// The type table of `text`, made by the first request that reads it after
    /// the text changed.
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
            tree: OnceCell::new(),
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
        self.tree = OnceCell::new();
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
        self.tree = OnceCell::new();
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

    /// The syntax tree of the text held, printed now when no request has
    /// asked since it last changed.
    ///
    /// # Specification
    /// trivial.
    fn tree(&self) -> &ContentResult
    {
        self.tree.get_or_init(|| ContentResult {
            text: printed(self.source()),
        })
    }

    /// What the hovers of the text held, the document at `path` that `session`
    /// judges, read, each import of its closure read as `shadows` holds it,
    /// made now when no hover has asked since it or its closure last changed.
    ///
    /// # Specification
    /// trivial.
    fn hovering<Store, Blocks>(
        &self,
        path: &Path,
        session: &Session<Store, Blocks>,
        shadows: &dyn Shadows,
    ) -> &Hovering
    {
        self.hovering
            .get_or_init(|| hovering(self.source(), path, session, shadows))
    }

    /// Drop what the hovers read off the text's closure, whose imports
    /// changed.
    ///
    /// # Specification
    /// trivial.
    fn reclose(&mut self)
    {
        self.hovering = OnceCell::new();
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
    /// The path an import names its file by, as [`named_path`] names it.
    path: PathBuf,
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
                path: self.path,
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
    /// - witness: `tests::session::an_edit_to_a_large_document_rechecks_its_forms`
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

/// The progress reported around the work one message starts: the messages
/// written before it is handled, and those written once its admissions ran.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Reported
{
    /// Written before the message is handled.
    pub begin: Vec<Outgoing>,
    /// Written once its admissions ran.
    pub end: Vec<Outgoing>,
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
/// An editor's copy shadows the disk for every face. An import of a document
/// some connection holds reads the copy the importing connection is answered
/// from — its own, or the latest when it holds none — and never the file at
/// its path; a change to a held file on disk changes no judgement. A change to
/// a copy rechecks every copy, on every connection, whose closure names its
/// file at its last judgement.
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
    /// The URI of each open document, by the path an import names its file
    /// by.
    paths: BTreeMap<PathBuf, DocumentUri>,
    /// Where each connection on a hub hears which held files another
    /// connection's editor changed.
    editors: BTreeMap<Peer, Changes>,
    /// Where each watching connection hears which document changed.
    watchers: BTreeMap<Peer, Sender<DocumentUri>>,
    /// The spelling its user's configuration names: what a connection writes
    /// types in until its editor's `gandr.presentation.spelling` says
    /// otherwise, and what a query writes them in.
    spelling: Spelling,
    /// Every source under the folders the connections opened, with the files
    /// each imports: where a reference or rename request finds the importers
    /// no editor holds. A cache the answers refresh, so it changes under a
    /// shared borrow.
    files: RefCell<Files>,
}

/// The copies the editors hold, read by an import in place of the file at
/// its path: `peer`'s own copy of each document, or the latest when it holds
/// none.
struct Shadowing<'held>
{
    /// The documents held, those out of the map being judged aside.
    held: &'held BTreeMap<DocumentUri, Held>,
    /// The documents a pass over the workspace has yet to come to.
    pending: Option<&'held BTreeMap<DocumentUri, Held>>,
    /// The URI of each open document, by the path an import names its file
    /// by.
    paths: &'held BTreeMap<PathBuf, DocumentUri>,
    /// The connection whose imports read.
    peer: Peer,
}

impl Shadows for Shadowing<'_>
{
    /// The text of `peer`'s view of the document held at `named`, if any.
    ///
    /// # Specification
    /// trivial.
    fn shadowed(
        &self,
        named: &Path,
    ) -> Option<SourceText<'_>>
    {
        let uri = self.paths.get(named)?;
        let held = self.held.get(uri).or_else(|| self.pending?.get(uri))?;
        Some(held.view(self.peer).text.source())
    }
}

/// A document a reference or rename request reads: its URI, its canonical
/// path, its text and what its hovers read.
struct Writer<'read>
{
    /// Its URI.
    uri: &'read DocumentUri,
    /// Its canonical path.
    path: &'read Path,
    /// Its text.
    text: SourceText<'read>,
    /// What its hovers read, its type table among it.
    hovering: &'read Hovering,
}

impl Workspace
{
    /// A workspace holding nothing, its user's configuration naming
    /// `spelling`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn spelled(spelling: Spelling) -> Self
    {
        Self {
            spelling,
            ..Self::default()
        }
    }
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

    /// Admit `peer`, a hub connection, as an editor: the paths of the held
    /// files another connection's editor changed, which `peer`'s copies'
    /// closures name, go to `changes`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn hear_edits(
        &mut self,
        peer: Peer,
        changes: Changes,
    )
    {
        let _prior = self.editors.insert(peer, changes);
    }

    /// The copies the editors hold, as `peer`'s imports read them.
    ///
    /// # Specification
    /// trivial.
    fn shadowing(
        &self,
        peer: Peer,
    ) -> Shadowing<'_>
    {
        Shadowing {
            held: &self.documents,
            pending: None,
            paths: &self.paths,
            peer,
        }
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

    /// The version of the copy `peer` holds of the document at `uri`, none
    /// when it holds none.
    ///
    /// # Specification
    /// trivial.
    fn held_by(
        &self,
        uri: &DocumentUri,
        peer: Peer,
    ) -> Option<DocumentVersion>
    {
        match self.documents.get(uri).map(|held| held.own(peer)) {
            Some(Maybe::Present(document)) => Some(document.version),
            Some(Maybe::Absent(_)) | None => None,
        }
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
        let held = self.documents.get(uri)?;
        let document = &held.document;
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
            crate::recheck::trial(
                uri,
                &document.session,
                &candidates,
                &self.shadowing(held.latest),
            ),
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
    ///   published diagnostics is kept beside it, after those kept before, its
    ///   trial's diagnostics answered, and the connection holding that copy
    ///   told, so its client may ask for its code lenses again; one that does
    ///   not is refused with them. Every copy's text, session and published
    ///   diagnostics are unchanged.
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
    ///   refused, the connection holding the document hears of the kept fill
    ///   once and of no refused one, and the next edit withdraws what was kept.
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
        let holding = self
            .documents
            .get_mut(uri)
            .ok_or(ProposalRefusal::NotHeld)?;
        let diagnostics = check(tried, &holding.document.published)?;
        holding.document.proposals.push(Proposal {
            settles: settles(&diagnostics),
            ..proposal
        });
        if let Some(changes) = self.editors.get(&holding.latest) {
            changes.proposed();
        }
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
            style: Style {
                spelling: self.spelling,
                ..STYLE
            },
            linked: Linked(true),
            offsets: LabelOffsets(true),
            detailing: LabelsDetailed(true),
            snipping: TakesSnippets(true),
            collapsing: FoldsCollapsed(true),
            watching: WatchesFiles(false),
            progress: ShowsProgress(false),
            reported: 0_u64,
            refreshing: Refreshing::NONE,
            sent: Requests(0_u64),
            cancelled: Vec::new(),
            trace: Trace::Off,
            pulling: PullsConfiguration(false),
            applying: AppliesEdits(false),
            editing: EditsShaped::BY_URI,
            showing: ShowsDocuments(false),
            listing: ListsFolders(false),
            viewer: ViewsContent(false),
            announced: BTreeMap::new(),
            offered: Vec::new(),
            choices: Vec::new(),
            streams: BTreeMap::new(),
            viewing: BTreeSet::new(),
        };
        let answer = match classify(request) {
            Err(malformed) => malformed.response(),
            Ok(Incoming::Request { id, method, params }) => {
                reader.request(self, id, &method, params)
            },
            Ok(Incoming::Notification { .. } | Incoming::Response { .. }) => return Value::Null,
        };
        serde_json::to_value(answer).unwrap_or(Value::Null)
    }

    /// Let `peer` go: it holds no copy any more and watches nothing, and a
    /// document no other connection holds is forgotten with its sessions; every
    /// other connection whose copies' closures name a forgotten document's
    /// file hears it changed.
    ///
    /// # Specification
    /// - requires: nothing; a peer that never connected or held nothing is
    ///   admitted.
    /// - ensures: `peer` watches and hears nothing, holds no copy of any
    ///   document and holds no folder open; every document left is held by
    ///   another connection.
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
    #[spec(ensures: !self.watchers.contains_key(&peer) && !self.editors.contains_key(&peer)
        && self.documents.values().all(|held| matches!(held.own(peer), Maybe::Absent(_))))]
    #[inline]
    pub fn depart(
        &mut self,
        peer: Peer,
    )
    {
        let _watcher = self.watchers.remove(&peer);
        let _editor = self.editors.remove(&peer);
        self.files.get_mut().depart(peer);
        for (uri, held) in core::mem::take(&mut self.documents) {
            if let Some(forgotten) = self.let_go(uri, held, peer) {
                self.edited(&forgotten, peer);
            }
        }
    }

    /// `path`, owned, when some copy's closure, at its last judgement, named
    /// it.
    ///
    /// # Specification
    /// trivial.
    fn named(
        &self,
        path: &Path,
    ) -> Option<PathBuf>
    {
        self.documents
            .values()
            .flat_map(|held| core::iter::once(&held.document).chain(held.others.values()))
            .any(|document| {
                document
                    .named
                    .binary_search_by(|named| named.as_path().cmp(path))
                    .is_ok()
            })
            .then(|| path.to_path_buf())
    }

    /// Tell every connection but `by` whose copies' closures name `path` that
    /// the text an import of it reads changed.
    ///
    /// # Specification
    /// trivial.
    fn edited(
        &self,
        path: &Path,
        by: Peer,
    )
    {
        for (&peer, changes) in &self.editors {
            let names = peer != by
                && self.documents.values().any(|held| {
                    matches!(held.own(peer), Maybe::Present(document)
                        if document.named.binary_search_by(|named| named.as_path().cmp(path)).is_ok())
                });
            if names {
                changes.edited(Vec::from([path.to_path_buf()]));
            }
        }
    }

    /// Keep `held`, the document at `uri`, without `peer`'s copy, forgetting
    /// it when that copy was the last, and tell every watcher when the copy
    /// let go was the latest; the path a forgotten document's file is named
    /// by.
    ///
    /// # Specification
    /// trivial.
    fn let_go(
        &mut self,
        uri: DocumentUri,
        held: Held,
        peer: Peer,
    ) -> Option<PathBuf>
    {
        if held.latest == peer {
            for watcher in self.watchers.values() {
                let _gone = watcher.send(uri.clone());
            }
        }
        if held.latest == peer && held.others.is_empty() {
            let _forgotten = self.paths.remove(&held.path);
            return Some(held.path);
        }
        if let Maybe::Present(held) = held.release(peer) {
            let _kept = self.documents.insert(uri, held);
        }
        None
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
        let Outgoing::Notification {
            params: Notified::Published(ref params),
            ..
        } = *message
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
/// the caret waits, how its hovers spell types and are written, whether its
/// client takes a definition as links, whether it takes a signature's
/// parameters as their places in the label, whether it watches files,
/// whether it shows progress, with how many pieces of work it was shown, and
/// whether it requests its code lenses again when asked, with how many times
/// it was asked.
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
    /// The form and spelling its editor's `gandr.presentation` settings name,
    /// read as the verbosity is, the spelling its workspace's configuration
    /// names when the editor names none, and the markup its client's markdown
    /// renderer reads, read at `initialize`.
    style: Style,
    /// Whether its client takes a definition as links, read at `initialize`.
    linked: Linked,
    /// Whether its client takes a signature's parameters as their places in
    /// the label, read at `initialize`.
    offsets: LabelOffsets,
    /// Whether its client shows a completion's label details, read at
    /// `initialize`.
    detailing: LabelsDetailed,
    /// Whether its client takes a completion's text as a snippet, read at
    /// `initialize`.
    snipping: TakesSnippets,
    /// Whether its client shows the text a fold names, read at `initialize`.
    collapsing: FoldsCollapsed,
    /// Whether its client watches files for it once asked, read at
    /// `initialize`.
    watching: WatchesFiles,
    /// Whether its client shows the progress of work the server starts, read
    /// at `initialize`.
    progress: ShowsProgress,
    /// How many pieces of work its progress was reported for; the next one's
    /// token is numbered after them.
    reported: u64,
    /// Which answers its client requests again when asked, read at
    /// `initialize`.
    refreshing: Refreshing,
    /// How many numbered requests of its own it sent its client; the next is
    /// numbered after them.
    sent: Requests,
    /// The tokens of the work this connection reported progress for that its
    /// client asked to cancel, in the order it asked.
    cancelled: Vec<ProgressToken>,
    /// How much of its exchanges its client has it trace, read at
    /// `initialize` and at each `$/setTrace`.
    trace: Trace,
    /// Whether its client answers a pull of its settings, read at
    /// `initialize`.
    pulling: PullsConfiguration,
    /// Whether its client applies an edit the server asks it to, read at
    /// `initialize`: a lens over one checked fill then runs the command
    /// applying it.
    applying: AppliesEdits,
    /// How its client takes a workspace edit, read at `initialize`: every
    /// edit the server sends it is shaped so.
    editing: EditsShaped,
    /// Whether its client shows a document the server asks it to, read at
    /// `initialize`: a fill kept elsewhere is then offered to its user.
    showing: ShowsDocuments,
    /// Whether its client answers a request for its workspace folders, read
    /// at `initialize`: a folder change that does not read then asks for
    /// them whole.
    listing: ListsFolders,
    /// Whether its client shows the text of a virtual document, read at
    /// `initialize`: the syntax trees it asks for are then recorded, and asked
    /// of it again after each change.
    viewer: ViewsContent,
    /// For each document it holds whose kept fills its user was offered, the
    /// version its copy was at: a fill is withdrawn only by an edit, so a
    /// fill kept at a later version is offered again.
    announced: BTreeMap<DocumentUri, DocumentVersion>,
    /// Each offer to show a kept fill, by the choice that put it, with the
    /// document and the fill's range.
    offered: Vec<(RequestId, DocumentUri, Range)>,
    /// Each choice this connection put to its user, by the request that put
    /// it, with the answer once read.
    choices: Vec<(RequestId, Choice)>,
    /// The last full token stream this connection sent for each document,
    /// with the id it sent it under: what a delta request is answered against.
    /// A document's entry goes when the connection closes it.
    streams: BTreeMap<DocumentUri, (ResultId, TokenStream)>,
    /// Each document whose syntax tree its client asked for, with the URI it
    /// asked under, when the client requests a virtual document's text again
    /// when asked: a change of the document asks it for the tree again, and the
    /// entry goes when the connection closes the document.
    viewing: BTreeSet<(DocumentUri, DocumentUri)>,
}

/// Where a choice put to the user stands.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Choice
{
    /// Not yet answered.
    Pending,
    /// Dismissed, or answered with an error.
    Dismissed,
    /// Answered with this choice.
    Chose(MessageAction),
}

/// Whether a client asked to cancel the work under a progress token.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Cancelled(pub bool);

/// The style a connection hovers in until `initialize` says otherwise: the
/// sugared form, in Unicode, in markdown.
const STYLE: Style = Style {
    form: Form::Sugared,
    spelling: Spelling::Unicode,
    markup: Markup::Markdown,
};

/// The action an offer to see a fill kept elsewhere puts to the user.
const SHOW_FILL: &str = "Show";

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
            linked: Linked(false),
            offsets: LabelOffsets(false),
            detailing: LabelsDetailed(false),
            snipping: TakesSnippets(false),
            collapsing: FoldsCollapsed(false),
            watching: WatchesFiles(false),
            progress: ShowsProgress(false),
            reported: 0_u64,
            refreshing: Refreshing::NONE,
            sent: Requests(0_u64),
            cancelled: Vec::new(),
            trace: Trace::Off,
            pulling: PullsConfiguration(false),
            applying: AppliesEdits(false),
            editing: EditsShaped::BY_URI,
            showing: ShowsDocuments(false),
            listing: ListsFolders(false),
            viewer: ViewsContent(false),
            announced: BTreeMap::new(),
            offered: Vec::new(),
            choices: Vec::new(),
            streams: BTreeMap::new(),
            viewing: BTreeSet::new(),
        }
    }

    /// The requests owed this connection's client once another connection
    /// kept a fill of a document it holds: its code lenses asked for again,
    /// then its user offered to see each such document's newest fill.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: nothing when the connection is not running; otherwise a
    ///   `workspace/codeLens/refresh` when its client requests lenses again
    ///   when asked, then, when its client shows a document the server asks it
    ///   to, one `window/showMessageRequest` with the one action [`SHOW_FILL`]
    ///   for each document whose latest copy it holds and keeps a fill, and
    ///   whose user this connection did not yet offer a fill at that copy's
    ///   version: the offer recorded with the newest kept fill's range, which a
    ///   later answer choosing the action shows.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a first kept fill offered, a second kept beside it
    ///   not offered, one kept after the next edit withdrew both offered again,
    ///   and a client that shows no document, a client that refreshes no lens
    ///   and one not yet initialised, each asserted at its exact messages.
    /// - witness: `server::tests::a_refreshing_client_is_asked_for_its_lenses_once_a_fill_is_kept_elsewhere`
    /// - witness: `server::tests::a_fill_kept_elsewhere_is_offered_to_its_editor_once`
    #[spec(ensures: |ret| self.phase == Phase::Running || ret.is_empty())]
    #[inline]
    pub fn proposed_elsewhere(
        &mut self,
        workspace: &Workspace,
    ) -> Vec<Outgoing>
    {
        if self.phase != Phase::Running {
            return Vec::new();
        }
        let mut asked = Vec::new();
        if self.refreshing.lenses {
            asked.push(self.asked(Refreshed::Lenses));
        }
        if self.showing.0 {
            asked.extend(
                workspace
                    .proposed_to(self.peer)
                    .filter_map(|(uri, version, kept)| {
                        self.offer(uri, version, kept.last()?.range)
                    }),
            );
        }
        asked
    }

    /// The choice offering this connection's user to see the fill of `range`
    /// kept for the document at `uri`, at `version`, recorded as offered;
    /// none when its user was already offered a fill at that version.
    ///
    /// # Specification
    /// trivial.
    fn offer(
        &mut self,
        uri: &DocumentUri,
        version: DocumentVersion,
        range: Range,
    ) -> Option<Outgoing>
    {
        if self.announced.get(uri) == Some(&version) {
            return None;
        }
        let named = uri.path();
        let asked = self.ask(ChoiceParams {
            kind: MessageType::INFO,
            message: format!(
                "A model proposed a checked fill for {}.",
                named.file_name().map_or_else(
                    || named.display().to_string(),
                    |file| file.to_string_lossy().into_owned()
                )
            ),
            actions: Vec::from([MessageAction {
                title: String::from(SHOW_FILL),
            }]),
        });
        if let Outgoing::Request { ref id, .. } = asked {
            self.offered.push((id.clone(), uri.clone(), range));
        }
        let _replaced = self.announced.insert(uri.clone(), version);
        Some(asked)
    }

    /// The requests asking this connection's client for its semantic tokens
    /// and folding ranges again, once something other than a document's own
    /// text changed what they answer: one for each its client requests again
    /// when asked, none when the connection is not running. Every fold this
    /// server answers is read off the document's own text, and a recheck of a
    /// copy whose closure changed asks for its tokens itself
    /// ([`Server::resynchronise`]), so nothing in this crate calls it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: while running, a tokens request when the client refreshes its
    ///   tokens, then a folds request when it refreshes its folds; nothing
    ///   otherwise.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a client refreshing both, either and neither, and one
    ///   not yet initialised, are asked exactly what they refresh.
    /// - witness: `server::tests::a_refreshing_client_is_asked_for_its_tokens_and_folds_once_invalidated`
    #[spec(ensures: |ret| ret.len() == if self.phase == Phase::Running {
        usize::from(self.refreshing.tokens).saturating_add(usize::from(self.refreshing.folds))
    } else {
        0
    })]
    #[inline]
    #[must_use]
    pub fn invalidated_elsewhere(&mut self) -> Vec<Outgoing>
    {
        if self.phase != Phase::Running {
            return Vec::new();
        }
        let mut asked = Vec::new();
        if self.refreshing.tokens {
            asked.push(self.asked(Refreshed::Tokens));
        }
        if self.refreshing.folds {
            asked.push(self.asked(Refreshed::Folds));
        }
        asked
    }

    /// The next request asking the client for `answer` again, counted.
    ///
    /// # Specification
    /// trivial.
    fn asked(
        &mut self,
        answer: Refreshed,
    ) -> Outgoing
    {
        refresh(answer, self.next_request())
    }

    /// The requests asking this connection's client for the syntax tree of the
    /// document at `uri` again: one under each URI the client asked for it by,
    /// each counted.
    ///
    /// # Specification
    /// trivial.
    fn reviewed(
        &mut self,
        uri: &DocumentUri,
    ) -> Vec<Outgoing>
    {
        let mut sent = self.sent;
        let asked = self
            .viewing
            .range((uri.clone(), DocumentUri::from("")) ..)
            .take_while(|&&(ref viewed, _)| viewed == uri)
            .map(|&(_, ref tree)| {
                sent = Requests(sent.0.saturating_add(1_u64));
                refresh_content(ContentParams { uri: tree.clone() }, sent)
            })
            .collect();
        self.sent = sent;
        asked
    }

    /// The number of the next numbered request this connection sends,
    /// counted.
    ///
    /// # Specification
    /// trivial.
    fn next_request(&mut self) -> Requests
    {
        self.sent = Requests(self.sent.0.saturating_add(1_u64));
        self.sent
    }

    /// The request putting `params` to this connection's user, recorded as
    /// pending until the client answers it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a `window/showMessageRequest` under a fresh numbered
    ///   identifier, recorded last as [`Choice::Pending`] under it.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a choice asked, answered with an action, with null
    ///   and with an error, and one never asked, read back as chosen,
    ///   dismissed, dismissed and unknown.
    /// - witness: `server::tests::a_choice_put_to_the_user_reads_its_answer`
    #[spec(ensures: |ret| matches!(ret, Outgoing::Request { ref id, .. }
        if matches!(self.choices.last(), Some(&(ref asked, Choice::Pending)) if asked == id)))]
    #[inline]
    #[must_use]
    pub fn ask(
        &mut self,
        params: ChoiceParams,
    ) -> Outgoing
    {
        let asked = choose(params, self.next_request());
        if let Outgoing::Request { ref id, .. } = asked {
            self.choices.push((id.clone(), Choice::Pending));
        }
        asked
    }

    /// Where the choice put by the request `id` stands; none when this
    /// connection put no such choice.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn chosen(
        &self,
        id: &RequestId,
    ) -> Option<&Choice>
    {
        self.choices
            .iter()
            .find(|&&(ref asked, _)| asked == id)
            .map(|&(_, ref choice)| choice)
    }

    /// `answer`, a whole-document token answer for the document at `uri`,
    /// as this connection sends it: the edits from the stream it last sent
    /// when `previous` names that stream, and the answer whole otherwise.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a token answer carrying an id is kept as the document's last
    ///   stream, and answered as the edits from the stream kept before it when
    ///   `previous` is that stream's id; an answer of nothing forgets the
    ///   document's stream. Edits are answered only for a `previous` given.
    /// - provides: `textDocument/semanticTokens/full` and its delta.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a full answer, a delta named by its id after an edit,
    ///   a delta repeated at the same id, a delta named by an unknown id, and a
    ///   delta after the document closed are each the exact wire answer.
    /// - witness: `server::tests::a_delta_answers_the_edits_from_the_last_full_stream`
    #[spec(ensures: |ret| previous.is_some() || !matches!(ret, Answer::Deltas(_)))]
    fn streamed(
        &mut self,
        uri: DocumentUri,
        previous: Option<&ResultId>,
        answer: Answer,
    ) -> Answer
    {
        let Answer::Tokens(SemanticTokens {
            result_id: Some(ref id),
            ref data,
        }) = answer
        else {
            let _forgotten = self.streams.remove(&uri);
            return answer;
        };
        let held = self.streams.insert(uri, (id.clone(), data.clone()));
        match (held, previous) {
            (Some((ref held, ref stream)), Some(previous)) if held == previous => {
                Answer::Deltas(SemanticTokensDelta {
                    result_id: id.clone(),
                    edits: data.edits_from(stream),
                })
            },
            (Some(_) | None, Some(_) | None) => answer,
        }
    }

    /// Whether this connection's client asked to cancel the work under
    /// `token`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn cancelled(
        &self,
        token: &ProgressToken,
    ) -> Cancelled
    {
        Cancelled(self.cancelled.contains(token))
    }

    /// Record that the client asked to cancel the work under `token`, when
    /// this connection reported progress under it. The work has ended by the
    /// time the cancellation is read, since it runs within the handling of
    /// the message that started it, so the record is all a cancellation does.
    ///
    /// # Specification
    /// - requires: nothing; any token is admissible input.
    /// - ensures: the token is recorded once when it is one this connection
    ///   issued, `gandr/<peer>/<n>` for `n` from one to the pieces of work
    ///   reported; nothing changes otherwise.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a token issued, the same again, one not yet issued
    ///   and another connection's are recorded once, once, never and never.
    /// - witness: `server::tests::a_cancelled_progress_is_recorded_against_its_token`
    #[spec(
        captures: count = self.cancelled.len(),
        ensures: self.cancelled.len() == count || self.cancelled.len() == count.saturating_add(1),
    )]
    fn cancel(
        &mut self,
        token: ProgressToken,
    )
    {
        let issued = token
            .0
            .strip_prefix(&format!("gandr/{}/", self.peer.0))
            .and_then(|count| count.parse::<u64>().ok())
            .is_some_and(|count| (1_u64 ..= self.reported).contains(&count));
        if issued && !self.cancelled.contains(&token) {
            self.cancelled.push(token);
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
    /// - witness: `tests::editor::scenarios::typing_a_declaration_holds_its_diagnostics_until_its_terminator`
    /// - witness: `tests::session::a_held_diagnostic_publishes_once_the_document_is_quiet`
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
        self.answer(workspace, classify(body), &[])
    }

    /// Handle one classified `message` over `workspace`, knowing the messages
    /// `later` the client sent after it.
    ///
    /// # Specification
    /// - requires: `later` is what the client sent after `message`, in order.
    /// - ensures: as [`Server::handle`], except that a request of a running
    ///   session other than `shutdown` that [`Withdrawn::of`] withdraws by
    ///   `later` is answered with the error the withdrawal owes, under its own
    ///   identifier, and not run; a `shutdown` of a running session whose
    ///   client watches files for it is answered after the request withdrawing
    ///   the watcher; a `workspace/executeCommand` of a running session is run
    ///   as `Server::execute` states; a response is handled as
    ///   `Server::response` states; a change of a document this connection
    ///   holds and whose syntax tree its client asked for asks the client for
    ///   the tree again under each URI it asked by, after the change's own
    ///   messages.
    /// - provides: the step of [`serve`] and of each hub connection, which read
    ///   ahead of the message they handle.
    /// - fails: never; every refusal is a message to the client.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a hover cancelled by a later message, one whose
    ///   document a later change edits, one with neither, and a `shutdown`
    ///   cancelled after it, are each asserted at their answer.
    /// - witness: `server::tests::a_request_withdrawn_by_a_later_message_is_not_run`
    /// - witness: `server::tests::a_watching_client_is_asked_to_watch_every_source`
    /// - witness: `server::tests::a_lens_applies_its_one_checked_fill`
    /// - witness: `server::tests::a_viewed_tree_answers_its_document_and_is_asked_again_after_each_change`
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
    pub fn answer(
        &mut self,
        workspace: &mut Workspace,
        message: Classified,
        later: &[Classified],
    ) -> Outcome
    {
        match message {
            Err(malformed) => Outcome::say(malformed.response()),
            Ok(Incoming::Response { id, result }) => self.response(workspace, &id, result),
            Ok(Incoming::Request { id, method, params }) => {
                let withdrawn = match (self.phase, method.as_ref()) {
                    (Phase::Running, name) if name != "shutdown" => {
                        Withdrawn::of(&id, &params, later)
                    },
                    _ => None,
                };
                let unwatching = self.phase == Phase::Running
                    && method.as_ref() == "shutdown"
                    && self.watching.0;
                if withdrawn.is_none()
                    && self.phase == Phase::Running
                    && method.as_ref() == "workspace/executeCommand"
                {
                    return self.execute(workspace, id, params);
                }
                let answered = match withdrawn {
                    Some(withdrawn) => withdrawn.response(id),
                    None => self.request(workspace, id, &method, params),
                };
                if unwatching {
                    Outcome {
                        messages: Vec::from([
                            unregister(UnregistrationParams::watched_files()),
                            answered,
                        ]),
                        log: Vec::new(),
                        flow: Flow::Continue,
                    }
                }
                else {
                    Outcome::say(answered)
                }
            },
            Ok(Incoming::Notification { method, params }) => {
                let changed = (self.phase == Phase::Running
                    && method.as_ref() == "textDocument/didChange")
                    .then(|| params.pointer("/textDocument/uri").and_then(Value::as_str))
                    .flatten()
                    .map(DocumentUri::from);
                let mut outcome = self.notification(workspace, &method, params);
                if let Some(uri) = changed
                    && workspace.documents.contains_key(&uri)
                {
                    outcome.messages.extend(self.reviewed(&uri));
                }
                outcome
            },
        }
    }

    /// Run the command `params` names, answering request `id`:
    /// [`APPLY_FILL`] asks the client to apply the checked fill its
    /// arguments name.
    ///
    /// # Specification
    /// - requires: nothing; any parameters are admissible input.
    /// - ensures: for [`APPLY_FILL`] naming a fill the document at its URI
    ///   still keeps, a `workspace/applyEdit` request carrying the fill's edit,
    ///   shaped as the client takes edits ([`WorkspaceEdit::shaped`]), under a
    ///   fresh numbered identifier, then the answer `null`; for one naming a
    ///   fill the document does not keep, `ContentModified`; for any other
    ///   command, or arguments that do not read, `InvalidParams`.
    /// - fails: never; every refusal is an answer.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the lens's command run, run again after the
    ///   document's next edit, an unknown command and arguments of another
    ///   shape, each asserted at its exact messages.
    /// - witness: `server::tests::a_lens_applies_its_one_checked_fill`
    #[spec(ensures: |ret| ret.flow == Flow::Continue && ret.log.is_empty()
        && matches!(ret.messages.as_slice(),
            [Outgoing::Failure { .. }]
            | [Outgoing::Request { .. }, Outgoing::Success { result: Answer::Nothing, .. }]))]
    fn execute(
        &mut self,
        workspace: &Workspace,
        id: RequestId,
        params: Value,
    ) -> Outcome
    {
        let named = serde_json::from_value::<ExecuteCommandParams>(params)
            .map_err(|error| error.to_string())
            .and_then(|params| {
                if params.command != APPLY_FILL {
                    return Err(format!("the server runs no command `{}`", params.command));
                }
                match *params.arguments.as_slice() {
                    [ref uri, ref range, Value::String(ref text)] => Ok((
                        DocumentUri::deserialize(uri).map_err(|error| error.to_string())?,
                        TextEdit {
                            range: Range::deserialize(range).map_err(|error| error.to_string())?,
                            new_text: text.clone(),
                        },
                    )),
                    _ => Err(format!(
                        "`{APPLY_FILL}` takes a document's URI, a range and the fill's text"
                    )),
                }
            });
        let (uri, fill) = match named {
            Ok(named) => named,
            Err(message) => {
                return Outcome::say(failure(id, ErrorCode::INVALID_PARAMS, message));
            },
        };
        let edit = match workspace.view(&uri, self.peer) {
            Maybe::Present(document) => applied(&uri, &document.proposals, fill),
            Maybe::Absent(_) => None,
        };
        let Some(edit) = edit
        else {
            return Outcome::say(failure(
                id,
                ErrorCode::CONTENT_MODIFIED,
                String::from(
                    "the fill is no longer kept: the document changed since it was offered",
                ),
            ));
        };
        let sent = self.next_request();
        Outcome {
            messages: Vec::from([
                apply_edit(
                    ApplyEditParams {
                        label: "Apply the checked fill",
                        edit: edit.shaped(self.editing, |uri| workspace.held_by(uri, self.peer)),
                    },
                    sent,
                ),
                success(id, Answer::Nothing),
            ]),
            log: Vec::new(),
            flow: Flow::Continue,
        }
    }

    /// `answer` with each edit it carries shaped as this connection's client
    /// takes edits ([`WorkspaceEdit::shaped`]), each version its own copy's.
    ///
    /// # Specification
    /// trivial.
    fn edited(
        &self,
        workspace: &Workspace,
        answer: Answer,
    ) -> Answer
    {
        let shape = |edit: WorkspaceEdit| {
            edit.shaped(self.editing, |uri| workspace.held_by(uri, self.peer))
        };
        if let Answer::Renamed(edit) = answer {
            return Answer::Renamed(shape(edit));
        }
        if let Answer::Actions(actions) = answer {
            return Answer::Actions(
                actions
                    .into_iter()
                    .map(|action| CodeAction {
                        edit: shape(action.edit),
                        ..action
                    })
                    .collect(),
            );
        }
        answer
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
    /// - witness: `tests::session::an_edit_to_a_large_document_rechecks_its_forms`
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
            Outgoing::Notification { method: "textDocument/publishDiagnostics", params: Notified::Published(ref params), .. }
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

    /// The progress of the work `message` starts: the messages written before
    /// it is handled, and those written once its admissions ran.
    ///
    /// # Specification
    /// - requires: `message` is the next message [`Server::answer`] handles.
    /// - ensures: for a running connection whose client shows progress, a
    ///   `textDocument/didOpen` begins one piece of work titled `Checking` on
    ///   the document's file name, and a `workspace/didChangeWatchedFiles`
    ///   naming a file the closure of a copy this connection holds named at its
    ///   last judgement, or a `workspace/didCreateFiles`, `didDeleteFiles` or
    ///   `didRenameFiles` naming such a file or a folder holding one, begins
    ///   one titled `Rechecking` on how many copies it rechecks. A piece of
    ///   work begins with a create request and a begin report under a token no
    ///   earlier piece used, and ends with one end report under the same token.
    ///   Every other message reports nothing and uses no token.
    /// - provides: what a client shows while a closure is checked and while the
    ///   watched files' dependants are rechecked.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an open and a watched-files change are reported to a
    ///   client that shows progress and to no other, each under a token of its
    ///   own; a change naming no closure, an edit and a request report nothing.
    /// - witness: `server::tests::progress_is_reported_around_the_work_a_message_starts`
    #[spec(
        captures: before = self.reported,
        ensures: |ret| if ret.begin.is_empty() {
            ret.end.is_empty() && self.reported == before
        } else {
            ret.begin.len() == 2 && ret.end.len() == 1 && self.reported == before.saturating_add(1)
        },
    )]
    #[inline]
    #[must_use]
    pub fn reported(
        &mut self,
        workspace: &Workspace,
        message: &Classified,
    ) -> Reported
    {
        let Ok(Incoming::Notification {
            ref method,
            ref params,
        }) = *message
        else {
            return Reported::default();
        };
        if self.phase != Phase::Running || !self.progress.0 {
            return Reported::default();
        }
        let (title, about) = match method.as_ref() {
            "textDocument/didOpen" => {
                let Some(uri) = params.pointer("/textDocument/uri").and_then(Value::as_str)
                else {
                    return Reported::default();
                };
                let path = DocumentUri::from(uri).path();
                let name = path.file_name().map_or_else(
                    || uri.to_owned(),
                    |name| name.to_string_lossy().into_owned(),
                );
                (WorkTitle("Checking"), name)
            },
            "workspace/didChangeWatchedFiles" => {
                let Ok(WatchedFilesParams { changes }) = WatchedFilesParams::deserialize(params)
                else {
                    return Reported::default();
                };
                return self.rechecking(
                    workspace,
                    Picks::Naming(&changed_paths(&changes), Origin::Disk),
                );
            },
            "workspace/didCreateFiles" | "workspace/didDeleteFiles" => {
                let Ok(FilesParams { files }) = FilesParams::deserialize(params)
                else {
                    return Reported::default();
                };
                return self.rechecking(workspace, Picks::Under(&changed_paths(&files)));
            },
            "workspace/didRenameFiles" => {
                let Ok(RenameFilesParams { files }) = RenameFilesParams::deserialize(params)
                else {
                    return Reported::default();
                };
                return self.rechecking(workspace, Picks::Under(&renamed_paths(&files)));
            },
            _ => return Reported::default(),
        };
        self.piece(title, about)
    }

    /// The progress of rechecking the copies this connection holds whose
    /// closures name a file of `changed`, the hub's watch having seen them
    /// change on disk.
    ///
    /// # Specification
    /// - requires: `changed` is sorted, as [`named_path`] names each file.
    /// - ensures: as [`Server::reported`] states for a watched-files change
    ///   naming `changed`.
    /// - provides: what a client shows while the hub's watch has dependants
    ///   rechecked.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — through [`Server::reported`]'s witness, the two
    ///   sharing one body.
    /// - witness: `server::tests::progress_is_reported_around_the_work_a_message_starts`
    #[spec(
        captures: before = self.reported,
        ensures: |ret| if ret.begin.is_empty() {
            ret.end.is_empty() && self.reported == before
        } else {
            ret.begin.len() == 2 && ret.end.len() == 1 && self.reported == before.saturating_add(1)
        },
    )]
    #[inline]
    #[must_use]
    pub fn reported_on_disk(
        &mut self,
        workspace: &Workspace,
        changed: &[PathBuf],
    ) -> Reported
    {
        if self.phase != Phase::Running || !self.progress.0 {
            return Reported::default();
        }
        self.rechecking(workspace, Picks::Naming(changed, Origin::Disk))
    }

    /// The progress of rechecking the copies this connection holds whose
    /// closures name a file of `changed`, another connection's editor having
    /// changed its copy of each.
    ///
    /// # Specification
    /// - requires: `changed` is sorted, as [`named_path`] names each file.
    /// - ensures: as [`Server::reported_on_disk`] states, for the copies
    ///   [`Server::edited_elsewhere`] rechecks.
    /// - provides: what a client shows while another editor's change has
    ///   dependants rechecked.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — through [`Server::reported`]'s witness, the three
    ///   sharing one body.
    /// - witness: `server::tests::progress_is_reported_around_the_work_a_message_starts`
    #[spec(
        captures: before = self.reported,
        ensures: |ret| if ret.begin.is_empty() {
            ret.end.is_empty() && self.reported == before
        } else {
            ret.begin.len() == 2 && ret.end.len() == 1 && self.reported == before.saturating_add(1)
        },
    )]
    #[inline]
    #[must_use]
    pub fn reported_elsewhere(
        &mut self,
        workspace: &Workspace,
        changed: &[PathBuf],
    ) -> Reported
    {
        if self.phase != Phase::Running || !self.progress.0 {
            return Reported::default();
        }
        self.rechecking(workspace, Picks::Naming(changed, Origin::Editor))
    }

    /// The progress of rechecking the copies `picks` picks, on a running
    /// connection whose client shows progress.
    ///
    /// # Specification
    /// trivial.
    fn rechecking(
        &mut self,
        workspace: &Workspace,
        picks: Picks<'_>,
    ) -> Reported
    {
        let rechecked = workspace
            .documents
            .values()
            .filter(|held| match held.own(self.peer) {
                Maybe::Present(document) => picked(picks, &workspace.paths, &document.named).0,
                Maybe::Absent(_) => false,
            })
            .count();
        match rechecked {
            0 => Reported::default(),
            1 => self.piece(WorkTitle("Rechecking"), String::from("1 open document")),
            many => self.piece(WorkTitle("Rechecking"), format!("{many} open documents")),
        }
    }

    /// One piece of work titled `title` on `about`, under a token no earlier
    /// piece used.
    ///
    /// # Specification
    /// trivial.
    fn piece(
        &mut self,
        title: WorkTitle,
        about: String,
    ) -> Reported
    {
        self.reported = self.reported.saturating_add(1);
        let token = ProgressToken(format!("gandr/{}/{}", self.peer.0, self.reported));
        Reported {
            begin: Vec::from(progress_begun(&token, title, about)),
            end: Vec::from([progress_ended(token)]),
        }
    }

    /// The files the closures of the copies this connection holds named at
    /// their last judgement, for the hub's watch to follow; none when its
    /// client watches files itself.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: empty unless the connection is running and its client does
    ///   not watch files; otherwise every path the closure of a copy it holds
    ///   named, as [`named_path`] names it.
    /// - provides: what the hub's watch follows for a connection.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a hub connection whose client watches nothing is told
    ///   of a rewritten import; one whose client watches is left to its client.
    /// - witness: `hub::tests::an_unwatching_client_is_told_of_a_rewritten_import`
    #[spec(ensures: |ret| ret.is_empty() || (self.phase == Phase::Running && !self.watching.0))]
    #[inline]
    #[must_use]
    pub fn followed(
        &self,
        workspace: &Workspace,
    ) -> BTreeSet<PathBuf>
    {
        if self.phase != Phase::Running || self.watching.0 {
            return BTreeSet::new();
        }
        workspace
            .documents
            .values()
            .filter_map(|held| match held.own(self.peer) {
                Maybe::Present(document) => Some(document.named.iter()),
                Maybe::Absent(_) => None,
            })
            .flatten()
            .filter(|named| !workspace.paths.contains_key(*named))
            .cloned()
            .collect()
    }

    /// Recheck the copies this connection holds whose closures name a file of
    /// `changed`, the hub's watch having seen them change on disk.
    ///
    /// # Specification
    /// - requires: `changed` is sorted, as [`named_path`] names each file.
    /// - ensures: on a running connection whose client does not watch files, as
    ///   [`Server::handle`] states for a watched-files change naming `changed`;
    ///   on any other, nothing.
    /// - provides: the hub's watch's change, handled as the client's own
    ///   notification would be.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a hub connection whose client watches nothing
    ///   republishes an open document when a file it imports is rewritten on
    ///   disk.
    /// - witness: `hub::tests::an_unwatching_client_is_told_of_a_rewritten_import`
    #[spec(ensures: |ret| ret.messages.is_empty() || (self.phase == Phase::Running && !self.watching.0))]
    #[inline]
    #[must_use]
    pub fn changed_on_disk(
        &mut self,
        workspace: &mut Workspace,
        changed: &[PathBuf],
    ) -> Outcome
    {
        if self.phase != Phase::Running || self.watching.0 {
            return Outcome::quiet();
        }
        self.resynchronise(workspace, Picks::Naming(changed, Origin::Disk))
    }

    /// Recheck the copies this connection holds whose closures name a file of
    /// `changed`, another connection's editor having changed its copy of each.
    ///
    /// # Specification
    /// - requires: `changed` is sorted, as [`named_path`] names each file.
    /// - ensures: on a running connection, every copy it holds whose closure,
    ///   at its last judgement, named a file of `changed` is rechecked, each
    ///   import read as the editors hold it, and republished in URI order, at
    ///   its version, to this connection alone, one timing line each; on any
    ///   other, nothing.
    /// - provides: another connection's edit, reaching the importers this one
    ///   holds.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a hub connection holding an importer republishes it
    ///   when another connection's editor changes the base it imports, and
    ///   again when that editor closes the base.
    /// - witness: `hub::tests::an_editor_s_copy_shadows_the_disk_for_every_connection`
    #[spec(ensures: |ret| ret.messages.is_empty() || self.phase == Phase::Running)]
    #[inline]
    #[must_use]
    pub fn edited_elsewhere(
        &mut self,
        workspace: &mut Workspace,
        changed: &[PathBuf],
    ) -> Outcome
    {
        if self.phase != Phase::Running {
            return Outcome::quiet();
        }
        self.resynchronise(workspace, Picks::Naming(changed, Origin::Editor))
    }

    /// After the copy of the file at `path` changed or was let go, recheck the
    /// copies this connection holds whose closures name it, into `outcome`,
    /// and tell every other connection whose copies name it.
    ///
    /// # Specification
    /// trivial.
    fn reclosed(
        &mut self,
        workspace: &mut Workspace,
        path: &Path,
        outcome: &mut Outcome,
    )
    {
        workspace.edited(path, self.peer);
        let rechecked = self.resynchronise(workspace, Picks::File(path));
        outcome.messages.extend(rechecked.messages);
        outcome.log.extend(rechecked.log);
    }

    /// Recheck the copies this connection holds that `picks` picks,
    /// republishing each to this connection alone, each import read as the
    /// editors hold it, and, when a copy was rechecked because its closure
    /// changed, ask a client that refreshes its semantic tokens for them
    /// again: each use is classified by what the new judgement resolved it to.
    ///
    /// # Specification
    /// trivial.
    fn resynchronise(
        &mut self,
        workspace: &mut Workspace,
        picks: Picks<'_>,
    ) -> Outcome
    {
        let peer = self.peer;
        let paths = &workspace.paths;
        let chosen = |document: &Document| picked(picks, paths, &document.named).0;
        let mut outcome = Outcome::quiet();
        if !workspace
            .documents
            .values()
            .any(|held| matches!(held.own(peer), Maybe::Present(document) if chosen(document)))
        {
            return outcome;
        }
        let mut pending = core::mem::take(&mut workspace.documents);
        while let Some((uri, mut held)) = pending.pop_first() {
            if let Maybe::Present(document) = held.own_mut(peer)
                && chosen(document)
            {
                if !matches!(picks, Picks::Every) {
                    document.text.reclose();
                }
                let shadows = Shadowing {
                    held: &workspace.documents,
                    pending: Some(&pending),
                    paths,
                    peer,
                };
                let rechecked = synchronised(
                    &uri,
                    document,
                    &shadows,
                    self.verbosity,
                    self.style.spelling,
                    self.quiet,
                );
                outcome.messages.extend(rechecked.messages);
                outcome.log.extend(rechecked.log);
            }
            let _kept = workspace.documents.insert(uri, held);
        }
        for message in &outcome.messages {
            workspace.published_by(peer, message);
        }
        if !matches!(picks, Picks::Every) && self.phase == Phase::Running && self.refreshing.tokens
        {
            outcome.messages.push(self.asked(Refreshed::Tokens));
        }
        outcome
    }

    /// The response to the request `id` calling `method` with `params`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: initialization and shutdown advance the lifecycle once, and
    ///   initialization takes the verbosity, the quiet interval and the
    ///   presentation form and spelling its options name, the user level,
    ///   [`QUIET`], the sugared form and the workspace's spelling when they
    ///   name none, and the markup and the definition links its client's
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
    /// - witness: `server::tests::completion_answers_the_names_a_word_may_complete_to_806`
    /// - witness: `server::tests::workspace_symbols_find_the_names_the_open_closures_declare`
    /// - witness: `server::tests::the_outline_requests_answer_a_known_document`
    /// - witness: `server::tests::a_hover_answers_a_known_declaration`
    /// - witness: `server::tests::definition_answers_what_a_use_refers_to_795`
    /// - witness: `server::tests::kept_proposals_reach_every_editor_surface`
    /// - witness: `server::tests::formatting_answers_the_edits_that_lay_a_document_out`
    /// - witness: `server::tests::a_configuration_change_republishes_at_its_verbosity`
    /// - witness: `server::tests::a_listed_item_resolves_as_it_came`
    /// - witness: `server::tests::a_moved_file_s_imports_follow_it`
    #[spec(
        captures: [phase = self.phase, initial = initial_settings(&params), markup = initial_markup(&params),
            linked = initial_links(&params), offsets = initial_offsets(&params), watching = initial_watching(&params),
            progress = initial_progress(&params), refreshing = initial_refreshing(&params)],
        ensures: |ret| match (phase, method.as_ref()) {
            (Phase::Waiting, "initialize") => self.phase == Phase::Running
                && self.verbosity == initial.verbosity().unwrap_or_default()
                && self.quiet == initial.quiet().unwrap_or(QUIET)
                && self.style == Style {
                    form: initial.form().unwrap_or(Form::Sugared),
                    spelling: initial.spelling().unwrap_or(workspace.spelling),
                    markup,
                }
                && self.linked == linked
                && self.offsets == offsets
                && self.watching == watching
                && self.progress == progress
                && self.refreshing == refreshing
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
                    Outgoing::Success { .. } | Outgoing::Notification { .. } | Outgoing::Request { .. } | Outgoing::Progress(_) => false,
                },
            (Phase::Running, "textDocument/semanticTokens/full/delta") =>
                self.phase == phase && match ret {
                    Outgoing::Success { result: Answer::Nothing | Answer::Tokens(_) | Answer::Deltas(_), .. } => true,
                    Outgoing::Failure { ref error, .. } => error.code == ErrorCode::INVALID_PARAMS,
                    Outgoing::Success { .. } | Outgoing::Notification { .. } | Outgoing::Request { .. } | Outgoing::Progress(_) => false,
                },
            (Phase::Running, "textDocument/completion") =>
                self.phase == phase && match ret {
                    Outgoing::Success { result: Answer::Nothing | Answer::Completions(_), .. } => true,
                    Outgoing::Failure { ref error, .. } => error.code == ErrorCode::INVALID_PARAMS,
                    Outgoing::Success { .. } | Outgoing::Notification { .. } | Outgoing::Request { .. } | Outgoing::Progress(_) => false,
                },
            (Phase::Running, "completionItem/resolve") =>
                self.phase == phase && match ret {
                    Outgoing::Success { result: Answer::Resolved(_), .. } => true,
                    Outgoing::Failure { ref error, .. } => error.code == ErrorCode::INVALID_PARAMS,
                    Outgoing::Success { .. } | Outgoing::Notification { .. } | Outgoing::Request { .. } | Outgoing::Progress(_) => false,
                },
            (Phase::Running, "codeAction/resolve" | "documentLink/resolve" | "workspaceSymbol/resolve") =>
                self.phase == phase && match ret {
                    Outgoing::Success { result: Answer::Unchanged(_), .. } => true,
                    Outgoing::Failure { ref error, .. } => error.code == ErrorCode::INVALID_PARAMS,
                    Outgoing::Success { .. } | Outgoing::Notification { .. } | Outgoing::Request { .. } | Outgoing::Progress(_) => false,
                },
            (Phase::Running, "codeLens/resolve") =>
                self.phase == phase && match ret {
                    Outgoing::Success { result: Answer::Unchanged(_) | Answer::Lens(_), .. } => true,
                    Outgoing::Failure { ref error, .. } => error.code == ErrorCode::INVALID_PARAMS,
                    Outgoing::Success { .. } | Outgoing::Notification { .. } | Outgoing::Request { .. } | Outgoing::Progress(_) => false,
                },
            (Phase::Running, "textDocument/signatureHelp") =>
                self.phase == phase && match ret {
                    Outgoing::Success { result: Answer::Nothing | Answer::Signatures(_), .. } => true,
                    Outgoing::Failure { ref error, .. } => error.code == ErrorCode::INVALID_PARAMS,
                    Outgoing::Success { .. } | Outgoing::Notification { .. } | Outgoing::Request { .. } | Outgoing::Progress(_) => false,
                },
            (Phase::Running, "textDocument/inlineCompletion") =>
                self.phase == phase && match ret {
                    Outgoing::Success { result: Answer::Nothing | Answer::Inline(_), .. } => true,
                    Outgoing::Failure { ref error, .. } => error.code == ErrorCode::INVALID_PARAMS,
                    Outgoing::Success { .. } | Outgoing::Notification { .. } | Outgoing::Request { .. } | Outgoing::Progress(_) => false,
                },
            (Phase::Running, "workspace/symbol") =>
                self.phase == phase && match ret {
                    Outgoing::Success { result: Answer::Found(ref found), .. } => found.len() <= FOUND_HELD,
                    Outgoing::Failure { ref error, .. } => error.code == ErrorCode::INVALID_PARAMS,
                    Outgoing::Success { .. } | Outgoing::Notification { .. } | Outgoing::Request { .. } | Outgoing::Progress(_) => false,
                },
            (Phase::Running, "textDocument/references") =>
                self.phase == phase && match ret {
                    Outgoing::Success { result: Answer::Nothing | Answer::Locations(_), .. } => true,
                    Outgoing::Failure { ref error, .. } => error.code == ErrorCode::INVALID_PARAMS,
                    Outgoing::Success { .. } | Outgoing::Notification { .. } | Outgoing::Request { .. } | Outgoing::Progress(_) => false,
                },
            (Phase::Running, "textDocument/prepareRename") =>
                self.phase == phase && match ret {
                    Outgoing::Success { result: Answer::Nothing | Answer::Renaming(_), .. } => true,
                    Outgoing::Failure { ref error, .. } => error.code == ErrorCode::INVALID_PARAMS,
                    Outgoing::Success { .. } | Outgoing::Notification { .. } | Outgoing::Request { .. } | Outgoing::Progress(_) => false,
                },
            (Phase::Running, "textDocument/rename") =>
                self.phase == phase && match ret {
                    Outgoing::Success { result: Answer::Nothing | Answer::Renamed(_), .. } => true,
                    Outgoing::Failure { ref error, .. } =>
                        error.code == ErrorCode::INVALID_PARAMS || error.code == ErrorCode::REQUEST_FAILED,
                    Outgoing::Success { .. } | Outgoing::Notification { .. } | Outgoing::Request { .. } | Outgoing::Progress(_) => false,
                },
            (Phase::Running, "workspace/willRenameFiles") =>
                self.phase == phase && match ret {
                    Outgoing::Success { result: Answer::Nothing | Answer::Renamed(_), .. } => true,
                    Outgoing::Failure { ref error, .. } => error.code == ErrorCode::INVALID_PARAMS,
                    Outgoing::Success { .. } | Outgoing::Notification { .. } | Outgoing::Request { .. } | Outgoing::Progress(_) => false,
                },
            (Phase::Running, "workspace/willCreateFiles" | "workspace/willDeleteFiles") =>
                self.phase == phase && match ret {
                    Outgoing::Success { result: Answer::Nothing, .. } => true,
                    Outgoing::Failure { ref error, .. } => error.code == ErrorCode::INVALID_PARAMS,
                    Outgoing::Success { .. } | Outgoing::Notification { .. } | Outgoing::Request { .. } | Outgoing::Progress(_) => false,
                },
            (Phase::Running, "textDocument/documentHighlight") =>
                self.phase == phase && match ret {
                    Outgoing::Success { result: Answer::Nothing | Answer::Highlights(_), .. } => true,
                    Outgoing::Failure { ref error, .. } => error.code == ErrorCode::INVALID_PARAMS,
                    Outgoing::Success { .. } | Outgoing::Notification { .. } | Outgoing::Request { .. } | Outgoing::Progress(_) => false,
                },
            (Phase::Running, "textDocument/linkedEditingRange") =>
                self.phase == phase && match ret {
                    Outgoing::Success { result: Answer::Nothing | Answer::Mirrored(_), .. } => true,
                    Outgoing::Failure { ref error, .. } => error.code == ErrorCode::INVALID_PARAMS,
                    Outgoing::Success { .. } | Outgoing::Notification { .. } | Outgoing::Request { .. } | Outgoing::Progress(_) => false,
                },
            (Phase::Running, "textDocument/prepareTypeHierarchy" | "typeHierarchy/supertypes" | "typeHierarchy/subtypes") =>
                self.phase == phase && match ret {
                    Outgoing::Success { result: Answer::Nothing, .. } => true,
                    Outgoing::Failure { ref error, .. } => error.code == ErrorCode::INVALID_PARAMS,
                    Outgoing::Success { .. } | Outgoing::Notification { .. } | Outgoing::Request { .. } | Outgoing::Progress(_) => false,
                },
            (Phase::Running, "textDocument/documentSymbol" | "textDocument/foldingRange" | "textDocument/selectionRange" | "textDocument/documentLink") =>
                self.phase == phase && match ret {
                    Outgoing::Success { result: Answer::Nothing | Answer::Symbols(_) | Answer::Folds(_) | Answer::Selections(_) | Answer::Imports(_), .. } => true,
                    Outgoing::Failure { ref error, .. } => error.code == ErrorCode::INVALID_PARAMS,
                    Outgoing::Success { .. } | Outgoing::Notification { .. } | Outgoing::Request { .. } | Outgoing::Progress(_) => false,
                },
            (Phase::Running, "textDocument/hover") =>
                self.phase == phase && match ret {
                    Outgoing::Success { result: Answer::Nothing | Answer::Hover(_), .. } => true,
                    Outgoing::Failure { ref error, .. } => error.code == ErrorCode::INVALID_PARAMS,
                    Outgoing::Success { .. } | Outgoing::Notification { .. } | Outgoing::Request { .. } | Outgoing::Progress(_) => false,
                },
            (Phase::Running, "textDocument/definition" | "textDocument/declaration" | "textDocument/typeDefinition") =>
                self.phase == phase && match ret {
                    Outgoing::Success { result: Answer::Nothing | Answer::Links(_) | Answer::Locations(_), .. } => true,
                    Outgoing::Failure { ref error, .. } => error.code == ErrorCode::INVALID_PARAMS,
                    Outgoing::Success { .. } | Outgoing::Notification { .. } | Outgoing::Request { .. } | Outgoing::Progress(_) => false,
                },
            (Phase::Running, "textDocument/codeLens" | "textDocument/codeAction") =>
                self.phase == phase && match ret {
                    Outgoing::Success { result: Answer::Nothing | Answer::Lenses(_) | Answer::Actions(_), .. } => true,
                    Outgoing::Failure { ref error, .. } => error.code == ErrorCode::INVALID_PARAMS,
                    Outgoing::Success { .. } | Outgoing::Notification { .. } | Outgoing::Request { .. } | Outgoing::Progress(_) => false,
                },
            (Phase::Running, "textDocument/formatting" | "textDocument/rangeFormatting" | "textDocument/rangesFormatting"
                | "textDocument/onTypeFormatting" | "textDocument/willSaveWaitUntil") =>
                self.phase == phase && match ret {
                    Outgoing::Success { result: Answer::Nothing | Answer::Edits(_), .. } => true,
                    Outgoing::Failure { ref error, .. } =>
                        error.code == ErrorCode::INVALID_PARAMS || error.code == ErrorCode::REQUEST_FAILED,
                    Outgoing::Success { .. } | Outgoing::Notification { .. } | Outgoing::Request { .. } | Outgoing::Progress(_) => false,
                },
            (Phase::Running, "gandr/importFiles") =>
                self.phase == phase && match ret {
                    Outgoing::Success { result: Answer::Nothing | Answer::Edits(_), .. } => true,
                    Outgoing::Failure { ref error, .. } => error.code == ErrorCode::INVALID_PARAMS,
                    Outgoing::Success { .. } | Outgoing::Notification { .. } | Outgoing::Request { .. } | Outgoing::Progress(_) => false,
                },
            (Phase::Running, "workspace/textDocumentContent") =>
                self.phase == phase && match ret {
                    Outgoing::Success { result: Answer::Content(_), .. } => true,
                    Outgoing::Failure { ref error, .. } =>
                        error.code == ErrorCode::INVALID_PARAMS || error.code == ErrorCode::REQUEST_FAILED,
                    Outgoing::Success { .. } | Outgoing::Notification { .. } | Outgoing::Request { .. } | Outgoing::Progress(_) => false,
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
                    spelling: settings.spelling().unwrap_or(workspace.spelling),
                    markup: initial_markup(&params),
                };
                self.linked = initial_links(&params);
                self.offsets = initial_offsets(&params);
                self.detailing = initial_detailing(&params);
                self.snipping = initial_snipping(&params);
                self.collapsing = initial_collapsing(&params);
                self.watching = initial_watching(&params);
                self.progress = initial_progress(&params);
                self.refreshing = initial_refreshing(&params);
                self.trace = initial_trace(&params);
                self.pulling = initial_pulling(&params);
                self.applying = initial_applying(&params);
                self.editing = initial_editing(&params);
                self.showing = initial_showing(&params);
                self.listing = initial_listing(&params);
                self.viewer = initial_viewer(&params);
                workspace.rooted(self.peer, &initial_roots(&params));
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
                    Ok(params) => {
                        let answer =
                            workspace.tokens(&params.text_document.uri, self.peer, Window::Whole);
                        success(id, self.streamed(params.text_document.uri, None, answer))
                    },
                    Err(error) => failure(id, ErrorCode::INVALID_PARAMS, error.to_string()),
                }
            },
            (Phase::Running, "textDocument/semanticTokens/full/delta") => {
                match serde_json::from_value::<DeltaParams>(params) {
                    Ok(params) => {
                        let answer =
                            workspace.tokens(&params.text_document.uri, self.peer, Window::Whole);
                        success(
                            id,
                            self.streamed(
                                params.text_document.uri,
                                Some(&params.previous_result_id),
                                answer,
                            ),
                        )
                    },
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
            (Phase::Running, "textDocument/completion") => {
                match serde_json::from_value::<PositionParams>(params) {
                    Ok(params) => success(
                        id,
                        workspace.completion(
                            &params.text_document.uri,
                            self.peer,
                            params.position,
                            (self.style.printed(), self.detailing, self.snipping),
                        ),
                    ),
                    Err(error) => failure(id, ErrorCode::INVALID_PARAMS, error.to_string()),
                }
            },
            (Phase::Running, "completionItem/resolve") => {
                match serde_json::from_value::<CompletionItem>(params) {
                    Ok(item) => success(id, workspace.resolve_completion(item, self.peer)),
                    Err(error) => failure(id, ErrorCode::INVALID_PARAMS, error.to_string()),
                }
            },
            (Phase::Running, "codeLens/resolve") => match LensResolution::deserialize(&params) {
                Ok(LensResolution {
                    range,
                    data: Some(data),
                }) => success(id, workspace.resolve_lens(range, data, self.peer)),
                Ok(LensResolution { data: None, .. }) => success(id, Answer::Unchanged(params)),
                Err(error) => failure(id, ErrorCode::INVALID_PARAMS, error.to_string()),
            },
            (
                Phase::Running,
                name @ ("codeAction/resolve" | "documentLink/resolve" | "workspaceSymbol/resolve"),
            ) => {
                let kind = match name {
                    "codeAction/resolve" => Unresolved::Action,
                    "documentLink/resolve" => Unresolved::Link,
                    _ => Unresolved::Symbol,
                };
                match kind.read(&params) {
                    Ok(()) => success(id, Answer::Unchanged(params)),
                    Err(error) => failure(id, ErrorCode::INVALID_PARAMS, error.to_string()),
                }
            },
            (Phase::Running, "textDocument/signatureHelp") => {
                match serde_json::from_value::<PositionParams>(params) {
                    Ok(params) => success(
                        id,
                        workspace.signature_help(
                            &params.text_document.uri,
                            self.peer,
                            params.position,
                            self.offsets,
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
            (Phase::Running, "workspace/symbol") => {
                match serde_json::from_value::<WorkspaceSymbolParams>(params) {
                    Ok(params) => success(
                        id,
                        workspace.symbols(self.peer, SourceText::from(params.query.as_str())),
                    ),
                    Err(error) => failure(id, ErrorCode::INVALID_PARAMS, error.to_string()),
                }
            },
            (Phase::Running, "textDocument/documentHighlight") => {
                match serde_json::from_value::<PositionParams>(params) {
                    Ok(params) => success(
                        id,
                        workspace.highlight(&params.text_document.uri, self.peer, params.position),
                    ),
                    Err(error) => failure(id, ErrorCode::INVALID_PARAMS, error.to_string()),
                }
            },
            (Phase::Running, "textDocument/linkedEditingRange") => {
                match serde_json::from_value::<PositionParams>(params) {
                    Ok(params) => success(
                        id,
                        workspace.linked_editing(
                            &params.text_document.uri,
                            self.peer,
                            params.position,
                        ),
                    ),
                    Err(error) => failure(id, ErrorCode::INVALID_PARAMS, error.to_string()),
                }
            },
            (Phase::Running, "textDocument/prepareTypeHierarchy") => {
                // The core has no subtyping, so no position names a type with
                // a hierarchy to show.
                match serde_json::from_value::<PositionParams>(params) {
                    Ok(_) => success(id, Answer::Nothing),
                    Err(error) => failure(id, ErrorCode::INVALID_PARAMS, error.to_string()),
                }
            },
            // Only an item `prepareTypeHierarchy` answered is asked about, and
            // it answers none.
            (Phase::Running, "typeHierarchy/supertypes" | "typeHierarchy/subtypes") => {
                success(id, Answer::Nothing)
            },
            (Phase::Running, "textDocument/references") => {
                match serde_json::from_value::<ReferenceParams>(params) {
                    Ok(params) => success(
                        id,
                        workspace.references(
                            &params.text_document.uri,
                            self.peer,
                            params.position,
                            params.context,
                        ),
                    ),
                    Err(error) => failure(id, ErrorCode::INVALID_PARAMS, error.to_string()),
                }
            },
            (Phase::Running, "textDocument/prepareRename") => {
                match serde_json::from_value::<PositionParams>(params) {
                    Ok(params) => success(
                        id,
                        workspace.prepare_rename(
                            &params.text_document.uri,
                            self.peer,
                            params.position,
                        ),
                    ),
                    Err(error) => failure(id, ErrorCode::INVALID_PARAMS, error.to_string()),
                }
            },
            (Phase::Running, "textDocument/rename") => {
                match serde_json::from_value::<RenameParams>(params) {
                    Ok(params) => match workspace.rename(
                        &params.text_document.uri,
                        self.peer,
                        params.position,
                        NewName(&params.new_name),
                    ) {
                        Ok(answer) => success(id, self.edited(workspace, answer)),
                        Err(refused) => failure(id, ErrorCode::REQUEST_FAILED, refused),
                    },
                    Err(error) => failure(id, ErrorCode::INVALID_PARAMS, error.to_string()),
                }
            },
            (Phase::Running, "workspace/willRenameFiles") => {
                match serde_json::from_value::<RenameFilesParams>(params) {
                    Ok(params) => success(
                        id,
                        self.edited(
                            workspace,
                            workspace.will_rename(self.peer, &Moves::of(&params.files)),
                        ),
                    ),
                    Err(error) => failure(id, ErrorCode::INVALID_PARAMS, error.to_string()),
                }
            },
            (Phase::Running, "workspace/willCreateFiles" | "workspace/willDeleteFiles") => {
                match serde_json::from_value::<FilesParams>(params) {
                    Ok(_) => success(id, Answer::Nothing),
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
                            Answer::Folds(
                                reading
                                    .folds()
                                    .iter()
                                    .map(|fold| fold.answered(self.collapsing))
                                    .collect(),
                            )
                        }),
                    ),
                    Err(error) => failure(id, ErrorCode::INVALID_PARAMS, error.to_string()),
                }
            },
            (Phase::Running, "textDocument/documentLink") => {
                match serde_json::from_value::<DocumentParams>(params) {
                    Ok(params) => {
                        let path = named_path(&params.text_document.uri.path());
                        success(
                            id,
                            workspace.outline(
                                &params.text_document.uri,
                                self.peer,
                                |reading, text| {
                                    Answer::Imports(
                                        reading.links(&LineIndex::new(text.as_ref().into()), &path),
                                    )
                                },
                            ),
                        )
                    },
                    Err(error) => failure(id, ErrorCode::INVALID_PARAMS, error.to_string()),
                }
            },
            (Phase::Running, "gandr/importFiles") => {
                match serde_json::from_value::<ImportFilesParams>(params) {
                    Ok(params) => {
                        let path = named_path(&params.text_document.uri.path());
                        let files: Vec<PathBuf> = params
                            .files
                            .iter()
                            .map(|file| named_path(&file.path()))
                            .collect();
                        success(
                            id,
                            workspace.outline(
                                &params.text_document.uri,
                                self.peer,
                                |reading, text| {
                                    Answer::Edits(reading.imported(
                                        text,
                                        &LineIndex::new(text.as_ref().into()),
                                        &path,
                                        &files,
                                    ))
                                },
                            ),
                        )
                    },
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
            (
                Phase::Running,
                "textDocument/definition"
                | "textDocument/declaration"
                | "textDocument/typeDefinition",
            ) => {
                let goto = if name == "textDocument/definition" {
                    Goto::Definition
                }
                else if name == "textDocument/declaration" {
                    Goto::Declaration
                }
                else {
                    Goto::TypeDefinition
                };
                match serde_json::from_value::<PositionParams>(params) {
                    Ok(params) => success(
                        id,
                        workspace.definition(
                            &params.text_document.uri,
                            self.peer,
                            params.position,
                            goto,
                            self.linked,
                        ),
                    ),
                    Err(error) => failure(id, ErrorCode::INVALID_PARAMS, error.to_string()),
                }
            },
            (Phase::Running, "textDocument/codeLens") => {
                match serde_json::from_value::<DocumentParams>(params) {
                    Ok(params) => success(
                        id,
                        workspace.code_lenses(&params.text_document.uri, self.peer, self.applying),
                    ),
                    Err(error) => failure(id, ErrorCode::INVALID_PARAMS, error.to_string()),
                }
            },
            (Phase::Running, "textDocument/codeAction") => {
                match serde_json::from_value::<CodeActionParams>(params) {
                    Ok(params) => success(
                        id,
                        match workspace.view(&params.text_document.uri, self.peer) {
                            Maybe::Present(document) => {
                                let mut offered = actions(
                                    &params.text_document.uri,
                                    &document.proposals,
                                    params.range,
                                    &params.context.diagnostics,
                                );
                                if let (Ok(grammar), Ok(forms)) = (grammar(), forms()) {
                                    offered.extend(repairs(
                                        (grammar, forms),
                                        (&params.text_document.uri, document.version),
                                        document.text.source(),
                                        (params.range, &params.context.diagnostics),
                                        self.editing,
                                    ));
                                }
                                self.edited(workspace, Answer::Actions(offered))
                            },
                            Maybe::Absent(_) => Answer::Nothing,
                        },
                    ),
                    Err(error) => failure(id, ErrorCode::INVALID_PARAMS, error.to_string()),
                }
            },
            (Phase::Running, "textDocument/formatting" | "textDocument/willSaveWaitUntil") => {
                match serde_json::from_value::<DocumentParams>(params) {
                    Ok(params) => {
                        workspace.format(id, &params.text_document.uri, self.peer, Scope::Whole)
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
                        Scope::Within(&[params.range]),
                    ),
                    Err(error) => failure(id, ErrorCode::INVALID_PARAMS, error.to_string()),
                }
            },
            (Phase::Running, "textDocument/rangesFormatting") => {
                match serde_json::from_value::<RangesParams>(params) {
                    Ok(params) => workspace.format(
                        id,
                        &params.text_document.uri,
                        self.peer,
                        Scope::Within(&params.ranges),
                    ),
                    Err(error) => failure(id, ErrorCode::INVALID_PARAMS, error.to_string()),
                }
            },
            (Phase::Running, "textDocument/onTypeFormatting") => {
                match serde_json::from_value::<TypedParams>(params) {
                    Ok(params) if params.ch == FORM_CLOSER => workspace.format(
                        id,
                        &params.text_document.uri,
                        self.peer,
                        Scope::Closing(params.position),
                    ),
                    Ok(_) => success(id, Answer::Edits(Vec::new())),
                    Err(error) => failure(id, ErrorCode::INVALID_PARAMS, error.to_string()),
                }
            },
            (Phase::Running, "workspace/textDocumentContent") => {
                match serde_json::from_value::<ContentParams>(params) {
                    Ok(ContentParams { uri }) => match uri.viewed() {
                        None => failure(
                            id,
                            ErrorCode::INVALID_PARAMS,
                            format!("`{uri}` names no document's syntax tree"),
                        ),
                        Some(viewed) => match workspace.view(&viewed, self.peer) {
                            Maybe::Present(document) => {
                                let tree = document.text.tree().clone();
                                if self.viewer.0 {
                                    let _added = self.viewing.insert((viewed, uri));
                                }
                                success(id, Answer::Content(tree))
                            },
                            Maybe::Absent(_) => failure(
                                id,
                                ErrorCode::REQUEST_FAILED,
                                format!("no document is open at `{viewed}`"),
                            ),
                        },
                    },
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
    ///   names a verbosity or a presentation spelling other than this
    ///   connection's takes them, then republishes every copy this connection
    ///   holds, in URI order, at its version, to this connection alone, logging
    ///   one timing line each; otherwise, one that names a zero interval
    ///   publishes what each copy holds back, as [`Server::release`] states,
    ///   and one naming neither changes nothing. A running-state `initialized`
    ///   from a client that watches files asks it, in one
    ///   `client/registerCapability` request, to watch every gandr source for
    ///   `workspace/didChangeWatchedFiles`; from any other client it sends
    ///   nothing. A running-state watched-files change rechecks every copy this
    ///   connection holds whose closure, at its last judgement, named a changed
    ///   file no connection holds, as [`named_path`] names it, and republishes
    ///   each in URI order, at its version, to this connection alone, logging
    ///   one timing line each; a copy whose closure names none is untouched.
    ///   Each import is judged as the editors hold it, as [`Workspace`] states:
    ///   after an open, a change or a close of a copy whose file some copy's
    ///   closure names, every copy this connection holds whose closure names it
    ///   is rechecked and republished after the copy's own publication, and
    ///   every other hub connection whose copies name it hears it changed. When
    ///   that rechecks a copy for what its closure names, a client that
    ///   refreshes its semantic tokens is then asked for them again, once.
    ///   Unknown, malformed and out-of-phase notifications leave documents
    ///   alone.
    /// - provides: document synchronization, configuration, file watching, the
    ///   folders the client opens and termination: a folder opened is a root of
    ///   the path table while this connection holds it open.
    /// - fails: unreadable parameters and changes to documents this connection
    ///   holds no copy of are ignored, except a folder change that does not
    ///   read from a client that lists its workspace folders, which asks for
    ///   them whole.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — open/change/close, empty change lists, unknown URIs,
    ///   malformed notifications and each lifecycle phase distinguish extra
    ///   responses, wrong versions and destructive updates through exact token
    ///   streams, publications and endings; a watched sibling's change, a
    ///   missing import written and an unrelated file distinguish the copies
    ///   rechecked through exact publications.
    /// - witness: `server::tests::synchronisation_publishes_and_close_clears`
    /// - witness: `server::tests::the_lifecycle_admits_requests_in_the_protocol_order`
    /// - witness: `server::tests::ignored_messages_and_empty_changes_preserve_document_text`
    /// - witness: `server::tests::ranged_changes_edit_the_held_text_in_order`
    /// - witness: `server::tests::a_configuration_change_republishes_at_its_verbosity`
    /// - witness: `server::tests::a_configuration_change_reanswers_hovers_in_its_form`
    /// - witness: `server::tests::a_presentation_spelling_respells_hovers_and_diagnostics_782`
    /// - witness: `server::tests::two_connections_hold_their_own_copies`
    /// - witness: `server::tests::a_watching_client_is_asked_to_watch_every_source`
    /// - witness: `server::tests::a_changed_file_rechecks_the_copies_whose_closure_names_it`
    /// - witness: `server::tests::an_editor_s_copy_shadows_the_disk_for_its_importers`
    /// - witness: `server::tests::a_folder_is_searched_while_the_client_holds_it_open`
    /// - witness: `server::tests::an_unread_folder_change_lists_the_folders_whole`
    /// - witness: `server::tests::a_file_operation_rechecks_the_copies_whose_closure_names_it`
    #[spec(
        captures: [phase = self.phase, count = workspace.documents.len()],
        ensures: |ret| {
            let published = ret.messages.iter().filter(|message| matches!(**message,
                Outgoing::Notification { params: Notified::Published(_), .. })).count();
            self.phase == phase
            && (ret.messages.len() <= 1
                || matches!(method.as_ref(), "textDocument/didOpen" | "textDocument/didChange" | "textDocument/didClose"
                    | "workspace/didChangeConfiguration" | "workspace/didChangeWatchedFiles" | "initialized"
                    | "workspace/didCreateFiles" | "workspace/didDeleteFiles" | "workspace/didRenameFiles"))
            && match method.as_ref() {
                "textDocument/didOpen" | "textDocument/didChange" | "workspace/didChangeWatchedFiles"
                | "workspace/didCreateFiles" | "workspace/didDeleteFiles" | "workspace/didRenameFiles" =>
                    ret.log.len() == published,
                "textDocument/didClose" => ret.log.len() == published.saturating_sub(1),
                "workspace/didChangeConfiguration" => ret.log.len() <= published,
                _ => ret.log.is_empty(),
            }
            && ret.flow == if method.as_ref() == "exit" { Flow::Exit(self.closed()) } else { Flow::Continue }
            && if ret.messages.is_empty() { workspace.documents.len() == count } else {
                phase == Phase::Running && ret.messages.iter().all(|message| match *message {
                    Outgoing::Notification { params: Notified::Published(ref params), .. } => {
                        let current = workspace.documents.get(&params.uri).is_some_and(|held| matches!(held.own(self.peer),
                            Maybe::Present(document) if params.version == Some(document.version)));
                        match method.as_ref() {
                            "textDocument/didOpen" | "textDocument/didChange" | "workspace/didChangeConfiguration"
                            | "workspace/didChangeWatchedFiles" | "workspace/didCreateFiles" | "workspace/didDeleteFiles"
                            | "workspace/didRenameFiles" => current,
                            "textDocument/didClose" => current || (params.version.is_none() && params.diagnostics.is_empty()
                                && workspace.documents.get(&params.uri)
                                    .is_none_or(|held| matches!(held.own(self.peer), Maybe::Absent(_)))),
                            _ => false,
                        }
                    },
                    Outgoing::Notification { params: Notified::Told(_), .. } =>
                        matches!(method.as_ref(), "initialized" | "workspace/didChangeConfiguration"),
                    Outgoing::Request { method: called, .. } => match method.as_ref() {
                        "initialized" => (called == "client/registerCapability" && self.watching.0)
                            || (called == "workspace/configuration" && self.pulling.0),
                        "workspace/didChangeConfiguration" => called == "workspace/configuration" && self.pulling.0,
                        "workspace/didChangeWorkspaceFolders" => {
                            called == "workspace/workspaceFolders" && self.listing.0
                        },
                        "textDocument/didOpen" | "textDocument/didChange" | "textDocument/didClose"
                        | "workspace/didChangeWatchedFiles" | "workspace/didCreateFiles"
                        | "workspace/didDeleteFiles" | "workspace/didRenameFiles" => {
                            called == "workspace/semanticTokens/refresh" && self.refreshing.tokens
                        },
                        _ => false,
                    },
                    Outgoing::Notification { params: Notified::Traced(_), .. } | Outgoing::Success { .. }
                    | Outgoing::Failure { .. } | Outgoing::Progress(_) => false,
                })
            }
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
                let version = text_document.version;
                let (uri, mut held, first) = if let Some((uri, held)) =
                    workspace.documents.remove_entry(&text_document.uri)
                {
                    (uri, held, false)
                }
                else {
                    let uri = text_document.uri;
                    let path = named_path(&uri.path());
                    let _indexed = workspace.paths.insert(path.clone(), uri.clone());
                    let held = Held {
                        latest: self.peer,
                        document: Document::opened(&uri, version),
                        others: BTreeMap::new(),
                        path,
                    };
                    (uri, held, true)
                };
                held.take_up(self.peer, &uri, version);
                let document = &mut held.document;
                document.version = version;
                document.text.replace(text_document.text);
                document.caret = Maybe::Absent(uncareted::Absent::Unranged);
                document.proposals.clear();
                let mut outcome = synchronised(
                    &uri,
                    document,
                    &workspace.shadowing(self.peer),
                    self.verbosity,
                    self.style.spelling,
                    self.quiet,
                );
                // The first copy of a file stands in for its disk text, so
                // what its importers read changes only where the two differ.
                let named = workspace.named(&held.path).filter(|path| {
                    !first || differs_from_disk(path, held.document.text.source()).0
                });
                let _kept = workspace.documents.insert(uri, held);
                for message in &outcome.messages {
                    workspace.published_by(self.peer, message);
                }
                if let Some(path) = named {
                    self.reclosed(workspace, &path, &mut outcome);
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
                let Some((uri, mut held)) = workspace.documents.remove_entry(&text_document.uri)
                else {
                    return Outcome::quiet();
                };
                held.promote(self.peer);
                let mut outcome = match held.own_mut(self.peer) {
                    Maybe::Present(document) => {
                        document.version = text_document.version;
                        document.proposals.clear();
                        for change in content_changes {
                            document.caret = document.text.apply(change);
                        }
                        synchronised(
                            &uri,
                            document,
                            &workspace.shadowing(self.peer),
                            self.verbosity,
                            self.style.spelling,
                            self.quiet,
                        )
                    },
                    Maybe::Absent(_) => Outcome::quiet(),
                };
                let named = if outcome.messages.is_empty() {
                    None
                }
                else {
                    workspace.named(&held.path)
                };
                let _kept = workspace.documents.insert(uri, held);
                for message in &outcome.messages {
                    workspace.published_by(self.peer, message);
                }
                if let Some(path) = named {
                    self.reclosed(workspace, &path, &mut outcome);
                }
                outcome
            },
            (Phase::Running, "textDocument/didClose") => {
                let Ok(DocumentParams { text_document }) = serde_json::from_value(params)
                else {
                    return Outcome::quiet();
                };
                let _forgotten = self.streams.remove(&text_document.uri);
                let _unoffered = self.announced.remove(&text_document.uri);
                self.viewing
                    .retain(|&(ref viewed, _)| *viewed != text_document.uri);
                let named = match workspace.documents.remove_entry(&text_document.uri) {
                    Some((uri, held)) => {
                        // The disk stands in for the last copy, so what its
                        // importers read changes only where the two differ.
                        let named = workspace.named(&held.path);
                        let differs = named.as_deref().map_or(Differs(false), |path| {
                            differs_from_disk(path, held.document.text.source())
                        });
                        let forgotten = workspace.let_go(uri, held, self.peer);
                        named.filter(|_| forgotten.is_none() || differs.0)
                    },
                    None => None,
                };
                let mut outcome = Outcome::say(publish(PublishParams {
                    uri: text_document.uri,
                    version: None,
                    diagnostics: Vec::new(),
                }));
                if let Some(path) = named {
                    self.reclosed(workspace, &path, &mut outcome);
                }
                outcome
            },
            (Phase::Running, "workspace/didChangeConfiguration") => {
                match serde_json::from_value::<ConfigurationParams>(params) {
                    Err(error) => Outcome::say(unread_settings(&error)),
                    Ok(ConfigurationParams {
                        settings:
                            Some(Sections {
                                gandr: Some(settings),
                            }),
                    }) => self.configured(workspace, settings),
                    Ok(_) if self.pulling.0 => Outcome::say(pull(self.next_request())),
                    Ok(_) => Outcome::quiet(),
                }
            },
            (Phase::Running, "initialized") => {
                let mut outcome = Outcome::quiet();
                if self.watching.0 {
                    outcome
                        .messages
                        .push(register(RegistrationParams::watched_files()));
                }
                if self.pulling.0 {
                    let sent = self.next_request();
                    outcome.messages.push(pull(sent));
                }
                if let Err(error) = grammar().and_then(|_| forms()) {
                    outcome.messages.push(tell(Told::Shown, MessageParams {
                        kind: MessageType::ERROR,
                        message: format!(
                            "gandr's grammar did not build, so no request is answered: {error}"
                        ),
                    }));
                }
                outcome
            },
            (Phase::Running, "$/setTrace") => {
                if let Ok(SetTraceParams { value }) = serde_json::from_value(params) {
                    self.trace = value;
                }
                Outcome::quiet()
            },
            (Phase::Running, "workspace/didChangeWatchedFiles") => {
                let Ok(WatchedFilesParams { changes }) = serde_json::from_value(params)
                else {
                    return Outcome::quiet();
                };
                self.resynchronise(
                    workspace,
                    Picks::Naming(&changed_paths(&changes), Origin::Disk),
                )
            },
            (Phase::Running, "workspace/didCreateFiles" | "workspace/didDeleteFiles") => {
                let Ok(FilesParams { files }) = serde_json::from_value(params)
                else {
                    return Outcome::quiet();
                };
                self.resynchronise(workspace, Picks::Under(&changed_paths(&files)))
            },
            (Phase::Running, "workspace/didRenameFiles") => {
                let Ok(RenameFilesParams { files }) = serde_json::from_value(params)
                else {
                    return Outcome::quiet();
                };
                self.resynchronise(workspace, Picks::Under(&renamed_paths(&files)))
            },
            (Phase::Running, "workspace/didChangeWorkspaceFolders") => {
                let Ok(FoldersChangedParams { event }) = serde_json::from_value(params)
                else {
                    return if self.listing.0 {
                        Outcome::say(list_folders(self.next_request()))
                    }
                    else {
                        Outcome::quiet()
                    };
                };
                workspace.unrooted(self.peer, &event.removed());
                workspace.rooted(self.peer, &event.added());
                Outcome::quiet()
            },
            (Phase::Running, "window/workDoneProgress/cancel") => {
                if let Ok(CancelProgressParams { token }) = serde_json::from_value(params) {
                    self.cancel(token);
                }
                Outcome::quiet()
            },
            (Phase::Waiting | Phase::Running | Phase::ShuttingDown, _) => Outcome::quiet(),
        }
    }

    /// Apply the `gandr` `settings` this connection's client gave, pushed or
    /// pulled: the quiet interval and the form at once, and the verbosity and
    /// spelling by republishing every copy it holds when either changed.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each setting `settings` names is this connection's; the
    ///   copies are republished when the verbosity or the spelling changed, and
    ///   released of what they hold back when the quiet interval is zero;
    ///   nothing is written otherwise.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as `workspace/didChangeConfiguration`, and a pulled
    ///   section applied as a pushed one.
    /// - witness: `server::tests::a_configuration_change_republishes_at_its_verbosity`
    /// - witness: `server::tests::a_pulled_setting_applies_as_a_pushed_one`
    #[spec(ensures: |ret| ret.log.len() <= ret.messages.len()
        && settings.verbosity().is_none_or(|verbosity| self.verbosity == verbosity))]
    fn configured(
        &mut self,
        workspace: &mut Workspace,
        settings: Settings,
    ) -> Outcome
    {
        if let Some(quiet) = settings.quiet() {
            self.quiet = quiet;
        }
        if let Some(form) = settings.form() {
            self.style.form = form;
        }
        let mut outcome = Outcome::quiet();
        let verbosity = settings
            .verbosity()
            .filter(|&verbosity| verbosity != self.verbosity);
        let spelling = settings
            .spelling()
            .filter(|&spelling| spelling != self.style.spelling);
        if verbosity.is_none() && spelling.is_none() {
            if settings.quiet().is_some_and(|quiet| quiet.is_zero()) {
                let uris: Vec<DocumentUri> = workspace.documents.keys().cloned().collect();
                for uri in &uris {
                    outcome.messages.extend(self.release(workspace, uri));
                }
            }
            return outcome;
        }
        self.verbosity = verbosity.unwrap_or(self.verbosity);
        self.style.spelling = spelling.unwrap_or(self.style.spelling);
        let republished = self.resynchronise(workspace, Picks::Every);
        outcome.messages.extend(republished.messages);
        outcome.log.extend(republished.log);
        outcome
    }

    /// Handle the client's answer `result` to the request of this
    /// connection's that `id` names: a pull's settings applied, a choice
    /// recorded, a fill offered and chosen shown, the folders listed made the
    /// roots, an edit the client did not apply logged, every other answer
    /// read and left.
    ///
    /// # Specification
    /// - requires: nothing; any response is admissible input.
    /// - ensures: a pull answered with a `gandr` section that reads applies it
    ///   as [`Server::configured`] does, and one that does not read is logged
    ///   to the client as a warning; a pull answered with null or an error
    ///   applies nothing; a choice this connection put is recorded as chosen
    ///   when the answer names an action, dismissed otherwise, and when it
    ///   offered a kept fill and the answer names [`SHOW_FILL`], the client is
    ///   asked to show the fill's document with its range selected; a list of
    ///   workspace folders replaces the folders this connection holds open, as
    ///   roots, null replacing them with none and an error leaving them; an
    ///   edit the client answers it did not apply is logged to it as a warning,
    ///   with its reason when it gave one; nothing else changes.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a pull answered with settings, with a section that
    ///   does not read, with null and with an error; a choice answered with an
    ///   action, null and an error; an offer answered with its action and
    ///   dismissed; folders listed; an edit applied and one refused; a
    ///   registration's answer.
    /// - witness: `server::tests::a_pulled_setting_applies_as_a_pushed_one`
    /// - witness: `server::tests::a_choice_put_to_the_user_reads_its_answer`
    /// - witness: `server::tests::a_fill_kept_elsewhere_is_offered_to_its_editor_once`
    /// - witness: `server::tests::an_unread_folder_change_lists_the_folders_whole`
    /// - witness: `server::tests::a_lens_applies_its_one_checked_fill`
    #[spec(ensures: |ret| ret.log.len() <= ret.messages.len() && ret.flow == Flow::Continue)]
    fn response(
        &mut self,
        workspace: &mut Workspace,
        id: &RequestId,
        result: Option<Value>,
    ) -> Outcome
    {
        match Answered::of(id) {
            Answered::Pulled => {
                let Some(result) = result.filter(|result| !result.is_null())
                else {
                    return Outcome::quiet();
                };
                match serde_json::from_value::<Vec<Option<Settings>>>(result) {
                    Err(error) => Outcome::say(unread_settings(&error)),
                    Ok(sections) => sections
                        .into_iter()
                        .next()
                        .flatten()
                        .map_or_else(Outcome::quiet, |settings| {
                            self.configured(workspace, settings)
                        }),
                }
            },
            Answered::Chosen => {
                let answer = result
                    .and_then(|result| serde_json::from_value::<Option<MessageAction>>(result).ok())
                    .flatten();
                let shown = self
                    .offered
                    .iter()
                    .position(|&(ref asked, ..)| asked == id)
                    .map(|at| self.offered.swap_remove(at))
                    .filter(|_| {
                        answer
                            .as_ref()
                            .is_some_and(|action| action.title == SHOW_FILL)
                    });
                if let Some(&mut (_, ref mut choice)) = self
                    .choices
                    .iter_mut()
                    .find(|&&mut (ref asked, _)| asked == id)
                {
                    *choice = answer.map_or(Choice::Dismissed, Choice::Chose);
                }
                shown.map_or_else(Outcome::quiet, |(_, uri, selection)| {
                    Outcome::say(show(
                        ShowDocumentParams {
                            uri,
                            take_focus: true,
                            selection,
                        },
                        self.next_request(),
                    ))
                })
            },
            Answered::Listed => {
                if let Some(folders) = result.and_then(|result| {
                    serde_json::from_value::<Option<Vec<WorkspaceFolder>>>(result).ok()
                }) {
                    workspace.rerooted(
                        self.peer,
                        &folders.as_deref().map_or_else(Vec::new, folder_roots),
                    );
                }
                Outcome::quiet()
            },
            Answered::Applied => result
                .and_then(|result| serde_json::from_value::<AppliedEdit>(result).ok())
                .filter(|answer| !answer.applied)
                .map_or_else(Outcome::quiet, |refused| {
                    Outcome::say(tell(Told::Logged, MessageParams {
                        kind: MessageType::WARNING,
                        message: format!(
                            "the editor did not apply the checked fill: {}",
                            refused
                                .failure_reason
                                .as_deref()
                                .unwrap_or("it gave no reason")
                        ),
                    }))
                }),
            Answered::Other => Outcome::quiet(),
        }
    }

    /// The traces of `log` this connection's client asked for: one
    /// `$/logTrace` per line at [`Trace::Messages`], naming the document and
    /// the version it reached, with what rechecking it cost besides at
    /// [`Trace::Verbose`]; none at [`Trace::Off`].
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: no trace at `off`; one per line, in order, otherwise, its
    ///   detail present exactly at `verbose`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an open traced at each level, and after the client
    ///   sets another.
    /// - witness: `server::tests::the_server_log_is_traced_at_the_level_the_client_sets`
    #[spec(ensures: |ret| ret.len() == if self.trace == Trace::Off { 0 } else { log.len() })]
    #[inline]
    #[must_use]
    pub fn traced(
        &self,
        log: &[Logged],
    ) -> Vec<Outgoing>
    {
        if self.trace == Trace::Off {
            return Vec::new();
        }
        log.iter()
            .map(|line| {
                trace(TraceParams {
                    message: format!("{} at version {}", line.uri, line.version),
                    verbose: (self.trace == Trace::Verbose).then(|| line.timing.to_string()),
                })
            })
            .collect()
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

    /// Each document whose latest copy `peer` holds and that keeps a fill,
    /// with that copy's version and the fills it keeps, in order.
    ///
    /// # Specification
    /// trivial.
    fn proposed_to(
        &self,
        peer: Peer,
    ) -> impl Iterator<Item = (&DocumentUri, DocumentVersion, &[Proposal])>
    {
        self.documents
            .iter()
            .filter(move |&(_, held)| held.latest == peer && !held.document.proposals.is_empty())
            .map(|(uri, held)| {
                (
                    uri,
                    held.document.version,
                    held.document.proposals.as_slice(),
                )
            })
    }

    /// Make `roots` the folders `peer` holds open in the path table, in
    /// place of every folder it held open before.
    ///
    /// # Specification
    /// trivial.
    fn rerooted(
        &self,
        peer: Peer,
        roots: &[PathBuf],
    )
    {
        let mut files = self.files.borrow_mut();
        files.depart(peer);
        for root in roots {
            files.root(peer, root);
        }
    }

    /// Add each of `roots`, a folder `peer` opened, to the path table.
    ///
    /// # Specification
    /// trivial.
    fn rooted(
        &self,
        peer: Peer,
        roots: &[PathBuf],
    )
    {
        let mut files = self.files.borrow_mut();
        for root in roots {
            files.root(peer, root);
        }
    }

    /// Withdraw each of `roots`, a folder `peer` closed, from the path table.
    ///
    /// # Specification
    /// trivial.
    fn unrooted(
        &self,
        peer: Peer,
        roots: &[PathBuf],
    )
    {
        let mut files = self.files.borrow_mut();
        for root in roots {
            files.unroot(peer, root);
        }
    }

    /// The tokens of the copy of the document at `uri` that `peer` is
    /// answered from, in `window`, each written use classified by what its
    /// judgement resolved it to.
    ///
    /// # Specification
    /// - requires: nothing; an unknown URI and any range are admitted.
    /// - ensures: an unknown document yields Nothing; a held document yields a
    ///   token stream, restricted to overlapping whole spans for a range
    ///   request. Empty and inverted ranges yield an empty stream, not Nothing.
    ///   A whole-document stream carries its result id; a range's carries none.
    ///   A copy with a session sends its spans as [`classified`] classifies
    ///   them over its type table, a name the table records as unresolved sent
    ///   as such; one without sends the highlighter's spans.
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
    /// - witness: `server::tests::a_use_is_sent_as_what_it_refers_to`
    #[spec(ensures: |ret| match ret {
        Answer::Nothing => !self.documents.contains_key(uri),
        Answer::Tokens(ref tokens) => self.documents.contains_key(uri)
            && tokens.data.as_ref().len().is_multiple_of(5)
            && tokens.result_id.is_some() == matches!(window, Window::Whole)
            && match window { Window::Within(range) if range.start >= range.end => tokens.data.as_ref().is_empty(), Window::Whole | Window::Within(_) => true },
        Answer::Initialize(_) | Answer::Completions(_) | Answer::Resolved(_) | Answer::Signatures(_) | Answer::Inline(_) | Answer::Symbols(_) | Answer::Folds(_) | Answer::Selections(_)
            | Answer::Hover(_) | Answer::Links(_) | Answer::Locations(_) | Answer::Edits(_) | Answer::Lenses(_) | Answer::Lens(_)
            | Answer::Actions(_) | Answer::Found(_) | Answer::Highlights(_) | Answer::Renaming(_) | Answer::Renamed(_)
            | Answer::Imports(_) | Answer::Mirrored(_) | Answer::Unchanged(_) | Answer::Deltas(_) | Answer::Content(_) => false,
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
        let written = document.text.reading().spans();
        let judged = document.session.as_ref().map_or_else(
            |_| Resolved {
                spans: written.to_vec(),
                unresolved: Vec::new(),
            },
            |session| {
                classified(
                    written,
                    document
                        .text
                        .hovering(&uri.path(), session, &self.shadowing(peer))
                        .table(),
                )
            },
        );
        let spans = match window {
            Window::Whole => judged.spans,
            Window::Within(range) => overlapping(
                &judged.spans,
                range.start.byte(&index),
                range.end.byte(&index),
            ),
        };
        let data = encode(&index, &spans, &judged.unresolved);
        Answer::Tokens(SemanticTokens {
            result_id: matches!(window, Window::Whole).then(|| data.result_id()),
            data,
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
        Answer::Initialize(_) | Answer::Tokens(_) | Answer::Completions(_) | Answer::Resolved(_) | Answer::Signatures(_) | Answer::Symbols(_) | Answer::Folds(_) | Answer::Selections(_)
            | Answer::Hover(_) | Answer::Links(_) | Answer::Locations(_) | Answer::Edits(_) | Answer::Lenses(_) | Answer::Lens(_)
            | Answer::Actions(_) | Answer::Found(_) | Answer::Highlights(_) | Answer::Renaming(_) | Answer::Renamed(_)
            | Answer::Imports(_) | Answer::Mirrored(_) | Answer::Unchanged(_) | Answer::Deltas(_) | Answer::Content(_) => false,
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
                    document
                        .text
                        .hovering(&uri.path(), session, &self.shadowing(peer)),
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

    /// What a completion request at `position` of the copy of the document at
    /// `uri` that `peer` is answered from offers, its types spelled in the
    /// printer style and its label details given as `presented` says.
    ///
    /// # Specification
    /// - requires: nothing; an unknown URI and any position are admitted.
    /// - ensures: an unknown document, and one whose session or grammar did not
    ///   build, yields Nothing; otherwise the list [`completions`] answers off
    ///   the copy's text and what it keeps for its hovers, made now when no
    ///   request has asked since the text last changed, as `presented` says.
    /// - provides: the answer to `textDocument/completion`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`completions`], and an unknown document answers
    ///   `null`.
    /// - witness: `server::tests::completion_answers_the_names_a_word_may_complete_to_806`
    #[spec(ensures: |ret| matches!(ret, Answer::Nothing | Answer::Completions(_))
        && (self.documents.contains_key(uri) || matches!(ret, Answer::Nothing)))]
    fn completion(
        &self,
        uri: &DocumentUri,
        peer: Peer,
        position: Position,
        presented: (gandr_surface_pretty::Style, LabelsDetailed, TakesSnippets),
    ) -> Answer
    {
        let Maybe::Present(document) = self.view(uri, peer)
        else {
            return Answer::Nothing;
        };
        let (Ok(session), Ok(grammar), Ok(forms)) = (document.session.as_ref(), grammar(), forms())
        else {
            return Answer::Nothing;
        };
        Answer::Completions(completions(
            grammar,
            forms,
            document.text.source(),
            document
                .text
                .hovering(&uri.path(), session, &self.shadowing(peer)),
            (uri, position),
            presented,
        ))
    }

    /// `item`, offered by a completion request, resolved off the copy of the
    /// document it names that `peer` is answered from.
    ///
    /// # Specification
    /// - requires: nothing; any item is admissible input.
    /// - ensures: an item naming no document, one naming a document no
    ///   connection holds, and one whose copy's session or grammar did not
    ///   build, answered as it came; otherwise [`resolved`] off the copy's text
    ///   and what it keeps for its hovers, made now when no request has asked
    ///   since the text last changed.
    /// - provides: the answer to `completionItem/resolve`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`resolved`], and an item offered in a document
    ///   since closed answers as it came.
    /// - witness: `server::tests::a_resolved_completion_reads_the_declared_head`
    #[spec(ensures: |ret| matches!(ret, Answer::Resolved(_)))]
    fn resolve_completion(
        &self,
        item: CompletionItem,
        peer: Peer,
    ) -> Answer
    {
        let held = item.data.as_ref().map(|data| data.uri.clone());
        let viewed = held.as_ref().map(|uri| (uri, self.view(uri, peer)));
        let Some((uri, Maybe::Present(document))) = viewed
        else {
            return Answer::Resolved(Box::new(item));
        };
        let Ok(session) = document.session.as_ref()
        else {
            return Answer::Resolved(Box::new(item));
        };
        Answer::Resolved(Box::new(resolved(
            item,
            document
                .text
                .hovering(&uri.path(), session, &self.shadowing(peer)),
        )))
    }

    /// What a workspace-symbol request for `query` answers `peer`: the names
    /// the open documents' import closures declare, each read off the copy
    /// `peer` is answered from.
    ///
    /// # Specification
    /// - requires: nothing; any query is admitted.
    /// - ensures: every name [`crate::search::Found::matching`] finds for
    ///   `query` in a held copy's closure, at most [`FOUND_HELD`], ascending by
    ///   name folded to lower case, then by name, document and range. A name an
    ///   open document writes is found where that document's copy writes it,
    ///   and once; a name a sibling no document holds open writes is found at
    ///   the sibling's path, once however many closures read it. Each copy's
    ///   index is made now when no request has asked since its text last
    ///   changed.
    /// - provides: the answer to `workspace/symbol`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a name a held document writes, a sibling's names read
    ///   by two importers, a held sibling's own copy shadowing the disk, and a
    ///   query no name holds each distinguish a missing, a doubled or a stale
    ///   symbol.
    /// - witness: `server::tests::workspace_symbols_find_the_names_the_open_closures_declare`
    #[spec(ensures: |ret| matches!(ret, Answer::Found(ref found) if found.len() <= FOUND_HELD))]
    fn symbols(
        &self,
        peer: Peer,
        query: SourceText<'_>,
    ) -> Answer
    {
        let shadows = self.shadowing(peer);
        let mut siblings: BTreeSet<(DocumentUri, Range)> = BTreeSet::new();
        let mut found: Vec<(String, SymbolInformation)> = Vec::new();
        for uri in self.documents.keys() {
            let Maybe::Present(document) = self.view(uri, peer)
            else {
                continue;
            };
            let Ok(session) = document.session.as_ref()
            else {
                continue;
            };
            let hovering = document.text.hovering(&uri.path(), session, &shadows);
            let own = hovering.table().own_source();
            for entry in hovering.found().matching(query) {
                let target = if entry.source == own {
                    uri.clone()
                }
                else {
                    let Some(path) = hovering
                        .source_path(entry.source)
                        .filter(|path| !self.paths.contains_key(*path))
                    else {
                        continue;
                    };
                    let Some(target) = DocumentUri::of_path(path)
                    else {
                        continue;
                    };
                    if !siblings.insert((target.clone(), entry.range)) {
                        continue;
                    }
                    target
                };
                found.push((entry.folded.clone(), SymbolInformation {
                    name: entry.name.clone(),
                    kind: entry.kind,
                    location: Location {
                        uri: target,
                        range: entry.range,
                    },
                    container_name: entry.container.clone(),
                }));
            }
        }
        found.sort_unstable_by(|first, second| {
            (
                &first.0,
                &first.1.name,
                &first.1.location.uri,
                first.1.location.range,
            )
                .cmp(&(
                    &second.0,
                    &second.1.name,
                    &second.1.location.uri,
                    second.1.location.range,
                ))
        });
        found.truncate(FOUND_HELD);
        Answer::Found(found.into_iter().map(|(_, symbol)| symbol).collect())
    }

    /// What a signature-help request at `position` of the copy of the document
    /// at `uri` that `peer` is answered from answers, to a client taking a
    /// parameter as its place in the label when `offsets` holds.
    ///
    /// # Specification
    /// - requires: nothing; an unknown URI and any position are admitted.
    /// - ensures: an unknown document, and one whose session did not build,
    ///   yields Nothing; otherwise what [`help`] answers off the copy's text,
    ///   its reading and what it keeps for its hovers, each made now when no
    ///   request has asked since the text last changed.
    /// - provides: the answer to `textDocument/signatureHelp`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`help`], and an unknown document answers `null`.
    /// - witness: `server::tests::signature_help_answers_the_declared_head_of_the_call`
    #[spec(ensures: |ret| matches!(ret, Answer::Nothing | Answer::Signatures(_))
        && (self.documents.contains_key(uri) || matches!(ret, Answer::Nothing)))]
    fn signature_help(
        &self,
        uri: &DocumentUri,
        peer: Peer,
        position: Position,
        offsets: LabelOffsets,
    ) -> Answer
    {
        let Maybe::Present(document) = self.view(uri, peer)
        else {
            return Answer::Nothing;
        };
        document
            .session
            .as_ref()
            .map_or(Answer::Nothing, |session| {
                help(
                    document.text.source(),
                    document.text.reading(),
                    document
                        .text
                        .hovering(&uri.path(), session, &self.shadowing(peer)),
                    position,
                    offsets,
                )
            })
    }

    /// What a `goto` request at `position` of the copy of the document at
    /// `uri` that `peer` is answered from answers, to a client taking links as
    /// `linked` says.
    ///
    /// # Specification
    /// - requires: nothing; an unknown URI and any position are admitted.
    /// - ensures: an unknown document, and one whose session holds no grammar,
    ///   yields Nothing; otherwise the targets [`targets`] answers off the
    ///   copy's text and what it keeps for its hovers, made now when no request
    ///   has asked since the text last changed.
    /// - provides: the answer to `textDocument/definition` and
    ///   `textDocument/typeDefinition`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`targets`], and an unknown document answers
    ///   `null`.
    /// - witness: `server::tests::definition_answers_what_a_use_refers_to_795`
    /// - witness: `server::tests::type_definition_answers_the_family_a_use_s_type_names_795`
    #[spec(ensures: |ret| matches!(ret, Answer::Nothing | Answer::Links(_) | Answer::Locations(_))
        && (self.documents.contains_key(uri) || matches!(ret, Answer::Nothing)))]
    fn definition(
        &self,
        uri: &DocumentUri,
        peer: Peer,
        position: Position,
        goto: Goto,
        linked: Linked,
    ) -> Answer
    {
        let Maybe::Present(document) = self.view(uri, peer)
        else {
            return Answer::Nothing;
        };
        document
            .session
            .as_ref()
            .map_or(Answer::Nothing, |session| {
                targets(
                    document.text.source(),
                    uri,
                    document
                        .text
                        .hovering(&uri.path(), session, &self.shadowing(peer)),
                    position,
                    goto,
                    linked,
                )
            })
    }

    /// What a highlight request at `position` of the copy of the document at
    /// `uri` that `peer` is answered from answers.
    ///
    /// # Specification
    /// - requires: nothing; an unknown URI and any position are admitted.
    /// - ensures: an unknown document, and one whose session holds no grammar,
    ///   yields Nothing; otherwise the highlights [`highlights`] answers off
    ///   the copy's text and what it keeps for its hovers, made now when no
    ///   request has asked since the text last changed.
    /// - provides: the answer to `textDocument/documentHighlight`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`highlights`], and an unknown document answers
    ///   `null`.
    /// - witness: `server::tests::a_highlight_marks_a_name_s_declaration_and_its_uses`
    #[spec(ensures: |ret| matches!(ret, Answer::Nothing | Answer::Highlights(_))
        && (self.documents.contains_key(uri) || matches!(ret, Answer::Nothing)))]
    fn highlight(
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
        document
            .session
            .as_ref()
            .map_or(Answer::Nothing, |session| {
                highlights(
                    document.text.source(),
                    document
                        .text
                        .hovering(&uri.path(), session, &self.shadowing(peer)),
                    position,
                )
            })
    }

    /// What a linked-editing request at `position` of the copy of the document
    /// at `uri` that `peer` is answered from answers.
    ///
    /// # Specification
    /// - requires: nothing; an unknown URI and any position are admitted.
    /// - ensures: an unknown document, and one whose session holds no grammar,
    ///   yields Nothing; otherwise what [`mirrored`] answers off the copy's
    ///   text and what it keeps for its hovers.
    /// - provides: the answer to `textDocument/linkedEditingRange`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`mirrored`], and an unknown document answers
    ///   `null`.
    /// - witness: `server::tests::linked_editing_mirrors_a_binder_within_its_declaration`
    #[spec(ensures: |ret| matches!(ret, Answer::Nothing | Answer::Mirrored(_))
        && (self.documents.contains_key(uri) || matches!(ret, Answer::Nothing)))]
    fn linked_editing(
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
        document
            .session
            .as_ref()
            .map_or(Answer::Nothing, |session| {
                mirrored(
                    document.text.source(),
                    document
                        .text
                        .hovering(&uri.path(), session, &self.shadowing(peer)),
                    position,
                )
            })
    }

    /// What a reference request at `position` of the copy of the document at
    /// `uri` that `peer` is answered from answers, the declaring name included
    /// when `context` asks for it.
    ///
    /// # Specification
    /// - requires: nothing; an unknown URI and any position are admitted.
    /// - ensures: an unknown document, and one whose session holds no grammar,
    ///   yields Nothing; otherwise, for the name [`placed`] places, when
    ///   `context` asks for it its declaring name first, then the name in its
    ///   declaration's other half when written in two, at the open document
    ///   whose path is the name's source when one is open and at that path
    ///   otherwise; then the uses of it each document [`Self::writers`] visits
    ///   makes, as [`located`] answers, in the order it visits them, the other
    ///   half left out. No name answers the empty list.
    /// - provides: the answer to `textDocument/references`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a sibling's name asked from an importer is found in
    ///   the sibling, in every open importer and in an importer no editor
    ///   holds, with its declaration when asked and without it otherwise; a
    ///   binder's uses stay in its document; a declaration written in two
    ///   halves answers both with its declaration and neither without; an
    ///   unknown document answers `null`.
    /// - witness: `server::tests::references_find_a_name_s_uses_in_every_open_document`
    /// - witness: `server::tests::references_leave_both_halves_out_with_the_declaration_1361`
    /// - witness: `server::tests::a_rename_rewrites_a_name_everywhere_it_is_written`
    #[spec(ensures: |ret| matches!(ret, Answer::Nothing | Answer::Locations(_))
        && (self.documents.contains_key(uri) || matches!(ret, Answer::Nothing)))]
    fn references(
        &self,
        uri: &DocumentUri,
        peer: Peer,
        position: Position,
        context: ReferenceContext,
    ) -> Answer
    {
        self.referring(uri, peer, position, context)
            .map_or(Answer::Nothing, Answer::Locations)
    }

    /// The locations [`Self::references`] answers, or none for an unknown
    /// document or one whose session holds no grammar.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: as [`Self::references`], its `Nothing` as none.
    /// - provides: what a reference request and a references lens count.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::references`].
    /// - witness: `server::tests::references_find_a_name_s_uses_in_every_open_document`
    /// - witness: `server::tests::a_references_lens_counts_a_name_s_uses_in_every_open_document`
    #[spec(ensures: |ret| self.documents.contains_key(uri) || ret.is_none())]
    fn referring(
        &self,
        uri: &DocumentUri,
        peer: Peer,
        position: Position,
        context: ReferenceContext,
    ) -> Option<Vec<Location>>
    {
        let shadows = self.shadowing(peer);
        let Maybe::Present(document) = self.view(uri, peer)
        else {
            return None;
        };
        let session = document.session.as_ref().ok()?;
        let Some(name) = placed(
            document.text.source(),
            &named_path(&uri.path()),
            document.text.hovering(&uri.path(), session, &shadows),
            position,
        )
        else {
            return Some(Vec::new());
        };
        let mut found = Vec::new();
        if context.include_declaration
            && let Some(range) = name.range
            && let Some(target) = self
                .paths
                .get(&name.path)
                .cloned()
                .or_else(|| DocumentUri::of_path(&name.path))
        {
            found.extend(
                core::iter::once(range)
                    .chain(name.second)
                    .map(|range| Location {
                        uri: target.clone(),
                        range,
                    }),
            );
        }
        let Ok(()) = self.writers::<Infallible>(&name, peer, &shadows, &mut |writer| {
            let declaring = writer.path == name.path.as_path();
            found.extend(
                located(
                    writer.text,
                    writer.uri,
                    writer.path,
                    writer.hovering,
                    &name.path,
                    name.named,
                )
                .into_iter()
                .filter(|location| !(declaring && Some(location.range) == name.second)),
            );
            Ok(())
        });
        Some(found)
    }

    /// What a code-lens request for the copy of the document at `uri` that
    /// `peer` is answered from answers: the lens over each range a model's
    /// kept proposals fill, and a references lens, unresolved, over each name
    /// the document declares.
    ///
    /// # Specification
    /// - requires: nothing; an unknown URI is admitted.
    /// - ensures: Nothing for an unknown document; otherwise the lenses
    ///   [`lenses`] answers for its proposals, given whether the client
    ///   `applies` edits, and one lens per range [`declared`] answers, carrying
    ///   the URI and the range's start as its data and no command, in range
    ///   order, a fill lens before a references lens over the same range. A
    ///   document whose session holds no grammar declares nothing.
    /// - provides: the answer to `textDocument/codeLens`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a document declaring two names and a constructor
    ///   lists a lens over each, with no command until it is resolved; a kept
    ///   fill still lists its own lens.
    /// - witness: `server::tests::a_references_lens_counts_a_name_s_uses_in_every_open_document`
    /// - witness: `server::tests::kept_proposals_reach_every_editor_surface`
    #[spec(ensures: |ret| matches!(ret, Answer::Nothing)
        || matches!(ret, Answer::Lenses(ref lenses) if lenses.is_sorted_by(|earlier, later| earlier.range <= later.range)
            && lenses.iter().all(|lens| lens.data.as_ref().is_none_or(|data|
                &data.uri == uri && lens.command.is_none() && data.position == lens.range.start))))]
    fn code_lenses(
        &self,
        uri: &DocumentUri,
        peer: Peer,
        applies: AppliesEdits,
    ) -> Answer
    {
        let shadows = self.shadowing(peer);
        let Maybe::Present(document) = self.view(uri, peer)
        else {
            return Answer::Nothing;
        };
        let mut found = lenses(uri, &document.proposals, applies);
        if let Ok(session) = document.session.as_ref() {
            found.extend(
                declared(
                    document.text.source(),
                    document.text.hovering(&uri.path(), session, &shadows),
                )
                .into_iter()
                .map(|range| CodeLens {
                    range,
                    command: None,
                    data: Some(LensData {
                        uri: uri.clone(),
                        position: range.start,
                    }),
                }),
            );
        }
        found.sort_by_key(|lens| lens.range);
        Answer::Lenses(found)
    }

    /// What a code-lens resolution of the references lens over `range`,
    /// counting the name `data` places, answers for `peer`: the lens titled
    /// with the number of uses a reference request finds, running the client's
    /// [`SHOW_REFERENCES`] with the URI, the position and those uses.
    ///
    /// # Specification
    /// - requires: nothing; an unknown URI is admitted.
    /// - ensures: the lens over `range` carrying `data`; its command titled `1
    ///   reference` or `N references` with the count of what
    ///   [`Self::referring`] answers at the position, the declaring name left
    ///   out, running [`SHOW_REFERENCES`] with the URI, the position and those
    ///   locations; no command when the document is not open.
    /// - provides: the answer to `codeLens/resolve` for a references lens.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a name used in its own document and in an open
    ///   importer counts both, a name used once is singular, and a lens whose
    ///   document was closed resolves to no command.
    /// - witness: `server::tests::a_references_lens_counts_a_name_s_uses_in_every_open_document`
    #[spec(ensures: |ret| matches!(ret, Answer::Lens(ref lens) if lens.range == range
        && lens.command.as_ref().is_none_or(|command| command.name == SHOW_REFERENCES
            && command.arguments.len() == 3_usize)))]
    fn resolve_lens(
        &self,
        range: Range,
        data: LensData,
        peer: Peer,
    ) -> Answer
    {
        let command = self
            .referring(&data.uri, peer, data.position, ReferenceContext {
                include_declaration: false,
            })
            .map(|found| Command {
                title: if found.len() == 1_usize {
                    String::from("1 reference")
                }
                else {
                    format!("{} references", found.len())
                },
                name: SHOW_REFERENCES,
                arguments: Vec::from([
                    serde_json::to_value(&data.uri).unwrap_or(Value::Null),
                    serde_json::to_value(data.position).unwrap_or(Value::Null),
                    serde_json::to_value(&found).unwrap_or(Value::Null),
                ]),
            });
        Answer::Lens(CodeLens {
            range,
            command,
            data: Some(data),
        })
    }

    /// Visit each document that may write the name `written` places, as
    /// `peer` is answered: every open document's copy, in URI order, then each
    /// source the path table finds importing the name's source, and that
    /// source itself, that no editor holds and whose file spells the name,
    /// read from disk and laid out with each import read as the editors hold
    /// it.
    ///
    /// # Specification
    /// - requires: `shadows` reads the copies `peer` is answered from.
    /// - ensures: `visit` is called once per document visited, in the order
    ///   above, until it fails; a document whose session holds no grammar, a
    ///   file that cannot be read and a path no URI names are passed over.
    /// - provides: the documents a reference or rename request reads, so the
    ///   two cannot answer a different set.
    /// - fails: the first failure `visit` returns.
    /// - panics: none.
    /// - executable: none — the visits are the caller's effects.
    ///
    /// # Errors
    /// The first failure `visit` returns.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an open importer, the unopened declaring source and
    ///   an unopened importer are each visited once, and a source importing
    ///   nothing is not.
    /// - witness: `server::tests::a_rename_rewrites_a_name_everywhere_it_is_written`
    fn writers<Failure>(
        &self,
        written: &Written,
        peer: Peer,
        shadows: &Shadowing<'_>,
        visit: &mut dyn FnMut(Writer<'_>) -> Result<(), Failure>,
    ) -> Result<(), Failure>
    {
        for held in self.documents.keys() {
            let Maybe::Present(document) = self.view(held, peer)
            else {
                continue;
            };
            let Ok(session) = document.session.as_ref()
            else {
                continue;
            };
            visit(Writer {
                uri: held,
                path: &named_path(&held.path()),
                text: document.text.source(),
                hovering: document.text.hovering(&held.path(), session, shadows),
            })?;
        }
        let Ok(grammar) = grammar()
        else {
            return Ok(());
        };
        let copies: Vec<(PathBuf, Vec<PathBuf>)> = self
            .paths
            .iter()
            .filter_map(|(path, uri)| match self.view(uri, peer) {
                Maybe::Present(document) => Some((
                    path.clone(),
                    imports_named(grammar, path, document.text.source()),
                )),
                Maybe::Absent(_) => None,
            })
            .collect();
        let mut unheld = self
            .files
            .borrow_mut()
            .importers(grammar, &written.path, &copies);
        unheld.push(written.path.clone());
        unheld.sort_unstable();
        unheld.dedup();
        let mut session: Option<DocumentSession> = None;
        let mut text = String::new();
        for path in unheld {
            if self.paths.contains_key(&path) {
                continue;
            }
            let Some(uri) = DocumentUri::of_path(&path)
            else {
                continue;
            };
            text.clear();
            let read = std::fs::File::open(&path)
                .and_then(|mut file| std::io::Read::read_to_string(&mut file, &mut text));
            if read.is_err() || !text.contains(written.spelled.as_str()) {
                continue;
            }
            let Ok(ref judging) = *session.get_or_insert_with(|| open(&uri))
            else {
                return Ok(());
            };
            let source = SourceText::from(text.as_str());
            visit(Writer {
                uri: &uri,
                path: &path,
                text: source,
                hovering: &hovering(source, &path, judging, shadows),
            })?;
        }
        Ok(())
    }

    /// What a prepare-rename request at `position` of the copy of the
    /// document at `uri` that `peer` is answered from answers.
    ///
    /// # Specification
    /// - requires: nothing; an unknown URI and any position are admitted.
    /// - ensures: what [`prepared`] answers off the copy, when the name it
    ///   places is declared in a document an editor holds or under a folder a
    ///   connection opened; Nothing otherwise, and for an unknown document or
    ///   one whose session holds no grammar.
    /// - provides: the answer to `textDocument/prepareRename`.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a declaring name and an imported name are prepared at
    ///   their written ranges, a keyword is not.
    /// - witness: `server::tests::a_rename_rewrites_a_name_everywhere_it_is_written`
    #[spec(ensures: |ret| matches!(ret, Answer::Nothing | Answer::Renaming(_))
        && (self.documents.contains_key(uri) || matches!(ret, Answer::Nothing)))]
    fn prepare_rename(
        &self,
        uri: &DocumentUri,
        peer: Peer,
        position: Position,
    ) -> Answer
    {
        let shadows = self.shadowing(peer);
        let Maybe::Present(document) = self.view(uri, peer)
        else {
            return Answer::Nothing;
        };
        let Ok(session) = document.session.as_ref()
        else {
            return Answer::Nothing;
        };
        let text = document.text.source();
        let table = document.text.hovering(&uri.path(), session, &shadows);
        let renamable = placed(text, &named_path(&uri.path()), table, position)
            .is_some_and(|name| matches!(self.renamable(&name), Ok(())));
        if !renamable {
            return Answer::Nothing;
        }
        prepared(text, table, position).map_or(Answer::Nothing, Answer::Renaming)
    }

    /// Whether a rename may rewrite the name `written` places: it is declared
    /// in a document an editor holds or under a folder a connection opened.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// Why it may not, as a rename request is refused.
    fn renamable(
        &self,
        written: &Written,
    ) -> Result<(), String>
    {
        if self.paths.contains_key(&written.path)
            || self.files.borrow().root_of(&written.path).is_some()
        {
            return Ok(());
        }
        Err(format!(
            "`{}` is declared outside every folder the editor opened; it is not renamed",
            written.spelled
        ))
    }

    /// What a rename request at `position` of the copy of the document at
    /// `uri` that `peer` is answered from answers: the edits writing
    /// `new_name` wherever the name there is written.
    ///
    /// # Specification
    /// - requires: nothing; an unknown URI, any position and any name are
    ///   admitted.
    /// - ensures: Nothing for an unknown document or one whose session holds no
    ///   grammar; otherwise, for the name [`placed`] places, the edits
    ///   replacing each of its [`sites`] in each document [`Self::writers`]
    ///   visits with `new_name`, by URI. The declaring source, with its sites
    ///   replaced, is tried beside its present text, each import read as `peer`
    ///   is answered.
    /// - provides: the answer to `textDocument/rename`.
    /// - fails: when no name is placed; when it is declared outside the
    ///   documents held and the folders opened; when a use does not end with
    ///   the name ([`Unrenamed`]); when the trial ranks the renamed source
    ///   lower or reports more errors for it than for its present text.
    /// - panics: none.
    /// - executable: none — the edits are each document's sites, whose own
    ///   specification states them.
    ///
    /// # Errors
    /// Why nothing is renamed, as above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a sibling's name renamed from an importer rewrites
    ///   the sibling, the open importer and an importer no editor holds; a
    ///   binder renames in its document alone; a keyword, a name already
    ///   declared and a position on nothing are refused.
    /// - witness: `server::tests::a_rename_rewrites_a_name_everywhere_it_is_written`
    fn rename(
        &self,
        uri: &DocumentUri,
        peer: Peer,
        position: Position,
        new_name: NewName<'_>,
    ) -> Result<Answer, String>
    {
        let shadows = self.shadowing(peer);
        let Maybe::Present(document) = self.view(uri, peer)
        else {
            return Ok(Answer::Nothing);
        };
        let Ok(session) = document.session.as_ref()
        else {
            return Ok(Answer::Nothing);
        };
        let Some(name) = placed(
            document.text.source(),
            &named_path(&uri.path()),
            document.text.hovering(&uri.path(), session, &shadows),
            position,
        )
        else {
            return Err("no name is written at the position".to_owned());
        };
        self.renamable(&name)?;
        let mut changes = BTreeMap::new();
        let mut declaring = None;
        self.writers(&name, peer, &shadows, &mut |writer| {
            let found = sites(writer.text, writer.path, writer.hovering, &name)?;
            if found.is_empty() {
                return Ok(());
            }
            let _edited = changes.insert(
                writer.uri.clone(),
                text_edits(writer.text, &found, new_name),
            );
            if writer.path == name.path {
                declaring = Some((
                    writer.uri.clone(),
                    String::from(<&str>::from(writer.text)),
                    found,
                ));
            }
            Ok(())
        })
        .map_err(|unrenamed: Unrenamed| unrenamed.to_string())?;
        if let Some((source, text, found)) = declaring {
            self.judged(
                &source,
                peer,
                (SourceText::from(text.as_str()), &found),
                (SourceText::from(name.spelled.as_str()), new_name),
                &shadows,
            )?;
        }
        Ok(Answer::Renamed(WorkspaceEdit::of(changes)))
    }

    /// What a `workspace/willRenameFiles` request moving files and folders
    /// as `moves` states answers, `peer` asking: the edits rewriting each path
    /// import's address the moves change, in every document an editor holds
    /// and every source under the folders the connections opened that moves
    /// or imports a file that moves.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: Nothing when no address changes; otherwise, by URI, each
    ///   document's edits as [`Reading::readdressed`] reads them, from the copy
    ///   `peer` is answered from for a held document and from the file for a
    ///   source [`Files::touching`] lists that no editor holds.
    /// - provides: the answer to `workspace/willRenameFiles`.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — each document's edits are its reading's, whose own
    ///   specification states them.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a moved file's held importer and unheld importer are
    ///   rewritten, its own imports follow it to another directory, a folder
    ///   moved rewrites the imports reaching into it, and a move no import
    ///   names answers Nothing.
    /// - witness: `server::tests::a_moved_file_s_imports_follow_it`
    fn will_rename(
        &self,
        peer: Peer,
        moves: &Moves,
    ) -> Answer
    {
        let mut changes = BTreeMap::new();
        for uri in self.documents.keys() {
            let Maybe::Present(document) = self.view(uri, peer)
            else {
                continue;
            };
            let text = document.text.source();
            let edits = document.text.reading().readdressed(
                &LineIndex::new(text.as_ref().into()),
                &named_path(&uri.path()),
                moves,
            );
            if !edits.is_empty() {
                let _edited = changes.insert(uri.clone(), edits);
            }
        }
        if let Ok(grammar) = grammar() {
            let touched = self.files.borrow_mut().touching(grammar, moves);
            let mut text = String::new();
            for path in touched {
                if self.paths.contains_key(&path) {
                    continue;
                }
                let Some(uri) = DocumentUri::of_path(&path)
                else {
                    continue;
                };
                text.clear();
                if std::fs::File::open(&path)
                    .and_then(|mut file| std::io::Read::read_to_string(&mut file, &mut text))
                    .is_err()
                {
                    continue;
                }
                let source = SourceText::from(text.as_str());
                let edits = Reading::of(source).readdressed(
                    &LineIndex::new(text.as_str().into()),
                    &path,
                    moves,
                );
                if !edits.is_empty() {
                    let _edited = changes.insert(uri, edits);
                }
            }
        }
        if changes.is_empty() {
            Answer::Nothing
        }
        else {
            Answer::Renamed(WorkspaceEdit::of(changes))
        }
    }

    /// Refuse a rename of `spelled` to `new_name` that its declaring source,
    /// the document at `uri` reading `text` with `found` its sites, does not
    /// survive: the renamed text is tried beside `text` and must be ranked no
    /// lower and report no more errors.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// The first error the renamed text reports that the present text does
    /// not, when the rename is refused.
    fn judged(
        &self,
        uri: &DocumentUri,
        peer: Peer,
        (text, found): (SourceText<'_>, &[ByteSpan]),
        (spelled, new_name): (SourceText<'_>, NewName<'_>),
        shadows: &Shadowing<'_>,
    ) -> Result<(), String>
    {
        let renamed = spliced(text, found, new_name);
        let fresh;
        let session = match self.view(uri, peer) {
            Maybe::Present(document) => &document.session,
            Maybe::Absent(_) => {
                fresh = open(uri);
                &fresh
            },
        };
        let tried = trial(
            uri,
            session,
            &[text, SourceText::from(renamed.as_str())],
            shadows,
        );
        let of = |index: usize| {
            tried
                .iter()
                .find(|tried| usize::from(tried.candidate) == index)
        };
        let (Some(before), Some(after)) = (of(0), of(1))
        else {
            return Ok(());
        };
        let errors = |tried: &Tried| {
            tried
                .diagnostics
                .iter()
                .filter(|diagnostic| diagnostic.severity == Severity::ERROR)
                .count()
        };
        if after.reached <= before.reached && errors(after) <= errors(before) {
            return Ok(());
        }
        let held: BTreeSet<&str> = before
            .diagnostics
            .iter()
            .map(|diagnostic| diagnostic.message.as_str())
            .collect();
        let new = after
            .diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.severity == Severity::ERROR)
            .find(|diagnostic| !held.contains(diagnostic.message.as_str()))
            .map_or("", |diagnostic| diagnostic.message.as_str());
        Err(format!(
            "renaming `{}` to `{}` leaves its source with an error it did not have: {new}",
            <&str>::from(spelled),
            new_name.0
        ))
    }

    /// The answer to a formatting request `id` over `scope` of the copy of
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
    /// - hypothesis: L3 — the known document out of layout, formatted whole,
    ///   over a range and over several ranges, a closed document and a document
    ///   in layout observe the edits, `null` and the empty list exactly.
    /// - witness: `server::tests::formatting_answers_the_edits_that_lay_a_document_out`
    #[spec(ensures: |ref ret| match *ret {
        Outgoing::Success { result: Answer::Nothing, .. } => !self.documents.contains_key(uri),
        Outgoing::Success { result: Answer::Edits(_), .. } => self.documents.contains_key(uri),
        Outgoing::Failure { ref error, .. } => error.code == ErrorCode::REQUEST_FAILED,
        Outgoing::Success { .. } | Outgoing::Notification { .. } | Outgoing::Request { .. } | Outgoing::Progress(_) => false,
    })]
    fn format(
        &self,
        id: RequestId,
        uri: &DocumentUri,
        peer: Peer,
        scope: Scope<'_>,
    ) -> Outgoing
    {
        let Maybe::Present(document) = self.view(uri, peer)
        else {
            return success(id, Answer::Nothing);
        };
        match edits(document.text.source(), scope) {
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

/// Whether the client sending the `initialize` parameters `params` takes a
/// definition as links; not when they cannot be read.
///
/// # Specification
/// trivial.
fn initial_links(params: &Value) -> Linked
{
    InitializeParams::deserialize(params)
        .map(|params| params.links())
        .unwrap_or_default()
}

/// Whether the client `initialize` names in `params` takes a signature's
/// parameters as their places in the label; not when the parameters do not
/// read.
///
/// # Specification
/// trivial.
fn initial_offsets(params: &Value) -> LabelOffsets
{
    InitializeParams::deserialize(params)
        .map(|params| params.label_offsets())
        .unwrap_or_default()
}

/// Whether the client `initialize` names in `params` shows a completion's
/// label details; not when the parameters do not read.
///
/// # Specification
/// trivial.
fn initial_detailing(params: &Value) -> LabelsDetailed
{
    InitializeParams::deserialize(params)
        .map(|params| params.label_details())
        .unwrap_or_default()
}

/// Whether the client `initialize` names in `params` takes a completion's
/// text as a snippet; not when the parameters do not read.
///
/// # Specification
/// trivial.
fn initial_snipping(params: &Value) -> TakesSnippets
{
    InitializeParams::deserialize(params)
        .map(|params| params.snippets())
        .unwrap_or_default()
}

/// Whether the client `initialize` names in `params` shows the text a fold
/// names; not when the parameters do not read.
///
/// # Specification
/// trivial.
fn initial_collapsing(params: &Value) -> FoldsCollapsed
{
    InitializeParams::deserialize(params)
        .map(|params| params.collapsed_folds())
        .unwrap_or_default()
}

/// Whether the client `initialize` names in `params` watches files for the
/// server once asked; not when the parameters do not read.
///
/// # Specification
/// trivial.
fn initial_watching(params: &Value) -> WatchesFiles
{
    InitializeParams::deserialize(params)
        .map(|params| params.watches_files())
        .unwrap_or_default()
}

/// Whether the client `initialize` names in `params` shows the progress of
/// work the server starts; not when the parameters do not read.
///
/// # Specification
/// trivial.
fn initial_progress(params: &Value) -> ShowsProgress
{
    InitializeParams::deserialize(params)
        .map(|params| params.shows_progress())
        .unwrap_or_default()
}

/// Which answers the client `initialize` names in `params` requests again
/// when asked; none when the parameters do not read.
///
/// # Specification
/// trivial.
fn initial_refreshing(params: &Value) -> Refreshing
{
    InitializeParams::deserialize(params)
        .map(|params| params.refreshing())
        .unwrap_or_default()
}

/// How much of its exchanges the client `initialize` names in `params` has
/// the server trace; `off` when the parameters do not read.
///
/// # Specification
/// trivial.
fn initial_trace(params: &Value) -> Trace
{
    InitializeParams::deserialize(params)
        .map(|params| params.trace())
        .unwrap_or_default()
}

/// Whether the client `initialize` names in `params` answers a pull of its
/// settings; not when the parameters do not read.
///
/// # Specification
/// trivial.
fn initial_pulling(params: &Value) -> PullsConfiguration
{
    InitializeParams::deserialize(params)
        .map(|params| params.pulls_configuration())
        .unwrap_or_default()
}

/// Whether the client `initialize` names in `params` applies an edit the
/// server asks it to; not when the parameters do not read.
///
/// # Specification
/// trivial.
fn initial_applying(params: &Value) -> AppliesEdits
{
    InitializeParams::deserialize(params)
        .map(|params| params.applies_edits())
        .unwrap_or_default()
}

/// How the client `initialize` names in `params` takes a workspace edit; by
/// URI when the parameters do not read.
///
/// # Specification
/// trivial.
fn initial_editing(params: &Value) -> EditsShaped
{
    InitializeParams::deserialize(params)
        .map(|params| params.edits_shaped())
        .unwrap_or_default()
}

/// Whether the client `initialize` names in `params` shows a document the
/// server asks it to; not when the parameters do not read.
///
/// # Specification
/// trivial.
fn initial_showing(params: &Value) -> ShowsDocuments
{
    InitializeParams::deserialize(params)
        .map(|params| params.shows_documents())
        .unwrap_or_default()
}

/// Whether the client `initialize` names in `params` answers a request for
/// its workspace folders; not when the parameters do not read.
///
/// # Specification
/// trivial.
fn initial_listing(params: &Value) -> ListsFolders
{
    InitializeParams::deserialize(params)
        .map(|params| params.lists_folders())
        .unwrap_or_default()
}

/// Whether the client `initialize` names in `params` shows the text of a
/// virtual document the server serves; not when the parameters do not read.
///
/// # Specification
/// trivial.
fn initial_viewer(params: &Value) -> ViewsContent
{
    InitializeParams::deserialize(params)
        .map(|params| params.views_content())
        .unwrap_or_default()
}

/// The warning logged to the client when its `gandr` settings do not read:
/// what `error` says, and that none of them is applied.
///
/// # Specification
/// trivial.
fn unread_settings(error: &serde_json::Error) -> Outgoing
{
    tell(Told::Logged, MessageParams {
        kind: MessageType::WARNING,
        message: format!("the `gandr` settings do not read, so none is applied: {error}"),
    })
}

/// The folders the client `initialize` names in `params` opened, each a
/// `file` URI's path; none when the parameters do not read.
///
/// # Specification
/// trivial.
fn initial_roots(params: &Value) -> Vec<PathBuf>
{
    InitializeParams::deserialize(params)
        .map(|params| params.roots())
        .unwrap_or_default()
}

/// The paths of the files `changes` names, as [`named_path`] names each,
/// sorted and without repeats.
///
/// # Specification
/// trivial.
fn changed_paths(changes: &[FileEvent]) -> Vec<PathBuf>
{
    let mut changed: Vec<PathBuf> = changes
        .iter()
        .map(|change| named_path(&change.uri.path()))
        .collect();
    changed.sort_unstable();
    changed.dedup();
    changed
}

/// The paths `renames` names, where each file or folder was and where it went,
/// as [`named_path`] names each, sorted and without repeats.
///
/// # Specification
/// trivial.
fn renamed_paths(renames: &[FileRename]) -> Vec<PathBuf>
{
    let mut renamed: Vec<PathBuf> = renames
        .iter()
        .flat_map(|rename| {
            [
                named_path(&rename.old_uri.path()),
                named_path(&rename.new_uri.path()),
            ]
        })
        .collect();
    renamed.sort_unstable();
    renamed.dedup();
    renamed
}

/// Whether a recheck picks a copy.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Picked(bool);

/// Whether `picks` picks a copy whose closure's sorted paths are `named`, the
/// files the editors hold being `held`.
///
/// # Specification
/// trivial.
fn picked(
    picks: Picks<'_>,
    held: &BTreeMap<PathBuf, DocumentUri>,
    named: &[PathBuf],
) -> Picked
{
    Picked(match picks {
        Picks::Every => true,
        Picks::Naming(changed, origin) => changed.iter().any(|path| {
            (origin == Origin::Editor || !held.contains_key(path))
                && named.binary_search(path).is_ok()
        }),
        Picks::File(path) => named
            .binary_search_by(|named| named.as_path().cmp(path))
            .is_ok(),
        Picks::Under(changed) => named.iter().any(|named| {
            !held.contains_key(named) && changed.iter().any(|path| named.starts_with(path))
        }),
    })
}

/// Whether an import of a file reads other text when an editor's copy of it
/// stands in for the disk, or the disk for the copy.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Differs(bool);

/// Whether `text` differs from the file at `path`: a file that cannot be
/// read differs from every copy.
///
/// # Specification
/// trivial.
fn differs_from_disk(
    path: &Path,
    text: SourceText<'_>,
) -> Differs
{
    Differs(std::fs::read(path).map_or(true, |disk| disk != <&str>::from(text).as_bytes()))
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

/// Recheck `document`, open at `uri`, at `verbosity` and in `spelling`,
/// holding back for
/// `quiet` the diagnostics of the form under its caret: the notification
/// publishing the rest and the line logging what the recheck cost.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one diagnostic notification naming the supplied URI and held
///   version, with the diagnostics the document's session judges for its whole
///   text, each import read as `shadows` holds it, rendered at `verbosity` with
///   their types in `spelling`, less those [`publishable`] holds for the form
///   under the document's caret while `quiet` is not zero; the copy records
///   every judged diagnostic as checked. One log line names the same URI and
///   version, its admission pending when the judgement left one, and whether
///   the publication held any.
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
/// - witness: `tests::session::an_edit_to_a_large_document_rechecks_its_forms`
/// - witness: `server::tests::a_configuration_change_republishes_at_its_verbosity`
/// - witness: `tests::editor::scenarios::typing_a_declaration_holds_its_diagnostics_until_its_terminator`
#[spec(ensures: |ret| ret.flow == Flow::Continue
    && matches!(*ret.messages.as_slice(), [Outgoing::Notification { method: "textDocument/publishDiagnostics",
        params: Notified::Published(ref params), .. }]
        if params.uri == *uri && params.version == Some(document.version)
            && params.diagnostics.len() <= document.checked.len())
    && matches!(*ret.log.as_slice(), [ref logged] if logged.uri == *uri && logged.version == document.version))]
fn synchronised(
    uri: &DocumentUri,
    document: &mut Document,
    shadows: &dyn Shadows,
    verbosity: Verbosity,
    spelling: Spelling,
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
        shadows,
        verbosity,
        spelling,
        caret,
    );
    let form = caret_range(document, rechecked.form);
    let (published, holding) = publishable(&rechecked.diagnostics, &form);
    document.checked = rechecked.diagnostics;
    document.named = rechecked.named;
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
/// writing each synchronisation's timing line to `log`, its user's
/// configuration naming `spelling`.
///
/// # Specification
/// - requires: nothing of the streams; `input` carries the client's frames,
///   `output` takes the server's, and `log` takes the operator's lines.
/// - ensures: each frame read is handled by one [`Server`] over a workspace
///   whose configured spelling is `spelling`: the progress the work it starts
///   reports, as [`Server::reported`] states, begins first, and every message
///   it produces is written as one frame, in order; then the admissions its
///   synchronisations left run, as [`Server::admit`] states, each correction
///   written as one frame, the progress ends, and every line logged is written
///   to `log` with a line terminator, before the next frame is read. A
///   synchronisation whose publication held a diagnostic back arms its
///   document's deadline the server's quiet interval later, and one that held
///   nothing disarms it; a deadline that passes with no frame read publishes
///   what the document holds back, as [`Server::release`] states. The session
///   ends at `exit` or at a stream closed at a frame boundary, as
///   [`Server::closed`] states. A line `log` refuses is dropped: the log is the
///   operator's, and the protocol never depends on it.
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
/// - witness: `tests::session::a_session_round_trips_over_in_memory_streams`
/// - witness: `tests::session::a_stream_closed_without_exit_ends_abruptly`
/// - witness: `tests::session::an_edit_to_a_large_document_rechecks_its_forms`
/// - witness: `tests::session::a_held_diagnostic_publishes_once_the_document_is_quiet`
#[inline]
pub fn serve<Input, Output, Log>(
    input: &mut Input,
    output: &mut Output,
    log: &mut Log,
    spelling: Spelling,
) -> Result<Served, TransportFault>
where
    Input: BufRead + Send,
    Output: Write,
    Log: Write,
{
    let mut workspace = Workspace::spelled(spelling);
    let mut server = Server::default();
    paced(input, Inbox::default(), |met, deadlines| {
        let (message, later) = match met {
            Met::Closed => return Ok(ControlFlow::Break(server.closed())),
            Met::Quiet(uri) => {
                for message in &server.release(&mut workspace, &uri) {
                    written(output, message)?;
                }
                return Ok(ControlFlow::Continue(()));
            },
            // No watch and no other connection holds this loop's inbox.
            Met::Changed(_) | Met::Edited(_) | Met::Proposed => {
                return Ok(ControlFlow::Continue(()));
            },
            Met::Frame { message, later } => (message, later),
        };
        let reported = server.reported(&workspace, &message);
        for message in &reported.begin {
            written(output, message)?;
        }
        let mut outcome = server.answer(&mut workspace, message, later);
        for message in &outcome.messages {
            written(output, message)?;
        }
        for message in &server.admit(&mut workspace, &mut outcome.log) {
            written(output, message)?;
        }
        for message in &reported.end {
            written(output, message)?;
        }
        deadlines.note(&outcome.log, server.quiet(), Instant::now());
        for line in &outcome.log {
            let _unlogged = writeln!(log, "{line}");
        }
        for message in &server.traced(&outcome.log) {
            written(output, message)?;
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
/// - witness: `tests::session::a_session_round_trips_over_in_memory_streams`
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
    use std::path::Path;
    use std::sync::mpsc::channel;

    use anodized::spec;
    use gandr_surface_diagnostics::Verbosity;
    use gandr_surface_dispatcher::named_path;
    use serde_json::Value;

    use super::Cancelled;
    use super::Choice;
    use super::Flow;
    use super::Outcome;
    use super::Peer;
    use super::Served;
    use super::Server;
    use super::Workspace;
    use crate::goto::Goto;
    use crate::position::Character;
    use crate::position::Line;
    use crate::position::Position;
    use crate::position::Range;
    use crate::proposal::Proposal;
    use crate::proposal::ProposalRefusal;
    use crate::proposal::Settles;
    use crate::protocol::ChoiceParams;
    use crate::protocol::ContentChange;
    use crate::protocol::DocumentUri;
    use crate::protocol::Linked;
    use crate::protocol::MessageAction;
    use crate::protocol::MessageType;
    use crate::protocol::ProgressToken;
    use crate::rpc::Classified;
    use crate::rpc::Outgoing;
    use crate::rpc::RequestId;
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
    /// - ensures: serialized outgoing messages remain in order, each a JSON-RPC
    ///   2.0 message.
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
    #[spec(ensures: |ret| ret.as_array().is_some_and(|messages| messages.iter().all(|message|
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
                                    "number","string","comment","macro","label",
                                    "unresolvedReference"],
                                "tokenModifiers":["declaration","defaultLibrary"]},
                            "full":{"delta":true},
                            "range":true},
                        "completionProvider":{"resolveProvider":true,
                            "completionItem":{"labelDetailsSupport":true}},
                        "inlineCompletionProvider":true,
                        "documentSymbolProvider":true,
                        "foldingRangeProvider":true,
                        "selectionRangeProvider":true,
                        "hoverProvider":true,
                        "signatureHelpProvider":{"triggerCharacters":["(",","],"retriggerCharacters":[")"]},
                        "definitionProvider":true,
                        "declarationProvider":true,
                        "typeDefinitionProvider":true,
                        "documentFormattingProvider":true,
                        "documentRangeFormattingProvider":{"rangesSupport":true},
                        "documentOnTypeFormattingProvider":{"firstTriggerCharacter":";"},
                        "codeLensProvider":{"resolveProvider":true},
                        "codeActionProvider":{"resolveProvider":true},
                        "executeCommandProvider":{"commands":["gandr.applyFill"]},
                        "workspaceSymbolProvider":{"resolveProvider":true},
                        "documentHighlightProvider":true,
                        "referencesProvider":true,
                        "renameProvider":{"prepareProvider":true},
                        "documentLinkProvider":{"resolveProvider":true},
                        "linkedEditingRangeProvider":true,
                        "workspace":{"workspaceFolders":{"supported":true,"changeNotifications":true},
                            "fileOperations":{"didCreate":{"filters":[
                                {"scheme":"file","pattern":{"glob":"**/*.gandr","matches":"file"}},
                                {"scheme":"file","pattern":{"glob":"**","matches":"folder"}}]},
                            "didRename":{"filters":[
                                {"scheme":"file","pattern":{"glob":"**/*.gandr","matches":"file"}},
                                {"scheme":"file","pattern":{"glob":"**","matches":"folder"}}]},
                            "didDelete":{"filters":[
                                {"scheme":"file","pattern":{"glob":"**/*.gandr","matches":"file"}},
                                {"scheme":"file","pattern":{"glob":"**","matches":"folder"}}]},
                            "willRename":{"filters":[
                                {"scheme":"file","pattern":{"glob":"**/*.gandr","matches":"file"}},
                                {"scheme":"file","pattern":{"glob":"**","matches":"folder"}}]}},
                            "textDocumentContent":{"schemes":["gandr-tree"]}}},
                    "serverInfo":{"name":"gandr","version":""#,
                env!("CARGO_PKG_VERSION"),
                r#""}}}]"#
            ))),
            "the advertised capabilities, whole"
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
                     "result":{"data":[0,0,3,0,0, 0,4,1,2,1, 0,4,2,9,0],
                        "resultId":"ac2c5e81f4c6deef122878dc6eb03960e2099f34556da16b15af990a3828c90c"}}]"#
            )),
            "the known document's tokens: `def`, `f` a declared function, `42`"
        );
    }

    /// Over two corpus sources, judged, each use whose referent the
    /// highlighter's guess misnames is sent as what it refers to, and each
    /// name the lowering refused as naming nothing is sent as
    /// `unresolvedReference`; every other token is the highlighter's, at the
    /// same range. The golden lists exactly the tokens whose type the
    /// judgement changed, as `line:column `text` before→after`.
    #[test]
    fn a_use_is_sent_as_what_it_refers_to()
    {
        let changed = |name: &str| -> Vec<String> {
            let path = Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../surface-corpus/fixture/model/data")
                .join(name);
            let text = std::fs::read_to_string(&path).expect("the source is read");
            let mut server = initialized();
            let opened = format!(
                r#"{{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{{"textDocument":{{"uri":"file:///tmp/judged.gandr","languageId":"gandr","version":1,"text":{}}}}}}}"#,
                serde_json::to_string(&text).expect("the text serialises")
            );
            let _published = send(&mut server, Json(&opened));
            let answered = send(
                &mut server,
                Json(
                    r#"{"jsonrpc":"2.0","id":2,"method":"textDocument/semanticTokens/full",
                        "params":{"textDocument":{"uri":"file:///tmp/judged.gandr"}}}"#,
                ),
            )[0]["result"]["data"]
                .clone();
            let judged: Vec<u32> = serde_json::from_value(answered).expect("a token stream");
            let index = gandr_surface_render_remote::LineIndex::new(text.as_str().into());
            let written = crate::tokens::encode(
                &index,
                crate::reading::Reading::of(gandr_surface_syntax::SourceText::from(text.as_str()))
                    .spans(),
                &[],
            );
            let absolute = |stream: &[u32]| {
                let (mut line, mut column) = (0_u32, 0_u32);
                stream
                    .as_chunks::<5>()
                    .0
                    .iter()
                    .map(|&[down, across, length, kind, _]| {
                        column = if down == 0 {
                            column.saturating_add(across)
                        }
                        else {
                            across
                        };
                        line = line.saturating_add(down);
                        (line, column, length, kind)
                    })
                    .collect::<Vec<_>>()
            };
            let (after, before) = (absolute(&judged), absolute(written.as_ref()));
            assert_eq!(
                after.len(),
                before.len(),
                "the judgement keeps every token's range"
            );
            let named = |kind: u32| {
                usize::try_from(kind)
                    .ok()
                    .and_then(|kind| crate::tokens::TOKEN_TYPES.get(kind))
                    .copied()
                    .unwrap_or("?")
            };
            after
                .iter()
                .zip(&before)
                .filter(|&(&(.., judged_kind), &(.., written_kind))| judged_kind != written_kind)
                .map(
                    |(&(line, column, length, judged_kind), &(.., written_kind))| {
                        let spelled = text
                            .lines()
                            .nth(usize::try_from(line).unwrap_or(usize::MAX))
                            .and_then(|row| {
                                let start = usize::try_from(column).unwrap_or(usize::MAX);
                                row.get(
                                    start
                                        .. start
                                            .saturating_add(usize::try_from(length).unwrap_or(0)),
                                )
                            })
                            .unwrap_or("?");
                        format!(
                            "{}:{column} `{spelled}` {}→{}",
                            line.saturating_add(1),
                            named(written_kind),
                            named(judged_kind)
                        )
                    },
                )
                .collect()
        };
        assert_eq!(
            changed("data-maybe.gandr"),
            [
                "25:56 `m` variable→parameter",
                "25:59 `m` variable→parameter",
                "26:7 `m` variable→parameter",
                "27:17 `m` variable→parameter",
                "28:20 `m` variable→parameter",
            ],
            "each use of the parameter `m` is a parameter; the family and its constructors \
             the highlighter already names"
        );
        assert_eq!(
            changed("sums-and-case.gandr"),
            ["8:4 `Inl` enumMember→unresolvedReference"],
            "the name the lowering refused `pick` for, an expected refusal, sent as unresolved; \
             the lowering stops at a declaration's first refusal, so its other names keep \
             their guess"
        );
    }

    #[test]
    fn a_delta_answers_the_edits_from_the_last_full_stream()
    {
        let mut server = server_over_the_known_document();
        let full = |server: &mut Connected| {
            send(
                server,
                Json(
                    r#"{"jsonrpc":"2.0","id":2,"method":"textDocument/semanticTokens/full",
                        "params":{"textDocument":{"uri":"file:///tmp/example.gandr"}}}"#,
                ),
            )[0]["result"]
                .clone()
        };
        let delta = |server: &mut Connected, previous: &str| {
            let request = format!(
                r#"{{"jsonrpc":"2.0","id":3,"method":"textDocument/semanticTokens/full/delta",
                    "params":{{"textDocument":{{"uri":"file:///tmp/example.gandr"}},
                    "previousResultId":"{previous}"}}}}"#
            );
            send(server, Json(&request))[0]["result"].clone()
        };
        let before = full(&mut server);
        let _published = send(
            &mut server,
            Json(
                r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{
                    "textDocument":{"uri":"file:///tmp/example.gandr","version":2},
                    "contentChanges":[{"text":"def f = 7 ;\n"}]}}"#,
            ),
        );
        let first = before["resultId"]
            .as_str()
            .expect("a full answer carries an id");
        let changed = delta(&mut server, first);
        assert_eq!(
            changed["edits"],
            serde_json::json!([{"start": 10_u32, "deleteCount": 5_u32, "data": [0_u32, 4_u32, 1_u32, 9_u32, 0_u32]}]),
            "`42` became `7`: the one token that changed"
        );
        let after = full(&mut server);
        assert_eq!(
            changed["resultId"], after["resultId"],
            "the delta's id is the full stream's"
        );
        let current = after["resultId"]
            .as_str()
            .expect("a full answer carries an id");
        assert_eq!(
            delta(&mut server, current),
            serde_json::json!({"resultId": current, "edits": []}),
            "nothing changed since: no edit"
        );
        assert_eq!(
            delta(&mut server, "stale"),
            after,
            "an id the connection did not send: the full stream"
        );
        let _closed = send(
            &mut server,
            Json(
                r#"{"jsonrpc":"2.0","method":"textDocument/didClose",
                    "params":{"textDocument":{"uri":"file:///tmp/example.gandr"}}}"#,
            ),
        );
        assert_eq!(
            delta(&mut server, current),
            serde_json::Value::Null,
            "a closed document: null"
        );
    }

    #[test]
    fn completion_answers_the_names_a_word_may_complete_to_806()
    {
        let mut server = initialized();
        let _published = send(
            &mut server,
            Json(
                r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":
                    {"uri":"file:///tmp/typing.gandr","languageId":"gandr","version":1,
                     "text":"def one : Integer ;\ndef one = 1 ;\ndef two : Integer ;\ndef two = on"}}}"#,
            ),
        );
        let ask = |server: &mut Connected, uri: &str| {
            let request = format!(
                r#"{{"jsonrpc":"2.0","id":8,"method":"textDocument/completion","params":{{
                    "textDocument":{{"uri":"{uri}"}},
                    "position":{{"line":3,"character":12}}}}}}"#
            );
            send(server, Json(&request))
        };
        assert_eq!(
            ask(&mut server, "file:///tmp/typing.gandr"),
            wire(Json(
                r#"[{"jsonrpc":"2.0","id":8,"result":{"isIncomplete":false,"items":[
                    {"label":"one","kind":3,"sortText":"0","textEdit":{
                        "range":{"start":{"line":3,"character":10},"end":{"line":3,"character":12}},
                        "newText":"one"},"detail":"one : Integer",
                        "data":{"uri":"file:///tmp/typing.gandr"}}]}}]"#
            )),
            "`on` in a value: the declaration starting with it, written over the word"
        );
        assert_eq!(
            ask(&mut server, "file:///tmp/unknown.gandr"),
            wire(Json(r#"[{"jsonrpc":"2.0","id":8,"result":null}]"#)),
            "a document the server does not hold: null"
        );
    }

    #[test]
    fn a_resolved_completion_reads_the_declared_head()
    {
        let mut server = initialized();
        let _published = send(
            &mut server,
            Json(
                r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":
                    {"uri":"file:///tmp/typing.gandr","languageId":"gandr","version":1,
                     "text":"/// The first.\ndef one : Integer ;\ndef one = 1 ;\ndef two : Integer ;\ndef two = on"}}}"#,
            ),
        );
        let offered = send(
            &mut server,
            Json(
                r#"{"jsonrpc":"2.0","id":8,"method":"textDocument/completion","params":{
                    "textDocument":{"uri":"file:///tmp/typing.gandr"},
                    "position":{"line":4,"character":12}}}"#,
            ),
        );
        let item = offered
            .pointer("/0/result/items/0")
            .cloned()
            .expect("`on` offers `one`");
        let resolve = |server: &mut Connected, item: &Value| {
            let request = serde_json::json!({"jsonrpc": "2.0", "id": 9_i32,
                "method": "completionItem/resolve", "params": item});
            send(server, Json(&request.to_string()))
        };
        let mut expected = item.clone();
        expected["detail"] = serde_json::json!("one : Integer");
        expected["documentation"] = serde_json::json!({"kind": "markdown", "value": "The first."});
        assert_eq!(
            resolve(&mut server, &item),
            serde_json::json!([{"jsonrpc": "2.0", "id": 9_i32, "result": expected}]),
            "a declared name resolves to its head and its documentation, the rest as offered"
        );
        let mut elsewhere = item;
        elsewhere["data"]["uri"] = serde_json::json!("file:///tmp/unknown.gandr");
        assert_eq!(
            resolve(&mut server, &elsewhere),
            serde_json::json!([{"jsonrpc": "2.0", "id": 9_i32, "result": elsewhere}]),
            "an item naming a document the server does not hold: as it came"
        );
        assert_eq!(
            resolve(&mut server, &serde_json::json!({"label": "one"})).pointer("/0/error/code"),
            Some(&serde_json::json!(-32_602_i32)),
            "an item that does not read: invalid parameters"
        );
    }

    #[test]
    fn workspace_symbols_find_the_names_the_open_closures_declare()
    {
        let directory = std::env::temp_dir().join(format!("gandr-symbols-{}", std::process::id()));
        let _cleared = std::fs::remove_dir_all(&directory);
        std::fs::create_dir_all(&directory).expect("the scratch directory is created");
        let base = "data Nat : Type {\n  Zero : Nat;\n  Succ : (n : Nat) --> Nat;\n}\n";
        let disk = [
            ("base.gandr", base),
            (
                "first.gandr",
                "import \"./base.gandr\" ;\ndef nought : Nat ;\ndef nought = Zero ;\n",
            ),
            (
                "second.gandr",
                "import \"./base.gandr\" ;\ndef other : Integer ;\ndef other = 2 ;\n",
            ),
            ("third.gandr", "def three : Integer ;\ndef three = 3 ;\n"),
            (
                "fourth.gandr",
                "import \"./third.gandr\" ;\ndef four : Integer ;\ndef four = 4 ;\n",
            ),
        ];
        for (file, text) in disk {
            std::fs::write(directory.join(file), text).expect("the source is written");
        }
        let uri = |file: &str| format!("file://{}", directory.join(file).display());
        let mut server = initialized();
        let opened = [
            ("first.gandr", disk[1].1),
            ("second.gandr", disk[2].1),
            ("third.gandr", "def thrice : Integer ;\ndef thrice = 3 ;\n"),
            ("fourth.gandr", disk[4].1),
            (
                "fifth.gandr",
                "theory Monoid {\n  sort M : Type;\n  oper mul : (x : M, y : M) --> M;\n}\nmodule \
                 Ints {\n  def twice = 2 ;\n}\n",
            ),
        ];
        for (file, text) in opened {
            let open = serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": uri(file), "languageId": "gandr", "version": 1_i32, "text": text}}});
            let _published = send(&mut server, Json(&open.to_string()));
        }
        let search = |server: &mut Connected, query: &str| {
            let request = serde_json::json!({"jsonrpc": "2.0", "id": 9_i32, "method": "workspace/symbol",
                "params": {"query": query}});
            send(server, Json(&request.to_string()))
        };
        let canonical =
            std::fs::canonicalize(&directory).expect("the scratch directory canonicalises");
        let base_uri = format!("file://{}", canonical.join("base.gandr").display());
        assert_eq!(
            search(&mut server, "su"),
            serde_json::json!([{"jsonrpc": "2.0", "id": 9_i32, "result": [
                {"name": "Succ", "kind": 9_i32, "containerName": "Nat", "location": {"uri": base_uri,
                    "range": {"start": {"line": 2_i32, "character": 2_i32},
                              "end": {"line": 2_i32, "character": 6_i32}}}}]}]),
            "a constructor a sibling two open closures read is found once, at the sibling's path, \
             held by its family"
        );
        let names = |answer: &Value| -> Vec<(String, u64, String)> {
            answer[0_usize]["result"]
                .as_array()
                .map(|found| {
                    found
                        .iter()
                        .map(|symbol| {
                            (
                                symbol["name"]
                                    .as_str()
                                    .map(String::from)
                                    .unwrap_or_default(),
                                symbol["kind"].as_u64().unwrap_or_default(),
                                symbol["location"]["uri"]
                                    .as_str()
                                    .map(String::from)
                                    .unwrap_or_default(),
                            )
                        })
                        .collect()
                })
                .unwrap_or_default()
        };
        assert_eq!(
            names(&search(&mut server, "nat")),
            [(String::from("Nat"), 10_u64, base_uri)],
            "the family, as an enum"
        );
        assert_eq!(
            names(&search(&mut server, "nou")),
            [(String::from("nought"), 12_u64, uri("first.gandr"))],
            "a name an open document writes, at its own URI"
        );
        assert_eq!(
            names(&search(&mut server, "the")),
            [
                (String::from("other"), 12_u64, uri("second.gandr")),
                (String::from("thrice"), 12_u64, uri("third.gandr"))
            ],
            "the characters apart, and an open sibling found as its own copy writes it, never as \
             the disk does"
        );
        assert_eq!(
            names(&search(&mut server, "qq")),
            [],
            "a query no name holds finds nothing"
        );
        let held = |answer: &Value| -> Vec<(String, u64, Option<String>)> {
            answer[0_usize]["result"]
                .as_array()
                .map(|found| {
                    found
                        .iter()
                        .map(|symbol| {
                            (
                                symbol["name"]
                                    .as_str()
                                    .map(String::from)
                                    .unwrap_or_default(),
                                symbol["kind"].as_u64().unwrap_or_default(),
                                symbol["containerName"].as_str().map(String::from),
                            )
                        })
                        .collect()
                })
                .unwrap_or_default()
        };
        assert_eq!(
            held(&search(&mut server, "mono")),
            [(String::from("Monoid"), 11_u64, None)],
            "a theory, as an interface, at the top of its source"
        );
        assert_eq!(
            held(&search(&mut server, "mul")),
            [(String::from("mul"), 6_u64, Some(String::from("Monoid")))],
            "a theory's operation, as a method held by its theory"
        );
        assert_eq!(
            held(&search(&mut server, "twi")),
            [(String::from("twice"), 12_u64, Some(String::from("Ints")))],
            "a module's member, held by its module"
        );
        assert_eq!(
            held(&search(&mut server, "nou")),
            [(String::from("nought"), 12_u64, None)],
            "a declaration written as a signature and a definition, once"
        );
        let _removed = std::fs::remove_dir_all(&directory);
    }

    #[test]
    fn references_find_a_name_s_uses_in_every_open_document()
    {
        let directory =
            std::env::temp_dir().join(format!("gandr-references-{}", std::process::id()));
        let _cleared = std::fs::remove_dir_all(&directory);
        std::fs::create_dir_all(&directory).expect("the scratch directory is created");
        let disk = [
            (
                "base.gandr",
                "data Nat : Type {\n  Zero : Nat;\n  Succ : (n : Nat) --> Nat;\n}\n\
                 def rec plus(n : Nat, m : Nat) -> -F Nat {\n  case m {\n    Zero => n,\n    \
                 Succ(p) => Succ(plus[<](n, p))\n  }\n}\n",
            ),
            (
                "first.gandr",
                "import \"./base.gandr\" ;\ndef nought : Nat ;\ndef nought = Zero ;\n",
            ),
            (
                "second.gandr",
                "import \"./base.gandr\" ;\ndef other : Nat ;\ndef other = Zero ;\n",
            ),
            (
                "unopened.gandr",
                "import \"./base.gandr\" ;\ndef unseen : Nat ;\ndef unseen = Zero ;\n",
            ),
        ];
        for (file, text) in disk {
            std::fs::write(directory.join(file), text).expect("the source is written");
        }
        let uri = |file: &str| format!("file://{}", directory.join(file).display());
        let mut server = initialized();
        for &(file, text) in disk.iter().take(3) {
            let open = serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": uri(file), "languageId": "gandr", "version": 1_i32, "text": text}}});
            let _published = send(&mut server, Json(&open.to_string()));
        }
        let mut references = |file: &str, line: u32, character: u32, declared: bool| {
            let request = serde_json::json!({"jsonrpc": "2.0", "id": 10_i32, "method": "textDocument/references",
                "params": {"textDocument": {"uri": uri(file)},
                    "position": at(Line::from(line), Character::from(character)),
                    "context": {"includeDeclaration": declared}}});
            send(&mut server, Json(&request.to_string()))
                .pointer("/0/result")
                .cloned()
                .unwrap_or(Value::Null)
        };
        let location = |file: &str, line: u32, start: u32, end: u32| {
            serde_json::json!({"uri": uri(file), "range": Range {
                start: at(Line::from(line), Character::from(start)),
                end: at(Line::from(line), Character::from(end)),
            }})
        };
        let uses = [
            location("base.gandr", 6, 4, 8),
            location("first.gandr", 2, 13, 17),
            location("second.gandr", 2, 12, 16),
        ];
        assert_eq!(
            references("first.gandr", 2, 14, true),
            Value::Array(
                core::iter::once(location("base.gandr", 1, 2, 6))
                    .chain(uses.iter().cloned())
                    .collect()
            ),
            "a sibling's constructor asked from an importer: its declaration at the open sibling, \
             then its uses in every open document, an unopened importer's not read"
        );
        assert_eq!(
            references("base.gandr", 1, 3, false),
            Value::Array(uses.to_vec()),
            "the same uses from the declaring name, the declaration left out"
        );
        assert_eq!(
            references("base.gandr", 6, 12, true),
            Value::Array(vec![
                location("base.gandr", 4, 13, 14),
                location("base.gandr", 6, 12, 13),
                location("base.gandr", 7, 28, 29),
            ]),
            "a parameter's uses stay in its declaration, though every importer reads the source"
        );
        assert_eq!(
            references("base.gandr", 5, 3, true),
            Value::Array(vec![]),
            "a keyword refers to nothing"
        );
        assert_eq!(
            references("closed.gandr", 0, 0, true),
            Value::Null,
            "a document the server does not hold answers null"
        );
        let _removed = std::fs::remove_dir_all(&directory);
    }

    /// The identity subject's base source, open beside an importer: a lens
    /// over each name the base declares, each resolving to the count of its
    /// uses in both documents, pinned row by row.
    #[test]
    fn a_references_lens_counts_a_name_s_uses_in_every_open_document()
    {
        let corpus = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../surface-corpus/fixture/model/identity")
            .canonicalize()
            .expect("the identity subject is checked out");
        let uri = |file: &str| format!("file://{}", corpus.join(file).display());
        let mut server = initialized();
        for file in ["circle-base.gandr", "circle-elim.gandr"] {
            let text = std::fs::read_to_string(corpus.join(file)).expect("the source is read");
            let open = serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": uri(file), "languageId": "gandr", "version": 1_i32, "text": text}}});
            let _published = send(&mut server, Json(&open.to_string()));
        }
        let written =
            std::fs::read_to_string(corpus.join("circle-base.gandr")).expect("the base is read");
        let lines: Vec<&str> = written.lines().collect();
        let listed = send(
            &mut server,
            Json(
                &serde_json::json!({"jsonrpc": "2.0", "id": 10_i32, "method": "textDocument/codeLens",
                    "params": {"textDocument": {"uri": uri("circle-base.gandr")}}})
                .to_string(),
            ),
        )
        .pointer("/0/result")
        .cloned()
        .unwrap_or(Value::Null);
        let lenses = listed.as_array().cloned().unwrap_or_default();
        assert!(
            lenses.iter().all(|lens| lens.get("command").is_none()),
            "a listed lens carries no command until it is resolved: {listed}"
        );
        let mut resolve = |lens: &Value| {
            let request = serde_json::json!({"jsonrpc": "2.0", "id": 11_i32, "method": "codeLens/resolve",
                "params": lens});
            send(&mut server, Json(&request.to_string()))
                .pointer("/0/result")
                .cloned()
                .unwrap_or(Value::Null)
        };
        let mut rows = Vec::new();
        let mut shown = None;
        for lens in &lenses {
            let resolved = resolve(lens);
            let line = lens
                .pointer("/range/start/line")
                .and_then(Value::as_u64)
                .unwrap_or(0);
            let start = lens
                .pointer("/range/start/character")
                .and_then(Value::as_u64)
                .unwrap_or(0);
            let end = lens
                .pointer("/range/end/character")
                .and_then(Value::as_u64)
                .unwrap_or(0);
            let name = lines
                .get(usize::try_from(line).unwrap_or(usize::MAX))
                .and_then(|text| {
                    text.get(
                        usize::try_from(start).unwrap_or(0) .. usize::try_from(end).unwrap_or(0),
                    )
                })
                .unwrap_or("");
            let title = resolved
                .pointer("/command/title")
                .and_then(Value::as_str)
                .unwrap_or("");
            if name == "invLooper" {
                shown = Some(resolved.clone());
            }
            rows.push(format!("{}: {name}: {title}", line.saturating_add(1)));
        }
        assert_eq!(
            rows,
            [
                "12: Empty: 0 references",
                "17: Circle: 32 references",
                "18: Base: 43 references",
                "19: loop: 21 references",
                "26: Int: 15 references",
                "27: Z: 7 references",
                "28: S: 4 references",
                "29: P: 4 references",
                "36: up: 1 reference",
                "42: down: 1 reference",
                "48: Nat: 3 references",
                "49: Zero: 0 references",
                "50: Succ: 0 references",
                "56: wind: 4 references",
                "68: spin: 4 references",
                "78: loopOn: 1 reference",
                "84: unloopOn: 1 reference",
                "99: sect: 2 references",
                "111: retr: 2 references",
                "122: selfloop: 1 reference",
                "130: selfrefl: 0 references",
                "139: invLooper: 3 references",
                "150: mul: 0 references",
            ],
            "each name the base declares, with its uses in both documents"
        );
        let location = |file: &str, line: u32, start: u32, end: u32| {
            serde_json::json!({"uri": uri(file), "range": Range {
                start: at(Line::from(line), Character::from(start)),
                end: at(Line::from(line), Character::from(end)),
            }})
        };
        assert_eq!(
            shown.and_then(|lens| lens.get("command").cloned()),
            Some(
                serde_json::json!({"title": "3 references", "command": "gandr.showReferences",
                "arguments": [uri("circle-base.gandr"), at(Line::from(138_u32), Character::from(4_u32)), [
                    location("circle-elim.gandr", 18, 46, 55),
                    location("circle-elim.gandr", 18, 56, 65),
                    location("circle-elim.gandr", 94, 35, 44),
                ]]})
            ),
            "the flip's command shows the importer's three calls of it: twice in \
             `involutive`'s type, once in `flipped`'s transport"
        );
        let closed = serde_json::json!({"range": {"start": at(Line::from(0_u32), Character::from(0_u32)),
            "end": at(Line::from(0_u32), Character::from(3_u32))},
            "data": {"uri": uri("closed.gandr"), "position": at(Line::from(0_u32), Character::from(0_u32))}});
        assert_eq!(
            resolve(&closed),
            closed,
            "a lens whose document is not open resolves to no command"
        );
    }

    #[test]
    fn a_rename_rewrites_a_name_everywhere_it_is_written()
    {
        let directory = std::env::temp_dir().join(format!("gandr-rename-{}", std::process::id()));
        let _cleared = std::fs::remove_dir_all(&directory);
        std::fs::create_dir_all(&directory).expect("the scratch directory is created");
        let directory =
            std::fs::canonicalize(&directory).expect("the scratch directory canonicalises");
        let disk = [
            (
                "base.gandr",
                "data Nat : Type {\n  Zero : Nat;\n  Succ : (n : Nat) --> Nat;\n}\n\
                 def rec plus(n : Nat, m : Nat) -> -F Nat {\n  case m {\n    Zero => n,\n    \
                 Succ(p) => Succ(plus[<](n, p))\n  }\n}\n",
            ),
            (
                "first.gandr",
                "import \"./base.gandr\" ;\ndef nought : Nat ;\ndef nought = Zero ;\n",
            ),
            (
                "unopened.gandr",
                "import \"./base.gandr\" ;\ndef unseen : Nat ;\ndef unseen = Zero ;\n",
            ),
            ("apart.gandr", "def apart : Integer ;\ndef apart = 1 ;\n"),
        ];
        for (file, text) in disk {
            std::fs::write(directory.join(file), text).expect("the source is written");
        }
        let uri = |file: &str| format!("file://{}", directory.join(file).display());
        let mut server = Connected::default();
        let initialize = serde_json::json!({"jsonrpc": "2.0", "id": 1_i32, "method": "initialize",
            "params": {"capabilities": {}, "rootUri": format!("file://{}", directory.display())}});
        let _answered = send(&mut server, Json(&initialize.to_string()));
        let open = serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
            "textDocument": {"uri": uri("first.gandr"), "languageId": "gandr", "version": 1_i32,
                "text": disk[1].1}}});
        let _published = send(&mut server, Json(&open.to_string()));
        let mut ask = |method: &str, file: &str, line: u32, character: u32, extra: Value| {
            let mut params = serde_json::json!({"textDocument": {"uri": uri(file)},
                "position": at(Line::from(line), Character::from(character))});
            if let (Some(params), Value::Object(extra)) = (params.as_object_mut(), extra) {
                params.extend(extra);
            }
            let request = serde_json::json!({"jsonrpc": "2.0", "id": 10_i32, "method": method, "params": params});
            send(&mut server, Json(&request.to_string()))
                .get(0)
                .cloned()
                .unwrap_or(Value::Null)
        };
        let range = |line: u32, start: u32, end: u32| Range {
            start: at(Line::from(line), Character::from(start)),
            end: at(Line::from(line), Character::from(end)),
        };
        let location = |file: &str, line: u32, start: u32, end: u32| serde_json::json!({"uri": uri(file), "range": range(line, start, end)});
        assert_eq!(
            ask(
                "textDocument/references",
                "first.gandr",
                2,
                14,
                serde_json::json!({"context": {"includeDeclaration": true}})
            )["result"],
            serde_json::json!([
                location("base.gandr", 1, 2, 6),
                location("first.gandr", 2, 13, 17),
                location("base.gandr", 6, 4, 8),
                location("unopened.gandr", 2, 13, 17),
            ]),
            "the declaration, then the open importer's use, then the uses of the sources no editor \
             holds, read from disk"
        );
        assert_eq!(
            ask(
                "textDocument/prepareRename",
                "first.gandr",
                2,
                14,
                Value::Null
            )["result"],
            serde_json::json!({"range": range(2, 13, 17), "placeholder": "Zero"}),
            "a use prepares the name as written there"
        );
        assert_eq!(
            ask(
                "textDocument/prepareRename",
                "first.gandr",
                1,
                1,
                Value::Null
            )["result"],
            Value::Null,
            "a keyword prepares nothing"
        );
        let edit = |line: u32, start: u32, end: u32| serde_json::json!({"range": range(line, start, end), "newText": "Nought"});
        assert_eq!(
            ask(
                "textDocument/rename",
                "first.gandr",
                2,
                14,
                serde_json::json!({"newName": "Nought"})
            )["result"],
            serde_json::json!({"changes": {
                uri("base.gandr"): [edit(1, 2, 6), edit(6, 4, 8)],
                uri("first.gandr"): [edit(2, 13, 17)],
                uri("unopened.gandr"): [edit(2, 13, 17)],
            }}),
            "a sibling's constructor is renamed at its declaration and every use, open or not; a \
             source importing nothing is untouched"
        );
        let refused = |answer: Value| {
            answer.pointer("/error/code") == Some(&serde_json::json!(-32803_i32))
                && answer.get("result").is_none()
        };
        assert!(
            refused(ask(
                "textDocument/rename",
                "first.gandr",
                2,
                14,
                serde_json::json!({"newName": "def"})
            )),
            "a keyword is refused as the new name"
        );
        assert!(
            refused(ask(
                "textDocument/rename",
                "first.gandr",
                2,
                14,
                serde_json::json!({"newName": "Succ"})
            )),
            "a name the declaring source declares already is refused"
        );
        assert!(
            refused(ask(
                "textDocument/rename",
                "first.gandr",
                1,
                1,
                serde_json::json!({"newName": "x"})
            )),
            "a position on no name is refused"
        );
        assert_eq!(
            ask(
                "textDocument/rename",
                "closed.gandr",
                0,
                0,
                serde_json::json!({"newName": "x"})
            )["result"],
            Value::Null,
            "a document the server does not hold answers null"
        );
        let _removed = std::fs::remove_dir_all(&directory);
    }

    #[test]
    fn a_rename_is_versioned_and_annotated_as_its_client_takes_edits()
    {
        let directory =
            std::env::temp_dir().join(format!("gandr-versioned-rename-{}", std::process::id()));
        let _cleared = std::fs::remove_dir_all(&directory);
        std::fs::create_dir_all(&directory).expect("the scratch directory is created");
        let directory =
            std::fs::canonicalize(&directory).expect("the scratch directory canonicalises");
        let disk = [
            ("base.gandr", "data Nat : Type {\n  Zero : Nat;\n}\n"),
            (
                "first.gandr",
                "import \"./base.gandr\" ;\ndef nought : Nat ;\ndef nought = Zero ;\n",
            ),
        ];
        for (file, text) in disk {
            std::fs::write(directory.join(file), text).expect("the source is written");
        }
        let uri = |file: &str| format!("file://{}", directory.join(file).display());
        let renamed = |capabilities: Value| {
            let mut server = Connected::default();
            let initialize = serde_json::json!({"jsonrpc": "2.0", "id": 1_i32, "method": "initialize",
                "params": {"capabilities": capabilities, "rootUri": format!("file://{}", directory.display())}});
            let _answered = send(&mut server, Json(&initialize.to_string()));
            let open = serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": uri("first.gandr"), "languageId": "gandr", "version": 7_i32,
                    "text": disk[1].1}}});
            let _published = send(&mut server, Json(&open.to_string()));
            let rename = serde_json::json!({"jsonrpc": "2.0", "id": 2_i32, "method": "textDocument/rename",
                "params": {"textDocument": {"uri": uri("first.gandr")},
                    "position": at(Line::from(2_u32), Character::from(14_u32)), "newName": "Nought"}});
            send(&mut server, Json(&rename.to_string()))[0]["result"].clone()
        };
        let edit = |line: u32, start: u32, end: u32| {
            serde_json::json!({"range": {
                "start": at(Line::from(line), Character::from(start)),
                "end": at(Line::from(line), Character::from(end))}, "newText": "Nought"})
        };
        let annotated = |line: u32, start: u32, end: u32| {
            let mut edit = edit(line, start, end);
            edit["annotationId"] = serde_json::json!("unheld");
            edit
        };
        assert_eq!(
            renamed(serde_json::json!({})),
            serde_json::json!({"changes": {
                uri("base.gandr"): [edit(1, 2, 6)],
                uri("first.gandr"): [edit(2, 13, 17)],
            }}),
            "a client that declares nothing takes the edits by URI"
        );
        assert_eq!(
            renamed(serde_json::json!({"workspace": {"workspaceEdit": {"documentChanges": true}}})),
            serde_json::json!({"documentChanges": [
                {"textDocument": {"uri": uri("base.gandr"), "version": null}, "edits": [edit(1, 2, 6)]},
                {"textDocument": {"uri": uri("first.gandr"), "version": 7_i32}, "edits": [edit(2, 13, 17)]},
            ]}),
            "a client that takes document changes gets its copy's version, and null for a file it \
             holds no copy of"
        );
        assert_eq!(
            renamed(serde_json::json!({"workspace": {"workspaceEdit": {
                "documentChanges": true, "changeAnnotationSupport": {}}}})),
            serde_json::json!({
                "documentChanges": [
                    {"textDocument": {"uri": uri("base.gandr"), "version": null},
                        "edits": [annotated(1, 2, 6)]},
                    {"textDocument": {"uri": uri("first.gandr"), "version": 7_i32},
                        "edits": [edit(2, 13, 17)]},
                ],
                "changeAnnotations": {"unheld": {
                    "label": "Edit a file this editor has not opened",
                    "needsConfirmation": true,
                    "description": "The edit changes the file on disk; this editor holds no copy of it."}},
            }),
            "a client that also takes annotations is asked to confirm the edit to the file it holds \
             no copy of"
        );
        let _removed = std::fs::remove_dir_all(&directory);
    }

    #[test]
    fn a_folder_is_searched_while_the_client_holds_it_open()
    {
        let directory = std::env::temp_dir().join(format!("gandr-folders-{}", std::process::id()));
        let _cleared = std::fs::remove_dir_all(&directory);
        std::fs::create_dir_all(&directory).expect("the scratch directory is created");
        let directory =
            std::fs::canonicalize(&directory).expect("the scratch directory canonicalises");
        let opened = "import \"./base.gandr\" ;\ndef nought : Nat ;\ndef nought = Zero ;\n";
        for (file, text) in [
            (
                "base.gandr",
                "data Nat : Type {\n  Zero : Nat;\n}\ndef zero : Nat ;\ndef zero = Zero ;\n",
            ),
            ("first.gandr", opened),
            (
                "unopened.gandr",
                "import \"./base.gandr\" ;\ndef unseen : Nat ;\ndef unseen = Zero ;\n",
            ),
        ] {
            std::fs::write(directory.join(file), text).expect("the source is written");
        }
        let uri = |file: &str| format!("file://{}", directory.join(file).display());
        let mut server = Connected::default();
        let initialize = serde_json::json!({"jsonrpc": "2.0", "id": 1_i32, "method": "initialize",
            "params": {"capabilities": {}}});
        let _answered = send(&mut server, Json(&initialize.to_string()));
        let open = serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
            "textDocument": {"uri": uri("first.gandr"), "languageId": "gandr", "version": 1_i32,
                "text": opened}}});
        let _published = send(&mut server, Json(&open.to_string()));
        let references = |server: &mut Connected| {
            let request = serde_json::json!({"jsonrpc": "2.0", "id": 10_i32,
                "method": "textDocument/references", "params": {
                    "textDocument": {"uri": uri("first.gandr")},
                    "position": at(Line::from(2_u32), Character::from(14_u32)),
                    "context": {"includeDeclaration": false}}});
            send(server, Json(&request.to_string()))
                .get(0)
                .and_then(|answer| answer.get("result"))
                .and_then(Value::as_array)
                .map(|found| {
                    found
                        .iter()
                        .filter_map(|location| location.get("uri").and_then(Value::as_str))
                        .map(str::to_owned)
                        .collect::<Vec<_>>()
                })
                .unwrap_or_default()
        };
        let folders = |side: &str| {
            serde_json::json!({"jsonrpc": "2.0", "method": "workspace/didChangeWorkspaceFolders",
                "params": {"event": {"added": [], "removed": [], side: [
                    {"uri": format!("file://{}", directory.display()), "name": "scratch"}]}}})
            .to_string()
        };
        assert_eq!(
            references(&mut server),
            [uri("first.gandr"), uri("base.gandr")],
            "with no folder open, the open document and the name's own source are searched"
        );
        assert_eq!(
            send(&mut server, Json(&folders("added"))),
            serde_json::json!([]),
            "a folder opened is answered with nothing"
        );
        assert_eq!(
            references(&mut server),
            [uri("first.gandr"), uri("base.gandr"), uri("unopened.gandr")],
            "a folder opened since `initialize` is searched for importers no editor holds"
        );
        let _closed = send(&mut server, Json(&folders("removed")));
        assert_eq!(
            references(&mut server),
            [uri("first.gandr"), uri("base.gandr")],
            "a folder closed is not searched"
        );
        let _removed = std::fs::remove_dir_all(&directory);
    }

    #[test]
    fn signature_help_answers_the_declared_head_of_the_call()
    {
        let open = |offsets: bool| {
            let mut server = Connected::default();
            let initialize = format!(
                r#"{{"jsonrpc":"2.0","id":1,"method":"initialize","params":{{"capabilities":
                {{"textDocument":{{"signatureHelp":{{"signatureInformation":
                {{"parameterInformation":{{"labelOffsetSupport":{offsets}}}}}}}}}}}}}}}"#
            );
            let _answered = send(&mut server, Json(&initialize));
            let _published = send(
                &mut server,
                Json(
                    r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":
                        {"uri":"file:///tmp/called.gandr","languageId":"gandr","version":1,
                         "text":"data Nat : Type {\n  Zero : Nat;\n  /// One more.\n  Succ : (n : Nat) --> Nat;\n}\ndef rec plus(n : Nat, m : Nat) -> -F Nat {\n  case m {\n    Zero => n,\n    Succ(p) => Succ(plus[<](n, p))\n  }\n}\ndef f : +U (-F Nat) ;\ndef f = thunk { plus(Zero, Succ()) } ;\ndef ap(g : +U (Nat -> -F Nat), x : Nat) -> -F Nat { g(x) }\n"}}}"#,
                ),
            );
            server
        };
        let ask = |server: &mut Connected, line: u32, character: u32| {
            let request = format!(
                r#"{{"jsonrpc":"2.0","id":9,"method":"textDocument/signatureHelp","params":{{
                    "textDocument":{{"uri":"file:///tmp/called.gandr"}},
                    "position":{{"line":{line},"character":{character}}}}}}}"#
            );
            send(server, Json(&request))
        };
        let mut offsets = open(true);
        let mut texts = open(false);
        let plus = |active: u32| {
            wire(Json(&format!(
                r#"[{{"jsonrpc":"2.0","id":9,"result":{{"signatures":[{{
                    "label":"plus(n : Nat, m : Nat) -> -F Nat",
                    "parameters":[{{"label":[5,12]}},{{"label":[14,21]}}]}}],
                    "activeSignature":0,"activeParameter":{active}}}}}]"#
            )))
        };
        assert_eq!(
            ask(&mut offsets, 12, 21),
            plus(0),
            "the first argument of a call, its parameters as places in the label"
        );
        assert_eq!(
            ask(&mut offsets, 12, 27),
            plus(1),
            "past the comma, the second"
        );
        let succ = wire(Json(
            r#"[{"jsonrpc":"2.0","id":9,"result":{"signatures":[{
                "label":"Succ : (n : Nat) --> Nat",
                "documentation":{"kind":"markdown","value":"One more."},
                "parameters":[{"label":[8,15]}]}],
                "activeSignature":0,"activeParameter":0}}]"#,
        ));
        assert_eq!(
            ask(&mut offsets, 12, 32),
            succ,
            "a constructor applied to no field yet, though the lowering refuses `f`"
        );
        assert_eq!(
            ask(&mut texts, 12, 27),
            wire(Json(
                r#"[{"jsonrpc":"2.0","id":9,"result":{"signatures":[{
                    "label":"plus(n : Nat, m : Nat) -> -F Nat",
                    "parameters":[{"label":"n : Nat"},{"label":"m : Nat"}]}],
                    "activeSignature":0,"activeParameter":1}}]"#
            )),
            "a client taking no offsets: each parameter as its text"
        );
        assert_eq!(
            ask(&mut offsets, 8, 32),
            wire(Json(
                r#"[{"jsonrpc":"2.0","id":9,"result":{"signatures":[{
                    "label":"plus(n : Nat, m : Nat) -> -F Nat",
                    "parameters":[{"label":[5,12]},{"label":[14,21]}]}],
                    "activeSignature":0,"activeParameter":1}}]"#
            )),
            "a recursive call, by its claim's name"
        );
        assert_eq!(
            ask(&mut offsets, 12, 34),
            wire(Json(r#"[{"jsonrpc":"2.0","id":9,"result":null}]"#)),
            "past the call: null"
        );
        assert_eq!(
            ask(&mut offsets, 13, 54),
            wire(Json(
                r#"[{"jsonrpc":"2.0","id":9,"result":{"signatures":[{
                    "label":"g : +U (Nat -> -F Nat)",
                    "parameters":[{"label":[8,11]}]}],
                    "activeSignature":0,"activeParameter":0}}]"#
            )),
            "a parameter typed by a function, by its written type"
        );
    }

    /// #843: a call typed up to its next argument without its `)`, as an
    /// editor that does not close brackets holds it, answers its head.
    #[test]
    fn signature_help_answers_inside_a_call_typed_before_its_close_843()
    {
        let mut server = Connected::default();
        let _answered = send(
            &mut server,
            Json(
                r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"capabilities":
                {"textDocument":{"signatureHelp":{"signatureInformation":
                {"parameterInformation":{"labelOffsetSupport":true}}}}}}}"#,
            ),
        );
        let _published = send(
            &mut server,
            Json(
                r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":
                    {"uri":"file:///tmp/typing.gandr","languageId":"gandr","version":1,
                     "text":"data Nat : Type {\n  Zero : Nat;\n  Succ : (n : Nat) --> Nat;\n}\ndef rec plus(n : Nat, m : Nat) -> -F Nat {\n  case m {\n    Zero => n,\n    Succ(p) => Succ(plus[<](n, p))\n  }\n}\ndef f : +U (-F Nat) ;\ndef f = thunk { plus(Zero, "}}}"#,
            ),
        );
        let ask = |server: &mut Connected, character: u32| {
            let request = format!(
                r#"{{"jsonrpc":"2.0","id":9,"method":"textDocument/signatureHelp","params":{{
                    "textDocument":{{"uri":"file:///tmp/typing.gandr"}},
                    "position":{{"line":11,"character":{character}}}}}}}"#
            );
            send(server, Json(&request))
        };
        let plus = |active: u32| {
            wire(Json(&format!(
                r#"[{{"jsonrpc":"2.0","id":9,"result":{{"signatures":[{{
                    "label":"plus(n : Nat, m : Nat) -> -F Nat",
                    "parameters":[{{"label":[5,12]}},{{"label":[14,21]}}]}}],
                    "activeSignature":0,"activeParameter":{active}}}}}]"#
            )))
        };
        assert_eq!(
            ask(&mut server, 27),
            plus(1),
            "past the comma at the end of the text, the second parameter"
        );
        assert_eq!(
            ask(&mut server, 21),
            plus(0),
            "at the first argument, the first"
        );
    }

    #[test]
    fn a_watching_client_is_asked_to_watch_every_source()
    {
        let started = |watching: &str| {
            let mut server = Connected::default();
            let initialize = format!(
                r#"{{"jsonrpc":"2.0","id":1,"method":"initialize","params":{{"capabilities":
                {{"workspace":{{"didChangeWatchedFiles":{{"dynamicRegistration":{watching}}}}}}}}}}}"#
            );
            let _answered = send(&mut server, Json(&initialize));
            server
        };
        let initialized = Json(r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#);
        let mut watching = started("true");
        assert_eq!(
            send(&mut watching, initialized),
            wire(Json(
                r#"[{"jsonrpc":"2.0","id":"client/registerCapability","method":"client/registerCapability",
                    "params":{"registrations":[{"id":"workspace/didChangeWatchedFiles",
                        "method":"workspace/didChangeWatchedFiles",
                        "registerOptions":{"watchers":[{"globPattern":"**/*.gandr"}]}}]}}]"#
            )),
            "a client that registers watchers dynamically is asked to watch every gandr source"
        );
        assert_eq!(
            send(
                &mut watching,
                Json(r#"{"jsonrpc":"2.0","id":"client/registerCapability","result":null}"#)
            ),
            wire(Json("[]")),
            "the client's answer is read and left"
        );
        let shutdown = Json(r#"{"jsonrpc":"2.0","id":9,"method":"shutdown"}"#);
        assert_eq!(
            send(&mut watching, shutdown),
            wire(Json(
                r#"[{"jsonrpc":"2.0","id":"client/unregisterCapability","method":"client/unregisterCapability",
                    "params":{"unregisterations":[{"id":"workspace/didChangeWatchedFiles",
                        "method":"workspace/didChangeWatchedFiles"}]}},
                    {"jsonrpc":"2.0","id":9,"result":null}]"#
            )),
            "at shutdown the watcher is withdrawn before the answer"
        );
        let mut unwatched = started("false");
        assert_eq!(
            send(&mut unwatched, initialized),
            wire(Json("[]")),
            "a client that does not is asked nothing"
        );
        assert_eq!(
            send(&mut unwatched, shutdown),
            wire(Json(r#"[{"jsonrpc":"2.0","id":9,"result":null}]"#)),
            "nor is anything withdrawn from it at shutdown"
        );
    }

    #[test]
    fn the_server_log_is_traced_at_the_level_the_client_sets()
    {
        let mut server = Connected::default();
        let _answered = send(
            &mut server,
            Json(r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"trace":"messages"}}"#),
        );
        let mut version = 0_u32;
        let mut traced = |server: &mut Connected| {
            version = version.saturating_add(1);
            let change = serde_json::json!({"jsonrpc": "2.0", "method": if version == 1 { "textDocument/didOpen" }
                else { "textDocument/didChange" }, "params": {"textDocument": {"uri": "file:///tmp/traced.gandr",
                "languageId": "gandr", "version": version, "text": "def one : Integer ;\ndef one = 1 ;\n"},
                "contentChanges": []}});
            let classified = crate::rpc::classify(&Body::from(change.to_string().into_bytes()));
            let outcome = server.server.answer(&mut server.workspace, classified, &[]);
            serde_json::to_value(server.server.traced(&outcome.log)).expect("the traces encode")
        };
        let set = |server: &mut Connected, value: &str| {
            let message = serde_json::json!({"jsonrpc": "2.0", "method": "$/setTrace", "params": {"value": value}});
            send(server, Json(&message.to_string()))
        };
        let trace = |message: &str| serde_json::json!([{"jsonrpc": "2.0", "method": "$/logTrace", "params": {"message": message}}]);
        assert_eq!(
            traced(&mut server),
            trace("file:///tmp/traced.gandr at version 1"),
            "at `messages` the open is traced by its document and version"
        );
        assert_eq!(
            set(&mut server, "verbose"),
            serde_json::json!([]),
            "setting the level is answered with nothing"
        );
        let verbose = traced(&mut server);
        assert_eq!(
            verbose.pointer("/0/params/message"),
            Some(&serde_json::json!("file:///tmp/traced.gandr at version 2")),
            "at `verbose` the change is traced by its document and version {verbose}"
        );
        assert!(
            verbose
                .pointer("/0/params/verbose")
                .and_then(Value::as_str)
                .is_some_and(|detail| !detail.is_empty()),
            "with what rechecking it cost besides: {verbose}"
        );
        let _unread = set(&mut server, "loud");
        assert_eq!(
            traced(&mut server).as_array().map(Vec::len),
            Some(1),
            "a level that does not read leaves the level as it was"
        );
        let _off = set(&mut server, "off");
        assert_eq!(
            traced(&mut server),
            serde_json::json!([]),
            "at `off` nothing is traced"
        );
    }

    #[test]
    fn a_pulled_setting_applies_as_a_pushed_one()
    {
        let started = |pulling: &str| {
            let mut server = Connected::default();
            let initialize = format!(
                r#"{{"jsonrpc":"2.0","id":1,"method":"initialize","params":{{"capabilities":
                {{"workspace":{{"configuration":{pulling}}}}}}}}}"#
            );
            let _answered = send(&mut server, Json(&initialize));
            server
        };
        let pulled = |number: u32| {
            serde_json::json!([{"jsonrpc": "2.0", "id": format!("workspace/configuration/{number}"),
                "method": "workspace/configuration", "params": {"items": [{"section": "gandr"}]}}])
        };
        let answered = |server: &mut Connected, number: u32, result: &Value| {
            let response = serde_json::json!({"jsonrpc": "2.0", "id": format!("workspace/configuration/{number}"),
                "result": result});
            send(server, Json(&response.to_string()))
        };
        let pushed = |server: &mut Connected, settings: &Value| {
            let message = serde_json::json!({"jsonrpc": "2.0", "method": "workspace/didChangeConfiguration",
                "params": {"settings": settings}});
            send(server, Json(&message.to_string()))
        };
        let warned = |answer: &Value| {
            answer.pointer("/0/method") == Some(&serde_json::json!("window/logMessage"))
                && answer.pointer("/0/params/type") == Some(&serde_json::json!(2_i32))
                && answer
                    .pointer("/0/params/message")
                    .and_then(Value::as_str)
                    .is_some_and(|message| message.contains("`gandr` settings do not read"))
        };
        let mut pulling = started("true");
        assert_eq!(
            send(
                &mut pulling,
                Json(r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#)
            ),
            pulled(1),
            "a client that answers pulls is asked for its `gandr` settings once initialised"
        );
        assert_eq!(
            answered(
                &mut pulling,
                1,
                &serde_json::json!([{"diagnostics": {"verbosity": "debug"}}])
            ),
            serde_json::json!([]),
            "its answer is read"
        );
        assert_eq!(
            pulling.server.verbosity,
            Verbosity::Debug,
            "and applied as a push is"
        );
        assert_eq!(
            pushed(&mut pulling, &Value::Null),
            pulled(2),
            "a push carrying no `gandr` section is followed by a pull"
        );
        assert_eq!(
            pushed(
                &mut pulling,
                &serde_json::json!({"gandr": {"diagnostics": {"verbosity": "detailed"}}})
            ),
            serde_json::json!([]),
            "a push carrying one is read as it came"
        );
        assert_eq!(pulling.server.verbosity, Verbosity::Detailed);
        let unread = answered(
            &mut pulling,
            2,
            &serde_json::json!([{"diagnostics": {"verbosity": "loud"}}]),
        );
        assert!(
            warned(&unread) && pulling.server.verbosity == Verbosity::Detailed,
            "a pulled section that does not read is logged as a warning, none of it applied: {unread}"
        );
        let unpushed = pushed(
            &mut pulling,
            &serde_json::json!({"gandr": {"diagnostics": {"verbosity": "loud"}}}),
        );
        assert!(
            warned(&unpushed) && pulling.server.verbosity == Verbosity::Detailed,
            "and so is a pushed one: {unpushed}"
        );
        assert_eq!(
            answered(&mut pulling, 2, &Value::Null),
            serde_json::json!([]),
            "a pull answered with null applies nothing"
        );
        assert_eq!(
            send(
                &mut pulling,
                Json(
                    r#"{"jsonrpc":"2.0","id":"workspace/configuration/2","error":{"code":-32601,"message":"no"}}"#
                )
            ),
            serde_json::json!([]),
            "nor one answered with an error"
        );
        assert_eq!(pulling.server.verbosity, Verbosity::Detailed);
        let mut pushing = started("false");
        assert_eq!(
            send(
                &mut pushing,
                Json(r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#)
            ),
            serde_json::json!([]),
            "a client that does not answer pulls is asked nothing"
        );
        assert_eq!(
            pushed(&mut pushing, &Value::Null),
            serde_json::json!([]),
            "nor after a push carrying no section"
        );
    }

    #[test]
    fn a_choice_put_to_the_user_reads_its_answer()
    {
        let mut server = initialized();
        let choice = || ChoiceParams {
            kind: MessageType::INFO,
            message: String::from("Recheck every open document?"),
            actions: Vec::from([
                MessageAction {
                    title: String::from("Recheck"),
                },
                MessageAction {
                    title: String::from("Leave"),
                },
            ]),
        };
        let asked = server.server.ask(choice());
        assert_eq!(
            serde_json::to_value(&asked).expect("the request encodes"),
            serde_json::json!({"jsonrpc": "2.0", "id": "window/showMessageRequest/1",
                "method": "window/showMessageRequest", "params": {"type": 3_i32,
                    "message": "Recheck every open document?",
                    "actions": [{"title": "Recheck"}, {"title": "Leave"}]}}),
            "the choice is put under a numbered identifier of its own"
        );
        let id = |number: u32| {
            RequestId::from(serde_json::json!(format!(
                "window/showMessageRequest/{number}"
            )))
        };
        assert_eq!(server.server.chosen(&id(1)), Some(&Choice::Pending));
        let answer = |server: &mut Connected, response: &str| send(server, Json(response));
        assert_eq!(
            answer(
                &mut server,
                r#"{"jsonrpc":"2.0","id":"window/showMessageRequest/1","result":{"title":"Recheck"}}"#
            ),
            serde_json::json!([]),
            "an answer is read, answered with nothing"
        );
        assert_eq!(
            server.server.chosen(&id(1)),
            Some(&Choice::Chose(MessageAction {
                title: String::from("Recheck")
            })),
            "an action chosen is recorded"
        );
        let _second = server.server.ask(choice());
        let _third = server.server.ask(choice());
        let _dismissed = answer(
            &mut server,
            r#"{"jsonrpc":"2.0","id":"window/showMessageRequest/2","result":null}"#,
        );
        let _refused = answer(
            &mut server,
            r#"{"jsonrpc":"2.0","id":"window/showMessageRequest/3","error":{"code":-32800,"message":"no"}}"#,
        );
        assert_eq!(
            (server.server.chosen(&id(2)), server.server.chosen(&id(3))),
            (Some(&Choice::Dismissed), Some(&Choice::Dismissed)),
            "a choice dismissed, or answered with an error, is recorded as dismissed"
        );
        assert_eq!(
            server.server.chosen(&id(4)),
            None,
            "a choice never put is unknown"
        );
    }

    #[test]
    fn a_refreshing_client_is_asked_for_its_lenses_once_a_fill_is_kept_elsewhere()
    {
        let started = |refreshing: &str| {
            let mut server = Connected::default();
            let initialize = format!(
                r#"{{"jsonrpc":"2.0","id":1,"method":"initialize","params":{{"capabilities":
                {{"workspace":{{"codeLens":{{"refreshSupport":{refreshing}}}}}}}}}}}"#
            );
            let _answered = send(&mut server, Json(&initialize));
            server
        };
        let mut refreshing = started("true");
        let asked = |number: u32| {
            Value::Array(vec![wire(Json(&format!(
                r#"{{"jsonrpc":"2.0","id":"workspace/codeLens/refresh/{number}",
                    "method":"workspace/codeLens/refresh"}}"#
            )))])
        };
        let proposed = |connected: &mut Connected| {
            serde_json::to_value(connected.server.proposed_elsewhere(&connected.workspace))
                .expect("the requests encode")
        };
        assert_eq!(
            proposed(&mut refreshing),
            asked(1),
            "the first kept fill asks once"
        );
        assert_eq!(
            proposed(&mut refreshing),
            asked(2),
            "each later one under its own identifier"
        );
        assert_eq!(
            proposed(&mut started("false")),
            serde_json::json!([]),
            "a client that does not refresh is asked nothing"
        );
        assert_eq!(
            proposed(&mut Connected::default()),
            serde_json::json!([]),
            "nor is one not yet initialised"
        );
    }

    #[test]
    fn a_refreshing_client_is_asked_for_its_tokens_and_folds_once_invalidated()
    {
        let started = |workspace: &str| {
            let mut server = Connected::default();
            let initialize = format!(
                r#"{{"jsonrpc":"2.0","id":1,"method":"initialize","params":{{"capabilities":
                {{"workspace":{workspace}}}}}}}"#
            );
            let _answered = send(&mut server, Json(&initialize));
            server
        };
        let asked = |method: &str, number: u32| serde_json::json!({"jsonrpc": "2.0", "id": format!("{method}/{number}"), "method": method});
        let invalidated = |server: &mut Connected| {
            serde_json::to_value(server.server.invalidated_elsewhere())
                .expect("the requests encode")
        };
        let tokens = "workspace/semanticTokens/refresh";
        let folds = "workspace/foldingRange/refresh";
        let mut every = started(
            r#"{"codeLens":{"refreshSupport":true},"semanticTokens":{"refreshSupport":true},
                "foldingRange":{"refreshSupport":true}}"#,
        );
        assert_eq!(
            invalidated(&mut every),
            serde_json::json!([asked(tokens, 1), asked(folds, 2)]),
            "a client refreshing both is asked for its tokens, then its folds"
        );
        assert_eq!(
            serde_json::to_value(every.server.proposed_elsewhere(&every.workspace))
                .expect("the request encodes"),
            serde_json::json!([asked("workspace/codeLens/refresh", 3)]),
            "every refresh is counted on the one connection"
        );
        assert_eq!(
            invalidated(&mut started(
                r#"{"semanticTokens":{"refreshSupport":true}}"#
            )),
            serde_json::json!([asked(tokens, 1)]),
            "one refreshing its tokens alone is asked for those"
        );
        assert_eq!(
            invalidated(&mut started(r#"{"foldingRange":{"refreshSupport":true}}"#)),
            serde_json::json!([asked(folds, 1)]),
            "one refreshing its folds alone is asked for those"
        );
        assert_eq!(
            invalidated(&mut started(r#"{"codeLens":{"refreshSupport":true}}"#)),
            serde_json::json!([]),
            "one refreshing neither is asked nothing"
        );
        assert_eq!(
            invalidated(&mut Connected::default()),
            serde_json::json!([]),
            "nor is one not yet initialised"
        );
    }

    #[test]
    fn a_viewed_tree_answers_its_document_and_is_asked_again_after_each_change()
    {
        let first = "def f = 1 ;\n";
        let started = |workspace: &str| {
            let mut server = Connected::default();
            let _answered = send(
                &mut server,
                Json(&format!(
                    r#"{{"jsonrpc":"2.0","id":1,"method":"initialize","params":{{"capabilities":
                    {{"workspace":{workspace}}}}}}}"#
                )),
            );
            let _opened = send(
                &mut server,
                Json(&serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen",
                    "params": {"textDocument": {"uri": "file:///tmp/tree.gandr", "languageId": "gandr",
                    "version": 1_i32, "text": first}}}).to_string()),
            );
            server
        };
        let content = |server: &mut Connected, id: u32, uri: &str| {
            send(
                server,
                Json(
                    &serde_json::json!({"jsonrpc": "2.0", "id": id,
                    "method": "workspace/textDocumentContent", "params": {"uri": uri}})
                    .to_string(),
                ),
            )
        };
        let tree = |id: u32, text: &str| {
            serde_json::json!([{"jsonrpc": "2.0", "id": id,
                "result": {"text": crate::syntax::printed(gandr_surface_syntax::SourceText::from(text))}}])
        };
        let changed = |server: &mut Connected, version: i32, text: &str| {
            let messages = send(
                server,
                Json(&serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didChange",
                    "params": {"textDocument": {"uri": "file:///tmp/tree.gandr", "version": version},
                    "contentChanges": [{"text": text}]}}).to_string()),
            );
            messages
                .as_array()
                .into_iter()
                .flatten()
                .filter(|message| {
                    message.get("method").and_then(Value::as_str)
                        == Some("workspace/textDocumentContent/refresh")
                })
                .cloned()
                .collect::<Vec<_>>()
        };
        let asked = |number: u32, uri: &str| {
            serde_json::json!({"jsonrpc": "2.0",
                "id": format!("workspace/textDocumentContent/refresh/{number}"),
                "method": "workspace/textDocumentContent/refresh", "params": {"uri": uri}})
        };
        let code = |answer: &Value| answer.pointer("/0/error/code").and_then(Value::as_i64);

        let mut viewing = started(r#"{"textDocumentContent":{"dynamicRegistration":true}}"#);
        assert_eq!(
            content(&mut viewing, 2, "gandr-tree:/tmp/tree.gandr"),
            tree(2, first),
            "a tree URI without its empty authority answers the open document's tree"
        );
        assert_eq!(
            content(&mut viewing, 3, "gandr-tree:///tmp/tree.gandr"),
            tree(3, first),
            "and so does one with it"
        );
        let second = "def f = 2 ;\n";
        assert_eq!(
            changed(&mut viewing, 2_i32, second),
            [
                asked(1, "gandr-tree:///tmp/tree.gandr"),
                asked(2, "gandr-tree:/tmp/tree.gandr")
            ],
            "a change asks for the tree again under each URI the client asked by"
        );
        assert_eq!(
            content(&mut viewing, 4, "gandr-tree:/tmp/tree.gandr"),
            tree(4, second),
            "the tree asked for again is the changed text's"
        );
        assert_eq!(
            code(&content(&mut viewing, 5, "gandr-tree:/tmp/other.gandr")),
            Some(-32_803_i64),
            "a document no editor holds open has no tree"
        );
        assert_eq!(
            code(&content(&mut viewing, 6, "file:///tmp/tree.gandr")),
            Some(-32_602_i64),
            "a URI of another scheme names no tree"
        );
        let _closed = send(
            &mut viewing,
            Json(
                r#"{"jsonrpc":"2.0","method":"textDocument/didClose","params":{"textDocument":{"uri":"file:///tmp/tree.gandr"}}}"#,
            ),
        );
        let _reopened = send(
            &mut viewing,
            Json(
                &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen",
                "params": {"textDocument": {"uri": "file:///tmp/tree.gandr", "languageId": "gandr",
                "version": 1_i32, "text": first}}})
                .to_string(),
            ),
        );
        assert!(
            changed(&mut viewing, 2_i32, second).is_empty(),
            "closing the document forgets that its tree was asked for"
        );

        let mut plain = started("{}");
        assert_eq!(
            content(&mut plain, 2, "gandr-tree:/tmp/tree.gandr"),
            tree(2, first),
            "a client that declares no content provider is answered"
        );
        assert!(
            changed(&mut plain, 2_i32, second).is_empty(),
            "but never asked again"
        );
    }

    #[test]
    fn a_cancelled_progress_is_recorded_against_its_token()
    {
        let mut server = Connected::default();
        let _answered = send(
            &mut server,
            Json(
                r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"capabilities":
                    {"window":{"workDoneProgress":true}}}}"#,
            ),
        );
        let open = Body::from(
            br#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":
                {"uri":"file:///tmp/progress.gandr","languageId":"gandr","version":1,
                 "text":"def one : Integer ;\ndef one = 1 ;\n"}}}"#
                .to_vec(),
        );
        let reported = server
            .server
            .reported(&server.workspace, &crate::rpc::classify(&open));
        assert_eq!(
            reported.end.len(),
            1,
            "the open is reported under `gandr/0/1`"
        );
        let token = |name: &str| ProgressToken(String::from(name));
        let cancel = |server: &mut Connected, name: &str| {
            let message = serde_json::json!({"jsonrpc": "2.0", "method": "window/workDoneProgress/cancel",
                "params": {"token": name}});
            send(server, Json(&message.to_string()))
        };
        assert_eq!(
            server.server.cancelled(&token("gandr/0/1")),
            Cancelled(false),
            "nothing is cancelled before the client asks"
        );
        assert_eq!(
            cancel(&mut server, "gandr/0/1"),
            serde_json::json!([]),
            "a cancellation is a notification, answered with nothing"
        );
        assert_eq!(
            server.server.cancelled(&token("gandr/0/1")),
            Cancelled(true),
            "the work it names is recorded as cancelled"
        );
        let _again = cancel(&mut server, "gandr/0/1");
        let _unissued = cancel(&mut server, "gandr/0/2");
        let _elsewhere = cancel(&mut server, "gandr/1/1");
        let _unread = send(
            &mut server,
            Json(
                r#"{"jsonrpc":"2.0","method":"window/workDoneProgress/cancel","params":{"token":7}}"#,
            ),
        );
        assert_eq!(
            server.server.cancelled,
            [token("gandr/0/1")],
            "the same token again, one not yet issued, another connection's and one that does not \
             read record nothing more"
        );
    }

    #[test]
    fn a_listed_item_resolves_as_it_came()
    {
        let mut server = initialized();
        let resolve = |server: &mut Connected, method: &str, item: &Value| {
            let request = serde_json::json!({"jsonrpc": "2.0", "id": 4_i32, "method": method, "params": item});
            send(server, Json(&request.to_string()))
        };
        let range = serde_json::json!({"start": {"line": 0_i32, "character": 0_i32},
            "end": {"line": 0_i32, "character": 3_i32}});
        for (method, item) in [
            (
                "codeAction/resolve",
                serde_json::json!({"title": "Fill", "kind": "quickfix", "isPreferred": true,
                    "edit": {"changes": {"file:///tmp/a.gandr": [{"range": range, "newText": "1"}]}},
                    "data": {"kept": 2_i32}}),
            ),
            (
                "codeLens/resolve",
                serde_json::json!({"range": range, "command": {"title": "✓ checks", "command": ""}}),
            ),
            (
                "documentLink/resolve",
                serde_json::json!({"range": range, "target": "file:///tmp/base.gandr",
                    "tooltip": "base"}),
            ),
            (
                "workspaceSymbol/resolve",
                serde_json::json!({"name": "Succ", "kind": 9_i32,
                    "location": {"uri": "file:///tmp/base.gandr", "range": range}}),
            ),
        ] {
            assert_eq!(
                resolve(&mut server, method, &item),
                serde_json::json!([{"jsonrpc": "2.0", "id": 4_i32, "result": item}]),
                "{method}: the item as it came, every field the client sent kept"
            );
        }
        for method in [
            "codeAction/resolve",
            "codeLens/resolve",
            "documentLink/resolve",
            "workspaceSymbol/resolve",
        ] {
            assert_eq!(
                resolve(&mut server, method, &serde_json::json!({"kind": 9_i32}))
                    .pointer("/0/error/code"),
                Some(&serde_json::json!(-32_602_i32)),
                "{method}: an item without what its kind requires is refused"
            );
        }
    }

    #[test]
    fn a_changed_file_rechecks_the_copies_whose_closure_names_it()
    {
        let directory = std::env::temp_dir().join(format!("gandr-watched-{}", std::process::id()));
        let _cleared = std::fs::remove_dir_all(&directory);
        std::fs::create_dir_all(&directory).expect("the scratch directory is created");
        let sources = [
            ("base.gandr", "def one : Integer ;\ndef one = 1 ;\n"),
            (
                "importer.gandr",
                "import \"./base.gandr\" ;\ndef two : Integer ;\ndef two = one ;\n",
            ),
            (
                "waiting.gandr",
                "import \"./later.gandr\" ;\ndef three : Integer ;\ndef three = four ;\n",
            ),
            ("alone.gandr", "def five : Integer ;\ndef five = 5 ;\n"),
        ];
        for (file, text) in sources {
            std::fs::write(directory.join(file), text).expect("the source is written");
        }
        let uri = |file: &str| format!("file://{}", directory.join(file).display());
        let mut server = initialized();
        for (file, text) in sources.into_iter().skip(1) {
            let open = serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": uri(file), "languageId": "gandr", "version": 1_i32, "text": text}}});
            let _published = send(&mut server, Json(&open.to_string()));
        }
        let changed = |server: &mut Connected, file: &str, kind: u8| {
            let notification = serde_json::json!({"jsonrpc": "2.0",
                "method": "workspace/didChangeWatchedFiles",
                "params": {"changes": [{"uri": uri(file), "type": kind}]}});
            let published = send(server, Json(&notification.to_string()));
            published
                .as_array()
                .map(|messages| {
                    messages
                        .iter()
                        .map(|message| {
                            (
                                message["params"]["uri"].as_str().map(String::from),
                                message["params"]["diagnostics"]
                                    .as_array()
                                    .map_or(0_usize, Vec::len),
                            )
                        })
                        .collect::<Vec<_>>()
                })
                .unwrap_or_default()
        };
        std::fs::write(
            directory.join("base.gandr"),
            "def uno : Integer ;\ndef uno = 1 ;\n",
        )
        .expect("the sibling is rewritten");
        let rewritten = changed(&mut server, "base.gandr", 2);
        assert!(
            matches!(rewritten.as_slice(), [(Some(published), errors)] if *published == uri("importer.gandr") && *errors > 0),
            "a sibling rewritten without `one` republishes its importer alone, now refused: {rewritten:?}"
        );
        std::fs::write(
            directory.join("later.gandr"),
            "def four : Integer ;\ndef four = 4 ;\n",
        )
        .expect("the missing import is written");
        assert_eq!(
            changed(&mut server, "later.gandr", 1),
            [(Some(uri("waiting.gandr")), 0_usize)],
            "a missing import written republishes the copy that waited for it, now clean"
        );
        assert_eq!(
            changed(&mut server, "elsewhere.gandr", 1),
            [],
            "a file no closure names rechecks nothing"
        );
        let _removed = std::fs::remove_dir_all(&directory);
    }

    #[test]
    fn a_file_operation_rechecks_the_copies_whose_closure_names_it()
    {
        let directory = std::env::temp_dir().join(format!("gandr-operated-{}", std::process::id()));
        let _cleared = std::fs::remove_dir_all(&directory);
        std::fs::create_dir_all(&directory).expect("the scratch directory is created");
        let directory =
            std::fs::canonicalize(&directory).expect("the scratch directory canonicalises");
        let sources = [
            (
                "waiting.gandr",
                "import \"./later.gandr\" ;\ndef three : Integer ;\ndef three = four ;\n",
            ),
            (
                "nested.gandr",
                "import \"./lib/five.gandr\" ;\ndef six : Integer ;\ndef six = five ;\n",
            ),
        ];
        for (file, text) in sources {
            std::fs::write(directory.join(file), text).expect("the source is written");
        }
        let uri = |file: &str| format!("file://{}", directory.join(file).display());
        let mut server = initialized();
        for (file, text) in sources {
            let open = serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": uri(file), "languageId": "gandr", "version": 1_i32, "text": text}}});
            let _published = send(&mut server, Json(&open.to_string()));
        }
        let operated = |server: &mut Connected, method: &str, files: Value| {
            let notification = serde_json::json!({"jsonrpc": "2.0", "method": method,
                "params": {"files": files}});
            send(server, Json(&notification.to_string()))
                .as_array()
                .map(|messages| {
                    messages
                        .iter()
                        .map(|message| {
                            (
                                message["params"]["uri"].as_str().map(String::from),
                                message["params"]["diagnostics"]
                                    .as_array()
                                    .map_or(0_usize, Vec::len),
                            )
                        })
                        .collect::<Vec<_>>()
                })
                .unwrap_or_default()
        };
        std::fs::write(
            directory.join("later.gandr"),
            "def four : Integer ;\ndef four = 4 ;\n",
        )
        .expect("the missing import is written");
        assert_eq!(
            operated(
                &mut server,
                "workspace/didCreateFiles",
                serde_json::json!([{"uri": uri("later.gandr")}])
            ),
            [(Some(uri("waiting.gandr")), 0_usize)],
            "a file created republishes the copy that waited for it, now clean"
        );
        std::fs::create_dir_all(directory.join("lib")).expect("the folder is created");
        std::fs::write(
            directory.join("lib/five.gandr"),
            "def five : Integer ;\ndef five = 5 ;\n",
        )
        .expect("the nested import is written");
        assert_eq!(
            operated(
                &mut server,
                "workspace/didCreateFiles",
                serde_json::json!([{"uri": uri("lib")}])
            ),
            [(Some(uri("nested.gandr")), 0_usize)],
            "a folder created republishes the copy importing a file under it"
        );
        std::fs::remove_file(directory.join("later.gandr")).expect("the import is deleted");
        let deleted = operated(
            &mut server,
            "workspace/didDeleteFiles",
            serde_json::json!([{"uri": uri("later.gandr")}]),
        );
        assert!(
            matches!(deleted.as_slice(), [(Some(published), errors)] if *published == uri("waiting.gandr") && *errors > 0),
            "a file deleted republishes its importer, now refused: {deleted:?}"
        );
        std::fs::rename(directory.join("lib"), directory.join("moved"))
            .expect("the folder is renamed");
        let renamed = operated(
            &mut server,
            "workspace/didRenameFiles",
            serde_json::json!([{"oldUri": uri("lib"), "newUri": uri("moved")}]),
        );
        assert!(
            matches!(renamed.as_slice(), [(Some(published), errors)] if *published == uri("nested.gandr") && *errors > 0),
            "a folder renamed republishes the copy importing a file it held, now refused: {renamed:?}"
        );
        assert_eq!(
            operated(
                &mut server,
                "workspace/didCreateFiles",
                serde_json::json!([{"uri": uri("elsewhere.gandr")}])
            ),
            [],
            "a file no closure names rechecks nothing"
        );
        let _removed = std::fs::remove_dir_all(&directory);
    }

    #[test]
    fn a_moved_file_s_imports_follow_it()
    {
        let directory = std::env::temp_dir().join(format!("gandr-moved-{}", std::process::id()));
        let _cleared = std::fs::remove_dir_all(&directory);
        std::fs::create_dir_all(directory.join("deeper")).expect("the scratch tree is created");
        let directory =
            std::fs::canonicalize(&directory).expect("the scratch directory canonicalises");
        let top = "import \"./deeper/mid.gandr\" ;\ndef three : Integer ;\ndef three = two ;\n";
        for (file, text) in [
            ("base.gandr", "def one : Integer ;\ndef one = 1 ;\n"),
            (
                "deeper/mid.gandr",
                "import \"../base.gandr\" ;\ndef two : Integer ;\ndef two = one ;\n",
            ),
            ("top.gandr", top),
            ("lone.gandr", "def four : Integer ;\ndef four = 4 ;\n"),
        ] {
            std::fs::write(directory.join(file), text).expect("the source is written");
        }
        let uri = |file: &str| format!("file://{}", directory.join(file).display());
        let mut server = Connected::default();
        let initialize = serde_json::json!({"jsonrpc": "2.0", "id": 1_i32, "method": "initialize",
            "params": {"capabilities": {}, "rootUri": format!("file://{}", directory.display())}});
        let _answered = send(&mut server, Json(&initialize.to_string()));
        let open = serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
            "textDocument": {"uri": uri("top.gandr"), "languageId": "gandr", "version": 1_i32, "text": top}}});
        let _published = send(&mut server, Json(&open.to_string()));
        let mut ask = |method: &str, params: Value| {
            let request = serde_json::json!({"jsonrpc": "2.0", "id": 10_i32, "method": method, "params": params});
            send(&mut server, Json(&request.to_string()))
                .get(0)
                .map_or(Value::Null, |answer| answer["result"].clone())
        };
        let mut renamed = |from: &str, to: &str| {
            ask(
                "workspace/willRenameFiles",
                serde_json::json!({"files": [{"oldUri": uri(from), "newUri": uri(to)}]}),
            )
        };
        let edit = |line: u32, start: u32, end: u32, text: &str| {
            serde_json::json!({"range": Range {
                start: at(Line::from(line), Character::from(start)),
                end: at(Line::from(line), Character::from(end)),
            }, "newText": text})
        };
        assert_eq!(
            renamed("base.gandr", "deeper/base.gandr"),
            serde_json::json!({"changes": {uri("deeper/mid.gandr"): [edit(0, 8, 21, "./base.gandr")]}}),
            "the importer no editor holds follows the moved file, read from disk"
        );
        assert_eq!(
            renamed("deeper/mid.gandr", "mid.gandr"),
            serde_json::json!({"changes": {
                uri("deeper/mid.gandr"): [edit(0, 8, 21, "./base.gandr")],
                uri("top.gandr"): [edit(0, 8, 26, "./mid.gandr")],
            }}),
            "the open importer follows the moved file, and the moved file's own import follows it to \
             its new directory"
        );
        assert_eq!(
            renamed("deeper", "renamed"),
            serde_json::json!({"changes": {uri("top.gandr"): [edit(0, 8, 26, "./renamed/mid.gandr")]}}),
            "a folder moved rewrites the imports reaching into it, and none of those moving with it"
        );
        assert_eq!(
            renamed("lone.gandr", "alone.gandr"),
            Value::Null,
            "a move no import names answers nothing"
        );
        for method in ["workspace/willCreateFiles", "workspace/willDeleteFiles"] {
            assert_eq!(
                ask(
                    method,
                    serde_json::json!({"files": [{"uri": uri("lone.gandr")}]})
                ),
                Value::Null,
                "{method} owes no edit"
            );
        }
        assert_eq!(
            ask(
                "textDocument/willSaveWaitUntil",
                serde_json::json!({"textDocument": {"uri": uri("top.gandr")}, "reason": 1_i32})
            ),
            serde_json::json!([]),
            "nothing is owed before a save"
        );
        let _removed = std::fs::remove_dir_all(&directory);
    }

    #[test]
    fn an_editor_s_copy_shadows_the_disk_for_its_importers()
    {
        let directory = std::env::temp_dir().join(format!("gandr-shadowed-{}", std::process::id()));
        let _cleared = std::fs::remove_dir_all(&directory);
        std::fs::create_dir_all(&directory).expect("the scratch directory is created");
        let declares_one = "def one : Integer ;\ndef one = 1 ;\n";
        let declares_uno = "def uno : Integer ;\ndef uno = 1 ;\n";
        let importer = "import \"./base.gandr\" ;\ndef two : Integer ;\ndef two = one ;\n";
        let base = directory.join("base.gandr");
        std::fs::write(&base, declares_one).expect("the base is written");
        std::fs::write(directory.join("importer.gandr"), importer)
            .expect("the importer is written");
        let uri = |file: &str| format!("file://{}", directory.join(file).display());
        let published = |server: &mut Connected, message: &Value| {
            send(server, Json(&message.to_string()))
                .as_array()
                .map(|messages| {
                    messages
                        .iter()
                        .map(|message| {
                            (
                                message["params"]["uri"].as_str().map(String::from),
                                message["params"]["diagnostics"]
                                    .as_array()
                                    .map_or(0_usize, Vec::len),
                            )
                        })
                        .collect::<Vec<_>>()
                })
                .unwrap_or_default()
        };
        let open = |file: &str, text: &str| {
            serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": uri(file), "languageId": "gandr", "version": 1_i32, "text": text}}})
        };
        let mut server = initialized();
        assert_eq!(
            published(&mut server, &open("importer.gandr", importer)),
            [(Some(uri("importer.gandr")), 0_usize)],
            "the importer checks against the base on disk"
        );
        let opened = published(&mut server, &open("base.gandr", declares_uno));
        assert!(
            matches!(opened.as_slice(), [(Some(own), 0_usize), (Some(importing), errors)]
                if *own == uri("base.gandr") && *importing == uri("importer.gandr") && *errors > 0),
            "the base opened without `one` republishes its importer, refused: {opened:?}"
        );
        let watched = serde_json::json!({"jsonrpc": "2.0", "method": "workspace/didChangeWatchedFiles",
            "params": {"changes": [{"uri": uri("base.gandr"), "type": 2_u8}]}});
        assert_eq!(
            published(&mut server, &watched),
            [],
            "a held file changed on disk rechecks nothing"
        );
        let edit = serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didChange", "params": {
            "textDocument": {"uri": uri("base.gandr"), "version": 2_i32},
            "contentChanges": [{"text": declares_one}]}});
        assert_eq!(
            published(&mut server, &edit),
            [
                (Some(uri("base.gandr")), 0_usize),
                (Some(uri("importer.gandr")), 0_usize)
            ],
            "the base edited back to `one` republishes its importer, clean"
        );
        std::fs::write(&base, declares_uno).expect("the base is rewritten");
        let close = serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didClose", "params": {
            "textDocument": {"uri": uri("base.gandr")}}});
        let closed = published(&mut server, &close);
        assert!(
            matches!(closed.as_slice(), [(Some(own), 0_usize), (Some(importing), errors)]
                if *own == uri("base.gandr") && *importing == uri("importer.gandr") && *errors > 0),
            "once the base is closed its importer reads the disk, without `one`: {closed:?}"
        );
        assert_eq!(
            published(&mut server, &open("base.gandr", declares_uno)),
            [(Some(uri("base.gandr")), 0_usize)],
            "a copy opened as the disk holds it rechecks no importer"
        );
        assert_eq!(
            published(&mut server, &close),
            [(Some(uri("base.gandr")), 0_usize)],
            "a copy closed as the disk holds it rechecks no importer"
        );
        let _removed = std::fs::remove_dir_all(&directory);
    }

    /// An importer rechecked because its base changed is classified anew:
    /// a client that refreshes its semantic tokens is asked for them again,
    /// and the importer's use of a name the base now declares is sent as
    /// what it refers to where it was unresolved before; a client that does
    /// not refresh is asked nothing.
    #[test]
    fn an_importer_rechecked_for_its_base_asks_for_its_tokens_again()
    {
        let directory =
            std::env::temp_dir().join(format!("gandr-retokened-{}", std::process::id()));
        let _cleared = std::fs::remove_dir_all(&directory);
        std::fs::create_dir_all(&directory).expect("the scratch directory is created");
        let declares_one = "def one : Integer ;\ndef one = 1 ;\n";
        let declares_uno = "def uno : Integer ;\ndef uno = 1 ;\n";
        let importer = "import \"./base.gandr\" ;\ndef two : Integer ;\ndef two = one ;\n";
        std::fs::write(directory.join("base.gandr"), declares_uno).expect("the base is written");
        std::fs::write(directory.join("importer.gandr"), importer)
            .expect("the importer is written");
        let uri = |file: &str| format!("file://{}", directory.join(file).display());
        let started = |workspace: &str| {
            let mut server = Connected::default();
            let initialize = format!(
                r#"{{"jsonrpc":"2.0","id":1,"method":"initialize","params":{{"capabilities":
                {{"workspace":{workspace}}}}}}}"#
            );
            let _answered = send(&mut server, Json(&initialize));
            let _initialized = send(
                &mut server,
                Json(r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#),
            );
            server
        };
        let open = |server: &mut Connected, file: &str, text: &str| {
            let message = serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen",
                "params": {"textDocument": {"uri": uri(file), "languageId": "gandr",
                "version": 1_i32, "text": text}}});
            send(server, Json(&message.to_string()))
                .as_array()
                .map(|messages| {
                    messages
                        .iter()
                        .filter_map(|message| message["method"].as_str().map(String::from))
                        .filter(|method| method.ends_with("/refresh"))
                        .collect::<Vec<_>>()
                })
                .unwrap_or_default()
        };
        let type_of_one = |server: &mut Connected| {
            let asked = serde_json::json!({"jsonrpc": "2.0", "id": 9_i32,
                "method": "textDocument/semanticTokens/full",
                "params": {"textDocument": {"uri": uri("importer.gandr")}}});
            let data: Vec<u32> = serde_json::from_value(
                send(server, Json(&asked.to_string()))[0]["result"]["data"].clone(),
            )
            .expect("a token stream");
            let (mut line, mut column) = (0_u32, 0_u32);
            data.as_chunks::<5>()
                .0
                .iter()
                .find_map(|&[down, across, _, kind, _]| {
                    column = if down == 0 {
                        column.saturating_add(across)
                    }
                    else {
                        across
                    };
                    line = line.saturating_add(down);
                    ((line, column) == (2, 10)).then_some(kind)
                })
        };
        let mut refreshing = started(r#"{"semanticTokens":{"refreshSupport":true}}"#);
        assert_eq!(
            open(&mut refreshing, "importer.gandr", importer),
            Vec::<String>::new(),
            "opening the importer itself asks for nothing"
        );
        assert_eq!(
            type_of_one(&mut refreshing),
            Some(14),
            "`one`, which the base on disk does not declare, is unresolved"
        );
        assert_eq!(
            open(&mut refreshing, "base.gandr", declares_one),
            ["workspace/semanticTokens/refresh"],
            "the base opened with `one` rechecks the importer and asks for its tokens again"
        );
        assert_eq!(
            type_of_one(&mut refreshing),
            Some(2),
            "`one` is now a function the base declares"
        );
        let mut quiet = started("{}");
        let _importing = open(&mut quiet, "importer.gandr", importer);
        assert_eq!(
            open(&mut quiet, "base.gandr", declares_one),
            Vec::<String>::new(),
            "a client that does not refresh its tokens is asked nothing"
        );
        let _removed = std::fs::remove_dir_all(&directory);
    }

    #[test]
    fn progress_is_reported_around_the_work_a_message_starts()
    {
        let directory = std::env::temp_dir().join(format!("gandr-progress-{}", std::process::id()));
        let _cleared = std::fs::remove_dir_all(&directory);
        std::fs::create_dir_all(&directory).expect("the scratch directory is created");
        let importer = "import \"./base.gandr\" ;\ndef two : Integer ;\ndef two = one ;\n";
        for (file, text) in [
            ("base.gandr", "def one : Integer ;\ndef one = 1 ;\n"),
            ("importer.gandr", importer),
        ] {
            std::fs::write(directory.join(file), text).expect("the source is written");
        }
        let uri = |file: &str| format!("file://{}", directory.join(file).display());
        let started = |shows: &str| {
            let mut server = Connected::default();
            let initialize = format!(
                r#"{{"jsonrpc":"2.0","id":1,"method":"initialize","params":{{"capabilities":
                {{"window":{{"workDoneProgress":{shows}}}}}}}}}"#
            );
            let _answered = send(&mut server, Json(&initialize));
            server
        };
        let reported = |server: &mut Connected, message: &Value| {
            let classified = crate::rpc::classify(&Body::from(message.to_string().into_bytes()));
            let reported = server.server.reported(&server.workspace, &classified);
            let mut outcome = server.server.answer(&mut server.workspace, classified, &[]);
            let _admitted = server.admit(&mut outcome.log);
            let encoded = |messages: &[Outgoing]| {
                Value::Array(
                    messages
                        .iter()
                        .map(|message| serde_json::to_value(message).expect("a message encodes"))
                        .collect(),
                )
            };
            (encoded(&reported.begin), encoded(&reported.end))
        };
        let open = serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
            "textDocument": {"uri": uri("importer.gandr"), "languageId": "gandr", "version": 1_i32,
                "text": importer}}});
        let watched = |file: &str| {
            serde_json::json!({"jsonrpc": "2.0", "method": "workspace/didChangeWatchedFiles",
                "params": {"changes": [{"uri": uri(file), "type": 2_i32}]}})
        };
        let ended = |token: &str| {
            serde_json::json!([{"jsonrpc": "2.0", "method": "$/progress",
                "params": {"token": token, "value": {"kind": "end"}}}])
        };
        let begun = |token: &str, title: &str, message: &str| {
            serde_json::json!([
                {"jsonrpc": "2.0", "id": format!("window/workDoneProgress/create {token}"),
                    "method": "window/workDoneProgress/create", "params": {"token": token}},
                {"jsonrpc": "2.0", "method": "$/progress", "params": {"token": token,
                    "value": {"kind": "begin", "title": title, "cancellable": false, "message": message}}},
            ])
        };
        let nothing = (serde_json::json!([]), serde_json::json!([]));
        let mut shows = started("true");
        assert_eq!(
            reported(&mut shows, &open),
            (
                begun("gandr/0/1", "Checking", "importer.gandr"),
                ended("gandr/0/1")
            ),
            "an open is checked under a progress token of its own"
        );
        assert_eq!(
            reported(&mut shows, &watched("base.gandr")),
            (
                begun("gandr/0/2", "Rechecking", "1 open document"),
                ended("gandr/0/2")
            ),
            "a change to a file a closure names rechecks under the next token"
        );
        assert_eq!(
            reported(
                &mut shows,
                &serde_json::json!({"jsonrpc": "2.0", "method": "workspace/didCreateFiles",
                    "params": {"files": [{"uri": format!("file://{}", directory.display())}]}})
            ),
            (
                begun("gandr/0/3", "Rechecking", "1 open document"),
                ended("gandr/0/3")
            ),
            "a file operation on a folder holding a file a closure names rechecks under the next token"
        );
        assert_eq!(
            reported(&mut shows, &watched("elsewhere.gandr")),
            nothing,
            "a change no closure names reports nothing"
        );
        assert_eq!(
            reported(
                &mut shows,
                &serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didChange", "params": {
                    "textDocument": {"uri": uri("importer.gandr"), "version": 2_i32},
                    "contentChanges": [{"text": "def two : Integer ;\ndef two = 2 ;\n"}]}})
            ),
            nothing,
            "an edit reports nothing"
        );
        assert_eq!(
            reported(
                &mut shows,
                &serde_json::json!({"jsonrpc": "2.0", "id": 2_i32, "method": "textDocument/hover",
                    "params": {"textDocument": {"uri": uri("importer.gandr")},
                        "position": {"line": 0_i32, "character": 0_i32}}})
            ),
            nothing,
            "a request reports nothing"
        );
        assert_eq!(
            reported(&mut started("false"), &open),
            nothing,
            "a client that shows no progress is sent none"
        );
        let _removed = std::fs::remove_dir_all(&directory);
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
            "textDocument/documentLink",
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
    fn a_fold_shows_its_head_only_to_a_client_that_takes_collapsed_text()
    {
        let folds = |capabilities: &str| {
            let mut server = Connected::default();
            let initialize = format!(
                r#"{{"jsonrpc":"2.0","id":1,"method":"initialize","params":{{"capabilities":{capabilities}}}}}"#
            );
            let _answered = send(&mut server, Json(&initialize));
            let open = r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":
                {"uri":"file:///tmp/folded.gandr","languageId":"gandr","version":1,
                 "text":"def f(x: Integer) -> -F Integer {\n  return x\n}\n"}}}"#;
            let _published = send(&mut server, Json(open));
            let request = r#"{"jsonrpc":"2.0","id":9,"method":"textDocument/foldingRange",
                "params":{"textDocument":{"uri":"file:///tmp/folded.gandr"}}}"#;
            send(&mut server, Json(request))
                .pointer("/0/result")
                .cloned()
                .unwrap_or(Value::Null)
        };
        assert_eq!(
            folds(r#"{"textDocument":{"foldingRange":{"foldingRange":{"collapsedText":true}}}}"#),
            wire(Json(
                r#"[{"startLine":0,"endLine":2,"collapsedText":"def f(x: Integer) -> -F Integer { … }"}]"#
            )),
            "a client that takes collapsed text is shown the function's head"
        );
        assert_eq!(
            folds("{}"),
            wire(Json(r#"[{"startLine":0,"endLine":2}]"#)),
            "one that does not is sent the lines alone"
        );
    }

    #[test]
    fn a_path_import_links_to_the_file_it_names()
    {
        let mut server = initialized();
        let open = |server: &mut Connected, uri: &str, text: &str| {
            let notification = format!(
                r#"{{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{{"textDocument":
                    {{"uri":"{uri}","languageId":"gandr","version":1,"text":"{text}"}}}}}}"#
            );
            drop(send(server, Json(&notification)));
        };
        let links = |server: &mut Connected, uri: &str| {
            let request = format!(
                r#"{{"jsonrpc":"2.0","id":9,"method":"textDocument/documentLink","params":{{
                    "textDocument":{{"uri":"{uri}"}}}}}}"#
            );
            send(server, Json(&request))
        };
        let importer = "file:///tmp/links/main.gandr";
        open(
            &mut server,
            importer,
            r#"import \"lib/base.gandr\" as b;\nimport \"std:prelude\";\ndef answer = 1 ;\n"#,
        );
        let file = named_path(Path::new("/tmp/links/lib/base.gandr"));
        let target = DocumentUri::of_path(&file).expect("an absolute path names a file URI");
        let tooltip = file.to_string_lossy();
        assert_eq!(
            links(&mut server, importer),
            wire(Json(&format!(
                r#"[{{"jsonrpc":"2.0","id":9,"result":[{{
                    "range":{{"start":{{"line":0,"character":8}},"end":{{"line":0,"character":22}}}},
                    "target":"{target}","tooltip":"{tooltip}"}}]}}]"#
            ))),
            "the path import's address links to the file beside the importer, its path the \
             tooltip; the scheme import links nowhere"
        );
        let malformed = "file:///tmp/links/malformed.gandr";
        open(
            &mut server,
            malformed,
            r#"import \"lib/base.gandr\" as ;\n"#,
        );
        assert_eq!(
            links(&mut server, malformed),
            wire(Json(r#"[{"jsonrpc":"2.0","id":9,"result":[]}]"#)),
            "imports that do not read link nowhere"
        );
    }

    #[test]
    fn dropped_sources_are_imported_after_the_last_import()
    {
        let directory = std::env::temp_dir().join(format!("gandr-drop-{}", std::process::id()));
        let _cleared = std::fs::remove_dir_all(&directory);
        std::fs::create_dir_all(directory.join("lib")).expect("the scratch tree is created");
        let directory =
            std::fs::canonicalize(&directory).expect("the scratch directory canonicalises");
        for file in [
            "main.gandr",
            "bare.gandr",
            "lib/base.gandr",
            "lib/more.gandr",
        ] {
            std::fs::write(directory.join(file), "").expect("the source is written");
        }
        let uri = |file: &str| {
            DocumentUri::of_path(&directory.join(file)).expect("an absolute path names a file URI")
        };
        let mut server = initialized();
        let open = |server: &mut Connected, file: &str, text: &str| {
            let notification = format!(
                r#"{{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{{"textDocument":
                    {{"uri":"{}","languageId":"gandr","version":1,"text":"{text}"}}}}}}"#,
                uri(file)
            );
            drop(send(server, Json(&notification)));
        };
        let import = |server: &mut Connected, file: &str, files: &[&str]| {
            let files = files
                .iter()
                .map(|dropped| format!("\"{}\"", uri(dropped)))
                .collect::<Vec<_>>()
                .join(",");
            let request = format!(
                r#"{{"jsonrpc":"2.0","id":9,"method":"gandr/importFiles","params":{{
                    "textDocument":{{"uri":"{}"}},"files":[{files}]}}}}"#,
                uri(file)
            );
            send(server, Json(&request))
        };
        open(
            &mut server,
            "main.gandr",
            r#"import \"./lib/base.gandr\" ;\ndef answer = 1 ;\n"#,
        );
        open(&mut server, "bare.gandr", r#"def answer = 1 ;\n"#);
        assert_eq!(
            import(&mut server, "main.gandr", &[
                "lib/base.gandr",
                "lib/more.gandr"
            ]),
            wire(Json(
                r#"[{"jsonrpc":"2.0","id":9,"result":[{
                    "range":{"start":{"line":1,"character":0},"end":{"line":1,"character":0}},
                    "newText":"import \"./lib/more.gandr\" ;\n"}]}]"#
            )),
            "the source not yet imported is imported on the line after the last import"
        );
        assert_eq!(
            import(&mut server, "bare.gandr", &["lib/more.gandr"]),
            wire(Json(
                r#"[{"jsonrpc":"2.0","id":9,"result":[{
                    "range":{"start":{"line":0,"character":0},"end":{"line":0,"character":0}},
                    "newText":"import \"./lib/more.gandr\" ;\n\n"}]}]"#
            )),
            "a document with no import gains it at its start, a blank line after"
        );
        assert_eq!(
            import(&mut server, "main.gandr", &["lib/base.gandr", "main.gandr"]),
            wire(Json(r#"[{"jsonrpc":"2.0","id":9,"result":[]}]"#)),
            "a source imported already, or the document itself, adds nothing"
        );
        let _cleared = std::fs::remove_dir_all(&directory);
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
                "textDocument/rangesFormatting",
                "file:///tmp/loose.gandr",
                r#""ranges":[{"start":{"line":0,"character":5},"end":{"line":0,"character":5}},
                    {"start":{"line":0,"character":0},"end":{"line":0,"character":3}}],"#
            ),
            wire(Json(
                r#"[{"jsonrpc":"2.0","id":7,"result":[{
                    "range":{"start":{"line":0,"character":4},"end":{"line":0,"character":9}},
                    "newText":"f ="}]}]"#
            )),
            "two ranges in one form: its edit once"
        );
        assert_eq!(
            ask(
                &mut server,
                "textDocument/onTypeFormatting",
                "file:///tmp/loose.gandr",
                r#""position":{"line":0,"character":14},"ch":";","#
            ),
            wire(Json(
                r#"[{"jsonrpc":"2.0","id":7,"result":[{
                    "range":{"start":{"line":0,"character":4},"end":{"line":0,"character":9}},
                    "newText":"f ="}]}]"#
            )),
            "a `;` closing the form: the form laid out"
        );
        assert_eq!(
            ask(
                &mut server,
                "textDocument/willSaveWaitUntil",
                "file:///tmp/loose.gandr",
                r#""reason":1,"#
            ),
            wire(Json(
                r#"[{"jsonrpc":"2.0","id":7,"result":[{
                    "range":{"start":{"line":0,"character":4},"end":{"line":0,"character":9}},
                    "newText":"f ="}]}]"#
            )),
            "a save about to happen: the whole document's edits"
        );
        assert_eq!(
            ask(
                &mut server,
                "textDocument/onTypeFormatting",
                "file:///tmp/loose.gandr",
                r#""position":{"line":0,"character":14},"ch":"x","#
            ),
            wire(Json(r#"[{"jsonrpc":"2.0","id":7,"result":[]}]"#)),
            "another character: no edit"
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
    fn no_position_names_a_type_hierarchy()
    {
        let mut server = server_over_the_known_document();
        assert_eq!(
            send(
                &mut server,
                Json(
                    r#"{"jsonrpc":"2.0","id":7,"method":"textDocument/prepareTypeHierarchy",
                        "params":{"textDocument":{"uri":"file:///tmp/example.gandr"},
                        "position":{"line":0,"character":4}}}"#
                )
            ),
            wire(Json(r#"[{"jsonrpc":"2.0","id":7,"result":null}]"#)),
            "a declared name: no hierarchy to prepare"
        );
        for method in ["typeHierarchy/supertypes", "typeHierarchy/subtypes"] {
            let request = format!(
                r#"{{"jsonrpc":"2.0","id":7,"method":"{method}","params":{{"item":{{}}}}}}"#
            );
            assert_eq!(
                send(&mut server, Json(&request)),
                wire(Json(r#"[{"jsonrpc":"2.0","id":7,"result":null}]"#)),
                "{method}: none"
            );
        }
        assert_eq!(
            send(
                &mut server,
                Json(
                    r#"{"jsonrpc":"2.0","id":7,"method":"textDocument/prepareTypeHierarchy","params":{}}"#
                )
            )[0]["error"]["code"],
            serde_json::json!(-32602_i32),
            "a request naming no position is refused"
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

    /// A data type, a recursive function over it and a numeral built of its
    /// constructors: each line names what a definition request there reads.
    const REFERRED: &str = "data Nat : Type {\n  Zero : Nat;\n  Succ : (n : Nat) --> Nat;\n}\n\
                            def rec plus(n : Nat, m : Nat) -> -F Nat {\n  case m {\n    Zero \
                            => n,\n    Succ(p) => Succ(plus[<](n, p))\n  }\n}\ndef two : Nat ;\n\
                            def two = Succ(Succ(Zero)) ;\n";

    /// A running server whose client takes definitions as links as `linked`
    /// says, holding [`REFERRED`] at `file:///tmp/referred.gandr`.
    ///
    /// # Specification
    /// trivial.
    fn referring(linked: Linked) -> Connected
    {
        let mut server = Connected::default();
        let initialize = format!(
            r#"{{"jsonrpc":"2.0","id":1,"method":"initialize","params":{{"capabilities":
                {{"textDocument":{{"definition":{{"linkSupport":{}}}}}}}}}}}"#,
            linked.0
        );
        let _answered = send(&mut server, Json(&initialize));
        let open = format!(
            r#"{{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{{"textDocument":
                {{"uri":"file:///tmp/referred.gandr","languageId":"gandr","version":1,
                 "text":{}}}}}}}"#,
            Value::String(REFERRED.to_owned())
        );
        let _published = send(&mut server, Json(&open));
        server
    }

    /// What the `goto` request at `position` of `uri` answers `server`.
    ///
    /// # Specification
    /// trivial.
    fn going(
        server: &mut Connected,
        goto: Goto,
        uri: &DocumentUri,
        position: Position,
    ) -> Value
    {
        let method = match goto {
            Goto::Definition => "textDocument/definition",
            Goto::Declaration => "textDocument/declaration",
            Goto::TypeDefinition => "textDocument/typeDefinition",
        };
        let request = serde_json::json!({
            "jsonrpc": "2.0", "id": 6_i32, "method": method,
            "params": {"textDocument": {"uri": uri.to_string()}, "position": position},
        });
        send(server, Json(&request.to_string()))
            .pointer("/0/result")
            .cloned()
            .unwrap_or(Value::Null)
    }

    /// One link in [`REFERRED`], from `origin` to `whole` with `named`
    /// selected.
    ///
    /// # Specification
    /// trivial.
    fn link(
        origin: Range,
        whole: Range,
        named: Range,
    ) -> Value
    {
        serde_json::json!({
            "originSelectionRange": origin,
            "targetUri": "file:///tmp/referred.gandr",
            "targetRange": whole,
            "targetSelectionRange": named,
        })
    }

    /// The position at `line` and `character`.
    ///
    /// # Specification
    /// trivial.
    fn at(
        line: Line,
        character: Character,
    ) -> Position
    {
        Position { line, character }
    }

    #[test]
    fn definition_answers_what_a_use_refers_to_795()
    {
        let uri = DocumentUri::from("file:///tmp/referred.gandr");
        let mut linked = referring(Linked(true));
        let mut located = referring(Linked(false));
        let position = |line: u32, character: u32| at(Line::from(line), Character::from(character));
        let range = |line: u32, start: u32, end: u32| Range {
            start: position(line, start),
            end: position(line, end),
        };
        let definition = |server: &mut Connected, line, character| {
            going(server, Goto::Definition, &uri, position(line, character))
        };
        let n = range(4, 13, 14);
        let plus = range(4, 8, 12);
        let nat = Range {
            start: position(0, 0),
            end: position(3, 1),
        };
        let succ = range(2, 2, 6);
        assert_eq!(
            definition(&mut linked, 6, 12),
            Value::Array(vec![link(range(6, 12, 13), n, n)]),
            "a parameter's use links to its binder"
        );
        assert_eq!(
            definition(&mut located, 6, 12),
            serde_json::json!([{"uri": "file:///tmp/referred.gandr", "range": n}]),
            "a client without links is answered the binder's location"
        );
        assert_eq!(
            definition(&mut linked, 6, 13),
            definition(&mut linked, 6, 12),
            "a caret just past a name answers the name"
        );
        assert_eq!(
            definition(&mut linked, 7, 21),
            Value::Array(vec![link(range(7, 20, 24), plus, plus)]),
            "a recursive call links to its declaration from its name, its marker aside (#827)"
        );
        assert_eq!(
            definition(&mut linked, 7, 31),
            Value::Array(vec![link(
                range(7, 31, 32),
                range(7, 9, 10),
                range(7, 9, 10)
            )]),
            "a pattern's binder is the referent of its use in the arm"
        );
        assert_eq!(
            definition(&mut linked, 7, 4),
            Value::Array(vec![link(range(7, 4, 8), nat, succ)]),
            "a constructor in a pattern links to its family with the constructor selected"
        );
        assert_eq!(
            definition(&mut linked, 11, 18),
            Value::Array(vec![link(range(11, 15, 19), nat, succ)]),
            "a constructor nested in another's arguments answers itself, from its name"
        );
        assert_eq!(
            definition(&mut linked, 11, 11),
            Value::Array(vec![link(range(11, 10, 14), nat, succ)]),
            "a constructor applied links from its name, not from its arguments (#827)"
        );
        assert_eq!(
            definition(&mut linked, 10, 10),
            Value::Array(vec![link(range(10, 10, 13), nat, range(0, 5, 8))]),
            "a written type links to its family"
        );
        assert_eq!(
            definition(&mut linked, 4, 1),
            Value::Array(vec![]),
            "a keyword refers to nothing"
        );
        assert_eq!(
            going(
                &mut linked,
                Goto::Definition,
                &DocumentUri::from("file:///tmp/closed.gandr"),
                position(0, 0)
            ),
            Value::Null,
            "a document the server does not hold answers null"
        );
    }

    #[test]
    fn a_highlight_marks_a_name_s_declaration_and_its_uses()
    {
        let mut server = referring(Linked(true));
        let mut highlight = |uri: &str, line: u32, character: u32| {
            let request = serde_json::json!({
                "jsonrpc": "2.0", "id": 7_i32, "method": "textDocument/documentHighlight",
                "params": {"textDocument": {"uri": uri},
                    "position": at(Line::from(line), Character::from(character))},
            });
            send(&mut server, Json(&request.to_string()))
                .pointer("/0/result")
                .cloned()
                .unwrap_or(Value::Null)
        };
        let mark = |kind: u8, line: u32, start: u32, end: u32| {
            serde_json::json!({"range": Range {
                start: at(Line::from(line), Character::from(start)),
                end: at(Line::from(line), Character::from(end)),
            }, "kind": kind})
        };
        let uri = "file:///tmp/referred.gandr";
        let n = Value::Array(vec![
            mark(1, 4, 13, 14),
            mark(2, 6, 12, 13),
            mark(2, 7, 28, 29),
        ]);
        assert_eq!(
            highlight(uri, 6, 12),
            n,
            "a parameter's use marks its binder, its use in an arm and in the recursive call"
        );
        assert_eq!(highlight(uri, 4, 13), n, "the binder marks the same");
        assert_eq!(
            highlight(uri, 6, 13),
            n,
            "a caret just past a name marks it"
        );
        let plus = Value::Array(vec![mark(1, 4, 8, 12), mark(2, 7, 20, 24)]);
        assert_eq!(
            highlight(uri, 4, 9),
            plus,
            "a recursive declaration marks its name and its call"
        );
        assert_eq!(highlight(uri, 7, 21), plus, "its call marks the same");
        assert_eq!(
            highlight(uri, 7, 5),
            Value::Array(vec![
                mark(1, 2, 2, 6),
                mark(2, 7, 4, 8),
                mark(2, 7, 15, 19),
                mark(2, 11, 10, 14),
                mark(2, 11, 15, 19),
            ]),
            "a constructor marks its name in the family, its pattern and its terms"
        );
        assert_eq!(
            highlight(uri, 4, 1),
            Value::Array(vec![]),
            "a keyword marks nothing"
        );
        assert_eq!(
            highlight("file:///tmp/closed.gandr", 0, 0),
            Value::Null,
            "a document the server does not hold answers null"
        );
    }

    #[test]
    fn linked_editing_mirrors_a_binder_within_its_declaration()
    {
        let mut server = referring(Linked(true));
        let mut linked = |uri: &str, line: u32, character: u32| {
            let request = serde_json::json!({
                "jsonrpc": "2.0", "id": 7_i32, "method": "textDocument/linkedEditingRange",
                "params": {"textDocument": {"uri": uri},
                    "position": at(Line::from(line), Character::from(character))},
            });
            send(&mut server, Json(&request.to_string()))
                .pointer("/0/result")
                .cloned()
                .unwrap_or(Value::Null)
        };
        let ranges = |sites: &[(u32, u32, u32)]| {
            serde_json::json!({"ranges": sites.iter().map(|&(line, start, end)| Range {
                start: at(Line::from(line), Character::from(start)),
                end: at(Line::from(line), Character::from(end)),
            }).collect::<Vec<_>>(), "wordPattern": gandr_surface_parser::WORD_PATTERN})
        };
        let uri = "file:///tmp/referred.gandr";
        let n = ranges(&[(4, 13, 14), (6, 12, 13), (7, 28, 29)]);
        assert_eq!(
            linked(uri, 4, 13),
            n,
            "a parameter's binder links itself and its uses"
        );
        assert_eq!(linked(uri, 7, 28), n, "a use links the same ranges");
        assert_eq!(
            linked(uri, 7, 9),
            ranges(&[(7, 9, 10), (7, 31, 32)]),
            "a binder a constructor pattern introduces links its use"
        );
        assert_eq!(
            linked(uri, 4, 9),
            Value::Null,
            "a declaration's name, which importers may use, links nothing"
        );
        assert_eq!(linked(uri, 7, 5), Value::Null, "nor does a constructor");
        assert_eq!(linked(uri, 4, 1), Value::Null, "a keyword links nothing");
        assert_eq!(
            linked("file:///tmp/closed.gandr", 0, 0),
            Value::Null,
            "a document the server does not hold answers null"
        );
    }

    #[test]
    fn type_definition_answers_the_family_a_use_s_type_names_795()
    {
        let uri = DocumentUri::from("file:///tmp/referred.gandr");
        let mut linked = referring(Linked(true));
        let position = |line: u32, character: u32| at(Line::from(line), Character::from(character));
        let range = |line: u32, start: u32, end: u32| Range {
            start: position(line, start),
            end: position(line, end),
        };
        let mut type_definition = |line, character| {
            going(
                &mut linked,
                Goto::TypeDefinition,
                &uri,
                position(line, character),
            )
        };
        let whole = Range {
            start: position(0, 0),
            end: position(3, 1),
        };
        let nat = |origin| Value::Array(vec![link(origin, whole, range(0, 5, 8))]);
        assert_eq!(
            type_definition(6, 12),
            nat(range(6, 12, 13)),
            "a parameter's use is typed by the family"
        );
        assert_eq!(
            type_definition(7, 9),
            nat(range(7, 9, 10)),
            "so is a binder in a constructor pattern"
        );
        assert_eq!(
            type_definition(11, 10),
            nat(range(11, 10, 26)),
            "and a numeral built of its constructors"
        );
        assert_eq!(
            type_definition(0, 1),
            Value::Array(vec![]),
            "a keyword types nothing"
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
            (configure("null"), "a section that names none"),
        ] {
            assert!(
                server.handle(&unchanged).messages.is_empty(),
                "{why} republishes nothing"
            );
        }
        let unread = server.handle(&configure(r#""loud""#)).messages;
        assert!(
            matches!(unread.as_slice(), [Outgoing::Notification {
                method: "window/logMessage",
                ..
            }]),
            "a value that names no level republishes nothing, and is logged as a warning: {unread:?}"
        );
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

    /// #782: a connection writes types in its workspace's configured spelling
    /// until its editor names one; naming another respells the next hover and
    /// republishes every diagnostic in it.
    #[test]
    fn a_presentation_spelling_respells_hovers_and_diagnostics_782()
    {
        let mut server = Connected {
            server: Server::default(),
            workspace: Workspace::spelled(super::Spelling::Ascii),
        };
        let _answered = send(
            &mut server,
            Json(r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"capabilities":{}}}"#),
        );
        let opened = send(
            &mut server,
            Json(
                r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{
                    "uri":"file:///tmp/r.gandr","languageId":"gandr","version":1,
                    "text":"def r : Integer ≃ String ;\ndef r = 1 ;\n"}}}"#,
            ),
        );
        let message = |published: &Value| {
            published
                .pointer("/0/params/diagnostics/0/message")
                .and_then(Value::as_str)
                .map(str::to_owned)
                .unwrap_or_default()
        };
        let hovered = |server: &mut Connected| {
            send(
                server,
                Json(
                    r#"{"jsonrpc":"2.0","id":5,"method":"textDocument/hover","params":{
                        "textDocument":{"uri":"file:///tmp/r.gandr"},
                        "position":{"line":0,"character":4}}}"#,
                ),
            )
            .pointer("/0/result/contents/value")
            .and_then(Value::as_str)
            .map(str::to_owned)
        };
        assert!(
            message(&opened).contains("expected `Integer <~> String`"),
            "the configured spelling publishes: {opened}"
        );
        assert_eq!(
            hovered(&mut server),
            Some(String::from(
                "```gandr\nr : Integer <~> String\n```\n\nrefused: the type this term \
                 synthesises does not convert to the type it is checked against"
            )),
            "and hovers"
        );
        let republished: Vec<Value> = server
            .handle(&Body::from(
                br#"{"jsonrpc":"2.0","method":"workspace/didChangeConfiguration",
                    "params":{"settings":{"gandr":{"presentation":{"spelling":"unicode"}}}}}"#
                    .to_vec(),
            ))
            .messages
            .iter()
            .map(|outgoing| serde_json::to_value(outgoing).expect("a message encodes"))
            .collect();
        assert!(
            message(&Value::from(republished.clone())).contains("expected `Integer ≃ String`"),
            "the editor's spelling republishes: {republished:?}"
        );
        assert_eq!(
            hovered(&mut server),
            Some(String::from(
                "```gandr\nr : Integer ≃ String\n```\n\nrefused: the type this term \
                 synthesises does not convert to the type it is checked against"
            )),
            "and the next hover answers in it"
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
    fn a_request_withdrawn_by_a_later_message_is_not_run()
    {
        let mut server = server_over_the_known_document();
        let read = |text: &str| crate::rpc::classify(&Body::from(text.as_bytes().to_vec()));
        let answer = |server: &mut Connected, request: &str, later: &[&str]| {
            let later: Vec<Classified> = later.iter().map(|&text| read(text)).collect();
            Value::Array(
                server
                    .server
                    .answer(&mut server.workspace, read(request), &later)
                    .messages
                    .iter()
                    .map(|outgoing| serde_json::to_value(outgoing).expect("a message encodes"))
                    .collect(),
            )
        };
        let hover = r#"{"jsonrpc":"2.0","id":5,"method":"textDocument/hover","params":{
            "textDocument":{"uri":"file:///tmp/example.gandr"},"position":{"line":0,"character":4}}}"#;
        let cancel = |id: u32| {
            format!(r#"{{"jsonrpc":"2.0","method":"$/cancelRequest","params":{{"id":{id}}}}}"#)
        };
        let change = r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{
            "textDocument":{"uri":"file:///tmp/example.gandr","version":2},"contentChanges":[]}}"#;
        assert_eq!(
            answer(&mut server, hover, &[&cancel(5)]),
            wire(Json(
                r#"[{"jsonrpc":"2.0","id":5,"error":{"code":-32800,"message":"the client cancelled the request"}}]"#
            )),
            "a cancellation read after the hover"
        );
        assert_eq!(
            answer(&mut server, hover, &[change]),
            wire(Json(
                r#"[{"jsonrpc":"2.0","id":5,"error":{"code":-32801,"message":"the document changed before the request was read"}}]"#
            )),
            "a change of its document read after it"
        );
        let ran = answer(&mut server, hover, &[&cancel(6)]);
        assert!(
            ran.pointer("/0/error").is_none() && ran.pointer("/0/result").is_some(),
            "a cancellation of another request leaves the hover run: {ran}"
        );
        let shutdown = r#"{"jsonrpc":"2.0","id":9,"method":"shutdown"}"#;
        assert_eq!(
            answer(&mut server, shutdown, &[&cancel(9)]),
            wire(Json(r#"[{"jsonrpc":"2.0","id":9,"result":null}]"#)),
            "the lifecycle is never withdrawn"
        );
        assert_eq!(server.closed(), Served::Clean);
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
                text: String::from("pure 3\n"),
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
            settles: Settles::default(),
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
        let inbox = crate::quiet::Inbox::default();
        workspace.hear_edits(first.peer, inbox.changes());
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
        assert_eq!(
            kept(&workspace),
            Some(vec![Proposal {
                settles: Settles(true),
                ..fill(hole, Json("42"), None)
            }]),
            "the kept fill records that it settles the document"
        );
        let mut met = Vec::new();
        let mut nothing: &[u8] = &[];
        let _ended = crate::quiet::paced(&mut nothing, inbox, |seen, _deadlines| {
            let closed = matches!(seen, crate::quiet::Met::Closed);
            met.push(format!("{seen:?}"));
            Ok(if closed {
                core::ops::ControlFlow::Break(())
            }
            else {
                core::ops::ControlFlow::Continue(())
            })
        });
        assert_eq!(
            met,
            ["Proposed", "Closed"],
            "the connection holding the document hears of the kept fill once, and of no refused one"
        );
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
        let fills: Vec<&Value> = lenses
            .as_array()
            .map(|lenses| {
                lenses
                    .iter()
                    .filter(|lens| lens.get("data").is_none())
                    .collect()
            })
            .unwrap_or_default();
        assert_eq!(
            fills
                .iter()
                .map(|lens| lens.pointer("/command/title").cloned())
                .collect::<Vec<_>>(),
            vec![
                Some(serde_json::json!("2 checked fills")),
                Some(serde_json::json!("1 checked fill"))
            ]
        );
        assert!(
            fills.iter().all(|lens| {
                lens.pointer("/command/command") == Some(&serde_json::json!(""))
                    && lens.pointer("/command/arguments").is_none()
            }),
            "a client that applies no edit the server asks of it is offered no lens command: {lenses}"
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

    #[test]
    fn a_fill_that_settles_its_document_is_the_preferred_fix()
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
        let partial = on_line(
            Line::from(1_u32),
            Character::from(8_u32),
            Character::from(15_u32),
        );
        let whole = Range {
            start: partial.start,
            end: at(Line::from(3_u32), Character::from(14_u32)),
        };
        for proposal in [
            fill(partial, Json("42"), None),
            fill(whole, Json("42 ;\ndef g : Integer ;\ndef g = 1"), None),
        ] {
            assert!(workspace.propose(&uri, held, proposal).is_ok());
        }
        let at_f = serde_json::json!({"range": {"start": {"line": 1_u32, "character": 8_u32},
            "end": {"line": 1_u32, "character": 15_u32}},
            "severity": 1_u8, "source": "gandr", "message": "f", "data": {"kept": "as sent"}});
        let at_g = serde_json::json!({"range": {"start": {"line": 3_u32, "character": 8_u32},
            "end": {"line": 3_u32, "character": 14_u32}},
            "severity": 1_u8, "source": "gandr", "message": "g"});
        let actions = asked(
            &workspace,
            Json("textDocument/codeAction"),
            Json(&format!(
                r#","range":{{"start":{{"line":1,"character":9}},"end":{{"line":1,"character":9}}}},"context":{{"diagnostics":[{at_f},{at_g}]}}"#
            )),
        );
        assert_eq!(
            actions.pointer("/0/diagnostics"),
            Some(&serde_json::json!([at_f])),
            "a fill names the diagnostic at its range, as the client sent it, and not one elsewhere"
        );
        assert_eq!(
            actions.pointer("/0/isPreferred"),
            None,
            "a fill that leaves an error is not preferred"
        );
        assert_eq!(
            actions.pointer("/1/diagnostics"),
            Some(&serde_json::json!([at_f, at_g])),
            "a fill over both refusals names both"
        );
        assert_eq!(
            actions.pointer("/1/isPreferred"),
            Some(&serde_json::json!(true)),
            "a fill that settles the document is preferred"
        );
    }

    /// The recovery fixture of #1391, open in the editor, is refused for the
    /// brace its definition never closes; the diagnostic the server judged,
    /// sent back with a code action request, is offered the brace past
    /// `return n + 1` as a preferred fix naming it.
    #[test]
    fn a_repaired_form_is_offered_its_closing()
    {
        let (mut workspace, [mut first, _second]) = two_connections();
        let uri = crate::protocol::DocumentUri::from("file:///tmp/shared.gandr");
        let path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../surface-parser/tests/fixtures/unclosed-body.gandr");
        let written = std::fs::read_to_string(&path).expect("the fixture is read");
        let opened = format!(
            r#","version":1,"text":{}}}"#,
            serde_json::to_string(&written).expect("the text serialises")
        );
        drop(first.handle(
            &mut workspace,
            &shared(Json("textDocument/didOpen"), Json(&opened)),
        ));
        let judged = workspace
            .documents
            .get(&uri)
            .map(|held| serde_json::to_value(&held.document.checked))
            .expect("the document is held")
            .expect("the diagnostics serialise");
        let refusal = judged
            .as_array()
            .and_then(|all| {
                all.iter().find(|diagnostic| {
                    diagnostic.get("code") == Some(&serde_json::json!("MalformedForm"))
                })
            })
            .cloned()
            .expect("the open body is refused");
        let end = at(Line::from(4_u32), Character::from(14_u32));
        assert_eq!(
            refusal.pointer("/range/start"),
            Some(&serde_json::json!(end)),
            "the refusal stands past the body, where #1391 placed it"
        );
        let actions = asked(
            &workspace,
            Json("textDocument/codeAction"),
            Json(&format!(
                r#","range":{{"start":{{"line":4,"character":14}},"end":{{"line":4,"character":14}}}},"context":{{"diagnostics":[{refusal}]}}"#
            )),
        );
        assert_eq!(
            actions,
            serde_json::json!([{
                "title": "Insert `}`",
                "kind": "quickfix",
                "diagnostics": [refusal],
                "isPreferred": true,
                "edit": {"changes": {"file:///tmp/shared.gandr": [
                    {"range": {"start": end, "end": end}, "newText": " }"}
                ]}},
            }]),
            "the brace the parser expects, inserted where the refusal stands"
        );
    }

    /// A lens over a range's one checked fill runs the command applying it:
    /// the server asks the client to apply the fill's edit and answers the
    /// command with nothing, a refused edit is logged with its reason, and
    /// once the document's next edit withdraws the fill the same command is
    /// refused as content modified.
    #[test]
    fn a_lens_applies_its_one_checked_fill()
    {
        let mut server = Connected::default();
        let _answered = send(
            &mut server,
            Json(
                r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"capabilities":{"workspace":{"applyEdit":true}}}}"#,
            ),
        );
        let _published = send(
            &mut server,
            Json(
                r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":
                    {"uri":"file:///tmp/fill.gandr","languageId":"gandr","version":1,
                     "text":"def f : Integer ;\ndef f = missing ;\n"}}}"#,
            ),
        );
        let uri = DocumentUri::from("file:///tmp/fill.gandr");
        let version = serde_json::from_value(serde_json::json!(1_i32)).expect("a version");
        let hole = on_line(
            Line::from(1_u32),
            Character::from(8_u32),
            Character::from(15_u32),
        );
        assert!(
            server
                .workspace
                .propose(&uri, version, fill(hole, Json("42"), None))
                .is_ok(),
            "the fill settles the document and is kept"
        );
        let range = serde_json::json!({"start": {"line": 1_u32, "character": 8_u32},
            "end": {"line": 1_u32, "character": 15_u32}});
        let listed = send(
            &mut server,
            Json(
                r#"{"jsonrpc":"2.0","id":2,"method":"textDocument/codeLens","params":{"textDocument":{"uri":"file:///tmp/fill.gandr"}}}"#,
            ),
        );
        assert_eq!(
            listed
                .pointer("/0/result")
                .and_then(Value::as_array)
                .and_then(|lenses| lenses.iter().find(|lens| lens.get("data").is_none()))
                .and_then(|lens| lens.get("command")),
            Some(
                &serde_json::json!({"title": "1 checked fill", "command": "gandr.applyFill",
                "arguments": ["file:///tmp/fill.gandr", range, "42"]})
            ),
            "the one fill's lens names the command and the fill"
        );
        let execute = |id: u32| {
            format!(
                r#"{{"jsonrpc":"2.0","id":{id},"method":"workspace/executeCommand","params":{{"command":"gandr.applyFill","arguments":["file:///tmp/fill.gandr",{range},"42"]}}}}"#
            )
        };
        assert_eq!(
            send(&mut server, Json(&execute(3))),
            serde_json::json!([
                {"jsonrpc": "2.0", "id": "workspace/applyEdit/1", "method": "workspace/applyEdit",
                    "params": {"label": "Apply the checked fill",
                        "edit": {"changes": {"file:///tmp/fill.gandr": [{"range": range, "newText": "42"}]}}}},
                {"jsonrpc": "2.0", "id": 3_u32, "result": null}
            ]),
            "the server asks the client to apply the fill, then answers the command"
        );
        assert_eq!(
            send(
                &mut server,
                Json(
                    r#"{"jsonrpc":"2.0","id":"workspace/applyEdit/1","result":{"applied":false,"failureReason":"the document is read-only"}}"#,
                ),
            ),
            serde_json::json!([{"jsonrpc": "2.0", "method": "window/logMessage",
                "params": {"type": 2_u8,
                    "message": "the editor did not apply the checked fill: the document is read-only"}}]),
            "an edit the client refused is logged with its reason"
        );
        assert_eq!(
            send(
                &mut server,
                Json(r#"{"jsonrpc":"2.0","id":"workspace/applyEdit/1","result":{"applied":true}}"#),
            ),
            serde_json::json!([]),
            "an applied one is read and left"
        );
        let _changed = send(
            &mut server,
            Json(
                r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":
                    {"uri":"file:///tmp/fill.gandr","version":2},
                    "contentChanges":[{"text":"def f : Integer ;\ndef f = missing ;\n"}]}}"#,
            ),
        );
        assert_eq!(
            send(&mut server, Json(&execute(4))).pointer("/0/error/code"),
            Some(&serde_json::json!(-32_801_i32)),
            "a fill the next edit withdrew is no longer applied"
        );
        assert_eq!(
            send(
                &mut server,
                Json(
                    r#"{"jsonrpc":"2.0","id":5,"method":"workspace/executeCommand","params":{"command":"gandr.unknown"}}"#,
                ),
            )
            .pointer("/0/error/code"),
            Some(&serde_json::json!(-32_602_i32)),
            "a command the server does not run is refused"
        );
    }

    /// A fill kept elsewhere for a document an editor holds is offered to
    /// its user once, shown when the user chooses to, and offered again only
    /// once the next edit withdrew what was offered; a client that shows no
    /// document is offered nothing.
    #[test]
    fn a_fill_kept_elsewhere_is_offered_to_its_editor_once()
    {
        let mut server = Connected::default();
        let _answered = send(
            &mut server,
            Json(
                r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"capabilities":{"window":{"showDocument":{"support":true}}}}}"#,
            ),
        );
        let _published = send(
            &mut server,
            Json(
                r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":
                    {"uri":"file:///tmp/offered.gandr","languageId":"gandr","version":1,
                     "text":"def f : Integer ;\ndef f = missing ;\n"}}}"#,
            ),
        );
        let uri = DocumentUri::from("file:///tmp/offered.gandr");
        let hole = on_line(
            Line::from(1_u32),
            Character::from(8_u32),
            Character::from(15_u32),
        );
        let propose = |server: &mut Connected, version: i32, text: &str| {
            let version = serde_json::from_value(serde_json::json!(version)).expect("a version");
            server
                .workspace
                .propose(&uri, version, fill(hole, Json(text), None))
                .is_ok()
        };
        let offered = |server: &mut Connected| {
            serde_json::to_value(server.server.proposed_elsewhere(&server.workspace))
                .expect("the requests encode")
        };
        let offer = |number: u32| {
            serde_json::json!([{"jsonrpc": "2.0", "id": format!("window/showMessageRequest/{number}"),
                "method": "window/showMessageRequest",
                "params": {"type": 3_u8, "message": "A model proposed a checked fill for offered.gandr.",
                    "actions": [{"title": "Show"}]}}])
        };
        assert!(propose(&mut server, 1_i32, "42"), "the fill is kept");
        assert_eq!(
            offered(&mut server),
            offer(1),
            "the first kept fill is offered"
        );
        assert!(
            propose(&mut server, 1_i32, "7"),
            "a second fill is kept beside it"
        );
        assert_eq!(
            offered(&mut server),
            serde_json::json!([]),
            "a fill kept beside one offered is not offered again"
        );
        assert_eq!(
            send(
                &mut server,
                Json(
                    r#"{"jsonrpc":"2.0","id":"window/showMessageRequest/1","result":{"title":"Show"}}"#
                ),
            ),
            serde_json::json!([{"jsonrpc": "2.0", "id": "window/showDocument/2",
                "method": "window/showDocument",
                "params": {"uri": "file:///tmp/offered.gandr", "takeFocus": true,
                    "selection": {"start": {"line": 1_u32, "character": 8_u32},
                        "end": {"line": 1_u32, "character": 15_u32}}}}]),
            "choosing to see the fill shows its document with its range selected"
        );
        assert_eq!(
            send(
                &mut server,
                Json(r#"{"jsonrpc":"2.0","id":"window/showDocument/2","result":{"success":true}}"#),
            ),
            serde_json::json!([]),
            "the client's answer is read and left"
        );
        let _changed = send(
            &mut server,
            Json(
                r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":
                    {"uri":"file:///tmp/offered.gandr","version":2},
                    "contentChanges":[{"text":"def f : Integer ;\ndef f = missing ;\n"}]}}"#,
            ),
        );
        assert!(propose(&mut server, 2_i32, "42"), "the fill is kept again");
        assert_eq!(
            offered(&mut server),
            offer(3),
            "a fill kept after the edit withdrew the one offered is offered again"
        );
        assert_eq!(
            send(
                &mut server,
                Json(r#"{"jsonrpc":"2.0","id":"window/showMessageRequest/3","result":null}"#),
            ),
            serde_json::json!([]),
            "a dismissed offer shows nothing"
        );
        let mut plain = initialized();
        let _opened = send(
            &mut plain,
            Json(
                r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":
                    {"uri":"file:///tmp/offered.gandr","languageId":"gandr","version":1,
                     "text":"def f : Integer ;\ndef f = missing ;\n"}}}"#,
            ),
        );
        assert!(propose(&mut plain, 1_i32, "42"), "the fill is kept");
        assert_eq!(
            offered(&mut plain),
            serde_json::json!([]),
            "a client that shows no document is offered nothing"
        );
    }

    /// A folder change that does not read, from a client that lists its
    /// workspace folders, asks for them whole, and the list answered replaces
    /// the folders the connection holds open; null leaves it none, and a
    /// client that lists none is asked nothing.
    #[test]
    fn an_unread_folder_change_lists_the_folders_whole()
    {
        let directory = std::env::temp_dir().join(format!("gandr-listed-{}", std::process::id()));
        std::fs::create_dir_all(&directory).expect("a scratch folder");
        let source = std::fs::canonicalize(&directory)
            .expect("the scratch folder resolves")
            .join("listed.gandr");
        let mut server = Connected::default();
        let _answered = send(
            &mut server,
            Json(
                r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"capabilities":{"workspace":{"workspaceFolders":true}}}}"#,
            ),
        );
        let unread = r#"{"jsonrpc":"2.0","method":"workspace/didChangeWorkspaceFolders","params":{"event":5}}"#;
        assert_eq!(
            send(&mut server, Json(unread)),
            serde_json::json!([{"jsonrpc": "2.0", "id": "workspace/workspaceFolders/1",
                "method": "workspace/workspaceFolders"}]),
            "the folders are asked for whole"
        );
        let listed = serde_json::json!({"jsonrpc": "2.0", "id": "workspace/workspaceFolders/1",
            "result": [{"uri": format!("file://{}", directory.display()), "name": "listed"}]});
        assert_eq!(
            send(&mut server, Json(&listed.to_string())),
            serde_json::json!([]),
            "the list is answered with nothing"
        );
        assert!(
            server.workspace.files.borrow().root_of(&source).is_some(),
            "the folder listed is a root"
        );
        let _again = send(&mut server, Json(unread));
        let _none = send(
            &mut server,
            Json(r#"{"jsonrpc":"2.0","id":"workspace/workspaceFolders/2","result":null}"#),
        );
        assert!(
            server.workspace.files.borrow().root_of(&source).is_none(),
            "a null list leaves the connection no folder"
        );
        assert_eq!(
            send(&mut initialized(), Json(unread)),
            serde_json::json!([]),
            "a client that lists no folders is asked nothing"
        );
        let _removed = std::fs::remove_dir_all(&directory);
    }

    /// #1034: a name declared in two halves answers its definition half to a
    /// definition request and its signature half to a declaration request,
    /// and a rename or a reference search reaches both halves' names.
    #[test]
    fn a_two_half_name_answers_each_half_and_renames_both_1034()
    {
        let mut server = initialized();
        let _published = send(
            &mut server,
            Json(
                r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":
                    {"uri":"file:///tmp/halves.gandr","languageId":"gandr","version":1,
                     "text":"def x : Integer ;\ndef x = 3 ;\ndef y = x ;\n"}}}"#,
            ),
        );
        let uri = DocumentUri::from("file:///tmp/halves.gandr");
        let at = |line: u32, character: u32| Position {
            line: Line::from(line),
            character: Character::from(character),
        };
        let name = |line: u32| {
            serde_json::json!([{"uri": "file:///tmp/halves.gandr",
                "range": {"start": {"line": line, "character": 4_u32},
                    "end": {"line": line, "character": 5_u32}}}])
        };
        assert_eq!(
            going(&mut server, Goto::Definition, &uri, at(2, 8)),
            name(1),
            "a use's definition: the definition half's name"
        );
        assert_eq!(
            going(&mut server, Goto::Declaration, &uri, at(2, 8)),
            name(0),
            "a use's declaration: the signature half's name"
        );
        assert_eq!(
            going(&mut server, Goto::Declaration, &uri, at(1, 4)),
            name(0),
            "the definition's own name declares at the signature"
        );
        let starts = |answer: &Value, pointer: &str| -> Vec<(u64, u64)> {
            let mut starts: Vec<(u64, u64)> = answer
                .pointer(pointer)
                .and_then(Value::as_array)
                .into_iter()
                .flatten()
                .filter_map(|edit| {
                    Some((
                        edit.pointer("/range/start/line")?.as_u64()?,
                        edit.pointer("/range/start/character")?.as_u64()?,
                    ))
                })
                .collect();
            starts.sort_unstable();
            starts
        };
        let renamed = send(
            &mut server,
            Json(
                r#"{"jsonrpc":"2.0","id":1,"method":"textDocument/rename","params":{
                    "textDocument":{"uri":"file:///tmp/halves.gandr"},
                    "position":{"line":2,"character":8},"newName":"z"}}"#,
            ),
        );
        assert_eq!(
            starts(&renamed, "/0/result/changes/file:~1~1~1tmp~1halves.gandr"),
            [(0, 4), (1, 4), (2, 8)],
            "a rename edits both halves' names and the use"
        );
        let found = send(
            &mut server,
            Json(
                r#"{"jsonrpc":"2.0","id":2,"method":"textDocument/references","params":{
                    "textDocument":{"uri":"file:///tmp/halves.gandr"},
                    "position":{"line":2,"character":8},"context":{"includeDeclaration":true}}}"#,
            ),
        );
        assert_eq!(
            starts(&found, "/0/result"),
            [(0, 4), (1, 4), (2, 8)],
            "the references are both halves' names and the use"
        );
    }

    /// #1361: a reference search that leaves the declaration out leaves out
    /// both halves of a name declared in two, and one that keeps it answers
    /// the declaring half first, then the other.
    #[test]
    fn references_leave_both_halves_out_with_the_declaration_1361()
    {
        let mut server = initialized();
        let _published = send(
            &mut server,
            Json(
                r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":
                    {"uri":"file:///tmp/unused.gandr","languageId":"gandr","version":1,
                     "text":"def x : Integer ;\ndef x = 3 ;\ndef y = x ;\ndef z : Integer ;\ndef z = 4 ;\n"}}}"#,
            ),
        );
        let mut references = |line: u32, character: u32, declared: bool| -> Vec<(u64, u64)> {
            let request = serde_json::json!({"jsonrpc": "2.0", "id": 1_i32,
                "method": "textDocument/references", "params": {
                    "textDocument": {"uri": "file:///tmp/unused.gandr"},
                    "position": {"line": line, "character": character},
                    "context": {"includeDeclaration": declared}}});
            send(&mut server, Json(&request.to_string()))
                .pointer("/0/result")
                .and_then(Value::as_array)
                .into_iter()
                .flatten()
                .filter_map(|location| {
                    Some((
                        location.pointer("/range/start/line")?.as_u64()?,
                        location.pointer("/range/start/character")?.as_u64()?,
                    ))
                })
                .collect()
        };
        assert_eq!(
            references(2, 8, false),
            [(2, 8)],
            "a used name without its declaration: the use alone, neither half"
        );
        assert_eq!(
            references(1, 4, false),
            [(2, 8)],
            "asked from the definition half, the same"
        );
        assert_eq!(
            references(3, 4, false),
            [],
            "an unused name declared in two halves has no reference"
        );
        assert_eq!(
            references(0, 4, true),
            [(0, 4), (1, 4), (2, 8)],
            "with its declaration: the signature half, the definition half, then the use"
        );
    }
}
