//! The hub's Reactive Agent Protocol face: the toolset that an agent runtime
//! discovers over HTTP, the invoke endpoint that acknowledges each call, and
//! the callbacks that carry each result and each new state of a subscription.
//!
//! `gandr serve` gives the hub a [`Toolset`] beside its socket, unless it is
//! told `--no-toolset`. The toolset listens on the loopback interface. A `GET`
//! of `/.well-known/rap-toolset` returns the manifest: the name `gandr`, the
//! invoke endpoint, and each operation of the hub's one table, with its name,
//! description and input schema. A `POST` to `/invoke` carries an
//! invocation. The toolset appends a row for the call to its store, answers
//! `200` with no body, and queues the call. An invocation that is not JSON,
//! that has no field RAP requires, or whose callback URL is not `http`, gets
//! `400`, because no result can reach its caller.
//!
//! One worker runs each queued call over the workspace that the editors share,
//! through the table that `tools/call` reads, and owes a `tool_result` to the
//! callback URL. The text of the result is the answer of the tool as JSON. A
//! refusal, an unknown operation and arguments that the tool cannot read give
//! a text that starts with `Error: `.
//!
//! # Frames
//!
//! The result of `diagnostics` is a frame of the render bus. Its text holds
//! the URI of the document, its version, and its diagnostic and goal cards.
//! Its `display_as` is one `text` segment with the lines that `gandr view`
//! prints for the same report, and its `version` is the version of the
//! document.
//!
//! A subscription follows a scope: the frame of one document, or the account
//! card of the declaration of one document that has a given name.
//! `subscribe_diagnostics` and `subscribe_account` open one. The worker
//! confirms each with a `tool_result` that carries `subscription: true`. Its
//! text names the subscription by the `id` of the call, which each event
//! carries as its `tool_call_id`.
//!
//! After each publication that changes the frame, the toolset owes a
//! `subscription_event` to the callback URL of each subscription to the
//! document. The text of the event is the whole frame, as the result of
//! `diagnostics` holds it, and never a change to an earlier frame. After each
//! admission that changes the card of a declaration, the text of the event is
//! the URI of the document, the name, and the card, or null when no
//! declaration has the name. The version is in the event alone, so an edit
//! that leaves the card the same sends nothing. A state that is the same as
//! the last one sends nothing.
//!
//! Each callback carries an `Idempotency-Key` header: the `id` of a result,
//! and `<tool_call_id>@<version>` for an event. Each event also carries its
//! version in its JSON. A runtime that receives one key twice keeps one copy.
//!
//! # The activity
//!
//! The hub's build with the `instrument` feature offers `subscribe_activity`,
//! which follows the work ledger of the hub's pool. While a row follows it,
//! the toolset watches the hub's fold of the activity ring, and each tick of
//! the fold that has events reaches each row. A row keeps the events that its
//! runtime did not take, 4096 at most, and counts each event that it drops.
//! It has one state in flight at most. The text of a state is the run of the
//! toolset, the drops, the pending events and the row of each core. Its key
//! is `<tool_call_id>@<run>.<sequence>`, with the sequence number of its last
//! event, and its version is null. The run is the time at which the toolset
//! started, so a restart repeats no key, and the table writes nothing when a
//! runtime takes a state. Once no row follows the activity, the toolset ends
//! its watch, and the hub folds nothing.
//!
//! # Jobs
//!
//! `check`, `test`, `replay` and `run` are long operations. The worker sends
//! each one to the thread of the jobs, and the result goes when the job ends:
//! the verdict line of the verb, the counts of the replay, or the line of the
//! run. A newer revision of a document that a `check`, a `test` or a `replay`
//! reads retires it, and a cancel or a closure ends it. In the hub's build with
//! the `instrument` feature, each running job hears the activity as a
//! `view_update`. The module `jobs` states the rest. The driver gives the
//! [`Verbs`] that `check` and `test` walk with.
//!
//! # The subscription table
//!
//! The subscription table is one file per workspace, readable by its owner
//! alone, and written whole through a rename after each change: a
//! subscription opened or dropped, and a state that a runtime took at a later
//! version. A table with no row has no file. When the toolset opens, it
//! resumes each row of the table. A resumed row hears no state of the version
//! that its runtime took, or of an earlier version. A later state that is the
//! same as the state of that version sends nothing.
//!
//! A `POST` to `/cancel_tool_call` with a `tool_call_id` drops that
//! subscription. A `POST` to `/close_thread` with a `thread_id` drops each
//! subscription of that `group_id`. Both answer `200` always. A delivery in
//! flight ends, and no event of the row follows it.
//!
//! # Boundaries
//!
//! A caller that wants a bearer sends its own token on the invocation, as
//! `Authorization: Bearer <token>`. The row keeps the token, and each callback
//! for that row sends it back in the same header. The hub mints no token. A
//! caller matches a result to its pending call by `group_id` and `id`, as RAP
//! states.
//!
//! The store is one file of JSON lines per workspace, and only its owner can
//! read it. The toolset writes the row of a call before it sends the `200`,
//! and the answer of the call before its first delivery. Thus a crash of the
//! hub loses no call that it acknowledged. When the toolset opens its store,
//! it delivers again each answer that no settlement follows. The worker
//! answers each row with no answer with an error. The toolset empties the file
//! each time no call is pending.
//!
//! The toolset accepts connections on one thread for each hardware thread of
//! the host, and on two at least. A client that stalls holds its own thread for
//! one second at most, and the other threads answer the other calls.
//!
//! The deliveries go on as many threads again, which belong to the toolset and
//! never to the pool of the engine. They retry as the [`Policy`] states. A
//! delivery that a runtime takes or refuses settles its call. A refusal also
//! drops a subscription. A subscription whose retries are spent stays, and it
//! is unreachable until a later state reaches it.
//!
//! The driver writes the URL of the manifest to the [`Announcement`] beside the
//! hub's socket, readable by its owner alone. A runtime that did not start the
//! hub reads the URL there, and the file goes when the hub stops.
//!
//! # Dependencies
//!
//! `httparse` reads the head of each request and of each callback's answer in
//! place. The rest of HTTP/1.1 that the toolset speaks, one request for each
//! connection, is written here. `gandr_surface_tui` prints the lines of a
//! report as `gandr view` prints them.
//!
//! # References
//!
//! - The Hydro project. "Reactive Agent Protocol specification." 2026. <https://reactiveagentprotocol.dev/docs/rap/spec/overview>
//!   — the manifest, the invocation, the acknowledgement, the callback and its
//!   `Error: ` text, the `subscription_event` and its fields, the `view_update`
//!   and its `view_type`, the `display_as` segments, and the retry of a `5xx`
//!   and never of a `4xx`.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::net::SocketAddr;
use core::ops::Range;
use core::time::Duration;
use std::fs::DirBuilder;
use std::fs::File;
use std::fs::OpenOptions;
use std::io;
use std::io::Read as _;
use std::io::Write;
use std::net::TcpListener;
use std::net::TcpStream;
use std::os::unix::fs::DirBuilderExt as _;
use std::os::unix::fs::OpenOptionsExt as _;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Mutex;
use std::sync::mpsc::Receiver;
use std::sync::mpsc::Sender;
use std::sync::mpsc::channel;
use std::thread;
use std::time::SystemTime;

#[cfg(feature = "instrument")]
use gandr_surface_lsp::Activities;
use gandr_surface_lsp::DocumentUri;
use gandr_surface_lsp::Peer;
#[cfg(feature = "instrument")]
use gandr_surface_lsp::Tick;
use gandr_surface_lsp::Workspace;
use gandr_surface_render_remote::AccountCard;
use gandr_surface_render_remote::DiagCard;
use gandr_surface_render_remote::DocId;
use gandr_surface_render_remote::FrameBody;
use gandr_surface_render_remote::FrameScope;
use gandr_surface_render_remote::GoalCard;
use gandr_surface_render_remote::RenderFrame;
use gandr_surface_render_remote::ReportView;
use gandr_surface_tui::report_lines;
use serde::Deserialize;
use serde::Serialize;
use serde_json::Value;
use serde_json::json;

use self::deliver::Deliveries;
use self::deliver::Fate;
pub use self::deliver::Policy;
use self::deliver::Post;
pub use self::deliver::Retries;
use self::deliver::Row;
use self::jobs::Command;
pub use self::jobs::Verbs;
use self::subscriptions::Generation;
use self::subscriptions::Kept;
use self::subscriptions::Snapshot;
use self::subscriptions::Table;
use crate::face::lock;
use crate::tools;
use crate::tools::Scope;

#[cfg(feature = "instrument")]
mod activity;
mod deliver;
mod jobs;
mod subscriptions;

/// The name of the tool whose result is a frame of the render bus.
const DIAGNOSTICS: &str = "diagnostics";

/// The path of the manifest under the base URL of the toolset, as RAP names
/// it.
const MANIFEST: &str = "/.well-known/rap-toolset";

/// The path of the invoke endpoint that the manifest names.
const INVOKE: &str = "/invoke";

/// The path at which a runtime cancels a subscription, as RAP names it.
const CANCEL: &str = "/cancel_tool_call";

/// The path at which a runtime closes a conversation, as RAP names it.
const CLOSE: &str = "/close_thread";

/// What the manifest says the toolset is.
const DESCRIPTION: &str = "The gandr engine hub: the documents its editors hold open, their \
                           diagnostics, the language server's queries over them, and the features \
                           ledger.";

/// The text of the result of a call that a crash of the hub lost.
const LOST: &str = "Error: the hub stopped before the call settled; invoke it again";

/// The acknowledgement of an invocation.
const ACKNOWLEDGED: &[u8] = b"HTTP/1.1 200 OK\r\ncontent-length: 0\r\nconnection: close\r\n\r\n";

/// The answer to a request for a path the toolset does not serve.
const NOT_FOUND: &[u8] =
    b"HTTP/1.1 404 Not Found\r\ncontent-length: 0\r\nconnection: close\r\n\r\n";

/// The answer to an invocation whose row the store could not write: RAP's
/// runtime tries a `5xx` again.
const UNSTORED: &[u8] =
    b"HTTP/1.1 503 Service Unavailable\r\ncontent-length: 0\r\nconnection: close\r\n\r\n";

/// The answer to a request whose body is larger than [`BODY_LIMIT`].
const TOO_LARGE: &[u8] =
    b"HTTP/1.1 413 Content Too Large\r\ncontent-length: 0\r\nconnection: close\r\n\r\n";

/// The headers a head can carry. A runtime sends fewer than twenty, and a head
/// with more is refused.
const HEADERS: usize = 64;

/// The bytes a head can take: 16 KiB, the limit that common HTTP servers set.
const HEAD_LIMIT: usize = 16 * 1024;

/// The bytes the body of an invocation can take: 16 MiB. A trial of 32
/// candidates over a document of 500 KiB fits.
const BODY_LIMIT: usize = 16 * 1024 * 1024;

/// How long an acceptor waits for the rest of a request: one second. A request
/// on the loopback interface arrives in microseconds. A client that stalls
/// holds its own acceptor no longer than this, and the other acceptors answer
/// the other calls.
const REQUEST_WAIT: Duration = Duration::from_secs(1);

/// How long the check of an address file waits for the listener it names:
/// half a second. A listener on the loopback interface accepts in
/// microseconds.
const ANNOUNCED_WAIT: Duration = Duration::from_millis(500);

/// An invocation, as a RAP runtime posts it to the invoke endpoint. The fields
/// that the hub does not read, such as `user_id`, are ignored.
#[derive(Deserialize)]
struct Invocation
{
    /// The tool to call.
    operation: String,
    /// The arguments of the tool; none when absent.
    #[serde(default)]
    arguments: Value,
    /// The identifier of the call, unique in its group.
    id: String,
    /// The identifier of the model's tool call, when a model made the call.
    #[serde(default)]
    call_id: Option<String>,
    /// Where the result goes.
    callback_url: String,
    /// The conversation that the call belongs to.
    group_id: String,
}

/// A call that the toolset acknowledged and did not answer: one row of its
/// store.
#[derive(Deserialize, Serialize)]
struct Pending
{
    /// The conversation that the call belongs to.
    group_id: String,
    /// The identifier of the call, unique in its group.
    id: String,
    /// The identifier of the model's tool call, when a model made the call.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    call_id: Option<String>,
    /// Where the result goes.
    callback_url: String,
    /// The bearer that the caller sent on the invocation, sent back on the
    /// callback.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    token: Option<String>,
    /// The tool to call.
    operation: String,
    /// When the toolset acknowledged the call, in milliseconds since the Unix
    /// epoch.
    started: u64,
}

/// The line of the store that records an acknowledged call.
#[repr(transparent)]
#[derive(Serialize)]
struct Opened<'row>
{
    /// The row.
    opened: &'row Pending,
}

/// The line of the store that records the answer of a call, written before
/// its first delivery.
#[repr(transparent)]
#[derive(Serialize)]
struct Answered<'row>
{
    /// The answer.
    answered: &'row Answer,
}

/// The line of the store that records a call that a runtime took or refused,
/// by its `group_id` and `id`.
#[repr(transparent)]
#[derive(Serialize)]
struct Settled<'row>
{
    /// The `group_id` and the `id` of the call.
    settled: (&'row String, &'row String),
}

/// A line of the store, as the toolset reads it back.
#[derive(Deserialize)]
#[serde(rename_all = "snake_case")]
enum Entry
{
    /// A call acknowledged.
    Opened(Pending),
    /// A call answered, before its first delivery.
    Answered(Answer),
    /// A call that a runtime took or refused, by its `group_id` and `id`.
    Settled((String, String)),
}

/// The answer of a call, as the store keeps it until a runtime takes it.
#[derive(Deserialize, Serialize)]
struct Answer
{
    /// The conversation that the call belongs to.
    group_id: String,
    /// The identifier of the call.
    id: String,
    /// The answer of the tool, or the reason it gave none.
    text: String,
    /// The lines that display the answer, when the tool has a display.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    display: Option<String>,
    /// The version of the document whose frame the answer is.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    version: Option<i32>,
    /// The scope of the subscription that the answer confirms.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    subscription: Option<Scope>,
}

/// The cards of a frame, as the text of a result or of an event holds them.
#[derive(Serialize)]
struct Cards<'frame>
{
    /// The document and its version.
    #[serde(flatten)]
    document: &'frame DocId,
    /// The diagnostic cards.
    diagnostics: &'frame [DiagCard],
    /// The goal cards, in source order.
    goals: &'frame [GoalCard],
}

/// The card of one declaration, as the text of an event holds it. The event
/// carries the version, so that a card that an edit leaves the same is the
/// same text.
#[derive(Serialize)]
struct Accounted<'card>
{
    /// The URI of the document.
    uri: &'card DocumentUri,
    /// The name of the declaration.
    declaration: &'card str,
    /// The card, or none when no declaration has the name.
    card: Option<&'card AccountCard>,
}

/// Bytes the toolset reads or writes, kept to be used again.
#[repr(transparent)]
#[derive(Default)]
struct Buffer(Vec<u8>);

/// The file of rows, how many of its rows no settlement follows, and the
/// buffer each line is encoded in.
struct Store
{
    /// The file, open to append.
    file: File,
    /// The rows in the file that no settlement follows.
    open: usize,
    /// The line being written, kept so a row allocates nothing once the
    /// buffer has grown to the longest row.
    line: Buffer,
}

impl Store
{
    /// Append `entry` to the file as one line, with one write.
    ///
    /// # Specification
    /// trivial.
    fn append<Line>(
        &mut self,
        entry: &Line,
    ) -> io::Result<()>
    where
        Line: Serialize,
    {
        self.line.0.clear();
        serde_json::to_writer(&mut self.line.0, entry).map_err(io::Error::other)?;
        self.line.0.push(b'\n');
        self.file.write_all(&self.line.0)
    }

    /// Record that the toolset acknowledged `pending`.
    ///
    /// # Specification
    /// trivial.
    fn opened(
        &mut self,
        pending: &Pending,
    ) -> io::Result<()>
    {
        self.append(&Opened { opened: pending })?;
        self.open = self.open.saturating_add(1);
        Ok(())
    }

    /// Record the answer of a call, before its first delivery.
    ///
    /// # Specification
    /// trivial.
    fn answered(
        &mut self,
        answer: &Answer,
    ) -> io::Result<()>
    {
        self.append(&Answered { answered: answer })
    }

    /// Record that a runtime took or refused the result of `row`, and empty
    /// the file when no other row is open. A row that is not a call changes
    /// nothing.
    ///
    /// # Specification
    /// trivial.
    fn settled(
        &mut self,
        row: &Row,
    ) -> io::Result<()>
    {
        let Row::Call(ref group_id, ref id) = *row
        else {
            return Ok(());
        };
        self.open = self.open.saturating_sub(1);
        if self.open == 0 {
            return self.file.set_len(0);
        }
        self.append(&Settled {
            settled: (group_id, id),
        })
    }
}

/// A subscription of a runtime to one scope.
struct Subscription
{
    /// The row as the table keeps it.
    kept: Kept,
    /// Where its events go, shared by each delivery.
    callback_url: Arc<str>,
    /// The bearer that the runtime sent, sent back on each event.
    token: Option<Arc<str>>,
    /// The routing of each event up to its version, encoded once.
    routing: String,
    /// The text of the last state owed to it.
    last: Option<Arc<str>>,
    /// Whether the retries of its last delivery were spent.
    unreachable: bool,
    /// The events of the activity that its runtime did not take, when it
    /// follows the activity.
    #[cfg(feature = "instrument")]
    ledger: activity::Ledger,
}

impl Subscription
{
    /// Owe `state` to this subscription, the row `row`, when the state is not
    /// the last one owed and its version is past the one the runtime took.
    ///
    /// # Specification
    /// trivial.
    fn owe(
        &mut self,
        row: &Row,
        state: &State,
        deliveries: &Deliveries,
    )
    {
        let version = state.version;
        match self.kept.last_version {
            // One state settles for each version, so this state is the one the
            // runtime took. A later state that is the same sends nothing.
            Some(taken) if version == taken => {
                self.last = Some(Arc::clone(&state.text));
                return;
            },
            Some(taken) if version < taken => return,
            Some(_) | None => {},
        }
        if self.last.as_ref() == Some(&state.text) {
            return;
        }
        self.last = Some(Arc::clone(&state.text));
        deliveries.owe(row.clone(), Post {
            callback_url: Arc::clone(&self.callback_url),
            token: self.token.clone(),
            key: alloc::format!("{}@{version}", self.kept.tool_call_id),
            version: Some(version),
            head: alloc::format!("{}{version},\"text\":", self.routing),
            text: Arc::clone(&state.text),
        });
    }

    /// Owe the next state of the activity to this subscription, the row
    /// `row`, when it has no state in flight and an event is pending. The
    /// state carries the row of each core that `occupancy` holds.
    ///
    /// # Specification
    /// trivial.
    #[cfg(feature = "instrument")]
    fn owe_ledger(
        &mut self,
        row: &Row,
        (run, occupancy): (activity::Run, &activity::Occupancy),
        deliveries: &Deliveries,
    )
    {
        let Some((last, text)) = self.ledger.owed(run, occupancy)
        else {
            return;
        };
        deliveries.owe(row.clone(), Post {
            callback_url: Arc::clone(&self.callback_url),
            token: self.token.clone(),
            key: alloc::format!("{}@{}.{}", self.kept.tool_call_id, run.0, u64::from(last)),
            version: None,
            head: alloc::format!("{}null,\"text\":", self.routing),
            text: Arc::from(quoted(&text)),
        });
    }
}

/// One state of a scope, as each subscription to it receives it.
struct State
{
    /// The version of the document.
    version: i32,
    /// The state as a JSON string, quoted once for all subscriptions.
    text: Arc<str>,
}

/// The toolset's watch of the hub's activity: the fold, the toolset's peer,
/// where each tick goes, and whether the watch is on.
#[cfg(feature = "instrument")]
struct Watch
{
    /// The hub's fold of the activity ring.
    activities: Activities,
    /// The toolset's connection to the hub.
    peer: Peer,
    /// Where each tick of the fold that has events goes.
    sender: Sender<Arc<Tick>>,
    /// Whether the toolset watches now.
    watching: bool,
}

/// The view of a running job: where its view updates go, and their head.
#[cfg(feature = "instrument")]
struct View
{
    /// Where its view updates go, shared by each delivery.
    callback_url: Arc<str>,
    /// The bearer that the runtime sent on the call, sent back on each update.
    token: Option<Arc<str>>,
    /// The `id` of the call.
    id: String,
    /// The type and the routing of each update, up to its content, encoded
    /// once.
    head: String,
}

/// The activity card of one tick, quoted once for every view: the run, the
/// sequence number of its last event, and its text.
#[cfg(feature = "instrument")]
struct Card
{
    /// The run of the toolset.
    run: activity::Run,
    /// The sequence number of the last event of the tick.
    last: gandr_core_fork::activity::Sequence,
    /// The card as a JSON string, quoted once for every view.
    text: Arc<str>,
}

#[cfg(feature = "instrument")]
impl View
{
    /// Owe `row` the card `card`.
    ///
    /// # Specification
    /// trivial.
    fn owe(
        &self,
        row: &Row,
        card: &Card,
        deliveries: &Deliveries,
    )
    {
        deliveries.owe(row.clone(), Post {
            callback_url: Arc::clone(&self.callback_url),
            token: self.token.clone(),
            key: alloc::format!("{}@{}.{}", self.id, card.run.0, u64::from(card.last)),
            version: None,
            head: self.head.clone(),
            text: Arc::clone(&card.text),
        });
    }
}

/// The subscriptions by row, the rows that follow each document by their
/// kind of scope, and the generation of their last change.
struct Subscriptions
{
    /// Each subscription.
    rows: BTreeMap<Row, Subscription>,
    /// The rows that follow the frame of each document.
    diagnostics: BTreeMap<DocumentUri, BTreeSet<Row>>,
    /// The rows that follow a declaration of each document.
    accounts: BTreeMap<DocumentUri, BTreeSet<Row>>,
    /// The rows that follow the activity.
    activity: BTreeSet<Row>,
    /// The running jobs that hear the activity as view updates, by the row of
    /// their view.
    #[cfg(feature = "instrument")]
    views: BTreeMap<Row, View>,
    /// The generation of the last change that the table must keep.
    generation: Generation,
    /// The watch of the hub's activity, once the toolset serves.
    #[cfg(feature = "instrument")]
    watch: Option<Watch>,
    /// When the toolset started to serve.
    #[cfg(feature = "instrument")]
    run: activity::Run,
    /// The row of each core at the last tick, encoded once for every row.
    #[cfg(feature = "instrument")]
    occupancy: activity::Occupancy,
}

impl Subscriptions
{
    /// The subscriptions that `kept` holds.
    ///
    /// # Specification
    /// trivial.
    fn resumed(kept: Vec<Kept>) -> Self
    {
        let mut subscriptions = Self {
            rows: BTreeMap::new(),
            diagnostics: BTreeMap::new(),
            accounts: BTreeMap::new(),
            activity: BTreeSet::new(),
            #[cfg(feature = "instrument")]
            views: BTreeMap::new(),
            generation: Generation::default(),
            #[cfg(feature = "instrument")]
            watch: None,
            #[cfg(feature = "instrument")]
            run: activity::Run(0),
            #[cfg(feature = "instrument")]
            occupancy: activity::Occupancy::default(),
        };
        for row in kept {
            let _row = subscriptions.insert(row);
        }
        subscriptions
    }

    /// Follow the scope of `kept`, replacing a subscription that has the same
    /// row, and give its row.
    ///
    /// # Specification
    /// trivial.
    fn insert(
        &mut self,
        kept: Kept,
    ) -> Row
    {
        let routing = alloc::format!(
            "{{\"type\":\"subscription_event\",\"group_id\":{},\"tool_call_id\":{},\"associative\":true,\"final\":false,\"version\":",
            quoted(&kept.group_id),
            quoted(&kept.tool_call_id)
        );
        let row = Row::Subscription(kept.group_id.clone(), kept.tool_call_id.clone());
        drop(self.remove(&row));
        match kept.scope {
            Scope::Diagnostics(ref document) => {
                let _fresh = self
                    .diagnostics
                    .entry(document.clone())
                    .or_default()
                    .insert(row.clone());
            },
            Scope::Account { ref document, .. } => {
                let _fresh = self
                    .accounts
                    .entry(document.clone())
                    .or_default()
                    .insert(row.clone());
            },
            Scope::Activity => {
                let _fresh = self.activity.insert(row.clone());
            },
        }
        drop(self.rows.insert(row.clone(), Subscription {
            callback_url: Arc::from(kept.callback_url.as_str()),
            token: kept.token.as_deref().map(Arc::from),
            routing,
            last: None,
            unreachable: false,
            #[cfg(feature = "instrument")]
            ledger: activity::Ledger::default(),
            kept,
        }));
        row
    }

    /// Drop the subscription `row`, and give it when there was one.
    ///
    /// # Specification
    /// trivial.
    fn remove(
        &mut self,
        row: &Row,
    ) -> Option<Subscription>
    {
        let subscription = self.rows.remove(row)?;
        let (index, document) = match subscription.kept.scope {
            Scope::Diagnostics(ref document) => (&mut self.diagnostics, document),
            Scope::Account { ref document, .. } => (&mut self.accounts, document),
            Scope::Activity => {
                let _removed = self.activity.remove(row);
                return Some(subscription);
            },
        };
        if let Some(rows) = index.get_mut(document) {
            let _removed = rows.remove(row);
            if rows.is_empty() {
                drop(index.remove(document));
            }
        }
        Some(subscription)
    }

    /// Mark a change that the table must keep, and give the rows as they
    /// stand, encoded for the table. The caller writes the snapshot after it
    /// lets go of the lock.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// The error encoding a row.
    fn snapshot(&mut self) -> io::Result<Snapshot>
    {
        self.generation = self.generation.next();
        let rows: Vec<&Kept> = self
            .rows
            .values()
            .map(|subscription| &subscription.kept)
            .collect();
        Snapshot::of(self.generation, &rows)
    }

    /// Owe `state`, a state of the frame of `document`, to each subscription
    /// that follows the frame.
    ///
    /// # Specification
    /// trivial.
    fn publish_diagnostics(
        &mut self,
        document: &DocumentUri,
        state: &State,
        deliveries: &Deliveries,
    )
    {
        let Some(rows) = self.diagnostics.get(document)
        else {
            return;
        };
        for row in rows {
            if let Some(subscription) = self.rows.get_mut(row) {
                subscription.owe(row, state, deliveries);
            }
        }
    }

    /// The names of the declarations of `document` that a subscription
    /// follows.
    ///
    /// # Specification
    /// trivial.
    fn declarations(
        &self,
        document: &DocumentUri,
    ) -> BTreeSet<String>
    {
        self.accounts
            .get(document)
            .into_iter()
            .flatten()
            .filter_map(|row| match self.rows.get(row)?.kept.scope {
                Scope::Account {
                    ref declaration, ..
                } => Some(declaration.clone()),
                Scope::Diagnostics(_) | Scope::Activity => None,
            })
            .collect()
    }

    /// Owe each subscription that follows a declaration of `document` the
    /// state of that declaration in `states`.
    ///
    /// # Specification
    /// trivial.
    fn publish_accounts(
        &mut self,
        document: &DocumentUri,
        states: &BTreeMap<String, State>,
        deliveries: &Deliveries,
    )
    {
        let Some(rows) = self.accounts.get(document)
        else {
            return;
        };
        for row in rows {
            let Some(subscription) = self.rows.get_mut(row)
            else {
                continue;
            };
            let state = match subscription.kept.scope {
                Scope::Account {
                    ref declaration, ..
                } => states.get(declaration),
                Scope::Diagnostics(_) | Scope::Activity => None,
            };
            if let Some(state) = state {
                subscription.owe(row, state, deliveries);
            }
        }
    }

    /// Watch the hub's activity while a row follows it or a job views it, and
    /// end the watch once none does.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// The host's refusal of the fold's thread.
    #[cfg(feature = "instrument")]
    fn follow(&mut self) -> io::Result<()>
    {
        let following = !self.activity.is_empty() || !self.views.is_empty();
        let Some(ref mut watch) = self.watch
        else {
            return Ok(());
        };
        if following == watch.watching {
            return Ok(());
        }
        if following {
            watch.activities.watch(
                watch.peer,
                watch.sender.clone(),
                gandr_surface_lsp::Cadence::Events,
            )?;
        }
        else {
            watch.activities.unwatch(watch.peer);
        }
        watch.watching = following;
        Ok(())
    }

    /// Start the view of the job of `pending`: each tick of the hub's
    /// activity that has events reaches it as a view update until it ends.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// The host's refusal of the fold's thread.
    #[cfg(feature = "instrument")]
    fn view(
        &mut self,
        pending: &Pending,
    ) -> io::Result<()>
    {
        let head = alloc::format!(
            "{{\"type\":\"view_update\",\"group_id\":{},\"tool_call_id\":{},\"view_type\":\"activity\",\"content\":",
            quoted(&pending.group_id),
            quoted(&pending.id)
        );
        drop(self.views.insert(
            Row::View(pending.group_id.clone(), pending.id.clone()),
            View {
                callback_url: Arc::from(pending.callback_url.as_str()),
                token: pending.token.as_deref().map(Arc::from),
                id: pending.id.clone(),
                head,
            },
        ));
        self.follow()
    }

    /// End the view of the job of the call `row`, with each view update that
    /// its delivery still owes.
    ///
    /// # Specification
    /// trivial.
    #[cfg(feature = "instrument")]
    fn unview(
        &mut self,
        row: &Row,
        deliveries: &Deliveries,
    )
    {
        let Row::Call(ref group_id, ref id) = *row
        else {
            return;
        };
        let view = Row::View(group_id.clone(), id.clone());
        if self.views.remove(&view).is_some() {
            deliveries.forget(&view);
            // Unwatching never fails; only a watch asks the host for a thread.
            drop(self.follow());
        }
    }

    /// Add the events of `tick` to each row that follows the activity, and
    /// owe each row with no state in flight its next state. Owe each running
    /// job the card of the tick as its view. `occupancy` is the row of each
    /// core of the tick, encoded.
    ///
    /// # Specification
    /// trivial.
    #[cfg(feature = "instrument")]
    fn publish_activity(
        &mut self,
        tick: &Tick,
        occupancy: activity::Occupancy,
        deliveries: &Deliveries,
    )
    {
        self.occupancy = occupancy;
        let Self {
            ref activity,
            ref mut rows,
            ref views,
            ref occupancy,
            run,
            ..
        } = *self;
        for row in activity {
            if let Some(subscription) = rows.get_mut(row) {
                subscription.ledger.heard(&tick.events);
                subscription.owe_ledger(row, (run, occupancy), deliveries);
            }
        }
        if views.is_empty() {
            return;
        }
        // One card for every view: the runtime keeps the latest of each.
        if let Some((last, text)) = activity::card(run, &tick.events, occupancy) {
            let card = Card {
                run,
                last,
                text: Arc::from(quoted(&text)),
            };
            for (row, view) in views {
                view.owe(row, &card, deliveries);
            }
        }
    }

    /// The runtime took the state that `row` had in flight: let go of what it
    /// carried, and owe the next state when an event is pending.
    ///
    /// # Specification
    /// trivial.
    #[cfg(feature = "instrument")]
    fn ledger_taken(
        &mut self,
        row: &Row,
        deliveries: &Deliveries,
    )
    {
        let Self {
            ref mut rows,
            ref occupancy,
            run,
            ..
        } = *self;
        if let Some(subscription) = rows.get_mut(row) {
            subscription.ledger.taken();
            subscription.owe_ledger(row, (run, occupancy), deliveries);
        }
    }
}

/// A call queued for the worker: its row, and its arguments, absent for a call
/// that a crash lost.
struct Call
{
    /// The row.
    pending: Pending,
    /// The arguments, absent for a call that a crash lost.
    arguments: Option<Value>,
}

/// What the worker's queue holds, in the order that the requests reached the
/// toolset. A cancel or a closure travels the same queue as the calls, so the
/// worker starts the job of each call that a runtime saw acknowledged before
/// it ends the jobs that the cancel names: an end that overtook the start of
/// its job would find no job, and the job would run to its end.
enum Queued
{
    /// A call to answer.
    Call(Call),
    /// The jobs that a cancel or a closure ends.
    End(Ending),
}

/// What a request asks for.
#[derive(Clone, Copy, Eq, PartialEq)]
enum Route
{
    /// The manifest.
    Manifest,
    /// A call.
    Invoke,
    /// The end of one subscription, by the `tool_call_id` of its call.
    Cancel,
    /// The end of each subscription of one conversation, by its `thread_id`.
    Close,
    /// A path the toolset does not serve.
    Unknown,
    /// A body past [`BODY_LIMIT`].
    TooLarge,
}

/// A request read whole.
struct Request
{
    /// What it asks for.
    route: Route,
    /// The bearer its `Authorization` header carries.
    bearer: Option<String>,
    /// Where its body lies in the buffer it was read into.
    body: Range<usize>,
}

/// The hub's Reactive Agent Protocol face: a listener, the store of the calls
/// it acknowledged, the calls that a crash cut short, and the subscriptions
/// with their table.
pub struct Toolset
{
    /// The listener, bound on the loopback interface.
    listener: TcpListener,
    /// The store of rows.
    store: Store,
    /// The calls that a crash cut short, each with its answer when the store
    /// kept one, answered first.
    lost: Vec<(Pending, Option<Answer>)>,
    /// The subscriptions.
    subscriptions: Subscriptions,
    /// The table that keeps the subscriptions.
    table: Table,
    /// When to retry a delivery, and how often.
    policy: Policy,
    /// The verbs that `check` and `test` walk with, when the driver gave them.
    verbs: Option<Arc<dyn Verbs>>,
}

impl Toolset
{
    /// A toolset that answers on `listener`, keeps its rows in the file
    /// `calls` and its subscriptions in the file `subscriptions`, and retries
    /// its deliveries as `policy` states.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the directories of `calls` and `subscriptions` exist, made
    ///   readable by their owner alone when this call made them, and `calls` is
    ///   open to append, made readable by its owner alone when this call made
    ///   it. Each row of `calls` that no settlement follows is kept with its
    ///   answer, when the store holds one, to be delivered again once the
    ///   toolset serves. A row with no answer is answered with an error. Each
    ///   row of `subscriptions` is resumed: once the toolset serves, it hears
    ///   the states of its scope whose version is past its `last_version`.
    /// - provides: `gandr serve`'s face, opened before the hub runs, so a store
    ///   or a table that cannot open stops the command.
    /// - fails: when a directory cannot be made, or a file opened or read, or
    ///   `subscriptions` holds no table.
    /// - panics: none.
    /// - executable: none — the effects are directories and files.
    ///
    /// # Errors
    /// The error making a directory, or opening or reading a file, or
    /// [`io::ErrorKind::InvalidData`] for a file that holds no table.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a store that holds an open row, an answered row and a
    ///   settled one opens. The open row is answered with an error, the
    ///   answered row with its answer, and the store is then empty. A table
    ///   that an earlier toolset wrote resumes its subscription, which hears a
    ///   later state and no state of the version it took.
    /// - witness: `rap::tests::a_call_a_crash_lost_is_answered_with_an_error`
    /// - witness: `rap::tests::an_account_subscription_outlives_a_restart_of_the_hub`
    #[inline]
    pub fn open(
        listener: TcpListener,
        calls: &Path,
        subscriptions: &Path,
        policy: Policy,
    ) -> io::Result<Self>
    {
        if let Some(directory) = calls.parent() {
            DirBuilder::new()
                .recursive(true)
                .mode(0o700)
                .create(directory)?;
        }
        let (table, kept) = Table::open(subscriptions)?;
        let written = match std::fs::read(calls) {
            Ok(written) => written,
            Err(error) if error.kind() == io::ErrorKind::NotFound => Vec::new(),
            Err(error) => return Err(error),
        };
        let file = OpenOptions::new()
            .append(true)
            .create(true)
            .mode(0o600)
            .open(calls)?;
        let mut open: BTreeMap<(String, String), (Pending, Option<Answer>)> = BTreeMap::new();
        for line in written.split(|&byte| byte == b'\n') {
            // A line that does not parse is one that a crash cut short.
            match serde_json::from_slice::<Entry>(line) {
                Ok(Entry::Opened(pending)) => {
                    drop(open.insert(
                        (pending.group_id.clone(), pending.id.clone()),
                        (pending, None),
                    ));
                },
                Ok(Entry::Answered(answer)) => {
                    if let Some(row) = open.get_mut(&(answer.group_id.clone(), answer.id.clone())) {
                        row.1 = Some(answer);
                    }
                },
                Ok(Entry::Settled(key)) => drop(open.remove(&key)),
                Err(_) => {},
            }
        }
        let lost: Vec<(Pending, Option<Answer>)> = open.into_values().collect();
        if lost.is_empty() {
            file.set_len(0)?;
        }
        Ok(Self {
            listener,
            store: Store {
                file,
                open: lost.len(),
                line: Buffer::default(),
            },
            lost,
            subscriptions: Subscriptions::resumed(kept),
            table,
            policy,
            verbs: None,
        })
    }

    /// This toolset, whose `check` and `test` walk their paths with `verbs`.
    /// A toolset with no verbs answers them with an error.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn walking(
        self,
        verbs: Arc<dyn Verbs>,
    ) -> Self
    {
        Self {
            verbs: Some(verbs),
            ..self
        }
    }

    /// The address the toolset listens on.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// The error reading the address of the listener.
    #[inline]
    pub fn address(&self) -> io::Result<SocketAddr>
    {
        self.listener.local_addr()
    }

    /// Serve the toolset over `workspace` as `peer`, telling `log` of each
    /// delivery that does not end taken, until accepting fails on every
    /// acceptor.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a `GET` of `/.well-known/rap-toolset` is answered with the
    ///   manifest, which names the invoke endpoint at the listener's address
    ///   and every operation of the hub's one table, by its name, description
    ///   and input schema. A `POST` to `/invoke` whose body is an invocation
    ///   with a callback URL in `http` is answered `200` with no body once its
    ///   row is in the store, `503` when the row cannot be written. Another
    ///   body is answered `400`, a body past the limit `413`, and another path
    ///   `404`. Each acknowledged call, and each call that a crash cut short,
    ///   is answered once by a `tool_result` owed to its callback URL with the
    ///   caller's bearer when it sent one. Its row is settled once a runtime
    ///   takes or refuses it. The text is the answer of the tool as JSON, or a
    ///   text that starts with `Error: `. The result of `diagnostics` carries
    ///   the cards of the document's frame, its version, and the lines that
    ///   `gandr view` prints as its `display_as`. A subscription operation adds
    ///   a row to the table before its result, which carries `subscription:
    ///   true`. Each publication that changes the frame of a document owes one
    ///   `subscription_event` to each subscription to the frame, and each
    ///   admission that changes the card of a declaration owes one to each
    ///   subscription to the declaration, unless the runtime took a state of
    ///   that version or a later one. While a row follows the activity, each
    ///   tick of the hub's fold that has events reaches it, and a row with no
    ///   state in flight is owed its next state. A long operation, `check`,
    ///   `test`, `replay` or `run`, is answered once its job ends, with the
    ///   verdict line of the verb, the counts of the replay, or the line of the
    ///   run. In the build with the `instrument` feature, each tick that has
    ///   events reaches each running job as a `view_update` of the type
    ///   `activity`. A newer revision of a document that a `check`, a `test` or
    ///   a `replay` reads retires it, and its text names the document and its
    ///   version. A `POST` to `/cancel_tool_call` or `/close_thread` is
    ///   answered `200` once the rows it names are dropped from the table and
    ///   their deliveries forgotten, and each job it names is answered
    ///   `cancelled`. Each delivery is retried as the policy states.
    /// - provides: `gandr serve`, the face beside the hub's socket.
    /// - fails: when accepting a connection fails on every acceptor for a
    ///   reason other than an interruption or an aborted connection.
    /// - panics: none.
    /// - executable: none — the effects are bytes on sockets and lines in a
    ///   file, and the workspace other connections change concurrently.
    ///
    /// # Errors
    /// The first error accepting a connection, or reading the listener's
    /// address.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — through a running hub, the manifest lists every tool;
    ///   `type_of` on a document an editor holds reaches a test listener with
    ///   the hover's type and the caller's bearer; an unknown operation reaches
    ///   it with an error and no bearer; a body that is not JSON is answered
    ///   `400`; a client that stalls holds no other call. `diagnostics` reaches
    ///   the listener with the cards and the printed lines. A subscription
    ///   hears one event for each edit that changes the frame, and one for each
    ///   admission that changes the card it follows. A cancel and a closed
    ///   thread end their rows. A listener that answers `503` once hears the
    ///   event again after the first wait, and one that answers `404` hears
    ///   nothing more. `check` on a corpus reaches the listener with its
    ///   verdict line and its activity, `replay` and `run` answer, and an edit
    ///   and a cancel end their jobs.
    /// - witness: `rap::tests::the_toolset_answers_a_call_by_its_callback`
    /// - witness: `rap::tests::a_call_a_crash_lost_is_answered_with_an_error`
    /// - witness: `rap::tests::a_stalled_client_holds_no_other_call`
    /// - witness: `rap::tests::a_subscription_hears_each_new_frame`
    /// - witness: `rap::tests::an_account_subscription_outlives_a_restart_of_the_hub`
    /// - witness: `rap::tests::a_cancel_and_a_closed_thread_drop_their_rows`
    /// - witness: `rap::tests::a_server_error_is_retried_and_a_refusal_is_not`
    /// - witness: `rap::tests::an_activity_subscription_hears_each_task_until_it_ends_6509`
    /// - witness: `rap::tests::a_long_operation_answers_when_its_job_ends`
    /// - witness: `rap::tests::a_newer_revision_retires_a_check_or_a_run_and_a_cancel_ends_a_job`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            pool_only_threads,
            reason = "io: the worker, the jobs and the fan-out block on the workspace lock or a channel, each delivery on its callback's socket, and each acceptor on its client's socket, for the toolset's life"
        )
    )]
    #[inline]
    pub fn serve<Log>(
        self,
        workspace: &Arc<Mutex<Workspace>>,
        peer: Peer,
        log: Log,
    ) -> io::Result<()>
    where
        Log: Write + Send,
    {
        let Self {
            listener,
            store,
            lost,
            subscriptions,
            table,
            policy,
            verbs,
        } = self;
        #[cfg(feature = "instrument")]
        let (mut subscriptions, mut log) = (subscriptions, log);
        let manifest = manifest(listener.local_addr()?);
        let deliveries = Deliveries::new(policy);
        let (queue, queued) = channel();
        for (pending, answer) in lost {
            match answer {
                Some(answer) => deliveries.owe(
                    Row::Call(pending.group_id.clone(), pending.id.clone()),
                    result(&pending, &answer),
                ),
                None => drop(queue.send(Queued::Call(Call {
                    pending,
                    arguments: None,
                }))),
            }
        }
        let (changed, changes) = channel();
        let (settled, settlements) = channel();
        let (jobs, commands) = channel();
        {
            let mut watched = lock(workspace);
            watched.watch(peer, changed);
            watched.watch_accounts(peer, settled);
        }
        // The toolset watches the hub's activity while a row follows it.
        #[cfg(feature = "instrument")]
        let ticks = {
            let (ticked, ticks) = channel();
            subscriptions.run = activity::Run(
                SystemTime::now()
                    .duration_since(SystemTime::UNIX_EPOCH)
                    .map_or(0, |since| {
                        u64::try_from(since.as_millis()).unwrap_or(u64::MAX)
                    }),
            );
            subscriptions.watch = Some(Watch {
                activities: lock(workspace).activity().clone(),
                peer,
                sender: ticked,
                watching: false,
            });
            if let Err(error) = subscriptions.follow() {
                drop(writeln!(
                    log,
                    "the toolset did not watch the activity for its resumed rows: {error}"
                ));
            }
            ticks
        };
        // An acknowledgement takes the store's lock for one line alone, so
        // acceptors at the host's width answer in parallel. Two at least keep a
        // client that stalls from holding every other call. The deliveries
        // take as many threads again, so a callback that stalls holds its own
        // row alone.
        let width = thread::available_parallelism().map_or(2, |width| width.get().max(2));
        let (store, subscriptions, log) = (
            Mutex::new(store),
            Mutex::new(subscriptions),
            Mutex::new(log),
        );
        let (listener, manifest, store, subscriptions, log, deliveries) = (
            &listener,
            &manifest,
            &store,
            &subscriptions,
            &log,
            &deliveries,
        );
        let table = &table;
        let held = Held {
            workspace,
            verbs: verbs.as_ref(),
            store,
            #[cfg(feature = "instrument")]
            subscriptions,
            deliveries,
            log,
        };
        thread::scope(|scope| {
            let worker = {
                let jobs = jobs.clone();
                scope.spawn(move || {
                    work(
                        queued,
                        (workspace, &jobs),
                        store,
                        subscriptions,
                        table,
                        deliveries,
                        log,
                    );
                })
            };
            let finished = jobs.clone();
            let held = &held;
            drop(scope.spawn(move || jobs::run(commands, finished, held)));
            let changing = jobs.clone();
            drop(scope.spawn(move || {
                fan_out(changes, (workspace, &changing), subscriptions, deliveries);
            }));
            let settling = jobs.clone();
            drop(scope.spawn(move || {
                fan_out_accounts(
                    settlements,
                    (workspace, &settling),
                    subscriptions,
                    deliveries,
                );
            }));
            #[cfg(feature = "instrument")]
            drop(scope.spawn(move || fan_out_activity(ticks, subscriptions, deliveries)));
            for _delivery in 0 .. width {
                drop(scope.spawn(move || {
                    deliveries.run(|row, fate| {
                        told(row, &fate, store, subscriptions, table, deliveries, log);
                    });
                }));
            }
            // Every acceptor starts before the first join.
            let mut acceptors = Vec::with_capacity(width);
            for _acceptor in 0 .. width {
                let desk = Desk {
                    manifest,
                    store,
                    queue: queue.clone(),
                    subscriptions,
                    table,
                    deliveries,
                    log,
                };
                acceptors.push(scope.spawn(move || accept(listener, &desk)));
            }
            // The worker ends once every acceptor has ended and it has answered
            // every queued call.
            drop(queue);
            let accepted = acceptors
                .into_iter()
                .map(|acceptor| {
                    acceptor
                        .join()
                        .unwrap_or_else(|_panic| Err(io::Error::other("an acceptor panicked")))
                })
                .fold(Ok(()), Result::and);
            // The jobs end once the worker started its last one. A job that did
            // not end keeps its row, which the next toolset answers.
            drop(worker.join());
            drop(jobs.send(Command::Stop));
            // The fan-out ends with its watch, and each delivery thread once
            // its attempt in flight ends. The store keeps each answer that no
            // runtime took.
            lock(workspace).depart(peer);
            #[cfg(feature = "instrument")]
            drop(lock(subscriptions).watch.take());
            deliveries.close();
            accepted
        })
    }
}

/// The file beside the hub's socket that names the URL of the toolset's
/// manifest. A runtime that did not start the hub reads the URL there.
#[repr(transparent)]
pub struct Announcement(PathBuf);

impl Announcement
{
    /// The file beside `socket`: the name of the socket with the extension
    /// `rap`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn beside(socket: &Path) -> Self
    {
        Self(socket.with_extension("rap"))
    }

    /// Refuse when the file names a toolset that still listens.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Ok` when no file is there, or when the URL in the file names
    ///   no address that accepts a connection within [`ANNOUNCED_WAIT`].
    /// - provides: the check that `gandr serve` makes before it opens a
    ///   toolset, so that a second hub of one workspace stops and names the
    ///   file.
    /// - fails: when the file names a listener that accepts, or the file cannot
    ///   be read.
    /// - panics: none.
    /// - executable: none — the result depends on a file and a listener.
    ///
    /// # Errors
    /// [`io::ErrorKind::AddrInUse`] that names the file and its URL, or the
    /// error of the read.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a second `gandr serve` in one workspace refuses and
    ///   names the file that the first one wrote.
    /// - witness: `rap::tests::an_announcement_names_the_manifest_and_refuses_a_second_hub`
    #[inline]
    pub fn vacant(&self) -> io::Result<()>
    {
        let url = match std::fs::read_to_string(&self.0) {
            Ok(url) => url,
            Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(()),
            Err(error) => return Err(error),
        };
        let url = url.trim_end();
        let listens = url
            .strip_prefix("http://")
            .and_then(|rest| rest.split_once('/'))
            .and_then(|(address, _path)| address.parse::<SocketAddr>().ok())
            .is_some_and(|address| TcpStream::connect_timeout(&address, ANNOUNCED_WAIT).is_ok());
        if listens {
            return Err(io::Error::new(
                io::ErrorKind::AddrInUse,
                alloc::format!(
                    "{} names a toolset that still listens at {url}",
                    self.0.display()
                ),
            ));
        }
        Ok(())
    }

    /// Write the URL of the manifest of the toolset at `address` to the file,
    /// readable by its owner alone.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the file holds one line, `http://<address>` followed by the
    ///   path of the manifest. The file replaces an earlier one whole, so a
    ///   reader never reads half a URL, and a crash leaves the earlier file or
    ///   the new one.
    /// - provides: the address of the toolset for a runtime, until the hub lets
    ///   the returned file go.
    /// - fails: when the file cannot be written or put in place.
    /// - panics: none.
    /// - executable: none — the effect is a file.
    ///
    /// # Errors
    /// The error of the write, the flush or the rename.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a client reads the URL from the file and fetches the
    ///   manifest there, and the file goes when the hub stops.
    /// - witness: `rap::tests::an_announcement_names_the_manifest_and_refuses_a_second_hub`
    #[inline]
    pub fn write(
        self,
        address: SocketAddr,
    ) -> io::Result<Announced>
    {
        let mut staged = self.0.clone().into_os_string();
        staged.push(".new");
        let staged = PathBuf::from(staged);
        match std::fs::remove_file(&staged) {
            Ok(()) => {},
            Err(error) if error.kind() == io::ErrorKind::NotFound => {},
            Err(error) => return Err(error),
        }
        let mut file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(&staged)?;
        file.write_all(alloc::format!("http://{address}{MANIFEST}\n").as_bytes())?;
        file.sync_all()?;
        drop(file);
        std::fs::rename(&staged, &self.0)?;
        Ok(Announced(self.0))
    }
}

/// The address file that an [`Announcement`] wrote. The file goes when the
/// hub lets this value go.
#[repr(transparent)]
pub struct Announced(PathBuf);

impl Drop for Announced
{
    /// Remove the file.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn drop(&mut self)
    {
        drop(std::fs::remove_file(&self.0));
    }
}

/// The answer to a `GET` of the manifest, encoded once: the manifest of the
/// toolset at `address`, which lists each operation of the hub's one table.
///
/// # Specification
/// trivial.
fn manifest(address: SocketAddr) -> Buffer
{
    let body = json!({
        "name": "gandr",
        "description": DESCRIPTION,
        "endpoint": alloc::format!("http://{address}{INVOKE}"),
        "tools": tools::offered(),
    })
    .to_string();
    let mut answer = alloc::format!(
        "HTTP/1.1 200 OK\r\ncontent-type: application/json\r\ncontent-length: {}\r\nconnection: close\r\n\r\n",
        body.len()
    )
    .into_bytes();
    answer.extend_from_slice(body.as_bytes());
    Buffer(answer)
}

/// The jobs that a cancel or a closure names: by the `group_id`, and by the
/// `id` when it names one.
struct Ending
{
    /// The conversation, when the request names one.
    group_id: Option<String>,
    /// The call, when the request names one.
    id: Option<String>,
}

/// What the thread of the jobs reads and writes besides its jobs: the
/// workspace, the verbs, the store, the subscriptions, the deliveries and the
/// log.
struct Held<'toolset, Log>
{
    /// The workspace that the editors share.
    workspace: &'toolset Arc<Mutex<Workspace>>,
    /// The verbs that the driver gave, when it gave them.
    verbs: Option<&'toolset Arc<dyn Verbs>>,
    /// The store of the calls.
    store: &'toolset Mutex<Store>,
    /// The subscriptions, which hold the views of the running jobs.
    #[cfg(feature = "instrument")]
    subscriptions: &'toolset Mutex<Subscriptions>,
    /// The deliveries.
    deliveries: &'toolset Deliveries,
    /// The log.
    log: &'toolset Mutex<Log>,
}

/// What each acceptor reads and writes besides its connection: the manifest,
/// the store, the worker's queue, the subscriptions and their table, the
/// deliveries and the log.
struct Desk<'toolset, Log>
{
    /// The answer to a `GET` of the manifest.
    manifest: &'toolset Buffer,
    /// The store of rows.
    store: &'toolset Mutex<Store>,
    /// The worker's queue, which a cancel and a closure end jobs on too.
    queue: Sender<Queued>,
    /// The subscriptions.
    subscriptions: &'toolset Mutex<Subscriptions>,
    /// The table that keeps the subscriptions.
    table: &'toolset Table,
    /// The deliveries.
    deliveries: &'toolset Deliveries,
    /// Where the toolset tells what went wrong.
    log: &'toolset Mutex<Log>,
}

/// Accept each connection `listener` takes and answer its one request at
/// `desk`, until accepting fails.
///
/// # Specification
/// trivial.
fn accept<Log>(
    listener: &TcpListener,
    desk: &Desk<'_, Log>,
) -> io::Result<()>
where
    Log: Write,
{
    let mut buffer = Buffer::default();
    loop {
        let mut stream = match listener.accept() {
            Ok((stream, _peer)) => stream,
            Err(error)
                if matches!(
                    error.kind(),
                    io::ErrorKind::Interrupted | io::ErrorKind::ConnectionAborted
                ) =>
            {
                continue;
            },
            Err(error) => return Err(error),
        };
        // A client that faults costs its own connection alone.
        drop(answer(&mut stream, &mut buffer, desk));
    }
}

/// Read the one request on `stream` into `buffer`, and answer it at `desk`.
///
/// # Specification
/// trivial.
fn answer<Log>(
    stream: &mut TcpStream,
    buffer: &mut Buffer,
    desk: &Desk<'_, Log>,
) -> io::Result<()>
where
    Log: Write,
{
    stream.set_read_timeout(Some(REQUEST_WAIT))?;
    stream.set_nodelay(true)?;
    let request = read_request(stream, buffer)?;
    let body = buffer.0.get(request.body).unwrap_or_default();
    match request.route {
        Route::Manifest => stream.write_all(&desk.manifest.0),
        Route::Unknown => stream.write_all(NOT_FOUND),
        Route::TooLarge => stream.write_all(TOO_LARGE),
        // RAP's cancellation and closure are best effort, so each is answered
        // `200` whatever its body names.
        Route::Cancel | Route::Close => {
            // A body that is not JSON names no row.
            let named = serde_json::from_slice(body).unwrap_or(Value::Null);
            ended(request.route, &named, desk);
            stream.write_all(ACKNOWLEDGED)
        },
        Route::Invoke => {
            let invocation = match serde_json::from_slice::<Invocation>(body) {
                Ok(invocation) if invocation.callback_url.starts_with("http://") => invocation,
                Ok(_) => return refuse(stream, &"the callback URL is not an `http` URL"),
                Err(error) => {
                    return refuse(
                        stream,
                        &alloc::format!("the body is not an invocation: {error}"),
                    );
                },
            };
            let Invocation {
                operation,
                arguments,
                id,
                call_id,
                callback_url,
                group_id,
            } = invocation;
            let pending = Pending {
                group_id,
                id,
                call_id,
                callback_url,
                token: request.bearer,
                operation,
                started: SystemTime::now()
                    .duration_since(SystemTime::UNIX_EPOCH)
                    .map_or(0, |since| {
                        u64::try_from(since.as_millis()).unwrap_or(u64::MAX)
                    }),
            };
            if lock(desk.store).opened(&pending).is_err() {
                return stream.write_all(UNSTORED);
            }
            // The call reaches the queue before its acknowledgement, so a
            // cancel that the runtime sends after it queues after the call.
            // The row is written: the call is answered whether or not the
            // acknowledgement reached its caller.
            drop(desk.queue.send(Queued::Call(Call {
                pending,
                arguments: Some(arguments),
            })));
            stream.write_all(ACKNOWLEDGED)
        },
    }
}

/// Drop each subscription that `request`, the body of a request on `route`,
/// names, and end each job that it names: a cancel names a `tool_call_id`,
/// and narrows to a `group_id` when it names one. A closure names a
/// `thread_id`, the `group_id` of its rows. Forget the deliveries of each row
/// dropped, and write the table at `desk` once. A body that names no row drops
/// nothing.
///
/// # Specification
/// trivial.
fn ended<Log>(
    route: Route,
    request: &Value,
    desk: &Desk<'_, Log>,
) where
    Log: Write,
{
    let named = |field| request.get(field).and_then(Value::as_str);
    let stopping = match route {
        Route::Cancel => named("tool_call_id").map(|id| Ending {
            group_id: named("group_id").map(String::from),
            id: Some(String::from(id)),
        }),
        Route::Close => named("thread_id").map(|group_id| Ending {
            group_id: Some(String::from(group_id)),
            id: None,
        }),
        Route::Manifest | Route::Invoke | Route::Unknown | Route::TooLarge => None,
    };
    if let Some(stopping) = stopping {
        drop(desk.queue.send(Queued::End(stopping)));
    }
    let mut subscriptions = lock(desk.subscriptions);
    let ending: Vec<Row> = subscriptions
        .rows
        .keys()
        .filter(|&row| match (route, row) {
            (Route::Cancel, &Row::Subscription(ref group_id, ref tool_call_id)) => {
                named("tool_call_id") == Some(tool_call_id.as_str())
                    && named("group_id").is_none_or(|named| named == group_id)
            },
            (Route::Close, &Row::Subscription(ref group_id, _)) => {
                named("thread_id") == Some(group_id.as_str())
            },
            _ => false,
        })
        .cloned()
        .collect();
    if ending.is_empty() {
        return;
    }
    for row in &ending {
        drop(subscriptions.remove(row));
        desk.deliveries.forget(row);
    }
    // The removal of a row only ends a watch, which cannot fail.
    #[cfg(feature = "instrument")]
    drop(subscriptions.follow());
    let snapshot = subscriptions.snapshot();
    drop(subscriptions);
    // A flush to the disk takes milliseconds, so the file is written outside
    // the lock of the subscriptions.
    if let Err(error) = snapshot.and_then(|snapshot| desk.table.write(&snapshot)) {
        drop(writeln!(
            lock(desk.log),
            "the toolset did not write its table after a request ended a subscription: {error}"
        ));
    }
}

/// Answer `400` on `stream`, saying `reason`.
///
/// # Specification
/// trivial.
fn refuse(
    stream: &mut TcpStream,
    reason: &dyn core::fmt::Display,
) -> io::Result<()>
{
    let reason = alloc::format!("{reason}");
    let answer = alloc::format!(
        "HTTP/1.1 400 Bad Request\r\ncontent-type: text/plain; charset=utf-8\r\ncontent-length: {}\r\nconnection: close\r\n\r\n{reason}",
        reason.len()
    );
    stream.write_all(answer.as_bytes())
}

/// Read one request from `stream` into `buffer`: its head, and the body its
/// `Content-Length` names.
///
/// # Specification
/// trivial.
fn read_request(
    stream: &mut TcpStream,
    buffer: &mut Buffer,
) -> io::Result<Request>
{
    buffer.0.clear();
    let mut chunk = [0_u8; 4096];
    let (route, bearer, head, length) = loop {
        let read = stream.read(&mut chunk)?;
        if read == 0 {
            return Err(io::ErrorKind::UnexpectedEof.into());
        }
        buffer
            .0
            .extend_from_slice(chunk.get(.. read).unwrap_or_default());
        let mut headers = [httparse::EMPTY_HEADER; HEADERS];
        let mut request = httparse::Request::new(&mut headers);
        match request.parse(&buffer.0).map_err(io::Error::other)? {
            httparse::Status::Partial if buffer.0.len() > HEAD_LIMIT => {
                return Err(io::ErrorKind::InvalidData.into());
            },
            httparse::Status::Partial => {},
            httparse::Status::Complete(head) => {
                let route = match (request.method, request.path) {
                    (Some("GET"), Some(MANIFEST)) => Route::Manifest,
                    (Some("POST"), Some(INVOKE)) => Route::Invoke,
                    (Some("POST"), Some(CANCEL)) => Route::Cancel,
                    (Some("POST"), Some(CLOSE)) => Route::Close,
                    _ => Route::Unknown,
                };
                let mut length = 0_usize;
                let mut bearer = None;
                for header in request.headers.iter() {
                    let value = core::str::from_utf8(header.value)
                        .unwrap_or_default()
                        .trim();
                    if header.name.eq_ignore_ascii_case("content-length") {
                        length = value.parse().map_err(io::Error::other)?;
                    }
                    else if header.name.eq_ignore_ascii_case("authorization") {
                        bearer = value
                            .split_once(' ')
                            .filter(|&(scheme, _token)| scheme.eq_ignore_ascii_case("bearer"))
                            .map(|(_scheme, token)| String::from(token.trim()));
                    }
                }
                break (route, bearer, head, length);
            },
        }
    };
    if length > BODY_LIMIT {
        return Ok(Request {
            route: Route::TooLarge,
            bearer,
            body: 0 .. 0,
        });
    }
    let end = head.saturating_add(length);
    let missing = end.saturating_sub(buffer.0.len());
    if missing > 0 {
        let _read = io::Read::take(&mut *stream, u64::try_from(missing).unwrap_or(u64::MAX))
            .read_to_end(&mut buffer.0)?;
    }
    if buffer.0.len() < end {
        return Err(io::ErrorKind::UnexpectedEof.into());
    }
    Ok(Request {
        route,
        bearer,
        body: head .. end,
    })
}

/// Answer each call `queued` holds over `workspace`, keep its answer in
/// `store`, open the subscription it confirms in `subscriptions` and `table`,
/// and owe its result to `deliveries`, telling `log` of each answer that the
/// store does not keep. Send each long operation to the thread of the jobs,
/// which answers it when its job ends, and each end of jobs after the starts
/// that the queue holds before it.
///
/// # Specification
/// trivial.
fn work<Log>(
    queued: Receiver<Queued>,
    (workspace, jobs): (&Mutex<Workspace>, &Sender<Command>),
    store: &Mutex<Store>,
    subscriptions: &Mutex<Subscriptions>,
    table: &Table,
    deliveries: &Deliveries,
    log: &Mutex<Log>,
) where
    Log: Write,
{
    for queued in queued {
        let Call { pending, arguments } = match queued {
            Queued::Call(call) => call,
            Queued::End(ending) => {
                drop(jobs.send(Command::End(ending)));
                continue;
            },
        };
        match job_of(&pending, arguments.as_ref()) {
            Some(Ok(job)) => {
                drop(jobs.send(Command::Start(pending, job)));
                continue;
            },
            Some(Err(refused)) => {
                owe_answer(&pending, &refused, store, deliveries, log);
                continue;
            },
            None => {},
        }
        let mut answer = answered(&pending, arguments, workspace);
        // A subscription reaches the table before its result is owed. The
        // lock is held until the result is owed, so that no event of the
        // subscription is owed before its result. This is the one write of
        // the table under the lock, and a subscription opens rarely.
        let opened = if let Some(ref scope) = answer.subscription {
            let mut held = lock(subscriptions);
            let row = held.insert(Kept {
                group_id: pending.group_id.clone(),
                tool_call_id: pending.id.clone(),
                callback_url: pending.callback_url.clone(),
                token: pending.token.clone(),
                scope: scope.clone(),
                last_version: None,
            });
            // A row that follows the activity starts the watch first.
            #[cfg(feature = "instrument")]
            let followed = held.follow();
            #[cfg(not(feature = "instrument"))]
            let followed = Ok(());
            let kept = followed
                .and_then(|()| held.snapshot())
                .and_then(|snapshot| table.write(&snapshot));
            if let Err(error) = kept {
                drop(held.remove(&row));
                #[cfg(feature = "instrument")]
                drop(held.follow());
                answer.subscription = None;
                answer.text =
                    alloc::format!("Error: the toolset did not keep the subscription: {error}");
            }
            Some(held)
        }
        else {
            None
        };
        owe_answer(&pending, &answer, store, deliveries, log);
        drop(opened);
    }
}

/// The job of the call `pending` with `arguments`, or the answer that refuses
/// its arguments, when the call is a long operation. A call that a crash cut
/// short has no arguments and no job.
///
/// # Specification
/// trivial.
fn job_of(
    pending: &Pending,
    arguments: Option<&Value>,
) -> Option<Result<tools::Job, Answer>>
{
    let name = Value::String(pending.operation.clone());
    let job = tools::job(&name, arguments?)?;
    Some(job.map_err(|refusal| Answer {
        group_id: pending.group_id.clone(),
        id: pending.id.clone(),
        text: alloc::format!("Error: {refusal}"),
        display: None,
        version: None,
        subscription: None,
    }))
}

/// Keep `answer`, the answer of the call `pending`, in `store`, and owe its
/// result to `deliveries`, telling `log` when the store does not keep it.
///
/// # Specification
/// trivial.
fn owe_answer<Log>(
    pending: &Pending,
    answer: &Answer,
    store: &Mutex<Store>,
    deliveries: &Deliveries,
    log: &Mutex<Log>,
) where
    Log: Write,
{
    let kept = lock(store).answered(answer);
    if let Err(error) = kept {
        drop(writeln!(
            lock(log),
            "the toolset did not keep the answer of the call {} of {}: {error}",
            pending.id,
            pending.group_id
        ));
    }
    deliveries.owe(
        Row::Call(pending.group_id.clone(), pending.id.clone()),
        result(pending, answer),
    );
}

/// The answer of the call `pending` with `arguments` over `workspace`, absent
/// arguments meaning a call that a crash cut short.
///
/// # Specification
/// trivial.
fn answered(
    pending: &Pending,
    arguments: Option<Value>,
    workspace: &Mutex<Workspace>,
) -> Answer
{
    let mut answer = Answer {
        group_id: pending.group_id.clone(),
        id: pending.id.clone(),
        text: String::new(),
        display: None,
        version: None,
        subscription: None,
    };
    answer.text = match arguments {
        None => String::from(LOST),
        // This face encodes the answer of `diagnostics` as the bus's frame of
        // the document, a projection of the state that the table's row reads.
        Some(arguments) if pending.operation == DIAGNOSTICS => {
            let workspace = lock(workspace);
            let frame =
                tools::held(&workspace, &arguments).map(|(uri, _version)| workspace.rendered(&uri));
            drop(workspace);
            match frame {
                Err(refusal) => alloc::format!("Error: {refusal}"),
                Ok(frame) => match frame.as_ref().and_then(carded) {
                    None => String::from("Error: the document closed"),
                    Some((document, report)) => {
                        answer.display = Some(report_lines(document, report).join("\n"));
                        answer.version = Some(i32::from(document.version));
                        cards(document, report)
                    },
                },
            }
        },
        // A subscription confirms with its scope, and the worker opens it. The
        // table answers every other operation, and refuses a name that it
        // does not hold.
        Some(arguments) => {
            let name = Value::String(pending.operation.clone());
            match tools::subscription(&name, &arguments) {
                Some(Ok(scope)) => {
                    let text = json!({ "subscription": pending.id, "scope": &scope }).to_string();
                    answer.subscription = Some(scope);
                    text
                },
                Some(Err(refusal)) => alloc::format!("Error: {refusal}"),
                None => {
                    let called = tools::call(&mut lock(workspace), Some(&name), &arguments);
                    match called {
                        Ok(answer) => answer.to_string(),
                        Err(refusal) => alloc::format!("Error: {refusal}"),
                    }
                },
            }
        },
    };
    answer
}

/// The document of `frame` and its report, when `frame` is the report of a
/// document.
///
/// # Specification
/// trivial.
fn carded(frame: &RenderFrame) -> Option<(&DocId, &ReportView)>
{
    match (frame.scope(), frame.body()) {
        (&FrameScope::Document(ref document), &FrameBody::Frame { ref report }) => {
            Some((document, report))
        },
        (
            &(FrameScope::Connection | FrameScope::Document(_)),
            &(FrameBody::Hello { .. }
            | FrameBody::Frame { .. }
            | FrameBody::Resync
            | FrameBody::Accounts { .. }
            | FrameBody::AccountPatch { .. }
            | FrameBody::Activity { .. }
            | FrameBody::Detach),
        ) => None,
    }
}

/// The text of the frame of `document`: its URI, its version, and the cards
/// of `report`, as JSON.
///
/// # Specification
/// trivial.
fn cards(
    document: &DocId,
    report: &ReportView,
) -> String
{
    serde_json::to_string(&Cards {
        document,
        diagnostics: &report.diagnostics,
        goals: &report.goals,
    })
    .unwrap_or_default()
}

/// `value` as JSON: a text as a JSON string, with its quotes.
///
/// # Specification
/// trivial.
fn quoted<Encoded>(value: &Encoded) -> String
where
    Encoded: Serialize + ?Sized,
{
    serde_json::to_string(value).unwrap_or_default()
}

/// The `tool_result` that carries `answer`, the answer of `pending`, keyed by
/// its `id`.
///
/// # Specification
/// trivial.
fn result(
    pending: &Pending,
    answer: &Answer,
) -> Post
{
    let mut head = alloc::format!(
        "{{\"type\":\"tool_result\",\"group_id\":{},\"id\":{},\"call_id\":{},",
        quoted(&pending.group_id),
        quoted(&pending.id),
        quoted(&pending.call_id)
    );
    if let Some(ref display) = answer.display {
        head.push_str("\"display_as\":[{\"type\":\"text\",\"content\":");
        head.push_str(&quoted(display));
        head.push_str("}],");
    }
    if let Some(version) = answer.version {
        head.push_str("\"version\":");
        head.push_str(&version.to_string());
        head.push(',');
    }
    if answer.subscription.is_some() {
        head.push_str("\"subscription\":true,");
    }
    head.push_str("\"text\":");
    Post {
        callback_url: Arc::from(pending.callback_url.as_str()),
        token: pending.token.as_deref().map(Arc::from),
        key: pending.id.clone(),
        version: answer.version,
        head,
        text: Arc::from(quoted(&answer.text)),
    }
}

/// Owe each subscription the new frame of each document that `changes` names,
/// until the workspace ends the watch, and tell the thread of the jobs of each
/// document. A document that no subscription follows costs a lookup.
///
/// # Specification
/// trivial.
fn fan_out(
    changes: Receiver<DocumentUri>,
    (workspace, jobs): (&Mutex<Workspace>, &Sender<Command>),
    subscriptions: &Mutex<Subscriptions>,
    deliveries: &Deliveries,
)
{
    for uri in changes {
        publish_frame(&uri, workspace, subscriptions, deliveries);
        // The thread of the jobs retires each job that reads an older revision.
        drop(jobs.send(Command::Changed(uri)));
    }
}

/// Owe each subscription to the frame of `uri` its new frame. A document that
/// no subscription follows costs a lookup.
///
/// # Specification
/// trivial.
fn publish_frame(
    uri: &DocumentUri,
    workspace: &Mutex<Workspace>,
    subscriptions: &Mutex<Subscriptions>,
    deliveries: &Deliveries,
)
{
    let followed = lock(subscriptions).diagnostics.contains_key(uri);
    if !followed {
        return;
    }
    let Some(frame) = lock(workspace).rendered(uri)
    else {
        return;
    };
    let Some((document, report)) = carded(&frame)
    else {
        return;
    };
    let state = State {
        version: i32::from(document.version),
        text: Arc::from(quoted(&cards(document, report))),
    };
    lock(subscriptions).publish_diagnostics(uri, &state, deliveries);
}

/// Owe each subscription to a declaration of a document that `settlements`
/// names the card of that declaration, after each admission that settles the
/// document, until the workspace ends the watch, and tell the thread of the
/// jobs of each admission. A document that no subscription follows costs a
/// lookup.
///
/// # Specification
/// trivial.
fn fan_out_accounts(
    settlements: Receiver<DocumentUri>,
    (workspace, jobs): (&Mutex<Workspace>, &Sender<Command>),
    subscriptions: &Mutex<Subscriptions>,
    deliveries: &Deliveries,
)
{
    // One map serves every pass, and each pass clears it.
    let mut states: BTreeMap<String, State> = BTreeMap::new();
    for uri in settlements {
        states.clear();
        publish_settled((&uri, &mut states), workspace, subscriptions, deliveries);
        // The thread of the jobs answers each replay that the admission ends.
        drop(jobs.send(Command::Settled(uri)));
    }
}

/// Owe each subscription to a declaration of `uri` the card of that
/// declaration, with `states` as the map of the states of the pass. A document
/// that no subscription follows costs a lookup.
///
/// # Specification
/// trivial.
fn publish_settled(
    (uri, states): (&DocumentUri, &mut BTreeMap<String, State>),
    workspace: &Mutex<Workspace>,
    subscriptions: &Mutex<Subscriptions>,
    deliveries: &Deliveries,
)
{
    let declarations = lock(subscriptions).declarations(uri);
    if declarations.is_empty() {
        return;
    }
    let Some((document, cards)) = lock(workspace).accounted(uri)
    else {
        return;
    };
    // The first card of a name in document order is the one that a
    // subscription to the name follows.
    for card in &cards {
        if declarations.contains(&card.name) && !states.contains_key(&card.name) {
            let accounted = Accounted {
                uri,
                declaration: &card.name,
                card: Some(card),
            };
            let state = account_state(&accounted, &document);
            drop(states.insert(String::from(card.name.as_str()), state));
        }
    }
    // A subscription to a name that no declaration has follows null.
    for declaration in declarations {
        if let alloc::collections::btree_map::Entry::Vacant(vacant) = states.entry(declaration) {
            let accounted = Accounted {
                uri,
                declaration: vacant.key(),
                card: None,
            };
            let state = account_state(&accounted, &document);
            let _null = vacant.insert(state);
        }
    }
    lock(subscriptions).publish_accounts(uri, states, deliveries);
}

/// The state that `accounted` gives each subscription to its declaration in
/// `document`.
///
/// # Specification
/// trivial.
fn account_state(
    accounted: &Accounted<'_>,
    document: &DocId,
) -> State
{
    State {
        version: i32::from(document.version),
        text: Arc::from(quoted(
            &serde_json::to_string(accounted).unwrap_or_default(),
        )),
    }
}

/// Add each tick of the hub's fold that `ticks` carries to each row that
/// follows the activity, until the toolset ends its watch. The row of each
/// core is encoded once for each tick, outside the lock.
///
/// # Specification
/// trivial.
#[cfg(feature = "instrument")]
fn fan_out_activity(
    ticks: Receiver<Arc<Tick>>,
    subscriptions: &Mutex<Subscriptions>,
    deliveries: &Deliveries,
)
{
    for tick in ticks {
        let occupancy = activity::rows(&tick.rows);
        lock(subscriptions).publish_activity(&tick, occupancy, deliveries);
    }
}

/// Act on `fate`, how the deliveries of `row` ended: settle a call that a
/// runtime took or refused, record the version of a state that a runtime took,
/// drop a subscription that a runtime refused, and mark one whose retries are
/// spent. A row that follows the activity lets go of the state it took and is
/// owed its next state on `deliveries`. A job whose view a runtime refused
/// hears no more updates. Tell `log` of each fate but a delivery taken, of a
/// subscription that is reachable again, and of a table that could not be
/// written.
///
/// # Specification
/// trivial.
fn told<Log>(
    row: &Row,
    fate: &Fate,
    store: &Mutex<Store>,
    subscriptions: &Mutex<Subscriptions>,
    table: &Table,
    #[cfg_attr(
        not(feature = "instrument"),
        expect(
            unused_variables,
            reason = "only a row that follows the activity is owed a state when its runtime takes one"
        )
    )]
    deliveries: &Deliveries,
    log: &Mutex<Log>,
) where
    Log: Write,
{
    match (row, fate) {
        (&Row::Call(..), &Fate::Spent(..)) => {},
        (&Row::Call(..), &(Fate::Taken(_) | Fate::Refused(_))) => {
            let settled = lock(store).settled(row);
            if let Err(error) = settled {
                drop(writeln!(
                    lock(log),
                    "the toolset did not settle {row}: {error}"
                ));
            }
        },
        (&Row::Subscription(..), &Fate::Taken(version)) => {
            let mut held = lock(subscriptions);
            #[cfg(feature = "instrument")]
            held.ledger_taken(row, deliveries);
            let (recovered, advanced) =
                held.rows
                    .get_mut(row)
                    .map_or((false, false), |subscription| {
                        let advanced = version.is_some_and(|version| {
                            subscription
                                .kept
                                .last_version
                                .is_none_or(|taken| version > taken)
                        });
                        if advanced {
                            subscription.kept.last_version = version;
                        }
                        (core::mem::take(&mut subscription.unreachable), advanced)
                    });
            let snapshot = advanced.then(|| held.snapshot());
            drop(held);
            if recovered {
                drop(writeln!(lock(log), "{row} is reachable again"));
            }
            // A flush to the disk takes milliseconds, so the file is written
            // outside the lock of the subscriptions.
            let saved = snapshot.map_or(Ok(()), |snapshot| table.write(&snapshot?));
            if let Err(error) = saved {
                drop(writeln!(
                    lock(log),
                    "the toolset did not write its table after {row} took a state: {error}"
                ));
            }
        },
        (&Row::Subscription(..), &Fate::Refused(_)) => {
            let mut held = lock(subscriptions);
            let snapshot = held.remove(row).map(|_dropped| held.snapshot());
            // The removal of a row only ends a watch, which cannot fail.
            #[cfg(feature = "instrument")]
            drop(held.follow());
            drop(held);
            let saved = snapshot.map_or(Ok(()), |snapshot| table.write(&snapshot?));
            if let Err(error) = saved {
                drop(writeln!(
                    lock(log),
                    "the toolset did not write its table after it dropped {row}: {error}"
                ));
            }
        },
        (&Row::Subscription(..), &Fate::Spent(..)) => {
            if let Some(subscription) = lock(subscriptions).rows.get_mut(row) {
                subscription.unreachable = true;
                // The next tick owes the events of the state it dropped.
                #[cfg(feature = "instrument")]
                subscription.ledger.spent();
            }
        },
        #[cfg(feature = "instrument")]
        (&Row::View(..), _) => {
            if matches!(*fate, Fate::Refused(_)) {
                let mut held = lock(subscriptions);
                drop(held.views.remove(row));
                // The removal of a view only ends a watch, which cannot fail.
                drop(held.follow());
                drop(held);
            }
        },
    }
    if !matches!(*fate, Fate::Taken(_)) {
        drop(writeln!(lock(log), "the delivery to {row} was {fate}"));
    }
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;
    use alloc::sync::Arc;
    use alloc::vec::Vec;
    use core::net::Ipv4Addr;
    use core::net::SocketAddr;
    use core::time::Duration;
    use std::io::Read as _;
    use std::io::Write as _;
    use std::net::TcpListener;
    use std::net::TcpStream;
    use std::path::Path;
    use std::path::PathBuf;
    use std::thread;

    use gandr_surface_dispatcher::Pool;
    use gandr_surface_dispatcher::Threads;
    use gandr_surface_dispatcher::Verb;
    use gandr_surface_dispatcher::Width;
    use gandr_surface_lsp::Peer;
    use gandr_surface_lsp::Workspace;
    use gandr_surface_lsp::bind;
    use gandr_surface_lsp::run_hub;
    use quenchant_shape::shape::Maybe;
    use serde_json::Value;
    use serde_json::json;

    use super::Announcement;
    use super::Buffer;
    use super::LOST;
    use super::Policy;
    use super::REQUEST_WAIT;
    use super::Toolset;
    use super::Verbs;
    use crate::face::tests::Editor;
    use crate::face::tests::Model;
    use crate::face::tests::Scratch;
    use crate::tools;

    /// An HTTP message: its head, and its body.
    struct Message
    {
        /// The start line and the headers, without the blank line.
        head: String,
        /// The body.
        body: Vec<u8>,
    }

    impl Message
    {
        /// The message `bytes` holds.
        ///
        /// # Specification
        /// trivial.
        fn parsed(Buffer(bytes): Buffer) -> Self
        {
            let end = bytes
                .windows(4)
                .position(|window| window == b"\r\n\r\n")
                .expect("a head ends");
            let (head, body) = bytes.split_at(end);
            Self {
                head: String::from_utf8(head.to_vec()).expect("a head is text"),
                body: body.get(4 ..).unwrap_or_default().to_vec(),
            }
        }

        /// Whether the head carries `header`, compared without case.
        ///
        /// # Specification
        /// trivial.
        fn carries(
            &self,
            header: &Value,
        ) -> Answer
        {
            let header = header.as_str().unwrap_or_default().to_ascii_lowercase();
            Answer(
                self.head
                    .to_ascii_lowercase()
                    .split("\r\n")
                    .any(|line| line == header),
            )
        }

        /// The body, parsed.
        ///
        /// # Specification
        /// trivial.
        fn json(&self) -> Value
        {
            serde_json::from_slice(&self.body).expect("the body is JSON")
        }
    }

    /// A yes or no the tests compare.
    #[repr(transparent)]
    #[derive(Debug, Eq, PartialEq)]
    struct Answer(bool);

    /// A hub serving `scratch`'s socket, with the line face and `toolset`
    /// beside it. The hub serves for the life of the test process.
    ///
    /// # Specification
    /// trivial.
    fn hub(
        scratch: &Scratch,
        toolset: Toolset,
    )
    {
        hub_over(
            scratch,
            toolset,
            Workspace::spelled(gandr_surface_lsp::Spelling::Unicode),
        );
    }

    /// A hub serving `scratch`'s socket over `workspace`, with the line face
    /// and `toolset` beside it. The hub serves for the life of the test
    /// process.
    ///
    /// # Specification
    /// trivial.
    fn hub_over(
        scratch: &Scratch,
        toolset: Toolset,
        workspace: Workspace,
    )
    {
        let socket = scratch.socket();
        let Maybe::Present(listener) = bind(&socket).expect("the socket binds")
        else {
            panic!("no other hub serves a fresh socket");
        };
        drop(thread::spawn(move || {
            run_hub(
                &listener,
                &socket,
                Duration::from_millis(100),
                std::io::sink(),
                Some(crate::serve),
                Some(Box::new(
                    move |workspace: alloc::sync::Arc<std::sync::Mutex<Workspace>>, peer: Peer| {
                        toolset
                            .serve(&workspace, peer, std::io::sink())
                            .expect("the toolset serves");
                    },
                )),
                workspace,
            )
            .expect("the hub serves");
        }));
    }

    /// A workspace whose pool has two threads, so a job runs beside the thread
    /// of the jobs, as on a host of two cores or more.
    ///
    /// # Specification
    /// trivial.
    fn parallel() -> Workspace
    {
        Workspace::spelled(gandr_surface_lsp::Spelling::Unicode).pooled(Arc::new(Pool::new(
            Width::Threads(Threads::from(
                core::num::NonZeroUsize::MIN.saturating_add(1),
            )),
        )))
    }

    /// A listener on the loopback interface, at a port the system picks.
    ///
    /// # Specification
    /// trivial.
    fn loopback() -> TcpListener
    {
        TcpListener::bind((Ipv4Addr::LOCALHOST, 0_u16)).expect("the loopback binds")
    }

    /// The file of rows inside `scratch`.
    ///
    /// # Specification
    /// trivial.
    fn calls(scratch: &Scratch) -> PathBuf
    {
        scratch.socket().with_file_name("state").join("calls.jsonl")
    }

    /// The subscription table inside `scratch`.
    ///
    /// # Specification
    /// trivial.
    fn table(scratch: &Scratch) -> PathBuf
    {
        scratch
            .socket()
            .with_file_name("state")
            .join("subscriptions.json")
    }

    /// A toolset whose store and table are inside `scratch`.
    ///
    /// # Specification
    /// trivial.
    fn opened(scratch: &Scratch) -> Toolset
    {
        Toolset::open(
            loopback(),
            &calls(scratch),
            &table(scratch),
            Policy::default(),
        )
        .expect("the store and the table open")
    }

    /// Each row of the table at `path` as its `tool_call_id` and its
    /// `last_version`, once they are `expected` or after ten seconds. A table
    /// with no file has no row.
    ///
    /// # Specification
    /// trivial.
    fn awaited(
        path: &Path,
        expected: &Value,
    ) -> Value
    {
        let deadline = std::time::Instant::now()
            .checked_add(Duration::from_secs(10))
            .expect("the deadline is representable");
        loop {
            let rows: Value = match std::fs::read(path) {
                Ok(bytes) => serde_json::from_slice(&bytes).expect("the table is JSON"),
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => json!([]),
                Err(error) => panic!("the table cannot be read: {error}"),
            };
            let summary = Value::Array(
                rows.as_array()
                    .expect("the table is an array")
                    .iter()
                    .map(|row| json!([row.get("tool_call_id"), row.get("last_version")]))
                    .collect(),
            );
            if &summary == expected || std::time::Instant::now() >= deadline {
                return summary;
            }
            thread::sleep(Duration::from_millis(10));
        }
    }

    /// Send `request` to `address` and read the answer until the toolset
    /// closes the connection.
    ///
    /// # Specification
    /// trivial.
    fn exchange(
        address: SocketAddr,
        request: &Message,
    ) -> Message
    {
        let mut stream = TcpStream::connect(address).expect("the toolset accepts");
        stream
            .write_all(alloc::format!("{}\r\n\r\n", request.head).as_bytes())
            .expect("the toolset reads the head");
        stream
            .write_all(&request.body)
            .expect("the toolset reads the body");
        let mut answer = Vec::new();
        let _read = stream
            .read_to_end(&mut answer)
            .expect("the toolset answers");
        Message::parsed(Buffer(answer))
    }

    /// A `POST` of `invocation` to the invoke endpoint at `address`, with
    /// `bearer` when one is given.
    ///
    /// # Specification
    /// trivial.
    fn invoke(
        address: SocketAddr,
        invocation: &Value,
        bearer: Option<&Value>,
    ) -> Message
    {
        let body = invocation.to_string().into_bytes();
        let mut head = alloc::format!(
            "POST /invoke HTTP/1.1\r\nhost: {address}\r\ncontent-type: application/json\r\ncontent-length: {}",
            body.len()
        );
        if let Some(bearer) = bearer.and_then(Value::as_str) {
            head.push_str("\r\nauthorization: Bearer ");
            head.push_str(bearer);
        }
        exchange(address, &Message { head, body })
    }

    /// The next request `callback` takes, read whole and answered `200`.
    ///
    /// # Specification
    /// trivial.
    fn received(callback: &TcpListener) -> Message
    {
        heard(callback, &json!("200 OK"))
    }

    /// The next request `callback` takes, read whole and answered with the
    /// status line `status`.
    ///
    /// # Specification
    /// trivial.
    fn heard(
        callback: &TcpListener,
        status: &Value,
    ) -> Message
    {
        answered(callback, status).0
    }

    /// The next request `callback` takes, read whole and answered with the
    /// status line `status`, and the instant just before the answer is
    /// written. The toolset reads the answer after that instant, so a wait
    /// the toolset starts when it reads the answer starts after it too.
    ///
    /// # Specification
    /// trivial.
    fn answered(
        callback: &TcpListener,
        status: &Value,
    ) -> (Message, std::time::Instant)
    {
        let (mut stream, _peer) = callback.accept().expect("the toolset calls back");
        stream
            .set_read_timeout(Some(Duration::from_secs(10)))
            .expect("the timeout is set");
        let mut bytes = Vec::new();
        let mut chunk = [0_u8; 4096];
        let message = loop {
            let read = stream.read(&mut chunk).expect("the callback reads");
            assert_ne!(read, 0_usize, "the toolset ended its request early");
            bytes.extend_from_slice(chunk.get(.. read).unwrap_or_default());
            if let Some(end) = bytes.windows(4).position(|window| window == b"\r\n\r\n") {
                let head = String::from_utf8_lossy(bytes.get(.. end).unwrap_or_default())
                    .to_ascii_lowercase();
                let length: usize = head
                    .split("\r\n")
                    .find_map(|line| line.strip_prefix("content-length: "))
                    .and_then(|length| length.parse().ok())
                    .expect("the request names its length");
                if bytes.len() >= end.saturating_add(4).saturating_add(length) {
                    break Message::parsed(Buffer(bytes));
                }
            }
        };
        let before = std::time::Instant::now();
        stream
            .write_all(
                alloc::format!(
                    "HTTP/1.1 {}\r\ncontent-length: 0\r\n\r\n",
                    status.as_str().unwrap_or_default()
                )
                .as_bytes(),
            )
            .expect("the toolset reads the answer");
        (message, before)
    }

    /// Whether `callback` takes no request for `wait`.
    ///
    /// # Specification
    /// trivial.
    fn quiet(
        callback: &TcpListener,
        wait: Duration,
    ) -> Answer
    {
        callback
            .set_nonblocking(true)
            .expect("the listener stops blocking");
        let started = std::time::Instant::now();
        let mut silent = Answer(true);
        while started.elapsed() < wait {
            if callback.accept().is_ok() {
                silent = Answer(false);
                break;
            }
            thread::sleep(Duration::from_millis(10));
        }
        callback
            .set_nonblocking(false)
            .expect("the listener blocks again");
        silent
    }

    /// The frame that the text of `message`, a result or an event, holds.
    ///
    /// # Specification
    /// trivial.
    fn framed(message: &Value) -> Value
    {
        serde_json::from_str(
            message
                .get("text")
                .and_then(Value::as_str)
                .expect("the message is a text"),
        )
        .expect("the text is a frame as JSON")
    }

    /// Hear the states of the activity row `work-1` on `callback` until one
    /// carries the end of an admission, and give the run that keys them.
    /// Each state routes to the row, has no version, and is keyed by the run
    /// and its last sequence number. The events come once each, in the order
    /// of their sequence numbers. They hold one admission, a `replay` task,
    /// and the judgement's `fork` tasks, each started and ended.
    ///
    /// # Specification
    /// trivial.
    fn admitted(callback: &TcpListener) -> Value
    {
        let mut run = Value::Null;
        let mut sequences: Vec<u64> = Vec::new();
        let mut tasks: Vec<(String, String)> = Vec::new();
        let mut admitted = false;
        while !admitted {
            let event = received(callback);
            let routed = event.json();
            assert_eq!(
                (
                    routed.get("type"),
                    routed.get("tool_call_id"),
                    routed.get("version")
                ),
                (
                    Some(&json!("subscription_event")),
                    Some(&json!("work-1")),
                    Some(&Value::Null)
                ),
                "an event of the activity routes to its row and has no version: {routed}"
            );
            let state = framed(&routed);
            let events = state["events"]
                .as_array()
                .expect("a state lists its events");
            let last = events
                .last()
                .and_then(|carried| carried["sequence"].as_u64())
                .expect("a state carries one event at least");
            assert_eq!(
                event.carries(&json!(alloc::format!(
                    "idempotency-key: work-1@{}.{last}",
                    state["run"]
                ))),
                Answer(true),
                "the key is the row, the run and the last sequence number: {}",
                event.head
            );
            run = state["run"].clone();
            for carried in events {
                sequences.push(carried["sequence"].as_u64().expect("an event is numbered"));
                let task = carried["task"].as_str().expect("an event names its task");
                let edge = carried["edge"].as_str().expect("an event names its edge");
                admitted |= (task, edge) == ("replay", "end");
                tasks.push((String::from(task), String::from(edge)));
            }
        }
        assert!(
            sequences.is_sorted_by(|earlier, later| earlier < later),
            "each event reaches the runtime once, in the order of the sequence numbers: {sequences:?}"
        );
        let count = |task: &str, edge: &str| {
            tasks
                .iter()
                .filter(|&&(ref named, ref edged)| named == task && edged == edge)
                .count()
        };
        assert_eq!(
            (count("replay", "start"), count("replay", "end")),
            (1, 1),
            "the admission is one replay task: {tasks:?}"
        );
        assert!(
            count("fork", "start") >= 1 && count("fork", "start") == count("fork", "end"),
            "the judgement and its molding jobs are fork tasks, each started and ended: {tasks:?}"
        );
        run
    }

    /// Each tool that `tools` lists, as its name and its input schema.
    ///
    /// # Specification
    /// trivial.
    fn entries(tools: Option<&Value>) -> Vec<Value>
    {
        tools
            .and_then(Value::as_array)
            .expect("the face lists its tools")
            .iter()
            .map(|tool| json!([tool.get("name"), tool.get("inputSchema")]))
            .collect()
    }

    #[test]
    fn both_faces_offer_one_table()
    {
        let scratch = Scratch::new(&json!("faces"));
        let toolset = opened(&scratch);
        let address = toolset.address().expect("the toolset listens");
        hub(&scratch, toolset);
        let mut editor = Editor::new(&scratch);
        let uri = json!("file:///tmp/faces.gandr");
        editor.edit(&uri, &json!(1_i32), &json!("def f = 42 ;\n"));
        let mut model = Model::new(&scratch);

        let listed = model.ask(&json!({ "jsonrpc": "2.0", "id": 1_i32, "method": "tools/list" }));
        let manifest = exchange(address, &Message {
            head: alloc::format!("GET /.well-known/rap-toolset HTTP/1.1\r\nhost: {address}"),
            body: Vec::new(),
        })
        .json();
        let (called_back, called): (Vec<Value>, Vec<Value>) = entries(manifest.get("tools"))
            .into_iter()
            .partition(|entry| {
                entry.get(0).and_then(Value::as_str).is_some_and(|name| {
                    name.starts_with("subscribe_")
                        || matches!(name, "check" | "replay" | "run" | "test")
                })
            });
        assert_eq!(
            called_back
                .iter()
                .map(|entry| entry.get(0))
                .collect::<Vec<_>>(),
            [
                Some(&json!("check")),
                Some(&json!("replay")),
                Some(&json!("run")),
                Some(&json!("subscribe_account")),
                Some(&json!("subscribe_activity")),
                Some(&json!("subscribe_diagnostics")),
                Some(&json!("test"))
            ],
            "the manifest alone offers the subscriptions and the long operations"
        );
        assert_eq!(
            called,
            entries(listed.pointer("/result/tools")),
            "the two faces name the same calls with the same schemas"
        );

        let arguments = json!({ "uri": uri, "line": 0_u32, "character": 4_u32 });
        let mut over_mcp = model
            .ask(
                &json!({ "jsonrpc": "2.0", "id": 2_i32, "method": "tools/call",
                "params": { "name": "type_of", "arguments": arguments } }),
            )
            .pointer("/result/structuredContent")
            .cloned()
            .expect("the call has a structured result");
        // Only the line face writes what changed since the model's last call.
        drop(
            over_mcp
                .as_object_mut()
                .and_then(|answer| answer.remove("changes")),
        );
        let callback = loopback();
        let callback_url = alloc::format!(
            "http://{}/results/faces",
            callback.local_addr().expect("the callback listens")
        );
        let acknowledged = invoke(
            address,
            &json!({ "operation": "type_of", "arguments": arguments, "id": "call-1",
                "callback_url": callback_url, "group_id": "thread-1" }),
            None,
        );
        assert!(
            acknowledged.head.starts_with("HTTP/1.1 200 "),
            "{}",
            acknowledged.head
        );
        let over_rap: Value = serde_json::from_str(
            received(&callback)
                .json()
                .get("text")
                .and_then(Value::as_str)
                .expect("the result is a text"),
        )
        .expect("the text is the answer as JSON");
        assert_eq!(
            over_rap, over_mcp,
            "a call of `type_of` over each face gives the same answer"
        );
    }

    #[test]
    fn the_toolset_answers_a_call_by_its_callback()
    {
        let scratch = Scratch::new(&json!("rap"));
        let toolset = opened(&scratch);
        let address = toolset.address().expect("the toolset listens");
        hub(&scratch, toolset);
        let mut editor = Editor::new(&scratch);
        let uri = json!("file:///tmp/rap.gandr");
        editor.edit(&uri, &json!(1_i32), &json!("def f = 42 ;\n"));

        let manifest = exchange(address, &Message {
            head: alloc::format!("GET /.well-known/rap-toolset HTTP/1.1\r\nhost: {address}"),
            body: Vec::new(),
        });
        assert!(
            manifest.head.starts_with("HTTP/1.1 200 "),
            "{}",
            manifest.head
        );
        let manifest = manifest.json();
        assert_eq!(
            manifest.get("endpoint"),
            Some(&json!(alloc::format!("http://{address}/invoke")))
        );

        let callback = loopback();
        let callback_url = alloc::format!(
            "http://{}/results/seat",
            callback.local_addr().expect("the callback listens")
        );
        let typed = invoke(
            address,
            &json!({ "operation": "type_of", "arguments": { "uri": uri, "line": 0_u32, "character": 4_u32 },
                "id": "call-1", "call_id": "model-1", "callback_url": callback_url, "group_id": "thread-1",
                "user_id": null }),
            Some(&json!("abc")),
        );
        assert!(typed.head.starts_with("HTTP/1.1 200 "), "{}", typed.head);
        assert!(typed.body.is_empty(), "the acknowledgement has no body");
        let result = received(&callback);
        assert!(
            result.head.starts_with("POST /results/seat HTTP/1.1"),
            "{}",
            result.head
        );
        assert_eq!(
            result.carries(&json!("authorization: Bearer abc")),
            Answer(true),
            "the callback carries the caller's bearer back"
        );
        let result = result.json();
        assert_eq!(
            (
                result.get("type"),
                result.get("group_id"),
                result.get("id"),
                result.get("call_id")
            ),
            (
                Some(&json!("tool_result")),
                Some(&json!("thread-1")),
                Some(&json!("call-1")),
                Some(&json!("model-1"))
            )
        );
        let answer: Value = serde_json::from_str(
            result
                .get("text")
                .and_then(Value::as_str)
                .expect("the result is a text"),
        )
        .expect("the text is the answer as JSON");
        assert_eq!(
            answer.pointer("/hover/contents/value"),
            Some(&json!("```gandr\nf : Integer\n```")),
            "the result is the type the hover prints"
        );

        let unknown = invoke(
            address,
            &json!({ "operation": "unknown", "arguments": {}, "id": "call-2", "callback_url": callback_url,
                "group_id": "thread-1" }),
            None,
        );
        assert!(
            unknown.head.starts_with("HTTP/1.1 200 "),
            "{}",
            unknown.head
        );
        let refused = received(&callback);
        assert_eq!(
            refused.carries(&json!("authorization: Bearer abc")),
            Answer(false),
            "a caller that sends no bearer receives none"
        );
        let refused = refused.json();
        assert_eq!(refused.get("call_id"), Some(&Value::Null));
        assert!(
            refused
                .get("text")
                .and_then(Value::as_str)
                .is_some_and(|text| text.starts_with("Error: ")),
            "{refused}"
        );

        let diagnosed = invoke(
            address,
            &json!({ "operation": "diagnostics", "arguments": { "uri": uri }, "id": "call-3",
                "callback_url": callback_url, "group_id": "thread-1" }),
            None,
        );
        assert!(
            diagnosed.head.starts_with("HTTP/1.1 200 "),
            "{}",
            diagnosed.head
        );
        let diagnosed = received(&callback);
        assert_eq!(
            diagnosed.carries(&json!("idempotency-key: call-3")),
            Answer(true),
            "a result is keyed by its call"
        );
        let diagnosed = diagnosed.json();
        assert_eq!(
            framed(&diagnosed),
            json!({ "uri": uri, "version": 1_i32, "diagnostics": [], "goals": [] }),
            "the result is the frame's cards"
        );
        assert_eq!(diagnosed.get("version"), Some(&json!(1_i32)));
        assert_eq!(
            diagnosed.pointer("/display_as/0/type"),
            Some(&json!("text"))
        );
        assert_eq!(
            diagnosed
                .pointer("/display_as/0/content")
                .and_then(Value::as_str)
                .and_then(|content| content.lines().next()),
            Some("uri file:///tmp/rap.gandr version 1 diagnostics 0 holes 0"),
            "the display is the lines `gandr view` prints"
        );

        let malformed = exchange(address, &Message {
            head: alloc::format!("POST /invoke HTTP/1.1\r\nhost: {address}\r\ncontent-length: 1"),
            body: Vec::from(*b"{"),
        });
        assert!(
            malformed.head.starts_with("HTTP/1.1 400 "),
            "{}",
            malformed.head
        );
        drop(editor);
    }

    #[test]
    fn a_call_a_crash_lost_is_answered_with_an_error()
    {
        let scratch = Scratch::new(&json!("rap-lost"));
        let callback = loopback();
        let callback_url = alloc::format!(
            "http://{}/results",
            callback.local_addr().expect("the callback listens")
        );
        let row = |id: &Value| {
            json!({ "opened": { "group_id": "thread-1", "id": id, "callback_url": callback_url,
                "token": "abc", "operation": "documents", "started": 0_u64 } })
        };
        let written = [
            row(&json!("lost")),
            row(&json!("kept")),
            json!({ "answered": { "group_id": "thread-1", "id": "kept", "text": "{\"documents\":[]}" } }),
            row(&json!("answered")),
            json!({ "settled": ["thread-1", "answered"] }),
        ];
        let calls = calls(&scratch);
        std::fs::create_dir_all(calls.parent().expect("the file has a directory"))
            .expect("the directory is made");
        std::fs::write(
            &calls,
            written
                .iter()
                .map(|line| alloc::format!("{line}\n"))
                .chain([String::from("{\"opened\":{\"group")])
                .collect::<String>(),
        )
        .expect("the store is written");
        let toolset = Toolset::open(loopback(), &calls, &table(&scratch), Policy::default())
            .expect("the store and the table open");
        hub(&scratch, toolset);
        let mut delivered = Vec::new();
        for _row in 0_i32 .. 2_i32 {
            let message = received(&callback);
            assert_eq!(
                message.carries(&json!("authorization: Bearer abc")),
                Answer(true)
            );
            let message = message.json();
            delivered.push((message.get("id").cloned(), message.get("text").cloned()));
        }
        delivered.sort_by_key(|&(ref id, _)| id.as_ref().and_then(Value::as_str).map(String::from));
        assert_eq!(
            delivered,
            [
                (Some(json!("kept")), Some(json!("{\"documents\":[]}"))),
                (Some(json!("lost")), Some(json!(LOST)))
            ],
            "a kept answer is delivered again, a row with no answer is answered with an error, \
             and a settled row is not answered"
        );
        let deadline = std::time::Instant::now()
            .checked_add(Duration::from_secs(10))
            .expect("the deadline is representable");
        while std::fs::metadata(&calls).is_ok_and(|file| file.len() != 0)
            && std::time::Instant::now() < deadline
        {
            thread::sleep(Duration::from_millis(10));
        }
        assert_eq!(
            std::fs::metadata(&calls).map(|file| file.len()).ok(),
            Some(0_u64),
            "the store is empty once no call is pending"
        );
    }

    #[test]
    fn a_stalled_client_holds_no_other_call()
    {
        let scratch = Scratch::new(&json!("rap-stalled"));
        let toolset = opened(&scratch);
        let address = toolset.address().expect("the toolset listens");
        hub(&scratch, toolset);
        let mut stalled = TcpStream::connect(address).expect("the toolset accepts");
        stalled
            .write_all(b"POST /invoke HTTP/1.1\r\n")
            .expect("the toolset reads a part of the head");
        let started = std::time::Instant::now();
        let manifest = exchange(address, &Message {
            head: alloc::format!("GET /.well-known/rap-toolset HTTP/1.1\r\nhost: {address}"),
            body: Vec::new(),
        });
        assert!(
            manifest.head.starts_with("HTTP/1.1 200 "),
            "{}",
            manifest.head
        );
        assert!(
            started.elapsed() < REQUEST_WAIT,
            "another acceptor answers while the stalled client holds its own"
        );
        drop(stalled);
    }

    /// Subscribe the runtime at `callback` through the toolset at `address`
    /// with `invocation`, which names the operation, its arguments, the `id`
    /// and the `group_id`, with the bearer `abc`. Read the result that
    /// confirms the subscription, and give its text.
    ///
    /// # Specification
    /// trivial.
    fn subscribed(
        address: SocketAddr,
        callback: &TcpListener,
        invocation: &Value,
    ) -> Value
    {
        let mut invocation = invocation.clone();
        if let Some(fields) = invocation.as_object_mut() {
            drop(fields.insert(
                String::from("callback_url"),
                json!(alloc::format!(
                    "http://{}/events",
                    callback.local_addr().expect("the callback listens")
                )),
            ));
        }
        let acknowledged = invoke(address, &invocation, Some(&json!("abc")));
        assert!(
            acknowledged.head.starts_with("HTTP/1.1 200 "),
            "{}",
            acknowledged.head
        );
        let confirmed = received(callback).json();
        assert_eq!(
            (
                confirmed.get("type"),
                confirmed.get("id"),
                confirmed.get("subscription")
            ),
            (
                Some(&json!("tool_result")),
                invocation.get("id"),
                Some(&json!(true))
            ),
            "the result confirms the subscription: {confirmed}"
        );
        framed(&confirmed)
    }

    /// A `POST` of `body` to the path `path` at `address`.
    ///
    /// # Specification
    /// trivial.
    fn posted(
        address: SocketAddr,
        path: &Value,
        body: &Value,
    ) -> Message
    {
        let body = body.to_string().into_bytes();
        let head = alloc::format!(
            "POST {} HTTP/1.1\r\nhost: {address}\r\ncontent-type: application/json\r\ncontent-length: {}",
            path.as_str().unwrap_or_default(),
            body.len()
        );
        exchange(address, &Message { head, body })
    }

    #[test]
    fn a_subscription_hears_each_new_frame()
    {
        let scratch = Scratch::new(&json!("rap-subscribed"));
        let callback = loopback();
        let uri = json!("file:///tmp/subscribed.gandr");
        let toolset = opened(&scratch);
        let address = toolset.address().expect("the toolset listens");
        hub(&scratch, toolset);
        assert_eq!(
            subscribed(
                address,
                &callback,
                &json!({ "operation": "subscribe_diagnostics", "arguments": { "uri": uri },
                    "id": "watch-1", "group_id": "thread-1" })
            ),
            json!({ "subscription": "watch-1", "scope": { "diagnostics": uri } }),
            "the result names the subscription and its scope, before the document opens"
        );
        let mut editor = Editor::new(&scratch);
        let mut other = json!("file:///tmp/other.gandr");
        for (version, text, count) in [
            (1_i32, "def f = 42 ;\n", 0_usize),
            (2_i32, "def f = missing ;\n", 1_usize),
            (3_i32, "def f = 42 ;\n", 0_usize),
        ] {
            editor.edit(&uri, &json!(version), &json!(text));
            let event = received(&callback);
            assert!(
                event.head.starts_with("POST /events HTTP/1.1"),
                "{}",
                event.head
            );
            assert_eq!(
                (
                    event.carries(&json!(alloc::format!("idempotency-key: watch-1@{version}"))),
                    event.carries(&json!("authorization: Bearer abc"))
                ),
                (Answer(true), Answer(true)),
                "an event is keyed by its frame's version and carries the bearer back"
            );
            let event = event.json();
            assert_eq!(
                (
                    event.get("type"),
                    event.get("group_id"),
                    event.get("tool_call_id"),
                    event.get("version")
                ),
                (
                    Some(&json!("subscription_event")),
                    Some(&json!("thread-1")),
                    Some(&json!("watch-1")),
                    Some(&json!(version))
                )
            );
            let frame = framed(&event);
            assert_eq!(
                (
                    frame.get("uri"),
                    frame.get("version"),
                    frame
                        .get("diagnostics")
                        .and_then(Value::as_array)
                        .map(Vec::len)
                ),
                (Some(&uri), Some(&json!(version)), Some(count)),
                "each event holds the whole frame at its version"
            );
            // A document that no subscription follows sends nothing.
            editor.edit(&other, &json!(1_i32), &json!("def g = 1 ;\n"));
            other = json!(alloc::format!("file:///tmp/other-{version}.gandr"));
        }
        assert_eq!(
            quiet(&callback, Duration::from_millis(300)),
            Answer(true),
            "no other event follows"
        );
        drop(editor);
    }

    #[test]
    fn an_account_subscription_outlives_a_restart_of_the_hub()
    {
        let earlier = Scratch::new(&json!("rap-account-earlier"));
        let later = Scratch::new(&json!("rap-account-later"));
        let callback = loopback();
        let uri = json!("file:///tmp/account.gandr");
        let declared = json!("def one : Integer ;\ndef one = 1 ;\n");
        let toolset = opened(&earlier);
        let address = toolset.address().expect("the toolset listens");
        hub(&earlier, toolset);
        assert_eq!(
            subscribed(
                address,
                &callback,
                &json!({ "operation": "subscribe_account",
                    "arguments": { "uri": uri, "declaration": "one" },
                    "id": "watch-1", "group_id": "thread-1" })
            ),
            json!({ "subscription": "watch-1",
                "scope": { "account": { "document": uri, "declaration": "one" } } }),
            "the result names the subscription and its scope"
        );
        let mut editor = Editor::new(&earlier);
        editor.edit(&uri, &json!(1_i32), &declared);
        let first = received(&callback);
        assert_eq!(
            first.carries(&json!("idempotency-key: watch-1@1")),
            Answer(true),
            "an event is keyed by its version"
        );
        let first = first.json();
        let card = framed(&first);
        assert_eq!(
            (
                first.get("version"),
                card.get("uri"),
                card.get("declaration"),
                card.pointer("/card/name")
            ),
            (
                Some(&json!(1_i32)),
                Some(&uri),
                Some(&json!("one")),
                Some(&json!("one"))
            ),
            "the event holds the card of the declaration, and its version beside it"
        );
        assert_eq!(
            awaited(&table(&earlier), &json!([["watch-1", 1_i32]])),
            json!([["watch-1", 1_i32]]),
            "the table keeps the version that the runtime took"
        );
        drop(editor);

        // A later hub opens the table that the earlier hub wrote, and a fresh
        // subscription beside the resumed row shows when a state settles.
        let toolset = Toolset::open(
            loopback(),
            &calls(&later),
            &table(&earlier),
            Policy::default(),
        )
        .expect("the store and the table open");
        let address = toolset.address().expect("the toolset listens");
        hub(&later, toolset);
        drop(subscribed(
            address,
            &callback,
            &json!({ "operation": "subscribe_account",
                "arguments": { "uri": uri, "declaration": "one" },
                "id": "watch-2", "group_id": "thread-2" }),
        ));
        let mut editor = Editor::new(&later);
        let heard = |version: i32| {
            let event = received(&callback).json();
            assert_eq!(event.get("version"), Some(&json!(version)), "{event}");
            json!([
                event.get("tool_call_id"),
                framed(&event).pointer("/card/name")
            ])
        };
        editor.edit(&uri, &json!(1_i32), &declared);
        assert_eq!(
            heard(1_i32),
            json!(["watch-2", "one"]),
            "the fresh subscription hears the state of the version that the resumed row took"
        );
        assert_eq!(
            quiet(&callback, Duration::from_millis(300)),
            Answer(true),
            "the resumed row hears no state of the version that its runtime took"
        );
        editor.edit(
            &uri,
            &json!(2_i32),
            &json!("def one : Integer ;\ndef one = 1 ;\n// a note\n"),
        );
        assert_eq!(
            quiet(&callback, Duration::from_millis(500)),
            Answer(true),
            "an edit that leaves the card the same sends nothing"
        );
        editor.edit(
            &uri,
            &json!(3_i32),
            &json!("def one : Integer ;\ndef one = 2 ;\n"),
        );
        let mut changed = [heard(3_i32), heard(3_i32)];
        changed.sort_by_key(ToString::to_string);
        assert_eq!(
            changed,
            [json!(["watch-1", "one"]), json!(["watch-2", "one"])],
            "an edit that changes the card reaches the resumed row and the fresh one"
        );
        assert_eq!(
            awaited(
                &table(&earlier),
                &json!([["watch-1", 3_i32], ["watch-2", 3_i32]])
            ),
            json!([["watch-1", 3_i32], ["watch-2", 3_i32]]),
            "the later hub keeps both rows at the version that the runtime took"
        );
        drop(editor);
    }

    #[test]
    fn a_cancel_and_a_closed_thread_drop_their_rows()
    {
        let scratch = Scratch::new(&json!("rap-ended"));
        let callback = loopback();
        let uri = json!("file:///tmp/ended.gandr");
        let toolset = opened(&scratch);
        let address = toolset.address().expect("the toolset listens");
        hub(&scratch, toolset);
        for (id, group_id) in [
            ("watch-1", "thread-1"),
            ("watch-2", "thread-1"),
            ("watch-3", "thread-2"),
        ] {
            drop(subscribed(
                address,
                &callback,
                &json!({ "operation": "subscribe_diagnostics", "arguments": { "uri": uri },
                    "id": id, "group_id": group_id }),
            ));
        }
        let opened = json!([["watch-1", null], ["watch-2", null], ["watch-3", null]]);
        assert_eq!(
            awaited(&table(&scratch), &opened),
            opened,
            "each subscription is a row of the table"
        );
        for (path, body) in [
            ("/cancel_tool_call", json!({ "tool_call_id": "watch-1" })),
            (
                "/cancel_tool_call",
                json!({ "tool_call_id": "watch-2", "group_id": "thread-2" }),
            ),
            ("/cancel_tool_call", json!({ "tool_call_id": "watch-9" })),
        ] {
            let ended = posted(address, &json!(path), &body);
            assert!(
                ended.head.starts_with("HTTP/1.1 200 "),
                "a cancel is answered `200` whatever it names: {}",
                ended.head
            );
        }
        let cancelled = json!([["watch-2", null], ["watch-3", null]]);
        assert_eq!(
            awaited(&table(&scratch), &cancelled),
            cancelled,
            "a cancel drops its row alone, and one that names another thread drops none"
        );
        let mut editor = Editor::new(&scratch);
        editor.edit(&uri, &json!(1_i32), &json!("def f = 42 ;\n"));
        let mut heard = [received(&callback), received(&callback)].map(|event| {
            event
                .json()
                .get("tool_call_id")
                .and_then(Value::as_str)
                .map(String::from)
        });
        heard.sort();
        assert_eq!(
            heard,
            [Some(String::from("watch-2")), Some(String::from("watch-3"))],
            "the cancelled row hears nothing"
        );
        assert_eq!(
            quiet(&callback, Duration::from_millis(300)),
            Answer(true),
            "no other event follows"
        );
        for thread in ["thread-1", "thread-2"] {
            let closed = posted(
                address,
                &json!("/close_thread"),
                &json!({ "thread_id": thread }),
            );
            assert!(closed.head.starts_with("HTTP/1.1 200 "), "{}", closed.head);
        }
        assert_eq!(
            (
                awaited(&table(&scratch), &json!([])),
                Answer(table(&scratch).exists())
            ),
            (json!([]), Answer(false)),
            "a closed thread drops each of its rows, and a table with no row has no file"
        );
        editor.edit(&uri, &json!(2_i32), &json!("def f = missing ;\n"));
        assert_eq!(
            quiet(&callback, Duration::from_millis(500)),
            Answer(true),
            "a closed thread hears nothing"
        );
        drop(editor);
    }

    #[test]
    fn an_activity_subscription_hears_each_task_until_it_ends_6509()
    {
        let earlier = Scratch::new(&json!("rap-activity-earlier"));
        let later = Scratch::new(&json!("rap-activity-later"));
        let callback = loopback();
        let uri = json!("file:///tmp/active.gandr");
        let toolset = opened(&earlier);
        let address = toolset.address().expect("the toolset listens");
        hub(&earlier, toolset);
        assert_eq!(
            subscribed(
                address,
                &callback,
                &json!({ "operation": "subscribe_activity", "arguments": {},
                    "id": "work-1", "group_id": "thread-1" })
            ),
            json!({ "subscription": "work-1", "scope": "activity" }),
            "the result names the subscription and its scope"
        );
        let mut editor = Editor::new(&earlier);
        editor.edit(&uri, &json!(1_i32), &json!("def f = 42 ;\n"));
        let first = admitted(&callback);
        assert_eq!(
            quiet(&callback, Duration::from_millis(300)),
            Answer(true),
            "the row hears nothing more than the tasks of the edit"
        );
        drop(editor);

        // A later hub resumes the row from the table that the earlier hub
        // wrote, and a later edit marks its tasks under the later run.
        let toolset = Toolset::open(
            loopback(),
            &calls(&later),
            &table(&earlier),
            Policy::default(),
        )
        .expect("the store and the table open");
        let address = toolset.address().expect("the toolset listens");
        hub(&later, toolset);
        // The hub starts the toolset on a thread of its own, so an edit can
        // run its tasks before the toolset watches the activity for the
        // resumed row. The row then never hears them. The toolset answers a
        // request only after it watches, so the edit waits for one answer.
        let manifest = exchange(address, &Message {
            head: alloc::format!("GET /.well-known/rap-toolset HTTP/1.1\r\nhost: {address}"),
            body: Vec::new(),
        });
        assert!(
            manifest.head.starts_with("HTTP/1.1 200 "),
            "{}",
            manifest.head
        );
        let mut editor = Editor::new(&later);
        editor.edit(&uri, &json!(1_i32), &json!("def f = 42 ;\n"));
        let second = admitted(&callback);
        assert_ne!(
            first, second,
            "a later hub keys its states by a run of its own, so it repeats no key"
        );
        let ended = posted(
            address,
            &json!("/cancel_tool_call"),
            &json!({ "tool_call_id": "work-1" }),
        );
        assert!(ended.head.starts_with("HTTP/1.1 200 "), "{}", ended.head);
        assert_eq!(
            awaited(&table(&earlier), &json!([])),
            json!([]),
            "a cancel drops the row"
        );
        editor.edit(&uri, &json!(2_i32), &json!("def f = 43 ;\n"));
        assert_eq!(
            quiet(&callback, Duration::from_millis(500)),
            Answer(true),
            "a cancelled row hears nothing"
        );
        drop(editor);
    }

    #[test]
    fn a_server_error_is_retried_and_a_refusal_is_not()
    {
        let scratch = Scratch::new(&json!("rap-retried"));
        let callback = loopback();
        let uri = json!("file:///tmp/retried.gandr");
        let toolset = opened(&scratch);
        let address = toolset.address().expect("the toolset listens");
        hub(&scratch, toolset);
        drop(subscribed(
            address,
            &callback,
            &json!({ "operation": "subscribe_diagnostics", "arguments": { "uri": uri },
                "id": "watch-1", "group_id": "thread-1" }),
        ));
        let mut editor = Editor::new(&scratch);
        editor.edit(&uri, &json!(1_i32), &json!("def f = 42 ;\n"));
        // The toolset starts its wait when it reads the 503, after `answered`
        // takes its instant, so the measured wait holds the whole policy wait
        // however late this thread runs after the write.
        let (failed, written) = answered(&callback, &json!("503 Service Unavailable"));
        let retried = received(&callback);
        let waited = written.elapsed();
        assert!(
            waited >= Policy::default().first && waited < Duration::from_secs(5),
            "the retry follows the first wait of the policy, not {waited:?}"
        );
        assert_eq!(
            (
                failed.json(),
                retried.carries(&json!("idempotency-key: watch-1@1"))
            ),
            (retried.json(), Answer(true)),
            "the retry is the same frame under the same key"
        );
        editor.edit(&uri, &json!(2_i32), &json!("def f = missing ;\n"));
        let refused = heard(&callback, &json!("404 Not Found"));
        assert_eq!(refused.json().get("version"), Some(&json!(2_i32)));
        editor.edit(&uri, &json!(3_i32), &json!("def f = 42 ;\n"));
        assert_eq!(
            quiet(&callback, Duration::from_secs(1)),
            Answer(true),
            "a listener that refused an event hears nothing more"
        );
        drop(editor);
    }

    #[test]
    fn an_announcement_names_the_manifest_and_refuses_a_second_hub()
    {
        let scratch = Scratch::new(&json!("rap-announced"));
        let toolset = opened(&scratch);
        let address = toolset.address().expect("the toolset listens");
        hub(&scratch, toolset);
        let socket = scratch.socket();
        let file = socket.with_extension("rap");
        assert_eq!(
            Announcement::beside(&socket)
                .vacant()
                .map_err(|error| error.kind()),
            Ok(()),
            "no file names a toolset yet"
        );
        let announced = Announcement::beside(&socket)
            .write(address)
            .expect("the file is written");
        let url = std::fs::read_to_string(&file).expect("the file reads");
        let (at, path) = url
            .trim_end()
            .strip_prefix("http://")
            .and_then(|rest| rest.split_once('/'))
            .expect("the file holds a URL");
        let manifest = exchange(at.parse().expect("the URL names an address"), &Message {
            head: alloc::format!("GET /{path} HTTP/1.1\r\nhost: {at}"),
            body: Vec::new(),
        })
        .json();
        assert_eq!(
            entries(manifest.get("tools")).len(),
            tools::offered().len(),
            "a client fetches the manifest at the URL that the file names"
        );
        let refused = Announcement::beside(&socket)
            .vacant()
            .expect_err("a second hub refuses while the first listens");
        assert_eq!(
            (
                refused.kind(),
                refused.to_string().contains(&*file.to_string_lossy())
            ),
            (std::io::ErrorKind::AddrInUse, true),
            "the refusal names the file: {refused}"
        );
        drop(announced);
        assert!(!file.exists(), "the file goes when the hub lets it go");
        let gone = loopback();
        let stale = Announcement::beside(&socket)
            .write(gone.local_addr().expect("the loopback has an address"))
            .expect("the file is written");
        drop(gone);
        assert_eq!(
            Announcement::beside(&socket)
                .vacant()
                .map_err(|error| error.kind()),
            Ok(()),
            "a file whose listener has gone is vacant"
        );
        drop(stale);
    }

    /// Verbs that print each path, and then the verdict line. A path that
    /// ends in `wait` prints a tick each 10 ms until its job is retired, for
    /// ten seconds at most.
    struct Echoing;

    impl Verbs for Echoing
    {
        /// Print each path of `paths`, and then the verdict line.
        ///
        /// # Specification
        /// trivial.
        fn walk(
            &self,
            _verb: Verb,
            paths: Vec<PathBuf>,
            _pool: &Pool,
            (printed, _faulted): (&mut dyn std::io::Write, &mut dyn std::io::Write),
        ) -> std::io::Result<()>
        {
            for path in &paths {
                writeln!(printed, "{}", path.display())?;
                if path.ends_with("wait") {
                    for _tick in 0_u32 .. 1000_u32 {
                        writeln!(printed, "tick")?;
                        thread::sleep(Duration::from_millis(10));
                    }
                }
            }
            writeln!(printed, "verdict: settled")
        }
    }

    /// The next result that `callback` takes, read whole and answered `200`,
    /// and the view updates that come before it.
    ///
    /// # Specification
    /// trivial.
    fn resulted(callback: &TcpListener) -> (Value, Vec<Value>)
    {
        let mut views = Vec::new();
        loop {
            let message = received(callback).json();
            if message.get("type") == Some(&json!("tool_result")) {
                return (message, views);
            }
            views.push(message);
        }
    }

    /// The `id`, the text and the display of `result`.
    ///
    /// # Specification
    /// trivial.
    fn told(result: &Value) -> Value
    {
        json!([
            result.get("id"),
            result.get("text"),
            result.pointer("/display_as/0/content")
        ])
    }

    #[test]
    fn a_long_operation_answers_when_its_job_ends()
    {
        let scratch = Scratch::new(&json!("rap-jobs"));
        let callback = loopback();
        let uri = json!("file:///tmp/jobs.gandr");
        let toolset = opened(&scratch).walking(Arc::new(Echoing));
        let address = toolset.address().expect("the toolset listens");
        hub_over(&scratch, toolset, parallel());
        let mut editor = Editor::new(&scratch);
        editor.edit(&uri, &json!(1_i32), &json!("def f = 42 ;\n"));
        let callback_url = json!(alloc::format!(
            "http://{}/results/jobs",
            callback.local_addr().expect("the callback listens")
        ));
        let call = |operation: &str, arguments: Value, id: &str| {
            let started = std::time::Instant::now();
            let acknowledged = invoke(
                address,
                &json!({ "operation": operation, "arguments": arguments, "id": id,
                    "callback_url": callback_url, "group_id": "thread-1" }),
                None,
            );
            let acknowledgement = started.elapsed();
            assert!(
                acknowledged.head.starts_with("HTTP/1.1 200 "),
                "{}",
                acknowledged.head
            );
            assert!(
                acknowledgement < Duration::from_millis(100),
                "a long operation is acknowledged at once: {acknowledgement:?}"
            );
            told(&resulted(&callback).0)
        };

        assert_eq!(
            call(
                "check",
                json!({ "paths": ["/tmp/a.gandr", "/tmp/b.gandr"] }),
                "check-1"
            ),
            json!([
                "check-1",
                "verdict: settled",
                "/tmp/a.gandr\n/tmp/b.gandr\nverdict: settled\n"
            ]),
            "the text is the verdict line, and the display is each line that the verb prints"
        );
        assert_eq!(
            call("test", json!({ "paths": [] }), "test-1"),
            json!(["test-1", "Error: `paths` must name one path or more", null]),
            "a walk of no path is refused"
        );
        assert_eq!(
            call("replay", json!({ "uri": uri }), "replay-1"),
            json!([
                "replay-1",
                "replay of version 1: 1 replayed, 0 refused, 0 withheld, 0 checked",
                "f: kernel replayed\n"
            ]),
            "a replay counts the declarations of the revision by the kernel's warrant"
        );
        assert_eq!(
            call(
                "replay",
                json!({ "uri": "file:///tmp/unheld.gandr" }),
                "replay-2"
            ),
            json!([
                "replay-2",
                "Error: the hub does not hold file:///tmp/unheld.gandr",
                null
            ]),
            "a replay of a document that the hub does not hold is refused"
        );
        assert_eq!(
            call("run", json!({ "uri": uri, "entry": "f" }), "run-1"),
            json!(["run-1", "42", "42"]),
            "a run answers the line that the run lens shows"
        );
        assert_eq!(
            call("run", json!({ "uri": uri, "entry": "g" }), "run-2"),
            json!([
                "run-2",
                "Error: no declaration of file:///tmp/jobs.gandr is named `g`",
                null
            ]),
            "a run of a name that no declaration has is refused"
        );
        drop(editor);
    }

    #[test]
    fn a_newer_revision_retires_a_check_or_a_run_and_a_cancel_ends_a_job()
    {
        let scratch = Scratch::new(&json!("rap-retired"));
        let callback = loopback();
        let uri = json!("file:///tmp/wait/held.gandr");
        let toolset = opened(&scratch).walking(Arc::new(Echoing));
        let address = toolset.address().expect("the toolset listens");
        hub_over(&scratch, toolset, parallel());
        let mut editor = Editor::new(&scratch);
        editor.edit(&uri, &json!(1_i32), &json!("def f = 42 ;\n"));
        let callback_url = json!(alloc::format!(
            "http://{}/results/retired",
            callback.local_addr().expect("the callback listens")
        ));
        let start = |id: &str, group_id: &str| {
            let acknowledged = invoke(
                address,
                &json!({ "operation": "check", "arguments": { "paths": ["/tmp/wait"] }, "id": id,
                    "callback_url": callback_url, "group_id": group_id }),
                None,
            );
            assert!(
                acknowledged.head.starts_with("HTTP/1.1 200 "),
                "{}",
                acknowledged.head
            );
        };

        start("check-1", "thread-1");
        // The check prints ticks for ten seconds unless a newer revision
        // retires it; the wait lets it start first.
        thread::sleep(Duration::from_millis(200));
        editor.edit(&uri, &json!(2_i32), &json!("def f = 43 ;\n"));
        assert_eq!(
            told(&resulted(&callback).0),
            json!([
                "check-1",
                "retired: file:///tmp/wait/held.gandr is at version 2",
                null
            ]),
            "the retired call names the document and its version"
        );

        editor.edit(
            &uri,
            &json!(3_i32),
            &json!(
                "def spin() -> [Partial] Integer =\n  var n = 30000000\n  while n > 0 { access n as v { resume v (v - 1) } };\n  pure n\n"
            ),
        );
        let acknowledged = invoke(
            address,
            &json!({ "operation": "run", "arguments": { "uri": uri, "entry": "spin" }, "id": "run-1",
                "callback_url": callback_url, "group_id": "thread-1" }),
            None,
        );
        assert!(
            acknowledged.head.starts_with("HTTP/1.1 200 "),
            "{}",
            acknowledged.head
        );
        // The run spends its budget unless a newer revision retires it; the
        // wait lets it start first, and the edit waits for no part of it.
        thread::sleep(Duration::from_millis(200));
        editor.edit(&uri, &json!(4_i32), &json!("def f = 44 ;\n"));
        assert_eq!(
            told(&resulted(&callback).0),
            json!([
                "run-1",
                "retired: file:///tmp/wait/held.gandr is at version 4",
                null
            ]),
            "a newer revision retires a run as it retires a check"
        );

        start("check-2", "thread-1");
        start("check-3", "thread-2");
        for (path, body) in [
            ("/cancel_tool_call", json!({ "tool_call_id": "check-2" })),
            ("/close_thread", json!({ "thread_id": "thread-2" })),
        ] {
            let ended = posted(address, &json!(path), &body);
            assert!(ended.head.starts_with("HTTP/1.1 200 "), "{}", ended.head);
        }
        let mut ended = [resulted(&callback).0, resulted(&callback).0].map(|result| told(&result));
        ended.sort_by_key(ToString::to_string);
        assert_eq!(
            ended,
            [
                json!(["check-2", "cancelled", null]),
                json!(["check-3", "cancelled", null])
            ],
            "a cancel and a closed thread each end their job"
        );
        assert_eq!(
            quiet(&callback, Duration::from_millis(300)),
            Answer(true),
            "an ended job delivers no result of its own"
        );
        drop(editor);
    }
}
