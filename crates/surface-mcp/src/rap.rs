//! The hub's Reactive Agent Protocol face: the toolset that an agent runtime
//! discovers over HTTP, the invoke endpoint that acknowledges each call, and
//! the callback that answers the call later.
//!
//! `gandr serve --port <port>` gives the hub a [`Toolset`] beside its socket.
//! The toolset listens on the loopback interface. A `GET` of
//! `/.well-known/rap-toolset` returns the manifest: the name `gandr`, the
//! invoke endpoint, and each tool of the Model Context Protocol face, with its
//! name, description and input schema. A `POST` to `/invoke` carries an
//! invocation. The toolset appends a row for the call to its store, answers
//! `200` with no body, and queues the call. An invocation that is not JSON,
//! that has no field RAP requires, or whose callback URL is not `http`, gets
//! `400`, because no result can reach its caller.
//!
//! One worker runs each queued call over the workspace that the editors share,
//! as `tools/call` runs it. The worker posts a `tool_result` to the callback
//! URL, then appends the settlement of the row. The text of the result is the
//! answer of the tool as JSON. A refusal, an unknown operation and arguments
//! that the tool cannot read give a text that starts with `Error: `.
//!
//! # Boundaries
//!
//! A caller that wants a bearer sends its own token on the invocation, as
//! `Authorization: Bearer <token>`. The row keeps the token, and the callback
//! for that row sends it back in the same header. The hub mints no token. A
//! caller matches a result to its pending call by `group_id` and `id`, as RAP
//! states.
//!
//! The store is one file of JSON lines per workspace, and only its owner can
//! read it. The toolset writes the row of a call before it sends the `200`, so
//! a crash of the hub loses no call that it acknowledged. When the toolset
//! opens its store, each row that no settlement follows is a call that a crash
//! lost. The worker answers each such call with an error and settles it. The
//! toolset empties the file each time no call is pending.
//!
//! The toolset accepts connections on one thread for each hardware thread of
//! the host, and on two at least. A client that stalls holds its own thread for
//! one second at most, and the other threads answer the other calls.
//!
//! The worker tries each delivery once. A delivery that fails is told on the
//! log of the hub, and its row is settled.
//!
//! # Dependencies
//!
//! `httparse` reads the head of each request and of each callback's answer in
//! place. The rest of HTTP/1.1 that the toolset speaks, one request for each
//! connection, is written here.
//!
//! # References
//!
//! - The Hydro project. "Reactive Agent Protocol specification." 2026. <https://reactiveagentprotocol.dev/docs/rap/spec/overview>
//!   — the manifest, the invocation, the acknowledgement, the callback and its
//!   `Error: ` text.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt::Write as _;
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
use std::net::ToSocketAddrs as _;
use std::os::unix::fs::DirBuilderExt as _;
use std::os::unix::fs::OpenOptionsExt as _;
use std::path::Path;
use std::sync::Mutex;
use std::sync::mpsc::Receiver;
use std::sync::mpsc::Sender;
use std::sync::mpsc::channel;
use std::thread;
use std::time::SystemTime;

use gandr_surface_lsp::Workspace;
use serde::Deserialize;
use serde::Serialize;
use serde_json::Value;
use serde_json::json;

use crate::face::lock;
use crate::tools;

/// The path of the manifest under the base URL of the toolset, as RAP names
/// it.
const MANIFEST: &str = "/.well-known/rap-toolset";

/// The path of the invoke endpoint that the manifest names.
const INVOKE: &str = "/invoke";

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

/// How long the worker waits on a callback, to connect, to send and to hear
/// the status: five seconds. A runtime acknowledges a result at once, and one
/// that does not holds the next delivery no longer than this.
// economy: one worker posts the results in order, so a slow callback holds the
// next one. #6340 moves each delivery to a task of its own, with retries.
const CALLBACK_WAIT: Duration = Duration::from_secs(5);

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

/// The line of the store that records an answered call, by its `group_id` and
/// `id`.
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
    /// A call answered, by its `group_id` and `id`.
    Settled((String, String)),
}

/// The result of a call, as the callback receives it.
#[derive(Serialize)]
struct ToolResult<'call>
{
    /// Always `tool_result`.
    #[serde(rename = "type")]
    kind: &'static str,
    /// The conversation that the call belongs to.
    group_id: &'call String,
    /// The identifier of the call.
    id: &'call String,
    /// The identifier of the model's tool call, or null.
    call_id: Option<&'call String>,
    /// The answer of the tool, or the reason it gave none.
    text: &'call String,
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

    /// Record that the worker answered `pending`, and empty the file when no
    /// other row is open.
    ///
    /// # Specification
    /// trivial.
    fn settled(
        &mut self,
        pending: &Pending,
    ) -> io::Result<()>
    {
        self.open = self.open.saturating_sub(1);
        if self.open == 0 {
            return self.file.set_len(0);
        }
        self.append(&Settled {
            settled: (&pending.group_id, &pending.id),
        })
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

/// What a request asks for.
#[derive(Clone, Copy, Eq, PartialEq)]
enum Route
{
    /// The manifest.
    Manifest,
    /// A call.
    Invoke,
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
/// it acknowledged, and the calls that a crash lost.
pub struct Toolset
{
    /// The listener, bound on the loopback interface.
    listener: TcpListener,
    /// The store of rows.
    store: Store,
    /// The calls that a crash lost, answered first.
    lost: Vec<Pending>,
}

impl Toolset
{
    /// A toolset that answers on `listener` and keeps its rows in the file
    /// `calls`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the directory of `calls` exists, made readable by its owner
    ///   alone when this call made it, and `calls` is open to append, made
    ///   readable by its owner alone when this call made it. Each row of
    ///   `calls` that no settlement follows is kept, to be answered with an
    ///   error once the toolset serves.
    /// - provides: `gandr serve --port`'s face, opened before the hub runs, so
    ///   a store that cannot open stops the command.
    /// - fails: when the directory cannot be made, or the file opened or read.
    /// - panics: none.
    /// - executable: none — the effects are a directory and a file.
    ///
    /// # Errors
    /// The error making the directory, or opening or reading the file.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a store that holds an open row and a settled one
    ///   opens, and only the open row is answered, with an error, after which
    ///   the store is empty.
    /// - witness: `rap::tests::a_call_a_crash_lost_is_answered_with_an_error`
    #[inline]
    pub fn open(
        listener: TcpListener,
        calls: &Path,
    ) -> io::Result<Self>
    {
        if let Some(directory) = calls.parent() {
            DirBuilder::new()
                .recursive(true)
                .mode(0o700)
                .create(directory)?;
        }
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
        let mut open = BTreeMap::new();
        for line in written.split(|&byte| byte == b'\n') {
            // A line that does not parse is one that a crash cut short.
            match serde_json::from_slice::<Entry>(line) {
                Ok(Entry::Opened(pending)) => {
                    drop(open.insert((pending.group_id.clone(), pending.id.clone()), pending));
                },
                Ok(Entry::Settled(key)) => drop(open.remove(&key)),
                Err(_) => {},
            }
        }
        let lost: Vec<Pending> = open.into_values().collect();
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
        })
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

    /// Serve the toolset over `workspace`, telling `log` of each delivery that
    /// fails, until accepting fails on every acceptor.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a `GET` of `/.well-known/rap-toolset` is answered with the
    ///   manifest, which names the invoke endpoint at the listener's address
    ///   and every tool that `tools/list` lists, by its name, description and
    ///   input schema. A `POST` to `/invoke` whose body is an invocation with a
    ///   callback URL in `http` is answered `200` with no body once its row is
    ///   in the store, `503` when the row cannot be written. Another body is
    ///   answered `400`, a body past the limit `413`, and another path `404`.
    ///   Each acknowledged call, and each call that a crash lost, is answered
    ///   once, in the order queued, by a `tool_result` posted to its callback
    ///   URL with the caller's bearer when it sent one, and its row is then
    ///   settled. The text is the answer of the tool as JSON, or a text that
    ///   starts with `Error: `.
    /// - provides: `gandr serve --port`, the face beside the hub's socket.
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
    ///   `400`; a client that stalls holds no other call.
    /// - witness: `rap::tests::the_toolset_answers_a_call_by_its_callback`
    /// - witness: `rap::tests::a_call_a_crash_lost_is_answered_with_an_error`
    /// - witness: `rap::tests::a_stalled_client_holds_no_other_call`
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            pool_only_threads,
            reason = "io: the worker blocks on the workspace lock and on each callback's socket, and each acceptor on its client's socket, for the toolset's life"
        )
    )]
    #[inline]
    pub fn serve<Log>(
        self,
        workspace: &Mutex<Workspace>,
        log: Log,
    ) -> io::Result<()>
    where
        Log: Write + Send,
    {
        let Self {
            listener,
            store,
            lost,
        } = self;
        let tools = tools::list();
        let names: BTreeSet<String> = tools
            .iter()
            .filter_map(|tool| tool.get("name").and_then(Value::as_str))
            .map(String::from)
            .collect();
        let manifest = manifest(listener.local_addr()?, tools);
        let store = Mutex::new(store);
        let (queue, queued) = channel();
        for pending in lost {
            drop(queue.send(Call {
                pending,
                arguments: None,
            }));
        }
        // An acknowledgement takes the store's lock for one line alone, so
        // acceptors at the host's width answer in parallel. Two at least keep a
        // client that stalls from holding every other call.
        let width = thread::available_parallelism().map_or(2, |width| width.get().max(2));
        let (listener, manifest, store, names) = (&listener, &manifest, &store, &names);
        thread::scope(|scope| {
            drop(scope.spawn(move || work(queued, workspace, store, names, log)));
            // Every acceptor starts before the first join.
            let mut acceptors = Vec::with_capacity(width);
            for _acceptor in 0 .. width {
                let queue = queue.clone();
                acceptors.push(scope.spawn(move || accept(listener, manifest, store, &queue)));
            }
            // The worker ends once every acceptor has ended and it has answered
            // every queued call.
            drop(queue);
            acceptors
                .into_iter()
                .map(|acceptor| {
                    acceptor
                        .join()
                        .unwrap_or_else(|_panic| Err(io::Error::other("an acceptor panicked")))
                })
                .fold(Ok(()), Result::and)
        })
    }
}

/// The answer to a `GET` of the manifest, encoded once: the manifest of the
/// toolset at `address`, listing `tools`.
///
/// # Specification
/// trivial.
fn manifest(
    address: SocketAddr,
    tools: Vec<Value>,
) -> Buffer
{
    let tools: Vec<Value> = tools
        .into_iter()
        .map(|mut tool| {
            // RAP's tool has no title.
            if let Some(fields) = tool.as_object_mut() {
                drop(fields.remove("title"));
            }
            tool
        })
        .collect();
    let body = json!({
        "name": "gandr",
        "description": DESCRIPTION,
        "endpoint": alloc::format!("http://{address}{INVOKE}"),
        "tools": tools,
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

/// Accept each connection `listener` takes and answer its one request, until
/// accepting fails.
///
/// # Specification
/// trivial.
fn accept(
    listener: &TcpListener,
    manifest: &Buffer,
    store: &Mutex<Store>,
    queue: &Sender<Call>,
) -> io::Result<()>
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
        drop(answer(&mut stream, &mut buffer, manifest, store, queue));
    }
}

/// Read the one request on `stream` into `buffer`, and answer it.
///
/// # Specification
/// trivial.
fn answer(
    stream: &mut TcpStream,
    buffer: &mut Buffer,
    manifest: &Buffer,
    store: &Mutex<Store>,
    queue: &Sender<Call>,
) -> io::Result<()>
{
    stream.set_read_timeout(Some(REQUEST_WAIT))?;
    stream.set_nodelay(true)?;
    let request = read_request(stream, buffer)?;
    match request.route {
        Route::Manifest => stream.write_all(&manifest.0),
        Route::Unknown => stream.write_all(NOT_FOUND),
        Route::TooLarge => stream.write_all(TOO_LARGE),
        Route::Invoke => {
            let body = buffer.0.get(request.body).unwrap_or_default();
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
            if lock(store).opened(&pending).is_err() {
                return stream.write_all(UNSTORED);
            }
            let acknowledged = stream.write_all(ACKNOWLEDGED);
            // The row is written: the call is answered whether or not the
            // acknowledgement reached its caller.
            drop(queue.send(Call {
                pending,
                arguments: Some(arguments),
            }));
            acknowledged
        },
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

/// Answer each call `queued` holds over `workspace`, post its result, and
/// settle its row in `store`, telling `log` of each delivery that fails.
///
/// # Specification
/// trivial.
fn work<Log>(
    queued: Receiver<Call>,
    workspace: &Mutex<Workspace>,
    store: &Mutex<Store>,
    names: &BTreeSet<String>,
    mut log: Log,
) where
    Log: Write,
{
    let (mut text, mut result, mut exchange) =
        (String::new(), Buffer::default(), Buffer::default());
    for Call {
        mut pending,
        arguments,
    } in queued
    {
        text.clear();
        let written = match arguments {
            None => text.write_str(LOST),
            Some(_) if !names.contains(&pending.operation) => {
                write!(text, "Error: no tool is named `{}`", pending.operation)
            },
            Some(arguments) => {
                let name = Value::String(core::mem::take(&mut pending.operation));
                let called = tools::call(&mut lock(workspace), Some(&name), &arguments);
                match called {
                    Ok(answer) => write!(text, "{answer}"),
                    Err(refusal) => write!(text, "Error: {refusal}"),
                }
            },
        };
        result.0.clear();
        let delivered = written
            .map_err(io::Error::other)
            .and_then(|()| {
                serde_json::to_writer(&mut result.0, &ToolResult {
                    kind: "tool_result",
                    group_id: &pending.group_id,
                    id: &pending.id,
                    call_id: pending.call_id.as_ref(),
                    text: &text,
                })
                .map_err(io::Error::other)
            })
            .and_then(|()| deliver(&pending, &result, &mut exchange));
        if let Err(error) = delivered {
            drop(writeln!(
                log,
                "the toolset did not deliver the call {} of {}: {error}",
                pending.id, pending.group_id
            ));
        }
        let settled = lock(store).settled(&pending);
        if let Err(error) = settled {
            drop(writeln!(
                log,
                "the toolset did not settle the call {}: {error}",
                pending.id
            ));
        }
    }
}

/// Post `result`, an encoded `tool_result`, to the callback URL of `pending`,
/// with the caller's bearer when it sent one, and read the status, the request
/// and the answer written in `exchange`.
///
/// # Specification
/// trivial.
///
/// # Errors
/// The error resolving, connecting, writing or reading, or a status other than
/// `2xx`.
fn deliver(
    pending: &Pending,
    result: &Buffer,
    exchange: &mut Buffer,
) -> io::Result<()>
{
    let rest = pending
        .callback_url
        .strip_prefix("http://")
        .ok_or_else(|| io::Error::other("the callback URL is not an `http` URL"))?;
    let (authority, path) = rest
        .find('/')
        .map_or((rest, "/"), |slash| rest.split_at(slash));
    let mut addresses = if authority.ends_with(']') || !authority.contains(':') {
        (
            authority.trim_start_matches('[').trim_end_matches(']'),
            80_u16,
        )
            .to_socket_addrs()?
    }
    else {
        authority.to_socket_addrs()?
    };
    let address = addresses
        .next()
        .ok_or_else(|| io::Error::other("the callback URL names no address"))?;
    let mut stream = TcpStream::connect_timeout(&address, CALLBACK_WAIT)?;
    stream.set_read_timeout(Some(CALLBACK_WAIT))?;
    stream.set_write_timeout(Some(CALLBACK_WAIT))?;
    stream.set_nodelay(true)?;
    exchange.0.clear();
    write!(
        exchange.0,
        "POST {path} HTTP/1.1\r\nhost: {authority}\r\ncontent-type: application/json\r\ncontent-length: {}\r\n",
        result.0.len()
    )?;
    if let Some(ref token) = pending.token {
        write!(exchange.0, "authorization: Bearer {token}\r\n")?;
    }
    exchange.0.extend_from_slice(b"connection: close\r\n\r\n");
    exchange.0.extend_from_slice(&result.0);
    stream.write_all(&exchange.0)?;
    exchange.0.clear();
    let mut chunk = [0_u8; 1024];
    loop {
        let read = stream.read(&mut chunk)?;
        if read == 0 {
            return Err(io::ErrorKind::UnexpectedEof.into());
        }
        exchange
            .0
            .extend_from_slice(chunk.get(.. read).unwrap_or_default());
        let mut headers = [httparse::EMPTY_HEADER; HEADERS];
        let mut answer = httparse::Response::new(&mut headers);
        match answer.parse(&exchange.0).map_err(io::Error::other)? {
            httparse::Status::Complete(_head) => {
                return match answer.code {
                    Some(200 ..= 299) => Ok(()),
                    code => Err(io::Error::other(alloc::format!(
                        "the callback answered {}",
                        code.unwrap_or_default()
                    ))),
                };
            },
            httparse::Status::Partial if exchange.0.len() > HEAD_LIMIT => {
                return Err(io::ErrorKind::InvalidData.into());
            },
            httparse::Status::Partial => {},
        }
    }
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;
    use alloc::vec::Vec;
    use core::net::Ipv4Addr;
    use core::net::SocketAddr;
    use core::time::Duration;
    use std::io::Read as _;
    use std::io::Write as _;
    use std::net::TcpListener;
    use std::net::TcpStream;
    use std::path::PathBuf;
    use std::thread;

    use gandr_surface_lsp::Workspace;
    use gandr_surface_lsp::bind;
    use gandr_surface_lsp::run_hub;
    use quenchant_shape::shape::Maybe;
    use serde_json::Value;
    use serde_json::json;

    use super::Buffer;
    use super::LOST;
    use super::REQUEST_WAIT;
    use super::Toolset;
    use crate::face::tests::Editor;
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
                    move |workspace: alloc::sync::Arc<std::sync::Mutex<Workspace>>| {
                        toolset
                            .serve(&workspace, std::io::sink())
                            .expect("the toolset serves");
                    },
                )),
                Workspace::spelled(gandr_surface_lsp::Spelling::Unicode),
            )
            .expect("the hub serves");
        }));
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
        stream
            .write_all(b"HTTP/1.1 200 OK\r\ncontent-length: 0\r\n\r\n")
            .expect("the toolset reads the answer");
        message
    }

    #[test]
    fn the_toolset_answers_a_call_by_its_callback()
    {
        let scratch = Scratch::new(&json!("rap"));
        let toolset = Toolset::open(loopback(), &calls(&scratch)).expect("the store opens");
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
        let listed: Vec<Value> = tools::list()
            .into_iter()
            .map(|tool| {
                json!([
                    tool.get("name"),
                    tool.get("description"),
                    tool.get("inputSchema")
                ])
            })
            .collect();
        let offered: Vec<Value> = manifest
            .get("tools")
            .and_then(Value::as_array)
            .expect("the manifest lists tools")
            .iter()
            .map(|tool| {
                json!([
                    tool.get("name"),
                    tool.get("description"),
                    tool.get("inputSchema")
                ])
            })
            .collect();
        assert_eq!(
            offered, listed,
            "the manifest offers every tool of the line face"
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
        let toolset = Toolset::open(loopback(), &calls).expect("the store opens");
        hub(&scratch, toolset);
        let lost = received(&callback);
        assert_eq!(
            lost.carries(&json!("authorization: Bearer abc")),
            Answer(true)
        );
        let lost = lost.json();
        assert_eq!(
            (lost.get("id"), lost.get("text")),
            (Some(&json!("lost")), Some(&json!(LOST))),
            "only the row no settlement follows is answered, with an error"
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
        let toolset = Toolset::open(loopback(), &calls(&scratch)).expect("the store opens");
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
}
