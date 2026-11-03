//! A client's side of a served session, off unless the `client` feature is
//! on.
//!
//! The editor tests, the benchmark report and the parser's report drive
//! [`serve`] over framed streams through it. The server's built artifact
//! carries none of it.
//!
//! The session runs over two OS pipes. [`spawned`] runs `serve` on a thread
//! of its own and hands the caller the client. [`hosting`] runs `serve` on
//! the calling thread and the caller's workload on a thread of its own, so a
//! profiler attributes the server's work to the thread that runs it. Every
//! call answers a [`Fault`] rather than panicking, and a caller asserts or
//! propagates it.
//!
//! Three calls read the server. [`Client::request`] waits for one request's
//! answer. [`Client::exchange`] sends one message and then `gandr/sync`,
//! which the server answers after everything the message before it owed, and
//! answers every message written in between. [`Client::finish`] closes the
//! client's stream and reads what the server writes until it ends.

use core::fmt;
use std::io;
use std::io::BufReader;
use std::io::Read as _;
use std::io::Write as _;
use std::thread::JoinHandle;

use anodized::spec;
use quenchant_shape::shape::Maybe;
use serde_json::Value;
use serde_json::json;

use crate::server::Served;
use crate::server::Workspace;
use crate::server::serve;
use crate::transport::Body;
use crate::transport::TransportFault;
use crate::transport::read_frame;
use crate::transport::write_frame;

/// The name of a protocol method.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Method(pub &'static str);

/// The method of the request whose answer follows everything the message
/// before it owed.
const SYNC: Method = Method("gandr/sync");

/// Why a call stopped before the server answered it.
#[derive(Debug)]
pub enum Fault
{
    /// A pipe between the client and the server refused.
    Pipe(io::Error),
    /// The server's streams, or a frame the server wrote, faulted.
    Transport(TransportFault),
    /// A message did not encode, or the server wrote a body that is not JSON.
    Json(serde_json::Error),
    /// The server ended before it answered the request with this method.
    Ended(Method),
    /// A thread of the session panicked.
    Panicked,
}

impl From<io::Error> for Fault
{
    /// A pipe's refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(fault: io::Error) -> Self
    {
        Self::Pipe(fault)
    }
}

impl From<TransportFault> for Fault
{
    /// The transport's fault.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(fault: TransportFault) -> Self
    {
        Self::Transport(fault)
    }
}

impl From<serde_json::Error> for Fault
{
    /// A message's encoding or decoding fault.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(fault: serde_json::Error) -> Self
    {
        Self::Json(fault)
    }
}

impl fmt::Display for Fault
{
    /// Writes why the call stopped.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Pipe(ref fault) => write!(f, "a pipe to the server refused: {fault}"),
            Self::Transport(ref fault) => write!(f, "the session's transport faulted: {fault}"),
            Self::Json(ref fault) => write!(f, "a message is not JSON: {fault}"),
            Self::Ended(method) => write!(f, "the server ended before it answered `{}`", method.0),
            Self::Panicked => write!(f, "a thread of the session panicked"),
        }
    }
}

impl core::error::Error for Fault
{
}

/// A request's answer, and every message the server wrote before it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Answered
{
    /// The answer: the message carrying the request's id.
    pub answer: Value,
    /// The messages written before the answer, in order.
    pub before: Vec<Value>,
}

/// One client of a served session, over two pipes.
#[derive(Debug)]
pub struct Client
{
    /// Where the client's messages go.
    input: io::PipeWriter,
    /// What the server writes.
    output: BufReader<io::PipeReader>,
    /// The identifier of the client's latest request.
    asked: u64,
}

/// The thread `serve` runs on for a [`spawned`] session.
#[repr(transparent)]
#[derive(Debug)]
pub struct Serving(JoinHandle<Result<Served, TransportFault>>);

/// A session whose `serve` runs on a thread of its own over fresh pipes,
/// serving `workspace`, and its client.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the client's messages reach `serve` and its writes reach the
///   client; no message is sent yet.
/// - provides: a client the caller drives one call at a time, and the thread
///   whose ending [`Serving::ended`] reads.
/// - fails: [`Fault::Pipe`] when a pipe does not open.
/// - panics: none.
/// - executable: none — unwitnessable provenance: the pipes and the thread are
///   the operating system's, and nothing in the answer shows where they lead.
///
/// # Errors
/// [`Fault::Pipe`], as above.
///
/// # Adequacy
/// - hypothesis: L2 — every single-editor scenario connects here and holds each
///   answer to a fresh in-process connection's; a client whose messages missed
///   the loop, or read another session's writes, changes an answer at the
///   keystroke that caused it.
/// - witness: `tests::editor::scenarios::sweeps::typing_each_corpus_source_keeps_every_answer_faithful`
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        pool_only_threads,
        reason = "io: the loop's thread blocks on the client's frames for the session's life"
    )
)]
#[inline]
pub fn spawned(workspace: Workspace) -> Result<(Client, Serving), Fault>
{
    let (mut read, input) = io::pipe()?;
    let (output, mut written) = io::pipe()?;
    let serving = std::thread::spawn(move || {
        serve(
            &mut BufReader::new(&mut read),
            &mut written,
            &mut io::sink(),
            workspace,
        )
    });
    Ok((Client::over(input, output), Serving(serving)))
}

/// A session whose `serve` runs on this thread over fresh pipes, serving
/// `workspace`.
///
/// `workload` drives its client on a thread of its own. The call answers
/// what the workload answered and how the session ended.
///
/// # Specification
/// - requires: `workload` ends the session, as `shutdown` and `exit` or
///   [`Client::finish`] do; the client is dropped with the workload otherwise,
///   which ends it.
/// - ensures: `serve` read every message the workload sent.
/// - provides: a session whose server a profiler on this thread reads.
/// - fails: [`Fault::Pipe`] when a pipe does not open, the workload's fault,
///   [`Fault::Panicked`] when the workload panics, and `serve`'s own fault.
/// - panics: resumes nothing: a panic of the workload is answered as a fault.
/// - executable: none — unwitnessable provenance: the answer is the workload's
///   and the server's, which the call holds nothing to check against.
///
/// # Errors
/// The faults above.
///
/// # Adequacy
/// - hypothesis: L3 — the parser report's latency workload and the benchmark's
///   language-server workloads run here; a session that dropped a change or
///   ended before the workload did fails them.
/// - witness: `tests::session::a_hosted_workload_answers_what_it_read`
#[cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        pool_only_threads,
        reason = "io: the workload's thread blocks on the server's answers while this thread serves"
    )
)]
#[inline]
pub fn hosting<Answer, Workload>(
    workspace: Workspace,
    workload: Workload,
) -> Result<(Answer, Served), Fault>
where
    Answer: Send + 'static,
    Workload: FnOnce(Client) -> Result<Answer, Fault> + Send + 'static,
{
    let (mut read, input) = io::pipe()?;
    let (output, mut written) = io::pipe()?;
    let client = std::thread::spawn(move || workload(Client::over(input, output)));
    let served = serve(
        &mut BufReader::new(&mut read),
        &mut written,
        &mut io::sink(),
        workspace,
    );
    drop(written);
    let answer = client.join().map_err(|_panic| Fault::Panicked)?;
    let served = served?;
    Ok((answer?, served))
}

impl Client
{
    /// A client writing to `input` and reading `output`.
    ///
    /// # Specification
    /// trivial.
    fn over(
        input: io::PipeWriter,
        output: io::PipeReader,
    ) -> Self
    {
        Self {
            input,
            output: BufReader::new(output),
            asked: 0,
        }
    }

    /// Write `messages` to the server, each as one frame, in one write, so
    /// the server reads them together. Reads nothing.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the server reads `messages` in order, after every message
    ///   sent before.
    /// - fails: [`Fault::Json`] for a message that does not encode,
    ///   [`Fault::Pipe`] when the server's end is closed.
    /// - panics: none.
    /// - executable: none — unwitnessable provenance: the frames leave for the
    ///   server's thread, and the client keeps nothing to check them against.
    ///
    /// # Errors
    /// The faults above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every change the benchmark and the parser report send
    ///   goes through here; a frame lost or reordered changes the document the
    ///   next request reads.
    /// - witness: `tests::session::a_hosted_workload_answers_what_it_read`
    #[inline]
    pub fn send(
        &mut self,
        messages: &[Value],
    ) -> Result<(), Fault>
    {
        let mut frames = Vec::new();
        for message in messages {
            let body = Body::from(serde_json::to_vec(message)?);
            write_frame(&mut frames, &body)?;
        }
        self.input.write_all(&frames)?;
        Ok(())
    }

    /// Send the request `method` with `params`, and read the server's
    /// messages until its answer. The request's id is a string the client
    /// numbers, so it meets no numeric id a caller sends.
    ///
    /// # Specification
    /// - requires: no request this client sent is still unanswered, and no
    ///   message the caller sends carries an id of the client's form.
    /// - ensures: the answer carries the request's id, and `before` holds every
    ///   message written before it, in order.
    /// - fails: [`Client::send`]'s faults, [`Fault::Transport`] for a frame
    ///   that does not read, [`Fault::Json`] for a body that is not JSON, and
    ///   [`Fault::Ended`] when the server ends first.
    /// - panics: none.
    ///
    /// # Errors
    /// The faults above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the benchmark and the parser report settle each
    ///   change with a document request; an answer matched to the wrong id
    ///   returns before the judgement settles.
    /// - witness: `tests::session::a_hosted_workload_answers_what_it_read`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|answered|
        answered.answer.get("id") == Some(&self.id())))]
    pub fn request(
        &mut self,
        method: Method,
        params: &Value,
    ) -> Result<Answered, Fault>
    {
        self.asked = self.asked.saturating_add(1);
        let id = self.id();
        self.send(&[json!({"jsonrpc": "2.0", "id": id, "method": method.0, "params": params})])?;
        let mut before = Vec::new();
        loop {
            let message = self.read(method)?;
            if message.get("method").is_none() && message.get("id") == Some(&id) {
                return Ok(Answered {
                    answer: message,
                    before,
                });
            }
            before.push(message);
        }
    }

    /// The id of the client's latest request.
    ///
    /// # Specification
    /// trivial.
    fn id(&self) -> Value
    {
        Value::String(format!("gandr/client {}", self.asked))
    }

    /// Send `message`, then `gandr/sync`, and answer every message the server
    /// wrote before it answered the sync: everything `message` owed.
    ///
    /// # Specification
    /// - requires: no request this client sent is still unanswered.
    /// - ensures: every message the server wrote for `message`, its answers,
    ///   notifications and the admissions it left, in order, and nothing for
    ///   the sync.
    /// - fails: [`Client::request`]'s faults.
    /// - panics: none.
    /// - executable: none — unwitnessable provenance: the messages are the
    ///   server's writes on its own thread, and nothing in the answer alone
    ///   tells them from another session's.
    ///
    /// # Errors
    /// The faults above.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every single-editor keystroke passes here; a step
    ///   that answered before the server's writes ended, or read another
    ///   step's, leaves a publication stale or a request answered other than
    ///   once, and the session fails at that keystroke.
    /// - witness: `tests::editor::scenarios::sweeps::typing_each_corpus_source_keeps_every_answer_faithful`
    #[inline]
    pub fn exchange(
        &mut self,
        message: &Value,
    ) -> Result<Vec<Value>, Fault>
    {
        self.send(core::slice::from_ref(message))?;
        let synced = self.request(SYNC, &Value::Null)?;
        Ok(synced.before)
    }

    /// Close the client's stream, and answer every message the server writes
    /// until it ends.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the server read every message sent before, and saw its input
    ///   close.
    /// - fails: [`Fault::Pipe`] when the server's stream does not read,
    ///   [`Fault::Transport`] for a frame that does not read, and
    ///   [`Fault::Json`] for a body that is not JSON.
    /// - panics: none.
    /// - executable: none — unwitnessable provenance: the messages are the
    ///   server's last writes, and the client keeps nothing to check them
    ///   against.
    ///
    /// # Errors
    /// The faults above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the served scenarios end here after `exit`; a server
    ///   that wrote after `exit` fails them.
    /// - witness: `tests::editor::scenarios::fixing_a_mismatch_clears_its_diagnostic`
    #[inline]
    pub fn finish(self) -> Result<Vec<Value>, Fault>
    {
        let Self { input, output, .. } = self;
        drop(input);
        let mut rest = Vec::new();
        output.into_inner().read_to_end(&mut rest)?;
        let mut stream = rest.as_slice();
        let mut messages = Vec::new();
        while let Maybe::Present(body) = read_frame(&mut stream)? {
            messages.push(serde_json::from_slice(body.as_ref())?);
        }
        Ok(messages)
    }

    /// The next message the server writes, read while `method` waits for its
    /// answer.
    ///
    /// # Specification
    /// trivial.
    fn read(
        &mut self,
        method: Method,
    ) -> Result<Value, Fault>
    {
        let Maybe::Present(body) = read_frame(&mut self.output)?
        else {
            return Err(Fault::Ended(method));
        };
        Ok(serde_json::from_slice(body.as_ref())?)
    }
}

impl Serving
{
    /// How the session's `serve` ended, once its thread has.
    ///
    /// # Specification
    /// - requires: the session's input is closed or `exit` was sent, so the
    ///   thread ends.
    /// - ensures: the ending `serve` answered.
    /// - fails: [`Fault::Panicked`] when the thread panicked, and `serve`'s own
    ///   [`Fault::Transport`].
    /// - panics: none.
    /// - executable: none — unwitnessable provenance: the ending is the
    ///   thread's result, which nothing the caller holds checks.
    ///
    /// # Errors
    /// The faults above.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the served scenarios end with `exit` and read a clean
    ///   ending here; a loop that ended abruptly fails them.
    /// - witness: `tests::editor::scenarios::fixing_a_mismatch_clears_its_diagnostic`
    #[inline]
    pub fn ended(self) -> Result<Served, Fault>
    {
        let served = self.0.join().map_err(|_panic| Fault::Panicked)?;
        Ok(served?)
    }
}
