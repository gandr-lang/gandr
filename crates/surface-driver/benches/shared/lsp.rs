//! A language-server client over pipes, for the workloads that time a
//! session's answers: the benchmark report's and the parser's report's.
//!
//! [`live`] serves a session on the calling thread, and a client on a thread
//! of its own speaks to it. The client waits for a judgement by asking for the
//! document's symbols, which the server answers once the document's judgement
//! settles. A workload runs on the client's thread, so a measure it takes
//! counts the client alone. The server runs on the calling thread, so a
//! profiler there attributes the server's work to the server's functions.

use core::fmt;
use std::io::BufReader;
use std::io::Read as _;
use std::io::Write as _;
use std::path::Path;

use gandr_surface_lsp::Spelling;
use gandr_surface_lsp::TransportFault;
use quenchant_shape::shape::Maybe;

/// Why a session stopped before its workload ended.
#[derive(Debug)]
pub enum Fault
{
    /// A pipe between the client and the server refused.
    Pipe(std::io::Error),
    /// The server's streams, or a frame the server wrote, faulted.
    Transport(TransportFault),
    /// The server wrote a body that is not JSON.
    Json(serde_json::Error),
    /// The server ended before it answered the request with this method.
    Ended(&'static str),
    /// The client's thread panicked.
    Client,
}

impl From<std::io::Error> for Fault
{
    /// A pipe's refusal.
    ///
    /// # Specification
    /// trivial.
    fn from(fault: std::io::Error) -> Self
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
    fn from(fault: TransportFault) -> Self
    {
        Self::Transport(fault)
    }
}

impl From<serde_json::Error> for Fault
{
    /// A body's decoding fault.
    ///
    /// # Specification
    /// trivial.
    fn from(fault: serde_json::Error) -> Self
    {
        Self::Json(fault)
    }
}

impl fmt::Display for Fault
{
    /// Writes why the session stopped.
    ///
    /// # Specification
    /// trivial.
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Pipe(ref fault) => write!(f, "a pipe to the server refused: {fault}"),
            Self::Transport(ref fault) => write!(f, "the session's transport faulted: {fault}"),
            Self::Json(ref fault) => write!(f, "the server wrote a body that is not JSON: {fault}"),
            Self::Ended(method) => write!(f, "the server ended before it answered `{method}`"),
            Self::Client => write!(f, "the client's thread panicked"),
        }
    }
}

impl core::error::Error for Fault
{
}

/// One message as a framed body: its `Content-Length` header, then the JSON.
///
/// # Specification
/// trivial.
fn framed(message: &serde_json::Value) -> Vec<u8>
{
    let body = message.to_string();
    let mut frame = format!("Content-Length: {}\r\n\r\n", body.len()).into_bytes();
    frame.extend_from_slice(body.as_bytes());
    frame
}

/// A language-server client speaking to a session over pipes. It opens one
/// document, waits for the open's judgement, and then runs its workload's
/// changes.
pub struct Client
{
    /// Where the client's messages go.
    input: std::io::PipeWriter,
    /// What the server writes.
    output: BufReader<std::io::PipeReader>,
    /// The document's URI.
    uri: String,
    /// The document's latest version.
    version: u32,
    /// The identifier of the client's latest request.
    asked: u32,
}

impl Client
{
    /// Write `messages` to the server in one write, so it reads them together.
    ///
    /// # Specification
    /// trivial.
    fn send(
        &mut self,
        messages: &[serde_json::Value],
    ) -> Result<(), Fault>
    {
        let frames: Vec<u8> = messages.iter().flat_map(framed).collect();
        self.input.write_all(&frames)?;
        Ok(())
    }

    /// Send the request `method` with `params`, and read the server's
    /// messages until its response.
    ///
    /// # Specification
    /// trivial.
    fn ask(
        &mut self,
        method: &'static str,
        params: &serde_json::Value,
    ) -> Result<(), Fault>
    {
        self.asked = self.asked.saturating_add(1);
        let id = self.asked;
        self.send(&[
            serde_json::json!({"jsonrpc": "2.0", "id": id, "method": method, "params": params}),
        ])?;
        loop {
            let frame = gandr_surface_lsp::read_frame(&mut self.output)?;
            let Maybe::Present(body) = frame
            else {
                return Err(Fault::Ended(method));
            };
            let message: serde_json::Value = serde_json::from_slice(body.as_ref())?;
            if message.get("method").is_none() && message.get("id") == Some(&serde_json::json!(id))
            {
                return Ok(());
            }
        }
    }

    /// Wait until the document's latest judgement settles: a request reading
    /// the document is answered only then.
    ///
    /// # Specification
    /// trivial.
    fn settle(&mut self) -> Result<(), Fault>
    {
        let params = serde_json::json!({"textDocument": {"uri": self.uri}});
        self.ask("textDocument/documentSymbol", &params)
    }

    /// Change the document to each of `edits` in order, each a whole text at
    /// the next version, sent in one write, and wait until the last change's
    /// judgement settles.
    ///
    /// # Specification
    /// trivial.
    pub fn change(
        &mut self,
        edits: &[String],
    ) -> Result<(), Fault>
    {
        let changes: Vec<serde_json::Value> = edits
            .iter()
            .map(|edit| {
                self.version = self.version.saturating_add(1);
                serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didChange", "params": {
                    "textDocument": {"uri": self.uri, "version": self.version},
                    "contentChanges": [{"text": edit}],
                }})
            })
            .collect();
        self.send(&changes)?;
        self.settle()
    }
}

/// Serve a language-server session on this thread while a client on its own
/// thread opens `path` at `text`, waits for the open's judgement, runs
/// `workload`, and shuts the session down. Answers what the workload
/// answered.
///
/// # Specification
/// trivial.
pub fn live<Answer, Workload>(
    path: &Path,
    text: String,
    workload: Workload,
) -> Result<Answer, Fault>
where
    Answer: Send + 'static,
    Workload: FnOnce(&mut Client) -> Result<Answer, Fault> + Send + 'static,
{
    let (mut read, input) = std::io::pipe()?;
    let (output, mut written) = std::io::pipe()?;
    let uri = format!("file://{}", path.display());
    let client = std::thread::spawn(move || {
        let mut client = Client {
            input,
            output: BufReader::new(output),
            uri,
            version: 1,
            asked: 0,
        };
        client.ask("initialize", &serde_json::json!({}))?;
        client.send(&[
            serde_json::json!({"jsonrpc": "2.0", "method": "initialized", "params": {}}),
            serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": client.uri, "languageId": "gandr", "version": 1_u8, "text": text},
            }}),
        ])?;
        client.settle()?;
        let answer = workload(&mut client)?;
        client.ask("shutdown", &serde_json::Value::Null)?;
        client.send(&[serde_json::json!({"jsonrpc": "2.0", "method": "exit"})])?;
        drop(client.input);
        let mut rest = Vec::new();
        client.output.read_to_end(&mut rest)?;
        Ok(answer)
    });
    // The workspace's own pool has one thread, so each admission runs where
    // it is submitted, and a count a profiler takes stays exact.
    let served = gandr_surface_lsp::serve(
        &mut BufReader::new(&mut read),
        &mut written,
        &mut std::io::sink(),
        gandr_surface_lsp::Workspace::spelled(Spelling::Unicode),
    );
    drop(written);
    let answer = client.join().map_err(|_panic| Fault::Client)?;
    core::hint::black_box(served?);
    answer
}
