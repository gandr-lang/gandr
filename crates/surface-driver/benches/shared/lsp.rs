//! One open document, edited over a served session, for the workloads that
//! time a session's answers: the benchmark report's and the parser's
//! report's.
//!
//! [`live`] hosts a session on the calling thread through
//! `gandr_surface_lsp::client::hosting`, and a workload drives a
//! [`Document`] on a thread of its own. The document waits for a judgement by
//! asking for its symbols, which the server answers once the document's
//! judgement settles. A measure the workload takes counts the client alone,
//! and a profiler on the calling thread attributes the server's work to the
//! server's functions.

use std::path::Path;

use gandr_surface_lsp::Spelling;
use gandr_surface_lsp::Workspace;
use gandr_surface_lsp::client::Client;
pub use gandr_surface_lsp::client::Fault;
use gandr_surface_lsp::client::Method;
use gandr_surface_lsp::client::hosting;
use serde_json::Value;
use serde_json::json;

/// One document open over a session's client.
pub struct Document
{
    /// The session's client.
    client: Client,
    /// The document's URI.
    uri: String,
    /// The document's latest version.
    version: u32,
}

impl Document
{
    /// Wait until the document's latest judgement settles: a request reading
    /// the document is answered only then.
    ///
    /// # Specification
    /// trivial.
    fn settle(&mut self) -> Result<(), Fault>
    {
        let params = json!({"textDocument": {"uri": self.uri}});
        self.client
            .request(Method("textDocument/documentSymbol"), &params)
            .map(drop)
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
        let changes: Vec<Value> = edits
            .iter()
            .map(|edit| {
                self.version = self.version.saturating_add(1);
                json!({"jsonrpc": "2.0", "method": "textDocument/didChange", "params": {
                    "textDocument": {"uri": self.uri, "version": self.version},
                    "contentChanges": [{"text": edit}],
                }})
            })
            .collect();
        self.client.send(&changes)?;
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
    Workload: FnOnce(&mut Document) -> Result<Answer, Fault> + Send + 'static,
{
    let uri = format!("file://{}", path.display());
    // The workspace's own pool has one thread, so each admission runs where
    // it is submitted, and a count a profiler takes stays exact.
    let (answer, served) = hosting(Workspace::spelled(Spelling::Unicode), move |mut client| {
        let _capabilities = client.request(Method("initialize"), &json!({}))?;
        client.send(&[
            json!({"jsonrpc": "2.0", "method": "initialized", "params": {}}),
            json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": uri, "languageId": "gandr", "version": 1_u8, "text": text},
            }}),
        ])?;
        let mut document = Document {
            client,
            uri,
            version: 1,
        };
        document.settle()?;
        let answer = workload(&mut document)?;
        let _shutdown = document.client.request(Method("shutdown"), &Value::Null)?;
        document
            .client
            .send(&[json!({"jsonrpc": "2.0", "method": "exit"})])?;
        let _rest = document.client.finish()?;
        Ok(answer)
    })?;
    core::hint::black_box(served);
    Ok(answer)
}
