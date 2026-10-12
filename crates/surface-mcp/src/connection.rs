//! One client's connection: the messages it sends, answered over the shared
//! workspace, and the notifications its subscriptions owe it when a document
//! changes.
//!
//! The connection speaks both eras of the protocol. A legacy client opens
//! with `initialize` and subscribes through `resources/subscribe`; a modern
//! one names its version in each request's `_meta`, may ask
//! `server/discover`, and opens `subscriptions/listen` streams. Nothing a
//! request answers depends on which era the client speaks, so one connection
//! serves both.

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use alloc::format;
use alloc::string::String;
use alloc::string::ToString as _;
use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;
use gandr_surface_lsp::DocumentUri;
use gandr_surface_lsp::DocumentVersion;
use gandr_surface_lsp::Workspace;
use serde_json::Map;
use serde_json::Value;
use serde_json::json;

use crate::tools;

/// The protocol revision that carries its version in every request.
pub const MODERN: &str = "2026-07-28";

/// The handshake-based revisions an `initialize` may name, newest first.
pub const LEGACY: [&str; 4] = ["2025-11-25", "2025-06-18", "2025-03-26", "2024-11-05"];

/// The `_meta` key a modern request names its protocol version under.
const VERSION_KEY: &str = "io.modelcontextprotocol/protocolVersion";

/// The `_meta` key a subscription's notifications name it under.
const SUBSCRIPTION_KEY: &str = "io.modelcontextprotocol/subscriptionId";

/// The `_meta` key a result names its server under.
const SERVER_KEY: &str = "io.modelcontextprotocol/serverInfo";

/// The scheme every resource this server serves is named under.
const SCHEME: &str = "gandr://";

/// The suffix naming a document's diagnostics resource.
const DIAGNOSTICS: &str = "/diagnostics";

/// How a model should use this server.
const INSTRUCTIONS: &str = "Reads the documents gandr's engine hub holds open: their diagnostics, \
                            outline, the syntax expected at a position and the type of a \
                            declaration. `trial` judges up to 32 candidate fills of a range at \
                            once without changing the document and ranks them, best first; \
                            `propose` offers one to the editors, shown only once it checks. \
                            Every tool result carries `changes`: the documents opened, changed \
                            or closed since this connection's previous call.";

/// Why a message is refused.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Refusal
{
    /// The line is not JSON.
    Parse,
    /// The value is not a request or a notification.
    InvalidRequest,
    /// No method of that name is served.
    MethodNotFound,
    /// The parameters name no resource served.
    ResourceNotFound,
}

/// One client's place: its subscriptions, and the version of each document
/// as its last tool call saw it.
#[derive(Debug, Default)]
pub struct Connection
{
    /// The resources subscribed through `resources/subscribe`.
    subscribed: BTreeSet<String>,
    /// Each open `subscriptions/listen` stream, by its request's identifier
    /// as JSON text, with that identifier and the resources it follows.
    listening: BTreeMap<String, (Value, BTreeSet<String>)>,
    /// The documents the last tool call saw, at the version it saw each.
    seen: BTreeMap<DocumentUri, DocumentVersion>,
}

impl Connection
{
    /// The messages `message`, one line the client sent, is answered with,
    /// read off `workspace`.
    ///
    /// # Specification
    /// - requires: nothing; any value is admitted.
    /// - ensures: a request is answered exactly once under its identifier,
    ///   except `subscriptions/listen`, which is acknowledged by a notification
    ///   and never answered while its stream is open; a notification is never
    ///   answered; a client's response is dropped. A request naming a protocol
    ///   version in `_meta` that is neither [`MODERN`] nor in [`LEGACY`] is
    ///   refused with the supported versions. A value that is no message is
    ///   answered with an invalid-request error under a `null` identifier.
    /// - provides: the whole protocol, but the bytes.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each era's opening, every tool and resource method,
    ///   both subscription styles, an unknown method, an unsupported version
    ///   and a malformed message, each asserted at its exact reply.
    /// - witness: `connection::tests::each_era_opens_and_lists_the_tools`
    /// - witness: `connection::tests::an_unsupported_version_names_the_supported_ones`
    /// - witness: `connection::tests::resources_name_each_documents_diagnostics`
    /// - witness: `connection::tests::subscriptions_hear_only_their_documents`
    #[spec(ensures: |ret| ret.len() <= 1)]
    #[inline]
    #[must_use]
    pub fn handle(
        &mut self,
        workspace: &mut Workspace,
        message: &Value,
    ) -> Vec<Value>
    {
        let Some(object) = message
            .as_object()
            .filter(|object| object.get("jsonrpc") == Some(&json!("2.0")))
        else {
            return vec![failure(&Value::Null, Refusal::InvalidRequest)];
        };
        let method = object.get("method").and_then(Value::as_str);
        match (object.get("id"), method) {
            | (Some(id), Some(_)) => vec![self.request(workspace, id, object)],
            | (None, Some("notifications/cancelled")) => {
                if let Some(id) = object
                    .get("params")
                    .and_then(|params| params.get("requestId"))
                {
                    drop(self.listening.remove(&id.to_string()));
                }
                Vec::new()
            },
            | (None, Some(_)) => Vec::new(),
            | (Some(_), None) if object.contains_key("result") || object.contains_key("error") => {
                Vec::new()
            },
            | (Some(_) | None, None) => vec![failure(&Value::Null, Refusal::InvalidRequest)],
        }
    }

    /// The answer to a line that is not JSON.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn unreadable() -> Value
    {
        failure(&Value::Null, Refusal::Parse)
    }

    /// The notifications this connection's subscriptions owe it now that the
    /// document at `uri` changed.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one `notifications/resources/updated` naming the document's
    ///   diagnostics resource when `resources/subscribe` named it, and one per
    ///   open `subscriptions/listen` stream that follows it, carrying that
    ///   stream's identifier in `_meta`; nothing for a document no subscription
    ///   follows.
    /// - provides: the push half of both subscription styles.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a change to a followed document notifies each style
    ///   once, a change to another notifies nothing, and a cancelled stream
    ///   hears nothing more.
    /// - witness: `connection::tests::subscriptions_hear_only_their_documents`
    #[spec(ensures: |ret| ret.len() <= self.listening.len().saturating_add(1))]
    #[inline]
    #[must_use]
    pub fn changed(
        &self,
        uri: &DocumentUri,
    ) -> Vec<Value>
    {
        let Some(resource) = resource_of(uri)
        else {
            return Vec::new();
        };
        let mut notifications = Vec::new();
        if self.subscribed.contains(&resource) {
            notifications.push(json!({
                "jsonrpc": "2.0",
                "method": "notifications/resources/updated",
                "params": { "uri": resource },
            }));
        }
        for listened in self.listening.values() {
            let (ref id, ref resources) = *listened;
            if resources.contains(&resource) {
                notifications.push(json!({
                    "jsonrpc": "2.0",
                    "method": "notifications/resources/updated",
                    "params": { "_meta": { SUBSCRIPTION_KEY: id }, "uri": resource },
                }));
            }
        }
        notifications
    }

    /// The reply to the request `id`, the message `object`.
    ///
    /// # Specification
    /// trivial.
    fn request(
        &mut self,
        workspace: &mut Workspace,
        id: &Value,
        object: &Map<String, Value>,
    ) -> Value
    {
        let params = object.get("params").cloned().unwrap_or(Value::Null);
        let method = object
            .get("method")
            .and_then(Value::as_str)
            .unwrap_or_default();
        match method {
            | "initialize" => return success(id, initialized(&params)),
            | "server/discover" => return success(id, discovered()),
            | _ => {},
        }
        if let Some(version) = params
            .get("_meta")
            .and_then(|meta| meta.get(VERSION_KEY))
            .and_then(Value::as_str)
            && version != MODERN
            && !LEGACY.contains(&version)
        {
            return json!({
                "jsonrpc": "2.0",
                "id": id,
                "error": {
                    "code": -32_022_i32,
                    "message": "Unsupported protocol version",
                    "data": { "supported": supported(), "requested": version },
                },
            });
        }
        let answered = match method {
            | "ping" => Ok(json!({})),
            | "tools/list" => {
                Ok(json!({ "tools": tools::list(), "ttlMs": 0_u32, "cacheScope": "private" }))
            },
            | "tools/call" => Ok(self.call(workspace, &params)),
            | "resources/list" => Ok(listed(workspace)),
            | "resources/read" => read(workspace, &params),
            | "resources/subscribe" => resource(&params).map(|resource| {
                let _new = self.subscribed.insert(resource);
                json!({})
            }),
            | "resources/unsubscribe" => resource(&params).map(|resource| {
                let _held = self.subscribed.remove(&resource);
                json!({})
            }),
            | "subscriptions/listen" => return self.listen(id, &params),
            | _ => Err(Refusal::MethodNotFound),
        };
        match answered {
            | Ok(result) => success(id, result),
            | Err(refusal) => failure(id, refusal),
        }
    }

    /// The result of the tool call `params` names, with what changed since
    /// this connection's last call.
    ///
    /// # Specification
    /// trivial.
    fn call(
        &mut self,
        workspace: &mut Workspace,
        params: &Value,
    ) -> Value
    {
        let changes = self.changes(workspace);
        let arguments = params
            .get("arguments")
            .cloned()
            .unwrap_or_else(|| json!({}));
        let (mut structured, failed) = match tools::call(workspace, params.get("name"), &arguments)
        {
            | Ok(structured) => (structured, false),
            | Err(refusal) => (json!({ "error": refusal.to_string() }), true),
        };
        if let Some(object) = structured.as_object_mut() {
            drop(object.insert(String::from("changes"), changes));
        }
        json!({
            "content": [{ "type": "text", "text": structured.to_string() }],
            "structuredContent": structured,
            "isError": failed,
        })
    }

    /// The documents opened or changed, and those closed, since the last
    /// call; the versions held now become the ones seen.
    ///
    /// # Specification
    /// trivial.
    fn changes(
        &mut self,
        workspace: &Workspace,
    ) -> Value
    {
        let held: BTreeMap<DocumentUri, DocumentVersion> = workspace
            .held()
            .map(|(uri, version)| (uri.clone(), version))
            .collect();
        let changed: Vec<Value> = held
            .iter()
            .filter(|&(uri, version)| self.seen.get(uri) != Some(version))
            .map(|(uri, version)| json!({ "uri": uri, "version": version }))
            .collect();
        let closed: Vec<Value> = self
            .seen
            .keys()
            .filter(|uri| !held.contains_key(*uri))
            .map(|uri| json!(uri))
            .collect();
        self.seen = held;
        json!({ "changed": changed, "closed": closed })
    }

    /// Open the `subscriptions/listen` stream the request `id` asks for, and
    /// acknowledge what it will hear.
    ///
    /// # Specification
    /// trivial.
    fn listen(
        &mut self,
        id: &Value,
        params: &Value,
    ) -> Value
    {
        let resources: BTreeSet<String> = params
            .pointer("/notifications/resourceSubscriptions")
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
            .filter(|&resource| document_of(resource).is_some())
            .filter_map(Value::as_str)
            .map(String::from)
            .collect();
        let acknowledged: Vec<&String> = resources.iter().collect();
        let acknowledgement = json!({
            "jsonrpc": "2.0",
            "method": "notifications/subscriptions/acknowledged",
            "params": {
                "_meta": { SUBSCRIPTION_KEY: id },
                "notifications": { "resourceSubscriptions": acknowledged },
            },
        });
        drop(
            self.listening
                .insert(id.to_string(), (id.clone(), resources)),
        );
        acknowledgement
    }
}

/// Every protocol version served, newest first.
///
/// # Specification
/// trivial.
fn supported() -> Vec<Value>
{
    core::iter::once(MODERN)
        .chain(LEGACY)
        .map(Value::from)
        .collect()
}

/// What this server can do, as both eras advertise it.
///
/// # Specification
/// trivial.
fn capabilities() -> Value
{
    json!({ "tools": {}, "resources": { "subscribe": true } })
}

/// The server's name and version.
///
/// # Specification
/// trivial.
fn identity() -> Value
{
    json!({ "name": "gandr", "version": env!("CARGO_PKG_VERSION") })
}

/// The result of a legacy `initialize` naming `params`.
///
/// # Specification
/// trivial.
fn initialized(params: &Value) -> Value
{
    let requested = params.get("protocolVersion").and_then(Value::as_str);
    let version = requested
        .filter(|requested| LEGACY.contains(requested))
        .unwrap_or(LEGACY[0]);
    json!({
        "protocolVersion": version,
        "capabilities": capabilities(),
        "serverInfo": identity(),
        "instructions": INSTRUCTIONS,
    })
}

/// The result of `server/discover`.
///
/// # Specification
/// trivial.
fn discovered() -> Value
{
    json!({
        "supportedVersions": supported(),
        "capabilities": capabilities(),
        "instructions": INSTRUCTIONS,
        "ttlMs": 0_u32,
        "cacheScope": "private",
    })
}

/// The diagnostics resource of every open `file` document.
///
/// # Specification
/// trivial.
fn listed(workspace: &Workspace) -> Value
{
    let resources: Vec<Value> = workspace
        .held()
        .filter_map(|(uri, _version)| {
            resource_of(uri).map(|resource| {
                json!({
                    "uri": resource,
                    "name": format!("diagnostics of {uri}"),
                    "mimeType": "application/json",
                })
            })
        })
        .collect();
    json!({ "resources": resources, "ttlMs": 0_u32, "cacheScope": "private" })
}

/// The contents of the resource `params` names.
///
/// # Specification
/// trivial.
fn read(
    workspace: &Workspace,
    params: &Value,
) -> Result<Value, Refusal>
{
    let named = params.get("uri").cloned().unwrap_or(Value::Null);
    let (uri, version, diagnostics) = document_of(&named)
        .and_then(|uri| {
            workspace
                .published(&uri)
                .map(|(version, diagnostics)| (uri.clone(), version, diagnostics))
        })
        .ok_or(Refusal::ResourceNotFound)?;
    let text = json!({ "uri": uri, "version": version, "diagnostics": diagnostics });
    Ok(json!({
        "contents": [{ "uri": named, "mimeType": "application/json", "text": text.to_string() }],
        "ttlMs": 0_u32,
        "cacheScope": "private",
    }))
}

/// The diagnostics resource `params` names, when it names one.
///
/// # Specification
/// trivial.
fn resource(params: &Value) -> Result<String, Refusal>
{
    params
        .get("uri")
        .filter(|&named| document_of(named).is_some())
        .and_then(Value::as_str)
        .map(String::from)
        .ok_or(Refusal::ResourceNotFound)
}

/// The diagnostics resource of the document at `uri`: `gandr://` and its
/// path, then `/diagnostics`; `None` for a URI that is not a `file` URI.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the resource names the document back through [`document_of`].
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an open document's resource is listed and read back.
/// - witness: `connection::tests::resources_name_each_documents_diagnostics`
#[spec(ensures: |ret| ret.as_ref().is_none_or(|resource|
    document_of(&Value::from(resource.as_str())).as_ref() == Some(uri)))]
fn resource_of(uri: &DocumentUri) -> Option<String>
{
    uri.to_string()
        .strip_prefix("file://")
        .map(|path| format!("{SCHEME}{path}{DIAGNOSTICS}"))
}

/// The document whose diagnostics the resource `named` names.
///
/// # Specification
/// trivial.
fn document_of(named: &Value) -> Option<DocumentUri>
{
    named
        .as_str()
        .and_then(|resource| resource.strip_prefix(SCHEME))
        .and_then(|rest| rest.strip_suffix(DIAGNOSTICS))
        .filter(|path| path.starts_with('/'))
        .map(|path| DocumentUri::from(format!("file://{path}").as_str()))
}

/// A successful reply to the request `id`, the result marked complete and
/// naming this server.
///
/// # Specification
/// trivial.
fn success(
    id: &Value,
    mut result: Value,
) -> Value
{
    if let Some(object) = result.as_object_mut() {
        drop(object.insert(String::from("resultType"), json!("complete")));
        drop(object.insert(String::from("_meta"), json!({ SERVER_KEY: identity() })));
    }
    json!({ "jsonrpc": "2.0", "id": id, "result": result })
}

/// A refusal of the request `id`.
///
/// # Specification
/// trivial.
fn failure(
    id: &Value,
    refusal: Refusal,
) -> Value
{
    let (code, message) = match refusal {
        | Refusal::Parse => (-32_700_i32, "Parse error"),
        | Refusal::InvalidRequest => (-32_600_i32, "Invalid Request"),
        | Refusal::MethodNotFound => (-32_601_i32, "Method not found"),
        | Refusal::ResourceNotFound => (-32_602_i32, "Resource not found"),
    };
    json!({ "jsonrpc": "2.0", "id": id, "error": { "code": code, "message": message } })
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;
    use alloc::vec::Vec;

    use gandr_surface_lsp::Body;
    use gandr_surface_lsp::Peer;
    use gandr_surface_lsp::Server;
    use gandr_surface_lsp::Workspace;
    use serde_json::Value;
    use serde_json::json;

    use super::Connection;
    use super::MODERN;

    /// A workspace an editor's connection, returned beside it, has
    /// initialised.
    ///
    /// # Specification
    /// trivial.
    fn editor() -> (Workspace, Server)
    {
        let mut workspace = Workspace::default();
        let mut server = Server::new(Peer::from(1_u64));
        sync(
            &mut server,
            &mut workspace,
            &json!({ "jsonrpc": "2.0", "id": 1_i32, "method": "initialize", "params": {} }),
        );
        (workspace, server)
    }

    /// Have `server` handle `message` over `workspace`, dropping what it
    /// answers.
    ///
    /// # Specification
    /// trivial.
    fn sync(
        server: &mut Server,
        workspace: &mut Workspace,
        message: &Value,
    )
    {
        let body = Body::from(message.to_string().into_bytes());
        drop(server.handle(workspace, &body));
    }

    /// The `didOpen` of `uri` at `version` with `text`.
    ///
    /// # Specification
    /// trivial.
    fn opened(
        uri: &Value,
        version: &Value,
        text: &Value,
    ) -> Value
    {
        json!({ "jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
            "textDocument": { "uri": uri, "languageId": "gandr", "version": version, "text": text } } })
    }

    /// The `didChange` of `uri` to `version`, the whole text `text`.
    ///
    /// # Specification
    /// trivial.
    fn changed(
        uri: &Value,
        version: &Value,
        text: &Value,
    ) -> Value
    {
        json!({ "jsonrpc": "2.0", "method": "textDocument/didChange", "params": {
            "textDocument": { "uri": uri, "version": version },
            "contentChanges": [{ "text": text }] } })
    }

    /// The one reply `connection` gives `message` over `workspace`.
    ///
    /// # Specification
    /// trivial.
    fn ask(
        connection: &mut Connection,
        workspace: &mut Workspace,
        message: &Value,
    ) -> Value
    {
        let mut replies = connection.handle(workspace, message);
        assert_eq!(replies.len(), 1, "one reply to {message}");
        replies.remove(0_usize)
    }

    /// The structured result of calling `tool` with `arguments`.
    ///
    /// # Specification
    /// trivial.
    fn call(
        connection: &mut Connection,
        workspace: &mut Workspace,
        tool: &Value,
        arguments: &Value,
    ) -> Value
    {
        let reply = ask(
            connection,
            workspace,
            &json!({ "jsonrpc": "2.0", "id": 9_i32, "method": "tools/call",
                "params": { "name": tool, "arguments": arguments } }),
        );
        let result = reply.get("result").expect("a tool call has a result");
        assert_eq!(
            result
                .pointer("/content/0/text")
                .and_then(Value::as_str)
                .map(String::from),
            result.get("structuredContent").map(Value::to_string),
            "the text content is the structured content"
        );
        result.clone()
    }

    #[test]
    fn each_era_opens_and_lists_the_tools()
    {
        let mut workspace = Workspace::default();
        let mut connection = Connection::default();
        let legacy = ask(
            &mut connection,
            &mut workspace,
            &json!({ "jsonrpc": "2.0", "id": 1_i32, "method": "initialize",
            "params": { "protocolVersion": "2025-06-18", "capabilities": {} } }),
        );
        assert_eq!(
            legacy.pointer("/result/protocolVersion"),
            Some(&json!("2025-06-18"))
        );
        assert_eq!(
            legacy.pointer("/result/capabilities/resources/subscribe"),
            Some(&json!(true))
        );
        assert_eq!(
            legacy.pointer("/result/resultType"),
            Some(&json!("complete"))
        );
        let unknown = ask(
            &mut connection,
            &mut workspace,
            &json!({ "jsonrpc": "2.0", "id": 2_i32, "method": "initialize",
            "params": { "protocolVersion": "1999-01-01" } }),
        );
        assert_eq!(
            unknown.pointer("/result/protocolVersion"),
            Some(&json!("2025-11-25")),
            "an unknown legacy version is answered with the newest"
        );
        let meta = json!({ "io.modelcontextprotocol/protocolVersion": MODERN });
        let discovered = ask(
            &mut connection,
            &mut workspace,
            &json!({ "jsonrpc": "2.0", "id": 3_i32, "method": "server/discover", "params": { "_meta": meta } }),
        );
        assert_eq!(
            discovered.pointer("/result/supportedVersions/0"),
            Some(&json!(MODERN))
        );
        let listed = ask(
            &mut connection,
            &mut workspace,
            &json!({ "jsonrpc": "2.0", "id": 4_i32, "method": "tools/list", "params": { "_meta": meta } }),
        );
        let names: Vec<&str> = listed
            .pointer("/result/tools")
            .and_then(Value::as_array)
            .expect("the tools are listed")
            .iter()
            .filter_map(|tool| tool.get("name").and_then(Value::as_str))
            .collect();
        assert_eq!(names, [
            "diagnostics",
            "documents",
            "expected_syntax",
            "outline",
            "propose",
            "trial",
            "type_of"
        ]);
        assert_eq!(
            ask(
                &mut connection,
                &mut workspace,
                &json!({ "jsonrpc": "2.0", "id": 5_i32, "method": "ping" })
            )
            .pointer("/result/resultType"),
            Some(&json!("complete"))
        );
        assert_eq!(
            ask(
                &mut connection,
                &mut workspace,
                &json!({ "jsonrpc": "2.0", "id": 6_i32, "method": "prompts/list" })
            )
            .pointer("/error/code"),
            Some(&json!(-32_601_i32))
        );
        assert_eq!(
            ask(&mut connection, &mut workspace, &json!(3_u8)),
            json!({ "jsonrpc": "2.0", "id": null, "error": { "code": -32_600_i32, "message": "Invalid Request" } })
        );
        assert_eq!(
            Connection::unreadable().pointer("/error/code"),
            Some(&json!(-32_700_i32))
        );
        assert!(
            connection
                .handle(
                    &mut workspace,
                    &json!({ "jsonrpc": "2.0", "method": "notifications/initialized" })
                )
                .is_empty(),
            "a notification is not answered"
        );
        assert!(
            connection
                .handle(
                    &mut workspace,
                    &json!({ "jsonrpc": "2.0", "id": 7_i32, "result": {} })
                )
                .is_empty(),
            "a client's response is dropped"
        );
    }

    #[test]
    fn an_unsupported_version_names_the_supported_ones()
    {
        let reply = ask(
            &mut Connection::default(),
            &mut Workspace::default(),
            &json!({ "jsonrpc": "2.0", "id": 1_i32, "method": "tools/list",
            "params": { "_meta": { "io.modelcontextprotocol/protocolVersion": "1900-01-01" } } }),
        );
        assert_eq!(reply.pointer("/error/code"), Some(&json!(-32_022_i32)));
        assert_eq!(
            reply.pointer("/error/data/requested"),
            Some(&json!("1900-01-01"))
        );
        assert_eq!(
            reply.pointer("/error/data/supported"),
            Some(&json!([
                MODERN,
                "2025-11-25",
                "2025-06-18",
                "2025-03-26",
                "2024-11-05"
            ]))
        );
    }

    #[test]
    fn each_tool_answers_through_the_wire()
    {
        let (mut workspace, mut server) = editor();
        let mut connection = Connection::default();
        let uri = json!("file:///tmp/mcp.gandr");
        sync(
            &mut server,
            &mut workspace,
            &opened(&uri, &json!(1_i32), &json!("def f = 42 ;\n")),
        );
        let documents = call(
            &mut connection,
            &mut workspace,
            &json!("documents"),
            &json!({}),
        );
        assert_eq!(
            documents.pointer("/structuredContent/documents"),
            Some(&json!([{ "uri": uri, "version": 1_i32 }]))
        );
        assert_eq!(
            documents.pointer("/structuredContent/changes"),
            Some(&json!({ "changed": [{ "uri": uri, "version": 1_i32 }], "closed": [] })),
            "the first call sees every open document as changed"
        );
        let named = json!({ "uri": uri });
        let diagnostics = call(
            &mut connection,
            &mut workspace,
            &json!("diagnostics"),
            &named,
        );
        assert_eq!(diagnostics.pointer("/isError"), Some(&json!(false)));
        assert_eq!(
            diagnostics.pointer("/structuredContent/version"),
            Some(&json!(1_i32))
        );
        assert_eq!(
            diagnostics.pointer("/structuredContent/diagnostics"),
            Some(&json!([]))
        );
        assert_eq!(
            diagnostics.pointer("/structuredContent/changes"),
            Some(&json!({ "changed": [], "closed": [] })),
            "nothing changed since the last call"
        );
        let outline = call(&mut connection, &mut workspace, &json!("outline"), &named);
        assert_eq!(
            outline.pointer("/structuredContent/symbols/0/name"),
            Some(&json!("f"))
        );
        let at = json!({ "uri": uri, "line": 0_u32, "character": 4_u32 });
        let typed = call(&mut connection, &mut workspace, &json!("type_of"), &at);
        assert_eq!(
            typed.pointer("/structuredContent/hover/contents/value"),
            Some(&json!("```gandr\nf : Integer\n```"))
        );
        let expected = call(
            &mut connection,
            &mut workspace,
            &json!("expected_syntax"),
            &json!({ "uri": uri, "line": 0_u32, "character": 7_u32 }),
        );
        assert_eq!(expected.pointer("/isError"), Some(&json!(false)));
        assert!(expected.pointer("/structuredContent/completions").is_some());
        let unplaced = call(&mut connection, &mut workspace, &json!("type_of"), &named);
        assert_eq!(
            unplaced.pointer("/isError"),
            Some(&json!(true)),
            "a position is required"
        );
        sync(
            &mut server,
            &mut workspace,
            &changed(&uri, &json!(2_i32), &json!("def g = missing ;\n")),
        );
        let refused = call(
            &mut connection,
            &mut workspace,
            &json!("diagnostics"),
            &named,
        );
        assert_eq!(
            refused.pointer("/structuredContent/version"),
            Some(&json!(2_i32))
        );
        assert_eq!(
            refused
                .pointer("/structuredContent/diagnostics")
                .and_then(Value::as_array)
                .map(Vec::len),
            Some(1_usize),
            "the edit's refusal is read at its version"
        );
        assert_eq!(
            refused.pointer("/structuredContent/changes/changed"),
            Some(&json!([{ "uri": uri, "version": 2_i32 }]))
        );
        let stranger = call(
            &mut connection,
            &mut workspace,
            &json!("diagnostics"),
            &json!({ "uri": "file:///tmp/elsewhere.gandr" }),
        );
        assert_eq!(stranger.pointer("/isError"), Some(&json!(true)));
        assert!(
            stranger
                .pointer("/structuredContent/error")
                .and_then(Value::as_str)
                .is_some_and(|error| error.contains("not open in the hub"))
        );
        let unknown = call(&mut connection, &mut workspace, &json!("normalise"), &named);
        assert_eq!(unknown.pointer("/isError"), Some(&json!(true)));
        sync(
            &mut server,
            &mut workspace,
            &json!({ "jsonrpc": "2.0", "method": "textDocument/didClose",
                "params": { "textDocument": { "uri": uri } } }),
        );
        let closed = call(
            &mut connection,
            &mut workspace,
            &json!("documents"),
            &json!({}),
        );
        assert_eq!(
            closed.pointer("/structuredContent/changes"),
            Some(&json!({ "changed": [], "closed": [uri] }))
        );
    }

    #[test]
    fn a_proposal_reaches_the_editor_once_it_checks()
    {
        let (mut workspace, mut server) = editor();
        let mut connection = Connection::default();
        let uri = json!("file:///tmp/proposal.gandr");
        sync(
            &mut server,
            &mut workspace,
            &opened(
                &uri,
                &json!(2_i32),
                &json!("def f : Integer ;\ndef f = missing ;\n"),
            ),
        );
        let hole = json!({ "start": { "line": 1_u32, "character": 8_u32 },
            "end": { "line": 1_u32, "character": 15_u32 } });
        let failing = call(
            &mut connection,
            &mut workspace,
            &json!("propose"),
            &json!({ "uri": uri, "version": 2_i32, "range": hole, "text": "\"one\"" }),
        );
        assert_eq!(failing.pointer("/isError"), Some(&json!(false)));
        assert_eq!(
            failing.pointer("/structuredContent/kept"),
            Some(&json!(false))
        );
        assert_eq!(
            failing
                .pointer("/structuredContent/diagnostics")
                .and_then(Value::as_array)
                .map(Vec::len),
            Some(1_usize),
            "a fill that does not check is answered with why"
        );
        let stale = call(
            &mut connection,
            &mut workspace,
            &json!("propose"),
            &json!({ "uri": uri, "version": 1_i32, "range": hole, "text": "42" }),
        );
        assert_eq!(stale.pointer("/isError"), Some(&json!(true)));
        let kept = call(
            &mut connection,
            &mut workspace,
            &json!("propose"),
            &json!({ "uri": uri, "version": 2_i32, "range": hole, "text": "42",
                "explanation": "the answer" }),
        );
        assert_eq!(kept.pointer("/structuredContent/kept"), Some(&json!(true)));
        let lenses = workspace.query(&Body::from(
            json!({ "jsonrpc": "2.0", "id": 1_i32, "method": "textDocument/codeLens",
                "params": { "textDocument": { "uri": uri } } })
            .to_string()
            .into_bytes(),
        ));
        assert_eq!(
            lenses.pointer("/result/0/command/title"),
            Some(&json!("1 checked fill")),
            "the editor sees the one fill that checked"
        );
    }

    #[test]
    fn a_trial_ranks_fills_through_the_wire()
    {
        let (mut workspace, mut server) = editor();
        let mut connection = Connection::default();
        let uri = json!("file:///tmp/trial.gandr");
        sync(
            &mut server,
            &mut workspace,
            &opened(
                &uri,
                &json!(1_i32),
                &json!("def f : Integer ;\ndef f = missing ;\n"),
            ),
        );
        let hole = json!({ "start": { "line": 1_u32, "character": 8_u32 },
            "end": { "line": 1_u32, "character": 15_u32 } });
        let tried = call(
            &mut connection,
            &mut workspace,
            &json!("trial"),
            &json!({ "uri": uri, "range": hole, "candidates": ["\"one\"", "42"] }),
        );
        assert_eq!(tried.pointer("/isError"), Some(&json!(false)));
        assert_eq!(
            tried.pointer("/structuredContent/version"),
            Some(&json!(1_i32))
        );
        let trials = tried
            .pointer("/structuredContent/trials")
            .and_then(Value::as_array)
            .expect("the trials are listed");
        assert_eq!(
            trials
                .iter()
                .map(|trial| (
                    trial.get("candidate").cloned(),
                    trial.get("reached").cloned(),
                    trial
                        .get("diagnostics")
                        .and_then(Value::as_array)
                        .map(Vec::len)
                ))
                .collect::<Vec<_>>(),
            [
                (Some(json!(1_i32)), Some(json!("judged")), Some(0_usize)),
                (Some(json!(0_i32)), Some(json!("judged")), Some(1_usize)),
            ],
            "the fill that checks ranks first"
        );
        let whole = call(
            &mut connection,
            &mut workspace,
            &json!("trial"),
            &json!({ "uri": uri, "candidates": ["def f : Integer ;\npure 3\n"] }),
        );
        assert_eq!(
            whole.pointer("/structuredContent/trials/0/reached"),
            Some(&json!("refusedWhole")),
            "without a range a candidate is the whole text"
        );
        let too_many = alloc::vec![json!("42"); crate::tools::MOST_CANDIDATES.saturating_add(1)];
        for refused in [
            json!({ "uri": uri, "candidates": [] }),
            json!({ "uri": uri, "candidates": [42_i32] }),
            json!({ "uri": uri, "candidates": too_many }),
            json!({ "uri": uri, "candidates": ["42"], "range": "the hole" }),
        ] {
            assert_eq!(
                call(&mut connection, &mut workspace, &json!("trial"), &refused)
                    .pointer("/isError"),
                Some(&json!(true)),
                "{refused}"
            );
        }
        assert_eq!(
            call(
                &mut connection,
                &mut workspace,
                &json!("diagnostics"),
                &json!({ "uri": uri })
            )
            .pointer("/structuredContent/diagnostics")
            .and_then(Value::as_array)
            .map(Vec::len),
            Some(1_usize),
            "the trial changed nothing the editor shows"
        );
    }

    #[test]
    fn resources_name_each_documents_diagnostics()
    {
        let (mut workspace, mut server) = editor();
        let mut connection = Connection::default();
        sync(
            &mut server,
            &mut workspace,
            &opened(
                &json!("file:///tmp/mcp.gandr"),
                &json!(3_i32),
                &json!("def f = 42 ;\n"),
            ),
        );
        let listed = ask(
            &mut connection,
            &mut workspace,
            &json!({ "jsonrpc": "2.0", "id": 1_i32, "method": "resources/list" }),
        );
        assert_eq!(
            listed.pointer("/result/resources/0/uri"),
            Some(&json!("gandr:///tmp/mcp.gandr/diagnostics"))
        );
        let read = ask(
            &mut connection,
            &mut workspace,
            &json!({ "jsonrpc": "2.0", "id": 2_i32, "method": "resources/read",
            "params": { "uri": "gandr:///tmp/mcp.gandr/diagnostics" } }),
        );
        let text: Value = serde_json::from_str(
            read.pointer("/result/contents/0/text")
                .and_then(Value::as_str)
                .expect("the contents are text"),
        )
        .expect("the contents are JSON");
        assert_eq!(
            text,
            json!({ "uri": "file:///tmp/mcp.gandr", "version": 3_i32, "diagnostics": [] })
        );
        for unknown in [
            "gandr:///tmp/closed.gandr/diagnostics",
            "file:///tmp/mcp.gandr",
        ] {
            assert_eq!(
                ask(
                    &mut connection,
                    &mut workspace,
                    &json!({ "jsonrpc": "2.0", "id": 3_i32, "method": "resources/read",
                        "params": { "uri": unknown } }),
                )
                .pointer("/error/code"),
                Some(&json!(-32_602_i32))
            );
        }
    }

    #[test]
    fn subscriptions_hear_only_their_documents()
    {
        let mut workspace = Workspace::default();
        let mut connection = Connection::default();
        let first = gandr_surface_lsp::DocumentUri::from("file:///tmp/first.gandr");
        let second = gandr_surface_lsp::DocumentUri::from("file:///tmp/second.gandr");
        let subscribed = ask(
            &mut connection,
            &mut workspace,
            &json!({ "jsonrpc": "2.0", "id": 1_i32, "method": "resources/subscribe",
            "params": { "uri": "gandr:///tmp/first.gandr/diagnostics" } }),
        );
        assert_eq!(
            subscribed.pointer("/result/resultType"),
            Some(&json!("complete"))
        );
        let acknowledged = ask(
            &mut connection,
            &mut workspace,
            &json!({ "jsonrpc": "2.0", "id": 7_i32, "method": "subscriptions/listen", "params": {
            "_meta": { "io.modelcontextprotocol/protocolVersion": MODERN },
            "notifications": {
                "toolsListChanged": true,
                "resourceSubscriptions": ["gandr:///tmp/second.gandr/diagnostics", "file:///tmp/x"],
            } } }),
        );
        assert_eq!(
            acknowledged,
            json!({ "jsonrpc": "2.0", "method": "notifications/subscriptions/acknowledged",
                "params": { "_meta": { "io.modelcontextprotocol/subscriptionId": 7_i32 },
                    "notifications": { "resourceSubscriptions": ["gandr:///tmp/second.gandr/diagnostics"] } } }),
            "the acknowledgement names what the stream will hear, unsupported types omitted"
        );
        assert_eq!(connection.changed(&first), [
            json!({ "jsonrpc": "2.0", "method": "notifications/resources/updated",
                "params": { "uri": "gandr:///tmp/first.gandr/diagnostics" } })
        ]);
        assert_eq!(connection.changed(&second), [
            json!({ "jsonrpc": "2.0", "method": "notifications/resources/updated",
                "params": { "_meta": { "io.modelcontextprotocol/subscriptionId": 7_i32 },
                    "uri": "gandr:///tmp/second.gandr/diagnostics" } })
        ]);
        assert!(
            connection
                .changed(&gandr_surface_lsp::DocumentUri::from(
                    "file:///tmp/third.gandr"
                ))
                .is_empty(),
            "a document nothing follows notifies nothing"
        );
        drop(ask(
            &mut connection,
            &mut workspace,
            &json!({ "jsonrpc": "2.0", "id": 2_i32, "method": "resources/unsubscribe",
            "params": { "uri": "gandr:///tmp/first.gandr/diagnostics" } }),
        ));
        assert!(connection.changed(&first).is_empty());
        assert!(
            connection
                .handle(
                    &mut workspace,
                    &json!({ "jsonrpc": "2.0", "method": "notifications/cancelled",
                        "params": { "requestId": 7_i32 } })
                )
                .is_empty()
        );
        assert!(
            connection.changed(&second).is_empty(),
            "a cancelled stream hears nothing more"
        );
    }
}
