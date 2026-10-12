//! The tools a model calls: each reads the documents the hub holds, at the
//! version the editor last synchronised.
//!
//! A tool names its document by the URI the editor opened it under. The
//! diagnostics are the ones last published to the editor, read without a
//! recheck; the outline, the expected syntax and a declaration's type are the
//! language server's own answers to the requests an editor sends for them.

use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_surface_lsp::Body;
use gandr_surface_lsp::DocumentUri;
use gandr_surface_lsp::DocumentVersion;
use gandr_surface_lsp::Workspace;
use serde_json::Value;
use serde_json::json;

/// Why a tool call produced no result.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ToolRefusal(String);

impl fmt::Display for ToolRefusal
{
    /// Writes why, one line.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(&self.0)
    }
}

/// The schema of a tool taking a document's URI alone.
///
/// # Specification
/// trivial.
fn document_schema() -> Value
{
    json!({
        "type": "object",
        "properties": {
            "uri": { "type": "string", "description": "The document's URI, as the editor opened it" },
        },
        "required": ["uri"],
    })
}

/// The schema of a tool taking a document's URI and a position in it.
///
/// # Specification
/// trivial.
fn position_schema() -> Value
{
    json!({
        "type": "object",
        "properties": {
            "uri": { "type": "string", "description": "The document's URI, as the editor opened it" },
            "line": { "type": "integer", "minimum": 0, "description": "The zero-based line" },
            "character": {
                "type": "integer",
                "minimum": 0,
                "description": "The zero-based UTF-16 code unit on the line",
            },
        },
        "required": ["uri", "line", "character"],
    })
}

/// Every tool, in name order.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the tools are listed in strictly ascending name order, each with
///   a description and an object input schema.
/// - provides: `tools/list`, deterministic so a client caches it.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the listed names are read back in order through the wire.
/// - witness: `connection::tests::each_era_opens_and_lists_the_tools`
#[spec(ensures: |ret| ret.is_sorted_by(|earlier, later| earlier.get("name").and_then(Value::as_str)
        < later.get("name").and_then(Value::as_str))
    && ret.iter().all(|tool| tool.pointer("/inputSchema/type") == Some(&json!("object"))))]
#[must_use]
pub fn list() -> Vec<Value>
{
    let empty = json!({ "type": "object", "properties": {} });
    Vec::from([
        json!({
            "name": "diagnostics",
            "title": "Diagnostics",
            "description": "The diagnostics last published for an open document: each refusal, warning and \
                            obligation the editor shows, with its range, code and message.",
            "inputSchema": document_schema(),
        }),
        json!({
            "name": "documents",
            "title": "Open documents",
            "description": "Every document the hub holds open, with the version it is at.",
            "inputSchema": empty,
        }),
        json!({
            "name": "expected_syntax",
            "title": "Expected syntax",
            "description": "The syntax the parser expects to close the form a position ends, as snippets.",
            "inputSchema": position_schema(),
        }),
        json!({
            "name": "outline",
            "title": "Outline",
            "description": "An open document's declarations, each nested inside the one that holds it.",
            "inputSchema": document_schema(),
        }),
        json!({
            "name": "type_of",
            "title": "Type of a declaration",
            "description": "The type and documentation of the declaration whose name is at a position.",
            "inputSchema": position_schema(),
        }),
    ])
}

/// The result of calling the tool `name` with `arguments` over `workspace`.
///
/// # Specification
/// - requires: nothing; any name and arguments are admitted.
/// - ensures: a document tool answers for a document the hub holds, naming its
///   URI and the version answered at; a document the hub does not hold,
///   arguments the tool cannot read, and a name no tool has are refused.
/// - provides: `tools/call`.
/// - fails: as above, with the reason in the refusal.
/// - panics: none.
///
/// # Errors
/// [`ToolRefusal`] for an unknown tool, unreadable arguments or a document
/// the hub does not hold.
///
/// # Adequacy
/// - hypothesis: L3 — every tool is called through the wire on a held document,
///   and one on a document the hub does not hold.
/// - witness: `connection::tests::each_tool_answers_through_the_wire`
#[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(Value::is_object))]
#[inline]
pub fn call(
    workspace: &Workspace,
    name: Option<&Value>,
    arguments: &Value,
) -> Result<Value, ToolRefusal>
{
    let name = name.and_then(Value::as_str).unwrap_or_default();
    if name == "documents" {
        let documents: Vec<Value> = workspace
            .held()
            .map(|(uri, version)| json!({ "uri": uri, "version": version }))
            .collect();
        return Ok(json!({ "documents": documents }));
    }
    let (uri, version) = held(workspace, arguments)?;
    let document = json!({ "uri": uri });
    let position = || -> Result<Value, ToolRefusal> {
        match (arguments.get("line"), arguments.get("character")) {
            | (Some(line), Some(character)) if line.is_u64() && character.is_u64() => {
                Ok(json!({ "line": line, "character": character }))
            },
            | _ => Err(ToolRefusal(String::from(
                "`line` and `character` must be non-negative integers",
            ))),
        }
    };
    let answer = match name {
        | "diagnostics" => {
            let (_version, diagnostics) = workspace
                .published(&uri)
                .ok_or_else(|| ToolRefusal(String::from("the document closed")))?;
            json!({ "diagnostics": diagnostics })
        },
        | "outline" => {
            let symbols = ask(
                workspace,
                &json!({ "method": "textDocument/documentSymbol", "params": { "textDocument": document } }),
            )?;
            json!({ "symbols": symbols })
        },
        | "expected_syntax" => {
            let completions = ask(
                workspace,
                &json!({
                    "method": "textDocument/inlineCompletion",
                    "params": {
                        "textDocument": document,
                        "position": position()?,
                        "context": { "triggerKind": 2_u8 },
                    },
                }),
            )?;
            json!({ "completions": completions })
        },
        | "type_of" => {
            let hover = ask(
                workspace,
                &json!({
                    "method": "textDocument/hover",
                    "params": { "textDocument": document, "position": position()? },
                }),
            )?;
            json!({ "hover": hover })
        },
        | _ => return Err(ToolRefusal(alloc::format!("no tool is named `{name}`"))),
    };
    let mut answered = json!({ "uri": uri, "version": version });
    if let (Some(into), Value::Object(from)) = (answered.as_object_mut(), answer) {
        into.extend(from);
    }
    Ok(answered)
}

/// The document `arguments` names, and its version, when the hub holds it.
///
/// # Specification
/// trivial.
fn held(
    workspace: &Workspace,
    arguments: &Value,
) -> Result<(DocumentUri, DocumentVersion), ToolRefusal>
{
    let named = arguments
        .get("uri")
        .and_then(Value::as_str)
        .ok_or_else(|| ToolRefusal(String::from("`uri` must name a document")))?;
    let uri = DocumentUri::from(named);
    let (version, _diagnostics) = workspace
        .published(&uri)
        .ok_or_else(|| ToolRefusal(alloc::format!("`{named}` is not open in the hub")))?;
    Ok((uri, version))
}

/// The result the language server gives `call`, a method and its
/// parameters, read off `workspace`.
///
/// # Specification
/// trivial.
fn ask(
    workspace: &Workspace,
    call: &Value,
) -> Result<Value, ToolRefusal>
{
    let mut request = json!({ "jsonrpc": "2.0", "id": 0_u8 });
    if let (Some(into), Some(from)) = (request.as_object_mut(), call.as_object()) {
        into.extend(from.clone());
    }
    let answered = workspace.query(&Body::from(request.to_string().into_bytes()));
    if let Some(error) = answered.get("error") {
        return Err(ToolRefusal(
            error
                .get("message")
                .and_then(Value::as_str)
                .map_or_else(|| error.to_string(), String::from),
        ));
    }
    Ok(answered.get("result").cloned().unwrap_or(Value::Null))
}
