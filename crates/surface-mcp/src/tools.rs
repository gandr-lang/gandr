//! The tools a model calls: each reads the documents the hub holds, at the
//! version the editor last synchronised, or the features ledger.
//!
//! A tool names its document by the URI the editor opened it under. The
//! diagnostics are the ones last published to the editor, read without a
//! recheck; the outline, the expected syntax and a declaration's type are the
//! language server's own answers to the requests an editor sends for them.
//! `ledger_list` and `ledger_show` answer what `gandr ledger list` and `gandr
//! ledger show` print, read from `ledger/features.sql` under a root the call
//! names or the server's working directory, and hold no document.
//!
//! # Changes ride on every tool result
//!
//! **Choice.** Every tool result carries `changes`: the documents opened or
//! changed since this connection's previous call, with their versions, and
//! those closed. A host that never surfaces subscription notifications to its
//! model still tells the model, on its next call, that an editor moved
//! underneath it.
//!
//! **Alternatives.** Subscriptions alone reach a model only through a host that
//! forwards them; a separate `changes` tool would have to be called to be
//! useful, which a model does not know to do.
//!
//! **Reversal.** The field is dropped once the hosts in use forward resource
//! updates to their models.
//!
//! # A trial splices each candidate into the held text
//!
//! **Choice.** The `trial` tool takes up to 32 candidate texts and an optional
//! range. With a range — a hole, or a declaration's body — each candidate
//! replaces it in the document's held text, as an editor's ranged change would;
//! without one, each candidate is the whole text. The language server's
//! `Workspace::trial` judges every candidate as a fresh session would, in
//! parallel, and the results come back best first: those judged before those
//! the lowering refused whole, then fewer refused and unsettled declarations,
//! then the candidate's own position. Each result carries the diagnostics a
//! synchronisation to that text would publish. The document, its session and
//! what the editor shows are unchanged.
//!
//! **Alternatives.** Candidates as whole texts alone would make a model copy
//! the document once per candidate for a fill of a few characters. A target
//! named by a declaration rather than a range would need a resolution step from
//! name to span that the editor's range already gives. No cap would let one
//! call hold the hub's lock for as long as a model cares to send; 32 is past
//! the batch the session's measurements were taken at (8 and 16), and a batch
//! at 16 candidates across the performance cores already costs a fraction of a
//! model turn.
//!
//! **Reversal.** A model host measured to send larger batches raises the cap,
//! or moves the trial off the hub's lock onto a copy of the session; a face
//! that names holes by their goal resolves the range from the goal.
//!
//! **Proposals.** `propose` is the trial of one fill that, when it checks, is
//! kept beside the document for its editors (the language server's
//! `Workspace::propose`). A fill that does not check is answered `kept: false`
//! with its diagnostics rather than refused, so the model reads why in the same
//! call; a stale version or a document the hub does not hold is a tool error,
//! since there is nothing to show. The language server's README records what
//! checking means and how the editor shows a kept fill.

use alloc::string::String;
use alloc::string::ToString as _;
use alloc::vec::Vec;
use core::fmt;
use std::path::PathBuf;

use anodized::spec;
use gandr_surface_dispatcher::Area;
use gandr_surface_dispatcher::Feature;
use gandr_surface_dispatcher::FeatureId;
use gandr_surface_dispatcher::FeatureLedger;
use gandr_surface_dispatcher::LedgerFault;
use gandr_surface_dispatcher::Status;
use gandr_surface_lsp::Body;
use gandr_surface_lsp::ContentChange;
use gandr_surface_lsp::DocumentUri;
use gandr_surface_lsp::DocumentVersion;
use gandr_surface_lsp::Proposal;
use gandr_surface_lsp::ProposalRefusal;
use gandr_surface_lsp::Range;
use gandr_surface_lsp::Reached;
use gandr_surface_lsp::Settles;
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

/// The schema of `root`, the tree a features ledger tool reads.
///
/// # Specification
/// trivial.
fn root_schema() -> Value
{
    json!({
        "type": "string",
        "description": "The tree holding `ledger/features.sql`; the server's working directory when not given",
    })
}

/// The schema of the features ledger's list: an area, a status and a root,
/// each optional.
///
/// # Specification
/// trivial.
fn ledger_list_schema() -> Value
{
    json!({
        "type": "object",
        "properties": {
            "area": { "type": "string", "description": "Only the features in this area, such as `syntax`" },
            "status": {
                "type": "string",
                "enum": ["implemented", "partial", "planned", "declined"],
                "description": "Only the features at this status",
            },
            "root": root_schema(),
        },
    })
}

/// The schema of the features ledger's show: a feature's id and a root.
///
/// # Specification
/// trivial.
fn ledger_show_schema() -> Value
{
    json!({
        "type": "object",
        "properties": {
            "id": { "type": "string", "description": "The feature's id, as `ledger_list` names it" },
            "root": root_schema(),
        },
        "required": ["id"],
    })
}

/// The most candidates one trial judges.
pub const MOST_CANDIDATES: usize = 32;

/// The schema of the trial tool: a document's URI, its candidates and the
/// range they fill.
///
/// # Specification
/// trivial.
fn trial_schema() -> Value
{
    let position = json!({
        "type": "object",
        "properties": {
            "line": { "type": "integer", "minimum": 0_u8 },
            "character": { "type": "integer", "minimum": 0_u8 },
        },
        "required": ["line", "character"],
    });
    json!({
        "type": "object",
        "properties": {
            "uri": { "type": "string", "description": "The document's URI, as the editor opened it" },
            "candidates": {
                "type": "array",
                "items": { "type": "string" },
                "minItems": 1,
                "maxItems": MOST_CANDIDATES,
                "description": "The texts to try: each fills `range`, or is the whole document without one",
            },
            "range": {
                "type": "object",
                "description": "The span each candidate replaces, in zero-based lines and UTF-16 code units: \
                                a hole or a declaration's body",
                "properties": { "start": position, "end": position },
                "required": ["start", "end"],
            },
        },
        "required": ["uri", "candidates"],
    })
}

/// The schema of the proposal tool: a document's URI and version, the range
/// a fill replaces, the fill and what it does.
///
/// # Specification
/// trivial.
fn propose_schema() -> Value
{
    let position = json!({
        "type": "object",
        "properties": {
            "line": { "type": "integer", "minimum": 0_u8 },
            "character": { "type": "integer", "minimum": 0_u8 },
        },
        "required": ["line", "character"],
    });
    json!({
        "type": "object",
        "properties": {
            "uri": { "type": "string", "description": "The document's URI, as the editor opened it" },
            "version": { "type": "integer", "description": "The document's version the fill was made against" },
            "range": {
                "type": "object",
                "description": "The span the fill replaces, in zero-based lines and UTF-16 code units",
                "properties": { "start": position, "end": position },
                "required": ["start", "end"],
            },
            "text": { "type": "string", "description": "The fill" },
            "explanation": { "type": "string", "description": "What the fill does, shown on hover" },
        },
        "required": ["uri", "version", "range", "text"],
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
            "name": "ledger_list",
            "title": "List the features ledger",
            "description": "The features of gandr, one per row of the features ledger: its id, area, name, \
                            status (implemented, partial, planned or declined) and one sentence on what it \
                            is, narrowed to an area and a status when given. Before writing a form, list \
                            its area.",
            "inputSchema": ledger_list_schema(),
        }),
        json!({
            "name": "ledger_show",
            "title": "Show a feature",
            "description": "One feature of the features ledger: its row, each of its exemplars' gandr \
                            sources whole, whose `///` comments explain the form, and the paths of the \
                            corpus sources and tests that witness it. Show each feature a form uses \
                            before writing it.",
            "inputSchema": ledger_show_schema(),
        }),
        json!({
            "name": "outline",
            "title": "Outline",
            "description": "An open document's declarations, each nested inside the one that holds it.",
            "inputSchema": document_schema(),
        }),
        json!({
            "name": "propose",
            "title": "Propose a fill to the editor",
            "description": "Offer a fill of a range of an open document to its editors. gandr judges the \
                            document with the fill applied; a fill that leaves no error, or fewer errors \
                            than the document has, is kept and shown in the editor as ghost text, a code \
                            lens, a code action and, with an explanation, a hover note, until the document \
                            is next edited. A fill that does not check is answered with its diagnostics and \
                            never shown. `version` is the document's version the fill was made against.",
            "inputSchema": propose_schema(),
        }),
        json!({
            "name": "trial",
            "title": "Try candidate fills",
            "description": "Judge candidate edits of an open document without changing it, best first: each \
                            candidate replaces `range` when given, or the whole text otherwise. Each result \
                            names the candidate's index, how far it got (`judged`, `refusedWhole` or \
                            `faulted`) and the diagnostics the edit would publish.",
            "inputSchema": trial_schema(),
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
///   URI and the version answered at; a features ledger tool answers from the
///   ledger under its root; a document the hub does not hold, arguments the
///   tool cannot read, a ledger that cannot be read or answer, and a name no
///   tool has are refused.
/// - provides: `tools/call`.
/// - fails: as above, with the reason in the refusal.
/// - panics: none.
///
/// # Errors
/// [`ToolRefusal`] for an unknown tool, unreadable arguments, a document the
/// hub does not hold, or a features ledger fault.
///
/// # Adequacy
/// - hypothesis: L3 — every tool is called through the wire on a held document,
///   and one on a document the hub does not hold; the features ledger tools
///   list and show the committed ledger, and refuse an unknown area, status and
///   id.
/// - witness: `connection::tests::each_tool_answers_through_the_wire`
/// - witness: `connection::tests::the_ledger_tools_read_the_committed_ledger_1827`
#[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(Value::is_object))]
#[inline]
pub fn call(
    workspace: &mut Workspace,
    name: Option<&Value>,
    arguments: &Value,
) -> Result<Value, ToolRefusal>
{
    let name = name.and_then(Value::as_str).unwrap_or_default();
    match name {
        "documents" => {
            let documents: Vec<Value> = workspace
                .held()
                .map(|(uri, version)| json!({ "uri": uri, "version": version }))
                .collect();
            return Ok(json!({ "documents": documents }));
        },
        "ledger_list" => return ledger_listed(arguments),
        "ledger_show" => return ledger_shown(arguments),
        _ => {},
    }
    let (uri, version) = held(workspace, arguments)?;
    let document = json!({ "uri": uri });
    let position = || -> Result<Value, ToolRefusal> {
        match (arguments.get("line"), arguments.get("character")) {
            (Some(line), Some(character)) if line.is_u64() && character.is_u64() => {
                Ok(json!({ "line": line, "character": character }))
            },
            _ => Err(ToolRefusal(String::from(
                "`line` and `character` must be non-negative integers",
            ))),
        }
    };
    let answer = match name {
        "diagnostics" => {
            let (_version, diagnostics) = workspace
                .published(&uri)
                .ok_or_else(|| ToolRefusal(String::from("the document closed")))?;
            json!({ "diagnostics": diagnostics })
        },
        "outline" => {
            let symbols = ask(
                workspace,
                &json!({ "method": "textDocument/documentSymbol", "params": { "textDocument": document } }),
            )?;
            json!({ "symbols": symbols })
        },
        "expected_syntax" => {
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
        "type_of" => {
            let hover = ask(
                workspace,
                &json!({
                    "method": "textDocument/hover",
                    "params": { "textDocument": document, "position": position()? },
                }),
            )?;
            json!({ "hover": hover })
        },
        "trial" => json!({ "trials": tried(workspace, &uri, arguments)? }),
        "propose" => proposed(workspace, &uri, arguments)?,
        _ => return Err(ToolRefusal(alloc::format!("no tool is named `{name}`"))),
    };
    let mut answered = json!({ "uri": uri, "version": version });
    if let (Some(into), Value::Object(from)) = (answered.as_object_mut(), answer) {
        into.extend(from);
    }
    Ok(answered)
}

/// The name of a features ledger tool's argument.
#[repr(transparent)]
#[derive(Clone, Copy)]
struct Argument(&'static str);

/// The tree holding the ledger.
const ROOT: Argument = Argument("root");

/// The area a list narrows to.
const AREA: Argument = Argument("area");

/// The status a list narrows to.
const STATUS: Argument = Argument("status");

/// The feature a show names.
const ID: Argument = Argument("id");

/// The string `argument` of `arguments`, when given.
///
/// # Specification
/// trivial.
fn text(
    arguments: &Value,
    argument: Argument,
) -> Result<Option<String>, ToolRefusal>
{
    match arguments.get(argument.0) {
        None | Some(&Value::Null) => Ok(None),
        Some(&Value::String(ref text)) => Ok(Some(text.clone())),
        Some(_) => Err(ToolRefusal(alloc::format!(
            "`{}` must be a string",
            argument.0
        ))),
    }
}

/// The features ledger under the root `arguments` names, or the server's
/// working directory.
///
/// # Specification
/// trivial.
fn ledger(arguments: &Value) -> Result<FeatureLedger, ToolRefusal>
{
    let root = text(arguments, ROOT)?.map_or_else(|| PathBuf::from("."), PathBuf::from);
    FeatureLedger::read(&root).map_err(|fault| refused(&fault))
}

/// A features ledger fault, as the refusal a tool answers.
///
/// # Specification
/// trivial.
fn refused(fault: &LedgerFault) -> ToolRefusal
{
    ToolRefusal(fault.to_string())
}

/// The features `arguments` narrows the ledger to, as JSON.
///
/// # Specification
/// - requires: nothing; any arguments are admitted.
/// - ensures: `features`, one object per feature of the ledger under the root
///   in the area and at the status named, each where named, in the ledger's
///   order.
/// - provides: the `ledger_list` tool, answering what `gandr ledger list`
///   prints.
/// - fails: an argument that is not a string, a status of no spelling, an area
///   no feature is in, or a ledger that cannot be read.
/// - panics: none.
///
/// # Errors
/// [`ToolRefusal`] naming the argument or the ledger's fault.
///
/// # Adequacy
/// - hypothesis: L3 — the committed ledger lists narrowed to an area and a
///   status through the wire, and an unknown area and status are refused.
/// - witness: `connection::tests::the_ledger_tools_read_the_committed_ledger_1827`
#[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|answer|
    answer.get("features").is_some_and(Value::is_array)))]
fn ledger_listed(arguments: &Value) -> Result<Value, ToolRefusal>
{
    let area = text(arguments, AREA)?.map(Area);
    let status = text(arguments, STATUS)?
        .map(|spelling| spelling.parse::<Status>())
        .transpose()
        .map_err(|fault| refused(&fault))?;
    let features: Vec<Value> = ledger(arguments)?
        .listed(area.as_ref(), status)
        .map_err(|fault| refused(&fault))?
        .iter()
        .map(Feature::json)
        .collect();
    Ok(json!({ "features": features }))
}

/// The feature `arguments` names, with its exemplars' sources and its corpus
/// paths, as JSON.
///
/// # Specification
/// - requires: nothing; any arguments are admitted.
/// - ensures: `feature`, the row's object; `exemplars`, each `{path, source}`;
///   `corpus`, its paths — what `gandr ledger show` prints.
/// - provides: the `ledger_show` tool.
/// - fails: no `id` string, an id no feature has, an exemplar that cannot be
///   read, or a ledger that cannot be read.
/// - panics: none.
///
/// # Errors
/// [`ToolRefusal`] naming the argument or the ledger's fault.
///
/// # Adequacy
/// - hypothesis: L3 — a committed feature shows its row and corpus through the
///   wire, and a missing and an unknown id are refused.
/// - witness: `connection::tests::the_ledger_tools_read_the_committed_ledger_1827`
#[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|answer|
    answer.pointer("/feature/id").and_then(Value::as_str) == arguments.get("id").and_then(Value::as_str)))]
fn ledger_shown(arguments: &Value) -> Result<Value, ToolRefusal>
{
    let id = text(arguments, ID)?
        .ok_or_else(|| ToolRefusal(String::from("`id` must name a feature")))?;
    let shown = ledger(arguments)?
        .shown(&FeatureId(id))
        .map_err(|fault| refused(&fault))?;
    Ok(shown.json())
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

/// What keeping the proposal `arguments` names over the document at `uri`
/// came to, as JSON.
///
/// # Specification
/// - requires: nothing; any arguments are admitted.
/// - ensures: a proposal that checks is kept, answered `kept: true` with its
///   trial's diagnostics; one that does not is answered `kept: false` with the
///   reason and its trial's diagnostics, and nothing is kept. A version that is
///   not the document's, a document the hub does not hold, and a version, range
///   or text that cannot be read are refused.
/// - provides: the `propose` tool.
/// - fails: as above, with the reason in the refusal.
/// - panics: none.
///
/// # Errors
/// [`ToolRefusal`] for unreadable arguments, a stale version or a document
/// the hub does not hold.
///
/// # Adequacy
/// - hypothesis: L3 — a checking fill is kept and read back through the
///   editor's lens, a failing one is answered with its diagnostics, and a stale
///   one is refused.
/// - witness: `connection::tests::a_proposal_reaches_the_editor_once_it_checks`
#[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|answer|
    answer.get("kept").is_some_and(Value::is_boolean)))]
fn proposed(
    workspace: &mut Workspace,
    uri: &DocumentUri,
    arguments: &Value,
) -> Result<Value, ToolRefusal>
{
    let version = arguments
        .get("version")
        .cloned()
        .and_then(|version| serde_json::from_value::<DocumentVersion>(version).ok())
        .ok_or_else(|| ToolRefusal(String::from("`version` must be the document's version")))?;
    let range = arguments
        .get("range")
        .cloned()
        .and_then(|range| serde_json::from_value::<Range>(range).ok())
        .ok_or_else(|| ToolRefusal(String::from("`range` must be a range")))?;
    let text = arguments
        .get("text")
        .and_then(Value::as_str)
        .map(String::from)
        .ok_or_else(|| ToolRefusal(String::from("`text` must be a text")))?;
    let explanation = arguments
        .get("explanation")
        .and_then(Value::as_str)
        .map(String::from);
    let proposal = Proposal {
        range,
        text,
        explanation,
        settles: Settles::default(),
    };
    match workspace.propose(uri, version, proposal) {
        Ok(diagnostics) => Ok(json!({ "kept": true, "diagnostics": diagnostics })),
        Err(ProposalRefusal::Unchecked { diagnostics }) => Ok(json!({
            "kept": false,
            "reason": ProposalRefusal::Unchecked { diagnostics: Vec::new() }.to_string(),
            "diagnostics": diagnostics,
        })),
        Err(refusal) => Err(ToolRefusal(refusal.to_string())),
    }
}

/// The trial of the candidates `arguments` names over the document at `uri`,
/// best first, as JSON.
///
/// # Specification
/// - requires: nothing; any arguments are admitted.
/// - ensures: one result per candidate, in the order the language server's
///   trial ranks them, each naming its index among the candidates, how far it
///   got and its diagnostics; each candidate fills `range` when one is given.
///   No candidates, more than [`MOST_CANDIDATES`], a candidate that is not a
///   string, or a range that is not one, are refused.
/// - provides: the `trial` tool.
/// - fails: as above, with the reason in the refusal.
/// - panics: none.
///
/// # Errors
/// [`ToolRefusal`] for unreadable candidates or range, or a document the hub
/// does not hold.
///
/// # Adequacy
/// - hypothesis: L3 — fills spliced over a hole are ranked through the wire,
///   and an empty batch, a non-string candidate and an oversized batch are
///   refused.
/// - witness: `connection::tests::a_trial_ranks_fills_through_the_wire`
#[spec(ensures: |ret| ret.as_ref().is_err() || ret.as_ref().is_ok_and(|trials|
    arguments.get("candidates").and_then(Value::as_array).map(Vec::len) == Some(trials.len())))]
fn tried(
    workspace: &Workspace,
    uri: &DocumentUri,
    arguments: &Value,
) -> Result<Vec<Value>, ToolRefusal>
{
    let candidates = arguments
        .get("candidates")
        .and_then(Value::as_array)
        .filter(|candidates| (1_usize ..= MOST_CANDIDATES).contains(&candidates.len()))
        .ok_or_else(|| {
            ToolRefusal(alloc::format!(
                "`candidates` must be an array of 1 to {MOST_CANDIDATES} texts"
            ))
        })?;
    let range = arguments.get("range").cloned().unwrap_or(Value::Null);
    let changes = candidates
        .iter()
        .map(|candidate| {
            if !candidate.is_string() {
                return Err(ToolRefusal(String::from("each candidate must be a text")));
            }
            serde_json::from_value::<ContentChange>(json!({ "range": range, "text": candidate }))
                .map_err(|error| ToolRefusal(alloc::format!("`range` is not a range: {error}")))
        })
        .collect::<Result<Vec<ContentChange>, ToolRefusal>>()?;
    let (_version, trials) = workspace
        .trial(uri, &changes)
        .ok_or_else(|| ToolRefusal(String::from("the document closed")))?;
    Ok(trials
        .into_iter()
        .map(|tried| {
            json!({
                "candidate": usize::from(tried.candidate),
                "reached": match tried.reached {
                    | Reached::Judged => "judged",
                    | Reached::RefusedWhole => "refusedWhole",
                    | Reached::Faulted => "faulted",
                },
                "diagnostics": tried.diagnostics,
            })
        })
        .collect())
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
