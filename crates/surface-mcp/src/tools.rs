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
use gandr_surface_ledger::Area;
use gandr_surface_ledger::Feature;
use gandr_surface_ledger::FeatureId;
use gandr_surface_ledger::FeatureLedger;
use gandr_surface_ledger::LedgerFault;
use gandr_surface_ledger::Status;
use gandr_surface_lsp::Body;
use gandr_surface_lsp::ContentChange;
use gandr_surface_lsp::DocumentUri;
use gandr_surface_lsp::DocumentVersion;
use gandr_surface_lsp::Position;
use gandr_surface_lsp::Prepared;
use gandr_surface_lsp::Proposal;
use gandr_surface_lsp::ProposalRefusal;
use gandr_surface_lsp::Range;
use gandr_surface_lsp::Reached;
use gandr_surface_lsp::Settles;
use gandr_surface_lsp::Workspace;
use serde::Deserialize;
use serde::Serialize;
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

/// The schema of a subscription to a declaration's account: a document's URI
/// and the name of a declaration in it.
///
/// # Specification
/// trivial.
fn account_schema() -> Value
{
    json!({
        "type": "object",
        "properties": {
            "uri": { "type": "string", "description": "The document's URI, as the editor opened it" },
            "declaration": { "type": "string", "description": "The name of a declaration of the document" },
        },
        "required": ["uri", "declaration"],
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

/// The schema of a tool that takes no argument.
///
/// # Specification
/// trivial.
fn empty_schema() -> Value
{
    json!({ "type": "object", "properties": {} })
}

/// The schema of `check` and `test`: the paths that the verb walks.
///
/// # Specification
/// trivial.
fn paths_schema() -> Value
{
    json!({
        "type": "object",
        "properties": {
            "paths": {
                "type": "array",
                "items": { "type": "string" },
                "minItems": 1,
                "description": "Each path to walk: a package's directory, a directory of sources or a \
                                source, relative to the hub's working directory",
            },
        },
        "required": ["paths"],
    })
}

/// The schema of `run`: a document's URI and the name of the declaration to
/// run.
///
/// # Specification
/// trivial.
fn run_schema() -> Value
{
    json!({
        "type": "object",
        "properties": {
            "uri": { "type": "string", "description": "The document's URI, as the editor opened it" },
            "entry": { "type": "string", "description": "The declaration to run, which takes no argument" },
        },
        "required": ["uri", "entry"],
    })
}

/// The position that `arguments` names, as the language server reads one.
///
/// # Specification
/// trivial.
fn position(arguments: &Value) -> Result<Value, ToolRefusal>
{
    match (arguments.get("line"), arguments.get("character")) {
        (Some(line), Some(character)) if line.is_u64() && character.is_u64() => {
            Ok(json!({ "line": line, "character": character }))
        },
        _ => Err(ToolRefusal(String::from(
            "`line` and `character` must be non-negative integers",
        ))),
    }
}

/// What a subscription follows: the bus scope that a subscription operation
/// names.
#[derive(Clone, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Scope
{
    /// The frame of one document: its diagnostic and goal cards.
    Diagnostics(DocumentUri),
    /// The account card of the declaration of one document that has the name
    /// `declaration`.
    Account
    {
        /// The document.
        document: DocumentUri,
        /// The name of the declaration.
        declaration: String,
    },
    /// The work ledger of the hub: the tasks that each core of its pool runs,
    /// as the hub folds the activity ring.
    Activity,
}

/// What a long operation runs: a verb over paths, the kernel's admission of
/// the revision of a document, or a declaration of a document.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Job
{
    /// `gandr check` of each path.
    Check(Vec<PathBuf>),
    /// `gandr test` of each path.
    Test(Vec<PathBuf>),
    /// The kernel's admission of the revision of a document that the hub
    /// holds.
    Replay(DocumentUri),
    /// The run of the declaration `entry` of a document that the hub holds, as
    /// the run lens of the document runs it.
    Run
    {
        /// The document.
        document: DocumentUri,
        /// The name of the declaration.
        entry: String,
    },
}

/// What answers an operation over the hub.
#[derive(Clone, Copy)]
enum Answer
{
    /// An answer that names no document: from the documents that the hub
    /// holds, or from the features ledger.
    Hub(fn(&mut Workspace, &Value) -> Result<Value, ToolRefusal>),
    /// An answer over one document that the hub holds. The call writes the
    /// URI of the document and the version it answered at beside it.
    Document(fn(&mut Workspace, &DocumentUri, &Value) -> Result<Value, ToolRefusal>),
    /// A subscription: the scope that the call follows, which may name a
    /// document that the hub does not hold now. The Reactive Agent Protocol
    /// toolset opens it, and the Model Context Protocol face does not offer it.
    Subscription(fn(&Value) -> Result<Scope, ToolRefusal>),
    /// A long operation: the job that the call runs. The Reactive Agent
    /// Protocol toolset runs it and answers by a callback when it ends, and the
    /// Model Context Protocol face does not offer it.
    Job(fn(&Value) -> Result<Job, ToolRefusal>),
}

/// One operation of the hub, as each face offers it.
struct Operation
{
    /// The name that a client calls it by.
    name: &'static str,
    /// The title that the Model Context Protocol shows. A tool of the
    /// Reactive Agent Protocol has no title.
    title: &'static str,
    /// What the operation answers.
    description: &'static str,
    /// The JSON Schema of its arguments.
    schema: fn() -> Value,
    /// What answers it.
    answer: Answer,
}

/// Every operation of the hub, in ascending name order. The Model Context
/// Protocol's `tools/list` and the Reactive Agent Protocol's manifest each
/// encode this table, and both faces call through it. Thus a row added here
/// reaches both faces, except a subscription and a long operation, which the
/// toolset alone serves. The hub's build with the `instrument` feature adds
/// `subscribe_activity`.
static OPERATIONS: [Operation; if cfg!(feature = "instrument") { 16 } else { 15 }] = [
    Operation {
        name: "check",
        title: "Check",
        description: "Check each path as `gandr check` does: a package's directory, a directory of \
                      sources or a source. The result arrives when the check ends. Its text is the \
                      verdict line, and its display holds each diagnostic snippet and the report. \
                      While the check runs, each tick of the hub's work ledger arrives as a view \
                      update of the type `activity`. A newer revision of a document that the hub \
                      holds under a path retires the check.",
        schema: paths_schema,
        answer: Answer::Job(|arguments| Ok(Job::Check(paths(arguments)?))),
    },
    Operation {
        name: "diagnostics",
        title: "Diagnostics",
        description: "The diagnostics last published for an open document: each refusal, warning and \
                      obligation the editor shows, with its range, code and message.",
        schema: document_schema,
        answer: Answer::Document(|workspace, uri, _arguments| {
            let (_version, diagnostics) = workspace
                .published(uri)
                .ok_or_else(|| ToolRefusal(String::from("the document closed")))?;
            Ok(json!({ "diagnostics": diagnostics }))
        }),
    },
    Operation {
        name: "documents",
        title: "Open documents",
        description: "Every document the hub holds open, with the version it is at.",
        schema: empty_schema,
        answer: Answer::Hub(|workspace, _arguments| {
            let documents: Vec<Value> = workspace
                .held()
                .map(|(uri, version)| json!({ "uri": uri, "version": version }))
                .collect();
            Ok(json!({ "documents": documents }))
        }),
    },
    Operation {
        name: "expected_syntax",
        title: "Expected syntax",
        description: "The syntax the parser expects to close the form a position ends, as snippets.",
        schema: position_schema,
        answer: Answer::Document(|workspace, uri, arguments| {
            let completions = ask(
                workspace,
                &json!({
                    "method": "textDocument/inlineCompletion",
                    "params": {
                        "textDocument": { "uri": uri },
                        "position": position(arguments)?,
                        "context": { "triggerKind": 2_u8 },
                    },
                }),
            )?;
            Ok(json!({ "completions": completions }))
        }),
    },
    Operation {
        name: "ledger_list",
        title: "List the features ledger",
        description: "The features of gandr, one per row of the features ledger: its id, area, name, \
                      status (implemented, partial, planned or declined) and one sentence on what it \
                      is, narrowed to an area and a status when given. Before writing a form, list \
                      its area.",
        schema: ledger_list_schema,
        answer: Answer::Hub(|_workspace, arguments| ledger_listed(arguments)),
    },
    Operation {
        name: "ledger_show",
        title: "Show a feature",
        description: "One feature of the features ledger: its row, each of its exemplars' gandr \
                      sources whole, whose `///` comments explain the form, and the paths of the \
                      corpus sources and tests that witness it. Show each feature a form uses \
                      before writing it.",
        schema: ledger_show_schema,
        answer: Answer::Hub(|_workspace, arguments| ledger_shown(arguments)),
    },
    Operation {
        name: "outline",
        title: "Outline",
        description: "An open document's declarations, each nested inside the one that holds it.",
        schema: document_schema,
        answer: Answer::Document(|workspace, uri, _arguments| {
            let symbols = ask(
                workspace,
                &json!({ "method": "textDocument/documentSymbol", "params": { "textDocument": { "uri": uri } } }),
            )?;
            Ok(json!({ "symbols": symbols }))
        }),
    },
    Operation {
        name: "propose",
        title: "Propose a fill to the editor",
        description: "Offer a fill of a range of an open document to its editors. gandr judges the \
                      document with the fill applied; a fill that leaves no error, or fewer errors \
                      than the document has, is kept and shown in the editor as ghost text, a code \
                      lens, a code action and, with an explanation, a hover note, until the document \
                      is next edited. A fill that does not check is answered with its diagnostics and \
                      never shown. `version` is the document's version the fill was made against.",
        schema: propose_schema,
        answer: Answer::Document(proposed),
    },
    Operation {
        name: "replay",
        title: "Replay",
        description: "The kernel's admission of the revision of an open document that the hub holds \
                      now. The result arrives when the admission ends. Its text counts the \
                      declarations by the kernel's warrant, and its display holds the kernel's title \
                      of each declaration. A newer revision of the document retires the replay.",
        schema: document_schema,
        answer: Answer::Job(|arguments| Ok(Job::Replay(named(arguments)?))),
    },
    Operation {
        name: "run",
        title: "Run",
        description: "Run the declaration `entry` of an open document, as its run lens runs it: a \
                      declaration that takes no argument. The result arrives when the run ends. Its \
                      text and its display are the line that `gandr run` prints.",
        schema: run_schema,
        answer: Answer::Job(|arguments| {
            let entry = arguments
                .get("entry")
                .and_then(Value::as_str)
                .ok_or_else(|| ToolRefusal(String::from("`entry` must name a declaration")))?;
            Ok(Job::Run {
                document: named(arguments)?,
                entry: String::from(entry),
            })
        }),
    },
    Operation {
        name: "subscribe_account",
        title: "Follow a declaration's account",
        description: "Follow the account card of the declaration of a document that has the name \
                      `declaration`. After each admission that changes the card, one event carries \
                      the card, or null once no declaration has the name. The card holds the \
                      checker's verdict and the kernel's warrant and title.",
        schema: account_schema,
        answer: Answer::Subscription(|arguments| {
            let declaration = arguments
                .get("declaration")
                .and_then(Value::as_str)
                .ok_or_else(|| {
                    ToolRefusal(String::from("`declaration` must name a declaration"))
                })?;
            Ok(Scope::Account {
                document: named(arguments)?,
                declaration: String::from(declaration),
            })
        }),
    },
    #[cfg(feature = "instrument")]
    Operation {
        name: "subscribe_activity",
        title: "Follow the work ledger",
        description: "Follow the work of the hub's pool: which task each core runs, and when the \
                      task starts and ends. Each event carries the tasks since the last event that \
                      the runtime took, the count of the tasks it dropped while the runtime was slow, \
                      and the busy time of each core over the last two seconds.",
        schema: empty_schema,
        answer: Answer::Subscription(|_arguments| Ok(Scope::Activity)),
    },
    Operation {
        name: "subscribe_diagnostics",
        title: "Follow a document's diagnostics",
        description: "Follow the diagnostics of a document. After each publication that changes its \
                      frame, one event carries the frame: the document's version, and its diagnostic \
                      and goal cards.",
        schema: document_schema,
        answer: Answer::Subscription(|arguments| Ok(Scope::Diagnostics(named(arguments)?))),
    },
    Operation {
        name: "test",
        title: "Test",
        description: "Test each path as `gandr test` does: each fixture settles and each pending \
                      source is refused. The result arrives when the test ends. Its text is the \
                      verdict line, and its display holds each line that the test prints. While the \
                      test runs, each tick of the hub's work ledger arrives as a view update of the \
                      type `activity`. A newer revision of a document that the hub holds under a \
                      path retires the test.",
        schema: paths_schema,
        answer: Answer::Job(|arguments| Ok(Job::Test(paths(arguments)?))),
    },
    Operation {
        name: "trial",
        title: "Try candidate fills",
        description: "Judge candidate edits of an open document without changing it, best first: each \
                      candidate replaces `range` when given, or the whole text otherwise. Each result \
                      names the candidate's index, how far it got (`judged`, `refusedWhole` or \
                      `faulted`) and the diagnostics the edit would publish.",
        schema: trial_schema,
        answer: Answer::Document(|workspace, uri, arguments| {
            Ok(json!({ "trials": tried(workspace, uri, arguments)? }))
        }),
    },
    Operation {
        name: "type_of",
        title: "Type of a declaration",
        description: "The type and documentation of the declaration whose name is at a position.",
        schema: position_schema,
        answer: Answer::Document(|workspace, uri, arguments| {
            let hover = ask(
                workspace,
                &json!({
                    "method": "textDocument/hover",
                    "params": { "textDocument": { "uri": uri }, "position": position(arguments)? },
                }),
            )?;
            Ok(json!({ "hover": hover }))
        }),
    },
];

/// Every tool that the Model Context Protocol face offers, in name order, as
/// its `tools/list` encodes the table: its name, title, description and input
/// schema. A subscription and a long operation are not offered, because the
/// face has no callback for their events or their results.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the tools are listed in strictly ascending name order, each with
///   a description and an object input schema, and no subscription and no long
///   operation is listed.
/// - provides: `tools/list`, deterministic so a client caches it.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the listed names are read back in order through the wire.
/// - witness: `connection::tests::each_era_opens_and_lists_the_tools`
#[spec(ensures: |ret| ret.is_sorted_by(|earlier, later| earlier.get("name").and_then(Value::as_str)
        < later.get("name").and_then(Value::as_str))
    && ret.iter().all(|tool| tool.pointer("/inputSchema/type") == Some(&json!("object"))
        && tool.get("name").and_then(Value::as_str).is_some_and(|name| !name.starts_with("subscribe_"))))]
#[must_use]
pub fn list() -> Vec<Value>
{
    OPERATIONS
        .iter()
        .filter(|operation| matches!(operation.answer, Answer::Hub(_) | Answer::Document(_)))
        .map(|operation| {
            json!({
                "name": operation.name,
                "title": operation.title,
                "description": operation.description,
                "inputSchema": (operation.schema)(),
            })
        })
        .collect()
}

/// Every tool, in name order, as the Reactive Agent Protocol's manifest
/// encodes the table: its name, description and input schema.
///
/// # Specification
/// - requires: nothing.
/// - ensures: every row of the table is offered in name order, each with the
///   name, the description and the input schema that [`list`] gives it, and no
///   title. The subscriptions and the long operations are offered too.
/// - provides: the tools of the manifest at `/.well-known/rap-toolset`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the manifest that the toolset serves and the `tools/list`
///   that the hub's socket answers name the same operations with the same
///   schemas.
/// - witness: `rap::tests::both_faces_offer_one_table`
#[spec(ensures: |ret| ret.len() == OPERATIONS.len()
    && ret.iter().all(|tool| tool.get("title").is_none()))]
#[must_use]
pub fn offered() -> Vec<Value>
{
    OPERATIONS
        .iter()
        .map(|operation| {
            json!({
                "name": operation.name,
                "description": operation.description,
                "inputSchema": (operation.schema)(),
            })
        })
        .collect()
}

/// The result of calling the tool `name` with `arguments` over `workspace`.
///
/// # Specification
/// - requires: nothing; any name and arguments are admitted.
/// - ensures: a document tool answers for a document the hub holds, naming its
///   URI and the version answered at; a features ledger tool answers from the
///   ledger under its root; a name no tool has, a subscription, a long
///   operation, a document the hub does not hold, arguments the tool cannot
///   read, and a ledger that cannot be read or answer are refused.
/// - provides: `tools/call`, and the invocations of the Reactive Agent
///   Protocol's toolset that open no subscription and run no job.
/// - fails: as above, with the reason in the refusal.
/// - panics: none.
///
/// # Errors
/// [`ToolRefusal`] for an unknown tool, a subscription, a long operation,
/// unreadable arguments, a document the hub does not hold, or a features
/// ledger fault.
///
/// # Adequacy
/// - hypothesis: L3 — every tool is called through the wire on a held document,
///   and one on a document the hub does not hold; the features ledger tools
///   list and show the committed ledger, and refuse an unknown area, status and
///   id. A subscription is refused.
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
    let operation = OPERATIONS
        .binary_search_by(|operation| operation.name.cmp(name))
        .ok()
        .and_then(|row| OPERATIONS.get(row))
        .ok_or_else(|| ToolRefusal(alloc::format!("no tool is named `{name}`")))?;
    match operation.answer {
        Answer::Hub(answer) => answer(workspace, arguments),
        Answer::Document(answer) => {
            let (uri, version) = held(workspace, arguments)?;
            let answer = answer(workspace, &uri, arguments)?;
            let mut answered = json!({ "uri": uri, "version": version });
            if let (Some(into), Value::Object(from)) = (answered.as_object_mut(), answer) {
                into.extend(from);
            }
            Ok(answered)
        },
        Answer::Subscription(_) => Err(ToolRefusal(alloc::format!(
            "`{name}` opens a subscription, which the Reactive Agent Protocol toolset serves"
        ))),
        Answer::Job(_) => Err(ToolRefusal(alloc::format!(
            "`{name}` is a long operation, which answers by a callback that the Reactive Agent \
             Protocol toolset serves"
        ))),
    }
}

/// The job that the long operation `name` runs with `arguments`, or `None`
/// when `name` names no long operation.
///
/// # Specification
/// - requires: nothing; any name and arguments are admitted.
/// - ensures: `None` for a name that names no long operation of the table.
///   Otherwise the job of the row, or the refusal of arguments that the row
///   cannot read. The document of a replay or a run need not be open in the
///   hub, and a path need not exist.
/// - provides: what the toolset starts a job on.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — through a running hub, `check` and `test` walk their
///   paths, `replay` answers the admission of a revision, and `run` answers the
///   line of a declaration's run.
/// - witness: `rap::tests::a_long_operation_answers_when_its_job_ends`
/// - witness: `rap::tests::a_newer_revision_retires_a_check_or_a_run_and_a_cancel_ends_a_job_6940`
#[spec(ensures: |ret| ret.is_none() || name.as_str().is_some_and(|named| matches!(named, "check" | "replay" | "run" | "test")))]
#[inline]
pub fn job(
    name: &Value,
    arguments: &Value,
) -> Option<Result<Job, ToolRefusal>>
{
    let name = name.as_str()?;
    let operation = OPERATIONS
        .binary_search_by(|operation| operation.name.cmp(name))
        .ok()
        .and_then(|row| OPERATIONS.get(row))?;
    match operation.answer {
        Answer::Job(job) => Some(job(arguments)),
        Answer::Hub(_) | Answer::Document(_) | Answer::Subscription(_) => None,
    }
}

/// The paths that `arguments` names: one string or more.
///
/// # Specification
/// trivial.
fn paths(arguments: &Value) -> Result<Vec<PathBuf>, ToolRefusal>
{
    let refused = || ToolRefusal(String::from("`paths` must name one path or more"));
    let paths = arguments
        .get("paths")
        .and_then(Value::as_array)
        .filter(|paths| !paths.is_empty())
        .ok_or_else(refused)?;
    paths
        .iter()
        .map(|path| path.as_str().map(PathBuf::from).ok_or_else(refused))
        .collect()
}

/// The scope that the subscription `name` opens with `arguments`, or `None`
/// when `name` names no subscription.
///
/// # Specification
/// - requires: nothing; any name and arguments are admitted.
/// - ensures: `None` for a name that names no subscription of the table, such
///   as `subscribe_activity` in a build without the `instrument` feature. The
///   name of each subscription starts with `subscribe_`. Otherwise the scope of
///   the row, or the refusal of arguments that the row cannot read. The
///   document need not be open in the hub.
/// - provides: what the toolset's worker opens a subscription on.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — through a running hub, `subscribe_diagnostics`,
///   `subscribe_account` and `subscribe_activity` confirm with their scopes,
///   and their events follow.
/// - witness: `rap::tests::a_subscription_hears_each_new_frame`
/// - witness: `rap::tests::an_account_subscription_outlives_a_restart_of_the_hub`
/// - witness: `rap::tests::an_activity_subscription_hears_each_task_until_it_ends_6509`
#[spec(ensures: |ret| ret.is_none() || name.as_str().is_some_and(|named| named.starts_with("subscribe_")))]
#[inline]
pub fn subscription(
    name: &Value,
    arguments: &Value,
) -> Option<Result<Scope, ToolRefusal>>
{
    let name = name.as_str()?;
    let operation = OPERATIONS
        .binary_search_by(|operation| operation.name.cmp(name))
        .ok()
        .and_then(|row| OPERATIONS.get(row))?;
    match operation.answer {
        Answer::Subscription(scope) => Some(scope(arguments)),
        Answer::Hub(_) | Answer::Document(_) | Answer::Job(_) => None,
    }
}

/// The document that `arguments` names by its `uri`, whether or not the hub
/// holds it.
///
/// # Specification
/// trivial.
fn named(arguments: &Value) -> Result<DocumentUri, ToolRefusal>
{
    arguments
        .get("uri")
        .and_then(Value::as_str)
        .map(DocumentUri::from)
        .ok_or_else(|| ToolRefusal(String::from("`uri` must name a document")))
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
pub fn held(
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

/// What a run of the declaration `entry` of `document` reads, as the run lens
/// of the document runs it: the first declaration of the outline in
/// depth-first order that has the name. [`Prepared::run`] then runs it with no
/// lock of the workspace.
///
/// # Specification
/// - requires: nothing; any document and name are admitted.
/// - ensures: what [`Workspace::prepared`] takes for the position of the name,
///   whose run gives the line that the run lens shows. A document that the hub
///   does not hold, a name that no declaration has, and a declaration that does
///   not run are refused.
/// - provides: the `run` job of the toolset, which holds the lock of the
///   workspace for this call alone.
/// - fails: as above, with the reason in the refusal.
/// - panics: none.
/// - executable: none — the run is what the line comes from, and only the run
///   computes it.
///
/// # Errors
/// [`ToolRefusal`] for a document that the hub does not hold, an unknown name,
/// or a declaration that does not run.
///
/// # Adequacy
/// - hypothesis: L3 — through a running hub, a value runs to its line, and a
///   name that no declaration has is refused.
/// - witness: `rap::tests::a_long_operation_answers_when_its_job_ends`
#[inline]
pub fn prepared(
    workspace: &Workspace,
    (document, entry): (&DocumentUri, &String),
) -> Result<Prepared, ToolRefusal>
{
    let symbols = ask(
        workspace,
        &json!({ "method": "textDocument/documentSymbol", "params": { "textDocument": { "uri": document } } }),
    )?;
    let mut unvisited: Vec<&Value> = symbols
        .as_array()
        .map(|top| top.iter().rev().collect())
        .unwrap_or_default();
    let mut position = None;
    while let Some(symbol) = unvisited.pop() {
        if symbol.get("name").and_then(Value::as_str) == Some(entry.as_str()) {
            position = symbol.pointer("/selectionRange/start");
            break;
        }
        if let Some(children) = symbol.get("children").and_then(Value::as_array) {
            unvisited.extend(children.iter().rev());
        }
    }
    let position = position.ok_or_else(|| {
        ToolRefusal(alloc::format!(
            "no declaration of {document} is named `{entry}`"
        ))
    })?;
    let position = Position::deserialize(position)
        .map_err(|error| ToolRefusal(alloc::format!("the outline's position: {error}")))?;
    workspace
        .prepared(document, position)
        .map_err(|unran| ToolRefusal(unran.to_string()))
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
