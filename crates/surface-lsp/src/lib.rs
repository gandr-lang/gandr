//! **The language server**: diagnostics, semantic tokens, inline completion,
//! the document's outline, hover and formatting over the Language Server
//! Protocol, served over any pair of byte streams.
//!
//! # Every synchronisation submits the document to its session
//!
//! Each open document holds a session. A synchronisation applies the
//! client's changes to the held text — a ranged change replaces its range, a
//! change naming none the whole text — and submits the text to the session,
//! whose form store molds only the forms the change touched; the submission
//! is the dispatcher's composition of the whole text. The server publishes,
//! as editor diagnostics, the reports the diagnostics renderer gives that
//! step: the same reports, at the same spans, under the same refusal names
//! `gandr check --goals` prints, less any diagnostic of the form the caret is
//! writing, which waits until the caret leaves the form, the form's
//! terminator arrives or the document is quiet (the `quiet` module states the
//! hold and its trade). Each synchronisation logs one line: the forms molded,
//! the items the incremental checker judged, and the wall. A token request
//! highlights the document whole through the grammar's role table,
//! the same classification a terminal face styles. An inline-completion
//! request molds the form the cursor is in up to the cursor and answers, as
//! ranked snippets, the ways the parser's completion query offers to go on
//! from there, less what is already written after the cursor. An outline
//! request reads the document's declarations, its multi-line forms or the
//! forms around a position off its parsed tree. A hover answers the innermost
//! node under the cursor with its type: a declaration's name its declared
//! type and documentation, a binder the type its uses were judged at, a term
//! its type (and the type it was checked against when the two differ), a
//! written type its universe, and any other position in a declaration's head
//! that declaration. The types come from a typed run over the document's
//! text, built at the first hover after an edit and kept until the next: its
//! entries are the nodes the run judged, the binders their uses resolve to,
//! the written types it formed, and the members of `theory` blocks and `data`
//! families at the types the description route states for them. Each type is
//! spelled in the form the editor's `gandr.presentation.form` names, the
//! sugared one unless it names the explicit one, and every construct with a
//! glyph in the spelling its `gandr.presentation.spelling` names, `unicode` or
//! `ascii`, the user's configured spelling (the [`Spelling`] [`serve`] and
//! `run_hub` are given) unless it names one; the same setting spells the types
//! its diagnostics name, and changing it republishes them. A client whose
//! markdown renderer keeps HTML reads every piece of gandr text a hover shows
//! coloured by the roles its semantic tokens carry, as the `markup` module
//! states, with the decision, its alternatives and its reversal.
//! A formatting request lays the document out through `gandr-surface-format`
//! and answers the edits that turn the held text into that layout: one
//! trimmed edit for the whole document, or one per top-level form a range
//! touches. Positions are counted in UTF-16 code units through the renderer
//! seam's line index.
//!
//! # The transport is the base protocol, written here
//!
//! A frame is a `Content-Length` header block and a JSON-RPC 2.0 body;
//! [`serve`] reads frames from one stream, handles each, writes every answer
//! and notification to the other, and every timing line to the log, until
//! `exit`. [`Capabilities`] is what `initialize` answers, for a client that
//! reads it before starting a session.
//!
//! # One hub serves a workspace's clients
//!
//! On Unix, `run_hub` serves every connection a socket accepts over one
//! workspace: each connection holds its own copy of every document it opens
//! and is answered for it, and the other faces read the copy that synchronised
//! last. `socket_for` names a workspace's socket, `bind` claims it unless
//! another hub serves it, and `relay` carries a client's streams to the hub
//! and back.
//!
//! # Example
//!
//! ```
//! use std::io::Cursor;
//!
//! use gandr_surface_lsp::Body;
//! use gandr_surface_lsp::Served;
//! use gandr_surface_lsp::Spelling;
//! use gandr_surface_lsp::serve;
//! use gandr_surface_lsp::write_frame;
//!
//! let mut input = Vec::new();
//! for message in [
//!     r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#,
//!     r#"{"jsonrpc":"2.0","id":2,"method":"shutdown"}"#,
//!     r#"{"jsonrpc":"2.0","method":"exit"}"#,
//! ] {
//!     write_frame(&mut input, &Body::from(message.as_bytes().to_vec()))?;
//! }
//! let mut output = Vec::new();
//! let served = serve(
//!     &mut Cursor::new(input),
//!     &mut output,
//!     &mut Vec::new(),
//!     Spelling::Unicode,
//! )?;
//! assert_eq!(
//!     served,
//!     Served::Clean,
//!     "exit after shutdown ends the session cleanly"
//! );
//! let written = String::from_utf8(output)?;
//! assert!(
//!     written.ends_with(r#"{"jsonrpc":"2.0","id":2,"result":null}"#),
//!     "{written}"
//! );
//! # Ok::<(), Box<dyn core::error::Error>>(())
//! ```
//!
//! Each decision, with the alternative it was chosen over and what would
//! reverse it, is in the module that owns it.
//!
//! # Coverage of the specification
//!
//! Every feature of the protocol, 3.17 and 3.18, with whether this server
//! serves it. Only a served feature is advertised: a capability with nothing
//! behind it would invite requests the server can only refuse.
//!
//! | Feature | Methods | State |
//! | ------- | ------- | ----- |
//! | lifecycle | `initialize`, `initialized`, `shutdown`, `exit` | served |
//! | document synchronisation | `textDocument/didOpen`, `didChange` (incremental), `didClose` | served |
//! | save notifications | `textDocument/willSave`, `willSaveWaitUntil`, `didSave` | declined: every change is judged as it arrives, so a save changes nothing the server holds |
//! | notebook synchronisation | `notebookDocument/*` | declined: gandr has no notebook format |
//! | published diagnostics | `textDocument/publishDiagnostics` | served |
//! | pulled diagnostics | `textDocument/diagnostic`, `workspace/diagnostic` | declined: every synchronisation publishes; reverses for a client that reads only pulled diagnostics |
//! | semantic tokens | `textDocument/semanticTokens/full`, `range` | served |
//! | semantic token deltas | `textDocument/semanticTokens/full/delta` | declined: a full answer per request; reverses when a measurement shows the transfer matters |
//! | inline completion | `textDocument/inlineCompletion` | served |
//! | document symbols | `textDocument/documentSymbol` | served |
//! | folding ranges | `textDocument/foldingRange` | served |
//! | selection ranges | `textDocument/selectionRange` | served |
//! | hover | `textDocument/hover` | served |
//! | inlay hints | `textDocument/inlayHint` | blocked: a face that reads each binder's type off the hover's type table, which is built on demand rather than per revision |
//! | signature help | `textDocument/signatureHelp` | blocked: a face reading the declaration a call applies off the referent index the type table keeps |
//! | completion | `textDocument/completion` | served: the binders in scope, the closure's declared names and the keywords the slot at the word's start admits, each starting with the word |
//! | definition, type definition | `textDocument/definition`, `typeDefinition` | served: what the use at the position refers to, and the families the type there names, as links when the client takes them |
//! | declaration, implementation | `textDocument/declaration`, `implementation` | declined: a signature and its definition make one declaration, which definition answers at its first form, and the core has no interfaces to implement |
//! | references, document highlight | `textDocument/references`, `documentHighlight` | blocked: the referent index read from referent to uses |
//! | rename, linked editing | `textDocument/prepareRename`, `rename`, `linkedEditingRange` | blocked: the same reverse reading |
//! | call hierarchy | `textDocument/prepareCallHierarchy`, `callHierarchy/*` | blocked: the same reverse reading |
//! | type hierarchy | `textDocument/prepareTypeHierarchy`, `typeHierarchy/*` | declined: the core has no subtyping to arrange types by |
//! | formatting | `textDocument/formatting`, `rangeFormatting` | served |
//! | on-type formatting | `textDocument/onTypeFormatting` | declined: a form's layout is decided once the form is whole, which range formatting at the cursor already serves on request |
//! | code actions, code lenses | `textDocument/codeAction`, `codeLens` | served for model proposals: a quick fix applying each checked fill, a lens counting a range's checked fills |
//! | commands | `workspace/executeCommand` | blocked: no command the pipeline produces |
//! | document links | `textDocument/documentLink` | blocked: a path import resolves to its sibling's file, which the dispatcher's `lay_out` reads, but the server answers no link request yet |
//! | document colours | `textDocument/documentColor`, `colorPresentation` | declined: gandr has no colour literals |
//! | inline values | `textDocument/inlineValue` | declined: they serve a debugger, and gandr has no debug adapter |
//! | monikers | `textDocument/moniker` | declined: no cross-repository index reads them |
//! | workspace symbols | `workspace/symbol` | blocked: a workspace of more than the open documents |
//! | workspace folders, file watching, file operations | `workspace/didChangeWorkspaceFolders`, `didChangeWatchedFiles`, `willCreateFiles` and the other file operations | blocked: a workspace of more than the open documents |
//! | configuration | `workspace/didChangeConfiguration` | served: the `gandr` section's `diagnostics.verbosity`, as the `recheck` module states, `diagnostics.quiet`, as the `quiet` module states, `presentation.form`, which every later hover reads, and `presentation.spelling`, which every later hover reads and which republishes the diagnostics |
//! | pulled configuration | `workspace/configuration` | declined: the settings are pushed; reverses for a client that only answers pulls |
//! | window messages and progress | `window/showMessage`, `logMessage`, `workDoneProgress/*` | declined: the timing line goes to the server's log; reverses for a client that reads only the protocol stream |
//! | gandr's extensions | `gandr/goals`, `gandr/syntaxTree`, `gandr/serverStatus`, the render-bus attach through the language server's stream | blocked: each as the assessment in § Extensions beyond the specification names; the bus itself is served on the hub's socket (the `bus` module) |
//!
//! # What editors add beyond the protocol
//!
//! A client speaks the protocol; what it does with a method the protocol does
//! not name decides where a gandr-specific view can live.
//!
//! | Editor | Beyond the protocol | What it means here |
//! | ------ | ------------------- | ------------------ |
//! | VS Code | an extension sends any request through its language client and draws a webview panel of its own HTML; proposed APIs are closed to published extensions | the one editor where a rich goal view is a panel; it needs an extension, and its panel reads whatever the extension fetches |
//! | Neovim | a client sends any request and installs a handler for any notification; floating windows and virtual text draw the answer | a plain-text goal request is shown with a few lines of configuration and no extension |
//! | Emacs | `eglot` and `lsp-mode` send any JSON-RPC request; a buffer draws the answer | as Neovim: a plain-text goal request suffices |
//! | Helix | the standard protocol only; no plugin system yet | sees only the specification's features, so every extension must degrade to them |
//! | Zed | extensions launch a server and label its completions and symbols | as Helix for anything beyond the specification |
//!
//! The table fixes two rules. A gandr extension answers plain, already-laid-out
//! text first, so the editors that can send a custom request show it without a
//! gandr extension of their own; a structured view rides beside it, never in
//! place of it. And nothing an editor needs to read a document correctly lives
//! only in an extension: diagnostics, goals as diagnostics, hover and tokens
//! stay in the specification, which Helix and Zed read.
//!
//! # Extensions beyond the specification
//!
//! The assessment the language server's coverage owes: the extensions three
//! servers of the closest kind add, and which gandr takes up.
//!
//! | Extension | Server | Recommendation | Why |
//! | --------- | ------ | -------------- | --- |
//! | a goal at a position: `$/lean/plainGoal`, `$/lean/plainTermGoal`; `proof/goals` | Lean 4; coq-lsp | **adopt** as `gandr/goals`: the goals the cursor's hole owes, each its expected type and its context, laid out by the printer as plain text, beside the same goals as `gandr-surface-render-remote`'s `GoalCard`s | the interaction model is holes and goals, which reach an editor only as information diagnostics; blocked with completion on goals whose types the checker spells |
//! | the infoview: `$/lean/rpc/connect`, `$/lean/rpc/call`, user widgets | Lean 4 | **decline** the RPC session; the side view reads the render bus instead | a remote-procedure session per file worker, with references a client must release and keep alive, duplicates what the render bus frames already carry: versioned goal and diagnostic cards one renderer or many read |
//! | file checking progress: `$/lean/fileProgress`; coq-lsp's progress and viewport | Lean 4; coq-lsp | **decline** | both check on demand or in order and report how far they got; every synchronisation here judges the whole document and publishes at once, and the timing line already says what it cost |
//! | syntax tree view: `rust-analyzer/viewSyntaxTree` | rust-analyzer | **adopt** as `gandr/syntaxTree`: the molded tree of a document, its molds, tiles, layout and repairs, as text | the tree exists for every request already, and grammar and parser work reads it; a debugging aid, advertised as one |
//! | snippet text edits | rust-analyzer | **adopt** with code actions: a repair the parser recorded becomes a fix whose holes are tab stops | inline completion already writes snippets, and code actions are served for model proposals; waits on the parser's repairs becoming fixes |
//! | runnables: `experimental/runnables` | rust-analyzer | **decline** the method; a code lens over each declaration that evaluates, running it as `gandr run` does, once commands exist | the specification's lenses and commands carry it, so Helix and Zed see it too |
//! | hover actions | rust-analyzer | **decline** until references exist | its actions are go-to and find-references links, and find-references waits on the referent index read in reverse |
//! | matching brace: `experimental/matchingBrace` | rust-analyzer | **decline** | selection ranges already grow from a tile to its form, and the client matches brackets itself |
//! | join lines: `experimental/joinLines`; on enter | rust-analyzer | **decline** | layout belongs to the source formatter, which formatting serves |
//! | server status: `experimental/serverStatus` | rust-analyzer | **adopt** as `gandr/serverStatus`: whether the latest revision's kernel admission is pending, done or refused | the admission runs after the diagnostics are published, and an editor cannot otherwise tell a revision the kernel has yet to admit from one it admitted |
//!
//! **The goal view is both.** `gandr/goals` is the portable answer: plain text
//! any client that sends a custom request shows, and the structured cards a
//! richer one draws. The live side view, which follows the cursor and the
//! check, reads the render bus: a terminal pane beside the editor reads its
//! frames directly, and a VS Code webview attaches to the same frames through
//! the language server's render-bus attach, so the cards a goal view draws are
//! the ones every renderer draws. An extension method answers once per request;
//! the bus streams what changed, so the side view is not a poll.
//!
//! **Reversal.** A client that can show neither a custom request's text nor a
//! side view, measured as the editor most authors use, moves goals into the
//! specification's features alone — inlay hints at each hole, a hover over it.
//! A render bus that cannot attach through the language server's stream moves
//! the webview onto `gandr/goals` alone.
//!
//! # Specification evidence
//!
//! Executable predicates cover UTF-16 projection and errors, token kinds and
//! grouping, half-open overlap, diagnostic shape, decoded URI bytes, request
//! classification, lifecycle transitions and document publication. Captures
//! retain only phase or counts; predicates do not clone server state, reparse
//! documents or compose them twice.
//!
//! Adequacy separates bounded observations from broader obligations. The
//! overlap witness exhausts ordered spans and all query endpoint pairs in a
//! five-offset domain, preserving input order and rejecting empty
//! intersections. Other witnesses cover Unicode and line endings, framing
//! ceilings, partial writes and flush failures, decoder refusals, lifecycle
//! errors and ignored updates. The corpus observers independently walk the
//! checked-in sources and compare diagnostics, causal labels and token bytes
//! with the dispatcher and renderer; agreement is evidence over that corpus,
//! not a proof for all programs.
//!
//! The editor simulation (`tests/editor.rs`) drives a connection one
//! keystroke at a time, in lockstep: a buffer models the editor's text,
//! cursor, auto-closed pairs and indentation, a typist reaches each corpus
//! source from an empty buffer and an erasure deletes it line by line, and
//! random edit scripts are undone to where they started. Every keystroke's
//! publication carries the latest version and every request is answered once
//! without an error. The oracle is a fresh connection opening the same text
//! whole: the published diagnostics, semantic tokens, outline, folding,
//! selection ranges and inline completion must equal its answers, at every
//! keystroke of the erasure and the scripts, and at every line of the corpus
//! typing, where a whole reparse per keystroke would cost minutes with
//! specifications enforced. A hover's documentation reads the session's last
//! accepted revision, which a fresh connection lacks, so it is held to
//! answering, not to agreeing. A hover at every byte of every corpus source
//! answers without a fault, and the share it answers is recorded as a floor
//! that rises with each position answered and falls only when a hover stops
//! answering one wrongly. Those sessions name a quiet interval of zero, since
//! their oracle has no caret and holds nothing; the quiet scenario types one
//! declaration under the interval and pins every keystroke's publication.
//!
//! **One execution per session.** A single editor's session is `serve`
//! itself, on a thread of its own over in-memory framed streams, so every
//! answer the session holds to the oracle is one the transport wrote, and the
//! session ends with `shutdown` and `exit`. The two-editor sessions share a
//! workspace, as the hub's connections do, so they run in process and replay
//! message for message through `serve` at their end. _Alternative:_ every
//! session in process and replayed, which ran the server's work twice: with
//! specifications enforced the replay was 45% of the corpus typing.
//! _Reversal:_ a check that only an in-process drive can make moves the
//! single-editor sessions back in process, with the replay.
//!
//! **Every corpus sweep samples on a pull request and runs whole nightly.**
//! With specifications enforced a sweep over the whole corpus takes minutes,
//! past the 30 s every test is held to, so each sweep sits in a `sweeps`
//! module and visits a sample its constant states under every pull-request
//! profile, and every source under the `nightly` nextest profile, which the
//! nightly workflow runs enforced — the erasure over the night's slice of
//! the corpus and the typing over the night's part of every source, the
//! whole of either every few nights. A sample ranks the corpus by its BLAKE3
//! digest under the sweep's name, holds a source of each corpus class, and
//! adds every source the change adds or modifies (`gandr-workflow-sweep`): a
//! run reproduces, and a corpus edit is swept on the pull request that makes
//! it. The typing samples only sources no longer than a kibibyte: the longest
//! source alone types for longer than the bound, and the erasure still holds a
//! long source to the oracle at every keystroke. The random edit scenarios
//! generate a quarter of their scripts from one fixed seed. A source that
//! fails in the sample fails the pull request and one outside it fails the
//! nightly run: nothing goes untested, part of it is tested later.
//! _Alternatives:_ the whole corpus on every pull request, which held the
//! enforcing lane past fifteen minutes; a stride over the length-sorted corpus,
//! which never visits a source between its steps until nightly; a random
//! sample, whose failure the next run cannot reproduce. _Reversal:_ a sweep
//! whose whole fits the bound leaves its `sweeps` module.
//!
//! Two effects cannot be observed by a useful return-value predicate: `serve`
//! owns opaque generic input/output streams, and `Capabilities::fmt` writes
//! through an opaque formatter. Their explicit exemptions are witnessed by
//! framed sessions, the advertised JSON and a refused-write sink. Semantic
//! diagnostic fields are asserted directly; diagnostic prose is compared with
//! its renderer rather than pinned as English wording.
//!
//! # References
//!
//! - Microsoft. "Language Server Protocol Specification 3.17." <https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/>
//!   — the base protocol, the lifecycle, document synchronisation, published
//!   diagnostics, semantic tokens, document symbols, folding and selection
//!   ranges, hover, document and range formatting, and the position encodings
//!   this server serves.
//! - Microsoft. "Language Server Protocol Specification 3.18." <https://microsoft.github.io/language-server-protocol/specifications/lsp/3.18/specification/>
//!   — `textDocument/inlineCompletion`, its snippet `StringValue`, and the
//!   snippet syntax a ghost text's tab stops are written in.
//! - JSON-RPC Working Group. "JSON-RPC 2.0 Specification." 2010, revised 2013. <https://www.jsonrpc.org/specification>
//!   — the envelope, the batch the server refuses, and the reserved error codes
//!   it answers with.
//! - Matthew Kerwin. "The 'file' URI Scheme." RFC 8089, February 2017.
//!   `doi:10.17487/RFC8089` — the URI a document is named by, whose
//!   percent-decoded path classifies its source root.
//! - The rust-analyzer contributors. "LSP Extensions." <https://rust-analyzer.github.io/book/contributing/lsp-extensions.html>
//!   — the `experimental/` and `rust-analyzer/` methods the extensions
//!   assessment weighs.
//! - The rust-analyzer contributors. "`crates/rust-analyzer/src/diagnostics.rs`." <https://github.com/rust-lang/rust-analyzer/blob/master/crates/rust-analyzer/src/diagnostics.rs>
//!   — the native syntax and semantic diagnostics kept apart and fetched as
//!   separate tasks, the precedent the quiet publication cites.
//! - The Lean developers. "Lean.Data.Lsp.Extra." <https://lean-lang.org/doc/api/Lean/Data/Lsp/Extra.html>
//!   — `$/lean/plainGoal`, `$/lean/plainTermGoal`, `$/lean/fileProgress` and
//!   the `$/lean/rpc/*` session the infoview runs on.
//! - The rocq-lsp developers. "rocq-lsp protocol documentation." <https://github.com/ejgallego/coq-lsp/blob/main/etc/doc/PROTOCOL.md>
//!   — the `proof/goals` request and the progress and viewport notifications.
//! - Microsoft. "Webview API." <https://code.visualstudio.com/api/extension-guides/webview>
//!   — the panel a VS Code extension draws its own view in.
//! - The Neovim developers. "LSP." <https://neovim.io/doc/user/lsp.html> — a
//!   client's `request` of any method and the handlers a notification is routed
//!   to.
//! - Free Software Foundation. "Eglot: The Emacs Client for the Language Server
//!   Protocol." <https://www.gnu.org/software/emacs/manual/html_mono/eglot.html>
//!   — the Emacs client, whose server connection is a JSON-RPC endpoint any
//!   request reaches.
//! - The Helix developers. "Helix." <https://helix-editor.com/> — no plugin
//!   system yet, so the standard protocol only.
//! - Zed Industries. "Language Extensions." <https://zed.dev/docs/extensions/languages>
//!   — what a Zed extension adds to a language server.

// Module documentation that predates the shape lint: 32 headings outside the
// vocabulary, 15 decision records, 3 issue references and 16 budgets exceeded.
// Each allow leaves with the rewrite that clears its count.
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    allow(
        module_doc_heading,
        doc_decision_record,
        doc_issue_reference,
        module_doc_budget,
        reason = "module documentation that predates the shape lint"
    )
)]
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(linear_search_in_loop, reason = "2 cost-shape sites; #814 lists them")
)]

extern crate alloc;

use core::fmt;

#[cfg(unix)]
mod bus;
mod complete;
mod format;
mod goto;
mod hover;
#[cfg(unix)]
mod hub;
mod inline;
mod markup;
mod outline;
mod position;
mod proposal;
mod protocol;
mod quiet;
mod reading;
mod recheck;
mod rpc;
mod server;
mod tokens;
mod transport;
mod view;

pub use gandr_surface_pretty::Spelling;

#[cfg(unix)]
pub use crate::bus::RENDER_BUS_PREFACE;
#[cfg(unix)]
pub use crate::hub::Face;
#[cfg(unix)]
pub use crate::hub::LINGER;
#[cfg(unix)]
pub use crate::hub::bind;
#[cfg(unix)]
pub use crate::hub::relay;
#[cfg(unix)]
pub use crate::hub::run_hub;
#[cfg(unix)]
pub use crate::hub::socket_for;
pub use crate::position::Character;
pub use crate::position::Line;
pub use crate::position::Position;
pub use crate::position::Range;
pub use crate::proposal::Proposal;
pub use crate::proposal::ProposalRefusal;
pub use crate::protocol::ContentChange;
pub use crate::protocol::Diagnostic;
pub use crate::protocol::DocumentUri;
pub use crate::protocol::DocumentVersion;
pub use crate::quiet::QUIET;
pub use crate::recheck::Reached;
pub use crate::recheck::Tried;
pub use crate::server::Peer;
pub use crate::server::Served;
pub use crate::server::Server;
pub use crate::server::Workspace;
pub use crate::server::serve;
pub use crate::tokens::TOKEN_MODIFIERS;
pub use crate::tokens::TOKEN_TYPES;
pub use crate::transport::Body;
pub use crate::transport::TransportFault;
pub use crate::transport::read_frame;
pub use crate::transport::write_frame;

/// The capabilities the server advertises: what `initialize` answers,
/// displayed as one line of JSON.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Capabilities;

impl fmt::Display for Capabilities
{
    /// Writes the `initialize` result as one line of JSON: the capabilities
    /// and the server's name and version.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: exactly the `result` an `initialize` request is answered
    ///   with, compact, with no line terminator.
    /// - provides: the driver's `gandr lsp --capabilities` line.
    /// - fails: propagates the formatter's own write failure, and reports one
    ///   for a result that does not encode.
    /// - panics: none.
    /// - executable: none — the generic formatter exposes neither its written
    ///   bytes nor the underlying writer; unit success and `fmt::Error` cannot
    ///   distinguish the required output or a refused write.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a pinned decoded capability object distinguishes
    ///   wrong protocol fields. L3 — a refusing formatter distinguishes a
    ///   swallowed write failure by the returned `fmt::Error`.
    /// - witness: `tests::capabilities::advertised_capabilities_name_the_token_legend`
    /// - witness: `tests::capabilities::a_refused_capabilities_write_is_propagated`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let line = serde_json::to_string(&protocol::InitializeResult::advertised())
            .map_err(|_unencodable| fmt::Error)?;
        f.write_str(&line)
    }
}
