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
//! that declaration. A theory, a module and a member a theory writes answer
//! as written, a theory with its members. The types come from a typed run
//! over the document's text, built at the first hover after an edit and kept
//! until the next: its entries are the nodes the run judged, the binders their
//! uses resolve to, the written types it formed, and the members of `theory`
//! blocks and `data` families at the types the description route states for
//! them. Each type is spelled in the form the editor's
//! `gandr.presentation.form` names, the
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
//! A served feature is served as completely as the specification allows: every
//! field of its result that the engine holds the data for is filled, and every
//! capability a client declares for it is honoured. A type the checker
//! already keeps belongs in a completion's label details and a symbol's detail,
//! and a repair the parser recorded belongs in a code action. A field is left
//! empty only when gandr cannot yet fill it, and the feature's row in the
//! table below then says what it waits on. A new feature fills its fields whole
//! in the change that serves it, never as a later pass.
//!
//! | Feature | Methods | State |
//! | ------- | ------- | ----- |
//! | lifecycle | `initialize`, `initialized`, `shutdown`, `exit` | served |
//! | tracing | `$/setTrace`, `$/logTrace` | served: the level `initialize` names, and each `$/setTrace` sets; at `messages` each line of the server's log is traced by its document and version, at `verbose` with what rechecking it cost besides |
//! | cancellation | `$/cancelRequest` | served: a request is answered `RequestCancelled` when its cancellation was read before it was handled, and `ContentModified` when a change of the document it reads was, without being run |
//! | progress | `window/workDoneProgress/create`, `$/progress`, `window/workDoneProgress/cancel` | served: to a client that declares `window.workDoneProgress`, an open begins `Checking` on the document's file name and a change of files on disk that rechecks open copies begins `Rechecking` on how many, under a token of its own, ended once the admissions ran; none is cancellable, and a cancellation naming a token the connection issued is recorded against it, the work it names having ended within the message that started it |
//! | document synchronisation | `textDocument/didOpen`, `didChange` (incremental), `didClose` | served: an editor's copy shadows the file at its path for every import on every connection, and an open, change or close of it rechecks and republishes every open copy whose closure names it, on each connection holding one, as the `server` module's `Workspace` states |
//! | save notifications | `textDocument/willSave`, `willSaveWaitUntil`, `didSave` | `willSave` and `willSaveWaitUntil` served, not advertised: every change is judged as it arrives, so a save owes no check; `willSave` is read and left, `willSaveWaitUntil` answered with the edits formatting the whole document answers; `didSave` declined for the same reason |
//! | notebook synchronisation | `notebookDocument/*` | declined: gandr has no notebook format |
//! | published diagnostics | `textDocument/publishDiagnostics` | served: the session's judgement, then a hint tagged `Unnecessary`, code `UnusedBinder`, at each lambda or bind binder no use refers to in a declaration the checker accepted, kept by the judgement beside its verdicts, as the `unused` module states — never a linear binder or a consumable capability, whose drop is the checker's refusal, nor a name starting with `_`; a refused declaration's binders wait on #1504. An unused import is not yet marked: it is #1116's row |
//! | pulled diagnostics | `textDocument/diagnostic`, `workspace/diagnostic` | declined: every synchronisation publishes; reverses for a client that reads only pulled diagnostics |
//! | semantic tokens | `textDocument/semanticTokens/full`, `full/delta`, `range`, `workspace/semanticTokens/refresh` | served: once a copy is judged, each written use classified by what the judgement resolved it to and a name nothing declares or binds as the custom `unresolvedReference`, as the `tokens` module states; a full answer carries its stream's digest as its id, a delta naming the stream the connection last sent answers one edit over the tokens between the ends the two streams share, and any other id the full stream; the refresh is asked of a client that declares it once a copy is rechecked because a file its closure names changed |
//! | inline completion | `textDocument/inlineCompletion` | served: a kept proposal's fill holding the position, then the parser's ghost texts closing the form the cursor ends, best first, each written on the cursor's line: a ghost text that would break the line, as closing a line comment does, is not offered. A request the client makes as the author types is answered with no item unless `gandr.inlineCompletion.trigger` is `automatic`; one the author invokes always is |
//! | document symbols | `textDocument/documentSymbol` | served: every declaration, nested in the one holding it — a module's members, and the members a theory, a family or a codata declaration writes among its own tiles — each with what it writes between its name and its body as its detail |
//! | folding ranges | `textDocument/foldingRange`, `workspace/foldingRange/refresh` | served, a multi-line member included, each form's range with what it writes before its body as its collapsed text for a client that shows one; the refresh is asked of a client that declares it once folds change from outside the document's text, which no fold this server answers does |
//! | selection ranges | `textDocument/selectionRange` | served, through a member before the form holding it |
//! | hover | `textDocument/hover` | served |
//! | inlay hints | `textDocument/inlayHint`, `workspace/inlayHint/refresh` | served: once a copy is judged, the type of each binder its form writes none for — a lambda's, a pattern's, a `run`'s, a `for`'s, a handler's — after its name, as the hover over the name spells it and as the `inlay` module states, over the range asked; the refresh is asked of a client that declares it once a copy is rechecked because a file its closure names changed. `inlayHint/resolve` is not offered: a hint's label linking to its type's declaration waits on the printer recording the declaration each name it writes stands for (#1441) |
//! | signature help | `textDocument/signatureHelp` | served: the head the innermost call's name was written with — a declaration's, a constructor's, or a binder's function type — its documentation, and the argument the position writes |
//! | completion | `textDocument/completion`, `completionItem/resolve` | served: the binders in scope, the closure's declared names and the keywords the slot at the word's start admits, each starting with the word; each name carries its type in the list — a binder's read off the table, a declared name's head — as its detail and, to a client that shows them, its label details; a declared name resolves to its documentation; to a client that takes snippets, a keyword inserts the form it opens, spelled as inline completion spells it, each hole a tab stop, filtered by the keyword |
//! | definition, declaration, type definition | `textDocument/definition`, `declaration`, `typeDefinition` | served: what the use at the position refers to, at its definition half and its signature half respectively for a name declared in two, either form for a name written once, and the families the type there names, as links when the client takes them |
//! | implementation | `textDocument/implementation` | declined: the core has no interfaces to implement |
//! | document highlight | `textDocument/documentHighlight` | served: the declaring name and every use of the name at a position, within the document, read off the type table's reverse use index, as the `uses` module states; a recursive call's use spans its marker with its name |
//! | references | `textDocument/references` | served: the declaring name when asked, then the uses of the name at a position in every open document and in every source under the folders the editor opened that imports its source, read from disk, matched by its source's path and its span, as the `uses` module states |
//! | rename | `textDocument/prepareRename`, `rename` | served: the declaring name and each use the reference request finds, narrowed to the name's spelling; the declaring source is tried with its edits applied and a rename that adds an error is refused, as the `rename` module states |
//! | linked editing | `textDocument/linkedEditingRange` | served: a binder local to a declaration and each of its uses, read off the type table's reverse use index, as the `uses` module states, with the parser's word pattern, so an edit that leaves a range no name ends the linked edit; a name the unit declares links nothing, since importers may write it, and rename serves it |
//! | call hierarchy | `textDocument/prepareCallHierarchy`, `callHierarchy/incomingCalls`, `callHierarchy/outgoingCalls` | served: an item is a declared value at its definition, read off the type table as the `calls` module states; its outgoing calls are the declared values the uses in its definition's form refer to, and its incoming calls its uses in every document a reference request reads, each grouped by the innermost definition holding it. A constructor and a binder are no item |
//! | type hierarchy | `textDocument/prepareTypeHierarchy`, `typeHierarchy/*` | served, not advertised: each answers `null`, as the core has no subtyping to arrange types by |
//! | formatting | `textDocument/formatting`, `rangeFormatting`, `rangesFormatting` | served: one layout per request, each top-level form a range touches edited once. The layout is canonical, so the request's `FormattingOptions` are not read: it writes no trailing whitespace and ends the text with one newline whatever `trimTrailingWhitespace`, `insertFinalNewline` and `trimFinalNewlines` ask, and indents by the printer's two spaces a level whatever `tabSize` and `insertSpaces` ask |
//! | on-type formatting | `textDocument/onTypeFormatting` | served: typing the `;` that closes a top-level form lays that form out, and any other character, or a `;` inside a form, edits nothing |
//! | code actions, code lenses | `textDocument/codeAction`, `codeAction/resolve`, `codeLens`, `codeLens/resolve`, `workspace/codeLens/refresh` | served: for model proposals, a quick fix applying each checked fill and a lens counting a range's checked fills, each whole in its answer and resolved as it came, the lens over a range's one fill running `gandr.applyFill` for a client that applies edits; once a fill is kept, the editor holding the document is asked for its lenses again when its client says it refreshes them. For each refusal of a malformed form the asked range meets, a preferred quick fix inserting the closing the grammar expects there, and for each written hole the asked range meets, a quick fix per name in scope that one trial of the document judges without a refusal at the hole, fewest errors left first, each as the `fix` module states. Over each name the document declares, a references lens listed without a command and resolved to the count of the uses a reference request there finds, the declaration left out, running `gandr.showReferences` with the URI, the position and those uses |
//! | commands, edits | `workspace/executeCommand`, `workspace/applyEdit` | served: `gandr.applyFill`, the one command the server runs, asks the client to apply the checked fill its arguments name while the document keeps it, and is refused as content modified once an edit withdrew it; an edit the client does not apply is logged with its reason; every edit the server sends is shaped as its client takes edits, as `protocol::WorkspaceEdit::shaped` states. `gandr.showReferences`, which a references lens names, is the client's to run |
//! | virtual documents | `workspace/textDocumentContent`, `workspace/textDocumentContent/refresh` | served for the scheme `gandr-tree`: `gandr-tree:` followed by the rest of an open document's `file` URI, with or without its empty authority, answers that document's molded tree, its layout and its obligations, printed as the `syntax` module states, once per held text; a client that declares `workspace.textDocumentContent` is asked for the tree again after each change to the document, under each URI it asked by, until it closes the document |
//! | document links | `textDocument/documentLink`, `documentLink/resolve` | served: each path import's address, between its quotes, linked to the file the dispatcher reads for it with that file's path as its tooltip, read off the document's held reading, as the `reading` module states, and resolved as it came; a scheme import links nowhere |
//! | document colours | `textDocument/documentColor`, `colorPresentation` | declined: gandr has no colour literals |
//! | inline values | `textDocument/inlineValue` | declined: they serve a debugger, and gandr has no debug adapter |
//! | monikers | `textDocument/moniker` | declined: no cross-repository index reads them |
//! | workspace symbols | `workspace/symbol`, `workspaceSymbol/resolve` | served: every declaration the outline reads in the open documents' import closures — a module's members, a theory's members and a family's constructors included — whose name holds the query's characters in order, without case, at most 128, as the `search` module states, each with the outline's kind, the name of the declaration holding it and its location, and resolved as it came; a source no open document's closure reads is not searched |
//! | file watching | `client/registerCapability`, `client/unregisterCapability`, `workspace/didChangeWatchedFiles` | served: a client that registers watchers dynamically is asked at `initialized` to watch `**/*.gandr`, and the watcher is withdrawn before `shutdown` is answered; on the hub, a connection whose client does not is watched by the hub itself, over the files its copies' closures name, as the `disk` module states; a changed file rechecks and republishes every open copy whose closure named it at its last judgement, a missing import written included, as the `server` module states; a change on disk to a file an editor holds is not read, its copy standing for it; a closure's read of a file a watcher reports — under a folder a watching client opened, or one the hub follows — stands without a look at the disk until the watcher reports it, and every other file is confirmed on disk at each lay-out |
//! | workspace folders | `workspace/didChangeWorkspaceFolders`, `workspace/workspaceFolders` | served: the folders a client opens, at `initialize` and as it opens and closes them, are the path table's roots while a connection holds them open, as the `files` module states; a folder change that does not read, from a client that lists its folders, asks for them whole, and the list replaces the connection's roots |
//! | file operations | `workspace/willRenameFiles`, `didRenameFiles`, `didCreateFiles`, `didDeleteFiles`, `willCreateFiles`, `willDeleteFiles` | served for gandr sources and folders on disk: a rename asked about before it is done is answered with the edits rewriting each path import's address it changes, in every document an editor holds and every source under the opened folders that moves or imports a file that moves, as the `relocate` module states; a creation, deletion or rename once done rechecks and republishes every open copy whose closure names a file it touched or one under a folder it touched; a creation or deletion asked about before it is done is answered with no edit, none being owed, and is not advertised |
//! | imported files | `gandr/importFiles`, gandr's own | served: the files a client names, as a drop of gandr sources into a document or a paste of text copied from another names them, are answered with one insertion of an `import "…" ;` line for each gandr source the document does not import yet, addressed from its directory as the `relocate` module states, after its last import or at its start |
//! | copied sources | `gandr/copiedSources`, gandr's own | served: the ranges a copy takes from a document are answered with the sources declaring what the names they hold whole refer to — the document's own for a declaration outside the ranges, a sibling's file otherwise, no binder and no declaration the ranges hold — as the `paste` module states, which a paste into another document imports |
//! | configuration | `workspace/didChangeConfiguration` | served: the `gandr` section's `diagnostics.verbosity`, as the `recheck` module states, `diagnostics.quiet`, as the `quiet` module states, `presentation.form`, which every later hover reads, `presentation.spelling`, which every later hover reads and which republishes the diagnostics, and `inlineCompletion.trigger`, which every later inline completion request reads |
//! | pulled configuration | `workspace/configuration` | served: a client that declares it is asked for its `gandr` section once initialised and after each push carrying none, its answer applied as a push is |
//! | window messages | `window/showMessage`, `showMessageRequest`, `showDocument`, `logMessage` | served: a grammar that did not build is shown as an error once initialised, and a `gandr` section, pushed or pulled, that does not read is logged as a warning naming why, none of it applied; a fill another face keeps for a document an editor holds is offered to a client that shows documents, once until the next edit withdraws it, and choosing to see it shows the document with the fill's range selected; the timing line goes to the server's log and, when traced, to `$/logTrace` |
//! | gandr's extensions | `gandr/goals`, `gandr/serverStatus`, the render-bus attach through the language server's stream | blocked: each as the assessment in § Extensions beyond the specification names; the bus itself is served on the hub's socket (the `bus` module); the syntax tree view is the `gandr-tree` virtual document |
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
//! | syntax tree view: `rust-analyzer/viewSyntaxTree` | rust-analyzer | **adopt** as the `gandr-tree` virtual document, served through the specification's `workspace/textDocumentContent`: the molded tree of a document, its molds, tiles, layout and repairs, as text | the tree exists for every request already, and grammar and parser work reads it; the specification's request reaches every 3.18 client where a custom method reaches only an extension that knows it |
//! | snippet text edits | rust-analyzer | **adopt** with code actions, as the specification's 3.18 `SnippetTextEdit`: a repair the parser recorded becomes a fix whose holes are tab stops, sent as a snippet to a client that declares `snippetEditSupport` | inline completion already writes snippets, and the parser's continuations at a refusal spell the closing; the specification's edit reaches every 3.18 client where rust-analyzer's `experimental.snippetTextEdit` reaches only its own |
//! | runnables: `experimental/runnables` | rust-analyzer | **decline** the method; a code lens over each declaration that evaluates, running it as `gandr run` does, once commands exist | the specification's lenses and commands carry it, so Helix and Zed see it too |
//! | hover actions | rust-analyzer | **decline** | its actions are go-to and find-references links, which every client offers from its own commands over the definitions and references the server answers |
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
//! the corpus and the typing over the night's part of sixteen of every
//! source, the whole of either every few nights. A sample ranks the corpus by
//! its BLAKE3 digest under the sweep's name, holds a source of each corpus
//! class, and adds every source the change adds or modifies
//! (`gandr-workflow-sweep`): a run reproduces, and a corpus edit is swept on
//! the pull request that makes it. The typing samples only sources no longer
//! than a kibibyte: the longest source alone types for longer than the bound,
//! and the erasure still holds a long source to the oracle at every keystroke.
//! The random edit scenarios generate a quarter of their scripts from one
//! fixed seed. A source that fails in the sample fails the pull request and
//! one outside it fails the nightly run: nothing goes untested, part of it is
//! tested later.
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

extern crate alloc;

use core::fmt;

#[cfg(unix)]
mod bus;
mod calls;
mod complete;
#[cfg(unix)]
mod disk;
mod files;
mod fix;
mod format;
mod goto;
mod hover;
#[cfg(unix)]
mod hub;
mod inlay;
mod inline;
mod markup;
mod outline;
mod paste;
mod position;
mod proposal;
mod protocol;
mod quiet;
mod reading;
mod recheck;
mod relocate;
mod rename;
mod rpc;
mod search;
mod server;
mod signature;
mod syntax;
mod tokens;
mod tracking;
mod transport;
mod unused;
mod uses;
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
pub use crate::proposal::Settles;
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
