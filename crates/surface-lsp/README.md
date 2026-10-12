# gandr-surface-lsp

The gandr language server: diagnostics, semantic tokens, inline completion, the document's outline and hover over the Language Server Protocol, served over any pair of byte streams.

<!-- toc -->

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Every synchronisation judges the document, publishes, then admits](#every-synchronisation-judges-the-document-publishes-then-admits)
- [Diagnostics are the renderer's reports](#diagnostics-are-the-renderers-reports)
- [Tokens are the highlighter's roles](#tokens-are-the-highlighters-roles)
- [Inline completion is the parser's expected syntax](#inline-completion-is-the-parsers-expected-syntax)
- [The outline is read off the tree](#the-outline-is-read-off-the-tree)
- [A hover reads the session](#a-hover-reads-the-session)
- [Positions count UTF-16 code units](#positions-count-utf-16-code-units)
- [The lifecycle and its error codes](#the-lifecycle-and-its-error-codes)
- [Formatting answers the formatter's layout as edits](#formatting-answers-the-formatters-layout-as-edits)
- [The transport is written here](#the-transport-is-written-here)
- [Document URIs](#document-uris)
- [Coverage of the specification](#coverage-of-the-specification)
- [What editors add beyond the protocol](#what-editors-add-beyond-the-protocol)
- [Extensions beyond the specification](#extensions-beyond-the-specification)
- [Specification evidence](#specification-evidence)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** `gandr-surface-lsp` serves a subset of the Language Server Protocol 3.17: the base protocol's framing, the JSON-RPC 2.0 envelope with its standard error codes, the lifecycle from `initialize` to `exit`, incremental document synchronisation, `textDocument/publishDiagnostics` after every synchronisation, `textDocument/semanticTokens/full` and `textDocument/semanticTokens/range`, `textDocument/documentSymbol`, `textDocument/foldingRange` and `textDocument/selectionRange`, and `textDocument/hover`; and, from 3.18, `textDocument/inlineCompletion`. `serve` runs one session over any `BufRead` and `Write` pair, logging one timing line per synchronisation to a third `Write`; `Capabilities` displays what `initialize` answers. The driver's `gandr lsp` serves it over standard input and output and logs to standard error.

**Why.** An editor should show what `gandr check` prints, where it prints it, while the source is written. The server is a face over the pipeline's own outputs, never a second pipeline: its diagnostics are the reports `gandr-surface-diagnostics` renders for the dispatcher's step, and its tokens are the roles `gandr-surface-grammar`'s highlighter classifies, so an editor, a terminal and a test cannot disagree about a refusal or a token.

**How.** Each open document holds a `gandr-surface-session` session under the source root its `file` URI's path classifies as. A synchronisation applies the client's changes to the held text and judges the text in the session, reads the judgement's step through `gandr-surface-diagnostics`' `entries` under `check --goals`, and publishes each report as one diagnostic: its span as the range, its refusal's vocabulary name as the code, its title, primary label and note as the message, its context loci and nested reasons as related information. Then it runs the kernel admission the judgement left. A token request parses the document, takes the highlighter's spans and delta-encodes them under the standard legend. An inline-completion request molds the form the cursor ends and spells what `gandr-surface-parser` expects to close it as a snippet. An outline request parses the document and reads its declarations, its multi-line forms or the forms around a position off the tree. A hover request finds the declaration whose name the cursor is on and reads its type and documentation off the document's session. A formatting request lays the held text out through `gandr-surface-format` and answers the edits that turn the text into that layout. Every position is a UTF-16 position read through `gandr-surface-render-remote`'s `LineIndex`. The server keeps the open documents' text and sessions and one grammar per process.

## References

- Microsoft. "Language Server Protocol Specification 3.17." <https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/> — the base protocol, the lifecycle, document synchronisation, published diagnostics, semantic tokens, document symbols, folding and selection ranges, hover, document and range formatting, and the position encodings this server serves.
- Microsoft. "Language Server Protocol Specification 3.18." <https://microsoft.github.io/language-server-protocol/specifications/lsp/3.18/specification/> — `textDocument/inlineCompletion`, its snippet `StringValue`, and the snippet syntax a ghost text's tab stops are written in.
- JSON-RPC Working Group. "JSON-RPC 2.0 Specification." 2010, revised 2013. <https://www.jsonrpc.org/specification> — the envelope, the batch the server refuses, and the reserved error codes it answers with.
- Matthew Kerwin. "The 'file' URI Scheme." RFC 8089, February 2017. `doi:10.17487/RFC8089` — the URI a document is named by, whose percent-decoded path classifies its source root.
- The rust-analyzer contributors. "LSP Extensions." <https://rust-analyzer.github.io/book/contributing/lsp-extensions.html> — the `experimental/` and `rust-analyzer/` methods the extensions assessment weighs.
- The Lean developers. "Lean.Data.Lsp.Extra." <https://lean-lang.org/doc/api/Lean/Data/Lsp/Extra.html> — `$/lean/plainGoal`, `$/lean/plainTermGoal`, `$/lean/fileProgress` and the `$/lean/rpc/*` session the infoview runs on.
- The rocq-lsp developers. "rocq-lsp protocol documentation." <https://github.com/ejgallego/coq-lsp/blob/main/etc/doc/PROTOCOL.md> — the `proof/goals` request and the progress and viewport notifications.
- Microsoft. "Webview API." <https://code.visualstudio.com/api/extension-guides/webview> — the panel a VS Code extension draws its own view in.
- The Neovim developers. "LSP." <https://neovim.io/doc/user/lsp.html> — a client's `request` of any method and the handlers a notification is routed to.
- Free Software Foundation. "Eglot: The Emacs Client for the Language Server Protocol." <https://www.gnu.org/software/emacs/manual/html_mono/eglot.html> — the Emacs client, whose server connection is a JSON-RPC endpoint any request reaches.
- The Helix developers. "Helix." <https://helix-editor.com/> — no plugin system yet, so the standard protocol only.
- Zed Industries. "Language Extensions." <https://zed.dev/docs/extensions/languages> — what a Zed extension adds to a language server.

## Provided features

- `serve` and `Served`: one session over a stream pair and a log, ending cleanly at `exit` or boundary EOF after `shutdown`, and abruptly before shutdown. Witnesses: `session::session::a_session_round_trips_over_in_memory_streams`, `session::session::a_stream_closed_without_exit_ends_abruptly`, `server::tests::the_lifecycle_admits_requests_in_the_protocol_order`.
- Incremental synchronisation: each content change applied in order, a ranged one to its range and one naming no range as the whole text, and the document judged again in its session, which molds only the forms the change touched; one log line per synchronisation names the forms molded, the items the incremental checker judged, the recheck's wall and the admission's. Witnesses: `server::tests::ranged_changes_edit_the_held_text_in_order`, `session::session::an_edit_to_a_large_document_rechecks_its_forms`.
- `Server::admit`: the kernel admission each synchronisation left, run once its diagnostics are published. Witnesses: `server::tests::an_admission_follows_its_synchronisation`, `recheck::tests::an_admission_follows_the_published_diagnostics`.
- `read_frame`, `read_frame::Absent`, `write_frame`, `Body` and `TransportFault`: the base protocol's framing, with a ceiling on a header line and on a body. Witnesses: `transport::tests::a_round_trip_preserves_the_payload`, `transport::tests::eof_at_a_boundary_is_clean`, `transport::tests::a_header_block_the_framing_cannot_read_is_refused`.
- The envelope: requests, notifications and responses told apart; a body outside the decoder-supported JSON fragment answered with a parse error, including invalid UTF-8 and exceeded number or nesting limits; a decoded batch or other invalid message refused as an invalid request. Witnesses: `rpc::tests::a_request_is_classified`, `rpc::tests::a_batch_is_rejected`, `rpc::tests::decoder_rejections_keep_the_parse_error_class`.
- Published diagnostics: one per report the renderer gives the document's step, at its range, under its code, with its message and related information; republished at every change, cleared at close. Witnesses: `server::tests::a_refused_program_is_published_as_an_editor_diagnostic`, `server::tests::synchronisation_publishes_and_close_clears`, `recheck::tests::causal_contexts_become_lsp_related_information`, `recheck::tests::a_labeled_context_keeps_its_locus_and_cause_in_related_information`, `recheck::tests::nested_reasons_become_lsp_related_information`, `recheck::tests::a_refusal_publishes_its_label_and_note`, `recheck::tests::a_fault_is_published_at_the_origin`, `session::session::a_refusal_is_published_where_the_renderer_renders_it`, `session::session::every_corpus_report_is_published_where_the_walk_renders_it`.
- Semantic tokens for the whole document and for a range, and `TOKEN_TYPES` and `TOKEN_MODIFIERS`, the legend. Witnesses: `tokens::tests::every_classified_role_maps_inside_the_legend`, `tokens::tests::the_legend_index_a_role_emits_names_what_that_role_means`, `tokens::tests::a_one_line_keyword_encodes_as_five_integers`, `tokens::tests::a_multiline_span_splits_and_drops_the_terminator`, `server::tests::semantic_tokens_full_answers_a_known_document`, `server::tests::a_range_returns_only_the_tokens_it_covers`, `server::tests::a_range_over_the_whole_document_agrees_with_the_full_stream`, `server::tests::a_token_straddling_the_range_edge_is_returned_whole`, `server::tests::an_inverted_range_yields_no_tokens`, `server::tests::an_empty_range_yields_no_tokens`, `recheck::tests::a_definition_produces_semantic_tokens`, `session::session::corpus_tokens_cover_the_highlighted_bytes`.
- Inline completion: the material the parser expects to close the innermost form at the cursor, as one snippet whose holes and lexical classes are tab stops; nothing where text follows the cursor on its line or the cursor is in a comment. Witnesses: `inline::tests::ghost_text_closes_the_innermost_form`, `inline::tests::no_ghost_text_where_text_or_a_comment_stands`, `server::tests::inline_completion_answers_the_expected_closer`.
- The outline: document symbols nesting each declaration inside the one that holds it, folding ranges over multi-line forms, documentation and block comments, and selection ranges growing from the innermost node around a position to the whole document. Witnesses: `outline::tests::declarations_nest_as_symbols`, `outline::tests::multi_line_forms_and_documentation_fold`, `outline::tests::a_selection_grows_from_the_innermost_form`, `server::tests::the_outline_requests_answer_a_known_document`.
- Hover: a declaration's name hovers its type and its documentation. Witnesses: `hover::tests::a_declaration_hovers_its_type_and_documentation`, `hover::tests::only_a_declared_name_hovers`, `hover::tests::each_member_hovers_its_own_type`, `server::tests::a_hover_answers_a_known_declaration`.
- Formatting: the whole document as one edit trimmed to the span its layout changes, and a range as one edit per top-level form it touches, each from `gandr-surface-format`. Witnesses: `format::tests::the_whole_document_is_one_trimmed_edit`, `format::tests::a_range_formats_the_forms_it_touches`, `server::tests::formatting_answers_the_edits_that_lay_a_document_out`.
- Positions in UTF-16 code units, a position past a line's end or past the last line clamped. Witnesses: `position::tests::utf16_counts_an_astral_character_as_two_units`, `position::tests::a_line_past_the_end_clamps`.
- `Capabilities`: the `initialize` result as one line of JSON. Witnesses: `capabilities::capabilities::advertised_capabilities_name_the_token_legend`, `server::tests::initialize_advertises_the_token_legend`.
- A `file` URI's percent-decoded path. Witness: `protocol::tests::a_file_uri_names_its_decoded_path`.
- One grammar per process, built at the first recheck. Witness: `recheck::tests::the_grammar_is_built_once_per_process`.

## Expected features

- **A client that reads UTF-16 positions.** The server answers `positionEncoding: "utf-16"`, the encoding every client supports, whatever encodings the client offers.
- **Documents named by `file` URIs.** The path classifies the document's source root as `gandr check` classifies a path: a document under a `fixture` directory settles as a fixture, one under `fixture/pending` is pending, and any other is strict. A URI of another scheme classifies as strict.

## Examples

```text
gandr lsp --capabilities
gandr lsp
```

`gandr lsp --capabilities` prints the `initialize` result as one line and exits; `gandr lsp` serves a session on standard input and output until `exit`. In memory:

```rust
use std::io::Cursor;

use gandr_surface_lsp::Body;
use gandr_surface_lsp::Served;
use gandr_surface_lsp::serve;
use gandr_surface_lsp::write_frame;

let mut input = Vec::new();
for message in [
    r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#,
    r#"{"jsonrpc":"2.0","id":2,"method":"shutdown"}"#,
    r#"{"jsonrpc":"2.0","method":"exit"}"#,
] {
    write_frame(&mut input, &Body::from(message.as_bytes().to_vec()))?;
}
let mut output = Vec::new();
let served = serve(&mut Cursor::new(input), &mut output, &mut Vec::new())?;
assert_eq!(served, Served::Clean, "exit after shutdown ends the session cleanly");
# Ok::<(), Box<dyn core::error::Error>>(())
```

The crate's tests run with `cargo nextest run -p gandr-surface-lsp`; the crate-level example runs with `cargo test -p gandr-surface-lsp --doc`.

## Every synchronisation judges the document, publishes, then admits

**Choice.** `didOpen` starts a session for the document and judges its text; `didChange` applies each content change to the held text in order — a ranged change replaces the bytes its two positions resolve to, an end before its start read as the start, and a change naming no range replaces the whole text — and judges the result in the same session. The session's form store takes up every top-level form the change left unchanged and molds the rest, and its judgement is the dispatcher's composition of the whole text, so the published diagnostics are what `gandr check` prints for it. Once the diagnostics are written, `serve` asks `Server::admit` to run the kernel admission the judgement left, so the client reads the reports before the kernel has re-derived the revision's acceptances. A disagreement the admission finds is published at the document's version in place of the reports, as one error at the origin naming the fault. A token request parses the whole text again.

**The log.** Each synchronisation writes one line to the log `serve` is given — `<uri> at version <n>: <molded>/<forms> forms molded, <judged>/<items> items judged, <wall> ms, admitted in <wall> ms` — naming the forms the parse molded, the items the incremental checker judged, the recheck's wall from the judgement to the diagnostics, and the admission's wall after them; a document refused whole has nothing to admit, and its line ends at the recheck's wall. A line the log refuses is dropped; the protocol never depends on it. Over a generated document of two thousand forms, one edit molds one to eight forms and publishes what opening the edited text publishes.

**Alternatives.** The recorded design keeps a checking session per open document and accepts incremental synchronisation; this is that design. Full synchronisation alone ships the whole buffer per keystroke and leaves the session nothing a change names; it stays as the change that names no range. The timing line could go to `window/logMessage`, which a client shows in its own channel, at the cost of a notification per change on the protocol stream; the server's log is where an operator reads it without touching the protocol. The admission runs on the serving thread after the publication, so it delays the next frame's read but never the diagnostics. Running it on a worker that the next change cancels would take it off the next keystroke too, at the cost of a session shared across threads.

**Reversal.** A client sending many small changes per notification, measured paying a line index per change, would batch them into one pass over the text; a client that reads only the protocol stream moves the timing line to `window/logMessage`; a measured wait of the next change on the admission moves the admission to a cancellable worker.

## Diagnostics are the renderer's reports

The one input is the dispatcher's step, read by `gandr-surface-diagnostics`' `entries` under the verb `check --goals`. A face that read refusals from a list kept beside the step could drop or duplicate one; reading the step means the editor receives exactly the reports the terminal prints, in the order it prints them.

| Report | Range | Code | Severity | Message | Related information |
| ------ | ----- | ---- | -------- | ------- | ------------------- |
| a refusal | the primary span | the refusal's vocabulary name | error | the title, the primary label and the note | each context locus, with its label, then each nested reason, outermost first, with its `while` clause |
| an unsettled declaration | the primary span | none | error | the title and the primary label | each context locus, with its label |
| a goal | the primary span | none | information | the title and the primary label | none |
| a shadowing warning | the shadowing name | `ShadowedBuiltin` | warning | the title and the primary label | none |
| a report the renderer leaves unlocated | the document's origin | as its kind | as its kind | the title, and the note of a refusal | none |
| a ledger line | the document's origin | none | error | the line | none |
| a fault before composition | the document's origin | none | error | the fault | none |

The message carries every line the terminal prints around the snippet: the title, then the primary locus's label on a line of its own, then a refused declaration's note after `note: `. The protocol gives a diagnostic one text field beside its range and related locations, so a label the underline carries in the terminal would otherwise never reach the editor. The alternative is the title alone, which leaves an editor user without the one line that says what the span is. The choice reverses when the protocol gains a field for the primary locus's label.

Every diagnostic's `source` is `gandr`. The code is the spelling a corpus `refuses` attribute states and a snippet's first line carries, so a code copied from the editor is an expectation a test can state. The alternative was the renderer seam's `DiagnosticCode` registry; the pipeline maps no refusal onto a registry code yet, and mapping refusals onto it here would be a second decision made in a face. The choice reverses when the pipeline's session report maps its refusals onto registry codes: the diagnostic's code becomes that spelling.

A goal is published at information severity because `check --goals` prints it as a report that does not fail the run. The alternative was the verb `check`, which withholds goals; an editor showing an open hole's goal beside it is the use the goal report exists for.

A builtin the document shadows is published at warning severity: the source's binding wins under the default policy, the module checks, and `check` prints the report without failing the run. Its code is `ShadowedBuiltin`, the refusal the reject policy files for the same bytes. Witness: `recheck::tests::a_shadowed_builtin_is_published_as_a_warning`.

The standing the renderer reads to choose what a pending source prints is the dispatcher's `Standing::of`, carried into the step by the session's submission: under the pending root, a source refused whole or carrying a refusal no expectation can state is pending, any other lowered; under the strict and fixture roots, a source refused whole is refused, any other settled or unsettled as its report's tally is. The L2 witness over every corpus source holds it to the walk's own reports.

## Tokens are the highlighter's roles

The tokens are the highlighter's `HlSpan`s, sorted and disjoint, delta-encoded as the protocol's five integers per token: line delta, start delta, length, type index, modifier bits. A span crossing a line splits into one token per line, its terminator dropped. A span the highlighter classified as nothing in particular, `HlRole::Other`, emits no token. Every other role maps onto the standard token types, so a client's theme colours gandr without a gandr-specific theme:

| Role | Type | Modifier |
| ---- | ---- | -------- |
| `Keyword`, `Boolean` | `keyword` | |
| `Operator` | `operator` | |
| `FunctionDef` | `function` | `declaration` |
| `FunctionCall` | `function` | |
| `VariableDef` | `variable` | `declaration` |
| `Variable` | `variable` | |
| `VariableParam` | `parameter` | |
| `Member` | `property` | |
| `Constructor` | `enumMember` | |
| `Type` | `type` | |
| `TypeBuiltin` | `type` | `defaultLibrary` |
| `TypeVariable` | `typeParameter` | |
| `Number` | `number` | |
| `StringLit`, `Character`, `Escape`, `Path` | `string` | |
| `Comment` | `comment` | |
| `Hole`, `Directive` | `macro` | |
| `Label` | `label` | |

A range request restricts which tokens are sent, never the coordinates they are sent in: the deltas still chain from the document's origin, and a token sharing at least one byte with the half-open range is sent whole rather than clipped, so a client can merge a range answer into a full one. Empty spans never intersect. An inverted or empty range answers no token. A request for a document the server does not hold answers `null`.

## Inline completion is the parser's expected syntax

An inline-completion request labels the text before the cursor, splits it at its predicted top-level form boundaries, molds the last form alone, and asks the parser's completion query what closes it: `Completion::innermost`, the holes of the operators above the innermost open form and that form's cheapest closing tiles. The answer is one item, inserted at the empty range at the cursor, whose text is a snippet. A tile is written as `tile_spelling` gives it, escaped for the snippet syntax; a lexical class such as `identifier` is a tab stop naming the class; a hole of an expression, a pattern or a type is a tab stop holding `?`, so accepting the ghost text unedited leaves holes the checker reports as goals. Items are separated by a space except after `(` or `[` and before `)`, `]`, `,`, `;` and a quote. So `def x = f(1` shows `)`, `def x = 1 +` shows `${1:?};`, and `run y <-` in a block shows `${1:?}; \}`. Over every line end of the corpus sources, accepting the ghost text with each tab stop filled closes a form and adds no repair.

Nothing is shown when text other than whitespace follows the cursor on its line, since the closer may already be written there, or when the text before the cursor ends in a line comment, a shebang or an unclosed block comment. The text after the cursor is never labeled, so the parser's lookahead reads only what precedes it. The material is structure only — closers, required keywords, holes and classes — never a name; names come from completion over goals.

- Alternatives: the whole completion to the end of the input, which closes every enclosing form at once and reads as noise past the innermost; molding the document from its start, which costs the whole prefix per request where the form costs its own tokens; the session's parse of the whole text, whose forms read the text after the cursor as lookahead and are kept by identity rather than by position.
- Reversal: a measured labeling cost on long documents moves the label pass onto the session's held labeling; an observed preference for less ghost text cuts the material at the first tile.

## The outline is read off the tree

The three outline requests parse the held text under the process's grammar, as a token request does, and read the molded tree alone; nothing the checker decides reaches them, so an outline is answered for a document that does not check.

- **Symbols.** A declaration is a form of the grammar's item or module-member sort, and its name is its first tile the highlighter classifies as a defined function, a defined value or a type. A declaration written inside another is among its children, so a module's members nest under it, a nested module's under that. A defined function is a `Function` symbol and a defined value a `Variable`; a declaration named by a type is a `Module`, an `Interface`, a `Struct` or an `Enum` by its keyword: `module`, `sign`, `codata`, and `data` or anything else. A symbol's range is its form's, widened over the attribute blocks standing directly before it, and its selection range is the name's tile. An attribute block is a form with no such tile, so it is no symbol.
- **Folding.** Every form, documentation node and block comment that ends on a later line than it starts folds from its first line to its last. Forms often share a first line, a function and its block say, and the client folds one range per line, so the outermost is answered. Documentation and block comments carry the `comment` kind, which a client's fold-all-comments reads.
- **Selection.** For each position the server walks down from the root, into the child holding the position, or, when none holds it, the child ending there, so a cursor just past a name selects the name. Layout is skipped, and a span its child repeats is given once. A document that does not parse answers the empty range at each position.

The alternatives were the lowered module, whose declarations carry names and spans but only for a document that lowers, and the highlighter's spans, which classify a name but say nothing of what encloses it. The choice reverses when a declaration's symbol must say what only lowering knows, its type in the symbol's detail say: the symbol then reads the session's lowered module, the tree still giving its ranges.

## A hover reads the session

A hover request finds the declaration whose name the cursor is on — from the name's first character to just past its last — among the declarations the outline reads off the tree, so a parameter, a use, a keyword or a word in a comment hovers nothing. It answers a fenced `gandr` block with the name and, when the document's session spells it, ` : ` and its type, then the declaration's documentation after a blank line, about the name's range:

- **The type** is the one the session's latest resume gives the declaration, spelled by the session's `type_at` at 80 columns: a signature, a synthesised type or a data declaration's universe, in the one spelling every face writes. The item is the occurrence of the declaration's name it is among the document's earlier non-module declarations, so two modules' members of one name each hover their own type.
- **The documentation** is what the session's latest accepted lowering filed for the declaring form, read under the form's content identity, which documentation does not reach: `///` lines and a `doc("…")` entry read to one text.

A declaration the session knows neither a type nor documentation for hovers nothing, and so does a document whose grammar did not build.

The alternative was to look the name under the cursor up as a word, wherever it stands, and answer the type of the last declaration it names, which hovers a parameter or a comment with an unrelated declaration's type; and to lower the document again per hover, which pays a lowering for what the session already holds. The occurrence counts the document's declarations as the tree orders them, which is the order the lowering admits them; a declaration the lowering refuses whole takes no item, so a later one of its name reads the next. The choice reverses when the session maps a declaring form to its item directly: the hover then asks for the form's item and stops counting.

## Positions count UTF-16 code units

The server advertises `positionEncoding: "utf-16"` and counts every range, related location and token in UTF-16 code units through the renderer seam's `LineIndex`, whose rows end at `\n`, `\r\n` and a lone `\r` as the protocol's do. UTF-16 is the encoding every client must support, so it is the one encoding that needs no negotiation and no second projection. This departs from the recorded design, which negotiates UTF-8 with a client that offers it: UTF-8 saves the conversion on an ASCII-heavy source, at the cost of a second projection and a negotiation, each to be tested apart, for a saving no measurement has shown matters beside a whole-document recheck. The choice reverses if a measurement shows the conversion costs a session more than a recheck does; the server then negotiates UTF-8 and the seam gains that column.

## The lifecycle and its error codes

| Phase | Request | Answer |
| ----- | ------- | ------ |
| before `initialize` | any but `initialize` | `-32002` server not initialized |
| running | `initialize` again | `-32600` invalid request |
| running | a method the server does not serve | `-32601` method not found |
| running | a served method with parameters it cannot read | `-32602` invalid params |
| running | a formatting request for a document the formatter refuses | `-32803` request failed, with the reason |
| after `shutdown` | any | `-32600` invalid request |
| any | a body outside the decoder-supported JSON fragment | `-32700` parse error, under a null id |
| any | decoded JSON that is not a request, notification or response, a batch included | `-32600` invalid request |

Before `initialize` every notification but `exit` is dropped. A notification is never answered: one whose parameters the server cannot read is dropped, a change to a document the server does not hold is dropped, and `$/` notifications and every other unknown one are ignored, as the protocol admits. A response from the client is read and discarded, since the server sends no request.

## Formatting answers the formatter's layout as edits

A formatting request parses the held text under the process's grammar and lays it out through `gandr-surface-format` at its default page of 100 columns, which keeps every token and comment, copies strings, shell blocks, holes and repaired forms as written, and refuses a layout whose parse differs from the text's. The answer is the edits that turn the held text into that layout; the server's copy changes only when the client applies them and synchronises back.

- **The whole document** answers no edit when the layout is the text's own, and otherwise one edit.
- **A range** answers one edit per top-level form whose span overlaps it, or holds it when the range is empty, and whose layout changed. A form carries the comments standing directly before it, as the formatter places them; the blank lines between forms are never edited. The formatter lays each top-level form out on its own, so a form's layout does not depend on its neighbours.
- **Every edit is trimmed** to the span between the longest prefix and the longest suffix the source and the layout share, both on character boundaries, so a client keeps its cursor, marks and undo granularity on every line the layout left alone.
- **A refusal** — a grammar that did not build, a parse that did not commit, or a layout the formatter refuses — answers `-32803` request failed with the reason, so the client says why the document was not formatted rather than silently leaving it.

The client's `options` — tab size, spaces or tabs — are read and set aside: the formatter's layout is the one `gandr fmt` writes, and a second layout per editor setting would make the two disagree. The alternatives were one edit replacing the whole document, which every client applies but which moves a cursor anywhere in it, and a minimal diff per line, which costs a diff for edits a client merges anyway. The choice reverses when a client is measured paying for the trimmed edit's size, or when the formatter gains settings a project chooses, which the server then reads from the workspace configuration rather than from `options`.

## The transport is written here

The framing, the envelope and the protocol types the server reads and writes are this crate's own, on `serde` and `serde_json` with `alloc` only. Each message the server writes is a typed value encoded once at the stream, so the field order on the wire is the struct's.

| Candidate | Why it lost |
| --------- | ----------- |
| `lsp-server` 0.10.0 | a body that is not JSON ends the connection with an I/O error rather than a parse-error answer; a declared length is allocated before a byte of the body arrives, with no ceiling; its message constructors unwrap; it brings `crossbeam-channel` threads and `log` for a loop this server runs on one thread |
| `lsp-types` 0.97.0 | the last release is from June 2024 and serves 3.16, with 3.17 behind an unstable feature; it carries the whole protocol, `bitflags` 1 and an old `fluent-uri` for the few types the server reads and writes |
| `ls-types` 0.0.6 | a 0.0 pre-release; the same whole-protocol surface for the same few types |
| `tower-lsp-server` 0.24.0-rc.1, `async-lsp` 0.2.4 | an async runtime and a service stack for a server that answers each request in order on one thread |

The reader limits an incoming header line to 1 KiB and an incoming body to 64 MiB, allocating body storage as bytes arrive rather than trusting the declared length. The writer emits the supplied body without applying those reader limits. The choice reverses when the server serves enough of the protocol that the types it writes outgrow a maintained crate's surface, or when a request must be answered concurrently with a recheck: then `ls-types`, or the async stack over it, is next.

## Document URIs

A document's URI is kept as the client spelled it, as the key it is synchronised and published under. Its path, for the root classification alone, is the `file` URI's path percent-decoded by `percent-encoding` 2.3.2 with `alloc` only, so `file:///x%C3%A9.gandr` names `/xé.gandr`. The alternatives were `fluent-uri` 0.4.1, a full RFC 3986 parser for one component, and `url` 2.5.8, whose `to_file_path` brings the WHATWG parser and internationalised domain names. The choice reverses when the server serves a workspace whose documents arrive under other schemes or remote authorities, which needs a parser.

## Coverage of the specification

Every feature of the protocol, 3.17 and 3.18, with whether this server serves it. Only a served feature is advertised: a capability with nothing behind it would invite requests the server can only refuse.

| Feature | Methods | State |
| ------- | ------- | ----- |
| lifecycle | `initialize`, `initialized`, `shutdown`, `exit` | served |
| document synchronisation | `textDocument/didOpen`, `didChange` (incremental), `didClose` | served |
| save notifications | `textDocument/willSave`, `willSaveWaitUntil`, `didSave` | declined: every change is judged as it arrives, so a save changes nothing the server holds |
| notebook synchronisation | `notebookDocument/*` | declined: gandr has no notebook format |
| published diagnostics | `textDocument/publishDiagnostics` | served |
| pulled diagnostics | `textDocument/diagnostic`, `workspace/diagnostic` | declined: every synchronisation publishes; reverses for a client that reads only pulled diagnostics |
| semantic tokens | `textDocument/semanticTokens/full`, `range` | served |
| semantic token deltas | `textDocument/semanticTokens/full/delta` | declined: a full answer per request; reverses when a measurement shows the transfer matters |
| inline completion | `textDocument/inlineCompletion` | served |
| document symbols | `textDocument/documentSymbol` | served |
| folding ranges | `textDocument/foldingRange` | served |
| selection ranges | `textDocument/selectionRange` | served |
| hover | `textDocument/hover` | served |
| inlay hints | `textDocument/inlayHint` | blocked: a binder's inferred type, which the resume records per item and not per binder |
| signature help | `textDocument/signatureHelp` | blocked: the declaration a call applies, which needs the use-to-binder map below |
| completion | `textDocument/completion` | blocked: goals whose types the checker spells |
| definition, declaration, type definition, implementation | `textDocument/definition`, `declaration`, `typeDefinition`, `implementation` | blocked: the lowering resolves every name but does not expose a use's binder |
| references, document highlight | `textDocument/references`, `documentHighlight` | blocked: the same use-to-binder map |
| rename, linked editing | `textDocument/prepareRename`, `rename`, `linkedEditingRange` | blocked: the same use-to-binder map |
| call hierarchy | `textDocument/prepareCallHierarchy`, `callHierarchy/*` | blocked: the same use-to-binder map |
| type hierarchy | `textDocument/prepareTypeHierarchy`, `typeHierarchy/*` | declined: the core has no subtyping to arrange types by |
| formatting | `textDocument/formatting`, `rangeFormatting` | served |
| on-type formatting | `textDocument/onTypeFormatting` | declined: a form's layout is decided once the form is whole, which range formatting at the cursor already serves on request |
| code actions, code lenses, commands | `textDocument/codeAction`, `codeLens`, `workspace/executeCommand` | blocked: no fix or command the pipeline produces |
| document links | `textDocument/documentLink` | blocked: imports bind an alias and resolve no address |
| document colours | `textDocument/documentColor`, `colorPresentation` | declined: gandr has no colour literals |
| inline values | `textDocument/inlineValue` | declined: they serve a debugger, and gandr has no debug adapter |
| monikers | `textDocument/moniker` | declined: no cross-repository index reads them |
| workspace symbols | `workspace/symbol` | blocked: a workspace of more than the open documents |
| workspace folders, file watching, file operations | `workspace/didChangeWorkspaceFolders`, `didChangeWatchedFiles`, `willCreateFiles` and the other file operations | blocked: a workspace of more than the open documents |
| configuration | `workspace/didChangeConfiguration`, `workspace/configuration` | blocked: the server has no setting yet |
| window messages and progress | `window/showMessage`, `logMessage`, `workDoneProgress/*` | declined: the timing line goes to the server's log; reverses for a client that reads only the protocol stream |
| gandr's extensions | `gandr/goals`, `gandr/syntaxTree`, `gandr/serverStatus`, the render-bus attach | blocked: each as [the assessment below](#extensions-beyond-the-specification) names |

## What editors add beyond the protocol

A client speaks the protocol; what it does with a method the protocol does not name decides where a gandr-specific view can live.

| Editor | Beyond the protocol | What it means here |
| ------ | ------------------- | ------------------ |
| VS Code | an extension sends any request through its language client and draws a webview panel of its own HTML; proposed APIs are closed to published extensions | the one editor where a rich goal view is a panel; it needs an extension, and its panel reads whatever the extension fetches |
| Neovim | a client sends any request and installs a handler for any notification; floating windows and virtual text draw the answer | a plain-text goal request is shown with a few lines of configuration and no extension |
| Emacs | `eglot` and `lsp-mode` send any JSON-RPC request; a buffer draws the answer | as Neovim: a plain-text goal request suffices |
| Helix | the standard protocol only; no plugin system yet | sees only the specification's features, so every extension must degrade to them |
| Zed | extensions launch a server and label its completions and symbols | as Helix today for anything beyond the specification |

The table fixes two rules. A gandr extension answers plain, already-laid-out text first, so the editors that can send a custom request show it without a gandr extension of their own; a structured view rides beside it, never in place of it. And nothing an editor needs to read a document correctly lives only in an extension: diagnostics, goals as diagnostics, hover and tokens stay in the specification, which Helix and Zed read.

## Extensions beyond the specification

The assessment the language server's coverage owes: the extensions three servers of the closest kind add, and which gandr takes up.

| Extension | Server | Recommendation | Why |
| --------- | ------ | -------------- | --- |
| a goal at a position: `$/lean/plainGoal`, `$/lean/plainTermGoal`; `proof/goals` | Lean 4; coq-lsp | **adopt** as `gandr/goals`: the goals the cursor's hole owes, each its expected type and its context, laid out by the printer as plain text, beside the same goals as `gandr-surface-render-remote`'s `GoalCard`s | the interaction model is holes and goals, which today reach an editor only as information diagnostics; blocked with completion on goals whose types the checker spells |
| the infoview: `$/lean/rpc/connect`, `$/lean/rpc/call`, user widgets | Lean 4 | **decline** the RPC session; the side view reads the render bus instead | a remote-procedure session per file worker, with references a client must release and keep alive, duplicates what the render bus frames already carry: versioned goal and diagnostic cards one renderer or many read |
| file checking progress: `$/lean/fileProgress`; coq-lsp's progress and viewport | Lean 4; coq-lsp | **decline** | both check on demand or in order and report how far they got; every synchronisation here judges the whole document and publishes at once, and the timing line already says what it cost |
| syntax tree view: `rust-analyzer/viewSyntaxTree` | rust-analyzer | **adopt** as `gandr/syntaxTree`: the molded tree of a document, its molds, tiles, layout and repairs, as text | the tree exists for every request already, and grammar and parser work reads it; a debugging aid, advertised as one |
| snippet text edits | rust-analyzer | **adopt** with code actions: a repair the parser recorded becomes a fix whose holes are tab stops | inline completion already writes snippets; waits on the code actions it would ride on |
| runnables: `experimental/runnables` | rust-analyzer | **decline** the method; a code lens over each declaration that evaluates, running it as `gandr run` does, once commands exist | the specification's lenses and commands carry it, so Helix and Zed see it too |
| hover actions | rust-analyzer | **decline** until definition and references exist | its actions are go-to and find-references links, which wait on the use-to-binder map |
| matching brace: `experimental/matchingBrace` | rust-analyzer | **decline** | selection ranges already grow from a tile to its form, and the client matches brackets itself |
| join lines: `experimental/joinLines`; on enter | rust-analyzer | **decline** | layout belongs to the source formatter, which formatting serves |
| server status: `experimental/serverStatus` | rust-analyzer | **adopt** as `gandr/serverStatus`: whether the latest revision's kernel admission is pending, done or refused | the admission runs after the diagnostics are published, and an editor cannot otherwise tell a revision the kernel has yet to admit from one it admitted |

**The goal view is both.** `gandr/goals` is the portable answer: plain text any client that sends a custom request shows, and the structured cards a richer one draws. The live side view, which follows the cursor and the check, reads the render bus: a terminal pane beside the editor reads its frames directly, and a VS Code webview attaches to the same frames through the language server's render-bus attach, so the cards a goal view draws are the ones every renderer draws. An extension method answers once per request; the bus streams what changed, so the side view is not a poll.

**Reversal.** A client that can show neither a custom request's text nor a side view, measured as the editor most authors use, moves goals into the specification's features alone — inlay hints at each hole, a hover over it. A render bus that cannot attach through the language server's stream moves the webview onto `gandr/goals` alone.

## Specification evidence

Executable predicates cover UTF-16 projection and errors, token kinds and grouping, half-open overlap, diagnostic shape, decoded URI bytes, request classification, lifecycle transitions and document publication. Captures retain only phase or counts; predicates do not clone server state, reparse documents or compose them twice.

Adequacy separates bounded observations from broader obligations. The overlap witness exhausts ordered spans and all query endpoint pairs in a five-offset domain, preserving input order and rejecting empty intersections. Other witnesses cover Unicode and line endings, framing ceilings, partial writes and flush failures, decoder refusals, lifecycle errors and ignored updates. The corpus observers independently walk the checked-in sources and compare diagnostics, causal labels and token bytes with the dispatcher and renderer; agreement is evidence over that corpus, not a proof for all programs.

Two effects cannot be observed by a useful return-value predicate: `serve` owns opaque generic input/output streams, and `Capabilities::fmt` writes through an opaque formatter. Their explicit exemptions are witnessed by framed sessions, the advertised JSON and a refused-write sink. Semantic diagnostic fields are asserted directly; diagnostic prose is compared with its renderer rather than pinned as English wording.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
