# gandr-surface-lsp

The gandr language server: diagnostics and semantic tokens over the Language Server Protocol, served over any pair of byte streams.

<!-- toc -->

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Every synchronisation judges the document, publishes, then admits](#every-synchronisation-judges-the-document-publishes-then-admits)
- [Diagnostics are the renderer's reports](#diagnostics-are-the-renderers-reports)
- [Tokens are the highlighter's roles](#tokens-are-the-highlighters-roles)
- [Positions count UTF-16 code units](#positions-count-utf-16-code-units)
- [The lifecycle and its error codes](#the-lifecycle-and-its-error-codes)
- [The transport is written here](#the-transport-is-written-here)
- [Document URIs](#document-uris)
- [Methods the server does not serve](#methods-the-server-does-not-serve)
- [Specification evidence](#specification-evidence)
- [Deferred behavioral floor](#deferred-behavioral-floor)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** `gandr-surface-lsp` serves a subset of the Language Server Protocol 3.17: the base protocol's framing, the JSON-RPC 2.0 envelope with its standard error codes, the lifecycle from `initialize` to `exit`, incremental document synchronisation, `textDocument/publishDiagnostics` after every synchronisation, and `textDocument/semanticTokens/full` and `textDocument/semanticTokens/range`. `serve` runs one session over any `BufRead` and `Write` pair, logging one timing line per synchronisation to a third `Write`; `Capabilities` displays what `initialize` answers. The driver's `gandr lsp` serves it over standard input and output and logs to standard error.

**Why.** An editor should show what `gandr check` prints, where it prints it, while the source is written. The server is a face over the pipeline's own outputs, never a second pipeline: its diagnostics are the reports `gandr-surface-diagnostics` renders for the dispatcher's step, and its tokens are the roles `gandr-surface-grammar`'s highlighter classifies, so an editor, a terminal and a test cannot disagree about a refusal or a token.

**How.** Each open document holds a `gandr-surface-session` session under the source root its `file` URI's path classifies as. A synchronisation applies the client's changes to the held text and judges the text in the session, reads the judgement's step through `gandr-surface-diagnostics`' `entries` under `check --goals`, and publishes each report as one diagnostic: its span as the range, its refusal's vocabulary name as the code, its title, primary label and note as the message, its context loci as related information. Then it runs the kernel admission the judgement left. A token request parses the document, takes the highlighter's spans and delta-encodes them under the standard legend. Every position is a UTF-16 position read through `gandr-surface-render-remote`'s `LineIndex`. The server keeps the open documents' text and sessions and one grammar per process.

## References

- Microsoft. "Language Server Protocol Specification 3.17." <https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/> — the base protocol, the lifecycle, document synchronisation, published diagnostics, semantic tokens and the position encodings this server serves.
- JSON-RPC Working Group. "JSON-RPC 2.0 Specification." 2010, revised 2013. <https://www.jsonrpc.org/specification> — the envelope, the batch the server refuses, and the reserved error codes it answers with.
- Matthew Kerwin. "The 'file' URI Scheme." RFC 8089, February 2017. `doi:10.17487/RFC8089` — the URI a document is named by, whose percent-decoded path classifies its source root.

## Provided features

- `serve` and `Served`: one session over a stream pair and a log, ending cleanly at `exit` or boundary EOF after `shutdown`, and abruptly before shutdown. Witnesses: `session::session::a_session_round_trips_over_in_memory_streams`, `session::session::a_stream_closed_without_exit_ends_abruptly`, `server::tests::the_lifecycle_admits_requests_in_the_protocol_order`.
- Incremental synchronisation: each content change applied in order, a ranged one to its range and one naming no range as the whole text, and the document judged again in its session, which molds only the forms the change touched; one log line per synchronisation names the forms molded, the items the incremental checker judged, the recheck's wall and the admission's. Witnesses: `server::tests::ranged_changes_edit_the_held_text_in_order`, `session::session::an_edit_to_a_large_document_rechecks_its_forms`.
- `Server::admit`: the kernel admission each synchronisation left, run once its diagnostics are published. Witnesses: `server::tests::an_admission_follows_its_synchronisation`, `recheck::tests::an_admission_follows_the_published_diagnostics`.
- `read_frame`, `read_frame::Absent`, `write_frame`, `Body` and `TransportFault`: the base protocol's framing, with a ceiling on a header line and on a body. Witnesses: `transport::tests::a_round_trip_preserves_the_payload`, `transport::tests::eof_at_a_boundary_is_clean`, `transport::tests::a_header_block_the_framing_cannot_read_is_refused`.
- The envelope: requests, notifications and responses told apart; a body outside the decoder-supported JSON fragment answered with a parse error, including invalid UTF-8 and exceeded number or nesting limits; a decoded batch or other invalid message refused as an invalid request. Witnesses: `rpc::tests::a_request_is_classified`, `rpc::tests::a_batch_is_rejected`, `rpc::tests::decoder_rejections_keep_the_parse_error_class`.
- Published diagnostics: one per report the renderer gives the document's step, at its range, under its code, with its message and related information; republished at every change, cleared at close. Witnesses: `server::tests::a_refused_program_is_published_as_an_editor_diagnostic`, `server::tests::synchronisation_publishes_and_close_clears`, `recheck::tests::causal_contexts_become_lsp_related_information`, `recheck::tests::a_labeled_context_keeps_its_locus_and_cause_in_related_information`, `recheck::tests::a_refusal_publishes_its_label_and_note`, `recheck::tests::a_fault_is_published_at_the_origin`, `session::session::a_refusal_is_published_where_the_renderer_renders_it`, `session::session::every_corpus_report_is_published_where_the_walk_renders_it`.
- Semantic tokens for the whole document and for a range, and `TOKEN_TYPES` and `TOKEN_MODIFIERS`, the legend. Witnesses: `tokens::tests::every_classified_role_maps_inside_the_legend`, `tokens::tests::the_legend_index_a_role_emits_names_what_that_role_means`, `tokens::tests::a_one_line_keyword_encodes_as_five_integers`, `tokens::tests::a_multiline_span_splits_and_drops_the_terminator`, `server::tests::semantic_tokens_full_answers_a_known_document`, `server::tests::a_range_returns_only_the_tokens_it_covers`, `server::tests::a_range_over_the_whole_document_agrees_with_the_full_stream`, `server::tests::a_token_straddling_the_range_edge_is_returned_whole`, `server::tests::an_inverted_range_yields_no_tokens`, `server::tests::an_empty_range_yields_no_tokens`, `recheck::tests::a_definition_produces_semantic_tokens`, `session::session::corpus_tokens_cover_the_highlighted_bytes`.
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
| a refusal | the primary span | the refusal's vocabulary name | error | the title, the primary label and the note | each context locus, with its label |
| an unsettled declaration | the primary span | none | error | the title and the primary label | each context locus, with its label |
| a goal | the primary span | none | information | the title and the primary label | none |
| a report the renderer leaves unlocated | the document's origin | as its kind | as its kind | the title, and the note of a refusal | none |
| a ledger line | the document's origin | none | error | the line | none |
| a fault before composition | the document's origin | none | error | the fault | none |

The message carries every line the terminal prints around the snippet: the title, then the primary locus's label on a line of its own, then a refused declaration's note after `note: `. The protocol gives a diagnostic one text field beside its range and related locations, so a label the underline carries in the terminal would otherwise never reach the editor. The alternative is the title alone, which leaves an editor user without the one line that says what the span is. The choice reverses when the protocol gains a field for the primary locus's label.

Every diagnostic's `source` is `gandr`. The code is the spelling a corpus `refuses` attribute states and a snippet's first line carries, so a code copied from the editor is an expectation a test can state. The alternative was the renderer seam's `DiagnosticCode` registry; the pipeline maps no refusal onto a registry code yet, and mapping refusals onto it here would be a second decision made in a face. The choice reverses when the pipeline's session report maps its refusals onto registry codes: the diagnostic's code becomes that spelling.

A goal is published at information severity because `check --goals` prints it as a report that does not fail the run. The alternative was the verb `check`, which withholds goals; an editor showing an open hole's goal beside it is the use the goal report exists for.

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

## Positions count UTF-16 code units

The server advertises `positionEncoding: "utf-16"` and counts every range, related location and token in UTF-16 code units through the renderer seam's `LineIndex`, whose rows end at `\n`, `\r\n` and a lone `\r` as the protocol's do. UTF-16 is the encoding every client must support, so it is the one encoding that needs no negotiation and no second projection. This departs from the recorded design, which negotiates UTF-8 with a client that offers it: UTF-8 saves the conversion on an ASCII-heavy source, at the cost of a second projection and a negotiation, each to be tested apart, for a saving no measurement has shown matters beside a whole-document recheck. The choice reverses if a measurement shows the conversion costs a session more than a recheck does; the server then negotiates UTF-8 and the seam gains that column.

## The lifecycle and its error codes

| Phase | Request | Answer |
| ----- | ------- | ------ |
| before `initialize` | any but `initialize` | `-32002` server not initialized |
| running | `initialize` again | `-32600` invalid request |
| running | a method the server does not serve | `-32601` method not found |
| running | a served method with parameters it cannot read | `-32602` invalid params |
| after `shutdown` | any | `-32600` invalid request |
| any | a body outside the decoder-supported JSON fragment | `-32700` parse error, under a null id |
| any | decoded JSON that is not a request, notification or response, a batch included | `-32600` invalid request |

Before `initialize` every notification but `exit` is dropped. A notification is never answered: one whose parameters the server cannot read is dropped, a change to a document the server does not hold is dropped, and `$/` notifications and every other unknown one are ignored, as the protocol admits. A response from the client is read and discarded, since the server sends no request.

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

## Methods the server does not serve

| Method | Who brings it |
| ------ | ------------- |
| `textDocument/hover` | the hover over a hole's goal, once the hole surface carries goals and the checker spells their types |
| `textDocument/completion` | the completion over goals, with the same two prerequisites |
| the render-bus attach and custom `gandr/` methods | a renderer in another process reading `gandr-surface-render-remote`'s frames |
| formatting | the printer, once the surface has one |

None is advertised: a capability with nothing behind it would invite requests the server can only refuse.

## Specification evidence

Executable predicates cover UTF-16 projection and errors, token kinds and grouping, half-open overlap, diagnostic shape, decoded URI bytes, request classification, lifecycle transitions and document publication. Captures retain only phase or counts; predicates do not clone server state, reparse documents or compose them twice.

Adequacy separates bounded observations from broader obligations. The overlap witness exhausts ordered spans and all query endpoint pairs in a five-offset domain, preserving input order and rejecting empty intersections. Other witnesses cover Unicode and line endings, framing ceilings, partial writes and flush failures, decoder refusals, lifecycle errors and ignored updates. The corpus observers independently walk the checked-in sources and compare diagnostics, causal labels and token bytes with the dispatcher and renderer; agreement is evidence over that corpus, not a proof for all programs.

Two effects cannot be observed by a useful return-value predicate: `serve` owns opaque generic input/output streams, and `Capabilities::fmt` writes through an opaque formatter. Their explicit exemptions are witnessed by framed sessions, the advertised JSON and a refused-write sink. Semantic diagnostic fields are asserted directly; diagnostic prose is compared with its renderer rather than pinned as English wording.

## Deferred behavioral floor

| Deferred witness | Missing former or reader |
| ---------------- | ------------------------ |
| `hover_at_the_origin_is_total` | Type-aware hover reader |
| `hovering_a_defined_name_reports_its_type` | Type-aware hover reader |
| `words_inside_comments_and_strings_do_not_hover` | Type-aware hover reader |
| `a_parameter_does_not_hover_as_an_unrelated_top_level_definition` | Type-aware hover reader |
| `hovering_an_unknown_name_is_none` | Type-aware hover reader |
| `the_word_scan_accepts_the_cursor_at_either_edge` | Type-aware hover reader |
| `an_earlier_redefined_name_hovers_its_own_type` | Type-aware hover reader |
| `a_redefined_name_hovers_its_latest_type` | Type-aware hover reader |

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
