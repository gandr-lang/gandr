# gandr-surface-render-remote

The renderer seam of the gandr surface: highlight and mark spans, diagnostic and goal cards, transcript blocks and the byte-to-position projections a renderer reads, and the versioned render-bus frame that carries them across a process boundary.

<!-- toc -->

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Readers](#readers)
- [A leaf beside the pipeline](#a-leaf-beside-the-pipeline)
- [Serialization behind a feature](#serialization-behind-a-feature)
- [Validated byte ranges](#validated-byte-ranges)
- [Two column units](#two-column-units)
- [Plain data built by name](#plain-data-built-by-name)
- [Stable diagnostic codes](#stable-diagnostic-codes)
- [The frame](#the-frame)
- [Forms this crate does not carry](#forms-this-crate-does-not-carry)
- [Deferred behavioral floor](#deferred-behavioral-floor)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** Three modules of owned data. `present` holds `HlSpan` and `MarkSpan` over a validated `ByteRange`, `DiagCard` and `GoalCard`, `TranscriptBlock` with its `OutKind` lines, `pos_of_byte` and `byte_of_pos`, the projection between a `ByteOffset` and a zero-based `Pos` of row and character column, and `LineIndex`, the projection between a `ByteOffset` and a zero-based `Utf16Pos` of row and UTF-16 column. `diagnostic` holds `DiagnosticCode`, the registry of stable codes with their localizable `DiagnosticTemplate`s, and `DiagnosticMessage`, a code's typed arguments. `wire` holds `RenderFrame`: a `FrameBody` — `Hello`, `Frame` carrying a `ReportView`, `Resync`, `Detach` — routed by a `FrameScope` to the connection or to one `DocId`, under `WIRE_SCHEMA_VERSION`. The crate is `no_std` over `core` and `alloc` and depends on no other workspace crate.

**Why.** A highlighter, a checker's report and a session loop each produce something a terminal, a language server or an agent paints, and each renderer must read the same vocabulary or the renderers fork. Putting that vocabulary in a crate that parses, lowers, types and marks nothing lets every renderer link it without linking the pipeline, and lets the pipeline project into it once. The frame is the same vocabulary for a renderer in another process.

**How.** Every type is owned data — strings, validated ranges and closed enums — so it crosses a thread channel as it is. The default-off `serde` feature derives a serde image for every type; the decode of a range and of a frame validates, so a decoded value holds every invariant a constructed one does. The character projection walks the text once per query; the line index records each row's start once and walks one row per query.

## References

- Eric Zhao, Raef Maroof, Anand Dukkipati, Andrew Blinn, Zhiyi Pan, and Cyrus Omar. "Total Type Error Localization and Recovery with Holes." _Proceedings of the ACM on Programming Languages_ 8, POPL (January 2024). `doi:10.1145/3632910` — marks: an error located at the term it concerns, and an empty hole tinted rather than reported, which `MarkSpan` and `MarkKind` carry.
- Kohei Honda, Vasco T. Vasconcelos, and Makoto Kubo. "Language Primitives and Type Discipline for Structured Communication-Based Programming." In _Programming Languages and Systems (ESOP 1998)_, Lecture Notes in Computer Science 1381, pages 122–138, 1998. `doi:10.1007/BFb0053567` — the binary session the frame's message set is the projection of.
- Simon J. Gay and Malcolm Hole. "Subtyping for Session Types in the Pi Calculus." _Acta Informatica_ 42, 2–3 (2005), pages 191–225. `doi:10.1007/s00236-005-0177-z` — the subtyping under which a typed endpoint can later carry the same messages.
- Microsoft. "Language Server Protocol Specification 3.17." <https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/> — the document URI and version a frame is routed by, and the position encoding a language server converts a character column into.

## Provided features

- `ByteOffset`, `ByteRange` and `InvertedRange`: a range's start is at or below its end, built or decoded. Witnesses: `present::tests::byte_range_ordering_includes_offset_extremes`, `present::tests::an_empty_range_is_a_position`, `present::tests::an_inverted_range_is_refused`, `present::tests::an_inverted_range_is_refused_on_decode`, `present::tests::range_and_position_errors_preserve_numeric_parameters`, `present::tests::byte_offsets_preserve_formatter_options`.
- `HlRole` and `HlSpan`: one role vocabulary for every renderer.
- `MarkKind` and `MarkSpan`: an error mark or an empty hole's tint, with its message.
- `DiagCard` and `GoalCard`: a refusal with its code, message, optional range, offending expression, elaboration note and derivation chain; a hole with its label, note, expected type, local context and range.
- `TranscriptBlock` and `OutKind`: an echoed submission, its highlights, and its result lines by kind.
- `SourceText`, `Pos`, `PositionRow`, `PositionColumn`, `pos_of_byte`, `byte_of_pos` and `PosOfByteError`: the projection. Witnesses: `present::tests::positions_round_trip_on_ascii`, `present::tests::positions_round_trip_on_multibyte_text`, `present::tests::positions_count_characters_not_bytes`, `present::tests::pos_of_byte_rejects_interior_multibyte_offsets`, `present::tests::out_of_range_positions_clamp`, `present::tests::the_empty_source_has_one_position`, `present::tests::the_end_of_the_source_is_a_position`.
- `LineIndex`, `Utf16Pos` and `Utf16Column`: the UTF-16 projection, over rows ended by `\n`, `\r\n` and a lone `\r`. Witnesses: `present::tests::utf16_columns_count_code_units_across_a_multibyte_boundary`, `present::tests::utf16_rows_end_at_every_protocol_terminator`, `present::tests::utf16_positions_clamp_past_the_end`, `present::tests::adjacent_terminators_preserve_empty_rows_and_crlf_clamping`.
- `DiagnosticCode`, `DIAGNOSTIC_CODES`, `DiagnosticTemplate`, `UnknownDiagnosticCode` and `DiagnosticMessage`: the code registry and the typed arguments. Witnesses: `diagnostic::tests::registry_codes_are_dense_unique_and_round_trip`, `diagnostic::tests::one_message_kind_has_one_code_independent_of_arguments`, `diagnostic::tests::code_wire_image_is_its_stable_spelling`, `diagnostic::tests::message_templates_preserve_argument_roles`.
- `RenderFrame`, `FrameScope`, `FrameBody`, `ReportView`, `DocId`, `DocumentUri`, `DocVersion`, `WireSchemaVersion` and `WIRE_SCHEMA_VERSION`: the frame. Witnesses: `wire::tests::document_scoped_constructors_populate_routing_keys`, `wire::tests::connection_scoped_constructors_omit_routing_keys`, `wire::tests::every_body_variant_round_trips_through_json`, `wire::tests::a_frame_is_refused_at_another_schema_version`, `wire::tests::deserialize_rejects_doc_uri_doc_version_lockstep_violations`, `wire::tests::deserialize_rejects_body_routing_mismatches`, `wire::tests::frame_body_is_adjacently_tagged_on_the_wire`, `wire::tests::decode_refusals_preserve_validation_precedence`, `wire::tests::decode_error_display_preserves_diagnostic_parameters`.
- `serde`, off by default: the serde image of every type above, with the validating decode of `ByteRange` and `RenderFrame`.

## Expected features

- **A producer.** The crate classifies, marks and checks nothing: spans come from a highlighter, marks from a marking pass, cards from a checker's report, transcript blocks from a session loop.
- **A serde format, under the feature.** The crate derives the serde data model; a transport chooses the format. The witnesses use JSON.

## Examples

```rust
use gandr_surface_render_remote::ByteOffset;
use gandr_surface_render_remote::ByteRange;
use gandr_surface_render_remote::DocId;
use gandr_surface_render_remote::DocVersion;
use gandr_surface_render_remote::DocumentUri;
use gandr_surface_render_remote::FrameScope;
use gandr_surface_render_remote::HlRole;
use gandr_surface_render_remote::HlSpan;
use gandr_surface_render_remote::Pos;
use gandr_surface_render_remote::PositionColumn;
use gandr_surface_render_remote::PositionRow;
use gandr_surface_render_remote::RenderFrame;
use gandr_surface_render_remote::ReportView;
use gandr_surface_render_remote::SourceText;
use gandr_surface_render_remote::pos_of_byte;

let source = "def x = 1 ;\ndef y = x ;";
let keyword = HlSpan {
    range: ByteRange::new(ByteOffset::from(12_usize), ByteOffset::from(15_usize))?,
    role: HlRole::Keyword,
};
assert_eq!(
    pos_of_byte(SourceText::from(source), keyword.range.start())?,
    Pos {
        row: PositionRow::from(1_usize),
        col: PositionColumn::from(0_usize),
    },
    "the second line's keyword opens the second row"
);

let document = DocId {
    uri: DocumentUri::from(String::from("file:///example.gandr")),
    version: DocVersion::from(3_i32),
};
let frame = RenderFrame::frame(
    document.clone(),
    ReportView {
        highlights: vec![keyword],
        ..ReportView::default()
    },
);
assert_eq!(
    frame.scope(),
    &FrameScope::Document(document),
    "a report frame is routed to its document"
);
```

The same example is the crate-level doctest. `cargo nextest run -p gandr-surface-render-remote` runs every test, the codec witnesses included. Set `RUSTFLAGS="--cfg anodized_panic"` to execute the specification predicates as well. Each nontrivial item names its bounded evidence under `# Adequacy`: independent images and boundary observations are L3; finite round-trips are L2, not independent oracles. Formatting witnesses preserve parameter roles rather than English sentences.

## Readers

Each form here has a reader that lands with it or next:

| Form | Reader |
| ---- | ------ |
| `HlRole`, `HlSpan`, `ByteOffset`, `ByteRange` | the mold highlighter in `gandr-surface-grammar`, which classifies each tile by its mold; then the language server's semantic tokens, the read-evaluate loop's echo and the terminal face's paint |
| `DiagCard`, `DiagnosticCode`, `DiagnosticMessage` | the read-evaluate loop's parse-repair cards under `W0012`; the session report that maps refusals onto codes, and the language server's diagnostics once they carry that report's codes |
| `TranscriptBlock`, `OutKind` | the read-evaluate loop's transcript encoder and the terminal face that draws it |
| `SourceText`, `Pos`, `pos_of_byte`, `byte_of_pos` | a renderer that addresses rows and columns: the terminal face's cursor, the language server's ranges |
| `LineIndex`, `Utf16Pos`, `Utf16Column` | the language server's diagnostic ranges, related locations and semantic tokens |
| `MarkSpan`, `GoalCard`, `RenderFrame` | a renderer in another process, through the frame's report |

## A leaf beside the pipeline

The crate depends on no workspace crate. A renderer that links it links strings, ranges and enums, never the parser, the checker or their dependencies, and nothing the pipeline adds can make a renderer re-implement typing: if a renderer needs information this vocabulary cannot carry, the fix is a field here filled by the pipeline, so every renderer gains it at once. `ByteOffset` is therefore this crate's own, not the concrete syntax tree's; a producer converts at its edge.

The alternatives were reusing the syntax tree's offset and span, which ties every renderer to the tree crate and its digest and specification dependencies, and a vocabulary per renderer, which forks the moment two renderers paint one report. The choice reverses only if a renderer genuinely needs the tree itself, which would make it a pipeline stage rather than a renderer.

## Serialization behind a feature

`serde` is off by default. It enables serde with `alloc`, for the owned strings and vectors and the tagged enums' buffered content, and `derive`. JSON (`serde_json`, `alloc` only) is a development dependency: the codec witnesses round-trip through it, and the crate chooses no format for a transport. The crate also names itself as a development dependency with `serde` on, so every test build carries the codec and the workspace suite runs the witnesses the serde impls cite; the default library build stays without it.

An in-process renderer pays for no serialization machinery. The alternatives were serde always on, which compiles the derive stack into every renderer, and a hand-written codec, which owns a format serde already provides through its data model. The choice reverses on a high-risk advisory or an unmaintained mark against serde, or on a transport whose format serde cannot carry.

## Validated byte ranges

`ByteRange::new` refuses an end below the start with `InvertedRange` rather than reordering the endpoints, which would turn a mis-measured span into a plausible one; an empty range is a position. The range's fields are private, so every range a span or a card carries is ordered, and the serde decode runs the same check. The wire image is `{"start": s, "end": e}`.

The alternative was the standard half-open `Range` with public fields, which admits an inverted range every renderer must defend against on every read. The choice reverses if a producer needs a directed range — a selection with an anchor — which would be a separate type rather than a relaxation of this one.

## Two column units

`pos_of_byte` counts the newlines before an offset for its row and the characters after the last of them for its column; a newline belongs to the row it ends. An offset at or past the end of the text is the position after its last character, so the empty text has the one position `0:0`. An offset strictly inside a multi-byte character is refused with `PosOfByteError`. `byte_of_pos` inverts it on every character start, clamping a column past its row's end to that row's newline and a row past the last to the end of the text.

`LineIndex` records the offset each row of one text starts at and projects against those starts in UTF-16 code units. `utf16_pos_of_byte` finds an offset's row by binary search and counts the units of the characters between the row's start and the offset, two for a character beyond the basic plane; an offset inside a character is refused with `PosOfByteError`, and one at or past the end is the position after the last character. `byte_of_utf16_pos` inverts it on content-character starts and the first byte of a terminator, resolving a column between the two units of such a character to its first byte, a column past its row's end to the row's terminator, and a row past the last to the end of the text. The LF inside CRLF projects beyond the content column and maps back to the preceding CR. Its rows end at `\n`, `\r\n` and a lone `\r`, the three terminators the language server protocol fixes, where `pos_of_byte` ends a row at `\n` alone; `row_bytes` gives a row's bytes without its terminator, the extent a span crossing rows is split by.

A character column is what an editor widget addresses; a UTF-16 column is what the language server protocol addresses by default and what every client accepts. Both projections live here so the language server reads its positions off the seam rather than re-deriving them. The alternatives were the language server converting character columns at its own boundary, which re-derives the projection in a second crate and walks each row twice, and one UTF-16 projection for every reader, which no editor widget addresses. The line index is built once per text because a language server projects every span of a document against the same text; `pos_of_byte` stays a per-query walk for a reader that projects one offset. The UTF-16 unit reverses if the language server negotiates UTF-8 or UTF-32 positions with a client that offers them, which adds that unit's column here.

## Plain data built by name

Spans, cards, transcript blocks, positions, document identities and reports are structs with public fields, built by naming each field. Two fields of one type — a range's endpoints aside — cannot be swapped by a positional call because there is none, and a reader matches on fields directly. A card's optional field is `Option`, the wire form of a value the producer did not supply: `null` in the image, never a guessed stand-in such as an enclosing range for an unlocated refusal. A mark's kind is the two-variant `MarkKind`, not a flag.

The alternatives were positional constructors, which admit swapped arguments of one type, and private fields behind accessors, which add surface without an invariant to keep. The choice reverses for a type that gains an invariant between its fields, which then takes private fields and a checking constructor, as `ByteRange` has.

## Stable diagnostic codes

`DiagnosticCode` is a registry of twelve codes, each spelled by a severity letter — `E` for an error, `W` for a warning — and its allocation number, `E0001` to `W0012`, and each carrying one localizable `DiagnosticTemplate` with its arguments named in braces. A code's spelling and its template occur once, in its registry row; the spelling is the code's display, its parse and its wire image. A code is never reused: a code nothing raises keeps its row. `DiagnosticMessage` is one variant per code with the template's arguments as fields, and its display fills the template.

The alternatives were the variant name as the wire image, which a rename breaks for every stored report, and free text, which a reworded message breaks for every reader matching it. The choice reverses if translations come to key on something other than the code.

## The frame

A `RenderFrame` is a `FrameBody` under a `FrameScope`. `Frame` and `Resync` are document-scoped: they carry the document's URI and the editor's version of it, the version the report describes, and a renderer paints a report only while that version matches the buffer it shows, asking for a resync otherwise, so a stale report is dropped rather than painted. `Hello`, the documents a server tracks, and `Detach` are connection-scoped. The four constructors are the only way to build a frame, so the scope always suits the body.

The wire image is `{"schema_version", "doc_uri", "doc_version", "body"}`, the body adjacently tagged by `kind` and `data`, the two routing keys `null` for a connection-scoped frame. The decode refuses another schema version, one routing key without the other, and routing that disagrees with the body, each with a message naming the broken rule. `WIRE_SCHEMA_VERSION` is `1`; it moves when a wire field is renamed, removed or changes meaning, and an added field leaves it.

The message set is the projection of one binary session, `?Attach . !Hello . μX. (!Frame . X & ?Resync . X & ?Detach . end)`, so a typed endpoint can later carry these frames as its messages without a change to them.

The alternative was two optional routing fields on the frame itself, which admits a URI without a version in memory and leaves the check to every reader. The choice reverses if a body ever concerns several documents at once, which would replace the scope's single document with a set.

## Forms this crate does not carry

Each form below is left out because no reader is scheduled for it; each arrives with the reader named beside it, and not before, because a form nothing reads is an untested promise.

| Form | Arrives with |
| ---- | ------------ |
| a node-keyed delta body, its patch form and the capability that advertises it | an incremental delta engine that produces patches, together with a renderer that applies them; until then every report is a whole `Frame` |
| obligation cards and their severity-ordered classes, and the capability that advertises them | the same delta engine's reader; until then a parser's recovery obligation can reach a renderer as a `DiagCard` under `W0012` |
| a capability advertisement on `Hello` | the first capability a server can back; a flag with no machinery behind it would advertise a channel no server fills |
| the typing machine's projection: the derivation forest, the control register, the frame-stack summary and the machine digest | an inspection face that paints the typing machine; the forest arrives as an arena of nodes addressed by id, never as nodes that own their children |
| attribute cards | an attribute inspection face |
| the type under a cursor and completion candidates | the language server's hover and completion over goals, once hole goals and the checker's spellings carry them |
| a preview frame of the buffer before submission | a terminal face that previews a buffer before it is submitted |

## Deferred behavioral floor

| Deferred witness | Missing former or reader |
| ---------------- | ------------------------ |
| `wire::projection_part_constructors_store_fields_verbatim` | Typing-machine projection reader |
| `wire::control_and_direction_defaults_are_the_projection_idle_states` | Typing-machine projection reader |
| `wire::mvp_capabilities_are_whole_frame_only` | Server capability advertisement |
| `wire::the_obligation_capability_is_the_row_capability` | Obligation-card wire reader |
| `wire::frames_round_trip_obligation_rows_and_an_empty_row_set` | Obligation-card wire reader |
| `present::obligation_classes_are_declared_low_severity_to_high` | Obligation-card wire reader |
| `wire::report_view_defaults_without_attributes` | Attribute-card wire reader |

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
