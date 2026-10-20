# gandr-surface-render-remote

The renderer seam of the gandr surface: highlight and mark spans, diagnostic and goal cards, transcript blocks and the byte-to-position projections a renderer reads, and the versioned render-bus frame that carries them across a process boundary.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** Three modules of owned data. `present` holds `HlSpan` and `MarkSpan` over a validated `ByteRange`, `DiagCard` and `GoalCard`, `TranscriptBlock` with its `OutKind` lines, `pos_of_byte` and `byte_of_pos`, the projection between a `ByteOffset` and a zero-based `Pos` of row and character column, and `LineIndex`, the projection between a `ByteOffset` and a zero-based `Utf16Pos` of row and UTF-16 column. `diagnostic` holds `DiagnosticCode`, the registry of stable codes with their localizable `DiagnosticTemplate`s, and `DiagnosticMessage`, a code's typed arguments. `wire` holds `RenderFrame`: a `FrameBody` — `Hello`, `Frame` carrying a `ReportView`, `Resync`, `Detach` — routed by a `FrameScope` to the connection or to one `DocId`, under `WIRE_SCHEMA_VERSION`. The crate is `no_std` over `core` and `alloc` and depends on no other workspace crate.

**Why.** A highlighter, a checker's report and a session loop each produce something a terminal, a language server or an agent paints, and each renderer must read the same vocabulary or the renderers fork. Putting that vocabulary in a crate that parses, lowers, types and marks nothing lets every renderer link it without linking the pipeline, and lets the pipeline project into it once. The frame is the same vocabulary for a renderer in another process.

**How.** Every type is owned data — strings, validated ranges and closed enums — so it crosses a thread channel as it is. The default-off `serde` feature derives a serde image for every type; the decode of a range and of a frame validates, so a decoded value holds every invariant a constructed one does. The character projection walks the text once per query; the line index records each row's start once and walks one row per query.

## Provided features

- `ByteOffset`, `ByteRange` and `InvertedRange`: a range's start is at or below its end, built or decoded. Witnesses: `present::tests::byte_range_ordering_includes_offset_extremes`, `present::tests::an_empty_range_is_a_position`, `present::tests::an_inverted_range_is_refused`, `present::tests::an_inverted_range_is_refused_on_decode`, `present::tests::range_and_position_errors_preserve_numeric_parameters`, `present::tests::byte_offsets_preserve_formatter_options`.
- `HlRole` and `HlSpan`: one role vocabulary for every renderer.
- `MarkKind` and `MarkSpan`: an error mark or an empty hole's tint, with its message.
- `DiagCard` and `GoalCard`: a refusal with its code, message, optional range, offending expression, elaboration note and derivation chain; a hole with its label, note, expected type, local context and range.
- `TranscriptBlock` and `OutKind`: an echoed submission, its highlights, and its result lines by kind.
- `SourceText`, `Pos`, `PositionRow`, `PositionColumn`, `pos_of_byte`, `byte_of_pos` and `PosOfByteError`: the projection. Witnesses: `present::tests::positions_round_trip_on_ascii`, `present::tests::positions_round_trip_on_multibyte_text`, `present::tests::positions_count_characters_not_bytes`, `present::tests::pos_of_byte_rejects_interior_multibyte_offsets`, `present::tests::out_of_range_positions_clamp`, `present::tests::the_empty_source_has_one_position`, `present::tests::the_end_of_the_source_is_a_position`.
- `LineIndex`, `Utf16Pos` and `Utf16Column`: the UTF-16 projection, over rows ended by `\n`, `\r\n` and a lone `\r`. Witnesses: `present::tests::utf16_columns_count_code_units_across_a_multibyte_boundary`, `present::tests::utf16_rows_end_at_every_protocol_terminator`, `present::tests::utf16_positions_clamp_past_the_end`, `present::tests::adjacent_terminators_preserve_empty_rows_and_crlf_clamping`.
- `DiagnosticCode`, `DIAGNOSTIC_CODES`, `DiagnosticTemplate`, `UnknownDiagnosticCode` and `DiagnosticMessage`: the code registry and the typed arguments. Witnesses: `diagnostic::tests::registry_codes_are_dense_unique_and_round_trip`, `diagnostic::tests::one_message_kind_has_one_code_independent_of_arguments`, `diagnostic::tests::code_wire_image_is_its_stable_spelling`, `diagnostic::tests::message_templates_preserve_argument_roles`.
- `RenderFrame`, `FrameScope`, `FrameBody`, `ReportView`, `DocId`, `DocumentUri`, `DocVersion`, `WireSchemaVersion` and `WIRE_SCHEMA_VERSION`: the frame. A report carries the document's text at its version, which its byte ranges address, so a renderer that holds no buffer of its own can place them; an image without the text decodes with it empty. Witnesses: `wire::tests::document_scoped_constructors_populate_routing_keys`, `wire::tests::connection_scoped_constructors_omit_routing_keys`, `wire::tests::every_body_variant_round_trips_through_json`, `wire::tests::a_report_written_without_its_source_still_decodes`, `wire::tests::a_frame_is_refused_at_another_schema_version`, `wire::tests::deserialize_rejects_doc_uri_doc_version_lockstep_violations`, `wire::tests::deserialize_rejects_body_routing_mismatches`, `wire::tests::frame_body_is_adjacently_tagged_on_the_wire`, `wire::tests::decode_refusals_preserve_validation_precedence`, `wire::tests::decode_error_display_preserves_diagnostic_parameters`.
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

## Where the detail lives

Mechanism, decisions with their alternatives and reversals, and witnesses live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| Readers, a leaf beside the pipeline, serialization behind a feature, forms not carried, references | [`src/lib.rs`](src/lib.rs) |
| Validated byte ranges, two column units, plain data built by name | [`present`](src/present.rs) |
| Stable diagnostic codes | [`diagnostic`](src/diagnostic.rs) |
| The frame | [`wire`](src/wire.rs) |

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
