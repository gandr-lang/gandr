# gandr-surface-repl

The read-evaluate loop over the interactive session: the completeness gate, the session loop and its meta-commands, the transcript encoder, and the batch and line-editor faces `gandr repl` runs.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** A `SessionLoop` takes lines and answers `LoopEvent`s. A line opening with `:` while no buffer waits is a meta-command — `:type <expression>`, `:load <file>`, `:reload`, `:reset`, `:help`, `:quit` or `:q`; any other line joins the buffer, and once the parser expects no further token the buffer is submitted to a `gandr-surface-session` `Session` as the next chunk of one growing revision. `:reload` resubmits each loaded file whose text on disk differs from its chunk in that chunk's place, kept only when nothing after it refuses the new text. `encode_submission` turns the session's answer into a `gandr-surface-render-remote` `TranscriptBlock`: the echo with its highlight spans, a type line `name : T` per checked declaration the chunk introduced or settled followed by the line of what running it came to, a goal line per declaration it left owing, the diagnostics renderer's report per refusal, and a warning per parse repair. `run_batch` drives the loop over any reader and writes a plain transcript; `run_interactive` drives it over a terminal through a line editor, and prints a notice above the line being edited when a loaded file changes on disk.

**Why.** The session judges revisions; a person types lines. The loop is what stands between: it decides when a buffer is worth submitting, owns the text the session judges, decides what of a revision is new, and says it in the vocabulary every renderer reads, so the line editor, the terminal face `gandr tui` and a pipe show the same lines.

**How.** The gate molds the buffer through the parser's push machine and submits when nothing is expected. The loop keeps the accepted text — every chunk kept so far — and submits it with the new chunk after it; the session runs the dispatcher's composition, so its verdicts are `gandr check --goals`'s for that text under the strict root. The encoder reads the step's diagnostics off the dispatcher's `entries`, laid out by `gandr-surface-render-terminal`, the settle report's declarations for what changed, and the incremental checker's checkpoints for each declaration's type, which `spell` lays out through the presentation printer, `gandr-surface-pretty`. The chunk joins the accepted text only when nothing was refused.

## Provided features

- **The gate.** `completeness` and the parser's `CompletionStatus`, re-exported. Witnesses: `tests::repl_loop::an_open_form_is_incomplete`, `tests::repl_loop::a_bare_atom_is_complete`, `tests::repl_loop::a_hole_is_complete`, `tests::repl_loop::a_declaration_waits_for_its_terminator`, `tests::repl_loop::an_empty_buffer_is_complete`.
- **The loop.** `SessionLoop`, `SessionLoop::new`, `offer`, `finish`, `prompt`, `discard`, `loaded`; `LoopEvent`, `Prompt`, `LoopError`, `Faulted`, `finished::Absent`. Witnesses: `tests::repl_loop::an_open_form_continues`, `tests::repl_loop::a_complete_atom_submits`, `tests::repl_loop::a_definition_is_visible_on_the_next_line`, `tests::repl_loop::a_refused_chunk_is_not_kept`, `tests::repl_loop::quit_stops_the_loop`, `tests::repl_loop::the_meta_commands_answer`, `tests::repl_loop::the_type_command_answers_without_keeping_the_probe`, `tests::repl_loop::a_loaded_file_is_one_chunk`, `tests::repl_loop::a_reloaded_file_replaces_its_chunk`, `tests::repl_loop::an_incomplete_buffer_is_submitted_at_end_of_input`, `tests::repl_loop::finishing_an_empty_loop_yields_nothing`, `tests::repl_loop::finishing_twice_reports_once`.
- **The encoder.** `encode_submission`, `Offer`, `Echo`, `Subject`, `Standings`, `Encoded`, `Disposition`. Witnesses: `tests::repl_loop::a_hole_encodes_as_a_goal_line`, `tests::repl_loop::a_later_definition_settles_an_earlier_goal`, `tests::repl_loop::an_outcome_only_refusal_is_visible_in_the_repl`, `tests::repl_loop::styled_session_diagnostics_reach_the_repl_transcript`, `render::tests::eval_renders_each_outcome_class`.
- **Live matching.** `encode_match` presents a session `MatchAnalysis`: per-arm yes/no/possibly answers, the selected or held arm, and independent exhaustiveness. It writes the same transcript seam as ordinary submissions, without turning coverage into admission. Witness: `tests::live_match::a_fill_updates_the_external_match_transcript`.
- **The type spelling.** `spell`, answering the printer's `Presentation` at the transcript's width. Witnesses: `tests::repl_loop::corpus_types_spell_as_their_source_writes_them`, `tests::repl_loop::a_dependent_function_names_its_type_with_its_binder`.
- **The echo's highlights.** `highlight_source`, `span_order`, `SpanOrder`. Witnesses: `highlight::tests::a_keyword_is_classified`, `highlight::tests::spans_are_sorted_and_disjoint`, `highlight::tests::the_disjointness_predicate_rejects_an_overlap`, `highlight::tests::an_unclassifiable_buffer_yields_no_panic`, `tests::repl_loop::a_submission_carries_highlight_spans`, `tests::repl_loop::transcript_spans_are_sorted_and_disjoint`.
- **Repair cards.** `repair_cards`. Witnesses: `remote::tests::cards_preserve_the_report_rows`, `remote::tests::a_clean_source_produces_no_cards`.
- **The faces.** `run_batch`, `write_block`, `run_interactive`, `drive`, `LineSource`, `Read`, `Ended`, `Fault`, `DiskWatch`, `disk_notice`. Witnesses: `tests::repl_loop::piped_value_prints_a_transcript`, `tests::repl_loop::an_unparseable_pipe_reports_rather_than_going_quiet`, `tests::repl_loop::unreadable_input_ends_the_batch_faulted`, `tests::repl_loop::the_terminal_face_discards_on_interrupt_and_submits_at_the_end`, `watch::tests::a_loaded_file_rewritten_is_noticed_once_per_line`.
- **The rows.** `rows`, `Row`, `Lead`, `Mark`: a block's one layout, which `write_block` prints. Witnesses: `tests::repl_loop::a_block_lays_out_as_rows`, `tests::repl_loop::piped_value_prints_a_transcript`.

## Expected features

- **A terminal, for the line-editor face.** `run_interactive` edits lines on the terminal standard input is attached to; the driver runs the batch face when standard input is not a terminal.

## Examples

```console
$ printf 'def answer = 42 ;\n:type answer\ndef later : String ;\n' | gandr repl
▸ def answer = 42 ;
answer : Integer
= 42
▸ :type answer
: Integer
▸ def later : String ;
? later : String
```

The crate's tests run with `cargo nextest run -p gandr-surface-repl`.

## Where the detail lives

Mechanism, decisions with their alternatives and reversals, and witnesses live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| A verb of the driver, kept chunks, the transcript, specification evidence, references | [`src/lib.rs`](src/lib.rs) |
| The line editor | [`interactive`](src/interactive.rs) |
| The loop reads declarations | [`session_loop`](src/session_loop.rs) |
| Completeness is the parser's | [`completeness`](src/completeness.rs) |
| Types spelled from the checkpoints, native universe-path presentation | [`render`](src/render.rs) |
| Repairs are cards | [`remote`](src/remote.rs) |
| A checked declaration prints what it runs to | [`encode`](src/encode.rs) |

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
