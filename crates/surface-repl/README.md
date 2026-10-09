# gandr-surface-repl

The read-evaluate loop over the interactive session: the completeness gate, the session loop and its meta-commands, the transcript encoder, and the batch and line-editor faces `gandr repl` runs.

<!-- toc -->

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [A verb of the driver](#a-verb-of-the-driver)
- [The line editor](#the-line-editor)
- [The loop reads declarations](#the-loop-reads-declarations)
- [A chunk is kept only when nothing in it was refused](#a-chunk-is-kept-only-when-nothing-in-it-was-refused)
- [Completeness is the parser's](#completeness-is-the-parsers)
- [Types are spelled from the checkpoints](#types-are-spelled-from-the-checkpoints)
- [Repairs are cards](#repairs-are-cards)
- [The transcript](#the-transcript)
- [What evaluation adds](#what-evaluation-adds)
- [Tests: the floor, the deferred rows, the defect](#tests-the-floor-the-deferred-rows-the-defect)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** A `SessionLoop` takes lines and answers `LoopEvent`s. A line opening with `:` while no buffer waits is a meta-command — `:type <expression>`, `:load <file>`, `:reset`, `:help`, `:quit` or `:q`; any other line joins the buffer, and once the parser expects no further token the buffer is submitted to a `gandr-surface-session` `Session` as the next chunk of one growing revision. `encode_submission` turns the session's answer into a `gandr-surface-render-remote` `TranscriptBlock`: the echo with its highlight spans, a type line `name : T` per checked declaration the chunk introduced or settled, a goal line per declaration it left owing, the diagnostics renderer's report per refusal, and a warning per parse repair. `run_batch` drives the loop over any reader and writes a plain transcript; `run_interactive` drives it over a terminal through a line editor.

**Why.** The session judges revisions; a person types lines. The loop is what stands between: it decides when a buffer is worth submitting, owns the text the session judges, decides what of a revision is new, and says it in the vocabulary every renderer reads, so the terminal, a later full-screen interface and a pipe show the same lines.

**How.** The gate molds the buffer through the parser's push machine and submits when nothing is expected. The loop keeps the accepted text — every chunk kept so far — and submits it with the new chunk after it; the session runs the dispatcher's composition, so its verdicts are `gandr check --goals`'s for that text under the strict root. The encoder reads the step's reports through `gandr-surface-diagnostics`, the settle report's declarations for what changed, and the incremental checker's checkpoints for each declaration's type, which `spell` writes in the surface's syntax. The chunk joins the accepted text only when nothing was refused.

## References

- David Moon, Andrew Blinn, Thomas J. Porter and Cyrus Omar. "Syntactic Completions with Material Obligations." _Proceedings of the ACM on Programming Languages_ 9, OOPSLA2 (2025). <https://doi.org/10.1145/3763182>, arXiv:2508.16848 — the expected set the gate reads, and the obligation classes a repair card names.
- The rustyline contributors. `rustyline` 18.0.1. <https://docs.rs/rustyline/18.0.1/rustyline/> — the line editor of the terminal face.

## Provided features

- **The gate.** `completeness` and the parser's `CompletionStatus`, re-exported. Witnesses: `loop::tests::an_open_form_is_incomplete`, `loop::tests::a_bare_atom_is_complete`, `loop::tests::a_hole_is_complete`, `loop::tests::a_declaration_waits_for_its_terminator`, `loop::tests::unused_completion_status_name_stays_in_scope`.
- **The loop.** `SessionLoop`, `SessionLoop::new`, `offer`, `finish`, `prompt`, `discard`; `LoopEvent`, `Prompt`, `LoopError`, `Faulted`, `finished::Absent`. Witnesses: `loop::tests::an_open_form_continues`, `loop::tests::a_complete_atom_submits`, `loop::tests::a_definition_is_visible_on_the_next_line`, `loop::tests::a_refused_chunk_is_not_kept`, `loop::tests::quit_stops_the_loop`, `loop::tests::the_meta_commands_answer`, `loop::tests::the_type_command_answers_without_keeping_the_probe`, `loop::tests::a_loaded_file_is_one_chunk`, `loop::tests::an_incomplete_buffer_is_submitted_at_end_of_input`, `loop::tests::finishing_an_empty_loop_yields_nothing`, `loop::tests::finishing_twice_reports_once`.
- **The encoder.** `encode_submission`, `Offer`, `Echo`, `Subject`, `Standings`, `Encoded`, `Disposition`, `spelled::Absent`. Witnesses: `loop::tests::a_hole_encodes_as_a_goal_line`, `loop::tests::a_later_definition_settles_an_earlier_goal`, `loop::tests::an_outcome_only_refusal_is_visible_in_the_repl`, `loop::tests::styled_session_diagnostics_reach_the_repl_transcript`, `loop::tests::a_checked_definition_names_its_type_in_the_renderers_spelling`.
- **The type renderer.** `spell`, `Spelling`, `Fidelity`. Witnesses: `render::tests::value_ty_covers_every_reachable_former`, `render::tests::comp_ty_covers_every_reachable_former`, `render::tests::ty_dispatches_on_polarity`, `render::tests::fidelity_tracks_unsupported_nodes_not_user_punctuation`, `render::tests::types_render_without_debug`, `render::tests::a_malformed_table_spells_unknown`, `loop::tests::corpus_types_spell_as_their_source_writes_them`.
- **The echo's highlights.** `highlight_source`, `span_order`, `SpanOrder`. Witnesses: `highlight::tests::a_keyword_is_classified`, `highlight::tests::spans_are_sorted_and_disjoint`, `highlight::tests::the_disjointness_predicate_rejects_an_overlap`, `highlight::tests::an_unclassifiable_buffer_yields_no_panic`, `loop::tests::a_submission_carries_highlight_spans`, `loop::tests::transcript_spans_are_sorted_and_disjoint`.
- **Repair cards.** `repair_cards`. Witnesses: `remote::tests::cards_preserve_the_report_rows`, `remote::tests::a_clean_source_produces_no_cards`.
- **The faces.** `run_batch`, `write_block`, `run_interactive`, `drive`, `LineSource`, `Read`, `Ended`, `Fault`. Witnesses: `loop::tests::piped_value_prints_a_transcript`, `loop::tests::an_unparseable_pipe_reports_rather_than_going_quiet`, `loop::tests::unreadable_input_ends_the_batch_faulted`, `loop::tests::the_terminal_face_discards_on_interrupt_and_submits_at_the_end`.
- **The rows.** `rows`, `Row`, `Lead`, `Mark`: a block's one layout, which `write_block` prints. Witnesses: `loop::tests::a_block_lays_out_as_rows`, `loop::tests::piped_value_prints_a_transcript`.

## Expected features

- **A terminal, for the line-editor face.** `run_interactive` edits lines on the terminal standard input is attached to; the driver runs the batch face when standard input is not a terminal.

## Examples

```console
$ printf 'def answer = 42 ;\n:type answer\ndef later : String ;\n' | gandr repl
▸ def answer = 42 ;
answer : Integer
▸ :type answer
: Integer
▸ def later : String ;
? later : String
```

The crate's tests run with `cargo nextest run -p gandr-surface-repl`.

## A verb of the driver

The loop is reached as `gandr repl`, one verb of the `gandr` binary beside `check`, `test` and `lsp`; bare `gandr` keeps its status report. The prior implementation made bare `gandr` the loop and `gandr <file>` a script run. That surface would change a landed driver witness and read a file name where a verb stands. The choice reverses if bare `gandr` is ruled the loop.

## The line editor

The terminal face edits lines with `rustyline` 18.0.1, defaults off. Off are `with-file-history`, which writes history in plain text, `with-dirs`, which only locates that file, and `custom-bindings`, a keymap the face does not use; history lives in memory for the run. On this workspace the editor adds six crates to a build — itself, `nix`, `cfg_aliases`, `log`, `unicode-segmentation` and `utf8parse` — beside `libc`, `bitflags`, `cfg-if`, `memchr` and `unicode-width`, which the build already carries, and compiles in about a second.

The recorded design and the prior implementation used `reedline`. Its 0.52.1 release with defaults off brings 43 crates, among them `crossterm`, `mio`, `signal-hook`, `chrono`, `serde_derive`, `strum` and `derive_more`, and its releases break their interface often; the loop uses none of what it adds over `rustyline` — menus, a multi-line edit buffer, a painter of its own. A raw-mode loop over `crossterm` alone would hand-write the line editing a maintained crate provides. `rustyline` is the most used line editor on crates.io and keeps a stable interface. The choice reverses on a high-risk advisory or an unmaintained mark against `rustyline`, or when a face needs what only `reedline` offers, such as completion menus or editing a whole buffer across lines.

The face is always built: `gandr repl` on a terminal needs it, so a feature gate would only make the default binary unable to do what its verb says.

## The loop reads declarations

The fragment's source is declarations. A bare expression such as `42` is refused whole by the lowering, and the loop shows that refusal as the diagnostics renderer writes it; `:type <expression>` answers an expression's type by submitting the probe `def it = <expression> ;` — under the first of `it`, `it1`, … that no accepted declaration carries — and keeping nothing. A goal is a declaration owing its body: a signature with no definition, answered with a goal line `name : T`; a later definition of the same name settles it, and its line becomes a type line. A hole inside a body is outside the fragment, so goals over sub-term holes arrive with the hole surface.

## A chunk is kept only when nothing in it was refused

The session judges whole revisions and keeps no text, so the loop owns the accepted text and submits it with each new chunk after it: a later line sees every declaration kept before it. A chunk is kept when its revision drew no refusal — no refusal, no unsettled declaration, no refusal of the revision as a whole — and is otherwise dropped, the accepted text and the declarations' standings unchanged. The encoder reports a declaration when the chunk introduced it, or when its outcome differs from the accepted revision's, which is how a definition settling an earlier signature is seen.

The alternative was keeping every chunk. A refused declaration would then be refused again at every later submission, and its report would repeat or have to be filtered by age; dropping it keeps the accepted text clean, so each revision's refusals are the chunk's own. A report's line and column count from the first kept line, since the revision is the whole session: `:load` submits a file's text as one chunk, and its reports address the session, not the file. The choice reverses when the lowering takes a seed of earlier declarations; the session then owns the line-append, a submission is the chunk alone, and reports address it.

## Completeness is the parser's

A buffer is submitted when the parser's push machine, having molded its tokens, expects nothing more: no open form and no owed operand. The loop parses nothing of its own. A hole `?` is a complete term, so a buffer holding one is submitted rather than continued — holes are typeable, never a reason to wait. Complete is not clean: a buffer the parser repairs inside can be complete, and is submitted and reported. At the end of input a buffer still waiting is submitted whatever its state, so an open form at the end of a pipe is reported rather than dropped; an interrupt on the terminal drops it.

## Types are spelled from the checkpoints

A type line names its type through `spell`, the one spelling every transcript line uses: the incremental checker's checkpoint holds a checked or owed item's signature, and a synthesised item's type, as content tables, and `spell` writes a table in the fragment's type syntax — `Integer`, `String`, `Unit`, `+U C`, `-F A`, `A -> C` right associative, an abstract type by its name. A node the surface cannot write yet — the numeric atom, a product, a sum, a universe, a lift, an element, a dependent arrow, an unresolved node — is written `?`, and the spelling is marked approximate, by the nodes it met rather than by the characters of a name. The walk keeps its own stack and a visit budget, so a malformed table spells `?` rather than looping. Over the strict corpus's `values` and `functions` sources every signature spells exactly as its source wrote it; the universe sources beside them wait for the layout printer.

The renderer is interim: it gives way to the layout printer, which spells every former and lays it out to a width. The prior implementation rendered surface types it built itself; here the types come back from the checker as content, so the renderer reads content, and it reads no `Debug` image.

## Repairs are cards

The session carries the parse's repairs beside its step. The encoder takes those inside the chunk and projects each onto a `DiagCard` under `W0012`, `parse repaired: <class>`, its span measured from the chunk's start; a warning line in the transcript carries it. A repair before the chunk belongs to text already accepted and is not repeated. The alternative was the published obligation vocabulary with its own cards and severity classes, which the renderer seam leaves to the recovery engine that will read them; the cards move to that vocabulary when it lands.

## The transcript

A block's layout is `rows`: the echo's rows, then each result line's, each row carrying its line's kind, its lead and its text without a terminator, and its byte offset in that line's text, so a renderer can lay the echo's highlight spans over it. A line's first row opens with its kind's mark — `▸` the echo, `?` a goal, `·` a note, `=` a value, `!` blame; a type line spells its own `name : T` and a diagnostic opens with its own severity, so neither takes a mark — a later row with text is indented to the mark's width, and a later empty row carries nothing. The rows are the one spelling of a block's layout both faces read: `write_block` prints each row on a line of its own, and a full-screen face paints the same rows, so the two never disagree about a mark or an indent. The batch face writes refusals plainly; the terminal face colours them when standard output is a terminal. A fault — a grammar that did not build, input that is not text, an editor that failed, a session fault — ends a face with `Ended::Faulted`, after the blocks before it are flushed; a refusal is a transcript line, never a fault.

## What evaluation adds

The loop types and does not run. Evaluation arrives with the next unit on the interactive lane: a checked declaration without holes is run and its value printed as a value line, a stuck or blamed run as a line of its own kind, and the script runner `gandr run` beside `gandr repl`. The render row that spells evaluation outcomes lands with it.

## Tests: the floor, the deferred rows, the defect

The prior implementation's loop and highlight suites and its type renderer's suite are the floor: 28 tests. 27 are here under their names; the 28th waits for evaluation.

| Suite | Floor | Here | Deferred |
| ----- | ----- | ---- | -------- |
| loop | 18 | 18 | 0 |
| highlight | 4 | 4 | 0 |
| render | 6 | 5 | 1 |

The crate carries 42 tests: the 27 ported rows, the two repair-card rows of the prior implementation's render-bus projection, and thirteen rows for what is new here — reading a meta-command, answering each, the probe, `:load`, the dropped chunk, a goal settled later, the declaration terminator, the terminal face over a scripted source, unreadable input, the malformed table, a checked definition's spelling, the corpus spelling, and a block's rows.

The ported rows take the fragment's forms. `a_complete_atom_submits` submits `42` and expects the lowering's refusal of it as a whole, exactly as the diagnostics renderer writes it. `a_hole_encodes_as_a_goal_line` takes a signature without a definition, the fragment's goal. `an_outcome_only_refusal_is_visible_in_the_repl` takes a definition the checker refuses against an earlier signature and expects the renderer's own report over the session's revision. `piped_value_prints_a_transcript` pipes `:load` of a strict corpus source and `:type`, the typing half of the prior row; its value lines wait for evaluation. `unused_completion_status_name_stays_in_scope` names the gate's answer through this crate and asserts the empty buffer complete. `an_unclassifiable_buffer_yields_no_panic` asserts the spans over unreadable text ordered and inside it. The render rows run over the checker's content tables, the prior surface types' formers each mapped to the content former that carries them.

Deferred, with what each needs: `eval_renders_each_outcome_class`, evaluation. The prior render-bus row `advertised_capabilities_match_the_live_path` waits with the capability form the renderer seam does not carry.

One defect of the prior implementation is absent: a transcript line named its type through a `Debug` image. Absent at L2: `loop::tests::a_checked_definition_names_its_type_in_the_renderers_spelling` reads the checked signature from a session's checkpoint and expects the loop's line to be `spell`'s spelling of it, and `loop::tests::corpus_types_spell_as_their_source_writes_them` expects every corpus signature's line to be the source's own text.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
