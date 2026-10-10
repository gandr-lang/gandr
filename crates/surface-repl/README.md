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
- [A checked declaration prints what it runs to](#a-checked-declaration-prints-what-it-runs-to)
- [Specification evidence](#specification-evidence)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** A `SessionLoop` takes lines and answers `LoopEvent`s. A line opening with `:` while no buffer waits is a meta-command — `:type <expression>`, `:load <file>`, `:reset`, `:help`, `:quit` or `:q`; any other line joins the buffer, and once the parser expects no further token the buffer is submitted to a `gandr-surface-session` `Session` as the next chunk of one growing revision. `encode_submission` turns the session's answer into a `gandr-surface-render-remote` `TranscriptBlock`: the echo with its highlight spans, a type line `name : T` per checked declaration the chunk introduced or settled followed by the line of what running it came to, a goal line per declaration it left owing, the diagnostics renderer's report per refusal, and a warning per parse repair. `run_batch` drives the loop over any reader and writes a plain transcript; `run_interactive` drives it over a terminal through a line editor.

**Why.** The session judges revisions; a person types lines. The loop is what stands between: it decides when a buffer is worth submitting, owns the text the session judges, decides what of a revision is new, and says it in the vocabulary every renderer reads, so the line editor, the terminal face `gandr tui` and a pipe show the same lines.

**How.** The gate molds the buffer through the parser's push machine and submits when nothing is expected. The loop keeps the accepted text — every chunk kept so far — and submits it with the new chunk after it; the session runs the dispatcher's composition, so its verdicts are `gandr check --goals`'s for that text under the strict root. The encoder reads the step's reports through `gandr-surface-diagnostics`, the settle report's declarations for what changed, and the incremental checker's checkpoints for each declaration's type, which `spell` lays out through the presentation printer, `gandr-surface-pretty`. The chunk joins the accepted text only when nothing was refused.

## References

- David Moon, Andrew Blinn, Thomas J. Porter and Cyrus Omar. "Syntactic Completions with Material Obligations." _Proceedings of the ACM on Programming Languages_ 9, OOPSLA2 (2025). <https://doi.org/10.1145/3763182>, arXiv:2508.16848 — the expected set the gate reads, and the obligation classes a repair card names.
- The rustyline contributors. `rustyline` 18.0.1. <https://docs.rs/rustyline/18.0.1/rustyline/> — the line editor of the terminal face.

## Provided features

- **The gate.** `completeness` and the parser's `CompletionStatus`, re-exported. Witnesses: `loop::tests::an_open_form_is_incomplete`, `loop::tests::a_bare_atom_is_complete`, `loop::tests::a_hole_is_complete`, `loop::tests::a_declaration_waits_for_its_terminator`, `loop::tests::an_empty_buffer_is_complete`.
- **The loop.** `SessionLoop`, `SessionLoop::new`, `offer`, `finish`, `prompt`, `discard`; `LoopEvent`, `Prompt`, `LoopError`, `Faulted`, `finished::Absent`. Witnesses: `loop::tests::an_open_form_continues`, `loop::tests::a_complete_atom_submits`, `loop::tests::a_definition_is_visible_on_the_next_line`, `loop::tests::a_refused_chunk_is_not_kept`, `loop::tests::quit_stops_the_loop`, `loop::tests::the_meta_commands_answer`, `loop::tests::the_type_command_answers_without_keeping_the_probe`, `loop::tests::a_loaded_file_is_one_chunk`, `loop::tests::an_incomplete_buffer_is_submitted_at_end_of_input`, `loop::tests::finishing_an_empty_loop_yields_nothing`, `loop::tests::finishing_twice_reports_once`.
- **The encoder.** `encode_submission`, `Offer`, `Echo`, `Subject`, `Standings`, `Encoded`, `Disposition`, `spelled::Absent`. Witnesses: `loop::tests::a_hole_encodes_as_a_goal_line`, `loop::tests::a_later_definition_settles_an_earlier_goal`, `loop::tests::an_outcome_only_refusal_is_visible_in_the_repl`, `loop::tests::styled_session_diagnostics_reach_the_repl_transcript`, `loop::tests::a_checked_definition_names_its_type_in_the_renderers_spelling`, `render::tests::eval_renders_each_outcome_class`.
- **The type spelling.** `spell`, answering the printer's `Presentation`. Witnesses: `render::tests::value_ty_covers_every_reachable_former`, `render::tests::comp_ty_covers_every_reachable_former`, `render::tests::ty_dispatches_on_polarity`, `render::tests::fidelity_tracks_unsupported_nodes_not_user_punctuation`, `render::tests::types_render_without_debug`, `render::tests::a_malformed_table_spells_unknown`, `loop::tests::corpus_types_spell_as_their_source_writes_them`, `loop::tests::a_dependent_function_names_its_type_with_its_binder`.
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
= 42
▸ :type answer
: Integer
▸ def later : String ;
? later : String
```

The crate's tests run with `cargo nextest run -p gandr-surface-repl`.

## A verb of the driver

The loop is reached as `gandr repl`, beside `check`, `test`, `lsp` and `tui`; bare `gandr` keeps its status report. Making bare `gandr` the loop or treating a file path as a verb would change the driver specification. The choice reverses if bare `gandr` is designated the loop.

## The line editor

The terminal face edits lines with `rustyline` 18.0.1, defaults off. Off are `with-file-history`, which writes history in plain text, `with-dirs`, which only locates that file, and `custom-bindings`, a keymap the face does not use; history lives in memory for the run. On this workspace the editor adds six crates to a build — itself, `nix`, `cfg_aliases`, `log`, `unicode-segmentation` and `utf8parse` — beside `libc`, `bitflags`, `cfg-if`, `memchr` and `unicode-width`, which the build already carries, and compiles in about a second.

The alternative, `reedline`, supplies menus, multiline editing and a painter this face does not use. A raw-mode loop over `crossterm` would hand-write line editing that `rustyline` provides. The choice reverses on a high-risk advisory or an unmaintained mark against `rustyline`, or when the face needs completion menus or whole-buffer editing.

The face is always built: `gandr repl` on a terminal needs it, so a feature gate would only make the default binary unable to do what its verb says.

## The loop reads declarations

The fragment's source is declarations. A bare expression such as `42` is refused whole by the lowering, and the loop shows that refusal as the diagnostics renderer writes it; `:type <expression>` answers an expression's type by submitting the probe `def it = <expression> ;` — under the first of `it`, `it1`, … that no accepted declaration carries — and keeping nothing. A goal is a declaration owing its body: a signature with no definition, answered with a goal line `name : T`; a later definition of the same name settles it, and its line becomes a type line. A hole inside a body is outside the fragment, so goals over sub-term holes arrive with the hole surface.

## A chunk is kept only when nothing in it was refused

The session judges whole revisions and keeps no text, so the loop owns the accepted text and submits it with each new chunk after it: a later line sees every declaration kept before it. A chunk is kept when its revision drew no refusal — no refusal, no unsettled declaration, no refusal of the revision as a whole — and is otherwise dropped, the accepted text and the declarations' standings unchanged. The encoder reports a declaration when the chunk introduced it, or when its outcome differs from the accepted revision's, which is how a definition settling an earlier signature is seen.

Keeping every chunk would repeat a refused declaration at each later submission or require age filtering. Dropping it keeps accepted text clean. Reports count lines and columns from the first accepted line: `:load` submits one chunk whose reports address the session, not the file. The choice reverses when lowering accepts earlier declarations as a seed, allowing reports to address each chunk alone.

## Completeness is the parser's

A buffer is submitted when the parser's push machine, having molded its tokens, expects nothing more. Complete is not clean: a repaired buffer can be complete and is submitted with its diagnostics. Empty fresh input is ignored. Offered text may contain pasted line breaks, which are preserved; meta-commands dispatch only without a pending buffer. EOF submits a pending buffer regardless of completeness. An interrupt discards pending text without forgetting accepted declarations.

## Types are spelled from the checkpoints

A type line names its type through `spell`, the one spelling every transcript line uses: the incremental checker's checkpoint holds a checked or owed item's signature, and a synthesised item's type, as content tables, and `spell` reads a table as a source of the presentation printer, `gandr-surface-pretty`, which lays the type out in its one spelling per former — `Integer`, `String`, `Unit`, `+U C`, `-F A`, `A -> C` right associative, `(x : A) -> C` with generated binder names, `Type`, `Type[-]`, `Type[+, l]`, a decode as the code it reads, a constant or an abstract type by its item key. A node the surface cannot write — the numeric atom, a lift, an unoccupied position, an unresolved node, a term — is written `?`, and the presentation is marked approximate, by the nodes it met rather than by the characters of a name. The printer keeps its own stack and a visit budget, so a malformed table spells `?` rather than looping. Over the strict corpus's `values`, `functions` and `classifier/universes` sources every signature spells exactly as its source wrote it.

The page is 100 columns, fixed rather than read off a terminal, so a transcript stays a function of its input. It bounds the type, not the `name :` before it, and a type wider than the page breaks onto continuation lines, which `rows` lays out as later rows of the type line. The choice reverses when a face lays types out at its own width: the terminal face once it reads the terminal's.

Types come from checker checkpoints rather than surface-built stand-ins or `Debug` images. The shared printer handles universes and dependent arrows as well as ordinary arrows and polarity bridges.

## Repairs are cards

The session carries parse repairs beside its step. The encoder selects obligations starting at or after the chunk boundary and projects each onto a `DiagCard` under `W0012`, with its span shifted to chunk-relative bytes. An obligation starting earlier, even one crossing the boundary, is omitted; a zero-width obligation at the boundary is retained. Distinct obligation classes have distinguishable messages. A richer recovery vocabulary is the alternative when the renderer seam supports structured recovery actions.

## The transcript

A block's `rows` layout contains the echo followed by result lines, retaining kinds, leads, text and byte offsets. The first row takes the kind's mark; subsequent nonempty rows take its indentation, and empty rows take no indentation. Type and diagnostic rows have no mark. CRLF terminators are stripped; a lone carriage return is retained. `write_block` writes this layout without flushing; faces flush on normal or faulted endings, but not after write errors. A flush error takes precedence over the ending being returned.

## A checked declaration prints what it runs to

After a checked declaration's type line, the encoder writes its evaluation: a value, goal blame, or a note for a stuck or unrunnable result. The run stage owns the spelling shared with `gandr run` and `runs` expectations. Goal declarations are not evaluated; probes answer only a type. The declaration is the evaluation unit because the fragment has no top-level expression; see [the session evaluation specification](../surface-session/README.md#a-hole-free-item-is-evaluated).

## Specification evidence

The crate has 52 tests. Predicates observe branch decisions, empty-state boundaries, byte ranges, type-absence precedence, preserved payloads and transcript kinds. They do not parse, print, evaluate or clone a whole session a second time. The corpus spelling witness covers one-line signatures in three selected strict sources, not every corpus file or arbitrary syntax. Diagnostic prose is not a golden interface.

| Boundary | Witness |
| -------- | ------- |
| Empty, incomplete and complete input | `loop::tests::an_empty_buffer_is_complete`, `loop::tests::a_declaration_waits_for_its_terminator` |
| Pasted lines, ignored blank input, interruption and retained declarations | `loop::tests::multiline_and_interrupted_buffers_preserve_accepted_declarations` |
| No resume, missing checkpoint and refused checkpoint | `encode::tests::missing_and_refused_types_keep_their_absence_reasons` |
| Unicode literal coverage and scalar boundaries | `highlight::tests::unicode_literals_keep_their_byte_boundaries` |
| Old, crossing and zero-width repairs; distinguishable repair classes | `remote::tests::repair_boundaries_preserve_locations_and_distinct_classes` |
| Every output kind, UTF-8 byte offsets, empty rows, CRLF and lone carriage returns | `loop::tests::row_kinds_and_unicode_boundaries_keep_their_meaning` |
| Empty transcript performs no write or flush | `loop::tests::empty_transcripts_do_not_touch_the_writer` |
| Partial-write refusal, skipped flush and flush-error precedence | `loop::tests::write_and_flush_failures_keep_their_kind` |
| End and failed reads leave later events unread and flush once | `loop::tests::terminal_endings_stop_reads_and_flush_once` |

The terminal adapter additionally needs a pseudo-terminal smoke: fresh and continuing prompts, a completed definition, an interrupted buffer, a definition referring to accepted text, and EOF with a pending buffer. Scripted tests observe the same state transitions but cannot establish terminal-device behavior.

Five items have explicit executable exemptions. Their boundary witnesses observe behavior that the signature cannot inspect without consuming it or adding an observer:

| Item | Why no runtime predicate |
| ---- | ------------------------ |
| `rows::line_rows` | The opaque one-shot iterator has no row observer or clone; consuming it would change the caller's rows. |
| `rows::rows` | The same opaque iterator boundary prevents observing rows before returning them. |
| `LineSource::read` | An abstract source exposes no history observer; the caller's stopping obligation is not a return-value property. |
| `interactive::drive` | Arbitrary sources can return any fault kind; generic writers expose neither transcript nor flush state. |
| `interactive::converse` | The same generic source and writer prevent observing the transcript and read sequence. |

Single-pass iterators and generic I/O remain the API instead of adding collection, cloning or observer traits solely for assertions. Reconsider an exemption if its API gains a non-consuming semantic observer. All predicates and witnesses run in the enforcing lane; executable checks are a bounded part of the specification, not proof of the whole protocol.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
