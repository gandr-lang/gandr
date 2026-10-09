# gandr-surface-tui

The gandr terminal face: the read-evaluate loop's transcript, an input pane and a status line, painted full-screen.

<!-- toc -->

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [A verb of the driver](#a-verb-of-the-driver)
- [One loop, shared](#one-loop-shared)
- [The renderer](#the-renderer)
- [The style maps](#the-style-maps)
- [The transcript pane](#the-transcript-pane)
- [Keys](#keys)
- [The smoke face](#the-smoke-face)
- [Tests: the floor and what is new](#tests-the-floor-and-what-is-new)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** An `App` holds one `gandr-surface-repl` `SessionLoop`, the line being edited, the lines the loop holds for the parser, and every `TranscriptBlock` the loop answered. `draw` paints it: a transcript pane of the blocks' rows, an input pane of the waiting lines and the line, and a status line. `style_of` styles a highlight span by its `HlRole` and `style_of_kind` a transcript line by its `OutKind`, each total over its enum. `drive` is the event loop — draw, read an `Input` from an `InputSource`, apply it through `App::handle` — and runs on the terminal under `run`, once off-screen under `run_smoke`, and over scripted keys in a test.

**Why.** The line editor prints a transcript that scrolls away; a full-screen face keeps the transcript in view beside the line being written. It is a renderer and nothing more: every line goes to the same loop `gandr repl` runs, every block is the loop's, and every row is laid out by the loop's `rows`, so the terminal face, the line editor and a pipe show the same lines.

**How.** `ratatui` lays out the three panes and diffs each frame onto the terminal through its `crossterm` backend, which also puts the terminal in raw mode on the alternate screen and reads its keys. The transcript pane counts the transcript's rows and paints the newest that fit: a row's lead in its kind's style, an echo row's text clipped against the block's highlight spans and painted by role, any other row's text in its kind's style. The loop renders refusals plainly, so the only styles in the pane are the face's own. The face parses, lowers, types and marks nothing.

## References

- The ratatui developers. `ratatui` 0.30.2. <https://docs.rs/ratatui/0.30.2/ratatui/> — the layout, styled text, widgets, the headless test backend and the terminal setup the face draws through.
- Timon Post and the crossterm contributors. `crossterm` 0.29.0. <https://docs.rs/crossterm/0.29.0/crossterm/> — raw mode, the alternate screen and key events, reached through ratatui's re-export.

## Provided features

- **The face's model.** `App`, `App::new`, `App::handle`, `App::transcript`; `Key`, `Handled`. Witnesses: `launch::tests::the_face_drives_the_loop_from_its_keys`, `launch::tests::a_waiting_buffer_shows_in_the_input_pane`, `launch::tests::an_outcome_refusal_is_visible_in_the_transcript_pane`.
- **The paint.** `draw`. Witnesses: `launch::tests::a_fixed_session_paints_as_the_golden`, `launch::tests::a_submitted_keyword_is_painted_in_the_keyword_colour`, `launch::tests::the_painted_frame_is_not_uniformly_default`, `launch::tests::the_transcript_pane_follows_the_newest_rows`, `launch::tests::a_waiting_buffer_shows_in_the_input_pane`.
- **The style maps.** `style_of`, total over `HlRole`, and `style_of_kind`, total over `OutKind`. Witnesses: `theme::tests::every_role_and_kind_sets_a_foreground`, `theme::tests::other_is_the_terminal_default`, `theme::tests::keyword_and_boolean_share_the_keyword_colour`, `launch::tests::a_fixed_session_paints_as_the_golden`.
- **The event loop and its faces.** `drive`, `Input`, `InputSource`, `run`, `run_smoke`, `SMOKE_NOTE`. Witnesses: `launch::tests::the_face_drives_the_loop_from_its_keys`, `launch::tests::smoke_writes_the_launch_note`.

## Expected features

- **A terminal, for `run`.** Standard input and output must both be a terminal; the driver refuses `gandr tui` otherwise. `run_smoke` and `drive` over a headless backend need none.

## Examples

```console
$ gandr tui --smoke
gandr tui: ready
$ gandr tui
```

`gandr tui` takes the terminal until Esc or `:quit`; each submission shows as `gandr repl` prints it, with the echo highlighted and each line coloured by its kind. The crate's tests run with `cargo nextest run -p gandr-surface-tui`.

## A verb of the driver

The face is reached as `gandr tui`, and its smoke face as `gandr tui --smoke`, verbs of the `gandr` binary beside `check`, `test`, `lsp` and `repl`; bare `gandr` keeps its status report. The prior implementation made bare `gandr` the read-evaluate loop, which would change a landed driver witness and read a file name where a verb stands. The choice reverses if bare `gandr` is ruled the loop.

## One loop, shared

The face owns no part of the loop. Each Enter offers the edited line to `SessionLoop::offer` and acts on its `LoopEvent`: a block joins the transcript, a line the parser waits on stays visible in the input pane until the block arrives, and `:quit` leaves. The loop keeps the buffer and the accepted text, decides completeness, submits to the session, and encodes the block; the face keeps a copy of the waiting lines only to show them, and drops it with the loop's buffer on an interrupt. The layout of a block is the loop's `rows`, which `write_block` also prints, so the face draws the same marks and indents as a pipe.

The prior implementation kept a continued buffer in its input line and offered it again whole at the next Enter, so the loop's buffer received the first line twice. Offering one line per Enter, as the line editor does, is the loop's contract; the waiting lines are the face's display alone. The alternative was a face that buffers lines itself and offers a whole buffer at once, which would decide completeness a second time, outside the loop. The choice reverses if the loop takes a whole buffer per offer.

## The renderer

The face draws with `ratatui` 0.30.2, defaults off, with one feature: `crossterm`, the backend `gandr tui` draws through. Off are `all-widgets`, which adds the calendar widget and `time`; `layout-cache`, an LRU of solved layouts that the face's one three-pane layout does not need; `macros`, a crate of span and layout macros the face does not use; `underline-color`, a style the face does not paint; and the other backends, `serde`, `palette`, `portable-atomic`, `scrolling-regions` and the unstable features, which the face has no use for. `crossterm` 0.29.0 is reached through `ratatui::crossterm` rather than pinned beside it, so the graph holds the one crossterm the backend was built against: raw mode is enabled and restored through a single copy of crossterm's terminal state, and a second pin could not drift from the backend's.

ratatui's crossterm backend takes crossterm with its default features and turns its own underline colour on, so crossterm's event reading, bracketed paste and its `derive_more` helpers build whatever the face asks; the feature set above is the smallest ratatui admits.

The face costs the driver 48 crates: `cargo tree -p gandr-lang -e normal,build` grows from 72 packages to 121, the face itself the 49th. They are ratatui's four crates; crossterm with `mio`, `signal-hook` and `rustix`; `parking_lot`; `kasuari`, the layout solver; `lru`, `compact_str`, `itertools`, `strum` and `unicode-truncate`; and eight procedural macro crates — `instability` with `darling`, `strum_macros`, `thiserror-impl`, `derive_more-impl`, `document-features`, `indoc` and `rustversion`. `kasuari` pins a third `hashbrown` and ratatui's default `hashbrown` a second `foldhash`; the workspace's duplicate-crate allowance names both with their reversal. Measured as clean builds of `gandr-lang`, the trees before and after interleaved four times, medians: the debug build's wall time rises from 5.8 s to 6.4 s and the release build's from 6.6 s to 7.9 s; the added crates take 12.6 s of compile time summed over units in debug and 16.3 s in release, which parallelism mostly hides, the largest in release `ratatui-core`, `darling_core`, `ratatui-widgets` and `itertools` at about a second each; the release binary grows from 5.09 MB to 5.60 MB. The face is always built: `gandr tui` needs it, and a feature gate would only make the default binary unable to do what its verb says.

The alternatives were `cursive`, which owns the event loop and its own view tree — the face's loop is `gandr-surface-repl`'s and must stay the driver of every submission — and has one maintainer and fewer than two hundred dependents; `termwiz`, the terminal layer of one terminal emulator, with one maintainer and a few dozen dependents; and `crossterm` alone, which would hand-write the layout, the styled text, the frame diffing and the headless backend ratatui provides. ratatui with crossterm is the pair the community's crate guides name for a terminal interface, ratatui maintained by a team and crossterm by some two hundred contributors, with no published advisory against either. The choice reverses on a high-risk advisory or an unmaintained mark against ratatui or crossterm, or when a face needs a backend ratatui does not carry.

## The style maps

`style_of` maps each of the 23 highlight roles to a style with a foreground, so no classified span takes the colour of the text around it; `HlRole::Other` maps to the terminal's default foreground on purpose, as plain variables do, rather than to no style. The roles the language server sends under one token type share a style — keywords and booleans, defined and called functions, defined and referenced variables, types and built-in types, the literal roles, holes and directives — and the map groups further where terminal colours run short. The map reads `HlRole` itself; the face does not depend on `gandr-surface-lsp` or its integer legend.

`style_of_kind` maps each of the 8 line kinds the same way, applied when a frame is drawn, so the whole history restyles with the theme: the echo's mark bold, a type line green as types are, a goal magenta as holes are, a diagnostic red, blame bold red, a stuck evaluation yellow, a value at the default, a note dark grey. Both maps are exhaustive matches, so a role or a kind added to the renderer seam stops the build until it is styled.

## The transcript pane

The pane shows the newest rows of the transcript that fit, bottom-aligned once the transcript outgrows it; earlier rows scroll away. Each row is a row of the loop's `rows`, with its mark or indent as [the transcript](../surface-repl/README.md#the-transcript) lays it out. An echo row is clipped against the block's highlight spans, so a span crossing rows paints on each; a span the highlighter's ordering excludes — overlapping the one before it, or off a character boundary — is passed over and its bytes painted at the default rather than guessed. Rows are not wrapped, so a diagnostic's snippet keeps its columns, and a row wider than the pane is cut at its edge.

Each frame counts the transcript's rows to find the newest that fit and paints only those. The cost of the count grows with the session; a running count beside the transcript replaces it if a long session lags.

## Keys

| Key | Does |
| --- | ---- |
| a character | types it at the end of the line |
| Backspace | removes the line's last character |
| Enter | offers the line to the loop |
| Ctrl-C | drops the line and the buffer the parser waits on |
| Esc | leaves |

`:quit` and every other meta-command go to the loop as lines. The face keeps no history, offers no completion, and edits only at the end of the line.

## The smoke face

`run_smoke` drives the same event loop as `gandr tui` over ratatui's headless backend, 80 columns by 24 rows, with an input source that asks to leave at its first read, then prints `gandr tui: ready`. The gate exercises the grammar, the loop's construction, one full paint and the event loop without a terminal, and the driver's witness spawns it as a user would.

## Tests: the floor and what is new

The prior implementation's suite is the floor: 6 tests, all here under their names. `smoke_writes_the_launch_note` also asserts the note's literal line. `an_outcome_refusal_is_visible_in_the_transcript_pane` takes a definition the checker refuses against an earlier signature, the fragment's form, and asserts the loop's refusal painted in the pane row for row, where the prior row only searched the block for a message. `a_submitted_keyword_is_painted_in_the_keyword_colour` and `the_painted_frame_is_not_uniformly_default` submit `def one = 1 ;`; the second reads the echo row alone, because the status line is styled whatever the transcript holds.

The crate carries 11 tests: the 6 ported rows and five for what is new here — both style maps' totality, a fixed session's frame against its golden, the event loop over scripted keys, a waiting buffer in the input pane, and the pane following the newest rows. The golden compares every symbol of a 48 by 16 frame and every style of the transcript pane; its types are spelled by the loop's renderer, the source it types spells its types the same way, and the roles it expects are read off the blocks, so it restates no spelling the surface owns.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
