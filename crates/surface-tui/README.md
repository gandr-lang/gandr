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
- [Specification and evidence](#specification-and-evidence)
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

| Surface | Contract and witnesses |
| ------- | ---------------------- |
| Application state | `App` edits Unicode scalars, submits one line, preserves accepted blocks and discards incomplete input on interrupt. The application witnesses cover exact source and retained names. |
| Painting | `draw` keeps the newest transcript rows and visible input tail; backend witnesses observe pane layout, roles, cursor geometry and malformed highlight boundaries. |
| Styling | Both const style maps have executable predicates. Finite witnesses cover all 23 roles and eight line kinds, semantic contrast and emphasis. |
| Event loop | `drive` draws before reading and stops on quit or failure. Scripted input, modifier boundaries and partial-write failure observe its transitions and error provenance. |

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

The face is reached as `gandr tui`, and its smoke face as `gandr tui --smoke`, verbs of the `gandr` binary beside `check`, `test`, `lsp` and `repl`; bare `gandr` keeps its status report. An explicit verb avoids interpreting a verb as source input. The alternative, making the bare command interactive, becomes appropriate only if the driver's command contract changes.

## One loop, shared

The face owns no part of the loop. Each Enter offers the edited line to `SessionLoop::offer` and acts on its `LoopEvent`: a block joins the transcript, a line the parser waits on stays visible in the input pane until the block arrives, and `:quit` leaves. The loop keeps the buffer and the accepted text, decides completeness, submits to the session, and encodes the block; the face keeps a copy of the waiting lines only to show them, and drops it with the loop's buffer on an interrupt. The layout of a block is the loop's `rows`, which `write_block` also prints, so the face draws the same marks and indents as a pipe.

Each submitted line is unterminated, as `SessionLoop::offer` requires; `App::handle` states that precondition for Enter. The waiting lines are display state, not input to offer again. Buffering and resubmitting a whole accumulated source would duplicate pending text and decide completeness outside the shared loop. That alternative becomes appropriate only if the loop changes to accept whole buffers.

## The renderer

The face draws with `ratatui` 0.30.2, defaults off, with one feature: `crossterm`, the backend `gandr tui` draws through. Off are `all-widgets`, which adds the calendar widget and `time`; `layout-cache`, an LRU of solved layouts that the face's one three-pane layout does not need; `macros`, a crate of span and layout macros the face does not use; `underline-color`, a style the face does not paint; and the other backends, `serde`, `palette`, `portable-atomic`, `scrolling-regions` and the unstable features, which the face has no use for. `crossterm` 0.29.0 is reached through `ratatui::crossterm` rather than pinned beside it, so the graph holds the one crossterm the backend was built against: raw mode is enabled and restored through a single copy of crossterm's terminal state, and a second pin could not drift from the backend's.

ratatui's crossterm backend takes crossterm with its default features and turns its own underline colour on, so crossterm's event reading, bracketed paste and its `derive_more` helpers build whatever the face asks; the feature set above is the smallest ratatui admits.

The face costs the driver 48 crates: `cargo tree -p gandr-lang -e normal,build` grows from 72 packages to 121, the face itself the 49th. They are ratatui's four crates; crossterm with `mio`, `signal-hook` and `rustix`; `parking_lot`; `kasuari`, the layout solver; `lru`, `compact_str`, `itertools`, `strum` and `unicode-truncate`; and eight procedural macro crates — `instability` with `darling`, `strum_macros`, `thiserror-impl`, `derive_more-impl`, `document-features`, `indoc` and `rustversion`. `kasuari` pins a third `hashbrown` and ratatui's default `hashbrown` a second `foldhash`; the workspace's duplicate-crate allowance names both with their reversal. Measured as clean builds of `gandr-lang`, the trees before and after interleaved four times, medians: the debug build's wall time rises from 5.8 s to 6.4 s and the release build's from 6.6 s to 7.9 s; the added crates take 12.6 s of compile time summed over units in debug and 16.3 s in release, which parallelism mostly hides, the largest in release `ratatui-core`, `darling_core`, `ratatui-widgets` and `itertools` at about a second each; the release binary grows from 5.09 MB to 5.60 MB. The face is always built: `gandr tui` needs it, and a feature gate would only make the default binary unable to do what its verb says.

The alternatives were `cursive`, which owns the event loop and its own view tree — the face's loop is `gandr-surface-repl`'s and must stay the driver of every submission — and has one maintainer and fewer than two hundred dependents; `termwiz`, the terminal layer of one terminal emulator, with one maintainer and a few dozen dependents; and `crossterm` alone, which would hand-write the layout, the styled text, the frame diffing and the headless backend ratatui provides. ratatui with crossterm is the pair the community's crate guides name for a terminal interface, ratatui maintained by a team and crossterm by some two hundred contributors, with no published advisory against either. The choice reverses on a high-risk advisory or an unmaintained mark against ratatui or crossterm, or when a face needs a backend ratatui does not carry.

## The style maps

`style_of` maps each of the 23 highlight roles to a style with a foreground, so no classified span takes the colour of the text around it; `HlRole::Other` maps to the terminal's default foreground on purpose, as plain variables do, rather than to no style. The roles the language server sends under one token type share a style — keywords and booleans, defined and called functions, defined and referenced variables, types and built-in types, the literal roles, holes and directives — and the map groups further where terminal colours run short. The map reads `HlRole` itself; the face does not depend on `gandr-surface-lsp` or its integer legend.

`style_of_kind` maps each of the 8 line kinds the same way, applied when a frame is drawn, so the whole history restyles with the theme: the echo's mark bold, a type line green as types are, a goal magenta as holes are, a diagnostic red, blame bold red, a stuck evaluation yellow, a value at the default, a note dark grey. Both maps are exhaustive matches, so a role or a kind added to the renderer seam stops the build until it is styled.

## The transcript pane

The pane shows the newest rows of the transcript that fit; earlier rows scroll away. Each row follows [the shared transcript layout](../surface-repl/README.md#the-transcript). Highlight spans are clipped to each echo row. A clipped span splitting a character or starting before the last accepted span ends is ignored: earlier styling remains and uncovered bytes retain the terminal default. Rows are not wrapped, so diagnostic snippets retain their columns.

Each frame counts the transcript's rows to find the newest that fit and paints only those. The cost of the count grows with the session; a running count beside the transcript replaces it if a long session lags.

The input pane selects visible waiting rows before converting coordinates, clips them at the right edge, and reserves one editable cell for the cursor. The current line uses ratatui's right-aligned `Line` renderer when its tail must be clipped; widths remain machine-sized until cursor placement. This retains the actual tail beyond 65,535 cells without hand-written Unicode clipping or collecting off-screen waiting rows. An empty inner pane requests no cursor. Keeping a single scrolled paragraph is simpler but its bounded scroll coordinates lose the true tail; reconsider it only if it can express the required offsets and cursor ownership.

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

## Specification and evidence

The crate specifies 26 nontrivial items: 21 executable predicates and 26 bounded adequacy arguments. Transparent accessors and the constant quit source remain trivial. Predicates cover editing transitions, style classifications, text conservation, coordinate saturation, key precedence, fault provenance and the test harness's transformations.

Five items need effect witnesses instead of predicates:

- `draw`, `draw_transcript` and `draw_input`: ratatui exposes the frame buffer only through a mutable borrow, which a predicate's `Fn` closure cannot take; frame cursor state has no getter. Tests observe the completed backend instead.
- `InputSource::next`: the abstract source has no pending-input or read-state observer.
- `drive`: generic input and backend traits expose no immutable queue or painted-state observer, and supplied faults may be arbitrary.

The 21 terminal-free tests cover application transitions, complete style classifications, Unicode and coordinate boundaries, malformed highlight precedence, modifier handling, independent frame layouts, transcript scrolling, failed-input termination and partial-write failure. A 22nd test, `the_terminal_face_completes_and_restores_its_settings`, is opt-in because it needs an attached terminal: it reads real quit keys and compares terminal settings before and after. The two cursor/tail regression witnesses fail on the previous renderer and pass with the corrected clipping. Wording-only and implementation-copy checks are not evidence; the frame golden compares literal pane layout rather than rebuilding the painter's algorithm.

`cargo nextest run -p gandr-surface-tui` runs the terminal-free witnesses. With `RUSTFLAGS='--cfg anodized_panic'`, it also executes their predicates. To exercise the native input and terminal predicates, build the `launch` test executable with that flag, then run it on a terminal with `--exact tests::the_terminal_face_completes_and_restores_its_settings --ignored --nocapture` and enter `:quit`. A public rendering probe covers empty panes, wide and combining characters, and a 65,537-character input; `gandr tui --smoke` exercises terminal-free launch. A real terminal session also discards an incomplete definition, evaluates and queries an accepted definition, quits through `:quit`, and restores terminal settings. Real terminal failure injection and font-dependent glyph appearance remain outside the deterministic test domain.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
