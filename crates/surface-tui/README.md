# gandr-surface-tui

The gandr terminal face: the read-evaluate loop's transcript, an input pane and a status line, painted full-screen; and the side view, which follows the engine hub's render bus beside an editor.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** An `App` holds one `gandr-surface-repl` `SessionLoop`, the line being edited, the lines the loop holds for the parser, and every `TranscriptBlock` the loop answered. `draw` paints it: a transcript pane of the blocks' rows, an input pane of the waiting lines and the line, and a status line. `style_of` styles a highlight span by its `HlRole` and `style_of_kind` a transcript line by its `OutKind`, each total over its enum. `drive` is the event loop — draw, read an `Input` from an `InputSource`, apply it through `App::handle` — and runs on the terminal under `run`, once off-screen under `run_smoke`, and over scripted keys in a test.

**Why.** The line editor prints a transcript that scrolls away; a full-screen face keeps the transcript in view beside the line being written. It is a renderer and nothing more: every line goes to the same loop `gandr repl` runs, every block is the loop's, and every row is laid out by the loop's `rows`, so the terminal face, the line editor and a pipe show the same lines.

**How.** `ratatui` lays out the three panes and diffs each frame onto the terminal through its `crossterm` backend, which also puts the terminal in raw mode on the alternate screen and reads its keys. The transcript pane counts the transcript's rows and paints the newest that fit: a row's lead in its kind's style, an echo row's text clipped against the block's highlight spans and painted by role, any other row's text in its kind's style. The loop renders refusals plainly, so the only styles in the pane are the face's own. The face parses, lowers, types and marks nothing.

## Provided features

| Surface | Contract and witnesses |
| ------- | ---------------------- |
| Application state | `App` edits Unicode scalars, submits one line, preserves accepted blocks and discards incomplete input on interrupt. The application witnesses cover exact source and retained names. |
| Painting | `draw` keeps the newest transcript rows and visible input tail; backend witnesses observe pane layout, roles, cursor geometry and malformed highlight boundaries. |
| Styling | Both const style maps have executable predicates. Finite witnesses cover all 23 roles and eight line kinds, semantic contrast and emphasis. |
| Event loop | `drive` draws before reading and stops on quit or failure. Scripted input, modifier boundaries and partial-write failure observe its transitions and error provenance. |
| Side view | `Following` keeps the last report of each document the render bus sends and follows the one checked last; `Following::rows` lays out its heading, cards and holes; `drive_following` paints them and stops at `q`, Esc, Ctrl-C, a detach or the hub's end; `follow` runs it on the terminal and `follow_plain` prints each report to a pipe. |

## Expected features

- **A terminal, for `run`.** Standard input and output must both be a terminal; the driver refuses `gandr tui` otherwise. `run_smoke` and `drive` over a headless backend need none.

## Examples

```console
$ gandr tui --smoke
gandr tui: ready
$ gandr tui
```

`gandr tui` takes the terminal until Esc or `:quit`; each submission shows as `gandr repl` prints it, with the echo highlighted and each line coloured by its kind. The crate's tests run with `cargo nextest run -p gandr-surface-tui`.

## Where the detail lives

Mechanism, decisions with their alternatives and reversals, and witnesses live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| A verb of the driver, one shared loop, the side view, specification and evidence, references | [`src/lib.rs`](src/lib.rs) |
| The renderer and its dependency cost, the smoke face | [`run`](src/run.rs) |
| The style maps | [`theme`](src/theme.rs) |
| The transcript pane | [`view`](src/view.rs) |
| Keys | [`app`](src/app.rs) |

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
