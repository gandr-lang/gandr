# gandr-surface-render-terminal

The terminal face of the diagnostics model: one `Diagnostic` laid out as the located source snippet `gandr check`, `gandr test`, the REPL and the TUI print.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** `render` writes a `gandr-surface-diagnostics` `Diagnostic` at a `Verbosity` in a `RenderStyle`: the severity, identifier and message on the first line, the path with line and column, the excerpt with each annotation and each located context marked under its bytes, each context as `label; while sentence`, each unlocated context and the note as notes, and the details the verbosity adds. A ledger line renders as `path: line`.

**Why.** A projection decides nothing: what a diagnostic says is decided once in the model, so the terminal and the editor cannot disagree. This crate is the only one in the workspace that depends on `annotate-snippets`, and none of its types crosses the API.

**How.** The excerpt the model holds is laid out by `annotate-snippets` from the excerpt's first line, each span rebased onto it, with Unicode decorations, plain or styled. Witnesses are named in the rustdoc.

## Provided features

| Surface | Behavior and evidence |
| ------- | --------------------- |
| `render` and `Rendered` | One diagnostic at each verbosity; goldens under `tests/golden/` for each causal shape, a missing terminator, an unclosed string, an unlocated rule and each other kind. |
| `RenderStyle` and `TerminalCapability` | Plain or styled output, following the caller's statement of whether its output is a terminal. |

## Expected features

- **A writer.** Rendering adds no framing terminator; the caller chooses the separator. Literal path controls can include a final line feed or carriage return. `Rendered::from(String)` preserves supplied bytes.
- **Terminal detection, if colour is wanted.** The caller states whether its output is a terminal; the crate reads no environment.

## Examples

```rust
use gandr_surface_dispatcher::Goals;
use gandr_surface_dispatcher::Verb;
use gandr_surface_dispatcher::Walk;
use gandr_surface_dispatcher::entries;
use gandr_surface_diagnostics::Verbosity;
use gandr_surface_render_terminal::RenderStyle;
use gandr_surface_render_terminal::render;
use quenchant_shape::shape::Maybe;

let verb = Verb::Check(Goals::Gated);
let mut walk = Walk::new(vec![std::path::PathBuf::from("broken.gandr")]);
while let Maybe::Present(step) = walk.step() {
    for diagnostic in entries(&step, verb) {
        println!("{}", render(&diagnostic, RenderStyle::Plain, Verbosity::User));
    }
}
```

The crate's tests run with `cargo nextest run -p gandr-surface-render-terminal`; the crate-level example runs with `cargo test -p gandr-surface-render-terminal --doc`.

## Where the detail lives

| Topic | Module |
| ----- | ------ |
| A projection of the model, the backend and its choice, specification discipline | [`src/lib.rs`](src/lib.rs) |
| The layout | [`render`](src/render.rs) |
| Colour | [`style`](src/style.rs) |

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
