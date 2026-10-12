# gandr-surface-diagnostics

The renderer for what one step of the dispatcher's walk prints: each refusal, each unsettled declaration, each goal and each shadowing warning as a located source snippet, and each ledger line a verb prints beside them.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** `gandr-surface-diagnostics` reads a `Step` of `gandr-surface-dispatcher`'s walk under the verb the walk runs and yields its entries in declaration order: a `Report` for each refusal, unsettled declaration and goal the verb prints, and a `Line` for each ledger line — a settled fixture, a pending source's refusal, a pending source the lowering reads. A report renders as a snippet: the class and message, the source's path with line and column, the lines its loci cover, each locus marked and labelled.

**Why.** A refusal names bytes, and a reader wants the line those bytes sit on. Rendering is a consumer of the step, never a second decision: the dispatcher's `shown` decides what a verb prints, and this crate decides only how. Keeping the layout here keeps the driver a process boundary and lets an editor or a test render the same report the driver prints.

**How.** `entries` walks the step's declaration reports in order and asks `shown` about each one. A report's loci come from its producer: the lowering's and the corpus root's refusals carry their spans, and a checker refusal's core nodes resolve through the origin table the step carries. Each locus is checked against the step's text, then `annotate-snippets` lays out the group with Unicode decorations, plain or styled. Witnesses are named under [Provided features](#provided-features).

## Provided features

| Surface | Behavior and evidence |
| ------- | --------------------- |
| Entry streams | Declaration order, verb filtering and persistent exhaustion. |

## Expected features

- **A step whose text is the text it composed.** `Step::Source` carries both; a span the text cannot answer leaves its report unlocated rather than quoting the wrong line.
- **A writer.** Rendering adds no framing terminator; the caller chooses the separator. Literal path controls can include a final line feed or carriage return. `Rendered::from(String)` preserves supplied bytes.
- **Terminal detection, if colour is wanted.** The caller states whether its output is a terminal; the crate reads no environment.

## Examples

```rust
use gandr_surface_diagnostics::RenderStyle;
use gandr_surface_diagnostics::Verbosity;
use gandr_surface_diagnostics::entries;
use gandr_surface_dispatcher::Goals;
use gandr_surface_dispatcher::Verb;
use gandr_surface_dispatcher::Walk;
use quenchant_shape::shape::Maybe;

let verb = Verb::Check(Goals::Gated);
let mut walk = Walk::new(vec![std::path::PathBuf::from("broken.gandr")]);
while let Maybe::Present(step) = walk.step() {
    for entry in entries(&step, verb) {
        println!("{}", entry.render(RenderStyle::Plain, Verbosity::User));
    }
}
```

The crate's tests run with `cargo nextest run -p gandr-surface-diagnostics`; the crate-level example runs with `cargo test -p gandr-surface-diagnostics --doc`.

## Where the detail lives

Mechanism, decisions with their alternatives and reversals, and witnesses live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| The one input, spans, the layout backend, specification discipline, references | [`src/lib.rs`](src/lib.rs) |
| What a report shows, shadowed builtins, native universe-path diagnostics | [`report`](src/report.rs) |
| The message and the title | [`message`](src/message.rs) |
| Verbosity | [`entry`](src/entry.rs) |
| Labels and the types they name | [`culprit`](src/culprit.rs) |
| Nested reasons, causal context | [`locus`](src/locus.rs) |
| Colour | [`style`](src/style.rs) |

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
