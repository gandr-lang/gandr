# gandr-surface-diagnostics

The renderer for what one step of the dispatcher's walk prints: each refusal, each unsettled declaration and each goal as a located source snippet, and each ledger line a verb prints beside them.

<!-- toc -->

- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [What a report shows](#what-a-report-shows)
- [The one input is the step](#the-one-input-is-the-step)
- [Every span is the producer's](#every-span-is-the-producers)
- [Context is causal](#context-is-causal)
- [The layout backend](#the-layout-backend)
- [Colour is the caller's choice](#colour-is-the-callers-choice)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** `gandr-surface-diagnostics` reads a `Step` of `gandr-surface-dispatcher`'s walk under the verb the walk runs and yields its entries in declaration order: a `Report` for each refusal, unsettled declaration and goal the verb prints, and a `Line` for each ledger line — a settled fixture, a pending source's refusal, a pending source the lowering reads. A report renders as a snippet: the class and message, the source's path with line and column, the lines its loci cover, each locus marked and labelled.

**Why.** A refusal names bytes, and a reader wants the line those bytes sit on. Rendering is a consumer of the step, never a second decision: the dispatcher's `shown` decides what a verb prints, and this crate decides only how. Keeping the layout here keeps the driver a process boundary and lets an editor or a test render the same report the driver prints.

**How.** `entries` walks the step's declaration reports in order and asks `shown` about each one. A report's loci come from its producer: the lowering's and the corpus root's refusals carry their spans, and a checker refusal's core nodes resolve through the origin table the step carries. Each locus is checked against the step's text, then `annotate-snippets` lays out the group with Unicode decorations, plain or styled. Witnesses are named under [Provided features](#provided-features).

## Provided features

- `entries`, `Entries`, `Entry` and `Line`: what a step prints under a verb, in order; a ledger line is one line, `<path>: <report>`, and a fault step has no entry. Witnesses: `diagnostics::diagnostics::each_verb_prints_its_entries`, `diagnostics::diagnostics::a_refused_declaration_renders_its_snippet`.
- `Report`, `Class`, `Unsettlement` and `report_span::Absent`: one report, its class — a refusal's failure class, the way a declaration is unsettled, or a goal — and its primary span or the reason it has none. Witnesses: `diagnostics::diagnostics::a_type_mismatch_renders_as_a_located_report`, `diagnostics::diagnostics::a_refused_declaration_renders_its_snippet`, `diagnostics::diagnostics::a_span_outside_the_text_is_unlocated`.
- `Report::render` and `Rendered`: the snippet, compared byte for byte against a golden for each kind. Witnesses: `diagnostics::diagnostics::a_type_mismatch_renders_as_a_located_report`, `diagnostics::diagnostics::an_unsettled_declaration_renders_as_its_golden`, `diagnostics::diagnostics::a_goal_renders_as_its_golden`, `diagnostics::diagnostics::a_pathless_report_names_input_and_renders_causal_context`, `diagnostics::diagnostics::a_labeled_context_retains_its_locus_and_cause`, `diagnostics::diagnostics::forced_styling_colors_actual_facade_annotations`.
- `Report::identifier`, `Report::title`, `Report::context`, `Title`, `Annotation`, `Label`, `report_identifier::Absent` and `report_context::Absent`: the parts a snippet lays out — the refusal's vocabulary name, the message, each context locus with its label — for a face that shows them apart, as an editor shows a code, a message and related locations. Witnesses: `diagnostics::diagnostics::a_report_names_and_titles_what_it_renders`, `diagnostics::diagnostics::a_report_exposes_the_context_it_marks`.
- `RenderStyle` and `TerminalCapability`: plain or styled, chosen from what the caller knows of its output. Witness: `diagnostics::diagnostics::render_style_follows_terminal_capability`.

## Expected features

- **A step whose text is the text it composed.** `Step::Source` carries both; a span the text cannot answer leaves its report unlocated rather than quoting the wrong line.
- **A writer.** `Rendered` is a `String` without a trailing line terminator; the caller writes it and chooses the separator.
- **Terminal detection, if colour is wanted.** The caller states whether its output is a terminal; the crate reads no environment.

## Examples

```rust
use gandr_surface_diagnostics::Entry;
use gandr_surface_diagnostics::RenderStyle;
use gandr_surface_diagnostics::entries;
use gandr_surface_dispatcher::Goals;
use gandr_surface_dispatcher::Verb;
use gandr_surface_dispatcher::Walk;
use quenchant_shape::shape::Maybe;

let verb = Verb::Check(Goals::Gated);
let mut walk = Walk::new(vec![std::path::PathBuf::from("broken.gandr")]);
while let Maybe::Present(step) = walk.step() {
    for entry in entries(&step, verb) {
        match entry {
            | Entry::Report(report) => println!("{}\n", report.render(RenderStyle::Plain)),
            | Entry::Line(line) => println!("{line}"),
        }
    }
}
```

The crate's tests run with `cargo nextest run -p gandr-surface-diagnostics`; the crate-level example runs with `cargo test -p gandr-surface-diagnostics --doc`.

## What a report shows

| Kind | Title | Primary locus and label | Note |
| ---- | ----- | ----------------------- | ---- |
| refusal | `error[<refusal>]: <message>` | the refusal's span, labelled with its failure class | the declaration, what it states and its surviving obligations |
| unsettled declaration | ``error: `<name>` states …; produced …`` | the declaration, labelled with how it is unsettled | none |
| goal | ``goal: `<name>` states …; produced …`` | the declaration, labelled with its surviving obligations | none |
| source refused as a whole | `error[<refusal>]: the lowering refused the source as a whole: …` | the refusal's span, labelled with its failure class | none |

The refusal name in the title is the spelling the corpus's `refuses` attribute states, so a reader can copy it into an expectation. A type mismatch renders as:

```text
error[TypeMismatch]: the type this term synthesises does not convert to the type it is checked against
  ╭▸ mismatch.gandr:2:13
  │
1 │ def wrong : Integer ;
  │             ─────── the type it is checked against
2 │ def wrong = "text" ;
  │             ━━━━━━ malformed source
  │
  ╰ note: unsettled `wrong` states checks owing 0
```

The checker's refusals are worded here, beside the one consumer that writes them; the lowering's and the corpus root's are their own `Display`. A mismatch label names the role of the type it marks — checked against, synthesised — rather than the type: the workspace has no printer for core types yet, and a label that printed a node id would read worse than one that names the role. A source with an empty path is named `<input>`.

## The one input is the step

`entries` reads the whole `Step` under its verb. A declaration and the refusal it produced are one `DeclarationReport`, so every refusal the walk carries reaches the renderer with its declaration; a face reading refusals from a list kept beside the declarations could drop one. The step carries the two things rendering needs and the composition already had: the source's text, borrowed, and the lowering's origin table, moved out of the lowered module once checking is done.

The alternative was the driver passing the text and the dispatcher exposing the module beside the step. That splits one fact across two calls that must agree. The choice reverses if a consumer renders reports for a source it never walked, at which point a report constructor taking text and origins directly joins `entries`.

## Every span is the producer's

A lowering refusal and a corpus refusal carry their spans. A checker refusal names core nodes; the origin table maps each node the lowering minted back to the syntax it came from. A node the table records nothing for leaves its locus absent, and a report with no primary locus names its source's path and quotes no line. Each span is checked against the step's text before it is laid out: a span outside the text, or one splitting a character, is unlocated, never clamped. Nothing searches the text for a plausible locus, and nothing widens an absent one to the whole declaration: a guessed locus misleads where an honest absence only fails to help.

## Context is causal

A report marks a second locus only when it is part of the cause: the earlier signature a duplicate repeats, the type a term is checked against, the type a term synthesises, the expected shape a former meets. Padding a snippet with every nearby node would make the cause harder to find, not easier. A context locus keeps its own span and its own label.

## The layout backend

The snippet layout is [`annotate-snippets`](https://docs.rs/annotate-snippets/0.12.16) 0.12.16, maintained by the Rust project and used by rustc and cargo, with default features off. It adds three crates to the graph — `annotate-snippets`, `anstyle`, which `clap` already brings, and `unicode-width` — and builds without `std`, so a rendering is a `String` and nothing else. None of its types crosses this crate's API.

| Candidate | Why it lost |
| --------- | ----------- |
| [`codespan-reporting`](https://docs.rs/codespan-reporting/0.13.1) 0.13.1 | the closest second: two crates, but colour goes through `termcolor` or a hand-written style writer, and its file database answers lookups fallibly where the step already holds the text |
| [`ariadne`](https://docs.rs/ariadne/0.6.0) 0.6.0 | one maintainer, its GitHub repository archived on a move to another host, and `yansi` always linked |
| [`miette`](https://docs.rs/miette/7.6.0) 7.6.0 | the graphical handler needs `fancy-base`, about thirty crates including `syn`, and reports must implement its `Diagnostic` trait |

The choice reverses on a security advisory or an unmaintained notice against `annotate-snippets`, on the Rust project ceasing to use it, or on a release that drops plain rendering or the `std`-free build; `codespan-reporting` is next.

## Colour is the caller's choice

`RenderStyle::Plain` writes no escape sequence; `RenderStyle::Styled` writes the same text coloured with the backend's default palette. `RenderStyle::for_terminal` maps what the caller knows of its output — a terminal or not — to a style, and the crate reads no environment variable and probes no stream. The driver prints plain text, so a pipe, a file and a test all see the same bytes.

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
