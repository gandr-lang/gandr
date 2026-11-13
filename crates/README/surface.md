# The `surface` crates

The member rows of the `surface` category of [`crates/README.md`](../README.md#members): one row for each directory, the directory and what it is.

```text
# Rows sort lexicographically by directory; the dependency order is § Layering.
crates/
├── surface-agentic/               the agentic face of the hub: the Reactive Agent Protocol's toolset by default, the Model Context Protocol for compatibility
├── surface-corpus/                the expectation schemas, the strict and fixture roots, the settle comparison, the runner's report shape, and the language's corpus
├── surface-diagnostics/           the diagnostics model: a refusal, an unsettled declaration, a goal, a warning and a ledger line built once for every face to project
├── surface-dispatcher/            routes a driver invocation; composes parse, lower, check and settle over the sources a verb walks
├── surface-driver/                the `gandr` driver binary, package `gandr-lang`: its verbs and their exit codes
├── surface-evaluate/              the run stage: the dispatcher's engine
├── surface-features/              the features ledger as data, read by the toolchain and the tools
├── surface-format/                the source formatter: a parsed source laid out at a page width, its tokens and comments kept and its meaning checked unchanged
├── surface-grammar/               the checked precedence-bounded grammar, its mold table and walk index, the built-in surface
├── surface-layout/                the document-layout engine: the sealed document arena, Pareto resolution with width taint, the plan arena and the first-order render machine
├── surface-lowering/              the molded tree into core terms, over its base
├── surface-lowering-base/         the lowering's base: refusals, forms, names, origins, descriptions, namespaces, node tables, circuits, the module pass
├── surface-lowering-capability/   the lowering's capability family
├── surface-lowering-exits/        the lowering's exits family
├── surface-lowering-native/       the lowering's native family
├── surface-lsp/                   the language server: its handlers and the hub
├── surface-lsp-base/              the server's base: the protocol, positions, markup, inline completion
├── surface-lsp-core/              the reading, hover, completion, tokens
├── surface-lsp-diagnostics/       the recheck, kernel tiers, fixes
├── surface-lsp-navigation/        references, rename, calls, hints
├── surface-parser/                the labeler, molder and resumable melder: source to molded tree with completion obligations
├── surface-pretty/                the presentation printer: a checked type or a normal-form value in its one surface spelling, laid out at a page width
├── surface-render-remote/         the renderer seam: highlight and mark spans, diagnostic and goal cards, transcript blocks, the byte-to-position projections, the versioned render-bus frame
├── surface-render-terminal/       the terminal face of the diagnostics model: a diagnostic laid out as a located source snippet, plain or styled
├── surface-repl/                  the read-evaluate loop: the completeness gate, the session loop and its meta-commands, the transcript encoder and its rows, the batch and line-editor faces
├── surface-session/               the interactive session: each revision lowered, judged and checkpointed for the REPL, server and terminal
├── surface-syntax/                the molded concrete syntax tree and the mold references a grammar and a parser exchange
└── surface-tui/                   the terminal face: the loop's transcript, an input pane and a status line full-screen, styled by highlight role and line kind
```
