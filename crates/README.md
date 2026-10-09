# crates

This file is the naming authority for the workspace's crates. A crate lives at `crates/<category>-<name>` and its package is `gandr-<category>-<name>`; the driver is the one exception, package `gandr-lang`, the name the project holds on the registry, where `gandr` belongs to an unrelated crate.

Three disciplines: consult this file before naming a crate; when it is silent, derive the name from the layering below and the crates beside it; add the row in the same change that adds the crate. A divergence is recorded here, not smoothed over.

## Layering

Categories are a layering order: a crate depends only on crates of its own category or of one listed before it. The categories are also the closed vocabulary of commit scopes.

```text
theory    reusable metatheory machinery
kernel    the certified trusted base and its substrate: levels, the term arena and sharing format, the checking machine
core      the core language: call-by-push-value syntax, the unified context, normalization by evaluation
storage   the content-addressed tier: authenticated record and value planes
surface   syntax, grammar, parsing, lowering, the pipeline a driver invocation enters, and the driver a human or a tool runs
workflow  repository tooling and gates
```

## Members

One row per directory: the directory, its package, and what it is.

```text
crates/
├── theory-cell-complexes/         gandr-theory-cell-complexes         command patterns, matching, the reduction order, the cell alphabet and store
├── theory-cell-complexes-tools/   gandr-theory-cell-complexes-tools   the toy alphabet and the adversary frame engine suites test against (dev only)
├── theory-circuit-algebras/       gandr-theory-circuit-algebras       the diagram view, the spine reading of a command pattern, embedding matching with its convexity check, the diagram normal form
├── theory-coherent-resolutions/   gandr-theory-coherent-resolutions   firing, critical pairs, replayable coherence certificates, budgeted completion
├── theory-computads/              gandr-theory-computads              descriptions elaborated into cells at the declaration's polarity, circuit rules instantiated where their shift question is well-posed, the convexity supply point
├── theory-deep-inference/         gandr-theory-deep-inference         shift equivalence, the causal order, the certificate normal form and replay plan, the causal web, the flow projection
├── theory-graphs/                 gandr-theory-graphs                 the precedence DAG, the walk machine, and the graph algorithms they read
├── theory-levitation/             gandr-theory-levitation             the first-order code universe and the tagged description table, rule faces, circuit rules and their elaboration, bridge arities, the generic programs, host well-formedness, the typed rule face
├── theory-orders/                 gandr-theory-orders                 order maintenance with constant-time comparison
├── kernel-strata/                 gandr-kernel-strata                 the universe-level oracle with checkable order evidence
├── kernel-term/                   gandr-kernel-term                   the term arena, the sharing format, the decode budgets
├── kernel-check-memo/             gandr-kernel-check-memo             the check-memo seam a checker consults
├── kernel-conversion-trace/       gandr-kernel-conversion-trace       the conversion-decision vocabulary and its sink
├── kernel-core/                   gandr-kernel-core                   the checking machine, conversion, admission, the check memo
├── core-term/                     gandr-core-term                     the core syntax and the one unified context
├── core-nbe/                      gandr-core-nbe                      the glued value domain, evaluation, readback, conversion (search-free steps and the concurrent machine), the sharing overlay, its erasure and its measure
├── core-checker/                  gandr-core-checker                  the checking judgement's four directed faces, the declaration input, the conversion boundary, the obligation ledger and the refusal vocabulary
├── core-incremental/              gandr-core-incremental              incremental checking: the item seam, the conservative footprint, validated resume, content-addressed checkpoints and the synthesis stream
├── core-sequent/                  gandr-core-sequent                  the command IL a core program is focused into and the two-region store its machine runs in
├── storage-chunker/               gandr-storage-chunker               content-defined chunk boundaries and their committed parameters
├── storage-records/               gandr-storage-records               the authenticated ordered-record plane
├── storage-values/                gandr-storage-values                the content-addressed value plane: typed chunk DAG and content pointers
├── storage-artifact/              gandr-storage-artifact              kernel artifacts on the record plane: declaration segments as keyed records under a BLAKE3 manifest identity, read back through the kernel's decoder
├── surface-syntax/                gandr-surface-syntax                the molded concrete syntax tree and the mold references a grammar and a parser exchange
├── surface-render-remote/         gandr-surface-render-remote         the renderer seam: highlight and mark spans, diagnostic and goal cards, transcript blocks, the byte-to-position projections, the versioned render-bus frame
├── surface-layout/                gandr-surface-layout                the document-layout engine: the sealed document arena, Pareto resolution with width taint, the plan arena and the first-order render machine
├── surface-pretty/                gandr-surface-pretty                the presentation printer: a checked type or a normal-form value in its one surface spelling, laid out at a page width
├── surface-grammar/               gandr-surface-grammar               the checked precedence-bounded grammar, its mold table and walk index, the built-in surface
├── surface-parser/                gandr-surface-parser                the labeler, molder and resumable melder: source to molded tree with completion obligations
├── surface-lowering/              gandr-surface-lowering              the molded tree into core terms: name resolution, the module collection pass, attributes, origins, refusals
├── surface-corpus/                gandr-surface-corpus                the expectation schemas, the strict and fixture roots, the settle comparison, the runner's report shape, and the language's corpus
├── surface-dispatcher/            gandr-surface-dispatcher            routes a driver invocation; composes parse, lower, check and settle over the sources a verb walks
├── surface-diagnostics/           gandr-surface-diagnostics           renders what a dispatcher step prints: a refusal, an unsettled declaration and a goal as a located source snippet, the ledger lines as text
├── surface-session/               gandr-surface-session               the interactive session: each revision lowered, judged, resumed through the incremental checker and checkpointed, with the edit actions from the revision before and the parser's repairs, for the REPL, language server and terminal faces
├── surface-lsp/                   gandr-surface-lsp                   the language server: the base protocol over byte streams, diagnostics from the renderer's reports, semantic tokens from the highlighter's roles
├── surface-repl/                  gandr-surface-repl                  the read-evaluate loop: the completeness gate, the session loop and its meta-commands, the transcript encoder and its rows, the batch and line-editor faces
├── surface-tui/                   gandr-surface-tui                   the terminal face: the loop's transcript, an input pane and a status line full-screen, styled by highlight role and line kind
└── surface-driver/                gandr-lang                          the `gandr` driver binary: `check`, `test`, `lsp`, `repl`, `tui` and the exit codes
```

`workflow` has no member: the policy library and the gate binary come from [quenchant](https://github.com/gandr-lang/quenchant) at the revision the root `Cargo.toml` pins.

## Crate README shape

Every crate's `README.md` follows one order. A section is present when the crate has content for it. A crate-specific section is named plainly by its subject, never by negation or metaphor.

1. `# <package>`, followed by one sentence stating what the crate is.
2. A table of contents linking every section below.
3. `## Synopsis`: three paragraphs, each opening with a bold word. **What.** names the thing the crate is, **Why.** the need it answers, and **How.** the mechanism, named concretely. The prose is dense, technical and in the present tense, and carries no history.
4. `## References`: the papers and technical artifacts the crate draws on. Each entry gives the full title, the authors, the venue, the date and a stable identifier (DOI, ISBN, arXiv, HAL), and one clause on what the crate takes from it.
5. `## Provided features`: what the crate provides, as items.
6. `## Expected features`: what the crate requires of its consumer or its environment to be useful, such as a digest function, a store implementation, a spawner, a target requirement or a specification facade's `cfg`. Absent or planned work is not listed here.
7. `## Examples`: runnable usage and the command that runs the crate's tests.
8. Crate-specific sections, one per decision or mechanism, each stated as present fact with its reason.
9. `## License`: `Apache-2.0 WITH LLVM-exception`, the workspace licence, whose text is at the repository root.

## Divergences

None.
