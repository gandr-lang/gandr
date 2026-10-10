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

One row per directory: the directory and what it is. The package name follows from the directory by the rule above.

```text
crates/
├── theory-cell-complexes/         command patterns, matching, the reduction order, the cell alphabet and store
├── theory-cell-complexes-tools/   the toy alphabet and the adversary frame engine suites test against (dev only)
├── theory-circuit-algebras/       the diagram view, the spine reading of a command pattern, embedding matching with its convexity check, the diagram normal form
├── theory-coherent-resolutions/   firing, critical pairs, replayable coherence certificates, budgeted completion
├── theory-computads/              descriptions elaborated into cells at the declaration's polarity, circuit rules instantiated where their shift question is well-posed, the convexity supply point
├── theory-deep-inference/         shift equivalence, the causal order, the certificate normal form and replay plan, the causal web, the flow projection, guarded-family prices
├── theory-graphs/                 the precedence DAG, the walk machine, and the graph algorithms they read
├── theory-levitation/             the first-order code universe and the tagged description table, rule faces, circuit rules and their elaboration, bridge arities, the generic programs, host well-formedness, the typed rule face
├── theory-nominal-automata/        nominal word and tree automata over caller-owned names, literal word membership and name dropping
├── theory-orders/                 order maintenance with constant-time comparison
├── theory-sites/                  the carrier's shapes as a site with stick-free objects: the morphism class over circuit wirings, its degree, the finite checks of its generalized Reedy structure
├── kernel-strata/                 the universe-level oracle with checkable order evidence
├── kernel-term/                   the term arena, native universe paths, Empty, List and session codes, hypothesis-indexed stage syntax, the sharing format and decode budgets
├── kernel-check-memo/             the check-memo seam a checker consults
├── kernel-conversion-trace/       the conversion-decision vocabulary and its sink
├── kernel-core/                   checking, conversion, admission and memoization; Path_U, identity and bridge recursion, higher fields, funext, Flow_U, guarded List observations and session-certificate replay; stage formation and replay
├── core-term/                     core syntax with native universe paths and the one unified context
├── core-nbe/                      the glued value domain, evaluation, readback, conversion and native path transport; the sharing overlay, its erasure and its measure; strict meta-level staging
├── core-checker/                  the checking judgement's four directed faces, the declaration input, the conversion boundary, the obligation ledger, the refusal vocabulary, residual readmission and guarded staging families
├── core-incremental/              incremental checking: the item seam, the conservative footprint, validated resume, content-addressed checkpoints and the synthesis stream
├── core-sequent/                  the command IL a core program is focused into and the two-region store its machine runs in
├── core-session/                  contractive binary session types, coinductive relation search, endpoint replay and certified recorded-run transport
├── storage-chunker/               content-defined chunk boundaries and their committed parameters
├── storage-records/               the authenticated ordered-record plane
├── storage-values/                the content-addressed value plane: typed chunk DAG and content pointers
├── storage-artifact/              kernel artifacts on the record plane: declaration segments as keyed records under a BLAKE3 manifest identity, read back through the kernel's decoder
├── surface-syntax/                the molded concrete syntax tree and the mold references a grammar and a parser exchange
├── surface-render-remote/         the renderer seam: highlight and mark spans, diagnostic and goal cards, transcript blocks, the byte-to-position projections, the versioned render-bus frame
├── surface-layout/                the document-layout engine: the sealed document arena, Pareto resolution with width taint, the plan arena and the first-order render machine
├── surface-pretty/                the presentation printer: a checked type or a normal-form value in its one surface spelling, laid out at a page width
├── surface-grammar/               the checked precedence-bounded grammar, its mold table and walk index, the built-in surface
├── surface-parser/                the labeler, molder and resumable melder: source to molded tree with completion obligations
├── surface-lowering/              the molded tree into core terms: name resolution, the module collection pass, attributes, origins, refusals
├── surface-corpus/                the expectation schemas, the strict and fixture roots, the settle comparison, the runner's report shape, and the language's corpus
├── surface-dispatcher/            routes a driver invocation; composes parse, lower, check and settle over the sources a verb walks
├── surface-diagnostics/           renders what a dispatcher step prints: a refusal, an unsettled declaration and a goal as a located source snippet, the ledger lines as text
├── surface-session/               the interactive session: each revision lowered, judged, resumed through the incremental checker and checkpointed, with the edit actions from the revision before and the parser's repairs, for the REPL, language server and terminal faces
├── surface-lsp/                   the language server: the base protocol over byte streams, diagnostics from the renderer's reports, semantic tokens from the highlighter's roles
├── surface-repl/                  the read-evaluate loop: the completeness gate, the session loop and its meta-commands, the transcript encoder and its rows, the batch and line-editor faces
├── surface-tui/                   the terminal face: the loop's transcript, an input pane and a status line full-screen, styled by highlight role and line kind
└── surface-driver/                the `gandr` driver binary, package `gandr-lang`: `check`, `test`, `lsp`, `repl`, `tui` and the exit codes
```

`workflow` has no member: the policy library and the gate binary come from [quenchant](https://github.com/gandr-lang/quenchant) at the revision the root `Cargo.toml` pins.

## Universe identity boundaries

The certified-equivalence type `Path_U` is native term syntax; conversion compares its raw classifier and map syntax, never replay-equivalence or certificate evidence. Transport is computation whose claims the kernel replays. Identity on elements and the bridge mode share a code fold; the higher field, funext and forward-only `Flow_U` are bounded in-memory rule languages. List has a finite native code and guarded, borrowed inhabitants observed only to a supplied budget. Session codes and their identity evidence are native; their directional flows transport recorded runs, not kernel endpoint values.

The decisions and exhaustion semantics live in [kernel-core](kernel-core/README.md#native-universe-paths); every assigned and reserved wire byte is in [kernel-term](kernel-term/README.md#tag-numbering-and-versioning). Frontend checking, cached content, presentation and the command IL each retain their own boundary: none turns stored candidate evidence into authority or introduces source syntax by representing it.

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
