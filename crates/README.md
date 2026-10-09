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
├── theory-graphs/             gandr-theory-graphs             the precedence DAG, the walk machine, and the graph algorithms they read
├── theory-orders/             gandr-theory-orders             order maintenance with constant-time comparison
├── kernel-strata/             gandr-kernel-strata             the universe-level oracle with checkable order evidence
├── kernel-term/               gandr-kernel-term               the term arena, the sharing format, the decode budgets
├── kernel-check-memo/         gandr-kernel-check-memo         the check-memo seam a checker consults
├── kernel-conversion-trace/   gandr-kernel-conversion-trace   the conversion-decision vocabulary and its sink
├── kernel-core/               gandr-kernel-core               the checking machine, conversion, admission, the check memo
├── core-term/                 gandr-core-term                 the core syntax and the one unified context
├── core-nbe/                  gandr-core-nbe                  the glued value domain, evaluation, readback, search-free conversion, the sharing overlay and its erasure
├── storage-chunker/           gandr-storage-chunker           content-defined chunk boundaries and their committed parameters
├── storage-records/           gandr-storage-records           the authenticated ordered-record plane
├── storage-values/            gandr-storage-values            the content-addressed value plane: typed chunk DAG and content pointers
├── surface-syntax/            gandr-surface-syntax            the concrete syntax tree and the mold references a grammar and a parser exchange
├── surface-grammar/           gandr-surface-grammar           the checked precedence-bounded grammar, its mold table and walk index, the built-in surface
├── surface-dispatcher/        gandr-surface-dispatcher        routes a driver invocation into the surface pipeline
└── surface-driver/            gandr-lang                      the `gandr` driver binary
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
