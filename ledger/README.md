# Ledgers

The language surface and its features, each checked by the gates. The syntax ledger is enumerated by the toolchain from its own grammar and never edited by hand; the features ledger is a table written by hand as features land; the exemplars are small sources written by hand and verified against the ledgers.

## Files

- `syntax.md`: the syntax ledger, for reading. Every rule of the built-in grammar, grouped by sort: its form spelled from its tiles and holes, its precedence group, node kind, admission and highlight roles, each committed rule linking its exemplar; then the internal rules, which no source molds, each with its reason, and every registered attribute with its payload and exemplar. The header names the grammar's fingerprint.
- `syntax.json`: the same rows, for machines. Each form is a tree whose tiles carry the mold the grammar's build assigned them, their tile kind, their spelling and their role; one rule or attribute per line.
- `features.sql`: the features ledger, the `sqlite3` dump of one table of what gandr implements, partly implements, plans and declines, each row with its evidence: the schema first, then one `INSERT` per row in `id` order. `features.db` is built from it and never tracked.
- `corpus/ledger/syntax/<rule>.gandr`: one exemplar per committed rule, opening with a `///` comment naming the rule; it holds one item holding a tile of the rule, two for a glyph rule, beside any declaration its items name.
- `corpus/ledger/attributes/<name>.gandr`: one exemplar per attribute, opening with a `///` comment naming it; it lowers with the attribute filed on the item it decorates, beside any declaration its payload names.
- `corpus/ledger/features/<feature id>.gandr`: a focused program for a row no corpus fixture shows, named by the row's id, opening with a `///` comment naming it. Every declaration states `checks`, `runs` or `normalizes` and settles; `owes` and `refuses` are findings there. A row a fixture shows names that fixture, never a copy.
- `corpus/ledger/diagnostics/<name>.gandr`: one per refusal name no form qualifies and per reserved or unadmitted boundary, refused with it; a name without one has a row of the gate's owed table, its reason or issue.

`ledger/` is a fixture root, so an exemplar states what the checker makes of its form, `refuses` included where the checker does not reach it yet, its comment naming the issue that would settle it.

How each row is read off the grammar, the notation a form is spelled in, why a rule is internal and what an exemplar must hold are in the `ledger` module of [`gandr-surface-dispatcher`](../crates/surface-dispatcher/src/ledger.rs).

## The features ledger

| Column | Holds |
| ------ | ----- |
| `id` | the row's slug, lowercase words joined by `-`, never renamed |
| `area` | the chapter a manual would put it in: `types`, `identity`, `recursion`, … |
| `name`, `line` | the heading, and one sentence saying what the feature is |
| `parent` | the row this one nests under, in the same area |
| `status` | `implemented`, `partial`, `planned` or `declined` |
| `notability`, `compared_to` | `ordinary`, `notable`, `uncommon` or `unique`; the last two say against what |
| `crate` | the owning crates, directory names under `crates/`, or a `contrib/` path |
| `corpus` | witnesses: a fixture path under `corpus/`, or a test file from the root, `::item` naming a test in it |
| `exemplar` | the program showing the row: a `model/` or `strict/` fixture from the root, or `corpus/ledger/features/<id>.gandr`; never `pathological/`. `crate-tests`: a mechanism no program shows, its evidence the tests in `corpus`; refused where `corpus` names a fixture |
| `issue` | tracker issues, `#n` separated by spaces |
| `since` | the pull request that landed an implemented or partial row, or the commit before pull requests |

A row's status needs its evidence, and the table's constraints refuse one without it: an implemented row a `crate` or a `corpus` witness; a partial row that and an open issue or a `pathological/` witness of what it still refuses; a planned or declined row the issue that records the plan or the decision. An implemented or partial row names an exemplar unless its area's evidence is crate tests: `editor`, `workflow`, `storage`, `tooling`, `incremental`, `algorithms`, `machine`, `staging`, `kernel`, `conversion`, `runtime`, `syntax`, `printing`, `diagnostics`, `rewriting`, `corpus`.

To edit it: `mise run ledger:build`, change `features.db` with `sqlite3`, `mise run ledger:dump`, and commit `features.sql`.

## Commands and gates

| Command | Does |
| ------- | ---- |
| `cargo run --package gandr-lang -- ledger syntax --write ledger` | regenerates `syntax.md` and `syntax.json` |
| `cargo run --package gandr-lang -- ledger exemplars corpus/ledger` | verifies every exemplar, printing `<file>: <fault>` for each that does not hold |
| `cargo run --package gandr-lang -- test corpus/ledger` | settles every exemplar |
| `mise run check:syntax-ledger` | regenerates both ledger files into a temporary directory and fails, printing the difference, while either differs from the committed file |
| `mise run check:syntax-exemplars` | fails while a committed rule, an attribute or a refusal has no exemplar or owed row, a file names none, an exemplar does not show what it names, or a features exemplar states `owes` or `refuses` |
| `mise run check:exemplars` | fails while an exemplar leaves a declaration unsettled |
| `mise run ledger:build`, `mise run ledger:dump` | build `features.db` from `features.sql`, and dump it back |
| `mise run check:ledger` | fails while `features.sql` breaks a constraint or is not its own re-dump, a `parent` names no row, a named path does not exist, a features exemplar is named by no row, or a language feature names no exemplar |

`mise run check` runs every gate and CI runs them on every change. A change to the grammar or to the attribute registry regenerates the ledger and updates the exemplars in the same commit; a change that lands, changes or retires a feature edits its row of `features.sql` in the same commit.

## Crate READMEs

A crate's `README.md` is its only document: an overview and conceptual entry that links into the crate's `src/lib.rs` `//!` docs and the owning module, where mechanism, invariants and specification detail live and `check:doc` builds them; a decision's choice, alternatives and reversal live in its pull request and issue. A crate carries no `docs/` directory and no changelog of its own. A behavioural floor or a deferred-row ledger is a tracking issue, linked from the README once; a measurement or a report belongs to neither. `check:markdown` refuses tracked markdown outside its README allowlist, and a README over its budget in `sizelint.toml`.

Every crate README follows one order. A section is present when the crate has content for it.

1. `# <package>`, followed by one sentence stating what the crate is.
2. A table of contents linking every section below.
3. `## Synopsis`: three paragraphs, each opening with a bold word. **What.** names the thing the crate is, **Why.** the need it answers, and **How.** the mechanism, named concretely. The prose is dense, technical and in the present tense, and carries no history.
4. `## References`: one entry per key the crate's modules cite, `` - `<key>` — <role>: `` then the full title, the authors, the venue, the date, a stable identifier (DOI, ISBN, arXiv, HAL) and one clause on what the crate takes from it.
5. `## Provided features`: what the crate provides, as items.
6. `## Expected features`: what the crate requires of its consumer or its environment to be useful, such as a digest function, a store implementation, a spawner, a target requirement or a specification facade's `cfg`. Absent or planned work is not listed here.
7. `## Examples`: runnable usage and the command that runs the crate's tests.
8. `## Where the detail lives`: the modules whose rustdoc states each mechanism and decision, as a table or one sentence.
9. `## License`: `Apache-2.0 WITH LLVM-exception`, the workspace licence, whose text is at the repository root.
