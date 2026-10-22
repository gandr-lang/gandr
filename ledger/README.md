# Ledgers

The language surface and its features, each checked by the gates. The syntax ledger is enumerated by the toolchain from its own grammar and never edited by hand; the features ledger is a table written by hand as features land; the exemplars are small sources written by hand and verified against the ledgers.

## Files

- `syntax.md`: the syntax ledger, for reading. Every rule of the built-in precedence-bounded grammar, grouped by sort: its form spelled from its tiles and holes, its precedence group, the named node kind it realises and the highlight roles of its tiles, each committed rule linking its exemplar. Then the internal rules, which no source molds, each with the reason and what the reason is read from (the grammar, the labeler or a parser probe), and every attribute of the lowering's registry with the payload it takes and a link to its exemplar. The header names the fingerprint of the grammar the ledger was generated from.
- `syntax.json`: the same rows, for machines. Each form is a tree whose tiles carry the mold the grammar's build assigned them, their tile kind, their spelling and their role; one rule or attribute per line.
- `features.sql`: the features ledger, the `sqlite3` dump of one table of what gandr implements, partly implements, plans and declines, each row with its evidence: the schema first, then one `INSERT` per row in `id` order. The database itself, `features.db`, is built from it and never tracked.
- `exemplars/syntax/<rule>.gandr`: one exemplar per committed rule, opening with a `///` comment naming the rule; it holds one item whose tree holds a tile of the rule.
- `exemplars/attributes/<name>.gandr`: one exemplar per attribute, opening with a `///` comment naming it; it lowers with the attribute filed on the item it decorates, beside any declaration its payload names.
- `exemplars/features/<feature id>.gandr`: a focused program for a row of the features ledger that no corpus fixture shows, named by the row's id, opening with a `///` comment naming it. Every declaration states `checks`, `runs` or `normalizes`, and every one settles; the directory is outside the corpus's fixture root, so an `owes` or `refuses` expectation is refused there. A row a corpus fixture shows names that fixture as its exemplar instead, never a copy of it.

The two kinds of exemplar are gated apart. A syntax or attribute exemplar shows a form, not a program: many stand where the checker's fragment does not reach yet (a shell block, a statement at the top level), so they are parsed and lowered and never checked. A features exemplar is a program, and it is checked and run.

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
| `corpus` | witnesses: a fixture path under `crates/surface-corpus/`, or a test file from the root, `::item` naming a test in it |
| `exemplar` | the program showing the row: a `model/` or `strict/` fixture, as a path from the root, or `ledger/exemplars/features/<id>.gandr`; never a `pathological/` one. `crate-tests` marks a mechanism no program shows, its evidence the tests `corpus` names, and is refused where `corpus` names a fixture |
| `issue` | tracker issues, `#n` separated by spaces |
| `since` | the pull request that landed an implemented or partial row, or the commit before pull requests |

A row's status needs its evidence, and the table's constraints refuse one without it: an implemented row a `crate` or a `corpus` witness; a partial row that and an open issue or a `pathological/` witness of what it still refuses; a planned or declined row the issue that records the plan or the decision.

To edit it: `mise run ledger:build`, change `features.db` with `sqlite3`, `mise run ledger:dump`, and commit `features.sql`.

## Commands and gates

| Command | Does |
| ------- | ---- |
| `cargo run --package gandr-lang -- ledger syntax --write ledger` | regenerates `syntax.md` and `syntax.json` |
| `cargo run --package gandr-lang -- ledger exemplars ledger/exemplars` | verifies every syntax and attribute exemplar, printing `<file>: <fault>` for each that does not hold |
| `cargo run --package gandr-lang -- test ledger/exemplars/features` | settles every features exemplar |
| `mise run check:syntax-ledger` | regenerates both ledger files into a temporary directory and fails, printing the difference, while either differs from the committed file |
| `mise run check:syntax-exemplars` | fails while a committed rule or an attribute has no exemplar, a file names neither, or an exemplar does not show what it names |
| `mise run check:exemplars` | fails while a features exemplar leaves a declaration unsettled |
| `mise run ledger:build`, `mise run ledger:dump` | build `features.db` from `features.sql`, and dump it back |
| `mise run check:ledger` | fails while `features.sql` breaks a constraint or is not its own re-dump, a `parent` names no row, a path a row names does not exist, or a features exemplar is named by no row |

`mise run check` runs every gate, these included, and CI runs them on every change. A change to the grammar or to the attribute registry regenerates the ledger and updates the exemplars in the same commit; a change that lands, changes or retires a feature edits its row of `features.sql` in the same commit.
