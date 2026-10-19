# Ledgers

The language surface, enumerated by the toolchain from its own grammar and checked by the gates. The ledger files are generated and never edited by hand; the exemplars are small sources written by hand and verified against the ledger.

## Files

- `syntax.md`: the syntax ledger, for reading. Every rule of the built-in precedence-bounded grammar, grouped by sort: its form spelled from its tiles and holes, its precedence group, the named node kind it realises and the highlight roles of its tiles, each committed rule linking its exemplar. Then the internal rules, which no source molds, each with the reason and what the reason is read from (the grammar, the labeler or a parser probe), and every attribute of the lowering's registry with the payload it takes and a link to its exemplar. The header names the fingerprint of the grammar the ledger was generated from.
- `syntax.json`: the same rows, for machines. Each form is a tree whose tiles carry the mold the grammar's build assigned them, their tile kind, their spelling and their role; one rule or attribute per line.
- `exemplars/syntax/<rule>.gandr`: one exemplar per committed rule, opening with a `///` comment naming the rule; it holds one item whose tree holds a tile of the rule.
- `exemplars/attributes/<name>.gandr`: one exemplar per attribute, opening with a `///` comment naming it; it lowers with the attribute filed on the item it decorates, beside any declaration its payload names.
- `exemplars/features/<feature id>.gandr`: one focused program per row of the features ledger, named by the row's id, opening with a `///` comment naming it. Every declaration states `checks`, `runs` or `normalizes`, and every one settles; the directory is outside the corpus's fixture root, so an `owes` or `refuses` expectation is refused there.

The two kinds of exemplar are gated apart. A syntax or attribute exemplar shows a form, not a program: many stand where the checker's fragment does not reach yet (a shell block, a statement at the top level), so they are parsed and lowered and never checked. A features exemplar is a program, and it is checked and run.

How each row is read off the grammar, the notation a form is spelled in, why a rule is internal and what an exemplar must hold are in the `ledger` module of [`gandr-surface-dispatcher`](../crates/surface-dispatcher/src/ledger.rs).

## Commands and gates

| Command | Does |
| ------- | ---- |
| `cargo run --package gandr-lang -- ledger syntax --write ledger` | regenerates `syntax.md` and `syntax.json` |
| `cargo run --package gandr-lang -- ledger exemplars ledger/exemplars` | verifies every syntax and attribute exemplar, printing `<file>: <fault>` for each that does not hold |
| `cargo run --package gandr-lang -- test ledger/exemplars/features` | settles every features exemplar |
| `mise run check:syntax-ledger` | regenerates both ledger files into a temporary directory and fails, printing the difference, while either differs from the committed file |
| `mise run check:syntax-exemplars` | fails while a committed rule or an attribute has no exemplar, a file names neither, or an exemplar does not show what it names |
| `mise run check:exemplars` | fails while a features exemplar leaves a declaration unsettled |

`mise run check` runs every gate, these included, and CI runs them on every change. A change to the grammar or to the attribute registry regenerates the ledger and updates the exemplars in the same commit.
