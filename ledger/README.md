# Ledgers

The language surface, enumerated by the toolchain from its own grammar and checked by the gates. Every file here is generated; none is edited by hand.

## Files

- `syntax.md`: the syntax ledger, for reading. Every rule of the built-in precedence-bounded grammar, grouped by sort: its form spelled from its tiles and holes, its precedence group, the named node kind it realises and the highlight roles of its tiles. Then the internal rules, whose form passes a tile the labeler reads as layout, so that no source molds them, and every attribute of the lowering's registry with the payload it takes. The header names the fingerprint of the grammar the ledger was generated from.
- `syntax.json`: the same rows, for machines. Each form is a tree whose tiles carry the mold the grammar's build assigned them, their tile kind, their spelling and their role; one rule or attribute per line.

How each row is read off the grammar, and the notation a form is spelled in, are in the `ledger` module of [`gandr-surface-dispatcher`](../crates/surface-dispatcher/src/ledger.rs).

## Commands and gates

| Command | Does |
| ------- | ---- |
| `cargo run --package gandr-lang -- ledger syntax --write ledger` | regenerates `syntax.md` and `syntax.json` |
| `mise run check:syntax-ledger` | regenerates both into a temporary directory and fails, printing the difference, while either differs from the committed file |

`mise run check` runs every gate, this one included, and CI runs it on every change. A change to the grammar or to the attribute registry regenerates the ledger in the same commit.
