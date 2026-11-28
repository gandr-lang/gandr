# gandr-workflow-feature-tiers

A spike. The binary `feature-tiers` measures how well the crates, the features ledger and the corpus fit a build and a test run in tiers by language feature.

## Synopsis

**What.** One run prints five tables: the layers of the workspace, the seam of each crate, the features ledger by area, the corpus against the ledger, and the grammar rules that the sources of the corpus use.

**Why.** A language feature can select a part of the build and a part of the tests only if three records agree: the crate that implements the feature, the sources that use it, and the row that names it. The tables show where they agree.

**How.** The run starts `cargo metadata` one time. It reads each row of the features ledger one time. It parses each source of `corpus/` and of `library/` one time with the built-in grammar.

## Examples

```sh
cargo run -p gandr-workflow-feature-tiers -- --root . --tier0 corpus/model/basics/machine-widths.gandr
```

`--tier0` names a source whose rules are the candidate rules of the lowest tier. The flag repeats. The last table counts the sources that use no other rule.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence. The licence text is at the repository root.
