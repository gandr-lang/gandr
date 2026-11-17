# gandr-surface-features

The features ledger of gandr as data: the record the toolchain step of `gandr check` reads, and the rows the tools list and show.

- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)

## Synopsis

**What.** A reader of `ledger/features.sql`, the table of what gandr implements, partly implements, plans and declines. `FeatureLedger::read` reads the table under a tree's root, and `FeatureLedger::built_in` reads the copy the binary was built with.

**Why.** The features ledger is a record, and three crates read it: the dispatcher's toolchain step checks a package's constraints against it, the driver lists and shows its rows, and the Model Context Protocol server answers `ledger_list` and `ledger_show`. The reader reads nothing of the dispatcher, so it compiles in a crate of its own, below the dispatcher and beside the checker's chain.

**How.** The ledger's one copy is a SQLite dump. The reader reads the table's `CREATE` statement and one `INSERT` statement per line, and passes over the dump's frame. A row of another shape refuses the ledger and names its line. The reader never runs the dump.

## Provided features

- `FeatureLedger`: the ledger's rows, read under a root or built in. `status` gives the status of one feature, `met` the ids the running build meets, `listed` the rows of an area and a status, and `shown` one row with its exemplars' sources and its corpus paths.
- `Feature`, `FeatureId`, `Area`, `Status` and `ShownFeature`: a row, its id, its area, where it stands, and a row as `ledger show` prints it. `Feature::json` and `ShownFeature::json` give each as a JSON object.
- `FeaturesFault` and `Malformed`: why the ledger could not be read or could not answer, and how a line of the dump fails.

## Expected features

- **A tree.** `FeatureLedger::read` reads `ledger/features.sql` and the exemplars it names under the root the caller gives.

## Examples

```sh
cargo nextest run -p gandr-surface-features
```

## Where the detail lives

The crate's root rustdoc ([`src/lib.rs`](src/lib.rs)) states the dump grammar the reader reads, and each item states its contract.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence. The licence text is at the repository root.
