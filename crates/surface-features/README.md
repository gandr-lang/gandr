# gandr-surface-features

The features ledger of gandr as data: the record the toolchain step of `gandr check` reads, and the rows the tools list and show.

- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)

## Synopsis

**What.** A reader of the features ledger: `ledger/features-schema.sql`, the table of what gandr implements, partly implements, plans and declines, and `ledger/features/<id>.sql`, one row each. `FeatureLedger::read` reads the ledger under a tree's root, and `FeatureLedger::built_in` reads the copy the binary was built with.

**Why.** The features ledger is a record, and three crates read it: the dispatcher's toolchain step checks a package's constraints against it, the driver lists and shows its rows, and the Model Context Protocol server answers `ledger_list` and `ledger_show`. The reader reads nothing of the dispatcher, so it compiles in a crate of its own, below the dispatcher and beside the checker's chain.

**How.** The ledger is SQLite text in one file for each row. The reader reads the table's `CREATE` statement from the schema file, then one `INSERT` statement from each row file, in the order of the ids. A row of another shape refuses the ledger and names its file and its line, and so does a row file that holds not one row or a row of another id. The reader never runs the text. A build script joins the schema and the rows into the copy that the binary carries.

## Provided features

- `FeatureLedger`: the ledger's rows, read under a root or built in. `status` gives the status of one feature, `met` the ids the running build meets, `listed` the rows of an area and a status, and `shown` one row with its exemplars' sources and its corpus paths.
- `Feature`, `FeatureId`, `Area`, `Status` and `ShownFeature`: a row, its id, its area, where it stands, and a row as `ledger show` prints it. `Feature::json` and `ShownFeature::json` give each as a JSON object.
- `FeaturesFault` and `Malformed`: why the ledger could not be read or could not answer, and how a line or a row file fails.

## Expected features

- **A tree.** `FeatureLedger::read` reads `ledger/features-schema.sql`, `ledger/features/` and the exemplars that the rows name under the root the caller gives.

## Examples

```sh
cargo nextest run -p gandr-surface-features
```

## Where the detail lives

The crate's root rustdoc ([`src/lib.rs`](src/lib.rs)) states the dump grammar the reader reads, and each item states its contract.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence. The licence text is at the repository root.
