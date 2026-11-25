# gandr-workflow-ledger-split

Splits the `sqlite3` dump of a ledger into the files of the tree: the schema, and the rows of each name in a file of their own.

- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [License](#license)

## Synopsis

**What.** `gandr-workflow-ledger-split` installs the `ledger-split` binary. `ledger-split --schema <file> --rows <path> <dump>` writes each line of the schema of the dump to `<file>`, and each row to the file of its name: `<path>` with `{}` as the first value of the row. The purposes ledger keeps the rows of each crate in `crates/<crate>/purposes.sql` this way.

**Why.** A ledger that keeps the rows of one name in one file gives two changes of two names two files, so they do not conflict. The tasks that normalize such a ledger, and the checks that hold it to its own dump, split the dump with this binary.

**How.** One read of the dump, and one pass over its lines. The binary drops the frame of the dump, `PRAGMA foreign_keys=OFF;`, `BEGIN TRANSACTION;` and `COMMIT;`. A line `INSERT INTO <table> VALUES('<name>', …` goes to the file of `<name>`, after the rows of that name before it. Each other line goes to the schema. Each file is written with one call at the end. The binary creates no directory, so a row of a crate with no directory fails the split. A name with a `/`, or `.` or `..`, fails the split too. `--cost` prints each part of the run with its count and its time.

## Provided features

- `ledger-split --schema <file> --rows <path> <dump>` prints the path of each file it writes, the schema first. A fault prints `ledger-split: <fault>` on standard error and exits `2`.
- `--cost` prints `ledger-split: read: 1 call, <n> µs` and `ledger-split: split and write: <lines> lines, <files> files, <n> µs` on standard error.
- `RowPath::new`, `split` and `Split` are the library behind the binary. `SplitFault` names each refusal.

## Expected features

The directory of each file exists before the split.

## Examples

```sh
sqlite3 purposes.db .dump > dump.sql
cargo run --locked -p gandr-workflow-ledger-split -- --schema .config/purposes/schema.sql --rows 'crates/{}/purposes.sql' dump.sql
cargo nextest run -p gandr-workflow-ledger-split
```

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
