# gandr-workflow-ledger-tasks

This crate runs the ledger tasks of gandr's surface. It writes the syntax ledger from the grammar. It verifies the exemplars and sweeps them for recovery. It reads the features ledger as a guide.

- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Dependencies](#dependencies)
- [License](#license)

## Synopsis

**What.** `gandr-workflow-ledger-tasks` installs the `ledger` binary. `ledger syntax --write <directory>` writes the syntax ledger as `syntax.md` and `syntax.json`. The ledger holds every rule of the built-in grammar and every attribute of the lowering's registry under the grammar's fingerprint. `ledger exemplars <directory>` verifies one exemplar for each committed rule and attribute ([`ledger/README.md`](../../ledger/README.md)). `ledger recovery <directory>` writes each literal tile of each syntax exemplar wrong and reads the first error. `ledger list [--area <area>] [--status <status>]` prints one line for each feature of `ledger/features.sql`. `ledger show <id>` prints a feature's row, its exemplars' sources whole and its corpus paths. Before you write a form, list its area and show each feature it uses.

**Why.** The ledger tasks are repository tooling, and no check of a source reads them. In the dispatcher, each build of the `gandr` binary compiled them. In this crate, the dispatcher and the `gandr` binary build without them, and an edit of a task builds this crate alone.

**How.** `clap` reads the arguments. The binary builds a `LedgerTask` and runs it. A run prints what its task wrote, found or read, then chooses the exit code. The `ledger` module states how each row is read off the grammar, the notation a form is spelled in, why a rule is internal and what an exemplar must hold. The recovery sweep walks each mutant as `gandr check` walks a source, through the dispatcher's `entries`, so the report is what a user who made the mistake reads.

## Provided features

- `ledger syntax --write <directory> [--exemplars <directory>]` prints the path of each file it writes. Without `--exemplars`, it reads the admissions under `<directory>/exemplars`.
- `ledger exemplars <directory>` prints each exemplar that does not hold, `<path>: <fault>`, then the count. It exits `1` when it finds one.
- `ledger recovery <directory>` prints the near-miss table, each mutant whose first error marks other bytes than its mutation, then the count. It exits `1` when it finds one.
- `ledger list` and `ledger show <id>` read `ledger/features.sql` under `--root`, the current directory by default.
- A fault prints `ledger: <fault>` on standard error and exits `2`.

## Expected features

The tasks need a checkout of the repository. They read `corpus/ledger` and `ledger/features.sql` under the paths given.

## Examples

```sh
mise run ledger:syntax
mise run check:syntax-exemplars
mise run ledger:recovery
cargo run --package gandr-workflow-ledger-tasks -- list --area syntax
cargo nextest run -p gandr-workflow-ledger-tasks
```

## Dependencies

`gandr-surface-grammar`, `gandr-surface-parser`, `gandr-surface-syntax` and `gandr-surface-lowering` give the grammar, the molder and the lowering. Each task reads its rows and its exemplars with them. `gandr-surface-dispatcher` walks each mutant of the recovery sweep. `gandr-surface-corpus` reads the expectations of an exemplar. `gandr-surface-diagnostics` gives the identifier and the severity of each first error. `gandr-surface-features` reads the features ledger. `gandr-core-term` gives the arena for the terms of an exemplar. `gandr-theory-graphs` gives the bound that the decision analysis reads. `clap` reads the arguments. `serde_json` writes the machine form. The root `Cargo.toml` records the features of each.

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
