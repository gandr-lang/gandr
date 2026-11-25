# gandr-workflow-twin-census

The census of the crates that the emitter depends on, read from `cargo metadata` and written to `ledger/twin-census.md`.

- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [License](#license)

## Synopsis

**What.** `gandr-workflow-twin-census` installs the `twin-census` binary. `twin-census --write` writes [`ledger/twin-census.md`](../../ledger/twin-census.md): one row for each crate of the workspace, with `yes` when `gandr-runtime-emitter` depends on the crate. `twin-census --check` refuses a committed census that is not the census of the workspace, and it names each row that differs.

**Why.** A twin is a function of a crate that gandr source states. A twin that the runtime loads as a record runs through the emitter, so a crate that the emitter depends on cannot take that carrier. The census gives that fact for each crate from the graph of Cargo, and the test of the crate fails while the committed census is stale.

**How.** One call of `cargo metadata --format-version 1 --locked` gives the resolved graph. A walk from the emitter over the normal and the build edges gives each crate under it. A dev edge is no part of the emitter. The graph is the one that Cargo resolves for the workspace, with the features of each member unified. `--cost` prints each part of the run with its count of calls and its time.

## Provided features

- `twin-census --write [--root <directory>]` writes the census, then prints its path and its counts.
- `twin-census --check [--root <directory>]` exits `1` and names each crate whose row differs when the committed census is stale.
- `--cost` prints `twin-census: <part>: 1 call, <n> µs` on standard error for each part: `cargo metadata`, `read`, `render`, and `write` or `compare`.
- `Workspace::read`, `Workspace::render`, `Workspace::counts` and `stale` are the library behind the binary. `CensusError` names each refusal.

## Expected features

`cargo` on the path, or in `CARGO`. The root holds `Cargo.toml` and `Cargo.lock` of the workspace.

## Examples

```sh
cargo run --locked -p gandr-workflow-twin-census -- --write
cargo run --locked -p gandr-workflow-twin-census -- --check --cost
cargo nextest run -p gandr-workflow-twin-census
```

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
