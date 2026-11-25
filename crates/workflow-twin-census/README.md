# gandr-workflow-twin-census

The census of the crates that the emitter depends on, of their generic public items and of their public functions that an export can carry, read from `cargo metadata` and rustdoc's JSON and written to `ledger/twin-census.md`.

- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [License](#license)

## Synopsis

**What.** `gandr-workflow-twin-census` installs the `twin-census` binary. `twin-census --write` writes [`ledger/twin-census.md`](../../ledger/twin-census.md): one row for each crate of the workspace, with `yes` when `gandr-runtime-emitter` depends on the crate, the count of public items of its library with a type parameter or a trait bound, and the count and the share of its public functions that an export can carry. `twin-census --check` refuses a committed census that is not the census of the workspace, and it names each row that differs.

**Why.** A twin is a function of a crate that gandr source states. A twin that the runtime loads as a record runs through the emitter, so a crate that the emitter depends on cannot take that carrier. An entry under the C convention carries no type parameter and no trait bound, so a generic item has no twin without a wrapper. An export carries fixed-width integers and addresses only, so a function with a different operand or result needs a wrapper too. The census gives the three facts for each crate, and the test of the crate fails while the committed census is stale.

**How.** One call of `cargo metadata --format-version 1 --locked` gives the resolved graph. A walk from the emitter over the normal and the build edges gives each crate under it. A dev edge is no part of the emitter. The graph is the one that Cargo resolves for the workspace, with the features of each member unified. One call of `cargo doc --workspace --no-deps --lib` writes rustdoc's JSON of each library to `twin-census/` below the target directory, with each lint of rustdoc capped at a warning. The binary reads the files at the same time, one thread for each core. An item counts when it is a public function, method, structure, enumeration, union, trait or type alias that the crate defines, and it has a type parameter (`impl Trait` too), a `where` clause with a trait bound, a supertrait, or an inherent implementation that is generic by the same rule. `--cost` prints each part of the run with its count of calls and its time.

A public function or method is in the export fragment when it is not generic, each operand is a fixed-width integer or an address, and its result is one of the two. The fixed-width integers are `u8` to `u64`, `i8` to `i64`, `usize` and `isize`: the widths of gandr. An address is a reference or a raw pointer to a sized type, `&self` too. A reference to a slice, to `str` or to a trait object has a length or a table beside the address, so it is not an address. A function with no result is not in the fragment, because an export gives one word.

## Provided features

- `twin-census --write [--root <directory>]` writes the census, then prints its path and its counts.
- `twin-census --check [--root <directory>]` exits `1` and names each crate whose row differs when the committed census is stale.
- `--cost` prints `twin-census: <part>: <n> call(s), <n> µs` on standard error for each part: `cargo metadata`, `read`, `cargo doc`, `read rustdoc`, `render`, and `write` or `compare`.
- `Workspace::read`, `Workspace::libraries`, `Workspace::set_surface`, `Workspace::render`, `Workspace::counts`, `rustdoc::read` and `stale` are the library behind the binary. `rustdoc::Surface` holds the three counts of one library. `CensusError` names each refusal.

## Expected features

`cargo` on the path, or in `CARGO`, with a nightly rustdoc that writes the JSON format 61. The root holds `Cargo.toml` and `Cargo.lock` of the workspace.

## Examples

```sh
cargo run --locked -p gandr-workflow-twin-census -- --write
cargo run --locked -p gandr-workflow-twin-census -- --check --cost
cargo nextest run -p gandr-workflow-twin-census
```

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
