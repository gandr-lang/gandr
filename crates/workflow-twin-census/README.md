# gandr-workflow-twin-census

The census of the crates that the emitter depends on, of their generic public items and of their public functions that an export can carry, read from `cargo metadata` and rustdoc's JSON and printed on standard output.

- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [License](#license)

## Synopsis

**What.** `gandr-workflow-twin-census` installs the `twin-census` binary. `twin-census` prints the census of the workspace as Markdown: one row for each crate, with `yes` when `gandr-runtime-emitter` depends on the crate, the count of public items of its library with a type parameter or a trait bound, and the count and the share of its public functions that an export can carry. A last section names the three crates for the next twins, each with its carrier, its public functions and its tests. No file of the tree holds the census.

**Why.** A twin is a function of a crate that gandr source states. A twin that the runtime loads as a record runs through the emitter, so a crate that the emitter depends on cannot take that carrier. An entry under the C convention carries no type parameter and no trait bound, so a generic item has no twin without a wrapper. An export carries fixed-width integers and addresses only, so a function with a different operand or result needs a wrapper too. The census gives the three facts for each crate. It is a function of the tree, so it is printed and not kept in a file.

**How.** One call of `cargo metadata --format-version 1 --locked` gives the resolved graph. A walk from the emitter over the normal and the build edges gives each crate under it. A dev edge is no part of the emitter. The graph is the one that Cargo resolves for the workspace, with the features of each member unified. One call of `cargo doc --workspace --no-deps --lib` writes rustdoc's JSON of each library to `twin-census/` below the target directory, with each lint of rustdoc capped at a warning. The binary reads the files at the same time, one thread for each core. An item counts when it is a public function, method, structure, enumeration, union, trait or type alias that the crate defines, and it has a type parameter (`impl Trait` too), a `where` clause with a trait bound, a supertrait, or an inherent implementation that is generic by the same rule. `--cost` prints each part of the run with its count of calls and its time.

A public function or method is in the export fragment when it is not generic, each operand is a fixed-width integer or an address, and its result is one of the two. The fixed-width integers are `u8` to `u64`, `i8` to `i64`, `usize` and `isize`: the widths of gandr. An address is a reference or a raw pointer to a sized type, `&self` too. A reference to a slice, to `str` or to a trait object has a length or a table beside the address, so it is not an address. A function with no result is not in the fragment, because an export gives one word.

A function that is not in the fragment has a wrapper when each of its types has a count of words: a fixed-width integer, an address, `bool` and `char` are one word; `()` is no word; a structure of the crate is the words of its fields; an enumeration of the crate is a tag word and the words of its widest variant; an alias is the type that it names; `Ordering` is one word; `Option` and `Result` are a tag word and the words of the widest argument. A generic type, a structure with a field that rustdoc strips, and each other type of a different crate have no words. A wrapper passes the operands as their words, and a result of more than one word goes to an address that the caller gives.

A crate can take a twin when it has a test, and each of its public functions is in the fragment or has a wrapper. A test is a function after `#[test]` in a source below `src/` or `tests/` of the crate. The census ranks these crates by the fewest generic public items, then by the most functions in the fragment, then by the most tests, and names the first three. The carrier of a crate under the emitter is the object; of each other crate, the object or the record.

## Provided features

- `twin-census [--root <directory>]` prints the census of the workspace at the root, and exits `1` with the reason on standard error when the census cannot be read.
- `--cost` prints `twin-census: <part>: <n> call(s), <n> µs` on standard error for each part: `cargo metadata`, `read`, `read tests`, `cargo doc`, `read rustdoc` and `render`. The tests are read while `cargo doc` runs.
- `Workspace::read`, `Workspace::libraries`, `Workspace::set_surface`, `Workspace::set_tests`, `Workspace::candidates`, `Workspace::render`, `Workspace::counts`, `rustdoc::read` and `test_names` are the library behind the binary. `rustdoc::Surface` holds the counts of one library and each public function with its `rustdoc::Carry`. `CensusError` names each refusal.

## Expected features

`cargo` on the path, or in `CARGO`, with a nightly rustdoc that writes the JSON format 61. The root holds `Cargo.toml` and `Cargo.lock` of the workspace.

## Examples

```sh
cargo run --locked -p gandr-workflow-twin-census
cargo run --locked -p gandr-workflow-twin-census -- --cost
cargo nextest run -p gandr-workflow-twin-census
```

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
