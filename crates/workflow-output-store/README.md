# gandr-workflow-output-store

The store of the values that a program computes from the tree and that the tree does not hold.

- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Dependencies](#dependencies)
- [License](#license)

## Synopsis

**What.** `gandr-workflow-output-store` is a workflow library. It holds each value of an output in one file below a directory, named by the key of the value. It holds the list of the values of each tree, and the values that a test gives.

**Why.** The writers of `gandr-workflow-outputs` and the tests of a crate both write to the store. A test crate that depends on this crate builds no writer of the outputs.

**How.** The key of a value is a BLAKE3 digest. A value is written beside its place and renamed into it, so a reader sees no part of a value and two writers need no lock. A test writes its value at the digest of its kind and its bytes, and an entry with the key and the name to the directory of its run.

## Provided features

- `Store` reads and writes a value by its kind and its key, and the list of the values of a kind by its git tree. `Digest` is a key or a tool, `Kind` a kind of output, and `Listed` one entry of a list.
- `given::give` gives the value of a test to the run that the environment names. `given::entries` reads the entries of a run in name order.

## Expected features

`GANDR_OUTPUT_STORE` names the store and `GANDR_OUTPUT_RUN` names the directory of a run of the tests of a kind. With either variable unset, a test gives nothing.

## Examples

```sh
cargo nextest run -p gandr-workflow-output-store
```

## Dependencies

`blake3` gives the key. The build graph holds it for the identities of contents. It uses no default features.

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
