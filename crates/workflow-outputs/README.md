# gandr-workflow-outputs

The values that a program computes from the tree and that the tree does not hold: the writer of each kind of output.

- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Dependencies](#dependencies)
- [License](#license)

## Synopsis

**What.** `gandr-workflow-outputs` is a workflow library and the `outputs` binary. An output is a value that is a function of the tree and of the tool, such as the recovery record of a corpus source. This crate holds the writer of each kind of output, and a store outside the tree that holds each value by the digest of its tool and its input.

**Why.** A test that compares a value with a file of the tree and the tool that computes the value for a store must write the same value. One writer serves both. A value that the tree does not hold is computed one time for each tool and each source, not one time for each run.

**How.** `Recorder::new` names each mold of a grammar by its rule, its label and its rank. `Recorder::record` parses a source and writes its record: `W`, the count of the obligations, the count of the positions and the fingerprint of the tree, separated by tabs. The fingerprint is the BLAKE3 digest of the significant nodes in preorder, so a change of the grammar that renumbers the molds does not move it.

The key of a value is the BLAKE3 digest of the tool and the input. The tool is the git tree identifier of each package that builds the writer, with the root manifest, the lock and the toolchain file. The input is the git object identifier of the source. The store holds one file for each key, written beside its place and renamed into it, so two runs need no lock.

## Provided features

- `Recorder` writes the recovery record of a source, and the fingerprint of a tree.
- `RecordError` names the refusal of the grammar or of the parser.
- `Roles` writes the roles that the highlight gives a source: one line for each span, with its byte range, its role and its text.
- `Store` reads and writes a value by its kind and its key; `Digest` is a key or a tool.
- `Tree` reads a commit or the work tree from git: its corpus sources, their contents in one batch, and the tool of a kind.
- `workspace::closure` gives the packages that build a package, from `cargo metadata`.
- `compute::values` gives the values of one kind for a tree: each from the store, or computed by the `Writer` of the kind on each core and written to the store. `compute::held` gives the values that the store holds. The kinds are `recovery` and `roles`.
- `checkout::compute` computes the values of a commit whose tool is not the tool of the run: the `outputs` binary of that commit runs in a detached work tree below `target/`, on the same store.
- `difference::changes` gives the sources whose values differ between two trees: added, removed or changed.
- `gauge` reads the size of the store and the count of the values of the base that a run computes again. A gauge past its bound writes one line with the priority `err` and runs the command that `GANDR_OUTPUT_EVENT` names.

## Expected features

`git` on the path. The store is the directory that `GANDR_OUTPUT_STORE` names, or `target/outputs` below the workspace root. `GANDR_OUTPUT_STORE_BOUND` sets the bound of the size of the store in bytes, and `GANDR_OUTPUT_RECOMPUTED_BOUND` the bound of the values of the base that one run computes again. `GANDR_OUTPUT_EVENT` names a command that takes the name of a gauge, its value and its bound.

## Examples

```sh
cargo nextest run -p gandr-workflow-outputs
cargo run -p gandr-workflow-outputs --bin outputs -- compute recovery --cost          # the work tree
cargo run -p gandr-workflow-outputs --bin outputs -- compute recovery --revision HEAD --print
cargo run -p gandr-workflow-outputs --bin outputs -- difference recovery --base origin/main --cost
```

## Dependencies

`blake3` gives the fingerprint and the key; it is already in the build graph for content identities, with default features off. `serde_json` reads the output of `cargo metadata`; it is already in the build graph of the workflow binaries.

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
