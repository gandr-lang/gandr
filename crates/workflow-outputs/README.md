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

**Why.** A file of the tree that a program writes conflicts in each pair of changes that move it, and a reader of a change cannot tell an intended difference from the noise. A value in the store conflicts with nothing. The landing compares the values of a change with the values of its base, and refuses a difference that no commit names. A value that the tree does not hold is computed one time for each tool and each input, not one time for each run.

**How.** `Recorder::new` names each mold of a grammar by its rule, its label and its rank. `Recorder::record` parses a source and writes its record: `W`, the count of the obligations, the count of the positions and the fingerprint of the tree, separated by tabs. The fingerprint is the BLAKE3 digest of the significant nodes in preorder, so a change of the grammar that renumbers the molds does not move it.

The key of a record or of the roles of a source is the BLAKE3 digest of the tool and the input. The tool of a kind is the git tree identifier of each package that computes the kind, the manifest of each package that builds the binary, the root manifest, the lock and the toolchain file. The input is the git object identifier of the source. The store holds one file for each key, written beside its place and renamed into it, so two runs need no lock.

The refusals of a source read the library and the other sources, so one walk computes them for each refusing source of a tree. The key of a text is the digest of its bytes, so two trees share a text that did not change. The list of the texts is at the digest of the tool with the corpus and the library, so a tree with those inputs needs no walk.

The store holds one list for each kind and each git tree that a run computed: each value of the tree with its key, its input and its name. A run reads the values of a tree with another tool from that list, so it needs no key of that tool.

## Provided features

- `Recorder` writes the recovery record of a source, and the fingerprint of a tree.
- `RecordError` names the refusal of the grammar or of the parser.
- `Roles` writes the roles that the highlight gives a source: one line for each span, with its byte range, its role and its text.
- `refusals::rendered` writes the refusals that `gandr check` prints for each refusing source of a checkout: each diagnostic plain, at the verbosity of a user.
- The store of `gandr-workflow-output-store` reads and writes a value by its kind and its key, and the list of the values of a kind by its git tree.
- `Tree` reads a commit or the work tree from git: its corpus sources, its refusing sources, their contents in one batch, and the tool of a kind.
- `workspace::closure` gives the packages that build a package, from `cargo metadata`. `compute::packages` names the packages that compute a kind.
- `compute::values` gives the values of one kind for a tree: each from the store, or computed by the `Writer` of the kind on each core and written to the store. It writes the list of the tree. `compute::held` gives the values that the store holds, and `compute::listed` the values that the list of a tree names. `compute::refusals` gives the refusals of a tree, from the list of its inputs or from one walk of a checkout. The kinds are `captures`, `formatted`, `hovers`, `printed`, `recovery`, `refusals`, `rendered`, `roles` and `uncommented`.
- `compute::TESTED` names each kind whose values only a test can compute: the package of its tests, the filter of nextest, and the paths of the tree that the tests read. `compute::tested_values` reads the list of a run at the digest of the tool with those inputs, or starts the tests in a checkout and lists the values that they give. The tests of the terminal face give the captures. The tests of the formatter, the printer and the terminal renderer give their texts. The tests of the language server give the hovers of the headline sources. The comment gate of the corpus gives the uncommented items of each source.
- `compute::RATCHETS` names each kind that is a ratchet. `uncommented` is one.
- `compute::work_tree_refusals` gives the refusals of the work tree of a checkout under the tool of that work tree. They come from the store, or from one walk that fills the store. The prose check reads the refusals of the corpus with it.
- `checkout::compute` computes the values of a commit whose tool is not the tool of the run: the `outputs` binary of that commit runs in a detached work tree below `target/`, on the same store. A binary that refuses its command line exits with 2. A commit whose binary refuses a kind thus has no value of the kind, and `outputs difference` shows each value of the head as a change.
- `difference::changes` gives the sources whose values differ between two trees: added, removed or changed. `difference::added` gives the members of a ratchet that the head has and the base does not have: a member is a line of a value, with no name of its source.
- `word::named` tells if a commit of a range names a kind in a trailer `Changes-output: <kind>`. `outputs difference` exits with 1 for a difference that no commit of the range names, so an output does not change without a word.
- One run of `outputs` answers each kind that its command line names: one kind, kinds with a comma between them, or `all`. A run reads each tree one time. Two runs do not make the checkout of one base at the same time: the second one waits for a lock.
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
