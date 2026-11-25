# gandr-workflow-outputs

The values that a program computes from the tree and that the tree does not hold: the writer of each kind of output.

- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Dependencies](#dependencies)
- [License](#license)

## Synopsis

**What.** `gandr-workflow-outputs` is a workflow library. An output is a value that is a function of the tree and of the tool, such as the recovery record of a corpus source. This crate holds the writer of each kind of output.

**Why.** A test that compares a value with a file of the tree and the tool that computes the value for a store must write the same value. One writer serves both.

**How.** `Recorder::new` names each mold of a grammar by its rule, its label and its rank. `Recorder::record` parses a source and writes its record: `W`, the count of the obligations, the count of the positions and the fingerprint of the tree, separated by tabs. The fingerprint is the BLAKE3 digest of the significant nodes in preorder, so a change of the grammar that renumbers the molds does not move it.

## Provided features

- `Recorder` writes the recovery record of a source, and the fingerprint of a tree.
- `RecordError` names the refusal of the grammar or of the parser.

## Expected features

None.

## Examples

```sh
cargo nextest run -p gandr-workflow-outputs
```

## Dependencies

`blake3` gives the fingerprint; it is already in the build graph for content identities, with default features off.

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
