# gandr-core-content

This crate gives the content form of a core node. A reader outside the checker needs a name for a type or a term that survives a second session. An arena id and an admission position do not survive it. The content form names a node by its canonical table instead.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [References](#references)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** A table lists every node that a root reaches, numbered by discovery. It holds no arena id and no admission position. Two arenas that hold equal terms give equal tables. A table mints back into an arena as a node with that content.

**Why.** The incremental store and the image of a command read one content form. The crate sits under the checker, so a crate that names a node by its content keeps the checker out of its tree.

**How.** A caller gives a `Resolver`, which names each constant as a `Reference` and places a reference back. The encoder reads the arena through it, and the mint places each constant through it.

## Provided features

- `ContentNode`, `SupportedNode`, `TypeContent` and `TypeMemo`: the node form, its supported table and the memo of the tables of one arena.
- `Encoder`, `DataRoots`, `tabled` and `tabled_roots`: the table of a set of roots.
- `TypeContent::mint` and `mint_table`: a table minted back into an arena.
- `Reference`, `ItemKey`, `KeyName`, `SourceTag` and `Occurrence`: the name of a constant outside its revision.
- `Resolver`: the seam where a caller names and places its constants.

## Expected features

- **A resolver.** Each caller supplies the names of its constants. The incremental checker supplies its layout.
- **`alloc`.** The crate allocates its tables.

## Examples

The witnesses live in the tests of `gandr-core-incremental`, which reads this crate through its layout.

## Where the detail lives

| Topic | Module |
| ----- | ------ |
| The table, the encoder, the projection and the mint | [`content`](src/content.rs) |
| The co-de Bruijn table and its factoring | [`support`](src/support.rs) |
| The name of a constant and the resolver | [`reference`](src/reference.rs) |
| The indices of a table | [`boundary`](src/boundary.rs) |

## References

- `vault:01a1e7b4-8c77-7a81-9165-ff37ea870424` — lineage: § io-direction-first-crate — the checker stays out of the tree of the embedded crate.
- `vault:01a178aa-74f1-7b03-a3a9-d145795bf4fd` — lineage: the design of the content form and its node keys.

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
