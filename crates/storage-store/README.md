# gandr-storage-store

`gandr-storage-store` holds the storage tier in one store: the value plane, the record plane and named roots under one directory.

<!-- toc -->
- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** `gandr-storage-store` is the facade every consumer of the storage tier opens: a `Store` rooted at a directory, holding the value plane's chunks, the record plane's nodes and a table of named roots. The driver roots it at the user's data directory, `$XDG_DATA_HOME/gandr/store`, and opens it once per run.

**Why.** The package lock, the build layer and the kernel's verdict cache each need a store on disk, and each opening the storage crates on its own would split one key space into three. The planes keep a persistent backend out of themselves, so the backend lives here, beside them.

**How.** Each plane is a directory of files, one per object, named by its identity in hexadecimal: `chunks/` for the value plane, `nodes/` for the record plane. An insertion is held in memory and written by the operation that made it, published through `gandr-core-publish` as a temporary file renamed into place; a load reads the file once and the plane verifies it every time. The roots are a small record tree on the record plane, named by the file `roots` and changed under `roots.lock`.

## References

- `Rainey-2026-localmem_typedirected_adaptive_serialization_location_contentaddressable_memory` — background: Michael Rainey, Michael H. Borkowski, Michael Vollmer, Chaitanya S. Koparkar, Mikah Kainen, and Vidush Singhal. "LoCalMem: Type-Directed Adaptive Serialization for Location- and Content-Addressable Memory." _Proceedings of the ACM on Programming Languages_ 10, ICFP, article 290, August 2026. [doi:10.1145/3828688](https://doi.org/10.1145/3828688) — the CAM the value plane is, which this store keeps on disk.
- `vault:01a17cb3-d471-72b2-9bd2-70a46f74c3de` — background: the build layer's design (§ build-owner-store) — the storage tier is the build layer's store, and its persistence is a backend beside the planes, not in them.
- `vault:01a178aa-ce14-7610-bcad-5aab5f9c0b0f` — background: the integrity design (§ the two layers) — integrity never stands for validity, the wall this store keeps.
- `vault:01a178aa-4bbc-7842-9a60-d11551c41e06` — background: the rollback audit (§ The real leak was in the filesystem) — the planes and the roots publish through `core-publish`, whose guard owns each temporary.

## Provided features

- `Store::open` makes the directory and its planes where they are missing and lists what they hold.
- `Store::commit` commits a `Stored` value under the store's chunking profile and the value's own codec identity, and returns its `ContentPtr`; `Store::deref` reads it back.
- `Store::write_tree` admits a record tree to the record plane; `Store::records` is the plane, a `BlockStore`, for opening a stored root and proving against it.
- `Store::set_root` names a pointer by a `RootName`, reading the roots again under the lock so two stores over one directory keep each other's; `Store::roots` reads them.
- `StoreError` names the file system's faults by path, and carries each plane's own refusal, a chunk or node changed on disk among them.

## Expected features

A stored value implements `CanonicalValue` and names its codec by `Stored::codec`, a new identity whenever its token encoding changes. A consumer opens one store per run and passes it to each part that reads or writes it. The store establishes integrity only: a consumer decides, or asks the kernel, whether the bytes a pointer names are valid.

## Examples

Run the crate's tests from the repository root:

```sh
mise exec -- cargo test -p gandr-storage-store
```

## Where the detail lives

Mechanism and witnesses live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| The facade's layer, its wall, references | [`src/lib.rs`](src/lib.rs) |
| The two planes on disk and their pending writes | [`plane`](src/plane.rs) |
| Named roots as a record tree | [`roots`](src/roots.rs) |
| The facade, its profile and its faults | [`store`](src/store.rs) |

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
