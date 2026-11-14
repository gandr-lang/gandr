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

**How.** Each plane is a log of records in segment files, `segment-<identity>` in hexadecimal: `chunks/` for the value plane, `nodes/` for the record plane. A record is a header of 64 bytes, which names the object's identity, its length and its place and ends in a checksum, and then the object's bytes. A plane scans its segments once, when the store opens, into an index from identity to record, and holds each record at a fixed slot of an append-only arena, so threads share one store with no lock. Each call holds a batch over a plane, the section of the plane that the call owns: an insertion goes into the batch, and when the call ends the batch appends its records to its shard's segment in one positioned write and marks the segment. Each shard appends to a segment of its own, and each process creates its segments exclusively, so no two writers share a segment. A load reads a record once in the process, and the plane verifies it every time. A load that misses scans the segments that other processes appended to since. The roots are a small record tree on the record plane, logged by the file `roots.log`, one line for each fold, and a journal of the namings since, `roots.log.journal`, both changed under `roots.lock`. One register writes them. A naming first syncs each marked segment with one `fdatasync`, so one sync covers every put since the last naming and a root never names an object a crash can lose. It then appends one synced entry, and the journal folds into the tree once it holds as many entries as the tree holds roots, so a naming costs amortised constant time. Each step of a fold is durable before the next starts, so a crash leaves roots whose objects load. Other threads hand their namings to the register's owner through a channel, and readers load the snapshot that the register publishes through `arc-swap`.

## References

- `Rainey-2026-localmem_typedirected_adaptive_serialization_location_contentaddressable_memory` — background: Michael Rainey, Michael H. Borkowski, Michael Vollmer, Chaitanya S. Koparkar, Mikah Kainen, and Vidush Singhal. "LoCalMem: Type-Directed Adaptive Serialization for Location- and Content-Addressable Memory." _Proceedings of the ACM on Programming Languages_ 10, ICFP, article 290, August 2026. [doi:10.1145/3828688](https://doi.org/10.1145/3828688) — the CAM the value plane is, which this store keeps on disk.
- `vault:01a17cb3-d471-72b2-9bd2-70a46f74c3de` — background: the build layer's design (§ build-owner-store) — the storage tier is the build layer's store, and its persistence is a backend beside the planes, not in them.
- `vault:01a178aa-ce14-7610-bcad-5aab5f9c0b0f` — background: the integrity design (§ the two layers) — integrity never stands for validity, the wall this store keeps.
- `vault:01a1d8c5-08cb-7e12-a5d5-9a2ad3279160` — anchor: the IO layer's design (§ io-layer-extents) — a shard is a log of its own, and a put appends with no directory entry.
- `vault:01a178ab-17e5-7352-bc0b-3caa7f1e476c` — background: the storage programme's chunk DAG, whose closure of a pointer `Store::closure` reads with no codec.
- `vault:01a1cf3f-b730-7152-9d64-050e5c00b32a` — lineage: the store's single writer plan (§ the idempotent part, § the register, § Refinements) — the planes' puts take `&self`, since two puts of one object write the same bytes; one register owns the roots; and the shard is per producer, each with a segment of its own.
- `vault:01a1d7fd-eeb5-7010-80e7-df4d768b6583` — anchor: the performance programme (§ performance-picture) — a put is durable before the root that names it, by one sync for each written segment and never one for each put.
- `vault:01a1d90b-b64a-7248-8f6e-e792b6e8cb9f` — background: the IO layer's probe (§ the grid) — one segment per shard, whose sync covers many puts, against a file per object and against the ring.

## Provided features

- `Store::open` makes the directory and its planes where they are missing, scans what they hold, and gives the store's `Register`.
- `Store::commit` commits a `Stored` value under the store's chunking profile and the value's own codec identity through `&self`, on any thread, and returns its `ContentPtr`; `Store::deref` reads it back.
- `Store::closure` reads where a value resides with no codec: its `Residence`, the chunks a dereference of its pointer loads, each verified, and the `ImageBytes` of their images. The store writes nothing for it.
- `Store::write_tree` admits a record tree to the record plane through `&self`; `Store::records` is a `NodeBatch` over the plane, a `BlockStore`, for opening a stored root and proving against it.
- `Register::name` names a pointer by a `RootName` in amortised constant time through `&mut self`, reading under the lock what another store over the same directory named since, so two stores keep each other's roots. A `Namer` hands a naming to the register's owner through `&self`, and `Register::drain` names every naming handed over under one lock. `Store::roots` loads the snapshot the register last published, with no lock.
- `Store::read_in` reads a directory, a file or a symbolic link into the store as an `Entry` (#6590): a directory is one record tree keyed by name, a file a blob cut by the chunker's byte profile, each piece one value. A file reads one buffer of 1 MiB at a time, and each piece goes to the value plane at its cut, so a read holds one buffer and one piece, never the file (#6719). A tree read again writes no object, and an edit writes only the pieces near it and the trees above it. `Store::write_out` writes an entry into a new path with the same bytes and executable bit, and refuses a name that would leave its directory. `Output` holds a root entry and the addresses it references; its identity is the root's address. The entries need a Unix target.
- `StoreError` names the file system's faults by path, and carries each plane's own refusal, a chunk or node changed on disk among them.

## Expected features

A stored value implements `CanonicalValue` and names its codec by `Stored::codec`, a new identity whenever its token encoding changes. A consumer opens one store per run and shares it with each part that reads or writes it, on any thread. The store establishes integrity only: a consumer decides, or asks the kernel, whether the bytes a pointer names are valid.

## Examples

Run the crate's tests from the repository root:

```sh
mise exec -- cargo test -p gandr-storage-store
```

Measure the load of many files into one store at once. The bench prints one row for each width: the rate of its puts, the 50th and 99th percentile of a call, and the wall of the open that scans the store after. `--files <n>` sets the count of files, and `--directory <path>` the device the stores stand on:

```sh
mise exec -- cargo bench -p gandr-storage-store --bench load -- --files 20000 --directory /path/on/the/device
```

## Where the detail lives

Mechanism and witnesses live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| The facade's layer, its wall, references | [`src/lib.rs`](src/lib.rs) |
| The two planes on disk, their segments, their scan at open and each call's batch | [`plane`](src/plane.rs) |
| The named points where a crash test stops a writer | [`crash`](src/crash.rs) |
| A built output as a tree of entries, and its blobs | [`entries`](src/entries.rs) |
| Named roots as a record tree and a journal of the namings since | [`roots`](src/roots.rs) |
| The one writer of the roots, its namers and the readers' snapshot | [`register`](src/register.rs) |
| The facade, its profile and its faults | [`store`](src/store.rs) |

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
