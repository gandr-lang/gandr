# gandr-boot-alloc

Memory for the bootstrap from the kernel's mapping calls, with no libc: whole pages, and a heap in size classes over them.

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

**What.** `map` gives a block of whole pages with a stated protection, `protect` changes the protection, and `unmap` gives the block back. A `Heap` cuts blocks in size classes from 16 bytes to 4 KiB out of runs of 64 KiB, or of one page when a page is larger. A block past the largest class takes whole pages of its own. The heap is an allocator of Rust's `alloc` through a shared reference, so a vector or a box can live in it.

**Why.** The parts of the bootstrap need memory before gandr has an allocator of its own. Rust's allocator takes its memory from libc, and the bootstrap links no libc on Linux. A crate of the layer `boot` is a stage of the bootstrap, and a twin in gandr replaces it.

**How.** On Linux each mapping call is a system call by the crate's own function in assembly, on x86-64, aarch64 and riscv64. On macOS it is a declared function of the system library, because the kernel there keeps no stable numbers for its calls. The caller states the size of a page, and the crate asks no library for it. Each class keeps a list of its free blocks and a cursor into its newest run, so an allocation is constant work. Only a new run costs a call to the host. The first block of each run holds the address of the run before it, and the end of the heap gives each run back.

## References

- `vault:01a1ebc5-2ff2-7833-b871-85901e734925` — newest: the data core of the bootstrap (§ boot-data-crates) — the rules of a crate of the layer `boot`, and the row of this crate.
- `vault:01a1e7b4-8c77-7a81-9165-ff37ea870424` — newest: the IO direction (§ io-direction-no-libc) — the path with no libc, and the census of the emitter's calls through libc.

## Provided features

- `map`, `protect` and `unmap`: whole pages from the host, each a `Block` with a `Protection`.
- `PageSize` and `Pages`: the size of a page that the caller states, and a count of pages.
- `Heap`: blocks in size classes over runs of pages, for one thread, with `allocate`, `grow` and `free`, and Rust's `Allocator` through `&Heap`.
- `Refused`: each refusal, as an `Operation` and an `ErrorNumber`.

## Expected features

- **A host of Linux or macOS.** The system call of each Linux target is written for x86-64, aarch64 and riscv64.
- **A page size from the caller.** A program reads it from its auxiliary vector or from its system library.
- **One thread for each heap.** A heap is not `Sync`, and two threads hold two heaps.

## Examples

The witnesses map, write and unmap pages on the host, refuse a count past the address space, keep the bytes of each live block of a heap, and count the bytes that the process maps before a heap starts and after it ends.

```sh
cargo test -p gandr-boot-alloc
```

## Where the detail lives

`src/lib.rs` states the face and the refusals; `src/heap.rs` the size classes and the runs; `src/sys/linux.rs` and its three modules the system calls; `src/sys/macos.rs` the calls of the system library.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
