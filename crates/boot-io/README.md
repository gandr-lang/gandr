# gandr-boot-io

The IO core of the bootstrap, with no libc: open a file, read it, write to a descriptor and close it, each by the crate's own system call.

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

**What.** `start` gives an `Io` handle, and `stop` ends it. `open` takes the path of a file as a `Range` of `boot-core` and gives a `Descriptor`. `read` writes the next bytes of the file into a `Place` and gives their count. `write` gives the bytes of a `Range` to a descriptor and gives the count that the kernel took. `close` ends the descriptor. Each refusal is a `Refused`: the name of the operation and the error number of the kernel.

**Why.** The tool chain reads each source through Rust's `std`, which links libc. The bootstrap needs a read with no libc before gandr states it itself. A crate of the layer `boot` is a stage of the bootstrap, and a twin in gandr replaces it.

**How.** On Linux x86-64, `open`, `read`, `write` and `close` each make one system call by the crate's own function in assembly. No function repeats a call, so an interrupted call is a refusal with `EINTR`, and a write that the kernel takes in part gives its short count. The crate has no ring, so `start` and `stop` make no system call. A form that reads through a ring keeps the address of the page of its ring in its `Io`. A path is the bytes of a `Range` with a zero byte after its last byte. No function allocates or panics, and the crate is `no_std`.

## References

- `vault:01a1ebc5-2ff2-7833-b871-85901e734925` — newest: the data core of the bootstrap (§ boot-data-crates) — the rules of a crate of the layer `boot`, and the row of this crate.
- `vault:01a1e7b4-8c77-7a81-9165-ff37ea870424` — newest: the IO direction (§ io-direction-core) — the IO core crate, whose signatures hold no generic parameter and no type of `std`.

## Provided features

- `start` and `stop`: the handle of the IO core.
- `open`: a file to read, from a path relative to the working directory or from the root. The kernel closes the descriptor when the process runs another program.
- `read`: the next bytes of a file into the start of a place, at most its length. The count 0 for a place that is not empty is the end of the file. An empty place gives the count 0 and takes no byte.
- `write`: the first bytes of a range to a descriptor, at most its length. A count below the length is a short write, and the caller gives the rest.
- `close`: the end of a descriptor.
- `Refused`, `Operation` and `ErrorNumber`: the refusal of the kernel, with the name of the operation.

## Expected features

- **A path with a zero byte after it.** No byte of the path is zero. The byte after its last byte is zero.
- **A live place.** The bytes of the place of a read are writable. No other access to them happens during the call.
- **A live range.** The bytes of the range of a write are readable. No other access writes them during the call.
- **A host of Linux on x86-64.** On each other target the crate compiles, and each use of one of its six functions is one error of the compiler that names the target.

## Examples

The witnesses run each function against one table of subjects, so a twin in gandr runs against the same cases. A witness reads a file of the tree whole in steps of one page, and compares the bytes with the bytes that `std` reads. Another witness reads each source of the corpus. One witness reads into an empty place. One witness interrupts a read that waits by a signal, and reads again. The witnesses of the write give bytes to a socket of `std`, and one makes a short write to a socket that does not wait. One witness closes the standard input, so it runs in a target of its own.

```sh
cargo test -p gandr-boot-io
```

## Where the detail lives

`src/lib.rs` states the face and the refusals; `src/sys.rs` the four file calls; `src/sys/x86_64.rs` the system call instruction; `src/target.rs` the face on a target with no system call of the crate.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
