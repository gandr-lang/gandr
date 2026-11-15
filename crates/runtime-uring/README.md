# gandr-runtime-uring

A Rust crate for the Linux Userspace API.

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

**What.** `gandr-runtime-uring` is the kernel's `io_uring` as Rust types. It holds the ring, its submission and completion queues, its registrar of files, and a preparer for each operation that liburing names. The crate is the owner's own text. The tree mends it in place to the tree's wall.

**Why.** gandr's storage, its transport and its standard library take their asynchronous IO from one ring for each worker. The ring removes a system call and a wait from each operation. The crate gives the whole interface of the ring, each operation the kernel offers, and not one consumer's subset of it.

**How.** `IoUring` sets up a ring through `IoUringBuilder`. The builder takes each setup flag at most once, and it fixes the sizes of the two kinds of entry in the ring's type. `SubmissionQueue` gives free entries, and a preparer method of `Sqe64` fills each one. `CompletionQueue` gives the ready completions, or waits for them, and marks each given one as seen when its run drops. The crate calls liburing, the kernel's C library of the ring, for each step. The module `base` holds the owner's newer system-call base beside the ring. It issues `io_uring_setup`, `io_uring_register` and `io_uring_enter` by inline assembly, with no C library. No call of the ring goes through it yet.

## References

- `vault:01a1d8c5-08cb-7e12-a5d5-9a2ad3279160` — anchor: the IO layer's design (§ io-layer-crate) — the owner's crate, copied whole and mended in place, with its build script and the made declarations of each architecture.

## Provided features

- `IoUring::new` sets up a ring of 4096 entries. `IoUring::builder` sets up a ring with the flags and the values that the caller names. These include polling, a polling thread and its core, the size of the completion queue and a shared work queue. They include a single issuer and deferred task work too. With `setup_mem`, the rings live in memory that the caller gives.
- `IoUring::squeue`, `IoUring::cqueue` and `IoUring::queues` borrow the queues. `IoUring::registrar` borrows the registrar, and `IoUring::ring_fd` the ring's own descriptor.
- `SubmissionQueue::get_sqe` and `SubmissionQueue::get_sqes` give free entries. `SubmissionQueue::submit` and `SubmissionQueue::submit_and_wait` submit them.
- `Sqe64` and `Sqe128` hold one preparer for each operation of liburing. The operations include read, write, sync, open, close, accept, connect, send, receive, poll, timeout, cancel, futex, splice, statx and the extended attributes. `Sqe64::set_flags` puts the entry's flags in place. `Sqe64::set_data` and `Sqe64::set_data64` put its user data in place.
- `CompletionQueue::ready` and `CompletionQueue::wait` give the completions as `Cqe16` or `Cqe32`.
- `Registrar::register_files` and `Registrar::register_files_sparse` register the ring's file table. `SlotDesc` names a slot of that table or a descriptor of the process.
- `base::io_uring_setup`, `base::io_uring_register`, `base::io_uring_register_with` and `base::io_uring_enter` issue the ring's three system calls by inline assembly on x86-64, aarch64, riscv64, powerpc64 and s390x. `base::Sqe64`, `base::Sqe128`, `base::Cqe16` and `base::Cqe32` are the four sizes of entry.

## Expected features

The crate runs on Linux alone. On another system it compiles empty. A kernel that refuses `io_uring` refuses `IoUring::new` with its error number.

The liburing crate makes its C library and its bindings in each build. So each build needs `make`, a C compiler and a `libclang`. With the `bindgen` feature on, this crate's build script also makes the base's declarations for the target, under `src/base/sys/linux/uapi/arch`. It reads the target's kernel headers from a variable such as `x86_64_LINUX_HEADERS`. Without that variable it makes nothing. On powerpc64 the build needs `--cfg asm_experimental_arch`, because the base's inline assembly is unstable there.

Each preparer is `unsafe`. The caller keeps each pointer of an entry valid until the kernel posts its completion, and each descriptor open. Each preparer's `# Safety` names what it reads.

## Examples

The example opens a ring and submits one operation that does nothing. Then it waits for the completion:

```rust,no_run
use gandr_runtime_uring::IoUring;
use gandr_runtime_uring::arg::Count;

fn main() -> std::io::Result<()> {
    let mut ring = IoUring::new()?;
    let (mut sq, mut cq) = ring.queues();
    let mut sqe = sq.get_sqe().ok_or_else(|| std::io::Error::other("the queue is full"))?;
    // SAFETY: a no-op reads no pointer and names no descriptor.
    unsafe { sqe.prep_nop() };
    sq.submit_and_wait(Count(1))?;
    assert_eq!(cq.wait(Count(1))?.count(), 1);
    Ok(())
}
```

Run the crate's tests from the repository root:

```sh
mise exec -- cargo nextest run -p gandr-runtime-uring
```

## Where the detail lives

The crate's lead in [`src/lib.rs`](src/lib.rs) names the parts. Each module's rustdoc states its mechanism. [`src/ring.rs`](src/ring.rs) holds the ring and its builder. [`src/squeue.rs`](src/squeue.rs) and [`src/cqueue.rs`](src/cqueue.rs) hold the queues. [`src/sqe.rs`](src/sqe.rs) and [`src/cqe.rs`](src/cqe.rs) hold the entries. Under [`src/sqe/`](src/sqe) each kind of operation has one module of preparers. [`src/base.rs`](src/base.rs) holds the owner's system-call base, and [`src/base/sys/linux/`](src/base/sys/linux) holds its error number, its entries of each architecture and its UAPI.

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
