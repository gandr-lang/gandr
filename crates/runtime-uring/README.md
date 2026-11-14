# gandr-runtime-uring

A Rust crate for the Linux Userspace API.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** `gandr-runtime-uring` is the kernel's `io_uring` as Rust types. It holds the ring, its submission and completion queues, its registrar of files, and a preparer for each operation that liburing names. The crate is the owner's own text. The tree mends it in place to the tree's wall.

**Why.** gandr's storage, its transport and its standard library take their asynchronous IO from one ring for each worker. The ring removes a system call and a wait from each operation. The crate gives the whole interface of the ring, each operation the kernel offers, and not one consumer's subset of it.

**How.** `IoUring` sets up a ring through `IoUringBuilder`. The builder takes each setup flag at most once, and it fixes the sizes of the two kinds of entry in the ring's type. `SubmissionQueue` gives free entries, and a preparer method of `Sqe64` fills each one. `CompletionQueue` gives the ready completions, or waits for them, and marks each given one as seen when its run drops. The crate calls liburing, the kernel's C library of the ring, for each step.

## Provided features

- `IoUring::new` sets up a ring of 4096 entries. `IoUring::builder` sets up a ring with the flags and the values that the caller names. These include polling, a polling thread and its core, the size of the completion queue and a shared work queue. They include a single issuer and deferred task work too.
- `IoUring::squeue`, `IoUring::cqueue` and `IoUring::queues` borrow the queues. `IoUring::registrar` borrows the registrar, and `IoUring::ring_fd` the ring's own descriptor.
- `SubmissionQueue::get_sqe` and `SubmissionQueue::get_sqes` give free entries. `SubmissionQueue::submit` and `SubmissionQueue::submit_and_wait` submit them.
- `Sqe64` and `Sqe128` hold one preparer for each operation of liburing. The operations include read, write, sync, open, close, accept, connect, send, receive, poll, timeout, cancel, futex, splice, statx and the extended attributes. `Sqe64::set_flags` puts the entry's flags in place. `Sqe64::set_data` and `Sqe64::set_data64` put its user data in place.
- `CompletionQueue::ready` and `CompletionQueue::wait` give the completions as `Cqe16` or `Cqe32`.
- `Registrar::register_files` and `Registrar::register_files_sparse` register the ring's file table. `SlotDesc` names a slot of that table or a descriptor of the process.

## Expected features

The crate runs on Linux alone. On another system it compiles empty. A kernel that refuses `io_uring` refuses `IoUring::new` with its error number.

The build compiles liburing from the liburing crate, so it needs a C compiler. With the `bindgen` feature on, the build script also makes the kernel's declarations for the target. Then it needs a `libclang` and the target's kernel headers, named by a variable such as `x86_64_LINUX_HEADERS`. With the feature off, which is the ordinary build, it needs neither.

Each preparer is `unsafe`. The caller keeps each pointer of an entry valid until the kernel posts its completion, and each descriptor open. Each preparer's `# Safety` names what it reads.

## Examples

The example sets up a ring and submits one operation that does nothing. Then it waits for the completion:

```rust,no_run
use gandr_runtime_uring::IoUring;

fn main() -> std::io::Result<()> {
    let mut ring = IoUring::new()?;
    let (mut sq, mut cq) = ring.queues();
    let mut sqe = sq.get_sqe().ok_or_else(|| std::io::Error::other("the queue is full"))?;
    // SAFETY: a no-op reads no pointer and names no descriptor.
    unsafe { sqe.prep_nop() };
    sq.submit_and_wait(1)?;
    assert_eq!(cq.wait(1)?.count(), 1);
    Ok(())
}
```

Run the crate's tests from the repository root:

```sh
mise exec -- cargo nextest run -p gandr-runtime-uring
```

## Where the detail lives

The crate's lead in [`src/lib.rs`](src/lib.rs) names the parts. Each module's rustdoc states its mechanism. [`src/ring.rs`](src/ring.rs) holds the ring and its builder. [`src/squeue.rs`](src/squeue.rs) and [`src/cqueue.rs`](src/cqueue.rs) hold the queues. [`src/sqe.rs`](src/sqe.rs) and [`src/cqe.rs`](src/cqe.rs) hold the entries. Under [`src/sqe/`](src/sqe) each kind of operation has one module of preparers.

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
