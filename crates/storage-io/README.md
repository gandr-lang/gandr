# gandr-storage-io

The IO layer of the storage tier. Each worker owns one io_uring. The crate issues the ring's system calls by the architecture's own instruction, with no C library.

- `src/uapi.rs` holds the io_uring layouts and the table of system-call numbers by architecture. `mise run uapi:generate` writes it from the pinned kernel, and the gate's `check:uapi` refuses a file that differs. The layouts are the same on each 64-bit Linux architecture.
- `src/sys.rs` issues `io_uring_setup`, `io_uring_enter`, `mmap` and `munmap` on x86-64 and riscv64.
- `src/ring.rs` maps the submission and completion queues, stages entries, submits them and reads each completion once.

A submission carries a key, and its completion carries the key back. An entry linked to the next one starts the next only when it succeeds; the kernel cancels the next one when it fails.
