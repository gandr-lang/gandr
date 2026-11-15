# gandr-storage-io

The IO layer of the storage tier. Each worker of the pool owns one io_uring. The crate issues the ring's system calls by the architecture's own instruction, with no C library.

- `src/uapi.rs` holds the io_uring layouts and the table of system-call numbers by architecture: x86-64, riscv64, aarch64, loongarch64, powerpc64 and s390x. `mise run uapi:generate` writes it from the pinned kernel, and the gate's `check:uapi` refuses a file that differs. The layouts are the same on each 64-bit Linux architecture.
- `src/sys.rs` issues `io_uring_setup`, `io_uring_enter`, `io_uring_register`, `mmap` and `munmap` on x86-64, aarch64 and riscv64. Each argument goes in a register of its own type, so a pointer keeps its provenance (`src/sys/registers.rs`, `src/sys/arch/`).
- `src/ring.rs` maps the submission and completion queues, stages entries, submits them and reads each completion once. It registers the ring's tables of fixed buffers and fixed files.
- `src/io.rs` is the completion contract. A buffer moves into each submission and comes back with its completion, keyed by the submission. `append` owns a segment's end. A full queue parks the caller until a submission completes.
- `src/blocking.rs` is the blocking form. The kernel can refuse the ring with `EPERM` or `ENOSYS`, or give a ring without stable submissions. Then the worker's own thread runs positioned calls behind the same interface.
- `src/buffer.rs` holds the buffer in the allocator that the caller names, such as a worker's region. `Io::register` fixes buffers within the process's limit of locked memory, which the first registration reads, and says how many it fixes. The rest run unregistered. An allocator that refuses the bytes refuses the registration by the budget.
- `src/faults.rs` is the simulator of faults: torn, lost, misdirected and corrupt IO, drawn from a seed, the same under each form. An `Io` without it draws nothing.

A submission carries a key, and its completion carries the key back. An entry linked to the next one starts the next only when it succeeds. The kernel cancels the next one when it fails. A sync is `fdatasync`, as the store's segment syncs.

The crate moves bytes only. The store's record plane checks a record's place and digest.

`cargo bench -p gandr-storage-io --bench batch -- --bench --directory <path>` times the packed write of a whole batch and its sync through each form.
