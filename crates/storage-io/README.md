# gandr-storage-io

The IO layer of the storage tier gives each worker of the pool one `io_uring` on the kernel's own system calls.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** `gandr-storage-io` gives each worker one `Io`: an `io_uring` that the worker owns, behind a completion contract. A buffer moves into each submission and comes back with its completion, keyed by the submission's `Pending`. Where the kernel refuses a ring, the same interface runs as a blocking form on the worker's own thread. `Io::form` says which form runs.

**Why.** The store's fold waits on the sync of each segment that a batch writes, and the transport waits on its sends and receives. A ring removes those waits and the system call for each operation, where a wait stands. One ring for each worker takes no lock, so the layer adds no contention between workers.

**How.** The crate issues `io_uring_setup`, `io_uring_enter`, `io_uring_register`, `mmap` and `munmap` by the architecture's own instruction, with each argument in a register of its own type. It maps the queues, links a write to its `fdatasync`, and fixes buffers from the caller's allocator and files in the ring's tables. A registration stays within the process's limit of locked memory. A seed draws torn, lost, misdirected and corrupt IO under each form for the store's tests. The layer moves bytes only, and the store's plane checks each record's place and digest.

## Provided features

- `Io::open` takes the ring. On `EPERM`, `ENOSYS` or a ring without stable submissions, it takes the blocking form. `Io::blocking` takes the blocking form alone. `Io::form` gives the `Form` that runs.
- `Io::append` writes a `Buffer` at a `Segment`'s end. `Io::read_at` reads at a `Position` of a `Handle`. `Io::sync` syncs a segment's data. `Io::cancel` cancels a `Pending` submission. A `Chain` links an entry to the next one.
- `Io::submit` enters the staged entries. `Io::wait` gives each `Done` once, with its `Pending`, its bytes `Moved` or its `Errno`, and its buffer.
- `Io::register` fixes `Count` buffers of one length in the caller's allocator. It gives a `Registered` table with its `Pinning`. `Io::fix` puts a file in the ring's table of `FILES` slots.
- A full queue refuses a submission with a `Refused` and its `Reason`. The `Refused` gives the buffer back.
- `Io::with_faults` draws `Fault`s from a `Seed` at the `Odds` given. `Io::faults` lists the faults that it draws.
- On a target without a ring, the crate holds the module `absent` alone, which states the absence.

## Expected features

Linux on x86-64, aarch64 or riscv64. Another target holds no ring and no item but `absent`. A kernel that refuses `io_uring` runs the blocking form, as a container of the CI does.

A consumer gives each worker its own `Io` and never shares one between threads. A buffer lives in an allocator that the consumer names. A registration needs a limit of locked memory, `RLIMIT_MEMLOCK`, that holds the buffers, and runs the rest unregistered past it.

## Examples

The example links a write, its sync and a read of the same bytes. Then it reads each completion:

```rust,no_run
use gandr_storage_io::Buffer;
use gandr_storage_io::Chain;
use gandr_storage_io::Count;
use gandr_storage_io::Handle;
use gandr_storage_io::Io;
use gandr_storage_io::Position;
use gandr_storage_io::Segment;

fn main() -> std::io::Result<()> {
    let mut io = Io::open(Count::from(8_u32)).expect("a ring, or the blocking form");
    let handle = Handle::from(std::fs::File::options().read(true).write(true).create(true).open("segment")?);
    let mut segment = Segment::new(handle.clone(), Position::from(0_u64));
    let write = io.append(&mut segment, Buffer::from(vec![0xa5_u8; 4096]), Chain::Linked).expect("the append stages");
    let sync = io.sync(&segment, Chain::Linked).expect("the sync stages");
    let read = io.read_at(&handle, Position::from(0_u64), Buffer::from(vec![0_u8; 4096]), Chain::Alone).expect("the read stages");
    println!("staged {write:?}, {sync:?} and {read:?}");
    while let Some(done) = io.wait().expect("the wait answers") {
        println!("{:?} moved {:?}", done.pending, done.outcome);
    }
    Ok(())
}
```

Time a packed batch and its sync under each form, then run the crate's tests, from the repository root:

```sh
cargo bench -p gandr-storage-io --bench batch -- --bench --directory <path> --shards 1,16,64 --workers 1,4 --rounds 100
mise exec -- cargo test -p gandr-storage-io
```

## Where the detail lives

The crate's lead in [`src/lib.rs`](src/lib.rs) names each module and what it holds. The modules hold the generated UAPI, the system calls and their typed registers, and the queues. They hold the completion contract, the blocking form, the buffers and the simulator of faults too.

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
