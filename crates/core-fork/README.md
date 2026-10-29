# gandr-core-fork

The fork that a check hands its independent jobs to, and its serial reference.

<!-- toc -->

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** A small `no_std` crate: the `Fork` trait, the two traits of its scope, and the serial reference. `Fork` runs a job on every item of a slice, runs two halves beside each other, or opens a scope whose jobs start before their waits. `Serial` runs every job on the calling thread, in order, and each spawned job at its wait.

**Why.** The kernel and the checker name no thread. The driver owns the threads, their number and their pool. A check states its independent jobs, and the driver decides where they run. The trait lives apart from every consumer. So a crate at any layer from the core upward forks without a dependency on the checker.

**How.** A consumer is generic over `F: Fork` and takes a `&F` from its caller. The driver hands it a fork over its one pool. A test hands it `Serial`. Every forked run equals the serial run, because the jobs are independent and the consumer reads their results in order. [`src/lib.rs`](src/lib.rs) states each method's obligations.

## References

- `vault:01a178aa-6b8e-7d60-a533-ec9379c0462a` — lineage: the futures design (§ futures-sax), whose reader waits for its writer. That wait sets the order that `Fork::join` states, and it is the wait that `Spawn::wait` performs.

## Provided features

- `Fork::each(items, start, job)`: `job` runs once on every item. Each worker gets one state from `start`.
- `Fork::join(left, right)`: both halves run once. The pair holds their results in argument order. The left half begins before the join waits for the right one, so the right half may wait for the left one, and never the reverse.
- `Fork::scope(body)`: `body` runs in a scope and gets the scope's spawner. When the call returns, each job that the scope spawned has ended, or its handle was dropped before it started and it never runs. By default the scope is serial.
- `Spawn::spawn(job)` and `Spawn::wait(handle)`: a spawn starts a job and answers its handle, and a wait answers the job's result. A wait runs a job that has not started on the waiting thread. While a started job runs elsewhere, the waiting worker runs other pending jobs. `Unwound` reports a job that panicked on another worker.
- `Scoped`: the shape of a scope's body and of each spawned job. Its `run` is generic over the spawner, so a job spawns its own jobs through the spawner that runs it.
- `Serial`: the items in slice order from one state, the left half before the right, and each spawned job at its wait. `Deferred` holds the job until then.

## Expected features

- **A driver's pool.** A consumer that wants more than one thread takes a `Fork` from the driver. This crate starts no thread.
- **Independent jobs.** A job reads shared data through `Sync` borrows and writes only its own item. The results are then the same at every width. A join's right half may wait for its left half alone.

## Examples

```rust
use gandr_core_fork::Fork;
use gandr_core_fork::Serial;

fn lengths<F: Fork>(fork: &F, words: &mut [(&str, usize)])
{
    fork.each(words, || (), |_state, (word, length)| *length = word.len());
}

let mut words = [("fork", 0), ("join", 0)];
lengths(&Serial, &mut words);
assert_eq!(words, [("fork", 4), ("join", 4)]);
```

The tests run as below, the second line the enforcing twin that checks every specification:

```sh
cargo nextest run -p gandr-core-fork
RUSTFLAGS="--cfg anodized_panic" cargo nextest run -p gandr-core-fork
```

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
