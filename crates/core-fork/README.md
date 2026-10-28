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

**What.** A small `no_std` crate with one trait and one implementation. `Fork` runs a job on every item of a slice, or runs two halves beside each other. `Serial` runs every job on the calling thread, in order.

**Why.** The kernel and the checker name no thread. The driver owns the threads, their number and their pool. A check states its independent jobs, and the driver decides where they run. The trait lives apart from every consumer. So a crate at any layer from the core upward forks without a dependency on the checker.

**How.** A consumer is generic over `F: Fork` and takes a `&F` from its caller. The driver hands it a fork over its one pool. A test hands it `Serial`. Every forked run equals the serial run, because the jobs are independent and the consumer reads their results in order. [`src/lib.rs`](src/lib.rs) states each method's obligations.

## References

- `vault:01a178aa-6b8e-7d60-a533-ec9379c0462a` — lineage: the futures design (§ futures-sax), whose reader waits for its writer. That wait sets the order that `Fork::join` states.

## Provided features

- `Fork::each(items, start, job)`: `job` runs once on every item. Each worker gets one state from `start`.
- `Fork::join(left, right)`: both halves run once. The pair holds their results in argument order. The left half begins before the join waits for the right one, so the right half may wait for the left one, and never the reverse.
- `Serial`: the items in slice order from one state, and the left half before the right.

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
