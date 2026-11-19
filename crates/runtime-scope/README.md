# gandr-runtime-scope

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

**What.** `gandr-runtime-scope` is a scoped runtime on the kernel's ring. One thread drives the futures of one scope, and each future requests the kernel's operations through the scope. The crate is the owner's own text. The tree mends it in place to the tree's wall.

**Why.** An operation of the ring writes memory after its request returns. A runtime that lets a task drop its operation while the kernel holds it makes the kernel write freed memory. The scope lends each operation memory for the scope's life, and the scope's end cancels and drains each operation that the kernel still holds. So the kernel writes only memory that the scope holds.

**How.** `Runtime` owns a ring from `gandr-runtime-uring` and a bounded table of slots. `Runtime::run` gives the scope's future a `Scope`, and polls the future after each wait for the ring. `Scope::request` prepares an entry of the ring in place and takes a slot of the table for it. The entry's user data names the slot, so each completion goes to its slot. When the future returns, the run cancels each operation in a slot and waits for every completion. A later run uses the same ring and table.

## Provided features

- `Runtime::with_depth` sets up a ring of the depth that the caller gives, and a table of as many slots. `Runtime::run` runs a scope's future, ends the scope, and gives the future's output. A run that fails spends the runtime, and a later run gives `RuntimeError::Spent`.
- `Scope::request` prepares an entry with a closure and gives the completion of its operation.
- `io::socket::Socket` creates, binds, listens on, accepts on and receives from a socket through the ring. A bind lends its address and an accept lends its peer's storage. A receive lends an `io::buf::Buf`, and the completion gives back the bytes received.
- `RuntimeError` names each refusal: the kernel's error number, a full table, a completion polled twice, a count past the buffer, a completion that names no slot, and a spent runtime.

## Expected features

The crate runs on Linux alone. On another system it compiles empty. A kernel that refuses `io_uring` refuses `Runtime::with_depth` with its error number.

The table has one slot for each entry of the ring. A request that finds every slot taken waits for a completion. When the kernel holds no operation of the table, the request gives `RuntimeError::Full`.

The scope's thread is the one thread of the runtime. After `Runtime::with_depth` makes the ring and the table, a request allocates nothing, and a run allocates nothing.

## Examples

The example runs a scope that creates a socket and drops it:

```rust,no_run
use gandr_runtime_scope::Depth;
use gandr_runtime_scope::Runtime;
use gandr_runtime_scope::RuntimeError;
use gandr_runtime_scope::io::socket::Socket;
use socket2::{Domain, Type};

fn main() -> Result<(), RuntimeError> {
    Runtime::with_depth(Depth::from(64_u16))?.run(async |scope| -> Result<(), RuntimeError> {
        let socket = Socket::new(scope, Domain::UNIX, Type::STREAM, None).await?;
        drop(socket);
        Ok(())
    })?
}
```

Run the crate's tests from the repository root:

```sh
mise exec -- cargo nextest run -p gandr-runtime-scope
```

## Where the detail lives

The crate's lead in [`src/lib.rs`](src/lib.rs) names the parts. [`src/runtime.rs`](src/runtime.rs) holds the run loop and the scope's end. [`src/scope.rs`](src/scope.rs) holds the request. [`src/submission.rs`](src/submission.rs) holds the table of slots, and [`src/completion.rs`](src/completion.rs) the completion. Under [`src/io/socket/`](src/io/socket) each operation of a socket has one module.

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
