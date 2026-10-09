# gandr-surface-dispatcher

Routes an understood `gandr` driver invocation to the outcome the driver renders.

<!-- toc -->

- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Optional tracing](#optional-tracing)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** `dispatch` maps an `Invocation` to an `Outcome`. The vocabulary has one invocation, `Invocation::Status`, the bare `gandr` invocation, which routes to `Outcome::Status` carrying a `StatusReport`. The report's text states that toolchain management is not implemented and links the repository.

**Why.** The driver owns the argument surface and the process boundary; what an understood invocation does belongs to a library, so routing can be enumerated without a process.

**How.** `dispatch` is a total match over the closed `Invocation` enum. It performs no I/O of its own. With tracing enabled it reports a span to the caller's subscriber; rendering the returned `Outcome` remains the driver's responsibility.

## Provided features

- `Invocation`: the invocations the driver understands.
- `Outcome` and `StatusReport`: what an invocation routes to.
- `dispatch`: total routing from one to the other.

## Expected features

- **A renderer.** The caller renders each `Outcome`. `StatusReport`'s `Display` writes one sentence and no line terminator, so the caller owns the line it sits on.

## Examples

```rust
use gandr_surface_dispatcher::Invocation;
use gandr_surface_dispatcher::Outcome;
use gandr_surface_dispatcher::dispatch;

fn render() {
    let Outcome::Status(report) = dispatch(Invocation::Status);
    println!("gandr — {report}");
}
```

Run the tests:

```sh
cargo nextest run -p gandr-surface-dispatcher
```

## Optional tracing

Enable `tracing` for an INFO span around `dispatch`. It records no argument or outcome payload and installs no subscriber. The [driver](../surface-driver/README.md#optional-tracing) owns output; the [evaluator](../core-nbe/README.md#optional-tracing) uses the same diagnostics interface independently. The dependency is optional and off by default, so ordinary routing has no instrumentation.

The choice is caller-owned structured diagnostics. Printing from this library would seize an output destination; installing a global subscriber would seize process policy. Revisit only when a library-owned diagnostic destination becomes an explicit API requirement, rather than an incidental side effect of dispatch.

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
