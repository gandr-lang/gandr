# gandr-surface-evaluate

The run stage of gandr: each run of a checked module's program, as native code that the emitter patches or on the portable executor of the emitter. The crate implements the engine that the dispatcher's composition, walk, type table and run verb take.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [References](#references)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** `Evaluator` implements `gandr_surface_dispatcher::Engine`: the runs of a settled module, the schedule of its concurrent runs, a run to a value, a call, an entry and a host. A `Machine` borrows the parts of a dispatcher `Program` that a run reads, and runs a declaration on the L machine. `Runs` gives a caller each run of a `Program` as a method. `Engine` chooses native code or the executor for one run.

**Why.** The dispatcher holds a program's data and the composition that builds it. The runs link the emitter, the network runtime and the exact reals. An edit of a run builds this crate and its consumers again, and the dispatcher stays as it is. The engine is a type parameter, so a call into the run stage costs no dynamic dispatch.

**How.** Each generic function of the dispatcher that runs a declaration takes `E: Engine`, and a caller names `Evaluator` once at the call. The dispatcher's `fixture` feature gives the tests of this crate the shared fixtures of the composition.

## Provided features

- `Evaluator`: the dispatcher's engine.
- `Machine` and `Runs`: a program's runs, through a borrow of its parts or by method.
- `ScheduledRuns`: the concurrent runs of a module on the driver's pool.
- `Engine`: native code or the executor for one run.
- `RealsAdapter`: the adapter of `std.reals.Eff` on `theory-exact-reals`.

## Expected features

- **A settled module.** The dispatcher composes a source and builds its `Program`. This crate runs the program and composes nothing.
- **A pool.** `ScheduledRuns` starts the writers of a concurrent run on the dispatcher's `Pool`.

## Examples

```rust
use core::ops::ControlFlow;

use gandr_surface_dispatcher::Pool;
use gandr_surface_dispatcher::Step;
use gandr_surface_dispatcher::Walk;
use gandr_surface_dispatcher::Width;
use gandr_surface_evaluate::Evaluator;

fn walk(paths: Vec<std::path::PathBuf>) {
    let _report = Walk::new(paths).visit::<Evaluator, _, _>(&Pool::new(Width::SERIAL), |step| {
        if let Step::Fault { path, fault } = step {
            eprintln!("{}: {fault}", path.display());
        }
        ControlFlow::<core::convert::Infallible>::Continue(())
    });
}
```

Run the tests:

```sh
cargo nextest run -p gandr-surface-evaluate
```

## Where the detail lives

Mechanism, decisions with their alternatives and reversals, and witnesses live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| The split from the dispatcher, the engine | [`src/lib.rs`](src/lib.rs) |
| The run stage, native universe-path boundaries | [`evaluate`](src/evaluate.rs) |
| A run's entry | [`evaluate::entry`](src/evaluate/entry.rs) |
| The adapter of exact reals | [`evaluate::reals`](src/evaluate/reals.rs) |

## References

- `vault:01a178aa-6b8e-7d60-a533-ec9379c0462a` — background: the futures try-first — the tree sum whose two cuts run on two threads.
- `vault:01a17f02-42f0-7920-bede-5615d3bade8c` — background: the compilation ruling — a run is a local artifact.
- `vault:01a178ab-17e5-7352-bc0b-3caa7f1e476c` — lineage: the storage programme's worlds.
- `vault:01a178aa-a419-7ab1-82e7-40a4f95938c6` — anchor: the first adapter of exact reals, a handle to a plan the host holds.
- `vault:01a1aa2d-a69c-7030-91e0-337d68d88151` — anchor: § presented-spaces-crates gives the adapter of stage C to the run stage; a draw is a probability operation.
- `vault:01a178aa-a7bd-7d03-a728-feae5af9d1a8` — anchor: a draw's native handler.
- `Taylor-2010-lambda_calculus_real_analysis` — exemplar: Taylor, _JLA_ 2:5, 2010, `doi:10.4115/jla.2010.2.5` — the laws a cut owes.
- `Escardó-2004-synthetic_topology_data_types_classical_spaces` — exemplar: Escardó, _ENTCS_ 87, 2004, `doi:10.1016/j.entcs.2004.09.017` — a comparison as an open.

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
