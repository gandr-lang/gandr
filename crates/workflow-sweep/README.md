# gandr-workflow-sweep

The corpus sources a sweep test visits: a stated, hashed and stratified sample under every pull-request profile, the whole corpus under the nightly `sweeps` profile.

- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Dependencies](#dependencies)
- [License](#license)

## Synopsis

**What.** `gandr-workflow-sweep` is a test-support library. A sweep — a test that drives the whole corpus through one feature, such as typing and erasing every source or molding every token drop — asks it which corpus sources to visit. Under the `sweeps` nextest profile the answer is every source; under every other profile it is the sweep's sample.

**Why.** Every test is held to 30 s on every pull request and merge-queue entry, plain and with specifications enforced, and no test leaves those lanes. A sweep over the whole corpus does not fit that bound, so it runs twice: over a bounded sample on every landing, and whole nightly. The sample is deterministic and stated in the sweep's documentation, so a failure reproduces anywhere.

**How.** nextest names the running profile in `NEXTEST_PROFILE`. A sample ranks its candidates by the BLAKE3 digest of the sweep's name and the source's path below `crates/surface-corpus`, keeps the first-ranked source of every class — `strict`, and each directory below `fixture`, the pending set among them — fills to its size in rank order, and adds every candidate the change adds or modifies. The change is measured against the revision `GANDR_SWEEP_BASE` names, or where `HEAD` left `origin/main` when it is unset; a source whose change is layout alone — the formatter lays it and its base out to one text — is no change. The [crate docs](src/lib.rs) record the alternatives and the reversal.

## Provided features

- `Sweep::asked` reads the run's coverage and change; `Sweep::visit` returns the sources to visit.
- `corpus::sources` walks the strict and fixture roots as the dispatcher's walk does, naming each source and its class.
- `Sample` names a sweep's sample and its size; `Sample::select` applies it.
- `SweepError` names the corpus entry or the `git` invocation behind every refusal.

## Expected features

`git` on the path when a run is sampled, in a checkout holding the base revision: CI sets `GANDR_SWEEP_BASE=HEAD^` over a two-commit checkout, as the obligations lane does.

## Examples

```sh
cargo nextest run -p gandr-surface-format                          # the sampled sweep
cargo nextest run --profile sweeps -p gandr-surface-format         # the whole corpus
GANDR_SWEEP_BASE=HEAD~3 cargo nextest run -p gandr-surface-format  # the last three commits' sources join the sample
cargo nextest run -p gandr-workflow-sweep
```

## Dependencies

`blake3` ranks the sources; it is already in the build graph for content identities, with default features off.

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
