# gandr-workflow-sweep

The corpus sources a sweep test visits: a stated, hashed and stratified sample under every pull-request profile, the whole corpus under the `sweeps` profile, and the night's slice of it for the costliest sweeps under the `nightly` profile.

- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Dependencies](#dependencies)
- [License](#license)

## Synopsis

**What.** `gandr-workflow-sweep` is a test-support library. A sweep — a test that drives the whole corpus through one feature, such as typing and erasing every source or molding every token drop — asks it which corpus sources to visit. Under the `sweeps` nextest profile the answer is every source; under the `nightly` profile it is every source too, except for a rotating sweep, which visits the night's slice; under every other profile it is the sweep's sample.

**Why.** Every test is held to 30 s on every pull request and merge-queue entry, and no test leaves those lanes. A sweep over the whole corpus does not fit that bound, so it runs twice: over a bounded sample on every landing, and whole nightly. The nightly run is itself held to fifteen minutes summed over its jobs, twenty at the most, and the costliest sweeps do not fit it whole: each visits one slice of the corpus a night over the nights it states, every input within them, and the typing types one part of every source a night, every keystroke within its nights. The sample, the slice and the part are deterministic and stated, so a failure reproduces anywhere.

**How.** nextest names the running profile in `NEXTEST_PROFILE`. A sample ranks its candidates by the BLAKE3 digest of the sweep's name and the source's name — `strict/…` below `crates/surface-corpus/strict`, `fixture/…` below the top-level `corpus`, its `ledger` held out — keeps the first-ranked source of every class — `strict`, and each directory below `fixture`, the pending set among them — then takes the candidates the change adds or modifies under either root, then fills in rank order, stopping at its size. A change wider than the size is ranked by the digest with the commit `HEAD` names first, so each commit visits another part of it and the nightly profile the rest. The change is measured against the revision `GANDR_SWEEP_BASE` names, or where `HEAD` left `origin/main` when it is unset; a source whose change is layout alone — the formatter lays it and its base out to one text — is no change. The [crate docs](src/lib.rs) record the alternatives and the reversal.

## Provided features

- `Sweep::asked` reads the run's coverage, change and rotation; `Sweep::visit` returns the sources to visit, and `Sweep::visit_rotating` the night's slice of them over the sweep's `Nights` under the `nightly` profile.
- `Rotation` names the night a nightly run visits, whether a source is in a sweep's slice and which part of a text it covers; `GANDR_SWEEP_NIGHT` replays another night.
- `corpus::sources` walks the strict and fixture roots as the dispatcher's walk does, naming each source and its class.
- `Sample` names a sweep's sample and its size; `Sample::select` applies it.
- `SweepError` names the corpus entry or the `git` invocation behind every refusal.

## Expected features

`git` on the path when a run is sampled, in a checkout holding the base revision: CI sets `GANDR_SWEEP_BASE=HEAD^` over a two-commit checkout, as the obligations lane does.

## Examples

```sh
cargo nextest run -p gandr-surface-format                          # the sampled sweep
cargo nextest run --profile sweeps -p gandr-surface-format         # the whole corpus
GANDR_SWEEP_NIGHT=20744 cargo nextest run --profile nightly -p gandr-surface-parser  # the slice of night 20744
GANDR_SWEEP_BASE=HEAD~3 cargo nextest run -p gandr-surface-format  # the last three commits' sources lead the sample
cargo nextest run -p gandr-workflow-sweep
```

## Dependencies

`blake3` ranks the sources; it is already in the build graph for content identities, with default features off.

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
