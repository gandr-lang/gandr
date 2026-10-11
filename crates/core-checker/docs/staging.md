# Guarded staging families

- [Production](#production)
- [Measurements](#measurements)
- [Guarded admission observer](#guarded-admission-observer)

## Production

`template::harvest` groups equations by producer identity, rule and shallow source shape. Joint anti-unification generalizes both sides together, so repeated points share one source-selected arm. A target-only point refuses production. The sole inferred relation is the predecessor of a positive outer-stage numeral; zero, inner-stage numerals and other offsets acquire no predecessor relation.

`template::analyze` generalizes a family's first and last members before the rest. A join point outside the two members' peak stays outside the family's: adding members only splits agreement, so the family's join disagrees at or above that point, by a column that is neither a peak point nor one below a peak point. The argument is the private `probe` function's documentation, and its specification checks the implication against the full generalization. Such a family is refused from the two members, and its cost counts members only, since no size was measured. A family the two leave open drops their generalization, keeps their import and imports its other members into the same graph; a point outside the whole family's peak still refuses it there, with every size. Every other verdict, cost and price is the full generalization's. Analysis first checks that every member's sides are arena terms, so a member the probe skips fails as its import would.

The first and last members are the extremes of producer order. On the observer's harvested programs they decide every family refused for a point outside the peak, 9 in `pow:0..8` and 7 in `double:0..8`; the first two members decide 7 and 2 of them. A probe in its own graph would import its two members again for every family it leaves open. Reusing the import places the last member's new content before the middle members', so a continuing family's node coordinates follow that order. Verdicts, sizes and prices depend on content, not coordinates. Serialized images number nodes and arms in coordinate order, so a continuing family's image bytes can differ by a few digits from an import in member order; five of the observer's families differ by 1 to 24 bytes. Revisit the member choice if producer order stops placing the most different members at the ends; the implication holds for any pair.

A family the probe leaves open generalizes its distinct members. Members with equal source and target terms generalize alike, so analysis imports each distinct pair of sides once, at its first occurrence, runs the generalizer over the distinct members, and expands every arm back to one entry per member. Every member keeps its guard row, and `F` still charges every member. A repeat adds no node, so coordinates, images, verdicts, sizes and prices equal those of a generalization over every member. Over exponents zero through 32 of the second iterator, the two largest paying families repeat 32 and 34 distinct pairs across 1,056 and 1,120 members, and their analysis takes 0.29 to 0.41 of its former time. The alternative was splitting a family by member across a fork. Members nest one another's content, so every chunk re-imports most of the family, and joining the chunks' graphs costs about what the serial import does; the split lost to the serial analysis at every width measured, over every member and over distinct members alike. Revisit a split when families stop nesting their members' content or the distinct analysis stops being dominated by import.

`template::analyze` constructs an untrusted candidate. `Candidate::produce` applies the selected strict price before replaying inheritance obligations. Each distinct region/entry/body triple is checked once per run, with every other point rigid. Classifier content belongs to the cache key. A ground family owes one check. A failed or unfinished check never becomes a positive cached verdict.

| Charge | Definition |
| ------ | ---------- |
| `F` | Every member's unfolded source and target nodes, plus one decision per member |
| `s` | Generalized sides, one shared decision, every distinct arm's nodes and one guard per arm |
| `T` | Distinct inheritance triples, or one for a ground family |
| `c` | Per-check kernel-fuel allowance, conservatively set to `s` |

`PriceGate::Unmemoized` requires `s < floor(F / s)`. `PriceGate::Memoized` requires representable `s + T*c < F` and enforces `c` on each cold check. Equality, overflow, a target-only point, failed inheritance or an exhausted check allowance leave the family plain. Caller-budget exhaustion remains a typed error. No warm-cache discount changes the cold price. These are abstract node/fuel charges; discovery, materialization and subsequent member admission are outside that bound.

`Template::admit` selects guards from the source, materializes one equation and replays it through the existing kernel rules. A poisoned cache cannot bypass replay. `template::readmit` also compares projected targets and replays the complete original certificate with its endpoint typing, connectivity and congruence premises intact. The template retains no member list; the complete-readmission API still receives the enclosing plain certificate. There is no kernel-side admission judgment for guarded families here.

The alternatives are independent member replay, which avoids discovery and projection costs; exact cross-member deduplication, which shares identical rather than near-identical equations; and a kernel-side judgment of the same equations, held for its trusted-surface cost. The producer retains ordinary replay as its authority. The selected guard refuses every family whose charge reaches its plain allowance. Revisit the price model only with a justified replacement bound; revisit kernel-side admission only when its additional trusted surface is justified. Neither a byte saving nor a warm cache licenses relaxing a refusal.

## Measurements

The `staging_templates` example measures strict powers at exponents zero through eight, a second iterator with step `p -> <~x * ~p * ~x>` at inputs two and three, and separately labeled repeated cancellation controls. Each gate gets a fresh cache. The following pooled families pay under the memoized gate; the unmemoized gate admits only the double-product zero family among these rows.

| Pooled family | Members | `F` | `s + T*c` | Checks / hits | Template + substitutions B | Plain B |
| ------------- | ------: | --: | --------: | ------------: | -------------------------: | ------: |
| Power zero | 9 | 126 | 28 | 1 / 0 | 652 | 5,472 |
| Power successor | 36 | 1,116 | 432 | 8 / 28 | 1,378 | 27,000 |
| Double-product zero | 18 | 306 | 34 | 1 / 0 | 713 | 11,718 |
| Double-product successor | 72 | 2,880 | 513 | 8 / 64 | 1,531 | 57,240 |
| Double-product cancellation | 144 | 2,736 | 2,123 | 10 / 134 | 1,586 | 47,786 |

The power cancellation family remains too expensive under `c = s`. The double-product beta family passes arithmetic pricing but exceeds its check allowance. Other families retain target-only or inheritance refusals. The fixed source-shape partition is a measured discovery strategy, not an exhaustive search for paying partitions.

Compact JSON includes classifier tables, constructor payloads and edges, roots, decisions and all guarded arms; each member contributes a guard row, including an empty row for a ground member. Plain bytes sum independently serialized reachable equation DAGs. This is a format-specific comparison, not a bound against optimal cross-member sharing. A candidate production refuses has descriptive image sizes, not admitted compression. A family analysis refuses for a point outside its peak has no candidate, so its candidate columns print a dash.

Full readmission repeats ordinary replay after projection. In one sequential release observation, 25 pooled power readmissions take 4.64 ms plain and 13.88 ms guarded; double-product takes 10.46 ms plain and 46.81 ms guarded. The byte savings are not a replay speedup. Cloning and serialization lie outside the timed intervals; production has its own interval. Heap high-water observations count scoped ownership, not process RSS. Plain residency includes the input arena and certificates; template-only residency owns a template and one regenerated instance; admission residency borrows its input arena. Those scopes are not interchangeable.

The byte observer uses default-off Serde and dev-only `serde_json`. Debug text and node counts do not measure encoded bytes; a binary codec answers a different size question. Revisit JSON when an interchange specification selects a format. Dev-only `allocation-counter 0.8.1` uses a synchronous thread-local System wrapper without runtime dependencies. DHAT adds backtrace and serialization machinery; `stats_alloc` lacks the required high-water observation. Revisit allocation counting for multithreaded workloads, an applicable advisory or maintenance loss. Measurement scopes are non-nested and fallible rather than unwinding.

Reproduce the family rows, complete-replay differential, allocation observations and power residual values:

```sh
cargo run -p gandr-core-checker --example staging_templates --release
cargo nextest run -p gandr-core-checker -p gandr-theory-deep-inference
RUSTFLAGS="--cfg anodized_panic" CARGO_TARGET_DIR=target/enforcing cargo nextest run -p gandr-core-checker -p gandr-theory-deep-inference
```

The example emits 540 family rows across 26 workloads and both prices. Its witnesses cover strict prices, source correlation, refusal variants, cold/warm caches, poisoned-cache admission, independent image reconstruction and ownership-scope release. Finite witnesses establish neither universal soundness nor a wall-clock bound.

## Guarded admission observer

`template::admission` exposes a paying family to the kernel's [guarded admission](../../kernel-core/docs/admission.md) as a `Proposal` plus one guard row per member. The `staging_templates` example's admission module is measurement scaffolding, not a supported scheduler. It times the kernel's judgments against local plain replay, and it is the only place a thread pool, a queue or a pool width appears; the kernel and this library spawn no thread.

- Without environment variables it reports `COMPRESSED` rows: schema, binding, largest member and admission at 1, 2, 4 and 8 scoped threads.
- `GANDR_HANDOFF=all` adds the standing-pool matrix. It covers `crossbeam-channel` MPMC, `crossbeam-deque` stealing and per-worker `rtrb`/`ringbuf` rings, with busy or parking waits, item or batch publication, drains of 1 or 32, and four task grains at 1, 2, 4 and 8 workers.
- `GANDR_SWEEP=1` fixes the transport to `rtrb` busy polling, batch publication, drain 32 and member grain. It sweeps 1–12 workers, with the dispatcher either spinning on the result rings or executing one shard itself, over lookup rows and empty jobs. A second pass of every cell counts allocations on every executing thread and sums them.

Every pooled verdict and counter is checked against an independently executed serial receipt. Workers borrow one immutable schema and one immutable binding per family and own their row buffers. The queue crates are dev-dependencies of this crate only; the observer's module documentation records why each was chosen and what would replace it. An allocator stays an environment variable of the measured process, such as `MallocNanoZone=0` on Darwin, never a library default. Busy polling reserves worker execution capacity and sets no CPU affinity. Thread-local allocation counting suffices for the pool because each thread reports its own count with its result.
