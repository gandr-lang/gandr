# Guarded staging families

- [Production](#production)
- [Drafts](#drafts)
- [Measurements](#measurements)
- [Guarded admission observer](#guarded-admission-observer)

## Production

`template::harvest` groups equations by producer identity, rule and shallow source shape. Joint anti-unification generalizes both sides together, so repeated points share one source-selected arm. A target-only point refuses production. The sole inferred relation is the predecessor of a positive outer-stage numeral; zero, inner-stage numerals and other offsets acquire no predecessor relation.

`template::analyze` generalizes a family's first and last members before the rest. A join point outside the two members' peak stays outside the family's: adding members only splits agreement, so the family's join disagrees at or above that point, by a column that is neither a peak point nor one below a peak point. The argument is the private `probe` function's documentation, and its specification checks the implication against the full generalization. Such a family is refused from the two members, and its cost counts members only, since no size was measured. A family the two leave open drops their generalization, keeps their import and imports its other members into the same graph; a point outside the whole family's peak still refuses it there, with every size. Every other verdict, cost and price is the full generalization's. Analysis first checks that every member's sides are arena terms, so a member the probe skips fails as its import would.

The first and last members are the extremes of producer order. On the observer's harvested programs they decide every family refused for a point outside the peak, 9 in `pow:0..8` and 7 in `double:0..8`; the first two members decide 7 and 2 of them. A probe in its own graph would import its two members again for every family it leaves open. Reusing the import places the last member's new content before the middle members', so a continuing family's node coordinates follow that order. Verdicts, sizes and prices depend on content, not coordinates. Serialized images number nodes and arms in coordinate order, so a continuing family's image bytes can differ by a few digits from an import in member order; five of the observer's families differ by 1 to 24 bytes. Revisit the member choice if producer order stops placing the most different members at the ends; the implication holds for any pair.

A family the probe leaves open generalizes its distinct members. Members with equal source and target terms generalize alike, so analysis imports each distinct pair of sides once, at its first occurrence, runs the generalizer over the distinct members, and expands every arm back to one entry per member. Every member keeps its guard row, and `F` still charges every member. A repeat adds no node, so coordinates, images, verdicts, sizes and prices equal those of a generalization over every member. Over exponents zero through 32 of the second iterator, the two largest paying families repeat 32 and 34 distinct pairs across 1,056 and 1,120 members, and their analysis takes 0.29 to 0.41 of its former time. The alternative was splitting a family by member across a fork. Members nest one another's content, so every chunk re-imports most of the family, and joining the chunks' graphs costs about what the serial import does; the split lost to the serial analysis at every width measured, over every member and over distinct members alike. Revisit a split when families stop nesting their members' content or the distinct analysis stops being dominated by import.

`template::analyze` constructs an untrusted candidate. `Candidate::produce` applies the selected strict price and schema allowance before replaying producer inheritance obligations. Each distinct region/entry/body triple is checked once per cache, with every other point rigid. The region is the rule and the generalized sides' content, never the producer's identity, so a cache carried across programs reuses every verdict an earlier program recorded; a cached verdict licenses nothing, since admission replays. Classifier content belongs to the cache key. A ground family owes one check. A failed or unfinished check never becomes a positive cached verdict.

| Charge | Definition |
| ------ | ---------- |
| `F` | Every member's unfolded source and target nodes, plus one decision per member |
| `s` | Generalized sides, one shared decision, every distinct arm's nodes and one guard per arm |
| `T` | Distinct inheritance triples, or one for a ground family |
| `c` | Per-check kernel-fuel allowance, conservatively set to `s` |

`PriceGate::Unmemoized` requires `s < floor(F / s)`. `PriceGate::Memoized` requires representable `s + T*c < F` and enforces `c` on each cold check. Equality, overflow, a target-only point, failed inheritance or an exhausted check allowance leave the family plain. Caller-budget exhaustion remains a typed error. No warm-cache discount changes the cold price. These are abstract node/fuel charges; discovery, materialization and subsequent member admission are outside that bound.

Before any inheritance-cache lookup, the producer emits its canonical proposal and probes `Schema::check` under the kernel's full proposal-byte allowance. `SchemaWorkBound` becomes `Production::SchemaWorkBound`, without spending the caller's producer-replay budget. The probe is independently capped and outside the prices above. Other kernel refusals remain consumer judgments; the producer retains no admission authority.

`Template::admit` selects guards from the source, materializes one equation and replays it through the existing kernel rules. A poisoned cache cannot bypass replay. `template::readmit` also compares projected targets and replays the complete original certificate with its endpoint typing, connectivity and congruence premises intact. The template retains no member list; the complete-readmission API still receives the enclosing plain certificate.

The alternatives are independent member replay, which avoids discovery and projection costs, and exact cross-member deduplication, which shares identical rather than near-identical equations. For the schema allowance, a second producer-side accounting formula would drift as the checker changes, so the producer uses the bounded kernel check itself. The consumer still checks its untrusted proposal independently. Revisit that probe if its measured cost outweighs the inheritance work it avoids; neither a byte saving nor a warm cache licenses relaxing either allowance.

## Drafts

`template::Memo` holds each harvest key's last emitted template, and `Memo::admit_family` drafts a family from it before the producer runs. The key is the rule and the shallow source shape; the program is not part of it, so the caller carries one memo, like one inheritance cache, from program to program. The result is the kernel's schema, the proposal's origin, what the drafter did, and the time drafting, production and the kernel each spent.

**The walk imports nothing.** Each member's source is compared with the template's peak in the member's own arena. A rigid constructor must agree, payloads and classifiers included; a point binds the member's subterm. The arm each point body selects is remembered per draft, so a body many members share is compared with the template's arms once rather than once per member. A new body tries the arms from the guard after the last one selected at its point, so members that arrive in the order the template numbered its arms compare one arm each. The verdict on each point-free pattern subtree against an arena term is remembered the same way, so a skeleton subterm every member shares, such as the program under an iterator, is compared once per draft. A body no arm holds becomes a new arm and is imported once. A member that disagrees with the skeleton rebases it: the innermost binder enclosing the first disagreement, or the disagreement itself outside any binder, is replaced at every occurrence on both sides by the member's own subterm, and the walk starts again. At most four replacements are made, and none that would remove a point. The memo holds a produced template compacted to the nodes its sides and arms reach. An admitted draft that imports nothing and leaves every node reachable keeps the held graph and renumbers its arms in place; one that leaves a node unreachable, by dropping an arm or by a rebase, is compacted again.

**A drafted schema is a fresh run's.** Arms no member selects are dropped and the rest are numbered by first selection in member order, which is how the producer numbers its own. The proposal is emitted canonically: nodes and classifiers in post-order from the two sides and the arms, each child and classifier component before its parent, unreachable content dropped. So a draft whose generalization is the producer's emits the producer's proposal exactly. The draft is offered only when its generalization is the producer's. A fresh run keeps a point exactly where member bodies disagree at the head, gives two positions one point exactly where their columns agree on every member, and reads a target column as a source point before reading it as one below a point. A point whose arms share one head, two points with equal columns, or a predecessor whose numeral is another point's body on every member withdraws the draft. The producer's price is then applied to the drafted `s` and `F`, computed from each point's occurrences in the sides without instantiating a member.

**The kernel is the only judge.** A drafted schema and every member's row go through `Schema::check`, `Schema::bind` and `Substitution::admit` as a produced one does. Under the memoized price, an admitted draft still falls back when one of the kernel's inheritance replays spent more than `c = s`, the allowance the producer would have enforced ([`Schema::largest_replay`](../../kernel-core/docs/admission.md#work-and-parallelism-obligations)). A draft the kernel refuses, a member the walk misses, or a withdrawn draft sends the family to the producer, and the memo then holds what the producer emits; a family the producer leaves plain vacates the key. When the producer or consumer reports `SchemaWorkBound`, the template held from before drafts exactly the members it still matches, without widening or rebase, and the kernel admits that subfamily as `FamilyAdmission::Partial`; the remaining members replay plainly, and the smaller template stays held.

**The controller weighs time.** Per key it keeps the producer's last time `P`, the last accepted and refused drafts' times `D_a` and `D_r`, and an acceptance average with weight 0.08 on each new family. The expected saving per drafted family is `a(P - D_a) - (1 - a)D_r`, positive above `a* = D_r / (P - D_a + D_r)`; a key drafts while its acceptance exceeds that, or while any of its times is unmeasured, and never while `D_a >= P`. Across the memo the same break-even is computed from averaged shares `D_a / P` and `D_r / P`, and below it the memo stops drafting. A family declined six times in a row, by its key or by the memo, drafts on the seventh, a probe duty of one in seven, so no estimate freezes. A widening that adds `f` arms is withdrawn when `f c >= P` for the memo's averaged import cost per arm `c`. Times come from a caller-supplied `Clock`; a clock that never advances makes every draft free and drafts every family that has a template.

The [draft baseline](https://github.com/gandr-lang/gandr/blob/ef17bb2bfc7d68f257f6dbf555f5839a7df609cc/crates/core-checker/docs/staging.md#drafts) records measurements before the schema-allowance probe. Production timing now includes that bounded probe; the controller learns the current path's cost rather than using fixed benchmark rates. The stopped-clock edit traces still compare each admitted draft's canonical proposal with a fresh run's, byte for byte.

The alternatives were these:

- _Import the members into a clone of the template's graph and generalize._ Importing is the producer's largest cost, so that draft costs more than the producer it replaces. Reversal: an import cheaper than the walk.
- _Exact drafts only._ They miss every family that gains an arm, which appending exponents or inputs always does. Reversal: none while arms grow.
- _Weigh the cap before the walk, as `D_exact + f c < P`._ The walk binds new bodies as it meets them, so `f` is known only once the walk is spent, and only the import remains to weigh. Reversal: a walk that counts new bodies before it binds them.
- _A node-count cost model instead of time._ It is deterministic but does not track what drafting and production cost on a host. Reversal: a count that predicts both times.
- _Hold the memo in the incremental session._ No session drives staging yet. Reversal: when one does, it holds the memo as it holds the cache.

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
