# Guarded admission

The one-subject page for the `admission` module of `gandr-kernel-core`. It covers the judgments that admit every member of a guarded family of staging equations without replaying the rule per member, their soundness boundary, their work bounds and the shape of a row. The crate's [README](../README.md) states the rest of the kernel. The [experimental stage universe](staging.md) defines the local equations this module admits.

<!-- toc -->

- [The judgments and their boundary](#the-judgments-and-their-boundary)
- [Schema judgment](#schema-judgment)
- [Admissible-substitution judgment](#admissible-substitution-judgment)
- [Instance judgment](#instance-judgment)
- [Work and parallelism obligations](#work-and-parallelism-obligations)
- [Decisions](#decisions)
- [Witnesses](#witnesses)

<!-- tocstop -->

## The judgments and their boundary

The kernel decides schema inheritance, rule-discrimination transparency, guarded substitution and exact instance-side agreement. A producer cache establishes none of them. Ordinary `stage::replay`, complete-certificate endpoint typing and connectivity remain authoritative and unchanged.

| Judgment | Kernel establishes | Witness |
| -------- | ------------------ | ------- |
| `Schema::check(T)` | Canonical backward skeleton and classifiers, source-rooted points, fixed rule observations, fresh-skolem inheritance per distinct point/arm obligation | Corrupt-step, mixed zero/positive and work-ceiling refusals |
| `Schema::substitute(σ)` | Every point supplied, schema-owned arm, equal repeated choices, exact classifier vocabulary | Unknown arm, missing point, correlation and classifier refusals |
| `Substitution::admit(sides)` | Exact content identities equal the schema instance's identities | Side and classifier-coordinate poisoning; no rule re-derivation |

**Why inheritance transfers.** Rule schemes are substitution-closed only when their observations remain fixed.

- Cancellation reads rigid quote/splice heads.
- Iteration reads a rigid iterator and either a rigid count or guards all in the same outer-natural zero/positive class. Positive predecessor is one numeric operation, not unary expansion.
- Beta requires rigid application/lambda heads and closed arms, preserving its binding behavior.

Unsupported or unstable observations are refused before an instance capability exists. Each point/arm inheritance probe holds other points at pairwise fresh rigid code constants. Repeated occurrences share a point, so correlation is explicit rather than inferred from content coincidence.

Fixed records are interned once, into the binding. Rows share that immutable binding and look up their dependent exact records in it without adding any. Constructor tags, stages, payloads, child content ids and classifier content ids all participate in record identity. Both consumer roots live in the binding's namespace. Collision resistance supplies no positive premise; digests are not used by this route, and **a fingerprint never authorizes a positive verdict**.

**Boundary.** The claim is about one recorded local equation. It does not type an open point, establish well-typed endpoints, connect arbitrary certificate steps, or replace complete typed replay. The supported beta guard discipline is conservative: rejecting an open arm is not a theorem that its ordinary equation is invalid. Soundness rests on the stated substitution/transparency argument; the finite differential is executable evidence, not a machine-checked metatheory.

## Schema judgment

`Schema(T)` requires a canonical backward-referencing skeleton, source-rooted points, exact classifier-vocabulary content, and one recorded local rule. Each distinct region/entry/body obligation is checked with other points represented by pairwise fresh rigid constants. A ground schema owes one check. A producer cache never establishes this judgment. The vocabulary binds classifier syntax, not an inferred type for an open point.

Inheritance alone is insufficient. Discrimination transparency requires every constructor or payload a recorded rule inspects to be rigid or fixed by its guard. For iteration this includes the count's stage and zero versus positive classification. For beta it includes the application and lambda heads and the binding behavior of every substituted body. A family allowing both zero and positive counts cannot inherit one iteration rule. A changed step must fail at schema validation, before any instance is considered.

Beta arms must be closed, so substituting them preserves the rigid binding skeleton. Structural cancellation does not inspect its body. Iteration requires outer-natural guard arms in one zero/positive class; predecessor is defined only for positive arms. These explicit observations, together with replay of each distinct inheritance obligation, justify substitution closure for the admitted rule fragment.

The fixed skeleton is interned once into a probe base: the vocabulary, the skolems and every node no guard changes. Each obligation clones the base, interns only its dependent nodes and replays its equation. The clone and its replay die with the obligation. The equation is the one a probe reified from scratch for the same binding would replay: the bound point takes its arm, every other point and predecessor a fresh rigid code.

## Admissible-substitution judgment

`T ⊢ σ admissible` requires exactly one guarded arm for every point, belonging to that schema's region, point and classifier content. Correlated occurrences select the same arm. Unknown arms, disagreement and classifier mismatch are distinct refusals. Dense point-ordered rows and validated immutable arm dictionaries permit work linear in the row's encoded size. The row does not authorize an unvalidated body through a claimed digest.

## Instance judgment

`Schema(T)` and `T ⊢ σ admissible` entail the local derivation `T[σ]` by substitution closure and discrimination transparency, without executing the derivation again. Connecting its sides to a consumer's claim is a separate obligation. Local equations do not establish endpoint typing or the connectivity of a complete certificate. Those premises remain required.

Let `D(T, σ)` count distinct rigid skeleton constructors above changed points. `Schema::bind` imports fixed schema terms and classifiers into the consumer's exactly interned arena once. Each row then looks up only the dependent plan in that arena; predecessor expressions add one constructor per used point. A planned record the arena lacks refuses the row as `SidesMismatch`. The arena holds every record of each live side, so a record it lacks belongs to no side. Two live input roots are then compared with two expected root ids in that same namespace. No materialized-side walk or classifier import remains in the member judgment. The binding cannot replace its arena or switch schemas, and a clone retains both associations.

**Refusal distinction.** A side whose classifier content differs under a reused numeric coordinate returns `SidesMismatch`, not `ClassifierMismatch`; a foreign row vocabulary still returns `ClassifierMismatch`. Diagnostic specificity is lost; positive exactness is not. A negative-only vocabulary check on the refusal path could restore the distinction, at the cost of walking both sides on every refusal. It would never be positive evidence.

## Work and parallelism obligations

For a family of independent rows, the advertised compressed bound must price schema validation once, every distinct inheritance obligation, all row validation, and side comparison separately. Repeating a body check for each guard is real work even when the encoding shares that body. Counting only row bytes cannot hide this work. No theorem here grants a compressed cannot-lose bound from measured compression ratios.

Schema validation has its own input-sized work ceiling: one charged node operation per byte of the native fixed-width proposal image (node, classifier, arm-index and descriptor slices). Every schema traversal and inheritance replay consumes that allowance. Each obligation charges the vocabulary and one unit per pattern node, the size of the base it clones. Exhaustion returns `SchemaWorkBound`, never a partial capability. Binding consumes the caller's preparation budget, and instance admission charges its reachable plan and root liveness checks. These are operation bounds, not CPU-time promises: exact ordered tables add logarithmic lookup cost. The native image is an experimental accounting format, not a wire format.

`Schema::work` reports the obligations checked, the fuel their replays spent and the dependent constructors; `Schema::largest_replay` reports the fuel of the most expensive single replay. A caller that enforces a per-check allowance on its own replays, as the memoized staging price does, compares that allowance with `largest_replay` before treating a schema checked here as one it would have emitted.

Row work is `O(|σ| + D(T, σ))` charged plan operations, plus two root liveness checks and two id comparisons. Binding is separately charged preparation, not free work: it imports fixed schema content and classifiers once. `D` is not generally depth; the fanout witness covers a shared point below many distinct parents. `Admission` separates row choices, dependent rigid constructors and looked-up constructors; its materialized term/classifier import counters are zero.

Members form an antichain. `Schema` and `Consumer` are `Sync`: one validated immutable schema and one immutable binding, shared by reference, with a `Row` buffer per worker, permit threads without shared mutable kernel state. The module spawns no thread. Pools, rings and widths belong to the caller; the guarded admission observer on the [staging families page](../../core-checker/docs/staging.md) measures them. Any parallel measurement must retain the same verdict at every thread count and report thread creation separately or include it on both sides. It must also distinguish local equation admission from complete typed certificate admission.

## Decisions

**Row shape.** A row validates its choices into a caller-owned `Row` buffer and compares by lookup in the shared binding. Once the buffer has grown to the largest schema it serves, a row allocates nothing.

- _Alternative:_ a row could intern its instance into a per-worker overlay or consumer clone. That allocates on every row, and under parallel rows the allocations contend on the platform allocator.
- _Alternative:_ a concurrent global allocator removes some of that contention but leaves the allocation.
- _Measured_ on 16 natural and 15 captured families, three runs each, on an Apple M3 Max under Darwin, a 16-core x86-64 under Linux and an arm64 Linux VM. With $R$ = (schema + pooled rows) / (schema + largest row), lookup rows keep $R \le 2$ at the best pool width on every family, worst 1.47, with zero allocations after warm-up. Interning rows reach 2.71 under Darwin's default allocator, and 2.22 at 8 workers with its nano zone off.
- _Reversal:_ a consumer that must admit instance records its arena does not yet hold.

**Shared probe base.** The schema reifies its fixed skeleton once and clones it per obligation. The alternative reifies every probe from scratch through an ordered map. The base is 1.38–1.65× faster on families with at least eight obligations, and its replays equal fresh probes'. Reversal: schemas whose obligations are few and whose fixed skeleton is small, where one clone per obligation costs more than it saves.

**Folded classifier refusal.** Coordinate-aliased classifier content refuses as `SidesMismatch`, as stated above. Reversal: a caller that acts differently on the two refusals.

## Witnesses

The permanent witnesses in `admission::tests` cover:

- corrupt steps, unknown arms, missing points and conflicting correlations;
- classifier content under reused coordinates, and side mismatch;
- records absent from the binding, and row-buffer reuse across schemas;
- zero/positive rule changes and the schema work ceiling;
- shared-base replay against fresh probes, and fanout;
- scheduling independence, foreign-schema bindings, future coordinates, and reuse after partial work exhaustion.

A standalone mutation campaign should target these admission predicates and exact constructor domains; no mutation score is claimed.
