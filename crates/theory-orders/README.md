# gandr-theory-orders

An order-maintenance structure: a collection held in a total order, where an element can be inserted beside another or removed, and any two elements can be compared in constant time.

Constant-time comparison is the operation the incremental pipeline needs and the reason this crate exists. Pre- and post-order timestamps over such a structure decide in O(1) whether one term encloses another, which is what drives the dirty-step priority queue an incremental checker schedules from.

The crate is the order structure and the containment query built directly on it, and nothing else. The lowest-enclosing-binder lookup, the per-node mark and dirty-bit layout, and any binding of order points to the concrete-syntax tree's reproducible identity are separate pieces that _consume_ this one.

## Status

Ported from the `theory-orders` crate of the pre-reboot prototype and revised against the reboot constraints. The revisions, all constraint-driven:

- **Typed inconsistency.** The prototype's internal setters silently no-oped when a link or label did not resolve, and its internal walks reported an unrelated `CapacityExhausted`. Every internal write now returns a typed result, and a violated arena invariant surfaces as `OrderError::Inconsistent` instead of a dropped write or a mislabelled capacity error. `remove` returns `Result<Option<T>, OrderError>` as a consequence: `Ok(None)` is a stale handle, `Err` is a corrupted arena.
- **No bare primitives in fields or signatures.** Slot reuse counters are a `SlotGeneration` wrapper rather than a raw `u32`, and the arithmetic on them goes through `successor`; the same applies to the live-element count and the label-universe width.
- **No dependencies.** `thiserror` is replaced with hand-written `Display` and `core::error::Error` impls, so the crate depends only on `core` and `alloc` and is `no_std`.
- **Pointer-width structure ids.** The prototype's structure-id counter was an `AtomicU64`, which does not exist on targets without 64-bit atomics. The counter is `AtomicUsize`, so the crate builds anywhere a compare-exchange exists.
- **One allocation per relabel.** The window buffer is allocated once and reused across the widening steps instead of once per step.
- **First-order iteration.** Iteration is an explicit `Iter` state machine over slot indices rather than a closure captured in `core::iter::from_fn`.

Everything already conformant in the prototype — no recursion, an arena flat and id-addressed rather than pointer-linked, no `as` casts, checked arithmetic, no `unwrap`/`expect`/`panic` outside tests — is preserved.

## What it provides

- `OrderMaintenance<T>`, a payload-carrying total order over opaque handles. Comparison is one integer comparison. Insertion at either end or beside an existing element, removal, navigation, iteration, and the ordinary queries complete the surface.
- `Interval` and `OrderMaintenance::interval_contains`, the pre/post-order containment test in constant time.
- `Pos`, the handle: opaque, generation-checked and structure-checked. A handle to a removed element or a handle from a different structure is detected rather than silently aliasing an unrelated element, and a slot whose generation counter is exhausted is retired instead of wrapping.
- Totality. Capacity exhaustion, structure-id exhaustion, unknown handles, and arena inconsistency are all typed `OrderError` values; construction is itself fallible rather than wrapping the process-wide structure-id counter.

The implementation is single-level list-labeling over a fixed label universe. Insertion takes the midpoint label of the gap between its neighbours when one exists; when the gap is exhausted it relabels the smallest power-of-two-aligned window around the insertion point that is at most half full and redistributes evenly. The density cap keeps that window always sparse enough for the relabel to succeed. Insertion is therefore O(log² n) amortized.

## The contract attributes

The `# Specification` prose is the statement of record; a combined `#[spec(...)]` attribute mirrors each requirement and postcondition a total, allocation-free Rust predicate can state. Twenty-one items carry one, and every clause is checked: negating any one of the twenty-four in place makes a named test in this crate fail under the enforcing lane.

The public surface's clauses are cross-checks through the crate's own observations rather than restatements of a field: `get` returns a payload exactly when `contains` reports the handle live, `cmp` is the label comparison of the two resolved elements with `Some(Equal)` confined to the reflexive arm, `interval_contains` is both bounds and their inclusivity, `push_front`/`push_back` land the returned handle at `first`/`last`, `insert_after`/`insert_before` place the new element against the neighbour captured at entry, and `remove` leaves the handle stale, its slot free or retired, and its former neighbours adjacent.

The relabel path carries the invariant it exists to preserve. `insert_between` and `link_new` state the adjacency each call site reads; `link_new` also states the whole wiring it performs; `redistribute`, `assign_labels`, and `spread_label` state the density arithmetic, and `assign_labels` and `relink_segment` state that every relabeled element carries the spread label of its position, that the labels strictly increase, and that the rebuilt segment is contiguous between its two bounds.

Six blocks stay prose, each naming its boundary in `- provides:`. Handle liveness is a returned classification (`None` or `OrderError::UnknownPosition`), never a precondition, so asserting it would turn a documented refusal into a panic. Structure-id and slot-limit claims are laws over other calls; `iter`'s postcondition quantifies over a walk the caller has yet to perform; `alloc`'s and `relabel_insert`'s speak of a payload moved into the slot or a window local to the call; `collect_window`'s could only be rechecked by walking the list again. `Interval::new` keeps its `const fn` API without the attribute, because the pinned expansion calls a non-const evaluator (`E0015`).

`anodized` supplies core-only specification helpers with default features disabled. The enforcing test lane selects `--cfg anodized_panic` for the whole dependency graph; no logic/BigInt dependency is enabled.

## Not provided

- The two-level refinement that would make insertion O(1) amortized. The single-level scheme is deliberate: comparison is the operation the consumer needs, and the simple relabel rule is fully inspectable.
- The byte-range resync against the syntax tree. Whether an adapter from this structure to concrete-syntax identity pays for itself waits on a dirty-frontier consumer.

The incremental typing layer is the intended consumer; it does not exist in this repository yet, so the crate currently has no in-workspace consumers.

## Target requirement

Structures carry a process-unique identity drawn from a shared atomic counter, so a handle from one structure is rejected by another instead of silently resolving against an unrelated element. That counter needs an atomic compare-exchange, which is the crate's only target requirement: `target_has_atomic = "ptr"`.

Every hosted target and every embedded target with a compare-exchange instruction qualifies — including 32-bit targets without 64-bit atomics such as `thumbv7m-none-eabi` and `riscv32imac-unknown-none-elf`. The excluded set is load/store-only cores such as `thumbv6m-none-eabi`, where a sound process-wide counter would need a critical section this crate has no way to obtain. Building for such a target fails with an explanatory `compile_error!` rather than a missing-atomic-type error.

## Using it

Build the order, insert relative to what is already there, and compare.

```rust
use gandr_theory_orders::OrderError;
use gandr_theory_orders::OrderMaintenance;

fn example() -> Result<(), OrderError> {
    let mut order: OrderMaintenance<()> = OrderMaintenance::new()?;
    let first = order.push_back(())?;
    let second = order.insert_after(first, ())?;
    let ordering = order.cmp(first, second);
    assert_eq!(ordering, Some(core::cmp::Ordering::Less));
    Ok(())
}
```

Labels are internal and never exposed, so a caller cannot depend on the numeric encoding a relabel is free to change. `Pos` is the only identity, and it stays valid across relabels.

## Theoretical ideas relied on

The order-maintenance problem; list-labeling over a sparse integer universe; pre- and post-order timestamp intervals as a constant-time containment test; incremental bidirectional typing driven by a dirty-step priority queue.

## Primary references

- Paul F. Dietz and Daniel D. Sleator. "Two Algorithms for Maintaining Order in a List." In _Proceedings of the Nineteenth Annual ACM Symposium on Theory of Computing (STOC '87)_, pages 365–372, 1987. `doi:10.1145/28395.28434` — the problem statement this crate solves.
- Alon Itai, Alan G. Konheim, and Michael Rodeh. "A Sparse Table Implementation of Priority Queues." In _Automata, Languages and Programming (ICALP 1981)_, edited by Shimon Even and Oded Kariv, Lecture Notes in Computer Science 115, pages 417–431, 1981. `doi:10.1007/3-540-10843-2_34` — the list-labeling scheme the relabel rule here refines.
- Michael A. Bender, Richard Cole, Erik D. Demaine, Martin Farach-Colton, and Jack Zito. "Two Simplified Algorithms for Maintaining Order in a List." In _Algorithms — ESA 2002_, edited by Rolf H. Möhring and Rajeev Raman, Lecture Notes in Computer Science 2461, pages 152–164, 2002. `doi:10.1007/3-540-45749-6_17` — the simplified algorithms and the amortized analysis the density cap is taken from.
- Thomas J. Porter, Marisa Kirisame, Ivan Wei, Pavel Panchekha, and Cyrus Omar. "Incremental Bidirectional Typing via Order Maintenance." _Proceedings of the ACM on Programming Languages_ 9, OOPSLA2 (October 2025), pages 1865–1892. `doi:10.1145/3763117`; preprint `arXiv:2504.08946` — the consumer this crate was commissioned for, and the source of the pre/post-order interval test.

## License

Apache-2.0 WITH LLVM-exception.
