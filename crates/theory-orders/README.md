# gandr-theory-orders

An order-maintenance structure: a total order over payload-carrying elements in which any two elements compare in constant time.

<!-- toc -->

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [List labeling](#list-labeling)
- [Handles and failures](#handles-and-failures)
- [Specification attributes](#specification-attributes)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** `OrderMaintenance<T>` holds a collection in a total order. An element is inserted at either end or beside another, removed, and compared with any other element in O(1). `Interval` and `OrderMaintenance::interval_contains` build the pre/post-order containment query on that comparison. The crate is `no_std` and depends only on `core`, `alloc` and the specification facade.

**Why.** An incremental checker schedules re-checking from a dirty-step priority queue ordered by position in the term, and it asks one question constantly: does this term enclose that one. Pre- and post-order timestamps drawn from an order-maintenance structure answer it with two integer comparisons. Binder lookup, the per-node mark and dirty-bit layout, and any binding of order points to the concrete-syntax tree's identity carry invariants of their own and live in the consumer.

**How.** Every element carries an integer label strictly increasing in list order, so comparison is one integer comparison. Labels come from list-labeling over a sparse integer universe: an insertion takes the midpoint of its neighbours' gap, and an exhausted gap relabels a window around the insertion point (see [List labeling](#list-labeling)). Elements live in a flat, id-addressed arena with a free list; a handle names its slot, the slot's generation and the structure's identity, so a stale or foreign handle is detected rather than resolved against an unrelated element.

## References

- Paul F. Dietz and Daniel D. Sleator. "Two Algorithms for Maintaining Order in a List." In _Proceedings of the Nineteenth Annual ACM Symposium on Theory of Computing (STOC '87)_, pages 365–372, 1987. `doi:10.1145/28395.28434` — the order-maintenance problem this crate solves.
- Alon Itai, Alan G. Konheim, and Michael Rodeh. "A Sparse Table Implementation of Priority Queues." In _Automata, Languages and Programming (ICALP 1981)_, edited by Shimon Even and Oded Kariv, Lecture Notes in Computer Science 115, pages 417–431, 1981. `doi:10.1007/3-540-10843-2_34` — the list-labeling scheme the relabel rule refines.
- Michael A. Bender, Richard Cole, Erik D. Demaine, Martin Farach-Colton, and Jack Zito. "Two Simplified Algorithms for Maintaining Order in a List." In _Algorithms — ESA 2002_, edited by Rolf H. Möhring and Rajeev Raman, Lecture Notes in Computer Science 2461, pages 152–164, 2002. `doi:10.1007/3-540-45749-6_17` — the simplified algorithm and amortized analysis the density cap comes from.
- Thomas J. Porter, Marisa Kirisame, Ivan Wei, Pavel Panchekha, and Cyrus Omar. "Incremental Bidirectional Typing via Order Maintenance." _Proceedings of the ACM on Programming Languages_ 9, OOPSLA2 (October 2025), pages 1865–1892. `doi:10.1145/3763117`; preprint `arXiv:2504.08946` — the incremental typing algorithm this crate serves, and the pre/post-order interval test.

## Provided features

- `OrderMaintenance<T>`: a payload-carrying total order over opaque handles. `push_front`, `push_back`, `insert_after` and `insert_before` insert; `remove` removes; `cmp` compares; `first`, `last`, `next`, `prev`, `get`, `contains`, `len`, `is_empty` and `iter` observe.
- `Interval` and `OrderMaintenance::interval_contains`: the pre/post-order containment test in constant time.
- `Pos`: the handle, opaque, generation-checked and structure-checked. It stays valid across relabels.
- `Iter`: in-order iteration as an explicit state machine over slot indices.
- `OrderError`: every failure as a typed value — capacity exhaustion, structure-id exhaustion, an unknown handle, an inconsistent arena.
- `LiveLen`, `OrderIsEmpty`, `HandleMembership`, `IntervalContainment`: the nominal results of the observation queries.

## Expected features

- **An atomic compare-exchange.** Each structure draws a process-unique identity from a shared `AtomicUsize`, so a handle from one structure is refused by another. The crate requires `target_has_atomic = "ptr"`. Every hosted target qualifies, as does every embedded target with a compare-exchange instruction, including 32-bit targets without 64-bit atomics such as `thumbv7m-none-eabi` and `riscv32imac-unknown-none-elf`. Load/store-only cores such as `thumbv6m-none-eabi` would need a critical section for a sound process-wide counter, which the crate has no way to obtain; building for one fails with an explanatory `compile_error!`.
- **`--cfg anodized_panic` for enforcement.** Built with this `cfg` across the whole dependency graph, the `#[spec]` attributes check their clauses at runtime and panic on a violation. The enforcing test lane sets it.

## Examples

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

Run the tests, then the enforcing twin with every specification checked:

```sh
cargo nextest run -p gandr-theory-orders
RUSTFLAGS="--cfg anodized_panic" cargo nextest run -p gandr-theory-orders
```

## List labeling

Insertion is single-level list-labeling over a fixed label universe. An insertion takes the midpoint label of the gap between its neighbours when one exists. When the gap is exhausted, it relabels the smallest power-of-two-aligned window around the insertion point that is at most half full and spreads the window's elements evenly across it. The density cap keeps that window sparse enough for the spread to succeed, so insertion is total and O(log² n) amortized. The window buffer is allocated once per relabel and reused across the widening steps.

The two-level refinement that makes insertion O(1) amortized is absent by choice: comparison, the operation consumers need, is O(1) under either scheme, and the single-level relabel rule stays fully inspectable. Revisit the refinement when a real edit-trace profile shows insertion cost dominates.

Labels are internal and never exposed, so no caller depends on a numeric encoding a relabel is free to change. `Pos` is the only identity.

## Handles and failures

A slot's generation counter is bumped each time the slot is freed, so a handle minted before the reuse no longer resolves. A slot whose generation counter is exhausted is retired rather than wrapped. A handle carries its structure's identity, and a handle from another structure is refused.

Handle liveness is a returned classification, never a precondition: an operation on a stale or foreign handle returns `None` or `OrderError::UnknownPosition`. Every internal write returns a typed result, so a violated arena invariant surfaces as `OrderError::Inconsistent` rather than as a dropped write. `remove` returns `Result<Option<T>, OrderError>`: `Ok(None)` is a stale handle, `Err` a corrupted arena. Construction is fallible too, so the process-wide structure-id counter never wraps.

## Specification attributes

The `# Specification` prose is the statement of record. A combined `#[spec(...)]` attribute mirrors each requirement and postcondition that a total, allocation-free Rust predicate can state, and every such clause is checked: negating any one in place makes a named test in this crate fail under the enforcing lane.

The public surface's clauses cross-check the crate's own observations rather than restating a field. `get` returns a payload exactly when `contains` reports the handle live. `cmp` is the label comparison of the two resolved elements, with `Some(Equal)` confined to the reflexive arm. `interval_contains` checks both bounds and their inclusivity. `push_front` and `push_back` land the returned handle at `first` and `last`. `insert_after` and `insert_before` place the new element against the neighbour captured at entry. `remove` leaves the handle stale, its slot free or retired, and its former neighbours adjacent.

The relabel path carries the invariant it preserves. `insert_between` and `link_new` state the adjacency each call site reads, and `link_new` the whole wiring it performs. `redistribute`, `assign_labels` and `spread_label` state the density arithmetic. `assign_labels` and `relink_segment` state that every relabeled element carries the spread label of its position, that the labels strictly increase, and that the rebuilt segment is contiguous between its two bounds.

A block stays prose, naming its boundary in `- provides:`, where a checked clause would change behaviour or cannot observe its claim:

- Handle liveness is a returned classification, so asserting it would turn a documented refusal into a panic.
- Structure-id and slot-limit claims are laws over other calls.
- `iter`'s postcondition quantifies over a walk the caller has yet to perform.
- `alloc` and `relabel_insert` speak of a payload moved into the slot or a window local to the call.
- `collect_window`'s claim could only be rechecked by walking the list again.
- `Interval::new` keeps its `const fn` signature, because the attribute's expansion calls a non-const evaluator (`E0015`).

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
