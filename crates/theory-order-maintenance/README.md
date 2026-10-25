# gandr-theory-order-maintenance

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

**How.** Every element carries a key strictly increasing in list order, in two levels: its group's label on a circle of `2^64` labels and its own label within the group, so comparison is at most two integer comparisons. An insertion takes the midpoint of its neighbours' labels in their group, and a full group splits (see [List labeling](#list-labeling)). Elements live in a flat, id-addressed arena with a free list, and their groups in a second one; a handle names its slot, the slot's generation and the structure's identity, so a stale or foreign handle is detected rather than resolved against an unrelated element.

## References

- Paul F. Dietz and Daniel D. Sleator. "Two Algorithms for Maintaining Order in a List." In _Proceedings of the Nineteenth Annual ACM Symposium on Theory of Computing (STOC '87)_, pages 365–372, 1987. `doi:10.1145/28395.28434` — the order-maintenance problem this crate solves, the relabel walk around the circle of group labels, and the two-level structure.
- Michael A. Bender, Richard Cole, Erik D. Demaine, Martin Farach-Colton, and Jack Zito. "Two Simplified Algorithms for Maintaining Order in a List." In _Algorithms — ESA 2002_, edited by Rolf H. Möhring and Rajeev Raman, Lecture Notes in Computer Science 2461, pages 152–164, 2002. `doi:10.1007/3-540-45749-6_17` — the two-level structure's amortized analysis.
- Bin Guo and Emil Sekerinski. "New Concurrent Order Maintenance Data Structure." _Journal of Parallel and Distributed Computing_ 211 (2026), 105238. `doi:10.1016/j.jpdc.2026.105238` — the two-level structure as built here: groups at the midpoint of the room after the full one, a split into groups of half the label width, and the rebalance and relabel procedures, with the concurrent operations a later structure takes from it.
- Thomas J. Porter, Marisa Kirisame, Ivan Wei, Pavel Panchekha, and Cyrus Omar. "Incremental Bidirectional Typing via Order Maintenance." _Proceedings of the ACM on Programming Languages_ 9, OOPSLA2 (October 2025), pages 1865–1892. `doi:10.1145/3763117`; preprint `arXiv:2504.08946` — the incremental typing algorithm this crate serves, and the pre/post-order interval test.

## Provided features

- `OrderMaintenance<T>`: a payload-carrying total order over opaque handles. `push_front`, `push_back`, `insert_after` and `insert_before` insert; `remove` removes; `cmp` compares; `first`, `last`, `next`, `prev`, `get`, `contains`, `len`, `is_empty` and `iter` observe. `new` builds one with the default group width, `with_group_width` with another.
- `GroupWidth`: the width of a group's labels, built `From` a `u32` clamped to `[4, 31]`; a full group splits into groups of half of it.
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
use gandr_theory_order_maintenance::OrderError;
use gandr_theory_order_maintenance::OrderMaintenance;

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
cargo nextest run -p gandr-theory-order-maintenance
RUSTFLAGS="--cfg anodized_panic" cargo nextest run -p gandr-theory-order-maintenance
```

## List labeling

Insertion is two-level list labeling. Consecutive elements share a group. A group's label is a point on a circle of `2^64` labels, and its place in the order is its distance around the circle from the first group's label. An element's label lies in `[0, 2^w)` within its group, `w` the group width. An insertion takes the midpoint of its neighbours' labels in their group: the predecessor's group, or the successor's at the front, the group's ends standing in for a neighbour in another group.

When a group has no label between the neighbours, it splits. Its last `w/2` elements become a new group after it, placed at the midpoint of the room between it and the next group around the circle, and the cut is repeated until `w/2` or fewer remain; each group the split makes, and the one it cut, spreads its elements evenly over its labels. When the room after the full group is under two labels, the groups after it are relabelled first: the walk takes successors around the circle until the `j`th lies more than `j²` labels on, and spreads the `j - 1` it passed evenly over that room. Past the last group the walk continues from the first, so the first group's label may move; every distance from it keeps its order. Insertion is O(1) amortized: a split is paid for by the `w/2` insertions that filled the group, and a group's insertion on the circle by the walk's own amortization. The structure is total up to the `u32` slot ceiling, because a circle of `2^64` labels holds the square of the most groups a structure can have.

The group width is a parameter. `GroupWidth::DEFAULT` is the widest, 31, which the crate's bench (`cargo bench -p gandr-theory-order-maintenance`) measures fastest, or within a few nanoseconds of the fastest, at every size from a thousand elements to a million. Its workloads are appends, insertion behind one element, random insertion, comparison, removal and a churn of the two.

Labels are internal and never exposed, so no caller depends on a numeric encoding a relabel is free to change. `Pos` is the only identity.

## Handles and failures

A slot's generation counter is bumped each time the slot is freed, so a handle minted before the reuse does not resolve. A slot whose generation counter is exhausted is retired rather than wrapped. A handle carries its structure's identity, and a handle from another structure is refused.

Handle liveness is a returned classification, never a precondition: an operation on a stale or foreign handle returns `None` or `OrderError::UnknownPosition`. Every internal write returns a typed result, so a violated arena invariant surfaces as `OrderError::Inconsistent` rather than as a dropped write. `remove` returns `Result<Option<T>, OrderError>`: `Ok(None)` is a stale handle, `Err` a corrupted arena. Construction is fallible too, so the process-wide structure-id counter never wraps.

## Specification attributes

The `# Specification` prose states the obligation. Executable `#[spec(...)]` clauses check the locally observable part under `--cfg anodized_panic`; each `# Adequacy` block names same-crate witnesses and the boundary of their evidence. Contracts use scalar captures and borrowed identity, not whole-arena or payload snapshots.

Handle liveness remains a returned classification, never an asserted prerequisite. Public predicates check membership, comparison, inclusive interval bounds, insertion adjacency and removal's stale handle and repaired neighbours. Arena predicates distinguish occupied, free, retired and absent slots, including the identity of returned borrows. The shared identity counter is bounded by monotone observations; a deterministic concurrent batch and the final-identity refusal witness its cross-call obligations.

The relabel predicates check the room a rebalance leaves, the groups a split leaves and their order, the exact spread labels, and every group's bookkeeping as each insertion and removal changes it. Allocation captures the old length and checks the returned handle without cloning its moved payload. Iterator predicates bind the owner and cursor and check each state transition; the independent sequence models, one over the default widths and one over a narrow circle whose groups split, rebalance and wrap past the last group, witness the complete walk. Numeric witnesses cover rounding, wide multiplication and the wrapped distance around the circle rather than inferring exact arithmetic from sorted keys alone.

Four items retain explicit executable boundaries:

| Item | Boundary |
| ---- | -------- |
| `Interval::new` | The datum does not hold the owning order. Its opaque `Pos` endpoints expose neither fields to this module nor a const value-equality observer. Const functions themselves are supported; this is an observer boundary. |
| `OrderError::fmt` | A formatter exposes a write-only sink, not independently readable output or its write outcome. Distinct failure classes and a bounded sink witness rendering without pinning wording. |
| `oracle::op_strategy` | The attribute backend cannot instrument the opaque returned strategy. A deterministic bounded census witnesses all five edit variants, not every numeric value or seed. |
| `order::tests::model::edit` | The same opaque-strategy boundary. The narrow sequence model's replay observes every edit it is handed. |

Revisit the interval boundary when a const-readable endpoint observer is available, and the strategy boundaries when the backend supports opaque returns. The sequence oracles, narrow-circle fixtures and negative observer cases remain necessary: executable local certificates do not establish amortized cost, complete machine-sized arithmetic coverage or the behaviour of malformed cyclic arenas.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
