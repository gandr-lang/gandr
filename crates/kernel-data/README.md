# gandr-kernel-data

The kernel's own data types: a region whose ids carry its brand, a small vector, a shared pointer with one count and a small string.

<!-- toc -->
- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** `gandr-kernel-data` holds the data types that the kernel owns. A `Region` holds values under a budget, and its ids carry its brand. A `SmallVec` keeps a few items in place, a `Shared` shares one value by one count, and a `SmallString` keeps a short text inline. The crate is `no_std` over `core` and `alloc`, and depends on no other workspace crate, so both chains of the kernel reach it as a leaf.

**Why.** A worker of the kernel owns what it writes, and what it shares is frozen. So a check needs ids that cannot leave their scope, and a store whose budget refuses and never aborts. It also needs containers that take no block of the global allocator for each small value. An index of a `Vec` carries no brand, an `Arc` keeps a weak count beside its strong count, and a `String` takes a block for each text.

**How.** A scope brands the region and hands its body one `Mint`, and each id takes the mint, so no id leaves the scope. Three crossings move an id between regions. A fork of `Width` children shares one frozen prefix, and each child keeps or drops its own suffix. A borrow of a region is an allocator, so the containers can draw from a region. The small vector tags its length with where its items live. The shared pointer keeps one count beside its value. The small string keeps the tag of its form in the spare values of its inline length byte.

## References

- `vault:01a178ab-17e5-7352-bc0b-3caa7f1e476c` — anchor: the storage programme (§ storage-programme-region-is-an-allocator) — the region is one allocator with a budget that refuses and never aborts, and a fork's suffix is a region of its own that the join folds or drops.
- `vault:01a1d7fd-eeb5-7010-80e7-df4d768b6583` — anchor: lines 1 to 3 and 5 of the performance picture — a worker owns its region, what is shared is frozen, each crossing is explicit, and what was written apart glues again at the cost of what differs.

## Provided features

- The region: `Region`, `scoped` and `scoped_in` hold values under a `Budget` with ids branded by the scope; `Adopt`, `Translation`, `Id::key` and `Region::seat` are the three crossings, and `Region::forks` forks `Width` children over one frozen prefix, each answer among the `Siblings`.
- The small vector: `SmallVec<T, N, A>` keeps up to `N` items in place and all of them past `N` in one block of `A`, and `try_reserve` answers a refused grow with `Refused`.
- The shared pointer: `Shared<T, A>` shares one value by one count with no weak count, `Unique<T, A>` builds the value before the share, and `ThinShared<H, T, A>` is one word over a header and a slice. An empty default of `ThinShared` with no header, over the global allocator, shares one static block and allocates nothing.
- The small string: `SmallString<A>` holds a text of up to 23 bytes inline, a static text, or a block of `A`, in 24 bytes for the global allocator.

## Expected features

A value of a region that forks implements `Rebase`, and the answer of a child implements `Branded`, so the glue reads each key and each id through the shift. `Region::forks` takes a `run` that enters each `Child` on the threads that it chooses, and the crate starts no thread. An allocator for the `_in` forms implements `core::alloc::Allocator`, and the global allocator is the default. The `loom` model of the shared count builds under `--cfg loom`.

## Examples

A region, a small vector, a shared pointer and a small string:

```rust
use gandr_kernel_data::Budget;
use gandr_kernel_data::Id;
use gandr_kernel_data::Shared;
use gandr_kernel_data::SmallString;
use gandr_kernel_data::SmallVec;
use gandr_kernel_data::scoped;

fn main() {
    // A region of one mebibyte: each id reads the value minted at it, and no
    // id leaves the scope.
    let read = scoped(Budget::from(0x10_0000_usize), |region, mut mint| {
        let id: Id<'_> = region.mint(&mut mint, 7_u64).expect("the budget holds it");
        region.get(id).copied()
    });
    assert_eq!(read, Some(7));

    // Four items in place, and no block.
    let small: SmallVec<u32, 4> = SmallVec::from([1, 2, 3, 4]);
    assert_eq!(small.as_slice(), &[1, 2, 3, 4]);

    // One value, two holders, one count.
    let shared = Shared::new(SmallVec::<u32, 4>::from([5, 6, 7, 8]));
    let other = Shared::clone(&shared);
    assert_eq!(other.as_slice(), &[5, 6, 7, 8]);

    // A text of six bytes, inline in the string's 24 bytes.
    let name: SmallString = SmallString::try_from("region").expect("the text fits inline");
    assert_eq!(&*name, "region");
}
```

Run the crate's tests from the repository root:

```sh
mise exec -- cargo test -p gandr-kernel-data
```

## Where the detail lives

Mechanism, invariants and witnesses live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| The crate's types, and how they meet | [`src/lib.rs`](src/lib.rs) |
| The region: the brand, the three crossings, the fork and its glue, the rollback forms, and a borrow of a region as an allocator | [`region`](src/region.rs) |
| The small vector: the tag in the length, the sizes and the refused grow | [`small_vec`](src/small_vec.rs) |
| The shared pointer: the one count, its orderings, the `loom` model and the sizes against `std` | [`shared`](src/shared.rs) |
| The thin shared pointer over a header and a slice | [`thin_shared`](src/thin_shared.rs) |
| The small string: the three forms, the tag in the length byte and the one `unsafe` | [`small_string`](src/small_string.rs) |

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
