# gandr-kernel-data

The kernel's own data types. The crate is `no_std` over `core` and `alloc`, and depends on no other workspace crate, so both chains reach it as a leaf.

## The region

A `Region` holds values under a budget, and refuses a value past it. A scope, `scoped`, brands the region and hands its body one `Mint`. Each id takes the mint, so no id leaves the scope.

A region holds the values of one or more families in one id space. An id `Id<'r, Kind>` names its family by a phantom kind, so an id of one family does not stand for an id of another. A region of one family takes the kind `()`.

Three crossings move an id between regions, and nothing else does:

| Crossing | Where | Form |
| -------- | ----- | ---- |
| `Adopt::adopt` | a fork | the parent's id, read as the child's: the id itself |
| `Translation::translate` | a join | the child's id, read as the parent's: below the mark the same offset, past it the offset that the glue moved its value to |
| `Id::key` and `Region::seat` | the end of a scope | the durable key's export, and its checked import |

`Region::forks` makes a fork of `Width` children over one frozen prefix. It borrows the parent's mint for the fork's whole life. So the parent makes no id while a child lives, and each id that a child adopts lies in the frozen prefix. Each child holds a suffix of its own, its own mint, its own brand, and an equal share of the parent's remaining budget. The caller's `run` enters each `Child`, on the threads it chooses. A child that the run does not enter runs at the glue, on the calling thread, so each child answers once. A child reads the frozen prefix by reference, so no child copies the prefix or takes a lock.

A body answers `Result<Family::Of<'child>, Dropped>`. An `Ok` keeps the child's suffix, and an `Err` drops it whole with its reason. The reason's type `Dropped` lies outside the child's brand, so no id of the child leaves through it, and `()` is the reason of a drop that names none. The glue appends the suffix of each child that keeps, in the order of the siblings. Each suffix moves past the suffixes before it by a `Shift`. `Rebase` reads each key that a value names through the shift, and `Branded::rebrand` reads each id of the answer through it. The answers come back as `Siblings`, one for each child in the order of the siblings. `Siblings` is never empty, so `Siblings::into_first` is total, and a fork of one child draws no list for its answers.

The one-child fork is the width `Width::ONE`, where the shift moves nothing. A rollback is such a fork. A transaction keeps its suffix on `Ok`. A speculation drops it always: its family is `Infallible`, and its verdict is the reason of the drop.

## The small vector

A `SmallVec<T, N, A>` keeps at most `N` items in place. Past `N`, it keeps all of its items in one block of the allocator `A`, `Global` by default. One word holds the length, and its high bit says where the items live. A union holds the inline array or the block's pointer and capacity, so each access branches once on that bit.

| `N` and `T` | Size | Storage |
| ----------- | ---- | ------- |
| two words of items or fewer | three words | in place up to `N` |
| more than two words of items | one word and the array | in place up to `N` |
| `N` of zero | three words | a plain heap vector |
| a zero-sized `T` | three words | a count, and never a block |

`try_reserve` returns the allocator's refusal as a `Refused`, and the vector stays as it was. A conversion from an array of `N` items has the never type as its error.

## The shared pointer

A `Shared<T, A>` shares one value by a count of holders, on `triomphe`'s design. Its block holds the count and the value, with no weak count. So `make_mut` and `get_mut` load the count once, and a sole holder writes in place. A `Unique<T, A>` builds the value before the share, and `into_shared` makes a `Shared` with no atomic operation.

A `ThinShared<H, T, A>` is one word. Its block holds the count, the length, a header and the items, so a holder of a slice is half the size of a fat pointer.

| Pointer | Holder | Block |
| ------- | ------ | ----- |
| `Shared<T>` | one word | one word and `T` |
| `std`'s `Arc<T>` | one word | two words and `T` |
| `ThinShared<H, T>` | one word | two words, `H` and the items |
| `std`'s `Arc<[T]>` | two words | two words and the items |

The orderings are `std`'s. A `loom` model explores each interleaving of clones, drops and mutable borrows on two and three threads: `RUSTFLAGS="--cfg loom" CARGO_TARGET_DIR=target/loom cargo test -p gandr-kernel-data --test tests --release model`.

## The small string

A `SmallString<A>` holds its text in one of three forms:

| Form | Holds |
| ---- | ----- |
| inline | a text of up to 23 bytes, in the string itself |
| static | a static text, which the string never frees |
| heap | a block of the allocator `A`, of the text's exact length |

The inline form keeps its length, from 0 to 23, as an enum of 24 values. The compiler keeps the form's tag in that byte's other values, so the string and an `Option` of it are 24 bytes for the global allocator. Each read of the text or its length takes one branch on that byte. A borrow of a region is an allocator, so a long text can live in a region. A refusal of the region is a `Refused`, as for the small vector, and never an abort.

The string takes and gives its text as a `Text`, and gives its length as a `ByteLength`. A `Fits` is a text of at most 23 bytes, and its string builds with no refusal to answer. `Clone` copies as a boxed `str` copies, and `try_clone` answers a refusal instead. The one `unsafe` of the type reads the text's bytes as UTF-8.

## References

- `vault:01a178ab-17e5-7352-bc0b-3caa7f1e476c` — anchor: the storage programme (§ storage-programme-region-is-an-allocator) — the region is one allocator with a budget that refuses and never aborts, and a fork's suffix is a region of its own that the join folds or drops.
- `vault:01a1d7fd-eeb5-7010-80e7-df4d768b6583` — anchor: lines 1 to 3 and 5 of the performance picture — a worker owns its region, what is shared is frozen, each crossing is explicit, and what was written apart glues again at the cost of what differs.
