# gandr-kernel-data

The kernel's own data types. The crate is `no_std` over `core` and `alloc`, and depends on no other workspace crate, so both chains reach it as a leaf.

## The region

A `Region` holds values under a budget, and refuses a value past it. A scope, `scoped`, brands the region and hands its body one `Mint`. Each id takes the mint, so no id leaves the scope.

A region holds the values of one or more families in one id space. An id `Id<'r, Kind>` names its family by a phantom kind, so an id of one family does not stand for an id of another. A region of one family takes the kind `()`.

Three crossings move an id between regions, and nothing else does:

| Crossing | Where | Form |
| -------- | ----- | ---- |
| `Adopt::adopt` | a fork | the parent's id, read as the child's: the id itself |
| `Translation::translate` | a join | the child's id, read as the parent's at the same offset |
| `Id::key` and `Region::seat` | the end of a scope | the durable key's export, and its checked import |

`Region::fork` borrows the parent's mint for the fork's whole life. So the parent makes no id while a child lives, and each id that a child adopts lies in its frozen prefix. A body that answers `None` drops the child's suffix whole. A body that answers `Some` folds the suffix into the parent at the offsets the child minted it at.

## The small vector

A `SmallVec<T, N, A>` keeps at most `N` items in place. Past `N`, it keeps all of its items in one block of the allocator `A`, `Global` by default. One word holds the length, and its high bit says where the items live. A union holds the inline array or the block's pointer and capacity, so each access branches once on that bit.

| `N` and `T` | Size | Storage |
| ----------- | ---- | ------- |
| two words of items or fewer | three words | in place up to `N` |
| more than two words of items | one word and the array | in place up to `N` |
| `N` of zero | three words | a plain heap vector |
| a zero-sized `T` | three words | a count, and never a block |

`try_reserve` returns the allocator's refusal as a `Refused`, and the vector stays as it was. A conversion from an array of `N` items has the never type as its error.

## References

- `vault:01a178ab-17e5-7352-bc0b-3caa7f1e476c` — anchor: the storage programme (§ storage-programme-region-is-an-allocator) — the region is one allocator with a budget that refuses and never aborts, and a fork's suffix is a region of its own that the join folds or drops.
- `vault:01a1d7fd-eeb5-7010-80e7-df4d768b6583` — anchor: lines 1 to 3 of the performance picture — a worker owns its region, what is shared is frozen, and each crossing is explicit.
