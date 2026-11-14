# gandr-kernel-data

The kernel's own data types. The crate is `no_std` over `core` and `alloc`, and depends on no other workspace crate, so both chains reach it as a leaf.

## The region

A `Region` holds values under a budget, and refuses a value past it. A scope, `scoped`, brands the region and hands its body one `Mint`. Each id takes the mint, so no id leaves the scope.

Three crossings move an id between regions, and nothing else does:

| Crossing | Where | Form |
| -------- | ----- | ---- |
| `Adopt::adopt` | a fork | the parent's id, read as the child's: the id itself |
| the fold's translation | a join | the child's id, read as the parent's at the same offset |
| `Id::key` and `Region::seat` | the end of a scope | the durable key's export, and its checked import |

`Region::fork` borrows the parent's mint for the fork's whole life. So the parent makes no id while a child lives, and each id that a child adopts lies in its frozen prefix. A body that answers `None` drops the child's suffix whole. A body that answers `Some` folds the suffix into the parent at the offsets the child minted it at.
