# gandr-boot-core

The operations of the bootstrap on a range of bytes, which allocate nothing: a copy, a move, a fill, a comparison, two searches, and the checks of UTF-8 and of a zero byte.

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

**What.** Each function takes each range as an address and a length. A `Range` is a range that the function reads, and a `Place` is a range that it writes. `copy` and `move_bytes` write a source into the start of a place, and a place that is too short gets `Short`. `fill` writes one byte to each byte of a place. `compare` orders two ranges by their first unequal byte. `find_byte` and `find_range` give a `Found`: the first position of a match, or an absence. `check_utf8` gives `Utf8::Valid` or the position of the first fault, and `find_zero` finds the end of a C string.

**Why.** The data core of the bootstrap needs these operations before gandr states them itself. Rust's own operations are generic or take slices, so the direct call of Rust cannot name them. The line between this crate and `boot-data` is the allocation: this crate allocates nothing. A crate of the layer `boot` is a stage of the bootstrap, and a twin in gandr replaces it.

**How.** Each function is `unsafe`, because its caller states that each range is live. A move takes two ranges that can share bytes, so a reference of Rust cannot hold them. An empty range can have any address, null too, and no function reads it. Each function reads or writes its ranges alone. The copies, the fill and the comparison go through the operations of Rust's `core`. The check of UTF-8 goes through `core::str::from_utf8`. No function panics, and the crate is `no_std`.

## References

- `vault:01a1ebc5-2ff2-7833-b871-85901e734925` — newest: the data core of the bootstrap (§ boot-data-crates, § boot-data-strings) — the rules of a crate of the layer `boot`, the line of the allocation between this crate and `boot-data`, and the two invariants of a string as checks over bytes.

## Provided features

- `copy` and `move_bytes`: a source into the start of a place, with ranges that share no byte or that can share bytes, and `Short` for a place that is too short.
- `fill`: one `Byte` into each byte of a place.
- `compare`: the order of two ranges, by the first unequal byte and then by the length.
- `find_byte` and `find_range`: the first position of a byte or of a range, as a `Found`.
- `check_utf8` and `find_zero`: the first fault of UTF-8 as a `Utf8`, and the first zero byte as a `Found`.
- `Range`, `Place`, `Length`, `Position` and `Byte`: the ranges and the numbers of the face, each of `repr(C)` or `repr(transparent)`.

## Expected features

- **Live ranges from the caller.** The bytes of each range that is not empty are live for the call, and no other write to them happens during it.
- **Ranges of a place that share no byte in a copy.** A caller with ranges that can share bytes calls `move_bytes`.

## Examples

The witnesses run each function against one table of subjects, so a twin in gandr runs against the same cases. A range that ends at the end of a page has a next page with no access, so a read past its end faults. Each function reads such a range, and the copy, the move and the fill also write one.

```sh
cargo test -p gandr-boot-core
```

## Where the detail lives

`src/lib.rs` states the face; `src/block.rs` the copy, the move, the fill and the comparison; `src/search.rs` the two searches; `src/check.rs` the check of UTF-8 and the zero byte.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
