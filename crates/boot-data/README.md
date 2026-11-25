# gandr-boot-data

The data of the bootstrap that allocates: a vector of bytes and a string buffer over the heap of `boot-alloc`.

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

**What.** A `Vector` holds bytes in a block of one `Heap` of `boot-alloc`: a capacity, a length, and one owner. `push` writes one byte after the last byte, `append` copies a `Range` of `boot-core` after it, and `truncate` keeps the first bytes. `reserve` makes room before the writes. `range` gives the bytes as a `Range`, so each operation of `boot-core` reads them, and `byte` reads one byte. The end of a vector gives its block back to the heap, and `release` does the same and gives the answer of the heap. A `StringBuffer` is a vector whose bytes are valid UTF-8, with one zero byte after the last byte: `append` checks its bytes before it writes them, `from_vector` checks the bytes of a vector, `range` gives the text, `terminated` gives the text and the zero, and `into_vector` gives the bytes back with no copy.

**Why.** The data core of the bootstrap needs an owner of bytes that grows before gandr states one itself. Rust's vector is generic over its element and its allocator, so the direct call of Rust cannot name it. The line between this crate and `boot-core` is the allocation: this crate allocates. A crate of the layer `boot` is a stage of the bootstrap, and a twin in gandr replaces it.

**How.** A growth asks the heap for twice the capacity, or for the bytes that the growth needs when they are more, and at least 16 bytes, the smallest size class. The heap moves the bytes that stand. The capacity is each byte that the heap grants, so a block of a size class is used whole. A growth past the size of a layout gives `Refusal::Size`, and a growth that the heap refuses gives `Refusal::Heap`. In each case the vector keeps its bytes. The string buffer runs `check_utf8` of `boot-core` at each way in, and bytes that are not UTF-8 get `Rejected::Utf8` with the position of the first fault, with the buffer unchanged. A buffer with no byte holds no block, and its bytes with the zero are one static zero byte. No function panics, each public function has no type parameter, and the crate is `no_std`.

## References

- `vault:01a1ebc5-2ff2-7833-b871-85901e734925` — newest: the data core of the bootstrap (§ boot-data-crates, § boot-data-sequences and § boot-data-strings) — the rules of a crate of the layer `boot`, the line of the allocation between this crate and `boot-core`, a vector as a capacity, a length and one linear owner, and an owner of a string as the same vector with a proof of UTF-8 and one zero byte after its last byte.

## Provided features

- `Vector`: a vector of bytes in a block of one heap, with `new`, `reserve`, `push`, `append`, `truncate`, `range`, `byte`, `length`, `capacity` and `release`.
- `Refusal`: a growth past the size of a layout, or one that the heap refuses.
- `StringBuffer`: a vector of valid UTF-8 with one zero byte after it, with `new`, `append`, `from_vector`, `into_vector`, `range`, `terminated`, `length` and `release`.
- `Rejected` and `Unchecked`: bytes that are not UTF-8 or a growth that the vector cannot make, and a vector that comes back with its cause.

## Expected features

- **One heap for each vector.** A vector lives no longer than its heap, and a heap is one thread's.
- **A range that is not the vector's own.** The bytes that `append` copies are no bytes of the block of the vector.

## Examples

The witnesses push 100,000 bytes through each size class of the heap and whole pages, and read each one back. They keep the block of a room within the capacity, refuse a room past the size of a layout with the vector unchanged, append after pushed bytes, cut, and release a block of whole pages. The witnesses of the string buffer append sequences of one to four bytes past one size class with a zero after each append, reject a byte that starts no sequence, a surrogate and a cut sequence at the position of the fault, and make a buffer of a vector and a vector of a buffer with no copy.

```sh
cargo test -p gandr-boot-data
```

## Where the detail lives

`src/lib.rs` states the face; `src/vector.rs` the vector, its growth and its refusal; `src/string.rs` the string buffer and its check of UTF-8.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
