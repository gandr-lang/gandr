# gandr-runtime-rust-record

The record of a Rust function as rustc builds it: its symbol, the passage of each operand and the layout of each type of its signature, under the toolchain's identity.

<!-- toc -->

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** A call from gandr into a Rust function must name the function's symbol and pass each operand as rustc passes it. That convention and each layout are rustc's own answers for one toolchain and one target, and no stable interface states them. This crate holds those answers as a `Record`, gives the record one canonical byte form, and keeps each record in a cache. It links no library of rustc. The reader, `runtime-rust-reader`, computes each record.

**Why.** Each request of the same crate on the same toolchain has the same answer. The cache gives that answer from an entry and starts no process. An entry holds the digest of each source that rustc read, so an edit of a source reads the crate again. The record refuses another toolchain's entry or another target's entry by name.

**How.** `Cache::read` names an entry by the BLAKE3 digest of the identity, the reader program's size and modification time, and the request. A hit hashes each source of the entry again. A miss runs the reader with the build's command line for the crate, word for word, and the reader puts each output of its run in a scratch directory. The cache decodes the entry that the reader writes and publishes it whole with `core-publish`. The decoder bounds each count by the bytes that remain, so a damaged entry is refused and never allocates past its length.

## References

- `vault:01a1e7b4-8c77-7a81-9165-ff37ea870424` — newest: a call into Rust uses rustc's own record of the function, never a guess from its source (§ io-direction-interop).

## Provided features

- `Request`: the build's arguments to `rustc` for the crate, word for word, and the paths of the functions. Cargo adds its own `-C metadata` value to each crate, and that value enters each symbol.
- `Record`: the `Identity` (the toolchain's commit and the target) and the `Outcome`, each requested `Function` or each `Refusal`.
- `Function`: the path, the `Linkage`, and an `Operand` for each argument and for the result. An operand is its `Passage` and its `Layout`.
- `Linkage`: the v0 `Symbol`, or `Absent` with its `Absence`. `Inlined` is a function that the build copies into each caller, so its object holds no symbol of it.
- `Passage`: `Ignore`, `Direct`, `Pair`, `Cast`, `Indirect` or `OnStack`. Each `Part` is an LLVM type, as rustc's LLVM backend spells it, and an `Extension`.
- `Layout`: the size, the stride, the alignment, the largest niche and the `Shape`. A struct's shape is each field at its offset. An enum's shape is its `Discriminant` and the fields of each arm.
- `Refusal`: `Generic`, `NotPublic`, `Missing`, or `Unstated` with the type and the `Unstatable` cause. Each refusal displays its function and its cause.
- `Entry::encode` and `Entry::decode`: the canonical bytes of the sources and the record. `Undecoded` names the first fault.
- `Cache::read`: an `Answer` with its `Origin`, `Cache` or `Process`, or an `Unread` that names the fault.

## Expected features

- **The reader at the build's toolchain.** `Identity::of_build` is the toolchain that built this crate. A reader on another toolchain writes an entry that the cache refuses.
- **A consumer that links by symbol refuses an absent symbol.** A small `pub fn` under `-C opt-level=3` has no symbol. The record states that, and the consumer that links by symbol refuses the function as `Inlined`.
- **A type of known layout.** An unsized type, an uninhabited type, an array and a union are refused as `Unstated`.

## Examples

```rust
use gandr_runtime_rust_record::Entry;
use gandr_runtime_rust_record::Identity;
use gandr_runtime_rust_record::Outcome;
use gandr_runtime_rust_record::Record;

let identity = Identity::of_build();
let entry = Entry { sources: Vec::new(), record: Record { identity: identity.clone(), outcome: Outcome::Read(Vec::new()) } };
let bytes = entry.encode();
assert_eq!(Entry::decode(bytes.as_encoded(), &identity), Ok(entry));
```

The tests run as below, the second line the enforcing twin that checks every specification. `check:rust-record` runs the reader's tests, which read real crates.

```sh
cargo nextest run -p gandr-runtime-rust-record
RUSTFLAGS="--cfg anodized_panic" cargo nextest run -p gandr-runtime-rust-record
```

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
