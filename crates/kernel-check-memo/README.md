# gandr-kernel-check-memo

The check-memo seam: a statically dispatched interface through which a checker skips a question it has already answered in this process, with storage, policy and lifetime owned outside the checker.

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

**What.** `CheckMemo<Support, Outcome>` is the seam a checker consults before answering a question and records into after. `NullMemo` never answers; `HashedMemo` stores entries keyed by a consumer-supplied support. The crate names no term, type or identifier of its own: support and outcome are type parameters, so the certified kernel depends on this crate without a cycle and no interning table enters the trusted base.

**Why.** A sharing-aware checker meets the same obligation many times over one shared graph, and re-checking each occurrence can cost work exponential in the sharing depth. A memo collapses that to one check per distinct support. Owning the memo outside the checker keeps the checker's own code a single function whose memoless and memoized forms differ only in a type parameter, so the two can be compared directly.

**How.** `CheckMemo` carries an associated `MemoActivity` constant, so a consumer branches on liveness at compile time and the `NullMemo` instantiation compiles to the memoless code. A support implements `MemoKey`: an accounting plane, a `ContentDigest`, and a deciding `agreement` over canonical content. `HashedMemo` keeps its entries densely and files each in a `HashIndex` — open addressing with linear probing and a tag byte per slot — under its digest's hash; the digest narrows the search and `agreement` decides, so a digest collision costs one comparison and degrades to a miss. `recall` returns a `MemoHit` carrying the recorded support beside the outcome; `remember` reports what it did and refuses at the accounting ceiling.

## References

- `Courant-2026-lazy_concurrent_convertibility_checker` — background: Nathanaëlle Courant and Xavier Leroy. "A Lazy, Concurrent Convertibility Checker." _Proceedings of the ACM on Programming Languages_ 10, POPL, Article 53, January 2026. `doi:10.1145/3776695` — §6.3 describes process re-sharing by hash-consing, a memo this seam can carry.

## Provided features

- `CheckMemo`: the seam. One trait, an associated `MemoActivity` constant read at compile time, and four operations: `recall`, `remember`, `entry_count`, `plane_entry_count`.
- `NullMemo`: the memo that never answers. Zero-sized, every method a constant.
- `HashedMemo`: the storage half. Dense entries filed by digest hash, plus the per-plane census and `bucket_count`.
- `HashIndex`, `TableHash`, `TablePosition` and `WordHasher`: the open-addressing index and its fixed-seed hash, which the kernel's interning, reach caches and rewrite memo file on too.
- `MemoKey`: what a support supplies — an accounting plane, a content digest and the deciding content comparison.
- `ContentDigest`, `DigestWord` and `ContentAgreement`: the digest and the relation beneath it.
- `MemoHit`: a served entry, the outcome together with the support it was recorded under.
- `MemoRecord`: what `remember` did — `Recorded`, `Replaced` or `Discarded`.
- `MemoEntryCount`, `MemoBucketCount` and `MemoError`: the accounting, with checked arithmetic and a typed refusal at the ceiling.

## Expected features

- **A complete support.** A memo is sound only when the consumer's support is the whole input to the computation it indexes. If two calls with equal supports could differ, the memo is a defect no property of this crate can rescue; the consumer owns that argument.
- **The digest function.** The consumer computes the digest from its own canonical content encoding, and `MemoKey::agreement` decides over that same content. The crate carries digest words and never interprets them.
- **A lifetime.** The memo lives as long as the consumer holds it. Nothing persists, nothing is evicted, and nothing is a wire format.
- **`--cfg anodized_panic` for enforcement.** Built with this `cfg` across the whole dependency graph, the `#[spec]` attributes check their clauses at runtime and panic on a violation. The enforcing test lane sets it.

## Examples

A consumer supplies its own support and outcome, and writes one walk generic in the memo.

```rust
use gandr_kernel_check_memo::CheckMemo;
use gandr_kernel_check_memo::MemoActivity;

fn answer<Memo, Support, Outcome>(support: Support, memo: &mut Memo) -> Option<Outcome>
where
    Memo: CheckMemo<Support, Outcome>,
    Support: gandr_kernel_check_memo::MemoKey,
    Outcome: Copy,
{
    if matches!(Memo::ACTIVITY, MemoActivity::Inactive) {
        return None;
    }
    let hit = memo.recall(&support)?;
    Some(*hit.outcome())
}
```

Instantiated at `NullMemo`, the whole body is a constant-false branch that monomorphization removes.

`tests/differential.rs` instantiates one walk over a shared arena at both memos and asserts outcome agreement, the expansion counts in closed form per plane, the hit and entry counts, and that the shared and unshared spellings cost the memoless walk identically. Run it with the unit tests, then the enforcing twin:

```sh
cargo nextest run -p gandr-kernel-check-memo
RUSTFLAGS="--cfg anodized_panic" cargo nextest run -p gandr-kernel-check-memo
```

## Where the detail lives

The seam's items, the hit and digest boundaries, the dependencies and the specification witnesses are stated in [`src/lib.rs`](src/lib.rs); each operation's obligation is on its item in [`src/memo.rs`](src/memo.rs), [`src/table.rs`](src/table.rs), [`src/key.rs`](src/key.rs), [`src/digest.rs`](src/digest.rs) and [`src/accounting.rs`](src/accounting.rs).

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
