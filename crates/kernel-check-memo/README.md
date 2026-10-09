# gandr-kernel-check-memo

The check-memo seam: a statically dispatched interface through which a checker skips a question it has already answered in this process, with storage, policy and lifetime owned outside the checker.

<!-- toc -->

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [What a hit claims](#what-a-hit-claims)
- [Digest and agreement](#digest-and-agreement)
- [Static dispatch](#static-dispatch)
- [Per-plane accounting](#per-plane-accounting)
- [Ordered storage](#ordered-storage)
- [Exhaustive matching](#exhaustive-matching)
- [Contract attributes](#contract-attributes)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** `CheckMemo<Support, Outcome>` is the seam a checker consults before answering a question and records into after. `NullMemo` never answers; `OrderedMemo` stores entries keyed by a consumer-supplied support. The crate names no term, type or identifier of its own: support and outcome are type parameters, so the certified kernel depends on this crate without a cycle and no interning table enters the trusted base.

**Why.** A sharing-aware checker meets the same obligation many times over one shared graph, and re-checking each occurrence can cost work exponential in the sharing depth. A memo collapses that to one check per distinct support. Owning the memo outside the checker keeps the checker's own code a single function whose memoless and memoized forms differ only in a type parameter, so the two can be compared directly.

**How.** `CheckMemo` carries an associated `MemoActivity` constant, so a consumer branches on liveness at compile time and the `NullMemo` instantiation compiles to the memoless code. A support implements `MemoKey`: an accounting plane, a `ContentDigest`, and a deciding `agreement` over canonical content. `OrderedMemo` is an ordered map from digest to the bucket of supports that produced it; the digest selects a bucket and `agreement` decides within it, so a digest collision costs one comparison and degrades to a miss. `recall` returns a `MemoHit` carrying the recorded support beside the outcome; `remember` reports what it did and refuses at the accounting ceiling.

## References

- Nathanaëlle Courant and Xavier Leroy. "A Lazy, Concurrent Convertibility Checker." _Proceedings of the ACM on Programming Languages_ 10, POPL, Article 53, January 2026. `doi:10.1145/3776695` — §6.3 describes process re-sharing by hash-consing, a memo this seam can carry.

## Provided features

- `CheckMemo`: the seam. One trait, an associated `MemoActivity` constant read at compile time, and four operations: `recall`, `remember`, `entry_count`, `plane_entry_count`.
- `NullMemo`: the memo that never answers. Zero-sized, every method a constant.
- `OrderedMemo`: the storage half. An ordered map from `ContentDigest` to its bucket of supports, plus the per-plane census and `bucket_count`.
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

## What a hit claims

A hit claims exactly one thing: this process already computed this answer for this support. It does not claim that the answer is right, that the support was well formed, or that anything was validated.

A hit carries its support. `MemoHit` hands back the support the entry was recorded under beside the outcome, so a consumer checking adoption compares demanded against supplied pointwise rather than intersecting footprints.

## Digest and agreement

A key is content-derived, so it survives relocation and two equal obligations key equally wherever they arise. The digest is a positive fast path and never a decision: different digests prove disagreement, and equal digests hand off to `MemoKey::agreement`. A collision therefore costs one comparison and is priced as recomputation, never as a wrong answer.

## Static dispatch

`MemoActivity` is an associated constant, so liveness is known at compile time. Under `NullMemo` every memo interaction, support construction included when the consumer guards it, is a constant-false branch, and the consumer compiles to the code it would have with no memo at all. The memoless path is the same function at a different type parameter, which is what makes a memoless-against-memoized differential meaningful.

## Per-plane accounting

A checker running two machines over one shared graph, such as a goal loop over terms and a formation walk over types, gives each machine its own plane. `entry_count` and `plane_entry_count` sit on the seam trait, so a differential asserts the collapse of each plane separately at either instantiation.

The counts are a contract that consumers assert through, so they use checked arithmetic. `remember` returns a `MemoRecord` and refuses with `MemoError::EntryCountOverflow` at the ceiling, leaving the memo as it was.

## Ordered storage

`OrderedMemo` uses ordered maps rather than hashed ones. No hasher enters the kernel's dependency wall, and iteration order is deterministic, so a measurement over the memo is re-derivable.

## Exhaustive matching

No enum here is `#[non_exhaustive]`. The workspace does not publish, so the attribute would protect no external consumer while forcing a wildcard arm at every match and defeating exhaustiveness exactly where a new variant should break every consumer.

## Contract attributes

The `# Specification` prose states the obligation; `#[spec(...)]` mirrors clauses that can be checked over one call. Each nontrivial item has a `# Adequacy` hypothesis naming the bounded evidence and the deviations its observer distinguishes.

- Checked arithmetic specifies the exact successor, per-plane lookup and overflow refusal, including unchanged accounting on failure.
- Ordered storage specifies digest-bucket lookup, support agreement, insertion versus replacement, and unchanged counts on refusal. Collision and ceiling tests also observe retained answers, rather than counts alone.
- The differential workload specifies its arena topology, framed content identity, folds and census arithmetic. Closed-form counts and ordinary versus memoized runs distinguish missing work from reused work.

Anodized evaluates postconditions after early `?` returns, so refusal paths are included. Production predicates capture scalar counts and membership facts, not owned snapshots; additional predicate traversals run only when enforcement is enabled.

A final `- executable: none` clause identifies the remaining data, declaration or external-context obligation. Instrumenting `CheckMemo` or `MemoKey` declarations would change the implementation interface; data-item expansion does not check construction. The bounded witnesses exercise the shipped implementations and fixture relations. They do not certify arbitrary consumer implementations of the semantic agreement laws.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
