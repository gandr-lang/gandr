# gandr-kernel-check-memo

The check-memo seam: a statically dispatched interface letting a checker skip a question it has already answered in this process, with the storage, the policy, and the lifetime owned outside the checker.

The crate names no term, type, or identifier of its own. A support and an outcome are type parameters, so the certified kernel can depend on this crate without a cycle and no interning table enters the trusted base.

A hit claims exactly one thing: this process already computed this answer for this support. It does not claim the answer is right, that the support was well formed, or that anything was validated. A memo is sound only when the consumer's support is the whole input to the computation it indexes, and the consumer owns that argument.

## Status

New in the reboot, derived from the `kernel-check-memo` crate of the pre-reboot prototype and revised against the ratified normalizer/elaborator plan, the milestones module's `seam-crates`. The plan governs where it and the prototype disagree.

Ref: 01a051fd-253b-7dbc-8cb8-d880c051ad15

Revisions against the prototype, each with its reason:

- **The key carries a content digest and a deciding comparison.** The prototype keyed a `BTreeMap` directly on a consumer-ordered support. The key here is content-derived from the start (the plan's incremental module, `support-is-soundness`), and it carries the digest contract with it: equal digests never decide agreement. `MemoKey` names both the digest and the deciding `agreement`, and `OrderedMemo` buckets by digest and decides by content — so a collision costs one comparison and degrades to a miss, priced strictly as recomputation and never as a wrong answer.
- **A hit carries its support.** `recall` returns a `MemoHit` holding the support the entry was recorded under beside the outcome, so adoption checking is a pointwise comparison of demanded against supplied rather than a footprint intersection.
- **Entry counts are accounted per plane.** A checker running two machines over one shared graph — a goal loop over terms and a formation walk over types — gives each machine its own plane. `entry_count` and `plane_entry_count` sit on the seam trait, so a differential can assert them at either instantiation.
- **Recording answers what it did, and the accounting is checked.** `remember` returns `MemoRecord::{Recorded, Replaced, Discarded}` and a typed `MemoError::EntryCountOverflow`, because the counts are a contract that later milestones assert through rather than telemetry.
- **`non_exhaustive` is dropped.** The workspace is `publish = false` end to end, so the attribute protects no external consumer while costing a wildcard arm at every match — defeating exhaustiveness precisely where a new variant should break every consumer.

Preserved from the prototype without change: the null-object seam with its compile-time activity constant, ordered rather than hashed storage, `no_std` with no dependencies, and the statement of what a hit claims.

## What it provides

- `CheckMemo`, the seam. One trait, an associated `MemoActivity` constant read at compile time, and four operations: `recall`, `remember`, `entry_count`, `plane_entry_count`.
- `NullMemo`, the memo that never answers. Zero-sized, every method a constant, so a consumer instantiated here compiles to the code it would have had with no memo at all. This is the memoless path — the same function at a different type parameter, not a second implementation.
- `OrderedMemo`, the storage half. An ordered map from `ContentDigest` to the bucket of supports that digested to it, plus the per-plane census. Ordered rather than hashed so no hasher enters the kernel's dependency wall and iteration order is deterministic, which is what makes a measurement over the memo re-derivable.
- `MemoKey`, what a consumer's support must supply: an accounting plane, a content digest, and the deciding content comparison.
- `ContentDigest`, `DigestWord`, `ContentAgreement` — the digest and the relation beneath it.
- `MemoEntryCount`, `MemoBucketCount`, `MemoError` — the accounting, with checked arithmetic and a typed refusal at the ceiling.

## The contract attributes

The `# Specification` prose states the item contract; a `#[spec(...)]` attribute mirrors it wherever the clause is a runtime predicate over one call.

Seven items carry one: `MemoEntryCount::successor` (its refusal is exactly the ceiling), `EntryCensus::plane` and `OrderedMemo::plane_entry_count` (a plane's count never exceeds the total), `OrderedMemo::bucket_count` (the bucket count never exceeds the entry count, so a collision is visible as the gap between them), `EntryCensus::record` (both counts move by one on success and neither moves on failure), `OrderedMemo::recall` (a served entry agrees with the demanded support, so no entry selected by digest alone can be served), and `OrderedMemo::remember` (only a fresh record moves the entry count). Anodized evaluates a postcondition after an early `?` return, so the transactional clauses hold on the refusal path too.

`CheckMemo`, `MemoKey` and `MemoKey::agreement` are declarations, where a clause requires the trait itself to carry `#[spec]` and changes what an implementor implements; `ContentDigest` is a data item, where an invariant is never checked at construction. Those blocks carry the reason in their own `- provides:` line, and what they claim is an obligation on the consumer's own relations.

`anodized` supplies core-only specification helpers with default features disabled. The enforcing test lane selects `--cfg anodized_panic` for the whole dependency graph; no logic/BigInt dependency is enabled.

## What it does not provide

- **Eviction, persistence, and any wire format.** Nothing here persists and nothing here is a wire format. A memo's lifetime is the consumer's.
- **The digest function.** The consumer computes the digest from its own canonical content encoding; this crate carries the words and never interprets them.
- **The memo's soundness argument.** This milestone lands the seam. Two instantiations, per-plane accounting on a real checker, and the six binding conditions are consumer obligations and belong to the plan's `kernel-core` milestone.

## Plan and obligations discharged

Milestone: `seam-crates`, the two seam crates in the milestones module.

Ref: 01a051fd-253b-7dbc-8cb8-d880c051ad15

Obligations this crate carries:

- **`obligation-08-the-memoless-path-is-the-same-function`.** Activity is a compile-time constant on a null-object seam; the crate's differential instantiates one walk twice and compares.
- **`obligation-09-the-memo-seam-names-no-term-type`.** Enforced by the generics. Storage is ordered rather than hashed.
- **`obligation-07-a-hit-claims-nothing-but-its-own-history`.** Stated on the trait, and no persistence surface exists to contradict it.
- **`obligation-06-supports-are-judgement-outputs`.** `MemoHit` carries the support the entry was recorded under, which is what makes pointwise adoption expressible at the seam.
- **`obligation-05-keys-are-content-derived-from-day-one`**, with the digest contract riding on the key: a digest is a positive fast path only, and equal digests hand off to the deciding comparison.
- **`obligation-02-differentials-assert-their-exercised-paths`.** The differential asserts expansion counts, hit counts, and entry counts rather than reporting them.
- **`obligation-10-memoize-every-plane-and-assert-per-plane`.** The accounting hook exists here; the two-machine instantiation is the plan's `kernel-core` milestone.

Ref: 01a05203-4468-7931-8246-761a8f853a27

Design context consulted in the proto tracker: `gandr-yvi9.5` (sharing-aware check memoization and the collapse law), `gandr-0bmd` (its residuals, including the unmeasured content-keyed collapse), `gandr-9he0` (the synthesized-context discipline: supports as judgement outputs, content-derived keys), `gandr-ib7m` (the content digest as a fast path with the deciding comparison beneath it), and `gandr-yvi9.2` (replay memoization, whose digest-bucket storage shape this crate's `OrderedMemo` takes).

## Using it

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

Instantiated at `NullMemo` the whole body is a constant-false branch that monomorphization removes.

## Theoretical ideas relied on

Support-keyed memoization, where soundness is exactly the claim that equal supports force equal answers; content-addressed keys, which survive relocation and make cross-declaration reuse reachable; the positive-fast-path digest contract, where a collision degrades to recomputation rather than to a wrong answer; and the null-object seam, which makes the unmemoized path a type parameter rather than a second implementation.

## Primary references

The ratified plan supplies the incremental module's `check-memo-vocab`, `support-is-soundness` and `two-machines-one-memo`, and the milestones module's `seam-crates`.

Ref: 01a051fd-253b-7dbc-8cb8-d880c051ad15

The harvested measurements supply `arc-02-the-storage-shape-and-its-reversal-condition`, `arc-05-the-collapse-law`, `arc-05-the-memo-key`, `arc-05-the-six-binding-conditions`, `successor-synthesized-context`, `successor-content-digest-contract`, and the replicate-from-start obligations cited above.

Ref: 01a05203-4468-7931-8246-761a8f853a27

- Nathanaëlle Courant and Xavier Leroy. "A Lazy, Concurrent Convertibility Checker." _Proceedings of the ACM on Programming Languages_ 10, POPL, Article 53, January 2026. `doi:10.1145/3776695` — §6.3 names process re-sharing by hash-consing as the memo the design asks for, which is a later instantiation of this seam.

## License

Apache-2.0 WITH LLVM-exception.
