# gandr-kernel-term

The kernel's term arena and sharing format: a flat, id-addressed arena with constructor-only minting and an admission watermark, the unified subterm-table encoding over it, canonical decode with a sharing-aware re-encoder, and the decode-time budgets that stop a small artifact from costing an unbounded amount of downstream work.

It holds **representation and bytes only** — no checker, no conversion, no environment, no admission choke point. It is `no_std` over `core` and `alloc` and depends on `gandr-kernel-strata` alone, which is the shape of the trusted base's dependency wall.

## Plan-milestone mapping

This crate is the second half of the `kernel-term` milestone of the ratified normalizer-and-elaborator plan, its milestones module; the first half is `gandr-kernel-strata`, which landed before it. The milestone's scope maps onto the modules one to one:

| plan clause | where it lives |
| ----------- | -------------- |
| the arena with constructor-only minting and the admission watermark | `src/arena.rs` |
| the four typed id families | `src/arena.rs`, over the node vocabularies in `src/term.rs` and `src/types.rs` |
| the tag table as a const protocol input | `src/tags.rs` |
| canonical encode, with the sharing-aware re-encoder | `src/encode.rs` |
| canonical decode and its rejection vocabulary | `src/decode.rs`, `src/error.rs` |
| the four amplification budgets in one forward scan | `src/budget.rs`, scanned in `src/decode.rs` |

Ref: 01a051fd-253b-7dbc-8cb8-d880c051ad15

The design page of record for the whole cluster governs where the plan defers to it: the arena and its four id families, the unified maximally-shared subterm table, the frozen tag block, the four budget constants and their floor argument, the canonical-form conditions, and the version-refusal posture are all that page's decisions.

Ref: 01a051fd-25fd-7f24-a5d4-a72eca18a687

The milestone's acceptance is the rejection suite, and it is complete: `tests/sharing_format.rs` carries the sharing round trip with sharing asserted at the shared nodes, the sharing determinism over two differently shared equal inputs, the four canonical-form refusals, the two amplification goldens, the boundary goldens derived from the constants, and the version refusal; `tests/adversarial_depth.rs` carries the teardown witness inside a small-stack thread.

## Status

Split out of the pre-reboot prototype's `kernel-core`, which held the whole trusted base in one crate, and revised against the reboot constraints. The split is the plan's own deviation from the standing preference for prototype crate names, and its reason is that the memo's support type and the conversion trace's identifier type both need the term vocabulary without needing a checker — so the arena, the format and the amplification defence land under the type-plane gate before any checking code exists.

The revisions, all constraint-driven:

- **The format plane is separated from the export path.** The prototype's writer and reader took an `Environment` and replayed declarations through the admission choke point. Here the encoder takes an arena and a marked declaration sequence, and the decoder returns one; the environment, admission and replay belong to `kernel-core` and consume this surface rather than living inside it.
- **No bare primitives at a signature.** The prototype's wire constants, budget constants and tag-table fields were bare `u8`, `u64` and `usize`. Every one now crosses a nominal boundary — `WireTag`, `ExpandedWork`, `TableEntryCount`, `GlobalIndex`, `LevelAtomOffset`, `ChildArity`, `TokenCount`, `FormatVersion` — and a signature reaches a primitive nowhere, the test suites included.
- **A declaration no longer carries a watermark it cannot use.** The prototype stored each declaration's content-start mark on the declaration itself, which a decoded declaration cannot meaningfully hold, since decode builds one table for the whole artifact. The builder still records the mark and still rolls the arena back when it is abandoned; a choke point takes its own mark.
- **The reserved-slot vocabulary says what it means.** The prototype refused a refuted minted-atom table under a variant whose name and message said the slot was "non-empty at v0", which described neither the version nor the failure. The slot family now states that one of its members is live and refuted rather than merely required to be empty.
- **References resolve away from their original artifact.** Bare letter-number invariant labels, section numbers and tracker identifiers are gone; where a claim needs a source, it is stated in full at the point of use.

Everything already conformant in the prototype is preserved: no recursion of any kind, transparent newtype wrappers, no `as` casts, checked or saturating arithmetic throughout, typed errors with no `unwrap`, `expect` or `panic` outside tests, and constructor-only minting so a dangling id is impossible within an arena.

## What it provides

- **A flat arena in four typed id families** — values, computations, value types and computation types — where a node's children are `Copy` ids rather than owned pointers. Teardown is a flat vector drop and the derived equality, hashing and debug instances are shallow, which is what retires the hand-written iterative destructor an owned-tree representation needs. Ids are minted only by constructors over already-allocated children, so a child id is always strictly less than its parent's.
- **The admission watermark**: a snapshot of the four family lengths, a truncation back to one, and the clamp a rollback needs when staging order is not admission order. A declaration builder ties content minting to it, so an abandoned build rolls back structurally rather than by remembering to.
- **The unified subterm table**: one per-artifact tagged table over all four families in a single index space, maximally shared under structural equality, declaration-segmented, with children referenced only by strictly earlier index in post-order first-completion order. Polarity is recoverable from the tag alone, so a child slot's requirement is a table lookup.
- **Canonical form enforced by re-encoding.** The encoder is untrusted and feeds no judgement; what enforces canonical form is a whole-artifact re-encode-compare on the reading side, and the maximal-sharing encoder _is_ the re-encoder. That one mechanism catches a redundant duplicate entry, a mis-ordered table and a dead entry. The re-encoder is itself sharing-aware, without which the canonical check would be an amplification vector rather than a defence.
- **The amplification defence**: the entry cap enforced as entries accrue, the per-declaration and artifact-total expanded-work caps off one forward scan of memoized saturating sizes, and the level-offset cap at the level decoder. The same scan yields deterministic metrics a caller can record as telemetry.
- **The node-tag table as a const protocol input**: one row per frozen tag with its child arity and its two storage-boundary verdicts, pinned against the arena's own child relation by a differential rather than by a comment.

## The contract attributes

The `# Specification` prose stays the statement of record; a combined `#[spec(...)]` attribute mirrors it where the clause is a cheap runtime predicate. Six items carry one:

- `check_budget` — acceptance exactly when both expanded-work caps hold, stated as one conjunction against the body's two sequential guards, at the point where the amplification defence binds;
- `EncodedArtifact::put_uvarint` and `ArtifactImage::span` — the terminator half of varint minimality, and the in-bounds condition of every adversarial read;
- `LevelSignature::new`, `DeclarationBuilder::sealed_def` and `DeclarationBuilder::abstract_type` — each pinning the content variant and the slot arity its finisher promises, which is what separates four adjacent finishers that differ only in a variant.

Two do not, and say so at the site. `TermArena::truncate_to` is the sharper refusal: `self.watermark() == watermark` is exactly the postcondition _under the precondition_, but the `- fails:` clause admits a stale watermark past the end as a documented no-op, so the predicate would turn that no-op into a panic. `TermArena::children_of` is skipped because the "strictly less than the node's own id" half is only defined within one family, and because it is the edge relation every walk over the arena runs.

`anodized` supplies core-only specification helpers with default features disabled. The enforcing test lane selects `--cfg anodized_panic` for the whole dependency graph; no logic/BigInt dependency is enabled.

## Not provided

No interning table, no content-keyed memo of values, and no sharing-creating pass: sharing is preserved by the kernel and never created, so what a decode hands over is the sharing a consumer sees, and id equality is a positive-only fast path deciding reflexive pairs alone. Compression lives outside the format — the canonical bytes remain the bytes, and a codec inside a reader would muddy a rejection vocabulary that has to stay clean.

Two capabilities a consumer will want are deliberately left to the crate that needs them rather than speculated here: grafting a decoded sub-DAG into another arena, which the admission path needs and this crate has no caller for, and the per-declaration byte-segment offsets an outer content-addressed layer would chunk on. The bytes are already declaration-segmented and self-delimiting; only the projection is absent.

The tag space above the frozen block is settled in one pass rather than claim by claim. The frozen block runs contiguously from zero through the universe-decoding former's own tag; the bytes between it and `0x20` are growth room for the core vocabulary; and `0x20` through `0x27` are reserved for a stored sharing plane — one sharing former per family, so polarity stays recoverable from the tag alone, plus held room for an explicit weakening form. The reserved block carries no former yet, and a decoder meeting one of its bytes refuses it by name exactly as it refuses any other unassigned byte. Settling the block rather than numbering it on demand is what keeps the core vocabulary from growing into it: the core grows through the growth room and resumes above the block.

## Using it

`cargo test -p gandr-kernel-term --all-targets` runs the suite. Consumers reach the crate through the kernel rather than directly.

```rust
use gandr_kernel_term::AdmissionMark;
use gandr_kernel_term::DeclarationBuilder;
use gandr_kernel_term::LevelSignature;
use gandr_kernel_term::MarkedDeclaration;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::decode;
use gandr_kernel_term::encode;

fn example() {
    let mut arena = TermArena::new();
    let declared = arena.value_type_unit();
    let unit = arena.value_unit();
    let body = arena.value_pair(unit, unit);
    let builder = DeclarationBuilder::new(&mut arena);
    let declaration = builder.def(LevelSignature::monomorphic(), declared, body);
    let sequence = [MarkedDeclaration::new(AdmissionMark::Checked, declaration)];

    let bytes = encode(&arena, &sequence);
    let artifact = decode(bytes.as_image()).expect("the artifact is canonical");
    assert_eq!(1, artifact.declarations().len());
}
```

## Theoretical ideas relied on

Hash-consing under structural equality as a canonical form for a stored term, which is what makes the bytes a function of the abstract environment rather than of decode history; the transactional staging overlay, where a checker's intermediates allocate past a mark and are truncated after the verdict on both verdicts alike; and the reading of a decoder's acceptance as a bounded-work guarantee, so that a defence against exponential expansion lives at an import boundary and takes no table into the trusted base.

## Primary references

- Simon L. Peyton Jones. _The Implementation of Functional Programming Languages_. Prentice Hall, 1987. `isbn:978-0134533339` — the graph representation and maximal sharing this format's stored plane realizes statically. Locator unverified: the ISBN identifies a printing and has not been checked against a title page.
- Nathanaëlle Courant and Xavier Leroy. "A Lazy, Concurrent Convertibility Checker." _Proceedings of the ACM on Programming Languages_ 10 (POPL), Article 53, January 2026. `doi:10.1145/3776695` — §6.4 builds, as a pre-pass, the hash-consed subterm DAG this format hands a consumer already built, which is why the transcription is a pass over a table rather than a pre-pass of its own.

## License

Apache-2.0 WITH LLVM-exception.
