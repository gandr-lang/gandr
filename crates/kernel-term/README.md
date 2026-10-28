# gandr-kernel-term

The kernel's term arena and sharing format: a flat, id-addressed arena, the unified subterm-table encoding over it, canonical decode, and the decode-time budgets that bound the work a small artifact can cost.

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

**What.** `TermArena` holds the kernel's terms and types in four typed id families: values, computations, value types and computation types. `encode` writes an arena and a sequence of marked declarations as one canonical artifact; `decode` reads an artifact back into a fresh arena, refusing anything malformed, non-canonical or over budget with a typed `DecodeError`. The crate holds representation and bytes only: the checker, conversion, the environment and the admission choke point live in `gandr-kernel-core` and consume this vocabulary. It is `no_std` over `core` and `alloc` and depends on `gandr-kernel-strata` alone among workspace crates.

**Why.** A kernel that checks large proofs needs shared subterms to stay shared from the bytes to the checker, or every reference to a shared subterm costs its full size again. Retaining that sharing is also an attack surface: a small artifact can name a DAG whose tree-expanded size is astronomical, so a reader must bound expanded work before anything downstream sees the artifact, without trusting the writer.

**How.** Four decisions interlock — an arena of `Copy` ids, one maximally shared subterm table per artifact, decode that retains sharing, and budgets on expanded work — and [`src/lib.rs`](src/lib.rs) states why none of them can be decided alone.

## References

- Simon L. Peyton Jones. _The Implementation of Functional Programming Languages_. Prentice Hall, 1987. `isbn:978-0134533339` — the graph representation and maximal sharing this format's stored plane realizes statically.
- Nathanaëlle Courant and Xavier Leroy. "A Lazy, Concurrent Convertibility Checker." _Proceedings of the ACM on Programming Languages_ 10 (POPL), Article 53, January 2026. `doi:10.1145/3776695` — §6.4 builds the hash-consed subterm DAG as a pre-pass; this format hands a consumer that DAG already built, so transcription is a pass over a table.
- `vault:01a12317-453f-7980-9c86-68f75917f3a6` — lineage: the bicontextual core (§ codebruijn-carrier, § footprint-from-support) — what a node mentions is a function of its content, so its support is computed once, when the node is minted, and carried.
- `vault:01a178aa-6917-7983-b5cd-86e2af86b3ec` — lineage: the kernel re-assessment's design (§ kernel-reassessment-design items 1 and 3) — the kernel derives every support from its own nodes rather than taking one across the bridge.
- `vault:01a178aa-a07b-7a23-bbcd-cf3893ccc160` — background: the effect-modalities design (§ The declaration) — a presentation may declare a sort classified `Type[-]`.
- `vault:01a178aa-ce14-7610-bcad-5aab5f9c0b0f` — background: § kernel-verdict-reuse — a verdict key reads each declaration's canonical segment.
- `vault:01a178aa-d585-7822-9cf0-40459729a925` — background: § module-sealing-landed-sealing-rung — an atom is fresh within its artifact alone, so a decoded artifact goes whole to one replay.

## Provided features

- **A flat arena in four typed id families** (`ValueId`, `ComputationId`, `ValueTypeId`, `CompTypeId`) where a node's children are `Copy` ids, minted only by constructors over already-allocated children.
- **A support carried on every node** (`Reads`, read by `TermArena::value_support` and its three siblings): the free de Bruijn indices the node mentions, computed from its children's supports when it is minted, so no consumer walks a term to learn which binders it reads.
- **The admission watermark** (`ArenaWatermark`) and `DeclarationBuilder`, which ties content minting to it so an abandoned declaration truncates itself.
- **The unified subterm table**: `encode` and `decode` over `EncodedArtifact` and `ArtifactImage`, with `DecodedArtifact` holding the arena and its `MarkedDeclaration` sequence, and `SegmentLayout` reporting each declaration segment's boundaries. `encode_prefix` and `encode_after` resume an encoding after a leading run of declarations (`EncodedPrefix`), and `decode_keeping` and `decode_after` a decode (`DecodedPrefix`), each answering as the whole one does; `SegmentEncoder` writes the segments one declaration at a time, as the kernel's verdict key reads them.
- **Structured names** (`StructuredName`, `NameSegment`) on every declaration.
- **Canonical form enforced by re-encoding**, and **the amplification defence**: `MAX_TABLE_ENTRIES`, `MAX_EXPANDED_TERM_WORK`, `MAX_ARTIFACT_EXPANDED_WORK` and `MAX_DECODED_LEVEL_OFFSET`, with `DecodeMetrics` from the same scan.
- **The node-tag table** (`NODE_TAG_TABLE`): one row per frozen tag, giving its child arity, its token bound and its two storage-boundary verdicts.
- **The experimental stage syntax** (`stage::Arena`): an append-only, interned rule-language arena for hypothesis-indexed staging, with no wire format.

## Expected features

- **Admission by the consumer.** Decoding checks format, canonicality and budgets, never typing. A decoded declaration is trusted only after an admission choke point (`gandr-kernel-core`) re-checks it.
- **`--cfg anodized_panic` for enforcement.** Built with this `cfg` across the whole dependency graph, the `#[spec]` attributes check their clauses at runtime and panic on a violation. The enforcing test lane sets it.

## Examples

Consumers reach the crate through the kernel; a direct round trip builds a declaration, encodes it and decodes it.

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
    let body = arena.value_tuple(&[unit, unit]);
    let builder = DeclarationBuilder::new(&mut arena);
    let declaration = builder.def(LevelSignature::monomorphic(), declared, body);
    let sequence = [MarkedDeclaration::new(AdmissionMark::Checked, declaration)];

    let bytes = encode(&arena, &sequence);
    let artifact = decode(bytes.as_image()).expect("the artifact is canonical");
    assert_eq!(1, artifact.declarations().len());
}
```

`tests/sharing_format.rs` carries the rejection suite: the sharing round trip with sharing asserted at the shared nodes, sharing determinism over two differently shared equal inputs, the canonical-form refusals, the amplification goldens, the boundary goldens derived from the constants, and the version refusal. `tests/adversarial_depth.rs` decodes and drops the deepest artifact the kernel round-trips inside a small-stack thread. Run them, then the enforcing twin:

```sh
cargo nextest run -p gandr-kernel-term
RUSTFLAGS="--cfg anodized_panic" cargo nextest run -p gandr-kernel-term
```

## Where the detail lives

Mechanism, decisions and specification detail live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| The four decisions, canonical form, sharing and compression, specification attributes | [`src/lib.rs`](src/lib.rs) |
| The arena, its disciplines and the watermark | [`src/arena.rs`](src/arena.rs) |
| The binders a node reads, and how each former closes the ones it binds | [`src/support.rs`](src/support.rs) |
| Declarations, structured names and the builder | [`src/decl.rs`](src/decl.rs) |
| Universe families, static operators, n-ary products and sums | [`src/types.rs`](src/types.rs) |
| Nominal data, structural records and fixpoint evidence | [`src/term.rs`](src/term.rs) |
| The byte table, versioning, universe paths, Lists and session codes | [`src/tags.rs`](src/tags.rs) |
| The amplification budgets | [`src/budget.rs`](src/budget.rs) |
| The encoder and its canonical order | [`src/encode.rs`](src/encode.rs) |
| Decode acceptance and its limits | [`src/decode.rs`](src/decode.rs) |
| The rejection vocabulary | [`src/error.rs`](src/error.rs) |
| The stage arena and its extents; its lookup files on `gandr-kernel-check-memo`'s hash index | [`src/stage.rs`](src/stage.rs) |

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
