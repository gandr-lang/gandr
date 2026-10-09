# gandr-kernel-term

The kernel's term arena and sharing format: a flat, id-addressed arena, the unified subterm-table encoding over it, canonical decode, and the decode-time budgets that bound the work a small artifact can cost.

<!-- toc -->

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Canonical form by re-encoding](#canonical-form-by-re-encoding)
- [Amplification budgets](#amplification-budgets)
- [Admission watermark](#admission-watermark)
- [Rejection vocabulary](#rejection-vocabulary)
- [Tag numbering and versioning](#tag-numbering-and-versioning)
- [Sharing and compression](#sharing-and-compression)
- [Specification attributes](#specification-attributes)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** `TermArena` holds the kernel's terms and types in four typed id families: values, computations, value types and computation types. `encode` writes an arena and a sequence of marked declarations as one canonical artifact; `decode` reads an artifact back into a fresh arena, refusing anything malformed, non-canonical or over budget with a typed `DecodeError`. The crate holds representation and bytes only: the checker, conversion, the environment and the admission choke point live in `gandr-kernel-core` and consume this vocabulary. It is `no_std` over `core` and `alloc` and depends on `gandr-kernel-strata` alone among workspace crates.

**Why.** A kernel that checks large proofs needs shared subterms to stay shared from the bytes to the checker, or every reference to a shared subterm costs its full size again. Retaining that sharing is also an attack surface: a small artifact can name a DAG whose tree-expanded size is astronomical, so a reader must bound expanded work before anything downstream sees the artifact, without trusting the writer.

**How.** Four decisions interlock. The representation is an arena of `Copy` ids, so a graph of shared ids is representable at all and teardown is a flat vector drop rather than a recursion over term depth. The format is one per-artifact tagged subterm table over all four families in a single index space, maximally shared under structural equality, declaration-segmented, with children referenced only by strictly earlier index in post-order first-completion order. Decode retains sharing, which the arena makes possible: a table entry is an arena id, and decode is arena construction. Because decode retains sharing, a single forward scan over memoized saturating sizes bounds the expanded work before any consumer runs. Owned trees would foreclose the format, which is why the four are decided together.

## References

- Simon L. Peyton Jones. _The Implementation of Functional Programming Languages_. Prentice Hall, 1987. `isbn:978-0134533339` — the graph representation and maximal sharing this format's stored plane realizes statically.
- Nathanaëlle Courant and Xavier Leroy. "A Lazy, Concurrent Convertibility Checker." _Proceedings of the ACM on Programming Languages_ 10 (POPL), Article 53, January 2026. `doi:10.1145/3776695` — §6.4 builds the hash-consed subterm DAG as a pre-pass; this format hands a consumer that DAG already built, so transcription is a pass over a table.

## Provided features

- **A flat arena in four typed id families** (`ValueId`, `ComputationId`, `ValueTypeId`, `CompTypeId`) where a node's children are `Copy` ids. Constructors require children already allocated in the same arena; same-family children precede their parent while the family length fits `u32`. Lookup checks the family index, not arena provenance. Truncation permits index reuse, and minting saturates the returned index at the `u32` ceiling. Derived equality, hashing and debug output are shallow.
- **The admission watermark** (`ArenaWatermark`): a snapshot of the four family lengths, truncation back to one, and the clamp a rollback needs when staging order differs from admission order. `DeclarationBuilder` ties content minting to it.
- **The unified subterm table**: `encode` and `decode` over `EncodedArtifact` and `ArtifactImage`, with `DecodedArtifact` holding the arena and its `MarkedDeclaration` sequence. Polarity is recoverable from the tag alone, so a child slot's requirement is a table lookup.
- **Canonical form enforced by re-encoding**, described in [Canonical form by re-encoding](#canonical-form-by-re-encoding).
- **The amplification defence**: `MAX_TABLE_ENTRIES`, `MAX_EXPANDED_TERM_WORK`, `MAX_ARTIFACT_EXPANDED_WORK` and `MAX_DECODED_LEVEL_OFFSET`, enforced during decode, and `DecodeMetrics`, the deterministic measurements the same scan yields for a caller to record.
- **The node-tag table** (`NODE_TAG_TABLE`): a const protocol input with one row per frozen tag, giving its child arity, its token bound and its two storage-boundary verdicts. A differential pins its arities against the arena's own child relation.

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
    let body = arena.value_pair(unit, unit);
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

## Canonical form by re-encoding

The encoder is untrusted and feeds no judgement. The reader enforces canonical form by re-encoding the whole decoded artifact and comparing bytes, and the maximal-sharing encoder is the re-encoder. One mechanism therefore catches a redundant duplicate entry, a mis-ordered table and a dead entry. The re-encoder is itself sharing-aware; a tree-walking re-encoder would turn the canonical check into an amplification vector.

Canonical bytes are a function of the declarations' abstract content, never of how they were built or decoded, so two differently shared equal inputs encode identically.

## Amplification budgets

Each budget bounds one axis and is enforced where it is cheapest:

| budget | axis | enforced |
| ------ | ---- | -------- |
| `MAX_TABLE_ENTRIES` | distinct graph nodes | as entries accrue |
| `MAX_EXPANDED_TERM_WORK` | tree work per declaration root | on the forward scan |
| `MAX_ARTIFACT_EXPANDED_WORK` | tree work over the whole artifact | on the same scan, one extra accumulator |
| `MAX_DECODED_LEVEL_OFFSET` | a level atom's successor offset | at the level decoder, per atom |

An entry's expanded size is one plus the saturating sum of its children's. Children are strictly earlier, so one forward scan computes every size in linear time. The artifact-total cap exists because many small declaration segments referencing one near-cap root pass the per-declaration cap individually while forcing many times its work together.

The budgets bound work without touching the checker, so they stay outside the trusted base, and they are reader acceptance policy only: they change neither the wire format nor canonicality. The constants are set against the deepest artifact the kernel itself round-trips, the adversarial-depth witness, and clear it with headroom while refusing an obvious billion-laughs artifact by orders of magnitude.

## Admission watermark

A choke point takes an `ArenaWatermark` before staging a declaration and truncates after the verdict, on rejection and on success alike. `DeclarationBuilder` records its own mark and truncates each family to `min(current_len, content_start)` when abandoned. Its mutable arena borrow also permits shrinking and reminting below that mark: abandonment preserves those leading nodes rather than restoring an earlier snapshot. A `Declaration` carries no watermark: decode builds one table for the whole artifact, so a decoded declaration has no meaningful content-start mark.

The mark stores lengths rather than copied nodes, keeping truncation allocation-free. Snapshot restoration would require retaining overwritten content; revisit that choice only if staging must restore arbitrary edits rather than discard an appended suffix. `TermArena::truncate_to` with a stale watermark past a family's end leaves that family unchanged.

## Rejection vocabulary

A decode failure is a format failure and never a typing failure. `DecodeError` is a rejection triple — truncation, an unknown tag at a named `TagSite`, a violated structural invariant at a named `MalformedSite` — plus two by-name refusals for the reserved parts of the format and a version refusal that names the version it met.

`ReservedKind` names the declaration kinds a module layer would export (`ModuleSig`, `ModuleDef`, `FunctorDef`); they are reserved together so graduating one into the kernel never renumbers a shipped format, and a live kind such as the abstract type has no variant. `ReservedSlot` names the slots and sections that must be empty, and the minted-atom table, the one live member, refused when the declarations decoded beside it refute it.

## Tag numbering and versioning

The tag space is one disjoint enumeration over the four families:

| region | tags | holds |
| ------ | ---- | ----- |
| frozen block | `0x00–0x19` | every former this crate mints, contiguous from zero through the universe-decoding former |
| growth room | `0x1A–0x1F` | the core vocabulary's next formers |
| sharing block | `0x20–0x27` | a stored sharing plane: one former per family, plus four held slots for an explicit weakening form |

The sharing block is reserved: `NODE_SHARE_VALUE`, `NODE_SHARE_COMPUTATION`, `NODE_SHARE_VALUE_TYPE` and `NODE_SHARE_COMP_TYPE` name its per-family bytes, and no entry carries one. A reader meeting one of its bytes refuses it by name at the node site, exactly as it refuses any other unassigned byte. Reserving the block keeps the core vocabulary from growing into it: the core grows through the growth room and resumes above `SHARING_BLOCK_LAST`, and the block stays contiguous, so a sharing former's family is a subtraction.

Assigning an unassigned tag or kind byte, or filling a reserved slot that is framed from the start, holds `FORMAT_VERSION`: the reader is a closed-vocabulary parser, so an unknown byte is a named refusal rather than a mis-parse. Reassigning a byte or changing a field's shape, order or width bumps it, because an older reader would otherwise parse successfully and wrongly.

## Sharing and compression

The kernel preserves sharing and never creates it. The crate has no interning table and no content-keyed memo of values; a decode hands over exactly the sharing the artifact encodes, id equality is a positive-only fast path deciding reflexive pairs, and any pass that creates sharing is elaborator-side. A decoded artifact owns its arena.

Compression is a storage and transport concern. The canonical bytes are the bytes, and no codec sits inside a reader whose rejection vocabulary has to stay clean. The bytes are declaration-segmented and self-delimiting.

## Specification attributes

The `# Specification` prose is the statement of record; a combined `#[spec(...)]` attribute mirrors it where the clause is a cheap runtime predicate.

- `check_budget` accepts exactly when both expanded-work caps hold, stated as one conjunction against the body's two sequential guards, where the amplification defence binds.
- `EncodedArtifact::put_uvarint` states the terminator half of varint minimality, and `ArtifactImage::span` the in-bounds condition of every adversarial read.
- `LevelSignature::new`, `DeclarationBuilder::sealed_def` and `DeclarationBuilder::abstract_type` pin the content variant and slot arity each finisher promises, which separates adjacent finishers that differ only in a variant.

Two sites keep prose and say why at the site. `TermArena::truncate_to` would panic on its documented stale-watermark no-op if `self.watermark() == watermark` were asserted. `TermArena::children_of` defines "strictly less than the node's own id" only within one family, and it is the edge relation every walk over the arena runs.

## License

Apache-2.0 WITH LLVM-exception, the workspace licence; the text is at the repository root.
