# gandr-storage-values

A content-addressed value plane with typed chunk DAGs, content pointers and flat canonical token bytes.

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Byte languages](#byte-languages)
- [Chunk boundaries and residues](#chunk-boundaries-and-residues)
- [Verification and decode budgets](#verification-and-decode-budgets)
- [The value manifest](#the-value-manifest)
- [The locality bound](#the-locality-bound)
- [Laws and their witnesses](#laws-and-their-witnesses)
- [Mutation](#mutation)
- [Specification attributes](#specification-attributes)
- [License](#license)

## Synopsis

**What.** `gandr-storage-values` stores one value as a typed chunk DAG addressed by `ContentPtr`, or as a flat canonical token body without a store. `cam_commit` produces a manifest and root pointer; `cam_deref` reconstructs a value through its codec. The crate uses `core` and `alloc` under `no_std`.

**Why.** Large values need content identities and structural sharing at their own constructor boundaries. Chunking by those boundaries lets unchanged subtrees share storage across values and edits. A decoder consumes one logical token stream regardless of the seams between chunks, keeping storage layout outside the codec.

**How.** A `CanonicalValue` emits a balanced stream of constructor, word and byte records. The typed scanner in `gandr-storage-chunker` selects constructor exits using a Merkle-derived residue and a token cap. Selected subtrees become domain-separated BLAKE3 chunks, replaced in their parents by digest-and-offset pointers. The reader verifies chunks, splices their token streams and charges decoding to a total work budget; heap-held traversal stacks avoid recursion in the storage paths.

## References

- Michael Rainey, Michael H. Borkowski, Michael Vollmer, Chaitanya S. Koparkar, Mikah Kainen, and Vidush Singhal. "LoCalMem: Type-Directed Adaptive Serialization for Location- and Content-Addressable Memory." _Proceedings of the ACM on Programming Languages_ 10, ICFP, article 290, August 2026. [doi:10.1145/3828688](https://doi.org/10.1145/3828688) — constructor-directed cuts, content pointers, the representation lemmas the laws stand in for, and the expected-chunk bound in Theorem 5.2.
- Athicha Muthitacharoen, Benjie Chen, and David Mazières. "A Low-Bandwidth Network File System." _Proceedings of the Eighteenth ACM Symposium on Operating Systems Principles (SOSP '01)_, pages 174–187, 2001. [doi:10.1145/502034.502052](https://doi.org/10.1145/502034.502052) — content-defined cuts that resynchronize after edits.
- Jack O'Connor, Jean-Philippe Aumasson, Samuel Neves, and Zooko Wilcox-O'Hearn. "BLAKE3: One Function, Fast Everywhere." Specification, 2020. [BLAKE3 specification](https://github.com/BLAKE3-team/BLAKE3-specs) — the digest family for chunk identities and boundary residues.
- Ralph C. Merkle. "A Digital Signature Based on a Conventional Encryption Function." _Advances in Cryptology — CRYPTO '87_, Lecture Notes in Computer Science 293, pages 369–378, 1988. [doi:10.1007/3-540-48184-2_32](https://doi.org/10.1007/3-540-48184-2_32) — deriving a subtree digest from its children's digests.

## Provided features

- `CanonicalValue`, `TokenSink` and `TokenReader` define the canonical codec boundary.
- `cam_commit` stores chunks and returns a `ValueManifest`; `cam_deref` decodes from a root or interior `ContentPtr`.
- `ValueManifest::encode`, `decode` and `identity` give a manifest one byte image and a BLAKE3 identity over it; `read_under` refuses a profile mismatch before loading a chunk; `closure` returns the `ValueClosure` a dereference loads and checks the manifest's token count against it.
- `encode_flat` and `decode_flat` round-trip a value without a store or child pointers.
- `VerifiedChunk`, `frame_chunk` and `verify_chunk_image` bind canonical framing to content identity.
- `ChunkStore` defines verified chunk storage; `InMemoryChunkStore` supplies an in-memory implementation.
- `expected_chunk_bound` and `measure_edit` express and measure chunk locality.
- `ValueError` distinguishes emission, framing, authentication, codec and budget failures.
- Property laws check the flat round trip, the commit–deref round trip, chunking invisible to the flat form, store-history independence and the cut rule over generated values and profiles; fixed witnesses check the adversarial ceiling at kappa one and the commit snapshot under mutation. [Laws and their witnesses](#laws-and-their-witnesses) names each test and the statement it stands for.

## Expected features

Consumers implement `CanonicalValue` with a deterministic emission and a decoder that reconstructs an equal value. Emission must contain exactly one balanced root constructor. Consumers agree on `ValueProfile`, including codec identity and version, typed chunker parameters and child-reference representation; the chunk encoding supports `ChildIndexBase::Absolute`. A reader states the profile it expects, and `ValueManifest::read_under` refuses a manifest committed under any other.

A persistent store implements `ChunkStore`, returning verified material for the requested digest. Flat encoding needs no store but rejects embedded content pointers because it cannot resolve them. Consumers supply an allocator and decide whether a decoded value is admissible for their application; chunk integrity alone does not establish that.

The optional executable specification checks use `--cfg anodized_panic` across the dependency graph, as in the enforcing test lane.

## Examples

Implement a two-word codec, then round-trip it through flat bytes and a chunk store:

```rust
use gandr_storage_chunker::Kappa;
use gandr_storage_chunker::TokenCap;
use gandr_storage_chunker::TypedChunkerParams;
use gandr_storage_values::CanonicalValue;
use gandr_storage_values::CanonicalWord;
use gandr_storage_values::ChildIndexBase;
use gandr_storage_values::CodecId;
use gandr_storage_values::CodecIdentity;
use gandr_storage_values::CodecVersion;
use gandr_storage_values::ConstructorTag;
use gandr_storage_values::InMemoryChunkStore;
use gandr_storage_values::TokenReader;
use gandr_storage_values::TokenSink;
use gandr_storage_values::ValueError;
use gandr_storage_values::ValueProfile;
use gandr_storage_values::cam_commit;
use gandr_storage_values::cam_deref;
use gandr_storage_values::decode_flat;
use gandr_storage_values::encode_flat;

#[derive(Debug, PartialEq)]
struct Point {
    x: CanonicalWord,
    y: CanonicalWord,
}

const POINT: u8 = 0x01;

impl CanonicalValue for Point {
    fn emit_tokens<Sink>(&self, sink: &mut Sink) -> Result<(), ValueError>
    where
        Sink: TokenSink + ?Sized,
    {
        sink.open(ConstructorTag::from(POINT))?;
        sink.word(self.x)?;
        sink.word(self.y)?;
        sink.close()
    }

    fn decode_tokens(reader: &mut TokenReader<'_>) -> Result<Self, ValueError> {
        let tag = reader.read_tag()?;
        if u8::from(tag) != POINT {
            return Err(ValueError::UnexpectedConstructor { found: tag, position: reader.position() });
        }
        let x = reader.read_word()?;
        let y = reader.read_word()?;
        reader.read_close()?;
        Ok(Self { x, y })
    }
}

fn main() -> Result<(), Box<dyn core::error::Error>> {
    let point = Point { x: CanonicalWord::from(3_u64), y: CanonicalWord::from(4_u64) };
    let flat = encode_flat(&point)?;
    let decoded = decode_flat::<Point>(flat.as_body())?;
    assert_eq!(decoded, point);

    let kappa = Kappa::try_from(4_u64)?;
    let cap = TokenCap::try_from(64_u64)?;
    let params = TypedChunkerParams::new(kappa, cap);
    let codec = CodecIdentity::new(CodecId::from(1_u16), CodecVersion::from(1_u16));
    let profile = ValueProfile::new(params, codec, ChildIndexBase::Absolute);
    let mut store = InMemoryChunkStore::new();
    let manifest = cam_commit(&mut store, &profile, &point)?;
    let decoded = cam_deref::<Point>(&store, manifest.root())?;
    assert_eq!(decoded, point);
    Ok(())
}
```

Run the crate's tests from the repository root:

```sh
mise exec -- cargo test -p gandr-storage-values
```

## Byte languages

Token bodies use fixed-width little-endian integers and explicit record kinds:

```text
record := 0x01 open  || u8 tag
        | 0x02 word  || u64le value
        | 0x03 bytes || u64le length || length bytes
        | 0x04 child || 32-byte chunk digest || u32le token offset
        | 0x05 close
```

A chunk frames a body; its digest is BLAKE3 over the whole image, including the domain:

```text
image := "gandr:storage-values:chunk:v1" || u16le version || u64le token count || u64le body length || body
```

Chunk insertion is first-write-wins: a fresh digest retains the offered image, while an existing digest retains its prior bytes. Reinsertion neither compares nor repairs those bytes. Loading recomputes the digest and checks the frame each time, so corrupted backing bytes are refused even after the original chunk is offered again. Equality of digests is not used as a deciding comparison of two images.

The chunk refinements check the digest, frame and cached token count. A verified body's slice must point into its image, not merely contain equal bytes elsewhere. The witnesses include empty and three-record bodies, forged cached fields, corrupted storage and a wrong digest combined with a malformed domain to distinguish refusal precedence.

A flat encoding is the same canonical body for a value that fits one chunk. Flat bodies contain no child records. A chunked value embeds each cut subtree as a child pointer at offset zero; interior content pointers can address other token offsets. Children nest in place rather than through a shared index table, so an insertion does not renumber sibling references. `cam_commit` rejects `ChildIndexBase::ChunkLocal` because this encoding carries no relative index base.

A manifest names a value and the profile it was committed under; its identity is BLAKE3 over the whole image:

```text
manifest := "gandr:storage-values:manifest:v1" || u16le version
         || u64le commitment length || chunker commitment
         || u8 digest family || u16le codec id || u16le codec version
         || u8 child index base || u8 boundary classification || u16le chunk frame version
         || 32-byte root digest || u32le root offset || u64le token count
```

The chunker commitment is the bytes `gandr-storage-chunker` documents for a typed profile: its domain, the typed algorithm's discriminator, kappa and the token cap. Each one-byte field is a tag with zero unassigned: digest family 1 is BLAKE3, child index base 1 is absolute and 2 chunk-local, boundary classification 1 is every constructor exit. The version and the chunk frame version are 1.

## Chunk boundaries and residues

A constructor's residue depends on its content, independent of cuts within its descendants:

```text
preimage(c) := "gandr:storage-values:residue:v1" || open record || item* || close record
item        := a word, bytes or child record c emitted | 0x00 || BLAKE3(preimage(nested constructor))
residue(c)  := the first eight bytes of BLAKE3(preimage(c)), as u64le
```

Each record appended to a body joins the scanner's count once, at the next boundary event: every record the value emits, and the one child record that takes a cut subtree's place in its parent. Every constructor exit except the outermost is a candidate: the scanner cuts when the pending count reaches the cap, otherwise when the residue is divisible by kappa, and a cut empties the count. The outermost constructor becomes the root chunk directly, avoiding an extra pointer-only root.

## Verification and decode budgets

`VerifiedChunk` can be obtained only by framing a body or verifying an image. Verification checks the domain, version, byte length, token count and digest. Both `ChunkStore` methods use this type, so implementations cannot return unverified byte buffers through the trait.

Emission checking rejects empty output, multiple roots, unmatched closes, unclosed constructors and payload outside a constructor. A reader entering a child chunk consumes exactly one subtree and returns to its parent when that subtree closes.

The flat sink's executable refinement bounds its addressed records by the bytes it has emitted. Its fixed wire witness checks all four flat record forms and the refusal positions for an embedded pointer and malformed emission; generated round trips cover values of at most 4096 records, not arbitrary consumer codecs.

Every decode charges one accumulator for records, payload bytes and chunk-image bytes verified at seams. Work beyond `MAX_DECODE_WORK` (2^34) is rejected, including repeated reads through different paths to a shared chunk. Authentication establishes the bytes named by a pointer; the codec and consumer retain responsibility for value validity.

The reader's executable refinement keeps spent work within the ceiling and forbids suspended chunk frames in flat mode. Fixed witnesses cover exact payload borrowing and charges, wrong record kinds, an interior child at offset two, and restoration of its parent's cursor. A refused read does not promise rollback of all cursor bookkeeping.

## The value manifest

A `ContentPtr` names bytes; a reader also needs the rules that produced them. `ValueManifest` carries both: the root pointer and token count, and the profile fields a reader must agree with: chunker commitment, digest family, codec identity and version, child index base, boundary classification and chunk frame version. `encode` writes the image in [Byte languages](#byte-languages), `decode` reads it back, and `identity` hashes it.

**The identity binds the profile.** Subject to BLAKE3 collision resistance, the identity binds every field, including the profile under which a value is read.

- **Alternatives.** Carrying the profile in every chunk frame lets a chunk be read alone, but spends the profile's bytes per chunk and stops identical bodies under different profiles from sharing. Letting each consumer choose which fields to bind lets two consumers name one value differently.
- **Reversal.** If the chunk frame comes to carry the profile, the manifest shrinks to the root pointer and token count.

**Decoding refuses by field.** `decode` reads the image in order through a cursor over the borrowed bytes, without recursion or allocation, and stops at the first fault: `MalformedManifest` names a field holding a value this build does not read (a foreign domain, another version, an unassigned tag, a commitment under another algorithm or with zero kappa or cap), `TruncatedManifest` names the field the image ends inside, and `TrailingManifestBytes` refuses bytes after the token count. The commitment is parsed by the chunker's documented layout; if the chunker exports a parser, decoding uses it instead. The manifest domain differs from the chunk domain, so neither image verifies as the other.

Manifest and profile refinements admit only the supported layout versions; they do not certify a root's presence or the truth of a declared token count. A canonical zero-count declaration remains readable as metadata and is refused by `closure` when its stored value delivers two records. Cursor witnesses cover zero-width reads, exact suffix borrowing and unchanged state on a truncated fixed-width read.

**The profile is checked before any load.** `read_under` compares the manifest's profile with the reader's and refuses with `IncompatibleProfile`, naming the first field that differs in image order, before the store is asked for a chunk. A matching profile reads through `cam_deref`.

**The closure is what a dereference loads.** `closure` walks the subtree the root addresses, entering every chunk a child record names, and returns the set of their digests. A chunk the store lacks is refused with `UnknownChunk` naming its digest; a stored chunk was verified when it was inserted. The walk visits each pointer once, keeps pending subtrees on a heap stack and charges the decode budget. It then compares the records a reader of the root delivers with the declared token count and refuses a difference with `TokenCountMismatch`. `measure_edit` reads the same walk. Collecting unreferenced chunks, persistent stores and re-committing under changed chunker constants belong to consumers.

**The token count includes embedded values.** The count is every record a reader delivers, so a child pointer a codec embeds counts the records of the subtree it names. `cam_commit` walks each embedded pointer's closure to count them, and refuses an embedded pointer whose chunks the store lacks with `UnknownChunk`. Counting only the records the codec emitted would make every manifest with an embedding fail its own closure check. If embedding-heavy codecs make that walk costly, the commit can remember each embedded pointer's count.

| Statement | Witness | Rung |
| --------- | ------- | ---- |
| The image and identity of one manifest, against bytes written by hand and an independent BLAKE3 tool | `the_manifest_bytes_are_pinned` | L2 |
| Every field with a second admissible value moves the identity | `each_manifest_field_moves_the_identity` | L3 |
| Generated commits' manifests decode and re-encode to the same bytes | `a_manifest_round_trips_through_its_bytes` | L2 |
| Each malformed image is refused by name, including every prefix length | `each_malformed_manifest_is_refused_by_name` | L3 |
| A manifest image is not a chunk image, nor the reverse | `a_manifest_image_is_refused_as_a_chunk` | L3 |
| A profile mismatch loads nothing; a match reads the value | `a_profile_mismatch_is_refused_before_any_chunk_is_read`, `a_matching_profile_reads_the_committed_value` | L3 |
| The closure is exactly what the commit wrote into an empty store, embeddings included | `the_closure_is_every_chunk_the_commit_wrote` | L2 |
| A missing descendant two seams down is refused by digest | `a_missing_descendant_fails_the_closure_by_name` | L3 |
| A count one over or one under is refused | `a_manifest_overstating_its_tokens_fails_the_closure` | L3 |

## The locality bound

`expected_chunk_bound` computes `2 + ceil(2d / kappa) + ceil(d / cap)` with checked arithmetic, using edit depth `d` and the profile's kappa and token cap. This is an expectation over boundary residues, not a worst-case guarantee for one edit.

The numerator is widened before division, so a depth whose double exceeds sixty-four bits still receives a bound when the result fits. At depth `u64::MAX`, the widest kappa and cap give five, not overflow. Overflow is reserved for an unrepresentable bound; a regression witness separates numerator, quotient, sum and final-addition width boundaries.

`measure_edit` walks the closure of the input and edited roots and counts chunks only the edited value's closure holds and chunks the two share. The locality suite compares the mean over all leaf edits of balanced corpora at depths two through eight with the bound. That finite measurement supplies evidence for those corpora, not a proof for arbitrary codecs or edits.

Executable measurement refinements require the affected and shared counts to form a nonempty, representable partition. Fixed identical and disjoint one-chunk values witness both extremes without assuming the probabilistic bound.

## Laws and their witnesses

LoCalMem states its representation results as deep-equality theorems over its own model and proves them mechanically. This crate does not port those proofs. Each statement it can observe has a named test standing in for it: a property differential over generated values and profiles, or a fixed witness where the statement is deterministic. Every one is evidence on the inputs it exercised, and none is a proof.

- **Alternatives.** Claiming nothing until a mechanized proof exists leaves observable obligations unchecked. Crediting a differential as the lemma beside it would close a proof obligation by relabelling it.
- **Reversal.** A mechanized proof of a statement over this crate's token vocabulary takes that row; its differential stays as the check that the code still meets it.

A rung names what the test compares against. **L2** is agreement with an independent reference on exercised inputs: the flat encoder, which holds no store and no scanner; a reference scanner written in the test from [Chunk boundaries and residues](#chunk-boundaries-and-residues), sharing no code with the commit path; an empty store. **L3** is an exact assertion at named boundaries. A measurement compares observed means with a stated bound.

| Statement | Witness | Rung |
| --------- | ------- | ---- |
| Segment soundness and completeness (Lemmas 3.4, 3.5) | `every_generated_value_round_trips_flat`, beside `every_record_round_trips_through_the_grammar` | L2 |
| Token bound (Lemma 3.6) | none owed: the flat form has no alias stratum to bound; the reader's total budget is `the_budget_admits_the_ceiling_and_refuses_one_past` | L3 |
| Deep equality (Lemma 4.4) | the codec's own equality over decoded values, the observer every witness below compares with | — |
| Duplication and evacuation (Lemmas 4.6, 4.7) | none: the crate has no regions, wrappers or collector ([Mutation](#mutation)) | — |
| Codec round trip (Lemma 5.5) | `every_generated_value_round_trips_flat` | L2 |
| Commit–load round trip (Lemma 5.7) | `every_generated_value_commits_and_derefs_back_equal` | L2 |
| Chunking transparency (Lemma 5.8) | `chunking_is_invisible_to_the_flat_form` | L2 |
| Store-history independence | `a_root_pointer_does_not_depend_on_what_the_store_holds` | L2 |
| Locality (Theorem 5.2, Corollary 5.3) | `measured_chunk_counts_sit_inside_the_locality_bound`, and the formula by `the_bound_matches_the_formula_by_hand` | measurement; L3 |
| The cut rule, a deterministic complement of locality | `the_cuts_agree_with_a_reference_scanner` | L2 |
| The adversarial ceiling, a deterministic complement of locality | `an_edit_under_every_cut_affects_exactly_its_path` | L3 |

What each law observes:

- **Flat round trip.** Decoding a generated value's flat bytes returns the value.
- **Commit–deref round trip.** Under every generated profile, the root pointer derefs to the value, and the manifest carries the profile.
- **Chunking invisible to the flat form.** The flat bytes of the dereffed value equal the original's, byte for byte; splicing each child chunk's body where its child record stands rebuilds the same bytes; the manifest's token count is the flat form's record count.
- **Store-history independence.** Committing into a store that already holds the value's subtrees, the value with a leaf edited, the value itself and unrelated values, some under other profiles, returns the manifest an empty store returns. The store ends holding exactly what it held and what the empty store came to hold.
- **The cut rule.** The reference recomputes every residue from the flat form alone and applies the cap first, then divisibility by kappa, never at the outermost constructor. Its cuts are the chunk boundaries read off the stored chunk DAG.
- **The adversarial ceiling.** Residues are a public function of content, so whoever controls content can grind them; the most it reaches is every constructor below the root its own chunk. Kappa one forces that ceiling deterministically, since every residue is then a multiple. The witness, a value of every shape with no repeated subtree, holds one chunk per constructor whatever the cap, and each leaf edit affects exactly the chunks of the constructors on its root path and shares every other. The cost is more chunks and lookups, never a wrong value, and the decode budget bounds the work.

The generators decide what this evidence covers. Values are constructor trees over seven shapes, with words and byte strings, biased toward deep spines, wide fans, repeated subtrees and the empty-payload constructor. Profiles are biased toward kappa one, powers of two, and caps at and below kappa; half the cut rule's cases set the cap where a run reaches it exactly at a boundary event, or passes it there by one record. A law checked only on balanced fixtures under one profile meets none of those edges. The generators and the reference scanner are test code; nothing ships them.

## Mutation

No API in this crate mutates a committed value or a stored chunk. `cam_commit` reads a value the caller owns and keeps none of it.

**Commit snapshots, witnessed.** A value committed, mutated in place through an exclusive borrow and committed again gets a second root. The first root still derefs to the value as committed and the second to the mutated value, and the store grows by exactly the chunks `measure_edit` reports the edit affected (`a_value_mutated_after_commit_commits_anew_and_the_old_pointer_still_reads_the_old_value`, L3).

**Transparency under in-place mutation, not this crate's.** That deep equality survives in-place mutation of wrapped, spliced or duplicated representations under exclusive access is a statement about a runtime value representation with indirection and a permission model. This crate has neither, and holds no regions, wrappers or collector to check it against. Exclusive borrows make the mutated value independent of the committed one; they do not establish the representation theorems.

- **Reversal.** An API that edits stored content in place, such as an in-place chunk editor or a mutable arena under the value plane, makes transparency under mutation this crate's obligation before it lands.

## Specification attributes

`# Specification` blocks state the admitted behavior; executable `#[spec(...)]` predicates check supported conditions on executed calls. Trait declarations state implementor obligations. `cam_deref` relies on the consumer's codec round-trip law without requiring an equality implementation on its result type.

The committing sink refines its live frame marks against the body and residue buffers it owns. Its literal nested-value witness checks exact stored bytes and record accounting; bounded generated values additionally compare cut positions against an independent scanner. Individual frame marks cannot establish these relationships without their owning buffers.

Closure refinements require a nonempty loaded set and at least an open/close pair in a completed subtree. Traversal refinements bound spent work and bind cached pointer counts to loaded digests. A fixed repeated-reference witness distinguishes two offsets of the same chunk and counts each logical occurrence, while the digest set still deduplicates physical chunks.

Shared fixtures refine a complete preorder tree, not merely a nonempty node list. Asymmetric byte goldens distinguish child order and leaf indices, and a five-kind scanner witness checks full child addresses. An exact callback trace enters two nested seams and returns to the outer source on the closing record, separating an observed maximum from the final depth. An empty emission script succeeds without invoking its sink; the enclosing encoders then refuse its missing value.

The independent model checks exact borrowed wire extents, while cut and splice witnesses distinguish logical record positions from byte offsets at cap boundaries. Its ledger refinement compares listed identities with authenticated backing entries; equal cardinalities alone do not establish agreement.

The generated codec refines the complete seven-shape field grammar, including counted children. Literal heterogeneous bytes distinguish leaf payloads from count words and interleaved fields, pin their depths and record indices, and preserve untouched data during word, binary and empty-byte edits. The generator's record budget constrains its producer rather than every value the codec can read.

Arena refinements bind backward child references, saturated expanded counts and exact frontier markers. Boundary witnesses distinguish 4096-record admission from 4097-record replacement, preserve unused roots and retain repeated children by occurrence. A compact doubling DAG reaches the counter width without expanding it; a separate frontier witness discards exactly the oldest root when the combined value exceeds the budget.

Prior-value recipes compare selected subtrees and edited leaves against their unchanged input without copying it into a predicate. Fixed field positions distinguish payload leaves from tagged words and interleaved labels, including empty-byte growth and leafless identity. Strategy factories state their sample bounds and an explicit executable exemption: observing a sample advances a runner. Their bounded round-trip, cut and history properties do not claim statistical frequencies or exhaustive coverage. Event-targeted caps describe positions before any earlier cut resets the pending run.

Load-count witnesses distinguish refused backend requests from profile preflight, which performs no load, and exercise the final representable counter transition. Helpers that receive only a store and digest cannot inspect the loaded body in a predicate without repeating observable I/O; their child-reference ordering is covered by the existing missing-descendant scenario.

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
