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
- [The locality bound](#the-locality-bound)
- [Specification attributes](#specification-attributes)
- [License](#license)

## Synopsis

**What.** `gandr-storage-values` stores one value as a typed chunk DAG addressed by `ContentPtr`, or as a flat canonical token body without a store. `cam_commit` produces a manifest and root pointer; `cam_deref` reconstructs a value through its codec. The crate uses `core` and `alloc` under `no_std`.

**Why.** Large values need content identities and structural sharing at their own constructor boundaries. Chunking by those boundaries lets unchanged subtrees share storage across values and edits. A decoder consumes one logical token stream regardless of the seams between chunks, keeping storage layout outside the codec.

**How.** A `CanonicalValue` emits a balanced stream of constructor, word and byte records. The typed scanner in `gandr-storage-chunker` selects constructor exits using a Merkle-derived residue and a token cap. Selected subtrees become domain-separated BLAKE3 chunks, replaced in their parents by digest-and-offset pointers. The reader verifies chunks, splices their token streams and charges decoding to a total work budget; heap-held traversal stacks avoid recursion in the storage paths.

## References

- Trevor Rainey, Nathan Borkowski, Michael Vollmer, Chaitanya Koparkar, Nathan Kainen, and Vidush Singhal. "LoCalMem: Type-Directed Adaptive Serialization for Location- and Content-Addressable Memory." _Proceedings of the ACM on Programming Languages_ 10, ICFP, article 290, August 2026. [doi:10.1145/3828688](https://doi.org/10.1145/3828688) — constructor-directed cuts, content pointers and the expected-chunk bound in Theorem 5.2.
- Athicha Muthitacharoen, Benjie Chen, and David Mazières. "A Low-Bandwidth Network File System." _Proceedings of the Eighteenth ACM Symposium on Operating Systems Principles (SOSP '01)_, pages 174–187, 2001. [doi:10.1145/502034.502052](https://doi.org/10.1145/502034.502052) — content-defined cuts that resynchronize after edits.
- Jack O'Connor, Jean-Philippe Aumasson, Samuel Neves, and Zooko Wilcox-O'Hearn. "BLAKE3: One Function, Fast Everywhere." Specification, 2020. [BLAKE3 specification](https://github.com/BLAKE3-team/BLAKE3-specs) — the digest family for chunk identities and boundary residues.
- Ralph C. Merkle. "A Digital Signature Based on a Conventional Encryption Function." _Advances in Cryptology — CRYPTO '87_, Lecture Notes in Computer Science 293, pages 369–378, 1988. [doi:10.1007/3-540-48184-2_32](https://doi.org/10.1007/3-540-48184-2_32) — deriving a subtree digest from its children's digests.

## Provided features

- `CanonicalValue`, `TokenSink` and `TokenReader` define the canonical codec boundary.
- `cam_commit` stores chunks and returns a `ValueManifest`; `cam_deref` decodes from a root or interior `ContentPtr`.
- `encode_flat` and `decode_flat` round-trip a value without a store or child pointers.
- `VerifiedChunk`, `frame_chunk` and `verify_chunk_image` bind canonical framing to content identity.
- `ChunkStore` defines verified chunk storage; `InMemoryChunkStore` supplies an in-memory implementation.
- `expected_chunk_bound` and `measure_edit` express and measure chunk locality.
- `ValueError` distinguishes emission, framing, authentication, codec and budget failures.

## Expected features

Consumers implement `CanonicalValue` with a deterministic emission and a decoder that reconstructs an equal value. Emission must contain exactly one balanced root constructor. Consumers agree on `ValueProfile`, including codec identity and version, typed chunker parameters and child-reference representation; the chunk encoding supports `ChildIndexBase::Absolute`.

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

A flat encoding is the same canonical body for a value that fits one chunk. Flat bodies contain no child records. A chunked value embeds each cut subtree as a child pointer at offset zero; interior content pointers can address other token offsets. Children nest in place rather than through a shared index table, so an insertion does not renumber sibling references. `cam_commit` rejects `ChildIndexBase::ChunkLocal` because this encoding carries no relative index base.

## Chunk boundaries and residues

A constructor's residue depends on its content, independent of cuts within its descendants:

```text
preimage(c) := "gandr:storage-values:residue:v1" || open record || item* || close record
item        := a word, bytes or child record c emitted | 0x00 || BLAKE3(preimage(nested constructor))
residue(c)  := the first eight bytes of BLAKE3(preimage(c)), as u64le
```

Each emitted record joins the scanner's count once, at the next boundary event. Every constructor exit except the outermost is a candidate: the scanner cuts when the pending count reaches the cap, otherwise when the residue is divisible by kappa. The outermost constructor becomes the root chunk directly, avoiding an extra pointer-only root.

## Verification and decode budgets

`VerifiedChunk` can be obtained only by framing a body or verifying an image. Verification checks the domain, version, byte length, token count and digest. Both `ChunkStore` methods use this type, so implementations cannot return unverified byte buffers through the trait.

Emission checking rejects empty output, multiple roots, unmatched closes, unclosed constructors and payload outside a constructor. A reader entering a child chunk consumes exactly one subtree and returns to its parent when that subtree closes.

Every decode charges one accumulator for records, payload bytes and chunk-image bytes verified at seams. Work beyond `MAX_DECODE_WORK` (2^34) is rejected, including repeated reads through different paths to a shared chunk. Authentication establishes the bytes named by a pointer; the codec and consumer retain responsibility for value validity.

## The locality bound

`expected_chunk_bound` computes `2 + ceil(2d / kappa) + ceil(d / cap)` with checked arithmetic, using edit depth `d` and the profile's kappa and token cap. This is an expectation over boundary residues, not a worst-case guarantee for one edit.

`measure_edit` counts chunks reachable only from the edited value and chunks shared with the input value. The locality suite compares the mean over all leaf edits of balanced corpora at depths two through eight with the bound. That finite measurement supplies evidence for those corpora, not a proof for arbitrary codecs or edits.

## Specification attributes

`# Specification` blocks state the admitted behavior; executable `#[spec(...)]` predicates check supported conditions on executed calls. Trait declarations state implementor obligations. `cam_deref` relies on the consumer's codec round-trip law without requiring an equality implementation on its result type.

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
