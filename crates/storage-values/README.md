# gandr-storage-values

A content-addressed value plane with typed chunk DAGs, content pointers and flat canonical token bytes.

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

**What.** `gandr-storage-values` stores one value as a typed chunk DAG addressed by `ContentPtr`, or as a flat canonical token body without a store. `cam_commit` produces a manifest and root pointer; `cam_deref` reconstructs a value through its codec. The crate uses `core` and `alloc` under `no_std`.

**Why.** Large values need content identities and structural sharing at their own constructor boundaries. Chunking by those boundaries lets unchanged subtrees share storage across values and edits. A decoder consumes one logical token stream regardless of the seams between chunks, keeping storage layout outside the codec.

**How.** A `CanonicalValue` emits a balanced stream of constructor, word and byte records. The typed scanner in `gandr-storage-chunker` selects constructor exits using a Merkle-derived residue and a token cap. Selected subtrees become domain-separated BLAKE3 chunks, replaced in their parents by digest-and-offset pointers. The reader verifies chunks, splices their token streams and charges decoding to a total work budget; heap-held traversal stacks avoid recursion in the storage paths.

## References

- `Rainey-2026-localmem_typedirected_adaptive_serialization_location_contentaddressable_memory` — exemplar: Michael Rainey, Michael H. Borkowski, Michael Vollmer, Chaitanya S. Koparkar, Mikah Kainen, and Vidush Singhal. "LoCalMem: Type-Directed Adaptive Serialization for Location- and Content-Addressable Memory." _Proceedings of the ACM on Programming Languages_ 10, ICFP, article 290, August 2026. [doi:10.1145/3828688](https://doi.org/10.1145/3828688) — the CAM this crate is: constructor-directed cuts, content pointers, the representation lemmas its laws stand in for and the locality bound.
- `vault:01a178aa-ce14-7610-bcad-5aab5f9c0b0f` — background: the integrity design (§ two walls) — a verified chunk is integrity only, so a codec's decoder still refuses a payload its value cannot hold.

## Provided features

- `CanonicalValue`, `TokenSink` and `TokenReader` define the canonical codec boundary.
- `cam_commit` stores chunks and returns a `ValueManifest`; `cam_deref` decodes from a root or interior `ContentPtr`.
- `ValueManifest::encode`, `decode` and `identity` give a manifest one byte image and a BLAKE3 identity over it; `read_under` refuses a profile mismatch before loading a chunk; `closure` returns the `ValueClosure` a dereference loads and checks the manifest's token count against it.
- `encode_flat` and `decode_flat` round-trip a value without a store or child pointers.
- `ValueProfile::classified` with a `BoundaryClassification::Tagged` set names the boundary constructors; every other constructor is an alias, kept inline in the chunk that holds it. A commit refuses an alias reopened inside itself with no boundary between, and a closure refuses a seam at an alias.
- `VerifiedChunk`, `frame_chunk` and `verify_chunk_image` bind canonical framing to content identity.
- `ChunkStore` defines verified chunk storage; `InMemoryChunkStore` supplies an in-memory implementation.
- `expected_chunk_bound` and `measure_edit` express and measure chunk locality.
- `ValueError` distinguishes emission, framing, authentication, codec and budget failures.
- Property laws check the flat round trip, the commit–deref round trip, chunking invisible to the flat form, store-history independence and the cut rule over generated values and profiles; fixed witnesses check the adversarial ceiling at kappa one and the commit snapshot under mutation. The crate root's rustdoc, § Laws and their witnesses, names each test and the statement it stands for.

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

## Where the detail lives

Mechanism, decisions with their alternatives and reversals, and witnesses live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| Encoding and chunking, verification and decode budgets, laws and their witnesses, mutation, specification attributes, references | [`src/lib.rs`](src/lib.rs) |
| Token body records | [`tokens`](src/tokens.rs) |
| Chunk frames, first-write-wins insertion, verified chunks | [`chunk`](src/chunk.rs) |
| Child references | [`index_base`](src/index_base.rs) |
| Residues and the cut rule | [`commit`](src/commit.rs) |
| The value manifest | [`manifest`](src/manifest.rs) |
| The locality bound and edit measurement | [`locality`](src/locality.rs) |

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
