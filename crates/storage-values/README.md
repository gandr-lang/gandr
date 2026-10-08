# gandr-storage-values

The storage tier's **value plane**: one value as a typed chunk DAG, addressed by content pointers, and the value's flat canonical bytes.

The record plane (`gandr-storage-records`) stores sorted keyed records. This crate stores a single value by the value's own constructors. A value walks itself into a canonical token stream; `cam_commit` cuts that stream at the constructor exits the committed typed chunker profile selects, frames each cut subtree as a chunk, and names the value by its root chunk's digest. `cam_deref` fetches, verifies and decodes, and the reader splices child chunks so a decoder never sees a seam. Two values sharing a subtree share its chunks, and an edit re-cuts only the chunks on its path to the root.

`encode_flat` and `decode_flat` give one value's canonical token bytes with no store. For a value that fits one chunk they are exactly the body that chunk frames, so bytes stored flat today commit through the chunk DAG later without being re-encoded.

## The byte languages

A token body is a sequence of records; every integer is little-endian at a fixed width.

```text
record := 0x01 open  || u8 tag
        | 0x02 word  || u64le value
        | 0x03 bytes || u64le length || length bytes
        | 0x04 child || 32-byte chunk digest || u32le token offset
        | 0x05 close
```

A chunk frames a body; the digest is BLAKE3 over the whole image, domain included.

```text
image  := "gandr:storage-values:chunk:v1" || u16le version || u64le token count || u64le body length || body
```

The cut decision reads a residue per constructor, hashed Merkle-wise so it does not depend on how the constructor's descendants were cut:

```text
preimage(c) := "gandr:storage-values:residue:v1" || open record || item* || close record
item        := a word, bytes or child record c emitted | 0x00 || BLAKE3(preimage(nested constructor))
residue(c)  := the first eight bytes of BLAKE3(preimage(c)), as u64le
```

Each constructor exit but the outermost is a boundary event carrying the records appended since the previous event and the residue; the typed scanner from `gandr-storage-chunker` cuts when the residue is divisible by kappa or the pending count reaches the cap. A cut subtree becomes a child record at offset zero in its parent's body.

## Status

Ported from the value module of the pre-reboot prototype's artifact crate and revised against the reboot constraints. The revisions:

- **A domain inside every hashed preimage.** The chunk image opens with `gandr:storage-values:chunk:v1`, and the residue, which the prototype hashed bare, opens with `gandr:storage-values:residue:v1`.
- **Little-endian throughout.** The prototype framed big-endian integers; every framed integer is now little-endian, the workspace's one byte order. The committed golden digest was re-derived for the new domain and byte order and checked against an independent BLAKE3 tool.
- **A total decode budget.** Every decode is charged to one accumulator — a unit per record, per payload byte, and per chunk-image byte verified on a seam — and refused past `MAX_DECODE_WORK` (two to the thirty-fourth). The prototype had no total, so a DAG referencing one chunk along many paths cost work in the number of paths.
- **A verified chunk is a type.** `ChunkStore::insert` takes a `VerifiedChunk` and `ChunkStore::load` must return one, obtainable only from `verify_chunk_image` or from a chunk this crate framed, so both store halves verify by construction and the read path hashes each chunk once rather than twice. Verification now checks the frame's token count against the body's records, which the prototype read and ignored, and framing counts the records itself rather than trusting a caller.
- **Each record counts once.** The prototype added every record to every open constructor and reported a constructor's whole count at its exit, so a record deep in a value joined the scanner's pending count once per ancestor. An event now carries the records appended since the previous event.
- **A Merkle residue.** The prototype hashed a subtree's bytes as they stood after its descendants' cuts, at every exit — work quadratic in depth, and a residue that moved when a descendant's cut did. Each emitted byte is now hashed once, under the constructor that emitted it, and a nested constructor contributes its subtree digest.
- **The emission is checked.** A value's walk must be exactly one balanced value; a close with nothing open, a payload outside every constructor, a second root, an unclosed constructor and an empty emission are each refused by name, where the prototype accepted the first silently.
- **The locality bound and its measurement are implemented.** The prototype's bound was a placeholder and its locality test an ignored stub. `expected_chunk_bound` computes `2 + ceil(2d / kappa) + ceil(d / cap)` with checked arithmetic over the committed cap directly, so the prototype's cap multiplier is gone; `measure_edit` counts the chunks an edit added and the chunks it left shared, and the contract suite reads the mean over every leaf edit of a balanced corpus, depths two to eight, against the bound.
- **The index-base question answered by the encoding.** Children nest in place and a cut subtree is named by digest, so there are no indices to re-base: a chunk-local base is refused by name, and the prototype's measurement and verdict scaffolds are replaced by `LocalityMeasurement` taken over an early edit.
- **A manifest of what this build does.** The sharing policy is dropped — an embedded committed value is a child record and nothing re-emits inline — the boundary classification names the one rule implemented, every constructor exit, and the manifest's unused magic is gone, since a manifest is described, not hashed.
- **The flat form**, new: the store-less canonical bytes of one value, tested equal to the single chunk's body.
- **Typed errors with no dependency.** Hand-written `Display` and `core::error::Error`, payloads typed (`ChunkDigest`, `TokenOffset`, `ChunkFrameField`, `TokenKind`, `EmissionFault`) where the prototype carried strings. The crate is `no_std` over `core` and `alloc`.
- **No recursion and no bare primitives.** The reader's seam stack and the commit traversal's frame stack are heap-held; no bare primitive crosses the crate's own signatures, every single-field wrapper is `#[repr(transparent)]`, arithmetic on counts and positions is checked, and there are no `as` conversions and no `unwrap`/`expect`/`panic` outside tests.

## Not ported

- **A persistent `ChunkStore`.** The trait is the boundary a persistent implementation joins at; the in-memory store is the only one here.
- **The kernel export artifact layer.** The prototype's artifact records and manifests describe the kernel's export format, which this repository does not have.
- **Session checkpoints.** Rung 4 of the storage programme consumes this plane and is not part of it.

## The contract attributes

The `# Specification` prose stays the statement of record, and a combined `#[spec(...)]` attribute states the same predicate wherever one is a runtime-checkable expression. Forty-nine of the crate's seventy blocks carry one. The remaining twenty-one stay prose: nine are trait method declarations with no body to attach a check to, eleven are formatter implementations whose result is text, and `cam_deref` returns a caller's codec value, about which nothing can be checked without an equality the codec does not owe.

`anodized` supplies core-only specification helpers with default features disabled. The enforcing test lane selects `--cfg anodized_panic` for the whole dependency graph.

## Using it

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

/// One constructor carrying two words.
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

fn example() -> Result<(), Box<dyn core::error::Error>> {
    let point = Point { x: CanonicalWord::from(3_u64), y: CanonicalWord::from(4_u64) };

    // The canonical bytes, with no store.
    let flat = encode_flat(&point)?;
    assert_eq!(decode_flat::<Point>(flat.as_body())?, point);

    // The same value committed into a chunk store and read back by pointer.
    let params = TypedChunkerParams::new(Kappa::try_from(4_u64)?, TokenCap::try_from(64_u64)?);
    let codec = CodecIdentity::new(CodecId::from(1_u16), CodecVersion::from(1_u16));
    let profile = ValueProfile::new(params, codec, ChildIndexBase::Absolute);
    let mut store = InMemoryChunkStore::new();
    let manifest = cam_commit(&mut store, &profile, &point)?;
    assert_eq!(cam_deref::<Point>(&store, manifest.root())?, point);

    Ok(())
}
```

## Ideas and references

The named ideas: content-defined chunking as a cut rule that travels with the data; a typed, constructor-directed boundary and the locality bound it admits; content addressing with the domain inside the hashed preimage; and Merkle hashing of a tree from its children's digests.

- Trevor Rainey, Nathan Borkowski, Michael Vollmer, Chaitanya Koparkar, Nathan Kainen, and Vidush Singhal. "LoCalMem: Type-Directed Adaptive Serialization for Location- and Content-Addressable Memory." _Proceedings of the ACM on Programming Languages_ 10, ICFP, article 290, August 2026. `doi:10.1145/3828688` — the boundary discipline: cuts at a type's own constructor exits under kappa and a token cap, content pointers into a chunk DAG, and the expected-chunk bound (Theorem 5.2) `expected_chunk_bound` states.
- Athicha Muthitacharoen, Benjie Chen, and David Mazières. "A Low-Bandwidth Network File System." In _Proceedings of the Eighteenth ACM Symposium on Operating Systems Principles (SOSP '01)_, pages 174–187, 2001 — the content-defined cut rule.
- Jack O'Connor, Jean-Philippe Aumasson, Samuel Neves, and Zooko Wilcox-O'Hearn. "BLAKE3: One Function, Fast Everywhere." Specification, 2020 — the digest family every chunk, residue and pointer is taken in.
- Ralph C. Merkle. "A Digital Signature Based on a Conventional Encryption Function." In _Advances in Cryptology — CRYPTO '87_, 1987 — hashing a tree from its children's digests, the shape of the residue.

## License

Apache-2.0 WITH LLVM-exception.
