# gandr-storage-chunker

**Content-defined chunking** for the storage tier: where a stream of canonical units is cut into chunks, decided by the content rather than by a position counter, under parameters a downstream root commits.

A store that cuts by position shifts every later cut when one byte is inserted, so two versions of a value share nothing past the edit. A store that cuts where the content says moves only the cuts near the edit, and the chunks around it keep their identities and their storage. This crate is that decision and nothing else: it reads no store, hashes no chunk and names no chunk. It returns where the cuts fall and why, and it has no dependencies.

## Two profiles

| profile | input | cuts | committed fields |
| ------- | ----- | ---- | ---------------- |
| **record-safe** (`ChunkerParams`) | canonical record bytes, as slices or as one buffer with record spans | between complete records, when a Gear rolling hash masked by the byte target is zero, or at a byte or record cap | Gear table, seed policy and salt, normalization, record-boundary rule, three byte limits, three record limits |
| **typed** (`TypedChunkerParams`) | boundary events a caller reports while walking its own grammar: the tokens since the previous event and a residue | when the residue is divisible by kappa, or when the pending tokens reach the cap | kappa, token cap |

The typed scanner never sees bytes. A caller reports an event wherever its grammar admits a cut — after a record, after a constructor closes — with a residue taken under the caller's own committed hash. Kappa is the expected number of events per content-defined cut; the cap bounds every chunk's tokens whatever the residues do. A record store whose records are its events, one token each, is the degenerate instance, and `gandr-storage-records` cuts its leaves that way.

Both profiles are deterministic, read each input once with no lookahead, and commit their parameters as bytes opening with one domain, `gandr:storage-chunker:params:v1`, followed by the algorithm discriminator and the profile's fields, every integer little-endian at a fixed width. Two writers that disagree on a parameter then produce different roots instead of silently different cuts.

## Status

Ported from the `storage-chunker` crate of the pre-reboot prototype and revised against the reboot constraints. The revisions:

- **A domain inside every commitment, and one layout per profile.** The prototype opened every commitment with a fixed magic and padded the typed profile's commitment with the record-safe profile's zeroed fields. A commitment now opens with the domain string, the algorithm discriminator selects the fields that follow, and each profile commits only its own fields.
- **Little-endian throughout.** The prototype committed big-endian integers; every committed integer is now little-endian, the workspace's one byte order.
- **The Gear table is built from its statement.** The prototype carried 256 literal constants. The table is the first 256 outputs of `SplitMix64` from the first sixty-four fractional bits of the square root of two, generated at compile time by that statement; a unit test pins entries at both ends and the middle against the table as first published, and every entry is equal to the prototype's.
- **Sixty-four-bit typed constants.** Kappa and the cap are sixty-four bits wide, so a power-of-two kappa covers every mask width the record plane admits (up to two to the thirty-second).
- **Unrepresentable states removed.** The algorithm is no longer an argument to the record-safe parameters, so a typed algorithm with record-safe fields cannot be built and its refusal is gone; a seed policy is either unsalted or a public salt, with no unsupported variant to refuse; one `UnsupportedProfileValue` refusal names the field and the raw value in place of four per-field variants.
- **An unreachable refusal removed.** A chunk closes the moment it reaches the record cap, so the prototype's refusal for a record that would cross the record cap before the minimums were met could never fire. It is gone; the byte-cap counterpart, which can fire, stays.
- **Typed errors with no dependency.** Hand-written `Display` and `core::error::Error` implementations, payloads typed (`RecordPosition`, `BytePosition`, `ByteCount`, `ProfileField`, `RawDiscriminator`). The crate is `no_std` over `core` and `alloc`.
- **No bare primitives across the crate's own signatures**, `#[repr(transparent)]` on every single-field wrapper, checked arithmetic wherever a count or a position is concerned, no `as` conversions, and no `unwrap`/`expect`/`panic` outside tests.

The `# Specification` blocks stay prose: the crate has no dependencies, so it carries no `#[spec(...)]` attributes, and every runtime-checkable claim is exercised by its witnesses instead.

## Using it

The typed profile, driven by a caller's own events:

```rust
use gandr_storage_chunker::BoundaryEvent;
use gandr_storage_chunker::BoundaryResidue;
use gandr_storage_chunker::ChunkerError;
use gandr_storage_chunker::CutDecision;
use gandr_storage_chunker::Kappa;
use gandr_storage_chunker::TokenCap;
use gandr_storage_chunker::TokenCount;
use gandr_storage_chunker::TypedChunker;
use gandr_storage_chunker::TypedChunkerParams;

fn example() -> Result<(), ChunkerError> {
    let params = TypedChunkerParams::new(Kappa::try_from(4_u64)?, TokenCap::try_from(64_u64)?);
    let mut scanner = TypedChunker::new(&params);

    let event = BoundaryEvent::new(TokenCount::from(3_u64), BoundaryResidue::from(8_u64));
    assert!(matches!(scanner.on_boundary(event), CutDecision::Cut(_)));

    // A root binds these bytes, not the parsed parameters.
    let _committed = params.commitment();

    Ok(())
}
```

## Ideas and references

The named ideas: content-defined chunking as a cut rule that travels with the data; the Gear rolling hash and the `FastCDC` cut-point discipline the record-safe profile follows; a typed, grammar-directed boundary in place of a byte-level one; and a splittable generator as the stated provenance of a constant table.

- Athicha Muthitacharoen, Benjie Chen, and David Mazières. "A Low-Bandwidth Network File System." In _Proceedings of the Eighteenth ACM Symposium on Operating Systems Principles (SOSP '01)_, pages 174–187, 2001 — the content-defined cut rule.
- Wen Xia, Hong Jiang, Dan Feng, Lei Tian, Min Fu, and Yukun Zhou. "Ddelta: A Deduplication-Inspired Fast Delta Compression Approach." _Performance Evaluation_ 79, 2014 — the Gear rolling hash.
- Wen Xia, Yukun Zhou, Hong Jiang, Dan Feng, Yu Hua, Yuchong Hu, Qing Liu, and Yucheng Zhang. "FastCDC: A Fast and Efficient Content-Defined Chunking Approach for Data Deduplication." In _2016 USENIX Annual Technical Conference (USENIX ATC '16)_, 2016; and Wen Xia, Xiangyu Zou, Hong Jiang, Yukun Zhou, Chuanyi Liu, Dan Feng, Yu Hua, Yuchong Hu, and Yucheng Zhang. "The Design of Fast Content-Defined Chunking for Data Deduplication Based Storage Systems." _IEEE Transactions on Parallel and Distributed Systems_ 31(9), 2020 — the masked Gear test under minimum and maximum limits the record-safe profile follows; it applies the test only between records and does not adopt normalized chunking.
- Trevor Rainey, Nathan Borkowski, Michael Vollmer, Chaitanya Koparkar, Nathan Kainen, and Vidush Singhal. "LoCalMem: Type-Directed Adaptive Serialization for Location- and Content-Addressable Memory." _Proceedings of the ACM on Programming Languages_ 10, ICFP, article 290, August 2026. `doi:10.1145/3828688` — the boundary discipline whose typed chunking profile the typed scanner implements: cuts at a type's own constructor boundaries, a residue divisible by kappa, and a hard token cap.
- Guy L. Steele Jr., Doug Lea, and Christine H. Flood. "Fast Splittable Pseudorandom Number Generators." In _Proceedings of the 2014 ACM International Conference on Object Oriented Programming Systems Languages & Applications (OOPSLA '14)_, 2014. `doi:10.1145/2660193.2660195` — `SplitMix64`, the generator the Gear table is stated by.

## License

Apache-2.0 WITH LLVM-exception.
