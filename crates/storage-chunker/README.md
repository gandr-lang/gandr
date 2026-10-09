# gandr-storage-chunker

Content-defined chunk boundaries over canonical records or typed boundary events, under parameters a downstream root commits.

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Two profiles](#two-profiles)
- [Parameter commitments](#parameter-commitments)
- [License](#license)

## Synopsis

**What.** `gandr-storage-chunker` decides where a stream of canonical units is cut and reports each cut's reason. It provides a record-safe Gear scanner and a typed scanner over caller-reported boundary events. The crate uses `core` and `alloc` under `no_std`; the anodized facade supplies executable specification checks.

**Why.** Position-based cuts shift after an insertion, changing the identity of otherwise unchanged chunks. Content-defined cuts let boundaries resynchronize after an edit, enabling storage consumers to share unchanged chunks. Explicit parameter commitments let a root bind the rule that produced its partition.

**How.** The record-safe profile scans canonical bytes with a Gear rolling hash and tests for cuts only between records, under byte and record limits. The typed profile accumulates token counts and cuts at an admissible event when its residue is divisible by kappa or its pending count reaches the cap. Both scanners make one forward pass without lookahead; hashing chunks and storing them belong to the consumer.

## References

- Athicha Muthitacharoen, Benjie Chen, and David Mazières. "A Low-Bandwidth Network File System." _Proceedings of the Eighteenth ACM Symposium on Operating Systems Principles (SOSP '01)_, pages 174–187, 2001. [doi:10.1145/502034.502052](https://doi.org/10.1145/502034.502052) — content-defined cuts that resynchronize after edits.
- Wen Xia, Hong Jiang, Dan Feng, Lei Tian, Min Fu, and Yukun Zhou. "Ddelta: A Deduplication-Inspired Fast Delta Compression Approach." _Performance Evaluation_ 79, pages 258–272, 2014. [doi:10.1016/j.peva.2014.07.016](https://doi.org/10.1016/j.peva.2014.07.016) — the Gear rolling hash.
- Wen Xia, Yukun Zhou, Hong Jiang, Dan Feng, Yu Hua, Yuchong Hu, Qing Liu, and Yucheng Zhang. "FastCDC: A Fast and Efficient Content-Defined Chunking Approach for Data Deduplication." _2016 USENIX Annual Technical Conference (USENIX ATC '16)_, 2016. [USENIX publication](https://www.usenix.org/conference/atc16/technical-sessions/presentation/xia), ISBN 978-1-931971-30-0 — the masked Gear cut test under size limits.
- Wen Xia, Xiangyu Zou, Hong Jiang, Yukun Zhou, Chuanyi Liu, Dan Feng, Yu Hua, Yuchong Hu, and Yucheng Zhang. "The Design of Fast Content-Defined Chunking for Data Deduplication Based Storage Systems." _IEEE Transactions on Parallel and Distributed Systems_ 31(9), 2020. [doi:10.1109/TPDS.2020.2984632](https://doi.org/10.1109/TPDS.2020.2984632) — the cut-point discipline, applied here only between records and without normalized chunking.
- Michael Rainey, Michael H. Borkowski, Michael Vollmer, Chaitanya S. Koparkar, Mikah Kainen, and Vidush Singhal. "LoCalMem: Type-Directed Adaptive Serialization for Location- and Content-Addressable Memory." _Proceedings of the ACM on Programming Languages_ 10, ICFP, article 290, August 2026. [doi:10.1145/3828688](https://doi.org/10.1145/3828688) — typed constructor boundaries, residue divisibility and a token cap.
- Guy L. Steele Jr., Doug Lea, and Christine H. Flood. "Fast Splittable Pseudorandom Number Generators." _Proceedings of the 2014 ACM International Conference on Object Oriented Programming Systems Languages & Applications (OOPSLA '14)_, 2014. [doi:10.1145/2660193.2660195](https://doi.org/10.1145/2660193.2660195) — `SplitMix64`, which generates the Gear table.

## Provided features

- `chunk_record_slices` and `chunk_spans` partition canonical records without splitting a record.
- `TypedChunker::on_boundary` reports a cut or continuation and identifies the cut reason.
- Validated parameter types reject zero kappa, zero token cap and inconsistent record-safe limits.
- `ParameterCommitment` encodes either profile for downstream root commitments.
- `ChunkerError` distinguishes invalid parameters, invalid spans and arithmetic failures.

## Expected features

Consumers supply canonical record bytes or grammar-admissible boundary events. A typed event carries the tokens since the preceding event and a residue from the consumer's committed hash rule. The scanner does not derive residues or validate the grammar.

A consumer defining chunk identities must bind the parameter commitment alongside its content. Use an allocator for the crate's `alloc`-backed results; `std` is not required.

## Examples

Drive the typed profile with a boundary whose residue satisfies the cut predicate:

```rust
use gandr_storage_chunker::BoundaryEvent;
use gandr_storage_chunker::BoundaryReason;
use gandr_storage_chunker::BoundaryResidue;
use gandr_storage_chunker::ChunkerError;
use gandr_storage_chunker::CutDecision;
use gandr_storage_chunker::Kappa;
use gandr_storage_chunker::TokenCap;
use gandr_storage_chunker::TokenCount;
use gandr_storage_chunker::TypedChunker;
use gandr_storage_chunker::TypedChunkerParams;

fn main() -> Result<(), ChunkerError> {
    let kappa = Kappa::try_from(4_u64)?;
    let cap = TokenCap::try_from(64_u64)?;
    let params = TypedChunkerParams::new(kappa, cap);
    let mut scanner = TypedChunker::new(&params);
    let event = BoundaryEvent::new(TokenCount::from(3_u64), BoundaryResidue::from(8_u64));

    assert_eq!(scanner.on_boundary(event), CutDecision::Cut(BoundaryReason::HashPredicate));
    assert_eq!(scanner.pending(), TokenCount::ZERO);

    // A downstream root binds these bytes.
    let _committed = params.commitment();
    Ok(())
}
```

Run the crate's tests from the repository root:

```sh
mise exec -- cargo test -p gandr-storage-chunker
```

## Two profiles

The profiles admit different cut positions and commit only the fields they use.

| Profile | Input | Cut rule | Parameters |
| ------- | ----- | -------- | ---------- |
| Record-safe (`ChunkerParams`) | Canonical record slices, or one buffer with record spans | Masked Gear predicate between complete records, subject to minimums and byte or record caps | Gear table, seed policy and salt, normalization, record-boundary rule, byte limits, record limits |
| Typed (`TypedChunkerParams`) | Token count and residue at each admissible boundary | Pending count reaches the token cap, otherwise residue is divisible by kappa | Kappa and token cap |

The typed scanner cuts only at reported events; a multi-token event can take the pending count past the cap. The cap takes precedence over the hash predicate, and a cut resets the count. One token per record with a power-of-two kappa gives the record-boundary rule used by `gandr-storage-records`.

The Gear table is generated at compile time from the first 256 outputs of `SplitMix64`, seeded by the first sixty-four fractional bits of the square root of two. A seed policy selects either the unsalted state or a public salt.

## Parameter commitments

A commitment opens with `gandr:storage-chunker:params:v1`, followed by an algorithm discriminator and that profile's fields. Every integer has a fixed width and little-endian encoding; the typed profile's kappa and token cap are both sixty-four bits. This framing distinguishes profiles without padding one profile with another's unused fields.

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
