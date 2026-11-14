# gandr-storage-artifact

Kernel artifacts on the authenticated record plane and the content-addressed value plane: one record per distinct declaration segment, keyed by the identity of the value leaf that holds its bytes, under a BLAKE3 manifest identity or a content pointer.

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

**What.** `gandr-storage-artifact` stores a kernel artifact — the canonical bytes `gandr-kernel-term`'s encoder writes for an admitted declaration sequence — in `gandr-storage-records` as an index tree of two records and one value leaf per distinct declaration segment. The index holds the header under the empty key and the order under `ORDER_KEY`. The order opens with the set's `Naming`, holds each record's key once, in key order, then four bytes per declaration: the slot of the record that stands there, and in a named set the kernel's content key of the entry. A record's key is the identity of its value leaf, so no record stores a key beside its bytes. An artifact never mixes the two forms: an admission whose artifact the store keeps names every place, and an export cut from bytes alone names none. `build` writes the index tree and the value leaves into a `BlockStore` and returns the `ArtifactManifest` naming them; `ArtifactManifest::read_under` reads them back through the kernel's bounded decoder. The crate uses `core` and `alloc` under `no_std`.

**Why.** An artifact is declaration-segmented, and a record keyed by the identity of its bytes' value leaf names the same bytes in every artifact that holds them. Storing it as records gives it a content identity, structural sharing between artifacts that share declarations at any position, and the record plane's authenticated loads, with no reshaping of the bytes. An insertion rewrites the order and the records whose bytes it changes; each other record stays. A session or a corpus run that persists its kernel environment needs exactly that, and needs the read back to stay as strict as a fresh decode.

**How.** `ArtifactRecordSet::from_artifact` decodes the image, cuts it where the decoder's `SegmentLayout` says each segment ends, and names each segment through one `ValueLeafHasher`, one pass over its bytes. A table that the digest's leading bytes index gives equal segments one record, so the records stand in the order of their first place with no sort. `build` builds a `RecordTree` over the header and the order under the caller's `TreeParams` and writes its nodes. It admits each record's value leaf as a `NamedValue`, so a store hashes no record a second time. It returns a manifest binding the kernel format version, the boundary commitment, the record count, the index root's identity and the set's naming; the manifest's identity is BLAKE3 over its domain-separated image. `read_under` refuses a foreign kernel format or boundary commitment before touching the store, loads the index root and its leaves through the store's verified load, rebuilds the index and refuses any disagreement with the manifest, checks the order whole, loads each value leaf through the store's verified load — the one hash that gives its key — refuses a record count or a form that is not the manifest's, reassembles the image, hands it to `decode` under `MAX_ARTIFACT_EXPANDED_WORK` and the other decode budgets, and refuses records not cut at the decode's segment boundaries.

## References

- `Rainey-2026-localmem_typedirected_adaptive_serialization_location_contentaddressable_memory` — exemplar: Michael Rainey, Michael H. Borkowski, Michael Vollmer, Chaitanya S. Koparkar, Mikah Kainen, and Vidush Singhal. "LoCalMem: Type-Directed Adaptive Serialization for Location- and Content-Addressable Memory." _Proceedings of the ACM on Programming Languages_ 10, ICFP, article 290, August 2026. [doi:10.1145/3828688](https://doi.org/10.1145/3828688); [mechanization artifact, doi:10.5281/zenodo.20315616](https://doi.org/10.5281/zenodo.20315616) — the CAM a keyed artifact instantiates, and the token-bound lemmas whose scope the crate root states.
- `vault:01a178ab-17e5-7352-bc0b-3caa7f1e476c` — anchor: the storage programme (§ storage-programme-gluing) — a record names its bytes and never its position, so a record under its value leaf's identity stays where it is across an insertion.
- `vault:01a178aa-ce14-7610-bcad-5aab5f9c0b0f` — background: the integrity design (§ two walls) — a pointer proves which bytes, so the value-plane codec checks the stream's shape alone and the kernel's decoder decides the bytes.

## Provided features

- `ArtifactRecordSet`: `from_artifact` cuts a kernel artifact at the decoder's segment boundaries, and `from_artifact_keeping` and `from_artifact_after` cut it through a decode resumed after a kept prefix; `from_segments` builds a set from a header and segments in order; `named` puts the kernel's content key of each entry beside its place and refuses a count that differs or a place without a name; `from_stored` reads a stored index and its value leaves back and refuses a misplaced record, a malformed order, keys out of order, a slot past the keys, a key without a place and a leaf that is not a value leaf; `places`, `names`, `naming`, `segments`, `order_image`, `record_refs`, `reassemble` and `ensure_cut_at` give the order, the names, their form, the segments in order, the order's record, the index tree's input, the image and the boundary check. Its `CanonicalValue` commits the set through `gandr-storage-values`, the artifact's constructor giving its form and each place's constructor holding the one before, so an edit shares every chunk before the edited declaration.
- `ArtifactRecord`, `RecordKey`, `Place`, `ContentName`, `Naming`, `unnamed`, `OrderImage`, `SegmentBytes`, `ReassembledArtifact`, `HEADER_KEY` and `ORDER_KEY`: one declaration record, its key — the identity of its value leaf — one place of the order and its slot, the kernel's content key, the form of a set's names, why a set has none, the order's bytes, the segment bytes, the reassembled image, and the keys of the header and the order.
- `build`: the commit path, writing the index tree and the value leaves into a `BlockStore` and returning their `ArtifactManifest`.
- `ArtifactManifest`: `encode`, `decode` and `identity` give a manifest one byte image under `MANIFEST_DOMAIN`, at layout version two, and one `ArtifactIdentity` over it; `read_under` reads the artifact back through the kernel's decoder.
- `ArtifactError` and `ManifestField`: every refusal by name — the kernel's, the record plane's, a malformed order, a place without its record, a record without a place, names that do not match the places, each manifest field, a foreign format or commitment, a tree mismatch, an order whose form is not the manifest's, a misplaced record and a record off a segment boundary.
- `transport`: canonical certificate-step encoding, durable `TransportStepId` readback and collision-checked graded factorization.

## Expected features

A consumer supplies the `BlockStore` and the `TreeParams` an artifact is committed and read under; a reader states the parameters it expects, and `read_under` refuses an artifact committed under any other boundary rule. A persistent store implements `BlockStore`'s verified load. A decoded artifact is not an admitted one: a consumer that trusts its declarations admits them through `gandr-kernel-core`'s choke point first.

The optional executable specification checks use `--cfg anodized_panic` across the dependency graph, as in the enforcing test lane.

Function predicates check current fields and captured transition state without replaying generic store I/O. Each nontrivial contract states bounded evidence in its `# Adequacy` section; formatter output, parser history and opaque strategy support use explicit exemptions where the item cannot observe the claimed property.

## Examples

Commit a one-declaration artifact and read it back:

```rust
use gandr_kernel_term::AdmissionMark;
use gandr_kernel_term::DeclarationBuilder;
use gandr_kernel_term::LevelSignature;
use gandr_kernel_term::MarkedDeclaration;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::decode;
use gandr_kernel_term::encode;
use gandr_storage_artifact::ArtifactError;
use gandr_storage_artifact::ArtifactRecordSet;
use gandr_storage_artifact::build;
use gandr_storage_records::InMemoryBlockStore;
use gandr_storage_records::TreeParams;

fn example() -> Result<(), ArtifactError> {
    let mut arena = TermArena::new();
    let declared = arena.value_type_unit();
    let body = arena.value_unit();
    let declaration =
        DeclarationBuilder::new(&mut arena).def(LevelSignature::monomorphic(), declared, body);
    let artifact = encode(&arena, &[MarkedDeclaration::new(AdmissionMark::Checked, declaration)]);

    let records = ArtifactRecordSet::from_artifact(artifact.as_image())?;
    let mut store = InMemoryBlockStore::new();
    let manifest = build(&records, TreeParams::current(), &mut store)?;

    let read = manifest.read_under(&store, TreeParams::current())?;
    assert_eq!(decode(artifact.as_image())?, read);
    Ok(())
}
```

Run the crate's tests, then the enforcing twin:

```sh
cargo nextest run -p gandr-storage-artifact
RUSTFLAGS='--cfg anodized_panic' cargo nextest run -p gandr-storage-artifact
```

## Where the detail lives

Mechanism, decisions with their alternatives and reversals, and witnesses live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| Integrity and validity, the kernel reader, scope of the mechanized bounds, laws and their witnesses, references | [`src/lib.rs`](src/lib.rs) |
| The record layout, the cuts, the declaration grain | [`record`](src/record.rs) |
| The set on the value plane: its tokens, the nesting and the index gaps | [`record::value`](src/record/value.rs) |
| The artifact manifest | [`manifest`](src/manifest.rs) |
| Certificate transport | [`transport`](src/transport.rs) |

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
