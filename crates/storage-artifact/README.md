# gandr-storage-artifact

Kernel artifacts on the authenticated record plane: one record per declaration segment, under a BLAKE3 manifest identity.

<!-- toc -->
- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** `gandr-storage-artifact` stores a kernel artifact — the canonical bytes `gandr-kernel-term`'s encoder writes for an admitted declaration sequence — as a sorted keyed record set in `gandr-storage-records`: the header under the empty key, then each declaration segment under its big-endian admission index. `build` writes the set's record tree into a `BlockStore` and returns the `ArtifactManifest` naming it; `ArtifactManifest::read_under` reads it back through the kernel's bounded decoder. The crate uses `core` and `alloc` under `no_std`.

**Why.** An artifact is a sorted unique keyed record set by construction: admission order keys each declaration, and the format is declaration-segmented. Storing it as records gives it a content identity, structural sharing between artifacts that share declarations, and the record plane's membership and range proofs, with no reshaping of the bytes. A session or a corpus run that persists its kernel environment needs exactly that, and needs the read back to stay as strict as a fresh decode.

**How.** `ArtifactRecordSet::from_artifact` decodes the image and cuts it where the decoder's `SegmentLayout` says each segment ends. `build` builds a `RecordTree` over the header and the declaration records under the caller's `TreeParams`, writes its nodes, and returns a manifest binding the kernel format version, the boundary commitment, the record count and the root node identity; the manifest's identity is BLAKE3 over its domain-separated image. `read_under` refuses a foreign kernel format or boundary commitment before touching the store, loads the root and its leaves through the store's verified load, rebuilds the tree from the loaded records and refuses any disagreement with the manifest, checks the keys, reassembles the image, hands it to `decode` under `MAX_ARTIFACT_EXPANDED_WORK` and the other decode budgets, and refuses records not cut at the decode's segment boundaries.

## Provided features

- `ArtifactRecordSet`: `from_artifact` cuts a kernel artifact at the decoder's segment boundaries; `from_records` builds a set from records in any order and refuses a repeated admission index; `from_stored` reads a stored tree's records back and refuses a misplaced key; `record_refs`, `reassemble` and `ensure_cut_at` give the tree input, the image and the boundary check.
- `ArtifactRecord`, `AdmissionKey`, `SegmentBytes`, `ReassembledArtifact` and `HEADER_KEY`: one declaration record, its fixed-width big-endian key, the segment bytes, the reassembled image and the header's key.
- `build`: the commit path, writing the record tree into a `BlockStore` and returning its `ArtifactManifest`.
- `ArtifactManifest`: `encode`, `decode` and `identity` give a manifest one byte image under `MANIFEST_DOMAIN` and one `ArtifactIdentity` over it; `read_under` reads the artifact back through the kernel's decoder.
- `ArtifactError` and `ManifestField`: every refusal by name — the kernel's, the record plane's, a repeated key, each manifest field, a foreign format or commitment, a tree mismatch, a misplaced record and a record off a segment boundary.
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
| The artifact manifest | [`manifest`](src/manifest.rs) |
| Certificate transport | [`transport`](src/transport.rs) |

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
