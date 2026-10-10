# gandr-storage-artifact

Kernel artifacts on the authenticated record plane: one record per declaration segment, under a BLAKE3 manifest identity.

- [Synopsis](#synopsis)
- [References](#references)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [The record layout](#the-record-layout)
- [Cuts come from the decoder](#cuts-come-from-the-decoder)
- [The artifact manifest](#the-artifact-manifest)
- [Integrity and validity](#integrity-and-validity)
- [The only storage crate that reads the kernel](#the-only-storage-crate-that-reads-the-kernel)
- [The declaration is the record grain](#the-declaration-is-the-record-grain)
- [Scope of the mechanized bounds](#scope-of-the-mechanized-bounds)
- [Certificate transport](#certificate-transport)
- [Laws and their witnesses](#laws-and-their-witnesses)
- [License](#license)

## Synopsis

**What.** `gandr-storage-artifact` stores a kernel artifact — the canonical bytes `gandr-kernel-term`'s encoder writes for an admitted declaration sequence — as a sorted keyed record set in `gandr-storage-records`: the header under the empty key, then each declaration segment under its big-endian admission index. `build` writes the set's record tree into a `BlockStore` and returns the `ArtifactManifest` naming it; `ArtifactManifest::read_under` reads it back through the kernel's bounded decoder. The crate uses `core` and `alloc` under `no_std`.

**Why.** An artifact is a sorted unique keyed record set by construction: admission order keys each declaration, and the format is declaration-segmented. Storing it as records gives it a content identity, structural sharing between artifacts that share declarations, and the record plane's membership and range proofs, with no reshaping of the bytes. A session or a corpus run that persists its kernel environment needs exactly that, and needs the read back to stay as strict as a fresh decode.

**How.** `ArtifactRecordSet::from_artifact` decodes the image and cuts it where the decoder's `SegmentLayout` says each segment ends. `build` builds a `RecordTree` over the header and the declaration records under the caller's `TreeParams`, writes its nodes, and returns a manifest binding the kernel format version, the boundary commitment, the record count and the root node identity; the manifest's identity is BLAKE3 over its domain-separated image. `read_under` refuses a foreign kernel format or boundary commitment before touching the store, loads the root and its leaves through the store's verified load, rebuilds the tree from the loaded records and refuses any disagreement with the manifest, checks the keys, reassembles the image, hands it to `decode` under `MAX_ARTIFACT_EXPANDED_WORK` and the other decode budgets, and refuses records not cut at the decode's segment boundaries.

## References

- Michael Rainey, Michael H. Borkowski, Michael Vollmer, Chaitanya S. Koparkar, Mikah Kainen, and Vidush Singhal. "LoCalMem: Type-Directed Adaptive Serialization for Location- and Content-Addressable Memory." _Proceedings of the ACM on Programming Languages_ 10, ICFP, article 290, August 2026. [doi:10.1145/3828688](https://doi.org/10.1145/3828688); [mechanization artifact, doi:10.5281/zenodo.20315616](https://doi.org/10.5281/zenodo.20315616) — the content-addressable model a keyed artifact instantiates, and the token-bound lemmas whose scope [a section below](#scope-of-the-mechanized-bounds) states.
- Alex Auvolat and François Taïani. "Merkle Search Trees: Efficient State-Based CRDTs in Open Networks." _38th IEEE International Symposium on Reliable Distributed Systems (SRDS)_, 2019. [arXiv:1908.05808](https://arxiv.org/abs/1908.05808) — an authenticated ordered structure whose shape is a function of its records, which is what makes the identity independent of build order.
- Jack O'Connor, Jean-Philippe Aumasson, Samuel Neves, and Zooko Wilcox-O'Hearn. "BLAKE3: One Function, Fast Everywhere." Specification, 2020. [BLAKE3 specification](https://github.com/BLAKE3-team/BLAKE3-specs) — the digest the manifest identity is taken in.

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

## The record layout

| Key | Value |
| --- | ----- |
| the empty key | the header: magic, version, minted-atom table, declaration count |
| admission index `i`, eight bytes big-endian | declaration segment `i` |

The header sits under the empty key, which sorts before every admission key, so the artifact image is the concatenation of the record values in key order and the record tree's root binds every byte of it. A record count is the declaration count plus one.

A segment may reference subterm-table entries an earlier segment introduced, so a record is a content-addressing grain and never an independently decodable unit: the reader reassembles the whole image and decodes it once.

Executable record refinements bind each key to its index and require strictly increasing, unique keys. Raw header and segment bytes, empty sets and noncontiguous indices remain admissible; those refinements do not certify kernel validity. Mutation witnesses separately corrupt the key binding, ordering and uniqueness.

**Choice.** The key is big-endian at a fixed width of eight bytes, and the header is a record of its own. **Alternatives.** A little-endian key, which the recorded design names, sorts index 256 before index 2 bytewise, and the record plane orders keys bytewise, so key order would stop being admission order past 255 declarations. The prior implementation kept the header beside the tree rather than in it, so its identity did not bind the header's bytes and a reader needed the header from somewhere else; here one root covers the whole image. **Reversal.** A record plane that orders keys by a typed comparison rather than bytewise makes the key's byte order free.

## Cuts come from the decoder

`from_artifact` decodes the image before it cuts it, and cuts where `DecodedArtifact::segments` reports each segment ends, so every set the commit path builds was decoded, budget-checked and delimited by the kernel first. On the way back, `ensure_cut_at` refuses a stored set whose bytes decode but whose records straddle or split segments: the boundaries a reader trusts are its own decoder's, never a writer's.

**Alternatives.** A segmenting encoder that reports its own cuts, as the prior implementation's `write_segmented` did, makes the writer the authority on where records end. A second parser of the format here would drift from the kernel's. **Reversal.** None planned: the decoder is the format's one reader.

## The artifact manifest

```text
image    := "gandr:storage-artifact:manifest:v1"
         || u16le manifest version
         || u16le kernel format version
         || u64le commitment length || boundary commitment
         || u64le record count
         || 32-byte root node identity
identity := BLAKE3(image)
```

**Choice.** The identity binds the record plane's boundary commitment, the record count, the root node identity and the kernel format version, under its own domain and its own type, `ArtifactIdentity`. The commitment is `TreeParams::boundary_commitment`, carried opaque; the root node's bytes carry the record encoding version, so the node identity binds that too. The hashing scheme is the value plane's, not a second one — one domain-separated image per manifest, BLAKE3 over it, a fixed-width little-endian layout, the reader's profile checked before any load. The type is distinct because an artifact identity and a value manifest digest name different things, and a signature that takes one must refuse the other. `decode` admits every kernel format and commitment, and `read_under` decides whether the reader shares them.

**Alternatives.** Typing the identity as `gandr-storage-values`' `ManifestDigest` would let an artifact identity stand where a committed value's is expected and compile. Binding the record tree's `TreeRoot` digest instead of its root node identity would leave a reader nothing to load the tree by. Copying the prior implementation's fixed 93-byte chunker commitment would carry a second commitment format beside the record plane's own. **Reversal.** A second manifest layout, or a reader that must recognise a value manifest and an artifact manifest in one slot, makes the shared scheme a shared type.

The manifest refinement admits only layout version one without narrowing the opaque metadata. The owned image refinement checks the exact domain, version and commitment length against the complete frame without allocating or decoding the kernel. Fixed witnesses reject every proper golden prefix, inconsistent lengths and trailing bytes, while retaining empty commitments, zero and maximum record counts, and future kernel versions as metadata.

## Integrity and validity

A matching identity proves which bytes these are, never that they are a valid artifact. `read_under` first establishes integrity — the stored records rebuild exactly the tree the manifest names, under the reader's own parameters — and then hands validity to the kernel's decoder alone, under its work budgets. `a_matching_identity_over_bytes_the_kernel_refuses_is_refused` holds the line: a tree whose identity matches the one the reader holds, over a header whose magic is one byte off, is refused with the decoder's own refusal. Nothing here re-checks typing, and nothing short-circuits the decoder because a hash matched; a decoded artifact is still unadmitted, and admission is the consumer's next wall.

## The only storage crate that reads the kernel

`gandr-storage-records` and `gandr-storage-values` stay kernel-free, so a consumer of the planes alone never pulls the kernel in; this crate is the one storage crate that depends on `gandr-kernel-term`. **Alternatives.** The export inside `gandr-storage-records` would make every record-plane consumer compile the kernel; the export inside the kernel would put storage plumbing and hashing in the trusted tier. **Reversal.** An outside consumer that needs the kernel export through the planes it already takes, without this crate.

## The declaration is the record grain

The record is the declaration segment, and nothing cuts inside one: no scanner here reads `NODE_TAG_TABLE`'s storage columns, and the record plane's content-defined leaves group whole records. The declaration boundary is the replay grain and the checkpoint grain as well, so one grain serves all three. Were a codec to cut inside segments, the table's conservative alias column governs which constructors are boundaries; the threshold column stays recorded with no reader. **Alternatives.** A value-plane codec over each segment, cut at the conservative column's boundary set, shares structure below a declaration at the cost of a second chunk language for one artifact. **Reversal.** A measured artifact whose single declarations outgrow the record plane's node budget, or whose edits land inside large declarations often enough that per-declaration records stop sharing.

## Scope of the mechanized bounds

The checked lemmas that bound a node's storage tokens under LoCalMem's boundary discipline quantify over this kernel's node tags `0x00` to `0x17`: twenty-four tags. `NODE_TAG_TABLE` holds thirty, `0x00` to `0x1D`; the six from `0x18` — the dependent arrow, the value-type decoding former, the computation-type universe, the computation-type decoding former and the two quote formers — are outside the bounds, as is any tag added later. Nothing in this crate reads a bound or a classification column, so no result here rests on the lemmas, and reconciling their vocabulary with the table is not this crate's work.

## Laws and their witnesses

| Statement | Witness |
| --------- | ------- |
| The manifest's image is a fixed layout and its identity is BLAKE3 of it | `manifest::tests::the_manifest_layout_is_golden`, `manifest::tests::the_identity_is_blake3_of_the_canonical_bytes` |
| The golden round-trips; every proper prefix and selected malformed fields receive the named refusal | `manifest::tests::the_manifest_round_trips_through_decode`, `manifest::tests::an_unknown_manifest_version_is_refused`, `manifest::tests::a_malformed_manifest_is_rejected`, `manifest::tests::a_bad_commitment_length_is_rejected`, `manifest::tests::truncation_at_every_prefix_is_rejected` |
| Perturbing each supplied manifest field changes the identity | `manifest::tests::any_field_perturbation_changes_the_identity` |
| A set is canonical in its record order and refuses a repeated index | `record::tests::from_records_sorts_any_permutation_canonically`, `record::tests::a_duplicate_admission_key_is_rejected` |
| Admission keys preserve numeric order across every native-word byte carry | `record::tests::admission_keys_preserve_numeric_order_across_byte_carries` |
| Cursor reads preserve exact suffixes and distinguish refusal before and after a length prefix | `manifest::tests::cursor_transitions_preserve_suffixes_and_refusal_positions` |
| Identity rendering preserves every byte and propagates sink refusal; diagnostic variants retain their payloads | `manifest::tests::identity_rendering_preserves_all_bytes_and_refusals`, `error::tests::every_refusal_renders_apart`, `error::tests::every_manifest_field_renders_apart` |
| The records reassemble to the artifact byte for byte | `artifact_contract::records_round_trip_to_a_byte_identical_artifact`, `artifact_contract::round_trip_over_generated_environments` |
| Repeated and permuted builds agree; header and segment perturbations change the identity | `artifact_contract::the_same_artifact_mints_the_same_identity`, `artifact_contract::a_permuted_build_order_yields_the_same_identity`, `artifact_contract::any_perturbation_changes_the_identity` |
| A committed artifact reads back as the decode of its own image, from a leaf root and from an internal one | `artifact_contract::tree_nodes_store_and_reopen`, `artifact_contract::round_trip_over_generated_environments` |
| The previous record encoding is refused before any node is written | `artifact_contract::unsupported_build_parameters_do_not_write_nodes` |
| A foreign kernel format or boundary rule is refused before any load | `artifact_contract::a_foreign_profile_or_format_is_refused_before_any_load` |
| A matching identity over bytes the kernel refuses is refused | `artifact_contract::a_matching_identity_over_bytes_the_kernel_refuses_is_refused` |
| Misplaced keys and records off a segment boundary are refused | `artifact_contract::a_stored_tree_with_misplaced_keys_is_refused`, `artifact_contract::records_cut_off_a_segment_boundary_are_refused` |

The `artifact_contract` witnesses live in `tests/artifact_contract.rs`, module `artifact_contract`.

## Certificate transport

`transport_step_id` hashes resolved sequent-cell content together with its application position. `TransportStepId` is a 32-byte BLAKE3 digest, with exact-width readback and no conversion to or from a build-local `PrimId`. Compile-fail witnesses enforce the type boundary; a 16-byte local-label image is refused. Hash equality identifies bytes, not proof validity.

The preimage is `gandr:transport-step:v1` followed by the borrowed fields from `theory-decomposition-spaces::transport::step_fields`. `StepIdEncoder` frames tags and checked counts as big-endian u64 values, and names as a checked u64 byte length followed by their UTF-8 bytes. It hashes incrementally without allocating a preimage. Cell content and position determine the result; allocation, insertion order and local labels do not.

`transport_step_index` resolves every normal-form primitive in the supplied store and preserves its grading under a durable key. Equal recorded factors sum multiplicities with u32 saturation; distinct factors at one digest refuse with both factors retained in the error. Unknown cells and unrepresentable widths refuse the entire result. Index values retain local replay handles: only the keys are portable, and an index is not a serialized certificate or a replay-validity witness.

**Choice.** Theory supplies borrowed structural fields; storage owns canonical framing and transport identity. The v1 format fixes widths and byte order independently of `Hash`. BLAKE3 uses the workspace dependency with defaults off and no additional features. **Alternatives.** Build-local hashes cannot address transport bytes; a byte buffer adds allocation per digest; a theory-to-storage dependency reverses layering. **Reversal.** A changed structural encoding needs a distinct versioned domain; a second alphabet can extend the structural field surface.

`tests/certificate_transport.rs::tests::a_publicly_composed_tracelet_round_trips_its_step_identities` composes through the public theory API, normalizes, encodes twice, decodes the identity images, resolves their factors and replays the reconstructed schedule. The two golden identities pin framing and the complete frame-defining cell. Six framing/width witnesses and ten identity/index witnesses form the compatibility floor, with no deferred rows. The 32-bit ceiling witness models a u32 source on every host; its successor witness runs on 64-bit targets.

The standalone mutation backlog covers the transport modules introduced after `1793bad` by `feat(storage): add certificate transport identities`. Target faults: omitted fields, reordered traversal, native-width encoding, lost byte-length prefixes, accepted non-32-byte images, merged unequal factors and dropped multiplicities. Observers are literal fields, pinned digest goldens, exact refusals and replay through decoded identities; finite witnesses do not establish collision resistance.

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
