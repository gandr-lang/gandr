//! Kernel artifacts on the authenticated record plane: one record per
//! declaration segment, under a BLAKE3 manifest identity.
//!
//! [`ArtifactRecordSet::from_artifact`] cuts a kernel artifact where the
//! kernel's decoder finds its segments end: the header under the empty key,
//! each declaration under its big-endian admission index. [`build`] writes the
//! set's record tree into a [`BlockStore`] and returns the
//! [`ArtifactManifest`] naming it; [`ArtifactManifest::identity`] is the one
//! identity an artifact has. [`ArtifactManifest::read_under`] reads the tree
//! back, checks it against the manifest, and hands the reassembled bytes to
//! the kernel's bounded decoder.
//!
//! # Integrity and validity
//!
//! The manifest identity addresses and authenticates bytes; it never vouches
//! for them. Validity is the kernel's decoder's alone, and admission after it
//! the consumer's.
//!
//! A matching identity proves which bytes these are, never that they are a
//! valid artifact. `read_under` first establishes integrity — the stored
//! records rebuild exactly the tree the manifest names, under the reader's own
//! parameters — and then hands validity to the kernel's decoder alone, under
//! its work budgets.
//! `a_matching_identity_over_bytes_the_kernel_refuses_is_refused` holds the
//! line: a tree whose identity matches the one the reader holds, over a header
//! whose magic is one byte off, is refused with the decoder's own refusal.
//! Nothing here re-checks typing, and nothing short-circuits the decoder
//! because a hash matched; a decoded artifact is still unadmitted, and
//! admission is the consumer's next wall.
//!
//! # Records and the manifest
//!
//! The record layout and where its cuts come from are stated in the `record`
//! module; the artifact manifest, its image and what its identity binds, in the
//! `manifest` module.
//!
//! # The only storage crate that reads the kernel
//!
//! `gandr-storage-records` and `gandr-storage-values` stay kernel-free, so a
//! consumer of the planes alone never pulls the kernel in; this crate is the
//! one storage crate that depends on `gandr-kernel-term`. **Alternatives.** The
//! export inside `gandr-storage-records` would make every record-plane consumer
//! compile the kernel; the export inside the kernel would put storage plumbing
//! and hashing in the trusted tier. **Reversal.** An outside consumer that
//! needs the kernel export through the planes it already takes, without this
//! crate.
//!
//! # Scope of the mechanized bounds
//!
//! The checked lemmas that bound a node's storage tokens under `LoCalMem`'s
//! boundary discipline quantify over this kernel's node tags `0x00` to `0x17`:
//! twenty-four tags. `NODE_TAG_TABLE` holds thirty, `0x00` to `0x1D`; the six
//! from `0x18` — the dependent arrow, the value-type decoding former, the
//! computation-type universe, the computation-type decoding former and the two
//! quote formers — are outside the bounds, as is any tag added later. Nothing
//! in this crate reads a bound or a classification column, so no result here
//! rests on the lemmas, and reconciling their vocabulary with the table is not
//! this crate's work.
//!
//! # Laws and their witnesses
//!
//! | Statement | Witness |
//! | --------- | ------- |
//! | The manifest's image is a fixed layout and its identity is BLAKE3 of it | `manifest::tests::the_manifest_layout_is_golden`, `manifest::tests::the_identity_is_blake3_of_the_canonical_bytes` |
//! | The golden round-trips; every proper prefix and selected malformed fields receive the named refusal | `manifest::tests::the_manifest_round_trips_through_decode`, `manifest::tests::an_unknown_manifest_version_is_refused`, `manifest::tests::a_malformed_manifest_is_rejected`, `manifest::tests::a_bad_commitment_length_is_rejected`, `manifest::tests::truncation_at_every_prefix_is_rejected` |
//! | Perturbing each supplied manifest field changes the identity | `manifest::tests::any_field_perturbation_changes_the_identity` |
//! | A set is canonical in its record order and refuses a repeated index | `record::tests::from_records_sorts_any_permutation_canonically`, `record::tests::a_duplicate_admission_key_is_rejected` |
//! | Admission keys preserve numeric order across every native-word byte carry | `record::tests::admission_keys_preserve_numeric_order_across_byte_carries` |
//! | Cursor reads preserve exact suffixes and distinguish refusal before and after a length prefix | `manifest::tests::cursor_transitions_preserve_suffixes_and_refusal_positions` |
//! | Identity rendering preserves every byte and propagates sink refusal; diagnostic variants retain their payloads | `manifest::tests::identity_rendering_preserves_all_bytes_and_refusals`, `error::tests::every_refusal_renders_apart`, `error::tests::every_manifest_field_renders_apart` |
//! | The records reassemble to the artifact byte for byte | `artifact_contract::records_round_trip_to_a_byte_identical_artifact`, `artifact_contract::round_trip_over_generated_environments` |
//! | Repeated and permuted builds agree; header and segment perturbations change the identity | `artifact_contract::the_same_artifact_mints_the_same_identity`, `artifact_contract::a_permuted_build_order_yields_the_same_identity`, `artifact_contract::any_perturbation_changes_the_identity` |
//! | A committed artifact reads back as the decode of its own image, from a leaf root and from an internal one | `artifact_contract::tree_nodes_store_and_reopen`, `artifact_contract::round_trip_over_generated_environments` |
//! | An unsupported record encoding is refused before any node is written | `artifact_contract::unsupported_build_parameters_do_not_write_nodes` |
//! | A foreign kernel format or boundary rule is refused before any load | `artifact_contract::a_foreign_profile_or_format_is_refused_before_any_load` |
//! | A matching identity over bytes the kernel refuses is refused | `artifact_contract::a_matching_identity_over_bytes_the_kernel_refuses_is_refused` |
//! | Misplaced keys and records off a segment boundary are refused | `artifact_contract::a_stored_tree_with_misplaced_keys_is_refused`, `artifact_contract::records_cut_off_a_segment_boundary_are_refused` |
//!
//! The `artifact_contract` witnesses live in `tests/artifact_contract.rs`,
//! module `artifact_contract`.
//!
//! # References
//!
//! - Michael Rainey, Michael H. Borkowski, Michael Vollmer, Chaitanya S.
//!   Koparkar, Mikah Kainen, and Vidush Singhal. "`LoCalMem`: Type-Directed
//!   Adaptive Serialization for Location- and Content-Addressable Memory."
//!   _Proceedings of the ACM on Programming Languages_ 10, ICFP, article 290,
//!   August 2026. [doi:10.1145/3828688](https://doi.org/10.1145/3828688);
//!   [mechanization artifact,
//!   doi:10.5281/zenodo.20315616](https://doi.org/10.5281/zenodo.20315616) —
//!   the content-addressable model a keyed artifact instantiates, and the
//!   token-bound lemmas whose scope § Scope of the mechanized bounds states.
//! - Alex Auvolat and François Taïani. "Merkle Search Trees: Efficient
//!   State-Based CRDTs in Open Networks." _38th IEEE International Symposium on
//!   Reliable Distributed Systems (SRDS)_, 2019.
//!   [arXiv:1908.05808](https://arxiv.org/abs/1908.05808) — an authenticated
//!   ordered structure whose shape is a function of its records, which is what
//!   makes the identity independent of build order.
//! - Jack O'Connor, Jean-Philippe Aumasson, Samuel Neves, and Zooko
//!   Wilcox-O'Hearn. "BLAKE3: One Function, Fast Everywhere." Specification,
//!   2020. [BLAKE3 specification](https://github.com/BLAKE3-team/BLAKE3-specs)
//!   — the digest the manifest identity is taken in.
//!
//! [`BlockStore`]: gandr_storage_records::BlockStore

#![no_std]

extern crate alloc;

pub mod error;
pub mod manifest;
pub mod record;
pub mod transport;

use anodized::spec;
use gandr_kernel_term::FORMAT_VERSION;
use gandr_storage_records::BlockStore;
use gandr_storage_records::RecordTree;
use gandr_storage_records::TreeParams;

pub use crate::error::ArtifactError;
pub use crate::error::ManifestField;
pub use crate::manifest::ARTIFACT_IDENTITY_LEN;
pub use crate::manifest::ArtifactIdentity;
pub use crate::manifest::ArtifactManifest;
pub use crate::manifest::ArtifactManifestVersion;
pub use crate::manifest::MANIFEST_DOMAIN;
pub use crate::manifest::ManifestImage;
pub use crate::manifest::ManifestImageBuf;
pub use crate::record::ADMISSION_KEY_LEN;
pub use crate::record::AdmissionKey;
pub use crate::record::ArtifactRecord;
pub use crate::record::ArtifactRecordSet;
pub use crate::record::HEADER_KEY;
pub use crate::record::ReassembledArtifact;
pub use crate::record::SegmentBytes;

/// Writes a record set's tree into `store` and names it.
///
/// # Specification
/// - requires: nothing; a set whose bytes are not an artifact commits, and is
///   refused when it is read back.
/// - ensures: on success every node of the tree built from
///   [`ArtifactRecordSet::record_refs`] under `params` is loadable from
///   `store`, and the manifest carries this build's kernel format version,
///   `params`' boundary commitment, the set's record count — the header and one
///   per declaration — and the tree's root node identity. The tree is a
///   function of the records alone, so equal sets, in whatever order their
///   records were gathered, mint equal identities.
/// - provides: the commit path, and the one place an artifact identity is
///   minted.
/// - fails: [`ArtifactError::Records`] carrying the record plane's refusal of
///   the parameters, the tree's shape or a node the store will not admit.
/// - panics: none.
///
/// # Errors
/// [`ArtifactError::Records`] — the record plane refuses.
///
/// # Adequacy
/// - hypothesis: L2 on the shared four-declaration artifact compares repeated
///   and permuted builds; header and segment perturbations change its identity.
///   Sixty-four generated environments of zero to 47 declarations read back
///   equal to their kernel decode. L3 refuses the previous record encoding
///   before writing any node. It distinguishes lost bytes, history-sensitive
///   identities and writes before parameter admission, not arbitrary store
///   failures, tree limits or all parameter combinations.
/// - witness: `artifact_contract::artifact_contract::the_same_artifact_mints_the_same_identity`
/// - witness: `artifact_contract::artifact_contract::a_permuted_build_order_yields_the_same_identity`
/// - witness: `artifact_contract::artifact_contract::any_perturbation_changes_the_identity`
/// - witness: `artifact_contract::artifact_contract::round_trip_over_generated_environments`
/// - witness: `artifact_contract::artifact_contract::unsupported_build_parameters_do_not_write_nodes`
#[inline]
#[spec(ensures: |ret| match ret {
    Ok(ref manifest) => *manifest.commitment() == params.boundary_commitment()
        && manifest.kernel_format() == FORMAT_VERSION
        && usize::try_from(u64::from(manifest.record_count()))
            .is_ok_and(|count| count == records.records().len().saturating_add(1_usize)),
    Err(ArtifactError::Records { .. }) => true,
    Err(_) => false,
})]
pub fn build<S>(
    records: &ArtifactRecordSet,
    params: TreeParams,
    store: &mut S,
) -> Result<ArtifactManifest, ArtifactError>
where
    S: BlockStore + ?Sized,
{
    let refs = records.record_refs();
    let tree = RecordTree::build(&refs, params)?;
    tree.write_to(store)?;

    Ok(ArtifactManifest::new(
        FORMAT_VERSION,
        params.boundary_commitment(),
        tree.root().record_count(),
        tree.root_node_hash(),
    ))
}
