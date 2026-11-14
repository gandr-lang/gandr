//! Kernel artifacts on the authenticated record plane and the content-addressed
//! value plane: one record per distinct declaration segment, keyed by the
//! digest of its bytes, under a BLAKE3 manifest identity or a content pointer.
//! In the storage
//! picture this crate is where the kernel's export enters the CAM, the
//! content-addressable memory of
//! `Rainey-2026-localmem_typedirected_adaptive_serialization_location_contentaddressable_memory`.
//! It stands on both walls in turn: the identity proves integrity, and
//! validity stays the kernel decoder's and, after it, admission's.
//!
//! [`ArtifactRecordSet::from_artifact`] cuts a kernel artifact where the
//! kernel's decoder finds its segments end: the header under the empty key,
//! the order of the declarations under [`ORDER_KEY`], and each distinct
//! segment under the digest of its bytes. [`build`] writes the
//! set's record tree into a [`BlockStore`] and returns the
//! [`ArtifactManifest`] naming it; [`ArtifactManifest::identity`] is the one
//! identity an artifact has. [`ArtifactManifest::read_under`] reads the tree
//! back, checks it against the manifest, and hands the reassembled bytes to
//! the kernel's bounded decoder. On the value plane the set is a
//! `CanonicalValue` of `gandr-storage-values`, which a value store commits to
//! a content pointer and reads back; the reader reassembles it and decodes it
//! the same way.
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
//! module, and the set's tokens on the value plane in `record::value`; the
//! artifact manifest, its image and what its identity binds, in the
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
//! | Equal segments share one record; each key is the digest of its bytes, each place names a held record and each record stands at a place | `record::tests::equal_segments_share_one_record`, `record::tests::record_refinements_bind_keys_and_places` |
//! | Names stand beside their places in order, and a count that differs is refused where the counts part | `record::tests::names_go_beside_their_places_in_order`, `artifact_contract::a_named_set_reads_back_with_its_names_7340` |
//! | Cursor reads preserve exact suffixes and distinguish refusal before and after a length prefix | `manifest::tests::cursor_transitions_preserve_suffixes_and_refusal_positions` |
//! | Identity rendering preserves every byte and propagates sink refusal; diagnostic variants retain their payloads | `manifest::tests::identity_rendering_preserves_all_bytes_and_refusals`, `error::tests::every_refusal_renders_apart`, `error::tests::every_manifest_field_renders_apart` |
//! | The records reassemble to the artifact byte for byte | `artifact_contract::records_round_trip_to_a_byte_identical_artifact`, `artifact_contract::round_trip_over_generated_environments` |
//! | Repeated builds agree; header, segment, order and name perturbations change the identity | `artifact_contract::the_same_artifact_mints_the_same_identity`, `artifact_contract::any_perturbation_changes_the_identity` |
//! | An insertion leaves every record whose bytes it does not change | `artifact_contract::an_insertion_leaves_every_record_it_does_not_rewrite_7340` |
//! | A set with names, without names and with unkeyed entries reads back off the value plane as the stream it was read from | `artifact_contract::a_named_set_reads_back_off_the_value_plane_7340` |
//! | A committed artifact reads back as the decode of its own image, from a leaf root and from an internal one | `artifact_contract::tree_nodes_store_and_reopen`, `artifact_contract::round_trip_over_generated_environments` |
//! | An unsupported record encoding is refused before any node is written | `artifact_contract::unsupported_build_parameters_do_not_write_nodes` |
//! | A foreign kernel format or boundary rule is refused before any load | `artifact_contract::a_foreign_profile_or_format_is_refused_before_any_load` |
//! | A matching identity over bytes the kernel refuses is refused | `artifact_contract::a_matching_identity_over_bytes_the_kernel_refuses_is_refused` |
//! | Misplaced keys, a malformed order, a place without its record, a record without a place and records off a segment boundary are refused | `artifact_contract::a_stored_tree_with_misplaced_keys_is_refused`, `artifact_contract::records_cut_off_a_segment_boundary_are_refused` |
//!
//! The `artifact_contract` witnesses live in `tests/artifact_contract.rs`,
//! module `artifact_contract`.
//!
//! # References
//!
//! - `Rainey-2026-localmem_typedirected_adaptive_serialization_location_contentaddressable_memory` — exemplar: the CAM
//!   a keyed artifact instantiates, and the token-bound lemmas whose scope
//!   § Scope of the mechanized bounds states.
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

// Module documentation that predates the shape lint: 12 headings outside the
// vocabulary, 6 decision records and 3 budgets exceeded. Each allow leaves with
// the rewrite that clears its count.
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    allow(
        module_doc_heading,
        doc_decision_record,
        module_doc_budget,
        reason = "module documentation that predates the shape lint"
    )
)]
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
pub use crate::record::ArtifactRecord;
pub use crate::record::ArtifactRecordSet;
pub use crate::record::CONTENT_NAME_LEN;
pub use crate::record::ContentName;
pub use crate::record::HEADER_KEY;
pub use crate::record::ORDER_KEY;
pub use crate::record::OrderImage;
pub use crate::record::PLACE_LEN;
pub use crate::record::Place;
pub use crate::record::RECORD_DOMAIN;
pub use crate::record::RECORD_KEY_LEN;
pub use crate::record::ReassembledArtifact;
pub use crate::record::RecordKey;
pub use crate::record::SegmentBytes;
pub use crate::record::unnamed;

/// Writes a record set's tree into `store` and names it.
///
/// # Specification
/// - requires: nothing; a set whose bytes are not an artifact commits, and is
///   refused when it is read back.
/// - ensures: on success every node of the tree built from
///   [`ArtifactRecordSet::record_refs`] under `params` is loadable from
///   `store`, and the manifest carries this build's kernel format version,
///   `params`' boundary commitment, the set's record count — the header, the
///   order and one per distinct segment — and the tree's root node identity.
///   The tree is a function of the records alone, and the records sort by key,
///   so equal sets mint equal identities.
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
///   builds; header, segment, order and name perturbations change its identity.
///   Sixty-four generated environments of zero to 47 declarations read back
///   equal to their kernel decode. L3 refuses the previous record encoding
///   before writing any node. It distinguishes lost bytes, history-sensitive
///   identities and writes before parameter admission, not arbitrary store
///   failures, tree limits or all parameter combinations.
/// - witness: `tests::artifact_contract::the_same_artifact_mints_the_same_identity`
/// - witness: `tests::artifact_contract::any_perturbation_changes_the_identity`
/// - witness: `tests::artifact_contract::round_trip_over_generated_environments`
/// - witness: `tests::artifact_contract::unsupported_build_parameters_do_not_write_nodes`
#[inline]
#[spec(ensures: |ret| match ret {
    Ok(ref manifest) => *manifest.commitment() == params.boundary_commitment()
        && manifest.kernel_format() == FORMAT_VERSION
        && usize::try_from(u64::from(manifest.record_count()))
            .is_ok_and(|count| count == records.records().len().saturating_add(2_usize)),
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
    let order = records.order_image();
    let refs = records.record_refs(&order);
    let tree = RecordTree::build(&refs, params)?;
    tree.write_to(store)?;

    Ok(ArtifactManifest::new(
        FORMAT_VERSION,
        params.boundary_commitment(),
        tree.root().record_count(),
        tree.root_node_hash(),
    ))
}
