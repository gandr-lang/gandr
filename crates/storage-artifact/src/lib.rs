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
//! the consumer's. See
//! [integrity and validity](https://github.com/gandr-lang/gandr/blob/main/crates/storage-artifact/README.md#integrity-and-validity).
//!
//! # Records and the manifest
//!
//! See [the record layout](https://github.com/gandr-lang/gandr/blob/main/crates/storage-artifact/README.md#the-record-layout)
//! and [the artifact manifest](https://github.com/gandr-lang/gandr/blob/main/crates/storage-artifact/README.md#the-artifact-manifest).
//!
//! [`BlockStore`]: gandr_storage_records::BlockStore

#![no_std]
// Specification backfill pending (gandr-lang/gandr#9): the executable-
// specification lints are allowed until this crate's own backfill lands.
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    allow(
        spec_attribute_present,
        adequacy_present,
        maybe_shape,
        erased_error_signature
    )
)]

extern crate alloc;

pub mod error;
pub mod manifest;
pub mod record;

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
/// - hypothesis: L2 agreement — one artifact committed twice into two stores
///   mints one identity, a permuted record order mints the same, one changed
///   segment moves it, and a generated environment's committed tree reads back
///   as the decode of its own image.
/// - witness: `artifact_contract::artifact_contract::the_same_artifact_mints_the_same_identity`
/// - witness: `artifact_contract::artifact_contract::a_permuted_build_order_yields_the_same_identity`
/// - witness: `artifact_contract::artifact_contract::any_perturbation_changes_the_identity`
/// - witness: `artifact_contract::artifact_contract::round_trip_over_generated_environments`
#[inline]
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|manifest|
    *manifest.commitment() == params.boundary_commitment()
        && manifest.kernel_format() == FORMAT_VERSION
        && usize::try_from(u64::from(manifest.record_count()))
            .is_ok_and(|count| count == records.records().len().saturating_add(1_usize))))]
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
