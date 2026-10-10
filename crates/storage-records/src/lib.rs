//! Authenticated ordered records with content-defined Merkle leaves and
//! root-checkable membership, absence and range proofs.
//!
//! [`RecordTree`] builds from strictly increasing keys under [`TreeParams`].
//! Its [`TreeRoot`] binds the parameters, record count and root-node identity.
//! Proof verification needs the expected root and query, not the tree or store.
//!
//! # Tree shape
//!
//! A tree is one leaf or one internal root over a run of leaves. See
//! [tree and proof shapes](https://github.com/gandr-lang/gandr/blob/main/crates/storage-records/README.md#tree-and-proof-shapes)
//! for layout limits and the scope of [`StoredRoot`].
//!
//! # Identity and agreement
//!
//! [`RecordTree::agrees_with`] decides record equality separately from root
//! identity. See [identity and agreement](https://github.com/gandr-lang/gandr/blob/main/crates/storage-records/README.md#identity-and-agreement).
//!
//! # Verification boundaries
//!
//! [`BlockStore`] admits verified node material. Proof decoders enforce
//! per-structure limits and a total work budget. See the
//! [decode budgets](https://github.com/gandr-lang/gandr/blob/main/crates/storage-records/README.md#decode-budgets),
//! [storage planes](https://github.com/gandr-lang/gandr/blob/main/crates/storage-records/README.md#storage-planes)
//! and [references](https://github.com/gandr-lang/gandr/blob/main/crates/storage-records/README.md#references).

#![no_std]

extern crate alloc;

pub mod boundary;
pub mod bytes;
pub mod error;
pub mod node;
pub mod params;
pub mod proof;
pub mod record;
pub mod store;
pub mod tree;
pub mod wire;

pub use crate::boundary::BoundaryMaskBits;
pub use crate::boundary::BoundaryParams;
pub use crate::boundary::BoundaryProfile;
pub use crate::boundary::BoundaryRecordCap;
pub use crate::boundary::ProfileCommitment;
pub use crate::boundary::RecordSpan;
pub use crate::bytes::EncodedNode;
pub use crate::bytes::NodeHash;
pub use crate::bytes::OwnedEncodedNode;
pub use crate::bytes::OwnedRecordEncoding;
pub use crate::bytes::OwnedRecordKey;
pub use crate::bytes::OwnedRecordValue;
pub use crate::bytes::RecordEncoding;
pub use crate::bytes::RecordKey;
pub use crate::bytes::RecordValue;
pub use crate::error::FailureContext;
pub use crate::error::RecordTreeError;
pub use crate::error::WireVersion;
pub use crate::node::ChildIndex;
pub use crate::node::ChildRef;
pub use crate::node::DecodedNode;
pub use crate::node::InternalNode;
pub use crate::node::LeafNode;
pub use crate::node::NodeKind;
pub use crate::node::NodeLayout;
pub use crate::node::StoredNode;
pub use crate::node::decode_node;
pub use crate::node::encode_internal;
pub use crate::node::encode_leaf;
pub use crate::node::hash_node;
pub use crate::node::inspect_node;
pub use crate::node::select_child;
pub use crate::node::verify_stored_node;
pub use crate::params::EncodingVersion;
pub use crate::params::HashAlgorithm;
pub use crate::params::SeparatorConvention;
pub use crate::params::TreeKind;
pub use crate::params::TreeParams;
pub use crate::params::TreeRoot;
pub use crate::proof::CarriedCount;
pub use crate::proof::CarriedIndex;
pub use crate::proof::MembershipProof;
pub use crate::proof::NonMembershipEvidence;
pub use crate::proof::NonMembershipProof;
pub use crate::proof::ProofEnvelope;
pub use crate::proof::ProofKind;
pub use crate::proof::ProofNode;
pub use crate::proof::RangeProof;
pub use crate::record::KeyBound;
pub use crate::record::KeyRange;
pub use crate::record::OwnedKeyBound;
pub use crate::record::OwnedKeyRange;
pub use crate::record::RangeContainment;
pub use crate::record::Record;
pub use crate::record::RecordCount;
pub use crate::record::RecordIndex;
pub use crate::record::RecordRef;
pub use crate::record::ensure_strictly_sorted;
pub use crate::store::BlockStore;
pub use crate::store::InMemoryBlockStore;
pub use crate::store::StoreOccupancy;
pub use crate::store::StoredNodeCount;
pub use crate::tree::RecordAgreement;
pub use crate::tree::RecordTree;
pub use crate::tree::StoredRoot;
pub use crate::wire::ChildCount;
pub use crate::wire::DecodeCompletion;
pub use crate::wire::DecodeWork;
pub use crate::wire::Domain;
pub use crate::wire::DomainTag;
pub use crate::wire::EncodedLength;
pub use crate::wire::ItemCapacity;
pub use crate::wire::LEAST_CHILD_BYTES;
pub use crate::wire::LEAST_RECORD_BYTES;
pub use crate::wire::MAX_LEAF_RECORDS;
pub use crate::wire::MAX_NODE_BYTES;
pub use crate::wire::MAX_NODE_CHILDREN;
pub use crate::wire::MAX_PROOF_NODES;
pub use crate::wire::MAX_PROOF_RECORDS;
pub use crate::wire::NodeCount;
pub use crate::wire::WireArray;
pub use crate::wire::WireBytes;
pub use crate::wire::WireLong;
pub use crate::wire::WireTag;
pub use crate::wire::WireWord;
