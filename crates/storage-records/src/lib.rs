//! The **authenticated ordered-record plane**: a content-defined Merkle search
//! tree over sorted byte records, with proofs that a key is present, that a key
//! is absent, or that a range holds exactly these records — each checkable
//! against a root alone, with no access to the store the tree was built into.
//!
//! # What the crate is for
//!
//! One artifact is a set of records under an ordering key. Two versions of such
//! an artifact usually differ in a few records, and the storage tier wants
//! three things from that: the unchanged parts to be shared rather than
//! rewritten, the whole to have one name, and a part to be provable against
//! that name without shipping the whole. A content-defined Merkle search tree
//! gives all three, because a leaf ends where the data says rather than where a
//! position counter says — so an edit perturbs the leaf it falls in and leaves
//! its neighbours identical, keeping their identities and their storage.
//!
//! # The plane this crate is, and the plane it is not
//!
//! The storage tier has two planes with two grains. This crate is the **keyed**
//! one: records under an ordering key, cut between records. The other is the
//! **value** plane — one large value cut between its own constructors, with a
//! chunk identity that is a function of the value's canonical bytes. The two
//! are expected to share a backing object, and they cannot share a verifier: a
//! chunk is not node material, and forcing a chunk through this crate's node
//! store would make its identity depend on this crate's leaf framing instead of
//! on the value's own bytes. Domain-separated digests are what make one backing
//! namespace safe for two byte languages, and every digest here carries its
//! domain inside the hashed preimage.
//!
//! # What a digest decides, and what it does not
//!
//! Every identity comparison in this crate is against an identity **recomputed
//! from bytes the comparer holds** — a store checks its own bytes, a verifier
//! checks the proof's bytes, a root manifest is resealed from its own
//! parameters. No comparison treats an equal digest as agreement between two
//! things not both in hand, because that direction of error is a silent false
//! agreement. Where an agreement question does arise, between two whole trees,
//! it has its own answer — [`RecordTree::agrees_with`] — in which the digest is
//! a fast path for disagreement and an equal pair is handed to the deciding
//! comparison over the records themselves.
//!
//! # Bounds
//!
//! A decoder facing hostile bytes is bounded twice: per-structure ceilings on
//! node size, leaf records, children and carried nodes, and a total accumulator
//! over one proof. The second is not implied by the first, because node count
//! and per-node record count are separately bounded and their product is not.
//!
//! # Shape and open work
//!
//! The tree is two levels: one leaf, or one internal root over a run of leaves.
//! Every proof shape is written for that and refuses any other. Depth beyond
//! two, a store-backed reader that walks a tree it does not hold in memory, and
//! a transport encoding for proofs are named open work rather than partial
//! implementations; the crate's `README.md` says where each belongs.
//!
//! The named ideas and their primary references are in this crate's
//! `README.md`.

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

pub use crate::boundary::BoundaryDecision;
pub use crate::boundary::BoundaryMaskBits;
pub use crate::boundary::BoundaryParams;
pub use crate::boundary::BoundaryProfile;
pub use crate::boundary::BoundaryRecordCap;
pub use crate::boundary::DigestPrefix;
pub use crate::boundary::LeafRunLength;
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
