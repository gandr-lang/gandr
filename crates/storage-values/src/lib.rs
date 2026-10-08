//! The storage tier's **value plane**: one value as a typed chunk DAG,
//! addressed by content pointers, and its flat canonical bytes.
//!
//! # What the crate is for
//!
//! The record plane stores sorted keyed records; this plane stores a single
//! value by the value's own constructors. A value walks itself into a
//! canonical token stream ([`CanonicalValue`], [`TokenSink`]);
//! [`cam_commit`] cuts that stream at constructor exits the committed typed
//! chunker profile selects, frames each cut subtree as a chunk whose domain is
//! inside its hashed preimage, and names the value by its root chunk's digest
//! ([`ContentPtr`], [`ValueManifest`]). [`cam_deref`] fetches, verifies and
//! decodes, the [`TokenReader`] splicing child chunks so a decoder never sees
//! a seam. Two values sharing a subtree share its chunks, and an edit re-cuts
//! only the chunks on its path, within the bound [`expected_chunk_bound`]
//! states.
//!
//! [`encode_flat`] and [`decode_flat`] give one value's canonical token bytes
//! with no store: for a value that fits one chunk, exactly the body that
//! chunk frames.
//!
//! # Failure
//!
//! Every refusal is a [`ValueError`] naming what was refused. No operation
//! panics, no count or length wraps, every decode is charged to one total
//! budget ([`MAX_DECODE_WORK`]), and no operation repairs a chunk, a stream or
//! an emission it was handed.
//!
//! The named ideas and their primary references are in this crate's
//! `README.md`.

#![no_std]

extern crate alloc;

pub mod chunk;
pub mod commit;
pub mod deref;
pub mod error;
pub mod flat;
pub mod index_base;
pub mod locality;
pub mod manifest;
pub mod ptr;
pub mod reader;
pub mod tokens;
pub mod units;

pub use crate::chunk::CHUNK_DOMAIN;
pub use crate::chunk::ChunkStore;
pub use crate::chunk::FramedChunk;
pub use crate::chunk::InMemoryChunkStore;
pub use crate::chunk::StoredChunkRef;
pub use crate::chunk::VerifiedChunk;
pub use crate::chunk::frame_chunk;
pub use crate::chunk::verify_chunk_image;
pub use crate::commit::RESIDUE_DOMAIN;
pub use crate::commit::cam_commit;
pub use crate::deref::cam_deref;
pub use crate::error::ChunkFrameField;
pub use crate::error::EmissionFault;
pub use crate::error::ValueError;
pub use crate::error::ValueQuantity;
pub use crate::flat::decode_flat;
pub use crate::flat::encode_flat;
pub use crate::index_base::ChildIndexBase;
pub use crate::locality::LocalityMeasurement;
pub use crate::locality::expected_chunk_bound;
pub use crate::locality::measure_edit;
pub use crate::manifest::BoundaryClassification;
pub use crate::manifest::CodecIdentity;
pub use crate::manifest::DigestFamily;
pub use crate::manifest::ValueManifest;
pub use crate::manifest::ValueProfile;
pub use crate::ptr::CHUNK_DIGEST_LEN;
pub use crate::ptr::ChunkDigest;
pub use crate::ptr::ContentPtr;
pub use crate::ptr::TokenOffset;
pub use crate::reader::TokenReader;
pub use crate::tokens::CanonicalValue;
pub use crate::tokens::ConstructorTag;
pub use crate::tokens::TokenKind;
pub use crate::tokens::TokenSink;
pub use crate::units::CanonicalWord;
pub use crate::units::ChunkBound;
pub use crate::units::ChunkCount;
pub use crate::units::ChunkFormatVersion;
pub use crate::units::ChunkImage;
pub use crate::units::ChunkImageBuf;
pub use crate::units::CodecId;
pub use crate::units::CodecVersion;
pub use crate::units::DecodeWork;
pub use crate::units::EditDepth;
pub use crate::units::FlatBytes;
pub use crate::units::MAX_DECODE_WORK;
pub use crate::units::SeamDepth;
pub use crate::units::TokenBody;
pub use crate::units::TokenBytes;
pub use crate::units::ValueManifestVersion;
