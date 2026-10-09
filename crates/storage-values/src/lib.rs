//! Content-addressed values as typed chunk DAGs or flat canonical token bytes.
//!
//! [`CanonicalValue`] defines a codec over [`TokenSink`] and [`TokenReader`].
//! [`cam_commit`] stores a value and returns its [`ValueManifest`];
//! [`cam_deref`] decodes from a [`ContentPtr`] while the reader splices child
//! chunks into one stream. [`encode_flat`] and [`decode_flat`] use the same
//! token language without a store or child pointers.
//!
//! # Encoding and chunking
//!
//! See the [byte languages](https://github.com/gandr-lang/gandr/blob/main/crates/storage-values/README.md#byte-languages)
//! and [boundary rules](https://github.com/gandr-lang/gandr/blob/main/crates/storage-values/README.md#chunk-boundaries-and-residues)
//! for canonical framing, child references and residue derivation.
//!
//! # Verification
//!
//! [`ValueError`] identifies emission, framing, authentication and codec
//! failures. [`MAX_DECODE_WORK`] bounds accumulated decode work. See
//! [verification and decode budgets](https://github.com/gandr-lang/gandr/blob/main/crates/storage-values/README.md#verification-and-decode-budgets).
//!
//! # The manifest
//!
//! A [`ValueManifest`] names a committed value under its [`ValueProfile`]:
//! [`ValueManifest::encode`] writes it as bytes under [`MANIFEST_DOMAIN`],
//! [`ValueManifest::decode`] refuses every other image by name, and
//! [`ValueManifest::identity`] is the [`ManifestDigest`] a consumer stores.
//! [`ValueManifest::read_under`] refuses a profile the reader does not share
//! before any chunk is loaded, and [`ValueManifest::closure`] loads every chunk
//! a reader would and checks the token count. See the
//! [value manifest](https://github.com/gandr-lang/gandr/blob/main/crates/storage-values/README.md#the-value-manifest).
//!
//! # Locality
//!
//! [`expected_chunk_bound`] states an expectation, while [`measure_edit`]
//! counts affected and shared chunks for one edit. See the
//! [locality bound](https://github.com/gandr-lang/gandr/blob/main/crates/storage-values/README.md#the-locality-bound)
//! and [references](https://github.com/gandr-lang/gandr/blob/main/crates/storage-values/README.md#references).

#![no_std]

extern crate alloc;

pub mod chunk;
pub mod closure;
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
pub use crate::closure::ValueClosure;
pub use crate::commit::RESIDUE_DOMAIN;
pub use crate::commit::cam_commit;
pub use crate::deref::cam_deref;
pub use crate::error::ChunkFrameField;
pub use crate::error::EmissionFault;
pub use crate::error::ManifestField;
pub use crate::error::ProfileField;
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
pub use crate::manifest::MANIFEST_DIGEST_LEN;
pub use crate::manifest::MANIFEST_DOMAIN;
pub use crate::manifest::ManifestDigest;
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
pub use crate::units::ManifestImage;
pub use crate::units::ManifestImageBuf;
pub use crate::units::SeamDepth;
pub use crate::units::TokenBody;
pub use crate::units::TokenBytes;
pub use crate::units::ValueManifestVersion;
