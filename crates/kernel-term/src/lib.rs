//! The kernel's **term arena and sharing format**: a flat, id-addressed arena
//! with constructor-only minting and an admission watermark, the unified
//! subterm-table encoding over it, and the decode-time budgets that stop a
//! small artifact from costing an unbounded amount of downstream work.
//!
//! The crate holds **representation and bytes only**. There is no checker here,
//! no conversion, no environment and no admission choke point; those consume
//! this vocabulary rather than living in it. It is `no_std` over `core` and
//! `alloc` and depends only on the kernel's level oracle, which is the shape of
//! the trusted base's dependency wall.
//!
//! # Four decisions that interlock
//!
//! **The representation is an arena**, in four typed `u32`-backed id families,
//! so that a graph of shared ids is representable at all and teardown is a flat
//! vector drop rather than a recursion over term depth.
//!
//! **The format is one per-artifact tagged subterm table** covering all four
//! families in a single index space, maximally shared under structural
//! equality, declaration-segmented, with children referenced only by strictly
//! earlier index in post-order first-completion order.
//!
//! **Decode retains sharing**, which is only possible because of the first
//! decision — a table entry *is* an arena id, and decode is arena construction.
//!
//! **The budgets exist because of the third.** Retaining sharing moves the
//! billion-laughs attack from memory to consumer time, so an artifact's
//! expanded work is bounded before anything downstream sees it.
//!
//! Owned trees would foreclose the format decision they look independent of.
//! That coupling is why the four are decided together.
//!
//! # Canonical form is enforced by re-encoding
//!
//! The writer is untrusted and feeds no judgement. What enforces canonical form
//! is a whole-artifact re-encode-compare on the reading side, and the
//! maximal-sharing encoder *is* the re-encoder — so a redundant duplicate
//! entry, a mis-ordered table and a dead entry are all caught by one mechanism
//! that needs no second implementation. The re-encoder is itself sharing-aware:
//! a tree-walking re-encoder would make the canonical check an amplification
//! vector rather than a defence.
//!
//! # Sharing and compression
//!
//! No interning table and no content-keyed memo of *values* belongs here or
//! anywhere the kernel can reach. Sharing is **preserved** by the kernel and
//! never **created**: what a decode hands over is the sharing a consumer sees,
//! id equality is a positive-only fast path deciding reflexive pairs alone, and
//! any pass that creates sharing is elaborator-side. Compression is a storage
//! and transport concern; the canonical bytes remain the bytes, and no codec
//! belongs inside a reader whose rejection vocabulary has to stay clean.
//!
//! The papers the crate draws on are in its `README.md`, § References.

#![no_std]

extern crate alloc;

mod arena;
mod base;
mod budget;
mod decl;
mod decode;
mod encode;
mod error;
pub mod stage;
mod tags;
mod term;
mod types;
mod wire;

pub use crate::arena::AnyNode;
pub use crate::arena::ArenaWatermark;
pub use crate::arena::CompTypeId;
pub use crate::arena::ComputationId;
pub use crate::arena::TermArena;
pub use crate::arena::ValueId;
pub use crate::arena::ValueTypeId;
pub use crate::base::BaseType;
pub use crate::base::FractionDigits;
pub use crate::base::IntegerLiteral;
pub use crate::base::Literal;
pub use crate::base::Magnitude;
pub use crate::base::NumericLiteral;
pub use crate::base::Sign;
pub use crate::base::StringLiteral;
pub use crate::budget::DecodeMetrics;
pub use crate::budget::ExpandedWork;
pub use crate::budget::GlobalIndex;
pub use crate::budget::LevelAtomOffset;
pub use crate::budget::MAX_ARTIFACT_EXPANDED_WORK;
pub use crate::budget::MAX_DECODED_LEVEL_OFFSET;
pub use crate::budget::MAX_EXPANDED_TERM_WORK;
pub use crate::budget::MAX_TABLE_ENTRIES;
pub use crate::budget::TableEntryCount;
pub use crate::decl::AdmissionMark;
pub use crate::decl::Declaration;
pub use crate::decl::DeclarationBuilder;
pub use crate::decl::DeclarationContent;
pub use crate::decl::LevelParamCount;
pub use crate::decl::LevelSignature;
pub use crate::decl::MarkedDeclaration;
pub use crate::decl::MintedAtom;
pub use crate::decl::NameSegment;
pub use crate::decl::StructuredName;
pub use crate::decode::DecodedArtifact;
pub use crate::decode::SegmentLayout;
pub use crate::decode::decode;
pub use crate::encode::encode;
pub use crate::error::DecodeError;
pub use crate::error::MalformedSite;
pub use crate::error::ReservedKind;
pub use crate::error::ReservedSlot;
pub use crate::error::TagSite;
pub use crate::tags::ADMISSION_CHECKED;
pub use crate::tags::ADMISSION_UNCHECKED;
pub use crate::tags::BASE_INTEGER;
pub use crate::tags::BASE_NUMERIC;
pub use crate::tags::BASE_STRING;
pub use crate::tags::ChildArity;
pub use crate::tags::FORMAT_VERSION;
pub use crate::tags::KIND_ABSTRACT_TYPE;
pub use crate::tags::KIND_AXIOM;
pub use crate::tags::KIND_DEF;
pub use crate::tags::KIND_FUNCTOR_DEF;
pub use crate::tags::KIND_MODULE_DEF;
pub use crate::tags::KIND_MODULE_SIG;
pub use crate::tags::LITERAL_INTEGER;
pub use crate::tags::LITERAL_NUMERIC;
pub use crate::tags::LITERAL_TEXT;
pub use crate::tags::MAGIC;
pub use crate::tags::NODE_C_ABSURD;
pub use crate::tags::NODE_C_APPLICATION;
pub use crate::tags::NODE_C_BIND;
pub use crate::tags::NODE_C_CASE;
pub use crate::tags::NODE_C_FORCE;
pub use crate::tags::NODE_C_LAMBDA;
pub use crate::tags::NODE_C_RETURN;
pub use crate::tags::NODE_C_TRANSPORT;
pub use crate::tags::NODE_CT_ARROW;
pub use crate::tags::NODE_CT_ELEMENT;
pub use crate::tags::NODE_CT_PI;
pub use crate::tags::NODE_CT_RETURNER;
pub use crate::tags::NODE_LIST_VALUE_RESERVED;
pub use crate::tags::NODE_SHARE_COMP_TYPE;
pub use crate::tags::NODE_SHARE_COMPUTATION;
pub use crate::tags::NODE_SHARE_VALUE;
pub use crate::tags::NODE_SHARE_VALUE_TYPE;
pub use crate::tags::NODE_TAG_TABLE;
pub use crate::tags::NODE_V_CONSTANT;
pub use crate::tags::NODE_V_INJECTION;
pub use crate::tags::NODE_V_LIFT;
pub use crate::tags::NODE_V_LITERAL;
pub use crate::tags::NODE_V_PAIR;
pub use crate::tags::NODE_V_PATH_EQUIV;
pub use crate::tags::NODE_V_PATH_PRODUCT;
pub use crate::tags::NODE_V_PATH_REFL;
pub use crate::tags::NODE_V_QUOTE;
pub use crate::tags::NODE_V_QUOTE_COMPUTATION;
pub use crate::tags::NODE_V_STATIC_APPLICATION;
pub use crate::tags::NODE_V_THUNK;
pub use crate::tags::NODE_V_UNIT;
pub use crate::tags::NODE_V_VARIABLE;
pub use crate::tags::NODE_VT_ABSTRACT;
pub use crate::tags::NODE_VT_BASE;
pub use crate::tags::NODE_VT_COMPUTATION_UNIVERSE;
pub use crate::tags::NODE_VT_ELEMENT;
pub use crate::tags::NODE_VT_EMPTY;
pub use crate::tags::NODE_VT_LIFT;
pub use crate::tags::NODE_VT_LIST;
pub use crate::tags::NODE_VT_PATH_UNIVERSE;
pub use crate::tags::NODE_VT_PRODUCT;
pub use crate::tags::NODE_VT_STATIC_PI;
pub use crate::tags::NODE_VT_SUM;
pub use crate::tags::NODE_VT_THUNK;
pub use crate::tags::NODE_VT_UNIT;
pub use crate::tags::NODE_VT_UNIVERSE;
pub use crate::tags::NodeTagDescription;
pub use crate::tags::NodeTagVerdict;
pub use crate::tags::RELATION_EQ;
pub use crate::tags::RELATION_LEQ;
pub use crate::tags::SHARING_BLOCK_FIRST;
pub use crate::tags::SHARING_BLOCK_LAST;
pub use crate::tags::SIDE_LEFT;
pub use crate::tags::SIDE_RIGHT;
pub use crate::tags::SIGN_NEGATIVE;
pub use crate::tags::SIGN_NON_NEGATIVE;
pub use crate::tags::TokenCount;
pub use crate::term::Computation;
pub use crate::term::ConstantIndex;
pub use crate::term::DeBruijnIndex;
pub use crate::term::EvidenceWord;
pub use crate::term::PathEvidence;
pub use crate::term::Side;
pub use crate::term::Value;
pub use crate::types::CompType;
pub use crate::types::GroundSort;
pub use crate::types::ValueType;
pub use crate::wire::ArtifactImage;
pub use crate::wire::ByteOffset;
pub use crate::wire::EncodedArtifact;
pub use crate::wire::FormatVersion;
pub use crate::wire::WireByte;
pub use crate::wire::WireTag;
