//! Content-addressed values as typed chunk DAGs or flat canonical token bytes:
//! the value plane of the CAM, the content-addressable memory of
//! `Rainey-2026-localmem_typedirected_adaptive_serialization_location_contentaddressable_memory`.
//! A committed value is named by a content pointer, a chunk's digest and a
//! token offset in it, which no world's location enters. A pointer proves
//! integrity: these are the bytes committed. It never proves validity, which
//! the codec and its consumer keep.
//!
//! [`CanonicalValue`] defines a codec over [`TokenSink`] and [`TokenReader`].
//! [`cam_commit`] stores a value and returns its [`ValueManifest`];
//! [`cam_deref`] decodes from a [`ContentPtr`] while the reader splices child
//! chunks into one stream. [`encode_flat`] and [`decode_flat`] use the same
//! token language without a store or child pointers.
//!
//! # Encoding and chunking
//!
//! The token body's records are stated in the `tokens` module, a chunk's frame
//! and its verification in `chunk`, child references in `index_base`, residues
//! and the cut rule in `commit`, and the flat form in `flat`.
//!
//! # Verification
//!
//! [`ValueError`] identifies emission, framing, authentication and codec
//! failures. [`MAX_DECODE_WORK`] bounds accumulated decode work.
//!
//! `VerifiedChunk` can be obtained only by framing a body or verifying an
//! image. Verification checks the domain, version, byte length, token count and
//! digest. Both `ChunkStore` methods use this type, so implementations cannot
//! return unverified byte buffers through the trait.
//!
//! Emission checking rejects empty output, multiple roots, unmatched closes,
//! unclosed constructors and payload outside a constructor. A reader entering a
//! child chunk consumes exactly one subtree and returns to its parent when that
//! subtree closes.
//!
//! The flat sink's executable refinement bounds its addressed records by the
//! bytes it has emitted. Its fixed wire witness checks all four flat record
//! forms and the refusal positions for an embedded pointer and malformed
//! emission; generated round trips cover values of at most 4096 records, not
//! arbitrary consumer codecs.
//!
//! Every decode charges one accumulator for records, payload bytes and
//! chunk-image bytes verified at seams. Work beyond `MAX_DECODE_WORK` (2^34) is
//! rejected, including repeated reads through different paths to a shared
//! chunk. Authentication establishes the bytes named by a pointer; the codec
//! and consumer retain responsibility for value validity.
//!
//! The reader's executable refinement keeps spent work within the ceiling and
//! forbids suspended chunk frames in flat mode. Fixed witnesses cover exact
//! payload borrowing and charges, wrong record kinds, an interior child at
//! offset two, and restoration of its parent's cursor. A refused read does not
//! promise rollback of all cursor bookkeeping.
//!
//! # The manifest
//!
//! A [`ValueManifest`] names a committed value under its [`ValueProfile`]:
//! [`ValueManifest::encode`] writes it as bytes under [`MANIFEST_DOMAIN`],
//! [`ValueManifest::decode`] refuses every other image by name, and
//! [`ValueManifest::identity`] is the [`ManifestDigest`] a consumer stores.
//! [`ValueManifest::read_under`] refuses a profile the reader does not share
//! before any chunk is loaded, and [`ValueManifest::closure`] loads every chunk
//! a reader would and checks the token count. The manifest's rule, image and
//! refusal order are stated in the `manifest` module.
//!
//! # Locality
//!
//! [`expected_chunk_bound`] states an expectation, while [`measure_edit`]
//! counts affected and shared chunks for one edit. The bound, its derivation
//! and its source are stated in the `locality` module.
//!
//! # Laws and their witnesses
//!
//! `LoCalMem` states its representation results as deep-equality theorems over
//! its own model and proves them mechanically. This crate does not port those
//! proofs. Each statement it can observe has a named test standing in for it: a
//! property differential over generated values and profiles, or a fixed witness
//! where the statement is deterministic. Every one is evidence on the inputs it
//! exercised, and none is a proof.
//!
//! - **Alternatives.** Claiming nothing until a mechanized proof exists leaves
//!   observable obligations unchecked. Crediting a differential as the lemma
//!   beside it would close a proof obligation by relabelling it.
//! - **Reversal.** A mechanized proof of a statement over this crate's token
//!   vocabulary takes that row; its differential stays as the check that the
//!   code still meets it.
//!
//! A rung names what the test compares against. **L2** is agreement with an
//! independent reference on exercised inputs: the flat encoder, which holds no
//! store and no scanner; a reference scanner written in the test from the cut
//! rule in the `commit` module, sharing no code with the commit path; an empty
//! store. **L3** is an exact assertion at named boundaries. A measurement
//! compares observed means with a stated bound.
//!
//! | Statement | Witness | Rung |
//! | --------- | ------- | ---- |
//! | Segment soundness and completeness (Lemmas 3.4, 3.5) | `every_generated_value_round_trips_flat`, beside `every_record_round_trips_through_the_grammar` | L2 |
//! | Token bound (Lemma 3.6) | an alias region never reopens its own tag, refused by name otherwise: `a_tagged_commit_reads_back_or_refuses_an_unbounded_alias`; the reader's total budget is `the_budget_admits_the_ceiling_and_refuses_one_past` | L2; L3 |
//! | Deep equality (Lemma 4.4) | the codec's own equality over decoded values, the observer every witness below compares with | — |
//! | Duplication and evacuation (Lemmas 4.6, 4.7) | none: the crate has no regions, wrappers or collector (§ Mutation) | — |
//! | Codec round trip (Lemma 5.5) | `every_generated_value_round_trips_flat` | L2 |
//! | Commit–load round trip (Lemma 5.7) | `every_generated_value_commits_and_derefs_back_equal`, and under a tagged classification `a_tagged_commit_reads_back_or_refuses_an_unbounded_alias` | L2 |
//! | Chunking transparency (Lemma 5.8) | `chunking_is_invisible_to_the_flat_form` | L2 |
//! | Store-history independence | `a_root_pointer_does_not_depend_on_what_the_store_holds` | L2 |
//! | Locality (Theorem 5.2, Corollary 5.3) | `measured_chunk_counts_sit_inside_the_locality_bound`, and the formula by `the_bound_matches_the_formula_by_hand` | measurement; L3 |
//! | The cut rule, a deterministic complement of locality | `the_cuts_agree_with_a_reference_scanner` | L2 |
//! | The adversarial ceiling, a deterministic complement of locality | `an_edit_under_every_cut_affects_exactly_its_path` | L3 |
//! | A seam stands only at a boundary constructor | `a_seam_at_an_alias_is_refused_by_name` | L3 |
//!
//! What each law observes:
//!
//! - **Flat round trip.** Decoding a generated value's flat bytes returns the
//!   value.
//! - **Commit–deref round trip.** Under every generated profile, the root
//!   pointer derefs to the value, and the manifest carries the profile.
//! - **Chunking invisible to the flat form.** The flat bytes of the dereffed
//!   value equal the original's, byte for byte; splicing each child chunk's
//!   body where its child record stands rebuilds the same bytes; the manifest's
//!   token count is the flat form's record count.
//! - **Store-history independence.** Committing into a store that already holds
//!   the value's subtrees, the value with a leaf edited, the value itself and
//!   unrelated values, some under other profiles, returns the manifest an empty
//!   store returns. The store ends holding exactly what it held and what the
//!   empty store came to hold.
//! - **The cut rule.** The reference recomputes every residue from the flat
//!   form alone and applies the cap first, then divisibility by kappa, never at
//!   the outermost constructor. Its cuts are the chunk boundaries read off the
//!   stored chunk DAG.
//! - **The adversarial ceiling.** Residues are a public function of content, so
//!   whoever controls content can grind them; the most it reaches is every
//!   constructor below the root its own chunk. Kappa one forces that ceiling
//!   deterministically, since every residue is then a multiple. The witness, a
//!   value of every shape with no repeated subtree, holds one chunk per
//!   constructor whatever the cap, and each leaf edit affects exactly the
//!   chunks of the constructors on its root path and shares every other. The
//!   cost is more chunks and lookups, never a wrong value, and the decode
//!   budget bounds the work.
//! - **Alias and boundary.** Under a generated tagged classification — any set
//!   of the seven shapes, every container a boundary, or one container an alias
//!   — a generated value either commits, derefs back equal, is cut where the
//!   reference scanner cuts when only boundary exits are events, and passes its
//!   closure; or is refused as a recursive alias exactly where a reading of its
//!   records alone finds an alias reopened inside itself with no boundary
//!   between.
//!
//! The generators decide what this evidence covers. Values are constructor
//! trees over seven shapes, with words and byte strings, biased toward deep
//! spines, wide fans, repeated subtrees and the empty-payload constructor.
//! Profiles are biased toward kappa one, powers of two, and caps at and below
//! kappa; half the cut rule's cases set the cap where a run reaches it exactly
//! at a boundary event, or passes it there by one record. A law checked only on
//! balanced fixtures under one profile meets none of those edges. The
//! generators and the reference scanner are test code; nothing ships them.
//!
//! # Mutation
//!
//! No API in this crate mutates a committed value or a stored chunk.
//! `cam_commit` reads a value the caller owns and keeps none of it.
//!
//! **Commit snapshots, witnessed.** A value committed, mutated in place through
//! an exclusive borrow and committed again gets a second root. The first root
//! still derefs to the value as committed and the second to the mutated value,
//! and the store grows by exactly the chunks `measure_edit` reports the edit
//! affected
//! (`a_value_mutated_after_commit_commits_anew_and_the_old_pointer_still_reads_the_old_value`,
//! L3).
//!
//! **Transparency under in-place mutation, not this crate's.** That deep
//! equality survives in-place mutation of wrapped, spliced or duplicated
//! representations under exclusive access is a statement about a runtime value
//! representation with indirection and a permission model. This crate has
//! neither, and holds no regions, wrappers or collector to check it against.
//! Exclusive borrows make the mutated value independent of the committed one;
//! they do not establish the representation theorems.
//!
//! - **Reversal.** An API that edits stored content in place, such as an
//!   in-place chunk editor or a mutable arena under the value plane, makes
//!   transparency under mutation this crate's obligation before it lands.
//!
//! # Specification attributes
//!
//! `# Specification` blocks state the admitted behavior; executable
//! `#[spec(...)]` predicates check supported conditions on executed calls.
//! Trait declarations state implementor obligations. `cam_deref` relies on the
//! consumer's codec round-trip law without requiring an equality implementation
//! on its result type.
//!
//! The committing sink refines its live frame marks against the body and
//! residue buffers it owns. Its literal nested-value witness checks exact
//! stored bytes and record accounting; bounded generated values additionally
//! compare cut positions against an independent scanner. Individual frame marks
//! cannot establish these relationships without their owning buffers.
//!
//! Closure refinements require a nonempty loaded set and at least an open/close
//! pair in a completed subtree. Traversal refinements bound spent work and bind
//! cached pointer counts to loaded digests. A fixed repeated-reference witness
//! distinguishes two offsets of the same chunk and counts each logical
//! occurrence, while the digest set still deduplicates physical chunks.
//!
//! Shared fixtures refine a complete preorder tree, not merely a nonempty node
//! list. Asymmetric byte goldens distinguish child order and leaf indices, and
//! a five-kind scanner witness checks full child addresses. An exact callback
//! trace enters two nested seams and returns to the outer source on the closing
//! record, separating an observed maximum from the final depth. An empty
//! emission script succeeds without invoking its sink; the enclosing encoders
//! then refuse its missing value.
//!
//! The independent model checks exact borrowed wire extents, while cut and
//! splice witnesses distinguish logical record positions from byte offsets at
//! cap boundaries. Its ledger refinement compares listed identities with
//! authenticated backing entries; equal cardinalities alone do not establish
//! agreement.
//!
//! The generated codec refines the complete seven-shape field grammar,
//! including counted children. Literal heterogeneous bytes distinguish leaf
//! payloads from count words and interleaved fields, pin their depths and
//! record indices, and preserve untouched data during word, binary and
//! empty-byte edits. The generator's record budget constrains its producer
//! rather than every value the codec can read.
//!
//! Arena refinements bind backward child references, saturated expanded counts
//! and exact frontier markers. Boundary witnesses distinguish 4096-record
//! admission from 4097-record replacement, preserve unused roots and retain
//! repeated children by occurrence. A compact doubling DAG reaches the counter
//! width without expanding it; a separate frontier witness discards exactly the
//! oldest root when the combined value exceeds the budget.
//!
//! Prior-value recipes compare selected subtrees and edited leaves against
//! their unchanged input without copying it into a predicate. Fixed field
//! positions distinguish payload leaves from tagged words and interleaved
//! labels, including empty-byte growth and leafless identity. Strategy
//! factories state their sample bounds and an explicit executable exemption:
//! observing a sample advances a runner. Their bounded round-trip, cut and
//! history properties do not claim statistical frequencies or exhaustive
//! coverage. Event-targeted caps describe positions before any earlier cut
//! resets the pending run.
//!
//! Load-count witnesses distinguish refused backend requests from profile
//! preflight, which performs no load, and exercise the final representable
//! counter transition. Helpers that receive only a store and digest cannot
//! inspect the loaded body in a predicate without repeating observable I/O;
//! their child-reference ordering is covered by the missing-descendant
//! scenario.
//!
//! # References
//!
//! - `Rainey-2026-localmem_typedirected_adaptive_serialization_location_contentaddressable_memory` — exemplar: the CAM
//!   this crate is, its constructor-directed cuts and content pointers, the
//!   representation lemmas the laws stand in for, and the expected-chunk bound
//!   in Theorem 5.2.
//! - Athicha Muthitacharoen, Benjie Chen, and David Mazières. "A Low-Bandwidth
//!   Network File System." _Proceedings of the Eighteenth ACM Symposium on
//!   Operating Systems Principles (SOSP '01)_, pages 174–187, 2001.
//!   [doi:10.1145/502034.502052](https://doi.org/10.1145/502034.502052) —
//!   content-defined cuts that resynchronize after edits.
//! - Jack O'Connor, Jean-Philippe Aumasson, Samuel Neves, and Zooko
//!   Wilcox-O'Hearn. "BLAKE3: One Function, Fast Everywhere." Specification,
//!   2020. [BLAKE3 specification](https://github.com/BLAKE3-team/BLAKE3-specs)
//!   — the digest family for chunk identities and boundary residues.
//! - Ralph C. Merkle. "A Digital Signature Based on a Conventional Encryption
//!   Function." _Advances in Cryptology — CRYPTO '87_, Lecture Notes in
//!   Computer Science 293, pages 369–378, 1988.
//!   [doi:10.1007/3-540-48184-2_32](https://doi.org/10.1007/3-540-48184-2_32) —
//!   deriving a subtree digest from its children's digests.

// Module documentation that predates the shape lint: 31 headings outside the
// vocabulary, 3 decision records and 3 budgets exceeded. Each allow leaves with
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
pub use crate::manifest::BoundaryTags;
pub use crate::manifest::CodecIdentity;
pub use crate::manifest::ConstructorClass;
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
