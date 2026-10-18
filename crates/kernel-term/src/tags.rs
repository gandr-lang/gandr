//! The frozen wire vocabulary: the artifact magic and version, every tagged
//! byte alphabet, and the node-tag table that states each node tag's shape and
//! its storage-boundary classification.
//!
//! # One disjoint enumeration over four families
//!
//! The subterm table is one table over all four families in a single index
//! space, because types share heavily *across* declarations and per-family
//! tables would forfeit that. One tag byte per entry is the accepted cost of
//! not forfeiting it, and it buys a property the alternative needed extra
//! checks for: **polarity is recoverable from the tag alone**, so a child
//! slot's polarity requirement is decided by a table lookup rather than by a
//! family-specific expectation threaded through the parser.
//!
//! # What holds the version and what bumps it
//!
//! Assigning a previously unassigned tag or kind byte, or filling a reserved
//! slot that framed itself from birth, **holds** the version. Reassigning an
//! existing byte, or changing a field's shape, ordering, or width, **bumps**
//! it.
//!
//! Holding is safe for the first two because of a property of the reader rather
//! than a convention: it is a closed-vocabulary parser over a rejection triple,
//! so a byte it does not know is a named refusal at a named site rather than a
//! mis-parse, and a reserved slot is framed identically whether it is empty or
//! full. Bumping is required for the third because reassigning a byte or moving
//! a field makes an older reader parse successfully and *wrongly*, which is the
//! failure the version field exists to prevent and the only one it can prevent.
//!
//! # The numbering
//!
//! The tag space is one disjoint enumeration over four families, and this
//! table is authoritative; [`NODE_TAG_TABLE`] supplies the assigned formers
//! and their arities. Native paths have distinct bytes. Element identity holds
//! `0x30–0x37` and function identity `0x38–0x47`; [Element and function
//! identity](#element-and-function-identity) states each assigned node's
//! children and inline payload, [The lazy product](#the-lazy-product) does
//! the same for `0x65–0x67` and [The dependent pair](#the-dependent-pair) for
//! `0x6A–0x6B`. The original `0x00–0x1F` meanings are frozen, including the
//! static operators at `0x1E–0x1F`.
//!
//! | Byte or range | Meaning | Artifact reader |
//! | ------------- | ------- | --------------- |
//! | `0x00–0x1F` | Original formers in [`NODE_TAG_TABLE`], less the retired unit type `0x01` and unit value `0x0B` | Admitted; the retired bytes refused |
//! | `0x20` | Reserved value sharing | Refused |
//! | `0x21` | Reserved computation sharing | Refused |
//! | `0x22` | Reserved value-type sharing | Refused |
//! | `0x23` | Reserved computation-type sharing | Refused |
//! | `0x24–0x27` | Held weakening slots | Refused |
//! | `0x28` | Retired: the empty value type | Refused |
//! | `0x29` | Retired: the absurd computation | Refused |
//! | `0x2A` | `Path_U`, two value-code children | Admitted |
//! | `0x2B` | Path reflexivity, one code child | Admitted |
//! | `0x2C` | Equivalence, evidence and three children | Admitted |
//! | `0x2D` | Product path, two path children | Admitted |
//! | `0x2E` | Transport, path and input children | Admitted |
//! | `0x2F` | Unassigned | Refused |
//! | `0x30` | Element `Path`, value-type child and two endpoint value children | Admitted |
//! | `0x31` | `here`, inline endpoint dialogues, one point value child | Admitted |
//! | `0x32` | Dependent transport, motive (value type under one binder), path and input children | Admitted |
//! | `0x33` | Guarded higher field, inline depth and layers, one evidence child per guard | Admitted |
//! | `0x34` | Returned endpoint, one computation child | Admitted |
//! | `0x35` | Telescope transport, motive (the dependent arrow over a two-entry telescope), path, source point, path over it and input children | Admitted |
//! | `0x36–0x37` | Unassigned element-identity growth | Refused |
//! | `0x38` | Higher evaluation, inline dialogues and three value children per component | Admitted |
//! | `0x39` | Related-inputs application, path, two arguments, evidence and a body under three binders | Admitted |
//! | `0x3A` | Quantified evaluation: steps over returned values, evidence and stuck normal forms | Admitted |
//! | `0x3B` | Reserved: dependent-arrow higher evaluation | Refused |
//! | `0x3C–0x47` | Held function-identity growth | Refused |
//! | `0x48` | `Flow_U`, two value-code children | Admitted |
//! | `0x49` | Session simulation evidence, classifier and payload-proof children | Admitted |
//! | `0x4A` | Element `Flow`, value-type child and source and target value children | Admitted |
//! | `0x4B` | `stay`, inline endpoint dialogues, one point value child | Admitted |
//! | `0x4C` | Forward flow, inline image dialogues, classifier, translator and one output child per image | Admitted |
//! | `0x4D` | Function flow, classifier and domain and codomain flow children | Admitted |
//! | `0x4E` | `then`, inline seam byte and two flow children | Admitted |
//! | `0x4F` | `ride`, motive (value type under one binder), flow and input children | Admitted |
//! | `0x50` | List code, one element-type child | Admitted |
//! | `0x51` | Native List nil, no children | Admitted |
//! | `0x52` | Session code, inline finite graph and one payload-type child | Admitted |
//! | `0x53–0x59` | Inline send, receive, select, offer, end, Mu and Var opcodes | Graph fields only; refused as native node tags |
//! | `0x5A` | Session Path evidence, classifier and payload-proof children | Admitted |
//! | `0x5B` | Native List cons, head and tail value children | Admitted |
//! | `0x5C` | Pure List fold, element type, result type, list and two branch children | Admitted |
//! | `0x5D` | Nominal data application, declaration and counted value arguments | Admitted |
//! | `0x5E` | Record type, ordered labels and value-type children | Admitted |
//! | `0x5F` | Constructor, classifier, tag and counted value fields | Admitted |
//! | `0x60` | Record value, ordered labels and value children | Admitted |
//! | `0x61` | Data case, scrutinee, motive and counted branches | Admitted |
//! | `0x62` | Record projection, label and value child | Admitted |
//! | `0x63` | Fixpoint, evidence byte and one computation child | Admitted |
//! | `0x64` | Tuple projection, component and value child | Admitted |
//! | `0x65` | Lazy product type, two computation-type children | Admitted |
//! | `0x66` | Lazy pairing, two computation children | Admitted |
//! | `0x67` | Lazy projection, inline side byte and one computation child | Admitted |
//! | `0x68` | Telescope ride, motive (the dependent arrow over a two-entry telescope), flow, source point, flow over it and input children | Admitted |
//! | `0x69` | Flow product, two flow children | Admitted |
//! | `0x6A` | Dependent pair type, first factor and second factor under its binder | Admitted |
//! | `0x6B` | Dependent split, scrutinee, motive under its binder and body under the two components | Admitted |
//! | `0x6C` | Unassigned | Refused |
//! | `0x6D` | Univalence, bi-invertible record child | Admitted |
//! | `0x6E–0xFF` | Unassigned | Refused |
//!
//! The admitted domain is sparse: the greatest assigned native byte is
//! `0x6D`, not a promise to accept every smaller byte. Boundary witnesses
//! admit assigned native tags, refuse inline opcodes and retired bytes as
//! native nodes, and retain the frozen block. The unit and the empty type are
//! zero-count products and sums, and List nil is a zero-child leaf; all three
//! may be bounded-alias targets, and no reservation becomes an alias target by
//! being below the maximum.
//!
//! On the wire, product, sum, tuple and case carry a child count before their
//! children; an injection carries its summand as an unsigned varint before its
//! one child, and a tuple projection carries its component the same way.
//! Format version 3 introduced the counted formers, and the reader refuses
//! version 2. The retired unit and empty bytes are refused as unassigned, so
//! no artifact spells the unit or the empty type twice.
//!
//! [`NODE_CT_PI`] is the dependent arrow: its codomain is scoped under a
//! binder, so it is a different node from the non-dependent [`NODE_CT_ARROW`]
//! at the same arity and takes its own tag rather than a flag on the arrow's.
//! [`NODE_VT_ELEMENT`] and [`NODE_VT_PATH_UNIVERSE`] carry value codes in
//! type positions. [`NODE_CT_ELEMENT`] is the computation-family decode;
//! path endpoints include closed first-order and finite session codes.
//!
//! The universe families hold four tags of the frozen block's growth room, one
//! per family: the computation universe [`NODE_VT_COMPUTATION_UNIVERSE`] among
//! the value types, the computation decode [`NODE_CT_ELEMENT`] among the
//! computation types, and the two quotes [`NODE_V_QUOTE`] and
//! [`NODE_V_QUOTE_COMPUTATION`] among the values. The sort of a universe is a
//! tag rather than an inline byte on [`NODE_VT_UNIVERSE`] for the reason the
//! dependent arrow is: a payload byte that changes what the node means is a
//! field-shape change, which bumps the version, where a fresh tag holds it.
//!
//! The static operators hold the last two tags of the growth room: the static
//! Pi [`NODE_VT_STATIC_PI`] among the value types and the static application
//! [`NODE_V_STATIC_APPLICATION`] among the values. The static lambda holds
//! none, because the kernel never represents it: a producer normalizes it away
//! before export. The growth room is spent, so the next former resumes above
//! [`SHARING_BLOCK_LAST`].
//!
//! The sharing block is **reserved and unassigned**: four per-family sharing
//! formers so polarity stays recoverable from the tag alone, and four held
//! slots for an explicit weakening form. [`NODE_SHARE_VALUE`],
//! [`NODE_SHARE_COMPUTATION`], [`NODE_SHARE_VALUE_TYPE`] and
//! [`NODE_SHARE_COMP_TYPE`] name its per-family bytes. No entry carries one,
//! and a reader meeting one refuses it by name at the node site, exactly as it
//! refuses any other unassigned byte. Reserving the block rather than
//! numbering it on demand is what stops the core vocabulary from growing into
//! it: the core resumes above [`SHARING_BLOCK_LAST`], and the block's
//! contiguity — the property that makes a sharing former's family a
//! subtraction rather than a lookup — survives.
//!
//! # Element and function identity
//!
//! Element identity takes the higher-field reservation because the higher
//! field is identity between identities: a higher cell inhabits an element
//! path whose value type is itself an element path, so the former and its
//! guarded inhabitant share one range. Function identity takes the funext
//! reservation for the same reason the range was held: identity at a thunk
//! code is the related-inputs product, introduced by higher evaluation.
//!
//! | byte | node | family | children, in order | inline payload |
//! | ---- | ---- | ------ | ------------------ | -------------- |
//! | `0x30` | [`NODE_VT_PATH`] | value type | the value type `A`; endpoint values `a`, `b` | none |
//! | `0x31` | [`NODE_V_HERE`] | value | the point `a` | the left, then the right endpoint dialogue |
//! | `0x32` | [`NODE_C_PATH_TRANSPORT`] | computation | the motive, a value type under one value binder; the path; the input value | none |
//! | `0x33` | [`NODE_V_HIGHER`] | value | one evidence value per guard layer, in layer order | depth, root, layer count, layers |
//! | `0x34` | [`NODE_V_RETURNED`] | value | the pure computation whose returned value the node stands for | none |
//! | `0x35` | [`NODE_C_TELESCOPE_TRANSPORT`] | computation | the motive, a computation type `Π (y : A). Π (z : B). F C`; the path; the second entry's source point; the path over the first; the input value | none |
//! | `0x38` | [`NODE_V_HIGHER_EVALUATION`] | value | per component: left returned value, right returned value, output evidence | component count, then per component the left and the right dialogue |
//! | `0x39` | [`NODE_C_RELATED_APPLICATION`] | computation | the function path; left and right arguments; argument evidence; the body under three value binders | none |
//! | `0x3A` | [`NODE_V_QUANTIFIED_EVALUATION`] | value | per step, in pre-order: for a return, left returned value, right returned value, output evidence; for an application, the left and the right closed normal form | step count, then per step its step word and the left and the right dialogue |
//!
//! The two structural invariants the reader names rather than reporting as
//! a bare polarity fault are an endpoint child of [`NODE_VT_PATH`] that is
//! not a value, and a motive child of either transport that is not of its
//! family: the motive of [`NODE_C_PATH_TRANSPORT`] is a type-level function,
//! a value type scoped under the endpoint binder, and the motive of
//! [`NODE_C_TELESCOPE_TRANSPORT`] is a computation type, the dependent arrow
//! whose binders are the telescope. A higher-field layer is
//! [`HIGHER_GUARD`] followed by its tail position, or [`HIGHER_REDIRECT`]
//! followed by its target position; positions, depth and counts are unsigned
//! varints, and dialogues use the decision alphabet of
//! [`NODE_V_PATH_EQUIV`]'s evidence. The child of [`NODE_V_RETURNED`] is a
//! computation-family node, so a value or type child is refused as a
//! polarity fault.
//!
//! A quantified evaluation's step word is zero for a return and one more than
//! the related premise's de Bruijn index for an application; the reader
//! refuses a fibre past the index range at
//! [`crate::MalformedSite::PathEvidence`], as it refuses a dialogue premise
//! past it, and reads three children after a return and two after an
//! application.
//!
//! [`NODE_V_DEPENDENT_EVALUATION`] names the next function-identity
//! introduction, identity at dependent arrows, and carries no shape yet; a
//! reader refuses it as it refuses any unassigned byte. Higher-order argument
//! coverage needed no node of its own: the evaluation's kernel-generated
//! coverage binds a function argument as two functions and their identity.
//! Filling a slot of the range holds [`FORMAT_VERSION`]: every byte in both
//! ranges is a node tag, refused by name by the closed-vocabulary reader until
//! it is admitted, so [`NODE_V_QUANTIFIED_EVALUATION`] means nothing else to
//! any reader that predates it.
//!
//! # The lazy product
//!
//! The computation product `C & D` persists as its own former, binary as the
//! core holds it; a lazy record of `n` entries is its right-nested chain.
//! [`crate::types`] states why it is not the record of thunks.
//!
//! | byte | node | family | children, in order | inline payload |
//! | ---- | ---- | ------ | ------------------ | -------------- |
//! | `0x65` | [`NODE_CT_WITH`] | computation type | the left component type; the right component type | none |
//! | `0x66` | [`NODE_C_WITH`] | computation | the left component; the right component | none |
//! | `0x67` | [`NODE_C_PROJECT`] | computation | the observed pairing | the side, [`SIDE_LEFT`] or [`SIDE_RIGHT`] |
//!
//! The side byte precedes the child, as a tuple projection's component does;
//! any other side byte is refused as an unknown tag at the side site, as the
//! fixpoint's evidence byte is. All three children are computation-family
//! nodes, so a value or value-type child is refused as a polarity fault.
//! The three bytes hold [`FORMAT_VERSION`]: a reader that predates them
//! refuses each by name as an unassigned byte, so no artifact means anything
//! else by them.
//!
//! # The dependent pair
//!
//! The dependent pair `Σ (x : A). B` persists as its own former beside the
//! product, binary, its second child scoped under the first's binder; its
//! eliminator is the dependent split, whose motive binds the scrutinee and
//! whose body binds the two components. The pair itself is the two-component
//! [`NODE_V_TUPLE`], and its projections are [`NODE_C_TUPLE_PROJECTION`].
//!
//! | byte | node | family | children, in order | inline payload |
//! | ---- | ---- | ------ | ------------------ | -------------- |
//! | `0x6A` | [`NODE_VT_SIGMA`] | value type | the first factor; the second factor, under one value binder | none |
//! | `0x6B` | [`NODE_C_SIGMA_SPLIT`] | computation | the scrutinee value; the motive, a computation type under one value binder; the body, under two value binders | none |
//!
//! The motive child of [`NODE_C_SIGMA_SPLIT`] is a computation-type node, so
//! a value-type child there is refused as a polarity fault, as it is for the
//! nominal case's motive. Both bytes hold [`FORMAT_VERSION`]: a reader that
//! predates them refuses each by name as an unassigned byte, so no artifact
//! means anything else by them.
//!
//! # Univalence
//!
//! Univalence `ua(e)` persists as its own value former over the bi-invertible
//! record it is admitted on. The record carries the laws as its evidence and
//! its type names the identity the node inhabits, so the node has one child
//! and no inline payload.
//!
//! | byte | node | family | children, in order | inline payload |
//! | ---- | ---- | ------ | ------------------ | -------------- |
//! | `0x6D` | [`NODE_V_UNIVALENCE`] | value | the record | none |
//!
//! The byte moves [`FORMAT_VERSION`] to 6: a reader at 5 refuses the
//! artifact by its version before it meets the byte.
//!
//! # Universe paths
//!
//! `PathUniverse` has two value-code children; reflexivity has one code,
//! product paths have two paths, and transport has a path and input value.
//! [`NODE_V_PATH_EQUIV`] carries inline portable evidence followed by its
//! classifier, forward map and backward map children. Evidence is source then
//! target: a dialogue count, then each dialogue's decision count and unsigned
//! decision words. Unknown words and oversized negative-premise positions are
//! malformed; decoding never certifies a round trip.
//!
//! The portable decision alphabet comes from `gandr-kernel-conversion-trace`;
//! unit anchors carry no arena identity. Reusing that vocabulary avoids a
//! second replay protocol. The sharing-format witness preserves all
//! decisions, empty dialogues and direction boundaries against independent
//! bytes, and rejects malformed words and truncated prefixes. **Reversal:** a
//! new framing version, if the alphabet needs payloads that cannot be encoded
//! without changing existing word meanings.
//!
//! # Lists
//!
//! The List code [`NODE_VT_LIST`] has one value-type child, its element code.
//! Its native introductions are [`NODE_V_LIST_NIL`] and [`NODE_V_LIST_CONS`],
//! not Sum encodings or nominal data constructors. [`NODE_C_LIST_FOLD`]
//! carries five children in order: ambient element type, ambient result type,
//! list value, nil branch and cons branch. Only the cons branch binds values:
//! head first, folded result second, so the result is index zero. Both
//! branches return the annotated result type. The ordinary sharing format
//! persists this pure fragment; guarded recursive observations remain
//! separate in-memory programs.
//!
//! # Session codes
//!
//! Session codes use [`NODE_VT_SESSION`]. Their inline graph stores a root,
//! node count, and finite nodes tagged send `0x53`, receive `0x54`, select
//! `0x55`, offer `0x56`, end `0x57`, binder `0x58` and variable `0x59`. Graph
//! integers are canonical unsigned varints. A label is its byte count followed
//! by its exact UTF-8 bytes, each encoded as an unsigned varint. Choice maps
//! are in label order. The graph's only native child is one n-ary payload-type
//! product; payload slots index its parts. Internal recursion references
//! finite graph positions, never a native type-arena back edge.
//!
//! [`NODE_V_SESSION_PATH`] has two native children: its `Path_U` classifier
//! and one tuple of native payload-path values. Inline evidence is a sorted
//! set of source/target state pairs followed by ordered source/target
//! payload-slot obligations. Decoding rejects unknown opcodes, malformed
//! UTF-8, duplicate labels or relation pairs, truncation and noncanonical
//! encodings. Counts consume input before growing allocations; exhausted input
//! is `Truncated`, while the ordinary table and expanded-work budgets retain
//! their typed refusals. Contractivity, scope, relation coverage and payload
//! typing belong to kernel formation. All relation data participates in
//! canonical bytes even when conversion erases derivation pairs.
//!
//! **Choice.** Inline finite graph data with one native payload-code child
//! preserves the format's fixed child arities and ordinary content sharing
//! without recursive Rust ownership. **Alternatives.** Separate native
//! constructors would spread finite graph framing across seven additional
//! native cases; a second opaque payload-identity scheme would bypass universe
//! formation. **Reversal.** A distinct protocol universe or a persisted
//! endpoint-value language requires its own formation and elimination rules.
//! These tags encode protocol types and identity evidence, not live channels.
//!
//! # Flows
//!
//! [`NODE_VT_FLOW_UNIVERSE`] is `Flow_U`, the forward-only twin of
//! [`NODE_VT_PATH_UNIVERSE`], with the same two value-code children: source
//! then target. [`NODE_VT_FLOW`] is the element family `Flow(A, x, y)`, framed
//! as [`NODE_VT_PATH`]: the carrier, then source and target. Neither
//! classifier names a certificate kind, so every forward introduction shares
//! them. The introductions:
//!
//! | Node | Inline | Children |
//! | ---- | ------ | -------- |
//! | [`NODE_V_STAY`] | endpoint dialogues, as [`NODE_V_HERE`] | the point |
//! | [`NODE_V_FORWARD_FLOW`] | an image count, then one dialogue per image | classifier, translator, one output per image |
//! | [`NODE_V_FUNCTION_FLOW`] | none | classifier, domain flow, codomain flow |
//! | [`NODE_V_THEN`] | the seam byte, [`SEAM_SEQUENCE`] or [`SEAM_FEEDBACK`] | first flow, second flow |
//! | [`NODE_V_FLOW_PRODUCT`] | none | first flow, second flow, framed as [`NODE_V_PATH_PRODUCT`] |
//! | [`NODE_V_SESSION_FLOW`] | simulation evidence, as [`NODE_V_SESSION_PATH`] | classifier, payload-path tuple |
//!
//! A forward flow's image dialogues and outputs are the replayed translator
//! images in pattern order, so readmission compares each recorded output
//! against a fresh run rather than trusting it. [`NODE_C_RIDE`] is directed
//! transport, framed as [`NODE_C_PATH_TRANSPORT`]; [`NODE_C_TELESCOPE_RIDE`]
//! is its telescope form, framed as [`NODE_C_TELESCOPE_TRANSPORT`]. A seam
//! byte outside its two-letter alphabet is refused at the seam site. Every
//! flow byte holds [`FORMAT_VERSION`]: a reader that predates them refuses
//! each by name as an unassigned byte, so no artifact means anything else by
//! them.

use anodized::spec;

use crate::wire::FormatVersion;
use crate::wire::WireTag;

/// The four-byte artifact magic. The trailing byte is a v-family marker,
/// independent of the version field, which is a separate little-endian
/// sixteen-bit field.
///
/// # Specification
/// - requires: the value is interpreted in its declared framing or tag role.
/// - ensures: identifies the artifact family independently of the fixed-width
///   version field.
/// - panics: none.
/// - executable: none — this protocol constant is not callable; writer, reader
///   and catalogue-boundary observations carry its evidence.
///
/// # Adequacy
/// - hypothesis: L3 observes exact header/version framing and the boundary
///   between frozen and reserved tags. Named version, magic and tag refusals
///   separate field confusion and accidental acceptance; changing the protocol
///   requires revising its conformance evidence.
/// - witness: `tests::sharing_format::a_foreign_magic_is_refused_at_the_header`
/// - witness: `tests::sharing_format::the_empty_sequence_encodes_to_a_bare_header`
/// - witness: `tags::tests::the_frozen_block_keeps_its_order_around_the_retired_tags`
/// - witness: `tags::tests::the_reserved_sharing_block_sits_above_the_frozen_block`
pub const MAGIC: [u8; 4] = *b"GKX1";

/// The format version this crate writes and the only one it accepts.
///
/// Version two writes the version field and every fixed-width integer field
/// little-endian. Version three makes products, sums, tuples and cases n-ary:
/// [`NODE_VT_PRODUCT`], [`NODE_VT_SUM`], [`NODE_V_TUPLE`] and [`NODE_C_CASE`]
/// carry an inline child count, [`NODE_V_INJECTION`] an inline summand
/// position, and the unit, empty, unit-value and absurd tags `0x01`, `0x28`,
/// `0x0B` and `0x29` are retired, because the unit is the empty product and
/// tuple and the empty type the empty sum, eliminated by a case of no
/// branches. A retired tag is refused as any unassigned byte is. Version four
/// gives the [`KIND_ABSTRACT_TYPE`] segment a second root, the representation
/// the atom was sealed over, and after it the extent of the admission that
/// minted the atom, so a replay re-checks the sealed members against the
/// representation and closes the atom where the producer closed it. Version
/// five gives [`NODE_V_HERE`] an inline payload before its point: the dialogue
/// relating the point to each endpoint, which the kernel replays where the
/// point and an endpoint differ.
///
/// A refusal names the version it met rather than guessing at it, which is
/// what makes an older reader meeting a newer artifact stop with an accurate
/// reason.
///
/// # Specification
/// - requires: the value is interpreted in its declared framing or tag role.
/// - ensures: selects the one accepted format version, including its two-byte
///   little-endian framing.
/// - panics: none.
/// - executable: none — this protocol constant is not callable; writer, reader
///   and catalogue-boundary observations carry its evidence.
///
/// # Adequacy
/// - hypothesis: L3 observes exact header/version framing and the boundary
///   between frozen and reserved tags. Named version, magic and tag refusals
///   separate field confusion and accidental acceptance; changing the protocol
///   requires revising its conformance evidence.
/// - witness: `tests::sharing_format::a_predecessor_version_is_refused_by_name`
/// - witness: `tests::sharing_format::the_empty_sequence_encodes_to_a_bare_header`
/// - witness: `tags::tests::the_frozen_block_keeps_its_order_around_the_retired_tags`
/// - witness: `tags::tests::the_reserved_sharing_block_sits_above_the_frozen_block`
pub const FORMAT_VERSION: FormatVersion = FormatVersion(6);

/// Admission mark: admitted through the checked choke point.
pub const ADMISSION_CHECKED: WireTag = WireTag(0);
/// Admission mark: admitted through the warned bypass.
pub const ADMISSION_UNCHECKED: WireTag = WireTag(1);

/// Declaration kind: a typed definition.
pub const KIND_DEF: WireTag = WireTag(0);
/// Declaration kind: a tracked typed hole.
pub const KIND_AXIOM: WireTag = WireTag(1);
/// Declaration kind: a sealed abstract type.
pub const KIND_ABSTRACT_TYPE: WireTag = WireTag(2);
/// Declaration kind: the reserved module-signature kind.
pub const KIND_MODULE_SIG: WireTag = WireTag(3);
/// Declaration kind: the reserved module-definition kind.
pub const KIND_MODULE_DEF: WireTag = WireTag(4);
/// Declaration kind: the reserved functor-definition kind.
pub const KIND_FUNCTOR_DEF: WireTag = WireTag(5);

/// Base-type atom: the integer atom.
pub const BASE_INTEGER: WireTag = WireTag(0);
/// Base-type atom: the string atom.
pub const BASE_STRING: WireTag = WireTag(1);
/// Base-type atom: the numeric atom.
pub const BASE_NUMERIC: WireTag = WireTag(2);

/// Literal sign: non-negative, which the canonical zero always is.
pub const SIGN_NON_NEGATIVE: WireTag = WireTag(0);
/// Literal sign: negative.
pub const SIGN_NEGATIVE: WireTag = WireTag(1);

/// Fixpoint evidence: no claim, a partial fixpoint.
pub const FIXPOINT_PARTIAL: WireTag = WireTag(0);
/// Fixpoint evidence: structural recursion on the first parameter, replayed
/// as the stage typing at position zero.
pub const FIXPOINT_STRUCTURAL_DESCENT: WireTag = WireTag(1);
/// Fixpoint evidence: structural recursion on the parameter at a position,
/// the position following as a varint.
pub const FIXPOINT_STAGED: WireTag = WireTag(2);

/// Literal kind: an integer literal.
pub const LITERAL_INTEGER: WireTag = WireTag(0);
/// Literal kind: a string literal.
pub const LITERAL_TEXT: WireTag = WireTag(1);
/// Literal kind: a numeric literal.
pub const LITERAL_NUMERIC: WireTag = WireTag(2);

/// Landmark-constraint relation: `left ≤ right`.
pub const RELATION_LEQ: WireTag = WireTag(0);
/// Landmark-constraint relation: `left = right`.
pub const RELATION_EQ: WireTag = WireTag(1);

/// Node tag: a value-type base atom, with a base-type byte inline.
pub const NODE_VT_BASE: WireTag = WireTag(0x00);
/// Node tag: the universe of value types, with an inline level.
pub const NODE_VT_UNIVERSE: WireTag = WireTag(0x02);
/// Node tag: the product former, with an inline component count, over its
/// component value types in order; the unit type is the product of none.
pub const NODE_VT_PRODUCT: WireTag = WireTag(0x03);
/// Node tag: the sum former, with an inline summand count, over its summand
/// value types in order; the empty type is the sum of none.
pub const NODE_VT_SUM: WireTag = WireTag(0x04);
/// Node tag: the value-type thunk former, over one computation type.
pub const NODE_VT_THUNK: WireTag = WireTag(0x05);
/// Node tag: the value-type lift, with an inline target level, over one value
/// type.
pub const NODE_VT_LIFT: WireTag = WireTag(0x06);
/// Node tag: the returner former, over one value type.
pub const NODE_CT_RETURNER: WireTag = WireTag(0x07);
/// Node tag: the arrow former, over a value-type domain and a computation-type
/// codomain.
pub const NODE_CT_ARROW: WireTag = WireTag(0x08);
/// Node tag: a bound value variable, with an inline de Bruijn index.
pub const NODE_V_VARIABLE: WireTag = WireTag(0x09);
/// Node tag: a constant reference, with an inline admission position.
pub const NODE_V_CONSTANT: WireTag = WireTag(0x0A);
/// Node tag: a literal value, with an inline literal kind and canonical
/// payload.
pub const NODE_V_LITERAL: WireTag = WireTag(0x0C);
/// Node tag: a tuple value, with an inline component count, over its
/// components in order; the unit value is the tuple of none.
pub const NODE_V_TUPLE: WireTag = WireTag(0x0D);
/// Node tag: a sum injection value, with an inline summand position, over one
/// value.
pub const NODE_V_INJECTION: WireTag = WireTag(0x0E);
/// Node tag: a thunk value, over one computation.
pub const NODE_V_THUNK: WireTag = WireTag(0x0F);
/// Node tag: a value lift, with an inline target level, over one value.
pub const NODE_V_LIFT: WireTag = WireTag(0x10);
/// Node tag: a lambda computation, over one computation.
pub const NODE_C_LAMBDA: WireTag = WireTag(0x11);
/// Node tag: an application, over a computation head and a value argument.
pub const NODE_C_APPLICATION: WireTag = WireTag(0x12);
/// Node tag: a returner computation, over one value.
pub const NODE_C_RETURN: WireTag = WireTag(0x13);
/// Node tag: a bind computation, over two computations.
pub const NODE_C_BIND: WireTag = WireTag(0x14);
/// Node tag: a force computation, over one value.
pub const NODE_C_FORCE: WireTag = WireTag(0x15);
/// Node tag: a case computation, with an inline branch count, over a value
/// scrutinee and its computation branches in summand order.
pub const NODE_C_CASE: WireTag = WireTag(0x16);
/// Node tag: a sealed abstract type, with the admission position of its
/// abstract-type declaration inline and no children.
pub const NODE_VT_ABSTRACT: WireTag = WireTag(0x17);
/// Node tag: the dependent arrow, over a value-type domain and a
/// computation-type codomain scoped under one value binder.
pub const NODE_CT_PI: WireTag = WireTag(0x18);
/// Node tag: the universe-decoding former, with an inline level and one value
/// child: the code the type is read off.
pub const NODE_VT_ELEMENT: WireTag = WireTag(0x19);
/// Node tag: the universe of computation types, with an inline level.
pub const NODE_VT_COMPUTATION_UNIVERSE: WireTag = WireTag(0x1A);
/// Node tag: the computation-decoding former, with an inline level and one
/// value child: the code the computation type is read off.
pub const NODE_CT_ELEMENT: WireTag = WireTag(0x1B);
/// Node tag: the code of a value type, over one value type.
pub const NODE_V_QUOTE: WireTag = WireTag(0x1C);
/// Node tag: the code of a computation type, over one computation type.
pub const NODE_V_QUOTE_COMPUTATION: WireTag = WireTag(0x1D);
/// Node tag: the static Pi, over a value-type domain and a value-type
/// codomain in the ambient context.
pub const NODE_VT_STATIC_PI: WireTag = WireTag(0x1E);
/// Node tag: a static application, over a value head and a value argument.
pub const NODE_V_STATIC_APPLICATION: WireTag = WireTag(0x1F);

/// Reserved node tag: the stored sharing plane's value-family sharing former.
pub const NODE_SHARE_VALUE: WireTag = WireTag(0x20);
/// Reserved node tag: the stored sharing plane's computation-family sharing
/// former.
pub const NODE_SHARE_COMPUTATION: WireTag = WireTag(0x21);
/// Reserved node tag: the stored sharing plane's value-type sharing former.
pub const NODE_SHARE_VALUE_TYPE: WireTag = WireTag(0x22);
/// Reserved node tag: the stored sharing plane's computation-type sharing
/// former.
pub const NODE_SHARE_COMP_TYPE: WireTag = WireTag(0x23);
/// The first tag of the reserved stored-sharing block.
///
/// # Specification
/// - requires: the value is interpreted in its declared framing or tag role.
/// - ensures: starts the reserved eight-tag sharing interval immediately after
///   the frozen node block.
/// - panics: none.
/// - executable: none — this protocol constant is not callable; writer, reader
///   and catalogue-boundary observations carry its evidence.
///
/// # Adequacy
/// - hypothesis: L3 observes exact header/version framing and the boundary
///   between frozen and reserved tags. Named version, magic and tag refusals
///   separate field confusion and accidental acceptance; changing the protocol
///   requires revising its conformance evidence.
/// - witness: `tags::tests::the_reserved_sharing_block_sits_above_the_frozen_block`
/// - witness: `tests::sharing_format::the_empty_sequence_encodes_to_a_bare_header`
/// - witness: `tags::tests::the_frozen_block_keeps_its_order_around_the_retired_tags`
pub const SHARING_BLOCK_FIRST: WireTag = NODE_SHARE_VALUE;
/// The last tag of the reserved stored-sharing block: the fourth held slot,
/// which the explicit weakening form would take one family at a time.
///
/// # Specification
/// - requires: the value is interpreted in its declared framing or tag role.
/// - ensures: ends the reserved eight-tag sharing interval without overlap with
///   the frozen node block.
/// - panics: none.
/// - executable: none — this protocol constant is not callable; writer, reader
///   and catalogue-boundary observations carry its evidence.
///
/// # Adequacy
/// - hypothesis: L3 observes exact header/version framing and the boundary
///   between frozen and reserved tags. Named version, magic and tag refusals
///   separate field confusion and accidental acceptance; changing the protocol
///   requires revising its conformance evidence.
/// - witness: `tags::tests::the_reserved_sharing_block_sits_above_the_frozen_block`
/// - witness: `tests::sharing_format::the_empty_sequence_encodes_to_a_bare_header`
/// - witness: `tags::tests::the_frozen_block_keeps_its_order_around_the_retired_tags`
pub const SHARING_BLOCK_LAST: WireTag = WireTag(0x27);

/// Node tag: universe paths, over source and target codes.
pub const NODE_VT_PATH_UNIVERSE: WireTag = WireTag(0x2A);

/// Node tag: reflexivity, over its code.
pub const NODE_V_PATH_REFL: WireTag = WireTag(0x2B);

/// Node tag: equivalence, with inline evidence and classifier/map children.
pub const NODE_V_PATH_EQUIV: WireTag = WireTag(0x2C);

/// Node tag: componentwise product of paths.
pub const NODE_V_PATH_PRODUCT: WireTag = WireTag(0x2D);

/// Node tag: transport, over a path and its source value.
pub const NODE_C_TRANSPORT: WireTag = WireTag(0x2E);

/// Node tag: element identity `Path(A, a, b)`, over the value type `A` and
/// the endpoint values `a` and `b`.
///
/// The first byte of the identity range: the higher field and function
/// identity are both inhabitants of this former at a particular value type.
pub const NODE_VT_PATH: WireTag = WireTag(0x30);

/// Node tag: `here(a)`, the diagonal of element identity, over its point,
/// with the dialogue relating the point to each endpoint.
///
/// One child rather than three: it inhabits `Path(A, a, b)` exactly when
/// both endpoints convert to its point, so storing them again would only
/// admit a disagreeing copy. The conversion itself travels as two dialogues,
/// left then right, each a decision count and the decision words of
/// [`NODE_V_PATH_EQUIV`]'s evidence: the kernel replays them, unfolding only
/// what they name, so a δ-step under a binder of an endpoint is a recorded
/// step rather than the kernel's own search.
pub const NODE_V_HERE: WireTag = WireTag(0x31);

/// Node tag: dependent transport along an element path, over the motive, the
/// path and the input value.
///
/// A byte apart from [`NODE_C_TRANSPORT`], which transports along a universe
/// path with the family implicit: here the motive is explicit syntax, a value
/// type scoped under one binder, so the substitution law has a family to
/// substitute each endpoint into.
pub const NODE_C_PATH_TRANSPORT: WireTag = WireTag(0x32);

/// Node tag: the guarded higher field, an inline guarded program over one
/// evidence value per guard layer.
///
/// Identity between identities is codata; its finite syntax is a graph whose
/// cycles a guard must break, replayed to the depth the node states. The
/// guard and redirect alphabet is [`HIGHER_GUARD`] and [`HIGHER_REDIRECT`].
pub const NODE_V_HIGHER: WireTag = WireTag(0x33);

/// Higher-field layer kind: expose one evidence value, then observe its tail.
pub const HIGHER_GUARD: WireTag = WireTag(0);
/// Higher-field layer kind: follow an edge without exposing a constructor.
pub const HIGHER_REDIRECT: WireTag = WireTag(1);

/// Node tag: a returned endpoint, the value a pure computation returns,
/// standing where a value is read, over that one computation.
///
/// An identity endpoint such as `mul(neutral, x)` is a computation's result
/// rather than a value former; the node keeps the computation, so the kernel
/// re-derives the result by its own reduction instead of trusting a value a
/// producer computed.
pub const NODE_V_RETURNED: WireTag = WireTag(0x34);

/// Node tag: transport over a two-entry telescope, over the motive, the path,
/// the second entry's source point, the path over the first, and the input
/// value.
///
/// A byte apart from [`NODE_C_PATH_TRANSPORT`] rather than a flag on it: the
/// motive here is a computation type, the dependent arrow `Π (y : A). Π (z :
/// B). F C` whose two binders are the telescope, and two more value children
/// carry the path's second coordinate, so a reader that predates the byte
/// refuses it whole instead of misreading a shorter node.
pub const NODE_C_TELESCOPE_TRANSPORT: WireTag = WireTag(0x35);

/// Node tag: higher evaluation, the introduction of identity at a thunk code,
/// with inline replay dialogues over three values per coverage component.
///
/// `refl` of a λ and function extensionality share it: both relate related
/// inputs to related outputs, one component per kernel-generated coverage
/// pattern, each replayed rather than trusted.
pub const NODE_V_HIGHER_EVALUATION: WireTag = WireTag(0x38);

/// Node tag: application at related inputs, the related-inputs product's
/// elimination, over the function path, both arguments, their evidence and
/// a body under three binders.
///
/// The body binds the left result, the right result and their identity,
/// innermost last: the output endpoints are the two returned values, which
/// only evaluation names, so the eliminator continues rather than returns.
pub const NODE_C_RELATED_APPLICATION: WireTag = WireTag(0x39);

/// Node tag: quantified evaluation, the introduction of identity at a thunk
/// code whose body applies its higher-order argument, with inline steps over
/// their value children.
///
/// Each coverage component is a pre-order tree: an application step relates
/// both sides stuck at the functions one premise relates, and opens one branch
/// per covering pattern of that function's result relation; a return step
/// closes a branch as a higher-evaluation component does.
pub const NODE_V_QUANTIFIED_EVALUATION: WireTag = WireTag(0x3A);

/// Reserved node tag: higher evaluation at a dependent arrow.
pub const NODE_V_DEPENDENT_EVALUATION: WireTag = WireTag(0x3B);

/// Node tag: forward-only universe flows, over source and target codes.
pub const NODE_VT_FLOW_UNIVERSE: WireTag = WireTag(0x48);

/// Node tag: finite session simulation, classifier and payload-proof tuple.
pub const NODE_V_SESSION_FLOW: WireTag = WireTag(0x49);

/// Node tag: directed element identity `Flow(A, x, y)`, over a value type and
/// two endpoint values.
pub const NODE_VT_FLOW: WireTag = WireTag(0x4A);

/// Node tag: directed reflexivity `stay`, inline endpoint dialogues and one
/// point value.
pub const NODE_V_STAY: WireTag = WireTag(0x4B);

/// Node tag: a leaf-natural forward flow, inline image dialogues, then its
/// classifier, translator and one output per image.
pub const NODE_V_FORWARD_FLOW: WireTag = WireTag(0x4C);

/// Node tag: the arrow's action at function codes, over its classifier and the
/// domain and codomain boundary flows.
pub const NODE_V_FUNCTION_FLOW: WireTag = WireTag(0x4D);

/// Node tag: composition `then`, an inline seam byte and two flows.
pub const NODE_V_THEN: WireTag = WireTag(0x4E);

/// Node tag: directed transport `ride`, over a motive under one value binder,
/// a flow and the input value.
pub const NODE_C_RIDE: WireTag = WireTag(0x4F);

/// Node tag: the strictly positive list code, over one element type.
pub const NODE_VT_LIST: WireTag = WireTag(0x50);

/// Node tag: finite session graph and one payload-telescope child.
pub const NODE_VT_SESSION: WireTag = WireTag(0x52);

/// Node tag: finite bisimulation, classifier and payload-proof tuple.
pub const NODE_V_SESSION_PATH: WireTag = WireTag(0x5A);

/// Declaration tag: a generative datatype with a checked constructor table.
pub const KIND_DATA: WireTag = WireTag(0x06);
/// Declaration tag: a typed definition whose segment closes with the path
/// endpoints its type conversions relate.
///
/// After the [`KIND_DEF`] fields comes a pair count, at least one, then per
/// pair the left and right endpoint roots and a dialogue: a decision count
/// and the decision words of [`NODE_V_HERE`]'s alphabet. The kernel replays a
/// pair's dialogue where a path type's endpoints meet that pair and its
/// forced reading leaves them apart. A definition with no related pair writes
/// [`KIND_DEF`], so every other artifact keeps its bytes, and a reader
/// predating this kind refuses it as an unknown declaration kind rather than
/// misreading it, which is why the format version holds.
pub const KIND_DEF_RELATING: WireTag = WireTag(0x07);
/// Declaration tag: a presented datatype, whose segment closes with the rules
/// rewriting its constructor terms.
///
/// After the [`KIND_DATA`] fields comes a rule count, at least one, then per
/// rule its left and its right side, each a node count and that many nodes
/// in pre-order: [`RULE_CONSTRUCTOR`] and a constructor ordinal, or
/// [`RULE_VARIABLE`] and a pattern variable's ordinal. The kernel reads the
/// rules wherever it converts the type's terms. A datatype with no rule
/// writes [`KIND_DATA`], so every other artifact keeps its bytes, and a reader
/// predating this kind refuses it as an unknown declaration kind rather than
/// misreading it, which is why the format version holds.
pub const KIND_DATA_PRESENTED: WireTag = WireTag(0x08);
/// Declaration tag: a typed definition whose segment closes with the laws its
/// folds rest on.
///
/// After the [`KIND_DEF`] fields comes the related block as
/// [`KIND_DEF_RELATING`] writes it, its pair count here possibly zero, then a
/// law count, at least one, and each law's admission position. The kernel
/// instantiates a law where a fold over a presented type computes the two
/// sides of the law's rule apart, and the definition's audit rests on every
/// law named. A definition resting on no law writes [`KIND_DEF`] or
/// [`KIND_DEF_RELATING`], so every other artifact keeps its bytes, and a
/// reader predating this kind refuses it as an unknown declaration kind rather
/// than misreading it, which is why the format version holds.
pub const KIND_DEF_LAWFUL: WireTag = WireTag(0x09);
/// Declaration tag: a type of words, a presented datatype whose segment closes
/// with the free cells it is minted over.
///
/// After the [`KIND_DATA_PRESENTED`] fields, its rule count here possibly
/// zero, comes the sort's admission position, then a cell count and per cell
/// its source and its target, each a rule side as the rules write theirs. The
/// kernel re-mints the constructor table and the rules from the cells and
/// reads `Path(T, a, a)` as the words where the sort `T`'s cells loop at `a`.
/// A presented datatype with no cell writes [`KIND_DATA_PRESENTED`], so every
/// other artifact keeps its bytes, and a reader predating this kind refuses it
/// as an unknown declaration kind rather than misreading it, which is why the
/// format version holds.
pub const KIND_DATA_WORDS: WireTag = WireTag(0x0A);
/// Rule node tag: a constructor of the declaration's own table.
pub const RULE_CONSTRUCTOR: WireTag = WireTag(0);
/// Rule node tag: a pattern variable.
pub const RULE_VARIABLE: WireTag = WireTag(1);
/// Node tag: nominal application with a counted argument vector.
pub const NODE_VT_DATA: WireTag = WireTag(0x5d);
/// Node tag: structural record classifier with counted labels and children.
pub const NODE_VT_RECORD: WireTag = WireTag(0x5e);
/// Node tag: constructor ordinal and counted field vector.
pub const NODE_V_CONSTRUCTOR: WireTag = WireTag(0x5f);
/// Node tag: record literal with counted labels and children.
pub const NODE_V_RECORD: WireTag = WireTag(0x60);
/// Node tag: motive-bearing nominal elimination with counted branches.
pub const NODE_C_DATA_CASE: WireTag = WireTag(0x61);
/// Node tag: named record projection.
pub const NODE_C_RECORD_PROJECTION: WireTag = WireTag(0x62);
/// Node tag: a guarded fixpoint, over one computation under its self binder.
pub const NODE_C_FIXPOINT: WireTag = WireTag(0x63);
/// Node tag: positional tuple projection.
pub const NODE_C_TUPLE_PROJECTION: WireTag = WireTag(0x64);
/// Node tag: the empty native list.
pub const NODE_V_LIST_NIL: WireTag = WireTag(0x51);
/// Node tag: a native cell, over its head and list tail.
pub const NODE_V_LIST_CONS: WireTag = WireTag(0x5B);
/// Node tag: pure fold, over element, result, list, nil and cons branches.
pub const NODE_C_LIST_FOLD: WireTag = WireTag(0x5C);
/// Node tag: the lazy product `C & D`, over its left and right component
/// computation types.
pub const NODE_CT_WITH: WireTag = WireTag(0x65);
/// Node tag: the lazy pairing of two computations, introducing the lazy
/// product of their types; neither component runs until it is observed.
pub const NODE_C_WITH: WireTag = WireTag(0x66);
/// Node tag: the projection of one side of a lazy pairing, with the side
/// byte inline before its one computation child.
pub const NODE_C_PROJECT: WireTag = WireTag(0x67);
/// Projection side: the left component of a lazy pairing.
pub const SIDE_LEFT: WireTag = WireTag(0);
/// Projection side: the right component of a lazy pairing.
pub const SIDE_RIGHT: WireTag = WireTag(1);
/// Node tag: directed transport over a two-entry telescope, over its motive,
/// flow, start point, flow over it and input value.
pub const NODE_C_TELESCOPE_RIDE: WireTag = WireTag(0x68);
/// Node tag: componentwise product of universe flows, over the flow of the
/// left components and the flow of the right.
pub const NODE_V_FLOW_PRODUCT: WireTag = WireTag(0x69);
/// Node tag: the dependent pair `Σ (x : A). B`, over its first factor and its
/// second factor scoped under the first's binder.
pub const NODE_VT_SIGMA: WireTag = WireTag(0x6A);
/// Node tag: the dependent pair's eliminator, over its scrutinee, its motive
/// under the scrutinee binder and its body under the two components.
pub const NODE_C_SIGMA_SPLIT: WireTag = WireTag(0x6B);
/// Node tag: univalence `ua(e)`, over the bi-invertible record it is admitted
/// on.
pub const NODE_V_UNIVALENCE: WireTag = WireTag(0x6D);
/// Composition seam: the first output feeds the second input.
pub const SEAM_SEQUENCE: WireTag = WireTag(0);
/// Composition seam: the second output also feeds back into the first input.
pub const SEAM_FEEDBACK: WireTag = WireTag(1);
/// The number of subterm-table child references an entry carries after its
/// inline payload.
///
/// # Specification
/// - requires: the quantity or verdict is interpreted for its row and
///   classification criterion.
/// - ensures: retains the row observation without converting a token bound into
///   a child count or collapsing the two classification criteria.
/// - panics: none.
/// - executable: none — this metadata carrier is not callable; row construction
///   and the complete catalogue witnesses observe its meaning.
///
/// # Adequacy
/// - hypothesis: L2 compares all 32 frozen rows with independently constructed
///   arena formers through their child relation. L3 observes the complete tag
///   interval, the reserved sharing boundary, one-token contributions,
///   finite/unbounded classifications and the base-atom split. These
///   distinguish tag reuse, wrong arity and collapsed classification criteria;
///   arbitrary extension vocabularies are outside this fixed catalogue.
/// - witness: `tags::tests::the_tag_table_matches_the_wire_arities`
/// - witness: `tags::tests::the_frozen_block_keeps_its_order_around_the_retired_tags`
/// - witness: `tags::tests::the_reserved_sharing_block_sits_above_the_frozen_block`
/// - witness: `tags::tests::every_row_states_one_token_and_agrees_with_its_verdicts`
/// - witness: `tags::tests::the_base_atom_row_is_the_one_verdict_split`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ChildArity
{
    /// Exactly this many child references follow the inline payload.
    Fixed(u8),
    /// This many fixed children precede an inline-counted child vector.
    Counted(u8),
}

/// A count of storage tokens: a tag's own contribution, or the finite bound on
/// a tag together with its inline payload.
///
/// # Specification
/// - requires: the quantity or verdict is interpreted for its row and
///   classification criterion.
/// - ensures: retains the row observation without converting a token bound into
///   a child count or collapsing the two classification criteria.
/// - panics: none.
/// - executable: none — this metadata carrier is not callable; row construction
///   and the complete catalogue witnesses observe its meaning.
///
/// # Adequacy
/// - hypothesis: L2 compares all 32 frozen rows with independently constructed
///   arena formers through their child relation. L3 observes the complete tag
///   interval, the reserved sharing boundary, one-token contributions,
///   finite/unbounded classifications and the base-atom split. These
///   distinguish tag reuse, wrong arity and collapsed classification criteria;
///   arbitrary extension vocabularies are outside this fixed catalogue.
/// - witness: `tags::tests::the_tag_table_matches_the_wire_arities`
/// - witness: `tags::tests::the_frozen_block_keeps_its_order_around_the_retired_tags`
/// - witness: `tags::tests::the_reserved_sharing_block_sits_above_the_frozen_block`
/// - witness: `tags::tests::every_row_states_one_token_and_agrees_with_its_verdicts`
/// - witness: `tags::tests::the_base_atom_row_is_the_one_verdict_split`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TokenCount(u8);

impl From<TokenCount> for u8
{
    /// The token count the wrapper carries.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: TokenCount) -> Self
    {
        count.0
    }
}

/// The storage-boundary classification recorded for one wire tag.
///
/// The alias criterion is the conservative rule: a tag is an alias only when
/// its payload has one constructor and a finite static token bound. The
/// threshold alternative admits a bounded multi-constructor payload when its
/// duplication bound fits a threshold the storage tier chooses; recording the
/// verdict symbolically lets the storage tier choose without reopening this
/// table.
///
/// # Specification
/// - requires: the quantity or verdict is interpreted for its row and
///   classification criterion.
/// - ensures: retains the row observation without converting a token bound into
///   a child count or collapsing the two classification criteria.
/// - panics: none.
/// - executable: none — this metadata carrier is not callable; row construction
///   and the complete catalogue witnesses observe its meaning.
///
/// # Adequacy
/// - hypothesis: L2 compares all 32 frozen rows with independently constructed
///   arena formers through their child relation. L3 observes the complete tag
///   interval, the reserved sharing boundary, one-token contributions,
///   finite/unbounded classifications and the base-atom split. These
///   distinguish tag reuse, wrong arity and collapsed classification criteria;
///   arbitrary extension vocabularies are outside this fixed catalogue.
/// - witness: `tags::tests::the_tag_table_matches_the_wire_arities`
/// - witness: `tags::tests::the_frozen_block_keeps_its_order_around_the_retired_tags`
/// - witness: `tags::tests::the_reserved_sharing_block_sits_above_the_frozen_block`
/// - witness: `tags::tests::every_row_states_one_token_and_agrees_with_its_verdicts`
/// - witness: `tags::tests::the_base_atom_row_is_the_one_verdict_split`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum NodeTagVerdict
{
    /// The constructor may be represented inline.
    Alias,
    /// The constructor is a content-defined boundary candidate.
    Boundary,
}

/// The first-order shape and storage classification of one node tag.
///
/// # Specification
/// - requires: when used as protocol metadata, the fields describe the
///   corresponding frozen node former.
/// - ensures: records the tag, child arity, one-token contribution, optional
///   inline bound and the two distinct storage classifications.
/// - provides: protocol metadata, not validation of arbitrary caller-authored
///   records. The const row constructors carry local predicates; the complete
///   catalogue is compared with arena observations.
/// - panics: none.
/// - executable: none — the record has no invocation boundary; const row
///   constructors check its local fields and catalogue witnesses check
///   cross-component agreement.
///
/// # Adequacy
/// - hypothesis: L2 compares all 32 frozen rows with independently constructed
///   arena formers through their child relation. L3 observes the complete tag
///   interval, the reserved sharing boundary, one-token contributions,
///   finite/unbounded classifications and the base-atom split. These
///   distinguish tag reuse, wrong arity and collapsed classification criteria;
///   arbitrary extension vocabularies are outside this fixed catalogue.
/// - witness: `tags::tests::the_tag_table_matches_the_wire_arities`
/// - witness: `tags::tests::the_frozen_block_keeps_its_order_around_the_retired_tags`
/// - witness: `tags::tests::the_reserved_sharing_block_sits_above_the_frozen_block`
/// - witness: `tags::tests::every_row_states_one_token_and_agrees_with_its_verdicts`
/// - witness: `tags::tests::the_base_atom_row_is_the_one_verdict_split`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NodeTagDescription
{
    /// The frozen wire tag.
    pub tag: WireTag,
    /// The number of child references emitted after the inline payload.
    pub child_arity: ChildArity,
    /// The tag's own token contribution.
    pub token_contribution: TokenCount,
    /// The finite inline token bound, or `None` for an unbounded payload.
    pub max_token_bound: Option<TokenCount>,
    /// The verdict under the single-constructor-plus-finite-bound criterion.
    pub alias_verdict: NodeTagVerdict,
    /// The verdict under the threshold criterion.
    pub threshold_verdict: NodeTagVerdict,
}

/// Build one row of [`NODE_TAG_TABLE`].
///
/// # Specification
/// - requires: `tag` is a native node tag, a former [`NODE_TAG_TABLE`] lists,
///   not an inline opcode or reservation, and the two verdicts are the
///   classifications recorded for it.
/// - ensures: returns the description carrying its arguments unchanged, with
///   the tag's own token contribution fixed at one.
/// - provides: the one row constructor, so every row agrees that a tag
///   contributes exactly one storage token.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 compares the native rows with independently constructed
///   arena formers through their child relation. L3 observes the complete tag
///   vocabulary, the reserved sharing boundary, one-token contributions,
///   finite/unbounded classifications and the base-atom split. These
///   distinguish tag reuse, wrong arity and collapsed classification criteria;
///   arbitrary extension vocabularies are outside this fixed catalogue.
/// - witness: `tags::tests::the_tag_table_matches_the_wire_arities`
/// - witness: `tags::tests::the_frozen_block_keeps_its_order_around_the_retired_tags`
/// - witness: `tags::tests::the_reserved_sharing_block_sits_above_the_frozen_block`
/// - witness: `tags::tests::every_row_states_one_token_and_agrees_with_its_verdicts`
/// - witness: `tags::tests::the_base_atom_row_is_the_one_verdict_split`
#[spec(
    requires: !matches!(tag.0, 0x01 | 0x0B) && (tag.0 <= NODE_V_STATIC_APPLICATION.0 || (tag.0 >= NODE_VT_PATH_UNIVERSE.0 && tag.0 <= NODE_C_TRANSPORT.0) || matches!(tag, NODE_VT_PATH | NODE_V_HERE | NODE_C_PATH_TRANSPORT | NODE_V_HIGHER | NODE_V_RETURNED | NODE_C_TELESCOPE_TRANSPORT | NODE_V_HIGHER_EVALUATION | NODE_C_RELATED_APPLICATION | NODE_V_QUANTIFIED_EVALUATION | NODE_VT_FLOW_UNIVERSE | NODE_V_SESSION_FLOW | NODE_VT_FLOW | NODE_V_STAY | NODE_V_FORWARD_FLOW | NODE_V_FUNCTION_FLOW | NODE_V_THEN | NODE_C_RIDE | NODE_VT_LIST | NODE_V_LIST_NIL | NODE_VT_SESSION | NODE_V_SESSION_PATH | NODE_V_LIST_CONS | NODE_C_LIST_FOLD | NODE_C_TELESCOPE_RIDE | NODE_V_FLOW_PRODUCT | NODE_VT_SIGMA | NODE_C_SIGMA_SPLIT | NODE_V_UNIVALENCE) || (tag.0 >= NODE_VT_DATA.0 && tag.0 <= NODE_C_PROJECT.0))
            && match max_token_bound { Some(bound) => bound.0 >= 1, None => true },
    ensures: |ret| ret.tag.0 == tag.0
            && matches!((ret.child_arity, child_arity), (ChildArity::Fixed(a), ChildArity::Fixed(b)) | (ChildArity::Counted(a), ChildArity::Counted(b)) if a == b)
            && ret.token_contribution.0 == 1
            && match (ret.max_token_bound, max_token_bound) { (Some(actual), Some(expected)) => actual.0 == expected.0, (None, None) => true, _ => false }
            && matches!((ret.alias_verdict, alias_verdict), (NodeTagVerdict::Alias, NodeTagVerdict::Alias) | (NodeTagVerdict::Boundary, NodeTagVerdict::Boundary))
            && matches!((ret.threshold_verdict, threshold_verdict), (NodeTagVerdict::Alias, NodeTagVerdict::Alias) | (NodeTagVerdict::Boundary, NodeTagVerdict::Boundary)),
)]
const fn row(
    tag: WireTag,
    child_arity: ChildArity,
    max_token_bound: Option<TokenCount>,
    alias_verdict: NodeTagVerdict,
    threshold_verdict: NodeTagVerdict,
) -> NodeTagDescription
{
    NodeTagDescription {
        tag,
        child_arity,
        token_contribution: TokenCount(1),
        max_token_bound,
        alias_verdict,
        threshold_verdict,
    }
}

/// A row for a former whose payload is unbounded, hence a boundary under both
/// criteria.
///
/// # Specification
/// - requires: `tag` names a native former [`NODE_TAG_TABLE`] lists whose
///   inline payload has no finite token bound.
/// - ensures: returns the row with no token bound and both verdicts
///   [`NodeTagVerdict::Boundary`].
/// - provides: the shorthand that keeps an unbounded payload from being
///   recorded as an alias by hand.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 compares the native rows with independently constructed
///   arena formers through their child relation. L3 observes the complete tag
///   vocabulary, the reserved sharing boundary, one-token contributions,
///   finite/unbounded classifications and the base-atom split. These
///   distinguish tag reuse, wrong arity and collapsed classification criteria;
///   arbitrary extension vocabularies are outside this fixed catalogue.
/// - witness: `tags::tests::the_tag_table_matches_the_wire_arities`
/// - witness: `tags::tests::the_frozen_block_keeps_its_order_around_the_retired_tags`
/// - witness: `tags::tests::the_reserved_sharing_block_sits_above_the_frozen_block`
/// - witness: `tags::tests::every_row_states_one_token_and_agrees_with_its_verdicts`
/// - witness: `tags::tests::the_base_atom_row_is_the_one_verdict_split`
#[spec(
    requires: !matches!(tag.0, 0x01 | 0x0B) && (tag.0 <= NODE_V_STATIC_APPLICATION.0 || (tag.0 >= NODE_VT_PATH_UNIVERSE.0 && tag.0 <= NODE_C_TRANSPORT.0) || matches!(tag, NODE_VT_PATH | NODE_V_HERE | NODE_C_PATH_TRANSPORT | NODE_V_HIGHER | NODE_V_RETURNED | NODE_C_TELESCOPE_TRANSPORT | NODE_V_HIGHER_EVALUATION | NODE_C_RELATED_APPLICATION | NODE_V_QUANTIFIED_EVALUATION | NODE_VT_FLOW_UNIVERSE | NODE_V_SESSION_FLOW | NODE_VT_FLOW | NODE_V_STAY | NODE_V_FORWARD_FLOW | NODE_V_FUNCTION_FLOW | NODE_V_THEN | NODE_C_RIDE | NODE_VT_LIST | NODE_V_LIST_NIL | NODE_VT_SESSION | NODE_V_SESSION_PATH | NODE_V_LIST_CONS | NODE_C_LIST_FOLD | NODE_C_TELESCOPE_RIDE | NODE_V_FLOW_PRODUCT | NODE_VT_SIGMA | NODE_C_SIGMA_SPLIT | NODE_V_UNIVALENCE) || (tag.0 >= NODE_VT_DATA.0 && tag.0 <= NODE_C_PROJECT.0))
            && !matches!(tag, NODE_VT_BASE | NODE_V_VARIABLE | NODE_V_CONSTANT | NODE_VT_ABSTRACT | NODE_V_LIST_NIL),
    ensures: |ret| ret.tag.0 == tag.0
            && matches!((ret.child_arity, child_arity), (ChildArity::Fixed(a), ChildArity::Fixed(b)) | (ChildArity::Counted(a), ChildArity::Counted(b)) if a == b)
            && ret.token_contribution.0 == 1
            && ret.max_token_bound.is_none()
            && matches!(ret.alias_verdict, NodeTagVerdict::Boundary)
            && matches!(ret.threshold_verdict, NodeTagVerdict::Boundary),
)]
const fn unbounded(
    tag: WireTag,
    child_arity: ChildArity,
) -> NodeTagDescription
{
    row(
        tag,
        child_arity,
        None,
        NodeTagVerdict::Boundary,
        NodeTagVerdict::Boundary,
    )
}

/// A row for a leaf whose payload is finitely bounded, hence an alias under
/// both criteria.
///
/// # Specification
/// - requires: `tag` names a leaf former whose inline payload is bounded by
///   `bound` storage tokens.
/// - ensures: returns the row with no children, that bound, and both verdicts
///   [`NodeTagVerdict::Alias`].
/// - provides: the shorthand for the conservative alias case, so the zero-arity
///   and the finite bound cannot disagree in a hand-written row.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 compares all 32 frozen rows with independently constructed
///   arena formers through their child relation. L3 observes the complete tag
///   interval, the reserved sharing boundary, one-token contributions,
///   finite/unbounded classifications and the base-atom split. These
///   distinguish tag reuse, wrong arity and collapsed classification criteria;
///   arbitrary extension vocabularies are outside this fixed catalogue.
/// - witness: `tags::tests::the_tag_table_matches_the_wire_arities`
/// - witness: `tags::tests::the_frozen_block_keeps_its_order_around_the_retired_tags`
/// - witness: `tags::tests::the_reserved_sharing_block_sits_above_the_frozen_block`
/// - witness: `tags::tests::every_row_states_one_token_and_agrees_with_its_verdicts`
/// - witness: `tags::tests::the_base_atom_row_is_the_one_verdict_split`
#[spec(
    requires: match tag { NODE_V_LIST_NIL => bound.0 >= 1, NODE_V_VARIABLE | NODE_V_CONSTANT | NODE_VT_ABSTRACT => bound.0 >= 2, _ => false },
    ensures: |ret| ret.tag.0 == tag.0
            && matches!(ret.child_arity, ChildArity::Fixed(0))
            && ret.token_contribution.0 == 1
            && match ret.max_token_bound { Some(actual) => actual.0 == bound.0, None => false }
            && matches!(ret.alias_verdict, NodeTagVerdict::Alias)
            && matches!(ret.threshold_verdict, NodeTagVerdict::Alias),
)]
const fn bounded_alias(
    tag: WireTag,
    bound: TokenCount,
) -> NodeTagDescription
{
    row(
        tag,
        ChildArity::Fixed(0),
        Some(bound),
        NodeTagVerdict::Alias,
        NodeTagVerdict::Alias,
    )
}

/// The complete node-tag vocabulary and its storage-boundary analysis.
///
/// This table is documentation and a const protocol input for the storage
/// tier; it alters no artifact byte. Its arities are pinned against the arena's
/// own child relation, and its rows are pinned against the encoder's wire
/// images by the round-trip suites, so a row that drifts from the code is a
/// test failure rather than a comment that quietly went stale.
///
/// # Specification
/// - requires: the consumer interprets rows by their tag and keeps the two
///   verdict criteria distinct.
/// - ensures: lists each native former exactly once in tag order with its child
///   arity, token contribution and storage classifications.
/// - panics: none.
/// - executable: none — this catalogue has no runtime invocation; its const
///   constructors enforce local fields and the witnesses compare the complete
///   protocol table.
///
/// # Adequacy
/// - hypothesis: L2 compares the native rows with independently constructed
///   arena formers through their child relation. L3 observes the complete tag
///   vocabulary, the reserved sharing boundary, one-token contributions,
///   finite/unbounded classifications and the base-atom split. These
///   distinguish tag reuse, wrong arity and collapsed classification criteria;
///   arbitrary extension vocabularies are outside this fixed catalogue.
/// - witness: `tags::tests::the_tag_table_matches_the_wire_arities`
/// - witness: `tags::tests::the_frozen_block_keeps_its_order_around_the_retired_tags`
/// - witness: `tags::tests::the_reserved_sharing_block_sits_above_the_frozen_block`
/// - witness: `tags::tests::every_row_states_one_token_and_agrees_with_its_verdicts`
/// - witness: `tags::tests::the_base_atom_row_is_the_one_verdict_split`
pub const NODE_TAG_TABLE: [NodeTagDescription; 74] = [
    row(
        NODE_VT_BASE,
        ChildArity::Fixed(0),
        Some(TokenCount(2)),
        NodeTagVerdict::Boundary,
        NodeTagVerdict::Alias,
    ),
    unbounded(NODE_VT_UNIVERSE, ChildArity::Fixed(0)),
    unbounded(NODE_VT_PRODUCT, ChildArity::Counted(0)),
    unbounded(NODE_VT_SUM, ChildArity::Counted(0)),
    unbounded(NODE_VT_THUNK, ChildArity::Fixed(1)),
    unbounded(NODE_VT_LIFT, ChildArity::Fixed(1)),
    unbounded(NODE_CT_RETURNER, ChildArity::Fixed(1)),
    unbounded(NODE_CT_ARROW, ChildArity::Fixed(2)),
    bounded_alias(NODE_V_VARIABLE, TokenCount(2)),
    bounded_alias(NODE_V_CONSTANT, TokenCount(2)),
    unbounded(NODE_V_LITERAL, ChildArity::Fixed(0)),
    unbounded(NODE_V_TUPLE, ChildArity::Counted(0)),
    unbounded(NODE_V_INJECTION, ChildArity::Fixed(1)),
    unbounded(NODE_V_THUNK, ChildArity::Fixed(1)),
    unbounded(NODE_V_LIFT, ChildArity::Fixed(1)),
    unbounded(NODE_C_LAMBDA, ChildArity::Fixed(1)),
    unbounded(NODE_C_APPLICATION, ChildArity::Fixed(2)),
    unbounded(NODE_C_RETURN, ChildArity::Fixed(1)),
    unbounded(NODE_C_BIND, ChildArity::Fixed(2)),
    unbounded(NODE_C_FORCE, ChildArity::Fixed(1)),
    unbounded(NODE_C_CASE, ChildArity::Counted(1)),
    bounded_alias(NODE_VT_ABSTRACT, TokenCount(2)),
    unbounded(NODE_CT_PI, ChildArity::Fixed(2)),
    unbounded(NODE_VT_ELEMENT, ChildArity::Fixed(1)),
    unbounded(NODE_VT_COMPUTATION_UNIVERSE, ChildArity::Fixed(0)),
    unbounded(NODE_CT_ELEMENT, ChildArity::Fixed(1)),
    unbounded(NODE_V_QUOTE, ChildArity::Fixed(1)),
    unbounded(NODE_V_QUOTE_COMPUTATION, ChildArity::Fixed(1)),
    unbounded(NODE_VT_STATIC_PI, ChildArity::Fixed(2)),
    unbounded(NODE_V_STATIC_APPLICATION, ChildArity::Fixed(2)),
    unbounded(NODE_VT_PATH_UNIVERSE, ChildArity::Fixed(2)),
    unbounded(NODE_V_PATH_REFL, ChildArity::Fixed(1)),
    unbounded(NODE_V_PATH_EQUIV, ChildArity::Fixed(3)),
    unbounded(NODE_V_PATH_PRODUCT, ChildArity::Fixed(2)),
    unbounded(NODE_C_TRANSPORT, ChildArity::Fixed(2)),
    unbounded(NODE_VT_PATH, ChildArity::Fixed(3)),
    unbounded(NODE_V_HERE, ChildArity::Fixed(1)),
    unbounded(NODE_C_PATH_TRANSPORT, ChildArity::Fixed(3)),
    unbounded(NODE_V_HIGHER, ChildArity::Counted(0)),
    unbounded(NODE_V_RETURNED, ChildArity::Fixed(1)),
    unbounded(NODE_C_TELESCOPE_TRANSPORT, ChildArity::Fixed(5)),
    unbounded(NODE_V_HIGHER_EVALUATION, ChildArity::Counted(0)),
    unbounded(NODE_C_RELATED_APPLICATION, ChildArity::Fixed(5)),
    unbounded(NODE_V_QUANTIFIED_EVALUATION, ChildArity::Counted(0)),
    unbounded(NODE_VT_FLOW_UNIVERSE, ChildArity::Fixed(2)),
    unbounded(NODE_V_SESSION_FLOW, ChildArity::Fixed(2)),
    unbounded(NODE_VT_FLOW, ChildArity::Fixed(3)),
    unbounded(NODE_V_STAY, ChildArity::Fixed(1)),
    unbounded(NODE_V_FORWARD_FLOW, ChildArity::Counted(2)),
    unbounded(NODE_V_FUNCTION_FLOW, ChildArity::Fixed(3)),
    unbounded(NODE_V_THEN, ChildArity::Fixed(2)),
    unbounded(NODE_C_RIDE, ChildArity::Fixed(3)),
    unbounded(NODE_VT_LIST, ChildArity::Fixed(1)),
    bounded_alias(NODE_V_LIST_NIL, TokenCount(1)),
    unbounded(NODE_VT_SESSION, ChildArity::Fixed(1)),
    unbounded(NODE_V_SESSION_PATH, ChildArity::Fixed(2)),
    unbounded(NODE_V_LIST_CONS, ChildArity::Fixed(2)),
    unbounded(NODE_C_LIST_FOLD, ChildArity::Fixed(5)),
    unbounded(NODE_VT_DATA, ChildArity::Counted(0)),
    unbounded(NODE_VT_RECORD, ChildArity::Counted(0)),
    unbounded(NODE_V_CONSTRUCTOR, ChildArity::Counted(1)),
    unbounded(NODE_V_RECORD, ChildArity::Counted(0)),
    unbounded(NODE_C_DATA_CASE, ChildArity::Counted(2)),
    unbounded(NODE_C_RECORD_PROJECTION, ChildArity::Fixed(1)),
    unbounded(NODE_C_FIXPOINT, ChildArity::Fixed(1)),
    unbounded(NODE_C_TUPLE_PROJECTION, ChildArity::Fixed(1)),
    unbounded(NODE_CT_WITH, ChildArity::Fixed(2)),
    unbounded(NODE_C_WITH, ChildArity::Fixed(2)),
    unbounded(NODE_C_PROJECT, ChildArity::Fixed(1)),
    unbounded(NODE_C_TELESCOPE_RIDE, ChildArity::Fixed(5)),
    unbounded(NODE_V_FLOW_PRODUCT, ChildArity::Fixed(2)),
    unbounded(NODE_VT_SIGMA, ChildArity::Fixed(2)),
    unbounded(NODE_C_SIGMA_SPLIT, ChildArity::Fixed(3)),
    unbounded(NODE_V_UNIVALENCE, ChildArity::Fixed(1)),
];

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;

    use anodized::spec;

    use super::NODE_TAG_TABLE;
    use super::NodeTagVerdict;
    use crate::arena::AnyNode;
    use crate::arena::TermArena;
    use crate::base::BaseType;
    use crate::base::IntegerLiteral;
    use crate::base::Literal;
    use crate::base::Magnitude;
    use crate::base::Sign;
    use crate::term::ConstantIndex;
    use crate::term::DeBruijnIndex;
    use crate::term::Summand;
    use crate::types::GroundSort;
    use crate::wire::WireTag;

    /// One node of every former, in the tag table's order, in a fresh arena.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns a fresh arena holding one node of every former, and
    ///   the nodes' cross-family references in the tag table's order.
    /// - provides: the fixture the table's arity comparison reads; every former
    ///   being present is what makes a missing or wrong arity a test failure
    ///   rather than an untested row.
    /// - panics: panics only through the arena constructors it calls, none of
    ///   which is fallible.
    ///
    /// # Adequacy
    /// - hypothesis: L2 compares all 32 frozen rows with independently
    ///   constructed arena formers through their child relation. L3 observes
    ///   the complete tag interval, the reserved sharing boundary, one-token
    ///   contributions, finite/unbounded classifications and the base-atom
    ///   split. These distinguish tag reuse, wrong arity and collapsed
    ///   classification criteria; arbitrary extension vocabularies are outside
    ///   this fixed catalogue.
    /// - witness: `tags::tests::the_tag_table_matches_the_wire_arities`
    #[spec(
        ensures: |ret| ret.1.len() == NODE_TAG_TABLE.len()
                && ret.1.iter().zip(NODE_TAG_TABLE.iter()).all(|(&node, row)| match node {
                    AnyNode::Value(id) => match ret.0.value(id) {
                        Some(&crate::Value::Constructor { .. }) => row.tag == super::NODE_V_CONSTRUCTOR,
                        Some(&crate::Value::Record(_)) => row.tag == super::NODE_V_RECORD,
                        Some(&crate::Value::Variable(_)) => row.tag == super::NODE_V_VARIABLE,
                        Some(&crate::Value::Constant(_)) => row.tag == super::NODE_V_CONSTANT,
                        Some(&crate::Value::Literal(_)) => row.tag == super::NODE_V_LITERAL,
                        Some(&crate::Value::Tuple(_)) => row.tag == super::NODE_V_TUPLE,
                        Some(&crate::Value::Injection(_, _)) => row.tag == super::NODE_V_INJECTION,
                        Some(&crate::Value::Thunk(_)) => row.tag == super::NODE_V_THUNK,
                        Some(&crate::Value::Lift { .. }) => row.tag == super::NODE_V_LIFT,
                        Some(&crate::Value::Quote(_)) => row.tag == super::NODE_V_QUOTE,
                        Some(&crate::Value::QuoteComputation(_)) => row.tag == super::NODE_V_QUOTE_COMPUTATION,
                        Some(&crate::Value::StaticApplication(_, _)) => row.tag == super::NODE_V_STATIC_APPLICATION,
                        Some(&crate::Value::PathRefl(_)) => row.tag == super::NODE_V_PATH_REFL,
                        Some(&crate::Value::PathProduct(_, _)) => row.tag == super::NODE_V_PATH_PRODUCT,
                        Some(&crate::Value::PathEquiv { .. }) => row.tag == super::NODE_V_PATH_EQUIV,
                        Some(&crate::Value::Univalence { .. }) => row.tag == super::NODE_V_UNIVALENCE,
                        Some(&crate::Value::Here { .. }) => row.tag == super::NODE_V_HERE,
                        Some(&crate::Value::Returned(_)) => row.tag == super::NODE_V_RETURNED,
                        Some(&crate::Value::Higher { .. }) => row.tag == super::NODE_V_HIGHER,
                        Some(&crate::Value::HigherEvaluation { .. }) => row.tag == super::NODE_V_HIGHER_EVALUATION,
                        Some(&crate::Value::QuantifiedEvaluation { .. }) => row.tag == super::NODE_V_QUANTIFIED_EVALUATION,
                        Some(&crate::Value::SessionPath { .. }) => row.tag == super::NODE_V_SESSION_PATH,
                        Some(&crate::Value::SessionFlow { .. }) => row.tag == super::NODE_V_SESSION_FLOW,
                        Some(&crate::Value::Stay { .. }) => row.tag == super::NODE_V_STAY,
                        Some(&crate::Value::ForwardFlow { .. }) => row.tag == super::NODE_V_FORWARD_FLOW,
                        Some(&crate::Value::FunctionFlow { .. }) => row.tag == super::NODE_V_FUNCTION_FLOW,
                        Some(&crate::Value::Then { .. }) => row.tag == super::NODE_V_THEN,
                        Some(&crate::Value::FlowProduct(..)) => row.tag == super::NODE_V_FLOW_PRODUCT,
                        Some(&crate::Value::ListNil) => row.tag == super::NODE_V_LIST_NIL,
                        Some(&crate::Value::ListCons(..)) => row.tag == super::NODE_V_LIST_CONS,
                        None => false,
                    },
                    AnyNode::Computation(id) => match ret.0.computation(id) {
                        Some(&crate::Computation::DataCase { .. }) => row.tag == super::NODE_C_DATA_CASE,
                        Some(&crate::Computation::RecordProjection(..)) => row.tag == super::NODE_C_RECORD_PROJECTION,
                        Some(&crate::Computation::TupleProjection(..)) => row.tag == super::NODE_C_TUPLE_PROJECTION,
                        Some(&crate::Computation::Lambda(_)) => row.tag == super::NODE_C_LAMBDA,
                        Some(&crate::Computation::Fixpoint { .. }) => row.tag == super::NODE_C_FIXPOINT,
                        Some(&crate::Computation::Application(_, _)) => row.tag == super::NODE_C_APPLICATION,
                        Some(&crate::Computation::Return(_)) => row.tag == super::NODE_C_RETURN,
                        Some(&crate::Computation::Bind(_, _)) => row.tag == super::NODE_C_BIND,
                        Some(&crate::Computation::Force(_)) => row.tag == super::NODE_C_FORCE,
                        Some(&crate::Computation::Case { .. }) => row.tag == super::NODE_C_CASE,
                        Some(&crate::Computation::SigmaSplit { .. }) => row.tag == super::NODE_C_SIGMA_SPLIT,
                        Some(&crate::Computation::Transport(_, _)) => row.tag == super::NODE_C_TRANSPORT,
                        Some(&crate::Computation::PathTransport { .. }) => row.tag == super::NODE_C_PATH_TRANSPORT,
                        Some(&crate::Computation::TelescopeTransport { .. }) => row.tag == super::NODE_C_TELESCOPE_TRANSPORT,
                        Some(&crate::Computation::Ride { .. }) => row.tag == super::NODE_C_RIDE,
                        Some(&crate::Computation::TelescopeRide { .. }) => row.tag == super::NODE_C_TELESCOPE_RIDE,
                        Some(&crate::Computation::RelatedApplication { .. }) => row.tag == super::NODE_C_RELATED_APPLICATION,
                        Some(&crate::Computation::ListFold { .. }) => row.tag == super::NODE_C_LIST_FOLD,
                        Some(&crate::Computation::With(_, _)) => row.tag == super::NODE_C_WITH,
                        Some(&crate::Computation::Project(_, _)) => row.tag == super::NODE_C_PROJECT,
                        None => false,
                    },
                    AnyNode::ValueType(id) => match ret.0.value_type(id) {
                        Some(&crate::ValueType::Data { .. }) => row.tag == super::NODE_VT_DATA,
                        Some(&crate::ValueType::Record(_)) => row.tag == super::NODE_VT_RECORD,
                        Some(&crate::ValueType::Base(_)) => row.tag == super::NODE_VT_BASE,
                        Some(&crate::ValueType::Universe { sort: GroundSort::Value, .. }) => row.tag == super::NODE_VT_UNIVERSE,
                        Some(&crate::ValueType::Universe { sort: GroundSort::Computation, .. }) => row.tag == super::NODE_VT_COMPUTATION_UNIVERSE,
                        Some(&crate::ValueType::Product(_)) => row.tag == super::NODE_VT_PRODUCT,
                        Some(&crate::ValueType::Sigma { .. }) => row.tag == super::NODE_VT_SIGMA,
                        Some(&crate::ValueType::Sum(_)) => row.tag == super::NODE_VT_SUM,
                        Some(&crate::ValueType::Thunk(_)) => row.tag == super::NODE_VT_THUNK,
                        Some(&crate::ValueType::Lift { .. }) => row.tag == super::NODE_VT_LIFT,
                        Some(&crate::ValueType::Abstract(_)) => row.tag == super::NODE_VT_ABSTRACT,
                        Some(&crate::ValueType::StaticPi { .. }) => row.tag == super::NODE_VT_STATIC_PI,
                        Some(&crate::ValueType::Element { .. }) => row.tag == super::NODE_VT_ELEMENT,
                        Some(&crate::ValueType::PathUniverse(_, _)) => row.tag == super::NODE_VT_PATH_UNIVERSE,
                        Some(&crate::ValueType::FlowUniverse(_, _)) => row.tag == super::NODE_VT_FLOW_UNIVERSE,
                        Some(&crate::ValueType::Path { .. }) => row.tag == super::NODE_VT_PATH,
                        Some(&crate::ValueType::Flow { .. }) => row.tag == super::NODE_VT_FLOW,
                        Some(&crate::ValueType::List(_)) => row.tag == super::NODE_VT_LIST,
                        Some(&crate::ValueType::Session { .. }) => row.tag == super::NODE_VT_SESSION,
                        Some(&crate::ValueType::Staged { .. }) | None => false,
                    },
                    AnyNode::CompType(id) => match ret.0.comp_type(id) {
                        Some(&crate::CompType::Returner(_)) => row.tag == super::NODE_CT_RETURNER,
                        Some(&crate::CompType::Arrow { .. }) => row.tag == super::NODE_CT_ARROW,
                        Some(&crate::CompType::Pi { .. }) => row.tag == super::NODE_CT_PI,
                        Some(&crate::CompType::Element { .. }) => row.tag == super::NODE_CT_ELEMENT,
                        Some(&crate::CompType::With(_, _)) => row.tag == super::NODE_CT_WITH,
                        None => false,
                    },
                })
    )]
    fn one_node_per_former() -> (TermArena, Vec<AnyNode>)
    {
        let mut arena = TermArena::new();
        let level = gandr_kernel_strata::Level::zero();
        let base = arena.value_type_base(BaseType::Integer);
        let unit_type = arena.value_type_unit();
        let universe = arena.value_type_universe(GroundSort::Value, level.clone());
        let product = arena.value_type_product(&[base, unit_type, base]);
        let sum = arena.value_type_sum(&[base, unit_type]);
        let returner = arena.comp_type_returner(unit_type);
        let thunk_type = arena.value_type_thunk(returner);
        let lift_type = arena.value_type_lift(unit_type, level.clone());
        let arrow = arena.comp_type_arrow(unit_type, returner);
        let variable = arena.value_variable(DeBruijnIndex::from(0));
        let constant = arena.value_constant(ConstantIndex::from(0));
        let unit = arena.value_unit();
        let literal = arena.value_literal(Literal::Integer(IntegerLiteral::new(
            Sign::NonNegative,
            Magnitude::zero(),
        )));
        let pair = arena.value_tuple(&[unit, unit, literal]);
        let injection = arena.value_injection(Summand::from(2_usize), unit);
        let ret = arena.computation_return(unit);
        let thunk = arena.value_thunk(ret);
        let lift = arena.value_lift(level.clone(), unit);
        let lambda = arena.computation_lambda(ret);
        let application = arena.computation_application(ret, unit);
        let bind = arena.computation_bind(ret, ret);
        let force = arena.computation_force(unit);
        let case = arena.computation_case(unit, &[ret, lambda, ret]);
        let atom = arena.value_type_abstract(ConstantIndex::from(0));
        let pi = arena.comp_type_pi(unit_type, returner);
        let element = arena.value_type_element(unit, level.clone());
        let computation_universe =
            arena.value_type_universe(GroundSort::Computation, level.clone());
        let comp_element = arena.comp_type_element(unit, level);
        let quote = arena.value_quote(unit_type);
        let quote_computation = arena.value_quote_computation(returner);
        let static_pi = arena.value_type_static_pi(universe, universe);
        let static_application = arena.value_static_application(constant, quote);
        let path_type = arena.value_type_path_universe(quote, quote);
        let refl = arena.value_path_refl(quote);
        let map = arena.value_thunk(lambda);
        let equiv = arena.value_path_equiv(path_type, map, map, alloc::sync::Arc::default());
        let product_path = arena.value_path_product(refl, refl);
        let transport = arena.computation_transport(product_path, pair);
        let element_path = arena.value_type_path(unit_type, unit, unit);
        let here = arena.value_here(unit);
        let element_transport = arena.computation_path_transport(unit_type, here, unit);
        let higher = arena.value_higher(
            alloc::sync::Arc::new(crate::HigherProgram {
                depth: crate::HigherDepth(1),
                root: crate::LayerPosition(0),
                layers: alloc::vec![
                    crate::HigherLayer::Guard {
                        tail: crate::LayerPosition(1),
                    },
                    crate::HigherLayer::Redirect(crate::LayerPosition(0)),
                ],
            }),
            alloc::boxed::Box::from([unit]),
        );
        let returned = arena.value_returned(ret);
        let telescope = arena.comp_type_pi(unit_type, pi);
        let telescope_transport =
            arena.computation_telescope_transport(telescope, here, unit, returned, literal);
        let evaluation = arena.value_higher_evaluation(
            alloc::sync::Arc::from([crate::EvaluationDialogues::default()]),
            alloc::boxed::Box::from([crate::EvaluationComponent {
                left: unit,
                right: literal,
                evidence: here,
            }]),
        );
        let related = arena.computation_related_application(here, (unit, literal), here, ret);
        let quantified = arena.value_quantified_evaluation(
            alloc::sync::Arc::from([
                crate::QuantifiedStep::Apply {
                    fibre: crate::DeBruijnIndex::from(0_u32),
                    dialogues: crate::EvaluationDialogues::default(),
                },
                crate::QuantifiedStep::Return(crate::EvaluationDialogues::default()),
            ]),
            alloc::boxed::Box::from([thunk, thunk, unit, literal, here]),
        );
        let session = arena.value_type_session(
            alloc::sync::Arc::new(crate::session::Graph {
                nodes: alloc::vec![crate::session::Node::End],
                root: crate::session::State(0),
            }),
            unit_type,
        );
        let session_path = arena.value_session_path(path_type, alloc::sync::Arc::default(), unit);
        let flow_type = arena.value_type_flow_universe(quote, quote);
        let session_flow = arena.value_session_flow(flow_type, alloc::sync::Arc::default(), unit);
        let element_flow = arena.value_type_flow(unit_type, unit, literal);
        let stay = arena.value_stay(unit);
        let forward_flow = arena.value_forward_flow(
            flow_type,
            map,
            alloc::boxed::Box::from([unit, literal]),
            alloc::sync::Arc::from([crate::Dialogue::new(), crate::Dialogue::new()]),
        );
        let function_flow = arena.value_function_flow(flow_type, stay, forward_flow);
        let then = arena.value_then(stay, forward_flow, crate::Seam::Sequence);
        let ride = arena.computation_ride(unit_type, stay, literal);
        let datatype = arena.value_type_data(ConstantIndex::from(0), alloc::vec![quote]);
        let label = crate::FieldLabel::from(alloc::string::String::from("field"));
        let record_type = arena.value_type_record(alloc::collections::BTreeMap::from([(
            label.clone(),
            unit_type,
        )]));
        let constructor =
            arena.value_constructor(datatype, crate::ConstructorTag::from(0), alloc::vec![unit]);
        let record =
            arena.value_record(alloc::collections::BTreeMap::from([(label.clone(), unit)]));
        let data_case = arena.computation_data_case(constructor, returner, alloc::vec![ret]);
        let projection = arena.computation_record_projection(record, label);
        let fixpoint = arena.computation_fixpoint(lambda, crate::FixpointEvidence::Partial);
        let tuple_projection =
            arena.computation_tuple_projection(pair, crate::Component::from(2_usize));
        let nil = arena.value_list_nil();
        let cons = arena.value_list_cons(unit, nil);
        let fold = arena.computation_list_fold(unit_type, unit_type, cons, ret, ret);
        let lazy_type = arena.comp_type_with(returner, arrow);
        let lazy_pair = arena.computation_with(ret, lambda);
        let lazy_projection = arena.computation_project(crate::Side::Right, lazy_pair);
        let telescope_ride =
            arena.computation_telescope_ride(telescope, stay, unit, returned, literal);
        let flow_product = arena.value_flow_product(stay, forward_flow);
        let sigma = arena.value_type_sigma(base, element_path);
        let sigma_split = arena.computation_sigma_split(pair, returner, bind);
        let univalence = arena.value_univalence(pair);
        let nodes = alloc::vec![
            AnyNode::ValueType(base),
            AnyNode::ValueType(universe),
            AnyNode::ValueType(product),
            AnyNode::ValueType(sum),
            AnyNode::ValueType(thunk_type),
            AnyNode::ValueType(lift_type),
            AnyNode::CompType(returner),
            AnyNode::CompType(arrow),
            AnyNode::Value(variable),
            AnyNode::Value(constant),
            AnyNode::Value(literal),
            AnyNode::Value(pair),
            AnyNode::Value(injection),
            AnyNode::Value(thunk),
            AnyNode::Value(lift),
            AnyNode::Computation(lambda),
            AnyNode::Computation(application),
            AnyNode::Computation(ret),
            AnyNode::Computation(bind),
            AnyNode::Computation(force),
            AnyNode::Computation(case),
            AnyNode::ValueType(atom),
            AnyNode::CompType(pi),
            AnyNode::ValueType(element),
            AnyNode::ValueType(computation_universe),
            AnyNode::CompType(comp_element),
            AnyNode::Value(quote),
            AnyNode::Value(quote_computation),
            AnyNode::ValueType(static_pi),
            AnyNode::Value(static_application),
            AnyNode::ValueType(path_type),
            AnyNode::Value(refl),
            AnyNode::Value(equiv),
            AnyNode::Value(product_path),
            AnyNode::Computation(transport),
            AnyNode::ValueType(element_path),
            AnyNode::Value(here),
            AnyNode::Computation(element_transport),
            AnyNode::Value(higher),
            AnyNode::Value(returned),
            AnyNode::Computation(telescope_transport),
            AnyNode::Value(evaluation),
            AnyNode::Computation(related),
            AnyNode::Value(quantified),
            AnyNode::ValueType(flow_type),
            AnyNode::Value(session_flow),
            AnyNode::ValueType(element_flow),
            AnyNode::Value(stay),
            AnyNode::Value(forward_flow),
            AnyNode::Value(function_flow),
            AnyNode::Value(then),
            AnyNode::Computation(ride),
            AnyNode::ValueType(arena.value_type_list(unit_type)),
            AnyNode::Value(nil),
            AnyNode::ValueType(session),
            AnyNode::Value(session_path),
            AnyNode::Value(cons),
            AnyNode::Computation(fold),
            AnyNode::ValueType(datatype),
            AnyNode::ValueType(record_type),
            AnyNode::Value(constructor),
            AnyNode::Value(record),
            AnyNode::Computation(data_case),
            AnyNode::Computation(projection),
            AnyNode::Computation(fixpoint),
            AnyNode::Computation(tuple_projection),
            AnyNode::CompType(lazy_type),
            AnyNode::Computation(lazy_pair),
            AnyNode::Computation(lazy_projection),
            AnyNode::Computation(telescope_ride),
            AnyNode::Value(flow_product),
            AnyNode::ValueType(sigma),
            AnyNode::Computation(sigma_split),
            AnyNode::Value(univalence),
        ];
        (arena, nodes)
    }

    #[test]
    fn the_tag_table_matches_the_wire_arities()
    {
        let (arena, nodes) = one_node_per_former();
        assert_eq!(
            NODE_TAG_TABLE.len(),
            nodes.len(),
            "the table has one row per former"
        );
        for (row, node) in NODE_TAG_TABLE.iter().zip(nodes.iter()) {
            let children = arena.children_of(*node);
            let inline_count = match *node {
                AnyNode::Value(id) => {
                    arena
                        .value(id)
                        .map_or(0, |matched_native_node| match *matched_native_node {
                            crate::Value::Constructor { ref fields, .. } => fields.len(),
                            crate::Value::Record(ref fields) => fields.len(),
                            crate::Value::Tuple(ref components) => components.len(),
                            crate::Value::Higher { ref evidence, .. } => evidence.len(),
                            crate::Value::HigherEvaluation { ref components, .. } => {
                                components.len().saturating_mul(3)
                            },
                            crate::Value::QuantifiedEvaluation { ref children, .. } => {
                                children.len()
                            },
                            crate::Value::ForwardFlow { ref outputs, .. } => outputs.len(),
                            crate::Value::SessionPath { .. }
                            | crate::Value::SessionFlow { .. }
                            | crate::Value::Stay { .. }
                            | crate::Value::FunctionFlow { .. }
                            | crate::Value::Then { .. }
                            | crate::Value::FlowProduct(..)
                            | crate::Value::PathRefl(_)
                            | crate::Value::PathProduct(..)
                            | crate::Value::PathEquiv { .. }
                            | crate::Value::Univalence { .. }
                            | crate::Value::Here { .. }
                            | crate::Value::Returned(_)
                            | crate::Value::Variable(_)
                            | crate::Value::Constant(_)
                            | crate::Value::Literal(_)
                            | crate::Value::Injection(..)
                            | crate::Value::ListNil
                            | crate::Value::ListCons(..)
                            | crate::Value::Thunk(_)
                            | crate::Value::Lift { .. }
                            | crate::Value::Quote(_)
                            | crate::Value::QuoteComputation(_)
                            | crate::Value::StaticApplication(..) => 0,
                        })
                },
                AnyNode::ValueType(id) => {
                    arena
                        .value_type(id)
                        .map_or(0, |matched_native_node| match *matched_native_node {
                            crate::ValueType::Data { ref arguments, .. } => arguments.len(),
                            crate::ValueType::Record(ref fields) => fields.len(),
                            crate::ValueType::Product(ref parts)
                            | crate::ValueType::Sum(ref parts) => parts.len(),
                            crate::ValueType::Session { .. }
                            | crate::ValueType::PathUniverse(..)
                            | crate::ValueType::FlowUniverse(..)
                            | crate::ValueType::Path { .. }
                            | crate::ValueType::Flow { .. }
                            | crate::ValueType::Base(_)
                            | crate::ValueType::Sigma { .. }
                            | crate::ValueType::List(_)
                            | crate::ValueType::Thunk(_)
                            | crate::ValueType::Universe { .. }
                            | crate::ValueType::Lift { .. }
                            | crate::ValueType::Element { .. }
                            | crate::ValueType::Abstract(_)
                            | crate::ValueType::StaticPi { .. }
                            | crate::ValueType::Staged { .. } => 0,
                        })
                },
                AnyNode::Computation(id) => match arena.computation(id) {
                    Some(&crate::Computation::DataCase { ref branches, .. }) => branches.len(),
                    Some(&crate::Computation::Case { ref branches, .. }) => branches.len(),
                    _ => 0,
                },
                AnyNode::CompType(_) => 0,
            };
            let expected = match row.child_arity {
                super::ChildArity::Fixed(count) => usize::from(count),
                super::ChildArity::Counted(prefix) => usize::from(prefix) + inline_count,
            };
            assert_eq!(expected, children.len(), "tag {} child arity", row.tag);
        }
    }

    #[test]
    fn assigned_wire_tags_are_unique_and_leave_reserved_bytes_unassigned()
    {
        let mut assigned = [false; 256];
        let reserved = u8::from(super::SHARING_BLOCK_FIRST) ..= u8::from(super::SHARING_BLOCK_LAST);
        for word in [
            crate::session::SEND,
            crate::session::RECEIVE,
            crate::session::SELECT,
            crate::session::OFFER,
            crate::session::END,
            crate::session::MU,
            crate::session::VAR,
        ] {
            let tag = usize::try_from(word.0).expect("session opcodes fit a byte");
            assert!(
                !core::mem::replace(&mut assigned[tag], true),
                "session opcodes are distinct"
            );
            assert!(
                (0x53 ..= 0x59).contains(&tag),
                "List and flow bytes remain untouched"
            );
        }
        for row in &NODE_TAG_TABLE {
            let tag = u8::from(row.tag);
            assert!(
                !core::mem::replace(&mut assigned[usize::from(tag)], true),
                "one wire byte cannot identify two formers"
            );
            assert!(
                !reserved.contains(&tag),
                "an assigned former cannot consume a reserved sharing byte"
            );
            let identity = matches!(tag, 0x30 ..= 0x35 | 0x38 ..= 0x3A | 0x48 ..= 0x4F);
            assert!(
                identity || !(0x30_u8 .. 0x50).contains(&tag),
                "only the assigned identity and flow bytes leave the identity, funext and flow ranges"
            );
        }
        for unassigned in (0x36_u8 ..= 0x37).chain(0x3B ..= 0x47) {
            assert!(
                !assigned[usize::from(unassigned)],
                "the unassigned identity growth names no former: {unassigned:#04x}"
            );
        }
        for assigned_flow in 0x48_u8 ..= 0x4F {
            assert!(
                assigned[usize::from(assigned_flow)],
                "the flow reservation is spent: {assigned_flow:#04x}"
            );
        }
        for sigma in [super::NODE_VT_SIGMA, super::NODE_C_SIGMA_SPLIT] {
            assert!(
                assigned[usize::from(u8::from(sigma))],
                "the dependent pair holds its bytes: {sigma}"
            );
        }
        assert!(
            assigned[usize::from(u8::from(super::NODE_V_UNIVALENCE))],
            "univalence holds its byte"
        );
        for unassigned in core::iter::once(0x6C_u8).chain(0x6E_u8 ..= u8::MAX) {
            assert!(
                !assigned[usize::from(unassigned)],
                "every byte above the dependent split but univalence's is unassigned: {unassigned:#04x}"
            );
        }
    }

    #[test]
    fn the_frozen_block_keeps_its_order_around_the_retired_tags()
    {
        let frozen: Vec<_> = NODE_TAG_TABLE
            .iter()
            .take(30)
            .map(|row| u8::from(row.tag))
            .collect();
        assert_eq!(
            frozen,
            (0_u8 ..= 0x1f)
                .filter(|tag| !matches!(tag, 0x01 | 0x0B))
                .collect::<Vec<_>>(),
            "the unit type and unit value tags are retired; no other frozen byte moved"
        );
    }

    #[test]
    fn the_reserved_sharing_block_sits_above_the_frozen_block()
    {
        assert_eq!(super::SHARING_BLOCK_FIRST, WireTag::from(0x20));
        assert_eq!(super::SHARING_BLOCK_LAST, WireTag::from(0x27));
        let expected: Vec<_> = (0_u8 ..= 0x1f)
            .filter(|tag| !matches!(tag, 0x01 | 0x0B))
            .chain(0x2a ..= 0x2e)
            .chain([0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x38, 0x39, 0x3A])
            .chain(0x48 ..= 0x4F)
            .chain([0x50, 0x51, 0x52, 0x5a, 0x5b, 0x5c])
            .chain(0x5d ..= 0x6b)
            .chain([0x6D])
            .collect();
        let actual: Vec<_> = NODE_TAG_TABLE.iter().map(|row| u8::from(row.tag)).collect();
        assert_eq!(actual, expected);
        for retired in [0x01_u8, 0x0B, 0x28, 0x29] {
            assert!(
                NODE_TAG_TABLE
                    .iter()
                    .all(|row| u8::from(row.tag) != retired),
                "the retired tag {retired:#04x} names no former"
            );
        }
        for counted in [
            super::NODE_VT_PRODUCT,
            super::NODE_VT_SUM,
            super::NODE_V_TUPLE,
        ] {
            let row = NODE_TAG_TABLE
                .iter()
                .find(|row| row.tag == counted)
                .expect("the n-ary formers have wire tags");
            assert_eq!(row.child_arity, super::ChildArity::Counted(0));
        }
    }

    #[test]
    fn every_row_states_one_token_and_agrees_with_its_verdicts()
    {
        for row in &NODE_TAG_TABLE {
            assert_eq!(
                1_u8,
                u8::from(row.token_contribution),
                "tag {} contributes its own token",
                row.tag
            );
            if let Some(bound) = row.max_token_bound {
                assert!(
                    u8::from(bound) >= u8::from(row.token_contribution),
                    "a finite bound covers the tag's own token at {}",
                    row.tag
                );
                assert_eq!(
                    NodeTagVerdict::Alias,
                    row.threshold_verdict,
                    "a finitely bounded payload is a threshold alias at {}",
                    row.tag
                );
            }
            else {
                assert_eq!(
                    NodeTagVerdict::Boundary,
                    row.alias_verdict,
                    "an unbounded payload is a boundary at {}",
                    row.tag
                );
                assert_eq!(
                    NodeTagVerdict::Boundary,
                    row.threshold_verdict,
                    "an unbounded payload is a threshold boundary at {}",
                    row.tag
                );
            }
        }
    }

    #[test]
    fn the_base_atom_row_is_the_one_verdict_split()
    {
        let base = NODE_TAG_TABLE
            .first()
            .expect("the table opens with the base atom");
        assert_eq!(
            NodeTagVerdict::Boundary,
            base.alias_verdict,
            "a multi-constructor payload is not a conservative alias"
        );
        assert_eq!(
            NodeTagVerdict::Alias,
            base.threshold_verdict,
            "its bounded duplication makes it a threshold alias"
        );
    }
}
