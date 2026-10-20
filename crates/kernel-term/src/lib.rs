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
//! Canonical bytes are a function of the declarations' abstract content, never
//! of how they were built or decoded, so two differently shared equal inputs
//! encode identically.
//!
//! # Sharing and compression
//!
//! Arena allocation does not intern nodes. Encoding does: child-first entry
//! bytes are content keys shared across declaration segments, so separately
//! allocated equal subgraphs become one wire entry. Decoding preserves the
//! sharing of the accepted canonical table in an owned, flat arena. Equal ids
//! identify one node; distinct ids do not establish semantic inequality, and
//! id equality is a positive-only fast path deciding reflexive pairs alone.
//! This format interning is neither an evaluation memo nor a proof of typing
//! or admission, and no content-keyed memo of *values* belongs anywhere the
//! kernel can reach: a pass that creates sharing for evaluation is
//! elaborator-side.
//!
//! Compression is a storage and transport concern. The canonical bytes are
//! the bytes, and no codec sits inside a reader whose rejection vocabulary has
//! to stay clean. The bytes are declaration-segmented and self-delimiting.
//!
//! # Presentations
//!
//! A data declaration may carry rules over its own constructors that present
//! its type ([`Presentation`]), encoded under its own declaration kind
//! ([`KIND_DATA_PRESENTED`]) so a free declaration's bytes are unchanged. The
//! rules' validation against a constructor table and their rewriting to
//! normal form live beside their representation: they are what a presentation
//! means, and the kernel and the engine must run one strategy to reach one
//! normal form. Neither is a judgement — the kernel's admission decides
//! whether a declaration's rules present its type, and its conversion decides
//! what the normal forms relate.
//!
//! **Choice.** Rule sides in pre-order over constructor tags and pattern
//! variables, so a rule names no arena node and crosses every boundary
//! unchanged. **Alternatives.** Rule sides as arena terms, which would tie a
//! presentation to one arena and widen the node vocabulary. **Reversal.** A
//! rule that must name a value of another type, a literal in a pattern,
//! takes a leaf payload in [`RuleNode`].
//!
//! A type of words carries, beside its rules, the free cells it is minted over
//! ([`FreeCells`]), encoded under a kind of its own ([`KIND_DATA_WORDS`]):
//! the presented fields, then the sort's position and each cell's endpoints as
//! closed rule sides over the sort's table. **Choice.** A kind of its own, as
//! a relating and a lawful definition each took one, so every presented
//! declaration keeps its bytes and an older reader refuses the words rather
//! than misreading them; the format version holds. **Alternatives.** The cell
//! list appended to every presented declaration, which moves every presented
//! artifact's bytes for a count most of them hold at zero. **Reversal.** When
//! most presented declarations carry cells, one kind with an always-written
//! count is the smaller format.
//!
//! # Specification attributes
//!
//! Clause-bearing items carry executable `#[spec(...)]` predicates or a local
//! `executable: none` explanation, with `# Adequacy` linking their evidence.
//! Checks observe decimal normalization, arena prefix frames, declaration
//! lifecycle and metadata, exact wire fields, borrowed cursor ranges, typed
//! refusals and budget precedence. Const predicates compare inner ordinals
//! without adding a second identity vocabulary. A predicate checks its stated
//! projection on an executed call; it does not turn a transported producer
//! claim into admission evidence.
//!
//! Encoding requires live, acyclic reachable graphs and an interner used with
//! the unchanged arena it addresses; enforced predicates reject stale roots.
//! Treating a missing computation or computation type as a unit is not a
//! valid alternative: those families have no unit former, and a fallible
//! recovery API would be a separate design, not a fabricated wire fallback.
//! Arena ids carry neither provenance nor a reuse generation, so a coincident
//! ordinal alone cannot establish origin.
//!
//! Literal byte fixtures independently pin every former, payload and child
//! position. Decoder witnesses vary every tag byte, proper prefixes,
//! reference order and polarity, normalization residues and the arithmetic
//! ceilings. Local normalization is not canonical-wire acceptance: decoding
//! also compares the whole artifact with its re-encoding, and that agreement
//! check is not an independent format oracle. Budget witnesses use explicit
//! expansion and widened arithmetic; the integration diamond model saturates
//! the final tree size, including the exact `u64::MAX` boundary, rather than
//! saturating a power before subtraction.
//!
//! The deep-graph witness (`tests/adversarial_depth.rs`) walks 100,000
//! thunk-over-returner links to unit and drops the sole decoded owner on a
//! 256 KiB stack. An entry count alone cannot prove depth; this is evidence
//! for that shape and stack bound, not all graph shapes or allocation
//! failures. Formatter effects, non-callable data and policy constants, the
//! consuming builder-discard boundary and an opaque test strategy state their
//! unobservable obligations and witnesses at their definitions.
//!
//! The papers the crate draws on are in its `README.md`, § References.

// Module documentation that predates the shape lint: 46 headings outside the
// vocabulary, 17 decision records, 1 issue reference and 7 budgets exceeded.
// Each allow leaves with the rewrite that clears its count.
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    allow(
        module_doc_heading,
        doc_decision_record,
        doc_issue_reference,
        module_doc_budget,
        reason = "module documentation that predates the shape lint"
    )
)]
#![no_std]

extern crate alloc;

mod arena;
mod base;
mod budget;
mod decl;
mod decode;
mod encode;
mod error;
mod identity;
mod presented;
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
pub use crate::decl::AtomInterface;
pub use crate::decl::Declaration;
pub use crate::decl::DeclarationBuilder;
pub use crate::decl::DeclarationContent;
pub use crate::decl::LevelParamCount;
pub use crate::decl::LevelSignature;
pub use crate::decl::MarkedDeclaration;
pub use crate::decl::MintedAtom;
pub use crate::decl::NameSegment;
pub use crate::decl::RelatedEndpoints;
pub use crate::decl::SealExtent;
pub use crate::decl::SealScope;
pub use crate::decl::StructuredName;
pub use crate::decl::interface;
pub use crate::decode::DecodedArtifact;
pub use crate::decode::SegmentLayout;
pub use crate::decode::decode;
pub use crate::encode::encode;
pub use crate::error::DecodeError;
pub use crate::error::MalformedSite;
pub use crate::error::ReservedKind;
pub use crate::error::ReservedSlot;
pub use crate::error::TagSite;
pub use crate::identity::Dialogue;
pub use crate::identity::EndpointDialogues;
pub use crate::identity::EvaluationComponent;
pub use crate::identity::EvaluationDialogues;
pub use crate::identity::HigherDepth;
pub use crate::identity::HigherLayer;
pub use crate::identity::HigherProgram;
pub use crate::identity::LayerPosition;
pub use crate::identity::QuantifiedStep;
pub use crate::identity::endpoint_words;
pub use crate::identity::evaluation_words;
pub use crate::identity::forward_words;
pub use crate::identity::quantified_words;
pub use crate::presented::Apartness;
pub use crate::presented::CellFault;
pub use crate::presented::CellIndex;
pub use crate::presented::ConstructorCount;
pub use crate::presented::Convergence;
pub use crate::presented::Exhausted;
pub use crate::presented::FieldCount;
pub use crate::presented::FreeCell;
pub use crate::presented::FreeCells;
pub use crate::presented::Normalized;
pub use crate::presented::Presentation;
pub use crate::presented::PresentedRule;
pub use crate::presented::RewriteFuel;
pub use crate::presented::RuleFault;
pub use crate::presented::RuleIndex;
pub use crate::presented::RuleNode;
pub use crate::presented::RuleRefusal;
pub use crate::presented::RuleSlot;
pub use crate::presented::RuleTerm;
pub use crate::presented::RuleVariable;
pub use crate::presented::TermReading;
pub use crate::presented::VariableCount;
pub use crate::presented::build_side;
pub use crate::tags::ADMISSION_CHECKED;
pub use crate::tags::ADMISSION_UNCHECKED;
pub use crate::tags::BASE_INTEGER;
pub use crate::tags::BASE_NUMERIC;
pub use crate::tags::BASE_STRING;
pub use crate::tags::ChildArity;
pub use crate::tags::FIXPOINT_PARTIAL;
pub use crate::tags::FIXPOINT_STAGED;
pub use crate::tags::FIXPOINT_STRUCTURAL_DESCENT;
pub use crate::tags::FORMAT_VERSION;
pub use crate::tags::HIGHER_GUARD;
pub use crate::tags::HIGHER_REDIRECT;
pub use crate::tags::KIND_ABSTRACT_INTERFACED;
pub use crate::tags::KIND_ABSTRACT_TYPE;
pub use crate::tags::KIND_AXIOM;
pub use crate::tags::KIND_DATA;
pub use crate::tags::KIND_DATA_PRESENTED;
pub use crate::tags::KIND_DATA_WORDS;
pub use crate::tags::KIND_DEF;
pub use crate::tags::KIND_DEF_LAWFUL;
pub use crate::tags::KIND_DEF_RELATING;
pub use crate::tags::KIND_FUNCTOR_DEF;
pub use crate::tags::KIND_MODULE_DEF;
pub use crate::tags::KIND_MODULE_SIG;
pub use crate::tags::LITERAL_INTEGER;
pub use crate::tags::LITERAL_NUMERIC;
pub use crate::tags::LITERAL_TEXT;
pub use crate::tags::MAGIC;
pub use crate::tags::NODE_C_APPLICATION;
pub use crate::tags::NODE_C_BIND;
pub use crate::tags::NODE_C_CASE;
pub use crate::tags::NODE_C_DATA_CASE;
pub use crate::tags::NODE_C_FIXPOINT;
pub use crate::tags::NODE_C_FORCE;
pub use crate::tags::NODE_C_LAMBDA;
pub use crate::tags::NODE_C_LIST_FOLD;
pub use crate::tags::NODE_C_PATH_TRANSPORT;
pub use crate::tags::NODE_C_PROJECT;
pub use crate::tags::NODE_C_RECORD_PROJECTION;
pub use crate::tags::NODE_C_RELATED_APPLICATION;
pub use crate::tags::NODE_C_RETURN;
pub use crate::tags::NODE_C_RIDE;
pub use crate::tags::NODE_C_SIGMA_SPLIT;
pub use crate::tags::NODE_C_TELESCOPE_RIDE;
pub use crate::tags::NODE_C_TELESCOPE_TRANSPORT;
pub use crate::tags::NODE_C_TRANSPORT;
pub use crate::tags::NODE_C_TUPLE_PROJECTION;
pub use crate::tags::NODE_C_WITH;
pub use crate::tags::NODE_CT_ARROW;
pub use crate::tags::NODE_CT_ELEMENT;
pub use crate::tags::NODE_CT_PI;
pub use crate::tags::NODE_CT_RETURNER;
pub use crate::tags::NODE_CT_WITH;
pub use crate::tags::NODE_SHARE_COMP_TYPE;
pub use crate::tags::NODE_SHARE_COMPUTATION;
pub use crate::tags::NODE_SHARE_VALUE;
pub use crate::tags::NODE_SHARE_VALUE_TYPE;
pub use crate::tags::NODE_TAG_TABLE;
pub use crate::tags::NODE_V_CONSTANT;
pub use crate::tags::NODE_V_CONSTRUCTOR;
pub use crate::tags::NODE_V_DEPENDENT_EVALUATION;
pub use crate::tags::NODE_V_FLOW_PRODUCT;
pub use crate::tags::NODE_V_FORWARD_FLOW;
pub use crate::tags::NODE_V_FUNCTION_FLOW;
pub use crate::tags::NODE_V_HERE;
pub use crate::tags::NODE_V_HIGHER;
pub use crate::tags::NODE_V_HIGHER_EVALUATION;
pub use crate::tags::NODE_V_INJECTION;
pub use crate::tags::NODE_V_LIFT;
pub use crate::tags::NODE_V_LIST_CONS;
pub use crate::tags::NODE_V_LIST_NIL;
pub use crate::tags::NODE_V_LITERAL;
pub use crate::tags::NODE_V_PATH_EQUIV;
pub use crate::tags::NODE_V_PATH_PRODUCT;
pub use crate::tags::NODE_V_PATH_REFL;
pub use crate::tags::NODE_V_QUANTIFIED_EVALUATION;
pub use crate::tags::NODE_V_QUOTE;
pub use crate::tags::NODE_V_QUOTE_COMPUTATION;
pub use crate::tags::NODE_V_RECORD;
pub use crate::tags::NODE_V_RETURNED;
pub use crate::tags::NODE_V_STATIC_APPLICATION;
pub use crate::tags::NODE_V_STAY;
pub use crate::tags::NODE_V_THEN;
pub use crate::tags::NODE_V_THUNK;
pub use crate::tags::NODE_V_TUPLE;
pub use crate::tags::NODE_V_UNIVALENCE;
pub use crate::tags::NODE_V_VARIABLE;
pub use crate::tags::NODE_VT_ABSTRACT;
pub use crate::tags::NODE_VT_BASE;
pub use crate::tags::NODE_VT_BRIDGE;
pub use crate::tags::NODE_VT_COMPUTATION_UNIVERSE;
pub use crate::tags::NODE_VT_DATA;
pub use crate::tags::NODE_VT_ELEMENT;
pub use crate::tags::NODE_VT_FLOW;
pub use crate::tags::NODE_VT_FLOW_UNIVERSE;
pub use crate::tags::NODE_VT_LIFT;
pub use crate::tags::NODE_VT_LIST;
pub use crate::tags::NODE_VT_PATH;
pub use crate::tags::NODE_VT_PATH_UNIVERSE;
pub use crate::tags::NODE_VT_PRODUCT;
pub use crate::tags::NODE_VT_RECORD;
pub use crate::tags::NODE_VT_SIGMA;
pub use crate::tags::NODE_VT_STATIC_PI;
pub use crate::tags::NODE_VT_SUM;
pub use crate::tags::NODE_VT_THUNK;
pub use crate::tags::NODE_VT_UNIVERSE;
pub use crate::tags::NodeTagDescription;
pub use crate::tags::NodeTagVerdict;
pub use crate::tags::RELATION_EQ;
pub use crate::tags::RELATION_LEQ;
pub use crate::tags::SEAM_FEEDBACK;
pub use crate::tags::SEAM_SEQUENCE;
pub use crate::tags::SHARING_BLOCK_FIRST;
pub use crate::tags::SHARING_BLOCK_LAST;
pub use crate::tags::SIDE_LEFT;
pub use crate::tags::SIDE_RIGHT;
pub use crate::tags::SIGN_NEGATIVE;
pub use crate::tags::SIGN_NON_NEGATIVE;
pub use crate::tags::TokenCount;
pub use crate::term::Component;
pub use crate::term::Computation;
pub use crate::term::ConstantIndex;
pub use crate::term::ConstructorTag;
pub use crate::term::DeBruijnIndex;
pub use crate::term::EvidenceWord;
pub use crate::term::FieldLabel;
pub use crate::term::FieldPosition;
pub use crate::term::FixpointEvidence;
pub use crate::term::OccurrenceSite;
pub use crate::term::ParameterPosition;
pub use crate::term::PathEvidence;
pub use crate::term::Seam;
pub use crate::term::Side;
pub use crate::term::Stage;
pub use crate::term::StageDepth;
pub use crate::term::StageId;
pub use crate::term::StagedPosition;
pub use crate::term::Standing;
pub use crate::term::Summand;
pub use crate::term::Value;
pub use crate::types::CompType;
pub use crate::types::GroundSort;
pub use crate::types::ValueType;
pub mod session;
pub use crate::tags::NODE_V_SESSION_FLOW;
pub use crate::tags::NODE_V_SESSION_PATH;
pub use crate::tags::NODE_VT_SESSION;
pub use crate::wire::ArtifactImage;
pub use crate::wire::ByteOffset;
pub use crate::wire::EncodedArtifact;
pub use crate::wire::FormatVersion;
pub use crate::wire::WireByte;
pub use crate::wire::WireTag;
