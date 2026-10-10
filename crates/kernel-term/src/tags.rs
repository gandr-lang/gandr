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
//! # The numbering above the frozen block
//!
//! The numbering above the frozen block is settled in one table, and the
//! dependent former's tag is assigned against it.
//!
//! | region        | tags        | holds                                                                |
//! | ------------- | ----------- | -------------------------------------------------------------------- |
//! | frozen block  | `0x00–0x1F` | every former this crate mints, contiguous from zero                  |
//! | sharing block | `0x20–0x27` | the stored sharing plane: one former per family, plus held weakening |
//! [`NODE_CT_PI`] is the dependent arrow: its codomain is scoped under a
//! binder, so it is a different node from the non-dependent [`NODE_CT_ARROW`]
//! at the same arity and takes its own tag rather than a flag on the arrow's.
//! [`NODE_VT_ELEMENT`] is the universe-decoding former, and it is the one tag
//! whose child crosses from a type to a *term*: everything the dependent arrow
//! can say depends on a type being able to mention a value, and this is the
//! former that lets it. [`NODE_CT_ELEMENT`] is its computation-family twin.
//!
//! The universe families took four tags from the growth room at once, one
//! family at a time: the computation universe [`NODE_VT_COMPUTATION_UNIVERSE`]
//! among the value types, the computation decode [`NODE_CT_ELEMENT`] among the
//! computation types, and the two quotes [`NODE_V_QUOTE`] and
//! [`NODE_V_QUOTE_COMPUTATION`] among the values. The sort of a universe is a
//! tag rather than an inline byte on [`NODE_VT_UNIVERSE`] for the reason the
//! dependent arrow is: a payload byte that changes what the node means is a
//! field-shape change, which bumps the version, where a fresh tag holds it.
//!
//! The static operators took the last two tags of the growth room: the
//! static Pi [`NODE_VT_STATIC_PI`] among the value types and the static
//! application [`NODE_V_STATIC_APPLICATION`] among the values. The static
//! lambda takes none, because the kernel never represents it: a producer
//! normalizes it away before export. The growth room is spent, so the next
//! former resumes above [`SHARING_BLOCK_LAST`].
//!
//! The sharing block is **reserved and unassigned**: four per-family sharing
//! formers so polarity stays recoverable from the tag alone, and four held
//! slots for an explicit weakening form. No entry carries one, and a reader
//! meeting one refuses it by name at the node site, exactly as it refuses any
//! other unassigned byte. Reserving the block rather than numbering it on
//! demand is what stops the core vocabulary from growing into it: the core
//! resumes above [`SHARING_BLOCK_LAST`], and the block's contiguity — the
//! property that makes a sharing former's family a subtraction rather than a
//! lookup — survives.

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
/// - witness: `sharing_format::sharing_format::a_foreign_magic_is_refused_at_the_header`
/// - witness: `sharing_format::sharing_format::the_empty_sequence_encodes_to_a_bare_header`
/// - witness: `tags::tests::the_tag_table_is_a_contiguous_frozen_block`
/// - witness: `tags::tests::the_reserved_sharing_block_sits_above_the_frozen_block`
pub const MAGIC: [u8; 4] = *b"GKX1";

/// The format version this crate writes and the only one it accepts.
///
/// Version two writes the version field and every fixed-width integer field
/// little-endian.
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
/// - witness: `sharing_format::sharing_format::a_predecessor_version_is_refused_by_name`
/// - witness: `sharing_format::sharing_format::the_empty_sequence_encodes_to_a_bare_header`
/// - witness: `tags::tests::the_tag_table_is_a_contiguous_frozen_block`
/// - witness: `tags::tests::the_reserved_sharing_block_sits_above_the_frozen_block`
pub const FORMAT_VERSION: FormatVersion = FormatVersion(2);

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

/// Injection side: the left injection.
pub const SIDE_LEFT: WireTag = WireTag(0);
/// Injection side: the right injection.
pub const SIDE_RIGHT: WireTag = WireTag(1);

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
/// Node tag: the value-type unit.
pub const NODE_VT_UNIT: WireTag = WireTag(0x01);
/// Node tag: the universe of value types, with an inline level.
pub const NODE_VT_UNIVERSE: WireTag = WireTag(0x02);
/// Node tag: the product former, over two value types.
pub const NODE_VT_PRODUCT: WireTag = WireTag(0x03);
/// Node tag: the sum former, over two value types.
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
/// Node tag: the unit value.
pub const NODE_V_UNIT: WireTag = WireTag(0x0B);
/// Node tag: a literal value, with an inline literal kind and canonical
/// payload.
pub const NODE_V_LITERAL: WireTag = WireTag(0x0C);
/// Node tag: a pair value, over two values.
pub const NODE_V_PAIR: WireTag = WireTag(0x0D);
/// Node tag: a sum injection value, with an inline side, over one value.
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
/// Node tag: a case computation, over a value scrutinee and two computation
/// branches.
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
/// - witness: `sharing_format::sharing_format::the_empty_sequence_encodes_to_a_bare_header`
/// - witness: `tags::tests::the_tag_table_is_a_contiguous_frozen_block`
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
/// - witness: `sharing_format::sharing_format::the_empty_sequence_encodes_to_a_bare_header`
/// - witness: `tags::tests::the_tag_table_is_a_contiguous_frozen_block`
pub const SHARING_BLOCK_LAST: WireTag = WireTag(0x27);

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
/// - witness: `tags::tests::the_tag_table_is_a_contiguous_frozen_block`
/// - witness: `tags::tests::the_reserved_sharing_block_sits_above_the_frozen_block`
/// - witness: `tags::tests::every_row_states_one_token_and_agrees_with_its_verdicts`
/// - witness: `tags::tests::the_base_atom_row_is_the_one_verdict_split`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ChildArity(u8);

impl From<ChildArity> for u8
{
    /// The child count the arity carries.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(arity: ChildArity) -> Self
    {
        arity.0
    }
}

impl From<ChildArity> for usize
{
    /// The child count the arity carries, widened for indexing.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(arity: ChildArity) -> Self
    {
        Self::from(arity.0)
    }
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
/// - witness: `tags::tests::the_tag_table_is_a_contiguous_frozen_block`
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
/// - witness: `tags::tests::the_tag_table_is_a_contiguous_frozen_block`
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
/// - witness: `tags::tests::the_tag_table_is_a_contiguous_frozen_block`
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
/// - requires: `tag` is one of the frozen node tags, and the two verdicts are
///   the classifications recorded for it.
/// - ensures: returns the description carrying its arguments unchanged, with
///   the tag's own token contribution fixed at one.
/// - provides: the one row constructor, so every row agrees that a tag
///   contributes exactly one storage token.
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
/// - witness: `tags::tests::the_tag_table_is_a_contiguous_frozen_block`
/// - witness: `tags::tests::the_reserved_sharing_block_sits_above_the_frozen_block`
/// - witness: `tags::tests::every_row_states_one_token_and_agrees_with_its_verdicts`
/// - witness: `tags::tests::the_base_atom_row_is_the_one_verdict_split`
#[spec(
    requires: tag.0 <= NODE_V_STATIC_APPLICATION.0
            && match max_token_bound { Some(bound) => bound.0 >= 1, None => true },
    ensures: |ret| ret.tag.0 == tag.0
            && ret.child_arity.0 == child_arity.0
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
/// - requires: `tag` names a former whose inline payload has no finite token
///   bound.
/// - ensures: returns the row with no token bound and both verdicts
///   [`NodeTagVerdict::Boundary`].
/// - provides: the shorthand that keeps an unbounded payload from being
///   recorded as an alias by hand.
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
/// - witness: `tags::tests::the_tag_table_is_a_contiguous_frozen_block`
/// - witness: `tags::tests::the_reserved_sharing_block_sits_above_the_frozen_block`
/// - witness: `tags::tests::every_row_states_one_token_and_agrees_with_its_verdicts`
/// - witness: `tags::tests::the_base_atom_row_is_the_one_verdict_split`
#[spec(
    requires: tag.0 <= NODE_V_STATIC_APPLICATION.0
            && !matches!(tag, NODE_VT_BASE | NODE_VT_UNIT | NODE_V_VARIABLE | NODE_V_CONSTANT | NODE_V_UNIT | NODE_VT_ABSTRACT),
    ensures: |ret| ret.tag.0 == tag.0
            && ret.child_arity.0 == child_arity.0
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
/// - witness: `tags::tests::the_tag_table_is_a_contiguous_frozen_block`
/// - witness: `tags::tests::the_reserved_sharing_block_sits_above_the_frozen_block`
/// - witness: `tags::tests::every_row_states_one_token_and_agrees_with_its_verdicts`
/// - witness: `tags::tests::the_base_atom_row_is_the_one_verdict_split`
#[spec(
    requires: match tag { NODE_VT_UNIT | NODE_V_UNIT => bound.0 >= 1, NODE_V_VARIABLE | NODE_V_CONSTANT | NODE_VT_ABSTRACT => bound.0 >= 2, _ => false },
    ensures: |ret| ret.tag.0 == tag.0
            && ret.child_arity.0 == 0
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
        ChildArity(0),
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
/// - ensures: lists each frozen former exactly once in tag order with its child
///   arity, token contribution and storage classifications.
/// - panics: none.
/// - executable: none — this catalogue has no runtime invocation; its const
///   constructors enforce local fields and the witnesses compare the complete
///   protocol table.
///
/// # Adequacy
/// - hypothesis: L2 compares all 32 frozen rows with independently constructed
///   arena formers through their child relation. L3 observes the complete tag
///   interval, the reserved sharing boundary, one-token contributions,
///   finite/unbounded classifications and the base-atom split. These
///   distinguish tag reuse, wrong arity and collapsed classification criteria;
///   arbitrary extension vocabularies are outside this fixed catalogue.
/// - witness: `tags::tests::the_tag_table_matches_the_wire_arities`
/// - witness: `tags::tests::the_tag_table_is_a_contiguous_frozen_block`
/// - witness: `tags::tests::the_reserved_sharing_block_sits_above_the_frozen_block`
/// - witness: `tags::tests::every_row_states_one_token_and_agrees_with_its_verdicts`
/// - witness: `tags::tests::the_base_atom_row_is_the_one_verdict_split`
pub const NODE_TAG_TABLE: [NodeTagDescription; 32] = [
    row(
        NODE_VT_BASE,
        ChildArity(0),
        Some(TokenCount(2)),
        NodeTagVerdict::Boundary,
        NodeTagVerdict::Alias,
    ),
    bounded_alias(NODE_VT_UNIT, TokenCount(1)),
    unbounded(NODE_VT_UNIVERSE, ChildArity(0)),
    unbounded(NODE_VT_PRODUCT, ChildArity(2)),
    unbounded(NODE_VT_SUM, ChildArity(2)),
    unbounded(NODE_VT_THUNK, ChildArity(1)),
    unbounded(NODE_VT_LIFT, ChildArity(1)),
    unbounded(NODE_CT_RETURNER, ChildArity(1)),
    unbounded(NODE_CT_ARROW, ChildArity(2)),
    bounded_alias(NODE_V_VARIABLE, TokenCount(2)),
    bounded_alias(NODE_V_CONSTANT, TokenCount(2)),
    bounded_alias(NODE_V_UNIT, TokenCount(1)),
    unbounded(NODE_V_LITERAL, ChildArity(0)),
    unbounded(NODE_V_PAIR, ChildArity(2)),
    unbounded(NODE_V_INJECTION, ChildArity(1)),
    unbounded(NODE_V_THUNK, ChildArity(1)),
    unbounded(NODE_V_LIFT, ChildArity(1)),
    unbounded(NODE_C_LAMBDA, ChildArity(1)),
    unbounded(NODE_C_APPLICATION, ChildArity(2)),
    unbounded(NODE_C_RETURN, ChildArity(1)),
    unbounded(NODE_C_BIND, ChildArity(2)),
    unbounded(NODE_C_FORCE, ChildArity(1)),
    unbounded(NODE_C_CASE, ChildArity(3)),
    bounded_alias(NODE_VT_ABSTRACT, TokenCount(2)),
    unbounded(NODE_CT_PI, ChildArity(2)),
    unbounded(NODE_VT_ELEMENT, ChildArity(1)),
    unbounded(NODE_VT_COMPUTATION_UNIVERSE, ChildArity(0)),
    unbounded(NODE_CT_ELEMENT, ChildArity(1)),
    unbounded(NODE_V_QUOTE, ChildArity(1)),
    unbounded(NODE_V_QUOTE_COMPUTATION, ChildArity(1)),
    unbounded(NODE_VT_STATIC_PI, ChildArity(2)),
    unbounded(NODE_V_STATIC_APPLICATION, ChildArity(2)),
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
    use crate::term::Side;
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
                && ret.1.iter().zip(NODE_TAG_TABLE.iter()).all(|(&node, row)| match node { AnyNode::Value(id) => match ret.0.value(id) { Some(&crate::Value::Variable(_)) => row.tag.0 == super::NODE_V_VARIABLE.0, Some(&crate::Value::Constant(_)) => row.tag.0 == super::NODE_V_CONSTANT.0, Some(&crate::Value::Unit) => row.tag.0 == super::NODE_V_UNIT.0, Some(&crate::Value::Literal(_)) => row.tag.0 == super::NODE_V_LITERAL.0, Some(&crate::Value::Pair(_, _)) => row.tag.0 == super::NODE_V_PAIR.0, Some(&crate::Value::Injection(_, _)) => row.tag.0 == super::NODE_V_INJECTION.0, Some(&crate::Value::Thunk(_)) => row.tag.0 == super::NODE_V_THUNK.0, Some(&crate::Value::Lift { .. }) => row.tag.0 == super::NODE_V_LIFT.0, Some(&crate::Value::Quote(_)) => row.tag.0 == super::NODE_V_QUOTE.0, Some(&crate::Value::QuoteComputation(_)) => row.tag.0 == super::NODE_V_QUOTE_COMPUTATION.0, Some(&crate::Value::StaticApplication(_, _)) => row.tag.0 == super::NODE_V_STATIC_APPLICATION.0, None => false, }, AnyNode::Computation(id) => match ret.0.computation(id) { Some(&crate::Computation::Lambda(_)) => row.tag.0 == super::NODE_C_LAMBDA.0, Some(&crate::Computation::Application(_, _)) => row.tag.0 == super::NODE_C_APPLICATION.0, Some(&crate::Computation::Return(_)) => row.tag.0 == super::NODE_C_RETURN.0, Some(&crate::Computation::Bind(_, _)) => row.tag.0 == super::NODE_C_BIND.0, Some(&crate::Computation::Force(_)) => row.tag.0 == super::NODE_C_FORCE.0, Some(&crate::Computation::Case { .. }) => row.tag.0 == super::NODE_C_CASE.0, None => false, }, AnyNode::ValueType(id) => match ret.0.value_type(id) { Some(&crate::ValueType::Base(_)) => row.tag.0 == super::NODE_VT_BASE.0, Some(&crate::ValueType::Unit) => row.tag.0 == super::NODE_VT_UNIT.0, Some(&crate::ValueType::Product(_, _)) => row.tag.0 == super::NODE_VT_PRODUCT.0, Some(&crate::ValueType::Sum(_, _)) => row.tag.0 == super::NODE_VT_SUM.0, Some(&crate::ValueType::Thunk(_)) => row.tag.0 == super::NODE_VT_THUNK.0, Some(&crate::ValueType::Universe { sort: GroundSort::Value, .. }) => row.tag.0 == super::NODE_VT_UNIVERSE.0, Some(&crate::ValueType::Universe { sort: GroundSort::Computation, .. }) => row.tag.0 == super::NODE_VT_COMPUTATION_UNIVERSE.0, Some(&crate::ValueType::Lift { .. }) => row.tag.0 == super::NODE_VT_LIFT.0, Some(&crate::ValueType::Element { .. }) => row.tag.0 == super::NODE_VT_ELEMENT.0, Some(&crate::ValueType::Abstract(_)) => row.tag.0 == super::NODE_VT_ABSTRACT.0, Some(&crate::ValueType::StaticPi { .. }) => row.tag.0 == super::NODE_VT_STATIC_PI.0, None => false, }, AnyNode::CompType(id) => match ret.0.comp_type(id) { Some(&crate::CompType::Returner(_)) => row.tag.0 == super::NODE_CT_RETURNER.0, Some(&crate::CompType::Arrow { .. }) => row.tag.0 == super::NODE_CT_ARROW.0, Some(&crate::CompType::Pi { .. }) => row.tag.0 == super::NODE_CT_PI.0, Some(&crate::CompType::Element { .. }) => row.tag.0 == super::NODE_CT_ELEMENT.0, None => false, }, }),
    )]
    fn one_node_per_former() -> (TermArena, Vec<AnyNode>)
    {
        let mut arena = TermArena::new();
        let level = gandr_kernel_strata::Level::zero();
        let base = arena.value_type_base(BaseType::Integer);
        let unit_type = arena.value_type_unit();
        let universe = arena.value_type_universe(GroundSort::Value, level.clone());
        let product = arena.value_type_product(base, unit_type);
        let sum = arena.value_type_sum(base, unit_type);
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
        let pair = arena.value_pair(unit, unit);
        let injection = arena.value_injection(Side::Left, unit);
        let ret = arena.computation_return(unit);
        let thunk = arena.value_thunk(ret);
        let lift = arena.value_lift(level.clone(), unit);
        let lambda = arena.computation_lambda(ret);
        let application = arena.computation_application(ret, unit);
        let bind = arena.computation_bind(ret, ret);
        let force = arena.computation_force(unit);
        let case = arena.computation_case(unit, ret, ret);
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
        let nodes = alloc::vec![
            AnyNode::ValueType(base),
            AnyNode::ValueType(unit_type),
            AnyNode::ValueType(universe),
            AnyNode::ValueType(product),
            AnyNode::ValueType(sum),
            AnyNode::ValueType(thunk_type),
            AnyNode::ValueType(lift_type),
            AnyNode::CompType(returner),
            AnyNode::CompType(arrow),
            AnyNode::Value(variable),
            AnyNode::Value(constant),
            AnyNode::Value(unit),
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
            assert_eq!(
                usize::from(row.child_arity),
                children.len(),
                "the declared arity of tag {} matches the arena's child relation",
                row.tag
            );
        }
    }

    #[test]
    fn the_tag_table_is_a_contiguous_frozen_block()
    {
        let tags: Vec<WireTag> = NODE_TAG_TABLE.iter().map(|row| row.tag).collect();
        let expected: Vec<WireTag> = (0_u8 .. 32).map(WireTag::from).collect();
        assert_eq!(expected, tags, "the node tags are contiguous from zero");
    }

    /// The settled numbering, asserted as the regions it splits into: the
    /// frozen block stays strictly below the sharing block and, the growth
    /// room spent by the static operators, meets it; the sharing block is
    /// eight contiguous tags. A frozen-block addition that grew into the
    /// reserved block would fail here rather than at the merge the settlement
    /// exists to avoid.
    #[test]
    fn the_reserved_sharing_block_sits_above_the_frozen_block()
    {
        let highest = NODE_TAG_TABLE.last().expect("the table is non-empty").tag;
        assert!(
            u8::from(highest) < u8::from(super::SHARING_BLOCK_FIRST),
            "the frozen block stays below the reserved sharing block"
        );
        assert_eq!(
            u8::from(highest).checked_add(1),
            Some(u8::from(super::SHARING_BLOCK_FIRST)),
            "and the growth room between them is spent, so the next former resumes above the \
             block"
        );
        let block = [
            super::NODE_SHARE_VALUE,
            super::NODE_SHARE_COMPUTATION,
            super::NODE_SHARE_VALUE_TYPE,
            super::NODE_SHARE_COMP_TYPE,
        ];
        for (offset, tag) in block.iter().enumerate() {
            let expected = u8::from(super::SHARING_BLOCK_FIRST)
                .checked_add(u8::try_from(offset).expect("four fits a byte"))
                .expect("the block does not wrap");
            assert_eq!(
                expected,
                u8::from(*tag),
                "the four per-family sharing formers open the block in family order"
            );
        }
        assert_eq!(
            8_u8,
            u8::from(super::SHARING_BLOCK_LAST)
                .checked_sub(u8::from(super::SHARING_BLOCK_FIRST))
                .and_then(|span| span.checked_add(1))
                .expect("the block is well ordered"),
            "the block is eight tags: four formers and four held weakening slots"
        );
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
