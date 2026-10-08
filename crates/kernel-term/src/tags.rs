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
//! | frozen block  | `0x00–0x19` | every former this crate mints, contiguous from zero                  |
//! | growth room   | `0x1A–0x1F` | held for the core vocabulary, contiguous continuation of the block   |
//! | sharing block | `0x20–0x27` | the stored sharing plane: one former per family, plus held weakening |
//!
//! [`NODE_CT_PI`] is the dependent arrow: its codomain is scoped under a
//! binder, so it is a different node from the non-dependent [`NODE_CT_ARROW`]
//! at the same arity and takes its own tag rather than a flag on the arrow's.
//! [`NODE_VT_ELEMENT`] is the universe-decoding former, and it is the one tag
//! whose child crosses from a type to a *term*: everything the dependent arrow
//! can say depends on a type being able to mention a value, and this is the
//! former that lets it.
//!
//! The sharing block is **reserved and unassigned**: four per-family sharing
//! formers so polarity stays recoverable from the tag alone, and four held
//! slots for an explicit weakening form. No entry carries one, and a reader
//! meeting one refuses it by name at the node site, exactly as it refuses any
//! other unassigned byte. Reserving the block rather than numbering it on
//! demand is what stops the core vocabulary from growing into it: the core
//! grows through the growth room and resumes above [`SHARING_BLOCK_LAST`], and
//! the block's contiguity — the property that makes a sharing former's family a
//! subtraction rather than a lookup — survives.

use crate::wire::FormatVersion;
use crate::wire::WireTag;

/// The four-byte artifact magic. The trailing byte is a v-family marker,
/// independent of the version field, which is a separate little-endian
/// sixteen-bit field.
pub const MAGIC: [u8; 4] = *b"GKX1";

/// The format version this crate writes and the only one it accepts.
///
/// Version two writes the version field and every fixed-width integer field
/// little-endian.
///
/// A refusal names the version it met rather than guessing at it, which is
/// what makes an older reader meeting a newer artifact stop with an accurate
/// reason.
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
/// Node tag: the universe former, with an inline level.
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
pub const SHARING_BLOCK_FIRST: WireTag = NODE_SHARE_VALUE;
/// The last tag of the reserved stored-sharing block: the fourth held slot,
/// which the explicit weakening form would take one family at a time.
pub const SHARING_BLOCK_LAST: WireTag = WireTag(0x27);

/// The number of subterm-table child references an entry carries after its
/// inline payload.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ChildArity(u8);

impl From<ChildArity> for u8
{
    #[inline]
    fn from(arity: ChildArity) -> Self
    {
        arity.0
    }
}

impl From<ChildArity> for usize
{
    #[inline]
    fn from(arity: ChildArity) -> Self
    {
        Self::from(arity.0)
    }
}

/// A count of storage tokens: a tag's own contribution, or the finite bound on
/// a tag together with its inline payload.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TokenCount(u8);

impl From<TokenCount> for u8
{
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
/// - requires: nothing — every field is an immutable description.
/// - ensures: `tag` is one of the frozen node tags; `child_arity` is the number
///   of child references the encoder emits after the inline payload, which the
///   arena's own child relation is differentially compared against; and the two
///   verdicts record the two storage classifications.
/// - provides: the const protocol input the storage tier reads, without
///   altering a single artifact byte. Table-wide protocol agreement stays
///   prose: a data-item `#[spec]` does not check const construction or compare
///   encoder and arena observations.
/// - fails: never.
/// - panics: none.
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
pub const NODE_TAG_TABLE: [NodeTagDescription; 26] = [
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
];

#[cfg(test)]
mod tests
{
    use alloc::format;
    use alloc::string::String;
    use alloc::vec::Vec;

    use super::NODE_TAG_TABLE;
    use super::NodeTagVerdict;
    use crate::arena::AnyNode;
    use crate::arena::TermArena;
    use crate::base::BaseType;
    use crate::base::FractionDigits;
    use crate::base::IntegerLiteral;
    use crate::base::Literal;
    use crate::base::Magnitude;
    use crate::base::NumericLiteral;
    use crate::base::Sign;
    use crate::base::StringLiteral;
    use crate::term::ConstantIndex;
    use crate::term::DeBruijnIndex;
    use crate::term::Side;
    use crate::wire::WireTag;

    /// One node of every former, in the tag table's order, in a fresh arena.
    fn one_node_per_former() -> (TermArena, Vec<AnyNode>)
    {
        let mut arena = TermArena::new();
        let level = gandr_kernel_strata::Level::zero();
        let base = arena.value_type_base(BaseType::Integer);
        let unit_type = arena.value_type_unit();
        let universe = arena.value_type_universe(level.clone());
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
        let element = arena.value_type_element(unit, level);
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
        let expected: Vec<WireTag> = (0_u8 .. 26).map(WireTag::from).collect();
        assert_eq!(expected, tags, "the node tags are contiguous from zero");
    }

    /// The settled numbering, asserted as the three regions it splits into: the
    /// frozen block stays strictly below the sharing block, the growth room
    /// between them is non-empty, and the sharing block is eight contiguous
    /// tags. A frozen-block addition that grew into the reserved block would
    /// fail here rather than at the merge the settlement exists to avoid.
    #[test]
    fn the_reserved_sharing_block_sits_above_the_frozen_block()
    {
        let highest = NODE_TAG_TABLE.last().expect("the table is non-empty").tag;
        assert!(
            u8::from(highest) < u8::from(super::SHARING_BLOCK_FIRST),
            "the frozen block stays below the reserved sharing block"
        );
        assert!(
            u8::from(highest).saturating_add(1) < u8::from(super::SHARING_BLOCK_FIRST),
            "and the growth room between them is non-empty"
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

    #[test]
    fn a_wire_tag_renders_as_its_byte()
    {
        assert_eq!(String::from("0x17"), format!("{}", WireTag::from(0x17)));
    }

    /// A literal of every kind is representable, which the encoder's literal
    /// arm needs and no other test in this module reaches.
    #[test]
    fn every_literal_kind_is_representable()
    {
        let text = Literal::Text(StringLiteral::new(String::from("x")));
        let numeric = Literal::Numeric(NumericLiteral::new(
            Sign::Negative,
            Magnitude::zero(),
            FractionDigits::none(),
        ));
        assert_ne!(text, numeric, "the literal kinds are distinct payloads");
    }
}
