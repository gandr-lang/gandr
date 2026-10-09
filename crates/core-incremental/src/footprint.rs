//! The conservative footprint: what an item's terms mention, read off its
//! content table.
//!
//! # A scan, not the judgement's support
//!
//! The footprint over-approximates: every reference anywhere in the item is a
//! read, whether or not the judgement would reach it. It answers one question
//! the support cannot: which items read a definition whose value changed, so
//! the change can be closed over readers that never consulted a type. A
//! variable is never a read — it is a de Bruijn index into the item's own
//! binders — so shadowing cannot hide a read or invent one. The references in
//! type positions, the signature and anything under a type former, are the
//! item's type support, kept apart because a value change reaches an item's
//! typing only through them.

use alloc::collections::BTreeSet;
use alloc::collections::VecDeque;
use alloc::vec::Vec;

use gandr_core_checker::body;
use quenchant_shape::shape::Maybe;

use crate::content::ItemContent;
use crate::content::Opacity;
use crate::content::Sort;
use crate::region::Reference;

/// Whether an item's body is a hole.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum HoleMark
{
    /// The item has a body.
    Filled,
    /// The item's body is a hole.
    Hole,
}

/// What an item's terms mention, conservatively.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Footprint
{
    /// Every reference the item mentions, in any position.
    reads: BTreeSet<Reference>,
    /// The references in type positions: the item's type support.
    type_reads: BTreeSet<Reference>,
    /// Whether every node resolved.
    opacity: Opacity,
    /// Whether the body is a hole.
    hole: HoleMark,
}

impl Footprint
{
    /// Every reference the item mentions, ascending.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn reads(&self) -> impl ExactSizeIterator<Item = &Reference>
    {
        self.reads.iter()
    }

    /// The references in type positions, ascending.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn type_reads(&self) -> impl ExactSizeIterator<Item = &Reference>
    {
        self.type_reads.iter()
    }

    /// Whether every node of the item resolved.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn opacity(&self) -> Opacity
    {
        self.opacity
    }

    /// Whether the item's body is a hole.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn hole(&self) -> HoleMark
    {
        self.hole
    }

    /// The footprint of these parts, as the decoder reassembles it.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn from_parts(
        reads: BTreeSet<Reference>,
        type_reads: BTreeSet<Reference>,
        opacity: Opacity,
        hole: HoleMark,
    ) -> Self
    {
        Self {
            reads,
            type_reads,
            opacity,
            hole,
        }
    }
}

/// Where a node is reached: among terms, or inside a type.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Position
{
    /// Reached through terms only.
    Term,
    /// Reached through a signature or a type former.
    Type,
}

/// The footprint of `content`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the reads are the references of every node reachable from either
///   root; the type reads are those of every node reachable through the
///   signature or through a type former; the item is opaque exactly when its
///   table holds an unresolved node; the hole mark is set exactly when the body
///   is a hole.
/// - provides: the read relation the value-changed closure runs over.
/// - panics: none.
/// - intension: visits each node at most once per position, so the scan is
///   linear in the table whatever its sharing.
///
/// # Adequacy
/// - hypothesis: L3 — the surfaces are the reach of the walk, the position a
///   node is reached in, the opacity and the hole mark, separated by a bound
///   variable that is no read, a constant under binders that is one, a hole, a
///   constant read from a signature, and a constant reached from the body and
///   from the signature at once.
/// - witness: `footprint::tests::shadowed_binder_is_not_a_read`
/// - witness: `footprint::tests::free_occurrence_under_binders_is_read`
/// - witness: `footprint::tests::hole_sets_has_hole`
/// - witness: `footprint::tests::ascription_names_are_reads`
/// - witness: `footprint::tests::type_support_holds_only_type_positions`
#[inline]
#[must_use]
pub fn footprint_of(content: &ItemContent) -> Footprint
{
    let mut reads = BTreeSet::new();
    let mut type_reads = BTreeSet::new();
    let mut reached: Vec<[bool; 2]> = alloc::vec![[false; 2]; content.nodes().len()];
    let mut queue = VecDeque::new();
    if let Maybe::Present(root) = content.signature() {
        queue.push_back((root, Position::Type));
    }
    if let Maybe::Present(root) = content.body() {
        queue.push_back((root, Position::Term));
    }
    while let Some((index, position)) = queue.pop_front() {
        let (Some(marks), Some(node)) = (
            reached.get_mut(usize::from(index)),
            content.nodes().get(usize::from(index)),
        )
        else {
            continue;
        };
        let mark = match position {
            | Position::Term => marks.first_mut(),
            | Position::Type => marks.last_mut(),
        };
        match mark {
            | Some(&mut true) | None => continue,
            | Some(mark) => *mark = true,
        }
        if let Maybe::Present(reference) = node.reference() {
            let _fresh = reads.insert(reference.clone());
            if position == Position::Type {
                let _fresh = type_reads.insert(reference.clone());
            }
        }
        let inner = match node.sort() {
            | Sort::ValueType | Sort::CompType => Position::Type,
            | Sort::Value | Sort::Computation => position,
        };
        queue.extend(node.children().iter().map(|(child, _)| (child, inner)));
    }
    Footprint {
        reads,
        type_reads,
        opacity: content.opacity(),
        hole: match content.body() {
            | Maybe::Absent(body::Absent::Hole) => HoleMark::Hole,
            | Maybe::Present(_) => HoleMark::Filled,
        },
    }
}

#[cfg(test)]
mod tests
{
    use alloc::collections::BTreeSet;
    use alloc::vec;

    use gandr_core_checker::Declaration;
    use gandr_core_checker::OriginToken;
    use gandr_core_checker::body;
    use gandr_core_checker::signature;
    use gandr_core_term::CoreArena;
    use gandr_core_term::ValueId;
    use gandr_core_term::ValueTypeId;
    use gandr_core_term::Zone;
    use gandr_kernel_strata::Level;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;
    use quenchant_shape::shape::Maybe;

    use super::Footprint;
    use super::HoleMark;
    use super::footprint_of;
    use crate::boundary::ItemOrdinal;
    use crate::boundary::Occurrence;
    use crate::content::Opacity;
    use crate::content::encode_item;
    use crate::region::Item;
    use crate::region::ItemKey;
    use crate::region::Program;
    use crate::region::Reference;

    /// The reference of the first item of `key`.
    ///
    /// # Specification
    /// trivial.
    fn named(key: &ItemKey) -> Reference
    {
        Reference::Item {
            key: key.clone(),
            occurrence: Occurrence::from(0_usize),
        }
    }

    /// The footprint of the last item of a program whose earlier items are
    /// holes named `a`, `b`, … at positions 0, 1, …, and whose last item has
    /// `signature` and `body`.
    ///
    /// # Specification
    /// trivial.
    fn last_footprint(
        arena: CoreArena,
        earlier: &[ItemKey],
        signature: Maybe<ValueTypeId, signature::Absent>,
        body: Maybe<ValueId, body::Absent>,
    ) -> Footprint
    {
        let mut items: alloc::vec::Vec<Item> = earlier
            .iter()
            .enumerate()
            .map(|(position, key)| {
                Item::new(
                    key.clone(),
                    Declaration::new(
                        ConstantIndex::from(position),
                        Maybe::Absent(signature::Absent::Unsigned),
                        Maybe::Absent(body::Absent::Hole),
                        OriginToken::from(position),
                    ),
                )
            })
            .collect();
        items.push(Item::new(
            ItemKey::from("last"),
            Declaration::new(
                ConstantIndex::from(earlier.len()),
                signature,
                body,
                OriginToken::from(earlier.len()),
            ),
        ));
        let program = Program::new(arena, items).expect("ascending");
        let encoded = encode_item(
            program.arena(),
            program.layout(),
            ItemOrdinal::from(earlier.len()),
        );
        assert_eq!(
            encoded.content.opacity(),
            Opacity::Transparent,
            "the fixture resolves"
        );
        footprint_of(&encoded.content)
    }

    #[test]
    fn shadowed_binder_is_not_a_read()
    {
        let mut arena = CoreArena::new();
        // thunk (λ. return v0): the variable is the lambda's own binder.
        let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let returned = arena.computation_return(bound);
        let lambda = arena.computation_lambda(returned);
        let thunk = arena.value_thunk(lambda);
        let footprint = last_footprint(
            arena,
            &[ItemKey::from("v0")],
            Maybe::Absent(signature::Absent::Unsigned),
            Maybe::Present(thunk),
        );
        assert_eq!(
            footprint.reads().count(),
            0_usize,
            "a bound variable reads nothing, whatever an earlier item is called"
        );
    }

    #[test]
    fn free_occurrence_under_binders_is_read()
    {
        let mut arena = CoreArena::new();
        // thunk (λ. λ. return d): the constant sits under two binders.
        let constant = arena.value_constant(ConstantIndex::from(0_usize));
        let returned = arena.computation_return(constant);
        let inner = arena.computation_lambda(returned);
        let outer = arena.computation_lambda(inner);
        let thunk = arena.value_thunk(outer);
        let d = ItemKey::from("d");
        let footprint = last_footprint(
            arena,
            core::slice::from_ref(&d),
            Maybe::Absent(signature::Absent::Unsigned),
            Maybe::Present(thunk),
        );
        assert_eq!(
            footprint.reads,
            BTreeSet::from([named(&d)]),
            "a constant under binders is a read"
        );
        assert_eq!(
            footprint.type_reads().count(),
            0_usize,
            "and not a type read"
        );
    }

    #[test]
    fn hole_sets_has_hole()
    {
        let mut arena = CoreArena::new();
        let integer = arena.value_type_base(BaseType::Integer);
        let unit = arena.value_unit();
        let holey = last_footprint(
            arena.clone(),
            &[],
            Maybe::Present(integer),
            Maybe::Absent(body::Absent::Hole),
        );
        assert_eq!(holey.hole(), HoleMark::Hole, "a hole sets the mark");
        let filled = last_footprint(
            arena,
            &[],
            Maybe::Absent(signature::Absent::Unsigned),
            Maybe::Present(unit),
        );
        assert_eq!(filled.hole(), HoleMark::Filled, "a body clears it");
        assert_eq!(
            (holey.opacity(), filled.opacity()),
            (Opacity::Transparent, Opacity::Transparent),
            "both resolve"
        );
    }

    #[test]
    fn ascription_names_are_reads()
    {
        let mut arena = CoreArena::new();
        let code = arena.value_constant(ConstantIndex::from(0_usize));
        let element = arena.value_type_element(code, Level::zero());
        let unit = arena.value_unit();
        let c = ItemKey::from("c");
        let footprint = last_footprint(
            arena,
            core::slice::from_ref(&c),
            Maybe::Present(element),
            Maybe::Present(unit),
        );
        assert_eq!(
            (footprint.reads, footprint.type_reads),
            (BTreeSet::from([named(&c)]), BTreeSet::from([named(&c)])),
            "a constant in the signature is a read and a type read"
        );
    }

    #[test]
    fn type_support_holds_only_type_positions()
    {
        let mut arena = CoreArena::new();
        // signature El(a); body (b, a): a is read in both positions, b only
        // among terms.
        let a = arena.value_constant(ConstantIndex::from(0_usize));
        let b = arena.value_constant(ConstantIndex::from(1_usize));
        let element = arena.value_type_element(a, Level::zero());
        let pair = arena.value_pair(b, a);
        let keys = vec![ItemKey::from("a"), ItemKey::from("b")];
        let footprint = last_footprint(arena, &keys, Maybe::Present(element), Maybe::Present(pair));
        let [ref a_key, ref b_key] = *keys.as_slice()
        else {
            panic!("two keys");
        };
        assert_eq!(
            footprint.reads,
            BTreeSet::from([named(a_key), named(b_key)]),
            "every mention is a read"
        );
        assert_eq!(
            footprint.type_reads,
            BTreeSet::from([named(a_key)]),
            "only the signature's mention is type support, though the body shares its node"
        );
    }
}
