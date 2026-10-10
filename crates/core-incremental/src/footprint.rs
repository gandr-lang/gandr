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
///
/// # Specification
/// - requires: interpreted with an item's body-presence field.
/// - ensures: a missing body is a hole, including when its signature is
///   present; a present root remains filled even when the root does not
///   resolve.
/// - panics: none.
/// - executable: none — the body-presence field is external to this tag.
///
/// # Adequacy
/// - hypothesis: L3 — absent and present bodies plus an unresolved root
///   distinguish confusion between body presence, signature presence and node
///   resolution through exact hole marks.
/// - witness: `footprint::tests::hole_sets_has_hole`
/// - witness: `footprint::tests::bounded_tables_separate_reachability_opacity_and_holes`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum HoleMark
{
    /// The item has a body.
    Filled,
    /// The item's body is a hole.
    Hole,
}

/// What an item's terms mention, conservatively.
///
/// # Specification
/// - requires: a computed footprint is interpreted against its source content.
/// - ensures: the scanner's type reads are a subset of its reads, with opacity
///   and body-presence marks matching that content.
/// - provides: inspectable read sets; a stored footprint is not evidence for
///   adopting a checkpoint.
/// - panics: none.
/// - executable: none — the source content and the provenance of stored
///   metadata are external; the scanner checks its own return boundary.
///
/// # Adequacy
/// - hypothesis: L3 — bound and free variables, shared type/term nodes,
///   unreachable nodes and body-presence boundaries distinguish incorrect sets
///   and marks by exact values. A corrupted stored footprint is separately
///   shown not to control adoption. Reassembled metadata is not certified by
///   the data declaration.
/// - witness: `footprint::tests::shadowed_binder_is_not_a_read`
/// - witness: `footprint::tests::free_occurrence_under_binders_is_read`
/// - witness: `footprint::tests::a_term_visit_does_not_suppress_a_later_type_visit`
/// - witness: `footprint::tests::bounded_tables_separate_reachability_opacity_and_holes`
/// - witness: `tests::incremental::a_stored_footprint_is_not_an_adoption_input`
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
///
/// # Specification
/// - requires: interpreted with the root and former path reaching a node.
/// - ensures: signature and type-former paths retain their type-position mark
///   independently of term-only paths to the same node.
/// - panics: none.
/// - executable: none — path ancestry is external to the carried tag.
///
/// # Adequacy
/// - hypothesis: L3 — a shared node reached first from the body and then from a
///   signature distinguishes a single visited bit from independent position
///   marks through exact type-read membership; a term-only reference in the
///   mixed fixture must remain outside type reads.
/// - witness: `footprint::tests::a_term_visit_does_not_suppress_a_later_type_visit`
/// - witness: `footprint::tests::type_support_holds_only_type_positions`
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
///   root; type reads include the references carried by a type former itself
///   and by nodes reachable through the signature or a type former. The item is
///   opaque exactly when its table holds an unresolved node; the hole mark is
///   set exactly when the body is a hole.
/// - provides: the read relation the value-changed closure runs over.
/// - panics: none.
/// - intension: visits each node at most once per position, so the scan is
///   linear in the table whatever its sharing.
///
/// # Adequacy
/// - hypothesis: L3 — bound variables, free references under binders,
///   signatures and term-first shared nodes distinguish false reads and lost
///   type-position visits by exact sets. Three bounded tables separate a
///   reachable cycle, unreachable references and unresolved nodes, absent roots
///   and an out-of-range present root through exact sets and marks. These
///   finite observations do not establish an unbounded work bound. A quoted
///   abstract type separates promoting its own read from promoting children
///   alone.
/// - witness: `footprint::tests::shadowed_binder_is_not_a_read`
/// - witness: `footprint::tests::free_occurrence_under_binders_is_read`
/// - witness: `footprint::tests::hole_sets_has_hole`
/// - witness: `footprint::tests::ascription_names_are_reads`
/// - witness: `footprint::tests::type_support_holds_only_type_positions`
/// - witness: `footprint::tests::a_term_visit_does_not_suppress_a_later_type_visit`
/// - witness: `footprint::tests::bounded_tables_separate_reachability_opacity_and_holes`
/// - witness: `footprint::tests::a_quoted_abstract_type_reads_its_own_reference_in_type_position`
#[anodized::spec(ensures: |ret| ret.type_reads.is_subset(&ret.reads)
    && ret.opacity == content.opacity()
    && ret.hole == match content.body() {
        Maybe::Absent(body::Absent::Hole) => HoleMark::Hole,
        Maybe::Present(_) => HoleMark::Filled,
    })]
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
        let position = match node.sort() {
            | Sort::ValueType | Sort::CompType => Position::Type,
            | Sort::Value | Sort::Computation => position,
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
        queue.extend(node.children().iter().map(|(child, _)| (child, position)));
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

    /// The footprint of an appended item with `signature` and `body`, after
    /// holes under the keys of `earlier` in their given order.
    ///
    /// # Specification
    /// - requires: the supplied signature, body and their descendants resolve
    ///   in `arena`; the fixture is finite.
    /// - ensures: returns the appended item's transparent footprint, preserving
    ///   the supplied body-presence mark and type-read inclusion.
    /// - panics: when the fixture is refused as out of order or has an
    ///   unresolved arena node.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — holes and filled bodies, bound and free variables and
    ///   shared type/term references distinguish encoding the wrong item or
    ///   losing its body/position information through exact marks and read
    ///   sets.
    /// - witness: `footprint::tests::hole_sets_has_hole`
    /// - witness: `footprint::tests::shadowed_binder_is_not_a_read`
    /// - witness: `footprint::tests::free_occurrence_under_binders_is_read`
    /// - witness: `footprint::tests::a_term_visit_does_not_suppress_a_later_type_visit`
    #[anodized::spec(ensures: |ret| ret.opacity == Opacity::Transparent
        && ret.type_reads.is_subset(&ret.reads)
        && ret.hole == match body {
            Maybe::Absent(body::Absent::Hole) => HoleMark::Hole,
            Maybe::Present(_) => HoleMark::Filled,
        })]
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

    #[test]
    fn a_term_visit_does_not_suppress_a_later_type_visit()
    {
        let mut arena = CoreArena::new();
        let a = arena.value_constant(ConstantIndex::from(0_usize));
        let element = arena.value_type_element(a, Level::zero());
        let key = ItemKey::from("a");
        let footprint = last_footprint(
            arena,
            core::slice::from_ref(&key),
            Maybe::Present(element),
            Maybe::Present(a),
        );
        assert_eq!(footprint.reads, BTreeSet::from([named(&key)]));
        assert_eq!(footprint.type_reads, BTreeSet::from([named(&key)]));
    }

    #[test]
    fn a_quoted_abstract_type_reads_its_own_reference_in_type_position()
    {
        let mut arena = CoreArena::new();
        let abstract_type = arena.value_type_abstract(ConstantIndex::from(0_usize));
        let quoted = arena.value_quote(abstract_type);
        let key = ItemKey::from("a");
        let footprint = last_footprint(
            arena,
            core::slice::from_ref(&key),
            Maybe::Absent(signature::Absent::Unsigned),
            Maybe::Present(quoted),
        );
        assert_eq!(footprint.reads, BTreeSet::from([named(&key)]));
        assert_eq!(footprint.type_reads, BTreeSet::from([named(&key)]));
    }

    #[test]
    fn bounded_tables_separate_reachability_opacity_and_holes()
    {
        let key = ItemKey::from("reachable");
        let cyclic = super::ItemContent::from_parts(
            Reference::Unoccupied,
            Maybe::Absent(signature::Absent::Unsigned),
            Maybe::Present(crate::boundary::NodeIndex::from(0_usize)),
            vec![
                crate::content::ContentNode::Pair(
                    crate::boundary::NodeIndex::from(0_usize),
                    crate::boundary::NodeIndex::from(1_usize),
                ),
                crate::content::ContentNode::Constant(named(&key)),
                crate::content::ContentNode::Constant(named(&ItemKey::from("unreachable"))),
                crate::content::ContentNode::Unresolved(super::Sort::Value),
            ],
        );
        let footprint = footprint_of(&cyclic);
        assert_eq!(footprint.reads, BTreeSet::from([named(&key)]));
        assert_eq!(footprint.type_reads, BTreeSet::new());
        assert_eq!(
            (footprint.opacity, footprint.hole),
            (Opacity::Opaque, HoleMark::Filled)
        );

        let dangling = super::ItemContent::from_parts(
            Reference::Unoccupied,
            Maybe::Present(crate::boundary::NodeIndex::from(usize::MAX)),
            Maybe::Present(crate::boundary::NodeIndex::from(usize::MAX)),
            vec![crate::content::ContentNode::Unresolved(super::Sort::Value)],
        );
        let footprint = footprint_of(&dangling);
        assert_eq!(
            (footprint.reads, footprint.type_reads),
            (BTreeSet::new(), BTreeSet::new())
        );
        assert_eq!(
            (footprint.opacity, footprint.hole),
            (Opacity::Opaque, HoleMark::Filled)
        );

        let empty = super::ItemContent::from_parts(
            Reference::Unoccupied,
            Maybe::Absent(signature::Absent::Unsigned),
            Maybe::Absent(body::Absent::Hole),
            vec![],
        );
        let footprint = footprint_of(&empty);
        assert_eq!(
            (footprint.reads, footprint.type_reads),
            (BTreeSet::new(), BTreeSet::new())
        );
        assert_eq!(
            (footprint.opacity, footprint.hole),
            (Opacity::Transparent, HoleMark::Hole)
        );
    }
}
