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

use anodized::spec;
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
#[spec(ensures: |ret| ret.type_reads.is_subset(&ret.reads)
    && ret.opacity == content.opacity()
    && ret.hole == match *(content.declaration()) {
crate::content::DeclarationRoots::Value { body:Maybe::Absent(body::Absent::Hole),.. } => HoleMark::Hole,
crate::content::DeclarationRoots::Value { body:Maybe::Present(_),.. } | crate::content::DeclarationRoots::Data(_) | crate::content::DeclarationRoots::Abstract(_) | crate::content::DeclarationRoots::World => HoleMark::Filled,
})]
#[inline]
#[must_use]
pub fn footprint_of(content: &ItemContent) -> Footprint
{
    let mut reads = BTreeSet::new();
    let mut type_reads = BTreeSet::new();
    let mut reached: Vec<[bool; 2]> = alloc::vec![[false; 2]; content.nodes().len()];
    let mut queue = VecDeque::new();
    queue.extend(content.declaration().iter().map(|(root, sort)| {
        (root, match sort {
            Sort::ValueType | Sort::CompType => Position::Type,
            Sort::Value | Sort::Computation => Position::Term,
        })
    }));
    while let Some((index, position)) = queue.pop_front() {
        let (Some(marks), Some(node)) = (
            reached.get_mut(usize::from(index)),
            content.nodes().get(usize::from(index)),
        )
        else {
            continue;
        };
        let position = match node.sort() {
            Sort::ValueType | Sort::CompType => Position::Type,
            Sort::Value | Sort::Computation => position,
        };
        let mark = match position {
            Position::Term => marks.first_mut(),
            Position::Type => marks.last_mut(),
        };
        match mark {
            Some(&mut true) | None => continue,
            Some(mark) => *mark = true,
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
        hole: match *(content.declaration()) {
            crate::content::DeclarationRoots::Value {
                body: Maybe::Absent(body::Absent::Hole),
                ..
            } => HoleMark::Hole,
            crate::content::DeclarationRoots::Value {
                body: Maybe::Present(_),
                ..
            }
            | crate::content::DeclarationRoots::Data(_)
            | crate::content::DeclarationRoots::Abstract(_)
            | crate::content::DeclarationRoots::World => HoleMark::Filled,
        },
    }
}

#[cfg(test)]
mod tests;
