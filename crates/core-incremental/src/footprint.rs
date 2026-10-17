//! The conservative footprint: what an item's terms mention, read off the
//! roots of its content table.
//!
//! # Read off the roots, not scanned
//!
//! The footprint over-approximates: every reference anywhere in the item is a
//! read, whether or not the judgement would reach it. It answers one question
//! the support cannot: which items read a definition whose value changed, so
//! the change can be closed over readers that never consulted a type. A
//! variable is never a read — it is an index into the item's own binders — so
//! shadowing cannot hide a read or invent one. The references in type
//! positions, the signature and anything under a type former, are the item's
//! type support, kept apart because a value change reaches an item's typing
//! only through them.
//!
//! Every node of the table carries the references beneath it, in value and
//! in type positions, built bottom-up when the table is factored and rebuilt
//! by the reader of a persisted one. The footprint is their union over the
//! declaration's roots: a type-sorted root's reads are all type reads, a
//! term root's value reads are reads in term positions. No walk of the table
//! is needed, so the footprint costs one union per root whatever the table's
//! size.

use alloc::collections::BTreeSet;

use anodized::spec;
use gandr_core_checker::body;
use quenchant_shape::shape::Maybe;

use crate::content::ItemContent;
use crate::content::Opacity;
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
/// - ensures: the type reads read off the roots are a subset of the reads, with
///   opacity and body-presence marks matching that content.
/// - provides: inspectable read sets; a stored footprint is not evidence for
///   adopting a checkpoint.
/// - panics: none.
/// - executable: none — the source content and the provenance of stored
///   metadata are external; [`footprint_of`] checks its own return boundary.
///
/// # Adequacy
/// - hypothesis: L3 — bound and free variables, shared type/term nodes,
///   unreachable nodes and body-presence boundaries distinguish incorrect sets
///   and marks by exact values. A corrupted stored footprint is separately
///   shown not to control adoption. Reassembled metadata is not certified by
///   the data declaration.
/// - witness: `footprint::tests::shadowed_binder_is_not_a_read`
/// - witness: `footprint::tests::free_occurrence_under_binders_is_read`
/// - witness: `footprint::tests::a_term_position_does_not_suppress_a_type_position`
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

/// The footprint of `content`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the reads are every reference beneath a root, in value or type
///   position; the type reads are those beneath a type-sorted root and those
///   beneath a type former under a term root. The item is opaque exactly when
///   [`ItemContent::opacity`] says so; the hole mark is set exactly when the
///   body is a hole.
/// - provides: the read relation the value-changed closure runs over.
/// - panics: none.
/// - intension: one union per root over the references the roots carry; no node
///   of the table is visited.
///
/// # Adequacy
/// - hypothesis: L2 — an independent walk of the arena, sharing no code with
///   the table, agrees with the read-off on generated programs over the
///   generator's vocabulary: literals, constants, holes, thunks of returns,
///   base, thunk and returner types and codes; L3 — bound variables, free
///   references under binders, signatures, a node shared by a term and a type
///   position and a quoted abstract type distinguish false reads and lost type
///   positions by exact sets.
/// - witness: `tests::supports::carried_footprint_matches_reference_walk`
/// - witness: `footprint::tests::shadowed_binder_is_not_a_read`
/// - witness: `footprint::tests::free_occurrence_under_binders_is_read`
/// - witness: `footprint::tests::hole_sets_has_hole`
/// - witness: `footprint::tests::ascription_names_are_reads`
/// - witness: `footprint::tests::type_support_holds_only_type_positions`
/// - witness: `footprint::tests::a_term_position_does_not_suppress_a_type_position`
/// - witness: `footprint::tests::a_quoted_abstract_type_reads_its_own_reference_in_type_position`
/// - witness: `footprint::tests::bounded_tables_separate_reachability_opacity_and_holes`
#[spec(ensures: |ret| ret.type_reads.is_subset(&ret.reads)
    && ret.opacity == content.opacity()
    && content.declaration().iter().all(|(root, _)| content.nodes().get(usize::from(root)).is_none_or(|node|
        node.value_reads().chain(node.type_reads()).all(|read| ret.reads.contains(read))
        && node.type_reads().all(|read| ret.type_reads.contains(read))))
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
    for (root, _) in content.declaration().iter() {
        let Some(node) = content.nodes().get(usize::from(root))
        else {
            continue;
        };
        reads.extend(node.value_reads().cloned());
        reads.extend(node.type_reads().cloned());
        type_reads.extend(node.type_reads().cloned());
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
