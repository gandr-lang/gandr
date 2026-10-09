//! The named-kind inventory: how each named node kind of the surface's
//! tree-sitter grammar is realised by this grammar.
//!
//! Named kinds are not grammar semantics: forms range over tiles and holes
//! only. A kind is realised either by structural forms, the rules whose
//! provenance is the kind's name, or, for the file root alone, by the
//! top-level item sequence. The inventory is the table an editor-facing
//! grammar is checked against; it never defines the tile vocabulary.
//!
//! The kinds only this grammar has — `data` and `codata` declarations,
//! `def rec` with copatterns, the loop forms, `import`, operator-fixity
//! declarations, and their reserved members — are listed apart in
//! [`PBG_ONLY_KINDS`](crate::PBG_ONLY_KINDS), so [`named_kind_parity`] never
//! enumerates them. The two lists are disjoint.

use alloc::vec::Vec;

use crate::surface::TREE_SITTER_NAMED_KINDS;

/// The named kinds the file root realises rather than a structural form.
const FILE_ROOT_KINDS: &[&str] = &["source_file"];

/// How a named kind is realised.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NamedKindRealization
{
    /// By the structural rules whose provenance is the kind's name.
    StructuralForms,
    /// By the file root: the top-level item sequence.
    FileRoot,
}

/// One row of the named-kind inventory.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NamedKindEntry
{
    /// The named kind.
    pub kind: &'static str,
    /// How the kind is realised.
    pub realization: NamedKindRealization,
}

/// A named kind's text.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NamedKind<'kind>(pub &'kind str);

/// Classifies how a named kind is realised.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the file root's kind is [`NamedKindRealization::FileRoot`]; every
///   other kind, an unknown one included, is
///   [`NamedKindRealization::StructuralForms`].
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 generative — every inventoried kind classified this way is
///   realised: the file root by the item sequence, every other kind by a
///   checked form with its provenance.
/// - witness: `tests::surface::named_kind_coverage_is_semantic`
#[inline]
#[must_use]
pub fn named_kind_realization(kind: NamedKind<'_>) -> NamedKindRealization
{
    if FILE_ROOT_KINDS.contains(&kind.0) {
        NamedKindRealization::FileRoot
    }
    else {
        NamedKindRealization::StructuralForms
    }
}

/// The named-kind inventory, in [`TREE_SITTER_NAMED_KINDS`] order.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one entry per kind of [`TREE_SITTER_NAMED_KINDS`], in order, each
///   classified by [`named_kind_realization`].
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 generative — the inventory is exactly the committed kind
///   list, and every entry is realised as classified.
/// - witness: `tests::surface::named_kind_coverage_is_semantic`
#[inline]
#[must_use]
pub fn named_kind_parity() -> Vec<NamedKindEntry>
{
    TREE_SITTER_NAMED_KINDS
        .iter()
        .map(|kind| NamedKindEntry {
            kind,
            realization: named_kind_realization(NamedKind(kind)),
        })
        .collect()
}
