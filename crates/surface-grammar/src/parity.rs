//! The named-kind inventory: how each named node kind of the surface's
//! tree-sitter grammar is realised by this grammar.
//!
//! Named kinds are not grammar semantics: forms range over tiles and holes
//! only. A kind is realised by structural forms, the rules whose provenance
//! is the kind's name; for the file root, by the top-level item sequence; or,
//! for a comment or a shebang, by the labeler, which reads it as layout
//! between tokens, so no form holds one. The inventory is the table an
//! editor-facing grammar is checked against; it never defines the tile
//! vocabulary.
//!
//! The kinds only this grammar has — `data` and `codata` declarations,
//! `def rec` with copatterns, the loop forms, `import`, operator-fixity
//! declarations, and their reserved members — are listed apart in
//! [`PBG_ONLY_KINDS`](crate::PBG_ONLY_KINDS), so [`named_kind_parity`] never
//! enumerates them. The two lists are disjoint.
//!
//! # Named-kind inventory
//!
//! `TREE_SITTER_NAMED_KINDS` lists, ascending, the 124 named node kinds of the
//! surface's tree-sitter grammar; `PBG_ONLY_KINDS` lists the kinds only this
//! grammar has, disjoint from them. `named_kind_parity` classifies every listed
//! kind: `source_file` is the file root, realised by the item forms; the
//! comments and the shebang are layout; and every other kind is realised by a
//! rule's provenance or an adaptation's surface form. A kind is never grammar
//! semantics: forms range over tiles and holes only, and the inventory is how
//! coverage of the named kinds is checked.
//!
//! A molded syntax tree names each form and tile by its `MoldId`;
//! `Pbg::named_kind` reads the kind back as the provenance of the rule the mold
//! was numbered for. The table records each mold's rule as it numbers the
//! molds, so the lookup is total over the table and refuses only an id past it,
//! as `Pbg::mold` does. The record is not folded into the fingerprint, which
//! keys the mold table a parser reads: two grammars with one mold table and
//! different rule provenance share a fingerprint, so a consumer reads kinds
//! from the grammar it holds, after checking the tree's fingerprint against it.
//! Reversal: fold each mold's provenance into the fingerprint once a consumer
//! keys stored kinds by fingerprint alone.

use alloc::vec::Vec;

use anodized::spec;

use crate::surface::TREE_SITTER_NAMED_KINDS;

/// How a named kind is realised.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NamedKindRealization
{
    /// By the structural rules whose provenance is the kind's name.
    StructuralForms,
    /// By the file root: the top-level item sequence.
    FileRoot,
    /// By the labeler: trivia between tokens, which no form holds.
    Layout,
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
/// - ensures: the file root's kind is [`NamedKindRealization::FileRoot`]; the
///   comments' and the shebang's are [`NamedKindRealization::Layout`]; every
///   other kind, an unknown one included, is
///   [`NamedKindRealization::StructuralForms`].
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: Across the committed kind inventory and explicit known,
///   unknown and near-root spellings, L3 classification and semantic
///   realization observations catch accidental file-root or layout aliases and
///   missing structural coverage; arbitrary user text is not exhausted.
/// - witness: `tests::surface::named_kind_coverage_is_semantic`
#[spec(ensures: |ret| ret == match kind.0 { "source_file" => NamedKindRealization::FileRoot, "block_comment" | "line_comment" | "shebang" => NamedKindRealization::Layout, _ => NamedKindRealization::StructuralForms })]
#[inline]
#[must_use]
pub fn named_kind_realization(kind: NamedKind<'_>) -> NamedKindRealization
{
    match kind.0 {
        "source_file" => NamedKindRealization::FileRoot,
        "block_comment" | "line_comment" | "shebang" => NamedKindRealization::Layout,
        _ => NamedKindRealization::StructuralForms,
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
/// - hypothesis: The complete committed inventory is an L2 finite census:
///   order, uniqueness, disjoint grammar-only kinds and realization
///   observations catch dropped, duplicated or misclassified entries; this does
///   not establish parser language equivalence.
/// - witness: `tests::surface::named_kind_coverage_is_semantic`
#[spec(ensures: |ret| ret.len() == TREE_SITTER_NAMED_KINDS.len() && ret.iter().zip(TREE_SITTER_NAMED_KINDS.iter()).all(|(entry, &kind)| entry.kind == kind && entry.realization == named_kind_realization(NamedKind(kind))))]
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
