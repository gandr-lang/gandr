//! The **concrete syntax tree of the gandr surface**: the molded node
//! vocabulary, byte spans, and a flat level-order arena whose every node
//! carries an arena position and, below the root, a cross-tree key.
//!
//! - [`NodeLabel`] is what a node is: a form or a tile named by its mold, grout
//!   a parser inserted, layout, or the root.
//! - [`TreeBuilder`] stages nodes bottom-up and finishes them into a
//!   [`SyntaxTree`], whose children are a contiguous range of strictly higher
//!   positions.
//! - [`NodeIndex`] addresses a node inside one tree; [`NodeKey`] addresses it
//!   across trees, runs and processes: the [`NodeDigest`] of its top-level
//!   form, hashed once as [`TreeBuilder::finish`] lays the tree out, and its
//!   rank in that form.
//! - [`SourceText`], [`ByteSpan`] and [`SourceFragment`] are byte-addressed
//!   source positions; [`SyntaxError`] is every refusal.
//! - [`MoldId`], [`GroutSort`], [`GroutShape`], [`GrammarFingerprint`] and
//!   [`ClosingClass`] are the grammar-facing references a molded tree carries;
//!   the grammar owns the tables they index.
//!
//! The crate holds **representation only**: it lexes and parses nothing, and
//! reads a source only to answer what a span covers. Its one target requirement
//! is an atomic compare-exchange, `target_has_atomic = "ptr"`, which the
//! process-wide builder-identity counter needs. The design is stated in this
//! crate's `README.md`, § Synopsis, and in each module's documentation.
//!
//! # Specification attributes
//!
//! Each nontrivial item's `# Specification` is paired with `# Adequacy`: the
//! input boundaries, observable results, fault classes and same-crate
//! witnesses. Executable `#[spec(...)]` clauses cover source slicing and
//! refusal precedence, delimiter recognition, checked identifiers, builder
//! transitions and arena walks. Enforcement captures scalar pre-state where an
//! operation consumes or mutates its inputs; it does not copy the staging arena
//! or repeat hashing.
//!
//! Constant functions use direct const-compatible predicates. The node
//! constructor checks every offered part; layout adoption checks source,
//! grammar and child-range geometry. Exact preservation of the moved node
//! vector remains covered by witnesses because const specifications do not
//! capture pre-state. Formatters expose a write-only sink; hashing's provenance
//! and cross-call identity laws need independent witnesses rather than a
//! repeated hash; type-level obligations are witnessed at construction and
//! observation boundaries. These items state their remaining non-executable
//! reasons. Run the suite both normally and with `--cfg anodized_panic` using
//! the commands above.
//!
//! # References
//!
//! - Jack O'Connor, Jean-Philippe Aumasson, Samuel Neves and Zooko
//!   Wilcox-O'Hearn. "BLAKE3: one function, fast everywhere." Specification, 9
//!   January 2020.
//!   <https://github.com/BLAKE3-team/BLAKE3-specs/blob/master/blake3.pdf> — the
//!   hash a form digest is.
//! - David Moon, Andrew Blinn, Thomas J. Porter and Cyrus Omar. "Syntactic
//!   Completions with Material Obligations." _Proceedings of the ACM on
//!   Programming Languages_ 9, OOPSLA2 (2025).
//!   <https://doi.org/10.1145/3763182>, arXiv:2508.16848 — molds, grout and the
//!   material a tree records.

// Module documentation that predates the shape lint: 23 headings outside the
// vocabulary and 3 decision records. Each allow leaves with the rewrite that
// clears its count.
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    allow(
        module_doc_heading,
        doc_decision_record,
        reason = "module documentation that predates the shape lint"
    )
)]
#![no_std]

#[cfg(not(target_has_atomic = "ptr"))]
compile_error!(
    "gandr-surface-syntax requires a target with atomic compare-exchange \
     (target_has_atomic = \"ptr\"): builder identities are minted from a \
     shared atomic counter"
);

extern crate alloc;

mod build;
mod digest;
mod error;
mod key;
mod label;
mod mold;
mod span;
mod tree;

pub use crate::build::StagedId;
pub use crate::build::TreeBuilder;
pub use crate::digest::NODE_DIGEST_LEN;
pub use crate::digest::NodeDigest;
pub use crate::error::SyntaxError;
pub use crate::key::FormRank;
pub use crate::key::NodeKey;
pub use crate::label::CarriesText;
pub use crate::label::LabelTag;
pub use crate::label::NodeLabel;
pub use crate::label::Significance;
pub use crate::mold::ClosingClass;
pub use crate::mold::DelimSpelling;
pub use crate::mold::GrammarFingerprint;
pub use crate::mold::GroutShape;
pub use crate::mold::GroutSort;
pub use crate::mold::MoldId;
pub use crate::span::ByteLength;
pub use crate::span::ByteOffset;
pub use crate::span::ByteSpan;
pub use crate::span::SourceFragment;
pub use crate::span::SourceText;
pub use crate::tree::ChildCount;
pub use crate::tree::Node;
pub use crate::tree::NodeCount;
pub use crate::tree::NodeIndex;
pub use crate::tree::NodeIndices;
pub use crate::tree::SyntaxTree;

/// Equality observed without invoking a non-const trait method.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ConstEquality
{
    /// Both represented values agree.
    Equal,
    /// The represented values differ.
    Unequal,
}

#[cfg(test)]
mod test_support
{
    /// A formatter destination that rejects every write.
    pub struct RefusingSink;

    impl core::fmt::Write for RefusingSink
    {
        /// Refuse the supplied fragment.
        ///
        /// # Specification
        /// trivial.
        #[inline]
        fn write_str(
            &mut self,
            _text: &str,
        ) -> core::fmt::Result
        {
            Err(core::fmt::Error)
        }
    }
}
