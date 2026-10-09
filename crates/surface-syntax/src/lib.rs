//! The **concrete syntax tree of the gandr surface**: the molded node
//! vocabulary, byte spans, and a flat level-order arena whose every node
//! carries an arena position and a content digest.
//!
//! - [`NodeLabel`] is what a node is: a form or a tile named by its mold, grout
//!   a parser inserted, layout, or the root.
//! - [`TreeBuilder`] stages nodes bottom-up and finishes them into a
//!   [`SyntaxTree`], whose children are a contiguous range of strictly higher
//!   positions.
//! - [`NodeIndex`] addresses a node inside one tree; [`NodeDigest`] addresses
//!   it across trees, runs and processes.
//! - [`SourceText`], [`ByteSpan`] and [`SourceFragment`] are byte-addressed
//!   source positions; [`SyntaxError`] is every refusal.
//! - [`MoldId`], [`GroutSort`], [`GroutShape`], [`GrammarFingerprint`] and
//!   [`ClosingClass`] are the grammar-facing references a molded tree carries;
//!   the grammar owns the tables they index.
//!
//! The crate holds **representation only**: it lexes and parses nothing, and
//! reads a source only to answer what a span covers. Its one target
//! requirement is an atomic compare-exchange, `target_has_atomic = "ptr"`,
//! which the process-wide builder-identity counter needs. The design is stated
//! in this crate's `README.md`, § Synopsis, and in the sections it links.

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
mod label;
mod mold;
mod span;
mod tree;

pub use crate::build::StagedId;
pub use crate::build::TreeBuilder;
pub use crate::digest::NODE_DIGEST_LEN;
pub use crate::digest::NodeDigest;
pub use crate::error::SyntaxError;
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
