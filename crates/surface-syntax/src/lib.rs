//! The **concrete syntax tree of the gandr surface**: the closed token
//! vocabulary, the closed node vocabulary, a flat node arena whose children are
//! an index range, byte spans, and the two identities every node carries.
//!
//! The crate holds **representation only**. There is no lexer here and no
//! parser; both consume this vocabulary rather than living in it, and nothing
//! here reads a source except to answer what a span covers.
//!
//! # Four decisions that interlock
//!
//! **The node carries its kind.** A form-name-free tree makes every consumer
//! re-derive the form from the children it happens to have; the lowering above
//! this one dispatches on forms, so the tree names them and the read adapter
//! that would otherwise sit between them never exists.
//!
//! **Children are a contiguous range of arena positions**, which costs two
//! fields per node and no second vector, and which is why the layout is
//! level-order: a children-before-parents arena cannot give a node's children a
//! contiguous range at all.
//!
//! **Level order gives parent-before-child**, so a walk in ascending position
//! order needs no stack, an index comparison decides ancestry direction, and a
//! cycle is unrepresentable rather than checked for.
//!
//! **The digest is computed while staging**, over the children's digests rather
//! than over their positions, which is what makes it survive the layout the
//! third decision imposes.
//!
//! # Two identities, and the distinction is load-bearing
//!
//! A node's [`NodeIndex`] addresses it inside one tree and nowhere else: the
//! next parse of an edited source lays the same declaration out at a different
//! position. A node's [`NodeDigest`] addresses it across trees, runs and
//! processes: it is a function of the node's form and content and of nothing
//! else, so the same declaration parsed from two files in two processes carries
//! one identity.
//!
//! Diagnostics and the origin table carry both. A side table keyed by position
//! is invalidated by an edit anywhere earlier in the file; a side table keyed
//! by digest is invalidated only by an edit to the thing it is about, which is
//! what makes the digest the key an attribute side table or a later checkpoint
//! wants.
//!
//! A digest is a *content* identity, not an occurrence identity: two
//! declarations with identical content have one digest, so a consumer keying on
//! it owes itself the argument that its declarations are distinct. In the
//! surface fragment they are — a declaration's digest folds its name, and a
//! module binding one name twice is refused above this crate — but the
//! obligation belongs to the consumer, and this crate states the identity
//! rather than assuming the use.
//!
//! # What the tree deliberately does not carry
//!
//! No trivia and no punctuation node. Whitespace is skipped by the lexer, and a
//! token whose presence the parent's kind determines — a signature's colon, a
//! lambda's dot — is recovered from the kind rather than stored. A grouping is
//! the one exception, because `(x)` and `x` differ in the token stream and in
//! nothing else, and the round-trip that compares a re-rendered stream against
//! the lexer's own is the reason the token vocabulary lives beside the tree.
//!
//! No attribute is a child of the declaration it decorates. An attribute block
//! is a child of the module, in source order, which is what keeps a
//! declaration's identity — the key its attribute side-table entry is filed
//! under — unchanged by attaching, editing or removing an attribute.
//!
//! # Target requirement
//!
//! A builder's identity is drawn from a process-wide atomic counter, so a
//! staged handle from one builder is rejected by another instead of silently
//! resolving against it. That counter needs an atomic compare-exchange, which
//! is the crate's only target requirement: `target_has_atomic = "ptr"`. Every
//! hosted target and every embedded target with a compare-exchange instruction
//! qualifies; load/store-only cores do not, and building for one fails with an
//! explanatory message rather than a missing-type error.
//!
//! The named ideas, the crate's status, and its plan-milestone mapping are in
//! this crate's `README.md`.

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
mod kind;
mod span;
mod token;
mod tree;

pub use crate::build::StagedId;
pub use crate::build::TreeBuilder;
pub use crate::digest::NODE_DIGEST_LEN;
pub use crate::digest::NodeDigest;
pub use crate::error::SyntaxError;
pub use crate::kind::CarriesText;
pub use crate::kind::KindTag;
pub use crate::kind::NodeKind;
pub use crate::span::ByteLength;
pub use crate::span::ByteOffset;
pub use crate::span::ByteSpan;
pub use crate::span::SourceFragment;
pub use crate::span::SourceText;
pub use crate::token::Token;
pub use crate::token::TokenKind;
pub use crate::token::TokenSpelling;
pub use crate::tree::ChildCount;
pub use crate::tree::Node;
pub use crate::tree::NodeCount;
pub use crate::tree::NodeIndex;
pub use crate::tree::NodeIndices;
pub use crate::tree::SyntaxTree;
