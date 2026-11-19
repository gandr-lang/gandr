//! The cross-tree identity of a node inside a form, [`NodeKey`]: the content
//! digest of the top-level form that holds it and its rank among that form's
//! significant nodes.
//!
//! # Why a form and a rank
//!
//! A side table that outlives one parse needs a key an edit elsewhere in the
//! file leaves alone. A top-level form's digest is such a key for the form, and
//! a rank inside the form extends it to every node the form holds: an edit to
//! another form changes neither, and an edit inside the form changes the
//! form's digest and so every key under it, which is exactly the set a
//! consumer re-derives when that form is lowered again. Layout and
//! documentation take no rank, so reformatting or re-documenting a form moves
//! no key.
//!
//! # Node keys
//!
//! A table that outlives one parse files a node under its `NodeKey`: the digest
//! of the top-level form holding it — a significant child of the root — and its
//! rank among that form's significant nodes in preorder, the form's own root
//! ranked zero. Layout, documentation and what they hold take no rank and have
//! no key, and neither does the root; the whole tree's identity is
//! `SyntaxTree::digest`. An edit to another form, to layout or to documentation
//! leaves a key alone; an edit inside the form changes the form's digest and so
//! every key under it, which is the set a consumer derives again when that form
//! is lowered again. `TreeBuilder::finish` ranks and digests the forms in one
//! walk, so `SyntaxTree::key` answers without one.
//!
//! - Choice: the form's digest and a rank. Only top-level forms need an
//!   identity at commit; a node inside one is found by its position in the
//!   form.
//! - Alternatives: the node's own digest, which needs a digest at every node
//!   and cannot tell apart two equal nodes in one form; an arena position,
//!   which an edit anywhere earlier in the file invalidates.
//! - Reversal: a consumer that needs a node's identity apart from its form's —
//!   reuse of a sub-form's work across a move — needs a digest of the node
//!   itself.

use crate::digest::NodeDigest;

/// A node's position among the significant nodes of its top-level form, in
/// preorder, the form's own root first.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FormRank(u32);

impl From<u32> for FormRank
{
    /// Read a preorder rank.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(rank: u32) -> Self
    {
        Self(rank)
    }
}

impl From<FormRank> for u32
{
    /// Read the rank back out.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(rank: FormRank) -> Self
    {
        rank.0
    }
}

/// The identity of one significant node across trees, runs and processes: the
/// digest of the top-level form holding it and its rank inside that form.
///
/// # Specification
/// - requires: nothing; the type is a carrier and admits any pair.
/// - ensures: two keys are equal exactly when their form digests and ranks are;
///   the order compares the form digest first.
/// - provides: the key every table that outlives one parse files a node under.
/// - fails: never.
/// - panics: none.
/// - executable: none — a carrier with no invariant beyond its fields.
///
/// # Adequacy
/// - hypothesis: L3 — keys read from parsed trees separate a node from its
///   form's other nodes, survive layout and documentation edits and an edit to
///   another form, and change with an edit inside the form.
/// - witness: `key::tests::a_key_names_its_form_and_rank`
/// - witness: `build::tests::keys_survive_layout_and_another_forms_edit`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct NodeKey
{
    /// The digest of the top-level form holding the node.
    form: NodeDigest,
    /// The node's rank among the form's significant nodes.
    rank: FormRank,
}

impl NodeKey
{
    /// The key of the node at `rank` in the form whose digest is `form`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        form: NodeDigest,
        rank: FormRank,
    ) -> Self
    {
        Self { form, rank }
    }

    /// The digest of the top-level form holding the node.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn form(&self) -> NodeDigest
    {
        self.form
    }

    /// The node's rank among its form's significant nodes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn rank(&self) -> FormRank
    {
        self.rank
    }
}

#[cfg(test)]
mod tests
{
    use super::FormRank;
    use super::NodeKey;
    use crate::digest::NodeDigest;

    #[test]
    fn a_key_names_its_form_and_rank()
    {
        let form = NodeDigest::from([3_u8; 32_usize]);
        let other = NodeDigest::from([4_u8; 32_usize]);
        let key = NodeKey::new(form, FormRank::from(2_u32));
        assert_eq!(key.form(), form);
        assert_eq!(u32::from(key.rank()), 2_u32);
        assert_ne!(key, NodeKey::new(form, FormRank::from(1_u32)));
        assert_ne!(key, NodeKey::new(other, FormRank::from(2_u32)));
        assert!(
            NodeKey::new(form, FormRank::from(9_u32)) < NodeKey::new(other, FormRank::from(0_u32)),
            "the form digest orders before the rank"
        );
    }
}
