//! Flat trees: the one representation every recursive datum of the crate is
//! held in.
//!
//! A code, a symbolic type reference, a free term and a generic value payload
//! are all trees, and none of them routes ownership through itself. Each is
//! one flat table in reverse pre-order: every subtree is a contiguous range
//! ending at its own root, every entry carries the node count of the subtree
//! it roots, and the root is held apart so a tree is never empty. A child is
//! found by skipping its elder siblings' ranges, a subtree is read or copied
//! as one slice, and building an application reuses its last argument's
//! buffer. No walk over a table recurses, and dropping one frees one vector.

use alloc::vec::Vec;
use core::iter;

use quenchant_shape::shape::Maybe;

quenchant_shape::reason_enum! {
    /// Why a leaf has no image under a leaf replacement.
    pub(crate) mod leaf_image {
        /// The reason the leaf has no image.
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub(crate) enum Absent {
            /// The replacement leaves this leaf as it is.
            Kept,
        }
    }
}

/// The number of children a tree node has.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ArgumentCount(usize);

impl From<usize> for ArgumentCount
{
    /// Wraps the primitive.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: usize) -> Self
    {
        Self(value)
    }
}

impl From<ArgumentCount> for usize
{
    /// Unwraps the primitive.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: ArgumentCount) -> Self
    {
        value.0
    }
}

/// The node count of a subtree, its root included.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Extent(usize);

impl Extent
{
    /// The extent of a single node.
    const ONE: Self = Self(1);

    /// The sum of two extents.
    ///
    /// # Specification
    /// - ensures: the exact sum whenever it is representable; otherwise
    ///   `usize::MAX`. A count of nodes held in memory never reaches that
    ///   bound, so every sum the crate forms is exact.
    /// - panics: none.
    #[inline]
    const fn saturating_add(
        self,
        rhs: Self,
    ) -> Self
    {
        Self(self.0.saturating_add(rhs.0))
    }
}

impl From<Extent> for usize
{
    /// Unwraps the primitive.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: Extent) -> Self
    {
        value.0
    }
}

/// What a node is, and how many children follow it in its table.
pub trait Head
{
    /// The node's number of children.
    ///
    /// # Specification
    /// trivial.
    fn arity(&self) -> ArgumentCount;
}

/// One node of a table: its head and the node count of the subtree it roots.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Entry<H>
{
    /// The node's head.
    head: H,
    /// The node count of the subtree this node roots, itself included.
    extent: Extent,
}

/// A tree held as one flat table in reverse pre-order, its root apart.
///
/// Two trees are structurally equal exactly when their tables are equal: the
/// layout is canonical, so the derived equality and hash are structural.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Tree<H>
{
    /// Every node below the root, in reverse pre-order.
    below: Vec<Entry<H>>,
    /// The root node.
    root: Entry<H>,
}

impl<H> Tree<H>
{
    /// A one-node tree.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn leaf(head: H) -> Self
    {
        Self {
            below: Vec::new(),
            root: Entry {
                head,
                extent: Extent::ONE,
            },
        }
    }

    /// A tree whose root is `head` over `children`, left to right.
    ///
    /// # Specification
    /// - requires: `head`'s arity is the number of `children`; every caller
    ///   computes the head from the children it passes.
    /// - ensures: the tree whose root is `head` and whose children are
    ///   `children` in order; the last child's table is reused as the new
    ///   table's buffer, so wrapping one child costs one appended node.
    /// - panics: none.
    #[inline]
    pub(crate) fn node(
        head: H,
        children: Vec<Self>,
    ) -> Self
    {
        let mut children = children;
        let mut below = match children.pop() {
            | Some(last) => {
                let mut below = last.below;
                below.push(last.root);
                below
            },
            | None => Vec::new(),
        };
        for child in children.into_iter().rev() {
            below.extend(child.below);
            below.push(child.root);
        }
        let extent = Extent(below.len()).saturating_add(Extent::ONE);
        Self {
            below,
            root: Entry { head, extent },
        }
    }

    /// The tree as a borrowed subtree.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn to_ref(&self) -> TreeRef<'_, H>
    {
        TreeRef {
            below: &self.below,
            root: &self.root,
        }
    }

    /// Every head of the tree, in table order: each node after its whole
    /// subtree, the root last.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn heads(&self) -> impl Iterator<Item = &H>
    {
        self.below
            .iter()
            .chain(iter::once(&self.root))
            .map(|entry| &entry.head)
    }
}

/// A borrowed subtree: a contiguous range of a table and its root.
#[derive(Debug)]
pub struct TreeRef<'tree, H>
{
    /// Every node below the root, in reverse pre-order.
    below: &'tree [Entry<H>],
    /// The subtree's root.
    root: &'tree Entry<H>,
}

impl<H> Clone for TreeRef<'_, H>
{
    /// Copies the borrow.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn clone(&self) -> Self
    {
        *self
    }
}

impl<H> Copy for TreeRef<'_, H>
{
}

impl<H> PartialEq for TreeRef<'_, H>
where
    H: PartialEq,
{
    /// Structural equality of the two subtrees.
    ///
    /// # Specification
    /// - ensures: positive exactly when the two table ranges and roots are
    ///   equal entry for entry, which for canonical tables is structural
    ///   equality.
    /// - panics: none.
    #[inline]
    fn eq(
        &self,
        other: &Self,
    ) -> bool
    {
        self.below == other.below && self.root == other.root
    }
}

impl<H> Eq for TreeRef<'_, H> where H: Eq
{
}

impl<'tree, H> TreeRef<'tree, H>
{
    /// The subtree's root head.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn head(self) -> &'tree H
    {
        &self.root.head
    }

    /// The subtree's node count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn size(self) -> Extent
    {
        self.root.extent
    }

    /// Every head of the subtree, root first, in pre-order.
    ///
    /// # Specification
    /// - ensures: one item per node, in pre-order: the root, then each child's
    ///   subtree in pre-order, left to right; so leaves are met left to right.
    /// - panics: none.
    #[inline]
    pub(crate) fn preorder(self) -> impl Iterator<Item = &'tree H>
    {
        iter::once(self.root)
            .chain(self.below.iter().rev())
            .map(|entry| &entry.head)
    }

    /// An owned copy of the subtree.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn to_tree(self) -> Tree<H>
    where
        H: Clone,
    {
        Tree {
            below: self.below.to_vec(),
            root: self.root.clone(),
        }
    }
}

impl<'tree, H> TreeRef<'tree, H>
where
    H: Head,
{
    /// The subtree's children, left to right.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn children(self) -> Children<'tree, H>
    {
        Children {
            rest: self.below,
            remaining: self.root.head.arity(),
        }
    }

    /// The subtree with each leaf `image` answers for replaced by its image.
    ///
    /// # Specification
    /// - ensures: the table rebuilt in index order: each answered leaf's image
    ///   is appended whole and each inner node's extent is one plus its
    ///   children's, which precede it; every other node is copied. The images
    ///   are inserted as given, in one pass.
    /// - panics: none.
    /// - intension: one output table; the pending child extents are a stack,
    ///   claimed by their parent as it is reached.
    #[inline]
    pub(crate) fn replace_leaves<'image, I>(
        self,
        mut image: I,
    ) -> Tree<H>
    where
        H: Clone + 'image,
        I: FnMut(&H) -> Maybe<TreeRef<'image, H>, leaf_image::Absent>,
    {
        let mut below: Vec<Entry<H>> = Vec::with_capacity(self.below.len());
        // The extents of the completed subtrees not yet claimed by a parent,
        // the most recent last.
        let mut completed: Vec<Extent> = Vec::new();
        for entry in self.below {
            let arity = usize::from(entry.head.arity());
            if arity == 0 {
                match image(&entry.head) {
                    | Maybe::Present(replacement) => {
                        below.extend(replacement.below.iter().cloned());
                        below.push(replacement.root.clone());
                        completed.push(replacement.size());
                    },
                    | Maybe::Absent(_) => {
                        below.push(entry.clone());
                        completed.push(Extent::ONE);
                    },
                }
                continue;
            }
            let first = completed.len().saturating_sub(arity);
            let extent = completed
                .drain(first ..)
                .fold(Extent::ONE, Extent::saturating_add);
            below.push(Entry {
                head: entry.head.clone(),
                extent,
            });
            completed.push(extent);
        }
        if usize::from(self.root.head.arity()) == 0 {
            return match image(&self.root.head) {
                | Maybe::Present(replacement) => replacement.to_tree(),
                | Maybe::Absent(_) => self.to_tree(),
            };
        }
        let extent = Extent(below.len()).saturating_add(Extent::ONE);
        Tree {
            below,
            root: Entry {
                head: self.root.head.clone(),
                extent,
            },
        }
    }
}

/// The children of a node, left to right.
#[derive(Debug)]
pub struct Children<'tree, H>
{
    /// The table range holding the children not yet yielded, the next one
    /// last.
    rest: &'tree [Entry<H>],
    /// How many children remain.
    remaining: ArgumentCount,
}

impl<H> Clone for Children<'_, H>
{
    /// Copies the cursor.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn clone(&self) -> Self
    {
        Self {
            rest: self.rest,
            remaining: self.remaining,
        }
    }
}

impl<'tree, H> Iterator for Children<'tree, H>
{
    type Item = TreeRef<'tree, H>;

    /// The next child.
    ///
    /// # Specification
    /// - ensures: yields the remaining children in left-to-right order; the
    ///   next child's root is the last node of `rest`, and its subtree the
    ///   `extent` nodes ending there. A range shorter than the extents it
    ///   records ends the iteration.
    /// - panics: none.
    #[inline]
    fn next(&mut self) -> Option<Self::Item>
    {
        if self.remaining.0 == 0 {
            return None;
        }
        let (root, before) = self.rest.split_last()?;
        let below_len = root.extent.0.checked_sub(1)?;
        let split = before.len().checked_sub(below_len)?;
        let (rest, below) = before.split_at_checked(split)?;
        self.rest = rest;
        self.remaining = ArgumentCount(self.remaining.0.saturating_sub(1));
        Some(TreeRef { below, root })
    }

    /// The exact number of remaining children.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>)
    {
        (self.remaining.0, Some(self.remaining.0))
    }
}

impl<H> ExactSizeIterator for Children<'_, H>
{
}
