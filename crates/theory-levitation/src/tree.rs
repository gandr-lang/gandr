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

use anodized::spec;
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — exact results at zero, below the ceiling, at the
    ///   ceiling and beyond it distinguish wrapping, truncation and an early
    ///   saturation boundary on representable extent pairs, in both const
    ///   evaluation and runtime calls.
    /// - witness: `tree::tests::extent_addition_saturates_at_usize_boundary`
    #[spec(ensures: |ret| ret.0 == self.0.saturating_add(rhs.0))]
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
    pub const fn leaf(head: H) -> Self
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero, one and two children, including asymmetric
    ///   nesting, are observed through exact child and preorder sequences;
    ///   reversal, omission and incorrect subtree extents change those reads.
    /// - witness: `tree::tests::tree_children_and_preorder_preserve_asymmetric_structure`
    #[inline]
    #[spec(
        captures: descendants = children.iter().fold(0_usize, |count, child| {
            count.saturating_add(child.below.len()).saturating_add(1)
        }),
        ensures: |ref tree| tree.below.len() == descendants
            && tree.root.extent.0 == descendants.saturating_add(1),
    )]
    pub fn node(
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
    pub fn to_ref(&self) -> TreeRef<'_, H>
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — equal separately built subtrees, changed roots,
    ///   changed descendants and swapped children distinguish omitted fields
    ///   and head-only comparison by the equality verdict.
    /// - witness: `tree::tests::subtree_equality_observes_heads_and_descendants`
    #[inline]
    #[spec(ensures: |equal| equal == (self.root == other.root
        && self.below.len() == other.below.len()
        && self.below.iter().zip(other.below).all(|(left, right)| left == right)))]
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
    #[must_use]
    pub const fn head(self) -> &'tree H
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
    /// - executable: none — the returned opaque iterator has no non-consuming
    ///   sequence observer; the backend also copies its opaque return type into
    ///   a closure signature, where Rust rejects it.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an asymmetric tree and a leaf are collected into
    ///   exact head sequences, separating reversal, omission and a misplaced
    ///   root while preserving left-to-right leaf order.
    /// - witness: `tree::tests::tree_children_and_preorder_preserve_asymmetric_structure`
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
    #[must_use]
    pub fn to_tree(self) -> Tree<H>
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
    #[must_use]
    pub fn children(self) -> Children<'tree, H>
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — root and nested leaves with present and absent images
    ///   are observed as exact child/preorder sequences. Images that themselves
    ///   contain replaceable leaves separate one-pass insertion from repeated
    ///   substitution; unequal arities expose stale extents.
    /// - witness: `tree::tests::leaf_images_are_inserted_once_and_keep_unanswered_leaves`
    #[inline]
    #[spec(ensures: |ref tree| tree.root.extent.0 == tree.below.len().saturating_add(1))]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero, one and two children pin order and exhaustion;
    ///   zero and oversized extents pin malformed-range refusal. Exact heads,
    ///   subtree sizes and remaining counts expose skip or decrement faults.
    /// - witness: `tree::tests::tree_children_and_preorder_preserve_asymmetric_structure`
    /// - witness: `tree::tests::child_cursor_declines_malformed_extents`
    #[inline]
    #[spec(
        captures: remaining = self.remaining.0,
        ensures: |ref child| match *child {
            | Some(child) => self.remaining.0.checked_add(1) == Some(remaining)
                && child.root.extent.0 == child.below.len().saturating_add(1),
            | None => self.remaining.0 == remaining,
        },
    )]
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

#[cfg(test)]
mod tests
{
    use alloc::vec;

    use super::*;

    /// A labelled test head with an explicit child count.
    #[derive(Clone, Debug, Eq, PartialEq)]
    struct TestHead
    {
        /// The semantic label observed by a traversal.
        label: u8,
        /// The number of immediate children.
        arity: ArgumentCount,
    }

    impl Head for TestHead
    {
        /// The declared child count.
        ///
        /// # Specification
        /// trivial.
        fn arity(&self) -> ArgumentCount
        {
            self.arity
        }
    }

    #[test]
    fn extent_addition_saturates_at_usize_boundary()
    {
        const EXACT: Extent = Extent(3).saturating_add(Extent(4));
        const CAPPED: Extent = Extent(usize::MAX).saturating_add(Extent::ONE);
        assert_eq!(EXACT, Extent(7));
        assert_eq!(CAPPED, Extent(usize::MAX));
        for (left, right, expected) in [
            (0, 0, 0),
            (3, 4, 7),
            (usize::MAX.saturating_sub(1), 1, usize::MAX),
            (usize::MAX.saturating_sub(1), 2, usize::MAX),
            (usize::MAX, usize::MAX, usize::MAX),
        ] {
            assert_eq!(Extent(left).saturating_add(Extent(right)), Extent(expected));
        }
    }

    #[test]
    fn tree_children_and_preorder_preserve_asymmetric_structure()
    {
        let leaf = Tree::leaf(TestHead {
            label: 1,
            arity: ArgumentCount(0),
        });
        let nullary = Tree::node(
            TestHead {
                label: 2,
                arity: ArgumentCount(0),
            },
            vec![],
        );
        let unary = Tree::node(
            TestHead {
                label: 3,
                arity: ArgumentCount(1),
            },
            vec![leaf.clone()],
        );
        let tree = Tree::node(
            TestHead {
                label: 4,
                arity: ArgumentCount(2),
            },
            vec![unary.clone(), nullary.clone()],
        );
        assert_eq!(
            leaf.to_ref()
                .preorder()
                .map(|head| head.label)
                .collect::<Vec<_>>(),
            [1]
        );
        assert_eq!(nullary.to_ref().children().next(), None);
        assert_eq!(unary.to_ref().size(), Extent(2));
        assert_eq!(tree.to_ref().size(), Extent(4));
        assert_eq!(
            tree.to_ref()
                .preorder()
                .map(|head| head.label)
                .collect::<Vec<_>>(),
            [4, 3, 1, 2]
        );
        let mut children = tree.to_ref().children();
        assert_eq!(children.len(), 2);
        assert_eq!(children.next(), Some(unary.to_ref()));
        assert_eq!(children.len(), 1);
        assert_eq!(children.next(), Some(nullary.to_ref()));
        assert_eq!(children.len(), 0);
        assert_eq!(children.next(), None);
        assert_eq!(children.next(), None);
    }

    #[test]
    fn subtree_equality_observes_heads_and_descendants()
    {
        let left = Tree::leaf(TestHead {
            label: 1,
            arity: ArgumentCount(0),
        });
        let right = Tree::leaf(TestHead {
            label: 2,
            arity: ArgumentCount(0),
        });
        let tree = Tree::node(
            TestHead {
                label: 3,
                arity: ArgumentCount(2),
            },
            vec![left.clone(), right.clone()],
        );
        let equal = tree.clone();
        let swapped = Tree::node(
            TestHead {
                label: 3,
                arity: ArgumentCount(2),
            },
            vec![right.clone(), left.clone()],
        );
        let changed_root = Tree::node(
            TestHead {
                label: 4,
                arity: ArgumentCount(2),
            },
            vec![left.clone(), right],
        );
        let shortened = Tree::node(
            TestHead {
                label: 3,
                arity: ArgumentCount(1),
            },
            vec![left],
        );
        assert_eq!(tree.to_ref(), equal.to_ref());
        assert_ne!(tree.to_ref(), swapped.to_ref());
        assert_ne!(tree.to_ref(), changed_root.to_ref());
        assert_ne!(tree.to_ref(), shortened.to_ref());
    }

    #[test]
    fn leaf_images_are_inserted_once_and_keep_unanswered_leaves()
    {
        let leaf = Tree::leaf(TestHead {
            label: 1,
            arity: ArgumentCount(0),
        });
        let kept = Tree::leaf(TestHead {
            label: 2,
            arity: ArgumentCount(0),
        });
        let image = Tree::node(
            TestHead {
                label: 3,
                arity: ArgumentCount(2),
            },
            vec![leaf.clone(), kept.clone()],
        );
        let tree = Tree::node(
            TestHead {
                label: 4,
                arity: ArgumentCount(2),
            },
            vec![leaf.clone(), kept.clone()],
        );
        let mut visits = Vec::new();
        let rebuilt = tree.to_ref().replace_leaves(|head| {
            visits.push(head.label);
            if head.label == 1 {
                Maybe::Present(image.to_ref())
            }
            else {
                Maybe::Absent(leaf_image::Absent::Kept)
            }
        });
        visits.sort_unstable();
        assert_eq!(visits, [1, 2]);
        assert_eq!(
            rebuilt
                .to_ref()
                .preorder()
                .map(|head| head.label)
                .collect::<Vec<_>>(),
            [4, 3, 1, 2, 2]
        );
        assert_eq!(rebuilt.to_ref().size(), Extent(5));
        let mut children = rebuilt.to_ref().children();
        assert_eq!(children.next(), Some(image.to_ref()));
        assert_eq!(children.next(), Some(kept.to_ref()));
        assert_eq!(children.next(), None);
        assert_eq!(
            leaf.to_ref()
                .replace_leaves(|_| Maybe::Present(image.to_ref())),
            image
        );
        assert_eq!(
            leaf.to_ref()
                .replace_leaves(|_| Maybe::Absent(leaf_image::Absent::Kept)),
            leaf
        );
    }

    #[test]
    fn child_cursor_declines_malformed_extents()
    {
        for extent in [Extent(0), Extent(2), Extent(usize::MAX)] {
            let entries = [Entry {
                head: TestHead {
                    label: 1,
                    arity: ArgumentCount(0),
                },
                extent,
            }];
            let mut children = Children {
                rest: &entries,
                remaining: ArgumentCount(1),
            };
            assert_eq!(children.next(), None);
            assert_eq!(children.remaining, ArgumentCount(1));
        }
        let mut empty = Children::<TestHead> {
            rest: &[],
            remaining: ArgumentCount(1),
        };
        assert_eq!(empty.next(), None);
    }
}
