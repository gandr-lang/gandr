//! E-class analyses: a datum on each class, kept as the join of its nodes'
//! data.

use core::fmt;

use gandr_theory_coherent_resolutions::TermHead;
use gandr_theory_coherent_resolutions::TermPlace;
use gandr_theory_coherent_resolutions::TermSize;

use crate::egraph::EGraph;
use crate::error::EGraphError;

/// Whether a join changes the datum it joins into.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Growth
{
    /// The datum grows: the join differs from the datum before it.
    Grew,
    /// The datum stays: the join equals the datum before it.
    Stayed,
}

/// An e-class analysis: a domain with a join, and a datum for each class.
///
/// After [`EGraph::rebuild`], the datum of each class is the join of `make`
/// over its nodes, and `modify` changes no class (egg, § 4.1). The e-graph
/// keeps that invariant through each union and each repair, under three laws:
///
/// - `merge` is the join of a semilattice: commutative, associative and
///   idempotent. It says whether the datum grows.
/// - `make` reads a node's head and its children's data alone, so two congruent
///   nodes give one datum.
/// - `modify` is idempotent: a second call after the first changes nothing.
pub trait Analysis: Sized
{
    /// The datum of a class.
    type Data: Clone + Eq + fmt::Debug;

    /// The datum of a node with the head `head`, whose children's classes
    /// hold `children`, in the order of the arguments.
    ///
    /// # Specification
    /// - ensures: the datum depends on `head` and `children` alone.
    /// - panics: none.
    /// - executable: none — the ensures is a statement about every call, and
    ///   one call holds no second call to compare.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — after a rebuild, each class's datum agrees with a
    ///   join of `make` over the class's members, folded apart from the repair.
    /// - declaration-only: the obligation is each implementation's datum; the
    ///   trait has no body to witness.
    fn make<'data, Children>(
        &self,
        head: TermHead,
        children: Children,
    ) -> Self::Data
    where
        Children: ExactSizeIterator<Item = &'data Self::Data>,
        Self::Data: 'data;

    /// Join `from` into `into`, and say whether `into` grows.
    ///
    /// # Specification
    /// - ensures: `into` becomes the join of the two data; the result is
    ///   [`Growth::Grew`] exactly when the join differs from `into` before the
    ///   call; and the join is commutative, associative and idempotent.
    /// - panics: none.
    /// - executable: none — the laws are statements about every three data,
    ///   which the property test samples.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — sampled triples of data separate a join that is not
    ///   commutative, associative or idempotent.
    /// - declaration-only: the obligation is each implementation's join; the
    ///   trait has no body to witness.
    fn merge(
        &self,
        into: &mut Self::Data,
        from: Self::Data,
    ) -> Growth;

    /// Change the e-graph after the datum of `class` grows: add a node to the
    /// class, or join it to another, each through the e-graph's own methods.
    ///
    /// # Specification
    /// - ensures: a second call after the first changes no class and no datum.
    /// - fails: as the e-graph's methods that it calls fail.
    /// - panics: none.
    /// - executable: none — the ensures compares the e-graph after two calls,
    ///   and the call holds no copy of it.
    ///
    /// # Errors
    /// - [`EGraphError`]: as the e-graph's methods that it calls refuse.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a second call after the first changes no class.
    /// - declaration-only: the obligation is each implementation's change; the
    ///   two implementations of this crate change nothing.
    fn modify(
        graph: &mut EGraph<Self>,
        class: TermPlace,
    ) -> Result<(), EGraphError>;
}

impl Analysis for ()
{
    type Data = ();

    /// No datum.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn make<'data, Children>(
        &self,
        _head: TermHead,
        _children: Children,
    ) -> Self::Data
    where
        Children: ExactSizeIterator<Item = &'data Self::Data>,
        Self::Data: 'data,
    {
    }

    /// No datum, which stays.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn merge(
        &self,
        _into: &mut Self::Data,
        _from: Self::Data,
    ) -> Growth
    {
        Growth::Stayed
    }

    /// No change.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn modify(
        _graph: &mut EGraph<Self>,
        _class: TermPlace,
    ) -> Result<(), EGraphError>
    {
        Ok(())
    }
}

/// The size of the smallest term that a class represents.
///
/// Each node counts one, so a node's size is one more than the sizes of its
/// children's classes, and the join is the smaller size. The datum is the cost
/// of the term that an extraction by size chooses, and not the term.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct Size;

impl Analysis for Size
{
    type Data = TermSize;

    /// One more than the sum of the children's sizes.
    ///
    /// # Specification
    /// - ensures: the result is one more than the sum of `children`, and the
    ///   sum stops at the largest size.
    /// - panics: none.
    /// - executable: none — the ensures sums `children`, which the call reads
    ///   only once.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a class whose smallest term is a constant, and a
    ///   class whose smallest term needs a child, separate the two sums.
    /// - witness: `tests::analysis::the_size_of_a_class_is_the_size_of_its_smallest_term`
    #[inline]
    fn make<'data, Children>(
        &self,
        _head: TermHead,
        children: Children,
    ) -> Self::Data
    where
        Children: ExactSizeIterator<Item = &'data Self::Data>,
        Self::Data: 'data,
    {
        let mut size = 1_usize;
        for &child in children {
            size = size.saturating_add(usize::from(child));
        }
        TermSize::from(size)
    }

    /// The smaller of the two sizes.
    ///
    /// # Specification
    /// - ensures: `into` becomes the smaller of the two sizes, and grows
    ///   exactly when `from` is smaller.
    /// - panics: none.
    /// - executable: none — the ensures compares with `into` before the call,
    ///   which the call changes.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the property test samples three sizes, and checks
    ///   that the join is commutative, associative and idempotent, and that it
    ///   reports its growth.
    /// - witness: `tests::analysis::the_merge_of_each_analysis_is_a_join`
    #[inline]
    fn merge(
        &self,
        into: &mut Self::Data,
        from: Self::Data,
    ) -> Growth
    {
        if from < *into {
            *into = from;
            Growth::Grew
        }
        else {
            Growth::Stayed
        }
    }

    /// No change: the size of a class names no node to add.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn modify(
        _graph: &mut EGraph<Self>,
        _class: TermPlace,
    ) -> Result<(), EGraphError>
    {
        Ok(())
    }
}
