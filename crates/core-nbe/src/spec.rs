//! The combinators this crate's specification clauses read the sharing overlay
//! through.
//!
//! A clause that restates a node's children variant by variant drifts from
//! the item it restates, and one that walks a task stack to find what a single
//! step queued costs as much as the stack. Each combinator here derives its
//! vocabulary from the item that defines it — a node's children from
//! [`Children`], the order a walk queues them in from
//! [`Children::push_reversed`] — and states a `# Clause cost` bound, so a
//! clause names the vocabulary once and reads only what the step it checks
//! wrote. The generic sequence claims these build on live in
//! `gandr-theory-spec-combinators`.

use anodized::spec;
use gandr_theory_spec_combinators::Holds;
use gandr_theory_spec_combinators::Mark;
use gandr_theory_spec_combinators::appended;

use crate::overlay::Children;
use crate::overlay::OverlayId;

/// The children of a node, left to right: nothing for a leaf, then the one,
/// two or three children the variant holds, leftmost first.
///
/// It is the one reading of [`Children`] a clause walks, so no clause restates
/// its variants; `spec::tests::listed_reads_children_left_to_right` pins the
/// order.
///
/// # Specification
/// trivial.
///
/// # Clause cost
/// - bound: reads no state; the iterator yields at most the three ids the value
///   itself holds.
#[inline]
pub fn listed(children: Children) -> impl DoubleEndedIterator<Item = OverlayId> + Clone
{
    let padded = match children {
        Children::Leaf => [None, None, None],
        Children::One(first) => [Some(first), None, None],
        Children::Two(first, second) => [Some(first), Some(second), None],
        Children::Three(first, second, third) => [Some(first), Some(second), Some(third)],
    };
    padded.into_iter().flatten()
}

/// Whether the tasks `tasks` gained since `mark` are one `enter(child)` per
/// child of `children`, rightmost first: what [`Children::push_reversed`]
/// queues so the leftmost child runs first off the stack.
///
/// # Specification
/// - ensures: holds exactly when `tasks` is the child count longer than `mark`
///   and, counting the children from the right, the task that many places past
///   `mark` equals `enter` of that child.
/// - provides: the claim a walk's step makes after queuing a node's children,
///   checked since the mark it captured rather than over the stack beneath it.
/// - panics: none.
///
/// # Clause cost
/// - bound: reads the length of `tasks` and compares at most the three tasks
///   past `mark`, once each, and once more when its own clause is checked.
///
/// # Adequacy
/// - hypothesis: L3 — children queued rightmost first hold; the same children
///   queued leftmost first, one child missing, one task too many, and a mark
///   one place early or late each fail, refuting a claim that checks only the
///   count, only the order, or the stack beneath the mark. The bound is a
///   property over every stack length up to the witness's bound: at most three
///   comparisons, six in an enforcing build.
/// - witness: `spec::tests::queued_since_holds_for_children_rightmost_first`
/// - witness: `spec::tests::queued_since_compares_at_most_three_tasks`
#[spec(ensures: |ret| bool::from(ret)
    == (usize::from(mark).checked_add(listed(children).count()) == Some(tasks.len())
        && listed(children).rev().enumerate().all(|(depth, child)|
            tasks.get(usize::from(mark).saturating_add(depth)) == Some(&enter(child)))))]
#[inline]
#[must_use]
pub fn queued_since<Task, Enter>(
    tasks: &[Task],
    mark: Mark,
    children: Children,
    enter: Enter,
) -> Holds
where
    Task: PartialEq,
    Enter: Fn(OverlayId) -> Task,
{
    let queued = appended(tasks, mark);
    let fits = usize::from(mark) <= tasks.len() && queued.len() == listed(children).count();
    Holds::from(
        fits && queued
            .iter()
            .rev()
            .zip(listed(children))
            .all(|(task, child)| *task == enter(child)),
    )
}

#[cfg(test)]
mod tests
{
    use alloc::vec::Vec;
    use core::cell::Cell;

    use anodized::spec;
    use gandr_theory_spec_combinators::Mark;

    use super::listed;
    use super::queued_since;
    use crate::overlay::Children;
    use crate::overlay::Overlay;
    use crate::overlay::OverlayId;
    use crate::overlay::ValueGraft;
    use crate::overlay::ValueNode;

    /// The deepest stack beneath the queued children the bound witness builds.
    const DEEPEST: usize = 256;

    /// How many times a combinator's comparisons run: once, and once more for
    /// its own clause in an enforcing build.
    const CHECKED: usize = if cfg!(anodized_panic) { 2 } else { 1 };

    /// A task naming one child, whose comparisons add to a shared tally.
    #[derive(Debug)]
    struct Counted<'tally>
    {
        /// The child the task enters.
        child: OverlayId,
        /// The comparisons made so far, shared by every task of a stack.
        tally: &'tally Cell<usize>,
    }

    impl PartialEq for Counted<'_>
    {
        /// Equal children, counting the comparison.
        ///
        /// # Specification
        /// - ensures: returns whether the two tasks enter the same child and
        ///   adds one to the shared tally.
        /// - panics: none.
        ///
        /// # Adequacy
        /// - hypothesis: L3 — the bound witness reads the tally after calls
        ///   that compare a known number of times; an uncounted comparison
        ///   would let a walking combinator pass.
        /// - witness: `spec::tests::queued_since_compares_at_most_three_tasks`
        #[spec(captures: before = self.tally.get(),
            ensures: |ret| ret == (self.child == other.child) && self.tally.get() == before.saturating_add(1))]
        fn eq(
            &self,
            other: &Self,
        ) -> bool
        {
            self.tally.set(self.tally.get().saturating_add(1));
            self.child == other.child
        }
    }

    /// Three distinct value ids, minted in order.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: three pairwise distinct value ids of `overlay`.
    /// - panics: when a mint is refused, which only the id ceiling causes.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the witnesses compare children by id, so equal ids
    ///   would let a reversed reading pass.
    /// - witness: `spec::tests::listed_reads_children_left_to_right`
    #[spec(ensures: |ret| ret.0 != ret.1 && ret.1 != ret.2 && ret.0 != ret.2)]
    fn three(overlay: &mut Overlay) -> (OverlayId, OverlayId, OverlayId)
    {
        let mut mint = || {
            overlay
                .mint_value(ValueNode::Grafted(ValueGraft::Unit))
                .map(OverlayId::Value)
                .expect("a fresh overlay mints a unit")
        };
        (mint(), mint(), mint())
    }

    #[test]
    fn listed_reads_children_left_to_right()
    {
        let mut overlay = Overlay::new();
        let (first, second, third) = three(&mut overlay);
        let read = |children: Children| listed(children).collect::<Vec<_>>();
        assert!(read(Children::Leaf).is_empty());
        assert_eq!(read(Children::One(first)), [first]);
        assert_eq!(read(Children::Two(first, second)), [first, second]);
        assert_eq!(read(Children::Three(first, second, third)), [
            first, second, third
        ]);
        assert_eq!(
            listed(Children::Three(first, second, third))
                .rev()
                .collect::<Vec<_>>(),
            [third, second, first]
        );
    }

    #[test]
    fn queued_since_holds_for_children_rightmost_first()
    {
        let mut overlay = Overlay::new();
        let (first, second, third) = three(&mut overlay);
        let children = Children::Three(first, second, third);
        let holds = |tasks: &[OverlayId], mark: usize| {
            bool::from(queued_since(tasks, Mark::from(mark), children, |child| {
                child
            }))
        };
        assert!(holds(&[first, third, second, first], 1));
        assert!(!holds(&[first, first, second, third], 1));
        assert!(!holds(&[first, third, second], 1));
        assert!(!holds(&[first, third, second, first, first], 1));
        assert!(!holds(&[first, third, second, first], 0));
        assert!(!holds(&[first, third, second, first], 2));
        let leaf = |tasks: &[OverlayId], mark: usize| {
            bool::from(queued_since(
                tasks,
                Mark::from(mark),
                Children::Leaf,
                |child| child,
            ))
        };
        assert!(leaf(&[first], 1));
        assert!(!leaf(&[first], 0));
        assert!(!leaf(&[first], 2));
        let two = |tasks: &[OverlayId]| {
            bool::from(queued_since(
                tasks,
                Mark::from(0),
                Children::Two(first, second),
                |child| child,
            ))
        };
        assert!(two(&[second, first]));
        assert!(!two(&[first, second]));
    }

    #[test]
    fn queued_since_compares_at_most_three_tasks()
    {
        let mut overlay = Overlay::new();
        let (first, second, third) = three(&mut overlay);
        let children = Children::Three(first, second, third);
        let tally = Cell::new(0_usize);
        let enter = |child| Counted {
            child,
            tally: &tally,
        };
        let mut beneath = Vec::new();
        for depth in 0 ..= DEEPEST {
            let mut tasks = Vec::new();
            tasks.extend(beneath.iter().map(|&child| enter(child)));
            tasks.extend([third, second, first].map(enter));
            tally.set(0);
            assert!(bool::from(queued_since(
                &tasks,
                Mark::from(depth),
                children,
                enter
            )));
            assert!(tally.get() <= CHECKED.saturating_mul(3));
            for mark in 0 ..= depth.saturating_add(4) {
                tally.set(0);
                let _answer = queued_since(&tasks, Mark::from(mark), children, enter);
                assert!(tally.get() <= CHECKED.saturating_mul(3));
            }
            beneath.push(first);
        }
    }
}
