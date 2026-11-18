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
mod tests;
