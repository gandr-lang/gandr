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
    /// - ensures: returns whether the two tasks enter the same child and adds
    ///   one to the shared tally.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the bound witness reads the tally after calls that
    ///   compare a known number of times; an uncounted comparison would let a
    ///   walking combinator pass.
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
/// - hypothesis: L3 — the witnesses compare children by id, so equal ids would
///   let a reversed reading pass.
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
