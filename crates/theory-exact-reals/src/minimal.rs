//! The minimal form of a plan graph under bisimulation, and the key that its
//! bytes give.
//!
//! Two nodes are bisimilar when they have one label and their operands are
//! bisimilar: position by position, or as multisets for a node that takes its
//! operands unordered. The coarsest such partition is the minimal form, and
//! the quotient by it is the canonical form of the graph. On a graph with no
//! cycle and ordered operands, the partition is the identity that the
//! canonical walk of a plan gives already. So the minimal form joins two
//! plans that differ only in the order of the operands of a sum, a product, a
//! meet or a join, and a recursive system with each of its unfoldings.
//!
//! [`PlanGraph::minimal`] refines the partition by labels until it is stable
//! for each of its blocks. A second refinement then numbers the classes of
//! the quotient. Each step of a refinement reads the structure alone, so
//! isomorphic quotients get one numbering. The BLAKE3 hash of the numbered
//! quotient is the [`PlanKey`].
//!
//! # Items
//!
//! - [`MinimalForm`], [`ClassId`] — the class of each node, and their count.
//! - [`PlanKey`] — the key of the minimal form.
//!
//! [`PlanGraph::minimal`]: crate::graph::PlanGraph::minimal
//!
//! # Boundaries
//!
//! A pass of the refinement reads the users of one splitter. A node lies in a
//! splitter at most `log n + 1` times, since each splitter but the first holds
//! at most half of the block it came from. So the passes read `O(m log n)`
//! uses over `n` nodes and `m` edges. A pass also sorts the users that it
//! reaches by their block and their count, which adds a factor of `log m` in
//! the worst case.
//!
//! # References
//!
//! - `vault:01a1b278-54ca-7062-94f4-4c94748c971e` — exemplar: the source page
//!   of Robert Paige and Robert E. Tarjan, "Three Partition Refinement
//!   Algorithms", SIAM Journal on Computing 16, 1987, `doi:10.1137/0216062`.
//!   Section 3 refines a partition to the coarsest one that is stable for a
//!   relation in `O(m log n)` time. Its size-stable refinement splits a block
//!   by the count of each element's edges into the splitter, and it queues each
//!   part but the largest. This module takes that refinement, with the count by
//!   position for an ordered node.
//! - `vault:01a1b278-4fbc-7c31-a4f3-2a171b335796` — anchor: the fixed-point
//!   ledger. Its row on plan bisimulation asks for a plan's minimal form and
//!   its key, and this module answers it with a key beside the canonical bytes.

use alloc::collections::VecDeque;
use alloc::vec::Vec;

use crate::graph::GraphError;
use crate::graph::GraphNode;
use crate::graph::Operands;
use crate::graph::PlanGraph;
use crate::plan::NodeCount;

/// The key context of the minimal form: the hash domain of [`PlanKey`].
const KEY_CONTEXT: &str = "gandr theory-exact-reals 2026-11-07 the minimal form of a plan graph";

/// A class of the minimal form: its canonical number.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ClassId(u32);

impl From<ClassId> for u32
{
    /// The number of the class.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(class: ClassId) -> Self
    {
        return class.0;
    }
}

/// The key of a minimal form: the BLAKE3 hash, under its own key context, of
/// the numbered quotient.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PlanKey([u8; 32]);

impl AsRef<[u8]> for PlanKey
{
    /// Borrow the bytes of the hash.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        return &self.0;
    }
}

/// The minimal form of a plan graph: the class of each node that the root
/// reaches, the count of the classes, and the key.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MinimalForm
{
    /// The class of each node, or nothing for a node that the root does not
    /// reach.
    classes: Vec<Option<ClassId>>,
    /// How many classes the form has.
    count: NodeCount,
    /// The key.
    key: PlanKey,
}

impl MinimalForm
{
    /// The class of `node`.
    ///
    /// # Specification
    /// - ensures: two nodes that the root reaches have one class exactly when
    ///   they are bisimilar.
    /// - fails: refuses a node past the last, and a node that the root does not
    ///   reach.
    /// - panics: none.
    /// - executable: none — the clause restates the partition.
    ///
    /// # Errors
    /// - [`GraphError::UnknownNode`]: the graph holds no node at `node`.
    /// - [`GraphError::Unreached`]: the root does not reach `node`.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — on generated recursive systems, two nodes share a
    ///   class exactly when a greatest fixed point by brute force relates them.
    ///   L3 — a node that the root does not reach is refused.
    /// - witness: `tests::minimal::classes_are_the_bisimulation_of_a_recursive_system`
    /// - witness: `tests::minimal::the_builder_refuses_by_name`
    #[inline]
    pub fn class(
        &self,
        node: GraphNode,
    ) -> Result<ClassId, GraphError>
    {
        return self
            .classes
            .get(usize::from(node))
            .ok_or(GraphError::UnknownNode)?
            .ok_or(GraphError::Unreached);
    }

    /// How many classes the form has: the nodes of the quotient.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn class_count(&self) -> NodeCount
    {
        return self.count;
    }

    /// The key of the form.
    ///
    /// # Specification
    /// - ensures: two graphs get one key exactly when their roots are
    ///   bisimilar, up to a collision of the hash.
    /// - panics: none.
    /// - executable: none — the clause restates the hash of the numbered
    ///   quotient.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a generated plan and its respelling with commuted
    ///   operands share one key, two generated plans share one exactly when
    ///   their unfoldings are equal, and two generated recursive systems share
    ///   one exactly when their roots are bisimilar.
    /// - witness: `tests::minimal::a_respelled_plan_keeps_its_key`
    /// - witness: `tests::minimal::two_plans_share_a_key_exactly_when_they_unfold_alike`
    /// - witness: `tests::minimal::classes_are_the_bisimulation_of_a_recursive_system`
    #[inline]
    #[must_use]
    pub const fn key(&self) -> PlanKey
    {
        return self.key;
    }
}

/// A node or a block of the refinement, by its number.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Member(u32);

impl From<Member> for usize
{
    /// The number as an index, or `usize::MAX` past the indices.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(member: Member) -> Self
    {
        return Self::try_from(member.0).unwrap_or(Self::MAX);
    }
}

/// A graph as the refinement reads it, each node a number.
#[derive(Debug, Default)]
struct Shape
{
    /// The label of each node, by its place in the graph's sorted labels.
    labels: Vec<u32>,
    /// Whether each node takes its operands unordered.
    unordered: Vec<bool>,
    /// Where each node's operands start, and past the last node where they
    /// end.
    starts: Vec<u32>,
    /// The operands of every node, each node's in one run.
    operands: Vec<Member>,
}

impl Shape
{
    /// The operands of `node`.
    ///
    /// # Specification
    /// trivial.
    fn operands_of(
        &self,
        node: Member,
    ) -> &[Member]
    {
        let at = usize::from(node);
        let start = self.starts.get(at).copied().map(Member);
        let end = self.starts.get(at.saturating_add(1)).copied().map(Member);
        return start
            .zip(end)
            .and_then(|(start, end)| self.operands.get(usize::from(start) .. usize::from(end)))
            .unwrap_or_default();
    }

    /// Close the node runs: the end of the last node's operands.
    ///
    /// # Specification
    /// trivial.
    fn close(&mut self)
    {
        self.starts
            .push(u32::try_from(self.operands.len()).unwrap_or(u32::MAX));
    }
}

/// A partition of a shape's nodes: the block of each node, and the count of
/// the blocks.
struct Partition
{
    /// The block of each node.
    block_of: Vec<u32>,
    /// How many blocks there are.
    count: usize,
}

/// A use of a node as an operand: the node that names it, and the weight that
/// the use adds to the user's count. An unordered user adds one, and an
/// ordered user adds the bit of the operand's position.
#[derive(Clone, Copy, Debug, Default)]
struct Use
{
    /// The node that names the operand.
    user: u32,
    /// What the use adds to the user's count.
    weight: u64,
}

/// The coarsest partition of `shape`'s nodes that refines the partition by
/// labels and is stable for each of its blocks: two nodes of one block have,
/// for each block, one count of operands in it, by position for an ordered
/// node. The blocks are numbered by the order of the labels and then in the
/// order in which the refinement makes them, and each step reads the
/// structure alone.
///
/// # Specification
/// trivial.
fn refine(shape: &Shape) -> Partition
{
    let at = |value: u32| usize::from(Member(value));
    let count = shape.labels.len();
    // The uses of each node, each with its user and its weight.
    let mut fan: Vec<u32> = alloc::vec![0; count.saturating_add(1)];
    for &operand in &shape.operands {
        if let Some(slot) = fan.get_mut(usize::from(operand).saturating_add(1)) {
            *slot = slot.saturating_add(1);
        }
    }
    let mut running = 0_u32;
    for slot in &mut fan {
        running = running.saturating_add(*slot);
        *slot = running;
    }
    let mut cursor = fan.clone();
    let mut uses: Vec<Use> = alloc::vec![Use::default(); shape.operands.len()];
    for (user, &unordered) in (0_u32 ..).zip(&shape.unordered) {
        for (position, &operand) in (0_u32 ..).zip(shape.operands_of(Member(user))) {
            let weight = if unordered {
                1
            }
            else {
                1_u64.checked_shl(position).unwrap_or_default()
            };
            if let Some(next) = cursor.get_mut(usize::from(operand)) {
                if let Some(slot) = uses.get_mut(at(*next)) {
                    *slot = Use { user, weight };
                }
                *next = next.saturating_add(1);
            }
        }
    }
    // The first blocks: a counting sort by label, the labels in their order.
    let labels = shape
        .labels
        .iter()
        .map(|&label| at(label).saturating_add(1))
        .max()
        .unwrap_or_default();
    let mut by_label: Vec<u32> = alloc::vec![0; labels];
    for &label in &shape.labels {
        if let Some(slot) = by_label.get_mut(at(label)) {
            *slot = slot.saturating_add(1);
        }
    }
    let mut block_of_label: Vec<u32> = alloc::vec![0; labels];
    let mut first: Vec<u32> = Vec::new();
    let mut end: Vec<u32> = Vec::new();
    let mut start = 0_u32;
    for (slot, &size) in block_of_label.iter_mut().zip(&by_label) {
        if size == 0 {
            continue;
        }
        *slot = u32::try_from(first.len()).unwrap_or(u32::MAX);
        first.push(start);
        start = start.saturating_add(size);
        end.push(start);
    }
    let mut next_place = first.clone();
    let mut elems: Vec<u32> = alloc::vec![0; count];
    let mut loc: Vec<u32> = alloc::vec![0; count];
    let mut block_of: Vec<u32> = alloc::vec![0; count];
    for (node, &label) in (0_u32 ..).zip(&shape.labels) {
        let block = block_of_label.get(at(label)).copied().unwrap_or_default();
        let Some(place) = next_place.get_mut(at(block))
        else {
            continue;
        };
        let here = *place;
        *place = place.saturating_add(1);
        if let Some(slot) = elems.get_mut(at(here)) {
            *slot = node;
        }
        if let Some(slot) = loc.get_mut(at(node)) {
            *slot = here;
        }
        if let Some(slot) = block_of.get_mut(at(node)) {
            *slot = block;
        }
    }
    let size_of = |first: &[u32], end: &[u32], block: u32| {
        let from = first.get(at(block)).copied().unwrap_or_default();
        let to = end.get(at(block)).copied().unwrap_or_default();
        return to.saturating_sub(from);
    };
    // Every block but the largest is a splitter at first: the count of a
    // node's operands in all the nodes is its arity, which its label fixes.
    let mut queued: Vec<bool> = alloc::vec![true; first.len()];
    let mut largest: Option<u32> = None;
    for block in (0_u32 ..).take(first.len()) {
        if largest.is_none_or(|held| size_of(&first, &end, block) > size_of(&first, &end, held)) {
            largest = Some(block);
        }
    }
    if let Some(slot) = largest.and_then(|block| queued.get_mut(at(block))) {
        *slot = false;
    }
    let mut queue: VecDeque<u32> = (0_u32 ..)
        .zip(&queued)
        .filter_map(|(block, &waits)| waits.then_some(block))
        .collect();
    let mut key: Vec<u64> = alloc::vec![0; count];
    let mut touched: Vec<u32> = Vec::new();
    let mut fresh: Vec<u32> = Vec::new();
    while let Some(splitter) = queue.pop_front() {
        if let Some(slot) = queued.get_mut(at(splitter)) {
            *slot = false;
        }
        let from = first.get(at(splitter)).copied().unwrap_or_default();
        let to = end.get(at(splitter)).copied().unwrap_or_default();
        for &member in elems.get(at(from) .. at(to)).unwrap_or_default() {
            let low = fan.get(at(member)).copied().unwrap_or_default();
            let high = fan
                .get(at(member).saturating_add(1))
                .copied()
                .unwrap_or_default();
            for &Use { user, weight } in uses.get(at(low) .. at(high)).unwrap_or_default() {
                if let Some(slot) = key.get_mut(at(user)) {
                    if *slot == 0 {
                        touched.push(user);
                    }
                    *slot = slot.saturating_add(weight);
                }
            }
        }
        touched.sort_unstable_by_key(|&node| {
            let block = block_of.get(at(node)).copied().unwrap_or_default();
            let weight = key.get(at(node)).copied().unwrap_or_default();
            return (block, weight);
        });
        let weight_of = |node: u32| key.get(at(node)).copied().unwrap_or_default();
        let mut next = 0_usize;
        while let Some(&leader) = touched.get(next) {
            let block = block_of.get(at(leader)).copied().unwrap_or_default();
            let mut past = next;
            while touched
                .get(past)
                .is_some_and(|&node| block_of.get(at(node)).copied() == Some(block))
            {
                past = past.saturating_add(1);
            }
            let group = touched.get(next .. past).unwrap_or_default();
            next = past;
            let size = size_of(&first, &end, block);
            let hit = u32::try_from(group.len()).unwrap_or(u32::MAX);
            let distinct = group
                .windows(2)
                .filter(|pair| {
                    return match **pair {
                        [one, two] => weight_of(one) != weight_of(two),
                        _ => false,
                    };
                })
                .count()
                .saturating_add(1);
            if distinct.saturating_add(usize::from(hit < size)) < 2 {
                continue;
            }
            // The touched nodes move to the block's tail, in the order of
            // their counts.
            let tail = end
                .get(at(block))
                .copied()
                .unwrap_or_default()
                .saturating_sub(hit);
            for (target, &node) in (tail ..).zip(group) {
                let here = loc.get(at(node)).copied().unwrap_or_default();
                let other = elems.get(at(target)).copied().unwrap_or_default();
                if let Some(slot) = elems.get_mut(at(here)) {
                    *slot = other;
                }
                if let Some(slot) = elems.get_mut(at(target)) {
                    *slot = node;
                }
                if let Some(slot) = loc.get_mut(at(other)) {
                    *slot = here;
                }
                if let Some(slot) = loc.get_mut(at(node)) {
                    *slot = target;
                }
            }
            let waits = queued.get(at(block)).copied().unwrap_or_default();
            // The untouched part keeps the block, or else the part of the
            // least count does.
            let mut keeps = hit == size;
            if !keeps && let Some(slot) = end.get_mut(at(block)) {
                *slot = tail;
            }
            let mut place = tail;
            let mut index = 0_usize;
            while let Some(&head) = group.get(index) {
                let weight = weight_of(head);
                let mut stop = index;
                while group
                    .get(stop)
                    .is_some_and(|&node| weight_of(node) == weight)
                {
                    stop = stop.saturating_add(1);
                }
                let length = u32::try_from(stop.saturating_sub(index)).unwrap_or(u32::MAX);
                index = stop;
                let past_part = place.saturating_add(length);
                if keeps {
                    if let Some(slot) = end.get_mut(at(block)) {
                        *slot = past_part;
                    }
                    keeps = false;
                }
                else {
                    let id = u32::try_from(first.len()).unwrap_or(u32::MAX);
                    first.push(place);
                    end.push(past_part);
                    queued.push(false);
                    for &node in elems.get(at(place) .. at(past_part)).unwrap_or_default() {
                        if let Some(slot) = block_of.get_mut(at(node)) {
                            *slot = id;
                        }
                    }
                    fresh.push(id);
                }
                place = past_part;
            }
            // A queued block queues each new part. Otherwise each part but
            // the largest is queued, and the block wins a tie.
            let mut kept = block;
            if !waits {
                for &part in &fresh {
                    if size_of(&first, &end, part) > size_of(&first, &end, kept) {
                        kept = part;
                    }
                }
            }
            for part in core::iter::once(block).chain(fresh.iter().copied()) {
                let joins = if waits { part != block } else { part != kept };
                if joins {
                    if let Some(slot) = queued.get_mut(at(part)) {
                        *slot = true;
                    }
                    queue.push_back(part);
                }
            }
            fresh.clear();
        }
        for &node in &touched {
            if let Some(slot) = key.get_mut(at(node)) {
                *slot = 0;
            }
        }
        touched.clear();
    }
    return Partition {
        block_of,
        count: first.len(),
    };
}

/// The minimal form of `graph`.
///
/// The work is a walk from the root, two refinements, and one hash of the
/// numbered quotient.
///
/// # Specification
/// trivial.
pub(crate) fn minimal(graph: &PlanGraph) -> MinimalForm
{
    let at = |value: u32| usize::from(Member(value));
    let number = |count: usize| u32::try_from(count).unwrap_or(u32::MAX);
    // The nodes that the root reaches, each numbered in the order of a walk
    // from the root.
    let total = usize::from(graph.node_count());
    let mut place_of: Vec<Option<u32>> = alloc::vec![None; total];
    let mut order: Vec<GraphNode> = Vec::with_capacity(total);
    if let Some(slot) = place_of.get_mut(usize::from(graph.root())) {
        *slot = Some(0);
        order.push(graph.root());
    }
    let mut walked = 0_usize;
    while let Some(&node) = order.get(walked) {
        walked = walked.saturating_add(1);
        for &operand in graph.operands_of(node) {
            if let Some(slot) = place_of.get_mut(usize::from(operand))
                && slot.is_none()
            {
                *slot = Some(number(order.len()));
                order.push(operand);
            }
        }
    }
    let mut reached = Shape::default();
    for &node in &order {
        reached
            .labels
            .push(graph.label_place(node).map(u32::from).unwrap_or_default());
        reached.unordered.push(
            graph
                .label_of(node)
                .is_some_and(|label| label.operands() == Operands::Unordered),
        );
        reached.starts.push(number(reached.operands.len()));
        reached
            .operands
            .extend(graph.operands_of(node).iter().map(|&operand| {
                return Member(
                    place_of
                        .get(usize::from(operand))
                        .copied()
                        .flatten()
                        .unwrap_or_default(),
                );
            }));
    }
    reached.close();
    let coarse = refine(&reached);
    let block_of = |node: u32| coarse.block_of.get(at(node)).copied().unwrap_or_default();
    // The quotient: each class as its first node, and its operands as their
    // classes.
    let mut first_of: Vec<Option<u32>> = alloc::vec![None; coarse.count];
    for (node, &block) in (0_u32 ..).zip(&coarse.block_of) {
        if let Some(slot) = first_of.get_mut(at(block))
            && slot.is_none()
        {
            *slot = Some(node);
        }
    }
    let leaders: Vec<u32> = first_of
        .into_iter()
        .map(Option::unwrap_or_default)
        .collect();
    let mut quotient = Shape::default();
    for &node in &leaders {
        quotient
            .labels
            .push(reached.labels.get(at(node)).copied().unwrap_or_default());
        quotient
            .unordered
            .push(reached.unordered.get(at(node)).copied().unwrap_or_default());
        quotient.starts.push(number(quotient.operands.len()));
        quotient.operands.extend(
            reached
                .operands_of(Member(node))
                .iter()
                .map(|&operand| Member(block_of(operand.0))),
        );
    }
    quotient.close();
    // The second refinement numbers the classes. The quotient is minimal, so
    // each of its blocks holds one class, and the numbers read the structure
    // alone.
    let numbered = refine(&quotient);
    let number_of = |block: u32| {
        numbered
            .block_of
            .get(at(block))
            .copied()
            .unwrap_or_default()
    };
    let mut class_of_number: Vec<u32> = alloc::vec![0; numbered.count];
    for (block, &numeral) in (0_u32 ..).zip(&numbered.block_of) {
        if let Some(slot) = class_of_number.get_mut(at(numeral)) {
            *slot = block;
        }
    }
    let mut hasher = blake3::Hasher::new_derive_key(KEY_CONTEXT);
    let word = |hasher: &mut blake3::Hasher, value: u32| {
        let _written = hasher.update(&value.to_le_bytes());
    };
    word(&mut hasher, number(numbered.count));
    word(&mut hasher, number_of(block_of(0)));
    let mut ids: Vec<u32> = Vec::new();
    for &class in &class_of_number {
        let leader = leaders.get(at(class)).copied().unwrap_or_default();
        let node = order
            .get(at(leader))
            .copied()
            .unwrap_or_else(|| graph.root());
        if let Some(label) = graph.label_of(node) {
            let _order = hasher.update(&[u8::from(label.operands() == Operands::Unordered)]);
            word(&mut hasher, number(label.as_ref().len()));
            let _bytes = hasher.update(label.as_ref());
        }
        ids.clear();
        ids.extend(
            quotient
                .operands_of(Member(class))
                .iter()
                .map(|&block| number_of(block.0)),
        );
        if quotient
            .unordered
            .get(at(class))
            .copied()
            .unwrap_or_default()
        {
            ids.sort_unstable();
        }
        word(&mut hasher, number(ids.len()));
        for &id in &ids {
            word(&mut hasher, id);
        }
    }
    let classes = place_of
        .iter()
        .map(|place| place.map(|node| ClassId(number_of(block_of(node)))))
        .collect();
    return MinimalForm {
        classes,
        count: NodeCount::from(numbered.count),
        key: PlanKey(*hasher.finalize().as_bytes()),
    };
}
