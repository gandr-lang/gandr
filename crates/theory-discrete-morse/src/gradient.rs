//! The gradient of a matching as a graph on places, and the edges of it that
//! close a cycle.

use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;

use crate::collapse::Count;

wrapper! {
    /// A node of a gradient graph: the place of a cell in the list that a
    /// walk or a matching reads.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Place(usize);
}

/// A node's state in a depth-first walk.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Mark
{
    /// The walk has not reached the node.
    Unseen,
    /// The node is on the walk's path.
    Open,
    /// The walk has left the node.
    Done,
}

/// The edges of the graph `edges` that close a cycle: each edge whose target
/// is on the path of a depth-first walk when the walk meets the edge. The walk
/// starts at each node in turn that no earlier walk reaches.
///
/// # Specification
/// - requires: each target is a place below the count of `edges`. A target past
///   it is read as a dead end.
/// - ensures: the count is zero exactly when the graph has no cycle, and it is
///   at most the number of edges.
/// - panics: none.
/// - intension: one walk over the whole graph, which reads each node and each
///   edge once, with an explicit stack and no recursion.
///
/// # Adequacy
/// - hypothesis: L3 — a scheme whose two redundant cells name each other's
///   partners closes one cycle, and an acyclic scheme closes none.
/// - witness: `tests::collapse::a_scheme_whose_gradient_turns_back_closes_a_cycle`
/// - witness: `tests::collapse::the_matching_of_a_triangle_collapses_onto_one_vertex`
#[spec(ensures: |ret| usize::from(ret) <= edges.iter().map(Vec::len).fold(0_usize, usize::saturating_add))]
pub fn cycles(edges: &[Vec<Place>]) -> Count
{
    let mut marks = vec![Mark::Unseen; edges.len()];
    let mut found = Count::default();
    let mut stack: Vec<(Place, Count)> = Vec::new();
    for start in 0 .. edges.len() {
        let Some(mark) = marks.get_mut(start)
        else {
            continue;
        };
        if *mark != Mark::Unseen {
            continue;
        }
        *mark = Mark::Open;
        stack.push((Place(start), Count::default()));
        while let Some(&mut (node, ref mut child)) = stack.last_mut() {
            let next = edges
                .get(node.0)
                .and_then(|targets| targets.get(usize::from(*child)))
                .copied();
            let Some(target) = next
            else {
                if let Some(mark) = marks.get_mut(node.0) {
                    *mark = Mark::Done;
                }
                let _left = stack.pop();
                continue;
            };
            *child = child.one_more();
            match marks.get(target.0).copied() {
                Some(Mark::Open) => found = found.one_more(),
                Some(Mark::Unseen) => {
                    if let Some(mark) = marks.get_mut(target.0) {
                        *mark = Mark::Open;
                    }
                    stack.push((target, Count::default()));
                },
                Some(Mark::Done) | None => {},
            }
        }
    }
    found
}
