//! The records of a conditional that the lowering's context holds.
//!
//! The classification reads a conditional and its `else` branches into these
//! records. The mint sweep reads them back, and `gandr-surface-lowering` names
//! each one at its old path.

use gandr_surface_syntax::NodeIndex;
use quenchant_shape::shape::Maybe;

use super::Block;
use super::FormStretch;
use super::native::Answer;
use super::native::answered;

/// A conditional as the minting reads it: the computation it tests, the block
/// it runs when that holds, what it runs when it does not, and the answer
/// written after its condition.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: each node and block was read by `Lowerer::conditional`.
/// - executable: none — the plan holds no source.
///
/// # Adequacy
/// - hypothesis: L3 — as `Lowerer::conditional`.
/// - witness: `gandr-surface-lowering::lower::conditional::tests::a_conditional_runs_the_branch_its_condition_selects`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Conditional
{
    /// The tested computation.
    pub condition: NodeIndex,
    /// The block run when the condition holds.
    pub then: Block,
    /// What runs when it does not.
    pub otherwise: Otherwise,
    /// The answer written after the condition, which the case is ascribed.
    pub answer: Maybe<Answer, answered::Absent>,
}

/// What a conditional runs when its condition does not hold.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: one variant per false branch the grammar writes.
/// - executable: none — the plan holds no source.
///
/// # Adequacy
/// - hypothesis: L3 — as `Lowerer::conditional`.
/// - witness: `gandr-surface-lowering::lower::conditional::tests::an_else_if_tests_its_own_condition_in_the_false_branch`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Otherwise
{
    /// The block after `else`.
    Block(Block),
    /// One or more conditionals after `else`, with a final false branch block.
    If
    {
        /// Its tested computation, read inside the outer false branch.
        condition: NodeIndex,
        /// The block it runs when that holds.
        then: Block,
        /// The remaining `else if` rungs, in source order.
        rest: FormStretch,
        /// The block it runs when it does not.
        otherwise: Block,
        /// The answer written after its condition, which its case is
        /// ascribed.
        answer: Maybe<Answer, answered::Absent>,
    },
}
