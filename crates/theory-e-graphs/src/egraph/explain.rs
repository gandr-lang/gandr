//! Explanations: the chain of reasons between two terms of one class, read
//! from the proof forest, and the replay that checks it.

use alloc::collections::BTreeMap;
use alloc::vec;
use alloc::vec::Vec;

use gandr_theory_coherent_resolutions::LawvereError;
use gandr_theory_coherent_resolutions::TermHead;
use gandr_theory_coherent_resolutions::TermPlace;
use gandr_theory_coherent_resolutions::TermTable;

use super::Direction;
use super::EGraph;
use super::Equation;
use super::EquationPlace;
use super::Reason;
use crate::analysis::Analysis;
use crate::error::EGraphError;

wrapper! {
    /// The place of a proof in its explanation.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct ProofPlace(usize);
}

wrapper! {
    /// The place of a step in its proof.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct StepPlace(usize);
}

wrapper! {
    /// The place of an argument of a node.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Position(usize);
}

/// Why one step of a proof holds.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum StepReason
{
    /// An input equation at an instance: the step starts at the side that
    /// `direction` names and ends at the other side, each variable `x`
    /// replaced by `values[x]`.
    Input
    {
        /// The equation.
        equation: EquationPlace,
        /// The side that the step starts from.
        direction: Direction,
        /// The value of each variable, by its place.
        values: Vec<TermPlace>,
    },
    /// A congruence: the two ends have one head, and the proof at each
    /// position joins their children at that position.
    Congruence
    {
        /// The proof for each argument, each an earlier proof of the
        /// explanation.
        children: Vec<ProofPlace>,
    },
}

/// One step of a proof: where it ends, and why.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Step
{
    /// The term the step ends at. It starts where the step before it ends.
    pub to: TermPlace,
    /// Why the step holds.
    pub reason: StepReason,
}

/// A chain of steps from one term to another.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Proof
{
    /// The term the first step starts at.
    pub from: TermPlace,
    /// The term the last step ends at.
    pub to: TermPlace,
    /// The steps, in order: none when the two ends are one term.
    pub steps: Vec<Step>,
}

/// An explanation of one equality, as a list of proofs.
///
/// Each congruence step points only at earlier proofs, and the last proof is
/// the one that the explanation gives. A pair of terms has one proof, so an
/// explanation shares each proof that two congruences need.
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
#[repr(transparent)]
pub struct Explanation
{
    /// The proofs, the last the explanation's own.
    pub proofs: Vec<Proof>,
}

/// Why an explanation does not replay: each forged step by name.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Refusal
{
    /// The explanation holds no proof.
    Empty,
    /// The last proof does not join the two terms that the caller names.
    Ends,
    /// The steps of the proof at this place do not end at its last term.
    Broken
    {
        /// The proof.
        proof: ProofPlace,
    },
    /// The step names an equation that the caller does not give.
    UnknownEquation
    {
        /// The proof.
        proof: ProofPlace,
        /// The step.
        step: StepPlace,
    },
    /// The two ends of the step are not the two sides of its equation under
    /// its values.
    NotAnInstance
    {
        /// The proof.
        proof: ProofPlace,
        /// The step.
        step: StepPlace,
    },
    /// The two ends of a congruence step differ in their head or their
    /// arguments' count, or the step gives another count of proofs.
    Incongruent
    {
        /// The proof.
        proof: ProofPlace,
        /// The step.
        step: StepPlace,
    },
    /// A congruence step points at a proof that is not earlier.
    Forward
    {
        /// The proof.
        proof: ProofPlace,
        /// The step.
        step: StepPlace,
        /// The argument.
        position: Position,
    },
    /// The proof that a congruence step names for an argument does not join
    /// the two ends' arguments at that position.
    ChildUnexplained
    {
        /// The proof.
        proof: ProofPlace,
        /// The step.
        step: StepPlace,
        /// The argument.
        position: Position,
    },
    /// The table refuses a place that a step names.
    Table(LawvereError),
}

/// One unit of the explanation's walk.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Task
{
    /// Explain the pair, once the proofs of its congruences' children exist.
    Enter(TermPlace, TermPlace),
    /// Explain the pair, the proofs of its congruences' children made.
    Leave(TermPlace, TermPlace),
}

/// Whether a path reads a proof-forest edge in its own direction.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Reading
{
    /// From the edge's node to its neighbour.
    Along,
    /// From the neighbour back to the edge's node.
    Against,
}

/// One edge of a path through the proof forest, as the path reads it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct PathEdge
{
    /// The node the path leaves.
    from: TermPlace,
    /// The node the path reaches.
    to: TermPlace,
    /// The place of the edge's reason.
    reason: usize,
    /// How the path reads the edge.
    reading: Reading,
}

impl<A> EGraph<A>
where
    A: Analysis,
{
    /// The explanation of the equality of the terms at `left` and `right`:
    /// the proof-forest path between them, each congruence on it explained
    /// by the proofs of its children.
    ///
    /// # Specification
    /// - ensures: the last proof joins `left` to `right`, each congruence step
    ///   points at earlier proofs only, and the explanation replays against the
    ///   table and the equations.
    /// - fails: [`EGraphError::Unheld`] when the e-graph does not hold a term;
    ///   [`EGraphError::Apart`] when the two lie in different classes.
    /// - panics: none.
    /// - executable: none — the ensures replays the result, which the witness
    ///   does.
    ///
    /// # Errors
    /// - [`EGraphError::Unheld`]: a term is not in the e-graph.
    /// - [`EGraphError::Apart`]: the two terms lie in different classes.
    /// - [`EGraphError::Unexplained`]: the proof forest is corrupt.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a chain of input equations and a congruence over it
    ///   each explain and replay, and two terms apart are refused.
    /// - witness: `tests::explain::each_explanation_replays`
    /// - witness: `tests::explain::terms_in_two_classes_have_no_explanation`
    #[inline]
    pub fn explain(
        &self,
        left: TermPlace,
        right: TermPlace,
    ) -> Result<Explanation, EGraphError>
    {
        if self.root(left)? != self.root(right)? {
            return Err(EGraphError::Apart(left, right));
        }
        let mut proofs = Vec::new();
        let mut made: BTreeMap<(TermPlace, TermPlace), ProofPlace> = BTreeMap::new();
        let mut tasks = vec![Task::Enter(left, right)];
        while let Some(task) = tasks.pop() {
            let (pair, waits) = match task {
                Task::Enter(from, to) => ((from, to), true),
                Task::Leave(from, to) => ((from, to), false),
            };
            if made.contains_key(&pair) {
                continue;
            }
            let path = self.path(pair)?;
            if waits {
                let mut waiting = false;
                for edge in &path {
                    for child in self.children(edge)? {
                        if !made.contains_key(&child) {
                            if !waiting {
                                waiting = true;
                                tasks.push(Task::Leave(pair.0, pair.1));
                            }
                            tasks.push(Task::Enter(child.0, child.1));
                        }
                    }
                }
                if waiting {
                    continue;
                }
            }
            let proof = self.proof(pair, &path, &made)?;
            let _absent = made.insert(pair, ProofPlace::from(proofs.len()));
            proofs.push(proof);
        }
        Ok(Explanation { proofs })
    }

    /// The pairs of children that a congruence edge needs explained, place
    /// by place; none for an input edge.
    ///
    /// # Specification
    /// trivial.
    fn children(
        &self,
        edge: &PathEdge,
    ) -> Result<Vec<(TermPlace, TermPlace)>, EGraphError>
    {
        match self.reasons.get(edge.reason) {
            Some(&Reason::Congruence) => {
                let from = self.table.node(edge.from)?;
                let to = self.table.node(edge.to)?;
                Ok(from
                    .children
                    .iter()
                    .copied()
                    .zip(to.children.iter().copied())
                    .collect())
            },
            Some(&Reason::Input { .. }) => Ok(Vec::new()),
            None => Err(EGraphError::Unexplained(edge.from, edge.to)),
        }
    }

    /// The proof of `pair` along `path`, each congruence's children read from
    /// `made`.
    ///
    /// # Specification
    /// trivial.
    fn proof(
        &self,
        (from, to): (TermPlace, TermPlace),
        path: &[PathEdge],
        made: &BTreeMap<(TermPlace, TermPlace), ProofPlace>,
    ) -> Result<Proof, EGraphError>
    {
        let unexplained = || EGraphError::Unexplained(from, to);
        let mut steps = Vec::with_capacity(path.len());
        for edge in path {
            let reason = match *self.reasons.get(edge.reason).ok_or_else(unexplained)? {
                Reason::Input {
                    equation,
                    direction,
                    ref values,
                } => StepReason::Input {
                    equation,
                    direction: match edge.reading {
                        Reading::Along => direction,
                        Reading::Against => direction.flipped(),
                    },
                    values: values.clone(),
                },
                Reason::Congruence => {
                    let mut children = Vec::new();
                    for child in self.children(edge)? {
                        children.push(*made.get(&child).ok_or_else(unexplained)?);
                    }
                    StepReason::Congruence { children }
                },
            };
            steps.push(Step {
                to: edge.to,
                reason,
            });
        }
        Ok(Proof { from, to, steps })
    }

    /// The nodes from `at` up to the root of its proof tree.
    ///
    /// # Specification
    /// trivial.
    fn ancestors(
        &self,
        at: TermPlace,
    ) -> Vec<TermPlace>
    {
        let mut chain = vec![at];
        let mut here = at;
        while let Some(&Some(edge)) = self.proof.get(usize::from(here)) {
            here = TermPlace::from(edge.to);
            chain.push(here);
        }
        chain
    }

    /// The path through the proof forest from the first node of `pair` to
    /// the second: up to their nearest common ancestor, then down.
    ///
    /// # Specification
    /// trivial.
    fn path(
        &self,
        (from, to): (TermPlace, TermPlace),
    ) -> Result<Vec<PathEdge>, EGraphError>
    {
        let (up, down) = (self.ancestors(from), self.ancestors(to));
        let (mut rise, mut fall) = (up.len(), down.len());
        while let (Some(previous_rise), Some(previous_fall)) =
            (rise.checked_sub(1), fall.checked_sub(1))
        {
            if up.get(previous_rise) != down.get(previous_fall) {
                break;
            }
            (rise, fall) = (previous_rise, previous_fall);
        }
        if rise == up.len() {
            return Err(EGraphError::Apart(from, to));
        }
        let edge = |node: TermPlace| match self.proof.get(usize::from(node)) {
            Some(&Some(edge)) => Ok(edge),
            Some(&None) | None => Err(EGraphError::Unexplained(from, to)),
        };
        let mut path = Vec::with_capacity(rise.saturating_add(fall));
        for &node in up.iter().take(rise) {
            let edge = edge(node)?;
            path.push(PathEdge {
                from: node,
                to: TermPlace::from(edge.to),
                reason: edge.reason,
                reading: Reading::Along,
            });
        }
        for &node in down.iter().take(fall).rev() {
            let edge = edge(node)?;
            path.push(PathEdge {
                from: TermPlace::from(edge.to),
                to: node,
                reason: edge.reason,
                reading: Reading::Against,
            });
        }
        Ok(path)
    }
}

impl Explanation
{
    /// Check the explanation step by step against `table` and `equations`
    /// alone: each input step is its equation at its values, each congruence
    /// step joins two nodes of one head whose arguments its earlier proofs
    /// join, and the last proof joins `left` to `right`.
    ///
    /// # Specification
    /// - ensures: the result is `Ok` exactly when every step of every proof
    ///   holds, each proof's steps end at its last term, and the last proof
    ///   joins `left` to `right`.
    /// - fails: each [`Refusal`] names the first fault that the check meets.
    /// - panics: none.
    /// - executable: none — the ensures is the check itself, and the call holds
    ///   no second check to compare.
    /// - intension: one walk over the steps, each congruence's proofs read by
    ///   their place; each input step reads the two sides of its equation once.
    ///
    /// # Errors
    /// - [`Refusal`]: a forged or broken step, by name.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each forgery of a true explanation meets its own
    ///   refusal, and the true explanation replays.
    /// - witness: `tests::explain::a_forged_step_is_refused_by_name`
    /// - witness: `tests::explain::each_explanation_replays`
    #[inline]
    pub fn replay(
        &self,
        table: &TermTable,
        equations: &[Equation],
        (left, right): (TermPlace, TermPlace),
    ) -> Result<(), Refusal>
    {
        let last = self.proofs.last().ok_or(Refusal::Empty)?;
        for (index, proof) in self.proofs.iter().enumerate() {
            let place = ProofPlace::from(index);
            let mut at = proof.from;
            for (step_index, step) in proof.steps.iter().enumerate() {
                let step_place = StepPlace::from(step_index);
                match step.reason {
                    StepReason::Input {
                        equation,
                        direction,
                        ref values,
                    } => {
                        let stated = equations.get(usize::from(equation)).ok_or(
                            Refusal::UnknownEquation {
                                proof: place,
                                step: step_place,
                            },
                        )?;
                        let (start, end) = match direction {
                            Direction::Forward => (stated.left, stated.right),
                            Direction::Backward => (stated.right, stated.left),
                        };
                        if instance(table, (start, values), at)? == Agreement::Differs
                            || instance(table, (end, values), step.to)? == Agreement::Differs
                        {
                            return Err(Refusal::NotAnInstance {
                                proof: place,
                                step: step_place,
                            });
                        }
                    },
                    StepReason::Congruence { ref children } => {
                        let have = table.node(at).map_err(Refusal::Table)?;
                        let want = table.node(step.to).map_err(Refusal::Table)?;
                        if have.head != want.head
                            || have.children.len() != want.children.len()
                            || children.len() != have.children.len()
                        {
                            return Err(Refusal::Incongruent {
                                proof: place,
                                step: step_place,
                            });
                        }
                        let arguments = have.children.iter().zip(&want.children);
                        for (position, (&child, (&from, &to))) in
                            children.iter().zip(arguments).enumerate()
                        {
                            let position = Position::from(position);
                            if usize::from(child) >= index {
                                return Err(Refusal::Forward {
                                    proof: place,
                                    step: step_place,
                                    position,
                                });
                            }
                            let joins = self
                                .proofs
                                .get(usize::from(child))
                                .is_some_and(|named| named.from == from && named.to == to);
                            if !joins {
                                return Err(Refusal::ChildUnexplained {
                                    proof: place,
                                    step: step_place,
                                    position,
                                });
                            }
                        }
                    },
                }
                at = step.to;
            }
            if at != proof.to {
                return Err(Refusal::Broken { proof: place });
            }
        }
        if (last.from, last.to) != (left, right) {
            return Err(Refusal::Ends);
        }
        Ok(())
    }
}

/// Whether a term is an instance of a pattern.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Agreement
{
    /// The term is the pattern under the values.
    Agrees,
    /// The term is not.
    Differs,
}

/// Whether the term at `term` is `pattern` with each variable `x` replaced by
/// `values[x]`, read from `table` with no change to it.
///
/// # Specification
/// trivial.
fn instance(
    table: &TermTable,
    (pattern, values): (TermPlace, &[TermPlace]),
    term: TermPlace,
) -> Result<Agreement, Refusal>
{
    let mut pending = vec![(pattern, term)];
    while let Some((want, have)) = pending.pop() {
        let wanted = table.node(want).map_err(Refusal::Table)?;
        match wanted.head {
            TermHead::Var(variable) => {
                if values.get(usize::from(variable)) != Some(&have) {
                    return Ok(Agreement::Differs);
                }
            },
            TermHead::Op(_) => {
                let had = table.node(have).map_err(Refusal::Table)?;
                if had.head != wanted.head || had.children.len() != wanted.children.len() {
                    return Ok(Agreement::Differs);
                }
                pending.extend(
                    wanted
                        .children
                        .iter()
                        .copied()
                        .zip(had.children.iter().copied()),
                );
            },
        }
    }
    Ok(Agreement::Agrees)
}
