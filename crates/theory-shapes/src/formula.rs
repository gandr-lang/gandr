//! Face formulas over finite membership atoms, and the entailment queries in
//! the conjunctive band and its column disjunctions.

use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;

use crate::error::ShapeError;
use crate::finite::Membership;
use crate::finite::Subshape;
use crate::index::NodeId;
use crate::index::Point;
use crate::index::PointCount;
use crate::index::Variable;

/// One node of a formula table; a child precedes its parent.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Node
{
    /// Truth, `⊤`.
    Top,
    /// Falsity, `⊥`.
    Bottom,
    /// The membership atom `x ∈ S`: the variable's point lies in the
    /// subshape.
    Member(Variable, Subshape),
    /// Conjunction of two earlier nodes.
    And(NodeId, NodeId),
    /// Disjunction of two earlier nodes.
    Or(NodeId, NodeId),
}

/// A face formula: a nonempty, topologically ordered table rooted at its last
/// node.
///
/// # Specification
/// - ensures: every child index is strictly less than its parent's, so the
///   table is acyclic and its last node is the root.
/// - provides: shared, stack-safe syntax for the bounded distributive lattice
///   over membership atoms; scopes and carriers are checked by
///   [`Problem::new`]. A node the root does not reach has no meaning.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — generated conjunctive tables with shared nodes, against
///   an independent truth-table evaluator, separate the connectives' readings;
///   L3 — an empty table and forward and self references separate the ordering
///   check.
/// - witness: `tests::faces::generated_queries_agree_with_brute_force`
/// - witness: `tests::faces::input_boundaries_are_checked`
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Formula
{
    /// The nodes, every child before its parent and the root last.
    nodes: Vec<Node>,
}

impl Formula
{
    /// Admits a topologically ordered formula table.
    ///
    /// # Specification
    /// - ensures: the table is nonempty and every child index is less than its
    ///   parent's.
    /// - fails: an empty table, and a table with a child at or after its
    ///   parent, are refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ShapeError::MalformedFormula`]: the table is empty or a child does
    ///   not precede its parent.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the empty table, a self reference and a forward
    ///   reference on either child separate the ordering check from a check of
    ///   one child; L2 — generated tables with shared nodes are admitted.
    /// - witness: `tests::faces::input_boundaries_are_checked`
    /// - witness: `tests::faces::generated_queries_agree_with_brute_force`
    #[inline]
    #[spec(ensures: |ref ret| match *ret {
        Ok(ref formula) => !formula.nodes.is_empty(),
        Err(error) => error == ShapeError::MalformedFormula,
    })]
    pub fn new(nodes: Vec<Node>) -> Result<Self, ShapeError>
    {
        if nodes.is_empty() {
            return Err(ShapeError::MalformedFormula);
        }
        for (index, node) in nodes.iter().enumerate() {
            if let Node::And(left, right) | Node::Or(left, right) = *node
                && (usize::from(left) >= index || usize::from(right) >= index)
            {
                return Err(ShapeError::MalformedFormula);
            }
        }
        Ok(Self { nodes })
    }

    /// Borrows the table, root last.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn nodes(&self) -> &[Node]
    {
        &self.nodes
    }

    /// Admits the formula as one side of a query and lists the conjuncts its
    /// root reaches.
    ///
    /// A column disjunction is a disjunction whose every operand is a
    /// membership atom or a column disjunction, all on one variable: `x ∈ S₁
    /// ∨ … ∨ x ∈ Sₙ`, which holds exactly when `x ∈ S₁ ∪ … ∪ Sₙ`.
    ///
    /// # Specification
    /// - ensures: every membership atom of the table names a variable of the
    ///   context and a subshape of that variable's carrier; a premise holds no
    ///   disjunction and every disjunction of a conclusion is a column
    ///   disjunction. The list holds every `⊥`, membership and (in a
    ///   conclusion) disjunction node the root reaches through conjunctions,
    ///   once each, in node order.
    /// - provides: the conjuncts the formula is: it holds at an assignment
    ///   exactly when every listed conjunct does.
    /// - fails: the first offending node in table order is refused: an atom
    ///   outside the context or in another carrier by its variable, a
    ///   disjunction outside the band by its node.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ShapeError::VariableOutside`]: an atom's variable is not in the
    ///   context.
    /// - [`ShapeError::WrongCarrier`]: an atom's subshape is not of its
    ///   variable's carrier.
    /// - [`ShapeError::Disjunction`]: a premise holds a disjunction, or a
    ///   conclusion holds one that is not a column disjunction.
    /// - [`ShapeError::MalformedFormula`]: unreachable for an admitted table; a
    ///   child outside the table.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an atom past the context, an atom in a smaller and in
    ///   a larger carrier and a disjunction, on either side of a query,
    ///   separate the scope, carrier and band checks, and a one-variable
    ///   disjunction admitted as a conclusion beside one across two variables
    ///   and one over `⊤` separates the column check; L2 — generated tables
    ///   whose root leaves atoms unreached, against an independent evaluator of
    ///   the root, separate a list that keeps an unreached atom or drops a
    ///   reached one.
    /// - witness: `tests::faces::input_boundaries_are_checked`
    /// - witness: `tests::faces::generated_queries_agree_with_brute_force`
    #[spec(ensures: |ref ret| match *ret {
        Ok(ref atoms) => atoms.iter().zip(atoms.iter().skip(1)).all(|pair| pair.0 < pair.1)
            && atoms.iter().all(|atom| match self.nodes.get(usize::from(*atom)) {
                Some(&(Node::Bottom | Node::Member(..))) => true,
                Some(&Node::Or(..)) => side == Side::Conclusion,
                _ => false,
            }),
        Err(ShapeError::VariableOutside(variable)) => usize::from(variable) >= context.len(),
        Err(ShapeError::WrongCarrier(variable)) => usize::from(variable) < context.len(),
        Err(ShapeError::Disjunction(node)) => matches!(self.nodes.get(usize::from(node)), Some(&Node::Or(..))),
        Err(error) => error == ShapeError::MalformedFormula,
    })]
    fn conjuncts(
        &self,
        context: &[PointCount],
        side: Side,
    ) -> Result<Vec<NodeId>, ShapeError>
    {
        // The variable every atom under a node names, when the node is an atom
        // or a column disjunction.
        let mut columns: Vec<Option<Variable>> = Vec::with_capacity(self.nodes.len());
        for (index, node) in self.nodes.iter().enumerate() {
            let column = match *node {
                Node::Member(variable, ref subset) => {
                    let carrier = context
                        .get(usize::from(variable))
                        .ok_or(ShapeError::VariableOutside(variable))?;
                    if subset.ambient() != *carrier {
                        return Err(ShapeError::WrongCarrier(variable));
                    }
                    Some(variable)
                },
                Node::Or(left, right) => {
                    let left = columns.get(usize::from(left)).copied().flatten();
                    let right = columns.get(usize::from(right)).copied().flatten();
                    match (side, left, right) {
                        (Side::Conclusion, Some(left), Some(right)) if left == right => Some(left),
                        _ => return Err(ShapeError::Disjunction(NodeId::from(index))),
                    }
                },
                Node::Top | Node::Bottom | Node::And(..) => None,
            };
            columns.push(column);
        }
        let mut reach = vec![Reach::Unreached; self.nodes.len()];
        if let Some(root) = reach.last_mut() {
            *root = Reach::Reached;
        }
        let mut atoms = Vec::new();
        for (index, node) in self.nodes.iter().enumerate().rev() {
            if reach.get(index) != Some(&Reach::Reached) {
                continue;
            }
            match *node {
                Node::And(left, right) => {
                    for child in [left, right] {
                        let slot = reach
                            .get_mut(usize::from(child))
                            .ok_or(ShapeError::MalformedFormula)?;
                        *slot = Reach::Reached;
                    }
                },
                Node::Bottom | Node::Member(..) | Node::Or(..) => atoms.push(NodeId::from(index)),
                Node::Top => {},
            }
        }
        atoms.reverse();
        Ok(atoms)
    }
}

/// Which side of a query a formula stands on.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Side
{
    /// The assumed face: conjunctions of atoms only.
    Premise,
    /// The required face: conjunctions of atoms and column disjunctions.
    Conclusion,
}

/// Whether the root of a formula reaches a node.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Reach
{
    /// The root reaches the node.
    Reached,
    /// No path from the root reaches the node.
    Unreached,
}

/// The truth of a formula at a total assignment.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Truth
{
    /// The formula holds.
    Yes,
    /// The formula fails.
    No,
}

/// An admitted entailment query over a context of finite carriers.
///
/// The premise is a conjunction of membership atoms; the conclusion a
/// conjunction of membership atoms and column disjunctions.
///
/// # Specification
/// - ensures: every atom of both formulas names a variable of the context and a
///   subshape of its carrier; the premise holds no disjunction, and every
///   disjunction of the conclusion has its atoms on one variable.
/// - provides: one query for [`decide`] and both validators, with the conjuncts
///   of each side listed once.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — ill-scoped, ill-carried and disjunctive atoms on either
///   side are refused, and a column disjunction is admitted as a conclusion
///   alone; L2 — every admitted generated query is decided in agreement with
///   brute force.
/// - witness: `tests::faces::input_boundaries_are_checked`
/// - witness: `tests::faces::generated_queries_agree_with_brute_force`
///
/// [`decide`]: crate::decide
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Problem
{
    /// One finite carrier per variable, in variable order.
    context: Vec<PointCount>,
    /// The assumed face.
    premise: Formula,
    /// The required face.
    conclusion: Formula,
    /// The premise's reachable conjuncts, in node order.
    premise_atoms: Vec<NodeId>,
    /// The conclusion's reachable conjuncts, in node order.
    conclusion_atoms: Vec<NodeId>,
}

impl Problem
{
    /// Admits a query in the conjunctive band and its column disjunctions.
    ///
    /// # Specification
    /// - ensures: both formulas are admitted against the context, the premise
    ///   first; the conjuncts of each are listed in node order.
    /// - fails: the premise's first offending node is refused before the
    ///   conclusion's: an atom outside the context or in another carrier by its
    ///   variable, a disjunction outside the band by its node.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`ShapeError::VariableOutside`]: an atom's variable is not in the
    ///   context.
    /// - [`ShapeError::WrongCarrier`]: an atom's subshape is not of its
    ///   variable's carrier.
    /// - [`ShapeError::Disjunction`]: the premise holds a disjunction, or the
    ///   conclusion holds one whose atoms are not all on one variable.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each refusal on the premise alone and on the
    ///   conclusion alone, and an atom refused on both sides, separate an
    ///   admission that checks one side or names the wrong defect; a column
    ///   disjunction refused as a premise and admitted as a conclusion
    ///   separates the sides; L2 — generated queries are admitted and decided.
    /// - witness: `tests::faces::input_boundaries_are_checked`
    /// - witness: `tests::faces::generated_queries_agree_with_brute_force`
    #[inline]
    #[spec(ensures: |ref ret| match *ret {
        Ok(ref problem) => problem.premise_atoms.iter()
                .all(|atom| matches!(problem.premise.nodes.get(usize::from(*atom)), Some(&(Node::Bottom | Node::Member(..)))))
            && problem.conclusion_atoms.iter()
                .all(|atom| matches!(problem.conclusion.nodes.get(usize::from(*atom)), Some(&(Node::Bottom | Node::Member(..) | Node::Or(..))))),
        Err(error) => matches!(error, ShapeError::VariableOutside(_) | ShapeError::WrongCarrier(_) | ShapeError::Disjunction(_)),
    })]
    pub fn new(
        context: Vec<PointCount>,
        premise: Formula,
        conclusion: Formula,
    ) -> Result<Self, ShapeError>
    {
        let premise_atoms = premise.conjuncts(&context, Side::Premise)?;
        let conclusion_atoms = conclusion.conjuncts(&context, Side::Conclusion)?;
        Ok(Self {
            context,
            premise,
            conclusion,
            premise_atoms,
            conclusion_atoms,
        })
    }

    /// Borrows the context, the premise and the conclusion, in that order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn parts(&self) -> (&[PointCount], &Formula, &Formula)
    {
        (&self.context, &self.premise, &self.conclusion)
    }

    /// The premise's conjuncts: the `⊥` and membership nodes its root
    /// reaches, in node order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn premise_atoms(&self) -> &[NodeId]
    {
        &self.premise_atoms
    }

    /// The conclusion's conjuncts: the `⊥`, membership and column disjunction
    /// nodes its root reaches, in node order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn conclusion_atoms(&self) -> &[NodeId]
    {
        &self.conclusion_atoms
    }
}

/// Evaluates one side of an admitted query at a total assignment.
///
/// # Specification
/// - requires: `atoms` lists the conjuncts of `formula`, and `assignment` gives
///   every variable a point.
/// - ensures: `Yes` exactly when every listed conjunct holds: a membership atom
///   holds when its variable's point is inside its subshape, a column
///   disjunction when one of its operands holds, `⊥` never.
/// - fails: an assignment too short for an atom's variable, or a point outside
///   the atom's carrier, is refused by name; a listed node that is not a
///   conjunct is malformed.
/// - panics: none.
/// - executable: none — the reading is the formula's semantics itself; the
///   independent evaluator in the agreement suite is its oracle.
///
/// # Errors
/// - [`ShapeError::VariableOutside`]: the assignment has no point for an atom's
///   variable.
/// - [`ShapeError::PointOutside`]: the point lies outside the atom's carrier.
/// - [`ShapeError::MalformedFormula`]: a listed node is not a conjunct.
///
/// # Adequacy
/// - hypothesis: L2 — every countermodel the oracle returns for generated
///   queries is read by this evaluator and by an independent truth-table
///   evaluator; L3 — assignments that falsify the premise and that satisfy the
///   conclusion separate the two polarities.
/// - witness: `tests::faces::generated_queries_agree_with_brute_force`
/// - witness: `tests::faces::forged_evidence_is_refused`
pub fn truth(
    formula: &Formula,
    atoms: &[NodeId],
    assignment: &[Point],
) -> Result<Truth, ShapeError>
{
    // Each node's reading at the assignment, children first; read only once a
    // column disjunction is listed.
    let mut readings: Vec<Option<Truth>> = Vec::new();
    for &atom in atoms {
        let reading = match formula.nodes.get(usize::from(atom)) {
            Some(&Node::Member(variable, ref subset)) => member(variable, subset, assignment)?,
            Some(&Node::Or(..)) => {
                if readings.is_empty() {
                    readings = disjunctions(formula, assignment)?;
                }
                readings
                    .get(usize::from(atom))
                    .copied()
                    .flatten()
                    .ok_or(ShapeError::MalformedFormula)?
            },
            Some(&Node::Bottom) => Truth::No,
            Some(&(Node::Top | Node::And(..))) | None => {
                return Err(ShapeError::MalformedFormula);
            },
        };
        if reading == Truth::No {
            return Ok(Truth::No);
        }
    }
    Ok(Truth::Yes)
}

/// Whether a membership atom holds at the assignment.
///
/// # Specification
/// - ensures: `Yes` exactly when the variable's point is inside the subshape.
/// - fails: a variable the assignment does not reach, and a point outside the
///   subshape's carrier, are refused by name.
/// - panics: none.
///
/// # Errors
/// - [`ShapeError::VariableOutside`]: the assignment has no point for the
///   variable.
/// - [`ShapeError::PointOutside`]: the point lies outside the carrier.
///
/// # Adequacy
/// - hypothesis: L2 — every countermodel the oracle returns is read through
///   this atom reading and by an independent truth-table evaluator.
/// - witness: `tests::faces::generated_queries_agree_with_brute_force`
#[spec(ensures: |ref ret| match *ret {
    Ok(_) => usize::from(variable) < assignment.len(),
    Err(error) => matches!(error, ShapeError::VariableOutside(_) | ShapeError::PointOutside(_)),
})]
fn member(
    variable: Variable,
    subset: &Subshape,
    assignment: &[Point],
) -> Result<Truth, ShapeError>
{
    let point = assignment
        .get(usize::from(variable))
        .ok_or(ShapeError::VariableOutside(variable))?;
    Ok(match subset.contains(*point)? {
        Membership::Inside => Truth::Yes,
        Membership::Outside => Truth::No,
    })
}

/// The reading at the assignment of every membership atom and every
/// disjunction of a table, children first; `None` at every other node.
///
/// # Specification
/// - requires: every disjunction of the table is a column disjunction.
/// - ensures: one entry per node; a disjunction reads `Yes` exactly when one of
///   its operands does.
/// - fails: an atom the assignment does not read is refused by name; a
///   disjunction over a node that is not an atom or a disjunction is malformed.
/// - panics: none.
///
/// # Errors
/// - [`ShapeError::VariableOutside`]: the assignment has no point for an atom's
///   variable.
/// - [`ShapeError::PointOutside`]: a point lies outside an atom's carrier.
/// - [`ShapeError::MalformedFormula`]: a disjunction's operand is not read.
///
/// # Adequacy
/// - hypothesis: L2 — every countermodel the oracle returns for a generated
///   column conclusion is read through these readings and by an independent
///   truth-table evaluator.
/// - witness: `tests::faces::generated_queries_agree_with_brute_force`
#[spec(ensures: |ref ret| match *ret {
    Ok(ref readings) => readings.len() == formula.nodes.len(),
    Err(error) => matches!(error, ShapeError::VariableOutside(_) | ShapeError::PointOutside(_) | ShapeError::MalformedFormula),
})]
fn disjunctions(
    formula: &Formula,
    assignment: &[Point],
) -> Result<Vec<Option<Truth>>, ShapeError>
{
    let mut readings: Vec<Option<Truth>> = Vec::with_capacity(formula.nodes.len());
    for node in &formula.nodes {
        let reading = match *node {
            Node::Member(variable, ref subset) => Some(member(variable, subset, assignment)?),
            Node::Or(left, right) => {
                let left = readings.get(usize::from(left)).copied().flatten();
                let right = readings.get(usize::from(right)).copied().flatten();
                match (left, right) {
                    (Some(Truth::Yes), Some(_)) | (Some(_), Some(Truth::Yes)) => Some(Truth::Yes),
                    (Some(Truth::No), Some(Truth::No)) => Some(Truth::No),
                    _ => return Err(ShapeError::MalformedFormula),
                }
            },
            Node::Top | Node::Bottom | Node::And(..) => None,
        };
        readings.push(reading);
    }
    Ok(readings)
}
