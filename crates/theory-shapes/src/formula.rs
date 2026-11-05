//! Face formulas over finite membership atoms, and the entailment queries in
//! the conjunctive band, its column disjunctions and the monotone band.

use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;
use gandr_theory_stone_duality::Generator;
use gandr_theory_stone_duality::Polynomial;

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

/// The band an admitted query lies in, which names how [`decide`] reads it.
///
/// [`decide`]: crate::decide
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Band
{
    /// The conjunctive band and its column disjunctions: each side is the
    /// list of its conjuncts.
    Conjunctive,
    /// Every atom of both tables is monotone, and a disjunction may cross
    /// variables: each side is a polynomial of the free distributive lattice
    /// on the context's variables, in normal form.
    Monotone
    {
        /// The premise's normal form.
        premise: Polynomial,
        /// The conclusion's normal form.
        conclusion: Polynomial,
    },
}

/// An admitted entailment query over a context of finite carriers.
///
/// In the conjunctive band the premise is a conjunction of membership atoms
/// and the conclusion a conjunction of membership atoms and column
/// disjunctions. In the monotone band every atom is `⊤`, `⊥` or the upper
/// point of a carrier of two points, and the connectives are free.
///
/// # Specification
/// - ensures: every atom of both formulas names a variable of the context and a
///   subshape of its carrier. In the conjunctive band the premise holds no
///   disjunction, and every disjunction of the conclusion has its atoms on one
///   variable. In the monotone band every atom of both tables is monotone.
/// - provides: one query for [`decide`] and both validators, with the conjuncts
///   of each side listed once, or the normal form of each side.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — ill-scoped, ill-carried and disjunctive atoms on either
///   side are refused, a column disjunction is admitted as a conclusion alone,
///   and a disjunction across variables is admitted only when every atom is
///   monotone; L2 — every admitted generated query is decided in agreement with
///   brute force.
/// - witness: `tests::faces::input_boundaries_are_checked`
/// - witness: `tests::faces::generated_queries_agree_with_brute_force`
/// - witness: `tests::faces::the_monotone_band_admits_positive_formulas_only`
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
    /// The premise's reachable conjuncts, in node order; empty in the
    /// monotone band.
    premise_atoms: Vec<NodeId>,
    /// The conclusion's reachable conjuncts, in node order; empty in the
    /// monotone band.
    conclusion_atoms: Vec<NodeId>,
    /// The band the query lies in.
    band: Band,
}

impl Problem
{
    /// Admits a query in the conjunctive band and its column disjunctions, or
    /// else in the monotone band.
    ///
    /// # Specification
    /// - ensures: both formulas are admitted against the context, the premise
    ///   first; the conjuncts of each are listed in node order. A query that
    ///   the conjunctive band refuses by a disjunction is admitted in the
    ///   monotone band when every atom of both tables is monotone.
    /// - fails: the premise's first offending node is refused before the
    ///   conclusion's: an atom outside the context or in another carrier by its
    ///   variable, a disjunction outside both bands by its node. A monotone
    ///   query whose normal form could pass the term budget is refused by the
    ///   node where it could.
    /// - panics: none.
    /// - intension: the conjunctive band is tried first, so a query it admits
    ///   takes the same path and the same work as before the monotone band.
    ///
    /// # Errors
    /// - [`ShapeError::VariableOutside`]: an atom's variable is not in the
    ///   context.
    /// - [`ShapeError::WrongCarrier`]: an atom's subshape is not of its
    ///   variable's carrier.
    /// - [`ShapeError::Disjunction`]: the premise holds a disjunction, or the
    ///   conclusion holds one whose atoms are not all on one variable, and an
    ///   atom of the query is not monotone.
    /// - [`ShapeError::PastBudget`]: every atom is monotone, but a normal form
    ///   could pass the term budget.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each refusal on the premise alone and on the
    ///   conclusion alone, and an atom refused on both sides, separate an
    ///   admission that checks one side or names the wrong defect; a column
    ///   disjunction refused as a premise and admitted as a conclusion
    ///   separates the sides; a lower-point atom beside a disjunction across
    ///   variables separates the monotone band from the rest; L2 — generated
    ///   queries are admitted and decided.
    /// - witness: `tests::faces::input_boundaries_are_checked`
    /// - witness: `tests::faces::generated_queries_agree_with_brute_force`
    /// - witness: `tests::faces::the_monotone_band_admits_positive_formulas_only`
    #[inline]
    #[spec(ensures: |ref ret| match *ret {
        Ok(ref problem) => match problem.band {
            Band::Conjunctive => problem.premise_atoms.iter()
                    .all(|atom| matches!(problem.premise.nodes.get(usize::from(*atom)), Some(&(Node::Bottom | Node::Member(..)))))
                && problem.conclusion_atoms.iter()
                    .all(|atom| matches!(problem.conclusion.nodes.get(usize::from(*atom)), Some(&(Node::Bottom | Node::Member(..) | Node::Or(..))))),
            Band::Monotone { .. } => problem.premise_atoms.is_empty() && problem.conclusion_atoms.is_empty(),
        },
        Err(error) => matches!(error, ShapeError::VariableOutside(_) | ShapeError::WrongCarrier(_) | ShapeError::Disjunction(_) | ShapeError::PastBudget(_)),
    })]
    pub fn new(
        context: Vec<PointCount>,
        premise: Formula,
        conclusion: Formula,
    ) -> Result<Self, ShapeError>
    {
        let conjunctive = premise
            .conjuncts(&context, Side::Premise)
            .and_then(|premise_atoms| {
                conclusion
                    .conjuncts(&context, Side::Conclusion)
                    .map(|conclusion_atoms| (premise_atoms, conclusion_atoms))
            });
        let (premise_atoms, conclusion_atoms, band) = match conjunctive {
            Ok((premise_atoms, conclusion_atoms)) => {
                (premise_atoms, conclusion_atoms, Band::Conjunctive)
            },
            Err(ShapeError::Disjunction(node)) => {
                let band = match (
                    premise.polynomial(&context),
                    conclusion.polynomial(&context),
                ) {
                    (Ok(premise), Ok(conclusion)) => Band::Monotone {
                        premise,
                        conclusion,
                    },
                    (Err(Monotone::Outside), _) | (_, Err(Monotone::Outside)) => {
                        return Err(ShapeError::Disjunction(node));
                    },
                    (Err(Monotone::PastBudget(at)), _) | (_, Err(Monotone::PastBudget(at))) => {
                        return Err(ShapeError::PastBudget(at));
                    },
                };
                (Vec::new(), Vec::new(), band)
            },
            Err(error) => return Err(error),
        };
        Ok(Self {
            context,
            premise,
            conclusion,
            premise_atoms,
            conclusion_atoms,
            band,
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

    /// The band the query lies in, with each side's normal form in the
    /// monotone band.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn band(&self) -> &Band
    {
        &self.band
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

/// The most terms a normal form of the monotone band holds. A meet or a join
/// that could pass it is refused before it is built, so a conjunction of many
/// disjunctions cannot grow a normal form without bound.
const TERM_BUDGET: usize = 1024;

/// Why a formula is not admitted in the monotone band.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Monotone
{
    /// An atom of the table is not monotone, or its variable lies outside
    /// the context or past the generators of one machine word.
    Outside,
    /// The normal form at this node could pass [`TERM_BUDGET`].
    PastBudget(NodeId),
}

/// The polynomial of one monotone atom: `⊤` for the whole carrier, `⊥` for
/// the empty subshape, and the variable's generator for the upper point
/// `{1}` of a carrier of two points.
///
/// # Specification
/// - ensures: a carrier of two points with its upper point alone reads as the
///   variable's generator.
/// - fails: any other atom, an atom outside the context or in another carrier,
///   and a variable past 64, are outside the band.
/// - panics: none.
///
/// # Errors
/// - [`Monotone::Outside`]: the atom is not monotone.
///
/// # Adequacy
/// - hypothesis: L3 — the upper point is admitted, and the lower point beside a
///   disjunction across two variables keeps the present refusal.
/// - witness: `tests::faces::the_monotone_band_admits_positive_formulas_only`
#[spec(ensures: |ref ret| ret.is_ok() || *ret == Err(Monotone::Outside))]
fn monotone_atom(
    context: &[PointCount],
    variable: Variable,
    subset: &Subshape,
) -> Result<Polynomial, Monotone>
{
    let carrier = context
        .get(usize::from(variable))
        .ok_or(Monotone::Outside)?;
    if subset.ambient() != *carrier {
        return Err(Monotone::Outside);
    }
    let decisions = subset.decisions();
    if decisions
        .iter()
        .all(|decision| *decision == Membership::Inside)
    {
        return Ok(Polynomial::top());
    }
    if decisions
        .iter()
        .all(|decision| *decision == Membership::Outside)
    {
        return Ok(Polynomial::bottom());
    }
    if decisions == [Membership::Outside, Membership::Inside] {
        return Polynomial::generator(Generator::from(usize::from(variable)))
            .map_err(|_past| Monotone::Outside);
    }
    Err(Monotone::Outside)
}

/// The normal form already built at a child node.
///
/// # Specification
/// trivial.
fn form_at(
    forms: &[Polynomial],
    child: NodeId,
) -> Result<&Polynomial, Monotone>
{
    forms.get(usize::from(child)).ok_or(Monotone::Outside)
}

impl Formula
{
    /// The polynomial the formula is in the free distributive lattice on the
    /// context's variables, when every atom of its table is monotone.
    ///
    /// # Specification
    /// - ensures: the polynomial holds at a vertex exactly when the formula
    ///   holds at the assignment that gives each variable the vertex's point.
    /// - fails: a table with an atom that is not monotone is outside the band;
    ///   a node whose normal form could pass the budget is refused by the node.
    /// - panics: none.
    /// - intension: one normal form per node in table order, so the work is the
    ///   meets and joins of the normal forms, each refused before it can pass
    ///   the budget. The band is a property of the whole table, as the
    ///   conjunctive band is.
    ///
    /// # Errors
    /// - [`Monotone::Outside`]: an atom of the table is not monotone.
    /// - [`Monotone::PastBudget`]: a meet or a join could pass the budget.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every polynomial on up to four variables, spelled as
    ///   a formula, decides as its truth table; L3 — a non-monotone atom keeps
    ///   the present refusal, and a conjunction of eleven disjunctions passes
    ///   the budget.
    /// - witness: `tests::cubes::the_crate_decides_every_monotone_polynomial`
    /// - witness: `tests::faces::the_monotone_band_admits_positive_formulas_only`
    #[spec(ensures: |ref ret| ret.is_ok() || matches!(*ret, Err(Monotone::Outside | Monotone::PastBudget(_))))]
    fn polynomial(
        &self,
        context: &[PointCount],
    ) -> Result<Polynomial, Monotone>
    {
        let mut forms: Vec<Polynomial> = Vec::with_capacity(self.nodes.len());
        for (index, node) in self.nodes.iter().enumerate() {
            let form = match *node {
                Node::Top => Polynomial::top(),
                Node::Bottom => Polynomial::bottom(),
                Node::Member(variable, ref subset) => monotone_atom(context, variable, subset)?,
                Node::And(left, right) => {
                    let (left, right) = (form_at(&forms, left)?, form_at(&forms, right)?);
                    if left.terms().len().saturating_mul(right.terms().len()) > TERM_BUDGET {
                        return Err(Monotone::PastBudget(NodeId::from(index)));
                    }
                    left.meet(right)
                },
                Node::Or(left, right) => {
                    let (left, right) = (form_at(&forms, left)?, form_at(&forms, right)?);
                    if left.terms().len().saturating_add(right.terms().len()) > TERM_BUDGET {
                        return Err(Monotone::PastBudget(NodeId::from(index)));
                    }
                    left.join(right)
                },
            };
            forms.push(form);
        }
        forms.pop().ok_or(Monotone::Outside)
    }
}

/// Evaluates a formula's root at a total assignment, every node of the table
/// in order.
///
/// # Specification
/// - ensures: `Yes` exactly when the root holds: `⊤` holds, `⊥` fails, an atom
///   holds when its variable's point is inside its subshape, and the
///   connectives read as conjunction and disjunction.
/// - fails: an atom the assignment does not read is refused by name.
/// - panics: none.
/// - executable: none — the reading is the formula's semantics itself; the
///   independent evaluator in the agreement suites is its oracle.
///
/// # Errors
/// - [`ShapeError::VariableOutside`]: the assignment has no point for an atom's
///   variable.
/// - [`ShapeError::PointOutside`]: a point lies outside an atom's carrier.
/// - [`ShapeError::MalformedFormula`]: a child is not read, or the table is
///   empty.
///
/// # Adequacy
/// - hypothesis: L2 — every countermodel the monotone band returns is read
///   through this evaluator, and forged assignments on either side of the
///   premise are refused.
/// - witness: `tests::cubes::the_crate_decides_every_monotone_polynomial`
/// - witness: `tests::faces::forged_monotone_evidence_is_refused`
pub fn evaluate(
    formula: &Formula,
    assignment: &[Point],
) -> Result<Truth, ShapeError>
{
    let mut readings: Vec<Truth> = Vec::with_capacity(formula.nodes.len());
    for node in &formula.nodes {
        let reading = match *node {
            Node::Top => Truth::Yes,
            Node::Bottom => Truth::No,
            Node::Member(variable, ref subset) => member(variable, subset, assignment)?,
            Node::And(left, right) | Node::Or(left, right) => {
                let left = readings.get(usize::from(left)).copied();
                let right = readings.get(usize::from(right)).copied();
                let (Some(left), Some(right)) = (left, right)
                else {
                    return Err(ShapeError::MalformedFormula);
                };
                let both = left == Truth::Yes && right == Truth::Yes;
                let either = left == Truth::Yes || right == Truth::Yes;
                let holds = if matches!(*node, Node::And(..)) {
                    both
                }
                else {
                    either
                };
                if holds { Truth::Yes } else { Truth::No }
            },
        };
        readings.push(reading);
    }
    readings.last().copied().ok_or(ShapeError::MalformedFormula)
}
