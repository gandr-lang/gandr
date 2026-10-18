//! Conjunctive entailment decided with evidence either way, and the two
//! validators that check that evidence against the query alone.

use alloc::vec;
use alloc::vec::Vec;

use anodized::spec;

use crate::error::ShapeError;
use crate::finite::Inclusion;
use crate::finite::Membership;
use crate::finite::SetOperation;
use crate::finite::Subshape;
use crate::formula::Node;
use crate::formula::Problem;
use crate::formula::Truth;
use crate::formula::truth;
use crate::index::NodeId;
use crate::index::Point;
use crate::index::Variable;

/// The premise membership atoms one step of a derivation rests on.
///
/// # Specification
/// - provides: untrusted node indices into the premise; they count only once
///   [`Derivation::validate`] finds each a reachable membership atom of the
///   premise on the variable it is cited for.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 — forged citations naming an unreachable node, a
///   connective, `⊥`, a conclusion node and an atom of another variable are
///   refused by name.
/// - witness: `tests::faces::forged_evidence_is_refused`
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct Citation
{
    /// The cited premise nodes.
    pub atoms: Vec<NodeId>,
}

/// A derivation of entailment in the finite face lattice: untrusted data,
/// checked by [`Self::validate`].
///
/// # Specification
/// - provides: the four ways a conjunctive entailment holds over finite
///   carriers: no assignment exists, the premise reaches `⊥`, the premise's
///   atoms on one variable meet in the empty subshape, or every conclusion atom
///   includes the meet of premise atoms on its variable.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 — every derivation the oracle returns on generated queries
///   is validated, and forged derivations of each form are refused with the
///   exact refusal.
/// - witness: `tests::faces::forged_evidence_is_refused`
/// - witness: `tests::faces::generated_queries_agree_with_brute_force`
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Derivation
{
    /// The variable's carrier has no point: there is no assignment at all.
    EmptyCarrier(Variable),
    /// The premise reaches `⊥` at this node.
    FalsePremise(NodeId),
    /// The cited premise atoms, all on this variable, meet in the empty
    /// subshape: no assignment satisfies the premise.
    Disjoint(Variable, Citation),
    /// One citation per conclusion atom, in node order: the cited premise
    /// atoms lie on the conclusion atom's variable and their meet is included
    /// in its subshape (`∧`-elimination, meet, monotonicity, then
    /// `∧`-introduction).
    Supported(Vec<Citation>),
}

/// A total assignment claimed to satisfy the premise and falsify the
/// conclusion: untrusted data, checked by [`Self::validate`].
///
/// # Specification
/// - provides: one point per variable, in variable order; it counts as a
///   countermodel only once validated.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 — every countermodel the oracle returns on generated
///   queries is validated and read by an independent evaluator; forged
///   assignments of the wrong length, outside a carrier, falsifying the premise
///   or satisfying the conclusion are refused by name.
/// - witness: `tests::faces::forged_evidence_is_refused`
/// - witness: `tests::faces::generated_queries_agree_with_brute_force`
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct Countermodel
{
    /// One point per variable, in variable order.
    pub assignment: Vec<Point>,
}

/// The answer to an entailment query, with its evidence.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Evidence
{
    /// Every assignment satisfying the premise satisfies the conclusion.
    Holds(Derivation),
    /// This assignment satisfies the premise and falsifies the conclusion.
    Refuted(Countermodel),
}

/// The premise atoms on one variable, and the meet of their subshapes.
#[derive(Clone, Debug)]
struct Column
{
    /// The meet, one decision per carrier point; the full carrier when no
    /// atom lies on the variable.
    meet: Vec<Membership>,
    /// The premise atoms on the variable, in node order.
    atoms: Vec<NodeId>,
}

/// Decides whether the premise entails the conclusion, with a derivation or a
/// countermodel.
///
/// # Specification
/// - ensures: `Holds` carries a derivation [`Derivation::validate`] accepts and
///   `Refuted` a countermodel [`Countermodel::validate`] accepts, so the answer
///   is entailment at every assignment of the finite carriers.
/// - provides: a total decision of the conjunctive band. In order of
///   precedence: `EmptyCarrier` at the least variable with an empty carrier;
///   `FalsePremise` at the premise's first `⊥`; `Disjoint` at the least
///   variable whose premise atoms meet in the empty subshape, citing all of
///   them; `Refuted` at the first conclusion atom in node order whose subshape
///   misses a point of its variable's meet, every variable at the least point
///   of its meet and the refuted variable at the least point the atom misses;
///   otherwise `Supported`, citing for each conclusion atom every premise atom
///   on its variable.
/// - fails: only on a broken invariant of an admitted [`Problem`], as a typed
///   refusal; never an answer.
/// - panics: none.
/// - intension: with `s` the total size of both formulas including their
///   subshape tables, `c` and `p` the numbers of conclusion and premise atoms
///   and `d` the largest carrier, the time is `O(s + c·(p + d))` and a
///   `Supported` derivation cites at most `c·p` atoms: polynomial in the query,
///   never a case tree over the carriers' product.
///
/// # Errors
/// - [`ShapeError::VariableOutside`], [`ShapeError::MalformedFormula`]:
///   unreachable for an admitted problem; a listed atom that is not one.
///
/// # Adequacy
/// - hypothesis: L1 — every answer is validated against the query by the
///   validators, which share no code with the decision; L2 — every atom pair,
///   every conjunction of two atoms against every atom in both directions, and
///   256 generated conjunctive tables per context, over every context of up to
///   two variables with carriers of up to four points and three variables of up
///   to two, against an independent truth table, separate a wrong polarity, a
///   lost atom and a wrong meet; L3 — an empty carrier, a premise `⊥` and a
///   disjoint premise pin the precedence, and a wide conjunction pins the size
///   bound.
/// - witness: `tests::faces::generated_queries_agree_with_brute_force`
/// - witness: `tests::faces::evidence_follows_the_stated_precedence`
/// - witness: `tests::faces::conjunctive_evidence_stays_polynomial`
/// - witness: `tests::faces::deep_formulas_use_no_call_stack`
#[inline]
#[spec(ensures: |ref ret| match *ret {
    Ok(Evidence::Holds(ref derivation)) => derivation.validate(problem).is_ok(),
    Ok(Evidence::Refuted(ref countermodel)) => countermodel.validate(problem).is_ok(),
    Err(error) => matches!(error, ShapeError::VariableOutside(_) | ShapeError::MalformedFormula),
})]
pub fn decide(problem: &Problem) -> Result<Evidence, ShapeError>
{
    let (context, premise, conclusion) = problem.parts();
    if let Some(variable) = context
        .iter()
        .position(|carrier| usize::from(*carrier) == 0)
    {
        return Ok(Evidence::Holds(Derivation::EmptyCarrier(Variable::from(
            variable,
        ))));
    }
    let mut columns: Vec<Column> = context
        .iter()
        .map(|carrier| Column {
            meet: vec![Membership::Inside; usize::from(*carrier)],
            atoms: Vec::new(),
        })
        .collect();
    for &atom in problem.premise_atoms() {
        match premise.nodes().get(usize::from(atom)) {
            Some(&Node::Member(variable, ref subset)) => {
                let column = columns
                    .get_mut(usize::from(variable))
                    .ok_or(ShapeError::VariableOutside(variable))?;
                for (entry, decision) in column.meet.iter_mut().zip(subset.decisions()) {
                    if *decision == Membership::Outside {
                        *entry = Membership::Outside;
                    }
                }
                column.atoms.push(atom);
            },
            Some(&Node::Bottom) => return Ok(Evidence::Holds(Derivation::FalsePremise(atom))),
            Some(&(Node::Top | Node::And(..) | Node::Or(..))) | None => {
                return Err(ShapeError::MalformedFormula);
            },
        }
    }
    let mut assignment = Vec::with_capacity(columns.len());
    for (variable, column) in columns.iter().enumerate() {
        match column
            .meet
            .iter()
            .position(|decision| *decision == Membership::Inside)
        {
            Some(point) => assignment.push(Point::from(point)),
            None => {
                return Ok(Evidence::Holds(Derivation::Disjoint(
                    Variable::from(variable),
                    Citation {
                        atoms: column.atoms.clone(),
                    },
                )));
            },
        }
    }
    let mut supports = Vec::with_capacity(problem.conclusion_atoms().len());
    for &atom in problem.conclusion_atoms() {
        match conclusion.nodes().get(usize::from(atom)) {
            Some(&Node::Member(variable, ref subset)) => {
                let column = columns
                    .get(usize::from(variable))
                    .ok_or(ShapeError::VariableOutside(variable))?;
                let escape = column.meet.iter().zip(subset.decisions()).position(|pair| {
                    *pair.0 == Membership::Inside && *pair.1 == Membership::Outside
                });
                if let Some(point) = escape {
                    let slot = assignment
                        .get_mut(usize::from(variable))
                        .ok_or(ShapeError::VariableOutside(variable))?;
                    *slot = Point::from(point);
                    return Ok(Evidence::Refuted(Countermodel { assignment }));
                }
                supports.push(Citation {
                    atoms: column.atoms.clone(),
                });
            },
            Some(&Node::Bottom) => return Ok(Evidence::Refuted(Countermodel { assignment })),
            Some(&(Node::Top | Node::And(..) | Node::Or(..))) | None => {
                return Err(ShapeError::MalformedFormula);
            },
        }
    }
    Ok(Evidence::Holds(Derivation::Supported(supports)))
}

impl Derivation
{
    /// Checks the derivation against the query, without deciding it.
    ///
    /// # Specification
    /// - ensures: success means the premise entails the conclusion at every
    ///   assignment: `EmptyCarrier` names a variable whose carrier is empty;
    ///   `FalsePremise` names a `⊥` the premise's root reaches; `Disjoint`
    ///   cites premise membership atoms of its variable whose meet is empty;
    ///   `Supported` holds one citation per conclusion atom, in node order,
    ///   each citing premise membership atoms of that atom's variable whose
    ///   meet the atom includes, and no conclusion atom is `⊥`.
    /// - fails: a derivation that does not establish the entailment is refused
    ///   with the first defect found, by the variable or node it concerns.
    /// - panics: none.
    /// - executable: none — the validator is itself the evidence route; its
    ///   oracle is the brute-force agreement suite, and an exit predicate could
    ///   only repeat the check.
    ///
    /// # Errors
    /// - [`ShapeError::VariableOutside`]: a named variable is not in the
    ///   context.
    /// - [`ShapeError::CarrierInhabited`]: `EmptyCarrier` names a variable with
    ///   a point.
    /// - [`ShapeError::NotPremiseBottom`]: `FalsePremise` names a node that is
    ///   not a reachable `⊥` of the premise.
    /// - [`ShapeError::NotPremiseMember`]: a citation names a node that is not
    ///   a reachable membership atom of the premise.
    /// - [`ShapeError::CitedVariable`]: a citation names an atom of another
    ///   variable.
    /// - [`ShapeError::NotDisjoint`]: `Disjoint`'s cited atoms meet in a
    ///   nonempty subshape.
    /// - [`ShapeError::CitationCount`]: `Supported` does not hold one citation
    ///   per conclusion atom.
    /// - [`ShapeError::Unsupported`]: a conclusion atom is `⊥`, or does not
    ///   include the meet of its citation.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — every derivation the oracle returns on generated
    ///   queries is accepted; forged derivations of each form, each carrying
    ///   one defect, are refused with the exact refusal, and a valid derivation
    ///   replayed against another query is refused.
    /// - witness: `tests::faces::forged_evidence_is_refused`
    /// - witness: `tests::faces::generated_queries_agree_with_brute_force`
    #[inline]
    pub fn validate(
        &self,
        problem: &Problem,
    ) -> Result<(), ShapeError>
    {
        let (context, premise, conclusion) = problem.parts();
        match *self {
            Self::EmptyCarrier(variable) => {
                let carrier = context
                    .get(usize::from(variable))
                    .ok_or(ShapeError::VariableOutside(variable))?;
                if usize::from(*carrier) == 0 {
                    Ok(())
                }
                else {
                    Err(ShapeError::CarrierInhabited(variable))
                }
            },
            Self::FalsePremise(node) => {
                let reached = problem.premise_atoms().binary_search(&node).is_ok();
                if reached && premise.nodes().get(usize::from(node)) == Some(&Node::Bottom) {
                    Ok(())
                }
                else {
                    Err(ShapeError::NotPremiseBottom(node))
                }
            },
            Self::Disjoint(variable, ref citation) => {
                let meet = cited_meet(problem, variable, citation)?;
                if meet.decisions().contains(&Membership::Inside) {
                    Err(ShapeError::NotDisjoint(variable))
                }
                else {
                    Ok(())
                }
            },
            Self::Supported(ref citations) => {
                if citations.len() != problem.conclusion_atoms().len() {
                    return Err(ShapeError::CitationCount);
                }
                for (&atom, citation) in problem.conclusion_atoms().iter().zip(citations) {
                    let Some(&Node::Member(variable, ref subset)) =
                        conclusion.nodes().get(usize::from(atom))
                    else {
                        return Err(ShapeError::Unsupported(atom));
                    };
                    let meet = cited_meet(problem, variable, citation)?;
                    let inclusion = meet.included(subset)?;
                    if let Inclusion::Escapes(_) = inclusion {
                        return Err(ShapeError::Unsupported(atom));
                    }
                }
                Ok(())
            },
        }
    }
}

/// The meet of a citation's premise atoms, all on one variable.
///
/// # Specification
/// - ensures: the meet lies in the variable's carrier and is the intersection
///   of every cited atom's subshape, the full carrier when nothing is cited.
/// - fails: a variable outside the context, a cited node that is not a
///   reachable membership atom of the premise, and a cited atom of another
///   variable are refused, the first cited defect first.
/// - panics: none.
///
/// # Errors
/// - [`ShapeError::VariableOutside`]: `variable` is not in the context.
/// - [`ShapeError::NotPremiseMember`]: a cited node is not a reachable
///   membership atom of the premise.
/// - [`ShapeError::CitedVariable`]: a cited atom lies on another variable.
///
/// # Adequacy
/// - hypothesis: L1 — forged citations of each defect are refused by name, and
///   a citation missing one needed atom leaves a meet the conclusion does not
///   include.
/// - witness: `tests::faces::forged_evidence_is_refused`
#[spec(ensures: |ref ret| match *ret {
    Ok(ref meet) => problem.parts().0.get(usize::from(variable)) == Some(&meet.ambient()),
    Err(ShapeError::VariableOutside(outside)) => outside == variable && usize::from(variable) >= problem.parts().0.len(),
    Err(ShapeError::NotPremiseMember(atom) | ShapeError::CitedVariable(atom)) => citation.atoms.contains(&atom),
    Err(_) => false,
})]
fn cited_meet(
    problem: &Problem,
    variable: Variable,
    citation: &Citation,
) -> Result<Subshape, ShapeError>
{
    let (context, premise, _) = problem.parts();
    let carrier = context
        .get(usize::from(variable))
        .ok_or(ShapeError::VariableOutside(variable))?;
    let empty = Subshape::new(*carrier, &[])?;
    let mut meet = empty.complement();
    for &atom in &citation.atoms {
        if problem.premise_atoms().binary_search(&atom).is_err() {
            return Err(ShapeError::NotPremiseMember(atom));
        }
        match premise.nodes().get(usize::from(atom)) {
            Some(&Node::Member(cited, ref subset)) => {
                if cited != variable {
                    return Err(ShapeError::CitedVariable(atom));
                }
                meet = meet.combine(subset, SetOperation::Meet)?;
            },
            Some(&(Node::Top | Node::Bottom | Node::And(..) | Node::Or(..))) | None => {
                return Err(ShapeError::NotPremiseMember(atom));
            },
        }
    }
    Ok(meet)
}

impl Countermodel
{
    /// Checks the assignment against the query, without deciding it.
    ///
    /// # Specification
    /// - ensures: success means the assignment gives every variable a point of
    ///   its carrier, satisfies the premise and falsifies the conclusion.
    /// - fails: an assignment of the wrong length, a point outside its carrier
    ///   by its variable, and an assignment that is not a countermodel are
    ///   refused, in that order.
    /// - panics: none.
    /// - executable: none — the validator is itself the evidence route; the
    ///   agreement suite reads every countermodel with an independent
    ///   evaluator.
    ///
    /// # Errors
    /// - [`ShapeError::AssignmentLength`]: the assignment and the context
    ///   differ in length.
    /// - [`ShapeError::AssignedOutside`]: the named variable's point lies
    ///   outside its carrier.
    /// - [`ShapeError::NotCountermodel`]: the premise fails or the conclusion
    ///   holds.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — every countermodel the oracle returns on generated
    ///   queries is accepted; L3 — forged assignments one short, one long, one
    ///   point past a carrier, falsifying the premise and satisfying the
    ///   conclusion are refused with the exact refusal.
    /// - witness: `tests::faces::forged_evidence_is_refused`
    /// - witness: `tests::faces::generated_queries_agree_with_brute_force`
    #[inline]
    pub fn validate(
        &self,
        problem: &Problem,
    ) -> Result<(), ShapeError>
    {
        let (context, premise, conclusion) = problem.parts();
        if self.assignment.len() != context.len() {
            return Err(ShapeError::AssignmentLength);
        }
        for (variable, (carrier, point)) in context.iter().zip(&self.assignment).enumerate() {
            if usize::from(*point) >= usize::from(*carrier) {
                return Err(ShapeError::AssignedOutside(Variable::from(variable)));
            }
        }
        let premise_truth = truth(premise, problem.premise_atoms(), &self.assignment)?;
        let conclusion_truth = truth(conclusion, problem.conclusion_atoms(), &self.assignment)?;
        if premise_truth == Truth::Yes && conclusion_truth == Truth::No {
            Ok(())
        }
        else {
            Err(ShapeError::NotCountermodel)
        }
    }
}
