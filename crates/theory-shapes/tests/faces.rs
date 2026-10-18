//! Conjunctive entailment: agreement with an independent truth table, the
//! stated precedence and size of the evidence, hostile evidence, and the
//! refusals of query admission.

use gandr_theory_shapes::Citation;
use gandr_theory_shapes::Countermodel;
use gandr_theory_shapes::Derivation;
use gandr_theory_shapes::Evidence;
use gandr_theory_shapes::Formula;
use gandr_theory_shapes::Membership;
use gandr_theory_shapes::Node;
use gandr_theory_shapes::NodeId;
use gandr_theory_shapes::Point;
use gandr_theory_shapes::PointCount;
use gandr_theory_shapes::Problem;
use gandr_theory_shapes::ShapeError;
use gandr_theory_shapes::Subshape;
use gandr_theory_shapes::Variable;
use gandr_theory_shapes::decide;

use crate::carriers::points;
use crate::carriers::subsets;

/// The truth of a formula at an assignment, as the reference evaluator reads
/// it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Reading
{
    /// The formula holds.
    Holds,
    /// The formula fails.
    Fails,
}

/// Evaluates every node of a formula at a total assignment, the root last,
/// by the textbook reading of each connective; written apart from the crate's
/// conjunct lists.
///
/// # Specification
/// trivial.
fn naive(
    formula: &Formula,
    assignment: &[Point],
) -> Reading
{
    let mut values: Vec<Reading> = Vec::with_capacity(formula.nodes().len());
    for node in formula.nodes() {
        let value = match *node {
            Node::Top => Reading::Holds,
            Node::Bottom => Reading::Fails,
            Node::Member(variable, ref subset) => {
                let point = assignment[usize::from(variable)];
                if subset.decisions()[usize::from(point)] == Membership::Inside {
                    Reading::Holds
                }
                else {
                    Reading::Fails
                }
            },
            Node::And(left, right) => {
                if values[usize::from(left)] == Reading::Holds
                    && values[usize::from(right)] == Reading::Holds
                {
                    Reading::Holds
                }
                else {
                    Reading::Fails
                }
            },
            Node::Or(left, right) => {
                if values[usize::from(left)] == Reading::Holds
                    || values[usize::from(right)] == Reading::Holds
                {
                    Reading::Holds
                }
                else {
                    Reading::Fails
                }
            },
        };
        values.push(value);
    }
    *values.last().expect("a root")
}

/// Every total assignment of a context, by an odometer over the carriers; an
/// empty carrier leaves none.
///
/// # Specification
/// trivial.
fn assignments(context: &[PointCount]) -> Vec<Vec<Point>>
{
    let mut rows = vec![Vec::new()];
    for carrier in context {
        let mut product = Vec::new();
        for row in &rows {
            for point in points(*carrier) {
                let mut extended = row.clone();
                extended.push(point);
                product.push(extended);
            }
        }
        rows = product;
    }
    rows
}

/// `⊤`, `⊥` and every membership atom of a context: one per subset of each
/// variable's carrier.
///
/// # Specification
/// trivial.
fn atoms(context: &[PointCount]) -> Vec<Node>
{
    let mut nodes = vec![Node::Top, Node::Bottom];
    for (variable, carrier) in context.iter().enumerate() {
        for (_, subset) in subsets(*carrier) {
            nodes.push(Node::Member(Variable::from(variable), subset));
        }
    }
    nodes
}

/// A deterministic generator, independent of the crate's traversal order.
#[repr(transparent)]
struct Seed(u64);

impl Seed
{
    /// Draws a node index below `bound` by a fixed linear congruence.
    ///
    /// # Specification
    /// trivial.
    fn index(
        &mut self,
        bound: NodeId,
    ) -> NodeId
    {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        let bound = u64::try_from(usize::from(bound)).expect("a small bound");
        let drawn = self.0.checked_shr(33).expect("a shift below 64");
        NodeId::from(
            usize::try_from(drawn.checked_rem(bound).expect("a positive bound"))
                .expect("a small index"),
        )
    }
}

/// The derivation forms and outcomes a run of the agreement suite met.
#[derive(Debug, Default)]
struct Tally
{
    /// Queries checked.
    queries: usize,
    /// `EmptyCarrier` derivations.
    empty: usize,
    /// `FalsePremise` derivations.
    bottom: usize,
    /// `Disjoint` derivations.
    disjoint: usize,
    /// `Supported` derivations.
    supported: usize,
    /// Countermodels.
    refuted: usize,
}

/// Decides one query, checks the answer against the truth table over
/// `rows`, and validates its evidence.
///
/// # Specification
/// trivial.
fn check(
    context: &[PointCount],
    premise: &Formula,
    conclusion: &Formula,
    rows: &[Vec<Point>],
    tally: &mut Tally,
)
{
    let entailed = rows.iter().all(|row| {
        naive(premise, row) == Reading::Fails || naive(conclusion, row) == Reading::Holds
    });
    let problem = Problem::new(context.to_vec(), premise.clone(), conclusion.clone())
        .expect("a conjunctive query");
    tally.queries = tally.queries.saturating_add(1);
    match decide(&problem).expect("a decision") {
        Evidence::Holds(derivation) => {
            assert!(entailed, "a derivation for a refuted query: {problem:?}");
            assert_eq!(derivation.validate(&problem), Ok(()));
            let count = match derivation {
                Derivation::EmptyCarrier(_) => &mut tally.empty,
                Derivation::FalsePremise(_) => &mut tally.bottom,
                Derivation::Disjoint(..) => &mut tally.disjoint,
                Derivation::Supported(_) => &mut tally.supported,
            };
            *count = count.saturating_add(1);
        },
        Evidence::Refuted(model) => {
            assert!(
                !entailed,
                "a countermodel for an entailed query: {problem:?}"
            );
            assert_eq!(model.validate(&problem), Ok(()));
            assert_eq!(naive(premise, &model.assignment), Reading::Holds);
            assert_eq!(naive(conclusion, &model.assignment), Reading::Fails);
            tally.refuted = tally.refuted.saturating_add(1);
        },
    }
}

/// One formula from a node list.
///
/// # Specification
/// trivial.
fn formula(nodes: Vec<Node>) -> Formula
{
    Formula::new(nodes).expect("an ordered table")
}

/// The membership atom of variable `$variable` in the subshape of a carrier
/// of `$carrier` points holding the listed points:
/// `member!(0, 3, [0, 1])` is `x₀ ∈ {0,1}` over `Fin(3)`.
macro_rules! member {
    ($variable:expr, $carrier:expr, [$($point:expr),* $(,)?]) => {
        Node::Member(
            Variable::from($variable),
            Subshape::new(PointCount::from($carrier), &[$(Point::from($point)),*])
                .expect("a subset"),
        )
    };
}

/// A context of the listed carrier sizes: `context![3, 2]`.
macro_rules! context {
    ($($size:expr),* $(,)?) => {
        vec![$(PointCount::from($size)),*]
    };
}

/// One citation from node numbers: `cite![0, 1]`.
macro_rules! cite {
    ($($atom:expr),* $(,)?) => {
        Citation {
            atoms: vec![$(NodeId::from($atom)),*],
        }
    };
}

/// A supported derivation, one citation per bracket:
/// `supported![&[0, 1], &[4]]`.
macro_rules! supported {
    ($(&[$($atom:expr),* $(,)?]),* $(,)?) => {
        Derivation::Supported(vec![$(cite![$($atom),*]),*])
    };
}

/// One countermodel from point numbers: `countermodel![1, 0]`.
macro_rules! countermodel {
    ($($point:expr),* $(,)?) => {
        Countermodel {
            assignment: vec![$(Point::from($point)),*],
        }
    };
}

#[test]
fn generated_queries_agree_with_brute_force()
{
    let mut tally = Tally::default();
    let mut seed = Seed(0xFACE_CAFE);
    let mut contexts: Vec<Vec<PointCount>> = vec![vec![]];
    for first in 0_usize ..= 4 {
        contexts.push(context![first]);
        for second in 0_usize ..= 4 {
            contexts.push(context![first, second]);
        }
    }
    for first in 0_usize ..= 2 {
        for second in 0_usize ..= 2 {
            for third in 0_usize ..= 2 {
                contexts.push(context![first, second, third]);
            }
        }
    }
    for context in contexts {
        let rows = assignments(&context);
        let basis = atoms(&context);
        let atomic: Vec<Formula> = basis
            .iter()
            .map(|node| formula(vec![node.clone()]))
            .collect();
        for left in &atomic {
            for right in &atomic {
                check(&context, left, right, &rows, &mut tally);
            }
        }
        // Every conjunction of two atoms against every atom, both ways.
        for first in &basis {
            for second in &basis {
                let both = formula(vec![
                    first.clone(),
                    second.clone(),
                    Node::And(NodeId::from(0_usize), NodeId::from(1_usize)),
                ]);
                for atom in &atomic {
                    check(&context, &both, atom, &rows, &mut tally);
                    check(&context, atom, &both, &rows, &mut tally);
                }
            }
        }
        // Shared conjunctive tables whose roots leave some atoms unreached.
        for _ in 0_usize .. 256 {
            let mut pair = Vec::with_capacity(2);
            for _ in 0_usize .. 2 {
                let mut nodes = basis.clone();
                for _ in 0_usize .. 32 {
                    let bound = NodeId::from(nodes.len());
                    let left = seed.index(bound);
                    let right = seed.index(bound);
                    nodes.push(Node::And(left, right));
                }
                pair.push(formula(nodes));
            }
            check(&context, &pair[0], &pair[1], &rows, &mut tally);
        }
    }
    assert!(
        tally.empty > 0
            && tally.bottom > 0
            && tally.disjoint > 0
            && tally.supported > 0
            && tally.refuted > 0,
        "every evidence form is exercised: {tally:?}"
    );
    println!("face agreement: {tally:?}");
}

#[test]
fn evidence_follows_the_stated_precedence()
{
    // An empty carrier comes first, even beside a premise `⊥`.
    let problem = Problem::new(
        context![2, 0],
        formula(vec![Node::Bottom]),
        formula(vec![member!(0, 2, [])]),
    )
    .expect("query");
    assert_eq!(
        decide(&problem),
        Ok(Evidence::Holds(Derivation::EmptyCarrier(Variable::from(
            1_usize
        ))))
    );
    // A premise `⊥` comes before a disjoint pair, at its own node.
    let problem = Problem::new(
        context![2],
        formula(vec![
            member!(0, 2, [0]),
            member!(0, 2, [1]),
            Node::And(NodeId::from(0_usize), NodeId::from(1_usize)),
            Node::Bottom,
            Node::And(NodeId::from(2_usize), NodeId::from(3_usize)),
        ]),
        formula(vec![Node::Bottom]),
    )
    .expect("query");
    assert_eq!(
        decide(&problem),
        Ok(Evidence::Holds(Derivation::FalsePremise(NodeId::from(
            3_usize
        ))))
    );
    // The least disjoint variable, citing every premise atom on it.
    let problem = Problem::new(
        context![3, 3, 2],
        formula(vec![
            member!(1, 3, [0, 1]),
            member!(0, 3, [2]),
            Node::And(NodeId::from(0_usize), NodeId::from(1_usize)),
            member!(2, 2, []),
            Node::And(NodeId::from(2_usize), NodeId::from(3_usize)),
            member!(1, 3, [2]),
            Node::And(NodeId::from(4_usize), NodeId::from(5_usize)),
        ]),
        formula(vec![Node::Bottom]),
    )
    .expect("query");
    assert_eq!(
        decide(&problem),
        Ok(Evidence::Holds(Derivation::Disjoint(
            Variable::from(1_usize),
            cite![0, 5]
        )))
    );
    // The first failing conclusion atom: every variable at the least point
    // of its meet, the refuted one at the least point the atom misses.
    let problem = Problem::new(
        context![3, 3],
        formula(vec![member!(0, 3, [1, 2])]),
        formula(vec![
            member!(1, 3, [0, 1, 2]),
            member!(0, 3, [2]),
            Node::And(NodeId::from(0_usize), NodeId::from(1_usize)),
            member!(1, 3, []),
            Node::And(NodeId::from(2_usize), NodeId::from(3_usize)),
        ]),
    )
    .expect("query");
    assert_eq!(decide(&problem), Ok(Evidence::Refuted(countermodel![1, 0])));
    // A conclusion `⊥` under a satisfiable premise.
    let problem = Problem::new(
        context![2],
        formula(vec![member!(0, 2, [1])]),
        formula(vec![Node::Bottom]),
    )
    .expect("query");
    assert_eq!(decide(&problem), Ok(Evidence::Refuted(countermodel![1])));
    // Each conclusion atom cites every premise atom on its variable.
    let problem = Problem::new(
        context![3, 3],
        formula(vec![
            member!(0, 3, [0, 1]),
            member!(1, 3, [2]),
            Node::And(NodeId::from(0_usize), NodeId::from(1_usize)),
            member!(0, 3, [1, 2]),
            Node::And(NodeId::from(2_usize), NodeId::from(3_usize)),
        ]),
        formula(vec![
            member!(0, 3, [1]),
            Node::Top,
            Node::And(NodeId::from(0_usize), NodeId::from(1_usize)),
            member!(1, 3, [1, 2]),
            Node::And(NodeId::from(2_usize), NodeId::from(3_usize)),
        ]),
    )
    .expect("query");
    assert_eq!(
        decide(&problem),
        Ok(Evidence::Holds(supported![&[0, 3], &[1]]))
    );
}

#[test]
fn conjunctive_evidence_stays_polynomial()
{
    // `∧ᵢ xᵢ ∈ {0,1} ⊢ ∧ᵢ xᵢ ∈ {0,1}` over 64 three-point carriers: a case
    // tree over the carriers needs `3·2⁶⁴ − 2` rules; the derivation cites one
    // premise atom per conclusion atom.
    let width = 64_usize;
    let mut nodes = vec![Node::Top];
    for variable in 0 .. width {
        let previous = NodeId::from(nodes.len().saturating_sub(1));
        nodes.push(member!(variable, 3, [0, 1]));
        nodes.push(Node::And(
            previous,
            NodeId::from(nodes.len().saturating_sub(1)),
        ));
    }
    let side = formula(nodes);
    let problem =
        Problem::new(vec![PointCount::from(3_usize); width], side.clone(), side).expect("query");
    let Ok(Evidence::Holds(Derivation::Supported(citations))) = decide(&problem)
    else {
        panic!("a conjunction entails itself by citation");
    };
    assert_eq!(citations.len(), width);
    for (citation, atom) in citations.iter().zip(problem.conclusion_atoms()) {
        assert_eq!(citation.atoms, vec![*atom]);
    }
    assert_eq!(Derivation::Supported(citations).validate(&problem), Ok(()));
}

#[test]
fn input_boundaries_are_checked()
{
    assert_eq!(Formula::new(vec![]), Err(ShapeError::MalformedFormula));
    for bad in [
        Node::And(NodeId::from(1_usize), NodeId::from(0_usize)),
        Node::And(NodeId::from(0_usize), NodeId::from(1_usize)),
        Node::Or(NodeId::from(2_usize), NodeId::from(0_usize)),
        Node::Or(NodeId::from(0_usize), NodeId::from(2_usize)),
    ] {
        assert_eq!(
            Formula::new(vec![Node::Top, bad]),
            Err(ShapeError::MalformedFormula)
        );
    }
    let top = formula(vec![Node::Top]);
    let outside = formula(vec![member!(1, 2, [0])]);
    let smaller = formula(vec![member!(0, 1, [0])]);
    let larger = formula(vec![member!(0, 3, [0])]);
    let either = formula(vec![
        member!(0, 2, [0]),
        member!(0, 2, [1]),
        Node::Or(NodeId::from(0_usize), NodeId::from(1_usize)),
    ]);
    // An unreached disjunction is refused too: the band is a property of the
    // table.
    let unreached = formula(vec![
        Node::Top,
        Node::Or(NodeId::from(0_usize), NodeId::from(0_usize)),
        Node::Top,
    ]);
    let pair = context![2];
    for (side, refusal) in [
        (
            &outside,
            ShapeError::VariableOutside(Variable::from(1_usize)),
        ),
        (&smaller, ShapeError::WrongCarrier(Variable::from(0_usize))),
        (&larger, ShapeError::WrongCarrier(Variable::from(0_usize))),
        (&either, ShapeError::Disjunction(NodeId::from(2_usize))),
        (&unreached, ShapeError::Disjunction(NodeId::from(1_usize))),
    ] {
        assert_eq!(
            Problem::new(pair.clone(), side.clone(), top.clone()),
            Err(refusal)
        );
        assert_eq!(
            Problem::new(pair.clone(), top.clone(), side.clone()),
            Err(refusal)
        );
    }
    // The premise is admitted first; within a table, the first offending
    // node.
    assert_eq!(
        Problem::new(pair.clone(), either, outside),
        Err(ShapeError::Disjunction(NodeId::from(2_usize)))
    );
    let mixed = formula(vec![
        member!(0, 3, [0]),
        member!(1, 2, [0]),
        Node::Or(NodeId::from(0_usize), NodeId::from(1_usize)),
    ]);
    assert_eq!(
        Problem::new(pair.clone(), mixed, top.clone()),
        Err(ShapeError::WrongCarrier(Variable::from(0_usize)))
    );
    // The conjuncts are the atoms the root reaches, once each, in node order.
    let shared = formula(vec![
        member!(0, 2, [0]),
        Node::Bottom,
        member!(0, 2, [1]),
        Node::And(NodeId::from(2_usize), NodeId::from(0_usize)),
        Node::And(NodeId::from(3_usize), NodeId::from(2_usize)),
    ]);
    let problem = Problem::new(pair, shared, top).expect("query");
    assert_eq!(problem.premise_atoms(), [
        NodeId::from(0_usize),
        NodeId::from(2_usize)
    ]);
    assert!(problem.conclusion_atoms().is_empty());
}

#[test]
fn forged_evidence_is_refused()
{
    // Premise `x ∈ {0,1} ∧ x ∈ {1,2} ∧ y ∈ {1}` with an unreached
    // `y ∈ {0}` at node 2; conclusion `x ∈ {1} ∧ y ∈ {1}`.
    let premise = formula(vec![
        member!(0, 3, [0, 1]),
        member!(0, 3, [1, 2]),
        member!(1, 2, [0]),
        Node::And(NodeId::from(0_usize), NodeId::from(1_usize)),
        member!(1, 2, [1]),
        Node::And(NodeId::from(3_usize), NodeId::from(4_usize)),
    ]);
    let conclusion = formula(vec![
        member!(0, 3, [1]),
        member!(1, 2, [1]),
        Node::And(NodeId::from(0_usize), NodeId::from(1_usize)),
    ]);
    let problem = Problem::new(context![3, 2], premise.clone(), conclusion).expect("query");
    let valid = supported![&[0, 1], &[4]];
    assert_eq!(decide(&problem), Ok(Evidence::Holds(valid.clone())));
    assert_eq!(valid.validate(&problem), Ok(()));
    let node = NodeId::from;
    let variable = Variable::from;
    for (forged, refusal) in [
        (supported![&[0, 1]], ShapeError::CitationCount),
        (supported![&[0, 1], &[4], &[]], ShapeError::CitationCount),
        (supported![&[0], &[4]], ShapeError::Unsupported(node(0))),
        (supported![&[0, 1], &[]], ShapeError::Unsupported(node(1))),
        (
            supported![&[0, 1], &[2]],
            ShapeError::NotPremiseMember(node(2)),
        ),
        (
            supported![&[3], &[4]],
            ShapeError::NotPremiseMember(node(3)),
        ),
        (
            supported![&[9], &[4]],
            ShapeError::NotPremiseMember(node(9)),
        ),
        (
            supported![&[0, 4], &[4]],
            ShapeError::CitedVariable(node(4)),
        ),
        (
            supported![&[0, 1], &[0]],
            ShapeError::CitedVariable(node(0)),
        ),
        (
            Derivation::EmptyCarrier(variable(0)),
            ShapeError::CarrierInhabited(variable(0)),
        ),
        (
            Derivation::EmptyCarrier(variable(2)),
            ShapeError::VariableOutside(variable(2)),
        ),
        (
            Derivation::FalsePremise(node(0)),
            ShapeError::NotPremiseBottom(node(0)),
        ),
        (
            Derivation::Disjoint(variable(0), cite![0, 1]),
            ShapeError::NotDisjoint(variable(0)),
        ),
        (
            Derivation::Disjoint(variable(1), cite![]),
            ShapeError::NotDisjoint(variable(1)),
        ),
        (
            Derivation::Disjoint(variable(2), cite![]),
            ShapeError::VariableOutside(variable(2)),
        ),
    ] {
        assert_eq!(forged.validate(&problem), Err(refusal), "{forged:?}");
    }
    // The valid derivation, replayed against a query it does not prove.
    let stronger =
        Problem::new(context![3, 2], premise, formula(vec![member!(0, 3, [0])])).expect("query");
    assert_eq!(valid.validate(&stronger), Err(ShapeError::CitationCount));
    assert_eq!(
        supported![&[0, 1]].validate(&stronger),
        Err(ShapeError::Unsupported(node(0)))
    );

    // `⊥`: reached, unreached, cited, and as a conclusion.
    let reached = Problem::new(
        context![1],
        formula(vec![
            member!(0, 1, [0]),
            Node::Bottom,
            Node::And(node(0), node(1)),
        ]),
        formula(vec![member!(0, 1, [])]),
    )
    .expect("query");
    assert_eq!(Derivation::FalsePremise(node(1)).validate(&reached), Ok(()));
    assert_eq!(
        Derivation::FalsePremise(node(2)).validate(&reached),
        Err(ShapeError::NotPremiseBottom(node(2)))
    );
    assert_eq!(
        Derivation::Disjoint(variable(0), cite![1]).validate(&reached),
        Err(ShapeError::NotPremiseMember(node(1)))
    );
    let unreached = Problem::new(
        context![1],
        formula(vec![Node::Bottom, Node::Top]),
        formula(vec![Node::Bottom]),
    )
    .expect("query");
    assert_eq!(
        Derivation::FalsePremise(node(0)).validate(&unreached),
        Err(ShapeError::NotPremiseBottom(node(0)))
    );
    assert_eq!(
        supported![&[]].validate(&unreached),
        Err(ShapeError::Unsupported(node(0)))
    );
    assert_eq!(decide(&unreached), Ok(Evidence::Refuted(countermodel![0])));

    // Valid disjointness and emptiness.
    let disjoint = Problem::new(
        context![2, 0],
        formula(vec![
            member!(0, 2, [0]),
            member!(0, 2, [1]),
            Node::And(node(0), node(1)),
        ]),
        formula(vec![Node::Bottom]),
    )
    .expect("query");
    assert_eq!(
        Derivation::Disjoint(variable(0), cite![0, 1]).validate(&disjoint),
        Ok(())
    );
    assert_eq!(
        Derivation::Disjoint(variable(0), cite![0]).validate(&disjoint),
        Err(ShapeError::NotDisjoint(variable(0)))
    );
    assert_eq!(
        Derivation::EmptyCarrier(variable(1)).validate(&disjoint),
        Ok(())
    );
    assert_eq!(
        Derivation::Disjoint(variable(1), cite![]).validate(&disjoint),
        Ok(())
    );

    // Countermodels against the entailed query, then a refutable one.
    for (assignment, refusal) in [
        (countermodel![], ShapeError::AssignmentLength),
        (countermodel![1, 1, 0], ShapeError::AssignmentLength),
        (
            countermodel![3, 0],
            ShapeError::AssignedOutside(variable(0)),
        ),
        (
            countermodel![1, 2],
            ShapeError::AssignedOutside(variable(1)),
        ),
        (countermodel![1, 1], ShapeError::NotCountermodel),
        (countermodel![0, 1], ShapeError::NotCountermodel),
    ] {
        assert_eq!(
            assignment.validate(&problem),
            Err(refusal),
            "{assignment:?}"
        );
    }
    let refutable = Problem::new(
        context![3],
        formula(vec![member!(0, 3, [0, 1])]),
        formula(vec![member!(0, 3, [1])]),
    )
    .expect("query");
    assert_eq!(decide(&refutable), Ok(Evidence::Refuted(countermodel![0])));
    assert_eq!(countermodel![0].validate(&refutable), Ok(()));
    assert_eq!(
        countermodel![1].validate(&refutable),
        Err(ShapeError::NotCountermodel)
    );
    assert_eq!(
        countermodel![2].validate(&refutable),
        Err(ShapeError::NotCountermodel)
    );
}

#[test]
fn deep_formulas_use_no_call_stack()
{
    // A hundred thousand conjunctions deep on both sides, each reusing the
    // one atom at node 0.
    let mut nodes = vec![member!(0, 2, [0])];
    for index in 1_usize ..= 100_000 {
        nodes.push(Node::And(
            NodeId::from(index.saturating_sub(1)),
            NodeId::from(0_usize),
        ));
    }
    let deep = formula(nodes);
    let problem = Problem::new(context![2], deep.clone(), deep).expect("query");
    assert_eq!(problem.premise_atoms(), [NodeId::from(0_usize)]);
    let evidence = decide(&problem).expect("decision");
    assert_eq!(evidence, Evidence::Holds(supported![&[0]]));
}
