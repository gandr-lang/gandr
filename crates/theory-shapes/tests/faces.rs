//! Independent total-assignment semantics and hostile certificate checks.

use gandr_theory_shapes::affine::Endpoint;
use gandr_theory_shapes::boundary::Case;
use gandr_theory_shapes::boundary::NodeId;
use gandr_theory_shapes::boundary::Point;
use gandr_theory_shapes::boundary::PointCount;
use gandr_theory_shapes::boundary::ShapeError;
use gandr_theory_shapes::boundary::Variable;
use gandr_theory_shapes::finite::Membership;
use gandr_theory_shapes::finite::Subshape;
use gandr_theory_shapes::formula::Formula;
use gandr_theory_shapes::formula::Node;
use gandr_theory_shapes::formula::Problem;
use gandr_theory_shapes::formula::Shape;
use gandr_theory_shapes::formula::Value;
use gandr_theory_shapes::oracle::Countermodel;
use gandr_theory_shapes::oracle::Derivation;
use gandr_theory_shapes::oracle::Evidence;
use gandr_theory_shapes::oracle::Rule;
use gandr_theory_shapes::oracle::decide;

/// A Boolean semantic observation confined to the reference evaluator.
#[repr(transparent)]
struct Satisfied(bool);

/// Evaluates a total assignment, independently of partial truth bounds.
///
/// # Specification
/// - requires: well-formed formula and total, well-sorted assignment.
/// - provides: ordinary two-valued evaluation of the formula.
/// - panics: malformed test fixtures.
///
/// # Adequacy
/// - hypothesis: L2 this truth-table observer distinguishes incorrect oracle
///   decisions; fixed endpoint cases anchor the intended interpretation.
/// - witness: `tests::faces::generated_queries_agree_with_brute_force`
/// - witness: `tests::faces::generic_coordinates_refute_endpoint_coverage`
fn naive(
    formula: &Formula,
    assignment: &[Value],
) -> Satisfied
{
    let mut values = Vec::with_capacity(formula.nodes().len());
    for node in formula.nodes() {
        let value = match *node {
            | Node::Top => true,
            | Node::Bottom => false,
            | Node::Endpoint(variable, endpoint) => {
                assignment[usize::from(variable)] == Value::Endpoint(endpoint)
            },
            | Node::Member(variable, ref subset) => {
                let Value::Point(point) = assignment[usize::from(variable)]
                else {
                    panic!("finite fixture");
                };
                subset.decisions()[usize::from(point)] == Membership::Inside
            },
            | Node::And(a, b) => values[usize::from(a)] && values[usize::from(b)],
            | Node::Or(a, b) => values[usize::from(a)] || values[usize::from(b)],
        };
        values.push(value);
    }
    Satisfied(*values.last().expect("root"))
}

/// Enumerates the full product without the production case decoder.
///
/// # Specification
/// - provides: all ternary bridge observations and all finite points, once per
///   coordinate; an empty carrier yields no assignments.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 full products expose branch-skipping by the search.
/// - witness: `tests::faces::generated_queries_agree_with_brute_force`
fn assignments(context: &[Shape]) -> Vec<Vec<Value>>
{
    let mut rows = vec![Vec::new()];
    for shape in context {
        let domain: Vec<Value> = match *shape {
            | Shape::Bridge => vec![
                Value::Generic,
                Value::Endpoint(Endpoint::Zero),
                Value::Endpoint(Endpoint::One),
            ],
            | Shape::Finite(count) => (0 .. usize::from(count))
                .map(|point| Value::Point(Point::from(point)))
                .collect(),
        };
        let mut product = Vec::new();
        for row in &rows {
            for &value in &domain {
                let mut extended = row.clone();
                extended.push(value);
                product.push(extended);
            }
        }
        rows = product;
    }
    rows
}

/// The atom basis, including every subset of each finite carrier.
///
/// # Specification
/// - requires: finite test carriers have at most four points.
/// - provides: both bridge endpoints, every finite membership atom, and bounds.
/// - panics: invalid test subset construction.
///
/// # Adequacy
/// - hypothesis: L2 exhaustive atoms expose omitted endpoint or subset cases.
/// - witness: `tests::faces::generated_queries_agree_with_brute_force`
fn atoms(context: &[Shape]) -> Vec<Node>
{
    let mut nodes = vec![Node::Top, Node::Bottom];
    for (index, shape) in context.iter().enumerate() {
        let variable = Variable::from(index);
        match *shape {
            | Shape::Bridge => {
                nodes.push(Node::Endpoint(variable, Endpoint::Zero));
                nodes.push(Node::Endpoint(variable, Endpoint::One));
            },
            | Shape::Finite(count) => {
                let width = u32::try_from(usize::from(count)).expect("small carrier");
                for mask in 0_usize .. 1_usize.checked_shl(width).expect("small mask") {
                    let points: Vec<Point> = (0 .. usize::from(count))
                        .filter(|point| {
                            mask & 1_usize
                                .checked_shl(u32::try_from(*point).expect("small point"))
                                .expect("small bit")
                                != 0
                        })
                        .map(Point::from)
                        .collect();
                    nodes.push(Node::Member(
                        variable,
                        Subshape::new(count, &points).expect("subset"),
                    ));
                }
            },
        }
    }
    nodes
}

/// A deterministic generator state, independent of production traversal.
#[repr(transparent)]
struct Seed(u64);

impl Seed
{
    /// Chooses an index by a fixed wrapping recurrence.
    ///
    /// # Specification
    /// - requires: the bound is positive.
    /// - provides: an index below the bound, with reproducible state evolution.
    /// - panics: a zero or nonrepresentable bound.
    ///
    /// # Adequacy
    /// - hypothesis: L2 generated DAG pairs exercise shared and deep
    ///   connectives.
    /// - witness: `tests::faces::generated_queries_agree_with_brute_force`
    fn index(
        &mut self,
        bound: NodeId,
    ) -> NodeId
    {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        let bound = u64::try_from(usize::from(bound)).expect("index bound");
        NodeId::from(
            usize::try_from(self.0.checked_rem(bound).expect("nonzero bound"))
                .expect("small remainder"),
        )
    }
}

/// Checks one query against a truth table and validates its evidence.
///
/// # Specification
/// - requires: well-formed formulas in the supplied context.
/// - ensures: oracle polarity equals the reference implication, and returned
///   evidence rechecks against the exact query.
/// - panics: any decision or evidence mismatch.
///
/// # Adequacy
/// - hypothesis: L1 and L2 jointly distinguish incorrect verdicts and invalid
///   certificates, including empty contexts and generic bridge coordinates.
/// - witness: `tests::faces::generated_queries_agree_with_brute_force`
fn check(
    context: &[Shape],
    left: &Formula,
    right: &Formula,
    rows: &[Vec<Value>],
)
{
    let expected = rows
        .iter()
        .all(|row| !naive(left, row).0 || naive(right, row).0);
    let problem =
        Problem::new(context.to_vec(), left.clone(), right.clone()).expect("sorted query");
    match decide(&problem).expect("decision") {
        | Evidence::Holds(proof) => {
            assert!(expected, "positive decision contradicts finite model");
            assert_eq!(proof.validate(&problem), Ok(()));
        },
        | Evidence::Refuted(model) => {
            assert!(!expected, "negative decision contradicts finite model");
            assert_eq!(model.validate(&problem), Ok(()));
            assert!(naive(left, &model.assignment).0);
            assert!(!naive(right, &model.assignment).0);
        },
    }
}

#[test]
fn generated_queries_agree_with_brute_force()
{
    let mut queries = 0_usize;
    let mut maximum_rows = 0_usize;
    let mut seed = Seed(0xFACE_CAFE);
    let mut contexts = vec![vec![]];
    for bridges in 0_usize ..= 4 {
        contexts.push(vec![Shape::Bridge; bridges]);
        for points in 0_usize ..= 4 {
            let mut context = vec![Shape::Bridge; bridges];
            context.push(Shape::Finite(PointCount::from(points)));
            contexts.push(context);
        }
    }
    // Two independent finite coordinates distinguish accidental point sharing.
    for left in 0_usize ..= 4 {
        for right in 0_usize ..= 4 {
            contexts.push(vec![
                Shape::Finite(PointCount::from(left)),
                Shape::Finite(PointCount::from(right)),
            ]);
        }
    }
    contexts.dedup();
    for context in contexts {
        let rows = assignments(&context);
        maximum_rows = maximum_rows.max(rows.len());
        let basis = atoms(&context);
        let atomic: Vec<Formula> = basis
            .iter()
            .map(|node| Formula::new(vec![node.clone()]).expect("atom"))
            .collect();
        for left in &atomic {
            for right in &atomic {
                check(&context, left, right, &rows);
                queries = queries.saturating_add(1);
            }
        }
        // Every ordered pair of atoms under each connective, against every
        // atom, in both entailment directions.
        for a in &basis {
            for b in &basis {
                for connective in [
                    Node::And(NodeId::from(0), NodeId::from(1)),
                    Node::Or(NodeId::from(0), NodeId::from(1)),
                ] {
                    let composite = Formula::new(vec![a.clone(), b.clone(), connective])
                        .expect("binary formula");
                    for atom in &atomic {
                        check(&context, &composite, atom, &rows);
                        check(&context, atom, &composite, &rows);
                        queries = queries.saturating_add(2);
                    }
                }
            }
        }
        for _ in 0_usize .. 256 {
            let mut pair = Vec::with_capacity(2);
            for _ in 0_usize .. 2 {
                let mut nodes = basis.clone();
                for _ in 0_usize .. 32 {
                    let bound = NodeId::from(nodes.len());
                    let a = seed.index(bound);
                    let b = seed.index(bound);
                    let op = seed.index(NodeId::from(2));
                    nodes.push(if usize::from(op) == 0 {
                        Node::And(a, b)
                    }
                    else {
                        Node::Or(a, b)
                    });
                }
                pair.push(Formula::new(nodes).expect("generated DAG"));
            }
            check(&context, &pair[0], &pair[1], &rows);
            queries = queries.saturating_add(1);
        }
    }
    println!("face agreement: {queries} queries; maximum {maximum_rows} assignments per context");
}

#[test]
fn generic_coordinates_refute_endpoint_coverage()
{
    let boundary = Formula::new(vec![
        Node::Endpoint(Variable::from(0), Endpoint::Zero),
        Node::Endpoint(Variable::from(0), Endpoint::One),
        Node::Or(NodeId::from(0), NodeId::from(1)),
    ])
    .expect("boundary");
    let top = Formula::new(vec![Node::Top]).expect("top");
    let problem = Problem::new(vec![Shape::Bridge], top, boundary).expect("query");
    let Evidence::Refuted(model) = decide(&problem).expect("decision")
    else {
        panic!("generic point must refute coverage");
    };
    assert_eq!(model.assignment, vec![Value::Generic]);
    assert_eq!(model.validate(&problem), Ok(()));
    let (_, left, right) = problem.parts();
    assert!(naive(left, &model.assignment).0);
    assert!(!naive(right, &model.assignment).0);
}

#[test]
fn input_boundaries_are_checked()
{
    assert_eq!(Formula::new(vec![]), Err(ShapeError::MalformedFormula));
    for bad in [
        Node::And(NodeId::from(0), NodeId::from(1)),
        Node::Or(NodeId::from(1), NodeId::from(0)),
    ] {
        assert_eq!(
            Formula::new(vec![Node::Top, bad]),
            Err(ShapeError::MalformedFormula)
        );
    }
    let top = Formula::new(vec![Node::Top]).expect("top");
    let endpoint =
        Formula::new(vec![Node::Endpoint(Variable::from(0), Endpoint::Zero)]).expect("atom");
    for (left, right) in [(endpoint.clone(), top.clone()), (top.clone(), endpoint)] {
        assert_eq!(
            Problem::new(vec![], left.clone(), right.clone()),
            Err(ShapeError::VariableOutside(Variable::from(0)))
        );
        assert_eq!(
            Problem::new(vec![Shape::Finite(PointCount::from(2))], left, right),
            Err(ShapeError::WrongShape(Variable::from(0)))
        );
    }
    let member = Formula::new(vec![Node::Member(
        Variable::from(0),
        Subshape::new(PointCount::from(2), &[]).expect("subset"),
    )])
    .expect("atom");
    for shape in [Shape::Bridge, Shape::Finite(PointCount::from(3))] {
        assert_eq!(
            Problem::new(vec![shape], member.clone(), top.clone()),
            Err(ShapeError::WrongShape(Variable::from(0)))
        );
    }
    assert_eq!(Shape::Bridge.value(Case::from(0)), Ok(Value::Generic));
    assert_eq!(
        Shape::Bridge.value(Case::from(1)),
        Ok(Value::Endpoint(Endpoint::Zero))
    );
    assert_eq!(
        Shape::Bridge.value(Case::from(2)),
        Ok(Value::Endpoint(Endpoint::One))
    );
    assert_eq!(
        Shape::Bridge.value(Case::from(3)),
        Err(ShapeError::CaseOutside)
    );
    for size in 0_usize ..= 4 {
        let shape = Shape::Finite(PointCount::from(size));
        for point in 0 .. size {
            assert_eq!(
                shape.value(Case::from(point)),
                Ok(Value::Point(Point::from(point)))
            );
        }
        assert_eq!(shape.value(Case::from(size)), Err(ShapeError::CaseOutside));
    }
}

#[test]
fn forged_evidence_is_refused()
{
    let atom = Formula::new(vec![Node::Endpoint(Variable::from(0), Endpoint::Zero)]).expect("atom");
    let problem = Problem::new(vec![Shape::Bridge], atom.clone(), atom).expect("identity");
    let Evidence::Holds(valid) = decide(&problem).expect("proof")
    else {
        panic!("reflexivity");
    };
    assert_eq!(valid.validate(&problem), Ok(()));
    for length in 0 .. valid.rules.len() {
        let broken = Derivation {
            rules: valid.rules.iter().copied().take(length).collect(),
        };
        assert_eq!(
            broken.validate(&problem),
            Err(ShapeError::InvalidDerivation)
        );
    }
    for rules in [
        vec![Rule::FalsePremise],
        vec![Rule::TrueConclusion],
        vec![Rule::Split(Variable::from(1))],
        vec![
            Rule::Split(Variable::from(0)),
            Rule::Split(Variable::from(0)),
        ],
    ] {
        assert_eq!(
            Derivation { rules }.validate(&problem),
            Err(ShapeError::InvalidDerivation)
        );
    }
    let mut extra = valid.clone();
    extra.rules.push(Rule::TrueConclusion);
    assert_eq!(extra.validate(&problem), Err(ShapeError::InvalidDerivation));
    let top = Formula::new(vec![Node::Top]).expect("top");
    let bottom = Formula::new(vec![Node::Bottom]).expect("bottom");
    let wrong =
        Problem::new(vec![Shape::Bridge], top.clone(), bottom.clone()).expect("false query");
    assert_eq!(valid.validate(&wrong), Err(ShapeError::InvalidDerivation));
    for (assignment, error) in [
        (vec![], ShapeError::AssignmentLength),
        (
            vec![Value::Unassigned],
            ShapeError::IncompleteAssignment(Variable::from(0)),
        ),
        (
            vec![Value::Point(Point::from(0))],
            ShapeError::WrongShape(Variable::from(0)),
        ),
        (vec![Value::Generic], ShapeError::NotCountermodel),
    ] {
        assert_eq!(Countermodel { assignment }.validate(&problem), Err(error));
    }
    let finite = Problem::new(
        vec![Shape::Finite(PointCount::from(1))],
        top.clone(),
        bottom.clone(),
    )
    .expect("finite query");
    assert_eq!(
        Countermodel {
            assignment: vec![Value::Point(Point::from(1))]
        }
        .validate(&finite),
        Err(ShapeError::PointOutside(Point::from(1)))
    );
    assert_eq!(
        Countermodel {
            assignment: vec![Value::Generic]
        }
        .validate(&finite),
        Err(ShapeError::WrongShape(Variable::from(0)))
    );
    let vacuous = Problem::new(vec![Shape::Bridge], bottom, top).expect("vacuous");
    assert_eq!(
        Countermodel {
            assignment: vec![Value::Generic]
        }
        .validate(&vacuous),
        Err(ShapeError::NotCountermodel)
    );
}

#[test]
fn deep_formulas_use_no_call_stack()
{
    let mut nodes = vec![Node::Top];
    for index in 1_usize ..= 100_000 {
        nodes.push(Node::And(
            NodeId::from(index.saturating_sub(1)),
            NodeId::from(0),
        ));
    }
    let problem = Problem::new(
        vec![],
        Formula::new(vec![Node::Top]).expect("top"),
        Formula::new(nodes).expect("deep"),
    )
    .expect("query");
    let Evidence::Holds(proof) = decide(&problem).expect("decision")
    else {
        panic!("top conjunction");
    };
    assert_eq!(proof.validate(&problem), Ok(()));
}
