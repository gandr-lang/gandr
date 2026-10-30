//! Named carriers: faces read by name, the mediator's refusal by name, and
//! one answer for every ordering of a boundary's names.

use gandr_theory_shapes::Boundary;
use gandr_theory_shapes::BoundaryError;
use gandr_theory_shapes::Formula;
use gandr_theory_shapes::Node;
use gandr_theory_shapes::NodeId;
use gandr_theory_shapes::Point;
use gandr_theory_shapes::PointCount;
use gandr_theory_shapes::Problem;
use gandr_theory_shapes::ShapeError;
use gandr_theory_shapes::Subshape;
use gandr_theory_shapes::UnionSquare;
use gandr_theory_shapes::Variable;
use gandr_theory_shapes::decide;

/// One name of a test boundary.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Name(char);

/// A list of names, one letter each.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Names(&'static str);

impl Names
{
    /// The names, in the order spelled.
    ///
    /// # Specification
    /// trivial.
    fn listed(self) -> Vec<Name>
    {
        self.0.chars().map(Name).collect()
    }
}

/// The boundary holding `names`, in the order listed.
///
/// # Specification
/// trivial.
fn boundary(names: Names) -> Boundary<Name>
{
    Boundary::new(names.listed()).expect("the names are distinct")
}

/// The face of `boundary` holding `names`.
///
/// # Specification
/// trivial.
fn face(
    boundary: &Boundary<Name>,
    names: Names,
) -> Subshape
{
    boundary
        .face(&names.listed())
        .expect("the boundary holds every name")
}

/// One variable over `boundary`, its premise the meet of `premise`'s faces and
/// its conclusion the face `conclusion`.
///
/// # Specification
/// trivial.
fn problem(
    boundary: &Boundary<Name>,
    premise: &[Names],
    conclusion: Names,
) -> Problem
{
    let x = Variable::from(0_usize);
    let mut nodes: Vec<Node> = premise
        .iter()
        .map(|names| Node::Member(x, face(boundary, *names)))
        .collect();
    let mut root = 0_usize;
    for right in 1 .. premise.len() {
        nodes.push(Node::And(NodeId::from(root), NodeId::from(right)));
        root = nodes.len().saturating_sub(1);
    }
    let premise = Formula::new(nodes).expect("the premise is a table");
    let conclusion = Formula::new(vec![Node::Member(x, face(boundary, conclusion))])
        .expect("the conclusion is a table");
    Problem::new(vec![boundary.carrier()], premise, conclusion).expect("the band admits it")
}

#[test]
fn permuted_copies_of_one_problem_decide_alike()
{
    // Two orderings of one boundary's names build one boundary, so one
    // problem stated in names over each decides to one answer: a derivation
    // when it holds, and a countermodel naming one point when it does not.
    let (listed, permuted) = (boundary(Names("dbac")), boundary(Names("cadb")));
    assert_eq!(listed, permuted);
    for (premise, conclusion) in [
        (&[Names("ab"), Names("bc")][..], Names("b")),
        (&[Names("ab")][..], Names("b")),
        (&[Names("bda"), Names("cdb")][..], Names("db")),
    ] {
        let answers = [&listed, &permuted]
            .map(|boundary| decide(&problem(boundary, premise, conclusion)).expect("decided"));
        assert_eq!(answers[0], answers[1], "{premise:?} ⊢ {conclusion:?}");
    }
}

#[test]
fn the_mediator_refuses_a_disagreement_by_its_name()
{
    // Over `a, b, c, d`, the left face `{a, b, c}` and the right `{b, c, d}`
    // meet in `{b, c}`. Maps agreeing there glue as the square glues them;
    // maps differing at `c` are refused by `c`.
    let names = boundary(Names("dbac"));
    let square =
        UnionSquare::new(&face(&names, Names("abc")), &face(&names, Names("bcd"))).expect("square");
    assert_eq!(
        names.mediator(&square, &['p', 'q', 'r'], &['q', 'r', 's']),
        Ok(vec!['p', 'q', 'r', 's'])
    );
    assert_eq!(
        names.mediator(&square, &['p', 'q', 'r'], &['q', 'x', 's']),
        Err(BoundaryError::Disagreement(Name('c')))
    );
    assert_eq!(
        names.mediator(&square, &['p', 'q'], &['q', 'r', 's']),
        Err(BoundaryError::Shape(ShapeError::MapLength(
            gandr_theory_shapes::Leg::Left
        )))
    );
    let smaller = boundary(Names("ab"));
    let other =
        UnionSquare::new(&face(&smaller, Names("a")), &face(&smaller, Names("b"))).expect("square");
    assert_eq!(
        names.mediator(&other, &['p'], &['q']),
        Err(BoundaryError::Shape(ShapeError::DifferentAmbient))
    );
}

#[test]
fn names_outside_or_twice_are_refused_by_name()
{
    assert_eq!(
        Boundary::new(Names("aba").listed()),
        Err(BoundaryError::Repeated(Name('a')))
    );
    let names = boundary(Names("dbac"));
    assert_eq!(names.carrier(), PointCount::from(4_usize));
    for (point, name) in Names("abcd").listed().into_iter().enumerate() {
        assert_eq!(names.point(name), Ok(Point::from(point)));
        assert_eq!(names.name(Point::from(point)), Ok(name));
    }
    assert_eq!(
        names.point(Name('z')),
        Err(BoundaryError::Unbound(Name('z')))
    );
    assert_eq!(
        names.face(&Names("az").listed()),
        Err(BoundaryError::Unbound(Name('z')))
    );
    assert_eq!(
        names.name(Point::from(4_usize)),
        Err(BoundaryError::Shape(ShapeError::PointOutside(Point::from(
            4_usize
        ))))
    );
    let empty = boundary(Names(""));
    assert_eq!(
        empty.point(Name('a')),
        Err(BoundaryError::Unbound(Name('a')))
    );
}
