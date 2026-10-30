use alloc::string::ToString as _;
use alloc::vec::Vec;

use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::compose::CellCount;
use gandr_core_term::compose::Composite;
use gandr_core_term::compose::Ends;
use gandr_core_term::compose::Heights;
use gandr_core_term::compose::Pasting;
use gandr_core_term::compose::Seam;
use gandr_core_term::compose::compose_columns;
use gandr_core_term::ua::Stratum;
use gandr_kernel_term::BaseType;
use gandr_theory_sites::Boundary;
use gandr_theory_sites::Degree;
use gandr_theory_sites::ShapeSize;
use gandr_theory_sites::Unfilled;

use super::CellReading;
use super::Endpoint;
use super::admit;
use super::cell;
use super::fill;
use super::fill_columns;
use crate::context::CheckBudget;
use crate::context::CheckingContext;
use crate::conversion::Agreement;
use crate::conversion::equivalent;
use crate::formation::form_value_type;
use crate::judgement::synthesise_value;
use crate::refusal::CheckRefusal;
use crate::refusal::ExpectedShape;
use crate::refusal::TermNode;
use crate::ua::Strata;
use crate::ua::StratumDefect;

/// A head `compose[degree, bound]`: its degree and its catalogue bound.
#[derive(Clone, Copy, Debug)]
struct Head(usize, usize);

/// The cell count `chain(m)` writes, `m`.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Cells(usize);

/// An integer literal a fixture writes.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Point(u8);

/// A leg of the cell at an index: its input, or its output.
#[derive(Clone, Copy, Debug)]
enum Leg
{
    /// The cell's input, where it starts.
    Start(usize),
    /// The cell's output, where it ends.
    End(usize),
}

/// A cell a fixture diagram draws.
#[derive(Clone, Copy, Debug)]
enum Drawn
{
    /// A path between two integer literals.
    Path(u8, u8),
    /// A cell of the unknown type.
    Unknown,
}

/// `compose[degree, bound](chain(cells), …)`.
///
/// # Specification
/// trivial.
fn chain(
    Head(degree, bound): Head,
    Cells(cells): Cells,
) -> Composite
{
    Composite {
        stratum: Stratum {
            degree: Degree::from(degree),
            bound: ShapeSize::from(bound),
        },
        pasting: Pasting::Chain {
            cells: CellCount::from(cells),
        },
    }
}

/// The integer literal `value`, minted fresh.
///
/// # Specification
/// trivial.
fn integer(
    arena: &mut CoreArena,
    Point(value): Point,
) -> ValueId
{
    let magnitude = gandr_kernel_term::Magnitude::from_decimal_text(value.to_string())
        .expect("the digits are decimal");
    arena.value_literal(gandr_kernel_term::Literal::Integer(
        gandr_kernel_term::IntegerLiteral::new(gandr_kernel_term::Sign::NonNegative, magnitude),
    ))
}

/// The diagram of `cells`, each endpoint a fresh literal.
///
/// # Specification
/// trivial.
fn diagram(
    arena: &mut CoreArena,
    cells: &[Drawn],
) -> Vec<Boundary<Endpoint>>
{
    cells
        .iter()
        .map(|drawn| match *drawn {
            Drawn::Path(left, right) => cell(
                Endpoint::Known(integer(arena, Point(left))),
                Endpoint::Known(integer(arena, Point(right))),
            ),
            Drawn::Unknown => cell(Endpoint::Unknown, Endpoint::Unknown),
        })
        .collect()
}

/// What [`filled`] gives: the outer endpoints or the refusal, beside the
/// diagram it read.
type Filled = (
    Result<(Endpoint, Endpoint), CheckRefusal>,
    Vec<Boundary<Endpoint>>,
);

/// The outer endpoints [`fill`] gives for `cells` over the chain of
/// `vertices` at `compose[5, 7]`, beside the diagram it read.
///
/// # Specification
/// trivial.
fn filled(
    vertices: Cells,
    cells: &[Drawn],
) -> Filled
{
    let mut arena = CoreArena::new();
    let at = integer(&mut arena, Point(0));
    let drawn = diagram(&mut arena, cells);
    let shape = admit(&mut Strata::default(), at, chain(Head(5, 7), vertices))
        .expect("the chain is a shape at 5 over 7");
    let context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    (fill(&context, (at, Seam::Outer), &shape, &drawn), drawn)
}

/// The endpoint at `leg`.
///
/// # Specification
/// trivial.
fn end_of(
    drawn: &[Boundary<Endpoint>],
    leg: Leg,
) -> Endpoint
{
    let (index, output) = match leg {
        Leg::Start(index) => (index, false),
        Leg::End(index) => (index, true),
    };
    let boundary = drawn.get(index).expect("the cell is drawn");
    let side = if output {
        boundary.outputs()
    }
    else {
        boundary.inputs()
    };
    *side.first().expect("a path has one leg each way")
}

#[test]
fn one_cell_reads_no_stratum()
{
    let mut arena = CoreArena::new();
    let at = integer(&mut arena, Point(0));
    let mut strata = Strata::default();
    let shape =
        admit(&mut strata, at, chain(Head(0, 0), Cells(1))).expect("one cell reads no stratum");
    assert_eq!(
        usize::from(shape.vertex_count()),
        1,
        "the chain of one cell is the corolla"
    );
    assert_eq!(
        admit(&mut strata, at, chain(Head(0, 0), Cells(2))),
        Err(CheckRefusal::ComposeUncertified {
            at,
            stratum: StratumDefect::Degree {
                degree: Degree::from(0_usize)
            },
        }),
        "two cells read the stratum, which degree zero is not"
    );
}

#[test]
fn composable_cells_fill_their_chain()
{
    let (ends, drawn) = filled(Cells(3), &[
        Drawn::Path(1, 2),
        Drawn::Path(2, 3),
        Drawn::Path(3, 4),
    ]);
    assert_eq!(
        ends,
        Ok((end_of(&drawn, Leg::Start(0)), end_of(&drawn, Leg::End(2)))),
        "the composite runs from the first cell's start to the last cell's end"
    );

    let (ends, drawn) = filled(Cells(3), &[
        Drawn::Path(1, 2),
        Drawn::Unknown,
        Drawn::Path(7, 8),
    ]);
    assert_eq!(
        ends,
        Ok((end_of(&drawn, Leg::Start(0)), end_of(&drawn, Leg::End(2)))),
        "a cell of the unknown type meets any endpoint"
    );

    let mut arena = CoreArena::new();
    let integer_type = arena.value_type_base(BaseType::Integer);
    let one = integer(&mut arena, Point(1));
    let points = [1, 1, 1].map(|value| integer(&mut arena, Point(value)));
    let cells = points.map(|point| arena.value_here(point));
    let composite = gandr_core_term::compose::compose(
        &mut arena,
        chain(Head(5, 7), Cells(3)),
        (integer_type, one),
        &cells,
    );
    let declared = arena.value_type_path(integer_type, one, one);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let declared = form_value_type(&mut context, declared)
        .expect("the path forms")
        .id();
    let synthesised =
        synthesise_value(&mut context, composite).expect("three reflexivities compose");
    assert_eq!(
        equivalent(&mut context, synthesised.produced().id(), declared),
        Ok(Agreement::Convertible),
        "the composite has the path between its outer endpoints"
    );
}

#[test]
fn a_composite_refuses_each_defect_by_name()
{
    let mut arena = CoreArena::new();
    let at = integer(&mut arena, Point(0));
    let mut strata = Strata::default();
    let refusals = [
        (
            chain(Head(0, 7), Cells(3)),
            CheckRefusal::ComposeUncertified {
                at,
                stratum: StratumDefect::Degree {
                    degree: Degree::from(0_usize),
                },
            },
        ),
        (
            chain(Head(5, 65), Cells(3)),
            CheckRefusal::ComposeUncertified {
                at,
                stratum: StratumDefect::Allowance {
                    bound: ShapeSize::from(65_usize),
                },
            },
        ),
        (
            chain(Head(5, 7), Cells(4)),
            CheckRefusal::ComposeNotAShape {
                at,
                pasting: chain(Head(5, 7), Cells(4)).pasting,
            },
        ),
        (
            chain(Head(4, 7), Cells(3)),
            CheckRefusal::ComposeNotAShape {
                at,
                pasting: chain(Head(4, 7), Cells(3)).pasting,
            },
        ),
        (
            chain(Head(5, 7), Cells(0)),
            CheckRefusal::ComposeNotAShape {
                at,
                pasting: chain(Head(5, 7), Cells(0)).pasting,
            },
        ),
    ];
    for (composite, refusal) in refusals {
        assert_eq!(
            admit(&mut strata, at, composite),
            Err(refusal),
            "{composite:?} is refused by name"
        );
    }

    assert!(
        matches!(
            filled(Cells(3), &[Drawn::Path(1, 2), Drawn::Path(2, 3)]).0,
            Err(CheckRefusal::ComposeDoesNotFill {
                defect: Unfilled::Cells { vertices, cells },
                ..
            }) if usize::from(vertices) == 3 && usize::from(cells) == 2
        ),
        "a cell short is refused by the count"
    );
    assert!(
        matches!(
            filled(Cells(3), &[Drawn::Path(1, 2), Drawn::Path(3, 4), Drawn::Path(4, 5)]).0,
            Err(CheckRefusal::ComposeDoesNotFill {
                defect: Unfilled::Wire { wire },
                ..
            }) if usize::from(wire) == 1
        ),
        "a middle endpoint that does not convert is refused at its wire"
    );

    let mut arena = CoreArena::new();
    let integer_type = arena.value_type_base(BaseType::Integer);
    let one = integer(&mut arena, Point(1));
    let written = integer(&mut arena, Point(1));
    let reflexive = arena.value_here(one);
    let composite = gandr_core_term::compose::compose(
        &mut arena,
        chain(Head(5, 7), Cells(3)),
        (integer_type, one),
        &[written, reflexive, reflexive],
    );
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    assert!(
        matches!(
            synthesise_value(&mut context, composite),
            Err(CheckRefusal::ShapeMismatch {
                at: TermNode::Value(cell),
                wanted: ExpectedShape::Path,
                ..
            }) if cell == written
        ),
        "a cell that is no path is refused by shape"
    );
}

/// The column heights `chain(m, (a₁, …, aₘ))` writes.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Written(&'static [usize]);

/// `compose[degree, bound](chain(m, (a₁, …, aₘ)), …)`.
///
/// # Specification
/// trivial.
fn columns(
    Head(degree, bound): Head,
    Written(heights): Written,
) -> Composite
{
    let heights: Vec<CellCount> = heights.iter().copied().map(CellCount::from).collect();
    Composite {
        stratum: Stratum {
            degree: Degree::from(degree),
            bound: ShapeSize::from(bound),
        },
        pasting: Pasting::Columns {
            heights: Heights::new(&heights).expect("the columns pack"),
        },
    }
}

#[test]
fn a_level_two_shape_is_read_at_level_two()
{
    let mut arena = CoreArena::new();
    let at = integer(&mut arena, Point(0));
    let mut strata = Strata::default();
    let whisker = columns(Head(4, 9), Written(&[1, 0]));
    let outer = admit(&mut strata, at, whisker).expect("the whisker is a shape at 4 over 9");
    assert_eq!(
        usize::from(outer.vertex_count()),
        2,
        "the whisker reads its outer chain of two columns"
    );
    for (composite, name) in [
        (columns(Head(3, 9), Written(&[1, 0])), "past its degree"),
        (columns(Head(4, 7), Written(&[1, 0])), "past its bound"),
    ] {
        assert!(
            matches!(
                admit(&mut strata, at, composite),
                Err(CheckRefusal::ComposeNotAShape { pasting, .. }) if pasting == composite.pasting
            ),
            "the whisker {name} is refused by name"
        );
    }

    let integer_type = arena.value_type_base(BaseType::Integer);
    let [zero, one, two, three] = [0, 1, 2, 3].map(|value| integer(&mut arena, Point(value)));
    let [first, second] = [(zero, one), (one, two)]
        .map(|(left, right)| arena.value_type_path(integer_type, left, right));
    let [low, high, onward, beyond] = [5, 6, 7, 8].map(|value| integer(&mut arena, Point(value)));
    let known = |carrier, left, right| CellReading::Known {
        carrier,
        left,
        right,
    };
    let misplaced = arena.value_type_path(integer_type, three, two);
    let horizontal = admit(&mut strata, at, columns(Head(5, 11), Written(&[1, 1])))
        .expect("the horizontal composite is a shape at 5 over 11");
    let vertical = admit(&mut strata, at, columns(Head(4, 9), Written(&[2])))
        .expect("the vertical composite is a shape at 4 over 9");
    let horizontal_heights = columns(Head(5, 11), Written(&[1, 1]));
    let vertical_heights = columns(Head(4, 9), Written(&[2]));
    let (Pasting::Columns { heights: across }, Pasting::Columns { heights: down }) =
        (horizontal_heights.pasting, vertical_heights.pasting)
    else {
        panic!("both are level-two pastings");
    };
    let context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    assert_eq!(
        fill_columns(&context, at, (across, &horizontal), &[
            known(first, low, high),
            known(second, onward, beyond)
        ]),
        Ok(()),
        "two 2-cells side by side fill the horizontal composite"
    );
    assert!(
        matches!(
            fill_columns(&context, at, (across, &horizontal), &[
                known(first, low, high),
                known(misplaced, onward, beyond)
            ]),
            Err(CheckRefusal::ComposeDoesNotFill {
                seam: Seam::Outer,
                defect: Unfilled::Wire { .. },
                ..
            })
        ),
        "a second column starting where the first does not end is refused at the outer seam"
    );
    assert!(
        matches!(
            fill_columns(&context, at, (down, &vertical), &[
                known(first, low, high),
                known(first, onward, beyond)
            ]),
            Err(CheckRefusal::ComposeDoesNotFill { seam: Seam::Column(before), defect: Unfilled::Wire { .. }, .. })
                if usize::from(before) == 0
        ),
        "a column's 2-cells that do not meet are refused at the column's seam"
    );
}

#[test]
fn a_level_two_composite_has_the_path_between_its_folds()
{
    for (head, heights) in [
        (Head(4, 9), Written(&[1, 0])),
        (Head(5, 11), Written(&[1, 1])),
    ] {
        let mut arena = CoreArena::new();
        let integer_type = arena.value_type_base(BaseType::Integer);
        let one = integer(&mut arena, Point(1));
        let point = arena.value_here(one);
        let loop_type = arena.value_type_path(integer_type, one, one);
        let surface = arena.value_here(point);
        let cells: Vec<(ValueId, Ends)> = heights
            .0
            .iter()
            .map(|&height| {
                if height == 0 {
                    (point, Ends {
                        carrier: integer_type,
                        left: one,
                        right: one,
                    })
                }
                else {
                    (surface, Ends {
                        carrier: loop_type,
                        left: point,
                        right: point,
                    })
                }
            })
            .collect();
        let (composite, ends) = compose_columns(&mut arena, columns(head, heights), &cells)
            .expect("the cells realise their shape");
        let declared = arena.value_type_path(ends.carrier, ends.left, ends.right);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        let declared = form_value_type(&mut context, declared)
            .expect("the path between the folds forms")
            .id();
        let synthesised = synthesise_value(&mut context, composite)
            .expect("the reflexive 2-cells compose at level two");
        assert_eq!(
            equivalent(&mut context, synthesised.produced().id(), declared),
            Ok(Agreement::Convertible),
            "{heights:?} has the path between its sources' fold and its targets'"
        );
    }
}
