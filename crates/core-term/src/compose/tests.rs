use gandr_kernel_term::BaseType;
use gandr_kernel_term::DeBruijnIndex;
use gandr_theory_sites::Degree;
use gandr_theory_sites::Shape;
use gandr_theory_sites::ShapeSize;

use super::CellCount;
use super::Composite;
use super::Ends;
use super::Heights;
use super::Pasting;
use super::compose_columns;
use crate::CertificateEquality;
use crate::CoreArena;
use crate::arena::ComputationId;
use crate::arena::ValueId;
use crate::syntax::Value;
use crate::syntax::Zone;
use crate::syntax::equal_certificate_syntax;
use crate::ua::Stratum;

/// The intuitionistic variable at `index`.
///
/// # Specification
/// trivial.
fn variable(
    arena: &mut CoreArena,
    index: DeBruijnIndex,
) -> ValueId
{
    arena.value_variable(Zone::Intuitionistic, index)
}

/// `compose[5, 7](chain(cells), …)`.
///
/// # Specification
/// trivial.
fn chain(cells: CellCount) -> Composite
{
    Composite {
        stratum: Stratum {
            degree: Degree::from(5_usize),
            bound: ShapeSize::from(7_usize),
        },
        pasting: Pasting::Chain { cells },
    }
}

/// The realisation a composite holds.
///
/// # Specification
/// trivial.
fn realised(
    arena: &CoreArena,
    composite: ValueId,
) -> ComputationId
{
    match arena.value(composite) {
        Some(&Value::Compose { realised, .. }) => realised,
        other => panic!("a composite, not {other:?}"),
    }
}

/// How two built terms compare as syntax.
///
/// # Specification
/// trivial.
fn compared(
    arena: &CoreArena,
    left: ComputationId,
    right: ComputationId,
) -> CertificateEquality
{
    let mut probe = arena.clone();
    let left = probe.value_thunk(left);
    let right = probe.value_thunk(right);
    equal_certificate_syntax(&probe, left, right)
}

#[test]
fn three_cells_realise_as_the_left_nested_fold()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let start = variable(&mut arena, 0_u32.into());
    let [first, second, third] = [1_u32, 2, 3].map(|index| variable(&mut arena, index.into()));
    let built = super::compose(
        &mut arena,
        chain(CellCount::from(3_usize)),
        (integer, start),
        &[first, second, third],
    );

    let inner = crate::identity::then(&mut arena, integer, start, first, second);
    let inner = arena.value_returned(inner);
    let left = crate::identity::then(&mut arena, integer, start, inner, third);
    assert_eq!(
        compared(&arena, realised(&arena, built), left),
        CertificateEquality::Equal,
        "the composite of three cells moves the first two's composite along the third"
    );

    let outer = crate::identity::then(&mut arena, integer, start, second, third);
    let outer = arena.value_returned(outer);
    let right = crate::identity::then(&mut arena, integer, start, first, outer);
    assert_eq!(
        compared(&arena, realised(&arena, built), right),
        CertificateEquality::Different,
        "the right-nested bracketing is another term"
    );

    let single = super::compose(
        &mut arena,
        chain(CellCount::from(1_usize)),
        (integer, start),
        &[first],
    );
    let returned = arena.computation_return(first);
    assert_eq!(
        compared(&arena, realised(&arena, single), returned),
        CertificateEquality::Equal,
        "one cell realises as itself returned"
    );
}

#[test]
fn the_binary_composite_is_the_least_stratum_of_two_cells()
{
    let two = Shape::chain(2_usize.into()).expect("the 2-chain is a shape");
    let Composite { stratum, pasting } = Composite::binary();
    assert_eq!(
        stratum,
        Stratum {
            degree: Degree::of(&two),
            bound: two.size(),
        },
        "the stratum is the 2-chain's own degree and size, so `then` reads the least one"
    );
    assert_eq!(pasting, Pasting::Chain {
        cells: CellCount::from(usize::from(two.vertex_count())),
    });
}

#[test]
fn heights_read_back_what_they_pack()
{
    let whisker = [1_usize, 0].map(CellCount::from);
    let heights = Heights::new(&whisker).expect("the whisker's columns pack");
    assert!(
        heights.columns().eq(whisker),
        "the whisker's heights read back"
    );
    let empty = Heights::new(&[]).expect("no column packs");
    assert_eq!(empty.columns().count(), 0, "no column reads back none");
    let filling = [CellCount::from(62_usize)];
    assert!(
        Heights::new(&filling).is_some_and(|heights| heights.columns().eq(filling)),
        "63 marks pack"
    );
    assert_eq!(
        Heights::new(&[CellCount::from(63_usize)]),
        None,
        "64 marks do not pack"
    );
}

/// `compose[degree, bound](chain(m, (a₁, …, aₘ)), …)`.
///
/// # Specification
/// trivial.
fn columns(heights: &[CellCount]) -> Composite
{
    Composite {
        stratum: Stratum {
            degree: Degree::from(5_usize),
            bound: ShapeSize::from(11_usize),
        },
        pasting: Pasting::Columns {
            heights: Heights::new(heights).expect("the columns pack"),
        },
    }
}

#[test]
fn a_level_two_composite_folds_its_columns_by_whiskers()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let [one, none] = [1_usize, 0].map(CellCount::from);
    let [
        start,
        middle,
        end,
        low,
        high,
        onward,
        onward_high,
        alpha,
        beta,
    ] = [0_u32, 1, 2, 3, 4, 5, 6, 7, 8].map(|index| variable(&mut arena, index.into()));
    let first = arena.value_type_path(integer, start, middle);
    let second = arena.value_type_path(integer, middle, end);
    let two_cell = |carrier, left, right| Ends {
        carrier,
        left,
        right,
    };
    let (whiskered, ends) = compose_columns(&mut arena, columns(&[one, none]), &[
        (alpha, two_cell(first, low, high)),
        (onward, two_cell(integer, middle, end)),
    ])
    .expect("the whisker realises");
    let right = crate::identity::whisker(
        &mut arena,
        (integer, start, end),
        (low, onward),
        crate::identity::Whisker::Right,
        alpha,
    );
    let right = arena.computation_return(right);
    assert_eq!(
        compared(&arena, realised(&arena, whiskered), right),
        CertificateEquality::Equal,
        "the whisker realises as the right whisker alone"
    );
    let sources = crate::identity::then(&mut arena, integer, start, low, onward);
    let sources = arena.value_returned(sources);
    let whole = arena.value_type_path(integer, start, end);
    assert_eq!(
        arena.value_type(ends.carrier),
        arena.value_type(whole),
        "the whisker stands over the paths from the first column's start to the last's end"
    );
    let (held, wanted) = (
        arena.computation_return(ends.left),
        arena.computation_return(sources),
    );
    assert_eq!(
        compared(&arena, held, wanted),
        CertificateEquality::Equal,
        "the whisker starts at the sources' fold"
    );

    let (horizontal, _) = compose_columns(&mut arena, columns(&[one, one]), &[
        (alpha, two_cell(first, low, high)),
        (beta, two_cell(second, onward, onward_high)),
    ])
    .expect("the horizontal composite realises");
    let right = crate::identity::whisker(
        &mut arena,
        (integer, start, end),
        (low, onward),
        crate::identity::Whisker::Right,
        alpha,
    );
    let left = crate::identity::whisker(
        &mut arena,
        (integer, start, end),
        (high, onward),
        crate::identity::Whisker::Left,
        beta,
    );
    let both = crate::identity::then(&mut arena, whole, sources, right, left);
    let both = arena.value_returned(both);
    let both = arena.computation_return(both);
    assert_eq!(
        compared(&arena, realised(&arena, horizontal), both),
        CertificateEquality::Equal,
        "the horizontal composite realises as the right whisker then the left"
    );

    assert_eq!(
        compose_columns(&mut arena, chain(CellCount::from(2_usize)), &[
            (alpha, two_cell(first, low, high)),
            (beta, two_cell(second, onward, onward_high)),
        ]),
        None,
        "a chain pasting realises no level-two composite"
    );
    assert_eq!(
        compose_columns(&mut arena, columns(&[one, one]), &[(
            alpha,
            two_cell(first, low, high)
        )]),
        None,
        "a cell short realises none"
    );
}
