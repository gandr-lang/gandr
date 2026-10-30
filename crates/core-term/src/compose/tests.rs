use gandr_kernel_term::BaseType;
use gandr_kernel_term::DeBruijnIndex;
use gandr_theory_sites::Degree;
use gandr_theory_sites::Shape;
use gandr_theory_sites::ShapeSize;

use super::CellCount;
use super::Composite;
use super::Ends;
use super::Level;
use super::Pasting;
use super::PastingError;
use super::Step;
use super::Tree;
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
        pasting: Pasting::chain(cells).expect("the chain packs"),
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
    assert_eq!(
        pasting,
        Pasting::chain(CellCount::from(usize::from(two.vertex_count())))
            .expect("the 2-chain packs"),
        "the hand-packed `[2]` is the chain the tree grafts"
    );
}

/// `[2]([1]([1]), [1]([1]))`, two 3-cells side by side.
///
/// # Specification
/// trivial.
fn two_three_cells() -> Tree
{
    let point = Tree::graft([]).expect("the point packs");
    let edge = Tree::graft([point]).expect("one leaf packs");
    let stalk = Tree::graft([edge]).expect("a stalk packs");
    Tree::graft([stalk, stalk]).expect("two stalks pack")
}

#[test]
fn a_tree_reads_back_what_it_grafts()
{
    let point = Tree::graft([]).expect("the point packs");
    assert_eq!(point, Tree::POINT, "no child grafts the point");
    let tree = two_three_cells();
    let stalk = Tree::graft([Tree::chain(CellCount::from(1_usize)).expect("[1] packs")])
        .expect("a stalk packs");
    assert!(
        tree.children().eq([stalk, stalk]),
        "the children read back in order"
    );
    assert_eq!(
        tree.leaves(),
        CellCount::from(2_usize),
        "two 3-cells, two leaves"
    );
    assert!(
        tree.columns().eq([1_usize, 1].map(CellCount::from)),
        "each stalk is one column of one child"
    );
    assert_eq!(
        Tree::from_walk(tree.walk()),
        Ok(tree),
        "the walk goes around the tree again"
    );

    let whisker = [1_usize, 0].map(CellCount::from);
    let level_two = Pasting::columns(&whisker).expect("the whisker packs");
    assert!(
        level_two.tree().columns().eq(whisker),
        "the whisker's columns read back"
    );
    assert_eq!(
        level_two.cells(),
        CellCount::from(2_usize),
        "a 2-cell and an empty column"
    );

    let filling = CellCount::from(31_usize);
    assert!(
        Tree::chain(filling).is_ok_and(|chain| chain.leaves() == filling),
        "31 leaves fill the word"
    );
    assert_eq!(
        Tree::chain(CellCount::from(32_usize)),
        Err(PastingError::PastTheWord),
        "32 leaves do not pack"
    );
    assert_eq!(
        Pasting::columns(&[CellCount::from(15_usize); 2]),
        Err(PastingError::PastTheWord),
        "a column's leaves count against the word"
    );
    for (walk, defect) in [
        (&[Step::Up][..], "goes up before it goes down"),
        (&[Step::Down][..], "ends below the root"),
    ] {
        assert_eq!(
            Tree::from_walk(walk.iter().copied()),
            Err(PastingError::NotATree),
            "a walk that {defect} goes around no tree"
        );
    }
    assert_eq!(
        Tree::from_walk([Step::Down, Step::Up].into_iter().cycle().take(64)),
        Err(PastingError::PastTheWord),
        "a walk of 64 steps does not pack"
    );
}

#[test]
fn a_pasting_stands_at_its_tree_s_height_or_above()
{
    let tree = two_three_cells();
    let three = Level::try_from(3_usize).expect("a byte holds three");
    assert!(
        Pasting::new(three, tree)
            .is_ok_and(|pasting| pasting.level() == three && pasting.tree() == tree),
        "two 3-cells stand at level three"
    );
    assert_eq!(
        Pasting::new(Level::TWO, tree),
        Err(PastingError::PastItsLevel),
        "two 3-cells stand at no level two"
    );
    assert!(
        Level::try_from(0_usize).is_err(),
        "no pasting stands at level zero"
    );

    let empty_columns =
        Pasting::columns(&[CellCount::from(0_usize); 2]).expect("two empty columns pack");
    let chain = Pasting::chain(CellCount::from(2_usize)).expect("the 2-chain packs");
    assert_eq!(
        empty_columns.tree(),
        chain.tree(),
        "[2](0, 0) is the tree [2]"
    );
    assert_ne!(
        empty_columns, chain,
        "the level parts the identities on a 2-chain from its composite"
    );
    assert_eq!(
        empty_columns.cells(),
        chain.cells(),
        "both read the two 1-cells"
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
        pasting: Pasting::columns(heights).expect("the columns pack"),
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
