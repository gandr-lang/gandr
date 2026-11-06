//! The bar complex of a block's Lawvere theory: the term table, the normal
//! forms, the faces of a cell and the truncation.
//!
//! Three small theories carry the witnesses. The free theory on one unary
//! operation `s` has no rule. The theory `s(z) ⇒ z` has one rule that rewrites
//! a composite. The theory of `a(z, x) ⇒ x` and `a(x, z) ⇒ x` has two rules
//! that keep their variables, so the boundary of each boundary is zero.

use alloc::collections::BTreeMap;

use gandr_theory_coherent_resolutions::Arity;
use gandr_theory_coherent_resolutions::Arrow;
use gandr_theory_coherent_resolutions::BarBound;
use gandr_theory_coherent_resolutions::BarCell;
use gandr_theory_coherent_resolutions::BarDegree;
use gandr_theory_coherent_resolutions::Degeneracy;
use gandr_theory_coherent_resolutions::LawvereError;
use gandr_theory_coherent_resolutions::LawvereTheory;
use gandr_theory_coherent_resolutions::NormalizationBudget;
use gandr_theory_coherent_resolutions::Occurrences;
use gandr_theory_coherent_resolutions::Operation;
use gandr_theory_coherent_resolutions::TermPlace;
use gandr_theory_coherent_resolutions::TermSize;
use gandr_theory_coherent_resolutions::TermTable;
use gandr_theory_coherent_resolutions::Variable;
use gandr_theory_coherent_resolutions::root_rewrite;
use gandr_theory_coherent_resolutions::truncated;
use gandr_theory_discrete_morse::Complex as _;
use gandr_theory_discrete_morse::Incidence;
use gandr_theory_discrete_morse::Standing;
use quenchant_shape::shape::Maybe;

/// The budget of each theory here: more rewrites than any witness takes.
const BUDGET: usize = 1_000;

/// The first variable of a context, in `table`.
///
/// # Specification
/// trivial.
fn first(table: &mut TermTable) -> TermPlace
{
    table.var(Variable::from(0_usize))
}

/// The arrow of `terms` in `source` variables.
///
/// # Specification
/// trivial.
fn arrow(
    source: Arity,
    terms: Vec<TermPlace>,
) -> Arrow
{
    Arrow { source, terms }
}

/// The faces of `cell` in `theory`, each with its incidence, by cell.
///
/// # Specification
/// trivial.
fn faces_of(
    theory: &mut LawvereTheory,
    cell: &BarCell,
) -> Result<BTreeMap<BarCell, Incidence>, LawvereError>
{
    let mut faces = Vec::new();
    theory.faces(cell, &mut faces)?;
    Ok(faces.into_iter().collect())
}

/// The theory `s(z) ⇒ z`, with the places of `s(x₀)` and `z`.
///
/// # Specification
/// trivial.
fn collapsing() -> Result<(LawvereTheory, TermPlace, TermPlace), LawvereError>
{
    let (s, z) = (Operation::from(0_usize), Operation::from(1_usize));
    let mut table = TermTable::default();
    let x0 = first(&mut table);
    let zero = table.op(z, Vec::new())?;
    let left = table.op(s, vec![zero])?;
    let successor = table.op(s, vec![x0])?;
    let theory = LawvereTheory::new(
        vec![Arity::from(1_usize), Arity::from(0_usize)],
        vec![(left, zero)],
        table,
        NormalizationBudget::from(BUDGET),
    );
    Ok((theory, successor, zero))
}

#[test]
fn a_term_is_interned_once_after_its_arguments() -> Result<(), LawvereError>
{
    let mut table = TermTable::default();
    let x0 = first(&mut table);
    let s = Operation::from(0_usize);
    let once = table.op(s, vec![x0])?;
    assert_eq!(
        table.op(s, vec![x0])?,
        once,
        "an equal node takes its place again"
    );
    assert_eq!(first(&mut table), x0, "a variable takes its place again");
    assert_eq!(table.size(once)?, TermSize::from(2_usize));
    let twice = table.op(s, vec![once])?;
    assert_eq!(table.size(twice)?, TermSize::from(3_usize));
    let stray = TermPlace::from(99_usize);
    assert_eq!(table.op(s, vec![stray]), Err(LawvereError::Unissued(stray)));
    assert_eq!(table.node(stray), Err(LawvereError::Unissued(stray)));
    Ok(())
}

#[test]
fn substitution_fills_each_variable_and_refuses_an_unfilled_one() -> Result<(), LawvereError>
{
    let mut table = TermTable::default();
    let (a, s, z) = (
        Operation::from(0_usize),
        Operation::from(1_usize),
        Operation::from(2_usize),
    );
    let x0 = first(&mut table);
    let x1 = table.var(Variable::from(1_usize));
    let pair = table.op(a, vec![x0, x1])?;
    let zero = table.op(z, Vec::new())?;
    let one = table.op(s, vec![zero])?;
    let filled = table.substituted(pair, &[one, zero])?;
    assert_eq!(filled, table.op(a, vec![one, zero])?);
    assert_eq!(
        table.substituted(pair, &[one]),
        Err(LawvereError::Unfilled(Variable::from(1_usize))),
        "a tuple of one term fills no second variable"
    );
    Ok(())
}

#[test]
fn occurrences_count_each_path_from_the_root() -> Result<(), LawvereError>
{
    let mut table = TermTable::default();
    let (a, s) = (Operation::from(0_usize), Operation::from(1_usize));
    let x0 = first(&mut table);
    let successor = table.op(s, vec![x0])?;
    let shared = table.op(a, vec![successor, successor])?;
    let mut counts = BTreeMap::new();
    table.occurrences(shared, &mut counts)?;
    assert_eq!(
        counts,
        BTreeMap::from([(Variable::from(0_usize), Occurrences::from(2_usize))]),
        "the one node `s(x₀)` stands on two paths"
    );
    Ok(())
}

#[test]
fn a_normal_form_rewrites_innermost_first_within_its_budget() -> Result<(), LawvereError>
{
    let (mut theory, successor, zero) = collapsing()?;
    let s = Operation::from(0_usize);
    let one = theory.table_mut().op(s, vec![zero])?;
    let two = theory.table_mut().op(s, vec![one])?;
    assert_eq!(theory.redex(one)?, Maybe::Present(zero));
    assert_eq!(
        theory.redex(two)?,
        Maybe::Absent(root_rewrite::Absent::NoRule),
        "no rule matches `s(s(z))` at its root"
    );
    assert_eq!(
        theory.normal_form(two)?,
        zero,
        "the inner redex rewrites first, which makes a redex at the root"
    );
    assert_eq!(theory.normal_form(successor)?, successor);

    let mut table = TermTable::default();
    let x0 = first(&mut table);
    let looped = table.op(Operation::from(0_usize), vec![x0])?;
    let mut looping = LawvereTheory::new(
        vec![Arity::from(1_usize)],
        vec![(looped, looped)],
        table,
        NormalizationBudget::from(10_usize),
    );
    assert_eq!(
        looping.normal_form(looped),
        Err(LawvereError::Exhausted(looped))
    );
    Ok(())
}

#[test]
fn a_cell_is_degenerate_on_a_leading_variable_or_a_later_identity() -> Result<(), LawvereError>
{
    let (theory, successor, zero) = collapsing()?;
    let table = theory.table();
    let x0 = TermPlace::from(0_usize);
    let (none, one) = (Arity::from(0_usize), Arity::from(1_usize));
    let cases = [
        (BarCell(Vec::new()), Degeneracy::Proper),
        (
            BarCell(vec![arrow(one, Vec::new())]),
            Degeneracy::Degenerate,
        ),
        (BarCell(vec![arrow(one, vec![x0])]), Degeneracy::Degenerate),
        (
            BarCell(vec![arrow(one, vec![successor]), arrow(one, vec![x0])]),
            Degeneracy::Degenerate,
        ),
        (
            BarCell(vec![arrow(one, vec![successor]), arrow(none, vec![zero])]),
            Degeneracy::Proper,
        ),
    ];
    for (cell, expected) in cases {
        assert_eq!(cell.degeneracy(table)?, expected, "{cell:?}");
    }
    Ok(())
}

#[test]
fn the_faces_of_a_cell_are_its_first_inner_and_last_faces() -> Result<(), LawvereError>
{
    let s = Operation::from(0_usize);
    let one = Arity::from(1_usize);
    let mut table = TermTable::default();
    let x0 = first(&mut table);
    let successor = table.op(s, vec![x0])?;
    let twice = table.op(s, vec![successor])?;
    let doubled = table.op(Operation::from(1_usize), vec![x0, x0])?;
    let mut free = LawvereTheory::new(
        vec![one, Arity::from(2_usize)],
        Vec::new(),
        table,
        NormalizationBudget::from(BUDGET),
    );
    let square = BarCell(vec![
        arrow(one, vec![successor]),
        arrow(one, vec![successor]),
    ]);
    assert_eq!(
        faces_of(&mut free, &square)?,
        BTreeMap::from([
            (
                BarCell(vec![arrow(one, vec![successor])]),
                Incidence::from(2_i64)
            ),
            (
                BarCell(vec![arrow(one, vec![twice])]),
                Incidence::from(-1_i64)
            ),
        ]),
        "the first and the last face of `[s(x₀)|s(x₀)]` are one cell, summed"
    );
    assert_eq!(
        faces_of(&mut free, &BarCell(vec![arrow(one, vec![doubled])]))?,
        BTreeMap::from([(BarCell(Vec::new()), Incidence::from(1_i64))]),
        "a term with two occurrences has the boundary `(2 − 1) []`"
    );
    assert_eq!(
        faces_of(&mut free, &BarCell(vec![arrow(one, vec![successor])]))?,
        BTreeMap::new(),
        "a term with one occurrence has the boundary zero"
    );

    let (mut theory, successor, zero) = collapsing()?;
    let cell = BarCell(vec![
        arrow(one, vec![successor]),
        arrow(Arity::from(0_usize), vec![zero]),
    ]);
    assert_eq!(
        faces_of(&mut theory, &cell)?,
        BTreeMap::from([(
            BarCell(vec![arrow(one, vec![successor])]),
            Incidence::from(1_i64)
        )]),
        "the composite `s(z)` rewrites to `z`, which cancels the first face"
    );
    Ok(())
}

#[test]
fn a_cell_outside_the_complex_stands_outside() -> Result<(), LawvereError>
{
    let (mut theory, successor, zero) = collapsing()?;
    let s = Operation::from(0_usize);
    let unreduced = theory.table_mut().op(s, vec![zero])?;
    let x0 = TermPlace::from(0_usize);
    let (none, one) = (Arity::from(0_usize), Arity::from(1_usize));
    let cases = [
        (BarCell(vec![arrow(one, vec![successor])]), Standing::Inside),
        (
            BarCell(vec![arrow(one, vec![successor]), arrow(none, vec![zero])]),
            Standing::Inside,
        ),
        (BarCell(vec![arrow(one, vec![x0])]), Standing::Outside),
        (
            BarCell(vec![arrow(one, vec![successor]), arrow(none, Vec::new())]),
            Standing::Outside,
        ),
        (
            BarCell(vec![arrow(none, vec![unreduced])]),
            Standing::Outside,
        ),
        (
            BarCell(vec![arrow(none, vec![successor])]),
            Standing::Outside,
        ),
    ];
    for (cell, expected) in cases {
        assert_eq!(theory.standing(&cell)?, expected, "{cell:?}");
    }
    Ok(())
}

#[test]
fn the_boundary_of_each_boundary_in_a_truncation_is_zero() -> Result<(), LawvereError>
{
    // `a` at place 0, `s` at place 1 and `z` at place 2: the rules name no
    // `s`, and the truncation builds its terms.
    let (a, z) = (Operation::from(0_usize), Operation::from(2_usize));
    let mut table = TermTable::default();
    let x0 = first(&mut table);
    let zero = table.op(z, Vec::new())?;
    let left_unit = table.op(a, vec![zero, x0])?;
    let right_unit = table.op(a, vec![x0, zero])?;
    let mut theory = LawvereTheory::new(
        vec![
            Arity::from(2_usize),
            Arity::from(1_usize),
            Arity::from(0_usize),
        ],
        vec![(left_unit, x0), (right_unit, x0)],
        table,
        NormalizationBudget::from(BUDGET),
    );
    let bound = BarBound {
        variables: Arity::from(2_usize),
        weight: TermSize::from(4_usize),
        degree: BarDegree::from(3_usize),
    };
    let truncation = theory.truncation(bound)?;
    for degree in 1 ..= 3_usize {
        let cells = truncation.cells(BarDegree::from(degree));
        assert!(!cells.is_empty(), "degree {degree} holds cells");
        for cell in cells {
            let Maybe::Present(faces) = truncation.faces(cell)
            else {
                panic!("{cell:?} has its faces");
            };
            let mut twice: BTreeMap<BarCell, i64> = BTreeMap::new();
            for &(ref face, outer) in faces {
                let Maybe::Present(below) = truncation.faces(face)
                else {
                    panic!("the face {face:?} of {cell:?} is in the truncation");
                };
                for &(ref lower, inner) in below {
                    let sum = twice.entry(lower.clone()).or_default();
                    *sum = sum.saturating_add(i64::from(outer).saturating_mul(i64::from(inner)));
                }
            }
            twice.retain(|_, sum| *sum != 0);
            assert_eq!(
                twice,
                BTreeMap::new(),
                "the boundary of the boundary of {cell:?}"
            );
        }
    }
    let unreduced = BarCell(vec![arrow(Arity::from(1_usize), vec![left_unit])]);
    assert_eq!(
        truncation.faces(&unreduced),
        Maybe::Absent(truncated::Absent::Outside),
        "the truncation holds no term that a rule rewrites"
    );
    assert!(
        truncation.cells(BarDegree::from(4_usize)).is_empty(),
        "the truncation holds no cell past its degree"
    );
    Ok(())
}
