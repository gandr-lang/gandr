//! Brown's collapsing scheme on the bar complex of `NatUnits`: the class and
//! the partner of each kind of cell, the rule that an overlap names, and the
//! check of the Morse crate on a truncation.

use alloc::collections::BTreeSet;

use gandr_theory_coherent_resolutions::Arity;
use gandr_theory_coherent_resolutions::Arrow;
use gandr_theory_coherent_resolutions::BarBound;
use gandr_theory_coherent_resolutions::BarCell;
use gandr_theory_coherent_resolutions::BarDegree;
use gandr_theory_coherent_resolutions::LawvereError;
use gandr_theory_coherent_resolutions::LawvereTheory;
use gandr_theory_coherent_resolutions::NormalizationBudget;
use gandr_theory_coherent_resolutions::Operation;
use gandr_theory_coherent_resolutions::RulePlace;
use gandr_theory_coherent_resolutions::TermPlace;
use gandr_theory_coherent_resolutions::TermSize;
use gandr_theory_coherent_resolutions::TermTable;
use gandr_theory_coherent_resolutions::Variable;
use gandr_theory_coherent_resolutions::overlapped;
use gandr_theory_discrete_morse::Budget;
use gandr_theory_discrete_morse::Class;
use gandr_theory_discrete_morse::Faults;
use gandr_theory_discrete_morse::MorseError;
use gandr_theory_discrete_morse::Scheme as _;
use quenchant_shape::shape::Maybe;

/// The terms of `NatUnits` that the witnesses name.
struct Terms
{
    /// The variable `x₁`.
    first: TermPlace,
    /// The variable `x₂`.
    second: TermPlace,
    /// `Zero`.
    nought: TermPlace,
    /// `add(x₁, x₂)`.
    sum: TermPlace,
    /// `add(x₁, x₁)`.
    double: TermPlace,
    /// `Succ(x₁)`.
    next: TermPlace,
    /// `Succ(Zero)`.
    one: TermPlace,
}

/// `NatUnits`: `Succ`, `Zero` and `add`, in name order, with the rules
/// `add(Zero, n) ⇒ n`, `add(m, Zero) ⇒ m` and
/// `add(Succ(m), n) ⇒ Succ(add(m, n))`.
///
/// # Specification
/// trivial.
fn nat_units() -> Result<(LawvereTheory, Terms), LawvereError>
{
    let (succ, zero, add) = (
        Operation::from(0_usize),
        Operation::from(1_usize),
        Operation::from(2_usize),
    );
    let mut table = TermTable::default();
    let first = table.var(Variable::from(0_usize));
    let second = table.var(Variable::from(1_usize));
    let nought = table.op(zero, Vec::new())?;
    let sum = table.op(add, vec![first, second])?;
    let double = table.op(add, vec![first, first])?;
    let next = table.op(succ, vec![first])?;
    let one = table.op(succ, vec![nought])?;
    let rules = vec![
        (table.op(add, vec![nought, first])?, first),
        (table.op(add, vec![first, nought])?, first),
        (
            table.op(add, vec![next, second])?,
            table.op(succ, vec![sum])?,
        ),
    ];
    let arities = [1_usize, 0, 2].map(Arity::from).to_vec();
    let theory = LawvereTheory::new(
        arities,
        rules,
        table,
        NormalizationBudget::from(1_000_usize),
    );
    Ok((theory, Terms {
        first,
        second,
        nought,
        sum,
        double,
        next,
        one,
    }))
}

/// The variables of an arrow's context in these witnesses.
#[derive(Clone, Copy, Debug)]
enum Context
{
    /// No variable.
    Closed,
    /// The variable `x₁`.
    One,
    /// The variables `x₁` and `x₂`.
    Two,
}

/// The arrow from the variables of `context` to `terms`.
///
/// # Specification
/// trivial.
fn arrow(
    context: Context,
    terms: &[TermPlace],
) -> Arrow
{
    let source = match context {
        Context::Closed => 0_usize,
        Context::One => 1,
        Context::Two => 2,
    };
    Arrow {
        source: Arity::from(source),
        terms: terms.to_vec(),
    }
}

/// The cell of `arrows`.
///
/// # Specification
/// trivial.
fn cell(arrows: &[Arrow]) -> BarCell
{
    BarCell(arrows.to_vec())
}

/// The left sides of the rules of `NatUnits`, as cells of degree two.
///
/// # Specification
/// trivial.
fn lefts(terms: &Terms) -> BTreeSet<BarCell>
{
    let &Terms {
        first,
        second,
        nought,
        sum,
        next,
        ..
    } = terms;
    BTreeSet::from([
        cell(&[
            arrow(Context::Two, &[sum]),
            arrow(Context::One, &[nought, first]),
        ]),
        cell(&[
            arrow(Context::Two, &[sum]),
            arrow(Context::One, &[first, nought]),
        ]),
        cell(&[
            arrow(Context::Two, &[sum]),
            arrow(Context::Two, &[next, second]),
        ]),
    ])
}

/// The two overlaps of the rules of `NatUnits`, as cells of degree three:
/// `add(Zero, Zero)` and `add(Succ(x₁), Zero)`.
///
/// # Specification
/// trivial.
fn overlaps(terms: &Terms) -> [BarCell; 2]
{
    let &Terms {
        first,
        second,
        nought,
        sum,
        next,
        ..
    } = terms;
    [
        cell(&[
            arrow(Context::Two, &[sum]),
            arrow(Context::One, &[first, nought]),
            arrow(Context::Closed, &[nought]),
        ]),
        cell(&[
            arrow(Context::Two, &[sum]),
            arrow(Context::Two, &[next, second]),
            arrow(Context::One, &[first, nought]),
        ]),
    ]
}

#[test]
fn the_cells_of_nat_units_take_the_classes_of_the_scheme() -> Result<(), LawvereError>
{
    // The subscript of an arrow counts the variables of its context.
    //
    // | Cell | Class | Partner |
    // | --- | --- | --- |
    // | `[Zero]₀` | essential | none |
    // | `[Zero]₁` | redundant | `[Zero₀|()₁]` |
    // | `[add(x₁, x₁)]₁` | redundant | `[add(x₁, x₂)|(x₁, x₁)₁]` |
    // | `[Succ(x₁)|(Zero)₀]` | collapsible | `[Succ(Zero)]₀` |
    // | `[add(x₁, x₂)|(Zero, Zero)₀]` | redundant | `[add(x₁, x₂)|(Zero, x₁)₁|(Zero)₀]` |
    // | `[add(x₁, x₂)|(Zero, x₁)₁|(Zero)₀]` | collapsible | `[add(x₁, x₂)|(Zero, Zero)₀]` |
    // | `[add(x₁, x₂)|(Succ(x₁), x₁)₁]` | redundant | `[add(x₁, x₂)|(Succ(x₁), x₂)₂|(x₁, x₁)₁]` |
    //
    // The redex `add(Zero, Zero)` of the fifth cell reads the first `Zero`,
    // so the rule `add(Zero, n) ⇒ n` cuts the tuple there. The sixth cell is
    // the fifth cell's partner, and the scheme names the fifth cell back.
    let (mut theory, terms) = nat_units()?;
    let Terms {
        first,
        second,
        nought,
        sum,
        double,
        next,
        one,
    } = terms;
    let (closed, unary, binary) = (Context::Closed, Context::One, Context::Two);
    let classes = [
        (cell(&[]), Class::Critical),
        (cell(&[arrow(closed, &[nought])]), Class::Critical),
        (
            cell(&[arrow(unary, &[nought])]),
            Class::Redundant(cell(&[arrow(closed, &[nought]), arrow(unary, &[])])),
        ),
        (
            cell(&[arrow(unary, &[double])]),
            Class::Redundant(cell(&[
                arrow(binary, &[sum]),
                arrow(unary, &[first, first]),
            ])),
        ),
        (
            cell(&[arrow(unary, &[next]), arrow(closed, &[nought])]),
            Class::Collapsible(cell(&[arrow(closed, &[one])])),
        ),
        (
            cell(&[arrow(binary, &[sum]), arrow(closed, &[nought, nought])]),
            Class::Redundant(cell(&[
                arrow(binary, &[sum]),
                arrow(unary, &[nought, first]),
                arrow(closed, &[nought]),
            ])),
        ),
        (
            cell(&[
                arrow(binary, &[sum]),
                arrow(unary, &[nought, first]),
                arrow(closed, &[nought]),
            ]),
            Class::Collapsible(cell(&[
                arrow(binary, &[sum]),
                arrow(closed, &[nought, nought]),
            ])),
        ),
        (
            cell(&[arrow(binary, &[sum]), arrow(unary, &[next, first])]),
            Class::Redundant(cell(&[
                arrow(binary, &[sum]),
                arrow(binary, &[next, second]),
                arrow(unary, &[first, first]),
            ])),
        ),
    ];
    for (held, class) in classes {
        assert_eq!(theory.class(&held)?, class, "{held:?}");
    }
    let [ref zero_first, ref succ_first] = overlaps(&terms);
    for essential in lefts(&terms).iter().chain([zero_first, succ_first]) {
        assert_eq!(theory.class(essential)?, Class::Critical, "{essential:?}");
    }
    Ok(())
}

#[test]
fn a_cell_led_by_a_variable_or_by_no_term_is_refused() -> Result<(), LawvereError>
{
    let (mut theory, terms) = nat_units()?;
    assert_eq!(
        theory.class(&cell(&[arrow(Context::One, &[terms.first])])),
        Err(LawvereError::LeadingVariable)
    );
    assert_eq!(
        theory.class(&cell(&[arrow(Context::Closed, &[])])),
        Err(LawvereError::NoTerm)
    );
    Ok(())
}

#[test]
fn an_overlap_names_the_rule_that_it_overlaps() -> Result<(), LawvereError>
{
    // `add(Zero, Zero)` is `add(m, Zero)` overlapped by `add(Zero, n)`, and
    // `add(Succ(x₁), Zero)` is `add(Succ(m), n)` overlapped by `add(m, Zero)`.
    let (mut theory, terms) = nat_units()?;
    let [zero_first, succ_first] = overlaps(&terms);
    assert_eq!(
        theory.overlapping(&zero_first)?,
        Maybe::Present(RulePlace::from(0_usize))
    );
    assert_eq!(
        theory.overlapping(&succ_first)?,
        Maybe::Present(RulePlace::from(1_usize))
    );
    assert_eq!(
        theory.overlapping(&cell(&[arrow(Context::Two, &[terms.sum])]))?,
        Maybe::Absent(overlapped::Absent::Short)
    );
    let stuck = cell(&[
        arrow(Context::One, &[terms.next]),
        arrow(Context::Closed, &[terms.nought]),
    ]);
    assert_eq!(
        theory.overlapping(&stuck)?,
        Maybe::Absent(overlapped::Absent::NoRedex)
    );
    Ok(())
}

#[test]
fn a_truncation_of_nat_units_collapses_onto_its_generators_rules_and_overlaps()
-> Result<(), MorseError<LawvereError>>
{
    // The try-first of the scheme's unit. The bound holds the largest
    // essential cell, `[add(x₁, x₂)|(Succ(x₁), x₂)₂|(x₁, Zero)₁]` of size
    // eight. The check finds no fault, and the critical cells are the three
    // generators, the three left sides and the two overlaps.
    let (mut theory, terms) = nat_units()?;
    let bound = BarBound {
        variables: Arity::from(2_usize),
        weight: TermSize::from(8_usize),
        degree: BarDegree::from(3_usize),
    };
    let truncation = theory.truncation(bound)?;
    let degrees = 1 ..= 3_usize;
    let cells = degrees.flat_map(|degree| truncation.cells(BarDegree::from(degree)));
    let done =
        gandr_theory_discrete_morse::collapse(&mut theory, cells, Budget::from(100_000_usize))?;
    assert_eq!(done.faults(), Faults::default());
    let mut by_degree = vec![BTreeSet::new(); 3];
    for critical in done.critical() {
        let slot = usize::from(critical.degree()).saturating_sub(1);
        if let Some(found) = by_degree.get_mut(slot) {
            let _new = found.insert(critical.clone());
        }
    }
    let generators = BTreeSet::from([
        cell(&[arrow(Context::One, &[terms.next])]),
        cell(&[arrow(Context::Closed, &[terms.nought])]),
        cell(&[arrow(Context::Two, &[terms.sum])]),
    ]);
    assert_eq!(by_degree, [
        generators,
        lefts(&terms),
        BTreeSet::from(overlaps(&terms))
    ]);
    Ok(())
}
