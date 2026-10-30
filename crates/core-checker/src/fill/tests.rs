use alloc::boxed::Box;
use alloc::string::ToString as _;

use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::compose::CellCount;
use gandr_core_term::compose::Composite;
use gandr_core_term::compose::Pasting;
use gandr_core_term::identity;
use gandr_core_term::ua::Stratum;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::DeBruijnIndex;
use gandr_theory_sites::Degree;
use gandr_theory_sites::ShapeSize;

use super::UnsupportedFamily;
use crate::context::CheckBudget;
use crate::context::CheckingContext;
use crate::conversion::Agreement;
use crate::conversion::equivalent;
use crate::judgement::synthesise_value;
use crate::nested::Nesting;
use crate::refusal::CheckRefusal;
use crate::ua::StratumDefect;
use crate::view::ValueTypeView;
use crate::view::value_type_view;

/// A head `fill[degree, bound]`: its degree and its catalogue bound.
#[derive(Clone, Copy, Debug)]
struct Head(usize, usize);

/// What a fixture generator relates.
#[derive(Clone, Copy, Debug)]
enum Sides
{
    /// `c₁ then c₂` to itself.
    Composite,
    /// `here(1)` to itself, mentioning no cell.
    Fixed,
}

/// The fixture's closed terms over the integers.
#[derive(Clone, Copy, Debug)]
struct Integers
{
    /// The integers.
    carrier: ValueTypeId,
    /// The literal `1`.
    one: ValueId,
    /// `Path(ℤ, 1, 1)`, every cell's type.
    cell: ValueTypeId,
    /// `here(1)`.
    reflexive: ValueId,
}

/// The fixture's integers, minted fresh.
///
/// # Specification
/// trivial.
fn integers(arena: &mut CoreArena) -> Integers
{
    let carrier = arena.value_type_base(BaseType::Integer);
    let magnitude = gandr_kernel_term::Magnitude::from_decimal_text(1_u8.to_string())
        .expect("the digits are decimal");
    let one = arena.value_literal(gandr_kernel_term::Literal::Integer(
        gandr_kernel_term::IntegerLiteral::new(gandr_kernel_term::Sign::NonNegative, magnitude),
    ));
    let cell = arena.value_type_path(carrier, one, one);
    let reflexive = arena.value_here(one);
    Integers {
        carrier,
        one,
        cell,
        reflexive,
    }
}

/// `fill[degree, bound](chain(2), …)`'s composite.
///
/// # Specification
/// trivial.
fn chain(Head(degree, bound): Head) -> Composite
{
    Composite {
        stratum: Stratum {
            degree: Degree::from(degree),
            bound: ShapeSize::from(bound),
        },
        pasting: Pasting::Chain {
            cells: CellCount::from(2_usize),
        },
    }
}

/// The variable `index` binders out.
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

/// `(c₁ : Path(ℤ, 1, 1)) => (c₂ : Path(ℤ, 1, 1)) => Path(Path(ℤ, 1, 1), s,
/// s)`, `s` the sides `sides` names, as a computation returning the curried
/// function `here(s)` ascribed that type.
///
/// # Specification
/// trivial.
fn generator(
    arena: &mut CoreArena,
    integers: Integers,
    sides: Sides,
) -> gandr_core_term::ComputationId
{
    let side = match sides {
        Sides::Composite => {
            let first = variable(arena, DeBruijnIndex::from(1_u32));
            let second = variable(arena, DeBruijnIndex::from(0_u32));
            let composite = identity::then(arena, integers.carrier, integers.one, first, second);
            arena.value_returned(composite)
        },
        Sides::Fixed => integers.reflexive,
    };
    let result = arena.value_type_path(integers.cell, side, side);
    let inner = arena.comp_type_returner(result);
    let inner = arena.comp_type_pi(integers.cell, inner);
    let thunked = arena.value_type_thunk(inner);
    let outer = arena.comp_type_returner(thunked);
    let outer = arena.comp_type_pi(integers.cell, outer);
    let thunked = arena.value_type_thunk(outer);
    let ty = arena.comp_type_returner(thunked);
    let reflexive = arena.value_here(side);
    let body = arena.computation_return(reflexive);
    let body = arena.computation_lambda(body);
    let body = arena.value_thunk(body);
    let body = arena.computation_return(body);
    let body = arena.computation_lambda(body);
    let body = arena.value_thunk(body);
    let body = arena.computation_return(body);
    arena.computation_ascribe(body, ty)
}

#[test]
fn a_free_cell_fills_its_square_by_induction()
{
    let mut arena = CoreArena::new();
    let integers = integers(&mut arena);
    // `p : Path(ℤ, 1, 1)`, then `α : Path(Path(ℤ, 1, 1), here(1), p)`.
    let moving = variable(&mut arena, DeBruijnIndex::from(0_u32));
    let lifted = arena.value_type_path(integers.cell, integers.reflexive, moving);
    let alpha = variable(&mut arena, DeBruijnIndex::from(0_u32));
    let p = variable(&mut arena, DeBruijnIndex::from(1_u32));
    let generator = generator(&mut arena, integers, Sides::Composite);
    let fill = arena.value_fill(
        chain(Head(5, 7)),
        generator,
        Box::from([alpha, integers.reflexive]),
    );
    let low = identity::then(
        &mut arena,
        integers.carrier,
        integers.one,
        integers.reflexive,
        integers.reflexive,
    );
    let low = arena.value_returned(low);
    let high = identity::then(
        &mut arena,
        integers.carrier,
        integers.one,
        p,
        integers.reflexive,
    );
    let high = arena.value_returned(high);
    let ends = arena.value_type_path(integers.cell, low, high);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    context.binders().open(Zone::Intuitionistic, integers.cell);
    context.binders().open(Zone::Intuitionistic, lifted);
    let square = synthesise_value(&mut context, fill)
        .expect("the induction on α checks against its square")
        .produced()
        .id();
    let head = context
        .whnf_value_type(square)
        .expect("the square has a head");
    let ValueTypeView::Path { carrier, .. } =
        value_type_view(context.arena(), head).expect("the square has a view")
    else {
        panic!("the square is a path between paths");
    };
    assert_eq!(
        equivalent(&mut context, carrier, ends),
        Ok(Agreement::Convertible),
        "the square runs from `u` with α at its left end to `v` with α at its right"
    );
    assert!(
        matches!(context.nesting().get(&fill), Some(&Nesting::Filled(_))),
        "the fill is decided as its induction"
    );
}

#[test]
fn a_fill_refuses_each_defect_by_name()
{
    let mut arena = CoreArena::new();
    let integers = integers(&mut arena);
    let alpha = variable(&mut arena, DeBruijnIndex::from(0_u32));
    let moving = variable(&mut arena, DeBruijnIndex::from(0_u32));
    let lifted = arena.value_type_path(integers.cell, integers.reflexive, moving);
    let flow = arena.value_type_flow(integers.cell, integers.reflexive, integers.reflexive);
    let composite = generator(&mut arena, integers, Sides::Composite);
    let fixed = generator(&mut arena, integers, Sides::Fixed);
    let uncertified = arena.value_fill(
        chain(Head(0, 7)),
        composite,
        Box::from([alpha, integers.reflexive]),
    );
    let unlifted = arena.value_fill(
        chain(Head(5, 7)),
        composite,
        Box::from([integers.reflexive, integers.reflexive]),
    );
    let sideless = arena.value_fill(
        chain(Head(5, 7)),
        fixed,
        Box::from([alpha, integers.reflexive]),
    );
    let directed = arena.value_fill(
        chain(Head(5, 7)),
        composite,
        Box::from([alpha, integers.reflexive]),
    );
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    context.binders().open(Zone::Intuitionistic, integers.cell);
    context.binders().open(Zone::Intuitionistic, lifted);
    assert_eq!(
        synthesise_value(&mut context, uncertified).map(|_| ()),
        Err(CheckRefusal::FillUncertified {
            at: uncertified,
            stratum: StratumDefect::Degree {
                degree: Degree::from(0_usize),
            },
        }),
        "a stratum the chain sub-site does not certify is refused by its defect"
    );
    assert!(
        matches!(
            synthesise_value(&mut context, unlifted),
            Err(CheckRefusal::NoFiller { at, .. }) if at == unlifted
        ),
        "a fill with no cell of X is refused"
    );
    assert!(
        matches!(
            synthesise_value(&mut context, sideless),
            Err(CheckRefusal::NoFiller { at, .. }) if at == sideless
        ),
        "sides that are no composites of the cells are refused"
    );
    context
        .binders()
        .close(Zone::Intuitionistic)
        .expect("α's binder is open");
    context.binders().open(Zone::Intuitionistic, flow);
    assert_eq!(
        synthesise_value(&mut context, directed).map(|_| ()),
        Err(CheckRefusal::GeneratorFamilyUnsupported {
            at: directed,
            cell: alpha,
            family: UnsupportedFamily::Flow,
        }),
        "a directed cell of X is refused with the family"
    );
}
