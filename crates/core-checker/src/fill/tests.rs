use alloc::boxed::Box;
use alloc::string::ToString as _;
use alloc::vec::Vec;

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
    /// `1` to `1`: the generator is `c₁ then c₂` itself, of dimension one.
    Composed,
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

/// The shape `chain(m)`: its cell count.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Shape(usize);

/// `fill[degree, bound](chain(cells), …)`'s composite.
///
/// # Specification
/// trivial.
fn chain(
    Head(degree, bound): Head,
    Shape(cells): Shape,
) -> Composite
{
    Composite {
        stratum: Stratum {
            degree: Degree::from(degree),
            bound: ShapeSize::from(bound),
        },
        pasting: Pasting::chain(CellCount::from(cells)).expect("the chain packs"),
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
/// function `here(s)` ascribed that type; for [`Sides::Composed`], `… =>
/// Path(ℤ, 1, 1)` returning `c₁ then c₂`.
///
/// # Specification
/// trivial.
fn generator(
    arena: &mut CoreArena,
    integers: Integers,
    sides: Sides,
) -> gandr_core_term::ComputationId
{
    let first = variable(arena, DeBruijnIndex::from(1_u32));
    let second = variable(arena, DeBruijnIndex::from(0_u32));
    let composite = identity::then(arena, integers.carrier, integers.one, first, second);
    let composite = arena.value_returned(composite);
    let (result, returned) = match sides {
        Sides::Composite => (
            arena.value_type_path(integers.cell, composite, composite),
            arena.value_here(composite),
        ),
        Sides::Fixed => (
            arena.value_type_path(integers.cell, integers.reflexive, integers.reflexive),
            arena.value_here(integers.reflexive),
        ),
        Sides::Composed => (integers.cell, composite),
    };
    let inner = arena.comp_type_returner(result);
    let inner = arena.comp_type_pi(integers.cell, inner);
    let thunked = arena.value_type_thunk(inner);
    let outer = arena.comp_type_returner(thunked);
    let outer = arena.comp_type_pi(integers.cell, outer);
    let thunked = arena.value_type_thunk(outer);
    let ty = arena.comp_type_returner(thunked);
    let body = arena.computation_return(returned);
    let body = arena.computation_lambda(body);
    let body = arena.value_thunk(body);
    let body = arena.computation_return(body);
    let body = arena.computation_lambda(body);
    let body = arena.value_thunk(body);
    let body = arena.computation_return(body);
    arena.computation_ascribe(body, ty)
}

/// `(x : ℤ) => (y : ℤ) => (c : Path(ℤ, x, y)) => Path(ℤ, x, y)`, the one
/// cell's pasting context, as a computation returning the curried function
/// answering `c` ascribed that type.
///
/// # Specification
/// trivial.
fn one_cell(
    arena: &mut CoreArena,
    integers: Integers,
) -> gandr_core_term::ComputationId
{
    let x = variable(arena, DeBruijnIndex::from(2_u32));
    let y = variable(arena, DeBruijnIndex::from(1_u32));
    let result = arena.value_type_path(integers.carrier, x, y);
    let codomain = arena.comp_type_returner(result);
    let x = variable(arena, DeBruijnIndex::from(1_u32));
    let y = variable(arena, DeBruijnIndex::from(0_u32));
    let cell = arena.value_type_path(integers.carrier, x, y);
    let codomain = arena.comp_type_pi(cell, codomain);
    let mut ty = codomain;
    for _ in 0_u8 .. 2_u8 {
        let thunked = arena.value_type_thunk(ty);
        let returned = arena.comp_type_returner(thunked);
        ty = arena.comp_type_pi(integers.carrier, returned);
    }
    let thunked = arena.value_type_thunk(ty);
    let ty = arena.comp_type_returner(thunked);
    let answered = variable(arena, DeBruijnIndex::from(0_u32));
    let mut body = arena.computation_return(answered);
    for _ in 0_u8 .. 3_u8 {
        let lambda = arena.computation_lambda(body);
        let thunk = arena.value_thunk(lambda);
        body = arena.computation_return(thunk);
    }
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
        chain(Head(5, 7), Shape(2)),
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
fn a_cell_of_dimension_one_fills_its_square_by_induction()
{
    let mut arena = CoreArena::new();
    let integers = integers(&mut arena);
    // `p : Path(ℤ, 1, 1)`, then `α : Path(Path(ℤ, 1, 1), here(1), p)`.
    let moving = variable(&mut arena, DeBruijnIndex::from(0_u32));
    let lifted = arena.value_type_path(integers.cell, integers.reflexive, moving);
    let alpha = variable(&mut arena, DeBruijnIndex::from(0_u32));
    let p = variable(&mut arena, DeBruijnIndex::from(1_u32));
    let generator = generator(&mut arena, integers, Sides::Composed);
    let fill = arena.value_fill(
        chain(Head(5, 7), Shape(2)),
        generator,
        Box::from([alpha, integers.reflexive]),
    );
    // `t⁻ then here(1)` to `here(1) then t⁺`, by `then`'s unit laws.
    let expected = arena.value_type_path(integers.cell, integers.reflexive, p);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    context.binders().open(Zone::Intuitionistic, integers.cell);
    context.binders().open(Zone::Intuitionistic, lifted);
    let square = synthesise_value(&mut context, fill)
        .expect("the induction on α checks against its square")
        .produced()
        .id();
    assert_eq!(
        equivalent(&mut context, square, expected),
        Ok(Agreement::Convertible),
        "the square runs from `c₁ then c₂` with α at its left end to it with α at its right"
    );
    assert!(
        matches!(context.nesting().get(&fill), Some(&Nesting::Filled(_))),
        "the fill is decided as its induction"
    );
}

/// A fill the rule decides computes to its induction wherever it stands. Over
/// the reflexive cell `here(here(1))` the induction is its base, `here` of the
/// square's side, the generator's `here` at the reflexive cells. So a type
/// mentioning the fill converts with one mentioning that `here`. Before the
/// rule decides it, the fill is inert and converts with nothing but itself.
#[test]
fn a_realised_fill_converts_with_here_in_a_type()
{
    let mut arena = CoreArena::new();
    let integers = integers(&mut arena);
    let still = arena.value_here(integers.reflexive);
    let generator = generator(&mut arena, integers, Sides::Composite);
    let fill = arena.value_fill(
        chain(Head(5, 7), Shape(2)),
        generator,
        Box::from([still, integers.reflexive]),
    );
    let side = identity::then(
        &mut arena,
        integers.carrier,
        integers.one,
        integers.reflexive,
        integers.reflexive,
    );
    let side = arena.value_returned(side);
    let generated = arena.value_here(side);
    let induced = arena.value_here(generated);
    let square = arena.value_type_path(integers.cell, side, side);
    let solid = arena.value_type_path(square, generated, generated);
    let at_fill = arena.value_type_path(solid, fill, fill);
    let at_here = arena.value_type_path(solid, induced, induced);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    assert_eq!(
        equivalent(&mut context, at_fill, at_here),
        Ok(Agreement::Apart),
        "an undecided fill is inert"
    );
    let _square =
        synthesise_value(&mut context, fill).expect("the induction on here(here(1)) checks");
    assert_eq!(
        equivalent(&mut context, at_fill, at_here),
        Ok(Agreement::Convertible),
        "the decided fill computes to the generator's `here` at the reflexive cells"
    );
}

#[test]
fn vertex_paths_fill_their_square_by_induction()
{
    let mut arena = CoreArena::new();
    let integers = integers(&mut arena);
    let index = |arena: &mut CoreArena, at: u32| variable(arena, DeBruijnIndex::from(at));
    // `x⁺ : ℤ`, `x→ : Path(ℤ, 1, x⁺)`, `y⁺ : ℤ`, `y→ : Path(ℤ, 1, y⁺)`.
    let right = index(&mut arena, 0);
    let vertex = arena.value_type_path(integers.carrier, integers.one, right);
    // `c⁺ : Path(ℤ, x⁺, y⁺)`.
    let (x, y) = (index(&mut arena, 3), index(&mut arena, 1));
    let ends = arena.value_type_path(integers.carrier, x, y);
    // `c→ : Path(Path(ℤ, 1, y⁺), here(1) then y→, x→ then c⁺)`.
    let (y, y_path) = (index(&mut arena, 2), index(&mut arena, 1));
    let (x_path, c) = (index(&mut arena, 3), index(&mut arena, 0));
    let outer = arena.value_type_path(integers.carrier, integers.one, y);
    let source = identity::then(
        &mut arena,
        integers.carrier,
        integers.one,
        integers.reflexive,
        y_path,
    );
    let source = arena.value_returned(source);
    let target = identity::then(&mut arena, integers.carrier, integers.one, x_path, c);
    let target = arena.value_returned(target);
    let square_cell = arena.value_type_path(outer, source, target);
    let generator = one_cell(&mut arena, integers);
    let (x_path, y_path, c_path) = (
        index(&mut arena, 4),
        index(&mut arena, 2),
        index(&mut arena, 0),
    );
    let fill = arena.value_fill(
        chain(Head(5, 7), Shape(1)),
        generator,
        Box::from([x_path, y_path, c_path]),
    );
    // `t⁻ then y→` to `x→ then t⁺`, `t⁻` the cell `here(1)` and `t⁺` `c⁺`.
    let (y, c) = (index(&mut arena, 3), index(&mut arena, 1));
    let outer = arena.value_type_path(integers.carrier, integers.one, y);
    let source = identity::then(
        &mut arena,
        integers.carrier,
        integers.one,
        integers.reflexive,
        y_path,
    );
    let source = arena.value_returned(source);
    let target = identity::then(&mut arena, integers.carrier, integers.one, x_path, c);
    let target = arena.value_returned(target);
    let expected = arena.value_type_path(outer, source, target);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    for ty in [
        integers.carrier,
        vertex,
        integers.carrier,
        vertex,
        ends,
        square_cell,
    ] {
        context.binders().open(Zone::Intuitionistic, ty);
    }
    let square = synthesise_value(&mut context, fill)
        .expect("the inductions on x→, y→ and c→ check against their square")
        .produced()
        .id();
    assert_eq!(
        equivalent(&mut context, square, expected),
        Ok(Agreement::Convertible),
        "the square runs from `t⁻ then y→` to `x→ then t⁺`"
    );
    assert!(
        matches!(context.nesting().get(&fill), Some(&Nesting::Filled(_))),
        "the fill is decided as its induction"
    );
}

#[test]
fn a_set_that_is_no_pasting_context_is_refused()
{
    let mut arena = CoreArena::new();
    let integers = integers(&mut arena);
    let index = |arena: &mut CoreArena, at: u32| variable(arena, DeBruijnIndex::from(at));
    let generator = one_cell(&mut arena, integers);
    // `y⁺ : ℤ`, `y→ : Path(ℤ, 1, y⁺)`, `q : Path(ℤ, 1, y⁺)`, `c⁺ : Path(ℤ, 1,
    // y⁺)`, then `c→ : Path(Path(ℤ, 1, y⁺), here(1) then q, c⁺)`.
    let right = index(&mut arena, 0);
    let vertex = arena.value_type_path(integers.carrier, integers.one, right);
    let right = index(&mut arena, 1);
    let other = arena.value_type_path(integers.carrier, integers.one, right);
    let right = index(&mut arena, 2);
    let ends = arena.value_type_path(integers.carrier, integers.one, right);
    let (y, q, c) = (
        index(&mut arena, 3),
        index(&mut arena, 1),
        index(&mut arena, 0),
    );
    let outer = arena.value_type_path(integers.carrier, integers.one, y);
    let source = identity::then(
        &mut arena,
        integers.carrier,
        integers.one,
        integers.reflexive,
        q,
    );
    let source = arena.value_returned(source);
    let square_cell = arena.value_type_path(outer, source, c);
    let (y_path, c_path) = (index(&mut arena, 3), index(&mut arena, 0));
    let unwhiskered = arena.value_fill(
        chain(Head(5, 7), Shape(1)),
        generator,
        Box::from([integers.one, y_path, c_path]),
    );
    // Past those, `x⁺ : ℤ` and `x→ : Path(ℤ, 1, x⁺)` beside the cell `here(1)`.
    let x_path = index(&mut arena, 0);
    let open = arena.value_fill(
        chain(Head(5, 7), Shape(1)),
        generator,
        Box::from([x_path, integers.one, integers.reflexive]),
    );
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    for ty in [integers.carrier, vertex, other, ends, square_cell] {
        context.binders().open(Zone::Intuitionistic, ty);
    }
    assert!(
        matches!(
            synthesise_value(&mut context, unwhiskered),
            Err(CheckRefusal::NoFiller { at, .. }) if at == unwhiskered
        ),
        "a cell's square whose side is no whisker of its vertex's path is refused"
    );
    for ty in [integers.carrier, vertex] {
        context.binders().open(Zone::Intuitionistic, ty);
    }
    assert!(
        matches!(
            synthesise_value(&mut context, open),
            Err(CheckRefusal::NoFiller { at, .. }) if at == open
        ),
        "a vertex of X beside a cell outside it is refused"
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
        chain(Head(0, 7), Shape(2)),
        composite,
        Box::from([alpha, integers.reflexive]),
    );
    let unlifted = arena.value_fill(
        chain(Head(5, 7), Shape(2)),
        composite,
        Box::from([integers.reflexive, integers.reflexive]),
    );
    let sideless = arena.value_fill(
        chain(Head(5, 7), Shape(2)),
        fixed,
        Box::from([alpha, integers.reflexive]),
    );
    let directed = arena.value_fill(
        chain(Head(5, 7), Shape(2)),
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

/// `fill[degree, bound](chain(2, (a₁, a₂)), …)`'s composite.
///
/// # Specification
/// trivial.
fn columns(
    Head(degree, bound): Head,
    heights: [CellCount; 2],
) -> Composite
{
    Composite {
        stratum: Stratum {
            degree: Degree::from(degree),
            bound: ShapeSize::from(bound),
        },
        pasting: Pasting::columns(&heights).expect("two columns pack"),
    }
}

#[test]
fn a_level_two_fill_names_x_by_its_columns()
{
    let mut arena = CoreArena::new();
    let integers = integers(&mut arena);
    let moving = variable(&mut arena, DeBruijnIndex::from(0_u32));
    let lifted = arena.value_type_path(integers.cell, integers.reflexive, moving);
    let alpha = variable(&mut arena, DeBruijnIndex::from(0_u32));
    let generator = generator(&mut arena, integers, Sides::Composite);
    let cells = || Box::from([alpha, integers.reflexive]);
    let [none, one, two] = [0_usize, 1, 2].map(CellCount::from);
    let whiskered = arena.value_fill(columns(Head(4, 9), [one, none]), generator, cells());
    let crossed = arena.value_fill(columns(Head(4, 9), [none, one]), generator, cells());
    let tall = arena.value_fill(columns(Head(6, 11), [two, none]), generator, cells());
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    context.binders().open(Zone::Intuitionistic, integers.cell);
    context.binders().open(Zone::Intuitionistic, lifted);
    assert!(
        synthesise_value(&mut context, whiskered).is_ok(),
        "the whisker names α as its column of one 2-cell and fills as the chain does"
    );
    for (refused, name) in [
        (crossed, "a column of one 2-cell at a plain cell"),
        (tall, "a column of two 2-cells"),
    ] {
        assert!(
            matches!(
                synthesise_value(&mut context, refused),
                Err(CheckRefusal::ComposeNotAShape { at, .. }) if at == refused
            ),
            "{name} is refused by name"
        );
    }
}

/// The variable at `position` of a context `depth` binders deep.
///
/// # Specification
/// trivial.
fn at(
    arena: &mut CoreArena,
    depth: DeBruijnIndex,
    position: DeBruijnIndex,
) -> ValueId
{
    let index = u32::from(depth)
        .saturating_sub(u32::from(position))
        .saturating_sub(1);
    variable(arena, DeBruijnIndex::from(index))
}

/// `f then g` over `Path(ℤ, start, _)`, returned.
///
/// # Specification
/// trivial.
fn composed(
    arena: &mut CoreArena,
    (carrier, start): (ValueTypeId, ValueId),
    (first, second): (ValueId, ValueId),
) -> ValueId
{
    let composite = identity::then(arena, carrier, start, first, second);
    arena.value_returned(composite)
}

/// `(f : Path(ℤ, x, y)) => (p : Path(ℤ, x, y)) => (a : Path(Path(ℤ, x, y), f,
/// p)) => (g : Path(ℤ, y, z)) => (q : Path(ℤ, y, z)) => (b : Path(Path(ℤ, y,
/// z), g, q)) => Path(Path(ℤ, x, z), f then g, p then q)`, thunked, under
/// `x`, `y` and `z`: the type of a horizontal composite of two 2-cells.
///
/// # Specification
/// trivial.
fn horizontal(
    arena: &mut CoreArena,
    integers: Integers,
) -> ValueTypeId
{
    let place = |arena: &mut CoreArena, depth: u32, position: u32| {
        at(
            arena,
            DeBruijnIndex::from(depth),
            DeBruijnIndex::from(position),
        )
    };
    let mut domains = Vec::new();
    for (depth, (start, end)) in [(3_u32, (0_u32, 1_u32)), (4, (0, 1))] {
        let (start, end) = (place(arena, depth, start), place(arena, depth, end));
        domains.push(arena.value_type_path(integers.carrier, start, end));
    }
    let (left, right, top, bottom) = (
        place(arena, 5, 0),
        place(arena, 5, 1),
        place(arena, 5, 3),
        place(arena, 5, 4),
    );
    let column = arena.value_type_path(integers.carrier, left, right);
    domains.push(arena.value_type_path(column, top, bottom));
    for depth in [6_u32, 7] {
        let (start, end) = (place(arena, depth, 1), place(arena, depth, 2));
        domains.push(arena.value_type_path(integers.carrier, start, end));
    }
    let (left, right, top, bottom) = (
        place(arena, 8, 1),
        place(arena, 8, 2),
        place(arena, 8, 6),
        place(arena, 8, 7),
    );
    let column = arena.value_type_path(integers.carrier, left, right);
    domains.push(arena.value_type_path(column, top, bottom));
    let (first, last) = (place(arena, 9, 0), place(arena, 9, 2));
    let (top, bottom, next_top, next_bottom) = (
        place(arena, 9, 3),
        place(arena, 9, 4),
        place(arena, 9, 6),
        place(arena, 9, 7),
    );
    let lo = composed(arena, (integers.carrier, first), (top, next_top));
    let hi = composed(arena, (integers.carrier, first), (bottom, next_bottom));
    let composites = arena.value_type_path(integers.carrier, first, last);
    let result = arena.value_type_path(composites, lo, hi);
    let mut codomain = arena.comp_type_returner(result);
    for (rank, &domain) in domains.iter().enumerate().rev() {
        if rank.saturating_add(1) < domains.len() {
            let thunked = arena.value_type_thunk(codomain);
            codomain = arena.comp_type_returner(thunked);
        }
        codomain = arena.comp_type_pi(domain, codomain);
    }
    arena.value_type_thunk(codomain)
}

/// Example 1.4 of the naturality paper over `ℤ`: the first column of `[2](1,
/// 1)` lifts, its 1-cells along their own carrier `Path(ℤ, x, y)`, and the
/// second stays.
#[test]
fn two_columns_fill_their_cylinders_by_induction()
{
    let mut arena = CoreArena::new();
    let integers = integers(&mut arena);
    let place = |arena: &mut CoreArena, depth: u32, position: u32| {
        at(
            arena,
            DeBruijnIndex::from(depth),
            DeBruijnIndex::from(position),
        )
    };
    // `x, y, z : ℤ`, `h` the generator, then the first column's cylinder:
    // `f`, `p` and `a` lifted, `aa` the square `a` fills.
    let mut context_types = Vec::from([integers.carrier; 3]);
    context_types.push(horizontal(&mut arena, integers));
    for (depth, ends) in [(4_u32, None), (5, None), (6, Some((4, 5)))]
        .into_iter()
        .chain([(7, None), (8, None), (9, Some((7, 8)))])
        .chain([(10, Some((4, 7))), (11, Some((5, 8)))])
    {
        let (left, right) = (place(&mut arena, depth, 0), place(&mut arena, depth, 1));
        let column = arena.value_type_path(integers.carrier, left, right);
        context_types.push(match ends {
            None => column,
            Some((lo, hi)) => {
                let (lo, hi) = (place(&mut arena, depth, lo), place(&mut arena, depth, hi));
                arena.value_type_path(column, lo, hi)
            },
        });
    }
    let (left, right) = (place(&mut arena, 12, 0), place(&mut arena, 12, 1));
    let column = arena.value_type_path(integers.carrier, left, right);
    let [fm, fa, pa, pp, am, ap] =
        [4, 6, 9, 8, 10, 11].map(|position| place(&mut arena, 12, position));
    let outer = arena.value_type_path(column, fm, pp);
    let source = composed(&mut arena, (column, fm), (am, pa));
    let target = composed(&mut arena, (column, fm), (fa, ap));
    context_types.push(arena.value_type_path(outer, source, target));
    // The second column, `g`, `q` and `b`, fixed.
    for depth in [13_u32, 14] {
        let (left, right) = (place(&mut arena, depth, 1), place(&mut arena, depth, 2));
        context_types.push(arena.value_type_path(integers.carrier, left, right));
    }
    let [left, right, top, bottom] = [1, 2, 13, 14].map(|position| place(&mut arena, 15, position));
    let column = arena.value_type_path(integers.carrier, left, right);
    context_types.push(arena.value_type_path(column, top, bottom));
    let [
        first,
        last,
        function,
        fm,
        fp,
        fa,
        pm,
        pp,
        pa,
        am,
        ap,
        aa,
        g0,
        q0,
        b0,
    ] = [0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
        .map(|position| place(&mut arena, 16, position));
    let generator = arena.computation_return(function);
    let [one] = [1_usize].map(CellCount::from);
    let fill = arena.value_fill(
        columns(Head(5, 11), [one, one]),
        generator,
        Box::from([fa, pa, aa, g0, q0, b0]),
    );
    let outside = arena.value_fill(
        columns(Head(5, 11), [one, one]),
        generator,
        Box::from([fa, pm, am, g0, q0, b0]),
    );
    // `t⁻ then (v ↑ X)` to `(u ↑ X) then t⁺`, `u ↑ X` and `v ↑ X` the right
    // whiskers of `f→` and `p→` by the second column's fixed 1-cells.
    let applied = |arena: &mut CoreArena, entries: [ValueId; 6]| {
        entries.into_iter().fold(function, |partial, entry| {
            let forced = arena.computation_force(partial);
            let applied = arena.computation_application(forced, entry);
            arena.value_returned(applied)
        })
    };
    let t_lo = applied(&mut arena, [fm, pm, am, g0, q0, b0]);
    let t_hi = applied(&mut arena, [fp, pp, ap, g0, q0, b0]);
    let ends = (integers.carrier, first, last);
    let u_up = identity::whisker(&mut arena, ends, (fm, g0), identity::Whisker::Right, fa);
    let v_up = identity::whisker(&mut arena, ends, (pm, q0), identity::Whisker::Right, pa);
    let composites = arena.value_type_path(integers.carrier, first, last);
    let u_lo = composed(&mut arena, (integers.carrier, first), (fm, g0));
    let v_hi = composed(&mut arena, (integers.carrier, first), (pp, q0));
    let sides = arena.value_type_path(composites, u_lo, v_hi);
    let source = composed(&mut arena, (composites, u_lo), (t_lo, v_up));
    let target = composed(&mut arena, (composites, u_lo), (u_up, t_hi));
    let expected = arena.value_type_path(sides, source, target);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    for ty in context_types {
        context.binders().open(Zone::Intuitionistic, ty);
    }
    let square = synthesise_value(&mut context, fill)
        .expect("the inductions on f→, p→ and a→ check against their cylinder")
        .produced()
        .id();
    assert_eq!(
        equivalent(&mut context, square, expected),
        Ok(Agreement::Convertible),
        "the square runs from `t⁻ then (v ↑ X)` to `(u ↑ X) then t⁺`"
    );
    assert!(
        matches!(context.nesting().get(&fill), Some(&Nesting::Filled(_))),
        "the fill is decided as its induction"
    );
    assert!(
        matches!(
            synthesise_value(&mut context, outside),
            Err(CheckRefusal::NoFiller { at, .. }) if at == outside
        ),
        "a 1-cell of X beside a 2-cell outside it is refused"
    );
}
