use alloc::sync::Arc;
use alloc::vec;

use gandr_core_term::CompType;
use gandr_core_term::CoreArena;
use gandr_kernel_term::BaseType;

use super::*;
use crate::CheckBudget;

#[test]
fn a_branch_binds_a_field_only_where_its_result_names_it()
{
    let mut arena = CoreArena::new();
    let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let integer = arena.value_type_base(BaseType::Integer);
    let boxed = ConstantIndex::from(0_usize);
    let signature = Arc::new(DataSignature::new(vec![], vec![vec![integer]], kind));
    let datatype = arena.value_type_data(boxed, vec![]);
    let closed = arena.comp_type_returner(integer);
    let scrutinee = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let named = arena.value_type_path(datatype, scrutinee, scrutinee);
    let dependent = arena.comp_type_returner(named);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    context.adopt_data(boxed, signature).expect("the box forms");
    let unnamed = branch_type(
        &mut context,
        datatype,
        ConstructorTag::from(0_usize),
        closed,
    )
    .expect("the closed branch forms");
    let renamed = branch_type(
        &mut context,
        datatype,
        ConstructorTag::from(0_usize),
        dependent,
    )
    .expect("the dependent branch forms");
    assert!(
        matches!(
            context.arena().comp_type(unnamed),
            Some(&CompType::Arrow { domain, codomain }) if domain == integer && codomain == closed
        ),
        "a result naming no field is the plain arrow over it"
    );
    assert!(
        matches!(
            context.arena().comp_type(renamed),
            Some(&CompType::Pi { domain, .. }) if domain == integer
        ),
        "a result naming the field binds it"
    );
}

/// A family indexed by the unit type whose one constructor `Mark(u)` stands
/// at its field: the branch at `Mark` binds `u`, then `Path(Unit, u, ())`
/// from that stated index to the scrutinee's, and the closed result. The
/// field is a Π because the equation names it; the equation an arrow
/// because the result names neither.
#[test]
fn an_indexed_branch_binds_its_equations_after_its_fields()
{
    let mut arena = CoreArena::new();
    let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let unit_type = arena.value_type_unit();
    let integer = arena.value_type_base(BaseType::Integer);
    let field = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let marked = ConstantIndex::from(0_usize);
    let signature = Arc::new(
        DataSignature::new(vec![], vec![vec![unit_type]], kind)
            .indexed(vec![unit_type], vec![vec![field]]),
    );
    let unit = arena.value_unit();
    let datatype = arena.value_type_data(marked, vec![unit]);
    let closed = arena.comp_type_returner(integer);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    context
        .adopt_data(marked, signature)
        .expect("the marked family forms");
    let branch = branch_type(
        &mut context,
        datatype,
        ConstructorTag::from(0_usize),
        closed,
    )
    .expect("the indexed branch forms");
    let arena = context.arena();
    let Some(&CompType::Pi {
        domain,
        codomain: rest,
    }) = arena.comp_type(branch)
    else {
        panic!("the field binds the equation that names it");
    };
    assert_eq!(domain, unit_type, "the field reads at its declared type");
    let Some(&CompType::Arrow {
        domain: equation,
        codomain,
    }) = arena.comp_type(rest)
    else {
        panic!("the equation binds a result that names it not");
    };
    assert_eq!(codomain, closed, "the result is the closed motive");
    let Some(&ValueType::Path {
        carrier,
        left,
        right,
    }) = arena.value_type(equation)
    else {
        panic!("the equation is a path: {:?}", arena.value_type(equation));
    };
    assert_eq!(carrier, unit_type, "the equation is at the index's type");
    assert_eq!(right, unit, "the equation ends at the scrutinee's index");
    assert_eq!(
        arena.value(left),
        Some(&Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(0_u32),
        }),
        "the equation starts at the index the constructor states, its field"
    );
}

/// A field stands below its declaration's universe: a box of types at the
/// smallest universe is refused at the field, and the same box one
/// universe up forms.
#[test]
fn a_field_above_its_declaration_s_universe_is_refused()
{
    let mut arena = CoreArena::new();
    let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let one = Level::zero().succ().expect("the successor of zero");
    let large = arena.value_type_universe(Sort::Ground(GroundSort::Value), one);
    let boxed = ConstantIndex::from(0_usize);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let refused = context.adopt_data(
        boxed,
        Arc::new(DataSignature::new(vec![], vec![vec![small]], small)),
    );
    assert!(
        matches!(
            refused,
            Err(CheckRefusal::DataFieldLevel { field, kind }) if field == small && kind == small
        ),
        "a type of types is no field at the smallest universe: {refused:?}"
    );
    let formed = context.adopt_data(
        boxed,
        Arc::new(DataSignature::new(vec![], vec![vec![small]], large)),
    );
    assert!(formed.is_ok(), "one universe up it forms: {formed:?}");
}

#[test]
fn a_later_field_reads_its_parameters_past_the_earlier_fields()
{
    // `Pair(a : Type) { mk : (x : El a, y : El a) }`, the second field's `a`
    // one binder out, past `x`; and `Box { put : (a : Type, x : El a) }`,
    // whose second field names the first.
    let mut arena = CoreArena::new();
    let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let one = Level::zero().succ().expect("the successor of zero");
    let large = arena.value_type_universe(Sort::Ground(GroundSort::Value), one);
    let integer = arena.value_type_base(BaseType::Integer);
    let code = arena.value_quote(integer);
    let near = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let far = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let first = arena.value_type_element(near, Level::zero());
    let second = arena.value_type_element(far, Level::zero());
    let pair = ConstantIndex::from(0_usize);
    let boxed = ConstantIndex::from(1_usize);
    let pairs = Arc::new(DataSignature::new(
        vec![kind],
        vec![vec![first, second]],
        kind,
    ));
    let boxes = Arc::new(DataSignature::new(vec![], vec![vec![kind, first]], large));
    let at_integer = arena.value_type_data(pair, vec![code]);
    let boxed_type = arena.value_type_data(boxed, vec![]);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    context.adopt_data(pair, pairs).expect("the pair forms");
    context.adopt_data(boxed, boxes).expect("the box forms");
    for (field, position) in [(first, 0_usize), (second, 1_usize)] {
        let outside = field_outside(
            &mut context,
            at_integer,
            field,
            FieldPosition::from(position),
        )
        .expect("the field reads at the application");
        assert_eq!(
            outside,
            Maybe::Present(integer),
            "field {position} reads its parameter at the argument"
        );
    }
    assert_eq!(
        field_outside(
            &mut context,
            boxed_type,
            first,
            FieldPosition::from(1_usize)
        ),
        Ok(Maybe::Absent(outside::Absent::Dependent)),
        "a field naming the one before it has no reading outside its constructor"
    );
}

#[test]
fn a_dependent_field_checks_at_the_value_of_the_field_it_names()
{
    // `Box { put : (a : Type, x : El a) }` at `put(⌜Integer⌝, _)`: the second
    // field checks at `Integer`.
    let mut arena = CoreArena::new();
    let kind = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let one = Level::zero().succ().expect("the successor of zero");
    let large = arena.value_type_universe(Sort::Ground(GroundSort::Value), one);
    let integer = arena.value_type_base(BaseType::Integer);
    let code = arena.value_quote(integer);
    let near = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let element = arena.value_type_element(near, Level::zero());
    let boxed = ConstantIndex::from(0_usize);
    let boxes = Arc::new(DataSignature::new(vec![], vec![vec![kind, element]], large));
    let datatype = arena.value_type_data(boxed, vec![]);
    let put = arena.value_constructor(datatype, ConstructorTag::from(0_usize), vec![code, code]);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    context.adopt_data(boxed, boxes).expect("the box forms");
    assert_eq!(
        field_at(
            &mut context,
            (datatype, put),
            kind,
            FieldPosition::from(0_usize)
        ),
        Ok(kind),
        "the first field checks at the universe"
    );
    assert_eq!(
        field_at(
            &mut context,
            (datatype, put),
            element,
            FieldPosition::from(1_usize)
        ),
        Ok(integer),
        "the second checks at the decode of the code the first gives"
    );
}
