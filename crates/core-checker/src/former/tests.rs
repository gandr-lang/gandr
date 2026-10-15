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
