//! A located declaration judged, then refused by name on readmission through
//! the bridge.

use alloc::vec::Vec;

use gandr_core_checker_base::CheckBudget;
use gandr_core_checker_base::CheckingContext;
use gandr_core_checker_base::Declaration;
use gandr_core_checker_base::OriginToken;
use gandr_core_checker_base::check_module;
use gandr_core_checker_base::fixture::worlds::At;
use gandr_core_checker_base::fixture::worlds::SEAT;
use gandr_core_checker_base::fixture::worlds::Spelled;
use gandr_core_checker_base::fixture::worlds::computation;
use gandr_core_checker_base::fixture::worlds::entry_point;
use gandr_core_checker_base::fixture::worlds::migrate;
use gandr_core_checker_base::fixture::worlds::operating;
use gandr_core_checker_base::fixture::worlds::text;
use gandr_core_checker_base::fixture::worlds::worlds;
use gandr_core_checker_bridge::bridge;
use gandr_core_term::CoreArena;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use quenchant_shape::shape::Maybe;

#[test]
fn readmission_refuses_a_located_declaration_by_name()
{
    let mut arena = CoreArena::new();
    let string = arena.value_type_base(BaseType::String);
    let report = text(&mut arena, Spelled("report"));
    let returned = arena.computation_return(report);
    let migration = migrate(&mut arena, SEAT, returned);
    let [operator, seat] = worlds();
    let module = [
        operator,
        seat,
        entry_point(&mut arena, At(2), string, migration).entered(operating()),
        Declaration::new(
            ConstantIndex::from(3_usize),
            Maybe::Present(string),
            Maybe::Present(report),
            OriginToken::from(3_usize),
        ),
    ];
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let report = check_module(&mut context, &module);
    let readmission = bridge::readmit(&mut arena, &report);
    let outcomes: Vec<_> = readmission
        .readmitted()
        .iter()
        .map(bridge::Readmitted::outcome)
        .collect();
    assert!(
        matches!(
            outcomes[..],
            [
                &bridge::Outcome::Static,
                &bridge::Outcome::Static,
                &bridge::Outcome::Refused(bridge::Refusal::Located { at }),
                &bridge::Outcome::Defined { .. },
            ] if at == computation(migration)
        ),
        "the worlds stay on the checker's side, the located declaration is refused at its migration, and the rest is readmitted: {outcomes:?}"
    );
}
