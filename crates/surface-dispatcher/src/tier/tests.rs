use gandr_core_checker::CodeDefinitions;
use gandr_core_checker::tier::ClosedTier as _;
use gandr_core_checker::tier::Meeting;
use gandr_core_term::CoreArena;
use gandr_core_term::Zone;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::Side;

use super::Emitted;

#[test]
fn the_emitter_meets_a_pair_computing_one_value_2282()
{
    // def id = thunk { \x. return x } ; def spin = thunk { \x. force spin x } ;
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let truth = core.value_injection(Side::Left.into(), unit);
    let falsity = core.value_injection(Side::Right.into(), unit);
    let bound = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let returned = core.computation_return(bound);
    let lambda = core.computation_lambda(returned);
    let identity = core.value_thunk(lambda);
    let spin = core.value_constant(ConstantIndex::from(1_usize));
    let forced = core.computation_force(spin);
    let again = core.computation_application(forced, bound);
    let lambda = core.computation_lambda(again);
    let spinning = core.value_thunk(lambda);
    let mut definitions = CodeDefinitions::new();
    definitions.define(ConstantIndex::from(0_usize), identity);
    definitions.define(ConstantIndex::from(1_usize), spinning);
    let called = |core: &mut gandr_core_term::CoreArena, constant: usize| {
        let head = core.value_constant(ConstantIndex::from(constant));
        let forced = core.computation_force(head);
        let applied = core.computation_application(forced, truth);
        core.value_returned(applied)
    };
    let identity_of_truth = called(&mut core, 0);
    let spun = called(&mut core, 1);
    let mut tier = Emitted::default();
    assert_eq!(
        tier.meet(&core, &definitions, (identity_of_truth, truth)),
        Meeting::Met,
        "`id true` runs to `true`"
    );
    assert_eq!(
        tier.meet(&core, &definitions, (identity_of_truth, falsity)),
        Meeting::Unmet,
        "`id true` runs to `true`, not `false`"
    );
    assert_eq!(
        tier.meet(&core, &definitions, (spun, truth)),
        Meeting::Unmet,
        "`spin true` runs past the tier's fuel"
    );
}

#[test]
fn a_pair_stepping_a_native_operation_is_the_machine_s_2282()
{
    // def sum = thunk { add(2, 3) } ;
    let mut core = CoreArena::new();
    let integer = |digits: &str| {
        let magnitude = gandr_kernel_term::Magnitude::from_decimal_text(digits.into())
            .expect("the digits are decimal");
        gandr_kernel_term::Literal::Integer(gandr_kernel_term::IntegerLiteral::new(
            gandr_kernel_term::Sign::NonNegative,
            magnitude,
        ))
    };
    let add = gandr_core_term::primitive::PRELUDE
        .iter()
        .copied()
        .find(|primitive| primitive.name().as_ref() == "add")
        .expect("native add");
    let two = core.value_literal(integer("2"));
    let three = core.value_literal(integer("3"));
    let five = core.value_literal(integer("5"));
    let added = core.computation_primitive(
        add,
        gandr_core_term::primitive::Arguments::Binary([two, three]),
    );
    let sum = core.value_thunk(added);
    let mut definitions = CodeDefinitions::new();
    definitions.define(ConstantIndex::from(0_usize), sum);
    let stepped = core.value_returned(added);
    let head = core.value_constant(ConstantIndex::from(0_usize));
    let forced = core.computation_force(head);
    let called = core.value_returned(forced);
    let mut tier = Emitted::default();
    assert_eq!(
        tier.meet(&core, &definitions, (stepped, five)),
        Meeting::Unmet,
        "`add(2, 3)` steps the native addition the kernel reads as a constant"
    );
    assert_eq!(
        tier.meet(&core, &definitions, (called, five)),
        Meeting::Unmet,
        "`force sum` reaches a definition stepping the native addition"
    );
}
