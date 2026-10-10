//! Canonical rendering and the L machine's public readback.

use gandr_core_term::Computation;
use gandr_core_term::CoreArena;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Side;
use gandr_kernel_term::Sign;
use gandr_kernel_term::StringLiteral;
use gandr_runtime_compile_host::render::RenderError;
use gandr_runtime_compile_host::render::canonical;

use crate::programs::integer;

#[test]
fn supported_programs_render_the_l_machines_pinned_answers()
{
    use gandr_core_sequent::CommandArena;
    use gandr_core_sequent::Definitions;
    use gandr_core_sequent::Machine;
    use gandr_core_sequent::Outcome;
    use gandr_core_sequent::Provenance;
    use gandr_core_sequent::StepCount;
    use gandr_core_sequent::focus_computation;
    for program in crate::programs::named() {
        let mut commands = CommandArena::new();
        let mut provenance = Provenance::new();
        let root = focus_computation(&program.core, program.root, &mut commands, &mut provenance)
            .expect("focus");
        let definitions = Definitions::new();
        let mut machine = Machine::new(&commands, &definitions);
        let Outcome::Halted(value) = machine.run(root, StepCount::from(1000_usize)).expect("run")
        else {
            panic!("closed program halts");
        };
        let mut read = CoreArena::new();
        let returned = machine.read_back(value, &mut read).expect("readback");
        let Some(&Computation::Return(value)) = read.computation(returned)
        else {
            panic!("positive result");
        };
        assert_eq!(
            canonical(&read, value).expect("canonical").as_ref(),
            program.answer
        );
    }
}
#[test]
fn a_nested_value_renders_in_source_order()
{
    let mut core = CoreArena::new();
    let one = integer(&mut core, 1_i64.into());
    let two = integer(&mut core, 2_i64.into());
    let unit = core.value_unit();
    let right = core.value_pair(two, unit);
    let left = core.value_injection(Side::Left, one);
    let root = core.value_pair(left, right);
    assert_eq!(
        canonical(&core, root).expect("nested").as_ref(),
        "(pair (inl (int 1)) (pair (int 2) (unit)))"
    );
    let right = core.value_injection(Side::Right, one);
    assert_eq!(
        canonical(&core, right).expect("right").as_ref(),
        "(inr (int 1))"
    );
}
#[test]
fn a_value_outside_the_slice_has_no_spelling()
{
    let mut core = CoreArena::new();
    let text = core.value_literal(Literal::Text(StringLiteral::new(String::from("text"))));
    assert_eq!(canonical(&core, text), Err(RenderError::OutsideSlice));
    let unit = core.value_unit();
    let nested = core.value_pair(unit, text);
    assert_eq!(canonical(&core, nested), Err(RenderError::OutsideSlice));
}
#[test]
fn literal_bounds_and_dangling_values_preserve_refusals()
{
    let mut core = CoreArena::new();
    for (value, expected) in [
        (i64::MIN, "(int -9223372036854775808)"),
        (i64::MAX, "(int 9223372036854775807)"),
    ] {
        let value = integer(&mut core, value.into());
        assert_eq!(
            canonical(&core, value).expect("endpoint").as_ref(),
            expected
        );
    }
    let magnitude =
        Magnitude::from_decimal_text(String::from("9223372036854775808")).expect("digits");
    let value = core.value_literal(Literal::Integer(IntegerLiteral::new(
        Sign::NonNegative,
        magnitude,
    )));
    assert_eq!(canonical(&core, value), Err(RenderError::IntegerOutOfRange));
    assert_eq!(
        canonical(&CoreArena::new(), value),
        Err(RenderError::DanglingValue(value))
    );
}
