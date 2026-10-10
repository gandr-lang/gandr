//! Closed programs in the currently represented positive fragment.

use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::Zone;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Side;
use gandr_kernel_term::Sign;
use gandr_runtime_compile_host::image::Literal as ImageLiteral;

/// Construct a signed core literal.
///
/// # Specification
/// trivial.
pub fn integer(
    core: &mut CoreArena,
    value: ImageLiteral,
) -> ValueId
{
    let value = i64::from(value);
    let magnitude =
        Magnitude::from_decimal_text(value.unsigned_abs().to_string()).expect("integer digits");
    let sign = if value < 0 {
        Sign::Negative
    }
    else {
        Sign::NonNegative
    };
    core.value_literal(Literal::Integer(IntegerLiteral::new(sign, magnitude)))
}
/// A program and the pinned independent value grammar it denotes.
pub struct Program
{
    /// Arena holding the computation.
    pub core: CoreArena,
    /// Closed computation.
    pub root: ComputationId,
    /// Canonical expected answer.
    pub answer: String,
}
/// The five non-grade positive-core examples.
///
/// # Specification
/// trivial.
pub fn named() -> Vec<Program>
{
    let mut core = CoreArena::new();
    let five = integer(&mut core, 5_i64.into());
    let root = core.computation_return(five);
    let cut = Program {
        core,
        root,
        answer: String::from("(int 5)"),
    };
    let mut core = CoreArena::new();
    let seven = integer(&mut core, 7_i64.into());
    let bound = core.computation_return(seven);
    let variable = core.value_variable(Zone::Intuitionistic, 0_u32.into());
    let body = core.computation_return(variable);
    let root = core.computation_bind(bound, body);
    let bind = Program {
        core,
        root,
        answer: String::from("(int 7)"),
    };
    let mut core = CoreArena::new();
    let three = integer(&mut core, 3_i64.into());
    let scrutinee = core.value_injection(Side::Left, three);
    let variable = core.value_variable(Zone::Intuitionistic, 0_u32.into());
    let arm = core.computation_return(variable);
    let root = core.computation_case(scrutinee, arm, arm);
    let case = Program {
        core,
        root,
        answer: String::from("(int 3)"),
    };
    let mut core = CoreArena::new();
    let one = integer(&mut core, 1_i64.into());
    let two = integer(&mut core, 2_i64.into());
    let pair = core.value_pair(one, two);
    let root = core.computation_return(pair);
    let ctor = Program {
        core,
        root,
        answer: String::from("(pair (int 1) (int 2))"),
    };
    let mut core = CoreArena::new();
    let eight = integer(&mut core, 8_i64.into());
    let injection = core.value_injection(Side::Right, eight);
    let bound = core.computation_return(injection);
    let variable = core.value_variable(Zone::Intuitionistic, 0_u32.into());
    let arm = core.computation_return(variable);
    let body = core.computation_case(variable, arm, arm);
    let root = core.computation_bind(bound, body);
    let compound = Program {
        core,
        root,
        answer: String::from("(int 8)"),
    };
    vec![cut, bind, case, ctor, compound]
}
