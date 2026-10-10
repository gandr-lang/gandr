//! Typed admission preserves the owning stage's evidence.

use gandr_core_checker::CheckBudget;
use gandr_core_checker::CheckRefusal;
use gandr_core_checker::CheckingContext;
use gandr_core_checker::form_comp_type;
use gandr_core_term::CoreArena;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::Literal;
use gandr_kernel_term::StringLiteral;
use gandr_runtime_compile_host::BridgeError;
use gandr_runtime_compile_host::Form;
use gandr_runtime_compile_host::LowerError;
use gandr_runtime_compile_host::TypedVerdict;
use gandr_runtime_compile_host::check_and_lower;
use gandr_runtime_compile_host::is_typed;

#[test]
fn typed_refusals_preserve_stage_and_payload()
{
    let mut core = CoreArena::new();
    let text = core.value_literal(Literal::Text(StringLiteral::new(String::from("outside"))));
    let root = core.computation_return(text);
    let string = core.value_type_base(BaseType::String);
    let integer = core.value_type_base(BaseType::Integer);
    let string = core.comp_type_returner(string);
    let integer = core.comp_type_returner(integer);
    let mut context = CheckingContext::new(&mut core, CheckBudget::DEFAULT);
    let string = form_comp_type(&mut context, string).expect("type");
    let integer = form_comp_type(&mut context, integer).expect("type");
    assert_eq!(
        check_and_lower(&mut context, root, string),
        Err(BridgeError::NotLowered(LowerError::OutsideSlice(
            Form::String
        )))
    );
    assert!(matches!(
        check_and_lower(&mut context, root, integer),
        Err(BridgeError::NotChecked(CheckRefusal::TypeMismatch(_)))
    ));
}
#[test]
fn the_typed_verdict_reports_what_the_checker_would_say()
{
    let mut core = CoreArena::new();
    let value = crate::programs::integer(&mut core, 5_i64.into());
    let root = core.computation_return(value);
    let integer = core.value_type_base(BaseType::Integer);
    let string = core.value_type_base(BaseType::String);
    let integer = core.comp_type_returner(integer);
    let string = core.comp_type_returner(string);
    let mut context = CheckingContext::new(&mut core, CheckBudget::DEFAULT);
    let integer = form_comp_type(&mut context, integer).expect("type");
    let string = form_comp_type(&mut context, string).expect("type");
    assert_eq!(
        is_typed(&mut context, root, integer),
        TypedVerdict::Admitted
    );
    assert!(matches!(
        is_typed(&mut context, root, string),
        TypedVerdict::Refused(BridgeError::NotChecked(CheckRefusal::TypeMismatch(_)))
    ));
}
