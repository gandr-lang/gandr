//! Positive image topology, binder scope, and refusal witnesses.

use gandr_core_term::CoreArena;
use gandr_core_term::Zone;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Side;
use gandr_kernel_term::Sign;
use gandr_kernel_term::StringLiteral;
use gandr_runtime_compile_host::BridgeError;
use gandr_runtime_compile_host::Form;
use gandr_runtime_compile_host::LowerError;
use gandr_runtime_compile_host::check_and_lower;
use gandr_runtime_compile_host::image::CtorTag;
use gandr_runtime_compile_host::image::ImageError;
use gandr_runtime_compile_host::image::MAX_IMAGE_NODES;
use gandr_runtime_compile_host::image::NodeKind;
use gandr_runtime_compile_host::lower_computation;

use crate::programs::integer;

#[test]
fn supported_programs_have_one_terminal_cut_and_backward_operands()
{
    for program in crate::programs::named() {
        let image = lower_computation(&program.core, program.root).expect("positive program");
        assert_eq!(image.nodes().last().expect("root").kind, NodeKind::Cut);
        assert_eq!(
            image
                .nodes()
                .iter()
                .filter(|node| node.kind == NodeKind::Cut)
                .count(),
            1
        );
        for (position, node) in image.nodes().iter().enumerate() {
            for &operand in &node.operands {
                assert!(usize::try_from(u32::from(operand)).expect("small index") < position);
            }
        }
    }
}
#[test]
fn a_variable_lowers_to_its_distance_from_the_innermost_binder()
{
    let mut core = CoreArena::new();
    let one = integer(&mut core, 1_i64.into());
    let two = integer(&mut core, 2_i64.into());
    let outer = core.computation_return(one);
    let inner = core.computation_return(two);
    let variable = core.value_variable(Zone::Intuitionistic, 1_u32.into());
    let body = core.computation_return(variable);
    let inner = core.computation_bind(inner, body);
    let root = core.computation_bind(outer, inner);
    let image = lower_computation(&core, root).expect("scoped program");
    let indices: Vec<_> = image
        .nodes()
        .iter()
        .filter(|node| node.kind == NodeKind::Var)
        .map(|node| u32::from(node.binder))
        .collect();
    assert_eq!(indices, vec![1]);
}
#[test]
fn each_dispatch_arm_binds_its_own_payload()
{
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let scrutinee = core.value_injection(Side::Left, unit);
    let variable = core.value_variable(Zone::Intuitionistic, 0_u32.into());
    let arm = core.computation_return(variable);
    let root = core.computation_case(scrutinee, arm, arm);
    let image = lower_computation(&core, root).expect("case");
    let indices: Vec<_> = image
        .nodes()
        .iter()
        .filter(|node| node.kind == NodeKind::Var)
        .map(|node| u32::from(node.binder))
        .collect();
    assert_eq!(indices, vec![0, 0]);
    let after = core.computation_return(variable);
    let root = core.computation_bind(root, after);
    assert!(lower_computation(&core, root).is_ok());
}
#[test]
fn a_pair_lowers_to_its_tag_with_two_fields()
{
    let mut core = CoreArena::new();
    let one = integer(&mut core, 1_i64.into());
    let two = integer(&mut core, 2_i64.into());
    let pair = core.value_pair(one, two);
    let root = core.computation_return(pair);
    let image = lower_computation(&core, root).expect("pair");
    let pair = image.nodes().get(2).expect("pair node");
    assert_eq!(pair.kind, NodeKind::Ctor);
    assert_eq!(pair.tag, CtorTag::Pair);
    assert_eq!(
        pair.operands
            .iter()
            .copied()
            .map(u32::from)
            .collect::<Vec<_>>(),
        vec![0, 1]
    );
    assert_eq!(
        image
            .nodes()
            .iter()
            .take(2)
            .map(|node| i64::from(node.literal))
            .collect::<Vec<_>>(),
        vec![1, 2]
    );
}
#[test]
fn supported_excluded_core_forms_are_refused_by_name()
{
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let ret = core.computation_return(unit);
    let lambda = core.computation_lambda(ret);
    let app = core.computation_application(ret, unit);
    let force = core.computation_force(unit);
    let text = core.value_literal(Literal::Text(StringLiteral::new(String::from("text"))));
    let text = core.computation_return(text);
    for (root, form) in [
        (lambda, Form::Lambda),
        (app, Form::Application),
        (force, Form::Force),
        (text, Form::String),
    ] {
        assert_eq!(
            lower_computation(&core, root),
            Err(LowerError::OutsideSlice(form))
        );
    }
    let thunk = core.value_thunk(ret);
    let constant = core.value_constant(0_usize.into());
    let ty = core.value_type_unit();
    let quote = core.value_quote(ty);
    let comp_ty = core.comp_type_returner(ty);
    let quote_comp = core.value_quote_computation(comp_ty);
    let static_lambda = core.value_static_lambda(unit);
    let static_app = core.value_static_application(static_lambda, unit);
    for (value, form) in [
        (thunk, Form::Thunk),
        (constant, Form::Constant),
        (quote, Form::Quote),
        (quote_comp, Form::QuoteComputation),
        (static_lambda, Form::StaticLambda),
        (static_app, Form::StaticApplication),
    ] {
        let root = core.computation_return(value);
        assert_eq!(
            lower_computation(&core, root),
            Err(LowerError::OutsideSlice(form))
        );
    }
}
#[test]
fn a_free_variable_is_refused_rather_than_lowered()
{
    let mut core = CoreArena::new();
    for zone in [Zone::Intuitionistic, Zone::Linear] {
        let index = 0_u32.into();
        let value = core.value_variable(zone, index);
        let root = core.computation_return(value);
        assert_eq!(
            lower_computation(&core, root),
            Err(LowerError::UnboundVariable { zone, index })
        );
    }
}
#[test]
fn a_computation_the_checker_refuses_never_reaches_the_lowering()
{
    use gandr_core_checker::CheckBudget;
    use gandr_core_checker::CheckingContext;
    use gandr_core_checker::form_comp_type;
    let mut core = CoreArena::new();
    let three = integer(&mut core, 3_i64.into());
    let arm = core.computation_return(three);
    let root = core.computation_case(three, arm, arm);
    assert!(lower_computation(&core, root).is_ok());
    let integer = core.value_type_base(BaseType::Integer);
    let expected = core.comp_type_returner(integer);
    let mut context = CheckingContext::new(&mut core, CheckBudget::DEFAULT);
    let expected = form_comp_type(&mut context, expected).expect("formed type");
    let refused = check_and_lower(&mut context, root, expected);
    assert!(matches!(
        refused,
        Err(BridgeError::NotChecked(
            gandr_core_checker::CheckRefusal::ShapeMismatch { .. }
        ))
    ));
}
#[test]
fn integer_payloads_cover_both_signed_extremes()
{
    for value in [i64::MIN, -1, 0, 1, i64::MAX] {
        let mut core = CoreArena::new();
        let value_id = integer(&mut core, value.into());
        let root = core.computation_return(value_id);
        let image = lower_computation(&core, root).expect("wire integer");
        assert_eq!(
            i64::from(image.nodes().first().expect("literal").literal),
            value
        );
    }
    for (sign, digits) in [
        (Sign::NonNegative, "9223372036854775808"),
        (Sign::Negative, "9223372036854775809"),
        (Sign::NonNegative, "18446744073709551616"),
    ] {
        let mut core = CoreArena::new();
        let magnitude = Magnitude::from_decimal_text(String::from(digits)).expect("digits");
        let value = core.value_literal(Literal::Integer(IntegerLiteral::new(sign, magnitude)));
        let root = core.computation_return(value);
        assert_eq!(
            lower_computation(&core, root),
            Err(LowerError::IntegerOutOfRange)
        );
    }
}
#[test]
fn dangling_roots_and_deep_programs_fail_without_recursion()
{
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let mut root = core.computation_return(unit);
    let empty = CoreArena::new();
    assert_eq!(
        lower_computation(&empty, root),
        Err(LowerError::DanglingComputation(root))
    );
    for _ in 0 .. MAX_IMAGE_NODES {
        root = core.computation_bind(root, root);
    }
    assert_eq!(
        lower_computation(&core, root),
        Err(LowerError::ImageRefused(ImageError::TooManyNodes))
    );
}
