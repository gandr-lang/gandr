use gandr_core_term::Computation;
use gandr_core_term::CoreArena;
use gandr_surface_syntax::SourceText;

use crate::error::LoweringRefusal;
use crate::lower::native::tests::lowered;
use crate::module::DeclarationOutcome;
use crate::resolve::SurfaceName;

/// The theory both tests open a model of.
const SEEDED: &str = "\
theory Seeded where {
  sort T : Type;
  oper read : (t : T) --> Integer;
  oper seed : T;
}
";

#[test]
fn a_model_opens_as_a_bind_over_the_rest_of_its_block_4788()
{
    // The opening binds what the ascribed return of `p` returns, so the
    // checker reads `s` as a variable of `p`'s model type, never as `p`.
    let source = alloc::format!(
        "{SEEDED}def opened(p : Model(Seeded)) -> Integer {{ module s = p; let r = s.read; r s.seed }}"
    );
    let mut arena = CoreArena::new();
    let module = lowered(SourceText::from(source.as_str()), &mut arena);
    let outcome = module
        .declarations()
        .iter()
        .next_back()
        .expect("the opening declares")
        .outcome();
    let DeclarationOutcome::Completed { body, .. } = outcome
    else {
        panic!("the opening lowers: {outcome:?}");
    };
    let Some(&gandr_core_term::Value::Thunk(mut at)) = arena.value(body)
    else {
        panic!("the body is a thunk: {:?}", arena.value(body));
    };
    let first = loop {
        match arena.computation(at) {
            Some(&Computation::Lambda(inner)) => at = inner,
            Some(&Computation::Bind(first, _)) => break first,
            other => panic!("the body opens with a bind: {other:?}"),
        }
    };
    let Some(&Computation::Ascribe { body: returned, .. }) = arena.computation(first)
    else {
        panic!(
            "the opening binds an ascribed return: {:?}",
            arena.computation(first)
        );
    };
    assert!(
        matches!(arena.computation(returned), Some(&Computation::Return(_))),
        "the ascription holds the return of the opened model: {:?}",
        arena.computation(returned)
    );
}

#[test]
fn a_value_at_no_model_type_is_refused_4788()
{
    // An integer parameter and a name nothing declares open no model.
    for (written, opened) in [
        ("def f(n : Integer) -> Integer { module s = n; n }", "n"),
        ("def g() -> Integer { module s = 7; 7 }", "7"),
    ] {
        let source = alloc::format!("{SEEDED}{written}");
        let mut arena = CoreArena::new();
        let module = lowered(SourceText::from(source.as_str()), &mut arena);
        let outcome = module
            .declarations()
            .iter()
            .next_back()
            .expect("the statement's declaration declares")
            .outcome();
        let DeclarationOutcome::Refused(LoweringRefusal::NotAModel { name, .. }) = outcome
        else {
            panic!("`{written}` is refused as no model: {outcome:?}");
        };
        assert_eq!(
            name,
            SurfaceName::from(opened),
            "the refusal names the operand"
        );
    }
}
