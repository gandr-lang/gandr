//! Operation routes: which operations become declarations, and what the
//! checker makes of them.

use alloc::format;
use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;

use gandr_core_checker::CheckBudget;
use gandr_core_checker::CheckingContext;
use gandr_core_checker::Declaration;
use gandr_core_checker::ModuleReport;
use gandr_core_checker::OriginToken;
use gandr_core_checker::Verdict;
use gandr_core_checker::body;
use gandr_core_checker::check_module;
use gandr_core_checker::signature;
use gandr_core_term::CompType;
use gandr_core_term::Computation;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueType;
use gandr_core_term::Zone;
use gandr_kernel_term::DeBruijnIndex;
use gandr_surface_syntax::SourceText;
use quenchant_shape::shape::Maybe;

use crate::fixture::grammar;
use crate::fixture::parsed;
use crate::lower::LoweringBudget;
use crate::lower::lower_module;
use crate::module::DeclarationOutcome;
use crate::module::LoweredModule;
use crate::namespace::Recognition;

/// Division with remainder over unary naturals: a two-output operation over a
/// five-input helper, with the divisor carried twice so no rule copies it.
const NAT_DIV: &str = "data NatDiv : Type {
    Zero : NatDiv;
    Succ : (n : NatDiv) --> NatDiv;
    oper walk(m : NatDiv, g : NatDiv, d : NatDiv, q : NatDiv, r : NatDiv) -> (quot : NatDiv, rem : NatDiv);
    oper divmod(m : NatDiv, n : NatDiv) -> (quot : NatDiv, rem : NatDiv);
    rule walk(Zero, g, d, q, r) ==> (q, r);
    rule walk(Succ(m), Zero, d, q, r) ==> walk(m, d, d, Succ(q), Zero);
    rule walk(Succ(m), Succ(g), d, q, r) ==> walk(m, g, d, q, Succ(r));
    rule divmod(m, Zero) ==> (Zero, m);
    rule divmod(m, Succ(d)) ==> walk(m, d, d, Zero, Zero);
}
";

/// The module the parser and the lowering make of `source`.
///
/// # Specification
/// trivial.
fn lowered<'source>(
    source: impl Into<SourceText<'source>>,
    arena: &mut CoreArena,
) -> LoweredModule<'source>
{
    let pbg = grammar();
    let tree = parsed(&pbg, source.into());

    lower_module(
        &pbg,
        &tree,
        arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
    )
    .unwrap()
}

/// The checker's verdicts over every declaration `module` did not refuse.
///
/// # Specification
/// trivial.
fn judged(
    module: &LoweredModule<'_>,
    arena: &mut CoreArena,
) -> ModuleReport
{
    let declarations: Vec<Declaration> = module
        .declarations()
        .iter()
        .filter_map(|declaration| {
            let origin = OriginToken::from(usize::from(declaration.origin()));
            let (declared, defined) = match declaration.outcome() {
                | DeclarationOutcome::Completed {
                    declared_type,
                    body,
                } => (Maybe::Present(declared_type), Maybe::Present(body)),
                | DeclarationOutcome::Uncompleted { declared_type } => (
                    Maybe::Present(declared_type),
                    Maybe::Absent(body::Absent::Hole),
                ),
                | DeclarationOutcome::Bodied { body } => (
                    Maybe::Absent(signature::Absent::Unsigned),
                    Maybe::Present(body),
                ),
                | DeclarationOutcome::Data(index) => {
                    return match module.data(index) {
                        | Maybe::Present(held) => Some(Declaration::data(
                            declaration.constant(),
                            Arc::clone(held),
                            origin,
                        )),
                        | Maybe::Absent(_) => None,
                    };
                },
                | DeclarationOutcome::Refused(_) => return None,
            };
            Some(Declaration::new(
                declaration.constant(),
                declared,
                defined,
                origin,
            ))
        })
        .collect();

    check_module(
        &mut CheckingContext::new(arena, CheckBudget::DEFAULT),
        &declarations,
    )
}

/// Each declaration's name and role, in admission order.
///
/// # Specification
/// trivial.
fn rows(module: &LoweredModule<'_>) -> Vec<String>
{
    module
        .declarations()
        .iter()
        .map(|declaration| format!("{} {:?}", declaration.name().as_ref(), declaration.role()))
        .collect()
}

#[test]
fn a_many_out_operation_lowers_to_a_function_the_checker_accepts()
{
    let mut arena = CoreArena::new();
    let module = lowered(NAT_DIV, &mut arena);
    assert_eq!(rows(&module), [
        "NatDiv Declared",
        "walk Operation",
        "divmod Operation"
    ]);
    let Some(divmod) = module.declarations().last()
    else {
        panic!("divmod is declared");
    };
    let DeclarationOutcome::Completed { declared_type, .. } = divmod.outcome()
    else {
        panic!("divmod lowers to a type and a body: {:?}", divmod.outcome());
    };
    let Some(&ValueType::Thunk(function)) = arena.value_type(declared_type)
    else {
        panic!("an operation is a thunked function");
    };
    let Some(&CompType::Arrow {
        codomain: after_m, ..
    }) = arena.comp_type(function)
    else {
        panic!("over its first input");
    };
    let Some(&CompType::Arrow {
        codomain: after_n, ..
    }) = arena.comp_type(after_m)
    else {
        panic!("over its second input");
    };
    let Some(&CompType::Returner { result, .. }) = arena.comp_type(after_n)
    else {
        panic!("returning after its two inputs");
    };
    let Some(result) = arena.value_type(result)
    else {
        panic!("the result type is minted");
    };
    let ValueType::Product(ref components) = *result
    else {
        panic!("a two-output operation returns one tuple");
    };
    assert_eq!(components.len(), 2_usize, "one component per output port");

    let report = judged(&module, &mut arena);
    let verdicts: Vec<_> = report
        .judged()
        .iter()
        .map(gandr_core_checker::Judged::verdict)
        .collect();
    assert!(
        matches!(verdicts.as_slice(), [
            Verdict::Data,
            Verdict::Checked { .. },
            Verdict::Checked { .. }
        ]),
        "the family forms and both operations check: {verdicts:?}"
    );
}

#[test]
fn a_call_reaches_the_operation_before_a_builtin_of_its_name()
{
    let source = "data NatAdd : Type {
    Zero : NatAdd;
    Succ : (n : NatAdd) --> NatAdd;
    oper add(m : NatAdd, n : NatAdd) -> NatAdd;
    rule add(Zero, n) ==> n;
    rule add(Succ(m), n) ==> Succ(add(m, n));
}
def two : +U (-F NatAdd) ;
def two = thunk { become add(Succ(Zero), Succ(Zero)) } ;
";
    let mut arena = CoreArena::new();
    let module = lowered(source, &mut arena);
    assert_eq!(rows(&module), [
        "NatAdd Declared",
        "add Operation",
        "two Declared"
    ]);
    let report = judged(&module, &mut arena);
    let verdicts: Vec<_> = report
        .judged()
        .iter()
        .map(gandr_core_checker::Judged::verdict)
        .collect();
    assert!(
        matches!(verdicts.as_slice(), [
            Verdict::Data,
            Verdict::Checked { .. },
            Verdict::Checked { .. }
        ]),
        "`add` is the family's operation, not the integer builtin: {verdicts:?}"
    );
}

#[test]
fn a_leaf_delivers_its_results_in_port_order()
{
    let source = "data Flag : Type {
    Down : Flag;
    Up : Flag;
    oper swap(a : Flag, b : Flag) -> (x : Flag, y : Flag);
    rule swap(a, b) ==> (b, a);
}
";
    let mut arena = CoreArena::new();
    let module = lowered(source, &mut arena);
    assert_eq!(rows(&module), ["Flag Declared", "swap Operation"]);
    let Some(swap) = module.declarations().last()
    else {
        panic!("swap is declared");
    };
    let DeclarationOutcome::Completed { body, .. } = swap.outcome()
    else {
        panic!("swap lowers to a type and a body: {:?}", swap.outcome());
    };
    let Some(&Value::Thunk(fixpoint)) = arena.value(body)
    else {
        panic!("an operation is a thunk");
    };
    let Some(&Computation::Fixpoint { body: outer, .. }) = arena.computation(fixpoint)
    else {
        panic!("of one fixpoint");
    };
    let Some(&Computation::Lambda(inner)) = arena.computation(outer)
    else {
        panic!("over its first input");
    };
    let Some(&Computation::Lambda(leaf)) = arena.computation(inner)
    else {
        panic!("over its second input");
    };
    let Some(&Computation::Return(returned)) = arena.computation(leaf)
    else {
        panic!("a rule of variables only is the tree's one leaf");
    };
    let Some(returned) = arena.value(returned)
    else {
        panic!("the returned value is minted");
    };
    let Value::Tuple(ref components) = *returned
    else {
        panic!("two outputs return one tuple");
    };
    assert_eq!(
        components
            .iter()
            .map(|&component| arena.value(component).cloned())
            .collect::<Vec<_>>(),
        [0_u32, 1_u32].map(|index| Some(Value::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(index),
        })),
        "`b`, the innermost input, is the first result and `a` the second"
    );
}

#[test]
fn an_operation_whose_rules_miss_a_constructor_is_not_callable()
{
    let source = "data NatOp : Type {
    Zero : NatOp;
    One : NatOp;
    oper half(m : NatOp, n : NatOp) -> NatOp;
    rule half(Zero, n) ==> n;
}
";
    let mut arena = CoreArena::new();
    let module = lowered(source, &mut arena);
    assert_eq!(
        rows(&module),
        ["NatOp Declared"],
        "no rule matches `One`, so the operation runs nowhere"
    );
}

#[test]
fn an_operation_calling_a_later_one_is_not_callable()
{
    let source = "data Flag : Type {
    Down : Flag;
    Up : Flag;
    oper first(x : Flag) -> Flag;
    oper second(x : Flag) -> Flag;
    rule first(x) ==> second(x);
    rule second(x) ==> x;
}
";
    let mut arena = CoreArena::new();
    let module = lowered(source, &mut arena);
    assert_eq!(
        rows(&module),
        ["Flag Declared", "second Operation"],
        "an operation calls only itself and earlier operations"
    );
}
