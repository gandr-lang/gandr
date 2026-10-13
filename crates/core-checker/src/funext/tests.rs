use alloc::vec::Vec;

use gandr_core_term::CertificateEquality;
use gandr_core_term::CoreArena;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::equal_certificate_syntax;
use gandr_kernel_conversion_trace::ConversionDecision;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use quenchant_shape::shape::Maybe;

use crate::context::CheckBudget;
use crate::context::CheckingContext;
use crate::declaration::Declaration;
use crate::declaration::OriginToken;
use crate::declaration::body;
use crate::fixture::Booleans;
use crate::fixture::booleans;
use crate::module::Judged;
use crate::module::ModuleReport;
use crate::module::Verdict;
use crate::module::check_module;
use crate::refusal::CheckRefusal;

/// A declaration position in a fixture module.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct At(usize);

/// The declaration at `position`, its origin the position itself.
///
/// # Specification
/// trivial.
fn declaration(
    At(position): At,
    declared: ValueTypeId,
    defined: Maybe<ValueId, body::Absent>,
) -> Declaration
{
    Declaration::new(
        ConstantIndex::from(position),
        Maybe::Present(declared),
        defined,
        OriginToken::from(position),
    )
}

/// The three boolean functions at positions zero to two, then `extra`.
///
/// # Specification
/// trivial.
fn judged(
    arena: &mut CoreArena,
    functions: &Booleans,
    extra: &[Declaration],
) -> ModuleReport
{
    let mut module = Vec::from([
        declaration(At(0), functions.function, Maybe::Present(functions.not)),
        declaration(At(1), functions.function, Maybe::Present(functions.not_not)),
        declaration(At(2), functions.function, Maybe::Present(functions.same)),
    ]);
    module.extend_from_slice(extra);
    let mut context = CheckingContext::new(arena, CheckBudget::DEFAULT);
    check_module(&mut context, &module)
}

/// `funext(c_left, c_right) : Path(function, c_left, c_right)` at
/// `position`, with its `funext` node.
///
/// # Specification
/// trivial.
fn extensionality(
    arena: &mut CoreArena,
    functions: &Booleans,
    position: At,
    (At(left), At(right)): (At, At),
) -> (Declaration, ValueId)
{
    let left = arena.value_constant(ConstantIndex::from(left));
    let right = arena.value_constant(ConstantIndex::from(right));
    let path = arena.value_type_path(functions.function, left, right);
    let funext = arena.value_funext(left, right);
    (declaration(position, path, Maybe::Present(funext)), funext)
}

#[test]
fn pointwise_equal_functions_relate_by_computation()
{
    let mut arena = CoreArena::new();
    let functions = booleans(&mut arena);
    let (twice, at) = extensionality(&mut arena, &functions, At(3), (At(1), At(2)));
    let report = judged(&mut arena, &functions, &[twice]);
    assert!(
        report
            .judged()
            .iter()
            .all(|judged| matches!(judged.verdict(), Verdict::Checked { .. })),
        "not ∘ not = id is decided by computation: {report:?}"
    );
    let Some(funext) = report.funexts().get(&at)
    else {
        panic!("the decision is recorded at the funext node");
    };
    assert_eq!(report.funexts().len(), 1);
    let returned: Vec<(ValueId, ValueId)> = funext
        .components()
        .iter()
        .map(|component| (component.left().returned(), component.right().returned()))
        .collect();
    assert_eq!(returned.len(), 2, "one component per injection of the sum");
    for (summand, &(left, right)) in returned.iter().enumerate() {
        assert_eq!(
            equal_certificate_syntax(&arena, left, right),
            CertificateEquality::Equal,
            "both functions return one value"
        );
        assert!(
            matches!(arena.value(left), Some(&Value::Injection(found, _)) if usize::from(found) == summand),
            "the coverage runs in the kernel's order and each input returns itself"
        );
    }
    let Some(first) = funext.components().first()
    else {
        panic!("two components");
    };
    let unfolded = |decisions: &[ConversionDecision<_>]| {
        decisions
            .iter()
            .filter(|decision| matches!(decision, ConversionDecision::Unfold { .. }))
            .count()
    };
    assert_eq!(
        (
            unfolded(first.left().decisions()),
            unfolded(first.right().decisions())
        ),
        (3, 1),
        "the trace unfolds negation twice inside its double, and the identity once"
    );
}

#[test]
fn what_the_rule_cannot_show_it_refuses_by_name()
{
    let mut arena = CoreArena::new();
    let functions = booleans(&mut arena);

    // Negation differs from the identity at both inputs.
    let (once, at) = extensionality(&mut arena, &functions, At(3), (At(0), At(2)));
    let report = judged(&mut arena, &functions, &[once]);
    assert_eq!(
        report.judged().get(3).map(Judged::verdict),
        Some(Verdict::Refused(CheckRefusal::PointwiseDistinct { at }))
    );
    assert!(
        report.funexts().is_empty(),
        "a refused funext records nothing"
    );

    // An axiom's application does not return: the rule shows nothing.
    let mut arena = CoreArena::new();
    let functions = booleans(&mut arena);
    let axiom = declaration(At(3), functions.function, Maybe::Absent(body::Absent::Hole));
    let (opaque, at) = extensionality(&mut arena, &functions, At(4), (At(3), At(3)));
    let report = judged(&mut arena, &functions, &[axiom, opaque]);
    assert_eq!(
        report.judged().get(4).map(Judged::verdict),
        Some(Verdict::Refused(CheckRefusal::PointwiseDistinct { at }))
    );

    // A function-typed domain is outside the coverage the rule decides.
    let mut arena = CoreArena::new();
    let functions = booleans(&mut arena);
    let returns = arena.comp_type_returner(functions.ty);
    let arrow = arena.comp_type_arrow(functions.function, returns);
    let higher = arena.value_type_thunk(arrow);
    let unit = arena.value_unit();
    let truth = arena.value_injection(0_usize.into(), unit);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let forced = arena.computation_force(bound);
    let applied = arena.computation_application(forced, truth);
    let lambda = arena.computation_lambda(applied);
    let at_truth = arena.value_thunk(lambda);
    let applying = declaration(At(3), higher, Maybe::Present(at_truth));
    let applier = arena.value_constant(ConstantIndex::from(3_usize));
    let path = arena.value_type_path(higher, applier, applier);
    let funext = arena.value_funext(applier, applier);
    let report = judged(&mut arena, &functions, &[
        applying,
        declaration(At(4), path, Maybe::Present(funext)),
    ]);
    assert_eq!(
        report.judged().get(4).map(Judged::verdict),
        Some(Verdict::Refused(CheckRefusal::FunextUnsupported {
            at: funext,
            classifier: higher,
        }))
    );

    // Open functions: the rule decides closed ones only.
    let mut arena = CoreArena::new();
    let functions = booleans(&mut arena);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let path = arena.value_type_path(functions.function, bound, bound);
    let returns_path = arena.comp_type_returner(path);
    let pi = arena.comp_type_pi(functions.function, returns_path);
    let declared = arena.value_type_thunk(pi);
    let funext = arena.value_funext(bound, bound);
    let returned = arena.computation_return(funext);
    let lambda = arena.computation_lambda(returned);
    let open = arena.value_thunk(lambda);
    let report = judged(&mut arena, &functions, &[declaration(
        At(3),
        declared,
        Maybe::Present(open),
    )]);
    assert!(
        matches!(
            report.judged().get(3).map(Judged::verdict),
            Some(Verdict::Refused(CheckRefusal::FunextUnsupported { at, .. })) if at == funext
        ),
        "{report:?}"
    );
}
