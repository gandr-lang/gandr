use alloc::vec::Vec;

use gandr_core_term::CertificateEquality;
use gandr_core_term::ComputationId;
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

use super::Step;
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

/// One of the two booleans.
#[derive(Clone, Copy, Debug)]
enum Truth
{
    /// The left injection.
    True,
    /// The right injection.
    False,
}

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

/// `funext(c_left, c_right) : Path(classifier, c_left, c_right)` at
/// `position`, with its `funext` node.
///
/// # Specification
/// trivial.
fn extensionality(
    arena: &mut CoreArena,
    classifier: ValueTypeId,
    position: At,
    (At(left), At(right)): (At, At),
) -> (Declaration, ValueId)
{
    let left = arena.value_constant(ConstantIndex::from(left));
    let right = arena.value_constant(ConstantIndex::from(right));
    let path = arena.value_type_path(classifier, left, right);
    let funext = arena.value_funext(left, right);
    (declaration(position, path, Maybe::Present(funext)), funext)
}

/// `U (domain → F +{(), ()})`.
///
/// # Specification
/// trivial.
fn into_booleans(
    arena: &mut CoreArena,
    functions: &Booleans,
    domain: ValueTypeId,
) -> ValueTypeId
{
    let returns = arena.comp_type_returner(functions.ty);
    let arrow = arena.comp_type_arrow(domain, returns);
    arena.value_type_thunk(arrow)
}

/// The boolean `truth`.
///
/// # Specification
/// trivial.
fn boolean(
    arena: &mut CoreArena,
    truth: Truth,
) -> ValueId
{
    let summand = match truth {
        Truth::True => 0_usize,
        Truth::False => 1_usize,
    };
    let unit = arena.value_unit();
    arena.value_injection(summand.into(), unit)
}

/// The intuitionistic variable at `index`.
///
/// # Specification
/// trivial.
fn variable(
    arena: &mut CoreArena,
    index: DeBruijnIndex,
) -> ValueId
{
    arena.value_variable(Zone::Intuitionistic, index)
}

/// `force h a`, `h` the variable at `function`.
///
/// # Specification
/// trivial.
fn applied(
    arena: &mut CoreArena,
    function: DeBruijnIndex,
    input: ValueId,
) -> ComputationId
{
    let function = variable(arena, function);
    let forced = arena.computation_force(function);
    arena.computation_application(forced, input)
}

/// `thunk (λh. body)`.
///
/// # Specification
/// trivial.
fn closed(
    arena: &mut CoreArena,
    body: ComputationId,
) -> ValueId
{
    let lambda = arena.computation_lambda(body);
    arena.value_thunk(lambda)
}

/// `thunk (λh. x ← force h true; rest)`, `rest` under `h` and `x`.
///
/// # Specification
/// trivial.
fn at_truth_then(
    arena: &mut CoreArena,
    rest: ComputationId,
) -> ValueId
{
    let truth = boolean(arena, Truth::True);
    let first = applied(arena, DeBruijnIndex::from(0_u32), truth);
    let bound = arena.computation_bind(first, rest);
    closed(arena, bound)
}

/// The kind of one recorded step.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Kind
{
    /// Both sides return.
    Return,
    /// Both sides apply the functions the premise at this index relates.
    Apply(DeBruijnIndex),
}

/// The kinds of the steps the decision recorded at `at`, in order.
///
/// # Specification
/// trivial.
fn kinds(
    report: &ModuleReport,
    at: ValueId,
) -> Vec<Kind>
{
    let Some(funext) = report.funexts().get(&at)
    else {
        panic!("the decision is recorded at the funext node: {report:?}");
    };
    funext
        .steps()
        .iter()
        .map(|step| match *step {
            Step::Return { .. } => Kind::Return,
            Step::Apply { fibre, .. } => Kind::Apply(fibre),
        })
        .collect()
}

#[test]
fn pointwise_equal_functions_relate_by_computation()
{
    let mut arena = CoreArena::new();
    let functions = booleans(&mut arena);
    let (twice, at) = extensionality(&mut arena, functions.function, At(3), (At(1), At(2)));
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
        .steps()
        .iter()
        .filter_map(|step| match *step {
            Step::Return {
                ref left,
                ref right,
            } => Some((left.returned(), right.returned())),
            Step::Apply { .. } => None,
        })
        .collect();
    assert_eq!(
        (returned.len(), funext.steps().len()),
        (2, 2),
        "one return per injection of the sum, and no application"
    );
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
    let Some(first) = funext.steps().first()
    else {
        panic!("two returns");
    };
    let Step::Return {
        ref left,
        ref right,
    } = *first
    else {
        panic!("the first step returns");
    };
    let unfolded = |decisions: &[ConversionDecision<_>]| {
        decisions
            .iter()
            .filter(|decision| matches!(decision, ConversionDecision::Unfold { .. }))
            .count()
    };
    assert_eq!(
        (unfolded(left.decisions()), unfolded(right.decisions())),
        (3, 1),
        "the trace unfolds negation twice inside its double, and the identity once"
    );
}

#[test]
fn a_higher_order_argument_is_decided_under_the_quantifier()
{
    // def at_truth : U ((Bool -> F Bool) -> F Bool) = λh. h(true) ;
    // def bound = λh. x ← h(true); return x ;
    // def twice = λh. x ← h(true); h(x) ;
    // def twice_bound = λh. x ← h(true); y ← h(x); return y ;
    let mut arena = CoreArena::new();
    let functions = booleans(&mut arena);
    let higher = into_booleans(&mut arena, &functions, functions.function);
    let truth = boolean(&mut arena, Truth::True);
    let tail = applied(&mut arena, DeBruijnIndex::from(0_u32), truth);
    let at_truth = closed(&mut arena, tail);
    let output = variable(&mut arena, DeBruijnIndex::from(0_u32));
    let returned = arena.computation_return(output);
    let bound = at_truth_then(&mut arena, returned);
    let again = applied(&mut arena, DeBruijnIndex::from(1_u32), output);
    let twice = at_truth_then(&mut arena, again);
    let again_bound = arena.computation_bind(again, returned);
    let twice_bound = at_truth_then(&mut arena, again_bound);
    let (reflexive, reflexive_at) = extensionality(&mut arena, higher, At(7), (At(3), At(3)));
    let (eta, eta_at) = extensionality(&mut arena, higher, At(8), (At(3), At(4)));
    let (nested, nested_at) = extensionality(&mut arena, higher, At(9), (At(5), At(6)));
    let report = judged(&mut arena, &functions, &[
        declaration(At(3), higher, Maybe::Present(at_truth)),
        declaration(At(4), higher, Maybe::Present(bound)),
        declaration(At(5), higher, Maybe::Present(twice)),
        declaration(At(6), higher, Maybe::Present(twice_bound)),
        reflexive,
        eta,
        nested,
    ]);
    assert!(
        report
            .judged()
            .iter()
            .all(|judged| matches!(judged.verdict(), Verdict::Checked { .. })),
        "a function argument is bound generically and its applications split: {report:?}"
    );
    let apply = Kind::Apply(DeBruijnIndex::from(0_u32));
    let back = Kind::Return;
    let once = Vec::from([apply, back, back]);
    assert_eq!(
        (kinds(&report, reflexive_at), kinds(&report, eta_at)),
        (once.clone(), once),
        "one application at the premise, then a return per boolean it may give"
    );
    assert_eq!(
        kinds(&report, nested_at),
        Vec::from([apply, apply, back, back, apply, back, back]),
        "the second application nests under each output of the first, in pre-order"
    );
    let Some(funext) = report.funexts().get(&reflexive_at)
    else {
        panic!("recorded");
    };
    let Some(first) = funext.steps().first()
    else {
        panic!("steps recorded");
    };
    let Step::Apply {
        ref left,
        ref right,
        ..
    } = *first
    else {
        panic!("the first step applies the argument");
    };
    assert!(
        [left, right].iter().all(|side| side
            .decisions()
            .iter()
            .any(|decision| matches!(decision, ConversionDecision::Unfold { .. }))),
        "each stuck side carries the trace unfolding its definition"
    );
    assert!(
        matches!(arena.value(left.normal()), Some(&Value::Thunk(_)))
            && equal_certificate_syntax(&arena, left.normal(), right.normal())
                != CertificateEquality::Equal,
        "the two normal forms apply the left and the right function"
    );
    let returned: Vec<ValueId> = funext
        .steps()
        .iter()
        .filter_map(|step| match *step {
            Step::Return { ref left, .. } => Some(left.returned()),
            Step::Apply { .. } => None,
        })
        .collect();
    assert!(
        returned
            .iter()
            .enumerate()
            .all(|(summand, &value)| matches!(
                arena.value(value),
                Some(&Value::Injection(found, _)) if usize::from(found) == summand
            )),
        "each branch returns the output it continues at"
    );
}

#[test]
fn what_the_rule_cannot_show_it_refuses_by_name()
{
    let mut arena = CoreArena::new();
    let functions = booleans(&mut arena);

    // Negation differs from the identity at both inputs.
    let (once, at) = extensionality(&mut arena, functions.function, At(3), (At(0), At(2)));
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
    let (opaque, at) = extensionality(&mut arena, functions.function, At(4), (At(3), At(3)));
    let report = judged(&mut arena, &functions, &[axiom, opaque]);
    assert_eq!(
        report.judged().get(4).map(Judged::verdict),
        Some(Verdict::Refused(CheckRefusal::PointwiseDistinct { at }))
    );

    // Applying the argument at different inputs, or applying it on one side
    // and returning on the other, is a difference the coverage shows.
    let mut arena = CoreArena::new();
    let functions = booleans(&mut arena);
    let higher = into_booleans(&mut arena, &functions, functions.function);
    let [at_truth, at_falsity] = [Truth::True, Truth::False].map(|truth| {
        let input = boolean(&mut arena, truth);
        let tail = applied(&mut arena, DeBruijnIndex::from(0_u32), input);
        closed(&mut arena, tail)
    });
    let truth = boolean(&mut arena, Truth::True);
    let constant = arena.computation_return(truth);
    let constant = closed(&mut arena, constant);
    let (inputs, inputs_at) = extensionality(&mut arena, higher, At(6), (At(3), At(4)));
    let (shapes, shapes_at) = extensionality(&mut arena, higher, At(7), (At(3), At(5)));
    let report = judged(&mut arena, &functions, &[
        declaration(At(3), higher, Maybe::Present(at_truth)),
        declaration(At(4), higher, Maybe::Present(at_falsity)),
        declaration(At(5), higher, Maybe::Present(constant)),
        inputs,
        shapes,
    ]);
    assert_eq!(
        [6, 7].map(|position| report.judged().get(position).map(Judged::verdict)),
        [
            Some(Verdict::Refused(CheckRefusal::PointwiseDistinct {
                at: inputs_at
            })),
            Some(Verdict::Refused(CheckRefusal::PointwiseDistinct {
                at: shapes_at
            })),
        ]
    );

    // A function argument whose own domain is a function would need function
    // identity between the inputs it is applied at.
    let mut arena = CoreArena::new();
    let functions = booleans(&mut arena);
    let higher = into_booleans(&mut arena, &functions, functions.function);
    let nested = into_booleans(&mut arena, &functions, higher);
    let truth = boolean(&mut arena, Truth::True);
    let constant = arena.computation_return(truth);
    let constant = closed(&mut arena, constant);
    let (relation, at) = extensionality(&mut arena, nested, At(4), (At(3), At(3)));
    let report = judged(&mut arena, &functions, &[
        declaration(At(3), nested, Maybe::Present(constant)),
        relation,
    ]);
    assert_eq!(
        report.judged().get(4).map(Judged::verdict),
        Some(Verdict::Refused(CheckRefusal::FunextUnsupported {
            at,
            classifier: nested,
        }))
    );

    // Open functions: the rule decides closed ones only.
    let mut arena = CoreArena::new();
    let functions = booleans(&mut arena);
    let bound = variable(&mut arena, DeBruijnIndex::from(0_u32));
    let path = arena.value_type_path(functions.function, bound, bound);
    let returns_path = arena.comp_type_returner(path);
    let pi = arena.comp_type_pi(functions.function, returns_path);
    let declared = arena.value_type_thunk(pi);
    let funext = arena.value_funext(bound, bound);
    let returned = arena.computation_return(funext);
    let open = closed(&mut arena, returned);
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
