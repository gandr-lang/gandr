use anodized::spec;
use gandr_core_nbe::DomainArena;
use gandr_core_nbe::Fuel;
use gandr_core_nbe::ReadbackMode;
use gandr_core_nbe::eval_computation;
use gandr_core_nbe::readback_computation;
use gandr_core_term::BinderDepth;
use gandr_core_term::Computation;
use gandr_core_term::CoreArena;
use gandr_core_term::Sort;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::Zone;
use gandr_kernel_conversion_trace::ConversionDecision;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GroundSort;
use quenchant_shape::shape::Maybe;

use super::CodeDefinitions;
use super::CoreNode;
use super::TermNode;
use super::TypeNode;
use super::Unfolded;
use super::loose_reach;
use super::unfolding;

/// The two atoms `reduct`, a quote of a product, pairs.
///
/// # Specification
/// - requires: `reduct` quotes a product whose two children resolve.
/// - ensures: the two stored children are returned in product order.
/// - panics: the recipe did not produce such a quote.
///
/// # Adequacy
/// - hypothesis: L3 — a two-argument static operator receives distinct type
///   codes, and its quoted product is asserted in argument order; this
///   separates swapped substitution and wrong quoted children.
/// - witness: `code::tests::a_static_step_reduces_saturated_instances_and_redexes_only`
#[spec(ensures: |ret| matches!(arena.value(reduct), Some(Value::Quote(quoted))
        if arena.value_type(*quoted).is_some_and(|held| matches!(*held, ValueType::Product(ref parts)
            if matches!(**parts, [first, second] if arena.value_type(first) == Some(&ret.0) && arena.value_type(second) == Some(&ret.1))))))]
fn quoted_pair(
    arena: &CoreArena,
    reduct: ValueId,
) -> (ValueType, ValueType)
{
    let Some(&Value::Quote(quoted)) = arena.value(reduct)
    else {
        panic!("the reduct is a quote: {:?}", arena.value(reduct));
    };
    let Some(held) = arena.value_type(quoted)
    else {
        panic!("the quote holds a product");
    };
    let ValueType::Product(ref parts) = *held
    else {
        panic!("the quote holds a product");
    };
    let [first, second] = **parts
    else {
        panic!("the quoted product is binary");
    };
    (
        arena.value_type(first).cloned().unwrap(),
        arena.value_type(second).cloned().unwrap(),
    )
}

#[test]
fn a_static_step_reduces_saturated_instances_and_redexes_only()
{
    // def Num : Type = Integer ;
    // def Both : Type -> Type -> Type = \A. \B. El A * El B ;
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let string = arena.value_type_base(BaseType::String);
    let num_body = arena.value_quote(integer);
    let integer_code = arena.value_quote(integer);
    let string_code = arena.value_quote(string);
    let outer = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let inner = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let first = arena.value_type_element(outer, Level::zero());
    let second = arena.value_type_element(inner, Level::zero());
    let product = arena.value_type_product(&[first, second]);
    let quoted = arena.value_quote(product);
    let inner_lambda = arena.value_static_lambda(quoted);
    let both_body = arena.value_static_lambda(inner_lambda);
    let mut definitions = CodeDefinitions::new();
    definitions.define(ConstantIndex::from(0_usize), num_body);
    definitions.define(ConstantIndex::from(1_usize), both_body);
    let num = arena.value_constant(ConstantIndex::from(0_usize));
    let both = arena.value_constant(ConstantIndex::from(1_usize));
    let partial = arena.value_static_application(both, integer_code);
    let saturated = arena.value_static_application(partial, string_code);
    let further = arena.value_static_application(saturated, integer_code);
    let num_applied = arena.value_static_application(num, string_code);
    let redex = arena.value_static_application(inner_lambda, string_code);
    let short = arena.value_static_application(both_body, integer_code);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let rigid = arena.value_static_application(bound, integer_code);
    let unknown = arena.value_constant(ConstantIndex::from(5_usize));

    let step = |arena: &mut CoreArena, code: ValueId| match definitions.reduce(arena, code).unwrap()
    {
        Maybe::Present(step) => {
            assert_eq!(step.redex(), code, "a step fires at the code itself");
            Maybe::Present((step.unfolded(), step.reduct()))
        },
        Maybe::Absent(reason) => Maybe::Absent(reason),
    };
    let defined = |position: usize| Unfolded::Definition(ConstantIndex::from(position));

    assert_eq!(
        step(&mut arena, num),
        Maybe::Present((defined(0), num_body)),
        "a constant with a body unfolds to that body"
    );
    let Maybe::Present((unfolded, reduct)) = step(&mut arena, saturated)
    else {
        panic!("a saturated instance reduces");
    };
    assert_eq!(unfolded, defined(1), "the instance unfolds its definition");
    assert_eq!(
        quoted_pair(&arena, reduct),
        (
            ValueType::Base(BaseType::Integer),
            ValueType::Base(BaseType::String)
        ),
        "the arguments instantiate the parameters outermost first, decoded on mint"
    );
    let Maybe::Present((unfolded, reduct)) = step(&mut arena, further)
    else {
        panic!("an instance under a further argument reduces");
    };
    let Some(&Value::StaticApplication(applied, argument)) = arena.value(reduct)
    else {
        panic!("the reduct stays applied to the argument the operator does not take");
    };
    assert_eq!(
        (unfolded, argument, quoted_pair(&arena, applied).1),
        (defined(1), integer_code, ValueType::Base(BaseType::String)),
        "the operator consumes its two parameters and re-applies the third argument"
    );
    let Maybe::Present((unfolded, reduct)) = step(&mut arena, num_applied)
    else {
        panic!("a nullary definition under an argument reduces");
    };
    assert_eq!(
        (unfolded, arena.value(reduct).cloned()),
        (
            defined(0),
            Some(Value::StaticApplication(num_body, string_code))
        ),
        "a body of no parameters stands under every argument"
    );
    let Maybe::Present((unfolded, reduct)) = step(&mut arena, redex)
    else {
        panic!("a saturated static redex reduces");
    };
    assert_eq!(
        (unfolded, quoted_pair(&arena, reduct).1),
        (
            Unfolded::Abstraction(inner_lambda),
            ValueType::Base(BaseType::String)
        ),
        "a static redex unfolds the abstraction at its head"
    );
    for code in [partial, short, rigid, unknown] {
        assert_eq!(
            step(&mut arena, code),
            Maybe::Absent(unfolding::Absent::Rigid),
            "an operator short of its arguments, a variable head and a constant without a \
                 body are rigid"
        );
    }
}

#[test]
fn a_closed_returned_code_runs_to_the_quote_it_returns()
{
    // def pick : U (Integer + Unit -> F Type) =
    //     thunk λ. case x { _ => return ⌜Integer⌝ ; _ => return ⌜Unit⌝ } ;
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let unit_type = arena.value_type_unit();
    let integer_code = arena.value_quote(integer);
    let unit_code = arena.value_quote(unit_type);
    let to_integer = arena.computation_return(integer_code);
    let to_unit = arena.computation_return(unit_code);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let case = arena.computation_case(bound, &[to_integer, to_unit]);
    let pick = arena.computation_lambda(case);
    let pick = arena.value_thunk(pick);
    let mut definitions = CodeDefinitions::new();
    definitions.define(ConstantIndex::from(0_usize), pick);
    let call = |arena: &mut CoreArena, argument: ValueId| {
        let head = arena.value_constant(ConstantIndex::from(0_usize));
        let forced = arena.computation_force(head);
        let applied = arena.computation_application(forced, argument);
        arena.value_returned(applied)
    };
    let zero = arena.value_literal(crate::fixture::integer_literal());
    let unit = arena.value_unit();
    let first = arena.value_injection(gandr_core_term::Summand::from(0_usize), zero);
    let second = arena.value_injection(gandr_core_term::Summand::from(1_usize), unit);
    let to_first = call(&mut arena, first);
    let to_second = call(&mut arena, second);
    let open = call(&mut arena, bound);
    for (code, quoted) in [(to_first, integer), (to_second, unit_type)] {
        let Maybe::Present(step) = definitions.reduce(&mut arena, code).unwrap()
        else {
            panic!("a closed call runs");
        };
        assert_eq!(step.unfolded(), Unfolded::Returned(code));
        assert!(
            matches!(arena.value(step.reduct()), Some(&Value::Quote(held))
                    if arena.value_type(held) == arena.value_type(quoted)),
            "the call runs to the quote its branch returns: {:?}",
            arena.value(step.reduct())
        );
        let certificate = definitions.certify(&arena, step).unwrap();
        assert!(
            certificate
                .decisions()
                .iter()
                .any(|decision| matches!(decision, ConversionDecision::Unfold { .. })),
            "the run's δ-step is a recorded unfolding: {:?}",
            certificate.decisions()
        );
    }
    assert_eq!(
        definitions.reduce(&mut arena, open).unwrap(),
        Maybe::Absent(unfolding::Absent::Rigid),
        "a call waiting on a binder is rigid"
    );
}

/// A model type's family field read at a binder, `tm(g)` under the `Σ` that
/// binds `tm`, decodes `↑((force tm) g)`: a run stuck on a binder. Each weak
/// head of such a decode asked the machine to run it, minting the claim it
/// read back, so a record converted against a model type of the same shape
/// ran the machine once per field it compared (#1369).
#[test]
fn a_call_of_a_binder_is_rigid_without_running_1369()
{
    let mut arena = CoreArena::new();
    let definitions = CodeDefinitions::new();
    let family = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let index = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let forced = arena.computation_force(family);
    let applied = arena.computation_application(forced, index);
    let called = arena.value_returned(applied);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let returning = arena.computation_return(bound);
    let sequenced = arena.computation_bind(applied, returning);
    let after_a_bind = arena.value_returned(sequenced);
    for code in [called, after_a_bind] {
        let before = arena.watermark();
        assert_eq!(
            definitions.reduce(&mut arena, code).unwrap(),
            Maybe::Absent(unfolding::Absent::Rigid),
            "a run whose head forces a binder is rigid"
        );
        assert_eq!(
            arena.watermark(),
            before,
            "the rigid answer is read off the run's head, no claim minted to run it"
        );
    }
}

#[test]
fn the_loose_reach_counts_only_binders_outside_the_root()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let unit = arena.value_type_unit();
    let closed = arena.value_quote(integer);
    let zero = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let one = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let two = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(2_u32));
    let linear = arena.value_variable(Zone::Linear, DeBruijnIndex::from(4_u32));
    let bound_inside = arena.value_static_lambda(zero);
    let reaching_out = arena.value_static_lambda(two);
    let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let decoded = arena.value_type_element(one, Level::zero());
    let returns = arena.comp_type_returner(decoded);
    let dependent = arena.comp_type_pi(small, returns);
    let under_pi = arena.value_quote_computation(dependent);
    let decoded_domain = arena.value_type_element(zero, Level::zero());
    let returns_unit = arena.comp_type_returner(unit);
    let in_domain = arena.comp_type_pi(decoded_domain, returns_unit);
    let domain_quote = arena.value_quote_computation(in_domain);
    let path_at_variable = arena.value_type_path(decoded, zero, zero);
    let value = |at| CoreNode::Term(TermNode::Value(at));
    let rows = [
        (value(closed), 0_usize, "a closed code reaches nothing"),
        (
            value(two),
            3_usize,
            "a bare variable reaches one past its index",
        ),
        (value(linear), 0_usize, "a linear variable counts no binder"),
        (
            value(bound_inside),
            0_usize,
            "a variable its own lambda binds reaches nothing",
        ),
        (
            value(reaching_out),
            2_usize,
            "a lambda's binder is subtracted from its body's reach",
        ),
        (
            value(under_pi),
            1_usize,
            "a dependent codomain's binder is subtracted",
        ),
        (
            value(domain_quote),
            1_usize,
            "a dependent domain sits outside the binder",
        ),
        (
            CoreNode::Type(TypeNode::Value(path_at_variable)),
            2_usize,
            "a type reaches through the decode at its carrier",
        ),
    ];
    for (root, reach, message) in rows {
        assert_eq!(
            loose_reach(&arena, root),
            Ok(BinderDepth::from(reach)),
            "{message}"
        );
    }
}

#[test]
fn definitions_reject_reordering_without_replacing_earlier_bodies()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let string = arena.value_type_base(BaseType::String);
    let original = arena.value_quote(integer);
    let replacement = arena.value_quote(string);
    let first = ConstantIndex::from(2_usize);
    let earlier = ConstantIndex::from(1_usize);
    let later = ConstantIndex::from(4_usize);
    let reference = arena.value_constant(first);
    let mut definitions = CodeDefinitions::new();
    definitions.define(first, original);
    definitions.define(first, replacement);
    definitions.define(earlier, replacement);
    definitions.define(later, replacement);
    assert_eq!(definitions.body(first), Maybe::Present(original));
    assert_eq!(
        definitions.body(earlier),
        Maybe::Absent(unfolding::Absent::Rigid)
    );
    assert_eq!(definitions.body(later), Maybe::Present(replacement));
    let Maybe::Present(step) = definitions.reduce(&mut arena, reference).unwrap()
    else {
        panic!("the retained definition still unfolds");
    };
    assert_eq!(step.reduct(), original);
    let certificate = definitions.certify(&arena, step).unwrap();
    assert_eq!(certificate.reduct(), original);
    assert_eq!(
        certificate.verdict(),
        gandr_core_nbe::MachineVerdict::Convertible
    );
}

#[test]
fn the_normaliser_unfolds_each_recorded_definition()
{
    let mut arena = CoreArena::new();
    let zero = arena.value_literal(crate::fixture::integer_literal());
    let defined = ConstantIndex::from(0_usize);
    let rigid = ConstantIndex::from(1_usize);
    let mut definitions = CodeDefinitions::new();
    definitions.define(defined, zero);
    // `return c`, evaluated and read back by the table's normaliser.
    let normal = |arena: &mut CoreArena, constant| {
        let reference = arena.value_constant(constant);
        let returned = arena.computation_return(reference);
        let mut domain = DomainArena::new();
        let fuel = Fuel::from(1_000_u32);
        let head = eval_computation(arena, &mut domain, definitions.normaliser(), fuel, returned)
            .expect("a returned constant evaluates");
        let read = readback_computation(
            arena,
            &mut domain,
            definitions.normaliser(),
            ReadbackMode::Unfolding,
            fuel,
            head,
        )
        .expect("a returned constant reads back");
        match arena.computation(read) {
            Some(&Computation::Return(answer)) => arena.value(answer).cloned(),
            other => panic!("a returned constant reads back as a return: {other:?}"),
        }
    };
    let body = arena.value(zero).cloned();
    assert_eq!(
        normal(&mut arena, defined),
        body,
        "a constant with a body unfolds to it"
    );
    assert_eq!(
        normal(&mut arena, rigid),
        Some(Value::Constant(rigid)),
        "a constant with no body stays as written"
    );
}
