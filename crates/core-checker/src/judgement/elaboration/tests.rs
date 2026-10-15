use alloc::vec::Vec;

use gandr_core_nbe::Definitions;
use gandr_core_nbe::DomainArena;
use gandr_core_nbe::DomainValue;
use gandr_core_nbe::Fuel;
use gandr_core_nbe::LoweredChain;
use gandr_core_nbe::NeutralHead;
use gandr_core_nbe::eval_value;
use gandr_core_term::CompType;
use gandr_core_term::Computation;
use gandr_core_term::CoreArena;
use gandr_core_term::DefinitionalEnvironment;
use gandr_core_term::FailureClass;
use gandr_core_term::Value;
use gandr_core_term::ValueType;
use gandr_core_term::Zone;
use gandr_core_term::hole::HoleId;
use gandr_core_term::hole::MarkIndex;
use gandr_core_term::hole::TermId;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use proptest::collection::vec;
use proptest::prelude::*;
use quenchant_shape::shape::Maybe;

use super::MarkEntry;
use super::Typing;
use super::elaborate_comp;
use super::elaborate_value;
use super::type_value;
use crate::CheckBudget;
use crate::CheckingContext;
use crate::Declaration;
use crate::OriginToken;
use crate::Verdict;
use crate::check_module;
use crate::fixture::integer_literal;
use crate::fixture::seed;
use crate::fixture::term_recipe;
use crate::fixture::type_recipe;
use crate::formation::form_comp_type;
use crate::formation::form_value_type;
use crate::judgement::Direction;
use crate::judgement::check_comp;
use crate::judgement::check_value;
use crate::judgement::synthesise_comp;
use crate::judgement::synthesise_value;
use crate::refusal::CheckRefusal;
use crate::refusal::TermNode;
use crate::refusal::TypeNode;
use crate::signature;

#[test]
fn a_total_run_marks_where_a_strict_run_refuses()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let product = arena.value_type_product(&[integer, integer]);
    let zero = arena.value_literal(integer_literal());
    let unit = arena.value_unit();
    let pair = arena.value_tuple(&[zero, unit]);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let expected = form_value_type(&mut context, product).unwrap();

    let strict = check_value(&mut context, pair, expected).unwrap_err();
    let elaboration = elaborate_value(&mut context, pair, Direction::Check(expected)).unwrap();
    assert_eq!(
        elaboration.marks(),
        [MarkEntry {
            at: TermId::Value(unit),
            refusal: strict,
        }],
        "the unit is marked with the strict refusal, and the run goes on"
    );
    assert_eq!(
        elaboration.produced(),
        expected,
        "a check produces its expected type"
    );
    let Some(&[first, second]) = context
        .arena()
        .value(elaboration.root())
        .and_then(Value::components)
    else {
        panic!("the elaborated root is still the pair");
    };
    assert_eq!(first, zero, "the well-typed component is untouched");
    assert_eq!(
        context.arena().value(second),
        Some(&Value::Mark {
            mark: MarkIndex::from(0_u32),
            body: unit,
        }),
        "the mismatched component is wrapped in the first mark"
    );
    assert!(
        check_value(&mut context, elaboration.root(), expected).is_ok(),
        "the marked term is well typed"
    );
}

#[test]
fn a_typed_run_keeps_the_type_of_every_term_it_judged()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let product = arena.value_type_product(&[integer, integer]);
    let zero = arena.value_literal(integer_literal());
    let unit = arena.value_unit();
    let pair = arena.value_tuple(&[zero, unit]);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let returned = arena.computation_return(bound);
    let lambda = arena.computation_lambda(returned);
    let identity = arena.value_thunk(lambda);
    let returns_integer = arena.comp_type_returner(integer);
    let arrow = arena.comp_type_arrow(integer, returns_integer);
    let thunk_arrow = arena.value_type_thunk(arrow);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let expected = form_value_type(&mut context, product).unwrap();
    let formed_arrow = form_value_type(&mut context, thunk_arrow).unwrap();
    let depth = context.depth(Zone::Intuitionistic);

    let synthesised = type_value(&mut context, zero, Direction::Synthesise);
    let &[only] = synthesised.typings()
    else {
        panic!("a literal is one judgement: {synthesised:?}");
    };
    assert_eq!(only.term, TermNode::Value(zero), "the literal is kept");
    assert!(
        matches!(only.ty, TypeNode::Value(found)
                if context.arena().value_type(found) == Some(&ValueType::Base(BaseType::Integer))),
        "a synthesis keeps the type it produced"
    );
    assert!(
        synthesised.marks().is_empty(),
        "an accepted run marks nothing"
    );

    let checked = type_value(&mut context, pair, Direction::Check(expected));
    assert_eq!(
        checked.typings().last(),
        Some(&Typing {
            term: TermNode::Value(pair),
            ty: TypeNode::Value(expected.id()),
        }),
        "the pair finishes last, at the type it was checked against"
    );
    let typed = |term| {
        checked
            .typings()
            .iter()
            .filter(|typing| typing.term == TermNode::Value(term))
            .map(|typing| typing.ty)
            .collect::<Vec<_>>()
    };
    let [TypeNode::Value(found), TypeNode::Value(factor)] = typed(unit)[..]
    else {
        panic!("the mismatched component is kept as synthesised, then as checked: {checked:?}");
    };
    assert_eq!(
        context.arena().value_type(found),
        Some(&ValueType::unit()),
        "the inner synthesis keeps the type the component has"
    );
    assert_eq!(
        context.arena().value_type(factor),
        Some(&ValueType::Base(BaseType::Integer)),
        "the check keeps the factor it was recovered at"
    );
    assert!(!typed(zero).is_empty(), "the well-typed component is kept");
    assert_eq!(
        checked
            .marks()
            .iter()
            .map(super::MarkEntry::at)
            .collect::<Vec<_>>(),
        [TermId::Value(unit)],
        "the typed run marks what the total run marks"
    );

    let read = type_value(&mut context, identity, Direction::Check(formed_arrow));
    assert!(
            read.typings().iter().any(|typing| typing.term == TermNode::Value(bound)
                && matches!(typing.ty, TypeNode::Value(found)
                    if context.arena().value_type(found) == Some(&ValueType::Base(BaseType::Integer)))),
            "the variable under the lambda is kept at its binder's type: {read:?}"
        );
    assert!(
        read.typings()
            .iter()
            .any(|typing| typing.term == TermNode::Computation(lambda)
                && typing.ty == TypeNode::Computation(arrow)),
        "the lambda is kept at the arrow it was checked against: {read:?}"
    );
    assert_eq!(
        context.depth(Zone::Intuitionistic),
        depth,
        "the typed run leaves the binders as found"
    );
}

#[test]
fn a_marked_bound_leaves_its_continuation_judged()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let zero = arena.value_literal(integer_literal());
    let forced = arena.computation_force(zero);
    let returned = arena.computation_return(zero);
    let bind = arena.computation_bind(forced, returned);
    let thunk = arena.value_thunk(bind);
    let returns_integer = arena.comp_type_returner(integer);
    let suspended = arena.value_type_thunk(returns_integer);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let expected = form_value_type(&mut context, suspended).unwrap();
    let depth = context.depth(Zone::Intuitionistic);

    let read = type_value(&mut context, thunk, Direction::Check(expected));
    assert!(
        read.marks()
            .iter()
            .all(|mark| mark.refusal != CheckRefusal::MachineInvariant),
        "the bound's mark is no fault of the bind: {read:?}"
    );
    assert!(
        read.typings()
            .iter()
            .any(|typing| typing.term == TermNode::Computation(returned)),
        "the continuation past the marked bound is judged and kept: {read:?}"
    );
    assert_eq!(
        context.depth(Zone::Intuitionistic),
        depth,
        "the typed run leaves the binders as found"
    );
}

#[test]
fn a_term_that_cannot_synthesise_is_checked_against_the_unknown_type()
{
    let mut arena = CoreArena::new();
    let zero = arena.value_literal(integer_literal());
    let forced = arena.computation_force(zero);
    let lambda = arena.computation_lambda(forced);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);

    let strict = synthesise_comp(&mut context, lambda).unwrap_err();
    let elaboration = elaborate_comp(&mut context, lambda, Direction::Synthesise).unwrap();
    assert_eq!(
        context.arena().comp_type(elaboration.produced().id()),
        Some(&CompType::Unknown),
        "a marked synthesis produces the unknown type"
    );
    let &[lambda_mark, force_mark] = elaboration.marks()
    else {
        panic!("the lambda and the force inside it are both marked");
    };
    assert_eq!(
        lambda_mark,
        MarkEntry {
            at: TermId::Computation(lambda),
            refusal: strict,
        },
        "the lambda is marked first, with the strict refusal"
    );
    assert_eq!(
        force_mark.at(),
        TermId::Computation(forced),
        "the body is judged against the unknown arrow and its force is marked"
    );
    assert!(
        matches!(force_mark.refusal(), CheckRefusal::ShapeMismatch { .. }),
        "a force of an integer is a shape mismatch"
    );
    let Some(&Computation::Mark { mark, body }) = context.arena().computation(elaboration.root())
    else {
        panic!("the root is marked");
    };
    assert_eq!(mark, MarkIndex::from(0_u32));
    let Some(&Computation::Lambda(inner)) = context.arena().computation(body)
    else {
        panic!("the mark wraps the lambda");
    };
    assert_eq!(
        context.arena().computation(inner),
        Some(&Computation::Mark {
            mark: MarkIndex::from(1_u32),
            body: forced,
        }),
        "the force inside is wrapped in the second mark"
    );
    assert!(
        synthesise_comp(&mut context, elaboration.root()).is_ok(),
        "the marked term synthesises"
    );
}

#[test]
fn an_unfilled_hole_elaborates_to_a_type_and_evaluates_indeterminate()
{
    let mut arena = CoreArena::new();
    let hole = HoleId::from(0_u32);
    let standing = arena.value_hole(hole);
    let zero = arena.value_literal(integer_literal());
    let program = arena.value_tuple(&[standing, zero]);
    let declarations = [Declaration::new(
        ConstantIndex::from(0_usize),
        Maybe::Absent(signature::Absent::Unsigned),
        Maybe::Present(program),
        OriginToken::from(0_usize),
    )];
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);

    let report = check_module(&mut context, &declarations);
    let [ref judged] = *report.judged()
    else {
        panic!("one verdict per declaration");
    };
    let Verdict::Synthesised { synthesised, .. } = judged.verdict()
    else {
        panic!("a program with an unfilled hole gets a type");
    };
    let Some(held) = context.arena().value_type(synthesised.produced().id())
    else {
        panic!("the pair synthesises a product");
    };
    let ValueType::Product(ref parts) = *held
    else {
        panic!("the pair synthesises a product");
    };
    let [first, second] = **parts
    else {
        panic!("the pair's product is binary");
    };
    assert_eq!(
        context.arena().value_type(first),
        Some(&ValueType::Unknown),
        "the hole's component is the unknown type"
    );
    assert_eq!(
        context.arena().value_type(second),
        Some(&ValueType::Base(BaseType::Integer)),
        "the literal's component is known"
    );
    let elaboration = elaborate_value(&mut context, program, Direction::Synthesise).unwrap();
    assert!(
        elaboration.marks().is_empty(),
        "an unfilled hole is no error"
    );

    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut domain = DomainArena::new();
    let evaluated = eval_value(
        context.arena(),
        &mut domain,
        definitions,
        Fuel::from(10_000_u32),
        program,
    )
    .unwrap();
    let Some(&[first, _]) = domain
        .value(evaluated)
        .and_then(|held| domain.components(held))
    else {
        panic!("the pair evaluates around the hole");
    };
    let Some(&DomainValue::Neutral { neutral, .. }) = domain.value(first)
    else {
        panic!("the hole's component is indeterminate");
    };
    assert!(
        matches!(
            domain.neutral(neutral).unwrap().head(),
            NeutralHead::Hole { hole: named, .. } if named == hole
        ),
        "the indeterminate result stands on the unfilled hole"
    );
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    #[test]
    fn the_strict_judgement_is_the_total_runs_oracle(
        recipe in term_recipe(),
        constants in vec(type_recipe(), 4),
        expected in type_recipe(),
    )
    {
        let mut arena = CoreArena::new();
        let terms = recipe.build(&mut arena);
        let constant_types: Vec<_> = constants.iter().map(|constant| constant.build(&mut arena)).collect();
        let (expected_value, expected_comp) = expected.build_both(&mut arena);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        seed(&mut context, &constant_types);
        let expected_value = form_value_type(&mut context, expected_value).unwrap();
        let expected_comp = form_comp_type(&mut context, expected_comp).unwrap();
        for &term in &terms.values {
            for direction in [Direction::Synthesise, Direction::Check(expected_value)] {
                let strict = match direction {
                    | Direction::Synthesise => synthesise_value(&mut context, term).map(|_| ()),
                    | Direction::Check(expected) => check_value(&mut context, term, expected).map(|_| ()),
                };
                let total = elaborate_value(&mut context, term, direction);
                match (strict, &total) {
                    | (Ok(()), &Ok(ref elaboration)) => prop_assert!(elaboration.marks().is_empty(), "an accepted term is not marked"),
                    | (Err(refusal), &Ok(ref elaboration)) => prop_assert_eq!(
                        elaboration.marks().first().map(MarkEntry::refusal),
                        Some(refusal),
                        "the first mark is the strict refusal"
                    ),
                    | (Ok(()), &Err(ref fault)) => prop_assert!(false, "an accepted term faults in a total run: {:?}", fault),
                    | (Err(_), &Err(ref fault)) => prop_assert_eq!(fault.classify(), FailureClass::EngineFault, "only an engine fault ends a total run"),
                }
                if let Ok(elaboration) = total {
                    let rechecked = check_value(&mut context, elaboration.root(), elaboration.produced());
                    prop_assert!(rechecked.is_ok(), "the marked term has the type the run produced: {:?}", rechecked);
                }
            }
        }
        for &term in &terms.comps {
            for direction in [Direction::Synthesise, Direction::Check(expected_comp)] {
                let strict = match direction {
                    | Direction::Synthesise => synthesise_comp(&mut context, term).map(|_| ()),
                    | Direction::Check(expected) => check_comp(&mut context, term, expected).map(|_| ()),
                };
                let total = elaborate_comp(&mut context, term, direction);
                match (strict, &total) {
                    | (Ok(()), &Ok(ref elaboration)) => prop_assert!(elaboration.marks().is_empty(), "an accepted term is not marked"),
                    | (Err(refusal), &Ok(ref elaboration)) => prop_assert_eq!(
                        elaboration.marks().first().map(MarkEntry::refusal),
                        Some(refusal),
                        "the first mark is the strict refusal"
                    ),
                    | (Ok(()), &Err(ref fault)) => prop_assert!(false, "an accepted term faults in a total run: {:?}", fault),
                    | (Err(_), &Err(ref fault)) => prop_assert_eq!(fault.classify(), FailureClass::EngineFault, "only an engine fault ends a total run"),
                }
                if let Ok(elaboration) = total {
                    let rechecked = check_comp(&mut context, elaboration.root(), elaboration.produced());
                    prop_assert!(rechecked.is_ok(), "the marked term has the type the run produced: {:?}", rechecked);
                }
            }
        }
    }
}
