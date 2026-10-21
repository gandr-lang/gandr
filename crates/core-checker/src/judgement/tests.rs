use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::BinderDepth;
use gandr_core_term::CertificateEquality;
use gandr_core_term::CompType;
use gandr_core_term::CompTypeId;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::FailureClass;
use gandr_core_term::Sort;
use gandr_core_term::Value;
use gandr_core_term::ValueId;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::hole::HoleId;
use gandr_core_term::hole::MarkIndex;
use gandr_kernel_strata::Level;
use gandr_kernel_strata::LevelConstant;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::Side;
use proptest::collection::vec;
use proptest::prelude::ProptestConfig;
use proptest::prelude::prop_assert;
use proptest::prelude::prop_assert_eq;
use proptest::prelude::proptest;
use quenchant_shape::shape::Maybe;

use super::Frame;
use super::Goal;
use super::Machine;
use super::Marking;
use super::Produced;
use super::Sessions;
use super::check_comp;
use super::check_value;
use super::check_value_with_failure;
use super::checked;
use super::synthesise_comp;
use super::synthesise_value;
use super::unadmitted_value;
use crate::context::Atom;
use crate::context::CheckBudget;
use crate::context::CheckingContext;
use crate::conversion::ConversionCount;
use crate::conversion::comp_bridge;
use crate::conversion::value_bridge;
use crate::failure::FrameRole;
use crate::failure::Obligation;
use crate::failure::Pursuit;
use crate::failure::Stage;
use crate::failure::judged;
use crate::fixture::Mode;
use crate::fixture::dangling_value;
use crate::fixture::integer_literal;
use crate::fixture::numeric_literal;
use crate::fixture::same_refusal;
use crate::fixture::seed;
use crate::fixture::term_recipe;
use crate::fixture::text_literal;
use crate::fixture::type_recipe;
use crate::fixture::typed_recipe;
use crate::formation::form_comp_type;
use crate::formation::form_value_type;
use crate::refusal::CheckRefusal;
use crate::refusal::CheckingForm;
use crate::refusal::CoreNode;
use crate::refusal::ExpectedShape;
use crate::refusal::Mismatch;
use crate::refusal::TermNode;
use crate::refusal::TypeNode;
use crate::refusal::UnadmittedFormer;

/// One row of a rule table: the term, what it synthesises, the type it is
/// checked against, and the crossings its check makes.
type Row<Term, Type> = (
    Term,
    Result<Type, CheckRefusal>,
    Type,
    Result<ConversionCount, CheckRefusal>,
);

#[test]
fn every_value_former_is_answered_in_both_modes()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let string = arena.value_type_base(BaseType::String);
    let unit_type = arena.value_type_unit();
    let sum = arena.value_type_sum(&[unit_type, unit_type]);
    let returns_integer = arena.comp_type_returner(integer);
    let thunk_returns_integer = arena.value_type_thunk(returns_integer);
    let arrow = arena.comp_type_arrow(integer, returns_integer);
    let thunk_arrow = arena.value_type_thunk(arrow);
    let variable = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let known = arena.value_constant(ConstantIndex::from(0_usize));
    let unknown = arena.value_constant(ConstantIndex::from(9_usize));
    let unit = arena.value_unit();
    let integer_value = arena.value_literal(integer_literal());
    let text = arena.value_literal(text_literal());
    let numeric = arena.value_literal(numeric_literal());
    let returned = arena.computation_return(integer_value);
    let thunk = arena.value_thunk(returned);
    let injection = arena.value_injection(Side::Left.into(), unit);
    let lift = arena.value_lift(Level::zero(), unit);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    seed(&mut context, &[thunk_arrow]);
    let unbound = CheckRefusal::UnboundIndex {
        at: variable,
        zone: Zone::Intuitionistic,
        index: DeBruijnIndex::from(0_u32),
        depth: BinderDepth::from(0_usize),
    };
    let not_known = CheckRefusal::UnknownConstant {
        at: unknown,
        constant: ConstantIndex::from(9_usize),
    };
    let crossed_once = Ok(ConversionCount::from(1_usize));
    let rows: [Row<ValueId, ValueTypeId>; 10] = [
        (variable, Err(unbound), integer, Err(unbound)),
        (known, Ok(thunk_arrow), thunk_arrow, crossed_once),
        (unknown, Err(not_known), integer, Err(not_known)),
        (
            unit,
            Ok(context.atom(Atom::Unit).id()),
            unit_type,
            crossed_once,
        ),
        (
            integer_value,
            Ok(context.atom(Atom::Integer).id()),
            integer,
            crossed_once,
        ),
        (
            text,
            Ok(context.atom(Atom::String).id()),
            string,
            crossed_once,
        ),
        (
            numeric,
            Err(unadmitted_value(numeric, UnadmittedFormer::NumericLiteral)),
            integer,
            Err(unadmitted_value(numeric, UnadmittedFormer::NumericLiteral)),
        ),
        (
            thunk,
            Err(CheckRefusal::NotSynthesisable {
                form: CheckingForm::Thunk(thunk),
            }),
            thunk_returns_integer,
            crossed_once,
        ),
        (
            injection,
            Err(CheckRefusal::NotSynthesisable {
                form: CheckingForm::Injection(injection),
            }),
            sum,
            crossed_once,
        ),
        (
            lift,
            Err(unadmitted_value(lift, UnadmittedFormer::ValueLift)),
            unit_type,
            Err(unadmitted_value(lift, UnadmittedFormer::ValueLift)),
        ),
    ];
    for (term, synthesised, expected, checked) in rows {
        assert_eq!(
            synthesise_value(&mut context, term).map(|found| found.produced().id()),
            synthesised,
            "{term:?} synthesises by its former's rule"
        );
        let expected = form_value_type(&mut context, expected).unwrap();
        assert_eq!(
            check_value(&mut context, term, expected).map(|evidence| evidence.conversions()),
            checked,
            "{term:?} checks by its former's rule"
        );
    }
}

#[test]
fn a_pair_synthesises_its_eager_product_and_checks_against_one()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let unit_type = arena.value_type_unit();
    let returns_integer = arena.comp_type_returner(integer);
    let suspended = arena.value_type_thunk(returns_integer);
    let product = arena.value_type_product(&[unit_type, integer]);
    let checking_only = arena.value_type_product(&[suspended, integer]);
    let unit = arena.value_unit();
    let zero = arena.value_literal(integer_literal());
    let returned = arena.computation_return(zero);
    let thunk = arena.value_thunk(returned);
    let pair = arena.value_tuple(&[unit, zero]);
    let with_thunk = arena.value_tuple(&[thunk, zero]);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let synthesised = synthesise_value(&mut context, pair)
        .map(|found| found.produced().id())
        .unwrap();
    let Some(held) = context.arena().value_type(synthesised)
    else {
        panic!("a pair synthesises an eager product");
    };
    let ValueType::Product(ref parts) = *held
    else {
        panic!("a pair synthesises an eager product");
    };
    let [first, second] = **parts
    else {
        panic!("the pair's product is binary");
    };
    assert_eq!(
        (first, second),
        (
            context.atom(Atom::Unit).id(),
            context.atom(Atom::Integer).id()
        ),
        "of its components' types, in order"
    );
    let product = form_value_type(&mut context, product).unwrap();
    let checking_only = form_value_type(&mut context, checking_only).unwrap();
    let integer = form_value_type(&mut context, integer).unwrap();
    assert_eq!(
        check_value(&mut context, pair, product).map(|evidence| evidence.conversions()),
        Ok(ConversionCount::from(2_usize)),
        "each component checks against its factor, crossing once"
    );
    assert_eq!(
        check_value(&mut context, with_thunk, checking_only).map(|evidence| evidence.conversions()),
        Ok(ConversionCount::from(2_usize)),
        "a component that only checks is checked, not synthesised: the thunk's returned \
             literal and the second component each cross once"
    );
    assert_eq!(
        synthesise_value(&mut context, with_thunk).map(|found| found.produced().id()),
        Err(CheckRefusal::NotSynthesisable {
            form: CheckingForm::Thunk(thunk),
        }),
        "while synthesis needs every component to synthesise"
    );
    assert_eq!(
        check_value(&mut context, pair, integer).map(|evidence| evidence.conversions()),
        Err(CheckRefusal::ShapeMismatch {
            at: TermNode::Value(pair),
            wanted: ExpectedShape::Product,
            found: TypeNode::Value(integer.id()),
        }),
        "a pair against no eager product is a shape mismatch"
    );
}

/// A tuple, an injection and a case are judged at any arity: a tuple
/// against a product of as many components, an injection against the
/// summand it names, a case against a sum of as many summands as it has
/// branches, the empty sum's case at no branch.
#[test]
fn n_ary_tuples_injections_and_cases_check_at_their_arity()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let string = arena.value_type_base(BaseType::String);
    let unit_type = arena.value_type_unit();
    let triple_type = arena.value_type_product(&[integer, string, unit_type]);
    let pair_type = arena.value_type_product(&[integer, string]);
    let single_type = arena.value_type_product(&[integer]);
    let three = arena.value_type_sum(&[integer, string, unit_type]);
    let empty = arena.value_type_sum(&[]);
    let returns_integer = arena.comp_type_returner(integer);
    let zero = arena.value_literal(integer_literal());
    let text = arena.value_literal(text_literal());
    let unit = arena.value_unit();
    let triple = arena.value_tuple(&[zero, text, unit]);
    let single = arena.value_tuple(&[zero]);
    let last = arena.value_injection(gandr_core_term::Summand::from(2_usize), unit);
    let beyond = arena.value_injection(gandr_core_term::Summand::from(3_usize), unit);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let payload = arena.computation_return(bound);
    let constant = arena.computation_return(zero);
    let scrutinee = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let three_way = arena.computation_case(scrutinee, &[payload, constant, constant]);
    let two_way = arena.computation_case(scrutinee, &[payload, constant]);
    let absurd = arena.computation_case(scrutinee, &[]);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let synthesised = synthesise_value(&mut context, triple)
        .map(|found| found.produced().id())
        .unwrap();
    let Some(held) = context.arena().value_type(synthesised)
    else {
        panic!("a tuple synthesises an eager product");
    };
    let ValueType::Product(ref parts) = *held
    else {
        panic!("a tuple synthesises an eager product");
    };
    assert_eq!(
        **parts,
        [
            context.atom(Atom::Integer).id(),
            context.atom(Atom::String).id(),
            context.atom(Atom::Unit).id()
        ],
        "a tuple of three synthesises the product of its three components' types"
    );
    let triple_type = form_value_type(&mut context, triple_type).unwrap();
    let pair_type = form_value_type(&mut context, pair_type).unwrap();
    let single_type = form_value_type(&mut context, single_type).unwrap();
    let three = form_value_type(&mut context, three).unwrap();
    assert_eq!(
        check_value(&mut context, triple, triple_type).map(|evidence| evidence.conversions()),
        Ok(ConversionCount::from(3_usize)),
        "each of three components checks against its factor"
    );
    assert_eq!(
        check_value(&mut context, single, single_type).map(|evidence| evidence.conversions()),
        Ok(ConversionCount::from(1_usize)),
        "a tuple of one checks against a product of one"
    );
    assert_eq!(
        check_value(&mut context, triple, pair_type).map(|evidence| evidence.conversions()),
        Err(CheckRefusal::ShapeMismatch {
            at: TermNode::Value(triple),
            wanted: ExpectedShape::Product,
            found: TypeNode::Value(pair_type.id()),
        }),
        "a tuple against a product of another arity is a shape mismatch"
    );
    assert_eq!(
        check_value(&mut context, last, three).map(|evidence| evidence.conversions()),
        Ok(ConversionCount::from(1_usize)),
        "an injection checks its payload against the summand it names"
    );
    assert_eq!(
        check_value(&mut context, beyond, three).map(|evidence| evidence.conversions()),
        Err(CheckRefusal::ShapeMismatch {
            at: TermNode::Value(beyond),
            wanted: ExpectedShape::Sum,
            found: TypeNode::Value(three.id()),
        }),
        "an injection past the last summand is a shape mismatch"
    );
    let returns_integer = form_comp_type(&mut context, returns_integer).unwrap();
    for (case, scrutinised, checked) in [
        (three_way, three.id(), Ok(ConversionCount::from(3_usize))),
        (
            two_way,
            three.id(),
            Err(CheckRefusal::ShapeMismatch {
                at: TermNode::Value(scrutinee),
                wanted: ExpectedShape::Sum,
                found: TypeNode::Value(three.id()),
            }),
        ),
        (absurd, empty, Ok(ConversionCount::default())),
    ] {
        context.binders().open(Zone::Intuitionistic, scrutinised);
        assert_eq!(
            check_comp(&mut context, case, returns_integer).map(|evidence| evidence.conversions()),
            checked,
            "{case:?} checks one branch per summand, under that summand"
        );
        context.binders().close(Zone::Intuitionistic).unwrap();
    }
}

/// A split binds one variable per component, component zero outermost:
/// reading component zero checks at its type and reading component one
/// there does not; a split of the unit binds nothing; a split of another
/// arity or of a non-product is a shape mismatch.
#[test]
fn a_split_binds_every_component_of_its_product()
{
    use gandr_core_term::ComponentCount;
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let string = arena.value_type_base(BaseType::String);
    let unit_type = arena.value_type_unit();
    let triple_type = arena.value_type_product(&[integer, string, unit_type]);
    let returns_integer = arena.comp_type_returner(integer);
    let scrutinee = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let first = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(2_u32));
    let second = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let returns_first = arena.computation_return(first);
    let returns_second = arena.computation_return(second);
    let three = ComponentCount::from(3_usize);
    let reads_first = arena.computation_split(scrutinee, three, returns_first);
    let reads_second = arena.computation_split(scrutinee, three, returns_second);
    let too_few = arena.computation_split(scrutinee, ComponentCount::from(2_usize), returns_first);
    let zero = arena.value_literal(integer_literal());
    let returns_zero = arena.computation_return(zero);
    let empty = arena.computation_split(scrutinee, ComponentCount::default(), returns_zero);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let triple_type = form_value_type(&mut context, triple_type).unwrap();
    let unit_type = form_value_type(&mut context, unit_type).unwrap();
    let integer = form_value_type(&mut context, integer).unwrap();
    let returns_integer = form_comp_type(&mut context, returns_integer).unwrap();
    let mismatch = |found: ValueTypeId| CheckRefusal::ShapeMismatch {
        at: TermNode::Value(scrutinee),
        wanted: ExpectedShape::Product,
        found: TypeNode::Value(found),
    };
    for (split, scrutinised, accepted) in [
        (reads_first, triple_type.id(), Some(true)),
        (reads_second, triple_type.id(), Some(false)),
        (too_few, triple_type.id(), None),
        (empty, unit_type.id(), Some(true)),
        (empty, integer.id(), None),
    ] {
        context.binders().open(Zone::Intuitionistic, scrutinised);
        let checked = check_comp(&mut context, split, returns_integer);
        match accepted {
            Some(true) => assert!(checked.is_ok(), "{split:?}: {checked:?}"),
            Some(false) => assert!(
                checked.is_err() && checked != Err(mismatch(scrutinised)),
                "{split:?} reads a component of another type: {checked:?}"
            ),
            None => assert_eq!(checked.map(|_| ()), Err(mismatch(scrutinised)), "{split:?}"),
        }
        context.binders().close(Zone::Intuitionistic).unwrap();
    }
}

/// A split synthesises its body's type strengthened out from under the
/// binders it opens: a body whose type reads no component gives the split
/// that type, the unit split a statement lowers to included, and every binder
/// closes; a body whose type reads a component is the bind's refusal, at the
/// split (#1374).
#[test]
fn a_split_synthesises_its_body_type_outside_its_binders()
{
    // def produce : U (F Integer) ; def pick : U ((A : Type) -> F El A) ;
    use gandr_core_term::ComponentCount;
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let string = arena.value_type_base(BaseType::String);
    let unit_type = arena.value_type_unit();
    let pair_type = arena.value_type_product(&[integer, string]);
    let returns_integer = arena.comp_type_returner(integer);
    let produces = arena.value_type_thunk(returns_integer);
    let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let codes = arena.value_type_product(&[small]);
    let bound_code = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let decoded = arena.value_type_element(bound_code, Level::zero());
    let returns_decoded = arena.comp_type_returner(decoded);
    let pi = arena.comp_type_pi(small, returns_decoded);
    let picks = arena.value_type_thunk(pi);
    let produce = arena.value_constant(ConstantIndex::from(0_usize));
    let pick = arena.value_constant(ConstantIndex::from(1_usize));
    let scrutinee = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let forced = arena.computation_force(produce);
    let over_pair = arena.computation_split(scrutinee, ComponentCount::from(2_usize), forced);
    let statement = arena.computation_split(scrutinee, ComponentCount::default(), forced);
    let head = arena.computation_force(pick);
    let code = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let picked = arena.computation_application(head, code);
    let dependent = arena.computation_split(scrutinee, ComponentCount::from(1_usize), picked);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    seed(&mut context, &[produces, picks]);
    let pair_type = form_value_type(&mut context, pair_type).unwrap();
    let unit_type = form_value_type(&mut context, unit_type).unwrap();
    let codes = form_value_type(&mut context, codes).unwrap();
    for (split, scrutinised) in [(over_pair, pair_type.id()), (statement, unit_type.id())] {
        context.binders().open(Zone::Intuitionistic, scrutinised);
        assert_eq!(
            synthesise_comp(&mut context, split).map(|found| found.produced().id()),
            Ok(returns_integer),
            "{split:?} has its body's type, which reads none of its components"
        );
        assert_eq!(
            context.binders().depth(Zone::Intuitionistic),
            BinderDepth::from(1_usize),
            "{split:?} closes every binder it opened"
        );
        context.binders().close(Zone::Intuitionistic).unwrap();
    }
    context.binders().open(Zone::Intuitionistic, codes.id());
    let refusal = synthesise_comp(&mut context, dependent).unwrap_err();
    assert!(
        matches!(refusal, CheckRefusal::DependentBind { at, .. } if at == dependent),
        "the body has `F El a`, which has no reading outside the split: {refusal:?}"
    );
}

#[test]
fn a_static_lambda_checks_only_against_a_static_pi()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let operator_type = arena.value_type_static_pi(small, small);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let identity = arena.value_static_lambda(bound);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let operator_type = form_value_type(&mut context, operator_type).unwrap();
    let integer = form_value_type(&mut context, integer).unwrap();
    assert_eq!(
        check_value(&mut context, identity, operator_type).map(|evidence| evidence.conversions()),
        Ok(ConversionCount::from(1_usize)),
        "the body checks against the codomain beneath a binder of the domain"
    );
    assert_eq!(
        check_value(&mut context, identity, integer).map(|evidence| evidence.conversions()),
        Err(CheckRefusal::ShapeMismatch {
            at: TermNode::Value(identity),
            wanted: ExpectedShape::StaticPi,
            found: TypeNode::Value(integer.id()),
        }),
        "against any other former it is a shape mismatch"
    );
    assert_eq!(
        synthesise_value(&mut context, identity).map(|found| found.produced().id()),
        Err(CheckRefusal::NotSynthesisable {
            form: CheckingForm::StaticLambda(identity),
        }),
        "and it synthesises nothing"
    );
    assert_eq!(
        context.binders().depth(Zone::Intuitionistic),
        BinderDepth::from(0_usize),
        "every binder the checks opened is closed"
    );
}

#[test]
fn every_comp_former_is_answered_in_both_modes()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let returns_integer = arena.comp_type_returner(integer);
    let arrow = arena.comp_type_arrow(integer, returns_integer);
    let thunk_arrow = arena.value_type_thunk(arrow);

    let unit = arena.value_unit();
    let integer_value = arena.value_literal(integer_literal());
    let variable = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let returns_variable = arena.computation_return(variable);
    let lambda = arena.computation_lambda(returns_variable);
    let function = arena.value_constant(ConstantIndex::from(0_usize));
    let force = arena.computation_force(function);
    let application = arena.computation_application(force, integer_value);
    let returned = arena.computation_return(integer_value);
    let bind = arena.computation_bind(application, force);
    let case = arena.computation_case(unit, &[returned, returned]);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    seed(&mut context, &[thunk_arrow]);
    let crossed = |crossings: usize| Ok(ConversionCount::from(crossings));
    let rows: [Row<ComputationId, CompTypeId>; 4] = [
        (force, Ok(arrow), arrow, crossed(1)),
        (
            application,
            Ok(returns_integer),
            returns_integer,
            crossed(2),
        ),
        (
            lambda,
            Err(CheckRefusal::NotSynthesisable {
                form: CheckingForm::Lambda(lambda),
            }),
            arrow,
            crossed(1),
        ),
        (bind, Ok(arrow), arrow, crossed(2)),
    ];
    for (term, synthesised, expected, checked) in rows {
        assert_eq!(
            synthesise_comp(&mut context, term).map(|found| found.produced().id()),
            synthesised,
            "{term:?} synthesises by its former's rule"
        );
        let expected = form_comp_type(&mut context, expected).unwrap();
        assert_eq!(
            check_comp(&mut context, term, expected).map(|evidence| evidence.conversions()),
            checked,
            "{term:?} checks by its former's rule"
        );
    }
    let found = synthesise_comp(&mut context, returned).map(|found| found.produced().id());
    let mut tally = ConversionCount::default();
    assert_eq!(
        found.and_then(|found| comp_bridge(
            &mut context,
            returned,
            found,
            returns_integer,
            &mut tally
        )),
        Ok(()),
        "a return synthesises the pure returner of what its value synthesises (#1142)"
    );
    let expected = form_comp_type(&mut context, returns_integer).unwrap();
    assert_eq!(
        check_comp(&mut context, returned, expected).map(|evidence| evidence.conversions()),
        crossed(1),
        "and checks against it by its value"
    );
    assert_eq!(
        synthesise_comp(&mut context, case).map(|found| found.produced().id()),
        Err(CheckRefusal::NotSynthesisable {
            form: CheckingForm::Case(case)
        })
    );
    let expected = form_comp_type(&mut context, returns_integer).unwrap();
    let Err(CheckRefusal::ShapeMismatch {
        at: TermNode::Value(at),
        wanted: ExpectedShape::Sum,
        found: TypeNode::Value(found),
    }) = check_comp(&mut context, case, expected)
    else {
        panic!("a unit scrutinee must report the required sum shape");
    };
    assert_eq!(at, unit);
    drop(context);
    assert_eq!(
        arena.value_type(found),
        Some(&ValueType::unit()),
        "the refusal reports the scrutinee's actual classifier, independent of arena allocation"
    );
}

#[test]
fn a_bind_synthesises_its_continuations_type()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let string = arena.value_type_base(BaseType::String);
    let returns_integer = arena.comp_type_returner(integer);
    let returns_string = arena.comp_type_returner(string);
    let arrow = arena.comp_type_arrow(integer, returns_string);
    let suspended_integer = arena.value_type_thunk(returns_integer);
    let suspended_arrow = arena.value_type_thunk(arrow);
    let produce = arena.value_constant(ConstantIndex::from(0_usize));
    let consume = arena.value_constant(ConstantIndex::from(1_usize));
    let bound = arena.computation_force(produce);
    let head = arena.computation_force(consume);
    let variable = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let body = arena.computation_application(head, variable);
    let bind = arena.computation_bind(bound, body);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    seed(&mut context, &[suspended_integer, suspended_arrow]);

    assert_eq!(
        synthesise_comp(&mut context, bind).map(|found| found.produced().id()),
        Ok(returns_string),
        "the bind has its body's type, the bound name typed by the returner it eliminates"
    );
    assert_eq!(
        context.binders().depth(Zone::Intuitionistic),
        BinderDepth::from(0_usize),
        "the bind closes the binder it opened"
    );
}

#[test]
fn host_operations_check_payloads_and_retain_effects()
{
    use gandr_core_term::effect::EffectRow;
    use gandr_core_term::effect::host::HostSignatures;
    let mut arena = CoreArena::new();
    let host = HostSignatures::new(&mut arena).expect("host interfaces");
    let variable = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let unit = arena.value_unit();
    let string = arena.value_literal(text_literal());
    for signature in [&host.exec, &host.fs, &host.proc, &host.env] {
        for operation in signature.operations() {
            let request =
                arena.computation_perform(signature.clone(), operation.name.clone(), variable);
            let wrong_payload = if matches!(
                arena.value_type(operation.payload),
                Some(ValueType::Base(BaseType::String))
            ) {
                unit
            }
            else {
                string
            };
            let wrong =
                arena.computation_perform(signature.clone(), operation.name.clone(), wrong_payload);
            let unknown = arena.computation_perform(signature.clone(), "missing".into(), variable);
            let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
            context
                .binders()
                .open(Zone::Intuitionistic, operation.payload);
            let inferred = synthesise_comp(&mut context, request)
                .expect("typed host payload")
                .produced()
                .id();
            assert_eq!(
                context.arena().comp_type(inferred),
                Some(&gandr_core_term::CompType::Returner {
                    result: operation.reply,
                    effects: EffectRow::singleton(signature.clone())
                })
            );
            assert!(
                matches!(
                    synthesise_comp(&mut context, wrong),
                    Err(CheckRefusal::TypeMismatch(_) | CheckRefusal::ShapeMismatch { .. })
                ),
                "{} rejects the wrong payload",
                operation.name.as_ref()
            );
            assert_eq!(
                synthesise_comp(&mut context, unknown).unwrap_err(),
                CheckRefusal::UnknownOperation { at: unknown }
            );
            assert_eq!(
                context.binders().depth(Zone::Intuitionistic),
                BinderDepth::from(1_usize)
            );
        }
    }
    let nil = arena.value_list_nil();
    let strings = arena.value_list_cons(string, nil);
    let mode = arena.value_tuple(&[strings, string]);
    let command = arena.value_tuple(&[string, mode]);
    let good = arena.computation_perform(host.exec.clone(), "exec".into(), command);
    let integer = arena.value_literal(integer_literal());
    let integers = arena.value_list_cons(integer, nil);
    let mode = arena.value_tuple(&[integers, string]);
    let command = arena.value_tuple(&[string, mode]);
    let bad = arena.computation_perform(host.exec, "exec".into(), command);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let inferred = synthesise_comp(&mut context, good)
        .expect("native string arguments")
        .produced();
    check_comp(&mut context, good, inferred).expect("perform checks by row subsumption");
    assert!(matches!(
        synthesise_comp(&mut context, bad),
        Err(CheckRefusal::TypeMismatch(_))
    ));
}

#[test]
fn handlers_discharge_only_their_own_interface()
{
    use gandr_core_term::control::EffectClause;
    use gandr_core_term::effect::EffectOp;
    use gandr_core_term::effect::EffectRow;
    use gandr_core_term::effect::EffectSig;
    let mut arena = CoreArena::new();
    let unit_type = arena.value_type_unit();
    let integer_type = arena.value_type_base(BaseType::Integer);
    let string_type = arena.value_type_base(BaseType::String);
    let answer = arena.comp_type_returner(string_type);
    let signature = EffectSig::new("Ask".into(), [EffectOp {
        name: "ask".into(),
        payload: unit_type,
        reply: integer_type,
    }])
    .unwrap();
    let other = EffectSig::new("Other".into(), [EffectOp {
        name: "other".into(),
        payload: unit_type,
        reply: string_type,
    }])
    .unwrap();
    let allowed =
        arena.comp_type_returner_with_effects(string_type, EffectRow::singleton(other.clone()));
    let unit = arena.value_unit();
    let integer = arena.value_literal(integer_literal());
    let string = arena.value_literal(text_literal());
    let zero = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let one = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let returned = arena.computation_return(string);
    let reply = arena.computation_return(integer);
    let first_resume = arena.computation_resume(zero, reply);
    let second_resume = arena.computation_resume(one, reply);
    let twice = arena.computation_bind(first_resume, second_resume);
    let clauses: alloc::sync::Arc<[_]> = [EffectClause {
        operation: "ask".into(),
        body: twice,
    }]
    .into();
    let subject = arena.computation_perform(signature.clone(), "ask".into(), unit);
    let good = arena.computation_handle(
        signature.clone(),
        subject,
        returned,
        alloc::sync::Arc::clone(&clauses),
    );
    let wrong_return = arena.computation_return(zero);
    let wrong_return = arena.computation_handle(
        signature.clone(),
        subject,
        wrong_return,
        alloc::sync::Arc::clone(&clauses),
    );
    let wrong_binder = arena.computation_resume(one, reply);
    let wrong_binder = arena.computation_handle(
        signature.clone(),
        subject,
        returned,
        [EffectClause {
            operation: "ask".into(),
            body: wrong_binder,
        }]
        .into(),
    );
    let missing = arena.computation_handle(signature.clone(), subject, returned, [].into());
    let unknown = arena.computation_handle(
        signature.clone(),
        subject,
        returned,
        [EffectClause {
            operation: "missing".into(),
            body: twice,
        }]
        .into(),
    );
    let extended = EffectSig::new("Ask".into(), [
        EffectOp {
            name: "ask".into(),
            payload: unit_type,
            reply: integer_type,
        },
        EffectOp {
            name: "tell".into(),
            payload: string_type,
            reply: unit_type,
        },
    ])
    .unwrap();
    let repeated = arena.computation_handle(
        extended,
        subject,
        returned,
        [
            EffectClause {
                operation: "ask".into(),
                body: twice,
            },
            EffectClause {
                operation: "ask".into(),
                body: twice,
            },
        ]
        .into(),
    );
    let other_request = arena.computation_perform(other, "other".into(), unit);
    let both = arena.computation_bind(subject, other_request);
    let residual = arena.computation_handle(signature.clone(), both, returned, clauses);
    let leaking_clause = arena.computation_bind(first_resume, other_request);
    let leaking_clause = arena.computation_handle(
        signature,
        subject,
        returned,
        [EffectClause {
            operation: "ask".into(),
            body: leaking_clause,
        }]
        .into(),
    );
    let conflict = EffectSig::new("Ask".into(), [EffectOp {
        name: "ask".into(),
        payload: unit_type,
        reply: string_type,
    }])
    .unwrap();
    let conflict = arena.computation_handle(
        conflict,
        subject,
        returned,
        [EffectClause {
            operation: "ask".into(),
            body: returned,
        }]
        .into(),
    );
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let answer = form_comp_type(&mut context, answer).unwrap();
    let allowed = form_comp_type(&mut context, allowed).unwrap();
    check_comp(&mut context, good, answer).expect("a deep resumption may be used twice");
    assert!(matches!(
        check_comp(&mut context, wrong_return, answer),
        Err(CheckRefusal::TypeMismatch(_))
    ));
    assert!(matches!(
        check_comp(&mut context, wrong_binder, answer),
        Err(CheckRefusal::ShapeMismatch {
            wanted: ExpectedShape::Stack,
            ..
        })
    ));
    for malformed in [missing, unknown, repeated] {
        assert_eq!(
            check_comp(&mut context, malformed, answer).unwrap_err(),
            CheckRefusal::HandlerCoverage { at: malformed }
        );
    }
    assert!(matches!(
        check_comp(&mut context, residual, answer),
        Err(CheckRefusal::TypeMismatch(_))
    ));
    check_comp(&mut context, residual, allowed)
        .expect("an unrelated effect remains in the answer row");
    assert!(matches!(
        check_comp(&mut context, leaking_clause, answer),
        Err(CheckRefusal::TypeMismatch(_))
    ));
    assert!(matches!(
        check_comp(&mut context, conflict, answer),
        Err(CheckRefusal::EffectSignatureConflict { .. })
    ));
    assert_eq!(
        synthesise_comp(&mut context, good).unwrap_err(),
        CheckRefusal::NotSynthesisable {
            form: CheckingForm::Handle(good)
        }
    );
    assert_eq!(
        context.binders().depth(Zone::Intuitionistic),
        BinderDepth::from(0_usize)
    );
}

#[test]
fn control_rules_preserve_rows_scopes_and_shapes()
{
    use gandr_core_term::control::StackFrame;
    use gandr_kernel_term::Component;
    let mut arena = CoreArena::new();
    let unit_type = arena.value_type_unit();
    let integer_type = arena.value_type_base(BaseType::Integer);
    let string_type = arena.value_type_base(BaseType::String);
    let returned_unit = arena.comp_type_returner(unit_type);
    let returned_integer = arena.comp_type_returner(integer_type);
    let returned_string = arena.comp_type_returner(string_type);
    let ambient_type = arena.value_type_unit();
    let arrow = arena.comp_type_arrow(ambient_type, returned_integer);
    let pair = arena.comp_type_with(&[returned_unit, arrow]);
    let suspended_pair = arena.value_type_thunk(pair);
    let outer = arena.value_constant(ConstantIndex::from(0_usize));
    let argument = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let forced = arena.computation_force(outer);
    let stack = arena.value_reify(
        [
            StackFrame::Bind(forced),
            StackFrame::Project(Component::from(1_usize)),
            StackFrame::Apply(argument),
        ]
        .into(),
    );
    let classifier = arena.value_type_stack(returned_integer, returned_integer);
    let effectful = arena.comp_type_returner_with_effects(
        integer_type,
        effect_row("Ask".into(), unit_type, integer_type),
    );
    let bad_classifier = arena.value_type_stack(effectful, returned_integer);
    let bad_stack = arena.value_reify([StackFrame::Project(Component::from(0_usize))].into());
    let past_stack = arena.value_reify(
        [
            StackFrame::Bind(forced),
            StackFrame::Project(Component::from(2_usize)),
            StackFrame::Apply(argument),
        ]
        .into(),
    );
    let code_type = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let bound_code = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let element = arena.value_type_element(bound_code, Level::zero());
    let returned_element = arena.comp_type_returner(element);
    let dependent = arena.comp_type_pi(code_type, returned_element);
    let quoted_string = arena.value_quote(string_type);
    let dependent_stack = arena.value_reify([StackFrame::Apply(quoted_string)].into());
    let dependent_classifier = arena.value_type_stack(dependent, returned_string);
    let unit = arena.value_unit();
    let integer = arena.value_literal(integer_literal());
    let string = arena.value_literal(text_literal());
    let return_unit = arena.computation_return(unit);
    let return_integer = arena.computation_return(integer);
    let return_string = arena.computation_return(string);
    let continuation = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let resumed = arena.computation_resume(continuation, return_integer);
    let shift = arena.computation_shift(resumed);
    let reset = arena.computation_reset(shift);
    let wrong_shift = arena.computation_shift(return_string);
    let wrong_reset = arena.computation_reset(wrong_shift);
    let negative_pair = arena.computation_with(&[reset, return_string]);
    let negative_pair_type = arena.comp_type_with(&[returned_integer, returned_string]);
    let nested = arena.computation_reset(negative_pair);
    let past = arena.computation_project(Component::from(2_usize), forced);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    seed(&mut context, &[suspended_pair]);
    context.binders().open(Zone::Intuitionistic, ambient_type);
    let classifier = form_value_type(&mut context, classifier).unwrap();
    check_value(&mut context, stack, classifier)
        .expect("later frames do not retain the bind's integer binder");
    let bad_classifier = form_value_type(&mut context, bad_classifier).unwrap();
    assert!(matches!(
        check_value(&mut context, stack, bad_classifier),
        Err(CheckRefusal::ShapeMismatch {
            wanted: ExpectedShape::Returner,
            ..
        })
    ));
    assert!(matches!(
        check_value(&mut context, bad_stack, classifier),
        Err(CheckRefusal::ShapeMismatch {
            wanted: ExpectedShape::With,
            ..
        })
    ));
    assert!(matches!(
        check_value(&mut context, past_stack, classifier),
        Err(CheckRefusal::ShapeMismatch {
            wanted: ExpectedShape::With,
            ..
        })
    ));
    assert_eq!(
        synthesise_comp(&mut context, past),
        Err(CheckRefusal::AbsentTupleComponent(past)),
        "a projection past the lazy product's last component is refused by position"
    );
    let dependent_classifier = form_value_type(&mut context, dependent_classifier).unwrap();
    check_value(&mut context, dependent_stack, dependent_classifier)
        .expect("stack application instantiates its Pi output");
    assert_eq!(
        synthesise_value(&mut context, stack).unwrap_err(),
        CheckRefusal::NotSynthesisable {
            form: CheckingForm::Reify(stack)
        }
    );
    let integer_answer = form_comp_type(&mut context, returned_integer).unwrap();
    check_comp(&mut context, reset, integer_answer).expect("capture and resume");
    assert_eq!(
        check_comp(&mut context, shift, integer_answer).unwrap_err(),
        CheckRefusal::ShiftWithoutReset { at: shift }
    );
    assert!(matches!(
        check_comp(&mut context, wrong_reset, integer_answer),
        Err(CheckRefusal::TypeMismatch(_))
    ));
    let pair_answer = form_comp_type(&mut context, negative_pair_type).unwrap();
    check_comp(&mut context, nested, pair_answer).expect("the inner reset supplies its own answer");
    for (term, form) in [
        (reset, CheckingForm::Reset(reset)),
        (shift, CheckingForm::Shift(shift)),
        (negative_pair, CheckingForm::With(negative_pair)),
    ] {
        assert_eq!(
            synthesise_comp(&mut context, term).unwrap_err(),
            CheckRefusal::NotSynthesisable { form }
        );
    }
    let resume_type = context
        .arena_mut()
        .value_type_stack(returned_integer, returned_string);
    context.binders().open(Zone::Intuitionistic, resume_type);
    let inferred = synthesise_comp(&mut context, resumed)
        .expect("resume delivers its output, not its input")
        .produced()
        .id();
    assert_eq!(inferred, returned_string);
    let wrong = context
        .arena_mut()
        .computation_resume(continuation, return_unit);
    assert!(matches!(
        synthesise_comp(&mut context, wrong),
        Err(CheckRefusal::TypeMismatch(_))
    ));
    assert_eq!(
        context.binders().depth(Zone::Intuitionistic),
        BinderDepth::from(2_usize)
    );
}

#[test]
fn reset_answers_are_weakened_through_intervening_binders()
{
    let mut arena = CoreArena::new();
    let universe = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let code = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let element = arena.value_type_element(code, Level::zero());
    let outer_code = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let result = arena.value_type_element(outer_code, Level::zero());
    let result = arena.comp_type_returner(result);
    let unit = arena.value_type_unit();
    let answer = arena.comp_type_arrow(unit, result);
    let outer_value = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(3_u32));
    let returned = arena.computation_return(outer_value);
    let body = arena.computation_lambda(returned);
    let shifted = arena.computation_shift(body);
    let body = arena.computation_lambda(shifted);
    let reset = arena.computation_reset(body);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    context.binders().open(Zone::Intuitionistic, universe);
    context.binders().open(Zone::Intuitionistic, element);
    let answer = form_comp_type(&mut context, answer).unwrap();
    check_comp(&mut context, reset, answer).expect(
        "answer code refers to the outer type binder through both lambdas and the captured stack",
    );
    assert_eq!(
        context.binders().depth(Zone::Intuitionistic),
        BinderDepth::from(2_usize)
    );
}

#[test]
fn pure_bind_into_lambda_is_unchanged()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let unit = arena.value_type_unit();
    let result = arena.comp_type_returner(integer);
    let expected = arena.comp_type_arrow(unit, result);
    let value = arena.value_literal(integer_literal());
    let add = gandr_core_term::primitive::PRELUDE
        .iter()
        .copied()
        .find(|primitive| primitive.name().as_ref() == "add")
        .expect("native add");
    let bound = arena.computation_primitive(
        add,
        gandr_core_term::primitive::Arguments::Binary([value, value]),
    );
    let outer = arena.value_variable(Zone::Intuitionistic, 1_u32.into());
    let returned = arena.computation_return(outer);
    let lambda = arena.computation_lambda(returned);
    let program = arena.computation_bind(bound, lambda);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let expected = form_comp_type(&mut context, expected).unwrap();
    check_comp(&mut context, program, expected)
        .expect("a pure bind may continue with a negative computation");
    assert_eq!(
        context.binders().depth(Zone::Intuitionistic),
        BinderDepth::from(0_usize)
    );
}

#[test]
fn effectful_bind_into_lambda_is_shape_mismatch()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let unit_type = arena.value_type_unit();
    let result = arena.comp_type_returner(integer);
    let expected = arena.comp_type_arrow(unit_type, result);
    let signature = effect_row("E".into(), unit_type, integer)
        .signatures()
        .next()
        .expect("one interface")
        .clone();
    let unit = arena.value_unit();
    let bound = arena.computation_perform(signature, "run".into(), unit);
    let outer = arena.value_variable(Zone::Intuitionistic, 1_u32.into());
    let returned = arena.computation_return(outer);
    let lambda = arena.computation_lambda(returned);
    let program = arena.computation_bind(bound, lambda);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let formed = form_comp_type(&mut context, expected).unwrap();
    assert_eq!(
        check_comp(&mut context, program, formed).unwrap_err(),
        CheckRefusal::ShapeMismatch {
            at: TermNode::Computation(program),
            wanted: ExpectedShape::Returner,
            found: TypeNode::Computation(expected)
        }
    );
    assert_eq!(
        context.binders().depth(Zone::Intuitionistic),
        BinderDepth::from(0_usize)
    );
}

#[test]
fn a_stack_bind_cannot_export_its_local_type_code()
{
    use gandr_core_term::control::StackFrame;
    let mut arena = CoreArena::new();
    let universe = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let code = arena.value_variable(Zone::Intuitionistic, 0_u32.into());
    let element = arena.value_type_element(code, Level::zero());
    let result = arena.comp_type_returner(element);
    let function = arena.comp_type_pi(universe, result);
    let suspended = arena.value_type_thunk(function);
    let constant = arena.value_constant(ConstantIndex::from(0_usize));
    let forced = arena.computation_force(constant);
    let body = arena.computation_application(forced, code);
    let stack = arena.value_reify([StackFrame::Bind(body)].into());
    let input = arena.comp_type_returner(universe);
    let unit = arena.value_type_unit();
    let output = arena.comp_type_returner(unit);
    let expected = arena.value_type_stack(input, output);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    seed(&mut context, &[suspended]);
    let expected = form_value_type(&mut context, expected).unwrap();
    assert!(
        matches!(check_value(&mut context, stack, expected), Err(CheckRefusal::DependentStack { at, .. }) if at == stack)
    );
    assert_eq!(
        context.binders().depth(Zone::Intuitionistic),
        BinderDepth::from(0_usize)
    );
}

#[test]
fn stack_bind_accumulates_input_and_body_rows()
{
    use gandr_core_term::control::StackFrame;
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let left = effect_row("Input".into(), integer, integer);
    let right = effect_row("Body".into(), integer, integer);
    let both = left.union(&right, &arena).expect("disjoint names");
    let input = arena.comp_type_returner_with_effects(integer, left);
    let output = arena.comp_type_returner_with_effects(integer, both);
    let missing = arena.comp_type_returner_with_effects(integer, right.clone());
    let value = arena.value_variable(Zone::Intuitionistic, 0_u32.into());
    let signature = right.signatures().next().expect("one interface").clone();
    let body = arena.computation_perform(signature, "run".into(), value);
    let stack = arena.value_reify([StackFrame::Bind(body)].into());
    let expected = arena.value_type_stack(input, output);
    let dropped_input = arena.value_type_stack(input, missing);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let expected = form_value_type(&mut context, expected).unwrap();
    check_value(&mut context, stack, expected).expect("the output retains both rows");
    let missing = form_value_type(&mut context, dropped_input).unwrap();
    assert!(matches!(
        check_value(&mut context, stack, missing),
        Err(CheckRefusal::TypeMismatch(_))
    ));
    assert_eq!(
        context.binders().depth(Zone::Intuitionistic),
        BinderDepth::from(0_usize)
    );
}

/// A one-operation interface for checking row accumulation.
///
/// # Specification
/// trivial.
fn effect_row(
    name: gandr_core_term::effect::EffectName,
    payload: ValueTypeId,
    reply: ValueTypeId,
) -> gandr_core_term::effect::EffectRow
{
    use gandr_core_term::effect::EffectOp;
    use gandr_core_term::effect::EffectRow;
    use gandr_core_term::effect::EffectSig;
    use gandr_core_term::effect::OperationName;
    EffectRow::singleton(
        EffectSig::new(name, [EffectOp {
            name: OperationName::from("run"),
            payload,
            reply,
        }])
        .expect("one operation"),
    )
}

/// The interface with no operations: its handler has no operation clauses.
///
/// # Specification
/// trivial.
fn empty_interface() -> gandr_core_term::effect::EffectSig
{
    gandr_core_term::effect::EffectSig::new("Empty".into(), []).expect("no operations")
}

#[test]
fn handle_against_a_non_returner_is_stuck()
{
    let mut arena = CoreArena::new();
    let unit_type = arena.value_type_unit();
    let returns_unit = arena.comp_type_returner(unit_type);
    let arrow = arena.comp_type_arrow(unit_type, returns_unit);
    let unit = arena.value_unit();
    let returned = arena.computation_return(unit);
    let handler = arena.computation_handle(empty_interface(), returned, returned, [].into());
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let arrow = form_comp_type(&mut context, arrow).unwrap();
    assert!(matches!(
        check_comp(&mut context, handler, arrow),
        Err(CheckRefusal::ShapeMismatch {
            at: TermNode::Computation(at),
            wanted: ExpectedShape::Returner,
            ..
        }) if at == handler
    ));
    assert_eq!(
        context.binders().depth(Zone::Intuitionistic),
        BinderDepth::from(0_usize)
    );
}

#[test]
fn handle_of_a_non_returner_scrutinee_is_a_shape_mismatch()
{
    let mut arena = CoreArena::new();
    let unit_type = arena.value_type_unit();
    let returns_unit = arena.comp_type_returner(unit_type);
    let arrow = arena.comp_type_arrow(unit_type, returns_unit);
    let suspended = arena.value_type_thunk(arrow);
    let function = arena.value_constant(ConstantIndex::from(0_usize));
    let subject = arena.computation_force(function);
    let unit = arena.value_unit();
    let returned = arena.computation_return(unit);
    let handler = arena.computation_handle(empty_interface(), subject, returned, [].into());
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    seed(&mut context, &[suspended]);
    let answer = form_comp_type(&mut context, returns_unit).unwrap();
    assert!(matches!(
        check_comp(&mut context, handler, answer),
        Err(CheckRefusal::ShapeMismatch {
            at: TermNode::Computation(at),
            wanted: ExpectedShape::Returner,
            found: TypeNode::Computation(found),
        }) if at == handler && found == arrow
    ));
}

#[test]
fn empty_signature_handler_finishes_after_the_return_clause()
{
    let mut arena = CoreArena::new();
    let integer_type = arena.value_type_base(BaseType::Integer);
    let answer = arena.comp_type_returner(integer_type);
    let suspended = arena.value_type_thunk(answer);
    let pure = arena.value_constant(ConstantIndex::from(0_usize));
    let subject = arena.computation_force(pure);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let on_return = arena.computation_return(bound);
    let handler = arena.computation_handle(empty_interface(), subject, on_return, [].into());
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    seed(&mut context, &[suspended]);
    let answer = form_comp_type(&mut context, answer).unwrap();
    check_comp(&mut context, handler, answer)
        .expect("a subject that performs nothing leaves the pure answer");
    assert_eq!(
        context.binders().depth(Zone::Intuitionistic),
        BinderDepth::from(0_usize)
    );
}

#[test]
fn handle_against_unknown_answer()
{
    use gandr_core_term::control::EffectClause;
    use gandr_core_term::effect::EffectOp;
    use gandr_core_term::effect::EffectSig;
    let mut arena = CoreArena::new();
    let unit_type = arena.value_type_unit();
    let integer_type = arena.value_type_base(BaseType::Integer);
    let unknown = arena.comp_type_unknown();
    let signature = EffectSig::new("Ask".into(), [EffectOp {
        name: "ask".into(),
        payload: unit_type,
        reply: integer_type,
    }])
    .unwrap();
    let unit = arena.value_unit();
    let subject = arena.computation_perform(signature.clone(), "ask".into(), unit);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let on_return = arena.computation_return(bound);
    let reply = arena.value_literal(integer_literal());
    let replied = arena.computation_return(reply);
    let resumed = arena.computation_resume(bound, replied);
    let held = arena.computation_hole(HoleId::from(0_u32));
    let handler = |arena: &mut CoreArena, body| {
        arena.computation_handle(
            signature.clone(),
            subject,
            on_return,
            [EffectClause {
                operation: "ask".into(),
                body,
            }]
            .into(),
        )
    };
    let resuming = handler(&mut arena, resumed);
    let holed = handler(&mut arena, held);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let unknown = form_comp_type(&mut context, unknown).unwrap();
    for term in [resuming, holed] {
        check_comp(&mut context, term, unknown)
            .expect("a handler against the unknown answer checks through the matched returner");
        assert_eq!(
            context.binders().depth(Zone::Intuitionistic),
            BinderDepth::from(0_usize)
        );
    }
    assert_eq!(
        synthesise_comp(&mut context, resuming).unwrap_err(),
        CheckRefusal::NotSynthesisable {
            form: CheckingForm::Handle(resuming)
        }
    );
}

/// `F Integer` and `F^⟨State⟩ Integer`, the first below the second, in the
/// arena that holds them.
///
/// # Specification
/// trivial.
fn pure_and_stateful() -> (CoreArena, CompTypeId, CompTypeId)
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let pure = arena.comp_type_returner(integer);
    let stateful = arena
        .comp_type_returner_with_effects(integer, effect_row("State".into(), integer, integer));
    (arena, pure, stateful)
}

#[test]
fn reify_empty_stack_is_identity()
{
    let (mut arena, pure, _) = pure_and_stateful();
    let unit = arena.value_type_unit();
    let other = arena.comp_type_returner(unit);
    let stack = arena.value_reify([].into());
    let identity = arena.value_type_stack(pure, pure);
    let changed = arena.value_type_stack(pure, other);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let identity = form_value_type(&mut context, identity).unwrap();
    check_value(&mut context, stack, identity).expect("the empty stack delivers what it consumes");
    let changed = form_value_type(&mut context, changed).unwrap();
    assert!(matches!(
        check_value(&mut context, stack, changed),
        Err(CheckRefusal::TypeMismatch(_))
    ));
}

#[test]
fn reify_delivered_answer_subsumes_up()
{
    let (mut arena, pure, stateful) = pure_and_stateful();
    let stack = arena.value_reify([].into());
    let widened = arena.value_type_stack(pure, stateful);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let widened = form_value_type(&mut context, widened).unwrap();
    check_value(&mut context, stack, widened)
        .expect("the delivered pure answer subsumes to the effectful one");
}

#[test]
fn reify_delivered_answer_cannot_drop_a_row()
{
    let (mut arena, pure, stateful) = pure_and_stateful();
    let stack = arena.value_reify([].into());
    let dropped = arena.value_type_stack(stateful, pure);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let dropped = form_value_type(&mut context, dropped).unwrap();
    assert!(matches!(
        check_value(&mut context, stack, dropped),
        Err(CheckRefusal::TypeMismatch(_))
    ));
}

#[test]
fn reify_against_non_stack_type_is_stuck()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let stack = arena.value_reify([].into());
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let integer = form_value_type(&mut context, integer).unwrap();
    assert!(matches!(
        check_value(&mut context, stack, integer),
        Err(CheckRefusal::ShapeMismatch {
            at: TermNode::Value(at),
            wanted: ExpectedShape::Stack,
            ..
        }) if at == stack
    ));
}

#[test]
fn reify_interior_bind_frame_threads_the_accumulated_row()
{
    use gandr_core_term::control::StackFrame;
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let input_row = effect_row("Input".into(), integer, integer);
    let body_row = effect_row("Body".into(), integer, integer);
    let both = input_row.union(&body_row, &arena).expect("disjoint names");
    let input = arena.comp_type_returner_with_effects(integer, input_row);
    let output = arena.comp_type_returner_with_effects(integer, both);
    let laundered = arena.comp_type_returner_with_effects(integer, body_row.clone());
    let bound = arena.value_variable(Zone::Intuitionistic, 0_u32.into());
    let signature = body_row.signatures().next().expect("one interface").clone();
    let performed = arena.computation_perform(signature.clone(), "run".into(), bound);
    let passed_on = arena.computation_perform(signature, "run".into(), bound);
    let stack =
        arena.value_reify([StackFrame::Bind(performed), StackFrame::Bind(passed_on)].into());
    let threaded = arena.value_type_stack(input, output);
    let laundered = arena.value_type_stack(input, laundered);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let threaded = form_value_type(&mut context, threaded).unwrap();
    check_value(&mut context, stack, threaded)
        .expect("the later frame receives the interior frame's row");
    let laundered = form_value_type(&mut context, laundered).unwrap();
    assert!(matches!(
        check_value(&mut context, stack, laundered),
        Err(CheckRefusal::TypeMismatch(_))
    ));
    assert_eq!(
        context.binders().depth(Zone::Intuitionistic),
        BinderDepth::from(0_usize)
    );
}

#[test]
fn resume_of_a_non_stack_is_a_shape_mismatch()
{
    let mut arena = CoreArena::new();
    let zero = arena.value_literal(integer_literal());
    let fed = arena.computation_return(zero);
    let resume = arena.computation_resume(zero, fed);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    assert!(matches!(
        synthesise_comp(&mut context, resume),
        Err(CheckRefusal::ShapeMismatch {
            wanted: ExpectedShape::Stack,
            ..
        })
    ));
}

#[test]
fn resume_delivering_a_row_cannot_drop_it()
{
    let (mut arena, pure, stateful) = pure_and_stateful();
    let stack_type = arena.value_type_stack(stateful, stateful);
    let continuation = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let zero = arena.value_literal(integer_literal());
    let fed = arena.computation_return(zero);
    let resume = arena.computation_resume(continuation, fed);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    context.binders().open(Zone::Intuitionistic, stack_type);
    let pure = form_comp_type(&mut context, pure).unwrap();
    assert!(matches!(
        check_comp(&mut context, resume, pure),
        Err(CheckRefusal::TypeMismatch(_))
    ));
}

#[test]
fn resume_delivered_answer_subsumes_up()
{
    let (mut arena, pure, stateful) = pure_and_stateful();
    let stack_type = arena.value_type_stack(pure, pure);
    let continuation = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let zero = arena.value_literal(integer_literal());
    let fed = arena.computation_return(zero);
    let resume = arena.computation_resume(continuation, fed);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    context.binders().open(Zone::Intuitionistic, stack_type);
    let stateful = form_comp_type(&mut context, stateful).unwrap();
    check_comp(&mut context, resume, stateful)
        .expect("the delivered pure answer subsumes to the effectful one");
}

#[test]
fn resume_of_a_hole_infers_unknown()
{
    let mut arena = CoreArena::new();
    let hole = arena.value_hole(HoleId::from(0_u32));
    let zero = arena.value_literal(integer_literal());
    let fed = arena.computation_return(zero);
    let resume = arena.computation_resume(hole, fed);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let inferred = synthesise_comp(&mut context, resume)
        .expect("a hole in stack position localizes rather than cascading")
        .produced()
        .id();
    assert_eq!(
        context.arena().comp_type(inferred),
        Some(&CompType::Unknown)
    );
}

#[test]
fn reset_is_transparent_on_the_type()
{
    let (mut arena, pure, _) = pure_and_stateful();
    let unit = arena.value_type_unit();
    let other = arena.comp_type_returner(unit);
    let zero = arena.value_literal(integer_literal());
    let returned = arena.computation_return(zero);
    let reset = arena.computation_reset(returned);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let pure = form_comp_type(&mut context, pure).unwrap();
    check_comp(&mut context, reset, pure).expect("a reset checks at its body's answer");
    let other = form_comp_type(&mut context, other).unwrap();
    assert!(matches!(
        check_comp(&mut context, reset, other),
        Err(CheckRefusal::TypeMismatch(_))
    ));
}

#[test]
fn shift_binds_the_continuation_at_the_captured_type()
{
    let (mut arena, pure, _) = pure_and_stateful();
    let unit = arena.value_unit();
    let continuation = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let fed = arena.computation_return(unit);
    let resumed = arena.computation_resume(continuation, fed);
    let shift = arena.computation_shift(resumed);
    let reset = arena.computation_reset(shift);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let pure = form_comp_type(&mut context, pure).unwrap();
    assert!(matches!(
        check_comp(&mut context, reset, pure),
        Err(CheckRefusal::TypeMismatch(_))
    ));
    assert_eq!(
        context.binders().depth(Zone::Intuitionistic),
        BinderDepth::from(0_usize)
    );
}

#[test]
fn bind_unions_effect_rows()
{
    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let string = arena.value_type_base(BaseType::String);
    let first = arena.comp_type_returner_with_effects(unit, effect_row("IO".into(), unit, unit));
    let second =
        arena.comp_type_returner_with_effects(string, effect_row("State".into(), unit, string));
    let types = [
        arena.value_type_thunk(first),
        arena.value_type_thunk(second),
    ];
    let first_value = arena.value_constant(ConstantIndex::from(0_usize));
    let second_value = arena.value_constant(ConstantIndex::from(1_usize));
    let bound = arena.computation_force(first_value);
    let body = arena.computation_force(second_value);
    let bind = arena.computation_bind(bound, body);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    seed(&mut context, &types);
    let produced = synthesise_comp(&mut context, bind)
        .expect("compatible interfaces")
        .produced()
        .id();
    let Some(&gandr_core_term::CompType::Returner {
        result,
        ref effects,
    }) = context.arena().comp_type(produced)
    else {
        panic!("bind returner");
    };
    assert_eq!(result, string);
    assert_eq!(
        effects
            .signatures()
            .map(|signature| signature.name().as_ref())
            .collect::<Vec<_>>(),
        ["IO", "State"]
    );
    assert_eq!(
        context.binders().depth(Zone::Intuitionistic),
        BinderDepth::from(0_usize)
    );
}

#[test]
fn check_mode_bind_subsumes_the_accumulated_row()
{
    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let demanded = arena.comp_type_returner_with_effects(unit, effect_row("IO".into(), unit, unit));
    let pure = arena.comp_type_returner(unit);
    let suspended = arena.value_type_thunk(demanded);
    let producer = arena.value_constant(ConstantIndex::from(0_usize));
    let bound = arena.computation_force(producer);
    let returned = arena.value_unit();
    let body = arena.computation_return(returned);
    let bind = arena.computation_bind(bound, body);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    seed(&mut context, &[suspended]);
    let expected = form_comp_type(&mut context, pure).expect("pure returner");
    let Err(CheckRefusal::TypeMismatch(Mismatch::Computation {
        at,
        synthesised,
        expected: found,
    })) = check_comp(&mut context, bind, expected)
    else {
        panic!("the bound effect cannot disappear into a pure continuation");
    };
    assert_eq!((at, found), (bind, pure));
    assert!(
        matches!(context.arena().comp_type(synthesised), Some(gandr_core_term::CompType::Returner { effects, .. }) if effects.contains(&"IO".into()) == gandr_core_term::effect::EffectPresence::Present)
    );
    assert_eq!(
        context.binders().depth(Zone::Intuitionistic),
        BinderDepth::from(0_usize)
    );
}

#[test]
fn check_mode_bind_accepts_a_contained_row()
{
    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let io = effect_row("IO".into(), unit, unit);
    let allowed = io
        .union(&effect_row("State".into(), unit, unit), &arena)
        .expect("distinct interfaces");
    let demanded = arena.comp_type_returner_with_effects(unit, io);
    let answer = arena.comp_type_returner_with_effects(unit, allowed);
    let suspended = arena.value_type_thunk(demanded);
    let producer = arena.value_constant(ConstantIndex::from(0_usize));
    let bound = arena.computation_force(producer);
    let value = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let body = arena.computation_return(value);
    let bind = arena.computation_bind(bound, body);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    seed(&mut context, &[suspended]);
    let expected = form_comp_type(&mut context, answer).expect("rowful returner");
    assert!(check_comp(&mut context, bind, expected).is_ok());
    assert_eq!(
        context.binders().depth(Zone::Intuitionistic),
        BinderDepth::from(0_usize)
    );
}

#[test]
fn bind_refuses_conflicting_operation_types_without_replacing_a_signature()
{
    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let string = arena.value_type_base(BaseType::String);
    let first = arena.comp_type_returner_with_effects(unit, effect_row("IO".into(), unit, unit));
    let second = arena.comp_type_returner_with_effects(unit, effect_row("IO".into(), string, unit));
    let types = [
        arena.value_type_thunk(first),
        arena.value_type_thunk(second),
    ];
    let first_value = arena.value_constant(ConstantIndex::from(0_usize));
    let second_value = arena.value_constant(ConstantIndex::from(1_usize));
    let bound = arena.computation_force(first_value);
    let body = arena.computation_force(second_value);
    let bind = arena.computation_bind(bound, body);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    seed(&mut context, &types);
    assert_eq!(
        synthesise_comp(&mut context, bind).map(|found| found.produced().id()),
        Err(CheckRefusal::EffectSignatureConflict {
            at: bind,
            first,
            second
        })
    );
    assert_eq!(
        context.binders().depth(Zone::Intuitionistic),
        BinderDepth::from(0_usize)
    );
}

#[test]
fn a_bind_checks_against_the_expected_computation()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let string = arena.value_type_base(BaseType::String);
    let returns_integer = arena.comp_type_returner(integer);
    let returns_string = arena.comp_type_returner(string);
    let suspended_integer = arena.value_type_thunk(returns_integer);
    let produce = arena.value_constant(ConstantIndex::from(0_usize));
    let bound = arena.computation_force(produce);
    let variable = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let body = arena.computation_return(variable);
    let bind = arena.computation_bind(bound, body);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    seed(&mut context, &[suspended_integer]);
    let expected = form_comp_type(&mut context, returns_integer).unwrap();
    let wrong = form_comp_type(&mut context, returns_string).unwrap();

    assert_eq!(
        check_comp(&mut context, bind, expected).map(|evidence| evidence.conversions()),
        Ok(ConversionCount::from(1_usize)),
        "the body checks against the expected type, under the bound name"
    );
    assert_eq!(
        check_comp(&mut context, bind, wrong).map(|evidence| evidence.conversions()),
        Err(CheckRefusal::TypeMismatch(Mismatch::Value {
            at: variable,
            synthesised: integer,
            expected: string,
        })),
        "the bound name has the type its returner returns, whatever the bind is checked \
             against"
    );
    let found = synthesise_comp(&mut context, bind).map(|found| found.produced().id());
    let mut tally = ConversionCount::default();
    assert_eq!(
        found.and_then(|found| comp_bridge(&mut context, bind, found, returns_integer, &mut tally)),
        Ok(()),
        "a body returning the bound name synthesises the returner of its type, and so does the \
             bind"
    );
}

#[test]
fn a_bind_of_a_non_returner_is_a_shape_mismatch()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let returns_integer = arena.comp_type_returner(integer);
    let arrow = arena.comp_type_arrow(integer, returns_integer);
    let suspended_arrow = arena.value_type_thunk(arrow);
    let function = arena.value_constant(ConstantIndex::from(0_usize));
    let bound = arena.computation_force(function);
    let unit = arena.value_unit();
    let body = arena.computation_return(unit);
    let bind = arena.computation_bind(bound, body);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    seed(&mut context, &[suspended_arrow]);
    let expected = form_comp_type(&mut context, returns_integer).unwrap();
    let refusal = CheckRefusal::ShapeMismatch {
        at: TermNode::Computation(bound),
        wanted: ExpectedShape::Returner,
        found: TypeNode::Computation(arrow),
    };

    assert_eq!(
        synthesise_comp(&mut context, bind).map(|found| found.produced().id()),
        Err(refusal),
        "a bound function returns nothing to bind"
    );
    assert_eq!(
        check_comp(&mut context, bind, expected).map(|evidence| evidence.conversions()),
        Err(refusal),
        "the refusal is the bound computation's, whatever the bind is checked against"
    );
    assert_eq!(
        context.binders().depth(Zone::Intuitionistic),
        BinderDepth::from(0_usize),
        "a refused bind opened no binder"
    );
}

#[test]
fn an_ascription_checks_its_body_and_synthesises_its_type()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let string = arena.value_type_base(BaseType::String);
    let returns_integer = arena.comp_type_returner(integer);
    let returns_string = arena.comp_type_returner(string);
    let suspended_integer = arena.value_type_thunk(returns_integer);
    let returns_suspended = arena.comp_type_returner(suspended_integer);
    let produce = arena.value_constant(ConstantIndex::from(0_usize));
    let forced = arena.computation_force(produce);
    let returned = arena.computation_return(produce);
    let ascribed = arena.computation_ascribe(forced, returns_integer);
    let mistyped = arena.computation_ascribe(forced, returns_string);
    let checked_only = arena.computation_ascribe(returned, returns_suspended);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    seed(&mut context, &[suspended_integer]);

    assert_eq!(
        synthesise_comp(&mut context, ascribed).map(|found| found.produced().id()),
        Ok(returns_integer),
        "an ascription synthesises the type it states"
    );
    assert_eq!(
        synthesise_comp(&mut context, checked_only).map(|found| found.produced().id()),
        Ok(returns_suspended),
        "a return, which only checks, synthesises once ascribed"
    );
    assert_eq!(
        synthesise_comp(&mut context, mistyped).map(|found| found.produced().id()),
        Err(CheckRefusal::TypeMismatch(Mismatch::Computation {
            at: forced,
            synthesised: returns_integer,
            expected: returns_string,
        })),
        "a body of another type is refused against the stated one"
    );
    let expected = form_comp_type(&mut context, returns_integer).unwrap();
    let wrong = form_comp_type(&mut context, returns_string).unwrap();
    assert!(
        check_comp(&mut context, ascribed, expected).is_ok(),
        "an ascription checks against its own type"
    );
    assert_eq!(
        check_comp(&mut context, ascribed, wrong).map(|evidence| evidence.conversions()),
        Err(CheckRefusal::TypeMismatch(Mismatch::Computation {
            at: ascribed,
            synthesised: returns_integer,
            expected: returns_string,
        })),
        "checked elsewhere, the stated type crosses the bridge"
    );
}

#[test]
fn a_mismatched_literal_is_refused_with_both_types()
{
    let mut arena = CoreArena::new();
    let string = arena.value_type_base(BaseType::String);
    let integer_value = arena.value_literal(integer_literal());
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let expected = form_value_type(&mut context, string).unwrap();
    let refusal = check_value(&mut context, integer_value, expected).unwrap_err();
    assert_eq!(
        refusal,
        CheckRefusal::TypeMismatch(Mismatch::Value {
            at: integer_value,
            synthesised: context.atom(Atom::Integer).id(),
            expected: string,
        }),
        "the value bridge names the literal, the atom it synthesised and the type expected"
    );
    assert_eq!(
        refusal.classify(),
        FailureClass::MalformedSource,
        "a mismatch is the author's"
    );
}

#[test]
fn a_mismatched_application_is_refused_at_the_computation_bridge()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let string = arena.value_type_base(BaseType::String);
    let returns_integer = arena.comp_type_returner(integer);
    let returns_string = arena.comp_type_returner(string);
    let arrow = arena.comp_type_arrow(integer, returns_integer);
    let thunk_arrow = arena.value_type_thunk(arrow);
    let function = arena.value_constant(ConstantIndex::from(0_usize));
    let force = arena.computation_force(function);
    let argument = arena.value_literal(integer_literal());
    let application = arena.computation_application(force, argument);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    seed(&mut context, &[thunk_arrow]);
    let expected = form_comp_type(&mut context, returns_string).unwrap();
    let refusal = check_comp(&mut context, application, expected).unwrap_err();
    assert_eq!(
        refusal,
        CheckRefusal::TypeMismatch(Mismatch::Computation {
            at: application,
            synthesised: returns_integer,
            expected: returns_string,
        }),
        "the computation bridge names the application, its codomain and the type expected"
    );
    assert_eq!(
        refusal.classify(),
        FailureClass::MalformedSource,
        "a mismatch is the author's"
    );
}

#[test]
fn an_introduction_against_the_wrong_former_is_a_shape_mismatch()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let returns_integer = arena.comp_type_returner(integer);
    let arrow = arena.comp_type_arrow(integer, returns_integer);
    let integer_value = arena.value_literal(integer_literal());
    let returned = arena.computation_return(integer_value);
    let thunk = arena.value_thunk(returned);
    let lambda = arena.computation_lambda(returned);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let formed_integer = form_value_type(&mut context, integer).unwrap();
    let formed_returner = form_comp_type(&mut context, returns_integer).unwrap();
    let formed_arrow = form_comp_type(&mut context, arrow).unwrap();
    let refusals = [
        (
            check_value(&mut context, thunk, formed_integer),
            TermNode::Value(thunk),
            ExpectedShape::Thunk,
            TypeNode::Value(integer),
        ),
        (
            check_comp(&mut context, lambda, formed_returner),
            TermNode::Computation(lambda),
            ExpectedShape::Arrow,
            TypeNode::Computation(returns_integer),
        ),
        (
            check_comp(&mut context, returned, formed_arrow),
            TermNode::Computation(returned),
            ExpectedShape::Returner,
            TypeNode::Computation(arrow),
        ),
    ];
    for (outcome, at, wanted, found) in refusals {
        let refusal = outcome.unwrap_err();
        assert_eq!(
            refusal,
            CheckRefusal::ShapeMismatch { at, wanted, found },
            "an introduction names the former it needed and the type it met"
        );
        assert_eq!(
            refusal.classify(),
            FailureClass::MalformedSource,
            "a shape mismatch is the author's"
        );
    }
}

#[test]
fn an_elimination_of_the_wrong_former_is_a_shape_mismatch()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let returns_integer = arena.comp_type_returner(integer);
    let thunk_returner = arena.value_type_thunk(returns_integer);
    let integer_value = arena.value_literal(integer_literal());
    let forced_literal = arena.computation_force(integer_value);
    let suspended = arena.value_constant(ConstantIndex::from(0_usize));
    let head = arena.computation_force(suspended);
    let application = arena.computation_application(head, integer_value);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    seed(&mut context, &[thunk_returner]);
    assert_eq!(
        synthesise_comp(&mut context, forced_literal),
        Err(CheckRefusal::ShapeMismatch {
            at: TermNode::Value(integer_value),
            wanted: ExpectedShape::Thunk,
            found: TypeNode::Value(context.atom(Atom::Integer).id()),
        }),
        "a forced value that synthesises no thunk type is refused at the value"
    );
    assert_eq!(
        synthesise_comp(&mut context, application),
        Err(CheckRefusal::ShapeMismatch {
            at: TermNode::Computation(head),
            wanted: ExpectedShape::Arrow,
            found: TypeNode::Computation(returns_integer),
        }),
        "a head that synthesises no arrow is refused at the head"
    );
}

#[test]
fn a_two_bridge_check_crosses_the_boundary_twice()
{
    // def g : U (Integer -> F Integer) ;
    // def f : U (Integer -> F Integer) = thunk { \x. (force g) x } ;
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let returns_integer = arena.comp_type_returner(integer);
    let arrow = arena.comp_type_arrow(integer, returns_integer);
    let thunk_arrow = arena.value_type_thunk(arrow);
    let function = arena.value_constant(ConstantIndex::from(0_usize));
    let head = arena.computation_force(function);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let application = arena.computation_application(head, bound);
    let lambda = arena.computation_lambda(application);
    let body = arena.value_thunk(lambda);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    seed(&mut context, &[thunk_arrow]);
    let expected = form_value_type(&mut context, thunk_arrow).unwrap();
    assert_eq!(
        check_value(&mut context, body, expected).map(|evidence| evidence.conversions()),
        Ok(ConversionCount::from(2_usize)),
        "the bound argument crosses the value bridge and the application the computation \
             bridge, and nothing else converts"
    );
}

#[test]
fn an_exhausted_allowance_is_refused_with_the_budget()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let returns_integer = arena.comp_type_returner(integer);
    let arrow = arena.comp_type_arrow(integer, returns_integer);
    let thunk_arrow = arena.value_type_thunk(arrow);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let returned = arena.computation_return(bound);
    let lambda = arena.computation_lambda(returned);
    let identity = arena.value_thunk(lambda);
    let expected = {
        let mut forming = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        form_value_type(&mut forming, thunk_arrow).unwrap()
    };
    let budget = CheckBudget::from(3_usize);
    let mut context = CheckingContext::new(&mut arena, budget);
    assert_eq!(
        form_value_type(&mut context, thunk_arrow),
        Err(CheckRefusal::BudgetExceeded { budget }),
        "formation runs in the same machine, under the same allowance"
    );
    let refusal = check_value(&mut context, identity, expected).unwrap_err();
    assert_eq!(
        refusal,
        CheckRefusal::BudgetExceeded { budget },
        "a run longer than the allowance is refused, naming the allowance"
    );
    assert_eq!(
        refusal.classify(),
        FailureClass::EngineFault,
        "an exhausted allowance is the engine's"
    );
    assert_eq!(
        context.binders().depth(Zone::Intuitionistic),
        BinderDepth::from(0_usize),
        "the binder the cut-short run opened is closed"
    );
}

#[test]
fn a_refusal_keeps_the_rules_it_stood_inside()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let returns_integer = arena.comp_type_returner(integer);
    let suspended = arena.value_type_thunk(returns_integer);
    let zero = arena.value_literal(integer_literal());
    let forced = arena.computation_force(zero);
    let thunk = arena.value_thunk(forced);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let expected = form_value_type(&mut context, suspended).unwrap();
    let failure = check_value_with_failure(&mut context, thunk, expected).unwrap_err();
    assert_eq!(
        failure.refusal(),
        check_value(&mut context, thunk, expected).unwrap_err(),
        "the strict face projects the failure's refusal"
    );
    let at = |obligation: &Obligation| (obligation.role(), obligation.at(), obligation.expected());
    assert_eq!(
        failure.obligations().iter().map(at).collect::<Vec<_>>(),
        [
            (
                FrameRole::ThunkBody,
                CoreNode::Term(TermNode::Value(thunk)),
                Maybe::Present(TypeNode::Value(expected.id())),
            ),
            (
                FrameRole::CompBridge,
                CoreNode::Term(TermNode::Computation(forced)),
                Maybe::Present(TypeNode::Computation(returns_integer)),
            ),
            (
                FrameRole::Force,
                CoreNode::Term(TermNode::Computation(forced)),
                Maybe::Absent(judged::Absent::Synthesised),
            ),
        ],
        "the thunk's body rule, the bridge and the force, outermost first, \
             each on the node whose rule pushed it"
    );
    assert_eq!(
        failure.pursuit().stage(),
        Stage::Resuming,
        "the force refused on resuming with its value's type"
    );
    assert!(
        failure.hypotheses().is_empty(),
        "no binder stands between the thunk and the force"
    );
    assert_eq!(
        failure.types().first().copied(),
        Some(TypeNode::Value(context.atom(Atom::Integer).id())),
        "the type the force found, which the refusal compares, is named first"
    );
    assert_eq!(
        context.depth(Zone::Intuitionistic),
        BinderDepth::from(0_usize),
        "the failure is read before the binders close"
    );
}

#[test]
fn a_refusal_under_a_bind_keeps_its_hypothesis()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let string = arena.value_type_base(BaseType::String);
    let returns_integer = arena.comp_type_returner(integer);
    let returns_string = arena.comp_type_returner(string);
    let suspended_integer = arena.value_type_thunk(returns_integer);
    let suspended_string = arena.value_type_thunk(returns_string);
    let produce = arena.value_constant(ConstantIndex::from(0_usize));
    let bound = arena.computation_force(produce);
    let variable = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let body = arena.computation_return(variable);
    let bind = arena.computation_bind(bound, body);
    let thunk = arena.value_thunk(bind);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    seed(&mut context, &[suspended_integer]);
    let expected = form_value_type(&mut context, suspended_string).unwrap();
    let failure = check_value_with_failure(&mut context, thunk, expected).unwrap_err();
    assert_eq!(
        failure.refusal(),
        CheckRefusal::TypeMismatch(Mismatch::Value {
            at: variable,
            synthesised: integer,
            expected: string,
        }),
        "the bound name has the returned type, not the expected one"
    );
    let rules = failure
        .obligations()
        .iter()
        .map(|obligation| (obligation.role(), obligation.at(), obligation.binders()))
        .collect::<Vec<_>>();
    assert_eq!(
        rules,
        [
            (
                FrameRole::ThunkBody,
                CoreNode::Term(TermNode::Value(thunk)),
                &[][..]
            ),
            (
                FrameRole::BindBody,
                CoreNode::Term(TermNode::Computation(bind)),
                &[integer][..]
            ),
            (
                FrameRole::ReturnValue,
                CoreNode::Term(TermNode::Computation(body)),
                &[][..]
            ),
            (
                FrameRole::ValueBridge,
                CoreNode::Term(TermNode::Value(variable)),
                &[][..]
            ),
        ],
        "the bind's body rule holds the one hypothesis it opened; the bridge \
             that refused is innermost"
    );
    assert_eq!(failure.hypotheses(), [integer], "one hypothesis is open");
    assert_eq!(
        failure.pursuit(),
        Pursuit::new(
            CoreNode::Term(TermNode::Value(variable)),
            Maybe::Present(TypeNode::Value(string)),
            Stage::Resuming,
        ),
        "the bridge's own goal is the one under way"
    );
    assert_eq!(
        context.depth(Zone::Intuitionistic),
        BinderDepth::from(0_usize),
        "the binder is closed after the failure is read"
    );
}

#[test]
fn a_refusal_under_binders_leaves_the_context_as_found()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let returns_integer = arena.comp_type_returner(integer);
    let inner = arena.comp_type_arrow(integer, returns_integer);
    let outer = arena.comp_type_arrow(integer, inner);
    let escaping = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(5_u32));
    let returns_escaping = arena.computation_return(escaping);
    let inner_lambda = arena.computation_lambda(returns_escaping);
    let outer_lambda = arena.computation_lambda(inner_lambda);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let expected = form_comp_type(&mut context, outer).unwrap();
    let refusal = check_comp(&mut context, outer_lambda, expected).unwrap_err();
    assert_eq!(
        refusal,
        CheckRefusal::UnboundIndex {
            at: escaping,
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(5_u32),
            depth: BinderDepth::from(2_usize),
        },
        "the variable is refused under the two binders the lambdas opened"
    );
    assert_eq!(
        refusal.classify(),
        FailureClass::EngineFault,
        "an unbound index is the producer's fault"
    );
    assert_eq!(
        synthesise_value(&mut context, escaping),
        Err(CheckRefusal::UnboundIndex {
            at: escaping,
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(5_u32),
            depth: BinderDepth::from(0_usize),
        }),
        "the next judgement in the context starts under no binder"
    );
}

#[test]
fn a_dangling_term_is_refused_as_a_fault()
{
    let mut arena = CoreArena::new();
    let dangling = dangling_value();
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let refusal = synthesise_value(&mut context, dangling).unwrap_err();
    assert_eq!(
        refusal,
        CheckRefusal::DanglingNode {
            node: CoreNode::Term(TermNode::Value(dangling)),
        },
        "an id the arena does not hold is refused rather than read"
    );
    assert_eq!(
        refusal.classify(),
        FailureClass::EngineFault,
        "a dangling id is the caller's fault, not the author's"
    );
}

#[test]
fn a_result_of_the_wrong_kind_is_a_machine_fault()
{
    let mut arena = CoreArena::new();
    let unit_type = arena.value_type_unit();
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    assert_eq!(
        checked(
            Produced::ValueType(unit_type.into()),
            ConversionCount::default()
        ),
        Err(CheckRefusal::MachineInvariant),
        "a check run that ends on a type is reported, not trusted"
    );
    let mut machine = Machine {
        context: &mut context,
        frames: Vec::new(),
        owner: Goal::Form(TypeNode::Value(unit_type)),
        native_types: Vec::new(),
        conversions: ConversionCount::default(),
        remaining: 1_usize,
        marking: Marking::Strict,
        anchors: Vec::new(),
        marks: Vec::new(),
        sessions: Sessions::new(BinderDepth::default()),
        root: Maybe::Absent(crate::respect::root::Absent::Unmarked),
        staged_motives: Vec::new(),
    };
    let refusal = machine
        .resume(Frame::LambdaBody, Produced::ValueType(unit_type.into()))
        .unwrap_err();
    assert_eq!(
        refusal,
        CheckRefusal::MachineInvariant,
        "a frame handed a result of another kind reports the miscount"
    );
    assert_eq!(
        refusal.classify(),
        FailureClass::EngineFault,
        "a machine invariant is the engine's"
    );
}

#[test]
fn machine_bookkeeping_preserves_zero_and_one_boundaries()
{
    let mut arena = CoreArena::new();
    let unit_type = arena.value_type_unit();
    let mut foreign = CoreArena::new();
    let foreign_unit = foreign.value_unit();
    let absent_comp = foreign.computation_return(foreign_unit);
    let absent_value = dangling_value();
    let budget = CheckBudget::from(1_usize);
    let mut context = CheckingContext::new(&mut arena, budget);
    let mut machine = Machine {
        context: &mut context,
        frames: Vec::new(),
        owner: Goal::Form(TypeNode::Value(unit_type)),
        native_types: Vec::new(),
        conversions: ConversionCount::default(),
        remaining: 1,
        marking: Marking::Strict,
        anchors: Vec::new(),
        marks: Vec::new(),
        sessions: Sessions::new(BinderDepth::default()),
        root: Maybe::Absent(crate::respect::root::Absent::Unmarked),
        staged_motives: Vec::new(),
    };
    assert_eq!(machine.charge(), Ok(()));
    assert_eq!(machine.remaining, 0);
    assert_eq!(
        machine.charge(),
        Err(CheckRefusal::BudgetExceeded { budget })
    );
    assert_eq!(machine.remaining, 0);
    assert_eq!(machine.close(), Err(CheckRefusal::MachineInvariant));
    machine
        .context
        .binders()
        .open(Zone::Intuitionistic, unit_type);
    assert_eq!(machine.close(), Ok(()));
    assert_eq!(
        machine.context.depth(Zone::Intuitionistic),
        BinderDepth::default()
    );
    machine
        .context
        .binders()
        .open(Zone::Intuitionistic, unit_type);
    machine.unwind(BinderDepth::default());
    assert_eq!(
        machine.context.depth(Zone::Intuitionistic),
        BinderDepth::default()
    );
    assert_eq!(
        machine.value(absent_value),
        Err(CheckRefusal::DanglingNode {
            node: CoreNode::Term(TermNode::Value(absent_value))
        })
    );
    assert_eq!(
        machine.computation(absent_comp),
        Err(CheckRefusal::DanglingNode {
            node: CoreNode::Term(TermNode::Computation(absent_comp))
        })
    );
    assert_eq!(
        machine.raises(unit_type),
        Err(CheckRefusal::MachineInvariant)
    );
}

#[test]
fn lift_formation_distinguishes_below_equal_and_above()
{
    let mut arena = CoreArena::new();
    let natural = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let below = arena.value_type_lift(natural, Level::zero());
    let equal = arena.value_type_lift(natural, Level::constant(LevelConstant::from(1_u64)));
    let above = arena.value_type_lift(natural, Level::constant(LevelConstant::from(2_u64)));
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    for at in [below, equal] {
        assert_eq!(
            form_value_type(&mut context, at),
            Err(CheckRefusal::OutOfFragment {
                at: CoreNode::Type(TypeNode::Value(at)),
                former: UnadmittedFormer::TypeLift
            })
        );
    }
    assert_eq!(
        form_value_type(&mut context, above).map(crate::formation::FormedValueType::id),
        Ok(above)
    );
}

/// The universe a judged type stands at, read off the arena.
///
/// # Specification
/// - requires: `value_type` names a universe in the context arena.
/// - ensures: its stored sort and level, without changing either.
/// - panics: the id names no universe.
///
/// # Adequacy
/// - hypothesis: L3 — quoted atoms, returners and universes expose exact sorts
///   and levels, separating wrong universe-family selection and successor loss
///   within this finite quote table.
/// - witness: `judgement::tests::a_universe_classifies_one_level_up_in_the_positive_sort`
#[spec(
        requires: matches!(context.arena().value_type(value_type), Some(ValueType::Universe { .. })),
        ensures: |ret| matches!(context.arena().value_type(value_type), Some(ValueType::Universe { sort, level }) if ret.0 == *sort && ret.1 == *level),
    )]
fn universe_of(
    context: &CheckingContext<'_>,
    value_type: ValueTypeId,
) -> (Sort, Level)
{
    match context.arena().value_type(value_type) {
        Some(&ValueType::Universe { sort, ref level }) => (sort, level.clone()),
        other => panic!("a universe was synthesised, not {other:?}"),
    }
}

#[test]
fn a_universe_classifies_one_level_up_in_the_positive_sort()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let returns_integer = arena.comp_type_returner(integer);
    let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let negative = arena.value_type_universe(Sort::Ground(GroundSort::Computation), Level::zero());
    let quoted_small = arena.value_quote(small);
    let quoted_negative = arena.value_quote(negative);
    let quoted_integer = arena.value_quote(integer);
    let quoted_returner = arena.value_quote_computation(returns_integer);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let one = Level::constant(LevelConstant::from(1_u64));
    let positive_one = (Sort::Ground(GroundSort::Value), one);
    let rows = [
        (quoted_small, positive_one.clone()),
        (quoted_negative, positive_one),
        (
            quoted_integer,
            (Sort::Ground(GroundSort::Value), Level::zero()),
        ),
        (
            quoted_returner,
            (Sort::Ground(GroundSort::Computation), Level::zero()),
        ),
    ];
    for (quote, universe) in rows {
        let synthesised = synthesise_value(&mut context, quote).unwrap();
        assert_eq!(
            universe_of(&context, synthesised.produced().id()),
            universe,
            "a quote has the universe of its type's family at the type's level"
        );
    }
}

#[test]
fn a_value_type_in_a_computation_universe_is_a_sort_mismatch()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let negative = arena.value_type_universe(Sort::Ground(GroundSort::Computation), Level::zero());
    let quoted = arena.value_quote(integer);
    let code = arena.value_constant(ConstantIndex::from(0_usize));
    let decoded = arena.comp_type_element(code, Level::zero());
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    seed(&mut context, &[small]);
    let expected = form_value_type(&mut context, negative).unwrap();
    let refusal = check_value(&mut context, quoted, expected).unwrap_err();
    assert!(
        matches!(
            refusal,
            CheckRefusal::SortMismatch { at, expected, .. } if at == quoted && expected == negative
        ),
        "a value type's code is refused at the computation universe, not lifted into it: \
             {refusal:?}"
    );
    assert_eq!(
        refusal.classify(),
        FailureClass::MalformedSource,
        "a sort mismatch is the author's"
    );
    assert!(
        matches!(
            form_comp_type(&mut context, decoded),
            Err(CheckRefusal::SortMismatch { at, synthesised, .. }) if at == code && synthesised == small
        ),
        "a computation decode of a value code is refused when formation crosses the decode \
             bridge"
    );
}

#[test]
fn a_bind_whose_type_mentions_its_binder_is_refused()
{
    // def mk : U (F Type) ; def pick : U ((A : Type) -> F El A) ;
    // x <- force mk ; (force pick) x
    let mut arena = CoreArena::new();
    let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let returns_small = arena.comp_type_returner(small);
    let make = arena.value_type_thunk(returns_small);
    let bound_code = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let decoded = arena.value_type_element(bound_code, Level::zero());
    let returns_decoded = arena.comp_type_returner(decoded);
    let pi = arena.comp_type_pi(small, returns_decoded);
    let pick = arena.value_type_thunk(pi);
    let mk = arena.value_constant(ConstantIndex::from(0_usize));
    let picker = arena.value_constant(ConstantIndex::from(1_usize));
    let bound = arena.computation_force(mk);
    let head = arena.computation_force(picker);
    let variable = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let body = arena.computation_application(head, variable);
    let bind = arena.computation_bind(bound, body);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    seed(&mut context, &[make, pick]);
    let refusal = synthesise_comp(&mut context, bind).unwrap_err();
    assert!(
        matches!(refusal, CheckRefusal::DependentBind { at, .. } if at == bind),
        "the body has `F El x`, which has no reading outside the bind: {refusal:?}"
    );
    assert_eq!(
        refusal.classify(),
        FailureClass::MalformedSource,
        "a dependent bind is the author's"
    );
    assert_eq!(
        context.binders().depth(Zone::Intuitionistic),
        BinderDepth::from(0_usize),
        "the refused bind closed the binder it opened"
    );
}

#[test]
fn a_dependent_application_instantiates_its_codomain_at_the_argument()
{
    // def id : U ((A : Type) -> F El A) ;
    // def lifted : U ((A : Type[+, 1]) -> F El A) ;
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let returns_integer = arena.comp_type_returner(integer);
    let one = Level::constant(LevelConstant::from(1_u64));
    let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let large = arena.value_type_universe(Sort::Ground(GroundSort::Value), one.clone());
    let bound_code = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let decoded = arena.value_type_element(bound_code, Level::zero());
    let returns_decoded = arena.comp_type_returner(decoded);
    let pi = arena.comp_type_pi(small, returns_decoded);
    let identity = arena.value_type_thunk(pi);
    let decoded_large = arena.value_type_element(bound_code, one.clone());
    let returns_large = arena.comp_type_returner(decoded_large);
    let large_pi = arena.comp_type_pi(large, returns_large);
    let lifting = arena.value_type_thunk(large_pi);
    let lifted_integer = arena.value_type_lift(integer, one);
    let returns_lifted = arena.comp_type_returner(lifted_integer);
    let function = arena.value_constant(ConstantIndex::from(0_usize));
    let lifter = arena.value_constant(ConstantIndex::from(1_usize));
    let code = arena.value_quote(integer);
    let head = arena.computation_force(function);
    let applied = arena.computation_application(head, code);
    let lifted_head = arena.computation_force(lifter);
    let lifted_code = arena.value_quote(integer);
    let lifted_applied = arena.computation_application(lifted_head, lifted_code);
    let returned = arena.computation_return(bound_code);
    let lambda = arena.computation_lambda(returned);
    let returns_small = arena.comp_type_returner(small);
    let small_identity = arena.comp_type_pi(small, returns_small);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    seed(&mut context, &[identity, lifting]);
    let expected = form_comp_type(&mut context, returns_integer).unwrap();
    assert!(
        check_comp(&mut context, applied, expected).is_ok(),
        "applying at the code of Integer has F Integer: the decode of a quote is its type"
    );
    assert!(
        check_comp(&mut context, lifted_applied, expected).is_err(),
        "a small code at a large domain is read at its lift, not as itself"
    );
    let lifted = form_comp_type(&mut context, returns_lifted).unwrap();
    assert!(
        check_comp(&mut context, lifted_applied, lifted).is_ok(),
        "the codomain is instantiated at the lifted code"
    );
    let identity_type = form_comp_type(&mut context, small_identity).unwrap();
    assert!(
        check_comp(&mut context, lambda, identity_type).is_ok(),
        "a lambda checks against a dependent arrow, its body against the codomain under the \
             binder"
    );
}

#[test]
fn a_family_at_a_call_argument_converts_with_the_type_written_with_it_720()
{
    // def ext : U (Integer -> F Integer) ;
    // def tm : U (Integer -> F Type) ;
    // def q : U ((g : Integer) -> F El⟨c ← ext(g); tm(c)⟩) ;
    // def use : U ((a : Integer) -> El⟨tm(a)⟩ -> F Unit) ;
    // use(ext(0), q(0)) : F Unit
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let returns_integer = arena.comp_type_returner(integer);
    let extending = arena.comp_type_arrow(integer, returns_integer);
    let extending = arena.value_type_thunk(extending);
    let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let returns_small = arena.comp_type_returner(small);
    let family = arena.comp_type_arrow(integer, returns_small);
    let family = arena.value_type_thunk(family);
    let variable = |arena: &mut CoreArena, index: u32| {
        arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index))
    };
    let at = |arena: &mut CoreArena, constant: usize, argument: ValueId| {
        let head = arena.value_constant(ConstantIndex::from(constant));
        let forced = arena.computation_force(head);
        arena.computation_application(forced, argument)
    };
    // `q`'s codomain as the lowering writes it: the call bound ahead.
    let g = variable(&mut arena, 0);
    let ahead = at(&mut arena, 0, g);
    let c = variable(&mut arena, 0);
    let read = at(&mut arena, 1, c);
    let bound = arena.computation_bind(ahead, read);
    let code = arena.value_returned(bound);
    let decoded = arena.value_type_element(code, Level::zero());
    let returns_decoded = arena.comp_type_returner(decoded);
    let point = arena.comp_type_pi(integer, returns_decoded);
    let point = arena.value_type_thunk(point);
    // `use`'s second domain, the family at its first binder.
    let a = variable(&mut arena, 0);
    let read = at(&mut arena, 1, a);
    let code = arena.value_returned(read);
    let decoded = arena.value_type_element(code, Level::zero());
    let unit = arena.value_type_unit();
    let returns_unit = arena.comp_type_returner(unit);
    let consumer = arena.comp_type_arrow(decoded, returns_unit);
    let consumer = arena.comp_type_pi(integer, consumer);
    let consumer = arena.value_type_thunk(consumer);
    let zero = arena.value_literal(integer_literal());
    let extended = at(&mut arena, 0, zero);
    let extended = arena.value_nested(extended);
    let zero = arena.value_literal(integer_literal());
    let pointed = at(&mut arena, 2, zero);
    let pointed = arena.value_nested(pointed);
    let first = at(&mut arena, 3, extended);
    let applied = arena.computation_application(first, pointed);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    seed(&mut context, &[extending, family, point, consumer]);
    let expected = form_comp_type(&mut context, returns_unit).unwrap();
    let verdict = check_comp(&mut context, applied, expected);
    assert!(
        verdict.is_ok(),
        "`use`'s second domain at the call `ext(0)` is `El⟨c ← ext(0); tm(c)⟩`, as `q(0)`'s \
         type is written: {verdict:?}"
    );
}

#[test]
fn a_hole_synthesises_the_unknown_type_and_checks_against_any()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let returns_integer = arena.comp_type_returner(integer);
    let value_hole = arena.value_hole(HoleId::from(0_u32));
    let comp_hole = arena.computation_hole(HoleId::from(1_u32));
    let unit = arena.value_unit();
    let marked = arena.value_mark(MarkIndex::from(0_u32), unit);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let integer = form_value_type(&mut context, integer).unwrap();
    let returns_integer = form_comp_type(&mut context, returns_integer).unwrap();

    let found = synthesise_value(&mut context, value_hole).unwrap();
    assert_eq!(
        context.arena().value_type(found.produced().id()),
        Some(&ValueType::Unknown),
        "a value hole synthesises the unknown type"
    );
    assert_eq!(
        check_value(&mut context, value_hole, integer).map(|evidence| evidence.conversions()),
        Ok(ConversionCount::default()),
        "a value hole checks against Integer without crossing a bridge"
    );
    let found = synthesise_comp(&mut context, comp_hole).unwrap();
    assert_eq!(
        context.arena().comp_type(found.produced().id()),
        Some(&CompType::Unknown),
        "a computation hole synthesises the unknown computation type"
    );
    assert_eq!(
        check_comp(&mut context, comp_hole, returns_integer).map(|evidence| evidence.conversions()),
        Ok(ConversionCount::default()),
        "a computation hole checks against F Integer"
    );
    assert!(
        check_value(&mut context, unit, integer).is_err(),
        "the unit is no integer"
    );
    assert!(
        check_value(&mut context, marked, integer).is_ok(),
        "a marked unit is not judged again"
    );
    let found = synthesise_value(&mut context, marked).unwrap();
    assert_eq!(
        context.arena().value_type(found.produced().id()),
        Some(&ValueType::Unknown),
        "a mark synthesises the unknown type"
    );
}

#[test]
fn a_pattern_hole_at_a_leaf_leaves_the_match_undecided()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let returns_integer = arena.comp_type_returner(integer);
    let pattern = arena.computation_hole(HoleId::from(4_u32));
    let written = arena.computation_hole(HoleId::from(5_u32));
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let returns_integer = form_comp_type(&mut context, returns_integer).unwrap();
    assert_eq!(
        check_comp(&mut context, pattern, returns_integer).map(|evidence| evidence.conversions()),
        Ok(ConversionCount::default()),
        "a hole no pattern was written with checks"
    );
    context.keep_pattern_holes(&[HoleId::from(4_u32)]);
    assert_eq!(
        check_comp(&mut context, pattern, returns_integer).map(|evidence| evidence.conversions()),
        Err(CheckRefusal::UndecidedCoverage(pattern)),
        "the leaf of a pattern hole is refused in checking"
    );
    assert_eq!(
        synthesise_comp(&mut context, pattern).map(|found| found.produced().id()),
        Err(CheckRefusal::UndecidedCoverage(pattern)),
        "and in synthesis"
    );
    assert_eq!(
        check_comp(&mut context, written, returns_integer).map(|evidence| evidence.conversions()),
        Ok(ConversionCount::default()),
        "a term hole still checks beside it"
    );
}

#[test]
fn an_introduction_against_the_unknown_type_checks_its_parts()
{
    let mut arena = CoreArena::new();
    let unknown_value = arena.value_type_unknown();
    let unknown_comp = arena.comp_type_unknown();
    let zero = arena.value_literal(integer_literal());
    let unit = arena.value_unit();
    let returned = arena.computation_return(zero);
    let thunk = arena.value_thunk(returned);
    let pair = arena.value_tuple(&[zero, thunk]);
    let injected = arena.value_injection(Side::Left.into(), pair);
    let static_lambda = arena.value_static_lambda(zero);
    let innermost = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let returns_innermost = arena.computation_return(innermost);
    let lambda = arena.computation_lambda(returns_innermost);
    let forced = arena.computation_force(unit);
    let ill_thunk = arena.value_thunk(forced);
    let ill_pair = arena.value_tuple(&[zero, ill_thunk]);
    let nil = arena.value_list_nil();
    let cons = arena.value_list_cons(zero, nil);
    let stack = arena.value_reify(
        [
            gandr_core_term::control::StackFrame::Apply(zero),
            gandr_core_term::control::StackFrame::Project(gandr_kernel_term::Component::from(
                0_usize,
            )),
        ]
        .into(),
    );
    let lazy = arena.computation_with(&[returned, returned]);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let unknown_value = form_value_type(&mut context, unknown_value).unwrap();
    let unknown_comp = form_comp_type(&mut context, unknown_comp).unwrap();

    for (term, message) in [
        (
            thunk,
            "a thunk against the unknown type checks its body against the unknown",
        ),
        (
            pair,
            "a pair against the unknown type checks both components",
        ),
        (
            injected,
            "an injection against the unknown type checks its body",
        ),
        (
            static_lambda,
            "a static lambda against the unknown type checks its body",
        ),
        (nil, "nil against the unknown type reads an unknown element"),
        (
            cons,
            "a cell against the unknown type checks its head and tail",
        ),
        (
            stack,
            "a stack against the unknown type runs its frames over unknowns",
        ),
    ] {
        assert!(
            check_value(&mut context, term, unknown_value).is_ok(),
            "{message}"
        );
    }
    for (term, message) in [
        (
            lambda,
            "a lambda binds the unknown domain and checks its body",
        ),
        (
            returned,
            "a return against the unknown type checks its value",
        ),
        (
            lazy,
            "a lazy product against the unknown type checks its components",
        ),
    ] {
        assert!(
            check_comp(&mut context, term, unknown_comp).is_ok(),
            "{message}"
        );
    }
    assert!(
        matches!(
            check_value(&mut context, ill_pair, unknown_value),
            Err(CheckRefusal::ShapeMismatch { .. })
        ),
        "the parts are still judged: a force of the unit inside is refused"
    );
}

/// The integers the identity fixtures below compare.
#[derive(Clone, Copy)]
enum Numeral
{
    /// `5`.
    Five,
    /// `6`.
    Six,
}

/// The integer literal `numeral` spells.
///
/// # Specification
/// trivial.
fn integer(numeral: Numeral) -> gandr_kernel_term::Literal
{
    let digits = match numeral {
        Numeral::Five => "5",
        Numeral::Six => "6",
    };
    let magnitude = gandr_kernel_term::Magnitude::from_decimal_text(digits.into())
        .expect("the digits are decimal");
    gandr_kernel_term::Literal::Integer(gandr_kernel_term::IntegerLiteral::new(
        gandr_kernel_term::Sign::NonNegative,
        magnitude,
    ))
}

#[test]
fn reflexivity_checks_by_endpoint_conversion()
{
    // def id : U (Integer -> F Integer) = thunk { \x. return x } ;
    let mut arena = CoreArena::new();
    let integer_type = arena.value_type_base(BaseType::Integer);
    let returns_integer = arena.comp_type_returner(integer_type);
    let arrow = arena.comp_type_arrow(integer_type, returns_integer);
    let thunk_arrow = arena.value_type_thunk(arrow);
    let parameter = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let identity_return = arena.computation_return(parameter);
    let identity_lambda = arena.computation_lambda(identity_return);
    let identity_body = arena.value_thunk(identity_lambda);
    let five = arena.value_literal(integer(Numeral::Five));
    let also_five = arena.value_literal(integer(Numeral::Five));
    let six = arena.value_literal(integer(Numeral::Six));
    let here_five = arena.value_here(five);
    let same = arena.value_type_path(integer_type, also_five, also_five);
    let apart = arena.value_type_path(integer_type, five, six);
    // \y. return here(y), against (y : Integer) -> F Path(Integer, e, y).
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let here_bound = arena.value_here(bound);
    let returns_here = arena.computation_return(here_bound);
    let reflexive = arena.computation_lambda(returns_here);
    let identity = arena.value_constant(ConstantIndex::from(0_usize));
    let forced = arena.computation_force(identity);
    let applied = arena.computation_application(forced, bound);
    let unfolds = arena.value_returned(applied);
    let add = gandr_core_term::primitive::PRELUDE
        .iter()
        .copied()
        .find(|primitive| primitive.name().as_ref() == "add")
        .expect("native add");
    let zero = arena.value_literal(integer_literal());
    let redex = arena.computation_primitive(
        add,
        gandr_core_term::primitive::Arguments::Binary([bound, zero]),
    );
    let stuck = arena.value_returned(redex);
    let pis = [unfolds, stuck].map(|endpoint| {
        let path = arena.value_type_path(integer_type, endpoint, bound);
        let returns_path = arena.comp_type_returner(path);
        arena.comp_type_pi(integer_type, returns_path)
    });
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    seed(&mut context, &[thunk_arrow]);
    let declared = form_value_type(&mut context, thunk_arrow).unwrap();
    context.define(ConstantIndex::from(0_usize), declared, identity_body);
    let same = form_value_type(&mut context, same).unwrap();
    assert!(
        check_value(&mut context, here_five, same).is_ok(),
        "equal literals are the same syntax at either endpoint"
    );
    let apart = form_value_type(&mut context, apart).unwrap();
    assert_eq!(
        check_value(&mut context, here_five, apart),
        Err(CheckRefusal::EndpointMismatch {
            at: here_five,
            left: five,
            right: six,
        }),
        "a point apart from one endpoint is refused naming both endpoints"
    );
    let [unfolding, refuting] = pis.map(|pi| form_comp_type(&mut context, pi).unwrap());
    let unfolded = check_comp(&mut context, reflexive, unfolding);
    assert!(
        unfolded.is_ok(),
        "a definition applied to the variable converts to the variable by unfolding: \
             {unfolded:?}"
    );
    assert_eq!(
        check_comp(&mut context, reflexive, refuting),
        Err(CheckRefusal::EndpointMismatch {
            at: here_bound,
            left: stuck,
            right: bound,
        }),
        "native addition does not reduce on a variable, so `y + 0` is not `y`"
    );
    assert_eq!(
        CheckRefusal::EndpointMismatch {
            at: here_bound,
            left: stuck,
            right: bound,
        }
        .classify(),
        FailureClass::MalformedSource,
        "an endpoint mismatch is the author's"
    );
    assert_eq!(
        context.binders().depth(Zone::Intuitionistic),
        BinderDepth::from(0_usize),
        "the refused check closed the binder it opened"
    );
}

/// A point the normaliser cannot run meets its endpoints by syntax alone:
/// `here(y + 0)` checks against `Path(Integer, y + 0, y + 0)` whether the
/// three sides are one node or three of the same syntax.
#[test]
fn reflexivity_at_a_stuck_native_point_meets_it_by_syntax()
{
    let mut arena = CoreArena::new();
    let integer_type = arena.value_type_base(BaseType::Integer);
    let add = gandr_core_term::primitive::PRELUDE
        .iter()
        .copied()
        .find(|primitive| primitive.name().as_ref() == "add")
        .expect("native add");
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let zero = arena.value_literal(integer_literal());
    let [point, left, right] = [(), (), ()].map(|()| {
        let redex = arena.computation_primitive(
            add,
            gandr_core_term::primitive::Arguments::Binary([bound, zero]),
        );
        arena.value_returned(redex)
    });
    // \y. return here(y + 0), against (y : Integer) -> F Path(Integer, l, r).
    let [(shared, shared_type), (copied, copied_type)] =
        [(point, point), (left, right)].map(|(left, right)| {
            let here = arena.value_here(point);
            let returned = arena.computation_return(here);
            let lambda = arena.computation_lambda(returned);
            let path = arena.value_type_path(integer_type, left, right);
            let returns = arena.comp_type_returner(path);
            (lambda, arena.comp_type_pi(integer_type, returns))
        });
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    for (body, pi, sides) in [
        (shared, shared_type, "one node"),
        (copied, copied_type, "three nodes of one syntax"),
    ] {
        let pi = form_comp_type(&mut context, pi).unwrap();
        let checked = check_comp(&mut context, body, pi);
        assert!(
            checked.is_ok(),
            "a stuck native point meets endpoints that are {sides}: {checked:?}"
        );
    }
}

#[test]
fn identity_at_an_open_type_is_a_neutral_fibre()
{
    let mut arena = CoreArena::new();
    let integer_type = arena.value_type_base(BaseType::Integer);
    let returns_integer = arena.comp_type_returner(integer_type);
    let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let zero = arena.value_literal(integer_literal());
    let five = arena.value_literal(integer(Numeral::Five));
    let variable = |arena: &mut CoreArena, index: u32| {
        arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index))
    };
    let decode = |arena: &mut CoreArena, index| {
        let code = variable(arena, index);
        arena.value_type_element(code, Level::zero())
    };
    // tr(Integer, here(5), 0) at the closed carrier Integer.
    let here_five = arena.value_here(five);
    let closed = arena.computation_path_transport(integer_type, here_five, zero);
    // \x. tr(Integer, here(x), 0) at the decode of a quoted Integer, and at
    // the decode of `c : U`, a code with no body for a quote to reach.
    let point = variable(&mut arena, 0_u32);
    let here_point = arena.value_here(point);
    let transport = arena.computation_path_transport(integer_type, here_point, zero);
    let transport_lambda = arena.computation_lambda(transport);
    let quoted = arena.value_quote(integer_type);
    let through_quote = arena.value_type_element(quoted, Level::zero());
    let quoted_pi = arena.comp_type_pi(through_quote, returns_integer);
    let code = arena.value_constant(ConstantIndex::from(0_usize));
    let opaque = arena.value_type_element(code, Level::zero());
    let opaque_pi = arena.comp_type_pi(opaque, returns_integer);
    // (a : U) -> (x : El a) -> F Path(El a, x, x): the carrier reads `a`.
    let decoded = decode(&mut arena, 0_u32);
    let open = decode(&mut arena, 1_u32);
    let open_path = arena.value_type_path(open, point, point);
    let returns_open_path = arena.comp_type_returner(open_path);
    let point_pi = arena.comp_type_pi(decoded, returns_open_path);
    let path_pi = arena.comp_type_pi(small, point_pi);
    let returned_here = arena.computation_return(here_point);
    let under_point = arena.computation_lambda(returned_here);
    let reflexive = arena.computation_lambda(under_point);
    // \a. \x. tr(Integer, here(x), 0) against (a : U) -> (x : El a) -> F
    // Integer: the reflexivity synthesises at the decode of `a`.
    let under_code = arena.computation_lambda(transport_lambda);
    let integer_pi = arena.comp_type_pi(decoded, returns_integer);
    let code_pi = arena.comp_type_pi(small, integer_pi);
    // (a : U) -> (x y : El a) -> Path(El a, x, y) -> F Path(El a, x, y),
    // and the same returning Path(El a, y, x).
    let echoed = |arena: &mut CoreArena, (left, right): (u32, u32)| {
        let carrier = decode(arena, 3_u32);
        let left = variable(arena, left);
        let right = variable(arena, right);
        let result = arena.value_type_path(carrier, left, right);
        let returns = arena.comp_type_returner(result);
        let carrier = decode(arena, 2_u32);
        let x = variable(arena, 1_u32);
        let y = variable(arena, 0_u32);
        let premise = arena.value_type_path(carrier, x, y);
        let pi = arena.comp_type_pi(premise, returns);
        let element = decode(arena, 1_u32);
        let pi = arena.comp_type_pi(element, pi);
        let element = decode(arena, 0_u32);
        let pi = arena.comp_type_pi(element, pi);
        arena.comp_type_pi(small, pi)
    };
    let forward_pi = echoed(&mut arena, (2_u32, 1_u32));
    let reversed_pi = echoed(&mut arena, (1_u32, 2_u32));
    let returned_path = arena.computation_return(point);
    let echo = arena.computation_lambda(returned_path);
    let echo = arena.computation_lambda(echo);
    let echo = arena.computation_lambda(echo);
    let echo = arena.computation_lambda(echo);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    seed(&mut context, &[small]);
    let synthesised = synthesise_comp(&mut context, closed).unwrap();
    assert!(
        matches!(
            context.arena().comp_type(synthesised.produced().id()),
            Some(&CompType::Returner { result, .. }) if result == integer_type
        ),
        "a transport at a closed carrier returns the motive at the right endpoint"
    );
    let quoted_pi = form_comp_type(&mut context, quoted_pi).unwrap();
    assert!(
        check_comp(&mut context, transport_lambda, quoted_pi).is_ok(),
        "the decode of a quoted closed carrier is read through to the carrier"
    );
    let opaque_pi = form_comp_type(&mut context, opaque_pi).unwrap();
    let opaque_checked = check_comp(&mut context, transport_lambda, opaque_pi);
    assert!(
        opaque_checked.is_ok(),
        "a transport at the decode of a code no quote reaches checks: {opaque_checked:?}"
    );
    let path_pi = form_comp_type(&mut context, path_pi).unwrap();
    let reflexive_checked = check_comp(&mut context, reflexive, path_pi);
    assert!(
        reflexive_checked.is_ok(),
        "a path type whose carrier reads a binder outside it forms, and reflexivity \
             checks there: {reflexive_checked:?}"
    );
    let code_pi = form_comp_type(&mut context, code_pi).unwrap();
    let synthesised_checked = check_comp(&mut context, under_code, code_pi);
    assert!(
        synthesised_checked.is_ok(),
        "reflexivity synthesises at the decode of a type variable: {synthesised_checked:?}"
    );
    let forward_pi = form_comp_type(&mut context, forward_pi).unwrap();
    let forward_checked = check_comp(&mut context, echo, forward_pi);
    assert!(
        forward_checked.is_ok(),
        "a path inhabits its own neutral fibre by structural conversion: {forward_checked:?}"
    );
    let reversed_pi = form_comp_type(&mut context, reversed_pi).unwrap();
    assert!(
        matches!(
            check_comp(&mut context, echo, reversed_pi),
            Err(CheckRefusal::TypeMismatch(_))
        ),
        "two neutral fibres with their endpoints exchanged do not convert"
    );
    assert_eq!(
        context.binders().depth(Zone::Intuitionistic),
        BinderDepth::from(0_usize),
        "each check closed the binders it opened"
    );
}

/// The constants a telescope transport test reads, admitted at positions
/// `0..7`: `a b : Integer`, `p : Path(Integer, a, b)`, the start
/// `z₀ : Path(Integer, a, a)`, the finish `z₁ : Path(Integer, a, b)`, the
/// identity over the path `q : Path(Path(Integer, a, b), ⟨tr(y.
/// Path(Integer, a, y), p, z₀)⟩, z₁)`, the operand `v :
/// Path(Path(Integer, a, a), z₀, z₀)`; and the motive `Π (y : Integer).
/// Π (z : Path(Integer, a, y)). F Path(Path(Integer, a, y), z, z)`.
struct TelescopeScene
{
    /// The constants `[a, b, p, z₀, z₁, q, v]`.
    constants: [ValueId; 7],
    /// Their types, in order.
    types: [ValueTypeId; 7],
    /// The motive.
    motive: CompTypeId,
    /// `F C[b, z₁]`, the type the transport returns.
    target: CompTypeId,
    /// `F C[a, z₀]`, the type at the source.
    source: CompTypeId,
}

/// [`TelescopeScene`], minted in `arena`.
///
/// # Specification
/// trivial.
fn telescope_scene(arena: &mut CoreArena) -> TelescopeScene
{
    let integer_type = arena.value_type_base(BaseType::Integer);
    let constants = [0_usize, 1, 2, 3, 4, 5, 6]
        .map(|position| arena.value_constant(ConstantIndex::from(position)));
    let [source_point, target_point, path, start, finish, _, _] = constants;
    let variable = |arena: &mut CoreArena, index: u32| {
        arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index))
    };
    let path_type = arena.value_type_path(integer_type, source_point, target_point);
    let loop_type = arena.value_type_path(integer_type, source_point, source_point);
    let endpoint = variable(arena, 0_u32);
    let family = arena.value_type_path(integer_type, source_point, endpoint);
    let carried = arena.computation_path_transport(family, path, start);
    let carried = arena.value_returned(carried);
    let over_type = arena.value_type_path(path_type, carried, finish);
    let operand_type = arena.value_type_path(loop_type, start, start);
    let endpoint = variable(arena, 1_u32);
    let element = variable(arena, 0_u32);
    let fibre = arena.value_type_path(integer_type, source_point, endpoint);
    let body = arena.value_type_path(fibre, element, element);
    let returned = arena.comp_type_returner(body);
    let entry = arena.comp_type_pi(family, returned);
    let motive = arena.comp_type_pi(integer_type, entry);
    let target_type = arena.value_type_path(path_type, finish, finish);
    let target = arena.comp_type_returner(target_type);
    let source = arena.comp_type_returner(operand_type);
    TelescopeScene {
        constants,
        types: [
            integer_type,
            integer_type,
            path_type,
            loop_type,
            path_type,
            over_type,
            operand_type,
        ],
        motive,
        target,
        source,
    }
}

#[test]
fn a_telescope_transport_replays_its_substitution_law()
{
    let mut arena = CoreArena::new();
    let scene = telescope_scene(&mut arena);
    let [_, _, p, start, _, over, operand] = scene.constants;
    let transport = arena.computation_telescope_transport(scene.motive, p, start, over, operand);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    seed(&mut context, &scene.types);
    let synthesised = synthesise_comp(&mut context, transport);
    assert!(
        synthesised.is_ok(),
        "a transport over a two-entry telescope synthesises: {synthesised:?}"
    );
    let target = form_comp_type(&mut context, scene.target).unwrap();
    let checked = check_comp(&mut context, transport, target);
    assert!(
        checked.is_ok(),
        "the result is the motive at the path's target and the identity's finish, \
             substituted outer binder first: {checked:?}"
    );
    let source = form_comp_type(&mut context, scene.source).unwrap();
    assert!(
        matches!(
            check_comp(&mut context, transport, source),
            Err(CheckRefusal::TypeMismatch(Mismatch::Computation { .. }))
        ),
        "the motive at the path's source is not the result"
    );
    let misplaced =
        context
            .arena_mut()
            .computation_telescope_transport(scene.motive, p, start, over, start);
    assert!(
        matches!(
            synthesise_comp(&mut context, misplaced),
            Err(CheckRefusal::TypeMismatch(Mismatch::Value { at, .. })) if at == start
        ),
        "the operand is checked at the motive over the source"
    );
}

#[test]
fn a_one_entry_telescope_motive_is_a_shape_mismatch()
{
    let mut arena = CoreArena::new();
    let scene = telescope_scene(&mut arena);
    let [_, _, p, start, _, over, operand] = scene.constants;
    let [integer_type, ..] = scene.types;
    let returns_integer = arena.comp_type_returner(integer_type);
    let one_entry = arena.comp_type_pi(integer_type, returns_integer);
    let transport = arena.computation_telescope_transport(one_entry, p, start, over, operand);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    seed(&mut context, &scene.types);
    assert!(
        matches!(
            synthesise_comp(&mut context, transport),
            Err(CheckRefusal::ShapeMismatch {
                at: TermNode::Computation(at),
                wanted: ExpectedShape::Telescope,
                ..
            }) if at == transport
        ),
        "a motive with one entry is refused by name"
    );
}

#[test]
fn an_identity_not_over_the_path_is_refused()
{
    let mut arena = CoreArena::new();
    let scene = telescope_scene(&mut arena);
    let [_, _, p, start, finish, _, operand] = scene.constants;
    let [_, _, path_type, ..] = scene.types;
    let stray_type = arena.value_type_path(path_type, finish, finish);
    let stray = arena.value_constant(ConstantIndex::from(7_usize));
    let transport = arena.computation_telescope_transport(scene.motive, p, start, stray, operand);
    let mut types = scene.types.to_vec();
    types.push(stray_type);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    seed(&mut context, &types);
    let refused = synthesise_comp(&mut context, transport);
    assert!(
        matches!(
            refused,
            Err(CheckRefusal::NotOver { at, synthesised, .. })
                if at == stray && synthesised == stray_type
        ),
        "an identity that does not start at the transported start is refused by name: \
             {refused:?}"
    );
    assert_eq!(
        refused.map(|_| ()).map_err(|refusal| refusal.classify()),
        Err(FailureClass::MalformedSource),
        "an identity not over its path is the author's"
    );
}

/// The constants a dependent pair test reads, admitted at positions
/// `0..6`: `a b : Integer`, `r : Path(Integer, a, a)`, `s : Σ (n :
/// Integer). Path(Integer, n, n)`, `r₂ : Path(Integer, a, a)` and `q :
/// Path(Σ…, #{a, r}, #{a, r})`; that Σ, and the pair `#{a, r}`.
struct SigmaScene
{
    /// The constants `[a, b, r, s, r₂, q]`.
    constants: [ValueId; 6],
    /// Their types, in order.
    types: [ValueTypeId; 6],
    /// `Σ (n : Integer). Path(Integer, n, n)`.
    sigma: ValueTypeId,
    /// The pair `#{a, r}`.
    pair: ValueId,
}

/// [`SigmaScene`], minted in `arena`.
///
/// # Specification
/// trivial.
fn sigma_scene(arena: &mut CoreArena) -> SigmaScene
{
    let integer = arena.value_type_base(BaseType::Integer);
    let constants = [0_usize, 1, 2, 3, 4, 5]
        .map(|position| arena.value_constant(ConstantIndex::from(position)));
    let [a, _, r, ..] = constants;
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let family = arena.value_type_path(integer, bound, bound);
    let sigma = arena.value_type_sigma(integer, family);
    let loop_a = arena.value_type_path(integer, a, a);
    let pair = arena.value_tuple(&[a, r]);
    let identity = arena.value_type_path(sigma, pair, pair);
    SigmaScene {
        constants,
        types: [integer, integer, loop_a, sigma, loop_a, identity],
        sigma,
        pair,
    }
}

/// `⟨value.index⟩`: a tuple projection read as the value it returns.
///
/// # Specification
/// trivial.
fn projected(
    arena: &mut CoreArena,
    value: ValueId,
    index: gandr_kernel_term::Component,
) -> ValueId
{
    let projection = arena.computation_tuple_projection(value, index);
    arena.value_returned(projection)
}

#[test]
fn a_pair_checks_against_a_dependent_pair_at_its_first_components_fibre()
{
    let mut arena = CoreArena::new();
    let scene = sigma_scene(&mut arena);
    let [_, b, r, ..] = scene.constants;
    let skewed = arena.value_tuple(&[b, r]);
    let triple = arena.value_tuple(&[b, r, r]);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    seed(&mut context, &scene.types);
    let sigma = form_value_type(&mut context, scene.sigma).unwrap();
    let checked = check_value(&mut context, scene.pair, sigma);
    assert!(
        checked.is_ok(),
        "`r : Path(Integer, a, a)` lies in the fibre over `a`: {checked:?}"
    );
    assert!(
        matches!(
            check_value(&mut context, skewed, sigma),
            Err(CheckRefusal::TypeMismatch(_))
        ),
        "the same second component over `b` lies in another fibre"
    );
    assert!(
        matches!(
            check_value(&mut context, triple, sigma),
            Err(CheckRefusal::ShapeMismatch { at, wanted: ExpectedShape::Sigma, .. })
                if at == TermNode::Value(triple)
        ),
        "a dependent pair has two components"
    );
    let synthesised = synthesise_value(&mut context, scene.pair)
        .map(|found| found.produced().id())
        .unwrap();
    assert!(
        matches!(
            context.arena().value_type(synthesised),
            Some(ValueType::Product(parts)) if parts.len() == 2
        ),
        "a pair with no type to check against synthesises the product, never a Σ"
    );
}

#[test]
fn a_projection_of_a_dependent_pair_reads_its_second_factor_at_the_first()
{
    let mut arena = CoreArena::new();
    let scene = sigma_scene(&mut arena);
    let [a, _, r, s, ..] = scene.constants;
    let [integer, ..] = scene.types;
    let first = arena.computation_tuple_projection(s, gandr_kernel_term::Component::from(0_usize));
    let second = arena.computation_tuple_projection(s, gandr_kernel_term::Component::from(1_usize));
    let off_path =
        arena.computation_tuple_projection(r, gandr_kernel_term::Component::from(0_usize));
    let at_first = projected(&mut arena, s, gandr_kernel_term::Component::from(0_usize));
    let fibre = arena.value_type_path(integer, at_first, at_first);
    let fibre = arena.comp_type_returner(fibre);
    let elsewhere = arena.value_type_path(integer, a, a);
    let elsewhere = arena.comp_type_returner(elsewhere);
    let returns_integer = arena.comp_type_returner(integer);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    seed(&mut context, &scene.types);
    let returns_integer = form_comp_type(&mut context, returns_integer).unwrap();
    assert!(
        check_comp(&mut context, first, returns_integer).is_ok(),
        "the first projection returns the first factor"
    );
    let fibre = form_comp_type(&mut context, fibre).unwrap();
    let checked = check_comp(&mut context, second, fibre);
    assert!(
        checked.is_ok(),
        "the second returns the second factor at the first projection: {checked:?}"
    );
    let elsewhere = form_comp_type(&mut context, elsewhere).unwrap();
    assert!(
        matches!(
            check_comp(&mut context, second, elsewhere),
            Err(CheckRefusal::TypeMismatch(_))
        ),
        "and at no other first component"
    );
    assert!(
        matches!(
            synthesise_comp(&mut context, off_path),
            Err(CheckRefusal::ShapeMismatch { .. })
        ),
        "a projection of a type that is no pair is a shape mismatch"
    );
}

#[test]
fn a_dependent_split_synthesises_its_motive_at_the_scrutinee()
{
    let mut arena = CoreArena::new();
    let scene = sigma_scene(&mut arena);
    let [a, _, _, s, ..] = scene.constants;
    let [integer, ..] = scene.types;
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let first_bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let at_first = projected(
        &mut arena,
        bound,
        gandr_kernel_term::Component::from(0_usize),
    );
    let motive = arena.value_type_path(integer, at_first, at_first);
    let motive = arena.comp_type_returner(motive);
    let returns_second = arena.computation_return(bound);
    let arity = gandr_core_term::ComponentCount::from(2_usize);
    let split = arena.computation_dependent_split(s, arity, motive, returns_second);
    let at_s = projected(&mut arena, s, gandr_kernel_term::Component::from(0_usize));
    let answered = arena.value_type_path(integer, at_s, at_s);
    let answered = arena.comp_type_returner(answered);
    let ambient = arena.computation_split(s, arity, returns_second);
    let product = arena.value_tuple(&[a, a]);
    let returns_integer = arena.comp_type_returner(integer);
    let returns_first = arena.computation_return(first_bound);
    let at_product =
        arena.computation_dependent_split(product, arity, returns_integer, returns_first);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    seed(&mut context, &scene.types);
    let answered = form_comp_type(&mut context, answered).unwrap();
    let checked = check_comp(&mut context, split, answered);
    assert!(
        checked.is_ok(),
        "the arm answers the motive at the pair of its components, and the split the motive \
             at its scrutinee: {checked:?}"
    );
    let ambient_checked = check_comp(&mut context, ambient, answered);
    assert!(
        matches!(ambient_checked, Err(CheckRefusal::ShapeMismatch { .. })),
        "a split with no motive does not eliminate a dependent pair: {ambient_checked:?}"
    );
    assert!(
        matches!(
            synthesise_comp(&mut context, at_product),
            Err(CheckRefusal::ShapeMismatch {
                wanted: ExpectedShape::Sigma,
                ..
            })
        ),
        "a split under a motive eliminates only a dependent pair"
    );
}

#[test]
fn a_tuple_of_paths_checks_at_the_identity_of_a_product()
{
    let mut arena = CoreArena::new();
    let scene = sigma_scene(&mut arena);
    let [a, b, ..] = scene.constants;
    let [integer, ..] = scene.types;
    let pairs = arena.value_type_product(&[integer, integer]);
    let pair = arena.value_tuple(&[a, b]);
    let identity = arena.value_type_path(pairs, pair, pair);
    let [here_a, here_b] = [a, b].map(|point| arena.value_here(point));
    let paths = arena.value_tuple(&[here_a, here_b]);
    let strayed = arena.value_tuple(&[here_b, here_b]);
    let short = arena.value_tuple(&[here_a]);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    seed(&mut context, &scene.types);
    let identity = form_value_type(&mut context, identity).unwrap();
    let checked = check_value(&mut context, paths, identity);
    assert!(
        checked.is_ok(),
        "a path between each pair of components relates the pairs: {checked:?}"
    );
    assert!(
        matches!(
            check_value(&mut context, strayed, identity),
            Err(CheckRefusal::EndpointMismatch { .. })
        ),
        "the first path must join the first components"
    );
    assert!(
        matches!(
            check_value(&mut context, short, identity),
            Err(CheckRefusal::ShapeMismatch { .. })
        ),
        "a tuple of another width is no path between the pairs"
    );
}

#[test]
fn a_pair_of_paths_checks_at_the_identity_of_a_dependent_pair()
{
    let mut arena = CoreArena::new();
    let scene = sigma_scene(&mut arena);
    let [a, b, r, s, stray, _] = scene.constants;
    let [.., identity] = scene.types;
    let here_a = arena.value_here(a);
    let here_r = arena.value_here(r);
    let paths = arena.value_tuple(&[here_a, here_r]);
    let here_stray = arena.value_here(stray);
    let strayed = arena.value_tuple(&[here_a, here_stray]);
    let here_b = arena.value_here(b);
    let moved = arena.value_tuple(&[here_b, here_r]);
    let declared = arena.value_type_path(scene.sigma, s, s);
    let first = projected(&mut arena, s, gandr_kernel_term::Component::from(0_usize));
    let second = projected(&mut arena, s, gandr_kernel_term::Component::from(1_usize));
    let here_first = arena.value_here(first);
    let here_second = arena.value_here(second);
    let projections = arena.value_tuple(&[here_first, here_second]);
    // `ring : Σ… = #{0, here(0)}`, and its identity with itself from the
    // reflexivities of another `0`.
    let ring = arena.value_constant(ConstantIndex::from(6_usize));
    let zero = arena.value_literal(integer_literal());
    let here_zero = arena.value_here(zero);
    let body = arena.value_tuple(&[zero, here_zero]);
    let around = arena.value_type_path(scene.sigma, ring, ring);
    let point = arena.value_literal(integer_literal());
    let here_point = arena.value_here(point);
    let here_here_point = arena.value_here(here_point);
    let unfolded = arena.value_tuple(&[here_point, here_here_point]);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    seed(&mut context, &scene.types);
    let identity = form_value_type(&mut context, identity).unwrap();
    let checked = check_value(&mut context, paths, identity);
    assert!(
        checked.is_ok(),
        "a path between the first components and, over it, one between the second: \
             {checked:?}"
    );
    assert!(
        matches!(
            check_value(&mut context, strayed, identity),
            Err(CheckRefusal::EndpointMismatch { .. })
        ),
        "the second path must end at the right second component"
    );
    assert!(
        matches!(
            check_value(&mut context, moved, identity),
            Err(CheckRefusal::EndpointMismatch { .. })
        ),
        "the first path must join the first components"
    );
    let declared = form_value_type(&mut context, declared).unwrap();
    let checked = check_value(&mut context, projections, declared);
    assert!(
        checked.is_ok(),
        "an endpoint that is no written pair is read through its projections: {checked:?}"
    );
    let sigma = form_value_type(&mut context, scene.sigma).unwrap();
    context
        .adopt(
            ConstantIndex::from(6_usize),
            Maybe::Present(sigma),
            Maybe::Present(body),
        )
        .unwrap();
    let around = form_value_type(&mut context, around).unwrap();
    let checked = check_value(&mut context, unfolded, around);
    assert!(
        checked.is_ok(),
        "a declared pair's endpoint is read through the pair it unfolds to, as an endpoint \
             at every other former unfolds: {checked:?}"
    );
}

#[test]
fn a_transport_along_a_path_at_a_dependent_pair_reads_its_motive_at_the_target()
{
    let mut arena = CoreArena::new();
    let scene = sigma_scene(&mut arena);
    let [a, b, r, _, _, q] = scene.constants;
    let [integer, _, loop_a, ..] = scene.types;
    let constant = arena.comp_type_returner(integer);
    let carried = arena.computation_path_transport(integer, q, a);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let at_first = projected(
        &mut arena,
        bound,
        gandr_kernel_term::Component::from(0_usize),
    );
    let family = arena.value_type_path(integer, at_first, at_first);
    let reading = arena.computation_path_transport(family, q, r);
    let at_target = arena.comp_type_returner(loop_a);
    let misplaced = arena.computation_path_transport(family, q, b);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    seed(&mut context, &scene.types);
    let constant = form_comp_type(&mut context, constant).unwrap();
    let checked = check_comp(&mut context, carried, constant);
    assert!(
        checked.is_ok(),
        "a motive that ignores its binder returns its own type: {checked:?}"
    );
    let at_target = form_comp_type(&mut context, at_target).unwrap();
    let checked = check_comp(&mut context, reading, at_target);
    assert!(
        checked.is_ok(),
        "a motive reading its binder's projection returns it at the target pair's: \
             {checked:?}"
    );
    assert!(
        matches!(
            synthesise_comp(&mut context, misplaced),
            Err(CheckRefusal::TypeMismatch(_))
        ),
        "the operand checks at the motive over the source pair"
    );
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    #[test]
    fn the_faces_agree_on_free_terms(
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
            let node = context.arena().value(term).cloned().unwrap();
            let synthesised = synthesise_value(&mut context, term);
            if let Ok(found) = synthesised {
                prop_assert!(
                    check_value(&mut context, term, found.produced()).is_ok(),
                    "a synthesising value checks against its synthesised type"
                );
            }
            let checked = check_value(&mut context, term, expected_value);
            match node {
                | Value::Thunk(_) => prop_assert_eq!(
                    synthesised,
                    Err(CheckRefusal::NotSynthesisable { form: CheckingForm::Thunk(term) }),
                    "a thunk does not synthesise"
                ),
                | Value::Tuple(ref components) if !components.is_empty() => {
                    prop_assert!(false, "the recipe mints no pair");
                },
                | Value::Primitive { .. } | Value::Variable { .. } | Value::Constant(_) | Value::Literal(_) | Value::Tuple(_) => {
                    let bridged = synthesised.and_then(|found| {
                        let mut tally = found.conversions();
                        value_bridge(&mut context, term, found.produced().id(), expected_value.id(), &mut tally)
                            .map(|()| tally)
                    });
                    prop_assert_eq!(
                        checked.map(|evidence| evidence.conversions()),
                        bridged,
                        "a synthesising value checks exactly as it synthesises, then crosses the value bridge"
                    );
                },
                | Value::Univalence(..)
                | Value::PathRefl(_) | Value::Here(_) | Value::Funext(..) | Value::Equiv(..) | Value::Ua { .. } | Value::Returned(_) | Value::Nested(_) | Value::Run(_)
                | Value::Constructor { .. } | Value::Record(_)
                | Value::Reify(_)
                | Value::PathProduct(..)
                | Value::PathEquiv {..}
                | Value::ListNil | Value::ListCons(..)
                | Value::Injection(..)
                | Value::Lift { .. }
                | Value::Quote(_)
                | Value::QuoteComputation(_)
                | Value::StaticLambda(_)
                | Value::StaticApplication(..)
                | Value::Hole(_)
                | Value::Mark { .. }
                | Value::SessionRelated { .. } | Value::Stay(_) | Value::Then(..) | Value::FlowProduct(..) | Value::Forward(_) | Value::FunctionFlow(..) | Value::Recorded(_) => {
                    prop_assert!(false, "the recipe mints no pair, injection, lift, quote, static operator, hole or mark");
                },
            }
            prop_assert_eq!(
                context.binders().depth(Zone::Intuitionistic),
                BinderDepth::from(0_usize),
                "every run leaves the binders where it found them"
            );
        }
        for &term in &terms.comps {
            let node = context.arena().computation(term).cloned().unwrap();
            let synthesised = synthesise_comp(&mut context, term);
            if let Ok(found) = synthesised {
                prop_assert!(
                    check_comp(&mut context, term, found.produced()).is_ok(),
                    "a synthesising computation checks against its synthesised type"
                );
            }
            let checked = check_comp(&mut context, term, expected_comp);
            match node {
                | Computation::Lambda(_) => prop_assert_eq!(
                    synthesised,
                    Err(CheckRefusal::NotSynthesisable { form: CheckingForm::Lambda(term) }),
                    "a lambda does not synthesise"
                ),
                | Computation::Return(value) => {
                    let value_synthesised = synthesise_value(&mut context, value);
                    prop_assert_eq!(
                        synthesised.is_ok(),
                        value_synthesised.is_ok(),
                        "a return synthesises exactly when its value does"
                    );
                },
                | Computation::Fixpoint { .. } => prop_assert!(false, "the free recipe mints no fixpoint"),
                | Computation::Primitive { .. } | Computation::Force(_) | Computation::Application(..) => {
                    let bridged = synthesised.and_then(|found| {
                        let mut tally = found.conversions();
                        comp_bridge(&mut context, term, found.produced().id(), expected_comp.id(), &mut tally)
                            .map(|()| tally)
                    });
                    let checked = checked.map(|evidence| evidence.conversions());
                    let agree = match (checked, bridged) {
                        | (Err(left), Err(right)) => same_refusal(context.arena(), left, right) == CertificateEquality::Equal,
                        | (left, right) => left == right,
                    };
                    prop_assert!(
                        agree,
                        "a synthesising computation checks exactly as it synthesises, then crosses the computation bridge: {:?} against {:?}",
                        checked,
                        bridged
                    );
                },
                | Computation::Transport(..) | Computation::PathTransport { .. } | Computation::Ride { .. } | Computation::TelescopeTransport { .. } | Computation::Bind(..) | Computation::Ascribe { .. } | Computation::DataCase { .. } | Computation::RecordProjection(..) | Computation::TupleProjection(..) => {
                    prop_assert!(false, "the free recipe mints no bind, ascription or native eliminator");
                },
                | Computation::ListFold { .. } | Computation::ListCase { .. } | Computation::Case { .. } | Computation::Split { .. }
                | Computation::Perform { .. } | Computation::Handle { .. } | Computation::Resume(..) | Computation::Abandon(_)
                | Computation::Exercise { .. } | Computation::Scope { .. }
                | Computation::Reset(_) | Computation::Shift(_) | Computation::With(..) | Computation::Project(..)
                | Computation::Hole(_) | Computation::Mark { .. } | Computation::Session(_) | Computation::Memory(_) | Computation::World(_) => {
                    prop_assert!(false, "the recipe mints no former outside the fragment, no hole and no mark");
                },
            }
            prop_assert_eq!(
                context.binders().depth(Zone::Intuitionistic),
                BinderDepth::from(0_usize),
                "every run leaves the binders where it found them"
            );
        }
    }

    #[test]
    fn well_typed_terms_synthesise_and_check_their_type(recipe in typed_recipe())
    {
        let mut arena = CoreArena::new();
        let terms = recipe.build(&mut arena);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        seed(&mut context, &terms.constants);
        for &(term, built, mode) in &terms.values {
            let expected = form_value_type(&mut context, built).unwrap();
            prop_assert!(
                check_value(&mut context, term, expected).is_ok(),
                "a well-typed value checks against its type"
            );
            let synthesised = synthesise_value(&mut context, term);
            match mode {
                | Mode::Synthesising => {
                    let found = synthesised.unwrap();
                    let mut scratch = ConversionCount::default();
                    prop_assert!(
                        value_bridge(&mut context, term, found.produced().id(), built, &mut scratch).is_ok(),
                        "a well-typed synthesising value synthesises its type"
                    );
                },
                | Mode::Checking => prop_assert!(
                    matches!(synthesised, Err(CheckRefusal::NotSynthesisable { .. })),
                    "a well-typed checking value is refused in synthesis"
                ),
            }
        }
        for &(term, built, mode) in &terms.comps {
            let expected = form_comp_type(&mut context, built).unwrap();
            prop_assert!(
                check_comp(&mut context, term, expected).is_ok(),
                "a well-typed computation checks against its type"
            );
            let synthesised = synthesise_comp(&mut context, term);
            match mode {
                | Mode::Synthesising => {
                    let found = synthesised.unwrap();
                    let mut scratch = ConversionCount::default();
                    prop_assert!(
                        comp_bridge(&mut context, term, found.produced().id(), built, &mut scratch).is_ok(),
                        "a well-typed synthesising computation synthesises its type"
                    );
                },
                | Mode::Checking => prop_assert!(
                    matches!(synthesised, Err(CheckRefusal::NotSynthesisable { .. })),
                    "a well-typed checking computation is refused in synthesis"
                ),
            }
        }
    }
}
