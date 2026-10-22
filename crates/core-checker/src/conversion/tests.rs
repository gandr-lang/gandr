use anodized::spec;
use gandr_core_term::CompTypeId;
use gandr_core_term::CoreArena;
use gandr_core_term::Sort;
use gandr_core_term::Zone;
use gandr_kernel_strata::Level;
use gandr_kernel_strata::LevelConstant;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GroundSort;
use proptest::prelude::ProptestConfig;
use proptest::prelude::prop_assert_eq;
use proptest::prelude::proptest;

use super::Agreement;
use super::ConversionCount;
use super::Pairing;
use super::convert;
use super::value_bridge;
use crate::code::Lift;
use crate::context::CheckBudget;
use crate::context::CheckingContext;
use crate::fixture::TypeRecipe;
use crate::fixture::dangling_value_type;
use crate::fixture::seed;
use crate::fixture::type_recipe;
use crate::refusal::CheckRefusal;
use crate::refusal::CoreNode;
use crate::refusal::Mismatch;
use crate::refusal::TypeNode;

#[test]
fn one_id_converts_without_being_read()
{
    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let dangling = dangling_value_type();
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    assert_eq!(
        convert(
            &mut context,
            Pairing::Values(dangling.into(), dangling.into())
        ),
        Ok(Agreement::Convertible),
        "one id is one node, so the pair is accepted without its node being read"
    );
    assert_eq!(
        convert(&mut context, Pairing::Values(unit.into(), dangling.into())),
        Err(CheckRefusal::DanglingNode {
            node: CoreNode::Type(TypeNode::Value(dangling)),
        }),
        "two ids are read, so the id the arena does not hold is met and refused"
    );
}

#[test]
fn equal_trees_at_distinct_ids_convert()
{
    let mut arena = CoreArena::new();
    let build = |arena: &mut CoreArena| {
        let integer = arena.value_type_base(BaseType::Integer);
        let universe = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
        let result = arena.comp_type_returner(integer);
        let pi = arena.comp_type_pi(universe, result);
        arena.value_type_thunk(pi)
    };
    let left = build(&mut arena);
    let right = build(&mut arena);
    assert_ne!(left, right, "the two trees sit at distinct ids");
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    assert_eq!(
        convert(&mut context, Pairing::Values(left.into(), right.into())),
        Ok(Agreement::Convertible),
        "conversion compares trees, not ids"
    );
}

#[test]
fn returner_rows_are_covariant_but_signature_types_are_invariant()
{
    use gandr_core_term::effect::EffectName;
    use gandr_core_term::effect::EffectOp;
    use gandr_core_term::effect::EffectRow;
    use gandr_core_term::effect::EffectSig;
    use gandr_core_term::effect::OperationName;
    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let pure = arena.comp_type_returner(unit);
    let signature = |name: &str, reply| {
        EffectRow::singleton(
            EffectSig::new(EffectName::from(name), alloc::vec![EffectOp {
                name: OperationName::from("get"),
                payload: unit,
                reply
            }])
            .unwrap(),
        )
    };
    let effectful = arena.comp_type_returner_with_effects(unit, signature("IO", unit));
    let pure_thunk = arena.value_type_thunk(pure);
    let effectful_thunk = arena.value_type_thunk(effectful);
    let first = arena.comp_type_returner_with_effects(unit, signature("State", pure_thunk));
    let second = arena.comp_type_returner_with_effects(unit, signature("State", effectful_thunk));
    let accepts_effectful = arena.comp_type_arrow(effectful_thunk, pure);
    let accepts_pure = arena.comp_type_arrow(pure_thunk, pure);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    assert_eq!(
        convert(
            &mut context,
            Pairing::SubComps(pure.into(), effectful.into())
        ),
        Ok(Agreement::Convertible)
    );
    assert_eq!(
        convert(
            &mut context,
            Pairing::SubComps(effectful.into(), pure.into())
        ),
        Ok(Agreement::Apart)
    );
    assert_eq!(
        convert(&mut context, Pairing::Comps(pure.into(), effectful.into())),
        Ok(Agreement::Apart)
    );
    assert_eq!(
        convert(
            &mut context,
            Pairing::SubValues(pure_thunk.into(), effectful_thunk.into())
        ),
        Ok(Agreement::Convertible)
    );
    assert_eq!(
        convert(
            &mut context,
            Pairing::SubComps(accepts_effectful.into(), accepts_pure.into())
        ),
        Ok(Agreement::Convertible)
    );
    assert_eq!(
        convert(
            &mut context,
            Pairing::SubComps(accepts_pure.into(), accepts_effectful.into())
        ),
        Ok(Agreement::Apart)
    );
    assert_eq!(
        convert(&mut context, Pairing::SubComps(first.into(), second.into())),
        Ok(Agreement::Apart)
    );
    assert_eq!(
        convert(&mut context, Pairing::SubComps(second.into(), first.into())),
        Ok(Agreement::Apart)
    );
}

/// A pure returner and an effectful one over the same result, the pure one
/// below the effectful one.
///
/// # Specification
/// trivial.
fn pure_below_effectful() -> (CoreArena, CompTypeId, CompTypeId)
{
    use gandr_core_term::effect::EffectName;
    use gandr_core_term::effect::EffectOp;
    use gandr_core_term::effect::EffectRow;
    use gandr_core_term::effect::EffectSig;
    use gandr_core_term::effect::OperationName;
    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let pure = arena.comp_type_returner(unit);
    let row = EffectRow::singleton(
        EffectSig::new(EffectName::from("IO"), alloc::vec![EffectOp {
            name: OperationName::from("get"),
            payload: unit,
            reply: unit
        }])
        .unwrap(),
    );
    let effectful = arena.comp_type_returner_with_effects(unit, row);
    (arena, pure, effectful)
}

/// `Stack(B, C) ⊑ Stack(B′, C′)` when `B′ ⊑ B` and `C ⊑ C′`: a stack that
/// accepts the effectful input and delivers the pure output stands where
/// one accepting the pure input and delivering the effectful output is
/// expected.
#[test]
fn stack_is_contravariant_in_b_covariant_in_c_positive()
{
    let (mut arena, pure, effectful) = pure_below_effectful();
    let narrow = arena.value_type_stack(effectful, pure);
    let wide = arena.value_type_stack(pure, effectful);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    assert_eq!(
        convert(&mut context, Pairing::SubValues(narrow.into(), wide.into())),
        Ok(Agreement::Convertible)
    );
}

/// Widening a stack's input or narrowing its output breaks the subsumption,
/// and so does the converse of a valid widening.
#[test]
fn stack_variance_negative()
{
    let (mut arena, pure, effectful) = pure_below_effectful();
    let narrow = arena.value_type_stack(effectful, pure);
    let wide = arena.value_type_stack(pure, effectful);
    let pure_to_pure = arena.value_type_stack(pure, pure);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    for (sub, sup) in [(wide, narrow), (pure_to_pure, narrow), (wide, pure_to_pure)] {
        assert_eq!(
            convert(&mut context, Pairing::SubValues(sub.into(), sup.into())),
            Ok(Agreement::Apart)
        );
    }
}

#[test]
fn differing_trees_are_apart_in_either_order()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let string = arena.value_type_base(BaseType::String);
    let unit = arena.value_type_unit();
    let returns_integer = arena.comp_type_returner(integer);
    let returns_string = arena.comp_type_returner(string);
    let thunk_integer = arena.value_type_thunk(returns_integer);
    let thunk_string = arena.value_type_thunk(returns_string);
    let arrow = arena.comp_type_arrow(unit, returns_integer);
    let one = Level::constant(LevelConstant::from(1_u64));
    let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let large = arena.value_type_universe(Sort::Ground(GroundSort::Value), one.clone());
    let negative = arena.value_type_universe(Sort::Ground(GroundSort::Computation), Level::zero());
    let lifted_once = arena.value_type_lift(integer, one);
    let lifted_twice = arena.value_type_lift(integer, Level::constant(LevelConstant::from(2_u64)));
    let inner = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let outer = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let decode_inner = arena.value_type_element(inner, Level::zero());
    let decode_outer = arena.value_type_element(outer, Level::zero());
    let loop_path = arena.value_type_path(integer, inner, inner);
    let open_path = arena.value_type_path(integer, inner, outer);
    let pairs = [
        Pairing::Values(integer.into(), string.into()),
        Pairing::Values(unit.into(), thunk_integer.into()),
        Pairing::Values(thunk_integer.into(), thunk_string.into()),
        Pairing::Comps(returns_integer.into(), arrow.into()),
        Pairing::Values(small.into(), large.into()),
        Pairing::Values(small.into(), negative.into()),
        Pairing::Values(lifted_once.into(), lifted_twice.into()),
        Pairing::Values(lifted_once.into(), integer.into()),
        Pairing::Values(decode_inner.into(), decode_outer.into()),
        Pairing::Values(loop_path.into(), open_path.into()),
        Pairing::Endpoints(inner, outer),
    ];
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    for pairing in pairs {
        let swapped = match pairing {
            Pairing::Assignable(left, right) => Pairing::Assignable(right, left),
            Pairing::Values(left, right) => Pairing::Values(right, left),
            Pairing::Comps(left, right) => Pairing::Comps(right, left),
            Pairing::Codes(left, right) => Pairing::Codes(right, left),
            Pairing::Terms(left, right) => Pairing::Terms(right, left),
            Pairing::Endpoints(left, right) => Pairing::Endpoints(right, left),
            Pairing::SubValues(left, right) => Pairing::SubValues(right, left),
            Pairing::SubComps(left, right) => Pairing::SubComps(right, left),
        };
        assert_eq!(
            convert(&mut context, pairing),
            Ok(Agreement::Apart),
            "{pairing:?} differ"
        );
        assert_eq!(
            convert(&mut context, swapped),
            Ok(Agreement::Apart),
            "{swapped:?} differ in the other order too"
        );
    }
}

#[test]
fn a_vacuous_dependent_arrow_is_the_plain_arrow_577()
{
    // #577: `Π(_ : Unit). F Integer` is `Unit -> F Integer`, and
    // `Π(_ : Unit). F El(#1)` — the ambient `#0` seen past the binder — is
    // `Unit -> F El(#0)`, in either order and under subtyping. A dependent
    // codomain naming its binder, `Π(_ : Unit). F El(#0)`, is apart from
    // `Unit -> F El(#0)`, and a differing domain still separates.
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let unit = arena.value_type_unit();
    let returns_integer = arena.comp_type_returner(integer);
    let named = |arena: &mut CoreArena, index: u32| {
        let code = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index));
        let decoded = arena.value_type_element(code, Level::zero());
        arena.comp_type_returner(decoded)
    };
    let (inner, outer) = (named(&mut arena, 0), named(&mut arena, 1));
    let cases = [
        (
            arena.comp_type_pi(unit, returns_integer),
            arena.comp_type_arrow(unit, returns_integer),
            Agreement::Convertible,
        ),
        (
            arena.comp_type_pi(unit, outer),
            arena.comp_type_arrow(unit, inner),
            Agreement::Convertible,
        ),
        (
            arena.comp_type_pi(unit, inner),
            arena.comp_type_arrow(unit, inner),
            Agreement::Apart,
        ),
        (
            arena.comp_type_pi(integer, returns_integer),
            arena.comp_type_arrow(unit, returns_integer),
            Agreement::Apart,
        ),
    ];
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    for (dependent, plain, expected) in cases {
        for pairing in [
            Pairing::Comps(dependent.into(), plain.into()),
            Pairing::Comps(plain.into(), dependent.into()),
            Pairing::SubComps(dependent.into(), plain.into()),
            Pairing::SubComps(plain.into(), dependent.into()),
        ] {
            assert_eq!(convert(&mut context, pairing), Ok(expected), "{pairing:?}");
        }
    }
}

#[test]
fn the_unknown_type_is_consistent_beside_a_differing_former()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let string = arena.value_type_base(BaseType::String);
    let unknown = arena.value_type_unknown();
    let unknown_computation = arena.comp_type_unknown();
    let returns_integer = arena.comp_type_returner(integer);
    let hole = arena.value_hole(gandr_core_term::hole::HoleId::from(0_u32));
    let variable = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let marked = arena.value_mark(gandr_core_term::hole::MarkIndex::from(0_u32), variable);
    let decode_hole = arena.value_type_element(hole, Level::zero());
    let decode_variable = arena.value_type_element(variable, Level::zero());
    let decode_marked = arena.value_type_element(marked, Level::zero());
    let known_left = arena.value_type_product(&[integer, integer]);
    let unknown_left = arena.value_type_product(&[unknown, integer]);
    let unknown_left_string = arena.value_type_product(&[unknown, string]);
    let unit_code = arena.value_unit();
    let consistent = [
        Pairing::Values(unknown.into(), integer.into()),
        Pairing::Values(decode_hole.into(), integer.into()),
        Pairing::Values(decode_marked.into(), decode_variable.into()),
        Pairing::Values(known_left.into(), unknown_left.into()),
        Pairing::Comps(unknown_computation.into(), returns_integer.into()),
        Pairing::Codes(hole, variable),
        Pairing::Terms(hole, variable),
        Pairing::Endpoints(hole, variable),
    ];
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    for pairing in consistent {
        let swapped = match pairing {
            Pairing::Assignable(left, right) => Pairing::Assignable(right, left),
            Pairing::Values(left, right) => Pairing::Values(right, left),
            Pairing::SubValues(left, right) => Pairing::SubValues(right, left),
            Pairing::Comps(left, right) => Pairing::Comps(right, left),
            Pairing::SubComps(left, right) => Pairing::SubComps(right, left),
            Pairing::Codes(left, right) => Pairing::Codes(right, left),
            Pairing::Terms(left, right) => Pairing::Terms(right, left),
            Pairing::Endpoints(left, right) => Pairing::Endpoints(right, left),
        };
        assert_eq!(
            convert(&mut context, pairing),
            Ok(Agreement::Convertible),
            "{pairing:?}"
        );
        assert_eq!(
            convert(&mut context, swapped),
            Ok(Agreement::Convertible),
            "{swapped:?}"
        );
    }
    assert_eq!(
        convert(
            &mut context,
            Pairing::Values(known_left.into(), unknown_left_string.into())
        ),
        Ok(Agreement::Apart),
        "the unknown factor agrees, the differing one does not"
    );
    assert_eq!(
        convert(&mut context, Pairing::Terms(variable, unit_code)),
        Ok(Agreement::Apart),
        "an index without a hole is compared as syntax"
    );
}

/// `def Num : Type = Integer`: a decode of `Num` is the integer atom
/// wherever it stands, and a decode of an undefined code is not.
#[test]
fn a_decode_of_a_defined_code_converts_with_its_body()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let string = arena.value_type_base(BaseType::String);
    let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let body = arena.value_quote(integer);
    let num = arena.value_constant(ConstantIndex::from(0_usize));
    let opaque = arena.value_constant(ConstantIndex::from(1_usize));
    let decoded = arena.value_type_element(num, Level::zero());
    let rigid = arena.value_type_element(opaque, Level::zero());
    let returns_decoded = arena.comp_type_returner(decoded);
    let returns_integer = arena.comp_type_returner(integer);
    let under_arrow = arena.comp_type_arrow(decoded, returns_decoded);
    let plain_arrow = arena.comp_type_arrow(integer, returns_integer);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    seed(&mut context, &[small, small]);
    context.define(
        ConstantIndex::from(0_usize),
        crate::formation::FormedValueType::derived(small),
        body,
    );
    assert_eq!(
        convert(
            &mut context,
            Pairing::Values(decoded.into(), integer.into())
        ),
        Ok(Agreement::Convertible),
        "the decode unfolds to the type its body quotes"
    );
    assert_eq!(
        convert(
            &mut context,
            Pairing::Comps(under_arrow.into(), plain_arrow.into())
        ),
        Ok(Agreement::Convertible),
        "and does so beneath every former the walk descends"
    );
    assert_eq!(
        convert(&mut context, Pairing::Values(decoded.into(), string.into())),
        Ok(Agreement::Apart),
        "the unfolded type is compared, not assumed"
    );
    assert_eq!(
        convert(&mut context, Pairing::Values(rigid.into(), integer.into())),
        Ok(Agreement::Apart),
        "a code with no body stays rigid"
    );
}

/// Codes compare at their reduced heads: a static instance of a defined
/// operator by its reduct, a rigid one by head and argument, a static
/// lambda by its body.
#[test]
fn static_codes_compare_by_head_argument_and_body()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let string = arena.value_type_base(BaseType::String);
    let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let operator_type = arena.value_type_static_pi(small, small);
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let decoded_bound = arena.value_type_element(bound, Level::zero());
    let squared = arena.value_type_product(&[decoded_bound, decoded_bound]);
    let squared_code = arena.value_quote(squared);
    let pair_body = arena.value_static_lambda(squared_code);
    let pair = arena.value_constant(ConstantIndex::from(0_usize));
    let integer_code = arena.value_quote(integer);
    let string_code = arena.value_quote(string);
    let instance = arena.value_static_application(pair, integer_code);
    let decoded_instance = arena.value_type_element(instance, Level::zero());
    let written = arena.value_type_product(&[integer, integer]);
    let rigid = |arena: &mut CoreArena, head: u32, argument| {
        let head = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(head));
        let applied = arena.value_static_application(head, argument);
        arena.value_type_element(applied, Level::zero())
    };
    let at_integer = rigid(&mut arena, 0, integer_code);
    let again = rigid(&mut arena, 0, integer_code);
    let at_string = rigid(&mut arena, 0, string_code);
    let other_head = rigid(&mut arena, 1, integer_code);
    let identity = arena.value_static_lambda(bound);
    let other_identity = arena.value_static_lambda(bound);
    let constant_body = arena.value_static_lambda(integer_code);
    let at_identity = rigid(&mut arena, 0, identity);
    let at_other_identity = rigid(&mut arena, 0, other_identity);
    let at_constant = rigid(&mut arena, 0, constant_body);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    seed(&mut context, &[operator_type]);
    context.define(
        ConstantIndex::from(0_usize),
        crate::formation::FormedValueType::derived(operator_type),
        pair_body,
    );
    for (pairing, agreement, message) in [
        (
            Pairing::Values(decoded_instance.into(), written.into()),
            Agreement::Convertible,
            "an instance of a defined operator converts with its reduct",
        ),
        (
            Pairing::Values(at_integer.into(), again.into()),
            Agreement::Convertible,
            "two rigid instances agree by head and argument",
        ),
        (
            Pairing::Values(at_integer.into(), at_string.into()),
            Agreement::Apart,
            "a different argument is apart",
        ),
        (
            Pairing::Values(at_integer.into(), other_head.into()),
            Agreement::Apart,
            "a different head is apart",
        ),
        (
            Pairing::Values(at_identity.into(), at_other_identity.into()),
            Agreement::Convertible,
            "two static lambdas over one body agree",
        ),
        (
            Pairing::Values(at_identity.into(), at_constant.into()),
            Agreement::Apart,
            "static lambdas over different bodies are apart",
        ),
    ] {
        assert_eq!(convert(&mut context, pairing), Ok(agreement), "{message}");
    }
}

#[test]
fn the_value_bridge_lifts_a_small_value_code_and_nothing_else()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let returns_integer = arena.comp_type_returner(integer);
    let one = Level::constant(LevelConstant::from(1_u64));
    let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let large = arena.value_type_universe(Sort::Ground(GroundSort::Value), one.clone());
    let small_negative =
        arena.value_type_universe(Sort::Ground(GroundSort::Computation), Level::zero());
    let large_negative =
        arena.value_type_universe(Sort::Ground(GroundSort::Computation), one.clone());
    let code = arena.value_quote(integer);
    let negative_code = arena.value_quote_computation(returns_integer);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let mut tally = ConversionCount::default();
    assert_eq!(
        value_bridge(&mut context, code, small, small, &mut tally),
        Ok(()),
        "a code checks at its own universe"
    );
    assert!(context.lifts().is_empty(), "and records no lift there");
    assert_eq!(
        value_bridge(&mut context, code, small, large, &mut tally),
        Ok(()),
        "a value code checks one universe up"
    );
    assert_eq!(
        context.lifts().get(&code),
        Some(&Lift::new(Level::zero(), one)),
        "and the crossing records the lift the kernel bridge writes"
    );
    assert_eq!(
        value_bridge(&mut context, code, large, small, &mut tally),
        Err(CheckRefusal::LevelMismatch {
            at: code,
            synthesised: large,
            expected: small,
        }),
        "no code moves down a universe"
    );
    assert_eq!(
        value_bridge(
            &mut context,
            negative_code,
            small_negative,
            large_negative,
            &mut tally
        ),
        Err(CheckRefusal::LevelMismatch {
            at: negative_code,
            synthesised: small_negative,
            expected: large_negative,
        }),
        "the core has no lift of a computation type, so a computation code stays at its level"
    );
    assert_eq!(
        value_bridge(&mut context, code, small, small_negative, &mut tally),
        Err(CheckRefusal::SortMismatch {
            at: code,
            synthesised: small,
            expected: small_negative,
        }),
        "no code crosses to the other sort"
    );
    assert_eq!(
        tally,
        ConversionCount::from(5_usize),
        "every call crossed once"
    );
}

#[test]
fn a_dangling_type_is_refused()
{
    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let dangling = dangling_value_type();
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    assert_eq!(
        convert(&mut context, Pairing::Values(unit.into(), dangling.into())),
        Err(CheckRefusal::DanglingNode {
            node: CoreNode::Type(TypeNode::Value(dangling)),
        }),
        "an id from another arena is refused rather than read"
    );
}

#[test]
fn crossing_counts_saturate_on_success_and_refusal()
{
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let string = arena.value_type_base(BaseType::String);
    let literal = arena.value_literal(crate::fixture::integer_literal());
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let mut tally = ConversionCount::from(usize::MAX - 1);
    assert_eq!(
        value_bridge(&mut context, literal, integer, integer, &mut tally),
        Ok(())
    );
    assert_eq!(usize::from(tally), usize::MAX);
    assert_eq!(
        value_bridge(&mut context, literal, integer, string, &mut tally),
        Err(CheckRefusal::TypeMismatch(
            crate::refusal::Mismatch::Value {
                at: literal,
                synthesised: integer,
                expected: string,
            }
        ))
    );
    assert_eq!(usize::from(tally), usize::MAX);
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    #[test]
    fn the_id_fast_path_agrees_with_the_structural_decision(
        first in type_recipe(),
        second in type_recipe(),
    )
    {
        let mut arena = CoreArena::new();
        let first_tree = TypeRecipe::build(&first, &mut arena);
        let first_copy = TypeRecipe::build(&first, &mut arena);
        let second_tree = TypeRecipe::build(&second, &mut arena);
        let second_copy = TypeRecipe::build(&second, &mut arena);
        let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
        prop_assert_eq!(
            convert(&mut context, Pairing::Values(first_tree.into(), first_copy.into())),
            Ok(Agreement::Convertible),
            "a tree converts with its copy at fresh ids"
        );
        let verdict = convert(&mut context, Pairing::Values(first_tree.into(), second_tree.into()));
        prop_assert_eq!(
            convert(&mut context, Pairing::Values(second_tree.into(), first_tree.into())),
            verdict,
            "the decision is symmetric"
        );
        prop_assert_eq!(
            convert(&mut context, Pairing::Values(first_copy.into(), second_copy.into())),
            verdict,
            "replacing either side by a copy at fresh ids keeps the verdict"
        );
        prop_assert_eq!(
            verdict == Ok(Agreement::Convertible),
            first.shape() == second.shape(),
            "the trees convert exactly when their shapes agree"
        );
    }
}

/// Two abstract types, both represented by `Integer`, admitted at
/// positions zero and one with seals that reach nothing past them, then a
/// value declaration at two the comparisons are read from.
///
/// # Specification
/// - requires: `context` has admitted nothing.
/// - ensures: the two atoms, the representation and the unit type, the context
///   having admitted all three declarations.
/// - panics: a declaration of the fixture is refused.
///
/// # Adequacy
/// - hypothesis: L3 — a reader past both seals separates identity from
///   representation.
/// - witness: `conversion::tests::a_sealed_atom_relates_to_no_representation`
/// - witness: `conversion::tests::sealed_atoms_relate_by_identity_alone`
#[spec(ensures: |ret| matches!(ret, [first, second, integer, unit]
        if first != second && integer != unit))]
fn sealed_pair(context: &mut CheckingContext<'_>) -> [gandr_core_term::ValueTypeId; 4]
{
    use crate::declaration::AbstractType;
    use crate::declaration::Declaration;
    use crate::declaration::OriginToken;
    use crate::seal::ComponentOrdinal;
    use crate::seal::SealSite;
    use crate::seal::SealingSite;
    let arena = context.arena_mut();
    let integer = arena.value_type_base(BaseType::Integer);
    let unit = arena.value_type_unit();
    let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let first = arena.value_type_abstract(ConstantIndex::from(0_usize));
    let second = arena.value_type_abstract(ConstantIndex::from(1_usize));
    let value = arena.value_unit();
    let atom = |position: usize| {
        Declaration::abstract_type(
            ConstantIndex::from(position),
            AbstractType::new(
                small,
                integer,
                gandr_kernel_term::SealExtent::from(0_usize),
                SealSite::new(SealingSite::from(0_usize), ComponentOrdinal::from(position)),
            ),
            OriginToken::from(position),
        )
    };
    let module = [
        atom(0),
        atom(1),
        Declaration::new(
            ConstantIndex::from(2_usize),
            quenchant_shape::shape::Maybe::Present(unit),
            quenchant_shape::shape::Maybe::Present(value),
            OriginToken::from(2_usize),
        ),
    ];
    let report = crate::module::check_module(context, &module);
    assert_eq!(report.abstract_types().len(), 2, "both atoms are admitted");
    [first, second, integer, unit]
}

#[test]
fn a_sealed_atom_relates_to_no_representation()
{
    let mut arena = CoreArena::new();
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let [atom, _, integer, unit] = sealed_pair(&mut context);
    for other in [integer, unit] {
        for pairing in [
            Pairing::Values(atom.into(), other.into()),
            Pairing::Values(other.into(), atom.into()),
            Pairing::SubValues(atom.into(), other.into()),
            Pairing::SubValues(other.into(), atom.into()),
        ] {
            assert_eq!(
                convert(&mut context, pairing),
                Ok(Agreement::Apart),
                "past its seal an atom relates to no type in either direction, its own representation included"
            );
        }
    }
}

#[test]
fn sealed_atoms_relate_by_identity_alone()
{
    let mut arena = CoreArena::new();
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let [first, second, ..] = sealed_pair(&mut context);
    let again = context
        .arena_mut()
        .value_type_abstract(ConstantIndex::from(0_usize));
    assert_eq!(
        convert(&mut context, Pairing::Values(first.into(), again.into())),
        Ok(Agreement::Convertible),
        "one atom converts with itself at a fresh id"
    );
    assert_eq!(
        convert(&mut context, Pairing::Values(first.into(), second.into())),
        Ok(Agreement::Apart),
        "two atoms with one representation stay apart"
    );
}

/// Two codes of one former agree exactly where every part the former
/// compares agrees: each former's twin at a fresh id converts, and changing
/// one part at a time — the literal, the arity, the summand, the tag, the
/// labels, the constant, the moves — sets the pair apart.
#[test]
fn codes_agree_exactly_where_their_parts_do()
{
    use alloc::collections::BTreeMap;
    use alloc::string::String;
    use alloc::sync::Arc;
    use alloc::vec;

    use gandr_core_term::Summand;
    use gandr_core_term::session::RecordedMove;
    use gandr_kernel_term::ConstructorTag;
    use gandr_kernel_term::FieldLabel;

    use crate::fixture::integer_literal;
    use crate::fixture::text_literal;

    let mut arena = CoreArena::new();
    let zero = arena.value_literal(integer_literal());
    let unit = arena.value_type_unit();
    let record = |arena: &mut CoreArena, labels: &[&str]| {
        let fields = labels
            .iter()
            .map(|&label| (FieldLabel::from(String::from(label)), zero))
            .collect::<BTreeMap<_, _>>();
        arena.value_record(fields)
    };
    let integer = arena.value_type_base(BaseType::Integer);
    let returns_zero = arena.comp_type_returner(integer);
    let string = arena.value_type_base(BaseType::String);
    let returns_text = arena.comp_type_returner(string);
    let recorded =
        |arena: &mut CoreArena, moves: &[RecordedMove]| arena.value_recorded(Arc::from(moves));
    let twins = [
        (
            arena.value_literal(integer_literal()),
            arena.value_literal(integer_literal()),
            "a literal",
        ),
        (
            arena.value_tuple(&[zero, zero]),
            arena.value_tuple(&[zero, zero]),
            "a tuple",
        ),
        (
            arena.value_injection(Summand::from(0_usize), zero),
            arena.value_injection(Summand::from(0_usize), zero),
            "an injection",
        ),
        (
            arena.value_constructor(unit, ConstructorTag::from(0_usize), vec![zero]),
            arena.value_constructor(unit, ConstructorTag::from(0_usize), vec![zero]),
            "a constructor",
        ),
        (
            record(&mut arena, &["a"]),
            record(&mut arena, &["a"]),
            "a record",
        ),
        (
            arena.value_constant(ConstantIndex::from(0_usize)),
            arena.value_constant(ConstantIndex::from(0_usize)),
            "a constant",
        ),
        (
            recorded(&mut arena, &[RecordedMove::Sent(zero)]),
            recorded(&mut arena, &[RecordedMove::Sent(zero)]),
            "a recorded run",
        ),
        (
            arena.value_quote_computation(returns_zero),
            arena.value_quote_computation(returns_zero),
            "a quoted computation type",
        ),
        (
            recorded(&mut arena, &[
                RecordedMove::Closed,
                RecordedMove::Sent(zero),
            ]),
            recorded(&mut arena, &[
                RecordedMove::Closed,
                RecordedMove::Sent(zero),
            ]),
            "a recorded run closing before it sends",
        ),
    ];
    let apart = [
        (
            twins[0].0,
            arena.value_literal(text_literal()),
            "literals that differ",
        ),
        (
            twins[1].0,
            arena.value_tuple(&[zero, zero, zero]),
            "tuples of different arities",
        ),
        (
            twins[2].0,
            arena.value_injection(Summand::from(1_usize), zero),
            "injections into different summands",
        ),
        (
            twins[3].0,
            arena.value_constructor(unit, ConstructorTag::from(1_usize), vec![zero]),
            "constructors with different tags",
        ),
        (
            twins[3].0,
            arena.value_constructor(unit, ConstructorTag::from(0_usize), vec![zero, zero]),
            "constructors with different field counts",
        ),
        (
            twins[4].0,
            record(&mut arena, &["a", "b"]),
            "records with different field counts",
        ),
        (
            twins[4].0,
            record(&mut arena, &["b"]),
            "records with different labels",
        ),
        (
            twins[5].0,
            arena.value_constant(ConstantIndex::from(1_usize)),
            "different constants",
        ),
        (
            twins[6].0,
            recorded(&mut arena, &[
                RecordedMove::Sent(zero),
                RecordedMove::Closed,
            ]),
            "runs of different lengths",
        ),
        (
            twins[6].0,
            recorded(&mut arena, &[RecordedMove::Received(zero)]),
            "runs whose moves differ",
        ),
        (
            twins[7].0,
            arena.value_quote_computation(returns_text),
            "quoted computation types that differ",
        ),
    ];
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    for (left, right, what) in twins {
        assert_ne!(left, right, "{what}'s twin sits at a fresh id");
        assert_eq!(
            convert(&mut context, Pairing::Codes(left, right)),
            Ok(Agreement::Convertible),
            "{what} converts with its twin"
        );
    }
    for (left, right, what) in apart {
        assert_eq!(
            convert(&mut context, Pairing::Codes(left, right)),
            Ok(Agreement::Apart),
            "{what} are apart"
        );
    }
}

/// Outside subtyping a type agrees only with its own shape: record types by
/// their labels, staged types by their stage, decoded computations by their
/// target, and a staged type never with its bare base in either order.
#[test]
fn invariant_types_agree_exactly_where_their_parts_do()
{
    use alloc::collections::BTreeMap;
    use alloc::string::String;

    use gandr_kernel_term::FieldLabel;
    use gandr_kernel_term::Stage;
    use gandr_kernel_term::StageId;

    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let record = |arena: &mut CoreArena, labels: &[&str]| {
        let fields = labels
            .iter()
            .map(|&label| (FieldLabel::from(String::from(label)), integer))
            .collect::<BTreeMap<_, _>>();
        arena.value_type_record(fields)
    };
    let at = |arena: &mut CoreArena, stage: usize| {
        arena.value_type_staged(integer, Stage::At(StageId::from(stage)))
    };
    let code = arena.value_constant(ConstantIndex::from(0_usize));
    let one = Level::constant(LevelConstant::from(1_u64));
    let values = [
        (
            record(&mut arena, &["a"]),
            record(&mut arena, &["a"]),
            Agreement::Convertible,
            "a record type converts with its twin",
        ),
        (
            record(&mut arena, &["a"]),
            record(&mut arena, &["a", "b"]),
            Agreement::Apart,
            "record types with different field counts are apart",
        ),
        (
            record(&mut arena, &["a"]),
            record(&mut arena, &["b"]),
            Agreement::Apart,
            "record types with different labels are apart",
        ),
        (
            at(&mut arena, 0),
            at(&mut arena, 0),
            Agreement::Convertible,
            "a staged type converts with its twin",
        ),
        (
            at(&mut arena, 0),
            at(&mut arena, 1),
            Agreement::Apart,
            "staged types at different stages are apart",
        ),
        (
            at(&mut arena, 0),
            integer,
            Agreement::Apart,
            "a staged type is apart from its bare base",
        ),
        (
            integer,
            at(&mut arena, 0),
            Agreement::Apart,
            "a bare base is apart from its staged type",
        ),
    ];
    let element = arena.comp_type_element(code, Level::zero());
    let twin = arena.comp_type_element(code, Level::zero());
    let higher = arena.comp_type_element(code, one);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    for (left, right, agreement, what) in values {
        assert_eq!(
            convert(&mut context, Pairing::Values(left.into(), right.into())),
            Ok(agreement),
            "{what}"
        );
    }
    assert_eq!(
        convert(&mut context, Pairing::Comps(element.into(), twin.into())),
        Ok(Agreement::Convertible),
        "a decoded computation converts with its twin"
    );
    assert_eq!(
        convert(&mut context, Pairing::Comps(element.into(), higher.into())),
        Ok(Agreement::Apart),
        "decoded computations at different targets are apart"
    );
}

/// A row's signatures meet a wider row's in name order: `{B}` stands below
/// `{A, B}` only when the walk passes over `A` to find `B`, and the wider
/// row does not stand below the narrower one.
#[test]
fn a_row_meets_its_signatures_in_a_wider_row_by_name()
{
    use gandr_core_term::effect::EffectName;
    use gandr_core_term::effect::EffectOp;
    use gandr_core_term::effect::EffectRow;
    use gandr_core_term::effect::EffectSig;
    use gandr_core_term::effect::OperationName;

    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let signature = |name: &str| {
        EffectSig::new(EffectName::from(name), alloc::vec![EffectOp {
            name: OperationName::from("get"),
            payload: unit,
            reply: unit
        }])
        .unwrap()
    };
    let narrow = EffectRow::from_signatures([signature("B")]).unwrap();
    let wide = EffectRow::from_signatures([signature("A"), signature("B")]).unwrap();
    let narrow = arena.comp_type_returner_with_effects(unit, narrow);
    let wide = arena.comp_type_returner_with_effects(unit, wide);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    assert_eq!(
        convert(&mut context, Pairing::SubComps(narrow.into(), wide.into())),
        Ok(Agreement::Convertible),
        "`{{B}}` meets its one signature past `A` in `{{A, B}}`"
    );
    assert_eq!(
        convert(&mut context, Pairing::SubComps(wide.into(), narrow.into())),
        Ok(Agreement::Apart),
        "`{{A, B}}` has a signature `{{B}}` lacks"
    );
}

/// Outside subtyping two capabilities agree only when each authority grants
/// within the other and the grade and region match: a capability converts
/// with its twin, and a wider or narrower authority, another grade or
/// another region sets the pair apart.
#[test]
fn invariant_capabilities_agree_on_authority_grade_and_region()
{
    use gandr_core_term::effect::EffectName;
    use gandr_core_term::effect::EffectOp;
    use gandr_core_term::effect::EffectRow;
    use gandr_core_term::effect::EffectSig;
    use gandr_core_term::effect::OperationName;
    use gandr_core_term::effect::capability::CapabilityGrade;
    use gandr_core_term::effect::capability::Region;
    use gandr_core_term::effect::capability::RegionDepth;

    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let signature = |name: &str| {
        EffectSig::new(EffectName::from(name), alloc::vec![EffectOp {
            name: OperationName::from("get"),
            payload: unit,
            reply: unit
        }])
        .unwrap()
    };
    let both = EffectRow::from_signatures([signature("A"), signature("B")]).unwrap();
    let one = EffectRow::from_signatures([signature("A")]).unwrap();
    let durable = CapabilityGrade::Durable;
    let held = Region::Held;
    let found = arena.value_type_capability(both.clone(), durable, held);
    let twin = arena.value_type_capability(both.clone(), durable, held);
    let narrower = arena.value_type_capability(one, durable, held);
    let consumable = arena.value_type_capability(both.clone(), CapabilityGrade::Consumable, held);
    let scoped =
        arena.value_type_capability(both, durable, Region::Scoped(RegionDepth::from(1_u32)));
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    for (left, right, agreement, what) in [
        (
            found,
            twin,
            Agreement::Convertible,
            "a capability converts with its twin",
        ),
        (
            found,
            narrower,
            Agreement::Apart,
            "a wider authority is apart from a narrower one",
        ),
        (
            narrower,
            found,
            Agreement::Apart,
            "a narrower authority is apart from a wider one",
        ),
        (
            found,
            consumable,
            Agreement::Apart,
            "another grade is apart",
        ),
        (found, scoped, Agreement::Apart, "another region is apart"),
    ] {
        assert_eq!(
            convert(&mut context, Pairing::Values(left.into(), right.into())),
            Ok(agreement),
            "{what}"
        );
    }
}

/// Kept types agree on their region exactly, and a kept type is a subtype
/// of another only where its region outlives the other's, and of the plain
/// type it keeps; a value held at a world and a world's capability agree
/// only at one world.
#[test]
fn kept_and_located_types_agree_on_their_region_and_world()
{
    use gandr_core_term::ValueTypeId;
    use gandr_core_term::effect::capability::Region;
    use gandr_core_term::effect::capability::RegionDepth;
    use gandr_core_term::world::World;
    use gandr_core_term::world::WorldType;

    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let scoped = |depth: u32| Region::Scoped(RegionDepth::from(depth));
    let shallow = arena.value_type_kept(integer, scoped(1));
    let shallow_twin = arena.value_type_kept(integer, scoped(1));
    let deep = arena.value_type_kept(integer, scoped(2));
    let elsewhere = World::Declared(ConstantIndex::from(0_usize));
    let mut located = |inner, world| arena.value_type_world(WorldType::At { inner, world });
    let at_host = located(integer, World::Host);
    let at_host_twin = located(integer, World::Host);
    let at_elsewhere = located(integer, elsewhere);
    let held_host = arena.value_type_world(WorldType::Capability(World::Host));
    let held_host_twin = arena.value_type_world(WorldType::Capability(World::Host));
    let held_elsewhere = arena.value_type_world(WorldType::Capability(elsewhere));
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    let invariant =
        |left: ValueTypeId, right: ValueTypeId| Pairing::Values(left.into(), right.into());
    let sub = |left: ValueTypeId, right: ValueTypeId| Pairing::SubValues(left.into(), right.into());
    for (pairing, agreement, what) in [
        (
            invariant(shallow, shallow_twin),
            Agreement::Convertible,
            "one region agrees",
        ),
        (
            invariant(shallow, deep),
            Agreement::Apart,
            "two regions are apart",
        ),
        (
            sub(shallow, deep),
            Agreement::Convertible,
            "a region outliving another is its subtype",
        ),
        (
            sub(deep, shallow),
            Agreement::Apart,
            "a region outlived by another is not",
        ),
        (
            sub(integer, shallow),
            Agreement::Convertible,
            "a plain value may be kept anywhere",
        ),
        (
            invariant(at_host, at_host_twin),
            Agreement::Convertible,
            "one world agrees",
        ),
        (
            invariant(at_host, at_elsewhere),
            Agreement::Apart,
            "two worlds are apart",
        ),
        (
            invariant(held_host, held_host_twin),
            Agreement::Convertible,
            "one world's capability agrees",
        ),
        (
            invariant(held_host, held_elsewhere),
            Agreement::Apart,
            "two worlds' capabilities are apart",
        ),
    ] {
        assert_eq!(convert(&mut context, pairing), Ok(agreement), "{what}");
    }
}

/// A path type converts with a data type only when the carrier's words name
/// that data type at the endpoints: over a carrier with no words, the path
/// and an unrelated parameterless data type are apart in either order.
#[test]
fn a_path_type_is_apart_from_data_it_does_not_read_as()
{
    let mut arena = CoreArena::new();
    let carrier = arena.value_type_data(ConstantIndex::from(0_usize), alloc::vec![]);
    let unrelated = arena.value_type_data(ConstantIndex::from(1_usize), alloc::vec![]);
    let point = arena.value_constructor(
        carrier,
        gandr_kernel_term::ConstructorTag::from(0_usize),
        alloc::vec![],
    );
    let path = arena.value_type_path(carrier, point, point);
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    assert_eq!(
        convert(&mut context, Pairing::Values(path.into(), unrelated.into())),
        Ok(Agreement::Apart),
        "a path no words read is apart from a data type"
    );
    assert_eq!(
        convert(&mut context, Pairing::Values(unrelated.into(), path.into())),
        Ok(Agreement::Apart),
        "and so is the data type from the path"
    );
}

/// A type read through a relocation converts exactly as the type it settles
/// to. Each former the walk reads through, and a decode beside them, is built
/// over a free type variable at three depths; each is moved by a raise of
/// every free index and by one past a binder it keeps, and compared against
/// every type of the three families, plain and moved alike, invariantly and
/// under subtyping, and across the value bridge: every answer, refusal and
/// count is the settled pair's.
#[test]
fn a_relocated_type_converts_as_its_settled_reading()
{
    use alloc::collections::BTreeMap;
    use alloc::string::String;
    use alloc::vec::Vec;

    use gandr_core_term::Binders;
    use gandr_core_term::Relocated;
    use gandr_core_term::ValueTypeId;
    use gandr_core_term::shift_value_type;
    use gandr_core_term::shift_value_type_under;
    use gandr_kernel_term::FieldLabel;

    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let one = Level::constant(LevelConstant::from(1_u64));
    let unit = arena.value_type_unit();
    let string = arena.value_type_base(BaseType::String);
    let large = arena.value_type_universe(Sort::Ground(GroundSort::Value), one.clone());
    let defined = arena.value_constant(ConstantIndex::from(0_usize));
    let decoded = arena.value_type_element(defined, Level::zero());
    let body = arena.value_quote(integer);
    let at = arena.value_quote(integer);
    let variable = |arena: &mut CoreArena, index: u32| {
        let code = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index));
        arena.value_type_element(code, Level::zero())
    };
    // Every type over the free variable `index`: the dependent pair's second
    // factor and the dependent arrow's codomain read it one binder deeper,
    // so the vacuous dependent arrow is the plain one.
    let family = |arena: &mut CoreArena, index: u32| {
        let free = variable(arena, index);
        let beneath = variable(arena, index.saturating_add(1));
        let bound = variable(arena, 0);
        let returns = arena.comp_type_returner(free);
        let returns_beneath = arena.comp_type_returner(beneath);
        let returns_bound = arena.comp_type_returner(bound);
        let arrow = arena.comp_type_arrow(free, returns);
        let vacuous = arena.comp_type_pi(free, returns_beneath);
        let dependent = arena.comp_type_pi(free, returns_bound);
        let lazy = arena.comp_type_with(&[returns, arrow]);
        let record = arena.value_type_record(BTreeMap::from([(
            FieldLabel::from(String::from("a")),
            free,
        )]));
        Vec::from([
            free,
            arena.value_type_product(&[free, integer]),
            record,
            arena.value_type_sum(&[integer, free]),
            arena.value_type_list(free),
            arena.value_type_thunk(returns),
            arena.value_type_thunk(arrow),
            arena.value_type_thunk(vacuous),
            arena.value_type_thunk(dependent),
            arena.value_type_thunk(lazy),
            arena.value_type_stack(returns, arrow),
            arena.value_type_static_pi(free, free),
            arena.value_type_sigma(free, beneath),
            arena.value_type_lift(free, one.clone()),
            arena.value_type_product(&[decoded, free]),
            arena.value_type_product(&[free, unit, small, string]),
            arena.value_type_product(&[free, large, string]),
            arena.value_type_product(&[free, integer, integer]),
            arena.value_type_lift(free, Level::zero()),
        ])
    };
    let types = [0_u32, 1, 2]
        .into_iter()
        .flat_map(|index| family(&mut arena, index))
        .collect::<Vec<ValueTypeId>>();
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    seed(&mut context, &[small]);
    context.define(
        ConstantIndex::from(0_usize),
        crate::formation::FormedValueType::derived(small),
        body,
    );
    let moves: [fn(&mut CoreArena, ValueTypeId) -> Relocated<ValueTypeId>; 2] = [
        |arena, subject| shift_value_type(arena, subject, Binders::ONE),
        |arena, subject| shift_value_type_under(arena, subject, Binders::ONE, Binders::ONE),
    ];
    let (mut convertible, mut apart) = (0_usize, 0_usize);
    for &subject in &types {
        for relocate in moves {
            let moved = relocate(context.arena_mut(), subject);
            let settled = moved.settle(context.arena_mut());
            for &other in &types {
                let other_moved = relocate(context.arena_mut(), other);
                let other_settled = other_moved.settle(context.arena_mut());
                for (left, right, plain) in [
                    (moved, Relocated::from(other), (settled, other)),
                    (Relocated::from(other), moved, (other, settled)),
                    (moved, other_moved, (settled, other_settled)),
                ] {
                    let wanted = convert(
                        &mut context,
                        Pairing::Values(plain.0.into(), plain.1.into()),
                    );
                    assert_eq!(
                        convert(&mut context, Pairing::Values(left, right)),
                        wanted,
                        "{left:?} against {right:?} answers as {plain:?}"
                    );
                    assert_eq!(
                        convert(&mut context, Pairing::SubValues(left, right)),
                        convert(
                            &mut context,
                            Pairing::SubValues(plain.0.into(), plain.1.into())
                        ),
                        "{left:?} below {right:?} answers as {plain:?}"
                    );
                    match wanted {
                        Ok(Agreement::Convertible) => convertible = convertible.saturating_add(1),
                        Ok(Agreement::Apart) => apart = apart.saturating_add(1),
                        Ok(
                            Agreement::NotBelow { .. } | Agreement::Amplified | Agreement::Escaped,
                        )
                        | Err(_) => {},
                    }
                }
                let (mut relocated_tally, mut settled_tally) =
                    (ConversionCount::default(), ConversionCount::default());
                let crossed = value_bridge(&mut context, at, moved, other, &mut relocated_tally);
                let wanted = value_bridge(&mut context, at, settled, other, &mut settled_tally);
                // The arena shares no trees, so a refusal names the settled
                // type at the id its own settling minted.
                if let (
                    Err(CheckRefusal::TypeMismatch(Mismatch::Value {
                        at: refused_at,
                        synthesised: named,
                        expected,
                    })),
                    Err(CheckRefusal::TypeMismatch(Mismatch::Value {
                        at: wanted_at,
                        synthesised: wanted_named,
                        expected: wanted_expected,
                    })),
                ) = (crossed, wanted)
                {
                    assert_eq!(
                        (refused_at, expected, wanted_named),
                        (wanted_at, wanted_expected, settled),
                        "{moved:?} is refused at {other:?} as {settled:?} is"
                    );
                    assert_eq!(
                        convert(&mut context, Pairing::Values(named.into(), settled.into())),
                        Ok(Agreement::Convertible),
                        "the refusal names {moved:?} settled"
                    );
                }
                else {
                    assert_eq!(
                        crossed, wanted,
                        "{moved:?} crosses to {other:?} as {settled:?} does"
                    );
                }
                assert_eq!(relocated_tally, settled_tally, "and counts as it does");
            }
        }
    }
    assert!(
        convertible > 0 && apart > 0,
        "the pairs agree and differ: {convertible} convertible, {apart} apart"
    );
}
