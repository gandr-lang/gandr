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
use crate::refusal::TypeNode;

#[test]
fn one_id_converts_without_being_read()
{
    let mut arena = CoreArena::new();
    let unit = arena.value_type_unit();
    let dangling = dangling_value_type();
    let mut context = CheckingContext::new(&mut arena, CheckBudget::DEFAULT);
    assert_eq!(
        convert(&mut context, Pairing::Values(dangling, dangling)),
        Ok(Agreement::Convertible),
        "one id is one node, so the pair is accepted without its node being read"
    );
    assert_eq!(
        convert(&mut context, Pairing::Values(unit, dangling)),
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
        convert(&mut context, Pairing::Values(left, right)),
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
        convert(&mut context, Pairing::SubComps(pure, effectful)),
        Ok(Agreement::Convertible)
    );
    assert_eq!(
        convert(&mut context, Pairing::SubComps(effectful, pure)),
        Ok(Agreement::Apart)
    );
    assert_eq!(
        convert(&mut context, Pairing::Comps(pure, effectful)),
        Ok(Agreement::Apart)
    );
    assert_eq!(
        convert(
            &mut context,
            Pairing::SubValues(pure_thunk, effectful_thunk)
        ),
        Ok(Agreement::Convertible)
    );
    assert_eq!(
        convert(
            &mut context,
            Pairing::SubComps(accepts_effectful, accepts_pure)
        ),
        Ok(Agreement::Convertible)
    );
    assert_eq!(
        convert(
            &mut context,
            Pairing::SubComps(accepts_pure, accepts_effectful)
        ),
        Ok(Agreement::Apart)
    );
    assert_eq!(
        convert(&mut context, Pairing::SubComps(first, second)),
        Ok(Agreement::Apart)
    );
    assert_eq!(
        convert(&mut context, Pairing::SubComps(second, first)),
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
        convert(&mut context, Pairing::SubValues(narrow, wide)),
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
            convert(&mut context, Pairing::SubValues(sub, sup)),
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
    let pi = arena.comp_type_pi(unit, returns_integer);
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
        Pairing::Values(integer, string),
        Pairing::Values(unit, thunk_integer),
        Pairing::Values(thunk_integer, thunk_string),
        Pairing::Comps(returns_integer, arrow),
        Pairing::Comps(arrow, pi),
        Pairing::Values(small, large),
        Pairing::Values(small, negative),
        Pairing::Values(lifted_once, lifted_twice),
        Pairing::Values(lifted_once, integer),
        Pairing::Values(decode_inner, decode_outer),
        Pairing::Values(loop_path, open_path),
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
        Pairing::Values(unknown, integer),
        Pairing::Values(decode_hole, integer),
        Pairing::Values(decode_marked, decode_variable),
        Pairing::Values(known_left, unknown_left),
        Pairing::Comps(unknown_computation, returns_integer),
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
            Pairing::Values(known_left, unknown_left_string)
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
        convert(&mut context, Pairing::Values(decoded, integer)),
        Ok(Agreement::Convertible),
        "the decode unfolds to the type its body quotes"
    );
    assert_eq!(
        convert(&mut context, Pairing::Comps(under_arrow, plain_arrow)),
        Ok(Agreement::Convertible),
        "and does so beneath every former the walk descends"
    );
    assert_eq!(
        convert(&mut context, Pairing::Values(decoded, string)),
        Ok(Agreement::Apart),
        "the unfolded type is compared, not assumed"
    );
    assert_eq!(
        convert(&mut context, Pairing::Values(rigid, integer)),
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
            Pairing::Values(decoded_instance, written),
            Agreement::Convertible,
            "an instance of a defined operator converts with its reduct",
        ),
        (
            Pairing::Values(at_integer, again),
            Agreement::Convertible,
            "two rigid instances agree by head and argument",
        ),
        (
            Pairing::Values(at_integer, at_string),
            Agreement::Apart,
            "a different argument is apart",
        ),
        (
            Pairing::Values(at_integer, other_head),
            Agreement::Apart,
            "a different head is apart",
        ),
        (
            Pairing::Values(at_identity, at_other_identity),
            Agreement::Convertible,
            "two static lambdas over one body agree",
        ),
        (
            Pairing::Values(at_identity, at_constant),
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
        convert(&mut context, Pairing::Values(unit, dangling)),
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
            convert(&mut context, Pairing::Values(first_tree, first_copy)),
            Ok(Agreement::Convertible),
            "a tree converts with its copy at fresh ids"
        );
        let verdict = convert(&mut context, Pairing::Values(first_tree, second_tree));
        prop_assert_eq!(
            convert(&mut context, Pairing::Values(second_tree, first_tree)),
            verdict,
            "the decision is symmetric"
        );
        prop_assert_eq!(
            convert(&mut context, Pairing::Values(first_copy, second_copy)),
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
            Pairing::Values(atom, other),
            Pairing::Values(other, atom),
            Pairing::SubValues(atom, other),
            Pairing::SubValues(other, atom),
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
        convert(&mut context, Pairing::Values(first, again)),
        Ok(Agreement::Convertible),
        "one atom converts with itself at a fresh id"
    );
    assert_eq!(
        convert(&mut context, Pairing::Values(first, second)),
        Ok(Agreement::Apart),
        "two atoms with one representation stay apart"
    );
}
