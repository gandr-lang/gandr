//! Witnesses for conversion: the worklist, its set-aside pairs and the
//! verdicts each forced rule reaches.

use gandr_kernel_strata::Level;
use gandr_kernel_strata::LevelConstant;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::IntegerWidth;
use gandr_kernel_term::Side;
use gandr_kernel_term::TermArena;

use super::ConversionGoal;
use super::Convertibility;
use super::convert_comp_type;
use super::convert_value_type;
use super::convertible_comp_types;
use super::convertible_value_types;
use crate::error::CompTypeHead;
use crate::error::KernelError;
use crate::error::ValueTypeHead;

/// The constant level `value`.
///
/// # Specification
/// trivial.
fn level(value: LevelConstant) -> Level
{
    Level::constant(value)
}

#[test]
fn value_type_conversion_is_reflexive()
{
    let mut arena = TermArena::new();
    let unit = arena.value_type_unit();
    let base = arena.value_type_base(BaseType::Integer);
    let product = arena.value_type_product(&[unit, base]);
    assert_eq!(
        Convertibility::Convertible,
        convertible_value_types(&arena, product, product),
        "a type converts with itself"
    );
}

#[test]
fn computation_type_conversion_is_reflexive()
{
    let mut arena = TermArena::new();
    let unit = arena.value_type_unit();
    let returner = arena.comp_type_returner(unit);
    let arrow = arena.comp_type_arrow(unit, returner);
    assert_eq!(
        Convertibility::Convertible,
        convertible_comp_types(&arena, arrow, arrow),
        "a computation type converts with itself"
    );
}

#[test]
fn structurally_equal_types_at_distinct_ids_convert()
{
    let mut arena = TermArena::new();
    let first_unit = arena.value_type_unit();
    let second_unit = arena.value_type_unit();
    let first = arena.value_type_product(&[first_unit, first_unit]);
    let second = arena.value_type_product(&[second_unit, second_unit]);
    assert_ne!(first, second, "the fixture mints two distinct arena nodes");
    assert_eq!(
        Convertibility::Convertible,
        convertible_value_types(&arena, first, second),
        "the id fast path is positive only: unequal ids decide nothing and the structural \
             walk decides"
    );
}

#[test]
fn related_pairs_set_aside_path_endpoints()
{
    let mut arena = TermArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let string = arena.value_type_base(BaseType::String);
    let first = arena.value_variable(DeBruijnIndex::from(0_u32));
    let second = arena.value_variable(DeBruijnIndex::from(1_u32));
    let one = arena.value_type_path(integer, first, second);
    let other = arena.value_type_path(integer, second, first);
    let mut pending = alloc::vec::Vec::new();
    assert_eq!(
        super::related_pairs(
            &arena,
            &crate::presented::FREE,
            super::ConversionGoal::ValueType(one, other),
            &mut pending
        ),
        Convertibility::Convertible,
        "differing endpoints are left to the caller"
    );
    assert_eq!(pending, [
        super::SetAside::Values(first, second),
        super::SetAside::Values(second, first)
    ]);
    assert_eq!(
        convertible_value_types(&arena, one, other),
        Convertibility::Distinct,
        "the structural walk compares the same endpoints"
    );
    let apart = arena.value_type_path(string, second, first);
    let mut pending = alloc::vec::Vec::new();
    assert_eq!(
        super::related_pairs(
            &arena,
            &crate::presented::FREE,
            super::ConversionGoal::ValueType(one, apart),
            &mut pending
        ),
        Convertibility::Distinct,
        "a differing domain still separates"
    );
}

#[test]
fn a_presented_constructor_is_set_aside_on_either_side()
{
    use gandr_kernel_strata::Level;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::ConstructorTag;
    use gandr_kernel_term::GroundSort;
    use gandr_kernel_term::LevelSignature;
    use gandr_kernel_term::Presentation;
    use gandr_kernel_term::PresentedRule;
    use gandr_kernel_term::RuleNode;
    use gandr_kernel_term::RuleVariable;

    let looped = ConstructorTag::from(1_usize);
    let x = RuleNode::Variable(RuleVariable::from(0_u32));
    let rules = Presentation::new(alloc::vec![PresentedRule::new(
        [
            RuleNode::Constructor(looped),
            RuleNode::Constructor(looped),
            x
        ]
        .into(),
        [x].into(),
    )]);
    let mut environment = crate::env::Environment::new();
    let mut staging = environment.stage();
    let kind = staging
        .arena()
        .value_type_universe(GroundSort::Value, Level::zero());
    let own = staging
        .arena()
        .value_type_data(ConstantIndex::from(0_usize), alloc::vec::Vec::new());
    let staged = staging
        .data(
            LevelSignature::monomorphic(),
            alloc::vec::Vec::new(),
            alloc::vec![alloc::vec![], alloc::vec![own]],
            kind,
        )
        .presented(rules);
    let _sort = environment.add_decl(staged).expect("the sort admits");
    let presentations = crate::presented::Presentations::of(environment.entries());
    let mut arena = environment.arena().clone();
    let own = arena.value_type_data(ConstantIndex::from(0_usize), alloc::vec::Vec::new());
    let base = arena.value_constructor(own, ConstructorTag::from(0_usize), alloc::vec::Vec::new());
    let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
    for (left, right) in [(variable, base), (base, variable)] {
        let mut pending = alloc::vec::Vec::new();
        assert_eq!(
            super::pending_endpoints(
                &arena,
                &presentations,
                super::ConversionGoal::Value(left, right),
                &mut pending
            ),
            Convertibility::Convertible
        );
        assert_eq!(pending, [super::SetAside::Values(left, right)]);
    }
}

#[test]
fn a_decode_of_a_returned_code_is_set_aside_against_another_former()
{
    // `El(⟨c⟩)` for a returned code against `Integer` is set aside, in
    // either order, for the caller to read; the plain walk, which reads
    // nothing, separates the two. A decode of a variable code is no
    // reduction and separates in place.
    let mut arena = TermArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
    let forced = arena.computation_force(variable);
    let code = arena.value_returned(forced);
    let decoded = arena.value_type_element(code, Level::zero());
    let rigid = arena.value_type_element(variable, Level::zero());
    for (one, other) in [(decoded, integer), (integer, decoded)] {
        let mut pending = alloc::vec::Vec::new();
        assert_eq!(
            super::pending_endpoints(
                &arena,
                &crate::presented::FREE,
                super::ConversionGoal::ValueType(one, other),
                &mut pending
            ),
            Convertibility::Convertible,
            "the decode waits to be read"
        );
        assert_eq!(pending, [super::SetAside::Decoded {
            code,
            other: integer
        }]);
        assert_eq!(
            convertible_value_types(&arena, one, other),
            Convertibility::Distinct
        );
    }
    let mut pending = alloc::vec::Vec::new();
    assert_eq!(
        super::pending_endpoints(
            &arena,
            &crate::presented::FREE,
            super::ConversionGoal::ValueType(rigid, integer),
            &mut pending
        ),
        Convertibility::Distinct
    );
    assert!(pending.is_empty());
}

#[test]
fn a_thunk_pair_forcing_a_thunk_is_set_aside_3733()
{
    // `thunk { λz. force (thunk (c x)) z }` against `thunk { λz. c(x, z) }`
    // holds a β-redex the walk cannot read, so the pair waits for a reader
    // that reduces; the plain walk separates the two. Two thunks forcing no
    // thunk literal separate in place.
    let mut arena = TermArena::new();
    let constant = arena.value_constant(ConstantIndex::from(0_usize));
    let x = arena.value_variable(DeBruijnIndex::from(1_u32));
    let z = arena.value_variable(DeBruijnIndex::from(0_u32));
    let forced = arena.computation_force(constant);
    let partial = arena.computation_application(forced, x);
    let recursion = arena.value_thunk(partial);
    let forced_recursion = arena.computation_force(recursion);
    let redex = arena.computation_application(forced_recursion, z);
    let redex = arena.computation_lambda(redex);
    let redex = arena.value_thunk(redex);
    let call = arena.computation_application(partial, z);
    let call = arena.computation_lambda(call);
    let call = arena.value_thunk(call);
    for (left, right) in [(redex, call), (call, redex)] {
        let mut pending = alloc::vec::Vec::new();
        assert_eq!(
            super::pending_endpoints(
                &arena,
                &crate::presented::FREE,
                super::ConversionGoal::Value(left, right),
                &mut pending
            ),
            Convertibility::Convertible,
            "the thunks wait to be read"
        );
        assert_eq!(pending, [super::SetAside::Values(left, right)]);
    }
    let returns_x = arena.computation_return(x);
    let returns_x = arena.value_thunk(returns_x);
    let mut pending = alloc::vec::Vec::new();
    assert_eq!(
        super::pending_endpoints(
            &arena,
            &crate::presented::FREE,
            super::ConversionGoal::Value(call, returns_x),
            &mut pending
        ),
        Convertibility::Distinct,
        "two thunks forcing no thunk separate in place"
    );
    assert!(pending.is_empty());
}

#[test]
fn conversion_separates_every_former()
{
    let mut arena = TermArena::new();
    let unit = arena.value_type_unit();
    let integer = arena.value_type_base(BaseType::Integer);
    let string = arena.value_type_base(BaseType::String);
    let numeric = arena.value_type_base(BaseType::Numeric);
    let character = arena.value_type_base(BaseType::Character);
    let [u32_width, u64_width, i32_width, i64_width] = [
        IntegerWidth::U32,
        IntegerWidth::U64,
        IntegerWidth::I32,
        IntegerWidth::I64,
    ]
    .map(|width| arena.value_type_base(BaseType::Fixed(width)));
    let product = arena.value_type_product(&[unit, integer]);
    let sum = arena.value_type_sum(&[unit, integer]);
    let returner = arena.comp_type_returner(unit);
    let thunk = arena.value_type_thunk(returner);
    let universe = arena.value_type_universe(GroundSort::Value, Level::zero());
    let atom = arena.value_type_abstract(ConstantIndex::from(0_usize));
    let code = arena.value_variable(DeBruijnIndex::from(0_u32));
    let element = arena.value_type_element(code, Level::zero());
    let lift = arena.value_type_lift(unit, level(LevelConstant::from(1)));
    let static_pi = arena.value_type_static_pi(universe, universe);
    let formers = [
        unit, integer, string, numeric, character, u32_width, u64_width, i32_width, i64_width,
        product, sum, thunk, universe, atom, element, lift, static_pi,
    ];
    for (one, left) in formers.iter().copied().enumerate() {
        for (other, right) in formers.iter().copied().enumerate() {
            let expected = if one == other {
                Convertibility::Convertible
            }
            else {
                Convertibility::Distinct
            };
            assert_eq!(
                expected,
                convertible_value_types(&arena, left, right),
                "formers {one}/{other}: distinct formers or base atoms separate in both directions"
            );
        }
    }
    let transposed = arena.value_type_product(&[integer, unit]);
    assert_eq!(
        Convertibility::Distinct,
        convertible_value_types(&arena, product, transposed),
        "and the children are compared in order"
    );
}

#[test]
fn universes_convert_by_canonical_level()
{
    let mut arena = TermArena::new();
    let zero = arena.value_type_universe(GroundSort::Value, level(LevelConstant::from(0)));
    let also_zero = arena.value_type_universe(GroundSort::Value, level(LevelConstant::from(0)));
    let one = arena.value_type_universe(GroundSort::Value, level(LevelConstant::from(1)));
    assert_eq!(
        Convertibility::Convertible,
        convertible_value_types(&arena, zero, also_zero),
        "one level is one universe"
    );
    assert_eq!(
        Convertibility::Distinct,
        convertible_value_types(&arena, zero, one),
        "and two levels are two universes"
    );
    let lift_zero = arena.value_type_lift(zero, level(LevelConstant::from(4)));
    let lift_five = arena.value_type_lift(zero, level(LevelConstant::from(5)));
    assert_eq!(
        Convertibility::Distinct,
        convertible_value_types(&arena, lift_zero, lift_five),
        "a lift's target is part of its identity"
    );
}

#[test]
fn sealed_atoms_are_nominal()
{
    let mut arena = TermArena::new();
    let first = arena.value_type_abstract(ConstantIndex::from(0_usize));
    let also_first = arena.value_type_abstract(ConstantIndex::from(0_usize));
    let second = arena.value_type_abstract(ConstantIndex::from(1_usize));
    let unit = arena.value_type_unit();
    let integer = arena.value_type_base(BaseType::Integer);
    assert_eq!(
        Convertibility::Convertible,
        convertible_value_types(&arena, first, also_first),
        "two references to one atom are one type"
    );
    assert_eq!(
        Convertibility::Distinct,
        convertible_value_types(&arena, first, second),
        "two atoms are two types however they were implemented"
    );
    for structural in [unit, integer] {
        assert_eq!(
            (Convertibility::Distinct, Convertibility::Distinct),
            (
                convertible_value_types(&arena, first, structural),
                convertible_value_types(&arena, structural, first),
            ),
            "and no arm relates an atom to a structural type in either direction, which is \
                 what opacity means here"
        );
    }
}

#[test]
fn an_arrow_separates_on_either_child()
{
    let mut arena = TermArena::new();
    let unit = arena.value_type_unit();
    let integer = arena.value_type_base(BaseType::Integer);
    let unit_returner = arena.comp_type_returner(unit);
    let integer_returner = arena.comp_type_returner(integer);
    let base = arena.comp_type_arrow(unit, unit_returner);
    let other_domain = arena.comp_type_arrow(integer, unit_returner);
    let other_codomain = arena.comp_type_arrow(unit, integer_returner);
    assert_eq!(
        Convertibility::Distinct,
        convertible_comp_types(&arena, base, other_domain),
        "the domain is compared"
    );
    assert_eq!(
        Convertibility::Distinct,
        convertible_comp_types(&arena, base, other_codomain),
        "and so is the codomain"
    );
}

/// The structural walk separates the two arrows on their head, and the
/// dependent one still compares child for child with itself.
///
/// The two formers hold the *same* two children here, so comparing their
/// children as they stand would have equated a codomain in the ambient context
/// with one under a binder; the walk mints nothing to weaken the plain one,
/// so it keeps them apart and leaves the pair to the readers that do
/// (`a_vacuous_dependent_arrow_is_the_plain_arrow_577`).
#[test]
fn the_structural_walk_keeps_the_two_arrows_apart()
{
    let mut arena = TermArena::new();
    let unit = arena.value_type_unit();
    let integer = arena.value_type_base(BaseType::Integer);
    let returner = arena.comp_type_returner(unit);
    let plain = arena.comp_type_arrow(unit, returner);
    let dependent = arena.comp_type_pi(unit, returner);
    assert_eq!(
        Convertibility::Distinct,
        convertible_comp_types(&arena, plain, dependent),
        "a non-dependent arrow and a dependent one are two types over the same children"
    );
    let also_dependent = arena.comp_type_pi(unit, returner);
    assert_eq!(
        Convertibility::Convertible,
        convertible_comp_types(&arena, dependent, also_dependent),
        "and two dependent arrows over equal children convert"
    );
    let other_domain = arena.comp_type_pi(integer, returner);
    assert_eq!(
        Convertibility::Distinct,
        convertible_comp_types(&arena, dependent, other_domain),
        "with the domain compared"
    );
    let integer_returner = arena.comp_type_returner(integer);
    let other_codomain = arena.comp_type_pi(unit, integer_returner);
    assert_eq!(
        Convertibility::Distinct,
        convertible_comp_types(&arena, dependent, other_codomain),
        "and the codomain compared too"
    );
}

/// #577: a dependent arrow whose codomain ignores its binder is the plain
/// arrow, in either order, once the plain codomain is weakened past the
/// binder; one whose codomain names its binder is not, and neither is one
/// whose domain differs.
///
/// The naming pair is the one that pins the weakening: both codomains read
/// `F El(#0)`, so comparing them as they stand would convert two types that
/// name different variables, and the dependent codomain `F El(#1)` — the
/// ambient `#0` seen under the binder — converts with the plain one.
#[test]
fn a_vacuous_dependent_arrow_is_the_plain_arrow_577()
{
    use gandr_kernel_term::CompType;

    use super::Codomains;
    use super::SetAside;
    use crate::replay::EndpointReading;
    use crate::replay::ReplayBudget;
    use crate::replay::Unfoldings;

    let mut arena = TermArena::new();
    let unit = arena.value_type_unit();
    let integer = arena.value_type_base(BaseType::Integer);
    let closed = arena.comp_type_returner(unit);
    let naming = |arena: &mut TermArena, index: u32| {
        let code = arena.value_variable(DeBruijnIndex::from(index));
        let decoded = arena.value_type_element(code, Level::zero());
        arena.comp_type_returner(decoded)
    };
    let (inner, outer) = (naming(&mut arena, 0), naming(&mut arena, 1));
    let pair = |arena: &mut TermArena, domain, dependent, plain| {
        (
            arena.comp_type_pi(domain, dependent),
            arena.comp_type_arrow(unit, plain),
        )
    };
    let cases = [
        (
            pair(&mut arena, unit, closed, closed),
            Convertibility::Convertible,
            EndpointReading::Converts,
            "a closed codomain ignores the binder",
        ),
        (
            pair(&mut arena, unit, outer, inner),
            Convertibility::Convertible,
            EndpointReading::Converts,
            "a codomain naming the ambient variable past the binder ignores it",
        ),
        (
            pair(&mut arena, unit, inner, inner),
            Convertibility::Distinct,
            EndpointReading::Apart,
            "a codomain naming the binder does not ignore it",
        ),
    ];
    for ((dependent, plain), verdict, reading, what) in cases {
        for goal in [
            ConversionGoal::CompType(dependent, plain),
            ConversionGoal::CompType(plain, dependent),
        ] {
            let before = arena.watermark();
            assert_eq!(super::equal_weakened(&mut arena, goal), verdict, "{what}");
            assert_eq!(arena.watermark(), before, "{what}: nothing is kept");
            let mut pending = alloc::vec::Vec::new();
            assert_eq!(
                super::pending_endpoints(&arena, &crate::presented::FREE, goal, &mut pending),
                Convertibility::Convertible,
                "{what}: the codomains wait to be read"
            );
            let Some(&CompType::Pi { codomain, .. }) = arena.comp_type(dependent)
            else {
                panic!("{what}: the dependent side is a dependent arrow");
            };
            let Some(&CompType::Arrow {
                codomain: plain_codomain,
                ..
            }) = arena.comp_type(plain)
            else {
                panic!("{what}: the plain side is a plain arrow");
            };
            assert_eq!(pending, [SetAside::Codomains(Codomains {
                dependent: codomain,
                plain: plain_codomain
            })]);
            assert_eq!(
                crate::replay::read_endpoints(
                    &mut arena,
                    &Unfoldings::default(),
                    &pending,
                    ReplayBudget::DEFAULT,
                    crate::replay::StuckEndpoints::Structural,
                ),
                reading,
                "{what}: read at a mode switch"
            );
        }
        assert_eq!(
            convertible_comp_types(&arena, dependent, plain),
            Convertibility::Distinct,
            "{what}: the structural walk keeps the two apart"
        );
    }
    let (dependent, plain) = pair(&mut arena, integer, closed, closed);
    let mut pending = alloc::vec::Vec::new();
    assert_eq!(
        super::pending_endpoints(
            &arena,
            &crate::presented::FREE,
            ConversionGoal::CompType(dependent, plain),
            &mut pending
        ),
        Convertibility::Distinct,
        "a differing domain still separates"
    );
    assert_eq!(
        super::equal_weakened(&mut arena, ConversionGoal::CompType(dependent, plain)),
        Convertibility::Distinct
    );
}

/// Two types read off codes converge exactly when the codes do, and the
/// comparison descends into the term language to decide it.
///
/// The separating half is the one that matters: without a term arm the walk
/// would have had to answer on the two `Element` nodes alone, and any
/// answer it gave would have been wrong for one of these pairs.
#[test]
fn types_read_off_codes_converge_with_their_codes()
{
    let mut arena = TermArena::new();
    let zero = level(LevelConstant::from(0));
    let one_code = arena.value_variable(DeBruijnIndex::from(0_u32));
    let other_code = arena.value_variable(DeBruijnIndex::from(1_u32));
    let one = arena.value_type_element(one_code, zero.clone());
    let same_code = arena.value_variable(DeBruijnIndex::from(0_u32));
    let also_one = arena.value_type_element(same_code, zero.clone());
    let other = arena.value_type_element(other_code, zero);
    assert_eq!(
        Convertibility::Convertible,
        convertible_value_types(&arena, one, also_one),
        "two spellings of one code are one type"
    );
    assert_eq!(
        Convertibility::Distinct,
        convertible_value_types(&arena, one, other),
        "and two different codes are two types"
    );
    let higher = arena.value_type_element(one_code, level(LevelConstant::from(1)));
    assert_eq!(
        Convertibility::Distinct,
        convertible_value_types(&arena, one, higher),
        "the carried universe is compared canonically too"
    );
    let unit = arena.value_type_unit();
    assert_eq!(
        Convertibility::Distinct,
        convertible_value_types(&arena, one, unit),
        "and no arm relates a code-read type to a structural one"
    );
}

/// Selected term-form counterexamples make the descent into terms a real
/// comparison rather than a reflexivity check.
///
/// A code is compared **without reducing**, so two applications separate on
/// their head and argument rather than on what they would evaluate to —
/// the incompleteness the convertibility machine closes, pinned here so it
/// is a recorded property rather than a surprise.
#[test]
fn code_comparison_separates_selected_term_forms_without_reducing()
{
    let mut arena = TermArena::new();
    let zero = level(LevelConstant::from(0));
    let element = |arena: &mut TermArena, code| {
        let target = zero.clone();
        arena.value_type_element(code, target)
    };
    let unit = arena.value_unit();
    let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
    let constant = arena.value_constant(ConstantIndex::from(0_usize));
    let other_constant = arena.value_constant(ConstantIndex::from(1_usize));
    let pair = arena.value_tuple(&[unit, variable]);
    let transposed = arena.value_tuple(&[variable, unit]);
    let left = arena.value_injection(Side::Left.into(), unit);
    let right = arena.value_injection(Side::Right.into(), unit);
    let returner = arena.computation_return(unit);
    let force = arena.computation_force(unit);
    let thunk = arena.value_thunk(returner);
    let forced_thunk = arena.value_thunk(force);

    let separated = [
        (unit, variable),
        (constant, other_constant),
        (pair, transposed),
        (left, right),
        (thunk, forced_thunk),
    ];
    for (one, other) in separated {
        let one = element(&mut arena, one);
        let other = element(&mut arena, other);
        assert_eq!(
            Convertibility::Distinct,
            convertible_value_types(&arena, one, other),
            "distinct codes do not convert"
        );
    }

    // The redex and its contractum: sound to separate, and incomplete.
    let identity_body = arena.computation_return(variable);
    let identity = arena.computation_lambda(identity_body);
    let redex = arena.computation_application(identity, unit);
    let redex_code = arena.value_thunk(redex);
    let contractum = arena.computation_return(unit);
    let contractum_code = arena.value_thunk(contractum);
    let redex_type = element(&mut arena, redex_code);
    let contractum_type = element(&mut arena, contractum_code);
    assert_eq!(
        Convertibility::Distinct,
        convertible_value_types(&arena, redex_type, contractum_type),
        "no reduction fires here, so a redex and its contractum separate"
    );
}

/// The intensional claim, exhibited rather than timed: two self-similar
/// composites whose tree expansion is over a billion pairs converge, and
/// converge fast, because each distinct pair is compared once.
///
/// Without the discharged set this comparison walks `2^depth` pairs and
/// does not finish; the depth is asserted through the arena's own node
/// count so the case cannot degenerate into a shallow composite and
/// keep passing.
#[test]
fn a_shared_composite_converts_without_expanding()
{
    let mut arena = TermArena::new();
    let mut left = arena.value_type_unit();
    let mut right = arena.value_type_unit();
    for _step in 0 .. 30_u32 {
        left = arena.value_type_product(&[left, left]);
        right = arena.value_type_product(&[right, right]);
    }
    assert_ne!(
        left, right,
        "the two spellings are distinct arena nodes at every level, so the id fast path \
             discharges nothing above the leaves"
    );
    assert_eq!(
        Convertibility::Convertible,
        convertible_value_types(&arena, left, right),
        "two structurally equal composites converge in their distinct pairs, not their \
             occurrences"
    );

    // And the separating direction on the same shape, so the set is not
    // hiding a difference.
    let integer = arena.value_type_base(BaseType::Integer);
    let mut other = integer;
    for _step in 0 .. 30_u32 {
        other = arena.value_type_product(&[other, other]);
    }
    assert_eq!(
        Convertibility::Distinct,
        convertible_value_types(&arena, left, other),
        "a composite over a different leaf still separates"
    );
}

#[test]
fn identity_requires_a_readable_root_in_every_family()
{
    let mut arena = TermArena::new();
    let live_value_type = arena.value_type_unit();
    let live_comp_type = arena.comp_type_returner(live_value_type);
    let live_value = arena.value_unit();
    let live_computation = arena.computation_return(live_value);
    let floor = arena.watermark();
    let stale_value_type = arena.value_type_unit();
    let stale_comp_type = arena.comp_type_returner(live_value_type);
    let stale_value = arena.value_unit();
    let stale_computation = arena.computation_return(live_value);
    arena.truncate_to(floor);
    let cases = [
        ("value type", [
            convertible_value_types(&arena, live_value_type, live_value_type),
            convertible_value_types(&arena, stale_value_type, stale_value_type),
            convertible_value_types(&arena, live_value_type, stale_value_type),
            convertible_value_types(&arena, stale_value_type, live_value_type),
        ]),
        ("computation type", [
            convertible_comp_types(&arena, live_comp_type, live_comp_type),
            convertible_comp_types(&arena, stale_comp_type, stale_comp_type),
            convertible_comp_types(&arena, live_comp_type, stale_comp_type),
            convertible_comp_types(&arena, stale_comp_type, live_comp_type),
        ]),
        ("value", [
            super::equal_values(&arena, live_value, live_value),
            super::equal_values(&arena, stale_value, stale_value),
            super::equal_values(&arena, live_value, stale_value),
            super::equal_values(&arena, stale_value, live_value),
        ]),
        ("computation", [
            super::equal_weakened(
                &mut arena,
                ConversionGoal::Computation(live_computation, live_computation),
            ),
            super::equal_weakened(
                &mut arena,
                ConversionGoal::Computation(stale_computation, stale_computation),
            ),
            super::equal_weakened(
                &mut arena,
                ConversionGoal::Computation(live_computation, stale_computation),
            ),
            super::equal_weakened(
                &mut arena,
                ConversionGoal::Computation(stale_computation, live_computation),
            ),
        ]),
    ];
    for (family, observed) in cases {
        assert_eq!(
            observed,
            [
                Convertibility::Convertible,
                Convertibility::Distinct,
                Convertibility::Distinct,
                Convertibility::Distinct,
            ],
            "{family}: identity requires readability; either unreadable side refuses"
        );
    }
}

#[test]
fn an_unreadable_id_fails_closed()
{
    let mut arena = TermArena::new();
    let floor = arena.watermark();
    let unit = arena.value_type_unit();
    let other = arena.value_type_base(BaseType::Integer);
    arena.truncate_to(floor);
    assert_eq!(
        Convertibility::Distinct,
        convertible_value_types(&arena, unit, other),
        "an id that resolves to nothing refuses rather than converting"
    );
}

#[test]
fn a_value_mismatch_names_both_heads()
{
    let mut arena = TermArena::new();
    let unit = arena.value_type_unit();
    let integer = arena.value_type_base(BaseType::Integer);
    assert_eq!(
        Ok(()),
        convert_value_type(&arena, unit, unit),
        "a converting pair passes"
    );
    let refused = convert_value_type(&arena, unit, integer);
    let KernelError::ValueTypeMismatch(mismatch) = refused.expect_err("a separating pair refuses")
    else {
        panic!("the refusal is a value-type mismatch");
    };
    assert_eq!(ValueTypeHead::Product, mismatch.expected().head());
    assert_eq!(ValueTypeHead::Base, mismatch.actual().head());
    assert_ne!(
        mismatch.expected().digest(),
        mismatch.actual().digest(),
        "and the two are separated by content, not only by head"
    );
}

#[test]
fn a_computation_mismatch_names_both_heads()
{
    let mut arena = TermArena::new();
    let unit = arena.value_type_unit();
    let returner = arena.comp_type_returner(unit);
    let arrow = arena.comp_type_arrow(unit, returner);
    assert_eq!(Ok(()), convert_comp_type(&arena, returner, returner));
    let refused = convert_comp_type(&arena, returner, arrow);
    let KernelError::ComputationTypeMismatch(mismatch) =
        refused.expect_err("a separating pair refuses")
    else {
        panic!("the refusal is a computation-type mismatch");
    };
    assert_eq!(CompTypeHead::Returner, mismatch.expected().head());
    assert_eq!(CompTypeHead::Arrow, mismatch.actual().head());
}

/// Every former whose children line up only when its own shape agrees —
/// labels, tags, arities, levels, stages, graphs, programs, sides — is
/// distinct where that shape differs and its children agree, and
/// converts where both agree.
#[test]
#[expect(
    clippy::too_many_lines,
    reason = "one pair per guarded former, each built in place"
)]
fn a_former_compares_its_children_only_where_its_shape_agrees()
{
    use alloc::collections::BTreeMap;
    use alloc::string::String;
    use alloc::sync::Arc;
    use alloc::vec::Vec;

    use gandr_kernel_term::Component;
    use gandr_kernel_term::ConstructorTag;
    use gandr_kernel_term::EvaluationComponent;
    use gandr_kernel_term::EvaluationDialogues;
    use gandr_kernel_term::FieldLabel;
    use gandr_kernel_term::HigherDepth;
    use gandr_kernel_term::HigherProgram;
    use gandr_kernel_term::LayerPosition;
    use gandr_kernel_term::QuantifiedStep;
    use gandr_kernel_term::Stage;
    use gandr_kernel_term::StageId;
    use gandr_kernel_term::session::Graph;
    use gandr_kernel_term::session::Node;
    use gandr_kernel_term::session::State;

    use super::equal_values;
    use super::equal_weakened;

    let mut arena = TermArena::new();
    let label = |name: &str| FieldLabel::from(String::from(name));
    let (zero, one) = (level(LevelConstant::from(0)), level(LevelConstant::from(1)));
    let unit_type = arena.value_type_unit();
    let unit = arena.value_unit();
    let returner = arena.comp_type_returner(unit_type);
    let returned = arena.computation_return(unit);

    // Value types: record labels, session graphs, stages.
    let record_type = |arena: &mut TermArena, name: &str| {
        arena.value_type_record(BTreeMap::from([(label(name), unit_type)]))
    };
    let session = |arena: &mut TermArena, root: usize| {
        let graph = Arc::new(Graph {
            root: State(root),
            nodes: alloc::vec![Node::End, Node::End],
        });
        arena.value_type_session(graph, unit_type)
    };
    let staged = |arena: &mut TermArena, stage: usize| {
        arena.value_type_staged(unit_type, Stage::At(StageId::from(stage)))
    };
    let types = [
        (
            record_type(&mut arena, "a"),
            record_type(&mut arena, "b"),
            "record labels",
        ),
        (
            session(&mut arena, 0),
            session(&mut arena, 1),
            "session graphs",
        ),
        (staged(&mut arena, 0), staged(&mut arena, 1), "stages"),
    ];
    for (left, right, what) in types {
        assert_eq!(
            convertible_value_types(&arena, left, right),
            Convertibility::Distinct,
            "{what} differ"
        );
    }
    let (a, also_a) = (record_type(&mut arena, "a"), record_type(&mut arena, "a"));
    assert_eq!(
        convertible_value_types(&arena, a, also_a),
        Convertibility::Convertible,
        "record types with one label set convert"
    );
    let element = |arena: &mut TermArena, at: Level| arena.comp_type_element(unit, at);
    let (low, high) = (
        element(&mut arena, zero.clone()),
        element(&mut arena, one.clone()),
    );
    assert_eq!(
        convertible_comp_types(&arena, low, high),
        Convertibility::Distinct,
        "element types at two levels"
    );

    // Values: tags, record labels, programs, evidence and component
    // counts, step shapes, child counts, lift levels.
    let constructor = |arena: &mut TermArena, tag: usize| {
        arena.value_constructor(unit_type, ConstructorTag::from(tag), Vec::new())
    };
    let record = |arena: &mut TermArena, name: &str| {
        arena.value_record(BTreeMap::from([(label(name), unit)]))
    };
    let higher = |arena: &mut TermArena, depth: u32, count: usize| {
        let program = Arc::new(HigherProgram {
            depth: HigherDepth(depth),
            root: LayerPosition(0),
            layers: Vec::new(),
        });
        arena.value_higher(program, alloc::vec![unit; count].into_boxed_slice())
    };
    let evaluation = |arena: &mut TermArena, count: usize| {
        let component = EvaluationComponent {
            left: unit,
            right: unit,
            evidence: unit,
        };
        let components = alloc::vec![component; count].into_boxed_slice();
        arena.value_higher_evaluation(Arc::from([]), components)
    };
    let quantified = |arena: &mut TermArena, fibre: Option<u32>, count: usize| {
        let step = fibre.map_or_else(
            || QuantifiedStep::Return(EvaluationDialogues::default()),
            |fibre| QuantifiedStep::Apply {
                fibre: DeBruijnIndex::from(fibre),
                dialogues: EvaluationDialogues::default(),
            },
        );
        arena.value_quantified_evaluation(
            Arc::from([step]),
            alloc::vec![unit; count].into_boxed_slice(),
        )
    };
    let lift = |arena: &mut TermArena, at: Level| arena.value_lift(at, unit);
    let values = [
        (
            constructor(&mut arena, 0),
            constructor(&mut arena, 1),
            "constructor tags",
        ),
        (
            record(&mut arena, "a"),
            record(&mut arena, "b"),
            "record labels",
        ),
        (
            higher(&mut arena, 1, 1),
            higher(&mut arena, 2, 1),
            "higher programs",
        ),
        (
            higher(&mut arena, 1, 1),
            higher(&mut arena, 1, 2),
            "higher evidence counts",
        ),
        (
            evaluation(&mut arena, 1),
            evaluation(&mut arena, 2),
            "evaluation component counts",
        ),
        (
            quantified(&mut arena, None, 1),
            quantified(&mut arena, Some(0), 1),
            "quantified step shapes",
        ),
        (
            quantified(&mut arena, None, 1),
            quantified(&mut arena, None, 2),
            "quantified child counts",
        ),
        (lift(&mut arena, zero), lift(&mut arena, one), "lift levels"),
    ];
    for (left, right, what) in values {
        assert_eq!(
            equal_values(&arena, left, right),
            Convertibility::Distinct,
            "{what} differ"
        );
    }
    let twins = [
        (record(&mut arena, "a"), record(&mut arena, "a"), "records"),
        (
            higher(&mut arena, 1, 1),
            higher(&mut arena, 1, 1),
            "higher fields",
        ),
        (
            quantified(&mut arena, Some(0), 1),
            quantified(&mut arena, Some(0), 1),
            "quantified evaluations",
        ),
    ];
    for (left, right, what) in twins {
        assert_eq!(
            equal_values(&arena, left, right),
            Convertibility::Convertible,
            "{what} of one shape and one child convert"
        );
    }

    // Computations: branch counts, labels, components, sides.
    let data_case = |arena: &mut TermArena, count: usize| {
        arena.computation_data_case(unit, returner, alloc::vec![returned; count])
    };
    let case = |arena: &mut TermArena, count: usize| {
        arena.computation_case(unit, &alloc::vec![returned; count])
    };
    let by_label =
        |arena: &mut TermArena, name: &str| arena.computation_record_projection(unit, label(name));
    let by_component = |arena: &mut TermArena, component: usize| {
        arena.computation_tuple_projection(unit, Component::from(component))
    };
    let project = |arena: &mut TermArena, component: usize| {
        arena.computation_project(Component::from(component), returned)
    };
    let with =
        |arena: &mut TermArena, count: usize| arena.computation_with(&alloc::vec![returned; count]);
    let computations = [
        (
            data_case(&mut arena, 1),
            data_case(&mut arena, 2),
            "data-case branch counts",
        ),
        (
            case(&mut arena, 1),
            case(&mut arena, 2),
            "case branch counts",
        ),
        (
            by_label(&mut arena, "a"),
            by_label(&mut arena, "b"),
            "projected labels",
        ),
        (
            by_component(&mut arena, 0),
            by_component(&mut arena, 1),
            "projected components",
        ),
        (
            project(&mut arena, 0),
            project(&mut arena, 2),
            "projected components of a lazy product",
        ),
        (
            with(&mut arena, 1),
            with(&mut arena, 2),
            "lazy product lengths",
        ),
    ];
    for (left, right, what) in computations {
        assert_eq!(
            equal_weakened(&mut arena, ConversionGoal::Computation(left, right)),
            Convertibility::Distinct,
            "{what} differ"
        );
    }
}
