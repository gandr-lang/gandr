use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::CoreArena;
use gandr_core_term::DefinitionalEnvironment;
use gandr_core_term::ValueId;
use gandr_core_term::Zone;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;

use super::Alike;
use super::CodeComparison;
use super::ConstantReading;
use super::compare_codes;
use super::motives_alike;
use crate::arena::DomainArena;
use crate::arena::DomainValueId;
use crate::arena::ValueClosureId;
use crate::closure::Environment;
use crate::closure::ValueBody;
use crate::domain::BinderLevel;
use crate::domain::DomainValue;
use crate::domain::Elimination;
use crate::domain::NeutralHead;
use crate::domain::TermFace;
use crate::domain::Unfolding;
use crate::eval::Definitions;
use crate::eval::Fuel;
use crate::eval::LoweredChain;
use crate::eval::eval_value_within;

/// Evaluate the quote `quote` in an environment binding `bound`, outermost
/// first, and name the code's closure.
///
/// # Specification
/// - requires: `quote` is a quote whose free variables `bound` binds.
/// - ensures: the closure the evaluated code suspends.
/// - panics: when the evaluation refuses or produces no code.
///
/// # Adequacy
/// - hypothesis: L2 — one written variable closes over different domain values,
///   while different written indices close over the same value through
///   different environment depths; reversing the supplied binding order or
///   losing a binding changes which codes agree.
/// - witness: `code::tests::a_quoted_variable_is_read_through_the_environment`
#[spec(ensures: |ret| domain.value_closure(ret).is_some_and(|closure| closure.body() == crate::ValueBody::Source(quote)
        && bound.iter().rev().enumerate().all(|(index, value)| u32::try_from(index).is_ok_and(|index|
            closure.environment().lookup(Zone::Intuitionistic, DeBruijnIndex::from(index)) == Some(*value))))) ]
fn code_of(
    core: &CoreArena,
    domain: &mut DomainArena,
    quote: ValueId,
    bound: &[DomainValueId],
) -> ValueClosureId
{
    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut supplied = Environment::new();
    for &value in bound {
        supplied.extend(Zone::Intuitionistic, value);
    }
    let (produced, _) = eval_value_within(
        core,
        domain,
        definitions,
        Fuel::from(64_u32),
        quote,
        supplied,
    )
    .expect("the quote evaluates");
    let Some(&DomainValue::Code { code, .. }) = domain.value(produced)
    else {
        panic!("a quote evaluates to a code");
    };
    code
}

/// A rigid variable neutral at `level`, as an environment holds one.
///
/// # Specification
/// trivial.
fn variable(
    domain: &mut DomainArena,
    level: BinderLevel,
) -> DomainValueId
{
    let neutral = domain
        .neutral_node(
            NeutralHead::Variable {
                zone: Zone::Intuitionistic,
                level,
            },
            Vec::new(),
            Unfolding::Rigid,
        )
        .expect("a neutral with no spine mints");
    domain
        .value_neutral(neutral, TermFace::Reduced)
        .expect("the neutral resolves")
}

/// Compare two codes with no definitions at all, every constant rigid.
///
/// # Specification
/// trivial.
fn compare_rigidly(
    core: &CoreArena,
    domain: &DomainArena,
    left: ValueClosureId,
    right: ValueClosureId,
) -> CodeComparison
{
    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    compare_codes(
        core,
        domain,
        ConstantReading::Read(definitions),
        left,
        right,
    )
    .expect("both closures hold quotes")
}

/// `Thunk(Π(_ : Unit). El(#0, level))` written afresh.
///
/// # Specification
/// trivial.
fn dependent_quote(
    core: &mut CoreArena,
    level: Level,
) -> ValueId
{
    let domain = core.value_type_unit();
    let bound = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let decoded = core.comp_type_element(bound, level);
    let pi = core.comp_type_pi(domain, decoded);
    let thunk = core.value_type_thunk(pi);
    core.value_quote(thunk)
}

#[test]
fn two_quotes_of_one_type_are_equal()
{
    let mut core = CoreArena::new();
    let first = dependent_quote(&mut core, Level::zero());
    let second = dependent_quote(&mut core, Level::zero());
    assert_ne!(first, second, "two nodes, so identity cannot answer");

    let mut domain = DomainArena::new();
    let left = code_of(&core, &mut domain, first, &[]);
    let right = code_of(&core, &mut domain, second, &[]);
    assert_eq!(
        CodeComparison::Equal,
        compare_codes(&core, &domain, ConstantReading::Unread, left, right)
            .expect("both closures hold quotes"),
        "the bound variable names one binder on each side, so the walk matches"
    );

    let third = dependent_quote(&mut core, Level::zero().succ().expect("level one exists"));
    let other = code_of(&core, &mut domain, third, &[]);
    assert_eq!(
        CodeComparison::Apart,
        compare_rigidly(&core, &domain, left, other),
        "a decode at another level is another type, and nothing in either unfolds"
    );
}

#[test]
fn one_body_over_one_environment_is_one_code()
{
    // `⌜Path(Unit, ⟨return #0⟩, ())⌝`: the walk reads a returned endpoint
    // by its place, which two evaluations of the quote do not share, so
    // only the closure itself can answer that the two are one code.
    let mut core = CoreArena::new();
    let carrier = core.value_type_unit();
    let bound = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let returner = core.computation_return(bound);
    let endpoint = core.value_returned(returner);
    let unit = core.value_unit();
    let path = core.value_type_path(carrier, endpoint, unit);
    let quote = core.value_quote(path);

    let mut domain = DomainArena::new();
    let here = variable(&mut domain, BinderLevel::from(0_u32));
    let there = variable(&mut domain, BinderLevel::from(1_u32));
    let one = code_of(&core, &mut domain, quote, &[here]);
    let again = code_of(&core, &mut domain, quote, &[here]);
    assert_ne!(one, again, "two evaluations close over the body twice");
    assert_eq!(
        CodeComparison::Equal,
        compare_rigidly(&core, &domain, one, again),
        "one body over one environment is one code, whatever the body holds"
    );
    let elsewhere = code_of(&core, &mut domain, quote, &[there]);
    assert_ne!(
        CodeComparison::Equal,
        compare_rigidly(&core, &domain, one, elsewhere),
        "the same body over another variable is not answered by the closure"
    );
}

#[test]
fn effect_rows_compare_names_and_scoped_operation_types()
{
    use gandr_core_term::effect::EffectName;
    use gandr_core_term::effect::EffectOp;
    use gandr_core_term::effect::EffectRow;
    use gandr_core_term::effect::EffectSig;
    use gandr_core_term::effect::OperationName;
    let mut core = CoreArena::new();
    let unit = core.value_type_unit();
    let integer = core.value_type_base(BaseType::Integer);
    let unit_quote = core.value_quote(unit);
    let integer_quote = core.value_quote(integer);
    let index = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let parameter = core.value_type_element(index, Level::zero());
    let mut quoted = |effect: &str, operation: &str, reply| {
        let signature = EffectSig::new(EffectName::from(effect), alloc::vec![EffectOp {
            name: OperationName::from(operation),
            payload: unit,
            reply
        }])
        .unwrap();
        let result = core.comp_type_returner_with_effects(unit, EffectRow::singleton(signature));
        core.value_quote_computation(result)
    };
    let dependent = quoted("State", "get", parameter);
    let concrete = quoted("State", "get", unit);
    let other_effect = quoted("Other", "get", unit);
    let other_operation = quoted("State", "put", unit);
    let mut domain = DomainArena::new();
    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let held_unit = eval_value_within(
        &core,
        &mut domain,
        definitions,
        Fuel::from(64_u32),
        unit_quote,
        Environment::new(),
    )
    .unwrap()
    .0;
    let held_integer = eval_value_within(
        &core,
        &mut domain,
        definitions,
        Fuel::from(64_u32),
        integer_quote,
        Environment::new(),
    )
    .unwrap()
    .0;
    let at_unit = code_of(&core, &mut domain, dependent, &[held_unit]);
    let at_integer = code_of(&core, &mut domain, dependent, &[held_integer]);
    let written = code_of(&core, &mut domain, concrete, &[]);
    assert_eq!(
        CodeComparison::Equal,
        compare_rigidly(&core, &domain, at_unit, written)
    );
    assert_eq!(
        CodeComparison::Apart,
        compare_rigidly(&core, &domain, at_integer, written)
    );
    for changed in [other_effect, other_operation] {
        let changed = code_of(&core, &mut domain, changed, &[]);
        assert_eq!(
            CodeComparison::Apart,
            compare_rigidly(&core, &domain, at_unit, changed)
        );
    }
}

#[test]
fn capability_types_compare_grade_region_and_authority_types_373()
{
    use gandr_core_term::effect::EffectName;
    use gandr_core_term::effect::EffectOp;
    use gandr_core_term::effect::EffectRow;
    use gandr_core_term::effect::EffectSig;
    use gandr_core_term::effect::OperationName;
    use gandr_core_term::effect::capability::CapabilityGrade;
    use gandr_core_term::effect::capability::Region;
    use gandr_core_term::effect::capability::RegionDepth;
    let mut core = CoreArena::new();
    let unit = core.value_type_unit();
    let integer = core.value_type_base(BaseType::Integer);
    let mut quoted = |reply, grade, region| {
        let signature = EffectSig::new(EffectName::from("Probe"), alloc::vec![EffectOp {
            name: OperationName::from("ask"),
            payload: unit,
            reply
        }])
        .unwrap();
        let capability = core.value_type_capability(EffectRow::singleton(signature), grade, region);
        core.value_quote(capability)
    };
    let scoped = Region::Scoped(RegionDepth::from(1_u32));
    let held = quoted(unit, CapabilityGrade::Durable, Region::Held);
    let other_reply = quoted(integer, CapabilityGrade::Durable, Region::Held);
    let other_grade = quoted(unit, CapabilityGrade::Consumable, Region::Held);
    let other_region = quoted(unit, CapabilityGrade::Durable, scoped);
    let mut domain = DomainArena::new();
    let [left, right, other_reply, other_grade, other_region] =
        [held, held, other_reply, other_grade, other_region]
            .map(|code| code_of(&core, &mut domain, code, &[]));
    assert_eq!(
        Ok(CodeComparison::Equal),
        compare_codes(&core, &domain, ConstantReading::Unread, left, right),
        "equal grade, region and authority shapes compare their authority types"
    );
    assert_eq!(
        Ok(CodeComparison::Apart),
        compare_codes(&core, &domain, ConstantReading::Unread, left, other_reply),
        "a queued authority type that differs separates the two"
    );
    for changed in [other_grade, other_region] {
        assert_eq!(
            Ok(CodeComparison::Apart),
            compare_codes(&core, &domain, ConstantReading::Unread, left, changed)
        );
    }
}

#[test]
fn control_type_codes_compare_distinct_inputs_and_outputs()
{
    let mut core = CoreArena::new();
    let unit = core.value_type_unit();
    let integer = core.value_type_base(BaseType::Integer);
    let returned_integer = core.comp_type_returner(integer);
    let unit_quote = core.value_quote(unit);
    let integer_quote = core.value_quote(integer);
    let index = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let parameter = core.value_type_element(index, Level::zero());
    let mut quote = |element, reverse| {
        let list = core.value_type_list(element);
        let input = core.comp_type_returner(list);
        let output = if reverse {
            core.comp_type_with(input, returned_integer)
        }
        else {
            core.comp_type_with(returned_integer, input)
        };
        let stack = core.value_type_stack(input, output);
        core.value_quote(stack)
    };
    let dependent = quote(parameter, false);
    let concrete = quote(unit, false);
    let reversed = quote(unit, true);
    let mut domain = DomainArena::new();
    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let held_unit = eval_value_within(
        &core,
        &mut domain,
        definitions,
        Fuel::from(64_u32),
        unit_quote,
        Environment::new(),
    )
    .unwrap()
    .0;
    let held_integer = eval_value_within(
        &core,
        &mut domain,
        definitions,
        Fuel::from(64_u32),
        integer_quote,
        Environment::new(),
    )
    .unwrap()
    .0;
    let at_unit = code_of(&core, &mut domain, dependent, &[held_unit]);
    let at_integer = code_of(&core, &mut domain, dependent, &[held_integer]);
    let written = code_of(&core, &mut domain, concrete, &[]);
    let reversed = code_of(&core, &mut domain, reversed, &[]);
    assert_eq!(
        CodeComparison::Equal,
        compare_rigidly(&core, &domain, at_unit, written)
    );
    assert_eq!(
        CodeComparison::Apart,
        compare_rigidly(&core, &domain, at_integer, written)
    );
    assert_eq!(
        CodeComparison::Apart,
        compare_rigidly(&core, &domain, at_unit, reversed)
    );
}

#[test]
fn rigid_quotes_of_different_types_are_apart()
{
    let mut core = CoreArena::new();
    let unit = core.value_type_unit();
    let unit_quote = core.value_quote(unit);
    let integer = core.value_type_base(BaseType::Integer);
    let integer_quote = core.value_quote(integer);
    let unit_result = core.value_type_unit();
    let returner = core.comp_type_returner(unit_result);
    let computation_quote = core.value_quote_computation(returner);

    let mut domain = DomainArena::new();
    let left = code_of(&core, &mut domain, unit_quote, &[]);
    let right = code_of(&core, &mut domain, integer_quote, &[]);
    let computation = code_of(&core, &mut domain, computation_quote, &[]);
    assert_eq!(
        CodeComparison::Apart,
        compare_codes(&core, &domain, ConstantReading::Unread, left, right)
            .expect("both closures hold quotes"),
        "two closed formers that differ hold nothing that could unfold"
    );
    assert_eq!(
        CodeComparison::Apart,
        compare_codes(&core, &domain, ConstantReading::Unread, left, computation)
            .expect("both closures hold quotes"),
        "and a value-type quote is apart from a computation-type quote"
    );
}

#[test]
fn a_decode_of_a_held_quote_compares_as_its_quoted_type()
{
    // `El x * El x` over `x := ⌜Integer⌝` against `Integer * Integer`, and
    // `El x` over `x := ⌜F Integer⌝` against `F Integer`: the decoding
    // rule a mint fires, fired where the environment holds the quote.
    let mut core = CoreArena::new();
    let integer = core.value_type_base(BaseType::Integer);
    let integer_quote = core.value_quote(integer);
    let returns = core.comp_type_returner(integer);
    let action_quote = core.value_quote_computation(returns);
    let bound = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let decoded = core.value_type_element(bound, Level::zero());
    let squared = core.value_type_product(&[decoded, decoded]);
    let squared_quote = core.value_quote(squared);
    let written = core.value_type_product(&[integer, integer]);
    let written_quote = core.value_quote(written);
    let acting = core.comp_type_element(bound, Level::zero());
    let acting_quote = core.value_quote_computation(acting);
    let string = core.value_type_base(BaseType::String);
    let other = core.value_type_product(&[integer, string]);
    let other_quote = core.value_quote(other);

    let mut domain = DomainArena::new();
    let chain = LoweredChain::new();
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let held = |domain: &mut DomainArena, quote: ValueId| {
        eval_value_within(
            &core,
            domain,
            definitions,
            Fuel::from(64_u32),
            quote,
            Environment::new(),
        )
        .expect("the quote evaluates")
        .0
    };
    let held_integer = held(&mut domain, integer_quote);
    let held_action = held(&mut domain, action_quote);
    let squared_code = code_of(&core, &mut domain, squared_quote, &[held_integer]);
    let written_code = code_of(&core, &mut domain, written_quote, &[]);
    let other_code = code_of(&core, &mut domain, other_quote, &[]);
    let acting_code = code_of(&core, &mut domain, acting_quote, &[held_action]);
    let action_code = code_of(&core, &mut domain, action_quote, &[]);
    assert_eq!(
        compare_rigidly(&core, &domain, squared_code, written_code),
        CodeComparison::Equal,
        "a value decode of a held quote reads as the quoted type"
    );
    assert_eq!(
        compare_rigidly(&core, &domain, acting_code, action_code),
        CodeComparison::Equal,
        "and so does a computation decode of a held computation quote"
    );
    assert_eq!(
        compare_rigidly(&core, &domain, squared_code, other_code),
        CodeComparison::Apart,
        "a decoded side still differs from a type it is not"
    );
}

#[test]
fn a_quote_over_a_defined_constant_is_undecided()
{
    let mut core = CoreArena::new();
    let constant = core.value_constant(ConstantIndex::from(0_usize));
    let decoded = core.value_type_element(constant, Level::zero());
    let decode_quote = core.value_quote(decoded);
    let unit = core.value_type_unit();
    let unit_quote = core.value_quote(unit);

    let mut domain = DomainArena::new();
    let left = code_of(&core, &mut domain, decode_quote, &[]);
    let right = code_of(&core, &mut domain, unit_quote, &[]);
    assert_eq!(
        CodeComparison::Undecided,
        compare_codes(&core, &domain, ConstantReading::Unread, left, right)
            .expect("both closures hold quotes"),
        "read without the definitions, the constant may unfold to the unit's quote"
    );
    assert_eq!(
        CodeComparison::Apart,
        compare_rigidly(&core, &domain, left, right),
        "read through definitions that give it no body, it cannot"
    );
}

#[test]
fn a_quoted_variable_is_read_through_the_environment()
{
    let mut core = CoreArena::new();
    let innermost = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let near = core.value_type_element(innermost, Level::zero());
    let near_quote = core.value_quote(near);
    let outer = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let far = core.value_type_element(outer, Level::zero());
    let far_quote = core.value_quote(far);

    let mut domain = DomainArena::new();
    let x = variable(&mut domain, BinderLevel::from(0_u32));
    let y = variable(&mut domain, BinderLevel::from(1_u32));
    let reads_x_near = code_of(&core, &mut domain, near_quote, &[x]);
    let reads_x_far = code_of(&core, &mut domain, far_quote, &[x, y]);
    let reads_y_near = code_of(&core, &mut domain, near_quote, &[y]);
    assert_eq!(
        CodeComparison::Equal,
        compare_rigidly(&core, &domain, reads_x_near, reads_x_far),
        "two different indices that the two environments resolve to one variable are equal"
    );
    assert_eq!(
        CodeComparison::Apart,
        compare_rigidly(&core, &domain, reads_x_near, reads_y_near),
        "and one index that the environments resolve to two variables is apart"
    );
}

#[test]
fn motives_written_apart_are_alike_read_through_their_environments_650()
{
    // #650: `c. Path(Unit, c, x)` written twice, once over `[x]` reading `x`
    // past the motive's binder as `#1` and once over `[x, y]` as `#2`, is one
    // family though the bodies and the depths differ; the first body over
    // `[y]` reads another variable and is not.
    let mut core = CoreArena::new();
    let unit = core.value_type_unit();
    let family = |core: &mut CoreArena, far: u32| {
        let endpoint = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let captured = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(far));
        core.value_type_path(unit, endpoint, captured)
    };
    let (near, far) = (family(&mut core, 1), family(&mut core, 2));

    let mut domain = DomainArena::new();
    let x = variable(&mut domain, BinderLevel::from(0_u32));
    let y = variable(&mut domain, BinderLevel::from(1_u32));
    let motive = |domain: &mut DomainArena, body, bound: &[DomainValueId]| {
        let mut environment = Environment::new();
        for &value in bound {
            environment.extend(Zone::Intuitionistic, value);
        }
        domain.value_closure_node(ValueBody::ValueType(body), environment)
    };
    let over_x = motive(&mut domain, near, &[x]);
    let over_x_far = motive(&mut domain, far, &[x, y]);
    let over_y = motive(&mut domain, near, &[y]);
    assert_eq!(
        Alike::Same,
        motives_alike(&core, &domain, over_x, over_x_far).expect("both motives resolve"),
        "two bodies reading one captured variable past the binder are one family"
    );
    assert_eq!(
        Alike::Different,
        motives_alike(&core, &domain, over_x, over_y).expect("both motives resolve"),
        "and one body over two different captures is not"
    );
}

#[test]
fn a_vacuous_dependent_arrow_is_the_plain_arrow_577()
{
    // #577: `⌜U(Π(_ : Unit). F Unit)⌝` is `⌜U(Unit -> F Unit)⌝`, in either
    // order, and over `x` the dependent `El(#1)` — `x` seen past the binder —
    // is the plain `El(#0)`; the dependent `El(#0)` names its own binder and
    // is apart from the plain one, which reads `x`.
    let mut core = CoreArena::new();
    let unit = core.value_type_unit();
    let closed = core.comp_type_returner(unit);
    let named = |core: &mut CoreArena, index: u32| {
        let bound = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index));
        core.comp_type_element(bound, Level::zero())
    };
    let (inner, outer) = (named(&mut core, 0), named(&mut core, 1));
    let quote = |core: &mut CoreArena, arrow| {
        let thunk = core.value_type_thunk(arrow);
        core.value_quote(thunk)
    };
    let dependent = |core: &mut CoreArena, codomain| {
        let pi = core.comp_type_pi(unit, codomain);
        quote(core, pi)
    };
    let plain = |core: &mut CoreArena, codomain| {
        let arrow = core.comp_type_arrow(unit, codomain);
        quote(core, arrow)
    };
    let cases = [
        (
            dependent(&mut core, closed),
            plain(&mut core, closed),
            CodeComparison::Equal,
            "a closed codomain ignores the binder",
        ),
        (
            dependent(&mut core, outer),
            plain(&mut core, inner),
            CodeComparison::Equal,
            "a codomain reading the environment past the binder ignores it",
        ),
        (
            dependent(&mut core, inner),
            plain(&mut core, inner),
            CodeComparison::Apart,
            "a codomain naming the binder does not ignore it",
        ),
    ];

    let mut domain = DomainArena::new();
    let x = variable(&mut domain, BinderLevel::from(0_u32));
    for (one, other, expected, what) in cases {
        let one = code_of(&core, &mut domain, one, &[x]);
        let other = code_of(&core, &mut domain, other, &[x]);
        assert_eq!(
            compare_rigidly(&core, &domain, one, other),
            expected,
            "{what}"
        );
        assert_eq!(
            compare_rigidly(&core, &domain, other, one),
            expected,
            "{what}, in either order"
        );
    }
}

#[test]
fn static_operators_compare_by_binder_and_spine()
{
    let mut core = CoreArena::new();
    let family = ConstantIndex::from(0_usize);
    let other_family = ConstantIndex::from(1_usize);
    // `⌜El (F #0)⌝` and `⌜El (G #0)⌝`, with the application written in the
    // quote, and `⌜El #0⌝`, whose code an environment supplies.
    let innermost = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let head = core.value_constant(family);
    let other_head = core.value_constant(other_family);
    let written = core.value_static_application(head, innermost);
    let other_written = core.value_static_application(other_head, innermost);
    let written_decode = core.value_type_element(written, Level::zero());
    let other_decode = core.value_type_element(other_written, Level::zero());
    let plain_decode = core.value_type_element(innermost, Level::zero());
    let written_quote = core.value_quote(written_decode);
    let other_quote = core.value_quote(other_decode);
    let plain_quote = core.value_quote(plain_decode);

    let mut domain = DomainArena::new();
    let x = variable(&mut domain, BinderLevel::from(0_u32));
    let y = variable(&mut domain, BinderLevel::from(1_u32));
    let held_neutral = domain
        .neutral_node(
            NeutralHead::Constant(family),
            Vec::from([Elimination::StaticApply(x)]),
            Unfolding::Rigid,
        )
        .expect("a statically applied neutral mints");
    let held = domain
        .value_neutral(held_neutral, TermFace::Reduced)
        .expect("a static spine stands as a value");

    let written_at_x = code_of(&core, &mut domain, written_quote, &[x]);
    let written_at_y = code_of(&core, &mut domain, written_quote, &[y]);
    let other_at_x = code_of(&core, &mut domain, other_quote, &[x]);
    let held_at_x = code_of(&core, &mut domain, plain_quote, &[held]);
    assert_eq!(
        CodeComparison::Equal,
        compare_rigidly(&core, &domain, written_at_x, held_at_x),
        "a written application and a held static spine compare by head and argument alike"
    );
    assert_eq!(
        CodeComparison::Apart,
        compare_rigidly(&core, &domain, written_at_x, written_at_y),
        "one rigid head at two rigid arguments is apart"
    );
    assert_eq!(
        CodeComparison::Apart,
        compare_rigidly(&core, &domain, written_at_x, other_at_x),
        "two rigid heads at one argument are apart"
    );

    // `λX. ⌜El X⌝` written twice, and `λX. ⌜Unit⌝`.
    let operators = [plain_quote, plain_quote, {
        let unit = core.value_type_unit();
        core.value_quote(unit)
    }]
    .map(|body| core.value_static_lambda(body));
    let [first, second, constant_operator] = operators.map(|lambda| {
        let chain = LoweredChain::new();
        let environment = DefinitionalEnvironment::new();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let (produced, _) = eval_value_within(
            &core,
            &mut domain,
            definitions,
            Fuel::from(64_u32),
            lambda,
            Environment::new(),
        )
        .expect("a static lambda evaluates");
        let Some(&DomainValue::StaticLambda {
            lambda: closure, ..
        }) = domain.value(produced)
        else {
            panic!("a static lambda evaluates to an operator");
        };
        closure
    });
    assert_eq!(
        CodeComparison::Equal,
        compare_rigidly(&core, &domain, first, second),
        "two operators alike under one shared binder are equal"
    );
    assert_eq!(
        CodeComparison::Undecided,
        compare_rigidly(&core, &domain, first, constant_operator),
        "two operators that differ are undecided: an operator is never declared apart"
    );
}

#[cfg(target_pointer_width = "64")]
#[test]
fn binder_numbers_stay_distinct_across_the_u32_boundary()
{
    let mut core = CoreArena::new();
    let unit = core.value_type_unit();
    let quote = core.value_quote(unit);
    let mut domain = DomainArena::new();
    let closure = domain.value_closure_node(crate::ValueBody::Source(quote), Environment::new());
    let place = super::Walk::opened(closure);
    let mut walk = super::Walk::new(&core, &domain, ConstantReading::Unread);
    walk.next =
        super::Binder(usize::try_from(u32::MAX).expect("a 64-bit index holds the 32-bit ceiling"));
    let (first, paired) = walk.crossed(place, place);
    let second = walk.crossed_alone(first);
    let at_zero = DeBruijnIndex::from(0_u32);
    assert_eq!(
        walk.local(first.chain, at_zero),
        walk.local(paired.chain, at_zero)
    );
    assert_ne!(
        walk.local(first.chain, at_zero),
        walk.local(second.chain, at_zero),
        "a fresh binder must not alias the preceding one at the 32-bit ceiling"
    );
    assert_eq!(
        walk.local(first.chain, at_zero),
        walk.local(second.chain, DeBruijnIndex::from(1_u32))
    );
}

#[test]
fn local_binders_shadow_only_their_own_chain()
{
    let mut core = CoreArena::new();
    let unit = core.value_type_unit();
    let quote = core.value_quote(unit);
    let mut domain = DomainArena::new();
    let closure = domain.value_closure_node(crate::ValueBody::Source(quote), Environment::new());
    let place = super::Walk::opened(closure);
    let mut walk = super::Walk::new(&core, &domain, ConstantReading::Unread);
    let old = walk.crossed_alone(place);
    let (left, right) = walk.crossed(old, place);
    let zero = DeBruijnIndex::from(0_u32);
    let one = DeBruijnIndex::from(1_u32);
    assert_eq!(walk.local(left.chain, zero), walk.local(right.chain, zero));
    assert_ne!(walk.local(left.chain, zero), walk.local(left.chain, one));
    assert_eq!(walk.local(old.chain, zero), walk.local(left.chain, one));
    assert_eq!(Err(zero), walk.local(right.chain, one));
    assert_eq!(
        Err(zero),
        walk.local(left.chain, DeBruijnIndex::from(2_u32))
    );
    assert_eq!(
        Err(one),
        walk.local(right.chain, DeBruijnIndex::from(2_u32))
    );
    assert_eq!(
        Err(DeBruijnIndex::from(u32::MAX - 2)),
        walk.local(left.chain, DeBruijnIndex::from(u32::MAX))
    );
    assert_eq!(
        Err(DeBruijnIndex::from(u32::MAX)),
        walk.local(place.chain, DeBruijnIndex::from(u32::MAX))
    );
    assert_eq!(Err(one), walk.local(super::Chain(usize::MAX), one));
}

#[test]
fn atom_resolution_refuses_missing_sources_and_preserves_zone()
{
    let mut core = CoreArena::new();
    let unit = core.value_type_unit();
    let quote = core.value_quote(unit);
    let int_zero = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let int_one = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let int_two = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(2_u32));
    let linear_zero = core.value_variable(Zone::Linear, DeBruijnIndex::from(0_u32));
    let core_floor = core.watermark();
    let absent_core = core.value_unit();
    core.truncate_to(core_floor);
    let mut domain = DomainArena::new();
    let int_head = domain
        .neutral_node(
            NeutralHead::Variable {
                zone: Zone::Intuitionistic,
                level: BinderLevel::from(9_u32),
            },
            Vec::new(),
            Unfolding::Rigid,
        )
        .expect("a variable is rigid");
    let int_value = domain
        .value_neutral(int_head, TermFace::Reduced)
        .expect("an empty spine is a value");
    let linear_head = domain
        .neutral_node(
            NeutralHead::Variable {
                zone: Zone::Linear,
                level: BinderLevel::from(4_u32),
            },
            Vec::new(),
            Unfolding::Rigid,
        )
        .expect("a variable is rigid");
    let linear_value = domain
        .value_neutral(linear_head, TermFace::Reduced)
        .expect("an empty spine is a value");
    let before_closures = domain.watermark();
    let mut environment = Environment::new();
    environment.extend(Zone::Intuitionistic, int_value);
    environment.extend(Zone::Linear, linear_value);
    let closure = domain.value_closure_node(crate::ValueBody::Source(quote), environment);
    let empty = domain.value_closure_node(crate::ValueBody::Source(quote), Environment::new());
    let before_absent = domain.watermark();
    let absent_held = domain.value_unit(TermFace::Reduced);
    domain.truncate_to(before_absent);
    let place = super::Walk::opened(closure);
    {
        let mut walk = super::Walk::new(&core, &domain, ConstantReading::Unread);
        let inside = walk.crossed_alone(place);
        let local = walk
            .local(inside.chain, DeBruijnIndex::from(0_u32))
            .expect("the local binder exists");
        assert_eq!(
            Ok(super::Atom::Local(local)),
            walk.atom(super::Node::Code(int_zero, inside))
        );
        assert_eq!(
            Ok(super::Atom::Variable(
                Zone::Intuitionistic,
                BinderLevel::from(9_u32)
            )),
            walk.atom(super::Node::Code(int_one, inside))
        );
        assert_eq!(
            Ok(super::Atom::Variable(
                Zone::Linear,
                BinderLevel::from(4_u32)
            )),
            walk.atom(super::Node::Code(linear_zero, inside))
        );
        assert_eq!(
            Err(crate::ConversionFault::MachineInvariant),
            walk.atom(super::Node::Code(int_two, inside))
        );
        assert_eq!(
            Err(crate::ConversionFault::MachineInvariant),
            walk.atom(super::Node::Code(int_zero, super::Walk::opened(empty)))
        );
        assert_eq!(
            Err(crate::ConversionFault::MachineInvariant),
            walk.atom(super::Node::Code(absent_core, place))
        );
        assert_eq!(
            Err(crate::ConversionFault::Domain(crate::DomainFault::Dangling)),
            walk.atom(super::Node::Held(absent_held))
        );
    }
    domain.truncate_to(before_closures);
    let walk = super::Walk::new(&core, &domain, ConstantReading::Unread);
    assert_eq!(
        Err(crate::ConversionFault::Domain(crate::DomainFault::Dangling)),
        walk.closure_atom(closure)
    );
    assert_eq!(
        Err(crate::ConversionFault::Domain(crate::DomainFault::Dangling)),
        walk.atom(super::Node::Code(int_zero, place))
    );
    assert_eq!(
        Err(crate::ConversionFault::Domain(crate::DomainFault::Dangling)),
        compare_codes(&core, &domain, ConstantReading::Unread, closure, closure)
    );
}

#[test]
fn stuck_prefixes_distinguish_heads_eliminations_and_refusals()
{
    let core = CoreArena::new();
    let mut domain = DomainArena::new();
    let floor = domain.watermark();
    let value = domain.value_unit(TermFace::Reduced);
    let neutral = domain
        .neutral_node(
            NeutralHead::Constant(ConstantIndex::from(0_usize)),
            Vec::from([Elimination::StaticApply(value), Elimination::Force]),
            Unfolding::Unforced(gandr_kernel_term::GlobalIndex::from(0_u32)),
        )
        .expect("a constant can unfold");
    let walk = super::Walk::new(&core, &domain, ConstantReading::Unread);
    assert_eq!(
        Ok(super::Atom::Constant(
            ConstantIndex::from(0_usize),
            super::Rigidity::Flexible
        )),
        walk.stuck(neutral, super::SpinePrefix(0))
    );
    assert_eq!(
        Ok(super::Atom::Applied(
            super::Node::Stuck(neutral, super::SpinePrefix(0)),
            super::Node::Held(value)
        )),
        walk.stuck(neutral, super::SpinePrefix(1))
    );
    assert_eq!(
        Ok(super::Atom::Other(super::Node::Stuck(
            neutral,
            super::SpinePrefix(2)
        ))),
        walk.stuck(neutral, super::SpinePrefix(2))
    );
    assert_eq!(
        Err(crate::ConversionFault::MachineInvariant),
        walk.stuck(neutral, super::SpinePrefix(3))
    );
    assert_eq!(
        Err(crate::ConversionFault::MachineInvariant),
        walk.stuck(neutral, super::SpinePrefix(usize::MAX))
    );
    domain.truncate_to(floor);
    let walk = super::Walk::new(&core, &domain, ConstantReading::Unread);
    assert_eq!(
        Err(crate::ConversionFault::Domain(crate::DomainFault::Dangling)),
        walk.stuck(neutral, super::SpinePrefix(0))
    );
}

#[test]
fn native_classifier_endpoints_compare_in_order_and_refuse_a_missing_target()
{
    let mut core = CoreArena::new();
    let unit = core.value_type_unit();
    let integer = core.value_type_base(BaseType::Integer);
    let source = core.value_quote(unit);
    let target = core.value_quote(integer);
    let path = core.value_type_path_universe(source, target);
    let path = core.value_quote(path);
    let reverse = core.value_type_path_universe(target, source);
    let reverse = core.value_quote(reverse);
    let along = core.value_type_path(unit, source, target);
    let along = core.value_quote(along);
    let against = core.value_type_path(unit, target, source);
    let against = core.value_quote(against);
    let mut foreign = core.clone();
    for _ in 0 .. 4_u8 {
        foreign.value_unit();
    }
    let missing = foreign.value_unit();
    let broken = core.value_type_path_universe(source, missing);
    let broken = core.value_quote(broken);
    assert!(core.value(missing).is_none());
    let mut domain = DomainArena::new();
    let left = code_of(&core, &mut domain, path, &[]);
    let right = code_of(&core, &mut domain, path, &[]);
    let reverse = code_of(&core, &mut domain, reverse, &[]);
    let [along_left, along_right, against] =
        [along, along, against].map(|code| code_of(&core, &mut domain, code, &[]));
    let broken = code_of(&core, &mut domain, broken, &[]);
    assert_eq!(
        Ok(CodeComparison::Equal),
        compare_codes(&core, &domain, ConstantReading::Unread, left, right)
    );
    assert_eq!(
        Ok(CodeComparison::Apart),
        compare_codes(&core, &domain, ConstantReading::Unread, left, reverse)
    );
    assert_eq!(
        Err(crate::ConversionFault::MachineInvariant),
        compare_codes(&core, &domain, ConstantReading::Unread, left, broken)
    );
    assert_eq!(
        Ok(CodeComparison::Equal),
        compare_codes(
            &core,
            &domain,
            ConstantReading::Unread,
            along_left,
            along_right
        ),
        "a path type compares its carrier and its endpoints"
    );
    assert_eq!(
        Ok(CodeComparison::Apart),
        compare_codes(&core, &domain, ConstantReading::Unread, along_left, against),
        "in order"
    );
    assert_eq!(
        Ok(CodeComparison::Apart),
        compare_codes(&core, &domain, ConstantReading::Unread, along_left, left),
        "and is apart from a universe path"
    );
}

#[test]
fn native_types_compare_identity_labels_and_value_arguments()
{
    use alloc::collections::BTreeMap;
    use alloc::string::String;

    use gandr_core_term::ConstructorTag;
    use gandr_core_term::FieldLabel;
    let mut core = CoreArena::new();
    let first = core.value_unit();
    let second = core.value_unit();
    let key = FieldLabel::from(String::from("key"));
    let other_key = FieldLabel::from(String::from("other"));
    let record = core.value_record(BTreeMap::from([(key.clone(), first)]));
    let same_record = core.value_record(BTreeMap::from([(key.clone(), second)]));
    let other_record = core.value_record(BTreeMap::from([(other_key.clone(), first)]));
    let name = ConstantIndex::from(0_usize);
    let other_name = ConstantIndex::from(1_usize);
    let indexed = core.value_type_data(name, Vec::from([record]));
    let repeated = core.value_type_data(name, Vec::from([same_record]));
    let renamed = core.value_type_data(other_name, Vec::from([record]));
    let relabeled = core.value_type_data(name, Vec::from([other_record]));
    let constructor_type = core.value_type_data(other_name, Vec::new());
    let constructor = core.value_constructor(
        constructor_type,
        ConstructorTag::from(0_usize),
        Vec::from([first]),
    );
    let other_constructor = core.value_constructor(
        constructor_type,
        ConstructorTag::from(1_usize),
        Vec::from([first]),
    );
    let tagged = core.value_type_data(name, Vec::from([constructor]));
    let retagged = core.value_type_data(name, Vec::from([other_constructor]));
    let unit_type = core.value_type_unit();
    let wide = core.value_type_record(BTreeMap::from([
        (key.clone(), unit_type),
        (other_key, unit_type),
    ]));
    let narrow = core.value_type_record(BTreeMap::from([(key.clone(), unit_type)]));
    let repeated_type = core.value_type_record(BTreeMap::from([(key.clone(), unit_type)]));
    let nested = core.value_type_record(BTreeMap::from([(key, narrow)]));
    let empty = core.value_type_record(BTreeMap::new());
    let mut domain = DomainArena::new();
    let [
        indexed,
        repeated,
        renamed,
        relabeled,
        tagged,
        retagged,
        wide,
        narrow,
        repeated_type,
        nested,
        empty,
    ] = [
        indexed,
        repeated,
        renamed,
        relabeled,
        tagged,
        retagged,
        wide,
        narrow,
        repeated_type,
        nested,
        empty,
    ]
    .map(|ty| {
        let quote = core.value_quote(ty);
        code_of(&core, &mut domain, quote, &[])
    });
    assert_eq!(
        compare_rigidly(&core, &domain, indexed, repeated),
        CodeComparison::Equal
    );
    assert_eq!(
        compare_rigidly(&core, &domain, indexed, renamed),
        CodeComparison::Apart
    );
    assert_eq!(
        compare_rigidly(&core, &domain, indexed, relabeled),
        CodeComparison::Apart
    );
    assert_eq!(
        compare_rigidly(&core, &domain, tagged, retagged),
        CodeComparison::Apart
    );
    assert_eq!(
        compare_rigidly(&core, &domain, narrow, repeated_type),
        CodeComparison::Equal
    );
    assert_eq!(
        compare_rigidly(&core, &domain, wide, narrow),
        CodeComparison::Apart,
        "width assignment is not definitional equality"
    );
    assert_eq!(
        compare_rigidly(&core, &domain, narrow, nested),
        CodeComparison::Apart
    );
    assert_eq!(
        compare_rigidly(&core, &domain, narrow, empty),
        CodeComparison::Apart
    );
}

#[test]
fn a_type_former_written_twice_is_one_code()
{
    use alloc::sync::Arc;

    use gandr_core_term::effect::EffectName;
    use gandr_core_term::effect::EffectOp;
    use gandr_core_term::effect::EffectRow;
    use gandr_core_term::effect::EffectSig;
    use gandr_core_term::effect::OperationName;
    use gandr_core_term::effect::capability::CapabilityGrade;
    use gandr_core_term::effect::capability::Region;
    use gandr_core_term::session::PayloadCount;
    use gandr_core_term::session::PayloadSlot;
    use gandr_core_term::session::Protocol;
    use gandr_core_term::session::ProtocolState;
    use gandr_core_term::session::ProtocolSyntax;
    use gandr_core_term::session::SessionType;
    use gandr_kernel_term::Stage;
    use gandr_kernel_term::StageId;

    let mut core = CoreArena::new();
    let unit = core.value_type_unit();
    let protocol = Arc::new(
        Protocol::new(
            alloc::vec![
                ProtocolSyntax::Send {
                    payload: PayloadSlot::from(0_usize),
                    next: ProtocolState::from(1_usize),
                },
                ProtocolSyntax::End,
            ],
            ProtocolState::from(0_usize),
            PayloadCount::from(1_usize),
        )
        .expect("a send then an end is a protocol"),
    );
    let session =
        SessionType::new(protocol, Arc::from([unit])).expect("one payload fills one slot");
    let ended = session
        .at(ProtocolState::from(1_usize))
        .expect("the end is a state");
    let stage = Stage::At(StageId::from(0_usize));
    let level = Level::zero().succ().expect("level one exists");
    let written = |core: &mut CoreArena| {
        let signature = EffectSig::new(EffectName::from("Probe"), alloc::vec![EffectOp {
            name: OperationName::from("ask"),
            payload: unit,
            reply: unit,
        }])
        .expect("one operation is a signature");
        let unit = core.value_type_unit();
        let unit_quote = core.value_quote(unit);
        let lifted_code = core.value_lift(level.clone(), unit_quote);
        [
            core.value_type_capability(
                EffectRow::singleton(signature),
                CapabilityGrade::Durable,
                Region::Held,
            ),
            core.value_type_lift(unit, level.clone()),
            core.value_type_session(session.clone()),
            core.value_type_staged(unit, stage),
            core.value_type_element(lifted_code, Level::zero()),
        ]
        .map(|ty| core.value_quote(ty))
    };
    let first = written(&mut core);
    let second = written(&mut core);
    let ended = core.value_type_session(ended);
    let ended = core.value_quote(ended);
    let mut domain = DomainArena::new();
    let ended = code_of(&core, &mut domain, ended, &[]);
    for (former, (left, right)) in [
        "a capability",
        "a lift",
        "a session",
        "a staged type",
        "a lifted code",
    ]
    .into_iter()
    .zip(first.into_iter().zip(second))
    {
        let left = code_of(&core, &mut domain, left, &[]);
        let right = code_of(&core, &mut domain, right, &[]);
        assert_eq!(
            CodeComparison::Equal,
            compare_rigidly(&core, &domain, left, right),
            "{former} compares by its parts, not its node"
        );
        if former == "a session" {
            assert_eq!(
                CodeComparison::Apart,
                compare_rigidly(&core, &domain, left, ended),
                "and a session is apart from its own protocol at another state"
            );
        }
    }
}

#[test]
fn first_order_arguments_compare_by_shape_and_arity()
{
    use alloc::collections::BTreeMap;
    use alloc::string::String;

    use gandr_core_term::ConstructorTag;
    use gandr_core_term::FieldLabel;
    use gandr_core_term::Summand;

    let mut core = CoreArena::new();
    let name = ConstantIndex::from(0_usize);
    let arguments = |core: &mut CoreArena| {
        let unit = core.value_unit();
        let nil = core.value_list_nil();
        let constructor_type = core.value_type_data(ConstantIndex::from(1_usize), Vec::new());
        [
            nil,
            core.value_list_cons(unit, nil),
            core.value_tuple(&[unit, unit]),
            core.value_injection(Summand::from(1_usize), unit),
            core.value_constructor(
                constructor_type,
                ConstructorTag::from(0_usize),
                Vec::from([unit]),
            ),
        ]
        .map(|argument| {
            let indexed = core.value_type_data(name, Vec::from([argument]));
            core.value_quote(indexed)
        })
    };
    let first = arguments(&mut core);
    let second = arguments(&mut core);
    let unit = core.value_unit();
    let single = core.value_tuple(&[unit]);
    let single = core.value_type_data(name, Vec::from([single]));
    let single = core.value_quote(single);
    let variable = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let held = core.value_type_data(name, Vec::from([variable]));
    let held = core.value_quote(held);
    let unit_term = core.value_unit();
    let labelled = core.value_record(BTreeMap::from([(
        FieldLabel::from(String::from("x")),
        unit_term,
    )]));

    let mut domain = DomainArena::new();
    let pair = code_of(&core, &mut domain, first[2], &[]);
    let single = code_of(&core, &mut domain, single, &[]);
    assert_eq!(
        CodeComparison::Apart,
        compare_rigidly(&core, &domain, pair, single),
        "a pair is apart from a one-tuple"
    );
    for (argument, (left, right)) in ["nil", "a cons", "a pair", "an injection", "a constructor"]
        .into_iter()
        .zip(first.into_iter().zip(second))
    {
        let left = code_of(&core, &mut domain, left, &[]);
        let right = code_of(&core, &mut domain, right, &[]);
        assert_eq!(
            CodeComparison::Equal,
            compare_rigidly(&core, &domain, left, right),
            "{argument} written twice is one argument"
        );
    }
    let records = [0_u32, 1_u32].map(|_| {
        let unit = domain.value_unit(TermFace::Reduced);
        let fields = domain.hold_fields([unit]);
        let record = domain
            .value_record(labelled, fields, TermFace::Reduced)
            .expect("the fields are live");
        code_of(&core, &mut domain, held, &[record])
    });
    assert_eq!(
        CodeComparison::Equal,
        compare_rigidly(&core, &domain, records[0], records[1]),
        "a held record is one argument with its twin"
    );
}
