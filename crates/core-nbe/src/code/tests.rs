use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::CoreArena;
use gandr_core_term::DefinitionalEnvironment;
use gandr_core_term::ValueId;
use gandr_core_term::Zone;
use gandr_kernel_conversion_trace::ConversionSide;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;

use super::Against;
use super::Alike;
use super::CodeComparison;
use super::CodeReading;
use super::ConstantReading;
use super::SetAside;
use super::WrittenCall;
use super::compare_codes;
use super::compare_codes_over;
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
            core.comp_type_with(&[input, returned_integer])
        }
        else {
            core.comp_type_with(&[returned_integer, input])
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
fn motives_calling_one_variable_family_are_alike_3802()
{
    // #3802: `z. Q(z)`, `Q` a variable family, lowered at each of two
    // transports. Each body decodes the pure call `Q(z)`, and the two calls
    // are distinct nodes. The machine quotes both motives under one fresh
    // endpoint and compares the quotes; the search-free step crosses the
    // motives' binders alike. Both read one family, also over captures of
    // different depths. A call of another family stays undecided, never
    // apart, as an unread call did.
    let mut core = CoreArena::new();
    let family = |core: &mut CoreArena, head: u32| {
        let function = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(head));
        let endpoint = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let forced = core.computation_force(function);
        let call = core.computation_application(forced, endpoint);
        let code = core.value_returned(call);
        core.value_type_element(code, Level::zero())
    };
    let (near, again, far) = (
        family(&mut core, 1),
        family(&mut core, 1),
        family(&mut core, 2),
    );

    let mut domain = DomainArena::new();
    let q = variable(&mut domain, BinderLevel::from(0_u32));
    let r = variable(&mut domain, BinderLevel::from(1_u32));
    let endpoint = variable(&mut domain, BinderLevel::from(2_u32));
    let motive = |domain: &mut DomainArena, body, bound: &[DomainValueId]| {
        let mut environment = Environment::new();
        for &value in bound {
            environment.extend(Zone::Intuitionistic, value);
        }
        domain.value_closure_node(ValueBody::ValueType(body), environment)
    };

    let quoted = motive(&mut domain, near, &[q, endpoint]);
    let quoted_again = motive(&mut domain, again, &[q, endpoint]);
    let quoted_other = motive(&mut domain, near, &[r, endpoint]);
    assert_eq!(
        CodeComparison::Equal,
        compare_rigidly(&core, &domain, quoted, quoted_again),
        "two quotes of one call under one endpoint are one code"
    );
    assert_eq!(
        CodeComparison::Undecided,
        compare_rigidly(&core, &domain, quoted, quoted_other),
        "a call of another family stays undecided, never apart"
    );

    let over_q = motive(&mut domain, near, &[q]);
    let over_q_again = motive(&mut domain, again, &[q]);
    let over_q_far = motive(&mut domain, far, &[q, r]);
    let over_r = motive(&mut domain, near, &[r]);
    assert_eq!(
        Alike::Same,
        motives_alike(&core, &domain, over_q, over_q_again).expect("both motives resolve"),
        "two lowerings of one call are one family"
    );
    assert_eq!(
        Alike::Same,
        motives_alike(&core, &domain, over_q, over_q_far).expect("both motives resolve"),
        "and so are two captures of different depths"
    );
    assert_eq!(
        Alike::Different,
        motives_alike(&core, &domain, over_q, over_r).expect("both motives resolve"),
        "but a call of another family is not"
    );
}

#[test]
fn motives_calling_thunks_written_apart_are_alike_3920()
{
    // #3920: `z. El(⟨force f z⟩)`, `f` bound to a thunk of `λq. return g`
    // closed over `g`. Each side writes the lambda in its own place, so the
    // two thunks close two body nodes over one capture. The walk reads them
    // by their bodies as syntax and their captures pair by pair. A thunk over
    // another capture, or of another body, stays undecided, never apart.
    let mut core = CoreArena::new();
    let family = |core: &mut CoreArena| {
        let function = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
        let endpoint = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let forced = core.computation_force(function);
        let call = core.computation_application(forced, endpoint);
        let code = core.value_returned(call);
        core.value_type_element(code, Level::zero())
    };
    let lambda = |core: &mut CoreArena, index: u32| {
        let read = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index));
        let returned = core.computation_return(read);
        core.computation_lambda(returned)
    };
    let (near, again) = (family(&mut core), family(&mut core));
    let (body, rewritten, other_body) = (
        lambda(&mut core, 1),
        lambda(&mut core, 1),
        lambda(&mut core, 0),
    );

    let mut domain = DomainArena::new();
    let g = variable(&mut domain, BinderLevel::from(0_u32));
    let h = variable(&mut domain, BinderLevel::from(1_u32));
    let endpoint = variable(&mut domain, BinderLevel::from(2_u32));
    let thunk = |domain: &mut DomainArena, body, capture| {
        let mut environment = Environment::new();
        environment.extend(Zone::Intuitionistic, capture);
        let closure = domain.comp_closure_node(body, environment);
        domain.value_thunk(closure, TermFace::Reduced)
    };
    let f = thunk(&mut domain, body, g);
    let f_rewritten = thunk(&mut domain, rewritten, g);
    let f_over_h = thunk(&mut domain, rewritten, h);
    let f_other = thunk(&mut domain, other_body, g);
    let motive = |domain: &mut DomainArena, body, bound: &[DomainValueId]| {
        let mut environment = Environment::new();
        for &value in bound {
            environment.extend(Zone::Intuitionistic, value);
        }
        domain.value_closure_node(ValueBody::ValueType(body), environment)
    };

    let quoted = motive(&mut domain, near, &[f, endpoint]);
    let quoted_rewritten = motive(&mut domain, again, &[f_rewritten, endpoint]);
    let quoted_over_h = motive(&mut domain, again, &[f_over_h, endpoint]);
    let quoted_other = motive(&mut domain, again, &[f_other, endpoint]);
    assert_eq!(
        CodeComparison::Equal,
        compare_rigidly(&core, &domain, quoted, quoted_rewritten),
        "a call of one lambda written twice over one capture is one code"
    );
    assert_eq!(
        CodeComparison::Undecided,
        compare_rigidly(&core, &domain, quoted, quoted_over_h),
        "the lambda over another capture stays undecided, never apart"
    );
    assert_eq!(
        CodeComparison::Undecided,
        compare_rigidly(&core, &domain, quoted, quoted_other),
        "and so does another lambda over the same capture"
    );

    let over_f = motive(&mut domain, near, &[f]);
    let over_f_rewritten = motive(&mut domain, again, &[f_rewritten]);
    let over_f_other = motive(&mut domain, again, &[f_other]);
    assert_eq!(
        Alike::Same,
        motives_alike(&core, &domain, over_f, over_f_rewritten).expect("both motives resolve"),
        "two motives calling the lambda written twice are one family"
    );
    assert_eq!(
        Alike::Different,
        motives_alike(&core, &domain, over_f, over_f_other).expect("both motives resolve"),
        "but a motive calling another lambda is not"
    );
}

#[test]
fn motives_applying_a_stated_lambda_agree_with_its_reduct_4073()
{
    // #4073: `z. El(⟨(λq. F q : U)(z)⟩)`, a stated lambda applied, as the
    // lowering instantiates a type written `F(x)` at the lambda. The type
    // written with the reduct reads `z. El(⟨F z⟩)`. The walk steps into the
    // lambda's body, its binder bound to `z`, so the two motives are one
    // family. So does the checker's elaboration: a nested lambda whose body
    // binds its stated binder, `y ← (return q : F A); F q`. A stated identity
    // applied to `z` reads as `z` itself. The redex is not a call of another
    // family. A lambda whose body transports, `λq. tr(El(#1), q, F)`, applied
    // to `z` is the transport written apart, and not one of another value.
    let mut core = CoreArena::new();
    let decoded = |core: &mut CoreArena, call| {
        let code = core.value_returned(call);
        core.value_type_element(code, Level::zero())
    };
    let call = |core: &mut CoreArena, function: u32, argument: u32| {
        let head = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(function));
        let read = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(argument));
        let forced = core.computation_force(head);
        core.computation_application(forced, read)
    };
    let stated = |core: &mut CoreArena, body, suspend: fn(&mut CoreArena, _) -> ValueId| {
        let lambda = core.computation_lambda(body);
        let thunk = suspend(core, lambda);
        let unit = core.value_type_unit();
        let ascribed = core.value_ascribe(thunk, unit);
        let forced = core.computation_force(ascribed);
        let endpoint = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        core.computation_application(forced, endpoint)
    };
    // `F z`, `F` at index 1 past the motive's binder.
    let reduct = call(&mut core, 1, 0);
    let reduct = decoded(&mut core, reduct);
    // `(λq. F q)(z)`: under the lambda's binder `F` stands at index 2.
    let body = call(&mut core, 2, 0);
    let redex = stated(&mut core, body, CoreArena::value_thunk);
    let redex = decoded(&mut core, redex);
    // `(λq. y ← (return q : F U); F q)(z)`, the lambda nested: past the bind
    // `q` stands at index 1 and `F` at index 3.
    let read = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let returned = core.computation_return(read);
    let unit = core.value_type_unit();
    let returner = core.comp_type_returner(unit);
    let checked = core.computation_ascribe(returned, returner);
    let applied = call(&mut core, 3, 1);
    let body = core.computation_bind(checked, applied);
    let elaborated = stated(&mut core, body, CoreArena::value_nested);
    let elaborated = decoded(&mut core, elaborated);
    // `(λq. return q)(z)`, against `El z`.
    let read = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let returned = core.computation_return(read);
    let identity = stated(&mut core, returned, CoreArena::value_thunk);
    let identity = decoded(&mut core, identity);
    let endpoint = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let bare = core.value_type_element(endpoint, Level::zero());
    // `(λq. tr(El(#1), q, F))(z)` against `tr(El(#1), z, F)`: past the
    // transport's binder its motive reads the endpoint at index 1, and `F`
    // stands at index 2 in the lambda, at index 1 outside it.
    let transported = |core: &mut CoreArena, value: u32| {
        let endpoint = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
        let along = core.value_type_element(endpoint, Level::zero());
        let path = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let value = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(value));
        core.computation_path_transport(along, path, value)
    };
    let composite = transported(&mut core, 1);
    let composite = decoded(&mut core, composite);
    let body = transported(&mut core, 2);
    let composed = stated(&mut core, body, CoreArena::value_thunk);
    let composed = decoded(&mut core, composed);

    let mut domain = DomainArena::new();
    let f = variable(&mut domain, BinderLevel::from(0_u32));
    let g = variable(&mut domain, BinderLevel::from(1_u32));
    let motive = |domain: &mut DomainArena, body, bound: DomainValueId| {
        let mut environment = Environment::new();
        environment.extend(Zone::Intuitionistic, bound);
        domain.value_closure_node(ValueBody::ValueType(body), environment)
    };
    let over_redex = motive(&mut domain, redex, f);
    let over_elaborated = motive(&mut domain, elaborated, f);
    let over_reduct = motive(&mut domain, reduct, f);
    let over_other = motive(&mut domain, reduct, g);
    let over_identity = motive(&mut domain, identity, f);
    let over_bare = motive(&mut domain, bare, f);
    let over_composed = motive(&mut domain, composed, f);
    let over_composite = motive(&mut domain, composite, f);
    let over_composite_other = motive(&mut domain, composite, g);
    assert_eq!(
        Alike::Same,
        motives_alike(&core, &domain, over_redex, over_reduct).expect("both motives resolve"),
        "a stated lambda applied is the call its body makes"
    );
    assert_eq!(
        Alike::Same,
        motives_alike(&core, &domain, over_reduct, over_redex).expect("both motives resolve"),
        "on either side"
    );
    assert_eq!(
        Alike::Same,
        motives_alike(&core, &domain, over_elaborated, over_reduct).expect("both motives resolve"),
        "and so is the lambda as the checker elaborates it"
    );
    assert_eq!(
        Alike::Different,
        motives_alike(&core, &domain, over_redex, over_other).expect("both motives resolve"),
        "but not a call of another family"
    );
    assert_eq!(
        Alike::Same,
        motives_alike(&core, &domain, over_identity, over_bare).expect("both motives resolve"),
        "a stated identity applied is its argument"
    );
    assert_eq!(
        Alike::Same,
        motives_alike(&core, &domain, over_composed, over_composite).expect("both motives resolve"),
        "a lambda whose body transports is the transport written apart"
    );
    assert_eq!(
        Alike::Different,
        motives_alike(&core, &domain, over_composed, over_composite_other)
            .expect("both motives resolve"),
        "but not one of another value"
    );
}

#[test]
fn motives_over_composites_written_apart_are_alike_3968()
{
    // #3968: `z. Path(El(c), s, ⟨tr(y. Path(El(c), s, y), g, z)⟩)`, the
    // composite `z then g` written as the path transport `then` lowers to.
    // Each side writes the transport in its own place, so the two composites
    // are two nodes. The walk reads them by their paths, their values and
    // their motives under one binder crossed alike. A composite along `s`
    // instead of `g` stays undecided, never apart.
    let mut core = CoreArena::new();
    let family = |core: &mut CoreArena, along: u32| {
        let read = |core: &mut CoreArena, index: u32| {
            core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index))
        };
        let (inner_carrier, inner_start, moving) = (read(core, 4), read(core, 3), read(core, 0));
        let inner_carrier = core.value_type_element(inner_carrier, Level::zero());
        let inner = core.value_type_path(inner_carrier, inner_start, moving);
        let (path, endpoint) = (read(core, along), read(core, 0));
        let composite = core.computation_path_transport(inner, path, endpoint);
        let returned = core.value_returned(composite);
        let (carrier, start) = (read(core, 3), read(core, 2));
        let carrier = core.value_type_element(carrier, Level::zero());
        core.value_type_path(carrier, start, returned)
    };
    let (near, again, astray) = (
        family(&mut core, 1),
        family(&mut core, 1),
        family(&mut core, 2),
    );

    let mut domain = DomainArena::new();
    let c = variable(&mut domain, BinderLevel::from(0_u32));
    let s = variable(&mut domain, BinderLevel::from(1_u32));
    let g = variable(&mut domain, BinderLevel::from(2_u32));
    let endpoint = variable(&mut domain, BinderLevel::from(3_u32));
    let motive = |domain: &mut DomainArena, body, bound: &[DomainValueId]| {
        let mut environment = Environment::new();
        for &value in bound {
            environment.extend(Zone::Intuitionistic, value);
        }
        domain.value_closure_node(ValueBody::ValueType(body), environment)
    };

    let over = motive(&mut domain, near, &[c, s, g]);
    let over_again = motive(&mut domain, again, &[c, s, g]);
    let over_astray = motive(&mut domain, astray, &[c, s, g]);
    assert_eq!(
        Alike::Same,
        motives_alike(&core, &domain, over, over_again).expect("both motives resolve"),
        "two motives over one composite written apart are one family"
    );
    assert_eq!(
        Alike::Different,
        motives_alike(&core, &domain, over, over_astray).expect("both motives resolve"),
        "but a motive over a composite along another path is not"
    );

    let quoted = motive(&mut domain, near, &[c, s, g, endpoint]);
    let quoted_again = motive(&mut domain, again, &[c, s, g, endpoint]);
    let quoted_astray = motive(&mut domain, astray, &[c, s, g, endpoint]);
    assert_eq!(
        CodeComparison::Equal,
        compare_rigidly(&core, &domain, quoted, quoted_again),
        "two quotes of one composite under one endpoint are one code"
    );
    assert_eq!(
        CodeComparison::Undecided,
        compare_rigidly(&core, &domain, quoted, quoted_astray),
        "a composite along another path stays undecided, never apart"
    );
}

#[test]
fn motives_reading_a_returned_composite_agree_with_its_fold_4057()
{
    // #4057: `p then q` lowers to the binary composite, which a value
    // position reads as returned, `z. El(⟨return compose(F, z; tr(El(#1), z,
    // F))⟩)`. The bridge erases it to its fold, so the walk reads it as the
    // fold written apart, `z. El(⟨tr(El(#1), z, F)⟩)`. A stated lambda whose
    // body returns the composite, applied to `z`, is the composite written
    // apart, as `(λq. (q then g) then h)(fm)` meets `(fm then g) then h`. A
    // composite of another value is not the fold.
    use alloc::boxed::Box;

    use gandr_core_term::ComputationId;
    use gandr_core_term::compose::Composite;
    let mut core = CoreArena::new();
    let decoded = |core: &mut CoreArena, call| {
        let code = core.value_returned(call);
        core.value_type_element(code, Level::zero())
    };
    // `tr(El(#1), #0, #value)`, past the transport's binder its motive reading
    // the path at index 1.
    let transported = |core: &mut CoreArena, value: u32| {
        let endpoint = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
        let along = core.value_type_element(endpoint, Level::zero());
        let path = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let value = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(value));
        core.computation_path_transport(along, path, value)
    };
    // The composite of `#value` and `#0` returned, its fold that transport.
    let returned = |core: &mut CoreArena, value: u32| -> ComputationId {
        let fold = transported(core, value);
        let first = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(value));
        let second = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let composite = core.value_compose(Composite::binary(), Box::from([first, second]), fold);
        core.computation_return(composite)
    };
    let fold = transported(&mut core, 1);
    let fold = decoded(&mut core, fold);
    let written = returned(&mut core, 1);
    let written = decoded(&mut core, written);
    // `(λq. return compose(F, q; tr(El(#1), q, F)))(z)`: `F` stands at index 2
    // in the lambda.
    let body = returned(&mut core, 2);
    let lambda = core.computation_lambda(body);
    let thunk = core.value_thunk(lambda);
    let unit = core.value_type_unit();
    let ascribed = core.value_ascribe(thunk, unit);
    let forced = core.computation_force(ascribed);
    let endpoint = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let applied = core.computation_application(forced, endpoint);
    let applied = decoded(&mut core, applied);

    let mut domain = DomainArena::new();
    let f = variable(&mut domain, BinderLevel::from(0_u32));
    let g = variable(&mut domain, BinderLevel::from(1_u32));
    let motive = |domain: &mut DomainArena, body, bound: DomainValueId| {
        let mut environment = Environment::new();
        environment.extend(Zone::Intuitionistic, bound);
        domain.value_closure_node(ValueBody::ValueType(body), environment)
    };
    let over_written = motive(&mut domain, written, f);
    let over_fold = motive(&mut domain, fold, f);
    let over_applied = motive(&mut domain, applied, f);
    let over_other = motive(&mut domain, fold, g);
    assert_eq!(
        Alike::Same,
        motives_alike(&core, &domain, over_written, over_fold).expect("both motives resolve"),
        "a returned composite is its fold"
    );
    assert_eq!(
        Alike::Same,
        motives_alike(&core, &domain, over_applied, over_written).expect("both motives resolve"),
        "a stated lambda returning the composite, applied, is the composite written apart"
    );
    assert_eq!(
        Alike::Different,
        motives_alike(&core, &domain, over_written, over_other).expect("both motives resolve"),
        "but not the fold of another value"
    );
}

#[test]
fn codes_over_held_values_the_walk_cannot_match_set_them_aside_4005()
{
    // #4005: `El(#0)` over a path an action returned, `⟨transport along p⟩`,
    // written once through each of two motives of one family written apart.
    // The two endpoints are two neutrals of one shape, which the walk compares
    // by identity, so the two codes are undecided. The walk that sets aside
    // finds them α-equal over the pair of endpoints, which the machine reads
    // through. So too for two thunks of `λq. return g` and `λq. return g to
    // t. return t`, whose bodies differ as written. One endpoint held twice
    // is one code, and a code over another former sets nothing aside.
    let mut core = CoreArena::new();
    let element = |core: &mut CoreArena, index: u32| {
        let read = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index));
        core.value_type_element(read, Level::zero())
    };
    let (inside, one_out, two_out) = (
        element(&mut core, 0),
        element(&mut core, 1),
        element(&mut core, 2),
    );
    let unit = core.value_type_unit();
    let called = {
        let function = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
        let endpoint = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let forced = core.computation_force(function);
        let call = core.computation_application(forced, endpoint);
        let code = core.value_returned(call);
        core.value_type_element(code, Level::zero())
    };
    let (returning, rebinding) = {
        let g = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
        let returned = core.computation_return(g);
        let bound = core.computation_return(g);
        let t = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let passed = core.computation_return(t);
        let rebound = core.computation_bind(bound, passed);
        (
            core.computation_lambda(returned),
            core.computation_lambda(rebound),
        )
    };

    let mut domain = DomainArena::new();
    let path = BinderLevel::from(0_u32);
    let g = variable(&mut domain, BinderLevel::from(1_u32));
    let carried = variable(&mut domain, BinderLevel::from(2_u32));
    let endpoint = variable(&mut domain, BinderLevel::from(3_u32));
    let (x, y) = (
        variable(&mut domain, BinderLevel::from(4_u32)),
        variable(&mut domain, BinderLevel::from(5_u32)),
    );
    let closure = |domain: &mut DomainArena, body, captures: &[DomainValueId]| {
        let mut environment = Environment::new();
        for &capture in captures {
            environment.extend(Zone::Intuitionistic, capture);
        }
        domain.value_closure_node(ValueBody::ValueType(body), environment)
    };
    // `⟨transport along p⟩` under a motive, minted afresh for each motive.
    let returned_path = |domain: &mut DomainArena, motive| {
        let transported = domain
            .neutral_node(
                NeutralHead::Variable {
                    zone: Zone::Intuitionistic,
                    level: path,
                },
                Vec::from([Elimination::PathTransport {
                    motive,
                    value: carried,
                }]),
                Unfolding::Rigid,
            )
            .expect("a transport along a variable mints");
        let call = domain.comp_neutral(transported, crate::domain::CompTermFace::Reduced);
        domain
            .neutral_node(NeutralHead::Returned(call), Vec::new(), Unfolding::Rigid)
            .expect("a returned call mints")
    };
    let held = |domain: &mut DomainArena, neutral| {
        domain
            .value_neutral(neutral, TermFace::Reduced)
            .expect("the returned call resolves")
    };
    let written = closure(&mut domain, one_out, &[x]);
    let apart = closure(&mut domain, two_out, &[x, y]);
    let through_written = returned_path(&mut domain, written);
    let through_apart = returned_path(&mut domain, apart);
    let (once, again, other) = (
        held(&mut domain, through_written),
        held(&mut domain, through_written),
        held(&mut domain, through_apart),
    );
    let over_once = closure(&mut domain, inside, &[once]);
    let over_again = closure(&mut domain, inside, &[again]);
    let over_other = closure(&mut domain, inside, &[other]);
    assert_eq!(
        Ok(CodeComparison::Undecided),
        compare_codes(
            &core,
            &domain,
            ConstantReading::Unread,
            over_once,
            over_other
        ),
        "two endpoints of one shape written apart are undecided by identity"
    );
    assert_eq!(
        Ok(CodeReading::Over(alloc::vec![SetAside::Held(once, other)])),
        compare_codes_over(
            &core,
            &domain,
            ConstantReading::Unread,
            over_once,
            over_other
        ),
        "setting the pair of endpoints aside, the two codes are α-equal over it"
    );
    assert_eq!(
        Ok(CodeReading::Compared(CodeComparison::Equal)),
        compare_codes_over(
            &core,
            &domain,
            ConstantReading::Unread,
            over_once,
            over_again
        ),
        "one endpoint held twice is one code, nothing set aside"
    );

    let thunk = |domain: &mut DomainArena, body| {
        let mut environment = Environment::new();
        environment.extend(Zone::Intuitionistic, g);
        let body = domain.comp_closure_node(body, environment);
        domain.value_thunk(body, TermFace::Reduced)
    };
    let f = thunk(&mut domain, returning);
    let f_rebinding = thunk(&mut domain, rebinding);
    let calling = closure(&mut domain, called, &[f, endpoint]);
    let calling_rebinding = closure(&mut domain, called, &[f_rebinding, endpoint]);
    let over_unit = closure(&mut domain, unit, &[f, endpoint]);
    assert_eq!(
        Ok(CodeComparison::Undecided),
        compare_codes(
            &core,
            &domain,
            ConstantReading::Unread,
            calling,
            calling_rebinding
        ),
        "two thunks whose bodies differ as written are undecided"
    );
    assert_eq!(
        Ok(CodeReading::Over(alloc::vec![SetAside::Held(
            f,
            f_rebinding
        )])),
        compare_codes_over(
            &core,
            &domain,
            ConstantReading::Unread,
            calling,
            calling_rebinding
        ),
        "setting the pair of thunks aside, the two codes are α-equal over it"
    );
    assert_eq!(
        Ok(CodeReading::Compared(CodeComparison::Undecided)),
        compare_codes_over(&core, &domain, ConstantReading::Unread, calling, over_unit),
        "a code over another former sets nothing aside and stays undecided"
    );
}

#[test]
fn a_written_call_against_a_held_endpoint_is_set_aside_4038()
{
    // #4038: `El(⟨tr(Unit, #0, #1)⟩)` written in one quote over `[v, p]`, and
    // `El(#0)` in the other over the endpoint that transport returned, held as
    // a definition's parameter holds it. The walk cannot match a written call
    // with a held one, so the codes are undecided. The walk that sets aside
    // hands the machine the call and the held computation, on either side.
    let mut core = CoreArena::new();
    let unit = core.value_type_unit();
    let index = |core: &mut CoreArena, at: u32| {
        core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(at))
    };
    let (path, carried) = (index(&mut core, 0), index(&mut core, 1));
    let call = core.computation_path_transport(unit, path, carried);
    let endpoint = core.value_returned(call);
    let written = core.value_type_element(endpoint, Level::zero());
    let read = index(&mut core, 0);
    let inside = core.value_type_element(read, Level::zero());

    let mut domain = DomainArena::new();
    let p = variable(&mut domain, BinderLevel::from(0_u32));
    let v = variable(&mut domain, BinderLevel::from(1_u32));
    let closure = |domain: &mut DomainArena, body, captures: &[DomainValueId]| {
        let mut environment = Environment::new();
        for &capture in captures {
            environment.extend(Zone::Intuitionistic, capture);
        }
        domain.value_closure_node(ValueBody::ValueType(body), environment)
    };
    let motive = closure(&mut domain, unit, &[]);
    let transported = domain
        .neutral_node(
            NeutralHead::Variable {
                zone: Zone::Intuitionistic,
                level: BinderLevel::from(0_u32),
            },
            Vec::from([Elimination::PathTransport { motive, value: v }]),
            Unfolding::Rigid,
        )
        .expect("a transport along a variable mints");
    let held = domain.comp_neutral(transported, crate::domain::CompTermFace::Reduced);
    let returned = domain
        .neutral_node(NeutralHead::Returned(held), Vec::new(), Unfolding::Rigid)
        .expect("a returned call mints");
    let endpoint_held = domain
        .value_neutral(returned, TermFace::Reduced)
        .expect("the returned call resolves");
    let writing = closure(&mut domain, written, &[v, p]);
    let holding = closure(&mut domain, inside, &[endpoint_held]);
    let set_aside = |side| {
        Ok(CodeReading::Over(alloc::vec![SetAside::Written(
            WrittenCall {
                side,
                call,
                closure: writing,
                against: Against::Returned(held),
            }
        )]))
    };

    assert_eq!(
        Ok(CodeComparison::Undecided),
        compare_codes(&core, &domain, ConstantReading::Unread, writing, holding),
        "a written call against a held endpoint is undecided by node"
    );
    assert_eq!(
        set_aside(ConversionSide::Left),
        compare_codes_over(&core, &domain, ConstantReading::Unread, writing, holding),
        "setting the written call aside, the two codes are α-equal over it"
    );
    assert_eq!(
        set_aside(ConversionSide::Right),
        compare_codes_over(&core, &domain, ConstantReading::Unread, holding, writing),
        "and so on the other side"
    );
}

#[test]
fn a_written_call_against_a_variable_or_a_call_is_set_aside_4179()
{
    // #4179: `El(⟨tr(Unit, #0, #1)⟩)` written over `[v, p]` against `El(#0)`
    // over `[p]`, a call against the variable it may reduce to, and against
    // `El(⟨tr(Unit, #1, #0)⟩)` over `[v, p]`, a call against a call whose
    // parts part. The walk that sets aside hands the machine each pair whole,
    // on either side. Two calls whose parts set aside held endpoints keep
    // those pairs, and a call against a constant sets nothing aside.
    let mut core = CoreArena::new();
    let unit = core.value_type_unit();
    let index = |core: &mut CoreArena, at: u32| {
        core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(at))
    };
    let (path, carried) = (index(&mut core, 0), index(&mut core, 1));
    let call = core.computation_path_transport(unit, path, carried);
    let endpoint = core.value_returned(call);
    let written = core.value_type_element(endpoint, Level::zero());
    let swapped = core.computation_path_transport(unit, carried, path);
    let endpoint = core.value_returned(swapped);
    let written_apart = core.value_type_element(endpoint, Level::zero());
    let read = index(&mut core, 0);
    let inside = core.value_type_element(read, Level::zero());
    let constant = core.value_constant(ConstantIndex::from(0_usize));
    let at_constant = core.value_type_element(constant, Level::zero());

    let mut domain = DomainArena::new();
    let p = variable(&mut domain, BinderLevel::from(0_u32));
    let v = variable(&mut domain, BinderLevel::from(1_u32));
    let closure = |domain: &mut DomainArena, body, captures: &[DomainValueId]| {
        let mut environment = Environment::new();
        for &capture in captures {
            environment.extend(Zone::Intuitionistic, capture);
        }
        domain.value_closure_node(ValueBody::ValueType(body), environment)
    };
    let returned = |domain: &mut DomainArena, level: u32| {
        let motive = closure(domain, unit, &[]);
        let transported = domain
            .neutral_node(
                NeutralHead::Variable {
                    zone: Zone::Intuitionistic,
                    level: BinderLevel::from(level),
                },
                Vec::from([Elimination::PathTransport { motive, value: v }]),
                Unfolding::Rigid,
            )
            .expect("a transport along a variable mints");
        let held = domain.comp_neutral(transported, crate::domain::CompTermFace::Reduced);
        let neutral = domain
            .neutral_node(NeutralHead::Returned(held), Vec::new(), Unfolding::Rigid)
            .expect("a returned call mints");
        domain
            .value_neutral(neutral, TermFace::Reduced)
            .expect("the returned call resolves")
    };
    let writing = closure(&mut domain, written, &[v, p]);
    let writing_apart = closure(&mut domain, written_apart, &[v, p]);
    let over_variable = closure(&mut domain, inside, &[p]);
    let over_constant = closure(&mut domain, at_constant, &[]);
    let (one, other) = (returned(&mut domain, 0), returned(&mut domain, 1));
    let over_one = closure(&mut domain, written, &[one, p]);
    let over_other = closure(&mut domain, written, &[other, p]);
    let written_call = |side, against| {
        Ok(CodeReading::Over(alloc::vec![SetAside::Written(
            WrittenCall {
                side,
                call,
                closure: writing,
                against,
            }
        )]))
    };
    let at_p = Against::Variable(Zone::Intuitionistic, BinderLevel::from(0_u32));
    let compared =
        |left, right| compare_codes_over(&core, &domain, ConstantReading::Unread, left, right);

    assert_eq!(
        written_call(ConversionSide::Left, at_p),
        compared(writing, over_variable),
        "a written call against a variable is set aside"
    );
    assert_eq!(
        written_call(ConversionSide::Right, at_p),
        compared(over_variable, writing),
        "and so on the other side"
    );
    assert_eq!(
        written_call(
            ConversionSide::Left,
            Against::Written(swapped, writing_apart)
        ),
        compared(writing, writing_apart),
        "two calls whose parts part are set aside whole"
    );
    assert_eq!(
        Ok(CodeReading::Over(alloc::vec![SetAside::Held(one, other)])),
        compared(over_one, over_other),
        "two calls whose parts set aside held endpoints keep those pairs"
    );
    assert_eq!(
        Ok(CodeReading::Compared(CodeComparison::Undecided)),
        compared(writing, over_constant),
        "a written call against a constant sets nothing aside"
    );
}

#[test]
fn thunks_of_one_lambda_over_captures_laid_out_apart_are_alike_3976()
{
    // #3976, the layouts #3952's review found: `λq. return g`, written once
    // where `g` is the last binder and again in a scope that binds more, or
    // binds `g` elsewhere. Each body reads `g` at the index its own closure
    // holds it at, so the two bodies differ as syntax, and the environments
    // differ in depth. The walk reads each body's free variables through its
    // own environment. A body whose free variable reaches another capture
    // stays undecided.
    let mut core = CoreArena::new();
    let family = |core: &mut CoreArena| {
        let function = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
        let endpoint = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let forced = core.computation_force(function);
        let call = core.computation_application(forced, endpoint);
        let code = core.value_returned(call);
        core.value_type_element(code, Level::zero())
    };
    let lambda = |core: &mut CoreArena, index: u32| {
        let read = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index));
        let returned = core.computation_return(read);
        core.computation_lambda(returned)
    };
    let (near, again) = (family(&mut core), family(&mut core));
    let (innermost, one_out) = (lambda(&mut core, 1), lambda(&mut core, 2));

    let mut domain = DomainArena::new();
    let g = variable(&mut domain, BinderLevel::from(0_u32));
    let h = variable(&mut domain, BinderLevel::from(1_u32));
    let endpoint = variable(&mut domain, BinderLevel::from(2_u32));
    // A thunk of `body` over `captures`, the last of them innermost.
    let thunk = |domain: &mut DomainArena, body, captures: &[DomainValueId]| {
        let mut environment = Environment::new();
        for &capture in captures {
            environment.extend(Zone::Intuitionistic, capture);
        }
        let closure = domain.comp_closure_node(body, environment);
        domain.value_thunk(closure, TermFace::Reduced)
    };
    let motive = |domain: &mut DomainArena, body, function| {
        let mut environment = Environment::new();
        environment.extend(Zone::Intuitionistic, function);
        environment.extend(Zone::Intuitionistic, endpoint);
        domain.value_closure_node(ValueBody::ValueType(body), environment)
    };
    let defined = thunk(&mut domain, innermost, &[g]);
    let bound_before = thunk(&mut domain, innermost, &[h, g]);
    let bound_after = thunk(&mut domain, one_out, &[g, h]);
    let swapped = thunk(&mut domain, innermost, &[h, g]);
    let another = thunk(&mut domain, innermost, &[g, h]);
    let quoted = motive(&mut domain, near, defined);
    for (thunk, why) in [
        (bound_before, "a binder bound before `g` reads it alike"),
        (
            bound_after,
            "a binder bound after `g` reads it one further out, alike",
        ),
    ] {
        let other = motive(&mut domain, again, thunk);
        assert_eq!(
            CodeComparison::Equal,
            compare_rigidly(&core, &domain, quoted, other),
            "{why}"
        );
    }
    let laid_after = motive(&mut domain, near, bound_after);
    let laid_swapped = motive(&mut domain, again, swapped);
    assert_eq!(
        CodeComparison::Equal,
        compare_rigidly(&core, &domain, laid_after, laid_swapped),
        "two environments of one depth holding `g` at other places read it alike"
    );
    let other = motive(&mut domain, again, another);
    assert_eq!(
        CodeComparison::Undecided,
        compare_rigidly(&core, &domain, quoted, other),
        "a body reaching `h` where the other reaches `g` stays undecided"
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
