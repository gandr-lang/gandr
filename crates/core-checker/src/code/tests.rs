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
fn the_loose_reach_descends_every_former_and_subtracts_only_its_binders()
{
    use alloc::collections::BTreeMap;
    use alloc::sync::Arc;
    use alloc::vec::Vec;

    use gandr_core_term::ComponentCount;
    use gandr_core_term::control::EffectClause;
    use gandr_core_term::control::StackFrame;
    use gandr_core_term::effect::EffectName;
    use gandr_core_term::effect::EffectOp;
    use gandr_core_term::effect::EffectRow;
    use gandr_core_term::effect::EffectSig;
    use gandr_core_term::effect::OperationName;
    use gandr_core_term::effect::capability::CapabilityGrade;
    use gandr_core_term::effect::capability::Region;
    use gandr_core_term::effect::capability::RegionDepth;
    use gandr_core_term::hole::MarkIndex;
    use gandr_core_term::memory::HoldGrade;
    use gandr_core_term::memory::MemoryForm;
    use gandr_core_term::session::RecordedMove;
    use gandr_core_term::session::SessionAction;
    use gandr_core_term::session::SessionRelation;
    use gandr_core_term::world::World;
    use gandr_core_term::world::WorldForm;
    use gandr_core_term::world::WorldType;
    use gandr_kernel_term::Component;
    use gandr_kernel_term::ConstructorTag;
    use gandr_kernel_term::FieldLabel;
    use gandr_kernel_term::PathEvidence;
    use gandr_kernel_term::Stage;
    use gandr_kernel_term::StageId;
    use gandr_kernel_term::Summand;

    let mut arena = CoreArena::new();
    let five = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(5_u32));
    let unit = arena.value_unit();
    let integer = arena.value_type_base(BaseType::Integer);
    let decoded = arena.value_type_element(five, Level::zero());
    let returns_decoded = arena.comp_type_returner(decoded);
    let returns_integer = arena.comp_type_returner(integer);
    let reads = arena.computation_return(five);
    let returns_unit = arena.computation_return(unit);
    let label = || FieldLabel::from(alloc::string::String::from("x"));
    let data_at_five = arena.value_type_data(ConstantIndex::from(0_usize), Vec::from([five]));
    let pair = ComponentCount::from(2_usize);
    let signature = |payload| {
        EffectSig::new(EffectName::from("Probe"), [EffectOp {
            name: OperationName::from("poke"),
            payload,
            reply: payload,
        }])
        .expect("one operation")
    };
    let plain = signature(integer);
    let naming = signature(decoded);
    let poking = |body| -> Arc<[EffectClause]> {
        Arc::from([EffectClause {
            operation: OperationName::from("poke"),
            body,
        }])
    };
    let effect_rows = [
        (
            arena.computation_perform(naming.clone(), OperationName::from("poke"), unit),
            6,
            "a performed operation's types",
        ),
        (
            arena.computation_perform(plain.clone(), OperationName::from("poke"), five),
            6,
            "a performed payload",
        ),
        (
            arena.computation_exercise(five, plain.clone(), OperationName::from("poke"), unit),
            6,
            "an exercised capability",
        ),
        (
            arena.computation_exercise(unit, naming.clone(), OperationName::from("poke"), five),
            6,
            "an exercised payload and types",
        ),
        (
            arena.computation_handle(plain.clone(), reads, returns_unit, poking(returns_unit)),
            6,
            "a handled subject binds none",
        ),
        (
            arena.computation_handle(plain.clone(), returns_unit, reads, poking(returns_unit)),
            5,
            "a handler's return binds one",
        ),
        (
            arena.computation_handle(plain.clone(), returns_unit, returns_unit, poking(reads)),
            4,
            "a handler's clause binds two",
        ),
        (
            arena.computation_scope(plain.clone(), reads, returns_unit, poking(returns_unit)),
            5,
            "a scoped subject binds its capability",
        ),
        (
            arena.computation_scope(plain, returns_unit, returns_unit, poking(reads)),
            4,
            "a scope's clause binds two",
        ),
        (
            arena.computation_scope(naming, returns_unit, returns_unit, poking(returns_unit)),
            6,
            "a scope's signature binds none",
        ),
        (
            arena.computation_ascribe(reads, returns_integer),
            6,
            "an ascribed body",
        ),
        (
            arena.computation_ascribe(returns_unit, returns_decoded),
            6,
            "an ascription",
        ),
        (
            arena.computation_session(SessionAction::Send {
                endpoint: DeBruijnIndex::from(0_u32),
                payload: five,
            }),
            6,
            "a sent payload",
        ),
        (
            arena.computation_session(SessionAction::Receive {
                endpoint: DeBruijnIndex::from(0_u32),
                body: reads,
            }),
            6,
            "a receive binds only linearly",
        ),
        (
            arena.computation_memory(MemoryForm::Hold {
                value: five,
                body: returns_unit,
                grade: HoldGrade::One,
            }),
            6,
            "a held value",
        ),
        (
            arena.computation_memory(MemoryForm::Hold {
                value: unit,
                body: reads,
                grade: HoldGrade::Many,
            }),
            6,
            "a hold binds only linearly",
        ),
        (
            arena.computation_world(WorldForm::Migrate {
                world: World::Host,
                body: reads,
            }),
            6,
            "a migration binds nothing",
        ),
    ];
    let value = |at| CoreNode::Term(TermNode::Value(at));
    let computation = |at| CoreNode::Term(TermNode::Computation(at));
    let value_type = |at| CoreNode::Type(TypeNode::Value(at));
    let comp_type = |at| CoreNode::Type(TypeNode::Computation(at));
    let rows: Vec<(CoreNode, usize, &str)> = Vec::from([
        (
            value(arena.value_record(BTreeMap::from([(label(), five)]))),
            6,
            "a record field",
        ),
        (
            value(arena.value_reify(Arc::from([StackFrame::Apply(five)]))),
            6,
            "an applied frame",
        ),
        (
            value(arena.value_reify(Arc::from([StackFrame::Bind(reads)]))),
            5,
            "a bind frame binds one",
        ),
        (
            value(arena.value_path_product(unit, five)),
            6,
            "a path product",
        ),
        (value(arena.value_funext(five, unit)), 6, "a funext"),
        (value(arena.value_equiv(unit, five)), 6, "an equivalence"),
        (value(arena.value_univalence(five, unit)), 6, "a univalence"),
        (value(arena.value_then(unit, five)), 6, "a composite"),
        (
            value(arena.value_flow_product(five, unit)),
            6,
            "a flow product",
        ),
        (
            value(arena.value_function_flow(unit, five)),
            6,
            "a function flow",
        ),
        (value(arena.value_list_cons(five, unit)), 6, "a cons cell"),
        (
            value(arena.value_static_application(unit, five)),
            6,
            "a static application",
        ),
        (value(arena.value_path_refl(five)), 6, "a reflexivity"),
        (value(arena.value_here(five)), 6, "a here"),
        (value(arena.value_stay(five)), 6, "a stay"),
        (value(arena.value_forward(five)), 6, "a forward"),
        (
            value(arena.value_injection(Summand::from(1_usize), five)),
            6,
            "an injection",
        ),
        (value(arena.value_lift(Level::zero(), five)), 6, "a lift"),
        (
            value(arena.value_mark(MarkIndex::from(0_u32), five)),
            6,
            "a marked value",
        ),
        (
            value(arena.value_returned(reads)),
            6,
            "a returned computation",
        ),
        (value(arena.value_nested(reads)), 6, "a nested computation"),
        (value(arena.value_run(reads)), 6, "a run"),
        (
            value(arena.value_constructor(data_at_five, ConstructorTag::from(0_usize), Vec::new())),
            6,
            "a constructor's datatype",
        ),
        (
            value(arena.value_constructor(
                integer,
                ConstructorTag::from(0_usize),
                Vec::from([five]),
            )),
            6,
            "a constructor's field",
        ),
        (
            computation(arena.computation_record_projection(five, label())),
            6,
            "a record projection",
        ),
        (
            computation(arena.computation_tuple_projection(five, Component::from(0_usize))),
            6,
            "a tuple projection",
        ),
        (
            computation(arena.computation_split(unit, pair, reads)),
            4,
            "a split binds its arity",
        ),
        (
            computation(arena.computation_dependent_split(
                unit,
                pair,
                returns_decoded,
                returns_unit,
            )),
            5,
            "a split's motive binds its scrutinee",
        ),
        (
            computation(arena.computation_resume(five, returns_unit)),
            6,
            "a resumed stack",
        ),
        (
            computation(arena.computation_with(&[reads])),
            6,
            "a with component",
        ),
        (computation(arena.computation_reset(reads)), 6, "a reset"),
        (
            computation(arena.computation_project(Component::from(0_usize), reads)),
            6,
            "a projected subject",
        ),
        (
            computation(arena.computation_mark(MarkIndex::from(0_u32), reads)),
            6,
            "a marked computation",
        ),
        (
            computation(arena.computation_shift(reads)),
            5,
            "a shift binds one",
        ),
        (
            computation(arena.computation_list_fold(integer, integer, unit, returns_unit, reads)),
            4,
            "a fold's cons arm binds two",
        ),
        (
            computation(arena.computation_list_fold(integer, integer, unit, reads, returns_unit)),
            6,
            "a fold's nil arm binds none",
        ),
        (
            computation(arena.computation_list_case(unit, returns_unit, reads)),
            4,
            "a list case's cons arm binds two",
        ),
        (
            computation(arena.computation_transport(five, unit)),
            6,
            "a transport",
        ),
        (
            computation(arena.computation_path_transport(decoded, unit, unit)),
            5,
            "a transport's motive binds one",
        ),
        (
            computation(arena.computation_ride(integer, unit, five)),
            6,
            "a ride's value",
        ),
        (
            computation(arena.computation_telescope_transport(
                returns_decoded,
                unit,
                unit,
                unit,
                unit,
            )),
            6,
            "a telescope's motive binds none of its own",
        ),
        (
            computation(arena.computation_abandon(five)),
            6,
            "an abandon",
        ),
        (
            computation(arena.computation_case(unit, &[reads])),
            5,
            "a case branch binds one",
        ),
        (
            computation(arena.computation_data_case(
                unit,
                returns_decoded,
                Vec::from([returns_unit]),
            )),
            5,
            "a data case's motive binds one",
        ),
        (
            computation(arena.computation_data_case(
                five,
                returns_integer,
                Vec::from([returns_unit]),
            )),
            6,
            "a data case's scrutinee",
        ),
        (
            computation(arena.computation_world(WorldForm::Hold { value: five })),
            6,
            "a held value",
        ),
        (
            computation(arena.computation_world(WorldForm::Leta {
                value: unit,
                body: reads,
            })),
            5,
            "a leta binds one",
        ),
        (value_type(data_at_five), 6, "a data type's argument"),
        (
            value_type(arena.value_type_record(BTreeMap::from([(label(), decoded)]))),
            6,
            "a record type's field",
        ),
        (
            value_type(arena.value_type_stack(returns_decoded, returns_integer)),
            6,
            "a stack type",
        ),
        (
            value_type(arena.value_type_path_universe(unit, five)),
            6,
            "a path universe",
        ),
        (
            value_type(arena.value_type_flow(integer, five, unit)),
            6,
            "a flow type",
        ),
        (value_type(arena.value_type_run(five)), 6, "a run type"),
        (
            value_type(arena.value_type_sum(&[integer, decoded])),
            6,
            "a summand",
        ),
        (
            value_type(arena.value_type_sigma(integer, decoded)),
            5,
            "a sigma's second binds one",
        ),
        (
            value_type(arena.value_type_sigma(decoded, integer)),
            6,
            "a sigma's first binds none",
        ),
        (
            value_type(arena.value_type_static_pi(decoded, integer)),
            6,
            "a static pi",
        ),
        (value_type(arena.value_type_list(decoded)), 6, "a list type"),
        (
            value_type(arena.value_type_lift(decoded, Level::zero())),
            6,
            "a lifted type",
        ),
        (
            value_type(arena.value_type_staged(decoded, Stage::At(StageId::from(0_usize)))),
            6,
            "a staged type",
        ),
        (
            value_type(arena.value_type_world(WorldType::At {
                inner: decoded,
                world: World::Host,
            })),
            6,
            "a type held at a world",
        ),
        (
            value_type(arena.value_type_capability(
                EffectRow::singleton(signature(decoded)),
                CapabilityGrade::Durable,
                Region::Scoped(RegionDepth::from(1_u32)),
            )),
            6,
            "a capability's operations",
        ),
        (
            value(arena.value_path_equiv(
                decoded,
                unit,
                unit,
                Arc::new(PathEvidence {
                    source: Vec::new(),
                    target: Vec::new(),
                }),
            )),
            6,
            "an equivalence's path type",
        ),
        (
            value(arena.value_path_equiv(
                integer,
                five,
                unit,
                Arc::new(PathEvidence {
                    source: Vec::new(),
                    target: Vec::new(),
                }),
            )),
            6,
            "an equivalence's forward map",
        ),
        (
            value(
                arena.value_recorded(Arc::from([RecordedMove::Closed, RecordedMove::Sent(five)])),
            ),
            6,
            "a recorded payload",
        ),
        (
            value(arena.value_session_related(SessionRelation::Subtyping, unit, five)),
            6,
            "a session relation",
        ),
        (
            comp_type(arena.comp_type_with(&[returns_decoded])),
            6,
            "a with type",
        ),
        (
            comp_type(arena.comp_type_element(five, Level::zero())),
            6,
            "a decoded computation type",
        ),
        (
            comp_type(arena.comp_type_codata(ConstantIndex::from(0_usize), Vec::from([five]))),
            6,
            "a codata argument",
        ),
    ]);
    let effect_rows = effect_rows.map(|(at, reach, former)| (computation(at), reach, former));
    for (root, reach, former) in rows.into_iter().chain(effect_rows) {
        assert_eq!(
            loose_reach(&arena, root),
            Ok(BinderDepth::from(reach)),
            "{former}"
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
