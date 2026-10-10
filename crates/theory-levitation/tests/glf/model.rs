//! Typed normal carriers of the generated identity-return presentation.
//!
//! Terms are compared at a fixed context and computation type. The raw core
//! lambda node erases its domain and codomain, so an untyped map cannot be
//! injective. Type parameters are instantiated by three distinct core types.

use gandr_core_nbe::CompTermFace;
use gandr_core_nbe::Definitions;
use gandr_core_nbe::DomainArena;
use gandr_core_nbe::DomainComp;
use gandr_core_nbe::Environment;
use gandr_core_nbe::Fuel;
use gandr_core_nbe::LoweredChain;
use gandr_core_nbe::ReadbackMode;
use gandr_core_nbe::eval_computation;
use gandr_core_nbe::readback_computation;
use gandr_core_term::CompType;
use gandr_core_term::CompTypeId;
use gandr_core_term::Computation;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::DefinitionalEnvironment;
use gandr_core_term::Value;
use gandr_core_term::ValueType;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::LevelSignature;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::SignDesc;
use gandr_theory_levitation::TermView;
use gandr_theory_levitation::first_order;
use proptest::prelude::*;

/// An external value-type parameter of the model.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Atom
{
    /// First parameter.
    Unit,
    /// Second parameter.
    Integer,
    /// Third parameter.
    String,
}

/// A scoped, typed model judgement in normal (implicit substitution) notation.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Judgement
{
    /// The ambient context, oldest first.
    context: Vec<Atom>,
    /// The computation type, retaining lambda annotations.
    ty: FreeTerm,
    /// The generated operations and canonical q/p variables.
    term: FreeTerm,
}

/// The corresponding judgement over core arena nodes.
#[derive(Clone, Debug)]
struct CoreJudgement
{
    /// The ambient context, oldest first.
    context: Vec<ValueTypeId>,
    /// The expected computation type.
    ty: CompTypeId,
    /// The computation term.
    term: ComputationId,
}

/// A seed selecting a variable from a nonempty context.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct VariableChoice(u32);

impl From<u8> for Atom
{
    /// Select one of the external parameter instances.
    ///
    /// # Specification
    /// trivial.
    fn from(value: u8) -> Self
    {
        match value % 3 {
            | 0 => Self::Unit,
            | 1 => Self::Integer,
            | _ => Self::String,
        }
    }
}

/// The syntax of one type parameter.
///
/// # Specification
/// trivial.
fn atom_term(atom: Atom) -> FreeTerm
{
    FreeTerm::var(match atom {
        | Atom::Unit => "A0",
        | Atom::Integer => "A1",
        | Atom::String => "A2",
    })
}

/// Interpret a type parameter in the core arena.
///
/// # Specification
/// trivial.
fn atom_core(
    core: &mut CoreArena,
    atom: Atom,
) -> ValueTypeId
{
    match atom {
        | Atom::Unit => core.value_type_unit(),
        | Atom::Integer => core.value_type_base(BaseType::Integer),
        | Atom::String => core.value_type_base(BaseType::String),
    }
}

/// Recover a parameter from its distinct core instance.
///
/// # Specification
/// - requires: `ty` is one of the three external parameter instances.
/// - ensures: the parameter whose instance is `ty`.
/// - panics: an unrelated or dangling core type is outside the fixture domain.
///
/// # Adequacy
/// - hypothesis: L3 — varying domains and result types distinguishes collapsed
///   parameter identities in either composite.
/// - witness: `tests::glf::model::identification`
#[anodized::spec(ensures: |result| matches!(result, Atom::Unit | Atom::Integer | Atom::String))]
fn core_atom(
    core: &CoreArena,
    ty: ValueTypeId,
) -> Atom
{
    match *core.value_type(ty).expect("held value type") {
        | ValueType::Unit => Atom::Unit,
        | ValueType::Base(BaseType::Integer) => Atom::Integer,
        | ValueType::Base(BaseType::String) => Atom::String,
        | _ => panic!("not a parameter instance"),
    }
}

/// Recover a parameter from its syntax.
///
/// # Specification
/// - requires: the node is a fixture's type parameter.
/// - ensures: the unique corresponding parameter.
/// - panics: another term is outside the fixture domain.
///
/// # Adequacy
/// - hypothesis: L3 — all three parameters in both composites expose collapse.
/// - witness: `tests::glf::model::identification`
#[anodized::spec(ensures: |result| matches!(result, Atom::Unit | Atom::Integer | Atom::String))]
fn term_atom(node: gandr_theory_levitation::TermNode<'_>) -> Atom
{
    match node.view() {
        | TermView::Var(name) => match name.as_ref() {
            | "A0" => Atom::Unit,
            | "A1" => Atom::Integer,
            | "A2" => Atom::String,
            | _ => panic!("not a type parameter"),
        },
        | _ => panic!("not a type parameter"),
    }
}

/// Canonical variable q[p]...[p], with the index counting weakenings.
///
/// # Specification
/// - ensures: exactly `index` weakenings of the newest variable.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — innermost, outermost and intermediate references expose
///   off-by-one errors and reversed index direction.
/// - witness: `tests::glf::model::identification`
#[anodized::spec(ensures: |ref term| matches!(term.view(), TermView::Op { .. }))]
fn variable(index: DeBruijnIndex) -> FreeTerm
{
    let mut term = FreeTerm::op("$q_VTm", []);
    for _ in 0 .. u32::from(index) {
        term = FreeTerm::op("$sub_VTm", [term, FreeTerm::op("$p_VTm", [])]);
    }
    term
}

/// Generate a normal judgement using the translated operation telescopes.
///
/// # Specification
/// - requires: `model` is the translated identity-return signature and context
///   plus domains is nonempty; choices name type parameters and a variable.
/// - ensures: a well-scoped term, with every lambda's type indices retained;
///   the returned variable may name any ambient or local binder.
/// - panics: a missing generated operation or empty total context violates the
///   fixture preconditions.
///
/// # Adequacy
/// - hypothesis: L3 — zero and many lambdas, differing domains, and every
///   reachable index distinguish a constant-identity generator.
/// - witness: `tests::glf::model::identification`
#[anodized::spec(captures: original = context.clone(), ensures: |ref judgement| judgement.context == original)]
fn generate(
    model: &SignDesc<()>,
    context: Vec<Atom>,
    domains: &[Atom],
    choice: VariableChoice,
) -> Judgement
{
    let lam = model
        .opers
        .iter()
        .find(|op| op.name.as_ref() == "lam")
        .expect("generated lambda");
    assert_eq!(
        lam.arity.inputs[3].arguments[0].to_string(),
        "$extend_VTm(G, A)"
    );
    let ret = model
        .opers
        .iter()
        .find(|op| op.name.as_ref() == "ret")
        .expect("generated return");
    assert_eq!(ret.arity.outputs[0].arguments[1].to_string(), "F(A)");
    let all: Vec<Atom> = context.iter().chain(domains).copied().collect();
    let index = choice
        .0
        .checked_rem(u32::try_from(all.len()).expect("bounded context"))
        .expect("nonempty context");
    let index = DeBruijnIndex::from(index);
    let result = all[all
        .len()
        .saturating_sub(1)
        .saturating_sub(usize::try_from(u32::from(index)).expect("bounded index"))];
    let mut ty = FreeTerm::op("F", [atom_term(result)]);
    let mut term = FreeTerm::op(ret.name.clone(), [atom_term(result), variable(index)]);
    for &domain in domains.iter().rev() {
        term = FreeTerm::op(lam.name.clone(), [atom_term(domain), ty.clone(), term]);
        ty = FreeTerm::op("Arrow", [atom_term(domain), ty]);
    }
    Judgement { context, ty, term }
}

/// Map generated type and term formers into the core arena, without recursion.
///
/// # Specification
/// - requires: a normal, well-typed identity-return judgement.
/// - ensures: F/Arrow/ret/lam/q[p] map to Returner/Arrow/Return/Lambda/Variable
///   respectively, preserving the context and all type parameter identities.
/// - panics: malformed fixture syntax is outside the domain.
///
/// # Adequacy
/// - hypothesis: L2 — both structural composites, including independently built
///   core inputs, distinguish omissions, reordering and index shifts.
/// - witness: `tests::glf::model::identification`
#[anodized::spec(ensures: |ref result| result.context.len() == judgement.context.len())]
fn to_core(
    core: &mut CoreArena,
    judgement: &Judgement,
) -> CoreJudgement
{
    let context = judgement
        .context
        .iter()
        .map(|&atom| atom_core(core, atom))
        .collect();
    let mut types = Vec::new();
    let mut node = judgement.ty.to_node();
    let result = loop {
        let TermView::Op { name, mut args } = node.view()
        else {
            panic!("computation type");
        };
        let first = args.next().expect("type argument");
        if name.as_ref() == "F" {
            break atom_core(core, term_atom(first));
        }
        assert_eq!(name.as_ref(), "Arrow");
        types.push(atom_core(core, term_atom(first)));
        node = args.next().expect("codomain");
    };
    let mut ty = core.comp_type_returner(result);
    for domain in types.into_iter().rev() {
        ty = core.comp_type_arrow(domain, ty);
    }
    let mut lambdas = 0_u32;
    let mut node = judgement.term.to_node();
    let value = loop {
        let TermView::Op { name, mut args } = node.view()
        else {
            panic!("computation term");
        };
        if name.as_ref() == "ret" {
            break args.nth(1).expect("return value");
        }
        assert_eq!(name.as_ref(), "lam");
        lambdas = lambdas.saturating_add(1);
        node = args.nth(2).expect("lambda body");
    };
    let mut value = value;
    let mut index = 0_u32;
    loop {
        let TermView::Op { name, mut args } = value.view()
        else {
            panic!("variable term");
        };
        if name.as_ref() == "$q_VTm" {
            break;
        }
        assert_eq!(name.as_ref(), "$sub_VTm");
        value = args.next().expect("weakened variable");
        assert!(
            matches!(args.next().expect("weakening").view(), TermView::Op { name, .. } if name.as_ref() == "$p_VTm")
        );
        index = index.saturating_add(1);
    }
    let value = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(index));
    let mut term = core.computation_return(value);
    for _ in 0 .. lambdas {
        term = core.computation_lambda(term);
    }
    CoreJudgement { context, ty, term }
}

/// Recover generated syntax from a core term at its expected type.
///
/// # Specification
/// - requires: `judgement` is a well-typed core identity-return judgement.
/// - ensures: the canonical generated term and type at the same context;
///   annotations are recovered from the judgement, not guessed from Lambda.
/// - panics: foreign formers or a type/term mismatch violate the precondition.
///
/// # Adequacy
/// - hypothesis: L2 — independently generated core spines and both composites
///   distinguish a dropped type, reversed binder or wrong q/p count.
/// - witness: `tests::glf::model::identification`
#[anodized::spec(ensures: |ref result| result.context.len() == judgement.context.len())]
fn from_core(
    core: &CoreArena,
    judgement: &CoreJudgement,
) -> Judgement
{
    let context = judgement
        .context
        .iter()
        .map(|&ty| core_atom(core, ty))
        .collect();
    let mut domains = Vec::new();
    let mut ty = judgement.ty;
    let mut term = judgement.term;
    let (result, index) = loop {
        match (
            core.comp_type(ty).expect("held type"),
            core.computation(term).expect("held term"),
        ) {
            | (&CompType::Arrow { domain, codomain }, &Computation::Lambda(body)) => {
                domains.push(core_atom(core, domain));
                ty = codomain;
                term = body;
            },
            | (&CompType::Returner(result), &Computation::Return(value)) => {
                let Value::Variable {
                    zone: Zone::Intuitionistic,
                    index,
                } = *core.value(value).expect("held variable")
                else {
                    panic!("intuitionistic variable");
                };
                break (core_atom(core, result), index);
            },
            | _ => panic!("foreign former or type mismatch"),
        }
    };
    let mut ty = FreeTerm::op("F", [atom_term(result)]);
    let mut term = FreeTerm::op("ret", [atom_term(result), variable(index)]);
    for domain in domains.into_iter().rev() {
        term = FreeTerm::op("lam", [atom_term(domain), ty.clone(), term]);
        ty = FreeTerm::op("Arrow", [atom_term(domain), ty]);
    }
    Judgement { context, ty, term }
}

/// Independently build a core judgement, without passing through model syntax.
///
/// # Specification
/// - requires: `domains` is nonempty and `choice` is an arbitrary index seed.
/// - ensures: a well-scoped closed lambda spine returning the selected
///   variable.
/// - panics: empty domains violate the fixture precondition.
///
/// # Adequacy
/// - hypothesis: L3 — mixed domains and extreme indices separate reverse-map
///   errors from mistakes shared by the forward construction.
/// - witness: `tests::glf::model::identification`
#[anodized::spec(ensures: |ref result| result.context.is_empty())]
fn independent_core(
    core: &mut CoreArena,
    domains: &[Atom],
    choice: VariableChoice,
) -> CoreJudgement
{
    let selected = usize::try_from(choice.0)
        .expect("bounded choice")
        .checked_rem(domains.len())
        .expect("nonempty domains");
    let result = atom_core(
        core,
        domains[domains.len().saturating_sub(1).saturating_sub(selected)],
    );
    let mut ty = core.comp_type_returner(result);
    let variable = core.value_variable(
        Zone::Intuitionistic,
        DeBruijnIndex::from(u32::try_from(selected).expect("bounded index")),
    );
    let mut term = core.computation_return(variable);
    for &domain in domains.iter().rev() {
        let domain = atom_core(core, domain);
        ty = core.comp_type_arrow(domain, ty);
        term = core.computation_lambda(term);
    }
    CoreJudgement {
        context: Vec::new(),
        ty,
        term,
    }
}

/// Assert structural core identity, ignoring allocator-assigned node ids.
///
/// # Specification
/// - requires: both inputs are identity-return judgements in `core`.
/// - ensures: returns only when context, types, formers and indices coincide.
/// - panics: a structural mismatch.
///
/// # Adequacy
/// - hypothesis: L3 — independently chosen domain and index variations expose
///   comparison of only one side of a judgement.
/// - witness: `tests::glf::model::identification`
#[anodized::spec(ensures: left.context.len() == right.context.len())]
fn assert_core_identity(
    core: &CoreArena,
    left: &CoreJudgement,
    right: &CoreJudgement,
)
{
    assert_eq!(
        left.context
            .iter()
            .map(|&ty| core_atom(core, ty))
            .collect::<Vec<_>>(),
        right
            .context
            .iter()
            .map(|&ty| core_atom(core, ty))
            .collect::<Vec<_>>()
    );
    let (mut lt, mut rt) = (left.ty, right.ty);
    loop {
        match (
            core.comp_type(lt).expect("left type"),
            core.comp_type(rt).expect("right type"),
        ) {
            | (
                &CompType::Arrow {
                    domain: ld,
                    codomain: lc,
                },
                &CompType::Arrow {
                    domain: rd,
                    codomain: rc,
                },
            ) => {
                assert_eq!(core.value_type(ld), core.value_type(rd));
                lt = lc;
                rt = rc;
            },
            | (&CompType::Returner(l), &CompType::Returner(r)) => {
                assert_eq!(core.value_type(l), core.value_type(r));
                break;
            },
            | _ => panic!("type shape changed"),
        }
    }
    let (mut lt, mut rt) = (left.term, right.term);
    loop {
        match (
            core.computation(lt).expect("left term"),
            core.computation(rt).expect("right term"),
        ) {
            | (&Computation::Lambda(l), &Computation::Lambda(r)) => {
                lt = l;
                rt = r;
            },
            | (&Computation::Return(l), &Computation::Return(r)) => {
                assert_eq!(core.value(l), core.value(r));
                break;
            },
            | _ => panic!("term shape changed"),
        }
    }
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 256, rng_seed: proptest::test_runner::RngSeed::Fixed(0x0047_4c46), ..ProptestConfig::default() })]
    #[test]
    fn identification(ambient in prop::collection::vec(0_u8..3, 1..9), domains in prop::collection::vec(0_u8..3, 0..48), choice in 0_u32..256) {
        let model = first_order(&super::identity_return()).expect("translated model");
        let context: Vec<Atom> = ambient.into_iter().map(Atom::from).collect();
        let domains: Vec<Atom> = domains.into_iter().map(Atom::from).collect();
        let judgement = generate(&model, context.clone(), &domains, VariableChoice(choice));
        let mut core = CoreArena::new();
        let mapped = to_core(&mut core, &judgement);
        prop_assert_eq!(from_core(&core, &mapped), judgement);
        let closed: Vec<Atom> = context.into_iter().chain(domains).collect();
        let independent = independent_core(&mut core, &closed, VariableChoice(choice));
        let recovered = from_core(&core, &independent);
        let rebuilt = to_core(&mut core, &recovered);
        assert_core_identity(&core, &independent, &rebuilt);
    }

    #[test]
    fn both_views(ambient in prop::collection::vec(0_u8..3, 1..9), domains in prop::collection::vec(0_u8..3, 0..64), choice in 0_u32..512) {
        let model = first_order(&super::identity_return()).expect("translated model");
        let context: Vec<Atom> = ambient.into_iter().map(Atom::from).collect();
        let domains: Vec<Atom> = domains.into_iter().map(Atom::from).collect();
        let judgement = generate(&model, context, &domains, VariableChoice(choice));
        let mut core = CoreArena::new();
        let open = to_core(&mut core, &judgement);
        // The public evaluator is closed. Abstract the ambient context, run
        // uncached quotation, then reopen exactly that many binders.
        let mut mapped = CoreJudgement { context: Vec::new(), ty: open.ty, term: open.term };
        for &domain in open.context.iter().rev() {
            mapped.ty = core.comp_type_arrow(domain, mapped.ty);
            mapped.term = core.computation_lambda(mapped.term);
        }
        let chain = LoweredChain::new();
        let environment = DefinitionalEnvironment::new();
        let definitions = Definitions::new(&chain, &environment, environment.root());
        let mut domain = DomainArena::new();
        let budget = Fuel::from(100_000_u32);
        let evaluated = eval_computation(&core, &mut domain, definitions, budget, mapped.term).expect("evaluation");
        let DomainComp::Lambda { body, face } = *domain.computation(evaluated).expect("lambda head") else { panic!("lambda must commute"); };
        prop_assert_eq!(face, CompTermFace::Source(mapped.term));
        let closure = domain.comp_closure(body).expect("held closure");
        prop_assert_eq!(closure.environment(), &Environment::new());
        let Computation::Lambda(expected_body) = *core.computation(mapped.term).expect("core lambda") else { panic!("lambda input"); };
        prop_assert_eq!(closure.body(), expected_body);
        let read = readback_computation(&mut core, &mut domain, definitions, ReadbackMode::Unfolding, budget, evaluated).expect("uncached readback");
        prop_assert_ne!(read, mapped.term);
        let mut rebuilt = CoreJudgement { term: read, ..mapped.clone() };
        assert_core_identity(&core, &mapped, &rebuilt);
        for _ in &open.context {
            let &Computation::Lambda(body) = core.computation(rebuilt.term).expect("quoted lambda") else { panic!("context abstraction"); };
            let &CompType::Arrow { codomain, .. } = core.comp_type(rebuilt.ty).expect("quoted arrow") else { panic!("context type"); };
            rebuilt.term = body;
            rebuilt.ty = codomain;
        }
        rebuilt.context = open.context;
        prop_assert_eq!(from_core(&core, &rebuilt), judgement);
    }
}

#[test]
pub fn kernel()
{
    let model = first_order(&super::identity_return()).expect("generated model");
    let judgement = generate(&model, Vec::new(), &[Atom::Unit], VariableChoice(0));
    let mut core = CoreArena::new();
    let mapped = to_core(&mut core, &judgement);
    let mut environment = gandr_kernel_core::Environment::new();
    let staged = {
        let mut staging = environment.stage();
        let arena = staging.arena();
        let (arrow, lambda) = trusted_image(&core, &mapped, arena);
        let declared = arena.value_type_thunk(arrow);
        let body = arena.value_thunk(lambda);
        staging.def(LevelSignature::monomorphic(), declared, body)
    };
    let checked = environment
        .add_decl(staged)
        .expect("identity-return admitted");
    assert_eq!(usize::from(checked.position()), 0);
    let staged = {
        let mut staging = environment.stage();
        let arena = staging.arena();
        let a = arena.value_type_unit();
        let result = arena.comp_type_returner(a);
        let declared = arena.value_type_thunk(result);
        let x = arena.value_variable(DeBruijnIndex::from(0_u32));
        let body = arena.computation_return(x);
        let lambda = arena.computation_lambda(body);
        let argument = arena.value_unit();
        // Application synthesizes its head; the expected result cannot supply
        // the lambda's missing domain annotation.
        let application = arena.computation_application(lambda, argument);
        let body = arena.value_thunk(application);
        staging.def(LevelSignature::monomorphic(), declared, body)
    };
    assert!(matches!(
        environment.add_decl(staged),
        Err(gandr_kernel_core::KernelError::NotInferable {
            form: gandr_kernel_core::NonInferableForm::Lambda
        })
    ));
}

#[test]
fn return_commutes_and_environment_extension_is_an_isomorphism()
{
    use gandr_core_nbe::DomainValue;
    use gandr_core_nbe::eval_value;
    use gandr_core_nbe::eval_value_within;
    let mut core = CoreArena::new();
    let first = core.value_unit();
    let second = core.value_constant(gandr_kernel_term::ConstantIndex::from(0_usize));
    let chain = LoweredChain::new();
    let definitions_environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(
        &chain,
        &definitions_environment,
        definitions_environment.root(),
    );
    let mut domain = DomainArena::new();
    let budget = Fuel::from(4096_u32);
    let first_value =
        eval_value(&core, &mut domain, definitions, budget, first).expect("first value");
    let second_value =
        eval_value(&core, &mut domain, definitions, budget, second).expect("second value");
    let mut environment = Environment::new();
    environment.extend(Zone::Intuitionistic, first_value);
    environment.extend(Zone::Linear, second_value);
    let original = environment.clone();
    environment.extend(Zone::Intuitionistic, second_value);
    assert_eq!(usize::from(environment.depth(Zone::Intuitionistic)), 2);
    assert_eq!(
        environment.depth(Zone::Linear),
        original.depth(Zone::Linear)
    );
    assert_eq!(
        environment.lookup(Zone::Linear, DeBruijnIndex::from(0_u32)),
        original.lookup(Zone::Linear, DeBruijnIndex::from(0_u32))
    );
    assert_eq!(
        environment.lookup(Zone::Intuitionistic, DeBruijnIndex::from(0_u32)),
        Some(second_value)
    );
    assert_eq!(
        environment.lookup(Zone::Intuitionistic, DeBruijnIndex::from(1_u32)),
        Some(first_value)
    );
    // Project prefix and final value, then pair them back. This is a data
    // isomorphism, not identity of the product with the Environment record.
    let last = environment
        .lookup(Zone::Intuitionistic, DeBruijnIndex::from(0_u32))
        .expect("final entry");
    let prefix = environment
        .lookup(Zone::Intuitionistic, DeBruijnIndex::from(1_u32))
        .expect("prefix entry");
    assert_eq!(
        Some(prefix),
        original.lookup(Zone::Intuitionistic, DeBruijnIndex::from(0_u32))
    );
    assert_eq!(last, second_value);
    let mut reconstructed = Environment::new();
    reconstructed.extend(Zone::Intuitionistic, prefix);
    reconstructed.extend(Zone::Intuitionistic, last);
    reconstructed.extend(
        Zone::Linear,
        original
            .lookup(Zone::Linear, DeBruijnIndex::from(0_u32))
            .expect("linear entry"),
    );
    assert_eq!(reconstructed, environment);
    // q reads the supplied semantic value exactly, without re-evaluation.
    let q = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let (read_q, _) = eval_value_within(&core, &mut domain, definitions, budget, q, environment)
        .expect("environment lookup");
    assert_eq!(read_q, second_value);
    for (term, expected) in [(first, first_value), (second, second_value)] {
        let returned = core.computation_return(term);
        let evaluated = eval_computation(&core, &mut domain, definitions, budget, returned)
            .expect("return evaluation");
        let DomainComp::Return { value, face } =
            *domain.computation(evaluated).expect("return head")
        else {
            panic!("ret constructor");
        };
        assert_eq!(face, CompTermFace::Source(returned));
        match (
            domain.value(value).expect("return value"),
            domain.value(expected).expect("independent value"),
        ) {
            | (&DomainValue::Unit { face: left }, &DomainValue::Unit { face: right }) => {
                assert_eq!(left, right);
            },
            | (
                &DomainValue::Neutral {
                    neutral: left,
                    face: left_face,
                },
                &DomainValue::Neutral {
                    neutral: right,
                    face: right_face,
                },
            ) => {
                // Distinct allocations are not a strict equality of handles.
                assert_ne!(left, right);
                assert_eq!(left_face, right_face);
                assert_eq!(domain.neutral(left), domain.neutral(right));
            },
            | _ => panic!("ret must preserve the semantic value constructor"),
        }
    }
}

/// Lower the identified core fragment into the trusted arena.
///
/// # Specification
/// - requires: a closed, well-typed identity-return core judgement.
/// - ensures: preserves types, lambdas, returns and intuitionistic indices.
/// - panics: a foreign former violates the fixture precondition.
///
/// # Adequacy
/// - hypothesis: L2 — admission of the mapped model identity and refusal when
///   its lambda is asked to synthesize separate checking from synthesis.
/// - witness: `tests::glf::model::kernel`
#[anodized::spec(ensures: |(ty, term)| arena.comp_type(ty).is_some() && arena.computation(term).is_some())]
fn trusted_image(
    core: &CoreArena,
    judgement: &CoreJudgement,
    arena: &mut gandr_kernel_term::TermArena,
) -> (
    gandr_kernel_term::CompTypeId,
    gandr_kernel_term::ComputationId,
)
{
    let mut domains = Vec::new();
    let mut ty = judgement.ty;
    let mut term = judgement.term;
    let (result, index) = loop {
        match (
            core.comp_type(ty).expect("core type"),
            core.computation(term).expect("core term"),
        ) {
            | (&CompType::Arrow { domain, codomain }, &Computation::Lambda(body)) => {
                domains.push(trusted_atom(core_atom(core, domain), arena));
                ty = codomain;
                term = body;
            },
            | (&CompType::Returner(result), &Computation::Return(value)) => {
                let Value::Variable {
                    zone: Zone::Intuitionistic,
                    index,
                } = *core.value(value).expect("core value")
                else {
                    panic!("variable");
                };
                break (trusted_atom(core_atom(core, result), arena), index);
            },
            | _ => panic!("identity-return fragment"),
        }
    };
    let mut ty = arena.comp_type_returner(result);
    let value = arena.value_variable(index);
    let mut term = arena.computation_return(value);
    for domain in domains.into_iter().rev() {
        ty = arena.comp_type_arrow(domain, ty);
        term = arena.computation_lambda(term);
    }
    (ty, term)
}

/// Interpret one parameter in the trusted arena.
///
/// # Specification
/// trivial.
fn trusted_atom(
    atom: Atom,
    arena: &mut gandr_kernel_term::TermArena,
) -> gandr_kernel_term::ValueTypeId
{
    match atom {
        | Atom::Unit => arena.value_type_unit(),
        | Atom::Integer => arena.value_type_base(BaseType::Integer),
        | Atom::String => arena.value_type_base(BaseType::String),
    }
}
