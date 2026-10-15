use alloc::vec::Vec;

use gandr_core_term::CoreArena;
use gandr_core_term::DefinitionalEnvironment;
use gandr_core_term::Transparency;
use gandr_core_term::Zone;
use gandr_kernel_check_memo::NullMemo;
use gandr_kernel_conversion_trace::ConversionDecision;
use gandr_kernel_conversion_trace::TraceLog;
use gandr_kernel_core::EngineClaim;
use gandr_kernel_core::KernelVerdict;
use gandr_kernel_core::Presentations;
use gandr_kernel_core::ReplayBudget;
use gandr_kernel_core::ReplayNode;
use gandr_kernel_core::ReplaySides;
use gandr_kernel_core::Unfoldable;
use gandr_kernel_core::Unfoldings;
use gandr_kernel_core::replay;
use gandr_kernel_strata::Level;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldCount;
use gandr_kernel_term::GlobalIndex;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::LevelSignature;
use gandr_kernel_term::Presentation;
use gandr_kernel_term::PresentedRule;
use gandr_kernel_term::RuleNode;
use gandr_kernel_term::RuleVariable;
use gandr_kernel_term::TermArena;

use self::Letter::Loop;
use self::Letter::Unloop;
use crate::arena::DomainArena;
use crate::closure::Environment;
use crate::domain::BinderLevel;
use crate::eval::Definitions;
use crate::eval::Fuel;
use crate::eval::LoweredChain;
use crate::eval::eval_comp_within;
use crate::eval::eval_value_within;
use crate::machine::MachineSettings;
use crate::machine::MachineVerdict;
use crate::machine::Problem;
use crate::machine::TraceNode;
use crate::machine::decide;
use crate::presented::Presented;

/// A letter of the circle, and the definition applying it: `looped` at
/// constant 1 applies `loop`, `unlooped` at constant 2 applies `unloop`.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
enum Letter
{
    /// `loop`, at tag 1.
    Loop,
    /// `unloop`, at tag 2.
    Unloop,
}

impl Letter
{
    /// The constructor's tag.
    ///
    /// # Specification
    /// trivial.
    fn tag(self) -> ConstructorTag
    {
        ConstructorTag::from(match self {
            Self::Loop => 1_usize,
            Self::Unloop => 2,
        })
    }

    /// The constant of the definition applying the letter.
    ///
    /// # Specification
    /// trivial.
    fn constant(self) -> ConstantIndex
    {
        ConstantIndex::from(match self {
            Self::Loop => 1_usize,
            Self::Unloop => 2,
        })
    }
}

/// Whether the circle's rules are recorded for a run.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Circle
{
    /// Presented by its two rules.
    Presented,
    /// Free: every word its own term.
    Free,
}

/// What the outer link's left endpoint is.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Start
{
    /// `base`, closed.
    Base,
    /// The path the bind binds, which the link's family then reads.
    Bound,
}

/// The chain `run q <- cong(inner, p); cong(outer, q)` and its path
/// returned, `p` the innermost variable.
///
/// # Specification
/// trivial.
struct Spelled
{
    /// The letter the first link applies.
    inner: Letter,
    /// The letter the second link applies.
    outer: Letter,
    /// The second link's left endpoint.
    start: Start,
}

/// The circle's two rules: `loop(unloop(x)) ~> x` and
/// `unloop(loop(x)) ~> x`.
///
/// # Specification
/// trivial.
fn circle() -> Presentation
{
    let looped = RuleNode::Constructor(Loop.tag());
    let unlooped = RuleNode::Constructor(Unloop.tag());
    let x = RuleNode::Variable(RuleVariable::from(0_u32));
    Presentation::new(alloc::vec![
        PresentedRule::new([looped, unlooped, x].into(), [x].into()),
        PresentedRule::new([unlooped, looped, x].into(), [x].into()),
    ])
}

/// The checker's spelling: the letter's function, the chain, its path
/// returned, and both read as endpoints.
///
/// # Specification
/// trivial.
fn core_terms(
    core: &mut CoreArena,
    spelled: &Spelled,
) -> [gandr_core_term::ComputationId; 2]
{
    let own = core.value_type_data(ConstantIndex::from(0_usize), Vec::new());
    let base = core.value_constructor(own, ConstructorTag::from(0_usize), Vec::new());
    let path = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let inner = core.value_constant(spelled.inner.constant());
    let first = gandr_core_term::identity::cong(core, own, inner, base, path);
    let outer = core.value_constant(spelled.outer.constant());
    let start = match spelled.start {
        Start::Base => base,
        Start::Bound => path,
    };
    let second = gandr_core_term::identity::cong(core, own, outer, start, path);
    let chain = core.computation_bind(first, second);
    [chain, core.computation_return(path)]
}

/// The function applying `letter`, in the checker's arena.
///
/// # Specification
/// trivial.
fn core_letter(
    core: &mut CoreArena,
    letter: Letter,
) -> gandr_core_term::ValueId
{
    let own = core.value_type_data(ConstantIndex::from(0_usize), Vec::new());
    let occurrence = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let word = core.value_constructor(own, letter.tag(), alloc::vec![occurrence]);
    let returned = core.computation_return(word);
    let lambda = core.computation_lambda(returned);
    core.value_thunk(lambda)
}

/// Where the pair stands: the chain against `return p`, or the chain
/// held as an endpoint against `p`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Sides
{
    /// Two computations.
    Computations,
    /// Two values, the chain a returned endpoint.
    Endpoints,
}

/// Decide the chain against its path under a rigid run, `p` a rigid
/// variable at level 0.
///
/// # Specification
/// trivial.
fn decided(
    circle_is: Circle,
    spelled: &Spelled,
    sides: Sides,
) -> (MachineVerdict, Vec<ConversionDecision<TraceNode>>)
{
    let mut core = CoreArena::new();
    let looped = core_letter(&mut core, Loop);
    let unlooped = core_letter(&mut core, Unloop);
    let [chain_term, returned] = core_terms(&mut core, spelled);
    let mut chain = LoweredChain::new();
    for (letter, body, global) in [(Loop, looped, 0_u32), (Unloop, unlooped, 1)] {
        let _height = chain
            .define(
                letter.constant(),
                GlobalIndex::from(global),
                Transparency::Manifest,
                &[],
                body,
            )
            .expect("the letter's function admits");
    }
    if circle_is == Circle::Presented {
        chain.present(
            ConstantIndex::from(0_usize),
            Presented::new(circle(), [0_usize, 1, 1].map(FieldCount::from).into()),
        );
    }
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root()).rigid();
    let mut domain = DomainArena::new();
    let path = super::variable(&mut domain, BinderLevel::from(0_u32)).expect("a variable");
    let mut bound = Environment::new();
    bound.extend(Zone::Intuitionistic, path);
    let fuel = Fuel::from(256_u32);
    let problem = match sides {
        Sides::Computations => {
            let (left, _) = eval_comp_within(
                &core,
                &mut domain,
                definitions,
                fuel,
                chain_term,
                bound.clone(),
            )
            .expect("the chain evaluates");
            let (right, _) =
                eval_comp_within(&core, &mut domain, definitions, fuel, returned, bound)
                    .expect("the return evaluates");
            Problem::computations(left, right)
        },
        Sides::Endpoints => {
            let held = core.value_returned(chain_term);
            let (left, _) = eval_value_within(&core, &mut domain, definitions, fuel, held, bound)
                .expect("the endpoint evaluates");
            Problem::values(left, path)
        },
    };
    let mut log = TraceLog::new();
    let report = decide::<_, NullMemo>(
        &core,
        &mut domain,
        definitions,
        MachineSettings::default(),
        problem.under(BinderLevel::from(1_u32)),
        &mut log,
    )
    .expect("the machine answers");
    (report.verdict(), log.decisions().copied().collect())
}

/// Replay `decisions` over the kernel's spelling of the same pair, the
/// circle presented and both functions unfoldable.
///
/// # Specification
/// trivial.
fn replayed(
    spelled: &Spelled,
    sides: Sides,
    decisions: &[ConversionDecision<TraceNode>],
) -> KernelVerdict
{
    let mut environment = gandr_kernel_core::Environment::new();
    let mut staging = environment.stage();
    let kind = staging
        .arena()
        .value_type_universe(GroundSort::Value, Level::zero());
    let own = staging
        .arena()
        .value_type_data(ConstantIndex::from(0_usize), Vec::new());
    let staged = staging
        .data(
            LevelSignature::monomorphic(),
            Vec::new(),
            alloc::vec![alloc::vec![], alloc::vec![own], alloc::vec![own]],
            kind,
        )
        .presented(circle());
    let _circle = environment.add_decl(staged).expect("the circle admits");
    let mut arena = environment.arena().clone();
    let own = arena.value_type_data(ConstantIndex::from(0_usize), Vec::new());
    let letter = |arena: &mut TermArena, letter: Letter| {
        let occurrence = arena.value_variable(DeBruijnIndex::from(0_u32));
        let word = arena.value_constructor(own, letter.tag(), alloc::vec![occurrence]);
        let returned = arena.computation_return(word);
        let lambda = arena.computation_lambda(returned);
        arena.value_thunk(lambda)
    };
    let looped = letter(&mut arena, Loop);
    let unlooped = letter(&mut arena, Unloop);
    let base = arena.value_constructor(own, ConstructorTag::from(0_usize), Vec::new());
    let path = arena.value_variable(DeBruijnIndex::from(0_u32));
    let cong = |arena: &mut TermArena, applied: Letter, start| {
        let function = arena.value_constant(applied.constant());
        let forced = arena.computation_force(function);
        let moving = arena.value_variable(DeBruijnIndex::from(0_u32));
        let application = arena.computation_application(forced, moving);
        let image = arena.value_returned(application);
        let lifted = match start {
            Start::Base => base,
            Start::Bound => arena.value_variable(DeBruijnIndex::from(1_u32)),
        };
        let motive = arena.value_type_path(own, lifted, image);
        let point = match start {
            Start::Base => base,
            Start::Bound => path,
        };
        let reflexivity = arena.value_here(point);
        arena.computation_path_transport(motive, path, reflexivity)
    };
    let first = cong(&mut arena, spelled.inner, Start::Base);
    let second = cong(&mut arena, spelled.outer, spelled.start);
    let chain = arena.computation_bind(first, second);
    let sides = match sides {
        Sides::Computations => {
            let returned = arena.computation_return(path);
            ReplaySides::Computations(chain, returned)
        },
        Sides::Endpoints => ReplaySides::Values(arena.value_returned(chain), path),
    };
    let unfoldings = Unfoldings::new(alloc::vec![
        Unfoldable::Opaque,
        Unfoldable::Body(looped),
        Unfoldable::Body(unlooped)
    ])
    .presenting(Presentations::of(environment.entries()));
    replay(
        &mut arena,
        &unfoldings,
        sides,
        EngineClaim::Convertible,
        decisions.iter().map(|decision| {
            decision.map(|node: TraceNode| match node {
                TraceNode::Constant(constant) => ReplayNode::Constant(constant),
                TraceNode::Value(_) | TraceNode::Computation(_) => ReplayNode::Other,
            })
        }),
        ReplayBudget::DEFAULT,
    )
}

#[test]
fn a_cong_chain_composing_to_the_identity_is_its_path()
{
    let identity = Spelled {
        inner: Unloop,
        outer: Loop,
        start: Start::Base,
    };
    for sides in [Sides::Computations, Sides::Endpoints] {
        let (verdict, decisions) = decided(Circle::Presented, &identity, sides);
        assert_eq!(
            verdict,
            MachineVerdict::Convertible,
            "`run q <- cong(unlooped, p); cong(looped, q)` is `p` at {sides:?}: {decisions:?}"
        );
        assert_eq!(
            replayed(&identity, sides, &decisions),
            KernelVerdict::Convertible,
            "the kernel fuses the same chain at {sides:?}: {decisions:?}"
        );
    }
    let twice = Spelled {
        inner: Loop,
        outer: Loop,
        start: Start::Base,
    };
    assert_ne!(
        decided(Circle::Presented, &twice, Sides::Computations).0,
        MachineVerdict::Convertible,
        "a chain composing to `looped ∘ looped` is not its path"
    );
    assert_ne!(
        decided(Circle::Free, &identity, Sides::Computations).0,
        MachineVerdict::Convertible,
        "over a free circle `loop(unloop(y))` is not `y`, so the chain stays a chain"
    );
    let reading = Spelled {
        inner: Unloop,
        outer: Loop,
        start: Start::Bound,
    };
    assert_ne!(
        decided(Circle::Presented, &reading, Sides::Computations).0,
        MachineVerdict::Convertible,
        "a link whose family reads the path its bind binds is no link"
    );
}
