use alloc::vec::Vec;

use gandr_core_term::CoreArena;
use gandr_core_term::DefinitionChain;
use gandr_core_term::DefinitionalEnvironment;
use gandr_core_term::Transparency;
use gandr_core_term::Zone;
use gandr_kernel_check_memo::NullMemo;
use gandr_kernel_conversion_trace::ConversionDecision;
use gandr_kernel_conversion_trace::TraceLog;
use gandr_kernel_core::EngineClaim;
use gandr_kernel_core::Environment;
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
use super::Presented;
use crate::arena::DomainArena;
use crate::eval::Definitions;
use crate::eval::Endpoints;
use crate::eval::Fuel;
use crate::eval::LoweredChain;
use crate::eval::eval_value;
use crate::machine::MachineSettings;
use crate::machine::MachineVerdict;
use crate::machine::Problem;
use crate::machine::TraceNode;
use crate::machine::decide;

/// A letter of a circle word over `base`, which stands at tag 0.
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
}

/// The circle's two rules: `loop(unloop(x)) ~> x` and
/// `unloop(loop(x)) ~> x`.
///
/// # Specification
/// trivial.
fn circle() -> Presentation
{
    let looped = RuleNode::Constructor(Letter::Loop.tag());
    let unlooped = RuleNode::Constructor(Letter::Unloop.tag());
    let x = RuleNode::Variable(RuleVariable::from(0_u32));
    Presentation::new(alloc::vec![
        PresentedRule::new([looped, unlooped, x].into(), [x].into()),
        PresentedRule::new([unlooped, looped, x].into(), [x].into()),
    ])
}

/// The circle word spelled by `letters` over `base`, outermost first, in
/// the checker's core arena.
///
/// # Specification
/// trivial.
fn core_word(
    core: &mut CoreArena,
    letters: &[Letter],
) -> gandr_core_term::ValueId
{
    let own = core.value_type_data(ConstantIndex::from(0_usize), Vec::new());
    let mut built = core.value_constructor(own, ConstructorTag::from(0_usize), Vec::new());
    for &letter in letters.iter().rev() {
        built = core.value_constructor(own, letter.tag(), alloc::vec![built]);
    }
    built
}

/// The same word in a kernel arena.
///
/// # Specification
/// trivial.
fn kernel_word(
    arena: &mut TermArena,
    letters: &[Letter],
) -> gandr_kernel_term::ValueId
{
    let own = arena.value_type_data(ConstantIndex::from(0_usize), Vec::new());
    let mut built = arena.value_constructor(own, ConstructorTag::from(0_usize), Vec::new());
    for &letter in letters.iter().rev() {
        built = arena.value_constructor(own, letter.tag(), alloc::vec![built]);
    }
    built
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

/// Decide `left` against `right` over the circle.
///
/// # Specification
/// trivial.
fn decided(
    circle_is: Circle,
    left: &[Letter],
    right: &[Letter],
) -> (MachineVerdict, Vec<ConversionDecision<TraceNode>>)
{
    let mut core = CoreArena::new();
    let left = core_word(&mut core, left);
    let right = core_word(&mut core, right);
    let mut chain = LoweredChain::new();
    if circle_is == Circle::Presented {
        chain.present(
            ConstantIndex::from(0_usize),
            Presented::new(circle(), [0_usize, 1, 1].map(FieldCount::from).into()),
        );
    }
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root());
    let mut domain = DomainArena::new();
    let left = eval_value(&core, &mut domain, definitions, Fuel::from(64_u32), left)
        .expect("the word evaluates");
    let right = eval_value(&core, &mut domain, definitions, Fuel::from(64_u32), right)
        .expect("the word evaluates");
    let mut log = TraceLog::new();
    let report = decide::<_, NullMemo>(
        &core,
        &mut domain,
        definitions,
        MachineSettings::default(),
        Problem::values(left, right),
        &mut log,
    )
    .expect("the machine answers");
    (report.verdict(), log.decisions().copied().collect())
}

#[test]
fn a_circle_word_reads_as_its_reduced_word()
{
    let (verdict, decisions) = decided(Circle::Presented, &[Loop, Unloop, Loop], &[Loop]);
    assert_eq!(
        verdict,
        MachineVerdict::Convertible,
        "`loop(unloop(loop(base)))` is `loop(base)` under the circle's rules"
    );
    let mut environment = Environment::new();
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
    let left = kernel_word(&mut arena, &[Loop, Unloop, Loop]);
    let right = kernel_word(&mut arena, &[Loop]);
    let unfoldings =
        Unfoldings::new(Vec::new()).presenting(Presentations::of(environment.entries()));
    let replayed = replay(
        &mut arena,
        &unfoldings,
        ReplaySides::Values(left, right),
        EngineClaim::Convertible,
        decisions.iter().map(|decision| {
            decision.map(|node: TraceNode| match node {
                TraceNode::Constant(constant) => ReplayNode::Constant(constant),
                TraceNode::Value(_) | TraceNode::Computation(_) => ReplayNode::Other,
            })
        }),
        ReplayBudget::DEFAULT,
    );
    assert_eq!(
        replayed,
        KernelVerdict::Convertible,
        "the kernel replays the derivation over the same normal forms"
    );
    assert_eq!(
        decided(
            Circle::Presented,
            &[Unloop, Loop, Unloop, Unloop, Loop, Loop],
            &[]
        )
        .0,
        MachineVerdict::Convertible,
        "nested inverse pairs cancel down to `base`"
    );
    assert_eq!(
        decided(Circle::Presented, &[Loop], &[]).0,
        MachineVerdict::NotConvertible,
        "a reduced word other than `base` stays apart from it"
    );
    assert_eq!(
        decided(Circle::Free, &[Loop, Unloop, Loop], &[Loop]).0,
        MachineVerdict::NotConvertible,
        "without the rules the two words are two terms"
    );
}

#[test]
fn a_held_call_under_a_presented_constructor_reads_as_what_it_returns()
{
    // `loop(⟨ident(unloop(base))⟩)` against `base`, `ident` the identity
    // at constant 1 and endpoints held. No decision names the leaf under
    // `loop`, so the normal form runs it to `unloop(base)` and the word
    // cancels; the kernel reads the same leaf by its own evaluator. Over a
    // free circle nothing cancels.
    let decided = |circle_is: Circle| {
        let mut core = CoreArena::new();
        let own = core.value_type_data(ConstantIndex::from(0_usize), Vec::new());
        let back = core_word(&mut core, &[Unloop]);
        let occurrence = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
        let returned = core.computation_return(occurrence);
        let lambda = core.computation_lambda(returned);
        let ident = core.value_thunk(lambda);
        let head = core.value_constant(ConstantIndex::from(1_usize));
        let forced = core.computation_force(head);
        let applied = core.computation_application(forced, back);
        let leaf = core.value_returned(applied);
        let word = core.value_constructor(own, Loop.tag(), alloc::vec![leaf]);
        let base = core_word(&mut core, &[]);
        let mut chain = DefinitionChain::new();
        let _height = chain
            .define(
                ConstantIndex::from(1_usize),
                GlobalIndex::from(0_u32),
                Transparency::Manifest,
                &[],
            )
            .expect("the identity admits");
        let Ok(mut chain) = LoweredChain::lower(chain, |_entry| Ok::<_, ConstantIndex>(ident))
        else {
            panic!("the identity lowers");
        };
        if circle_is == Circle::Presented {
            chain.present(
                ConstantIndex::from(0_usize),
                Presented::new(circle(), [0_usize, 1, 1].map(FieldCount::from).into()),
            );
        }
        let environment = DefinitionalEnvironment::new();
        let definitions = Definitions::new(&chain, &environment, environment.root())
            .reading_endpoints(Endpoints::Hold);
        let mut domain = DomainArena::new();
        let left = eval_value(&core, &mut domain, definitions, Fuel::from(64_u32), word)
            .expect("the word evaluates");
        let right = eval_value(&core, &mut domain, definitions, Fuel::from(64_u32), base)
            .expect("the word evaluates");
        let mut log = TraceLog::new();
        let report = decide::<_, NullMemo>(
            &core,
            &mut domain,
            definitions,
            MachineSettings::default(),
            Problem::values(left, right),
            &mut log,
        )
        .expect("the machine answers");
        (
            report.verdict(),
            log.decisions().copied().collect::<Vec<_>>(),
        )
    };
    let (verdict, decisions) = decided(Circle::Presented);
    assert_eq!(verdict, MachineVerdict::Convertible, "{decisions:?}");
    let mut environment = Environment::new();
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
    let occurrence = arena.value_variable(DeBruijnIndex::from(0_u32));
    let returned = arena.computation_return(occurrence);
    let lambda = arena.computation_lambda(returned);
    let ident = arena.value_thunk(lambda);
    let back = kernel_word(&mut arena, &[Unloop]);
    let head = arena.value_constant(ConstantIndex::from(1_usize));
    let forced = arena.computation_force(head);
    let applied = arena.computation_application(forced, back);
    let leaf = arena.value_returned(applied);
    let own = arena.value_type_data(ConstantIndex::from(0_usize), Vec::new());
    let word = arena.value_constructor(own, Loop.tag(), alloc::vec![leaf]);
    let base = kernel_word(&mut arena, &[]);
    let unfoldings = Unfoldings::new(alloc::vec![Unfoldable::Opaque, Unfoldable::Body(ident)])
        .presenting(Presentations::of(environment.entries()));
    let replayed = replay(
        &mut arena,
        &unfoldings,
        ReplaySides::Values(word, base),
        EngineClaim::Convertible,
        decisions.iter().map(|decision| {
            decision.map(|node: TraceNode| match node {
                TraceNode::Constant(constant) => ReplayNode::Constant(constant),
                TraceNode::Value(_) | TraceNode::Computation(_) => ReplayNode::Other,
            })
        }),
        ReplayBudget::DEFAULT,
    );
    assert_eq!(
        replayed,
        KernelVerdict::Convertible,
        "the kernel reads the leaf and replays the derivation: {decisions:?}"
    );
    assert_ne!(
        decided(Circle::Free).0,
        MachineVerdict::Convertible,
        "over a free circle `loop(unloop(base))` is not `base`"
    );
}
