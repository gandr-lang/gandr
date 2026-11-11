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
    let mut built = core.value_constructor(
        ConstantIndex::from(0_usize),
        own,
        ConstructorTag::from(0_usize),
        Vec::new(),
    );
    for &letter in letters.iter().rev() {
        built = core.value_constructor(
            ConstantIndex::from(0_usize),
            own,
            letter.tag(),
            alloc::vec![built],
        );
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
    let mut built = arena.value_constructor(
        ConstantIndex::from(0_usize),
        own,
        ConstructorTag::from(0_usize),
        Vec::new(),
    );
    for &letter in letters.iter().rev() {
        built = arena.value_constructor(
            ConstantIndex::from(0_usize),
            own,
            letter.tag(),
            alloc::vec![built],
        );
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
        let word =
            core.value_constructor(ConstantIndex::from(0_usize), own, Loop.tag(), alloc::vec![
                leaf
            ]);
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
    let word = arena.value_constructor(ConstantIndex::from(0_usize), own, Loop.tag(), alloc::vec![
        leaf
    ]);
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

/// The sort `S`, with `Base` at tag 0 and `Other` at tag 1.
const SORT: usize = 0;
/// The words of one loop at `Base`.
const WORDS: usize = 1;
/// The words of one 2-cell at `here(Base)`.
const CELLS: usize = 2;
/// `ident`, the identity on `S`.
const IDENT: usize = 3;

/// A side of a pair the reflexivity witnesses decide.
#[derive(Clone, Copy, Debug)]
enum Side
{
    /// `here(⟨ident(Base)⟩)`, its point a held call.
    HeldHere,
    /// `here(here(Base))`.
    TwiceHere,
    /// `here(Other)`, off the point.
    OtherHere,
    /// `here(Base)`.
    Here,
    /// The empty word of the loop's words.
    Empty,
    /// The empty word of the 2-cell's words.
    EmptyCell,
    /// `here(ε)`, for `ε` the empty word of the loop's words.
    HereEmpty,
    /// `⟨tr(y. Path[.A = S](Base, y), w, ε)⟩`, for `w` the loop's word
    /// [`MOVED`]: the empty path moved along a word of four letters.
    Moved,
    /// The word [`MOVED`] itself.
    Word,
}

/// The word the [`Side::Moved`] transport runs along, as tags of the loop's
/// words: `loop`, `loop`, its inverse, `loop`.
const MOVED: [usize; 4] = [1, 1, 2, 1];

/// The cells of one loop at `Base`, wrapped `wraps` times.
///
/// # Specification
/// trivial.
fn looped_cells(wraps: gandr_kernel_term::Reflexivities) -> gandr_kernel_term::FreeCells
{
    let base = || -> alloc::boxed::Box<[RuleNode]> {
        [RuleNode::Constructor(ConstructorTag::from(0_usize))].into()
    };
    gandr_kernel_term::FreeCells::new(ConstantIndex::from(SORT), alloc::vec![
        gandr_kernel_term::FreeCell::new(base(), base())
    ])
    .wrapped(wraps)
}

/// `side` in the checker's core arena.
///
/// # Specification
/// trivial.
fn core_side(
    core: &mut CoreArena,
    side: Side,
) -> gandr_core_term::ValueId
{
    let carrier = core.value_type_data(ConstantIndex::from(SORT), Vec::new());
    let at = |core: &mut CoreArena, tag: usize| {
        core.value_constructor(
            ConstantIndex::from(SORT),
            carrier,
            ConstructorTag::from(tag),
            Vec::new(),
        )
    };
    let empty = |core: &mut CoreArena, words: usize| {
        let own = core.value_type_data(ConstantIndex::from(words), Vec::new());
        core.value_constructor(
            ConstantIndex::from(words),
            own,
            ConstructorTag::from(0_usize),
            Vec::new(),
        )
    };
    match side {
        Side::HeldHere => {
            let base = at(core, 0);
            let head = core.value_constant(ConstantIndex::from(IDENT));
            let forced = core.computation_force(head);
            let applied = core.computation_application(forced, base);
            let held = core.value_returned(applied);
            core.value_here(held)
        },
        Side::TwiceHere => {
            let base = at(core, 0);
            let once = core.value_here(base);
            core.value_here(once)
        },
        Side::OtherHere => {
            let other = at(core, 1);
            core.value_here(other)
        },
        Side::Here => {
            let base = at(core, 0);
            core.value_here(base)
        },
        Side::Empty => empty(core, WORDS),
        Side::EmptyCell => empty(core, CELLS),
        Side::HereEmpty => {
            let end = empty(core, WORDS);
            core.value_here(end)
        },
        Side::Moved | Side::Word => {
            let own = core.value_type_data(ConstantIndex::from(WORDS), Vec::new());
            let end = empty(core, WORDS);
            let word = MOVED.iter().rev().fold(end, |rest, &tag| {
                core.value_constructor(
                    ConstantIndex::from(WORDS),
                    own,
                    ConstructorTag::from(tag),
                    alloc::vec![rest],
                )
            });
            if matches!(side, Side::Word) {
                return word;
            }
            let base = at(core, 0);
            let moving = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
            let family = core.value_type_path(carrier, base, moving);
            let moved = core.computation_path_transport(family, word, end);
            core.value_returned(moved)
        },
    }
}

/// Decide `left` against `right` with endpoints held, the loop's words and the
/// 2-cell's words presented and `ident` defined.
///
/// # Specification
/// trivial.
fn decided_sides(
    left: Side,
    right: Side,
) -> (MachineVerdict, Vec<ConversionDecision<TraceNode>>)
{
    let mut core = CoreArena::new();
    let left = core_side(&mut core, left);
    let right = core_side(&mut core, right);
    let occurrence = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let returned = core.computation_return(occurrence);
    let lambda = core.computation_lambda(returned);
    let ident = core.value_thunk(lambda);
    let mut chain = DefinitionChain::new();
    let _height = chain
        .define(
            ConstantIndex::from(IDENT),
            GlobalIndex::from(0_u32),
            Transparency::Manifest,
            &[],
        )
        .expect("the identity admits");
    let Ok(mut chain) = LoweredChain::lower(chain, |_entry| Ok::<_, ConstantIndex>(ident))
    else {
        panic!("the identity lowers");
    };
    chain.admit_data(
        ConstantIndex::from(SORT),
        gandr_kernel_term::ConstructorCount::from(2_usize),
    );
    for (words, wraps) in [(WORDS, 0_usize), (CELLS, 1)] {
        chain.present(
            ConstantIndex::from(words),
            Presented::new(
                Presentation::words(looped_cells(gandr_kernel_term::Reflexivities::from(wraps))),
                [0_usize, 1, 1].map(FieldCount::from).into(),
            )
            .classified(core.value_type_data(ConstantIndex::from(words), Vec::new())),
        );
    }
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root())
        .reading_endpoints(Endpoints::Hold);
    let mut domain = DomainArena::new();
    let left = eval_value(&core, &mut domain, definitions, Fuel::from(64_u32), left)
        .expect("the side evaluates");
    let right = eval_value(&core, &mut domain, definitions, Fuel::from(64_u32), right)
        .expect("the side evaluates");
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

/// `side` in a kernel arena.
///
/// # Specification
/// trivial.
fn kernel_side(
    arena: &mut TermArena,
    side: Side,
) -> gandr_kernel_term::ValueId
{
    let carrier = arena.value_type_data(ConstantIndex::from(SORT), Vec::new());
    let at = |arena: &mut TermArena, tag: usize| {
        arena.value_constructor(
            ConstantIndex::from(SORT),
            carrier,
            ConstructorTag::from(tag),
            Vec::new(),
        )
    };
    let empty = |arena: &mut TermArena, words: usize| {
        let own = arena.value_type_data(ConstantIndex::from(words), Vec::new());
        arena.value_constructor(
            ConstantIndex::from(words),
            own,
            ConstructorTag::from(0_usize),
            Vec::new(),
        )
    };
    match side {
        Side::HeldHere => {
            let base = at(arena, 0);
            let head = arena.value_constant(ConstantIndex::from(IDENT));
            let forced = arena.computation_force(head);
            let applied = arena.computation_application(forced, base);
            let held = arena.value_returned(applied);
            arena.value_here(held)
        },
        Side::TwiceHere => {
            let base = at(arena, 0);
            let once = arena.value_here(base);
            arena.value_here(once)
        },
        Side::OtherHere => {
            let other = at(arena, 1);
            arena.value_here(other)
        },
        Side::Here => {
            let base = at(arena, 0);
            arena.value_here(base)
        },
        Side::Empty => empty(arena, WORDS),
        Side::EmptyCell => empty(arena, CELLS),
        Side::HereEmpty => {
            let end = empty(arena, WORDS);
            arena.value_here(end)
        },
        Side::Moved | Side::Word => {
            let own = arena.value_type_data(ConstantIndex::from(WORDS), Vec::new());
            let end = empty(arena, WORDS);
            let word = MOVED.iter().rev().fold(end, |rest, &tag| {
                arena.value_constructor(
                    ConstantIndex::from(WORDS),
                    own,
                    ConstructorTag::from(tag),
                    alloc::vec![rest],
                )
            });
            if matches!(side, Side::Word) {
                return word;
            }
            let base = at(arena, 0);
            let moving = arena.value_variable(DeBruijnIndex::from(0_u32));
            let family = arena.value_type_path(carrier, base, moving);
            let moved = arena.computation_path_transport(family, word, end);
            arena.value_returned(moved)
        },
    }
}

/// The kernel's replay of `dialogue` for `left` against `right`, over the
/// sort, the loop's words and the 2-cell's words admitted and `ident`
/// unfolding.
///
/// # Specification
/// trivial.
fn replayed_sides(
    left: Side,
    right: Side,
    dialogue: &[ConversionDecision<ReplayNode>],
) -> KernelVerdict
{
    let mut environment = Environment::new();
    let mut staging = environment.stage();
    let kind = staging
        .arena()
        .value_type_universe(GroundSort::Value, Level::zero());
    let staged = staging.data(
        LevelSignature::monomorphic(),
        Vec::new(),
        alloc::vec![alloc::vec![], alloc::vec![]],
        kind,
    );
    let _sort = environment.add_decl(staged).expect("the sort admits");
    for (words, wraps) in [(WORDS, 0_usize), (CELLS, 1)] {
        let mut staging = environment.stage();
        let kind = staging
            .arena()
            .value_type_universe(GroundSort::Value, Level::zero());
        let own = staging
            .arena()
            .value_type_data(ConstantIndex::from(words), Vec::new());
        let staged = staging
            .data(
                LevelSignature::monomorphic(),
                Vec::new(),
                alloc::vec![alloc::vec![], alloc::vec![own], alloc::vec![own]],
                kind,
            )
            .presented(Presentation::words(looped_cells(
                gandr_kernel_term::Reflexivities::from(wraps),
            )));
        let _words = environment.add_decl(staged).expect("the words admit");
    }
    let mut arena = environment.arena().clone();
    let occurrence = arena.value_variable(DeBruijnIndex::from(0_u32));
    let returned = arena.computation_return(occurrence);
    let lambda = arena.computation_lambda(returned);
    let ident = arena.value_thunk(lambda);
    let left = kernel_side(&mut arena, left);
    let right = kernel_side(&mut arena, right);
    let unfoldings = Unfoldings::new(alloc::vec![
        Unfoldable::Opaque,
        Unfoldable::Opaque,
        Unfoldable::Opaque,
        Unfoldable::Body(ident),
    ])
    .presenting(Presentations::of(environment.entries()));
    replay(
        &mut arena,
        &unfoldings,
        ReplaySides::Values(left, right),
        EngineClaim::Convertible,
        dialogue.iter().copied(),
        ReplayBudget::DEFAULT,
    )
}

/// The dialogue the evaluator recorded, as the kernel names its nodes.
///
/// # Specification
/// trivial.
fn replay_nodes(decisions: &[ConversionDecision<TraceNode>])
-> Vec<ConversionDecision<ReplayNode>>
{
    decisions
        .iter()
        .map(|decision| {
            decision.map(|node: TraceNode| match node {
                TraceNode::Constant(constant) => ReplayNode::Constant(constant),
                TraceNode::Value(_) | TraceNode::Computation(_) => ReplayNode::Other,
            })
        })
        .collect()
}

#[test]
fn a_reflexivity_at_a_looped_point_presents_as_its_empty_word_6477()
{
    // #6477: `here(p)` at the point a type of words loops at, and that
    // type's empty word, spell one path. Before the fix the evaluator planned
    // a reflexivity and an empty word apart, and the kernel's table did too.
    // A reflexivity on either side of the pair reads so.
    for (left, right, reading) in [
        (
            Side::HeldHere,
            Side::Empty,
            "a reflexivity at the point a held call returns is the loop's empty word",
        ),
        (
            Side::Empty,
            Side::HeldHere,
            "the loop's empty word is a reflexivity at the point a held call returns",
        ),
        (
            Side::TwiceHere,
            Side::EmptyCell,
            "the reflexivity of the point's reflexivity is the 2-cell's empty word",
        ),
    ] {
        let (verdict, decisions) = decided_sides(left, right);
        assert_eq!(
            verdict,
            MachineVerdict::Convertible,
            "{reading}: {decisions:?}"
        );
        assert_eq!(
            replayed_sides(left, right, &replay_nodes(&decisions)),
            KernelVerdict::Convertible,
            "{reading}, and the kernel replays the dialogue: {decisions:?}"
        );
    }
    assert_ne!(
        decided_sides(Side::OtherHere, Side::Empty).0,
        MachineVerdict::Convertible,
        "a reflexivity off the point is no empty word"
    );
}

/// #6741: at a point with a loop and a 2-cell, a reflexivity at the loop's
/// empty word is the 2-cell's empty word, as the reflexivity of the point's
/// reflexivity is.
#[test]
fn a_reflexivity_at_the_loops_empty_word_presents_as_the_cells_empty_word_6741()
{
    for (left, right) in [
        (Side::HereEmpty, Side::EmptyCell),
        (Side::EmptyCell, Side::HereEmpty),
    ] {
        let (verdict, decisions) = decided_sides(left, right);
        assert_eq!(
            verdict,
            MachineVerdict::Convertible,
            "{left:?} against {right:?}: {decisions:?}"
        );
        assert_eq!(
            replayed_sides(left, right, &replay_nodes(&decisions)),
            KernelVerdict::Convertible,
            "{left:?} against {right:?}, and the kernel replays the dialogue: {decisions:?}"
        );
    }
}

#[test]
fn a_dialogue_recorded_before_the_reading_replays_unchanged_6477()
{
    // The dialogues the evaluator recorded before #6477 for two reflexivities
    // at the looped point, read off its trace log: the held call's point
    // decomposed and unfolded, and two equal reflexivities shared. The kernel
    // replays each one, and the evaluator still records it, because two
    // reflexivities keep the rule that compares their points.
    let shared = ConversionDecision::ComparedShared {
        left: ReplayNode::Other,
        right: ReplayNode::Other,
    };
    let ident = ReplayNode::Constant(ConstantIndex::from(IDENT));
    for (left, right, dialogue) in [
        (Side::HeldHere, Side::Here, alloc::vec![
            ConversionDecision::Decompose,
            ConversionDecision::Unfold { constant: ident },
            ConversionDecision::ReduceLeft { redex: ident },
            shared,
        ]),
        (Side::TwiceHere, Side::TwiceHere, alloc::vec![shared]),
        (Side::HeldHere, Side::HeldHere, alloc::vec![shared]),
        (Side::Here, Side::Here, alloc::vec![shared]),
    ] {
        assert_eq!(
            replayed_sides(left, right, &dialogue),
            KernelVerdict::Convertible,
            "{left:?} against {right:?} replays as it did before the reading"
        );
        let (verdict, decisions) = decided_sides(left, right);
        assert_eq!(
            (verdict, replay_nodes(&decisions)),
            (MachineVerdict::Convertible, dialogue),
            "{left:?} against {right:?} records the dialogue it recorded before the reading"
        );
    }
}

#[test]
fn a_dialogue_an_older_build_records_for_a_moved_word_replays_unchanged()
{
    // The dialogue the evaluator on `landing` records for the empty path moved
    // along `loop ∷ loop ∷ back(loop) ∷ loop` against that word, read off its
    // trace log: the two sides shared once each is evaluated, so the move
    // along the word records nothing. The move along the whole word records
    // nothing either: the kernel replays the older dialogue, and the evaluator
    // still records it.
    let shared = ConversionDecision::ComparedShared {
        left: ReplayNode::Other,
        right: ReplayNode::Other,
    };
    for (left, right) in [
        (Side::Moved, Side::Word),
        (Side::Word, Side::Moved),
        (Side::Moved, Side::Moved),
    ] {
        let dialogue = alloc::vec![shared];
        assert_eq!(
            replayed_sides(left, right, &dialogue),
            KernelVerdict::Convertible,
            "{left:?} against {right:?} replays as the older build recorded it"
        );
        let (verdict, decisions) = decided_sides(left, right);
        assert_eq!(
            (verdict, replay_nodes(&decisions)),
            (MachineVerdict::Convertible, dialogue),
            "{left:?} against {right:?} records the dialogue the older build recorded"
        );
    }
}
