use alloc::vec;
use alloc::vec::Vec;

use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::DefinitionalEnvironment;
use gandr_core_term::Transparency;
use gandr_core_term::ValueId;
use gandr_core_term::Zone;
use gandr_kernel_check_memo::NullMemo;
use gandr_kernel_conversion_trace::TraceLog;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorCount;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FieldCount;
use gandr_kernel_term::FreeCell;
use gandr_kernel_term::FreeCells;
use gandr_kernel_term::GlobalIndex;
use gandr_kernel_term::Presentation;
use gandr_kernel_term::RuleNode;

use crate::arena::DomainArena;
use crate::eval::Definitions;
use crate::eval::Fuel;
use crate::eval::LoweredChain;
use crate::eval::eval_computation;
use crate::machine::MachineSettings;
use crate::machine::MachineVerdict;
use crate::machine::Problem;
use crate::machine::TraceNode;
use crate::machine::decide;
use crate::presented::Presented;

/// The sort `S` of one point, `Base`.
const SORT: usize = 0;
/// The words of one loop at `Base`.
const WORDS: usize = 1;
/// `loop`, whose body is the word of its letter.
const LOOP: usize = 2;
/// `flip`, the case over `S` whose loop arm answers the inverse letter.
const FLIP: usize = 3;
/// `first`, a case over its first of two arguments whose loop arm answers
/// the loop by its name.
const FIRST: usize = 4;
/// `second`, the same over its second of two arguments.
const SECOND: usize = 5;
/// `zero`, a call whose body returns the empty word.
const ZERO: usize = 6;

/// The terms the witnesses build on, in the checker's arena.
struct Circle
{
    /// `S`.
    carrier: gandr_core_term::ValueTypeId,
    /// `Base`.
    point: ValueId,
    /// The empty word.
    empty: ValueId,
    /// The word of the loop's letter.
    letter: ValueId,
    /// The word of its inverse.
    inverse: ValueId,
    /// The constant `loop`.
    named: ValueId,
    /// `flip`'s body: `thunk (λx. case x { Base ⇒ return Base; loop ⇒
    /// return back(loop) })`.
    flip: ValueId,
    /// `first`'s body: `thunk (λa. λb. case a { Base ⇒ return b; loop ⇒
    /// return loop })`.
    first: ValueId,
    /// `second`'s body: `thunk (λb. λa. case a { Base ⇒ return b; loop ⇒
    /// return loop })`.
    second: ValueId,
    /// `zero`'s body: `thunk (return ε)`.
    zero: ValueId,
}

/// The circle's terms.
///
/// # Specification
/// trivial.
fn circle(core: &mut CoreArena) -> Circle
{
    let carrier = core.value_type_data(ConstantIndex::from(SORT), Vec::new());
    let own = core.value_type_data(ConstantIndex::from(WORDS), Vec::new());
    let point = core.value_constructor(carrier, ConstructorTag::from(0_usize), Vec::new());
    let empty = core.value_constructor(own, ConstructorTag::from(0_usize), Vec::new());
    let letter = core.value_constructor(own, ConstructorTag::from(1_usize), vec![empty]);
    let inverse = core.value_constructor(own, ConstructorTag::from(2_usize), vec![empty]);
    let named = core.value_constant(ConstantIndex::from(LOOP));
    let kept = core.comp_type_returner(carrier);
    let at_point = core.computation_return(point);
    let at_loop = core.computation_return(inverse);
    let scrutinee = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let case = core.computation_data_case(scrutinee, kept, vec![at_point, at_loop]);
    let lambda = core.computation_lambda(case);
    let flip = core.value_thunk(lambda);
    // Over two arguments, the case over the one at `over`, the other
    // returned at the point and the loop's name its loop arm.
    let binary = |core: &mut CoreArena, over: u32, other: u32| {
        let scrutinee = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(over));
        let kept_value = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(other));
        let at_point = core.computation_return(kept_value);
        let at_loop = core.computation_return(named);
        let case = core.computation_data_case(scrutinee, kept, vec![at_point, at_loop]);
        let inner = core.computation_lambda(case);
        let outer = core.computation_lambda(inner);
        core.value_thunk(outer)
    };
    let first = binary(core, 1, 0);
    let second = binary(core, 0, 1);
    let returned = core.computation_return(empty);
    let zero = core.value_thunk(returned);
    Circle {
        carrier,
        point,
        empty,
        letter,
        inverse,
        named,
        flip,
        first,
        second,
        zero,
    }
}

/// Whether a chain records the sort's constructor count.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Count
{
    /// The count is recorded.
    Recorded,
    /// It is not.
    Missing,
}

/// The chain the witnesses run over: the words presented, `loop` and
/// `flip` defined, and the sort's constructor count as `count` says.
///
/// # Specification
/// trivial.
fn chain(
    circle: &Circle,
    count: Count,
) -> LoweredChain
{
    let base = || -> alloc::boxed::Box<[RuleNode]> {
        [RuleNode::Constructor(ConstructorTag::from(0_usize))].into()
    };
    let cells = FreeCells::new(ConstantIndex::from(SORT), vec![FreeCell::new(
        base(),
        base(),
    )]);
    let mut chain = LoweredChain::new();
    chain.present(
        ConstantIndex::from(WORDS),
        Presented::new(
            Presentation::words(cells),
            [0_usize, 1, 1].map(FieldCount::from).into(),
        ),
    );
    if count == Count::Recorded {
        chain.admit_data(ConstantIndex::from(SORT), ConstructorCount::from(1_usize));
    }
    for (constant, global, body) in [
        (ConstantIndex::from(LOOP), 0_u32, circle.letter),
        (ConstantIndex::from(FLIP), 1_u32, circle.flip),
        (ConstantIndex::from(FIRST), 2_u32, circle.first),
        (ConstantIndex::from(SECOND), 3_u32, circle.second),
        (ConstantIndex::from(ZERO), 4_u32, circle.zero),
    ] {
        let _height = chain
            .define(
                constant,
                GlobalIndex::from(global),
                Transparency::Manifest,
                &[],
                body,
            )
            .expect("the definition admits");
    }
    chain
}

/// Decide `left` against `right` over `chain`, or `None` when `left` does
/// not evaluate.
///
/// # Specification
/// trivial.
fn decided(
    core: &CoreArena,
    chain: &LoweredChain,
    (left, right): (ComputationId, ComputationId),
) -> Option<MachineVerdict>
{
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(chain, &environment, environment.root());
    let mut domain = DomainArena::new();
    let fuel = Fuel::from(512_u32);
    let left = eval_computation(core, &mut domain, definitions, fuel, left).ok()?;
    let right = eval_computation(core, &mut domain, definitions, fuel, right)
        .expect("the expected side evaluates");
    let mut log = TraceLog::<TraceNode>::new();
    let report = decide::<_, NullMemo>(
        core,
        &mut domain,
        definitions,
        MachineSettings::default(),
        Problem::computations(left, right),
        &mut log,
    )
    .expect("the machine answers");
    Some(report.verdict())
}

#[test]
fn transport_along_the_loop_moves_the_endpoint()
{
    let mut core = CoreArena::new();
    let circle = circle(&mut core);
    let chain = chain(&circle, Count::Recorded);
    let moving = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let family = core.value_type_path(circle.carrier, circle.point, moving);
    let moved = core.computation_return(circle.letter);
    let stayed = core.computation_return(circle.empty);
    // Along the word and along the constant naming it alike.
    for path in [circle.letter, circle.named] {
        let transported = core.computation_path_transport(family, path, circle.empty);
        assert_eq!(
            decided(&core, &chain, (transported, moved)),
            Some(MachineVerdict::Convertible),
            "reflexivity at the point carried along the loop is the loop"
        );
        assert_eq!(
            decided(&core, &chain, (transported, stayed)),
            Some(MachineVerdict::NotConvertible),
            "and not reflexivity"
        );
    }
}

#[test]
fn the_loop_conjugates_a_loop_to_itself()
{
    let mut core = CoreArena::new();
    let circle = circle(&mut core);
    let chain = chain(&circle, Count::Recorded);
    let moving = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let family = core.value_type_path(circle.carrier, moving, moving);
    for operand in [circle.letter, circle.inverse, circle.empty] {
        let transported = core.computation_path_transport(family, circle.named, operand);
        let fixed = core.computation_return(operand);
        assert_eq!(
            decided(&core, &chain, (transported, fixed)),
            Some(MachineVerdict::Convertible),
            "conjugation by the loop fixes every loop at the point"
        );
    }
    let transported = core.computation_path_transport(family, circle.named, circle.letter);
    let moved = core.computation_return(circle.empty);
    assert_eq!(
        decided(&core, &chain, (transported, moved)),
        Some(MachineVerdict::NotConvertible),
        "and moves no loop to another"
    );
}

#[test]
fn cong_along_the_loop_is_the_arm_s_image()
{
    let mut core = CoreArena::new();
    let circle = circle(&mut core);
    let moving = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let flip = core.value_constant(ConstantIndex::from(FLIP));
    let forced = core.computation_force(flip);
    let applied = core.computation_application(forced, moving);
    let through = core.value_returned(applied);
    // `cong(flip, loop)`: reflexivity at `flip(Base)`, carried along the
    // loop in the family of paths from it to `flip(y)`.
    let family = core.value_type_path(circle.carrier, circle.point, through);
    let cong = core.computation_path_transport(family, circle.named, circle.empty);
    let image = core.computation_return(circle.inverse);
    assert_eq!(
        decided(&core, &chain(&circle, Count::Recorded), (cong, image)),
        Some(MachineVerdict::Convertible),
        "the flip's image of the loop is its loop arm's answer, the inverse"
    );
    let looped = core.computation_return(circle.letter);
    assert_eq!(
        decided(&core, &chain(&circle, Count::Recorded), (cong, looped)),
        Some(MachineVerdict::NotConvertible),
        "and not the loop"
    );
    assert_ne!(
        decided(&core, &chain(&circle, Count::Missing), (cong, image)),
        Some(MachineVerdict::Convertible),
        "without the sort's constructor count the arm is not found"
    );
}

#[test]
fn cong_along_the_loop_reads_a_map_of_two_arguments()
{
    let mut core = CoreArena::new();
    let circle = circle(&mut core);
    let chain = chain(&circle, Count::Recorded);
    let moving = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let looped = core.computation_return(circle.letter);
    let inverted = core.computation_return(circle.inverse);
    // `cong(y. first(y, Base), loop)` and `cong(y. second(Base, y), loop)`:
    // the point runs through one argument, the other stays at `Base`.
    for (constant, arguments) in [
        (FIRST, [moving, circle.point]),
        (SECOND, [circle.point, moving]),
    ] {
        let named = core.value_constant(ConstantIndex::from(constant));
        let mut applied = core.computation_force(named);
        for argument in arguments {
            applied = core.computation_application(applied, argument);
        }
        let through = core.value_returned(applied);
        let family = core.value_type_path(circle.carrier, circle.point, through);
        let cong = core.computation_path_transport(family, circle.named, circle.empty);
        assert_eq!(
            decided(&core, &chain, (cong, looped)),
            Some(MachineVerdict::Convertible),
            "the image of the loop is the arm's answer, the loop read by its name"
        );
        assert_eq!(
            decided(&core, &chain, (cong, inverted)),
            Some(MachineVerdict::NotConvertible),
            "and not its inverse"
        );
    }
}

#[test]
fn cong_along_the_loop_reads_both_arguments_of_a_diagonal_464()
{
    let mut core = CoreArena::new();
    let circle = circle(&mut core);
    let chain = chain(&circle, Count::Recorded);
    let own = core.value_type_data(ConstantIndex::from(WORDS), Vec::new());
    let moving = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let twice = core.value_constructor(own, ConstructorTag::from(1_usize), vec![circle.letter]);
    let twice = core.computation_return(twice);
    let looped = core.computation_return(circle.letter);
    // `cong(y. first(y, y), loop)` and `cong(y. second(y, y), loop)`: the
    // loop runs through both arguments, the first route's image then the
    // second's — the arm's `loop` through the argument the case is over,
    // and through the other, the branch at the point returning it, the
    // loop itself.
    for constant in [FIRST, SECOND] {
        let named = core.value_constant(ConstantIndex::from(constant));
        let forced = core.computation_force(named);
        let applied = core.computation_application(forced, moving);
        let applied = core.computation_application(applied, moving);
        let through = core.value_returned(applied);
        let family = core.value_type_path(circle.carrier, circle.point, through);
        let cong = core.computation_path_transport(family, circle.named, circle.empty);
        assert_eq!(
            decided(&core, &chain, (cong, twice)),
            Some(MachineVerdict::Convertible),
            "the diagonal's image of the loop is the loop through each argument in turn"
        );
        assert_eq!(
            decided(&core, &chain, (cong, looped)),
            Some(MachineVerdict::NotConvertible),
            "and not the loop through one argument alone"
        );
    }
}

#[test]
fn cong_along_the_loop_reads_a_call_bound_into_the_next()
{
    let mut core = CoreArena::new();
    let circle = circle(&mut core);
    let chain = chain(&circle, Count::Recorded);
    let flip = core.value_constant(ConstantIndex::from(FLIP));
    let moving = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let forced = core.computation_force(flip);
    let inner = core.computation_application(forced, moving);
    // Under the bind the bound result is the innermost variable.
    let outer = core.computation_application(forced, moving);
    let bound = core.computation_bind(inner, outer);
    let through = core.value_returned(bound);
    // `cong(y. ⟨x ← flip(y); flip(x)⟩, loop)`: the loop through the flip and
    // then the flip again, the inverse of the inverse.
    let family = core.value_type_path(circle.carrier, circle.point, through);
    let cong = core.computation_path_transport(family, circle.named, circle.empty);
    let looped = core.computation_return(circle.letter);
    let inverted = core.computation_return(circle.inverse);
    assert_eq!(
        decided(&core, &chain, (cong, looped)),
        Some(MachineVerdict::Convertible),
        "the image of the loop through a flip bound into a flip is the loop"
    );
    assert_eq!(
        decided(&core, &chain, (cong, inverted)),
        Some(MachineVerdict::NotConvertible),
        "and not its inverse"
    );
}

#[test]
fn a_word_appends_on_its_first_word()
{
    let mut core = CoreArena::new();
    let circle = circle(&mut core);
    let chain = chain(&circle, Count::Recorded);
    let own = core.value_type_data(ConstantIndex::from(WORDS), Vec::new());
    let moving = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let family = core.value_type_path(circle.carrier, circle.point, moving);
    // Under `λq. λp.`: `q` is index 1, `p` index 0.
    let after = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let before = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let binary = |core: &mut CoreArena, body: ComputationId| {
        let inner = core.computation_lambda(body);
        core.computation_lambda(inner)
    };
    // `here(Base) then q` is `q`.
    let unit = core.computation_path_transport(family, after, circle.empty);
    let unit = binary(&mut core, unit);
    let itself = core.computation_return(after);
    let itself = binary(&mut core, itself);
    assert_eq!(
        decided(&core, &chain, (unit, itself)),
        Some(MachineVerdict::Convertible),
        "the empty word moved along a path is the path"
    );
    // `(loop ∷ p) then q` is `loop ∷ (p then q)`.
    let consed = core.value_constructor(own, ConstructorTag::from(1_usize), vec![before]);
    let appended = core.computation_path_transport(family, after, consed);
    let appended = binary(&mut core, appended);
    let rest = core.computation_path_transport(family, after, before);
    let held = core.value_returned(rest);
    let prefixed = core.value_constructor(own, ConstructorTag::from(1_usize), vec![held]);
    let prefixed = core.computation_return(prefixed);
    let prefixed = binary(&mut core, prefixed);
    assert_eq!(
        decided(&core, &chain, (appended, prefixed)),
        Some(MachineVerdict::Convertible),
        "a letter before a path moved along another stays first"
    );
    let inverted = core.value_constructor(own, ConstructorTag::from(2_usize), vec![held]);
    let inverted = core.computation_return(inverted);
    let inverted = binary(&mut core, inverted);
    assert_eq!(
        decided(&core, &chain, (appended, inverted)),
        Some(MachineVerdict::NotConvertible),
        "and is no other letter"
    );
}

#[test]
fn a_composite_over_a_call_to_the_empty_word_is_its_second_word_473()
{
    let mut core = CoreArena::new();
    let circle = circle(&mut core);
    let chain = chain(&circle, Count::Recorded);
    let moving = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let family = core.value_type_path(circle.carrier, circle.point, moving);
    let after = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    // `zero then q` is `q`, `zero` a call that returns the empty word.
    let zero = core.value_constant(ConstantIndex::from(ZERO));
    let forced = core.computation_force(zero);
    let held = core.value_returned(forced);
    let composite = core.computation_path_transport(family, after, held);
    let composite = core.computation_lambda(composite);
    let itself = core.computation_return(after);
    let itself = core.computation_lambda(itself);
    // The checker holds an endpoint's call at its definition, as `spin(Z)`
    // stands in `spin(Z) then spin(a)`.
    let environment = DefinitionalEnvironment::new();
    let definitions = Definitions::new(&chain, &environment, environment.root())
        .reading_endpoints(crate::eval::Endpoints::Hold);
    let mut domain = DomainArena::new();
    let fuel = Fuel::from(512_u32);
    let left = eval_computation(&core, &mut domain, definitions, fuel, composite)
        .expect("the composite evaluates");
    let right = eval_computation(&core, &mut domain, definitions, fuel, itself)
        .expect("the path evaluates");
    let mut log = TraceLog::<TraceNode>::new();
    let report = decide::<_, NullMemo>(
        &core,
        &mut domain,
        definitions,
        MachineSettings::default(),
        Problem::computations(left, right),
        &mut log,
    )
    .expect("the machine answers");
    assert_eq!(
        report.verdict(),
        MachineVerdict::Convertible,
        "a call returning the empty word moved along a path is the path"
    );
}

/// A letter of a word over the one loop.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Letter
{
    /// The loop.
    Loop,
    /// Its inverse.
    Inverse,
}

impl Letter
{
    /// The inverse letter.
    ///
    /// # Specification
    /// trivial.
    const fn inverted(self) -> Self
    {
        match self {
            Self::Loop => Self::Inverse,
            Self::Inverse => Self::Loop,
        }
    }
}

/// How an endpoint of a path family over `S` reads the family's binder.
#[derive(Clone, Copy, Debug)]
enum Endpoint
{
    /// The point, never reading the binder.
    Fixed,
    /// The binder itself.
    Moving,
    /// `⟨flip(y)⟩`, a call on the binder.
    Flipped,
}

/// What an endpoint makes of the word a transport runs along: nothing where
/// it is fixed, the word where it moves, and each letter's image under `flip`
/// — its loop arm, the inverse letter — where it is the call.
///
/// # Specification
/// trivial.
fn imaged(
    endpoint: Endpoint,
    word: &[Letter],
) -> Vec<Letter>
{
    match endpoint {
        Endpoint::Fixed => Vec::new(),
        Endpoint::Moving => word.to_vec(),
        Endpoint::Flipped => word.iter().map(|letter| letter.inverted()).collect(),
    }
}

/// A word a transport reads: the path it runs along, or the operand it moves.
#[derive(Clone, Copy, Debug)]
enum Along
{
    /// The word spelled by its letters.
    Spelled(&'static [Letter]),
    /// The constant `loop`, whose body is the word of the loop's letter.
    Named,
}

/// The word spelled by `letters`, the first letter outermost.
///
/// # Specification
/// trivial.
fn spelled(
    core: &mut CoreArena,
    letters: &[Letter],
) -> ValueId
{
    let own = core.value_type_data(ConstantIndex::from(WORDS), Vec::new());
    letters.iter().rev().fold(
        core.value_constructor(own, ConstructorTag::from(0_usize), Vec::new()),
        |tail, letter| {
            let tag = match *letter {
                Letter::Loop => ConstructorTag::from(1_usize),
                Letter::Inverse => ConstructorTag::from(2_usize),
            };
            core.value_constructor(own, tag, vec![tail])
        },
    )
}

/// `letters` in the free group's normal form: each letter met beside its
/// inverse cancels with it.
///
/// # Specification
/// trivial.
fn reduced(letters: impl IntoIterator<Item = Letter>) -> Vec<Letter>
{
    let mut kept = Vec::new();
    for letter in letters {
        if kept.last() == Some(&letter.inverted()) {
            let _cancelled = kept.pop();
        }
        else {
            kept.push(letter);
        }
    }
    kept
}

/// Transport along a word in `y. Path(S, l(y), r(y))`, each endpoint fixed,
/// the binder or a call on it, is conjugation: `l(w)⁻¹ · v · r(w)`, an
/// endpoint's image of the word as [`imaged`] reads it, and the named `loop`,
/// as path or as operand, reads as its letter. The answer is checked against
/// the word the free group computes, and against that word with one more
/// letter.
#[test]
fn transport_along_a_word_conjugates_by_its_moving_endpoints()
{
    let paths = [
        Along::Spelled(&[]),
        Along::Spelled(&[Letter::Loop]),
        Along::Spelled(&[Letter::Inverse]),
        Along::Spelled(&[Letter::Loop, Letter::Loop]),
        Along::Spelled(&[Letter::Loop, Letter::Inverse]),
        Along::Named,
    ];
    let operands = [
        Along::Spelled(&[]),
        Along::Spelled(&[Letter::Inverse]),
        Along::Named,
    ];
    let families = [
        (Endpoint::Fixed, Endpoint::Moving),
        (Endpoint::Moving, Endpoint::Fixed),
        (Endpoint::Moving, Endpoint::Moving),
        (Endpoint::Fixed, Endpoint::Fixed),
        (Endpoint::Flipped, Endpoint::Fixed),
        (Endpoint::Fixed, Endpoint::Flipped),
        (Endpoint::Flipped, Endpoint::Moving),
        (Endpoint::Moving, Endpoint::Flipped),
        (Endpoint::Flipped, Endpoint::Flipped),
    ];
    for (left, right) in families {
        for path in paths {
            for operand in operands {
                let mut core = CoreArena::new();
                let circle = circle(&mut core);
                let chain = chain(&circle, Count::Recorded);
                let moving = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
                let flip = core.value_constant(ConstantIndex::from(FLIP));
                let forced = core.computation_force(flip);
                let applied = core.computation_application(forced, moving);
                let flipped = core.value_returned(applied);
                let at = |endpoint| match endpoint {
                    Endpoint::Fixed => circle.point,
                    Endpoint::Moving => moving,
                    Endpoint::Flipped => flipped,
                };
                let family = core.value_type_path(circle.carrier, at(left), at(right));
                let mut read = |word| match word {
                    Along::Spelled(letters) => (spelled(&mut core, letters), letters),
                    Along::Named => (circle.named, &[Letter::Loop][..]),
                };
                let (along, word) = read(path);
                let (held, moved) = read(operand);
                let expected = reduced(
                    imaged(left, word)
                        .iter()
                        .rev()
                        .map(|letter| letter.inverted())
                        .chain(moved.iter().copied())
                        .chain(imaged(right, word)),
                );
                let transported = core.computation_path_transport(family, along, held);
                let answer = spelled(&mut core, &expected);
                let answer = core.computation_return(answer);
                let longer = reduced(expected.iter().copied().chain([Letter::Loop]));
                let longer = spelled(&mut core, &longer);
                let longer = core.computation_return(longer);
                assert_eq!(
                    [
                        decided(&core, &chain, (transported, answer)),
                        decided(&core, &chain, (transported, longer)),
                    ],
                    [
                        Some(MachineVerdict::Convertible),
                        Some(MachineVerdict::NotConvertible),
                    ],
                    "{left:?} {right:?} {path:?} {operand:?}"
                );
            }
        }
    }
}
