//! Generated terms for the property witnesses: a program of steps over a
//! stack of values and a stack of computations builds a computation, and a
//! few redexes applied over it make its head reduce.
//!
//! Redexes meet their introductions in place or through a beta, so the
//! eliminations of a generated term read values bound in other scopes, and
//! its variables read binders of its own and binders past it.

use alloc::vec::Vec;

use gandr_kernel_term::Component;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::EquationCount;
use gandr_kernel_term::FixpointEvidence;
use gandr_kernel_term::StagedPosition;
use gandr_kernel_term::Summand;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::ValueId;

/// A generated term's construction: the steps that build its stacks, then
/// the redexes applied over them in turn.
#[derive(Clone, Debug)]
pub struct Program
{
    /// The steps, in order.
    pub steps: Vec<Step>,
    /// The redexes applied after them, the last at the head.
    pub heads: Vec<Head>,
}

/// Programs of up to forty steps and one to three redexes, so that every
/// term they build is a redex.
///
/// # Specification
/// trivial.
pub fn program() -> impl proptest::strategy::Strategy<Value = Program>
{
    use proptest::strategy::Strategy as _;
    (
        proptest::collection::vec(step(), 0 .. 40),
        proptest::collection::vec(head(), 1 .. 4),
    )
        .prop_map(|(steps, heads)| Program { steps, heads })
}

/// One step of a generated term's construction: an operation over a stack of
/// values and a stack of computations, an operand missing from either read as
/// the innermost variable or its return, so that a body built from nothing
/// reads the binder it stands under.
#[derive(Clone, Copy, Debug)]
pub enum Step
{
    /// The variable at this index.
    Variable(u8),
    /// The unit.
    Unit,
    /// The empty list.
    Nil,
    /// A cell, its head below its tail.
    Cons,
    /// A pair, its first component below its second.
    Pair,
    /// An injection of the top value into this summand.
    Inject(u8),
    /// A constructor at this tag over a datatype indexed by the top value;
    /// tag one takes the next value as its field.
    Construct(u8),
    /// A thunk of the top computation.
    Thunk,
    /// A returned endpoint of the top computation.
    Returned,
    /// A return of the top value.
    Return,
    /// A lambda over the top computation.
    Lambda,
    /// The top computation applied to the top value.
    Apply,
    /// The computation below the top one bound into it.
    Bind,
    /// A force of the top value.
    Force,
    /// A case of the top value, its first branch below its second.
    Case,
    /// A dependent split of the top value into the top computation.
    Split,
    /// A list case of the top value, its nil branch below its cell branch.
    ListCase,
    /// A list fold of the top value, its nil branch below its cell branch.
    Fold,
    /// A data case of the top value, its first branch below its second,
    /// under this many index equations.
    DataCase(u8),
    /// A fixpoint over the top computation, its evidence chosen by this.
    Fixpoint(u8),
    /// A projection of this side of the top computation.
    Project(u8),
    /// A lazy pairing, its first side below its second.
    With,
    /// A projection of this component of the top value.
    Select(u8),
    /// An elimination met by its introduction.
    Redex(Head),
}

/// A redex and how it meets its introduction.
#[derive(Clone, Copy, Debug)]
pub struct Head
{
    /// The elimination and introduction.
    pub redex: Redex,
    /// Whether a beta around the redex passes it its introduction, so that
    /// the redex reads it through a cell of another environment.
    pub passed: bool,
}

/// An elimination met by its introduction, built from the stacks' tops, so
/// that a generated term reduces and its bodies read what each step binds.
#[derive(Clone, Copy, Debug)]
pub enum Redex
{
    /// `(λ. c) v`.
    Beta,
    /// `return v to x. c`.
    Let,
    /// `force (thunk c)`.
    Delay,
    /// A case of an injection into this summand.
    Choose(u8),
    /// A split of a pair.
    Unpair,
    /// A list case of a list of this many cells.
    MatchList(u8),
    /// A fold over a list of this many cells.
    FoldList(u8),
    /// A data case of a constructor at this tag, under this many index
    /// equations.
    Match(u8, u8),
    /// A fixpoint over `λ. c`, its evidence chosen by this, applied to a
    /// constructor.
    Recurse(u8),
    /// A projection of this side of a lazy pair.
    Pick(u8),
    /// A projection of this component of a pair.
    Index(u8),
}

/// The redexes a generated term is built with, beta and let most often.
///
/// # Specification
/// trivial.
fn redex() -> impl proptest::strategy::Strategy<Value = Redex>
{
    use alloc::vec;

    use proptest::prelude::Just;
    use proptest::strategy::Strategy as _;
    proptest::prop_oneof![
        4 => Just(Redex::Beta),
        3 => Just(Redex::Let),
        2 => Just(Redex::Delay),
        2 => (0_u8 .. 2).prop_map(Redex::Choose),
        2 => Just(Redex::Unpair),
        2 => (0_u8 .. 2).prop_map(Redex::MatchList),
        2 => (0_u8 .. 4).prop_map(Redex::FoldList),
        2 => (0_u8 .. 2, 0_u8 .. 2).prop_map(|(tag, equations)| Redex::Match(tag, equations)),
        2 => (0_u8 .. 3).prop_map(Redex::Recurse),
        1 => (0_u8 .. 2).prop_map(Redex::Pick),
        1 => (0_u8 .. 2).prop_map(Redex::Index),
    ]
}

/// The redexes a generated term is built with, each introduction met in
/// place or passed through a beta.
///
/// # Specification
/// trivial.
fn head() -> impl proptest::strategy::Strategy<Value = Head>
{
    use proptest::strategy::Strategy as _;
    (redex(), proptest::bool::ANY).prop_map(|(redex, passed)| Head { redex, passed })
}

/// The steps a generated term is built by, binders, applications and returns
/// most often, so that most terms reduce.
///
/// # Specification
/// trivial.
fn step() -> impl proptest::strategy::Strategy<Value = Step>
{
    use alloc::vec;

    use proptest::prelude::Just;
    use proptest::strategy::Strategy as _;
    proptest::prop_oneof![
        6 => (0_u8 .. 4).prop_map(Step::Variable),
        2 => Just(Step::Unit),
        1 => Just(Step::Nil),
        2 => Just(Step::Cons),
        2 => Just(Step::Pair),
        2 => (0_u8 .. 2).prop_map(Step::Inject),
        2 => (0_u8 .. 2).prop_map(Step::Construct),
        3 => Just(Step::Thunk),
        1 => Just(Step::Returned),
        5 => Just(Step::Return),
        5 => Just(Step::Lambda),
        6 => Just(Step::Apply),
        3 => Just(Step::Bind),
        2 => Just(Step::Force),
        2 => Just(Step::Case),
        2 => Just(Step::Split),
        2 => Just(Step::ListCase),
        2 => Just(Step::Fold),
        2 => (0_u8 .. 2).prop_map(Step::DataCase),
        2 => (0_u8 .. 4).prop_map(Step::Fixpoint),
        1 => (0_u8 .. 2).prop_map(Step::Project),
        1 => Just(Step::With),
        1 => (0_u8 .. 2).prop_map(Step::Select),
        30 => head().prop_map(Step::Redex),
    ]
}

/// The top value of `values`, or the innermost variable when there is none.
///
/// # Specification
/// trivial.
fn popped_value(
    arena: &mut TermArena,
    values: &mut Vec<ValueId>,
) -> ValueId
{
    values
        .pop()
        .unwrap_or_else(|| arena.value_variable(DeBruijnIndex::from(0_u32)))
}

/// The top computation of `computations`, or the innermost variable's
/// return when there is none.
///
/// # Specification
/// trivial.
fn popped_computation(
    arena: &mut TermArena,
    computations: &mut Vec<ComputationId>,
) -> ComputationId
{
    computations.pop().unwrap_or_else(|| {
        let innermost = arena.value_variable(DeBruijnIndex::from(0_u32));
        arena.computation_return(innermost)
    })
}

/// The computation `program` builds: the last one on its computation stack,
/// a redex when it applies any.
///
/// # Specification
/// trivial.
pub fn generated(
    arena: &mut TermArena,
    program: &Program,
) -> ComputationId
{
    let unit_type = arena.value_type_unit();
    let motive = arena.comp_type_returner(unit_type);
    let mut values = Vec::new();
    let mut computations = Vec::new();
    for &step in &program.steps {
        match step {
            Step::Variable(index) => {
                values.push(arena.value_variable(DeBruijnIndex::from(u32::from(index))));
            },
            Step::Unit => values.push(arena.value_unit()),
            Step::Nil => values.push(arena.value_list_nil()),
            Step::Cons => {
                let tail = popped_value(arena, &mut values);
                let head = popped_value(arena, &mut values);
                values.push(arena.value_list_cons(head, tail));
            },
            Step::Pair => {
                let second = popped_value(arena, &mut values);
                let first = popped_value(arena, &mut values);
                values.push(arena.value_tuple(&[first, second]));
            },
            Step::Inject(summand) => {
                let body = popped_value(arena, &mut values);
                values.push(arena.value_injection(Summand::from(usize::from(summand)), body));
            },
            Step::Construct(tag) => {
                let constructor =
                    constructed(arena, &mut values, ConstructorTag::from(usize::from(tag)));
                values.push(constructor);
            },
            Step::Thunk => {
                let body = popped_computation(arena, &mut computations);
                values.push(arena.value_thunk(body));
            },
            Step::Returned => {
                let body = popped_computation(arena, &mut computations);
                values.push(arena.value_returned(body));
            },
            Step::Return => {
                let value = popped_value(arena, &mut values);
                computations.push(arena.computation_return(value));
            },
            Step::Lambda => {
                let body = popped_computation(arena, &mut computations);
                computations.push(arena.computation_lambda(body));
            },
            Step::Apply => {
                let argument = popped_value(arena, &mut values);
                let head = popped_computation(arena, &mut computations);
                computations.push(arena.computation_application(head, argument));
            },
            Step::Bind => {
                let body = popped_computation(arena, &mut computations);
                let bound = popped_computation(arena, &mut computations);
                computations.push(arena.computation_bind(bound, body));
            },
            Step::Force => {
                let value = popped_value(arena, &mut values);
                computations.push(arena.computation_force(value));
            },
            Step::Case => {
                let second = popped_computation(arena, &mut computations);
                let first = popped_computation(arena, &mut computations);
                let scrutinee = popped_value(arena, &mut values);
                computations.push(arena.computation_case(scrutinee, &[first, second]));
            },
            Step::Split => {
                let body = popped_computation(arena, &mut computations);
                let scrutinee = popped_value(arena, &mut values);
                computations.push(arena.computation_sigma_split(scrutinee, motive, body));
            },
            Step::ListCase => {
                let on_cons = popped_computation(arena, &mut computations);
                let on_nil = popped_computation(arena, &mut computations);
                let list = popped_value(arena, &mut values);
                computations.push(arena.computation_list_case(list, on_nil, on_cons));
            },
            Step::Fold => {
                let on_cons = popped_computation(arena, &mut computations);
                let on_nil = popped_computation(arena, &mut computations);
                let list = popped_value(arena, &mut values);
                computations
                    .push(arena.computation_list_fold(unit_type, unit_type, list, on_nil, on_cons));
            },
            Step::DataCase(equations) => {
                let second = popped_computation(arena, &mut computations);
                let first = popped_computation(arena, &mut computations);
                let scrutinee = popped_value(arena, &mut values);
                computations.push(arena.computation_data_case_with_equations(
                    scrutinee,
                    motive,
                    Vec::from([first, second]),
                    EquationCount::from(usize::from(equations)),
                ));
            },
            Step::Fixpoint(kind) => {
                let body = popped_computation(arena, &mut computations);
                let evidence = match kind {
                    0 => FixpointEvidence::StructuralDescent,
                    1 => FixpointEvidence::Partial,
                    position => FixpointEvidence::Staged {
                        position: StagedPosition::from(usize::from(position).saturating_sub(2)),
                    },
                };
                computations.push(arena.computation_fixpoint(body, evidence));
            },
            Step::Project(side) => {
                let pair = popped_computation(arena, &mut computations);
                computations
                    .push(arena.computation_project(Component::from(usize::from(side)), pair));
            },
            Step::With => {
                let second = popped_computation(arena, &mut computations);
                let first = popped_computation(arena, &mut computations);
                computations.push(arena.computation_with(&[first, second]));
            },
            Step::Select(component) => {
                let tuple = popped_value(arena, &mut values);
                computations.push(
                    arena.computation_tuple_projection(
                        tuple,
                        Component::from(usize::from(component)),
                    ),
                );
            },
            Step::Redex(redex) => {
                let built = redexed(arena, redex, &mut values, &mut computations);
                computations.push(built);
            },
        }
    }
    for &head in &program.heads {
        let built = redexed(arena, head, &mut values, &mut computations);
        computations.push(built);
    }
    popped_computation(arena, &mut computations)
}

/// A constructor at `tag` over a datatype indexed by the top of `values`; tag
/// one takes the next value as its field.
///
/// # Specification
/// trivial.
fn constructed(
    arena: &mut TermArena,
    values: &mut Vec<ValueId>,
    tag: ConstructorTag,
) -> ValueId
{
    let index = popped_value(arena, values);
    let datatype = arena.value_type_data(ConstantIndex::from(0_usize), Vec::from([index]));
    let fields = if tag == ConstructorTag::from(0_usize) {
        Vec::new()
    }
    else {
        Vec::from([popped_value(arena, values)])
    };
    arena.value_constructor(datatype, tag, fields)
}

/// How many cells a generated list holds.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Cells(u8);

/// A list of `cells` values off the top of `values`, the topmost innermost.
///
/// # Specification
/// trivial.
fn listed(
    arena: &mut TermArena,
    values: &mut Vec<ValueId>,
    cells: Cells,
) -> ValueId
{
    let mut list = arena.value_list_nil();
    for _cell in 0 .. cells.0 {
        let head = popped_value(arena, values);
        list = arena.value_list_cons(head, list);
    }
    list
}

/// `introduction` as a redex's scrutinee: itself, or when `head` passes it,
/// the variable a beta around the redex binds to it, saved in `argument`.
///
/// # Specification
/// trivial.
fn scrutinised(
    arena: &mut TermArena,
    head: Head,
    introduction: ValueId,
    argument: &mut Option<ValueId>,
) -> ValueId
{
    if head.passed {
        *argument = Some(introduction);
        arena.value_variable(DeBruijnIndex::from(0_u32))
    }
    else {
        introduction
    }
}

/// `head`'s redex, built from the tops of `values` and `computations`.
///
/// # Specification
/// trivial.
fn redexed(
    arena: &mut TermArena,
    head: Head,
    values: &mut Vec<ValueId>,
    computations: &mut Vec<ComputationId>,
) -> ComputationId
{
    let unit_type = arena.value_type_unit();
    let motive = arena.comp_type_returner(unit_type);
    let mut argument = None;
    let built = match head.redex {
        Redex::Beta => {
            let value = popped_value(arena, values);
            let body = popped_computation(arena, computations);
            let lambda = arena.computation_lambda(body);
            arena.computation_application(lambda, value)
        },
        Redex::Let => {
            let value = popped_value(arena, values);
            let body = popped_computation(arena, computations);
            let bound = arena.computation_return(value);
            arena.computation_bind(bound, body)
        },
        Redex::Delay => {
            let body = popped_computation(arena, computations);
            let thunk = arena.value_thunk(body);
            let thunk = scrutinised(arena, head, thunk, &mut argument);
            arena.computation_force(thunk)
        },
        Redex::Choose(summand) => {
            let second = popped_computation(arena, computations);
            let first = popped_computation(arena, computations);
            let body = popped_value(arena, values);
            let injection = arena.value_injection(Summand::from(usize::from(summand)), body);
            let injection = scrutinised(arena, head, injection, &mut argument);
            arena.computation_case(injection, &[first, second])
        },
        Redex::Unpair => {
            let body = popped_computation(arena, computations);
            let second = popped_value(arena, values);
            let first = popped_value(arena, values);
            let pair = arena.value_tuple(&[first, second]);
            let pair = scrutinised(arena, head, pair, &mut argument);
            arena.computation_sigma_split(pair, motive, body)
        },
        Redex::MatchList(cells) => {
            let on_cons = popped_computation(arena, computations);
            let on_nil = popped_computation(arena, computations);
            let list = listed(arena, values, Cells(cells));
            let list = scrutinised(arena, head, list, &mut argument);
            arena.computation_list_case(list, on_nil, on_cons)
        },
        Redex::FoldList(cells) => {
            let on_cons = popped_computation(arena, computations);
            let on_nil = popped_computation(arena, computations);
            let list = listed(arena, values, Cells(cells));
            let list = scrutinised(arena, head, list, &mut argument);
            arena.computation_list_fold(unit_type, unit_type, list, on_nil, on_cons)
        },
        Redex::Match(tag, equations) => {
            let second = popped_computation(arena, computations);
            let first = popped_computation(arena, computations);
            let scrutinee = constructed(arena, values, ConstructorTag::from(usize::from(tag)));
            let scrutinee = scrutinised(arena, head, scrutinee, &mut argument);
            arena.computation_data_case_with_equations(
                scrutinee,
                motive,
                Vec::from([first, second]),
                EquationCount::from(usize::from(equations)),
            )
        },
        Redex::Recurse(kind) => {
            let body = popped_computation(arena, computations);
            let lambda = arena.computation_lambda(body);
            let evidence = match kind {
                0 => FixpointEvidence::StructuralDescent,
                1 => FixpointEvidence::Staged {
                    position: StagedPosition::from(0_usize),
                },
                _ => FixpointEvidence::Partial,
            };
            let fixpoint = arena.computation_fixpoint(lambda, evidence);
            let constructor = constructed(arena, values, ConstructorTag::from(1_usize));
            let constructor = scrutinised(arena, head, constructor, &mut argument);
            arena.computation_application(fixpoint, constructor)
        },
        Redex::Pick(side) => {
            let second = popped_computation(arena, computations);
            let first = popped_computation(arena, computations);
            let pair = arena.computation_with(&[first, second]);
            arena.computation_project(Component::from(usize::from(side)), pair)
        },
        Redex::Index(component) => {
            let second = popped_value(arena, values);
            let first = popped_value(arena, values);
            let pair = arena.value_tuple(&[first, second]);
            let pair = scrutinised(arena, head, pair, &mut argument);
            arena.computation_tuple_projection(pair, Component::from(usize::from(component)))
        },
    };
    argument.map_or(built, |argument| {
        let lambda = arena.computation_lambda(built);
        arena.computation_application(lambda, argument)
    })
}
