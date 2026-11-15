//! Guarded corecursion: a coinductive datatype at the value universe, the guard
//! the kernel checks on a fixpoint into it, and the fold it refuses over it.
//! The conversion that unfolds a guarded fixpoint is witnessed in the replay's
//! own tests.

use anodized::spec;
use gandr_kernel_core::CheckedId;
use gandr_kernel_core::Environment;
use gandr_kernel_core::GuardBreak;
use gandr_kernel_core::GuardNode;
use gandr_kernel_core::KernelError;
use gandr_kernel_strata::Level;
use gandr_kernel_term::CompTypeId;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DataFixpoint;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FixpointEvidence;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::LevelSignature;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueTypeId;

/// How many times `succ` applies to `zero` in a numeral.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Successors(usize);

/// Admit `Nat`: `zero`, and `succ` over the family itself.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the position of a checked data declaration at the environment's
///   next position.
/// - panics: if the strictly positive declaration is refused.
///
/// # Adequacy
/// - hypothesis: L3 — the streams and the delay type over naturals admit after
///   it.
/// - witness: `tests::guard::the_stream_of_ones_is_guarded`
#[spec(captures: position = environment.entries().len(), ensures: |ret| usize::from(ret) == position)]
fn nat(environment: &mut Environment) -> ConstantIndex
{
    let position = ConstantIndex::from(environment.entries().len());
    let mut staging = environment.stage();
    let arena = staging.arena();
    let own = arena.value_type_data(position, vec![]);
    let kind = arena.value_type_universe(GroundSort::Value, Level::zero());
    let declaration = staging.data(
        LevelSignature::monomorphic(),
        vec![],
        vec![vec![], vec![own]],
        kind,
    );
    environment
        .add_decl(declaration)
        .expect("Nat is strictly positive")
        .position()
}

/// The natural `count` over the admitted `Nat`.
///
/// # Specification
/// trivial.
fn numeral(
    arena: &mut TermArena,
    nat: ConstantIndex,
    count: Successors,
) -> ValueId
{
    let nat_type = arena.value_type_data(nat, vec![]);
    let mut value = arena.value_constructor(nat, nat_type, ConstructorTag::from(0), vec![]);
    for _step in 0 .. count.0 {
        value = arena.value_constructor(nat, nat_type, ConstructorTag::from(1), vec![value]);
    }
    value
}

/// Admit a datatype at the value universe whose constructors take the fields
/// `fields` builds over the datatype itself, read as `fixpoint`.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the admission's verdict for the declaration at the environment's
///   next position.
///
/// # Adequacy
/// - hypothesis: L3 — the coinductive delay type admits; an indexed coinductive
///   datatype is refused as not free.
/// - witness: `tests::guard::the_bind_of_the_delay_model_is_guarded`
/// - witness: `tests::guard::a_coinductive_datatype_admits_no_fold`
#[spec(captures: position = environment.entries().len(), ensures: |ret| ret.as_ref().map_or(true, |admitted| usize::from(admitted.position()) == position))]
fn datatype(
    environment: &mut Environment,
    fixpoint: DataFixpoint,
    fields: impl FnOnce(&mut TermArena, ValueTypeId) -> Vec<Vec<ValueTypeId>>,
) -> Result<CheckedId, KernelError>
{
    let position = ConstantIndex::from(environment.entries().len());
    let mut staging = environment.stage();
    let arena = staging.arena();
    let own = arena.value_type_data(position, vec![]);
    let constructors = fields(arena, own);
    let kind = arena.value_type_universe(GroundSort::Value, Level::zero());
    let declaration = staging.data(LevelSignature::monomorphic(), vec![], constructors, kind);
    let declaration = match fixpoint {
        DataFixpoint::Greatest => declaration.coinductive(),
        DataFixpoint::Least => declaration,
    };
    environment.add_decl(declaration)
}

/// Admit `Stream = Cons Nat (U (F Stream))`, read as `fixpoint`.
///
/// # Specification
/// - requires: `nat` names the admitted `Nat`.
/// - ensures: the position of the admitted declaration.
/// - panics: if the declaration is refused.
///
/// # Adequacy
/// - hypothesis: L3 — the coinductive stream holds the stream of ones, and the
///   inductive one refuses it.
/// - witness: `tests::guard::the_stream_of_ones_is_guarded`
/// - witness: `tests::guard::a_guarded_fixpoint_stands_only_at_a_coinductive_type`
#[spec(captures: position = environment.entries().len(), ensures: |ret| usize::from(ret) == position)]
fn stream(
    environment: &mut Environment,
    nat: ConstantIndex,
    fixpoint: DataFixpoint,
) -> ConstantIndex
{
    datatype(environment, fixpoint, |arena, own| {
        let nat_type = arena.value_type_data(nat, vec![]);
        let returns = arena.comp_type_returner(own);
        let rest = arena.value_type_thunk(returns);
        vec![vec![nat_type, rest]]
    })
    .expect("a stream's tail is a thunk of a returner of the stream")
    .position()
}

/// Admit `Delay = Now Nat | Later (U (F Delay)) | Op (U (Nat → F Delay))`, the
/// delay type with one operation, read as `fixpoint`.
///
/// # Specification
/// - requires: `nat` names the admitted `Nat`.
/// - ensures: the position of the admitted declaration.
/// - panics: if the declaration is refused.
///
/// # Adequacy
/// - hypothesis: L3 — the coinductive delay type holds `never` and `bind`, and
///   refuses a fold that the inductive one admits.
/// - witness: `tests::guard::the_bind_of_the_delay_model_is_guarded`
/// - witness: `tests::guard::a_coinductive_datatype_admits_no_fold`
#[spec(captures: position = environment.entries().len(), ensures: |ret| usize::from(ret) == position)]
fn delay(
    environment: &mut Environment,
    nat: ConstantIndex,
    fixpoint: DataFixpoint,
) -> ConstantIndex
{
    datatype(environment, fixpoint, |arena, own| {
        let nat_type = arena.value_type_data(nat, vec![]);
        let returns = arena.comp_type_returner(own);
        let later = arena.value_type_thunk(returns);
        let resumed = arena.comp_type_arrow(nat_type, returns);
        let op = arena.value_type_thunk(resumed);
        vec![vec![nat_type], vec![later], vec![op]]
    })
    .expect("each recursive field of the delay type is a thunk")
    .position()
}

/// Admit a definition whose declared type and body `build` gives.
///
/// # Specification
/// - requires: the roots `build` mints live in the staging arena.
/// - ensures: the admission's verdict for the declaration at the environment's
///   next position.
///
/// # Adequacy
/// - hypothesis: L3 — `Now 1` admits, and a structural fold over the
///   coinductive delay type is refused.
/// - witness: `tests::guard::the_stream_of_ones_is_guarded`
/// - witness: `tests::guard::a_coinductive_datatype_admits_no_fold`
#[spec(captures: position = environment.entries().len(), ensures: |ret| ret.as_ref().map_or(true, |admitted| usize::from(admitted.position()) == position))]
fn define(
    environment: &mut Environment,
    build: impl FnOnce(&mut TermArena) -> (ValueTypeId, ValueId),
) -> Result<CheckedId, KernelError>
{
    let mut staging = environment.stage();
    let (declared, body) = build(staging.arena());
    let declaration = staging.def(LevelSignature::monomorphic(), declared, body);
    environment.add_decl(declaration)
}

/// Admit `thunk (fix s. body)` at `U expected`, the fixpoint under `evidence`,
/// where `build` gives `expected` and `body`.
///
/// # Specification
/// - requires: `body` reads the self binder at index zero.
/// - ensures: the admission's verdict for the declaration at the environment's
///   next position.
///
/// # Adequacy
/// - hypothesis: L3 — the stream of ones admits, and a call through no
///   constructor is refused by name.
/// - witness: `tests::guard::the_stream_of_ones_is_guarded`
/// - witness: `tests::guard::a_call_through_no_constructor_is_refused`
#[spec(captures: position = environment.entries().len(), ensures: |ret| ret.as_ref().map_or(true, |admitted| usize::from(admitted.position()) == position))]
fn corecursion(
    environment: &mut Environment,
    evidence: FixpointEvidence,
    build: impl FnOnce(&mut TermArena) -> (CompTypeId, ComputationId),
) -> Result<CheckedId, KernelError>
{
    define(environment, |arena| {
        let (expected, body) = build(arena);
        let fixpoint = arena.computation_fixpoint(body, evidence);
        (
            arena.value_type_thunk(expected),
            arena.value_thunk(fixpoint),
        )
    })
}

/// `return C(fields)` for the constructor `tag` of the datatype `family`.
///
/// # Specification
/// trivial.
fn construct(
    arena: &mut TermArena,
    family: ConstantIndex,
    tag: ConstructorTag,
    fields: Vec<ValueId>,
) -> ComputationId
{
    let datatype = arena.value_type_data(family, vec![]);
    let value = arena.value_constructor(family, datatype, tag, fields);
    arena.computation_return(value)
}

/// `force s` for the self binder at `index`.
///
/// # Specification
/// trivial.
fn call(
    arena: &mut TermArena,
    index: DeBruijnIndex,
) -> ComputationId
{
    let own = arena.value_variable(index);
    arena.computation_force(own)
}

/// `fix s. return Cons n (thunk (force s))` at `F Stream`: the stream of the
/// natural `n`, read from the self binder at index zero.
///
/// # Specification
/// trivial.
fn repeat(
    arena: &mut TermArena,
    (nat, stream): (ConstantIndex, ConstantIndex),
    n: Successors,
) -> (CompTypeId, ComputationId)
{
    let stream_type = arena.value_type_data(stream, vec![]);
    let expected = arena.comp_type_returner(stream_type);
    let head = numeral(arena, nat, n);
    let rest = call(arena, DeBruijnIndex::from(0));
    let tail = arena.value_thunk(rest);
    (
        expected,
        construct(arena, stream, ConstructorTag::from(0), vec![head, tail]),
    )
}

/// Admit `observe : U (U (F Delay) → F Delay) = thunk (λq. force q)`, a
/// function that observes its argument.
///
/// # Specification
/// - requires: `delay` names the admitted delay type.
/// - ensures: the position of the admitted definition.
/// - panics: if the definition is refused.
///
/// # Adequacy
/// - hypothesis: L3 — the guarded fixpoint passed bare to `observe` is refused
///   as bare, and an application of `observe` above a call is refused at the
///   node.
/// - witness: `tests::guard::a_fixpoint_that_is_no_call_is_refused`
/// - witness: `tests::guard::a_node_that_is_none_of_the_five_is_refused`
#[spec(captures: position = environment.entries().len(), ensures: |ret| usize::from(ret) == position)]
fn observer(
    environment: &mut Environment,
    delay: ConstantIndex,
) -> ConstantIndex
{
    define(environment, |arena| {
        let delay_type = arena.value_type_data(delay, vec![]);
        let returns = arena.comp_type_returner(delay_type);
        let thunk = arena.value_type_thunk(returns);
        let arrow = arena.comp_type_arrow(thunk, returns);
        let forced = call(arena, DeBruijnIndex::from(0));
        let lambda = arena.computation_lambda(forced);
        (arena.value_type_thunk(arrow), arena.value_thunk(lambda))
    })
    .expect("a function that forces its argument checks")
    .position()
}

#[test]
fn the_stream_of_ones_is_guarded()
{
    let mut environment = Environment::new();
    let nat = nat(&mut environment);
    let stream = stream(&mut environment, nat, DataFixpoint::Greatest);
    let ones = corecursion(&mut environment, FixpointEvidence::Guarded, |arena| {
        repeat(arena, (nat, stream), Successors(1))
    });
    assert!(
        ones.is_ok(),
        "the call stands under `Cons` and its thunk: {ones:?}"
    );
    // `never = fix s. Later (thunk (force s))` and `Now 1`, into the delay
    // type.
    let delay = delay(&mut environment, nat, DataFixpoint::Greatest);
    let never = corecursion(&mut environment, FixpointEvidence::Guarded, |arena| {
        let delay_type = arena.value_type_data(delay, vec![]);
        let expected = arena.comp_type_returner(delay_type);
        let rest = call(arena, DeBruijnIndex::from(0));
        let later = arena.value_thunk(rest);
        (
            expected,
            construct(arena, delay, ConstructorTag::from(1), vec![later]),
        )
    });
    assert!(never.is_ok(), "the call stands under `Later`: {never:?}");
    let now = define(&mut environment, |arena| {
        let delay_type = arena.value_type_data(delay, vec![]);
        let one = numeral(arena, nat, Successors(1));
        let value = arena.value_constructor(delay, delay_type, ConstructorTag::from(0), vec![one]);
        (delay_type, value)
    });
    assert!(
        now.is_ok(),
        "a value of the delay type passes as any value: {now:?}"
    );
}

#[test]
fn the_bind_of_the_delay_model_is_guarded()
{
    let mut environment = Environment::new();
    let nat = nat(&mut environment);
    let delay = delay(&mut environment, nat, DataFixpoint::Greatest);
    // bind = fix s. λp. λk. case p {
    //   Now a ⇒ (force k) a
    //   Later p' ⇒ return Later (thunk (q ← force p'; (force s) q k))
    //   Op κ ⇒ return Op (thunk (λx. y ← (force κ) x; (force s) y k))
    // }
    let bind = corecursion(&mut environment, FixpointEvidence::Guarded, |arena| {
        let nat_type = arena.value_type_data(nat, vec![]);
        let delay_type = arena.value_type_data(delay, vec![]);
        let returns = arena.comp_type_returner(delay_type);
        let continuation = arena.comp_type_arrow(nat_type, returns);
        let thunked = arena.value_type_thunk(continuation);
        let tail = arena.comp_type_arrow(thunked, returns);
        let expected = arena.comp_type_arrow(delay_type, tail);
        let variable =
            |arena: &mut TermArena, index: u32| arena.value_variable(DeBruijnIndex::from(index));
        // `Now a`: a = 0, k = 1.
        let then = variable(arena, 1);
        let resume = arena.computation_force(then);
        let answer = variable(arena, 0);
        let resumed = arena.computation_application(resume, answer);
        let now = arena.computation_lambda(resumed);
        // `Later p'`: inside the bind, q = 0, p' = 1, k = 2, s = 4.
        let pending = variable(arena, 0);
        let step = arena.computation_force(pending);
        let own = call(arena, DeBruijnIndex::from(4));
        let stepped = variable(arena, 0);
        let applied = arena.computation_application(own, stepped);
        let then = variable(arena, 2);
        let again = arena.computation_application(applied, then);
        let sequenced = arena.computation_bind(step, again);
        let later = arena.value_thunk(sequenced);
        let later = construct(arena, delay, ConstructorTag::from(1), vec![later]);
        let later = arena.computation_lambda(later);
        // `Op κ`: inside the bind, y = 0, x = 1, κ = 2, k = 3, s = 5.
        let kappa = variable(arena, 1);
        let resume = arena.computation_force(kappa);
        let argument = variable(arena, 0);
        let replied = arena.computation_application(resume, argument);
        let own = call(arena, DeBruijnIndex::from(5));
        let reply = variable(arena, 0);
        let applied = arena.computation_application(own, reply);
        let then = variable(arena, 3);
        let again = arena.computation_application(applied, then);
        let sequenced = arena.computation_bind(replied, again);
        let abstraction = arena.computation_lambda(sequenced);
        let op = arena.value_thunk(abstraction);
        let op = construct(arena, delay, ConstructorTag::from(2), vec![op]);
        let op = arena.computation_lambda(op);
        // The case on p: p = 1 under λp. λk.
        let scrutinee = variable(arena, 1);
        let case = arena.computation_data_case(scrutinee, returns, vec![now, later, op]);
        let body = arena.computation_lambda(case);
        (expected, arena.computation_lambda(body))
    });
    assert!(
        bind.is_ok(),
        "each call passes a branch, a constructor, its thunk, an abstraction or a let that \
         binds no call: {bind:?}"
    );
}

#[test]
fn a_nested_fixpoint_checks_as_two_walks()
{
    let mut environment = Environment::new();
    let nat = nat(&mut environment);
    let stream = stream(&mut environment, nat, DataFixpoint::Greatest);
    // fix s. return Cons 1 (thunk (fix t. body)), body as given, s at 1 in it.
    let nested = |environment: &mut Environment, guarded: bool| {
        corecursion(environment, FixpointEvidence::Guarded, |arena| {
            let stream_type = arena.value_type_data(stream, vec![]);
            let expected = arena.comp_type_returner(stream_type);
            let outer = call(arena, DeBruijnIndex::from(1));
            let inner = if guarded {
                let two = numeral(arena, nat, Successors(2));
                let rest = arena.value_thunk(outer);
                construct(arena, stream, ConstructorTag::from(0), vec![two, rest])
            }
            else {
                outer
            };
            let fixpoint = arena.computation_fixpoint(inner, FixpointEvidence::Guarded);
            let tail = arena.value_thunk(fixpoint);
            let one = numeral(arena, nat, Successors(1));
            (
                expected,
                construct(arena, stream, ConstructorTag::from(0), vec![one, tail]),
            )
        })
    };
    let admitted = nested(&mut environment, true);
    assert!(
        admitted.is_ok(),
        "the outer call stands under a constructor inside the inner body: {admitted:?}"
    );
    assert_eq!(
        nested(&mut environment, false).map(|_| ()),
        Err(KernelError::Unguarded(GuardBreak::Unconstructed)),
        "the constructors outside the inner fixpoint do not count inside it"
    );
}

#[test]
fn a_node_that_is_none_of_the_five_is_refused()
{
    let mut environment = Environment::new();
    let nat = nat(&mut environment);
    let delay = delay(&mut environment, nat, DataFixpoint::Greatest);
    let observe = observer(&mut environment, delay);
    // fix s. return Later (thunk ((force observe) (thunk (force s)))): the call
    // stands in an argument of another function.
    let refused = corecursion(&mut environment, FixpointEvidence::Guarded, |arena| {
        let delay_type = arena.value_type_data(delay, vec![]);
        let expected = arena.comp_type_returner(delay_type);
        let function = arena.value_constant(observe);
        let forced = arena.computation_force(function);
        let own = call(arena, DeBruijnIndex::from(0));
        let argument = arena.value_thunk(own);
        let applied = arena.computation_application(forced, argument);
        let later = arena.value_thunk(applied);
        (
            expected,
            construct(arena, delay, ConstructorTag::from(1), vec![later]),
        )
    });
    assert_eq!(
        refused.map(|_| ()),
        Err(KernelError::Unguarded(GuardBreak::Node(
            GuardNode::Application
        ))),
        "an application of another function is none of the five"
    );
}

#[test]
fn an_argument_that_holds_the_fixpoint_is_refused()
{
    let mut environment = Environment::new();
    let nat = nat(&mut environment);
    let stream = stream(&mut environment, nat, DataFixpoint::Greatest);
    // fix s. λt. return Cons 1 (thunk ((force s) (thunk ((force s) t)))).
    let refused = corecursion(&mut environment, FixpointEvidence::Guarded, |arena| {
        let stream_type = arena.value_type_data(stream, vec![]);
        let returns = arena.comp_type_returner(stream_type);
        let thunk = arena.value_type_thunk(returns);
        let expected = arena.comp_type_arrow(thunk, returns);
        let inner = call(arena, DeBruijnIndex::from(1));
        let t = arena.value_variable(DeBruijnIndex::from(0));
        let inner = arena.computation_application(inner, t);
        let argument = arena.value_thunk(inner);
        let outer = call(arena, DeBruijnIndex::from(1));
        let outer = arena.computation_application(outer, argument);
        let tail = arena.value_thunk(outer);
        let one = numeral(arena, nat, Successors(1));
        let body = construct(arena, stream, ConstructorTag::from(0), vec![one, tail]);
        (expected, arena.computation_lambda(body))
    });
    assert_eq!(
        refused.map(|_| ()),
        Err(KernelError::Unguarded(GuardBreak::Argument)),
        "the call's argument holds the fixpoint"
    );
}

#[test]
fn a_fixpoint_that_is_no_call_is_refused()
{
    let mut environment = Environment::new();
    let nat = nat(&mut environment);
    let delay = delay(&mut environment, nat, DataFixpoint::Greatest);
    let observe = observer(&mut environment, delay);
    // fix s. return Later (thunk ((force observe) s)): the bare s.
    let refused = corecursion(&mut environment, FixpointEvidence::Guarded, |arena| {
        let delay_type = arena.value_type_data(delay, vec![]);
        let expected = arena.comp_type_returner(delay_type);
        let function = arena.value_constant(observe);
        let forced = arena.computation_force(function);
        let own = arena.value_variable(DeBruijnIndex::from(0));
        let applied = arena.computation_application(forced, own);
        let later = arena.value_thunk(applied);
        (
            expected,
            construct(arena, delay, ConstructorTag::from(1), vec![later]),
        )
    });
    assert_eq!(
        refused.map(|_| ()),
        Err(KernelError::Unguarded(GuardBreak::Bare)),
        "a bare fixpoint is no call"
    );
}

#[test]
fn a_call_through_no_constructor_is_refused()
{
    let mut environment = Environment::new();
    let nat = nat(&mut environment);
    let delay = delay(&mut environment, nat, DataFixpoint::Greatest);
    // fix s. force s.
    let refused = corecursion(&mut environment, FixpointEvidence::Guarded, |arena| {
        let delay_type = arena.value_type_data(delay, vec![]);
        (
            arena.comp_type_returner(delay_type),
            call(arena, DeBruijnIndex::from(0)),
        )
    });
    assert_eq!(
        refused.map(|_| ()),
        Err(KernelError::Unguarded(GuardBreak::Unconstructed)),
        "no constructor stands on the path to the call"
    );
}

#[test]
fn a_let_is_transparent_unless_it_binds_the_fixpoint()
{
    let mut environment = Environment::new();
    let nat = nat(&mut environment);
    let stream = stream(&mut environment, nat, DataFixpoint::Greatest);
    // fix s. n ← return 1; return Cons n (thunk (force s)), s at 1 in the body.
    let transparent = corecursion(&mut environment, FixpointEvidence::Guarded, |arena| {
        let stream_type = arena.value_type_data(stream, vec![]);
        let expected = arena.comp_type_returner(stream_type);
        let one = numeral(arena, nat, Successors(1));
        let bound = arena.computation_return(one);
        let n = arena.value_variable(DeBruijnIndex::from(0));
        let rest = call(arena, DeBruijnIndex::from(1));
        let tail = arena.value_thunk(rest);
        let body = construct(arena, stream, ConstructorTag::from(0), vec![n, tail]);
        (expected, arena.computation_bind(bound, body))
    });
    assert!(
        transparent.is_ok(),
        "a let whose bound term holds no call is transparent: {transparent:?}"
    );
    // fix s. return Cons 1 (thunk (x ← force s; return x)).
    let refused = corecursion(&mut environment, FixpointEvidence::Guarded, |arena| {
        let stream_type = arena.value_type_data(stream, vec![]);
        let expected = arena.comp_type_returner(stream_type);
        let bound = call(arena, DeBruijnIndex::from(0));
        let x = arena.value_variable(DeBruijnIndex::from(0));
        let returned = arena.computation_return(x);
        let sequenced = arena.computation_bind(bound, returned);
        let tail = arena.value_thunk(sequenced);
        let one = numeral(arena, nat, Successors(1));
        (
            expected,
            construct(arena, stream, ConstructorTag::from(0), vec![one, tail]),
        )
    });
    assert_eq!(
        refused.map(|_| ()),
        Err(KernelError::Unguarded(GuardBreak::Node(GuardNode::Let))),
        "a let whose bound term holds the call is an occurrence at the let"
    );
}

#[test]
fn a_guarded_fixpoint_stands_only_at_a_coinductive_type()
{
    let mut environment = Environment::new();
    let nat = nat(&mut environment);
    let stream = stream(&mut environment, nat, DataFixpoint::Least);
    let refused = corecursion(&mut environment, FixpointEvidence::Guarded, |arena| {
        repeat(arena, (nat, stream), Successors(1))
    });
    assert_eq!(
        refused.map(|_| ()),
        Err(KernelError::GuardedNotCoinductive),
        "an inductive datatype with a thunked field is an initial algebra"
    );
}

#[test]
fn a_coinductive_datatype_admits_no_fold()
{
    let mut environment = Environment::new();
    let nat = nat(&mut environment);
    // fix[<] s. λp. return 0 at Delay → F Nat.
    let fold = |environment: &mut Environment, delay: ConstantIndex| {
        corecursion(environment, FixpointEvidence::StructuralDescent, |arena| {
            let nat_type = arena.value_type_data(nat, vec![]);
            let delay_type = arena.value_type_data(delay, vec![]);
            let returns = arena.comp_type_returner(nat_type);
            let expected = arena.comp_type_arrow(delay_type, returns);
            let zero = numeral(arena, nat, Successors(0));
            let body = arena.computation_return(zero);
            (expected, arena.computation_lambda(body))
        })
    };
    let inductive = delay(&mut environment, nat, DataFixpoint::Least);
    let admitted = fold(&mut environment, inductive);
    assert!(
        admitted.is_ok(),
        "an initial algebra admits a fold: {admitted:?}"
    );
    let coinductive = delay(&mut environment, nat, DataFixpoint::Greatest);
    assert_eq!(
        fold(&mut environment, coinductive).map(|_| ()),
        Err(KernelError::FoldOverCoinductive),
        "the final coalgebra admits no fold"
    );
    // A coinductive datatype indexed by `Nat` is no final coalgebra of its
    // constructors alone.
    let mut staging = environment.stage();
    let arena = staging.arena();
    let nat_type = arena.value_type_data(nat, vec![]);
    let zero = numeral(arena, nat, Successors(0));
    let kind = arena.value_type_universe(GroundSort::Value, Level::zero());
    let indexed = staging.indexed(
        LevelSignature::monomorphic(),
        vec![],
        (vec![nat_type], vec![vec![]], vec![vec![zero]]),
        kind,
    );
    assert_eq!(
        environment.add_decl(indexed.coinductive()).map(|_| ()),
        Err(KernelError::CoinductiveNotFree),
        "a coinductive datatype is indexed by nothing"
    );
}
