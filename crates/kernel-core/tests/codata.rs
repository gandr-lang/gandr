//! Codata declarations: admission, the guard on self reference, and the
//! introductions and eliminations that read a codata type through its
//! observations.

use anodized::spec;
use gandr_kernel_core::CheckedId;
use gandr_kernel_core::Environment;
use gandr_kernel_core::KernelError;
use gandr_kernel_strata::Level;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FixpointEvidence;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::LevelSignature;
use gandr_kernel_term::Side;
use gandr_kernel_term::ValueId;

/// Admit `Nat`: `zero`, and `succ` over the family itself.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the returned identifier names a checked data declaration at the
///   environment's next position.
/// - panics: if the strictly positive block is refused.
///
/// # Adequacy
/// - hypothesis: L3 — the streams over naturals admit after it.
/// - witness: `tests::codata::a_stream_is_admitted_and_observed`
#[spec(captures: position = environment.entries().len(), ensures: |ret| usize::from(ret.position()) == position)]
fn nat(environment: &mut Environment) -> CheckedId
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
}

/// The shape of a stream's tail observation.
#[derive(Clone, Copy, Debug)]
enum Tail
{
    /// `Stream A`: the declaration at its parameter.
    Uniform,
    /// `Stream ⌜1⌝`: the declaration at another argument.
    Elsewhere,
    /// `U (Stream A) → F 1`: the declaration in a domain.
    Unguarded,
}

/// Stage `Stream A = ν. { head : F (El A); tail : … }`, the tail as `tail`
/// says, in a computation universe, and admit it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the admission's verdict for the declaration at the environment's
///   next position.
///
/// # Adequacy
/// - hypothesis: L3 — the uniform tail admits; the tail elsewhere and the tail
///   in a domain are refused.
/// - witness: `tests::codata::a_stream_is_admitted_and_observed`
/// - witness: `tests::codata::an_unguarded_self_reference_is_refused`
/// - witness: `tests::codata::a_non_uniform_self_reference_is_refused`
#[spec(captures: position = environment.entries().len(), ensures: |ret| ret.as_ref().map_or(true, |admitted| usize::from(admitted.position()) == position))]
fn stream(
    environment: &mut Environment,
    tail: Tail,
) -> Result<CheckedId, KernelError>
{
    let position = ConstantIndex::from(environment.entries().len());
    let mut staging = environment.stage();
    let arena = staging.arena();
    let universe = arena.value_type_universe(GroundSort::Value, Level::zero());
    let parameter = arena.value_variable(DeBruijnIndex::from(0));
    let element = arena.value_type_element(parameter, Level::zero());
    let head = arena.comp_type_returner(element);
    let rest = match tail {
        Tail::Uniform => arena.comp_type_codata(position, vec![parameter]),
        Tail::Elsewhere => {
            let unit = arena.value_type_unit();
            let code = arena.value_quote(unit);
            arena.comp_type_codata(position, vec![code])
        },
        Tail::Unguarded => {
            let own = arena.comp_type_codata(position, vec![parameter]);
            let thunk = arena.value_type_thunk(own);
            let unit = arena.value_type_unit();
            let returns = arena.comp_type_returner(unit);
            arena.comp_type_arrow(thunk, returns)
        },
    };
    let kind = arena.value_type_universe(GroundSort::Computation, Level::zero());
    let declaration = staging.codata(
        LevelSignature::monomorphic(),
        vec![universe],
        vec![head, rest],
        kind,
    );
    environment.add_decl(declaration)
}

/// `succ zero` over the admitted `Nat`.
///
/// # Specification
/// trivial.
fn one(
    arena: &mut gandr_kernel_term::TermArena,
    nat: ConstantIndex,
) -> ValueId
{
    let nat_type = arena.value_type_data(nat, vec![]);
    let zero = arena.value_constructor(nat_type, ConstructorTag::from(0), vec![]);
    arena.value_constructor(nat_type, ConstructorTag::from(1), vec![zero])
}

/// Admit `ones : U (Stream ⌜Nat⌝) = thunk (fix s. return 1 & force s)`.
///
/// # Specification
/// - requires: `nat` and `stream` name admitted declarations.
/// - ensures: the admission's verdict.
///
/// # Adequacy
/// - hypothesis: L3 — the fixpoint pairing a head with its own tail checks at
///   the stream and is observed at its head.
/// - witness: `tests::codata::a_stream_is_admitted_and_observed`
#[spec(captures: position = environment.entries().len(), ensures: |ret| ret.as_ref().map_or(true, |admitted| usize::from(admitted.position()) == position))]
fn ones(
    environment: &mut Environment,
    (nat, stream): (ConstantIndex, ConstantIndex),
) -> Result<CheckedId, KernelError>
{
    let mut staging = environment.stage();
    let arena = staging.arena();
    let nat_type = arena.value_type_data(nat, vec![]);
    let nat_code = arena.value_quote(nat_type);
    let streamed = arena.comp_type_codata(stream, vec![nat_code]);
    let declared = arena.value_type_thunk(streamed);
    let one = one(arena, nat);
    let head = arena.computation_return(one);
    let own = arena.value_variable(DeBruijnIndex::from(0));
    let tail = arena.computation_force(own);
    let pairing = arena.computation_with(head, tail);
    let fixpoint = arena.computation_fixpoint(pairing, FixpointEvidence::Partial);
    let value = arena.value_thunk(fixpoint);
    let declaration = staging.def(LevelSignature::monomorphic(), declared, value);
    environment.add_decl(declaration)
}

#[test]
fn a_stream_is_admitted_and_observed()
{
    let mut environment = Environment::new();
    let nat = nat(&mut environment).position();
    let stream = stream(&mut environment, Tail::Uniform)
        .expect("a stream's tail stands at its parameter behind an observation")
        .position();
    let ones = ones(&mut environment, (nat, stream))
        .expect("a pairing checks against a stream through its observations")
        .position();
    // `second : U (F Nat) = thunk (π₁ (π₂ (force ones)))`: each projection
    // reads the stream it eliminates through its observations.
    let mut staging = environment.stage();
    let arena = staging.arena();
    let nat_type = arena.value_type_data(nat, vec![]);
    let returns = arena.comp_type_returner(nat_type);
    let declared = arena.value_type_thunk(returns);
    let named = arena.value_constant(ones);
    let forced = arena.computation_force(named);
    let rest = arena.computation_project(Side::Right, forced);
    let second = arena.computation_project(Side::Left, rest);
    let value = arena.value_thunk(second);
    let declaration = staging.def(LevelSignature::monomorphic(), declared, value);
    let observed = environment.add_decl(declaration);
    assert!(observed.is_ok(), "{observed:?}");
}

#[test]
fn a_single_observation_reads_as_itself()
{
    let mut environment = Environment::new();
    let nat = nat(&mut environment).position();
    // `Machine = ν. { step : Nat → F Nat }`.
    let position = ConstantIndex::from(environment.entries().len());
    let mut staging = environment.stage();
    let arena = staging.arena();
    let nat_type = arena.value_type_data(nat, vec![]);
    let returns = arena.comp_type_returner(nat_type);
    let step = arena.comp_type_arrow(nat_type, returns);
    let kind = arena.value_type_universe(GroundSort::Computation, Level::zero());
    let declaration = staging.codata(LevelSignature::monomorphic(), vec![], vec![step], kind);
    let machine = environment
        .add_decl(declaration)
        .expect("one observation admits")
        .position();
    assert_eq!(machine, position);
    // `successor : U Machine = thunk (λx. return (succ x))`.
    let mut staging = environment.stage();
    let arena = staging.arena();
    let nat_type = arena.value_type_data(nat, vec![]);
    let own = arena.comp_type_codata(machine, vec![]);
    let declared = arena.value_type_thunk(own);
    let argument = arena.value_variable(DeBruijnIndex::from(0));
    let successor = arena.value_constructor(nat_type, ConstructorTag::from(1), vec![argument]);
    let returned = arena.computation_return(successor);
    let lambda = arena.computation_lambda(returned);
    let value = arena.value_thunk(lambda);
    let declaration = staging.def(LevelSignature::monomorphic(), declared, value);
    let successor = environment
        .add_decl(declaration)
        .expect("a lambda checks against the one observation")
        .position();
    // `two : U (F Nat) = thunk ((force successor) 1)`.
    let mut staging = environment.stage();
    let arena = staging.arena();
    let nat_type = arena.value_type_data(nat, vec![]);
    let returns = arena.comp_type_returner(nat_type);
    let declared = arena.value_type_thunk(returns);
    let named = arena.value_constant(successor);
    let forced = arena.computation_force(named);
    let one = one(arena, nat);
    let applied = arena.computation_application(forced, one);
    let value = arena.value_thunk(applied);
    let declaration = staging.def(LevelSignature::monomorphic(), declared, value);
    let applied = environment.add_decl(declaration);
    assert!(applied.is_ok(), "{applied:?}");
}

#[test]
fn the_observation_product_is_not_the_codata_type()
{
    let mut environment = Environment::new();
    let nat = nat(&mut environment).position();
    let stream = stream(&mut environment, Tail::Uniform)
        .expect("a stream admits")
        .position();
    let ones = ones(&mut environment, (nat, stream))
        .expect("ones admits")
        .position();
    // `product : U (F Nat & Stream ⌜Nat⌝) = ones`: no η, so the stream is not
    // its observation product.
    let mut staging = environment.stage();
    let arena = staging.arena();
    let nat_type = arena.value_type_data(nat, vec![]);
    let nat_code = arena.value_quote(nat_type);
    let head = arena.comp_type_returner(nat_type);
    let tail = arena.comp_type_codata(stream, vec![nat_code]);
    let product = arena.comp_type_with(head, tail);
    let declared = arena.value_type_thunk(product);
    let value = arena.value_constant(ones);
    let declaration = staging.def(LevelSignature::monomorphic(), declared, value);
    assert!(matches!(
        environment.add_decl(declaration),
        Err(KernelError::ValueTypeMismatch(_))
    ));
}

#[test]
fn a_data_head_is_not_codata()
{
    let mut environment = Environment::new();
    let nat = nat(&mut environment).position();
    let mut staging = environment.stage();
    let arena = staging.arena();
    let named = arena.comp_type_codata(nat, vec![]);
    let declared = arena.value_type_thunk(named);
    let declaration = staging.axiom(LevelSignature::monomorphic(), declared);
    assert_eq!(
        environment
            .add_decl(declaration)
            .map(gandr_kernel_core::CheckedId::position),
        Err(KernelError::NotACodataType { index: nat })
    );
}

#[test]
fn a_value_universe_is_no_codata_kind()
{
    let mut environment = Environment::new();
    let mut staging = environment.stage();
    let arena = staging.arena();
    let unit = arena.value_type_unit();
    let returns = arena.comp_type_returner(unit);
    let kind = arena.value_type_universe(GroundSort::Value, Level::zero());
    let declaration = staging.codata(LevelSignature::monomorphic(), vec![], vec![returns], kind);
    assert_eq!(
        environment
            .add_decl(declaration)
            .map(gandr_kernel_core::CheckedId::position),
        Err(KernelError::CodataKindNotUniverse)
    );
}

#[test]
fn a_codata_without_observations_is_refused()
{
    let mut environment = Environment::new();
    let mut staging = environment.stage();
    let arena = staging.arena();
    let kind = arena.value_type_universe(GroundSort::Computation, Level::zero());
    let declaration = staging.codata(LevelSignature::monomorphic(), vec![], vec![], kind);
    assert_eq!(
        environment
            .add_decl(declaration)
            .map(gandr_kernel_core::CheckedId::position),
        Err(KernelError::CodataWithoutObservations)
    );
}

#[test]
fn an_unguarded_self_reference_is_refused()
{
    let mut environment = Environment::new();
    assert_eq!(
        stream(&mut environment, Tail::Unguarded).map(gandr_kernel_core::CheckedId::position),
        Err(KernelError::CodataOccurrence)
    );
}

#[test]
fn a_non_uniform_self_reference_is_refused()
{
    let mut environment = Environment::new();
    assert_eq!(
        stream(&mut environment, Tail::Elsewhere).map(gandr_kernel_core::CheckedId::position),
        Err(KernelError::CodataOccurrence)
    );
}

#[test]
fn an_ill_typed_codata_argument_is_refused()
{
    let mut environment = Environment::new();
    let nat = nat(&mut environment).position();
    let stream = stream(&mut environment, Tail::Uniform)
        .expect("a stream admits")
        .position();
    // `U (Stream 1)`: a natural is no type code.
    let mut staging = environment.stage();
    let arena = staging.arena();
    let one = one(arena, nat);
    let streamed = arena.comp_type_codata(stream, vec![one]);
    let declared = arena.value_type_thunk(streamed);
    let declaration = staging.axiom(LevelSignature::monomorphic(), declared);
    assert!(matches!(
        environment.add_decl(declaration),
        Err(KernelError::ValueTypeMismatch(_))
    ));
}
