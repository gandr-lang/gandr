use alloc::vec::Vec;

use gandr_core_term::CertificateEquality;
use gandr_core_term::CoreArena;
use gandr_core_term::Sort;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_core_term::equal_certificate_syntax;
use gandr_core_term::hole::HoleId;
use gandr_core_term::hole::NominationIndex;
use gandr_core_term::tactic::Tactic;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GroundSort;
use quenchant_shape::shape::Maybe;

use crate::Verdict;
use crate::bridge::Outcome;
use crate::bridge::readmit;
use crate::context::CheckBudget;
use crate::context::CheckingContext;
use crate::declaration::Declaration;
use crate::declaration::OriginToken;
use crate::declaration::signature;
use crate::module::check_module;
use crate::refusal::CheckRefusal;
use crate::refusal::TacticFault;

/// The hole the `place`th splice writes, running `tactic`.
///
/// # Specification
/// trivial.
fn spliced(
    arena: &mut CoreArena,
    place: NominationIndex,
    tactic: Tactic,
) -> ValueId
{
    let hole = HoleId::spliced(place, tactic).expect("a splice's name");
    arena.value_hole(hole)
}

/// The value declaration at `place`, of `declared` when one is given,
/// defined by `body`.
///
/// # Specification
/// trivial.
fn declaration(
    place: ConstantIndex,
    declared: Maybe<ValueTypeId, signature::Absent>,
    body: ValueId,
) -> Declaration
{
    Declaration::new(
        place,
        declared,
        Maybe::Present(body),
        OriginToken::from(usize::from(place)),
    )
}

/// Whether the kernel admitted a declaration the judgement accepted.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Readmitted
{
    /// Admitted as a definition.
    Defined,
    /// Not admitted.
    Refused,
}

/// Judge `module`, then readmit what the judgement accepted: each verdict,
/// and whether the kernel admitted each declaration.
///
/// # Specification
/// trivial.
fn judged(
    arena: &mut CoreArena,
    module: &[Declaration],
) -> Vec<(Verdict, Readmitted)>
{
    let report = {
        let mut context = CheckingContext::new(arena, CheckBudget::DEFAULT);
        check_module(&mut context, module)
    };
    let readmission = readmit(arena, &report);
    report
        .judged()
        .iter()
        .zip(readmission.readmitted())
        .map(|(judged, entry)| {
            let readmitted = if matches!(*entry.outcome(), Outcome::Defined { .. }) {
                Readmitted::Defined
            }
            else {
                Readmitted::Refused
            };
            (judged.verdict(), readmitted)
        })
        .collect()
}

#[test]
fn assumption_answers_the_innermost_binder_of_the_goal_type_2762()
{
    // def pick : U (Integer -> Unit -> Integer -> F Integer)
    //          = thunk λ λ λ. return ~assumption ;
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let unit = arena.value_type_unit();
    let returns = arena.comp_type_returner(integer);
    let last = arena.comp_type_arrow(integer, returns);
    let middle = arena.comp_type_arrow(unit, last);
    let first = arena.comp_type_arrow(integer, middle);
    let declared = arena.value_type_thunk(first);
    let hole = spliced(&mut arena, NominationIndex::from(0_u32), Tactic::ASSUMPTION);
    let wrap = |arena: &mut CoreArena, value| {
        let returned = arena.computation_return(value);
        let inner = arena.computation_lambda(returned);
        let middle = arena.computation_lambda(inner);
        let outer = arena.computation_lambda(middle);
        arena.value_thunk(outer)
    };
    let body = wrap(&mut arena, hole);
    let innermost = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let expected = wrap(&mut arena, innermost);
    let outcomes = judged(&mut arena, &[declaration(
        ConstantIndex::from(0_usize),
        Maybe::Present(declared),
        body,
    )]);
    let [(verdict, admitted)] = *outcomes.as_slice()
    else {
        panic!("one declaration, one outcome");
    };
    assert!(
        matches!(verdict, Verdict::Checked { body, .. } if equal_certificate_syntax(&arena, body, expected) == CertificateEquality::Equal),
        "the splice is filled with the innermost integer binder: {verdict:?}"
    );
    assert_eq!(
        admitted,
        Readmitted::Defined,
        "the kernel replays the filled body, never meeting the splice"
    );
}

#[test]
fn intro_states_its_new_goal_under_the_binder_it_opens_2762()
{
    // def id : U ((a : Type) -> El a -> F (El a))
    //        = ~intro(intro(assumption)) ;
    // The second binder's type and the codomain both read the first binder:
    // each new goal is the context one binder longer, its type under it.
    let mut arena = CoreArena::new();
    let small = arena.value_type_universe(Sort::Ground(GroundSort::Value), Level::zero());
    let bound = arena.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let element = arena.value_type_element(bound, Level::zero());
    let returns = arena.comp_type_returner(element);
    let arrow = arena.comp_type_arrow(element, returns);
    let polymorphic = arena.comp_type_pi(small, arrow);
    let declared = arena.value_type_thunk(polymorphic);
    let twice = Tactic::ASSUMPTION
        .intro()
        .and_then(Tactic::intro)
        .expect("two introductions");
    let hole = spliced(&mut arena, NominationIndex::from(0_u32), twice);
    let returned = arena.computation_return(bound);
    let inner = arena.computation_lambda(returned);
    let outer = arena.computation_lambda(inner);
    let identity = arena.value_thunk(outer);
    let outcomes = judged(&mut arena, &[declaration(
        ConstantIndex::from(0_usize),
        Maybe::Present(declared),
        hole,
    )]);
    let [(verdict, admitted)] = *outcomes.as_slice()
    else {
        panic!("one declaration, one outcome");
    };
    assert!(
        matches!(verdict, Verdict::Checked { body, .. } if equal_certificate_syntax(&arena, body, identity) == CertificateEquality::Equal),
        "two introductions and an assumption answer the identity: {verdict:?}"
    );
    assert_eq!(
        admitted,
        Readmitted::Defined,
        "the kernel replays the identity the tactic wrote"
    );
}

#[test]
fn a_tactic_with_no_answer_names_why()
{
    // def none  : U (Unit -> F Integer) = thunk λ. return ~assumption ;
    // def flat  : Integer = ~intro(assumption) ;
    // def loose = ~assumption ;
    let mut arena = CoreArena::new();
    let integer = arena.value_type_base(BaseType::Integer);
    let unit = arena.value_type_unit();
    let returns = arena.comp_type_returner(integer);
    let from_unit = arena.comp_type_arrow(unit, returns);
    let suspended = arena.value_type_thunk(from_unit);
    let unanswered = spliced(&mut arena, NominationIndex::from(0_u32), Tactic::ASSUMPTION);
    let returned = arena.computation_return(unanswered);
    let lambda = arena.computation_lambda(returned);
    let none = arena.value_thunk(lambda);
    let introducing = Tactic::ASSUMPTION.intro().expect("one introduction");
    let flat = spliced(&mut arena, NominationIndex::from(1_u32), introducing);
    let loose = spliced(&mut arena, NominationIndex::from(2_u32), Tactic::ASSUMPTION);
    let outcomes = judged(&mut arena, &[
        declaration(
            ConstantIndex::from(0_usize),
            Maybe::Present(suspended),
            none,
        ),
        declaration(ConstantIndex::from(1_usize), Maybe::Present(integer), flat),
        declaration(
            ConstantIndex::from(2_usize),
            Maybe::Absent(signature::Absent::Unsigned),
            loose,
        ),
    ]);
    let faults: Vec<_> = outcomes
        .iter()
        .map(|&(verdict, admitted)| {
            let Verdict::Refused(CheckRefusal::TacticRefused { tactic, fault, .. }) = verdict
            else {
                return None;
            };
            Some((tactic, fault, admitted))
        })
        .collect();
    assert_eq!(faults, [
        Some((
            Tactic::ASSUMPTION,
            TacticFault::NoHypothesis,
            Readmitted::Refused
        )),
        Some((introducing, TacticFault::NoFunction, Readmitted::Refused)),
        Some((
            Tactic::ASSUMPTION,
            TacticFault::Unplaced,
            Readmitted::Refused
        )),
    ]);
}
