//! End-to-end witnesses from staged source to admitted first-order CBPV.

use gandr_core_nbe::stage::normalize;
use gandr_core_nbe::stage::power;
use gandr_kernel_term::Computation;
use gandr_kernel_term::Value;
use gandr_kernel_term::stage::Model;

use super::*;

/// Interpret an admitted residual operand independently of register lowering.
///
/// # Specification
/// trivial.
fn value(
    arena: &TermArena,
    id: ValueId,
    bindings: &[Natural],
) -> Natural
{
    match *arena.value(id).unwrap() {
        | Value::Variable(index) => *bindings
            .iter()
            .rev()
            .nth(usize::try_from(u32::from(index)).unwrap())
            .unwrap(),
        | Value::Literal(Literal::Integer(ref literal)) => {
            Natural(literal.magnitude().as_ref().parse().unwrap())
        },
        | ref other => panic!("non-first-order operand: {other:?}"),
    }
}

/// Execute the actual admitted declaration, resolving the primitive by
/// identity.
///
/// # Specification
/// trivial.
fn admitted_result(
    environment: &Environment,
    admitted: Admitted,
    input: Natural,
) -> Natural
{
    let arena = environment.arena();
    let Value::Thunk(body) = *arena.value(admitted.body).unwrap()
    else {
        panic!("function thunk");
    };
    let Computation::Lambda(mut body) = *arena.computation(body).unwrap()
    else {
        panic!("one top-level lambda");
    };
    let mut bindings = Vec::from([input]);
    loop {
        match *arena.computation(body).unwrap() {
            | Computation::Return(result) => return value(arena, result, &bindings),
            | Computation::Bind(bound, continuation) => {
                let Computation::Application(head, right) = *arena.computation(bound).unwrap()
                else {
                    panic!("binary primitive");
                };
                let Computation::Application(head, left) = *arena.computation(head).unwrap()
                else {
                    panic!("binary primitive");
                };
                let Computation::Force(head) = *arena.computation(head).unwrap()
                else {
                    panic!("primitive force");
                };
                assert_eq!(
                    arena.value(head),
                    Some(&Value::Constant(admitted.multiplication.position()))
                );
                let left = value(arena, left, &bindings);
                let right = value(arena, right, &bindings);
                bindings.push(Natural(left.0.checked_mul(right.0).unwrap()));
                body = continuation;
            },
            | ref other => panic!("non-first-order computation: {other:?}"),
        }
    }
}

#[test]
fn power_is_admitted_and_executed()
{
    let mut arena = Arena::default();
    let model = Model(0);
    let token = arena.alloc_type(Type::In(model)).unwrap();
    let pow = power(&mut arena, model).unwrap();
    let inner = arena.alloc_type(Type::Nat(Stage::Inner(model))).unwrap();
    for exponent in 0_usize ..= 8 {
        let count = arena
            .alloc(Term::Natural(Stage::Outer, Natural(exponent)))
            .unwrap();
        let source = arena.alloc(Term::Apply(pow, count)).unwrap();
        let input = arena.alloc(Term::Variable(Index(0))).unwrap();
        let input = arena.alloc(Term::Quote(input)).unwrap();
        let source = arena.alloc(Term::Apply(source, input)).unwrap();
        let source = arena.alloc(Term::Splice(source)).unwrap();
        let source = arena.alloc(Term::Lambda(inner, source)).unwrap();
        let source = arena.alloc(Term::Quote(source)).unwrap();
        let certificate = normalize(&mut arena, source, &mut Budget(1_000_000)).unwrap();
        let residual = compile(&mut arena, &[token], &certificate, &mut Budget(1_000_000)).unwrap();
        assert_eq!(
            residual
                .instructions()
                .iter()
                .filter(|instruction| matches!(instruction, Instruction::Multiply(..)))
                .count(),
            exponent
        );
        let mut environment = Environment::new();
        let admitted = residual.admit(&mut environment).unwrap();
        let audit = environment.audit(admitted.definition);
        assert!(audit.unchecked_admissions().is_empty());
        if exponent == 0 {
            assert!(audit.axioms().is_empty());
        }
        else {
            assert_eq!(audit.axioms(), &[admitted.multiplication.position()]);
        }
        for input in 0_usize ..= 5 {
            let expected = Natural(input.checked_pow(u32::try_from(exponent).unwrap()).unwrap());
            assert_eq!(residual.execute(Natural(input)), Ok(expected));
            assert_eq!(
                admitted_result(&environment, admitted, Natural(input)),
                expected
            );
        }
        if exponent > 1 {
            assert_eq!(
                residual.execute(Natural(usize::MAX)),
                Err(StageError::Overflow)
            );
        }
    }
}

#[test]
fn unreplayed_and_open_residuals_are_refused()
{
    let mut arena = Arena::default();
    let model = Model(0);
    let token = arena.alloc_type(Type::In(model)).unwrap();
    let nat = arena.alloc_type(Type::Nat(Stage::Inner(model))).unwrap();
    let outer_variable = arena.alloc(Term::Variable(Index(1))).unwrap();
    let lambda = arena.alloc(Term::Lambda(nat, outer_variable)).unwrap();
    let quoted = arena.alloc(Term::Quote(lambda)).unwrap();
    let certificate = Certificate {
        source: quoted,
        target: quoted,
        steps: Vec::new(),
    };
    assert_eq!(
        compile(&mut arena, &[token, nat], &certificate, &mut Budget(1000)),
        Err(StageError::NotResidual)
    );
    let pow = power(&mut arena, model).unwrap();
    let exponent = arena
        .alloc(Term::Natural(Stage::Outer, Natural(2)))
        .unwrap();
    let source = arena.alloc(Term::Apply(pow, exponent)).unwrap();
    let input = arena.alloc(Term::Variable(Index(0))).unwrap();
    let input = arena.alloc(Term::Quote(input)).unwrap();
    let source = arena.alloc(Term::Apply(source, input)).unwrap();
    let source = arena.alloc(Term::Splice(source)).unwrap();
    let source = arena.alloc(Term::Lambda(nat, source)).unwrap();
    let source = arena.alloc(Term::Quote(source)).unwrap();
    let mut certificate = normalize(&mut arena, source, &mut Budget(100_000)).unwrap();
    certificate.steps.clear();
    assert_eq!(
        compile(&mut arena, &[token], &certificate, &mut Budget(100_000)),
        Err(StageError::InvalidCertificate)
    );
    assert_eq!(
        compile(&mut arena, &[], &certificate, &mut Budget(100_000)),
        Err(StageError::MissingHypothesis(model))
    );
}
