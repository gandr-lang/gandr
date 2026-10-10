//! Independent observations of the staged power program and conversion traces.

use gandr_kernel_core::stage::infer;
use gandr_kernel_core::stage::replay;

use super::*;

#[test]
fn round_trips_replay()
{
    let mut arena = Arena::default();
    let model = Model(0);
    let token = arena.alloc_type(Type::In(model)).unwrap();
    let inner = arena.alloc_type(Type::Nat(Stage::Inner(model))).unwrap();
    let lifted = arena.alloc_type(Type::Lift(inner)).unwrap();
    let variable = arena.alloc(Term::Variable(Index(0))).unwrap();
    let quote = arena.alloc(Term::Quote(variable)).unwrap();
    let splice_quote = arena.alloc(Term::Splice(quote)).unwrap();
    let certificate = normalize(&mut arena, splice_quote, &mut Budget(1000)).unwrap();
    assert_eq!(certificate.target, variable);
    assert_eq!(
        replay(&mut arena, &[token, inner], &certificate, &mut Budget(1000)),
        Ok(inner)
    );
    let splice = arena.alloc(Term::Splice(variable)).unwrap();
    let quote_splice = arena.alloc(Term::Quote(splice)).unwrap();
    let certificate = normalize(&mut arena, quote_splice, &mut Budget(1000)).unwrap();
    assert_eq!(certificate.target, variable);
    assert_eq!(
        replay(
            &mut arena,
            &[token, lifted],
            &certificate,
            &mut Budget(1000)
        ),
        Ok(lifted)
    );
    assert_eq!(
        normalize(&mut arena, quote_splice, &mut Budget(0)),
        Err(StageError::Exhausted)
    );
}

#[test]
fn power_residualizes()
{
    let mut arena = Arena::default();
    let model = Model(0);
    let token = arena.alloc_type(Type::In(model)).unwrap();
    let program = power(&mut arena, model).unwrap();
    let inner = arena.alloc_type(Type::Nat(Stage::Inner(model))).unwrap();
    let function = arena.alloc_type(Type::Arrow(inner, inner)).unwrap();
    let lifted = arena.alloc_type(Type::Lift(function)).unwrap();
    let outer = arena.alloc_type(Type::Nat(Stage::Outer)).unwrap();
    let signature = arena.alloc_type(Type::Arrow(outer, lifted)).unwrap();
    assert_eq!(
        infer(&mut arena, &[token], program, &mut Budget(100_000)),
        Ok(signature)
    );
    for exponent in 0_usize ..= 8 {
        let numeral = arena
            .alloc(Term::Natural(Stage::Outer, Natural(exponent)))
            .unwrap();
        let source = arena.alloc(Term::Apply(program, numeral)).unwrap();
        let mut certificate = normalize(&mut arena, source, &mut Budget(1_000_000)).unwrap();
        assert_eq!(
            replay(&mut arena, &[token], &certificate, &mut Budget(1_000_000)),
            Ok(lifted)
        );
        let Term::Quote(lambda) = arena.term(certificate.target).unwrap()
        else {
            panic!("quoted residual");
        };
        let Term::Lambda(domain, body) = arena.term(lambda).unwrap()
        else {
            panic!("one top-level function");
        };
        assert_eq!(domain, inner);
        // The residual grammar admits no closure, application, splice,
        // iterator, or free variable other than the function's argument.
        let mut pending = Vec::from([body]);
        let mut multiplications = 0_usize;
        while let Some(term) = pending.pop() {
            match arena.term(term).unwrap() {
                | Term::Variable(Index(0)) | Term::Natural(Stage::Inner(Model(0)), Natural(1)) => {
                },
                | Term::Multiply(left, right) => {
                    multiplications += 1;
                    pending.push(left);
                    pending.push(right);
                },
                | other => panic!("non-first-order residual: {other:?}"),
            }
        }
        assert_eq!(multiplications, exponent);
        for input in 0_usize ..= 5 {
            let mut tasks = Vec::from([(body, false)]);
            let mut values = Vec::new();
            while let Some((term, ready)) = tasks.pop() {
                match arena.term(term).unwrap() {
                    | Term::Variable(Index(0)) => values.push(input),
                    | Term::Natural(_, Natural(value)) => values.push(value),
                    | Term::Multiply(left, right) if !ready => {
                        tasks.push((term, true));
                        tasks.push((right, false));
                        tasks.push((left, false));
                    },
                    | Term::Multiply(..) => {
                        let right = values.pop().unwrap();
                        let left = values.pop().unwrap();
                        values.push(left.checked_mul(right).unwrap());
                    },
                    | _ => panic!("residual grammar"),
                }
            }
            assert_eq!(
                values,
                Vec::from([input.checked_pow(u32::try_from(exponent).unwrap()).unwrap()])
            );
        }
        // Keeping the right endpoint while deleting its derivation cannot
        // turn a producer normal form into a kernel-certified one.
        certificate.steps.clear();
        assert_eq!(
            replay(&mut arena, &[token], &certificate, &mut Budget(1_000_000)),
            Err(StageError::InvalidCertificate)
        );
    }
}
