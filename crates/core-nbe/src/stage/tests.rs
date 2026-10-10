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
    let lifted_nat = arena.alloc_type(Type::Lift(inner)).unwrap();
    let meta_function = arena
        .alloc_type(Type::Arrow(lifted_nat, lifted_nat))
        .unwrap();
    let outer = arena.alloc_type(Type::Nat(Stage::Outer)).unwrap();
    let signature = arena.alloc_type(Type::Arrow(outer, meta_function)).unwrap();
    assert_eq!(
        infer(&mut arena, &[token], program, &mut Budget(100_000)),
        Ok(signature)
    );
    for exponent in 0_usize ..= 8 {
        let numeral = arena
            .alloc(Term::Natural(Stage::Outer, Natural(exponent)))
            .unwrap();
        let source = arena.alloc(Term::Apply(program, numeral)).unwrap();
        let input = arena.alloc(Term::Variable(Index(0))).unwrap();
        let input = arena.alloc(Term::Quote(input)).unwrap();
        let source = arena.alloc(Term::Apply(source, input)).unwrap();
        let source = arena.alloc(Term::Splice(source)).unwrap();
        let source = arena.alloc(Term::Lambda(inner, source)).unwrap();
        let source = arena.alloc(Term::Quote(source)).unwrap();
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

#[test]
fn object_computations_remain_residual()
{
    let mut arena = Arena::default();
    let model = Model(0);
    let token = arena.alloc_type(Type::In(model)).unwrap();
    let inner = arena.alloc_type(Type::Nat(Stage::Inner(model))).unwrap();
    let outer = arena.alloc_type(Type::Nat(Stage::Outer)).unwrap();
    let universe = arena.alloc_type(Type::Universe(model)).unwrap();
    let lifted = arena.alloc_type(Type::Lift(inner)).unwrap();
    let object_function = arena.alloc_type(Type::Arrow(inner, inner)).unwrap();
    let meta_function = arena.alloc_type(Type::Arrow(lifted, lifted)).unwrap();
    let variable = arena.alloc(Term::Variable(Index(0))).unwrap();
    for (domain, stage) in [
        (token, Stage::Outer),
        (outer, Stage::Outer),
        (lifted, Stage::Outer),
        (meta_function, Stage::Outer),
        (inner, Stage::Inner(model)),
        (universe, Stage::Inner(model)),
        (object_function, Stage::Inner(model)),
    ] {
        let identity = arena.alloc(Term::Lambda(domain, variable)).unwrap();
        let applied = arena.alloc(Term::Apply(identity, variable)).unwrap();
        let certificate = normalize(&mut arena, applied, &mut Budget(1000)).unwrap();
        let expected = if stage == Stage::Outer {
            variable
        }
        else {
            applied
        };
        assert_eq!(certificate.target, expected);
        assert_eq!(
            replay(
                &mut arena,
                &[token, domain],
                &certificate,
                &mut Budget(1000)
            ),
            Ok(domain)
        );
    }
    // Object beta would duplicate the argument computation and erase sharing.
    let square = arena.alloc(Term::Multiply(variable, variable)).unwrap();
    let lambda = arena.alloc(Term::Lambda(inner, square)).unwrap();
    let application = arena.alloc(Term::Apply(lambda, square)).unwrap();
    let quoted = arena.alloc(Term::Quote(application)).unwrap();
    let certificate = normalize(&mut arena, quoted, &mut Budget(1000)).unwrap();
    assert_eq!(certificate.target, quoted);
    assert_eq!(
        replay(&mut arena, &[token, inner], &certificate, &mut Budget(1000)),
        Ok(lifted)
    );
    for (stage, domain) in [(Stage::Outer, outer), (Stage::Inner(model), inner)] {
        let one = arena.alloc(Term::Natural(stage, Natural(1))).unwrap();
        let identity = arena.alloc(Term::Lambda(domain, variable)).unwrap();
        let elimination = arena.alloc(Term::Eliminate(one, domain)).unwrap();
        let certificate = normalize(&mut arena, elimination, &mut Budget(1000)).unwrap();
        let expected = if stage == Stage::Outer {
            one
        }
        else {
            elimination
        };
        assert_eq!(certificate.target, expected);
        assert_eq!(
            replay(&mut arena, &[token], &certificate, &mut Budget(1000)),
            Ok(domain)
        );
        for count in 0 ..= 2 {
            let count = arena.alloc(Term::Natural(stage, Natural(count))).unwrap();
            let iteration = arena.alloc(Term::Iterate(count, one, identity)).unwrap();
            let certificate = normalize(&mut arena, iteration, &mut Budget(1000)).unwrap();
            let expected = if stage == Stage::Outer {
                one
            }
            else {
                iteration
            };
            assert_eq!(arena.term(certificate.target), arena.term(expected));
            assert_eq!(
                replay(&mut arena, &[token], &certificate, &mut Budget(1000)),
                Ok(domain)
            );
        }
    }
}

#[test]
fn function_accumulator_retains_object_redexes()
{
    let mut arena = Arena::default();
    let model = Model(0);
    let token = arena.alloc_type(Type::In(model)).unwrap();
    let outer = arena.alloc_type(Type::Nat(Stage::Outer)).unwrap();
    let inner = arena.alloc_type(Type::Nat(Stage::Inner(model))).unwrap();
    let function = arena.alloc_type(Type::Arrow(inner, inner)).unwrap();
    let lifted = arena.alloc_type(Type::Lift(function)).unwrap();
    let one = arena
        .alloc(Term::Natural(Stage::Inner(model), Natural(1)))
        .unwrap();
    let initial = arena.alloc(Term::Lambda(inner, one)).unwrap();
    let initial = arena.alloc(Term::Quote(initial)).unwrap();
    let input = arena.alloc(Term::Variable(Index(0))).unwrap();
    let previous = arena.alloc(Term::Variable(Index(1))).unwrap();
    let previous = arena.alloc(Term::Splice(previous)).unwrap();
    let applied = arena.alloc(Term::Apply(previous, input)).unwrap();
    let product = arena.alloc(Term::Multiply(input, applied)).unwrap();
    let body = arena.alloc(Term::Lambda(inner, product)).unwrap();
    let body = arena.alloc(Term::Quote(body)).unwrap();
    let step = arena.alloc(Term::Lambda(lifted, body)).unwrap();
    let exponent = arena.alloc(Term::Variable(Index(0))).unwrap();
    let body = arena.alloc(Term::Iterate(exponent, initial, step)).unwrap();
    let program = arena.alloc(Term::Lambda(outer, body)).unwrap();
    for exponent in 0_usize ..= 8 {
        let numeral = arena
            .alloc(Term::Natural(Stage::Outer, Natural(exponent)))
            .unwrap();
        let source = arena.alloc(Term::Apply(program, numeral)).unwrap();
        let certificate = normalize(&mut arena, source, &mut Budget(1_000_000)).unwrap();
        assert_eq!(
            replay(&mut arena, &[token], &certificate, &mut Budget(1_000_000)),
            Ok(lifted)
        );
        let Term::Quote(mut function) = arena.term(certificate.target).unwrap()
        else {
            panic!("quoted function");
        };
        // Read the residual recurrence itself, not the producer's rule tags.
        for _ in 0 .. exponent {
            let Term::Lambda(domain, body) = arena.term(function).unwrap()
            else {
                panic!("object lambda");
            };
            assert_eq!(domain, inner);
            let Term::Multiply(left, right) = arena.term(body).unwrap()
            else {
                panic!("object multiplication");
            };
            assert_eq!(arena.term(left), Ok(Term::Variable(Index(0))));
            let Term::Apply(previous, argument) = arena.term(right).unwrap()
            else {
                panic!("object redex must survive strict staging");
            };
            assert_eq!(arena.term(argument), Ok(Term::Variable(Index(0))));
            function = previous;
        }
        let Term::Lambda(domain, body) = arena.term(function).unwrap()
        else {
            panic!("base object lambda");
        };
        assert_eq!(domain, inner);
        assert_eq!(
            arena.term(body),
            Ok(Term::Natural(Stage::Inner(model), Natural(1)))
        );
    }
}

#[test]
fn malformed_sources_and_classifier_budgets_are_refused()
{
    let mut arena = Arena::default();
    let absent = TermId(usize::MAX);
    assert_eq!(
        normalize(&mut arena, absent, &mut Budget(100)),
        Err(StageError::UnknownTerm(absent))
    );
    let absent = TypeId(usize::MAX);
    assert_eq!(
        classifier_stage(&arena, absent, &mut Budget(100)),
        Err(StageError::UnknownType(absent))
    );
    let outer = arena.alloc_type(Type::Nat(Stage::Outer)).unwrap();
    assert_eq!(
        classifier_stage(&arena, outer, &mut Budget(0)),
        Err(StageError::Exhausted)
    );
    let variable = arena.alloc(Term::Variable(Index(0))).unwrap();
    let head = arena.alloc(Term::Lambda(outer, variable)).unwrap();
    let application = arena.alloc(Term::Apply(head, variable)).unwrap();
    assert!(matches!(
        contract(&mut arena, application, &mut Budget(0)),
        Err(StageError::Exhausted)
    ));
}
