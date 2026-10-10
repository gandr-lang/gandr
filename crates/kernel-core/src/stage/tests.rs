//! Kernel-only adversarial witnesses for stage formation and replay.

use gandr_kernel_term::stage::Index;
use gandr_kernel_term::stage::Step;

use super::*;

#[test]
fn hypotheses_and_universe_boundary()
{
    let mut arena = Arena::default();
    let model = Model(0);
    let token = arena.alloc_type(Type::In(model)).unwrap();
    let wrong = arena.alloc_type(Type::In(Model(1))).unwrap();
    let inner = arena.alloc_type(Type::Nat(Stage::Inner(model))).unwrap();
    let outer = arena.alloc_type(Type::Nat(Stage::Outer)).unwrap();
    assert_eq!(
        form(&arena, &[], inner, &mut Budget(100)),
        Err(StageError::MissingHypothesis(model))
    );
    assert_eq!(
        form(&arena, &[wrong], inner, &mut Budget(100)),
        Err(StageError::MissingHypothesis(model))
    );
    assert_eq!(
        form(&arena, &[token, token], inner, &mut Budget(100)),
        Ok(Stage::Inner(model))
    );
    let lift = arena.alloc_type(Type::Lift(inner)).unwrap();
    let nested = arena.alloc_type(Type::Lift(lift)).unwrap();
    assert_eq!(
        form(&arena, &[token], nested, &mut Budget(100)),
        Err(StageError::StageMismatch)
    );
    let crossed = arena.alloc_type(Type::Arrow(inner, outer)).unwrap();
    assert_eq!(
        form(&arena, &[token], crossed, &mut Budget(100)),
        Err(StageError::StageMismatch)
    );
    let code = arena.alloc(Term::Code(inner)).unwrap();
    let universe = arena.alloc_type(Type::Universe(model)).unwrap();
    assert_eq!(
        infer(&mut arena, &[token], code, &mut Budget(100)),
        Ok(universe)
    );
    let self_code = arena.alloc(Term::Code(universe)).unwrap();
    assert_eq!(
        infer(&mut arena, &[token], self_code, &mut Budget(100)),
        Err(StageError::TypeMismatch)
    );
    let large_arrow = arena.alloc_type(Type::Arrow(universe, inner)).unwrap();
    let large_code = arena.alloc(Term::Code(large_arrow)).unwrap();
    assert_eq!(
        infer(&mut arena, &[token], large_code, &mut Budget(100)),
        Err(StageError::TypeMismatch)
    );
    let escape = arena.alloc(Term::Eliminate(code, outer)).unwrap();
    assert_eq!(
        infer(&mut arena, &[token], escape, &mut Budget(100)),
        Err(StageError::InnerToOuter)
    );
    let permitted = arena.alloc(Term::Eliminate(code, universe)).unwrap();
    assert_eq!(
        infer(&mut arena, &[token], permitted, &mut Budget(100)),
        Ok(universe)
    );
    let count = arena
        .alloc(Term::Natural(Stage::Inner(model), Natural(1)))
        .unwrap();
    let zero = arena
        .alloc(Term::Natural(Stage::Outer, Natural(0)))
        .unwrap();
    let variable = arena.alloc(Term::Variable(Index(0))).unwrap();
    let step = arena.alloc(Term::Lambda(outer, variable)).unwrap();
    let escape = arena.alloc(Term::Iterate(count, zero, step)).unwrap();
    assert_eq!(
        infer(&mut arena, &[token], escape, &mut Budget(1000)),
        Err(StageError::InnerToOuter)
    );
    assert_eq!(
        infer(&mut arena, &[], variable, &mut Budget(100)),
        Err(StageError::Unbound(Index(0)))
    );
}

#[test]
fn conversion_round_trips()
{
    let mut arena = Arena::default();
    let token = arena.alloc_type(Type::In(Model(0))).unwrap();
    let inner = arena.alloc_type(Type::Nat(Stage::Inner(Model(0)))).unwrap();
    let lifted = arena.alloc_type(Type::Lift(inner)).unwrap();
    let variable = arena.alloc(Term::Variable(Index(0))).unwrap();
    let quote = arena.alloc(Term::Quote(variable)).unwrap();
    let splice_quote = arena.alloc(Term::Splice(quote)).unwrap();
    let first = Certificate {
        source: splice_quote,
        target: variable,
        steps: Vec::from([Step {
            source: splice_quote,
            target: variable,
            rule: Rule::SpliceQuote,
        }]),
    };
    assert_eq!(
        replay(&mut arena, &[token, inner], &first, &mut Budget(1000)),
        Ok(inner)
    );
    let splice = arena.alloc(Term::Splice(variable)).unwrap();
    let quote_splice = arena.alloc(Term::Quote(splice)).unwrap();
    let second = Certificate {
        source: quote_splice,
        target: variable,
        steps: Vec::from([Step {
            source: quote_splice,
            target: variable,
            rule: Rule::QuoteSplice,
        }]),
    };
    assert_eq!(
        replay(&mut arena, &[token, lifted], &second, &mut Budget(1000)),
        Ok(lifted)
    );
}

#[test]
fn certificate_tampering_is_refused()
{
    let mut arena = Arena::default();
    let token = arena.alloc_type(Type::In(Model(0))).unwrap();
    let one = arena
        .alloc(Term::Natural(Stage::Inner(Model(0)), Natural(1)))
        .unwrap();
    let two = arena
        .alloc(Term::Natural(Stage::Inner(Model(0)), Natural(2)))
        .unwrap();
    let quoted = arena.alloc(Term::Quote(one)).unwrap();
    let source = arena.alloc(Term::Splice(quoted)).unwrap();
    let mut certificate = Certificate {
        source,
        target: one,
        steps: Vec::from([Step {
            source,
            target: one,
            rule: Rule::SpliceQuote,
        }]),
    };
    assert!(replay(&mut arena, &[token], &certificate, &mut Budget(1000)).is_ok());
    certificate.target = two;
    assert_eq!(
        replay(&mut arena, &[token], &certificate, &mut Budget(1000)),
        Err(StageError::InvalidCertificate)
    );
    certificate.steps.first_mut().unwrap().target = two;
    assert_eq!(
        replay(&mut arena, &[token], &certificate, &mut Budget(1000)),
        Err(StageError::InvalidCertificate)
    );
    certificate.target = one;
    certificate.steps.first_mut().unwrap().target = one;
    certificate.steps.first_mut().unwrap().rule = Rule::QuoteSplice;
    assert_eq!(
        replay(&mut arena, &[token], &certificate, &mut Budget(1000)),
        Err(StageError::InvalidCertificate)
    );
    certificate.steps.clear();
    assert_eq!(
        replay(&mut arena, &[token], &certificate, &mut Budget(1000)),
        Err(StageError::InvalidCertificate)
    );
    assert_eq!(
        replay(&mut arena, &[token], &certificate, &mut Budget(0)),
        Err(StageError::Exhausted)
    );
}
