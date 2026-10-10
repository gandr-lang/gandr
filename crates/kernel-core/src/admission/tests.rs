//! Differential and adversarial witnesses for compressed local judgments.

use super::*;

/// A two-arm cancellation schema with one repeated point.
///
/// # Specification
/// trivial.
fn cancellation() -> Proposal
{
    Proposal {
        classifiers: Vec::new(),
        nodes: Vec::from([
            Node::Rigid(Term::Natural(Stage::Outer, Natural(2))),
            Node::Rigid(Term::Natural(Stage::Outer, Natural(3))),
            Node::Point(Point(0)),
            Node::Rigid(Term::Quote(TermId(2))),
            Node::Rigid(Term::Splice(TermId(3))),
        ]),
        equation: Step {
            source: TermId(4),
            target: TermId(2),
            rule: Rule::SpliceQuote,
        },
        arms: Vec::from([Vec::from([TermId(0), TermId(1)])]),
    }
}

#[test]
fn schema_and_instance_refusals()
{
    let schema = Schema::check(cancellation(), &mut Budget(10_000)).unwrap();
    assert_eq!(schema.work().0, Work(2));
    assert_eq!(schema.work().2, Work(2));
    for guard in 0_usize .. 2 {
        let choices = [Choice {
            point: Point(0),
            guard: Guard(guard),
        }];
        let row = schema.substitute(schema.classifiers(), &choices).unwrap();
        let mut arena = Arena::default();
        let body = arena
            .alloc(Term::Natural(
                Stage::Outer,
                Natural(guard.saturating_add(2)),
            ))
            .unwrap();
        let quote = arena.alloc(Term::Quote(body)).unwrap();
        let source = arena.alloc(Term::Splice(quote)).unwrap();
        let step = Step {
            source,
            target: body,
            rule: Rule::SpliceQuote,
        };
        let wrong = arena
            .alloc(Term::Natural(Stage::Outer, Natural(10)))
            .unwrap();
        let mut consumer = schema.bind(arena.clone(), &mut Budget(10_000)).unwrap();
        let observation = row.admit(&mut consumer, step, &mut Budget(10_000)).unwrap();
        assert_eq!(observation.choices, Work(1));
        assert_eq!(observation.comparisons, Work(0));
        let endpoint = arena
            .alloc(Term::Natural(Stage::Outer, Natural(0)))
            .unwrap();
        let certificate = Certificate {
            source: endpoint,
            target: endpoint,
            steps: Vec::from([step]),
        };
        assert!(crate::stage::replay(&mut arena, &[], &certificate, &mut Budget(10_000)).is_ok());
        assert_eq!(
            row.admit(
                &mut consumer,
                Step {
                    target: wrong,
                    ..step
                },
                &mut Budget(10_000)
            ),
            Err(Refusal::SidesMismatch)
        );
    }
    assert!(matches!(
        schema.substitute(schema.classifiers(), &[]),
        Err(Refusal::MissingPoint(Point(0)))
    ));
    assert!(matches!(
        schema.substitute(schema.classifiers(), &[Choice {
            point: Point(0),
            guard: Guard(2)
        }]),
        Err(Refusal::UnknownArm(Point(0)))
    ));
    assert!(matches!(
        schema.substitute(schema.classifiers(), &[Choice {
            point: Point(1),
            guard: Guard(0)
        }]),
        Err(Refusal::UnknownArm(Point(1)))
    ));
    let choices = [
        Choice {
            point: Point(0),
            guard: Guard(0),
        },
        Choice {
            point: Point(0),
            guard: Guard(1),
        },
    ];
    assert!(matches!(
        schema.substitute(schema.classifiers(), &choices),
        Err(Refusal::Correlation(Point(0)))
    ));
    assert!(matches!(
        schema.substitute(&[Type::Nat(Stage::Outer)], &choices),
        Err(Refusal::ClassifierMismatch)
    ));
    let mut corrupt = cancellation();
    corrupt.equation.target = TermId(0);
    assert!(matches!(
        Schema::check(corrupt, &mut Budget(10_000)),
        Err(Refusal::CorruptStep)
    ));
    let mut corrupt = cancellation();
    corrupt.equation.rule = Rule::QuoteSplice;
    assert!(matches!(
        Schema::check(corrupt, &mut Budget(10_000)),
        Err(Refusal::Transparency)
    ));
    let mut malformed = cancellation();
    malformed.nodes.push(Node::Rigid(Term::Quote(TermId(100))));
    assert!(matches!(
        Schema::check(malformed, &mut Budget(10_000)),
        Err(Refusal::Malformed)
    ));
}

/// Successor schema whose count point controls both sides.
///
/// # Specification
/// trivial.
fn successor() -> Proposal
{
    Proposal {
        classifiers: Vec::from([Type::Nat(Stage::Outer)]),
        nodes: Vec::from([
            Node::Rigid(Term::Natural(Stage::Outer, Natural(1))),
            Node::Rigid(Term::Natural(Stage::Outer, Natural(2))),
            Node::Rigid(Term::Variable(gandr_kernel_term::stage::Index(0))),
            Node::Rigid(Term::Lambda(TypeId(0), TermId(2))),
            Node::Point(Point(0)),
            Node::Predecessor(Point(0)),
            Node::Rigid(Term::Iterate(TermId(4), TermId(0), TermId(3))),
            Node::Rigid(Term::Iterate(TermId(5), TermId(0), TermId(3))),
            Node::Rigid(Term::Apply(TermId(3), TermId(7))),
        ]),
        equation: Step {
            source: TermId(6),
            target: TermId(8),
            rule: Rule::IterateSuccessor,
        },
        arms: Vec::from([Vec::from([TermId(0), TermId(1)])]),
    }
}

#[test]
fn successor_and_transparency()
{
    let schema = Schema::check(successor(), &mut Budget(10_000)).unwrap();
    for guard in 0_usize .. 2 {
        let choice = Choice {
            point: Point(0),
            guard: Guard(guard),
        };
        let row = schema.substitute(schema.classifiers(), &[choice]).unwrap();
        let (mut arena, step) = schema
            .probe(
                &BTreeMap::from([(Point(0), TermId(guard))]),
                &mut Budget(10_000),
            )
            .unwrap();
        let mut consumer = schema.bind(arena.clone(), &mut Budget(10_000)).unwrap();
        assert!(row.admit(&mut consumer, step, &mut Budget(10_000)).is_ok());
        let certificate = Certificate {
            source: step.source,
            target: step.target,
            steps: Vec::from([step]),
        };
        assert_eq!(
            crate::stage::replay(&mut arena, &[], &certificate, &mut Budget(10_000)),
            Ok(TypeId(0))
        );
    }
    let mut flipped = successor();
    flipped.nodes[1] = Node::Rigid(Term::Natural(Stage::Outer, Natural(0)));
    assert!(matches!(
        Schema::check(flipped, &mut Budget(10_000)),
        Err(Refusal::Transparency)
    ));
    let (mut arena, positive) = schema
        .probe(
            &BTreeMap::from([(Point(0), TermId(0))]),
            &mut Budget(10_000),
        )
        .unwrap();
    let Term::Iterate(_, initial, function) = arena.term(positive.source).unwrap()
    else {
        panic!("successor source must be an iterator");
    };
    let zero = arena
        .alloc(Term::Natural(Stage::Outer, Natural(0)))
        .unwrap();
    let source = arena.alloc(Term::Iterate(zero, initial, function)).unwrap();
    let mut certificate = Certificate {
        source,
        target: initial,
        steps: Vec::from([Step {
            source,
            target: initial,
            rule: Rule::IterateZero,
        }]),
    };
    assert_eq!(
        crate::stage::replay(&mut arena, &[], &certificate, &mut Budget(10_000)),
        Ok(TypeId(0))
    );
    certificate.steps[0].rule = Rule::IterateSuccessor;
    assert_eq!(
        crate::stage::replay(&mut arena, &[], &certificate, &mut Budget(10_000)),
        Err(StageError::InvalidCertificate)
    );
    let mut corrupt = successor();
    corrupt.equation.target = TermId(0);
    assert!(matches!(
        Schema::check(corrupt, &mut Budget(10_000)),
        Err(Refusal::CorruptStep)
    ));
}

#[test]
fn classifier_coordinates_are_not_content()
{
    let proposal = Proposal {
        classifiers: Vec::from([Type::Nat(Stage::Outer)]),
        nodes: Vec::from([
            Node::Rigid(Term::Code(TypeId(0))),
            Node::Rigid(Term::Quote(TermId(0))),
            Node::Rigid(Term::Splice(TermId(1))),
        ]),
        equation: Step {
            source: TermId(2),
            target: TermId(0),
            rule: Rule::SpliceQuote,
        },
        arms: Vec::new(),
    };
    let schema = Schema::check(proposal, &mut Budget(10_000)).unwrap();
    let row = schema.substitute(schema.classifiers(), &[]).unwrap();
    let mut arena = Arena::default();
    let ty = arena.alloc_type(Type::In(Model(0))).unwrap();
    let body = arena.alloc(Term::Code(ty)).unwrap();
    let quote = arena.alloc(Term::Quote(body)).unwrap();
    let source = arena.alloc(Term::Splice(quote)).unwrap();
    let mut consumer = schema.bind(arena, &mut Budget(10_000)).unwrap();
    assert_eq!(
        row.admit(
            &mut consumer,
            Step {
                source,
                target: body,
                rule: Rule::SpliceQuote
            },
            &mut Budget(10_000)
        ),
        Err(Refusal::SidesMismatch)
    );
}

#[test]
fn bound_arenas_preserve_exactness_and_recovery()
{
    let schema = Schema::check(cancellation(), &mut Budget(10_000)).unwrap();
    let other = Schema::check(cancellation(), &mut Budget(10_000)).unwrap();
    let mut arena = Arena::default();
    // Shift all coordinates away from the schema's numbering.
    arena
        .alloc(Term::Natural(Stage::Outer, Natural(99)))
        .unwrap();
    let steps: Vec<_> = [Natural(2), Natural(3)]
        .into_iter()
        .map(|value| {
            let target = arena.alloc(Term::Natural(Stage::Outer, value)).unwrap();
            let quote = arena.alloc(Term::Quote(target)).unwrap();
            let source = arena.alloc(Term::Splice(quote)).unwrap();
            Step {
                source,
                target,
                rule: Rule::SpliceQuote,
            }
        })
        .collect();
    let mut consumer = schema.bind(arena.clone(), &mut Budget(10_000)).unwrap();
    let mut foreign = other.bind(arena, &mut Budget(10_000)).unwrap();
    for (guard, step) in steps.iter().enumerate() {
        let row = schema
            .substitute(schema.classifiers(), &[Choice {
                point: Point(0),
                guard: Guard(guard),
            }])
            .unwrap();
        let observed = row.admit(&mut consumer, *step, &mut Budget(100)).unwrap();
        assert_eq!(observed.comparisons, Work(0));
        assert_eq!(observed.classifiers, Work(0));
        assert_eq!(observed.instantiations, Work(2));
        assert_eq!(
            row.admit(&mut foreign, *step, &mut Budget(100)),
            Err(Refusal::Malformed)
        );
        let wrong = steps[guard.wrapping_add(1) % 2];
        assert_eq!(
            row.admit(&mut consumer, wrong, &mut Budget(100)),
            Err(Refusal::SidesMismatch)
        );
        let other_row = schema
            .substitute(schema.classifiers(), &[Choice {
                point: Point(0),
                guard: Guard(guard.wrapping_add(1) % 2),
            }])
            .unwrap();
        assert_eq!(
            other_row.admit(&mut consumer, wrong, &mut Budget(3)),
            Err(Refusal::Syntax(StageError::Exhausted))
        );
        assert_eq!(
            row.admit(&mut consumer, *step, &mut Budget(100)),
            Ok(observed)
        );
        assert_eq!(
            row.admit(&mut consumer.clone(), *step, &mut Budget(100)),
            Ok(observed)
        );
    }
    // A caller cannot name a future root that instantiation would make live.
    let mut prefix = Arena::default();
    let target = prefix
        .alloc(Term::Natural(Stage::Outer, Natural(2)))
        .unwrap();
    prefix
        .alloc(Term::Natural(Stage::Outer, Natural(3)))
        .unwrap();
    let mut future = prefix.clone();
    let quote = future.alloc(Term::Quote(target)).unwrap();
    let source = future.alloc(Term::Splice(quote)).unwrap();
    let mut consumer = schema.bind(prefix, &mut Budget(10_000)).unwrap();
    let row = schema
        .substitute(schema.classifiers(), &[Choice {
            point: Point(0),
            guard: Guard(0),
        }])
        .unwrap();
    assert_eq!(
        row.admit(
            &mut consumer,
            Step {
                source,
                target,
                rule: Rule::SpliceQuote
            },
            &mut Budget(100)
        ),
        Err(Refusal::Syntax(StageError::UnknownTerm(source)))
    );
}

#[test]
fn schema_work_is_bounded_by_input()
{
    let mut proposal = cancellation();
    proposal.arms[0].clear();
    for value in 1000_usize .. 1256 {
        let id = TermId(proposal.nodes.len());
        proposal
            .nodes
            .push(Node::Rigid(Term::Natural(Stage::Outer, Natural(value))));
        proposal.arms[0].push(id);
    }
    let mut body = TermId(2);
    for _ in 0_usize .. 256 {
        let id = TermId(proposal.nodes.len());
        proposal
            .nodes
            .push(Node::Rigid(Term::Multiply(body, TermId(2))));
        body = id;
    }
    let quote = TermId(proposal.nodes.len());
    proposal.nodes.push(Node::Rigid(Term::Quote(body)));
    let source = TermId(proposal.nodes.len());
    proposal.nodes.push(Node::Rigid(Term::Splice(quote)));
    proposal.equation = Step {
        source,
        target: body,
        rule: Rule::SpliceQuote,
    };
    assert!(matches!(
        Schema::check(proposal, &mut Budget(10_000_000)),
        Err(Refusal::SchemaWorkBound)
    ));
    assert!(matches!(
        Schema::check(cancellation(), &mut Budget(0)),
        Err(Refusal::Syntax(StageError::Exhausted))
    ));
}

#[test]
fn affected_constructors_measure_fanout_not_depth()
{
    for width in [8_usize, 32] {
        let mut proposal = cancellation();
        let mut level = Vec::new();
        for offset in 0 .. width {
            let literal = TermId(proposal.nodes.len());
            proposal.nodes.push(Node::Rigid(Term::Natural(
                Stage::Outer,
                Natural(offset.saturating_add(100)),
            )));
            let branch = TermId(proposal.nodes.len());
            proposal
                .nodes
                .push(Node::Rigid(Term::Multiply(TermId(2), literal)));
            level.push(branch);
        }
        while level.len() > 1 {
            let mut next = Vec::new();
            for pair in level.chunks(2) {
                let &[a, b] = pair
                else {
                    panic!("power-of-two width");
                };
                let id = TermId(proposal.nodes.len());
                proposal.nodes.push(Node::Rigid(Term::Multiply(a, b)));
                next.push(id);
            }
            level = next;
        }
        let body = level[0];
        let quote = TermId(proposal.nodes.len());
        proposal.nodes.push(Node::Rigid(Term::Quote(body)));
        let source = TermId(proposal.nodes.len());
        proposal.nodes.push(Node::Rigid(Term::Splice(quote)));
        proposal.equation = Step {
            source,
            target: body,
            rule: Rule::SpliceQuote,
        };
        let schema = Schema::check(proposal, &mut Budget(1_000_000)).unwrap();
        let affected = Work(width.saturating_mul(2).saturating_add(1));
        assert_eq!(schema.work().2, affected);
        let choices = [Choice {
            point: Point(0),
            guard: Guard(0),
        }];
        let row = schema.substitute(schema.classifiers(), &choices).unwrap();
        let (arena, step) = schema
            .probe(
                &BTreeMap::from([(Point(0), TermId(0))]),
                &mut Budget(100_000),
            )
            .unwrap();
        let mut consumer = schema.bind(arena, &mut Budget(100_000)).unwrap();
        assert_eq!(
            row.admit(&mut consumer, step, &mut Budget(100_000))
                .unwrap()
                .instantiations,
            affected
        );
    }
}

#[test]
fn thread_counts_preserve_valid_and_poisoned_rows()
{
    extern crate std;
    let schema = Schema::check(cancellation(), &mut Budget(10_000)).unwrap();
    let selections = [
        Guard(0),
        Guard(1),
        Guard(2),
        Guard(0),
        Guard(2),
        Guard(1),
        Guard(0),
        Guard(1),
    ];
    let expected = selections.map(|guard| {
        if guard.0 < 2 {
            Ok(())
        }
        else {
            Err(Refusal::UnknownArm(Point(0)))
        }
    });
    for threads in [1_usize, 2, 4, 8] {
        let actual = std::thread::scope(|scope| {
            let handles: Vec<_> = selections
                .chunks(selections.len().div_ceil(threads))
                .map(|chunk| {
                    let schema = &schema;
                    scope.spawn(move || {
                        chunk
                            .iter()
                            .map(|guard| {
                                schema
                                    .substitute(schema.classifiers(), &[Choice {
                                        point: Point(0),
                                        guard: *guard,
                                    }])
                                    .map(|_| ())
                            })
                            .collect::<Vec<_>>()
                    })
                })
                .collect();
            let mut actual = Vec::new();
            for handle in handles {
                actual.extend(handle.join().unwrap());
            }
            actual
        });
        assert_eq!(actual, expected);
    }
}
