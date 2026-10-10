//! Differential and adversarial witnesses for compressed local judgments.

use alloc::collections::BTreeMap;

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

/// Intern `splice (quote n)` and return its cancellation equation.
///
/// # Specification
/// trivial.
fn cancelled(
    arena: &mut Arena,
    value: Natural,
) -> Step
{
    let target = arena.alloc(Term::Natural(Stage::Outer, value)).unwrap();
    let quote = arena.alloc(Term::Quote(target)).unwrap();
    let source = arena.alloc(Term::Splice(quote)).unwrap();
    Step {
        source,
        target,
        rule: Rule::SpliceQuote,
    }
}

/// The single choice selecting `guard` at point zero.
///
/// # Specification
/// trivial.
const fn only(guard: Guard) -> [Choice; 1]
{
    [Choice {
        point: Point(0),
        guard,
    }]
}

/// Reify one inheritance probe from scratch, as an independent reference for
/// the shared probe base: the bound point takes its arm, every other point and
/// predecessor a fresh rigid code.
///
/// # Specification
/// - ensures: both sides are live in the returned arena under the schema's
///   rule; only nodes reachable from the equation's sides are interned.
/// - fails: malformed syntax or staging allocation/refusal.
/// - panics: none.
///
/// # Errors
/// Returns `Refusal` for malformed predecessors or syntax.
///
/// # Adequacy
/// - hypothesis: L2 — the shared probe base must replay the step this
///   independent walk reifies for every binding.
/// - witness: `admission::tests::shared_base_replays_fresh_probes`
#[spec(
    captures: before = budget.0,
    ensures: |ret| budget.0 <= before && ret.as_ref().ok().is_none_or(|probed|
        probed.0.term(probed.1.source).is_ok()
        && probed.0.term(probed.1.target).is_ok()
        && probed.1.rule == schema.proposal.equation.rule),
)]
fn probe(
    schema: &Schema,
    bindings: &BTreeMap<Point, TermId>,
    budget: &mut Budget,
) -> Result<(Arena, Step), Refusal>
{
    budget.0 = budget
        .0
        .checked_sub(
            schema
                .proposal
                .classifiers
                .len()
                .saturating_add(schema.skolems.len()),
        )
        .ok_or(StageError::Exhausted)?;
    let mut arena = schema.vocabulary.clone();
    let mut known = BTreeMap::new();
    let mut pending = Vec::from([
        (schema.proposal.equation.source, false),
        (schema.proposal.equation.target, false),
    ]);
    while let Some((id, ready)) = pending.pop() {
        budget.spend()?;
        if known.contains_key(&id) {
            continue;
        }
        let term = match schema.proposal.node(id)? {
            | Node::Point(point) => {
                if let Some(arm) = bindings.get(&point) {
                    if let Some(value) = known.get(arm) {
                        known.insert(id, *value);
                    }
                    else {
                        pending.extend([(id, true), (*arm, false)]);
                    }
                    continue;
                }
                Term::Code(*schema.skolems.get(point.0).ok_or(Refusal::Malformed)?)
            },
            | Node::Predecessor(point) => {
                if let Some(arm) = bindings.get(&point) {
                    let Node::Rigid(Term::Natural(Stage::Outer, Natural(value))) =
                        schema.proposal.node(*arm)?
                    else {
                        return Err(Refusal::Malformed);
                    };
                    let value = value.checked_sub(1).ok_or(Refusal::Transparency)?;
                    Term::Natural(Stage::Outer, Natural(value))
                }
                else {
                    let skolem = point.0.saturating_add(schema.proposal.arms.len());
                    Term::Code(*schema.skolems.get(skolem).ok_or(Refusal::Malformed)?)
                }
            },
            | Node::Rigid(term) => {
                if !ready {
                    pending.push((id, true));
                    pending.extend(
                        term.children()
                            .into_iter()
                            .flatten()
                            .map(|child| (child, false)),
                    );
                    continue;
                }
                let mut children = [Child::Vacant; 3];
                for (source, target) in term.children().into_iter().zip(&mut children) {
                    if let Child::Present(source) = source {
                        *target = Child::Present(*known.get(&source).ok_or(Refusal::Malformed)?);
                    }
                }
                term.rebuild(children)?
            },
        };
        known.insert(id, arena.alloc(term)?);
    }
    let side = |id: &TermId| known.get(id).copied().ok_or(Refusal::Malformed);
    let source = side(&schema.proposal.equation.source)?;
    let target = side(&schema.proposal.equation.target)?;
    Ok((arena, Step {
        source,
        target,
        rule: schema.proposal.equation.rule,
    }))
}

#[test]
fn schema_and_instance_refusals()
{
    let schema = Schema::check(cancellation(), &mut Budget(10_000)).unwrap();
    assert_eq!(schema.work().0, Work(2));
    assert_eq!(schema.work().2, Work(2));
    let mut buffer = Row::default();
    for guard in 0_usize .. 2 {
        let choices = only(Guard(guard));
        let mut arena = Arena::default();
        let step = cancelled(&mut arena, Natural(guard.saturating_add(2)));
        let wrong = arena
            .alloc(Term::Natural(Stage::Outer, Natural(10)))
            .unwrap();
        let consumer = schema.bind(arena.clone(), &mut Budget(10_000)).unwrap();
        let mut row = schema
            .substitute(schema.classifiers(), &choices, &mut buffer)
            .unwrap();
        let observation = row.admit(&consumer, step, &mut Budget(10_000)).unwrap();
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
                &consumer,
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
        schema.substitute(schema.classifiers(), &[], &mut buffer),
        Err(Refusal::MissingPoint(Point(0)))
    ));
    assert!(matches!(
        schema.substitute(schema.classifiers(), &only(Guard(2)), &mut buffer),
        Err(Refusal::UnknownArm(Point(0)))
    ));
    assert!(matches!(
        schema.substitute(
            schema.classifiers(),
            &[Choice {
                point: Point(1),
                guard: Guard(0)
            }],
            &mut buffer
        ),
        Err(Refusal::UnknownArm(Point(1)))
    ));
    let choices = [only(Guard(0)), only(Guard(1))].concat();
    assert!(matches!(
        schema.substitute(schema.classifiers(), &choices, &mut buffer),
        Err(Refusal::Correlation(Point(0)))
    ));
    assert!(matches!(
        schema.substitute(&[Type::Nat(Stage::Outer)], &choices, &mut buffer),
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
    let mut buffer = Row::default();
    for guard in 0_usize .. 2 {
        let choices = only(Guard(guard));
        let (mut arena, step) = probe(
            &schema,
            &BTreeMap::from([(Point(0), TermId(guard))]),
            &mut Budget(10_000),
        )
        .unwrap();
        let consumer = schema.bind(arena.clone(), &mut Budget(10_000)).unwrap();
        let mut row = schema
            .substitute(schema.classifiers(), &choices, &mut buffer)
            .unwrap();
        assert!(row.admit(&consumer, step, &mut Budget(10_000)).is_ok());
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
    let (mut arena, positive) = probe(
        &schema,
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
    let mut buffer = Row::default();
    let mut row = schema
        .substitute(schema.classifiers(), &[], &mut buffer)
        .unwrap();
    let mut arena = Arena::default();
    let ty = arena.alloc_type(Type::In(Model(0))).unwrap();
    let body = arena.alloc(Term::Code(ty)).unwrap();
    let quote = arena.alloc(Term::Quote(body)).unwrap();
    let source = arena.alloc(Term::Splice(quote)).unwrap();
    let consumer = schema.bind(arena, &mut Budget(10_000)).unwrap();
    assert_eq!(
        row.admit(
            &consumer,
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
    let steps = [Natural(2), Natural(3)].map(|value| cancelled(&mut arena, value));
    let consumer = schema.bind(arena.clone(), &mut Budget(10_000)).unwrap();
    let foreign = other.bind(arena, &mut Budget(10_000)).unwrap();
    let mut buffer = Row::default();
    let mut other_buffer = Row::default();
    for (guard, step) in steps.iter().enumerate() {
        let mut row = schema
            .substitute(schema.classifiers(), &only(Guard(guard)), &mut buffer)
            .unwrap();
        let observed = row.admit(&consumer, *step, &mut Budget(100)).unwrap();
        assert_eq!(observed.comparisons, Work(0));
        assert_eq!(observed.classifiers, Work(0));
        assert_eq!(observed.instantiations, Work(2));
        assert_eq!(
            row.admit(&foreign, *step, &mut Budget(100)),
            Err(Refusal::Malformed)
        );
        let wrong = steps[guard.wrapping_add(1) % 2];
        assert_eq!(
            row.admit(&consumer, wrong, &mut Budget(100)),
            Err(Refusal::SidesMismatch)
        );
        let mut other_row = schema
            .substitute(
                schema.classifiers(),
                &only(Guard(guard.wrapping_add(1) % 2)),
                &mut other_buffer,
            )
            .unwrap();
        assert_eq!(
            other_row.admit(&consumer, wrong, &mut Budget(3)),
            Err(Refusal::Syntax(StageError::Exhausted))
        );
        assert_eq!(row.admit(&consumer, *step, &mut Budget(100)), Ok(observed));
        assert_eq!(
            row.admit(&consumer.clone(), *step, &mut Budget(100)),
            Ok(observed)
        );
    }
    // A caller cannot name a root absent from the bound arena.
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
    let consumer = schema.bind(prefix, &mut Budget(10_000)).unwrap();
    let mut row = schema
        .substitute(schema.classifiers(), &only(Guard(0)), &mut buffer)
        .unwrap();
    assert_eq!(
        row.admit(
            &consumer,
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
fn rows_absent_from_the_binding_refuse()
{
    let schemas = [cancellation(), successor()]
        .map(|proposal| Schema::check(proposal, &mut Budget(10_000)).unwrap());
    // One row buffer serves both schemas and every row; a fresh buffer per
    // row is the reference that reuse must not perturb.
    let mut buffer = Row::default();
    for schema in &schemas {
        let (arena, step) = if schema.proposal.equation.rule == Rule::SpliceQuote {
            let mut arena = Arena::default();
            // Only the first arm's instance is interned.
            let step = cancelled(&mut arena, Natural(2));
            arena
                .alloc(Term::Natural(Stage::Outer, Natural(3)))
                .unwrap();
            (arena, step)
        }
        else {
            probe(
                schema,
                &BTreeMap::from([(Point(0), TermId(0))]),
                &mut Budget(10_000),
            )
            .unwrap()
        };
        let shared = schema.bind(arena, &mut Budget(10_000)).unwrap();
        for guard in 0_usize .. 2 {
            let reused = schema
                .substitute(schema.classifiers(), &only(Guard(guard)), &mut buffer)
                .unwrap()
                .admit(&shared, step, &mut Budget(10_000));
            let fresh = schema
                .substitute(
                    schema.classifiers(),
                    &only(Guard(guard)),
                    &mut Row::default(),
                )
                .unwrap()
                .admit(&shared, step, &mut Budget(10_000));
            assert_eq!(reused, fresh);
            if guard == 0 {
                assert!(reused.is_ok());
            }
            else {
                assert_eq!(reused, Err(Refusal::SidesMismatch));
            }
        }
    }
}

#[test]
fn shared_base_replays_fresh_probes()
{
    let mut ground = cancellation();
    ground.nodes[2] = Node::Rigid(Term::Natural(Stage::Outer, Natural(4)));
    ground.arms.clear();
    for proposal in [cancellation(), successor(), ground] {
        let shared = Schema::check(proposal.clone(), &mut Budget(10_000)).unwrap();
        let mut fresh = Schema::check(proposal, &mut Budget(10_000)).unwrap();
        fresh.checks = Work(0);
        fresh.replay_work = Work(0);
        let bindings: Vec<_> = if fresh.proposal.arms.is_empty() {
            Vec::from([BTreeMap::new()])
        }
        else {
            fresh
                .proposal
                .arms
                .iter()
                .enumerate()
                .flat_map(|(point, arms)| {
                    arms.iter()
                        .map(move |arm| BTreeMap::from([(Point(point), *arm)]))
                })
                .collect()
        };
        for binding in &bindings {
            let (arena, step) = probe(&fresh, binding, &mut Budget(10_000)).unwrap();
            fresh.discharge(arena, step, &mut Budget(10_000)).unwrap();
        }
        assert_eq!(shared.work(), fresh.work());
    }
    let mut corrupt = successor();
    corrupt.equation.target = TermId(0);
    assert_eq!(
        Schema::check(corrupt, &mut Budget(10_000)).map(|schema| schema.work()),
        Err(Refusal::CorruptStep)
    );
    let mut fresh = Schema::check(successor(), &mut Budget(10_000)).unwrap();
    fresh.proposal.equation.target = TermId(0);
    let (arena, step) = probe(
        &fresh,
        &BTreeMap::from([(Point(0), TermId(0))]),
        &mut Budget(10_000),
    )
    .unwrap();
    assert_eq!(
        fresh.discharge(arena, step, &mut Budget(10_000)),
        Err(Refusal::CorruptStep)
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
    let mut buffer = Row::default();
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
        let (arena, step) = probe(
            &schema,
            &BTreeMap::from([(Point(0), TermId(0))]),
            &mut Budget(100_000),
        )
        .unwrap();
        let consumer = schema.bind(arena, &mut Budget(100_000)).unwrap();
        let mut row = schema
            .substitute(schema.classifiers(), &only(Guard(0)), &mut buffer)
            .unwrap();
        assert_eq!(
            row.admit(&consumer, step, &mut Budget(100_000))
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
    let mut arena = Arena::default();
    let steps = [Natural(2), Natural(3)].map(|value| cancelled(&mut arena, value));
    let consumer = schema.bind(arena, &mut Budget(10_000)).unwrap();
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
            Ok(Work(2))
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
                    let consumer = &consumer;
                    let steps = &steps;
                    scope.spawn(move || {
                        let mut buffer = Row::default();
                        chunk
                            .iter()
                            .map(|guard| {
                                let choice = [Choice {
                                    point: Point(0),
                                    guard: *guard,
                                }];
                                let mut row = schema.substitute(
                                    schema.classifiers(),
                                    &choice,
                                    &mut buffer,
                                )?;
                                let step = steps[guard.0 % 2];
                                row.admit(consumer, step, &mut Budget(100))
                                    .map(|admission| admission.instantiations)
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
