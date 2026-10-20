use alloc::boxed::Box;

use gandr_kernel_term::Component;
use gandr_kernel_term::Side;

use super::*;
use crate::il::CopatternArm;
use crate::il::PatternArm;
use crate::il::Route;

/// Mint the unit producer.
///
/// # Specification
/// trivial.
fn unit(arena: &mut CommandArena) -> ProducerId
{
    arena
        .mint_producer(ProducerNode::Constructor {
            tag: ConstructorTag::Tuple(ProducerArity::ZERO),
            producers: Box::from([]),
            consumers: Box::from([]),
        })
        .expect("a leaf mints")
}

/// Mint `★`.
///
/// # Specification
/// trivial.
fn top(arena: &mut CommandArena) -> ConsumerId
{
    arena
        .mint_consumer(ConsumerNode::Top)
        .expect("a leaf mints")
}

/// Build `⟨() |+ consumer⟩`, so a consumer under test is reached in its
/// ordinary position.
///
/// # Specification
/// - requires: the consumer's children resolve and the arena has room.
/// - ensures: a positive cut from a nullary unit to the supplied consumer.
/// - provides: the consumer in the checker's ordinary elimination position.
/// - panics: on a refused node or cut allocation.
///
/// # Adequacy
/// - hypothesis: L3 — scope, polarity and arity fixtures observe the requested
///   side of a positive cut. These distinguish the wrong wrapper polarity, an
///   incorrect terminal side and a replaced node kind. Only small arenas with
///   live child references are in the fixture domain.
/// - witness: `check::tests::scope_tracks_binders`
/// - witness: `check::tests::destructor_consumer_arity_is_checked`
/// - witness: `check::tests::a_head_answered_twice_is_rejected`
#[spec(
        captures: [kind = core::mem::discriminant(&consumer)],
        ensures: |ret| arena.command(ret).is_some_and(|node| match *node {
            | CommandNode::Cut { polarity, producer, consumer } => polarity == Polarity::Positive
                && arena.consumer(consumer).is_some_and(|node| core::mem::discriminant(node) == kind)
                && arena.producer(producer).is_some_and(|node| matches!(*node,
                    ProducerNode::Constructor { tag: ConstructorTag::Tuple(ProducerArity::ZERO), ref producers, ref consumers }
                    if producers.is_empty() && consumers.is_empty())),
            | _ => false,
        }),
    )]
fn cut_against_unit(
    arena: &mut CommandArena,
    consumer: ConsumerNode,
) -> CommandId
{
    let producer = unit(arena);
    let consumer = arena.mint_consumer(consumer).expect("children resolve");
    arena
        .mint_cut(Polarity::Positive, producer, consumer)
        .expect("children resolve")
}

/// Build `⟨producer |+ ★⟩`.
///
/// # Specification
/// - requires: the producer's children resolve and the arena has room.
/// - ensures: a positive cut from the supplied producer to the terminal.
/// - provides: the producer in a closed observation context.
/// - panics: on a refused node or cut allocation.
///
/// # Adequacy
/// - hypothesis: L3 — scope, polarity and arity fixtures observe the requested
///   side of a positive cut. These distinguish the wrong wrapper polarity, an
///   incorrect terminal side and a replaced node kind. Only small arenas with
///   live child references are in the fixture domain.
/// - witness: `check::tests::terminal_cut_is_wellformed`
/// - witness: `check::tests::scope_tracks_binders`
/// - witness: `check::tests::constructor_arity_is_checked`
/// - witness: `check::tests::polarity_mismatch_is_rejected`
#[spec(
        captures: [kind = core::mem::discriminant(&producer)],
        ensures: |ret| arena.command(ret).is_some_and(|node| match *node {
            | CommandNode::Cut { polarity, producer, consumer } => polarity == Polarity::Positive
                && arena.producer(producer).is_some_and(|node| core::mem::discriminant(node) == kind)
                && matches!(arena.consumer(consumer), Some(&ConsumerNode::Top)),
            | _ => false,
        }),
    )]
fn cut_against_top(
    arena: &mut CommandArena,
    producer: ProducerNode,
) -> CommandId
{
    let producer = arena.mint_producer(producer).expect("children resolve");
    let consumer = top(arena);
    arena
        .mint_cut(Polarity::Positive, producer, consumer)
        .expect("children resolve")
}

#[test]
fn control_scopes_are_local_to_each_body()
{
    use gandr_core_term::control::EffectClause;
    use gandr_core_term::control::StackFrame;
    use gandr_core_term::effect::EffectOp;
    use gandr_core_term::effect::EffectSig;
    let mut arena = CommandArena::new();
    let producers: [ProducerId; 5] = core::array::from_fn(|index| {
        arena
            .mint_producer(ProducerNode::Variable {
                zone: Zone::Intuitionistic,
                index: u32::try_from(index).expect("small index").into(),
            })
            .expect("variable")
    });
    let consumers: [ConsumerId; 4] = core::array::from_fn(|index| {
        arena
            .mint_consumer(ConsumerNode::Covariable(
                u32::try_from(index).expect("small index").into(),
            ))
            .expect("covariable")
    });
    let subject = arena
        .mint_cut(Polarity::Positive, producers[0], consumers[1])
        .expect("subject");
    let on_return = arena
        .mint_cut(Polarity::Positive, producers[2], consumers[1])
        .expect("return branch");
    let clause = arena
        .mint_cut(Polarity::Positive, producers[4], consumers[2])
        .expect("operation branch");
    let ty = arena.annotations_mut().value_type_unit();
    let signature = EffectSig::new("E".into(), [EffectOp {
        name: "op".into(),
        payload: ty,
        reply: ty,
    }])
    .expect("one operation");
    let handled = arena
        .mint_command(CommandNode::Handle {
            signature: signature.clone(),
            introduces: crate::il::Introduces::Nothing,
            subject,
            on_return,
            clauses: alloc::sync::Arc::from([EffectClause {
                operation: "op".into(),
                body: clause,
            }]),
            continuation: consumers[3],
        })
        .expect("handler");
    let performed = arena
        .mint_command(CommandNode::Perform {
            signature,
            operation: "op".into(),
            route: Route::Nearest,
            payload: producers[0],
            continuation: consumers[3],
        })
        .expect("request");
    let terminal = top(&mut arena);
    let reset = arena
        .mint_command(CommandNode::Reset {
            body: on_return,
            continuation: terminal,
        })
        .expect("reset");
    let shifted = arena
        .mint_command(CommandNode::Shift {
            body: on_return,
            continuation: terminal,
        })
        .expect("shift");
    let resumed = arena
        .mint_command(CommandNode::Resume {
            stack: producers[0],
            body: on_return,
            continuation: terminal,
        })
        .expect("resume");
    let bind_body = arena
        .mint_cut(Polarity::Positive, producers[2], consumers[2])
        .expect("frame body");
    let literal = cut_against_top(
        &mut arena,
        ProducerNode::Reify(alloc::sync::Arc::from([
            StackFrame::Apply(producers[0]),
            StackFrame::Bind(bind_body),
            StackFrame::Project(Component::from(0_usize)),
            StackFrame::Apply(producers[3]),
        ])),
    );
    for (root, values, covalues) in [
        (handled, &[0, 1, 2][..], &[0, 1, 3][..]),
        (performed, &[0][..], &[3][..]),
        (reset, &[2][..], &[0][..]),
        (shifted, &[1][..], &[0][..]),
        (resumed, &[0, 2][..], &[0][..]),
        (literal, &[0, 1, 3][..], &[1][..]),
    ] {
        assert_eq!(
            Ok(FreeSet {
                producers: values
                    .iter()
                    .copied()
                    .map(|index: u32| (Zone::Intuitionistic, index.into()))
                    .collect(),
                covariables: covalues
                    .iter()
                    .copied()
                    .map(CovariableIndex::from)
                    .collect(),
            }),
            check_command(&arena, root)
        );
    }
}

/// `⟨() |+ ★⟩` is well formed and closed.
#[test]
fn terminal_cut_is_wellformed()
{
    let mut arena = CommandArena::new();
    let root = cut_against_top(&mut arena, ProducerNode::Constructor {
        tag: ConstructorTag::Tuple(ProducerArity::ZERO),
        producers: Box::from([]),
        consumers: Box::from([]),
    });
    assert_eq!(
        Ok(FreeSet::default()),
        check_command(&arena, root),
        "the terminal cut has no free variable or covariable"
    );
}

/// A variable past every binder is free, counted from the command; the
/// same index under a `μ̃` is bound. A covariable past a `μ` is free.
#[test]
fn scope_tracks_binders()
{
    let mut arena = CommandArena::new();
    let variable = ProducerNode::Variable {
        zone: Zone::Intuitionistic,
        index: DeBruijnIndex::from(0_u32),
    };
    let root = cut_against_top(&mut arena, variable.clone());
    let free = check_command(&arena, root).expect("well formed");
    assert!(
        free.producers()
            .contains(&(Zone::Intuitionistic, DeBruijnIndex::from(0_u32))),
        "x0 is free at the root"
    );

    let occurrence = arena.mint_producer(variable).expect("a leaf mints");
    let inner_top = top(&mut arena);
    let inner = arena
        .mint_cut(Polarity::Positive, occurrence, inner_top)
        .expect("children resolve");
    let root = cut_against_unit(&mut arena, ConsumerNode::MuTilde { body: inner });
    assert_eq!(
        Ok(FreeSet::default()),
        check_command(&arena, root),
        "the μ̃ binds x0"
    );

    let escaping = arena
        .mint_consumer(ConsumerNode::Covariable(CovariableIndex::from(1_u32)))
        .expect("a leaf mints");
    let value = unit(&mut arena);
    let body = arena
        .mint_cut(Polarity::Positive, value, escaping)
        .expect("children resolve");
    let root = cut_against_top(&mut arena, ProducerNode::Mu { body });
    let free = check_command(&arena, root).expect("well formed");
    assert_eq!(
        Some(&CovariableIndex::from(0_u32)),
        free.covariables().first(),
        "α1 under one μ is the root's free α0"
    );

    let own = arena
        .mint_producer(ProducerNode::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(0_u32),
        })
        .expect("a leaf mints");
    let outer = arena
        .mint_producer(ProducerNode::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(1_u32),
        })
        .expect("a leaf mints");
    let return_point = arena
        .mint_consumer(ConsumerNode::Covariable(CovariableIndex::from(0_u32)))
        .expect("a leaf mints");
    let pair = arena
        .mint_producer(ProducerNode::Constructor {
            tag: ConstructorTag::Tuple(ProducerArity::TWO),
            producers: Box::from([own, outer]),
            consumers: Box::from([]),
        })
        .expect("fields resolve");
    let body = arena
        .mint_cut(Polarity::Positive, pair, return_point)
        .expect("children resolve");
    let root = cut_against_top(&mut arena, ProducerNode::Fixpoint {
        body,
        evidence: gandr_kernel_term::FixpointEvidence::StructuralDescent,
    });
    let free = check_command(&arena, root).expect("well formed");
    assert_eq!(
        (
            alloc::collections::BTreeSet::from([(
                Zone::Intuitionistic,
                DeBruijnIndex::from(0_u32)
            )]),
            alloc::collections::BTreeSet::new()
        ),
        (free.producers().clone(), free.covariables().clone()),
        "a recursive thunk binds x0 and α0, so only x1 is free, as the root's x0"
    );

    let branch = arena
        .mint_producer(ProducerNode::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(0_u32),
        })
        .expect("a leaf mints");
    let then = top(&mut arena);
    let root = cut_against_unit(&mut arena, ConsumerNode::DataCase {
        branches: Box::from([branch]),
        then,
    });
    let free = check_command(&arena, root).expect("well formed");
    assert!(
        free.producers()
            .contains(&(Zone::Intuitionistic, DeBruijnIndex::from(0_u32))),
        "a nominal match binds nothing, so its branch's x0 is free"
    );
}

/// A root the arena does not hold is dangling.
#[test]
fn dangling_reference_is_rejected()
{
    let arena = CommandArena::new();
    let phantom = CommandId::from(7_u32);
    assert_eq!(
        Err(CheckRefusal::DanglingCommand(phantom)),
        check_command(&arena, phantom),
        "an unresolved command is dangling"
    );
}

/// A `μ` as a pair's field is a non-value.
#[test]
fn non_value_argument_is_rejected()
{
    let mut arena = CommandArena::new();
    let value = unit(&mut arena);
    let inner_top = top(&mut arena);
    let inner = arena
        .mint_cut(Polarity::Positive, value, inner_top)
        .expect("children resolve");
    let capture = arena
        .mint_producer(ProducerNode::Mu { body: inner })
        .expect("the body resolves");
    let other = unit(&mut arena);
    let root = cut_against_top(&mut arena, ProducerNode::Constructor {
        tag: ConstructorTag::Tuple(ProducerArity::TWO),
        producers: Box::from([capture, other]),
        consumers: Box::from([]),
    });
    assert_eq!(
        Err(CheckRefusal::NonValueArgument(capture)),
        check_command(&arena, root),
        "a capture in field position is a non-value"
    );

    let then = top(&mut arena);
    let root = cut_against_unit(&mut arena, ConsumerNode::DataCase {
        branches: Box::from([capture]),
        then,
    });
    assert_eq!(
        Err(CheckRefusal::NonValueArgument(capture)),
        check_command(&arena, root),
        "a capture as a nominal match's branch is a non-value"
    );
}

/// A copattern object cut positively is a polarity mismatch.
#[test]
fn polarity_mismatch_is_rejected()
{
    let mut arena = CommandArena::new();
    let root = cut_against_top(&mut arena, ProducerNode::Cocase {
        arms: Box::from([]),
    });
    let refused = check_command(&arena, root);
    assert!(
        matches!(
            refused,
            Err(CheckRefusal::PolarityMismatch {
                cut: Polarity::Positive,
                observed: Polarity::Negative,
                ..
            })
        ),
        "a copattern object cut positively is refused: {refused:?}"
    );
}

/// A pair of one field contradicts its head.
#[test]
fn constructor_arity_is_checked()
{
    let mut arena = CommandArena::new();
    let only = unit(&mut arena);
    let root = cut_against_top(&mut arena, ProducerNode::Constructor {
        tag: ConstructorTag::Tuple(ProducerArity::TWO),
        producers: Box::from([only]),
        consumers: Box::from([]),
    });
    assert_eq!(
        Err(CheckRefusal::ProducerArity {
            head: ArityHead::Constructor(ConstructorTag::Tuple(ProducerArity::TWO)),
            expected: ProducerArity::TWO,
            found: ProducerArity::ONE,
        }),
        check_command(&arena, root),
        "a pair needs two fields"
    );
}

/// A constructor is held to the consumer arity its head declares, none.
#[test]
fn constructor_consumer_arity_is_checked()
{
    let mut arena = CommandArena::new();
    let stray = top(&mut arena);
    let root = cut_against_top(&mut arena, ProducerNode::Constructor {
        tag: ConstructorTag::Tuple(ProducerArity::ZERO),
        producers: Box::from([]),
        consumers: Box::from([stray]),
    });
    assert_eq!(
        Err(CheckRefusal::ConsumerArity {
            head: ArityHead::Constructor(ConstructorTag::Tuple(ProducerArity::ZERO)),
            expected: ConsumerArity::ZERO,
            found: ConsumerArity::ONE,
        }),
        check_command(&arena, root),
        "no constructor of the core's types carries a consumer"
    );
}

/// A destructor frame is held to its one return continuation in both
/// directions.
#[test]
fn destructor_consumer_arity_is_checked()
{
    let mut arena = CommandArena::new();
    let root = cut_against_unit(&mut arena, ConsumerNode::Destructor {
        tag: DestructorTag::Force,
        producers: Box::from([]),
        consumers: Box::from([]),
    });
    assert_eq!(
        Err(CheckRefusal::ConsumerArity {
            head: ArityHead::Destructor(DestructorTag::Force),
            expected: ConsumerArity::ONE,
            found: ConsumerArity::ZERO,
        }),
        check_command(&arena, root),
        "a frame without its continuation is refused"
    );
    let first = top(&mut arena);
    let second = top(&mut arena);
    let root = cut_against_unit(&mut arena, ConsumerNode::Destructor {
        tag: DestructorTag::Force,
        producers: Box::from([]),
        consumers: Box::from([first, second]),
    });
    assert_eq!(
        Err(CheckRefusal::ConsumerArity {
            head: ArityHead::Destructor(DestructorTag::Force),
            expected: ConsumerArity::ONE,
            found: ConsumerArity::from(2_usize),
        }),
        check_command(&arena, root),
        "a frame with two continuations is refused"
    );
}

/// The count comes from the head: one consumer child is admitted at a
/// frame and refused at a constructor, none admitted at a constructor and
/// refused at a frame.
#[test]
fn consumer_arity_follows_the_head_not_a_constant()
{
    let mut arena = CommandArena::new();
    let one = top(&mut arena);
    let root = cut_against_unit(&mut arena, ConsumerNode::Destructor {
        tag: DestructorTag::Force,
        producers: Box::from([]),
        consumers: Box::from([one]),
    });
    assert!(
        check_command(&arena, root).is_ok(),
        "one consumer child meets the frame's declaration"
    );
    let root = cut_against_top(&mut arena, ProducerNode::Constructor {
        tag: ConstructorTag::Tuple(ProducerArity::ZERO),
        producers: Box::from([]),
        consumers: Box::from([]),
    });
    assert!(
        check_command(&arena, root).is_ok(),
        "no consumer child meets the constructor's declaration"
    );
    let root = cut_against_top(&mut arena, ProducerNode::Constructor {
        tag: ConstructorTag::Tuple(ProducerArity::ZERO),
        producers: Box::from([]),
        consumers: Box::from([one]),
    });
    assert!(
        matches!(
            check_command(&arena, root),
            Err(CheckRefusal::ConsumerArity { .. })
        ),
        "the same one child violates the constructor's declaration"
    );
    let root = cut_against_unit(&mut arena, ConsumerNode::Destructor {
        tag: DestructorTag::Force,
        producers: Box::from([]),
        consumers: Box::from([]),
    });
    assert!(
        matches!(
            check_command(&arena, root),
            Err(CheckRefusal::ConsumerArity { .. })
        ),
        "the same empty list violates the frame's declaration"
    );
}

/// A match answering one constructor twice, and a copattern object
/// answering one destructor twice, are refused by the repeated head.
#[test]
fn a_head_answered_twice_is_rejected()
{
    let mut arena = CommandArena::new();
    let value = unit(&mut arena);
    let inner_top = top(&mut arena);
    let body = arena
        .mint_cut(Polarity::Positive, value, inner_top)
        .expect("children resolve");
    let left = ConstructorTag::Injection(Side::Left.into());
    let root = cut_against_unit(&mut arena, ConsumerNode::Case {
        arms: Box::from([
            PatternArm {
                constructor: left.clone(),
                body,
            },
            PatternArm {
                constructor: left.clone(),
                body,
            },
        ]),
    });
    assert_eq!(
        Err(CheckRefusal::DuplicateArm(ArityHead::Constructor(left))),
        check_command(&arena, root),
        "a match answers each constructor once"
    );
    let object = arena
        .mint_producer(ProducerNode::Cocase {
            arms: Box::from([
                CopatternArm {
                    destructor: DestructorTag::Apply,
                    body,
                },
                CopatternArm {
                    destructor: DestructorTag::Apply,
                    body,
                },
            ]),
        })
        .expect("the arms resolve");
    let outer_top = top(&mut arena);
    let root = arena
        .mint_cut(Polarity::Negative, object, outer_top)
        .expect("children resolve");
    assert_eq!(
        Err(CheckRefusal::DuplicateArm(ArityHead::Destructor(
            DestructorTag::Apply
        ))),
        check_command(&arena, root),
        "an object answers each destructor once"
    );
}

/// Intrinsic polarity is a total table over node kinds and destructor
/// heads.
#[test]
fn every_node_kind_declares_its_intrinsic_polarity()
{
    let body = CommandId::from(0_u32);
    for (node, expected) in [
        (
            ProducerNode::Variable {
                zone: Zone::Intuitionistic,
                index: 0_u32.into(),
            },
            None,
        ),
        (ProducerNode::Constant(0_usize.into()), None),
        (
            ProducerNode::Literal(gandr_kernel_term::Literal::Text(
                gandr_kernel_term::StringLiteral::new("text".into()),
            )),
            Some(Polarity::Positive),
        ),
        (
            ProducerNode::Constructor {
                tag: ConstructorTag::Tuple(ProducerArity::ZERO),
                producers: Box::from([]),
                consumers: Box::from([]),
            },
            Some(Polarity::Positive),
        ),
        (ProducerNode::Thunk { body }, Some(Polarity::Positive)),
        (
            ProducerNode::Fixpoint {
                body,
                evidence: gandr_kernel_term::FixpointEvidence::Partial,
            },
            Some(Polarity::Positive),
        ),
        (
            ProducerNode::Cocase {
                arms: Box::from([]),
            },
            Some(Polarity::Negative),
        ),
        (ProducerNode::Mu { body }, None),
    ] {
        assert_eq!(expected, producer_polarity(&node));
    }
    for (node, expected) in [
        (ConsumerNode::Covariable(0_u32.into()), None),
        (ConsumerNode::Top, None),
        (ConsumerNode::MuTilde { body }, None),
        (
            ConsumerNode::Case {
                arms: Box::from([]),
            },
            Some(Polarity::Positive),
        ),
        (
            ConsumerNode::DataCase {
                branches: Box::from([]),
                then: ConsumerId::from(0_u32),
            },
            Some(Polarity::Positive),
        ),
        (
            ConsumerNode::Destructor {
                tag: DestructorTag::Apply,
                producers: Box::from([]),
                consumers: Box::from([]),
            },
            Some(Polarity::Negative),
        ),
        (
            ConsumerNode::Destructor {
                tag: DestructorTag::Force,
                producers: Box::from([]),
                consumers: Box::from([]),
            },
            Some(Polarity::Positive),
        ),
    ] {
        assert_eq!(expected, consumer_polarity(&node));
    }
}

/// A `μ̃` binds an intuitionistic variable and a `μ` a covariable, and
/// neither binds a linear variable: the free set under each counts past only
/// the binders of its own space.
#[test]
fn scope_boundaries_keep_linear_variables_free()
{
    let mut arena = CommandArena::new();
    let mut fields = Vec::new();
    for (zone, index) in [
        (Zone::Intuitionistic, 0_u32),
        (Zone::Intuitionistic, 2),
        (Zone::Linear, 0),
    ] {
        fields.push(
            arena
                .mint_producer(ProducerNode::Variable {
                    zone,
                    index: index.into(),
                })
                .expect("leaf"),
        );
    }
    let triple = arena
        .mint_producer(ProducerNode::Constructor {
            tag: ConstructorTag::Tuple(ProducerArity::from(3_usize)),
            producers: fields.into_boxed_slice(),
            consumers: Box::from([]),
        })
        .expect("fields resolve");
    let returned = arena
        .mint_consumer(ConsumerNode::Covariable(1_u32.into()))
        .expect("leaf");
    let inner = arena
        .mint_cut(Polarity::Positive, triple, returned)
        .expect("children resolve");
    let under_mu_tilde = cut_against_unit(&mut arena, ConsumerNode::MuTilde { body: inner });
    let under_mu = cut_against_top(&mut arena, ProducerNode::Mu { body: inner });
    for (root, producers, covariables) in [
        (
            inner,
            BTreeSet::from([
                (Zone::Intuitionistic, DeBruijnIndex::from(0_u32)),
                (Zone::Intuitionistic, 2_u32.into()),
                (Zone::Linear, 0_u32.into()),
            ]),
            BTreeSet::from([CovariableIndex::from(1_u32)]),
        ),
        (
            under_mu_tilde,
            BTreeSet::from([
                (Zone::Intuitionistic, DeBruijnIndex::from(1_u32)),
                (Zone::Linear, 0_u32.into()),
            ]),
            BTreeSet::from([CovariableIndex::from(1_u32)]),
        ),
        (
            under_mu,
            BTreeSet::from([
                (Zone::Intuitionistic, DeBruijnIndex::from(0_u32)),
                (Zone::Intuitionistic, 2_u32.into()),
                (Zone::Linear, 0_u32.into()),
            ]),
            BTreeSet::from([CovariableIndex::from(0_u32)]),
        ),
    ] {
        assert_eq!(
            Ok(FreeSet {
                producers,
                covariables
            }),
            check_command(&arena, root)
        );
    }
}

/// Counts precede child lookup, then the first bad producer wins without
/// scheduling.
#[test]
fn child_refusals_follow_declared_precedence()
{
    let mut arena = CommandArena::new();
    let value = unit(&mut arena);
    let continuation = top(&mut arena);
    let body = arena
        .mint_cut(Polarity::Positive, value, continuation)
        .expect("live children");
    let capture = arena
        .mint_producer(ProducerNode::Mu { body })
        .expect("live body");
    let missing_producer = ProducerId::from(u32::MAX);
    let missing_consumer = ConsumerId::from(u32::MAX);
    for (head, producer_arity, consumer_arity, producers, consumers, expected) in [
        (
            ArityHead::Destructor(DestructorTag::Apply),
            ProducerArity::ONE,
            ConsumerArity::ONE,
            [].as_slice(),
            [].as_slice(),
            CheckRefusal::ProducerArity {
                head: ArityHead::Destructor(DestructorTag::Apply),
                expected: ProducerArity::ONE,
                found: ProducerArity::ZERO,
            },
        ),
        (
            ArityHead::Destructor(DestructorTag::Apply),
            ProducerArity::ONE,
            ConsumerArity::ONE,
            [missing_producer].as_slice(),
            [].as_slice(),
            CheckRefusal::ConsumerArity {
                head: ArityHead::Destructor(DestructorTag::Apply),
                expected: ConsumerArity::ONE,
                found: ConsumerArity::ZERO,
            },
        ),
        (
            ArityHead::Destructor(DestructorTag::Apply),
            ProducerArity::ONE,
            ConsumerArity::ONE,
            [missing_producer].as_slice(),
            [missing_consumer].as_slice(),
            CheckRefusal::DanglingProducer(missing_producer),
        ),
        (
            ArityHead::Destructor(DestructorTag::Apply),
            ProducerArity::ONE,
            ConsumerArity::ONE,
            [capture].as_slice(),
            [missing_consumer].as_slice(),
            CheckRefusal::NonValueArgument(capture),
        ),
        (
            ArityHead::Constructor(ConstructorTag::Tuple(ProducerArity::TWO)),
            ProducerArity::TWO,
            ConsumerArity::ZERO,
            [capture, missing_producer].as_slice(),
            [].as_slice(),
            CheckRefusal::NonValueArgument(capture),
        ),
        (
            ArityHead::Constructor(ConstructorTag::Tuple(ProducerArity::TWO)),
            ProducerArity::TWO,
            ConsumerArity::ZERO,
            [missing_producer, capture].as_slice(),
            [].as_slice(),
            CheckRefusal::DanglingProducer(missing_producer),
        ),
    ] {
        let walk = Walk {
            arena: &arena,
            stack: alloc::vec![NodeAddress::Command(body)],
        };
        assert_eq!(
            Err(expected),
            walk.fields(head, producer_arity, consumer_arity, producers, consumers)
        );
        assert_eq!(&[NodeAddress::Command(body)], walk.stack.as_slice());
    }
    let mut walk = Walk {
        arena: &arena,
        stack: Vec::new(),
    };
    assert_eq!(
        Err(CheckRefusal::DanglingConsumer(missing_consumer)),
        walk.consumer(missing_consumer)
    );
    assert_eq!(
        Err(CheckRefusal::DanglingProducer(missing_producer)),
        walk.producer(missing_producer)
    );
}
