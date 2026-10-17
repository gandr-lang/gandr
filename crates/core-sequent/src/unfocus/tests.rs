use alloc::boxed::Box;

use gandr_theory_cell_complexes::Polarity;

use super::*;
use crate::il::CovariableIndex;

/// `λ. ⟨() |+ α1⟩` decoded from the root: the arm's covariable `1` is the
/// root's `★`, a jump out of the lambda the core cannot state.
#[test]
fn an_escaping_covariable_is_refused_and_rolled_back()
{
    let mut arena = CommandArena::new();
    let unit = arena
        .mint_producer(ProducerNode::Constructor {
            tag: ConstructorTag::Tuple(ProducerArity::ZERO),
            producers: Box::from([]),
            consumers: Box::from([]),
        })
        .expect("a leaf mints");
    let outer = arena
        .mint_consumer(ConsumerNode::Covariable(CovariableIndex::from(1_u32)))
        .expect("a leaf mints");
    let body = arena
        .mint_cut(Polarity::Positive, unit, outer)
        .expect("children resolve");
    let object = arena
        .mint_producer(ProducerNode::Cocase {
            arms: Box::from([crate::il::CopatternArm {
                destructor: DestructorTag::Apply,
                body,
            }]),
        })
        .expect("the body resolves");
    let top = arena
        .mint_consumer(ConsumerNode::Top)
        .expect("a leaf mints");
    let root = arena
        .mint_cut(Polarity::Negative, object, top)
        .expect("children resolve");

    let mut core = CoreArena::new();
    let kept = core.value_unit();
    let mark = core.watermark();
    assert_eq!(
        Err(UnfocusRefusal::EscapingContinuation(outer)),
        unfocus_command(&arena, root, &mut core),
        "the arm returns past its own return point"
    );
    assert_eq!(mark, core.watermark(), "the core arena is back at its mark");
    assert!(core.value(kept).is_some(), "earlier nodes are kept");
}

/// A `μ` standing as a pair's field has no core reading, and neither has a
/// match whose arms are not the two injections.
#[test]
fn a_capture_standing_as_a_value_is_outside_the_image()
{
    let mut arena = CommandArena::new();
    let unit = arena
        .mint_producer(ProducerNode::Constructor {
            tag: ConstructorTag::Tuple(ProducerArity::ZERO),
            producers: Box::from([]),
            consumers: Box::from([]),
        })
        .expect("a leaf mints");
    let top = arena
        .mint_consumer(ConsumerNode::Top)
        .expect("a leaf mints");
    let inner = arena
        .mint_cut(Polarity::Positive, unit, top)
        .expect("children resolve");
    let capture = arena
        .mint_producer(ProducerNode::Mu { body: inner })
        .expect("the body resolves");
    let pair = arena
        .mint_producer(ProducerNode::Constructor {
            tag: ConstructorTag::Tuple(ProducerArity::TWO),
            producers: Box::from([capture, unit]),
            consumers: Box::from([]),
        })
        .expect("fields resolve");
    let mut core = CoreArena::new();
    assert_eq!(
        Err(UnfocusRefusal::ProducerOutsideTheImage(capture)),
        unfocus_value(&arena, pair, &mut core),
        "a capture is not a value"
    );

    let matcher = arena
        .mint_consumer(ConsumerNode::Case {
            arms: Box::from([
                crate::il::PatternArm {
                    constructor: ConstructorTag::Tuple(ProducerArity::ZERO),
                    body: inner,
                },
                crate::il::PatternArm {
                    constructor: ConstructorTag::Injection(Summand::from(1_usize)),
                    body: inner,
                },
            ]),
        })
        .expect("the arms resolve");
    let matched = arena
        .mint_cut(Polarity::Positive, unit, matcher)
        .expect("children resolve");
    assert_eq!(
        Err(UnfocusRefusal::ConsumerOutsideTheImage(matcher)),
        unfocus_command(&arena, matched, &mut core),
        "the core splits one tuple pattern or cases on a sum, never a mix"
    );
    assert_eq!(
        CoreArena::new().watermark(),
        core.watermark(),
        "nothing is left behind"
    );
}

/// Each binder counter saturates without changing the other counter.
#[test]
fn binder_depths_saturate_independently()
{
    let bounds = [
        (0_u32, 1_u32),
        (1, 2),
        (u32::MAX.saturating_sub(1), u32::MAX),
        (u32::MAX, u32::MAX),
    ];
    for (producers, next_producers) in bounds {
        for (covariables, next_covariables) in bounds {
            let depth = Depth {
                producers,
                covariables,
            };
            assert_eq!(
                Depth {
                    producers: next_producers,
                    covariables
                },
                depth.under_producer()
            );
            assert_eq!(
                Depth {
                    producers,
                    covariables: next_covariables
                },
                depth.under_covariable()
            );
        }
    }
}

/// Substitution respects the binder boundary, closing order, residual index
/// and zone.
#[test]
fn closing_substitution_distinguishes_binders_and_zones()
{
    use gandr_core_term::Value;

    let arena = CommandArena::new();
    let mut core = CoreArena::new();
    let first = core.value_unit();
    let second = core.value_constant(7_usize.into());
    let closing = [first, second];
    for (zone, index, producers, length, expected) in [
        (Zone::Intuitionistic, 0_u32, 0_u32, 2_usize, Value::unit()),
        (
            Zone::Intuitionistic,
            1,
            0,
            2,
            Value::Constant(7_usize.into()),
        ),
        (Zone::Intuitionistic, 2, 0, 2, Value::Variable {
            zone: Zone::Intuitionistic,
            index: 0_u32.into(),
        }),
        (Zone::Intuitionistic, 0, 1, 2, Value::Variable {
            zone: Zone::Intuitionistic,
            index: 0_u32.into(),
        }),
        (Zone::Intuitionistic, 1, 1, 2, Value::unit()),
        (
            Zone::Intuitionistic,
            2,
            1,
            2,
            Value::Constant(7_usize.into()),
        ),
        (Zone::Intuitionistic, 3, 1, 2, Value::Variable {
            zone: Zone::Intuitionistic,
            index: 1_u32.into(),
        }),
        (Zone::Intuitionistic, 1, 0, 0, Value::Variable {
            zone: Zone::Intuitionistic,
            index: 1_u32.into(),
        }),
        (Zone::Linear, 2, 1, 2, Value::Variable {
            zone: Zone::Linear,
            index: 2_u32.into(),
        }),
    ] {
        let mut walk = Unfocusing {
            arena: &arena,
            core: &mut core,
            closing: &closing[.. length],
            tasks: Vec::new(),
            values: Vec::new(),
            computations: Vec::new(),
        };
        walk.variable(zone, index.into(), Depth {
            producers,
            covariables: 0,
        });
        let value = walk.pop_value().expect("one variable reading");
        assert_eq!(Some(&expected), walk.core.value(value));
        match expected {
            Value::Tuple(_) => assert_eq!(first, value),
            Value::Constant(_) => assert_eq!(second, value),
            Value::Primitive { .. }
            | Value::PathRefl(_)
            | Value::PathProduct(..)
            | Value::PathEquiv { .. }
            | Value::Here(_)
            | Value::Funext(..)
            | Value::Equiv(..)
            | Value::Univalence(..)
            | Value::Ua { .. }
            | Value::SessionRelated { .. }
            | Value::Stay(_)
            | Value::Then(..)
            | Value::FlowProduct(..)
            | Value::Forward(_)
            | Value::FunctionFlow(..)
            | Value::Recorded(_)
            | Value::Returned(_)
            | Value::Nested(_)
            | Value::Run(_)
            | Value::Variable { .. }
            | Value::Literal(_)
            | Value::Injection(..)
            | Value::ListNil
            | Value::ListCons(..)
            | Value::Thunk(_)
            | Value::Lift { .. }
            | Value::Quote(_)
            | Value::QuoteComputation(_)
            | Value::StaticLambda(_)
            | Value::StaticApplication(..)
            | Value::Constructor { .. }
            | Value::Record(_)
            | Value::Hole(_)
            | Value::Mark { .. }
            | Value::Reify(_) => {},
        }
    }
}

#[test]
fn closing_fold_annotations_substitutes_captured_codes()
{
    use gandr_core_term::Computation;
    use gandr_core_term::ValueType;
    let mut source = CoreArena::new();
    let captured = source.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let element = source.value_type_element(captured, gandr_kernel_strata::Level::zero());
    let result = source.value_type_list(element);
    let nil = source.value_list_nil();
    let on_nil = source.computation_return(nil);
    let head = source.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let tail = source.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let cell = source.value_list_cons(head, tail);
    let on_cons = source.computation_return(cell);
    let fold = source.computation_list_fold(element, result, nil, on_nil, on_cons);
    let mut arena = CommandArena::new();
    let mut provenance = crate::focus::Provenance::new();
    let root = crate::focus::focus_computation(&source, fold, &mut arena, &mut provenance)
        .expect("open annotation focuses");
    let mut core = CoreArena::new();
    let unit = core.value_type_unit();
    let code = core.value_quote(unit);
    let Decoded::Computation(closed) =
        decode(&arena, Root::Command(root), &mut core, &[code]).expect("captured code closes")
    else {
        panic!("computation");
    };
    let &Computation::ListFold {
        element,
        result,
        on_cons,
        ..
    } = core.computation(closed).expect("fold")
    else {
        panic!("native fold");
    };
    assert_eq!(core.value_type(element), Some(&ValueType::unit()));
    assert!(
        matches!(core.value_type(result), Some(&ValueType::List(inner)) if core.value_type(inner) == Some(&ValueType::unit()))
    );
    let &Computation::Return(cell) = core.computation(on_cons).expect("cons branch")
    else {
        panic!("return");
    };
    let &gandr_core_term::Value::ListCons(head, tail) = core.value(cell).expect("cell")
    else {
        panic!("native cell");
    };
    for (id, index) in [(head, 1_u32), (tail, 0_u32)] {
        assert_eq!(
            core.value(id),
            Some(&gandr_core_term::Value::Variable {
                zone: Zone::Intuitionistic,
                index: DeBruijnIndex::from(index)
            })
        );
    }
}

/// Missing roots and malformed positive and negative heads are refused
/// without residue.
#[test]
fn decoding_refuses_missing_roots_and_malformed_heads()
{
    let mut arena = CommandArena::new();
    let mut core = CoreArena::new();
    core.value_unit();
    let mark = core.watermark();
    let missing_command = CommandId::from(0_u32);
    let missing_producer = ProducerId::from(0_u32);
    assert_eq!(
        Err(UnfocusRefusal::DanglingCommand(missing_command)),
        unfocus_command(&arena, missing_command, &mut core)
    );
    assert_eq!(
        Err(UnfocusRefusal::DanglingProducer(missing_producer)),
        unfocus_value(&arena, missing_producer, &mut core)
    );
    assert_eq!(
        Err(UnfocusRefusal::DanglingProducer(missing_producer)),
        decode(&arena, Root::Copattern(missing_producer), &mut core, &[])
    );
    assert_eq!(mark, core.watermark());
    let unit = arena
        .mint_producer(ProducerNode::Constructor {
            tag: ConstructorTag::Tuple(ProducerArity::ZERO),
            producers: Box::from([]),
            consumers: Box::from([]),
        })
        .expect("leaf");
    let top = arena.mint_consumer(ConsumerNode::Top).expect("leaf");
    let back = arena
        .mint_consumer(ConsumerNode::Covariable(CovariableIndex::from(0_u32)))
        .expect("leaf");
    let body = arena
        .mint_cut(Polarity::Positive, unit, back)
        .expect("live children");
    assert_eq!(
        Err(UnfocusRefusal::ProducerOutsideTheImage(unit)),
        decode(&arena, Root::Copattern(unit), &mut core, &[])
    );
    for node in [
        ProducerNode::Constructor {
            tag: ConstructorTag::Tuple(ProducerArity::ZERO),
            producers: Box::from([unit]),
            consumers: Box::from([]),
        },
        ProducerNode::Constructor {
            tag: ConstructorTag::Tuple(ProducerArity::TWO),
            producers: Box::from([]),
            consumers: Box::from([]),
        },
        ProducerNode::Constructor {
            tag: ConstructorTag::Injection(Side::Left.into()),
            producers: Box::from([]),
            consumers: Box::from([]),
        },
        ProducerNode::Constructor {
            tag: ConstructorTag::Lift(Level::zero()),
            producers: Box::from([]),
            consumers: Box::from([]),
        },
        ProducerNode::Constructor {
            tag: ConstructorTag::Tuple(ProducerArity::ZERO),
            producers: Box::from([]),
            consumers: Box::from([top]),
        },
    ] {
        let bad = arena.mint_producer(node).expect("references resolve");
        assert_eq!(
            Err(UnfocusRefusal::ProducerOutsideTheImage(bad)),
            unfocus_value(&arena, bad, &mut core)
        );
        assert_eq!(mark, core.watermark());
    }
    let apply = crate::il::CopatternArm {
        destructor: DestructorTag::Apply,
        body,
    };
    let force = crate::il::CopatternArm {
        destructor: DestructorTag::Force,
        body,
    };
    let shapes: [Box<[crate::il::CopatternArm]>; 3] =
        [Box::from([]), Box::from([force]), Box::from([apply, apply])];
    for arms in shapes {
        let bad = arena
            .mint_producer(ProducerNode::Cocase { arms })
            .expect("references resolve");
        assert_eq!(
            Err(UnfocusRefusal::ProducerOutsideTheImage(bad)),
            decode(&arena, Root::Copattern(bad), &mut core, &[])
        );
        assert_eq!(
            Err(UnfocusRefusal::ProducerOutsideTheImage(bad)),
            unfocus_value(&arena, bad, &mut core)
        );
        assert_eq!(mark, core.watermark());
    }
    for node in [
        ConsumerNode::Destructor {
            tag: DestructorTag::Force,
            producers: Box::from([unit]),
            consumers: Box::from([top]),
        },
        ConsumerNode::Destructor {
            tag: DestructorTag::Force,
            producers: Box::from([]),
            consumers: Box::from([]),
        },
        ConsumerNode::Case {
            arms: Box::from([
                crate::il::PatternArm {
                    constructor: ConstructorTag::Injection(Side::Right.into()),
                    body,
                },
                crate::il::PatternArm {
                    constructor: ConstructorTag::Injection(Side::Left.into()),
                    body,
                },
            ]),
        },
    ] {
        let bad = arena.mint_consumer(node).expect("references resolve");
        let root = arena
            .mint_cut(Polarity::Positive, unit, bad)
            .expect("references resolve");
        assert_eq!(
            Err(UnfocusRefusal::ConsumerOutsideTheImage(bad)),
            unfocus_command(&arena, root, &mut core)
        );
        assert_eq!(mark, core.watermark());
    }
}

/// Return-point depth and application arities select distinct spine
/// outcomes.
#[test]
fn spines_distinguish_return_points_and_frame_arities()
{
    let mut arena = CommandArena::new();
    let mut core = CoreArena::new();
    let value = core.value_unit();
    let result = core.computation_return(value);
    let producer = arena
        .mint_producer(ProducerNode::Constant(0_usize.into()))
        .expect("leaf");
    let top = arena.mint_consumer(ConsumerNode::Top).expect("leaf");
    let zero = arena
        .mint_consumer(ConsumerNode::Covariable(CovariableIndex::from(0_u32)))
        .expect("leaf");
    let one = arena
        .mint_consumer(ConsumerNode::Covariable(CovariableIndex::from(1_u32)))
        .expect("leaf");
    for (consumer, depth, expected) in [
        (top, 0_u32, Ok(())),
        (top, 1, Err(UnfocusRefusal::EscapingContinuation(top))),
        (zero, 0, Err(UnfocusRefusal::EscapingContinuation(zero))),
        (zero, 1, Ok(())),
        (one, 1, Err(UnfocusRefusal::EscapingContinuation(one))),
    ] {
        let mut walk = Unfocusing {
            arena: &arena,
            core: &mut core,
            closing: &[],
            tasks: Vec::new(),
            values: Vec::new(),
            computations: alloc::vec![result],
        };
        assert_eq!(
            expected,
            walk.spine(consumer, Depth {
                producers: 0,
                covariables: depth
            })
        );
        assert_eq!([result], walk.computations.as_slice());
    }
    for node in [
        ConsumerNode::Destructor {
            tag: DestructorTag::Apply,
            producers: Box::from([]),
            consumers: Box::from([top]),
        },
        ConsumerNode::Destructor {
            tag: DestructorTag::Apply,
            producers: Box::from([producer]),
            consumers: Box::from([]),
        },
        ConsumerNode::Destructor {
            tag: DestructorTag::Force,
            producers: Box::from([]),
            consumers: Box::from([top]),
        },
        ConsumerNode::Case {
            arms: Box::from([]),
        },
    ] {
        let consumer = arena.mint_consumer(node).expect("references resolve");
        let mut walk = Unfocusing {
            arena: &arena,
            core: &mut core,
            closing: &[],
            tasks: Vec::new(),
            values: Vec::new(),
            computations: alloc::vec![result],
        };
        assert_eq!(
            Err(UnfocusRefusal::ConsumerOutsideTheImage(consumer)),
            walk.spine(consumer, Depth::ROOT)
        );
    }
    let missing = ConsumerId::from(u32::MAX);
    let mut walk = Unfocusing {
        arena: &arena,
        core: &mut core,
        closing: &[],
        tasks: Vec::new(),
        values: Vec::new(),
        computations: alloc::vec![result],
    };
    assert_eq!(
        Err(UnfocusRefusal::DanglingConsumer(missing)),
        walk.spine(missing, Depth::ROOT)
    );
}

/// Decoding pops exact last results and rejects both underflow and a
/// surplus root.
#[test]
fn decoding_result_stacks_refuse_underflow_and_surplus()
{
    let mut arena = CommandArena::new();
    let unit = arena
        .mint_producer(ProducerNode::Constructor {
            tag: ConstructorTag::Tuple(ProducerArity::ZERO),
            producers: Box::from([]),
            consumers: Box::from([]),
        })
        .expect("leaf");
    let mut core = CoreArena::new();
    let first = core.value_unit();
    let last = core.value_constant(1_usize.into());
    let before = core.computation_return(first);
    let after = core.computation_return(last);
    let mut walk = Unfocusing {
        arena: &arena,
        core: &mut core,
        closing: &[],
        tasks: Vec::new(),
        values: alloc::vec![first, last],
        computations: alloc::vec![before, after],
    };
    assert_eq!(Ok(last), walk.pop_value());
    assert_eq!(Ok(first), walk.pop_value());
    assert_eq!(Err(UnfocusRefusal::DecodeInvariant), walk.pop_value());
    assert_eq!(Ok(after), walk.pop_computation());
    assert_eq!(Ok(before), walk.pop_computation());
    assert_eq!(Err(UnfocusRefusal::DecodeInvariant), walk.pop_computation());
    walk.values.push(first);
    assert_eq!(
        Err(UnfocusRefusal::DecodeInvariant),
        walk.run(Root::Value(unit))
    );
}
