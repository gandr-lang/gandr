//! Higher-field boundary, productivity and computed symmetry witnesses.

use alloc::vec;

use gandr_kernel_term::BaseType;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::Side;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::ValueId;

use super::Cell;
use super::Codata;
use super::Depth;
use super::HigherError;
use super::HigherId;
use super::Layer;
use super::ObservationBudget;
use super::relation;
use super::symmetry;
use crate::conv::Convertibility;
use crate::conv::equal_values;
use crate::identity_recursion::RelationError;
use crate::replay::ReplayBudget;

/// A productive, one-node corecursive field.
///
/// # Specification
/// trivial.
fn guarded(evidence: ValueId) -> Codata
{
    Codata {
        nodes: vec![Layer::Guard {
            evidence,
            tail: HigherId(0),
        }],
        root: HigherId(0),
    }
}

/// Eight constructor observations with one unit per instruction.
///
/// # Specification
/// trivial.
fn budget() -> ObservationBudget
{
    ObservationBudget {
        depth: Depth(8),
        replay: ReplayBudget::from(8_u64),
    }
}

#[test]
fn symmetry_on_a_boolean_square_computes()
{
    let mut arena = TermArena::new();
    let unit_type = arena.value_type_unit();
    let boolean = arena.value_type_sum(unit_type, unit_type);
    let code = arena.value_quote(boolean);
    let unit = arena.value_unit();
    let x = arena.value_variable(DeBruijnIndex::from(0_u32));
    let y = arena.value_variable(DeBruijnIndex::from(1_u32));
    let context = [unit_type, unit_type];
    let higher = guarded(unit);
    for side in [Side::Left, Side::Right] {
        let a = arena.value_injection(side, x);
        let b = arena.value_injection(side, y);
        assert_eq!(equal_values(&arena, a, b), Convertibility::Distinct);
        let path = Cell {
            code,
            left: a,
            right: b,
            evidence: unit,
        };
        let square = symmetry(&mut arena, &context, path, &higher, budget()).expect("fibre action");
        assert_eq!(square.top, path);
        assert_eq!((square.right.left, square.right.right), (b, a));
        assert_eq!((square.bottom.left, square.bottom.right), (a, a));
        assert_eq!(square.left, square.bottom);
        for face in [square.top, square.right, square.bottom, square.left] {
            let checked = face
                .check(&mut arena, &context)
                .expect("checked square face");
            let evidence = checked.native_evidence().expect("native face");
            assert_eq!(
                equal_values(&arena, evidence, unit),
                Convertibility::Convertible
            );
        }
        assert_eq!(square.filler.depth, Depth(8));
        square
            .filler
            .head
            .check(&mut arena, &context)
            .expect("identity of composites");
        let wrong = guarded(a);
        assert!(matches!(
            symmetry(&mut arena, &context, path, &wrong, budget()),
            Err(HigherError::Relation(RelationError::Typing(_)))
        ));
        // A neutral inhabitant of Unit is valid evidence, but the parent's
        // native transport does not reduce this non-reflexive proof-index action.
        assert!(matches!(
            symmetry(
                &mut arena,
                &context,
                Cell {
                    evidence: x,
                    ..path
                },
                &higher,
                budget()
            ),
            Err(HigherError::NeutralTransport)
        ));
    }
}

#[test]
fn non_productive_certificate_is_refused()
{
    let mut arena = TermArena::new();
    let unit_type = arena.value_type_unit();
    let code = arena.value_quote(unit_type);
    let unit = arena.value_unit();
    let cell = Cell {
        code,
        left: unit,
        right: unit,
        evidence: unit,
    };
    let direct = Codata {
        nodes: vec![Layer::Redirect(HigherId(0))],
        root: HigherId(0),
    };
    assert!(matches!(
        direct.observe(&mut arena, &[], cell, cell, budget()),
        Err(HigherError::NonProductive(HigherId(0)))
    ));
    let indirect = Codata {
        nodes: vec![Layer::Redirect(HigherId(1)), Layer::Redirect(HigherId(0))],
        root: HigherId(0),
    };
    assert!(matches!(
        indirect.observe(&mut arena, &[], cell, cell, budget()),
        Err(HigherError::NonProductive(HigherId(0)))
    ));
    let productive = guarded(unit);
    let observed = productive
        .observe(&mut arena, &[], cell, cell, budget())
        .expect("guarded cycle");
    assert_eq!(observed.depth, Depth(8));
    assert_eq!(observed.head.left, unit);
    assert_eq!(observed.head.right, unit);
    assert!(matches!(
        productive.observe(&mut arena, &[], cell, cell, ObservationBudget {
            replay: ReplayBudget::from(7_u64),
            ..budget()
        }),
        Err(HigherError::DepthBound)
    ));
    assert!(matches!(
        productive.observe(&mut arena, &[], cell, cell, ObservationBudget {
            replay: ReplayBudget::from(0_u64),
            ..budget()
        }),
        Err(HigherError::DepthBound)
    ));
    assert!(matches!(
        productive.observe(&mut arena, &[], cell, cell, ObservationBudget {
            depth: Depth(0),
            ..budget()
        }),
        Err(HigherError::ZeroDepth)
    ));
    let late = Codata {
        nodes: vec![
            Layer::Guard {
                evidence: unit,
                tail: HigherId(1),
            },
            Layer::Redirect(HigherId(1)),
        ],
        root: HigherId(0),
    };
    let one = ObservationBudget {
        depth: Depth(1),
        ..budget()
    };
    assert_eq!(
        late.observe(&mut arena, &[], cell, cell, one)
            .expect("only observed prefix")
            .depth,
        Depth(1)
    );
    assert!(matches!(
        late.observe(&mut arena, &[], cell, cell, budget()),
        Err(HigherError::NonProductive(HigherId(1)))
    ));
    let missing = Codata {
        nodes: vec![Layer::Guard {
            evidence: unit,
            tail: HigherId(1),
        }],
        root: HigherId(0),
    };
    assert!(matches!(
        missing.observe(&mut arena, &[], cell, cell, budget()),
        Err(HigherError::UnknownLayer(HigherId(1)))
    ));
    let injected = arena.value_injection(Side::Left, unit);
    let corrupt = Codata {
        nodes: vec![
            Layer::Guard {
                evidence: unit,
                tail: HigherId(1),
            },
            Layer::Guard {
                evidence: injected,
                tail: HigherId(1),
            },
        ],
        root: HigherId(0),
    };
    assert!(matches!(
        corrupt.observe(&mut arena, &[], cell, cell, budget()),
        Err(HigherError::Relation(RelationError::Typing(_)))
    ));
    let routed = Codata {
        nodes: vec![Layer::Redirect(HigherId(1)), Layer::Guard {
            evidence: unit,
            tail: HigherId(0),
        }],
        root: HigherId(0),
    };
    assert_eq!(
        routed
            .observe(&mut arena, &[], cell, cell, ObservationBudget {
                depth: Depth(4),
                ..budget()
            })
            .expect("redirect after each guard")
            .depth,
        Depth(4)
    );
    assert!(matches!(
        routed.observe(&mut arena, &[], cell, cell, budget()),
        Err(HigherError::DepthBound)
    ));
}

#[test]
fn higher_fibres_preserve_boundaries()
{
    let mut arena = TermArena::new();
    let unit_type = arena.value_type_unit();
    let boolean = arena.value_type_sum(unit_type, unit_type);
    let product = arena.value_type_product(boolean, boolean);
    let code = arena.value_quote(product);
    let unit = arena.value_unit();
    let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
    let truth = arena.value_injection(Side::Left, unit);
    let falsity = arena.value_injection(Side::Right, unit);
    let value = arena.value_pair(truth, falsity);
    let p = arena.value_pair(unit, variable);
    let q = arena.value_pair(variable, unit);
    let evidence = arena.value_pair(unit, unit);
    let left = Cell {
        code,
        left: value,
        right: value,
        evidence: p,
    };
    let right = Cell {
        evidence: q,
        ..left
    };
    let higher = guarded(evidence);
    let observed = higher
        .observe(&mut arena, &[unit_type], left, right, budget())
        .expect("product higher fibre");
    assert_eq!(observed.head.left, p);
    assert_eq!(observed.head.right, q);
    assert_eq!(observed.head.evidence, evidence);
    observed
        .head
        .check(&mut arena, &[unit_type])
        .expect("same recursion on product fibre");
    let erased = guarded(unit);
    assert!(matches!(
        erased.observe(&mut arena, &[unit_type], left, right, budget()),
        Err(HigherError::Relation(RelationError::Typing(_)))
    ));
    let invalid = arena.value_pair(unit, truth);
    assert!(matches!(
        higher.observe(
            &mut arena,
            &[unit_type],
            left,
            Cell {
                evidence: invalid,
                ..right
            },
            budget()
        ),
        Err(HigherError::Relation(RelationError::Typing(_)))
    ));
    let other = arena.value_pair(truth, truth);
    assert!(matches!(
        higher.observe(
            &mut arena,
            &[unit_type],
            left,
            Cell {
                right: other,
                ..right
            },
            budget()
        ),
        Err(HigherError::Boundary)
    ));
    assert!(matches!(
        Cell {
            right: other,
            ..left
        }
        .check(&mut arena, &[unit_type]),
        Err(HigherError::Relation(RelationError::Typing(_)))
    ));
    let bool_code = arena.value_quote(boolean);
    let bool_relation = relation(&arena, bool_code).expect("Bool relation");
    let diagonal = bool_relation
        .reflexivity(&mut arena, &[boolean], variable)
        .expect("suspended diagonal");
    assert!(matches!(
        diagonal.native_evidence(),
        Err(RelationError::NeutralFiber)
    ));
    let integer = arena.value_type_base(BaseType::Integer);
    let integer_code = arena.value_quote(integer);
    let other_variable = arena.value_variable(DeBruijnIndex::from(1_u32));
    assert!(matches!(
        Cell {
            code: integer_code,
            left: variable,
            right: other_variable,
            evidence: unit
        }
        .check(&mut arena, &[integer, integer]),
        Err(HigherError::Relation(RelationError::NeutralFiber))
    ));
}
