//! Finite recursion, laziness and stratum-boundary witnesses.

use alloc::vec;
use alloc::vec::Vec;

use gandr_kernel_strata::Level;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::Side;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;

use super::Progress;
use super::Steps;
use crate::higher_field::Codata;
use crate::higher_field::Depth;
use crate::higher_field::HigherError;
use crate::higher_field::HigherId;
use crate::higher_field::Layer;
use crate::identity_recursion::Domain;
use crate::identity_recursion::Inhabitation;
use crate::identity_recursion::Mode;
use crate::identity_recursion::RelationError;
use crate::identity_recursion::interpret;
use crate::replay::ReplayBudget;

/// Build raw constructor syntax without deriving an equality verdict.
///
/// # Specification
/// trivial.
pub fn list(
    arena: &mut TermArena,
    values: &[ValueId],
) -> Codata
{
    let unit = arena.value_unit();
    let nil = arena.value_injection(Side::Left, unit);
    let mut nodes = Vec::with_capacity(values.len().saturating_add(1));
    nodes.push(Layer::Guard {
        evidence: nil,
        tail: HigherId(usize::MAX),
    });
    let mut root = HigherId(0);
    for &value in values.iter().rev() {
        let evidence = arena.value_injection(Side::Right, value);
        nodes.push(Layer::Guard {
            evidence,
            tail: root,
        });
        root = HigherId(nodes.len().saturating_sub(1));
    }
    Codata { nodes, root }
}

#[test]
fn list_identity_is_lazy()
{
    let mut arena = TermArena::new();
    let unit = arena.value_type_unit();
    let boolean = arena.value_type_sum(unit, unit);
    let list_type = arena.value_type_list(boolean);
    let code = arena.value_quote(list_type);
    let relation = interpret(&arena, Mode::Identity, Domain::Elements(code))
        .expect("one code fold")
        .elements()
        .expect("recursive relation");
    let unit = arena.value_unit();
    let truth = arena.value_injection(Side::Left, unit);
    let falsity = arena.value_injection(Side::Right, unit);
    for (left, right, fiber, depth, steps) in [
        (vec![], vec![], Inhabitation::Unit, 1, 2),
        (
            vec![truth, falsity, truth],
            vec![truth, falsity, truth],
            Inhabitation::Unit,
            4,
            8,
        ),
        (
            vec![truth, falsity],
            vec![truth, truth],
            Inhabitation::Empty,
            2,
            4,
        ),
        (vec![truth], vec![truth, falsity], Inhabitation::Empty, 2, 4),
    ] {
        let left = list(&mut arena, &left);
        let right = list(&mut arena, &right);
        let observed = relation
            .observe_lists(&mut arena, &left, &right, ReplayBudget::from(steps))
            .expect("finite fibre");
        assert_eq!(observed.fiber, fiber);
        assert_eq!(observed.progress, Progress {
            depth: Depth(depth),
            steps: Steps(steps)
        });
        let refused = relation
            .observe_lists(
                &mut arena,
                &left,
                &right,
                ReplayBudget::from(steps.saturating_sub(1)),
            )
            .expect_err("one missing instruction");
        assert!(matches!(refused.reason, HigherError::DepthBound));
        assert_eq!(refused.progress.steps, Steps(steps.saturating_sub(1)));
    }
    // A distinguishing constructor does not touch either invalid tail.
    let left_head = arena.value_injection(Side::Right, truth);
    let right_head = arena.value_injection(Side::Right, falsity);
    let left = Codata {
        nodes: vec![Layer::Guard {
            evidence: left_head,
            tail: HigherId(999),
        }],
        root: HigherId(0),
    };
    let right = Codata {
        nodes: vec![Layer::Guard {
            evidence: right_head,
            tail: HigherId(999),
        }],
        root: HigherId(0),
    };
    let observed = relation
        .observe_lists(&mut arena, &left, &right, ReplayBudget::from(2_u64))
        .expect("lazy mismatch");
    assert_eq!(observed.fiber, Inhabitation::Empty);
    assert_eq!(observed.progress.depth, Depth(1));
    let non_list = arena.value_quote(boolean);
    let non_list = interpret(&arena, Mode::Identity, Domain::Elements(non_list))
        .expect("Bool fold")
        .elements()
        .expect("relation");
    assert!(matches!(
        non_list
            .observe_lists(&mut arena, &left, &right, ReplayBudget::from(2_u64))
            .expect_err("not List")
            .reason,
        HigherError::Relation(RelationError::Classifier)
    ));
}

#[test]
fn uncertified_stratum_refuses()
{
    let mut arena = TermArena::new();
    let unit_type = arena.value_type_unit();
    let list_type = arena.value_type_list(unit_type);
    let code = arena.value_quote(list_type);
    let relation = interpret(&arena, Mode::Identity, Domain::Elements(code))
        .expect("fold")
        .elements()
        .expect("list");
    let unit = arena.value_unit();
    let head = arena.value_injection(Side::Right, unit);
    let looped = Codata {
        nodes: vec![Layer::Redirect(HigherId(0))],
        root: HigherId(0),
    };
    let refused = relation
        .observe_lists(&mut arena, &looped, &looped, ReplayBudget::from(20_u64))
        .expect_err("no constructor");
    assert!(matches!(
        refused.reason,
        HigherError::NonProductive(HigherId(0))
    ));
    assert_eq!(refused.progress, Progress {
        depth: Depth(0),
        steps: Steps(1)
    });
    let delayed = Codata {
        nodes: vec![
            Layer::Guard {
                evidence: head,
                tail: HigherId(1),
            },
            Layer::Redirect(HigherId(2)),
            Layer::Redirect(HigherId(1)),
        ],
        root: HigherId(0),
    };
    let refused = relation
        .observe_lists(&mut arena, &delayed, &delayed, ReplayBudget::from(20_u64))
        .expect_err("late loop");
    assert!(matches!(
        refused.reason,
        HigherError::NonProductive(HigherId(1))
    ));
    assert_eq!(refused.progress, Progress {
        depth: Depth(1),
        steps: Steps(4)
    });
    let productive = Codata {
        nodes: vec![Layer::Guard {
            evidence: head,
            tail: HigherId(0),
        }],
        root: HigherId(0),
    };
    let refused = relation
        .observe_lists(
            &mut arena,
            &productive,
            &productive,
            ReplayBudget::from(8_u64),
        )
        .expect_err("productivity is not decidability");
    assert!(matches!(refused.reason, HigherError::DepthBound));
    assert_eq!(refused.progress, Progress {
        depth: Depth(4),
        steps: Steps(8)
    });
    let absent = Codata {
        nodes: vec![],
        root: HigherId(2),
    };
    let refused = relation
        .observe_lists(&mut arena, &absent, &productive, ReplayBudget::from(8_u64))
        .expect_err("missing node");
    assert!(matches!(
        refused.reason,
        HigherError::UnknownLayer(HigherId(2))
    ));
    assert_eq!(refused.progress.depth, Depth(0));
    let malformed = Codata {
        nodes: vec![Layer::Guard {
            evidence: unit,
            tail: HigherId(0),
        }],
        root: HigherId(0),
    };
    assert!(matches!(
        relation
            .observe_lists(
                &mut arena,
                &malformed,
                &productive,
                ReplayBudget::from(8_u64)
            )
            .expect_err("unrolled sum required")
            .reason,
        HigherError::Relation(RelationError::Evidence)
    ));
}

#[test]
fn list_code_forms_without_unfolding()
{
    let mut arena = TermArena::new();
    let unit = arena.value_type_unit();
    let list_type = arena.value_type_list(unit);
    let quote = arena.value_quote(list_type);
    let universe = arena.value_type_universe(GroundSort::Value, Level::zero());
    crate::check::check_closed_value(&mut arena, quote, universe)
        .expect("list code at element level");
    assert_eq!(arena.value_type(list_type), Some(&ValueType::List(unit)));
    let other_unit = arena.value_type_unit();
    let other_list = arena.value_type_list(other_unit);
    assert_eq!(
        crate::conv::convertible_value_types(&arena, list_type, other_list),
        crate::conv::Convertibility::Convertible
    );
    assert_eq!(
        crate::conv::convertible_value_types(&arena, list_type, unit),
        crate::conv::Convertibility::Distinct
    );
}
