//! The universe clause reaches native paths without erasing certificate action.

use alloc::vec;

use gandr_kernel_strata::Level;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;

use super::apply;
use super::boolean;
use super::engine;
use super::equivalence;
use crate::conv::Convertibility;
use crate::conv::convertible_value_types;
use crate::higher_field::Codata;
use crate::higher_field::Depth;
use crate::higher_field::HigherError;
use crate::higher_field::HigherId;
use crate::higher_field::Layer;
use crate::higher_field::ObservationBudget;
use crate::higher_field::PointwiseEvidence;
use crate::higher_field::Reduction;
use crate::identity_recursion::Domain;
use crate::identity_recursion::Fiber;
use crate::identity_recursion::Interpretation;
use crate::identity_recursion::Mode;
use crate::identity_recursion::RelationError;
use crate::identity_recursion::Transport;
use crate::identity_recursion::interpret;
use crate::identity_recursion::recursive::tests::list;
use crate::path_universe;
use crate::replay::EngineClaim;
use crate::replay::KernelVerdict;
use crate::replay::ReplayBudget;

#[test]
fn universe_clause_is_native()
{
    let mut arena = TermArena::new();
    let boolean = boolean(&mut arena);
    let universe = arena.value_type_universe(GroundSort::Value, Level::zero());
    let universe_code = arena.value_quote(universe);
    let Interpretation::Elements(relation) =
        interpret(&arena, Mode::Identity, Domain::Elements(universe_code)).expect("universe fold")
    else {
        panic!("a code of codes contributes an element clause");
    };
    let budget = ReplayBudget::DEFAULT;
    let fiber = relation
        .fiber(&mut arena, &[], boolean.code, boolean.code)
        .expect("code identity");
    assert!(matches!(fiber.get(fiber.root()), Ok(Fiber::Universe(..))));
    let folded = fiber.native(&mut arena).expect("native universe fibre");
    let native = arena.value_type_path_universe(boolean.code, boolean.code);
    assert_eq!(
        convertible_value_types(&arena, folded, native),
        Convertibility::Convertible
    );
    let unit_type = arena.value_type_unit();
    assert_eq!(
        convertible_value_types(&arena, folded, unit_type),
        Convertibility::Distinct
    );
    let unit = arena.value_unit();
    assert!(matches!(
        relation.witness(&mut arena, &[], boolean.code, boolean.code, unit),
        Err(RelationError::Typing(_))
    ));

    let reflexive = relation
        .reflexivity(&mut arena, &[], boolean.code)
        .expect("native reflexivity");
    let refl = reflexive.native_evidence().expect("native proof");
    assert!(matches!(arena.value(refl), Some(&Value::PathRefl(code)) if code == boolean.code));
    let negation = equivalence(&mut arena, boolean, boolean.not, boolean.not);
    let identity = relation
        .witness(&mut arena, &[], boolean.code, boolean.code, negation)
        .expect("nontrivial code identity");
    let applied = apply(&mut arena, boolean.not, boolean.truth);
    let expected = arena.computation_return(boolean.falsity);
    let (claim, dialogue) = engine(&arena, applied, expected);
    assert_eq!(claim, EngineClaim::Convertible);
    assert_eq!(
        path_universe::replay_transport(
            &mut arena,
            path_universe::Transport {
                path: identity.native_evidence().expect("certificate"),
                value: boolean.truth
            },
            expected,
            claim,
            &dialogue,
            budget,
        )
        .expect("native translator replay"),
        KernelVerdict::Convertible
    );
    let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
    let motive = arena.value_type_element(variable, Level::zero());
    assert!(matches!(
        relation
            .transport(&mut arena, &[], &identity, motive, boolean.truth)
            .expect("nontrivial action remains explicit"),
        Transport::Neutral { .. }
    ));
    assert!(
        matches!(relation.transport(&mut arena, &[], &reflexive, motive, boolean.truth).expect("reflexive action"), Transport::Return(value) if value == boolean.truth)
    );
    assert!(matches!(
        relation.compose(&mut arena, &[], &identity, &identity),
        Err(RelationError::CertificateOperationRequired)
    ));

    let nested = arena.value_type_product(universe, unit_type);
    let nested_code = arena.value_quote(nested);
    let Interpretation::Elements(nested_relation) =
        interpret(&arena, Mode::Identity, Domain::Elements(nested_code)).expect("nested universe")
    else {
        panic!("element clause")
    };
    let pair = arena.value_pair(boolean.code, unit);
    let nested_fiber = nested_relation
        .fiber(&mut arena, &[], pair, pair)
        .expect("nested fibre")
        .native(&mut arena)
        .expect("nested native fibre");
    let expected_nested = arena.value_type_product(native, unit_type);
    assert_eq!(
        convertible_value_types(&arena, nested_fiber, expected_nested),
        Convertibility::Convertible
    );
    let projected = nested_relation
        .fiber(&mut arena, &[nested], variable, variable)
        .expect("open product fibre");
    assert!(matches!(
        projected.native(&mut arena),
        Err(RelationError::NeutralFiber)
    ));
    let sum = arena.value_type_sum(universe, unit_type);
    let sum_code = arena.value_quote(sum);
    let sums = interpret(&arena, Mode::Identity, Domain::Elements(sum_code))
        .expect("sum containing codes")
        .elements()
        .expect("element clause");
    let diagonal = sums
        .reflexivity(&mut arena, &[sum], variable)
        .expect("suspended diagonal");
    assert!(
        matches!(sums.transport(&mut arena, &[sum], &diagonal, unit_type, unit)
        .expect("suspended reflexivity still computes"), Transport::Return(value) if value == unit)
    );

    let list_type = arena.value_type_list(universe);
    let list_code = arena.value_quote(list_type);
    let Interpretation::Elements(lists) =
        interpret(&arena, Mode::Identity, Domain::Elements(list_code)).expect("list of codes")
    else {
        panic!("list clause")
    };
    let unit_code = arena.value_quote(unit_type);
    let left = list(&mut arena, &[unit_code]);
    let right = list(&mut arena, &[boolean.code]);
    let refusal = lists
        .observe_lists(&mut arena, &left, &right, budget)
        .expect_err("code syntax inequality is not Empty");
    assert!(matches!(
        refusal.reason,
        HigherError::Relation(RelationError::CertificateOperationRequired)
    ));

    let path_code = arena.value_quote(native);
    let Interpretation::Elements(higher) =
        interpret(&arena, Mode::Identity, Domain::Elements(path_code)).expect("certificate clause")
    else {
        panic!("higher clause")
    };
    let higher = higher
        .fiber(&mut arena, &[], negation, negation)
        .expect("higher obligations");
    assert!(matches!(
        higher.native(&mut arena),
        Err(RelationError::HigherFieldRequired)
    ));
    let fields = higher
        .certificate(&mut arena, budget)
        .expect("native four-field record");
    let evidence = PointwiseEvidence {
        left: Reduction {
            value: boolean.falsity,
            dialogue: dialogue.clone(),
        },
        right: Reduction {
            value: boolean.falsity,
            dialogue,
        },
        identity: unit,
        higher: Codata {
            nodes: vec![Layer::Guard {
                evidence: unit,
                tail: HigherId(0),
            }],
            root: HigherId(0),
        },
    };
    let observed = fields
        .forward
        .observe(&mut arena, boolean.truth, &evidence, ObservationBudget {
            depth: Depth(2),
            replay: budget,
        })
        .expect("forward field replay");
    assert_eq!(observed.depth, Depth(2));
    let wrong = PointwiseEvidence {
        identity: boolean.truth,
        ..evidence
    };
    assert!(matches!(
        fields
            .forward
            .observe(&mut arena, boolean.truth, &wrong, ObservationBudget {
                depth: Depth(2),
                replay: budget
            }),
        Err(HigherError::Relation(_))
    ));
    assert!(matches!(
        fiber.certificate(&mut arena, budget),
        Err(HigherError::Relation(RelationError::Classifier))
    ));
    assert!(matches!(
        interpret(&arena, Mode::Bridge, Domain::Elements(universe_code)),
        Err(RelationError::UnsupportedType(_))
    ));
}
