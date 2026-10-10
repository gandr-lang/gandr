//! Certificate observations share the parent's independent engine fixtures.

use alloc::vec;

use anodized::spec;
use gandr_kernel_conversion_trace::ConversionDecision;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::ValueId;

use super::apply;
use super::boolean;
use super::engine;
use super::equivalence;
use super::inlined_triple_negation;
use crate::error::KernelError;
use crate::higher_field::Codata;
use crate::higher_field::CoherenceEvidence;
use crate::higher_field::Depth;
use crate::higher_field::HigherError;
use crate::higher_field::HigherId;
use crate::higher_field::Layer;
use crate::higher_field::ObservationBudget;
use crate::higher_field::PointwiseEvidence;
use crate::higher_field::Reduction;
use crate::higher_field::unfold;
use crate::identity_recursion::RelationError;
use crate::path_universe::Dialogue;
use crate::path_universe::PathError;
use crate::replay::EngineClaim;
use crate::replay::KernelVerdict;
use crate::replay::ReplayBudget;
use crate::replay::ReplayNode;

/// A single guard reused at arbitrary finite observation depth.
///
/// # Specification
/// trivial.
fn higher(unit: ValueId) -> Codata
{
    Codata {
        nodes: vec![Layer::Guard {
            evidence: unit,
            tail: HigherId(0),
        }],
        root: HigherId(0),
    }
}

/// Ask the independent engine for a proposed translator reduction.
///
/// # Specification
/// - requires: the proposed sample computation belongs to the fixture fragment.
/// - ensures: retains `value` and a portable trace from the separate engine.
/// - provides: an untrusted proposed translator reduction.
/// - panics: if the fixed fixture fails in that engine.
///
/// # Adequacy
/// - hypothesis: L3 — the kernel independently replays each proposed output.
/// - witness: `path_universe::tests::higher_field_tests::certificate_identity_unfolds`
#[spec(ensures: |ret| ret.value == value && ret.dialogue.0.iter().all(|step| match *step {
    ConversionDecision::ReduceLeft { redex } | ConversionDecision::ReduceRight { redex } => redex == ReplayNode::Other,
    ConversionDecision::ConstShortcut { constant } | ConversionDecision::Unfold { constant } | ConversionDecision::Postpone { constant } | ConversionDecision::Freeze { constant, .. } => constant == ReplayNode::Other,
    ConversionDecision::EtaExpand { variable, .. } => variable == ReplayNode::Other,
    ConversionDecision::Force { thunk } => thunk == ReplayNode::Other,
    ConversionDecision::ComparedShared { left, right } => left == ReplayNode::Other && right == ReplayNode::Other,
    ConversionDecision::Decompose | ConversionDecision::NegativeSubgoal { .. } => true,
}))]
fn reduction(
    arena: &mut TermArena,
    map: ValueId,
    input: ValueId,
    value: ValueId,
) -> Reduction
{
    let applied = apply(arena, map, input);
    let returned = arena.computation_return(value);
    let (claim, dialogue) = engine(arena, applied, returned);
    assert_eq!(claim, EngineClaim::Convertible);
    Reduction { value, dialogue }
}

/// Ask the independent engine for a composite's round-trip dialogue.
///
/// # Specification
/// - requires: the fixed composite is well-typed in the fixture fragment.
/// - ensures: the engine evaluates both translators against the input and
///   erases syntax-arena anchors from its returned dialogue.
/// - provides: untrusted evidence for independent higher-field replay.
/// - panics: if the fixed round trip fails in that engine.
///
/// # Adequacy
/// - hypothesis: L3 — both composed legs remain in the replay obligation.
/// - witness: `path_universe::tests::higher_field_tests::certificate_identity_unfolds`
#[spec(ensures: |ret| ret.0.iter().all(|step| match *step {
    ConversionDecision::ReduceLeft { redex } | ConversionDecision::ReduceRight { redex } => redex == ReplayNode::Other,
    ConversionDecision::ConstShortcut { constant } | ConversionDecision::Unfold { constant } | ConversionDecision::Postpone { constant } | ConversionDecision::Freeze { constant, .. } => constant == ReplayNode::Other,
    ConversionDecision::EtaExpand { variable, .. } => variable == ReplayNode::Other,
    ConversionDecision::Force { thunk } => thunk == ReplayNode::Other,
    ConversionDecision::ComparedShared { left, right } => left == ReplayNode::Other && right == ReplayNode::Other,
    ConversionDecision::Decompose | ConversionDecision::NegativeSubgoal { .. } => true,
}))]
fn round_trip(
    arena: &mut TermArena,
    first: ValueId,
    second: ValueId,
    input: ValueId,
) -> Dialogue
{
    let first = apply(arena, first, input);
    let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
    let second = apply(arena, second, variable);
    let composite = arena.computation_bind(first, second);
    let expected = arena.computation_return(input);
    let (claim, dialogue) = engine(arena, composite, expected);
    assert_eq!(claim, EngineClaim::Convertible);
    dialogue
}

#[test]
fn certificate_identity_unfolds()
{
    let mut arena = TermArena::new();
    let boolean = boolean(&mut arena);
    let thrice = inlined_triple_negation(&mut arena);
    let left = equivalence(&mut arena, boolean, boolean.not, boolean.not);
    let right = equivalence(&mut arena, boolean, boolean.not, thrice);
    let budget = ObservationBudget {
        depth: Depth(6),
        replay: ReplayBudget::DEFAULT,
    };
    let identity = unfold(&mut arena, left, right, budget.replay).expect("record identity type");
    let unit = arena.value_unit();
    for (input, opposite) in [
        (boolean.truth, boolean.falsity),
        (boolean.falsity, boolean.truth),
    ] {
        for (field, first, second) in [
            (identity.forward, boolean.not, boolean.not),
            (identity.backward, boolean.not, thrice),
        ] {
            let left = reduction(&mut arena, first, input, opposite);
            let right = reduction(&mut arena, second, input, opposite);
            let evidence = PointwiseEvidence {
                left,
                right,
                identity: unit,
                higher: higher(unit),
            };
            let prefix = field
                .observe(&mut arena, input, &evidence, budget)
                .expect("pointwise identity");
            assert_eq!(prefix.depth, Depth(6));
            assert_eq!(prefix.head.left, unit);
            assert_eq!(prefix.head.right, unit);
            let mut wrong = evidence.clone();
            wrong.right.value = input;
            assert!(matches!(
                field.observe(&mut arena, input, &wrong, budget),
                Err(HigherError::Replay(_))
            ));
            wrong.right = evidence.right.clone();
            wrong.identity = input;
            assert!(matches!(
                field.observe(&mut arena, input, &wrong, budget),
                Err(HigherError::Relation(RelationError::Typing(_)))
            ));
            assert!(matches!(
                field.observe(&mut arena, unit, &evidence, budget),
                Err(HigherError::Relation(RelationError::Typing(_)))
            ));
        }
        for (field, first, second) in [
            (identity.source_coherence, boolean.not, thrice),
            (identity.target_coherence, thrice, boolean.not),
        ] {
            let left = round_trip(&mut arena, boolean.not, boolean.not, input);
            let right = round_trip(&mut arena, first, second, input);
            let evidence = CoherenceEvidence {
                left,
                right,
                higher: higher(unit),
            };
            let prefix = field
                .observe(&mut arena, input, &evidence, budget)
                .expect("round-trip higher coherence");
            assert_eq!(prefix.depth, Depth(6));
            assert_eq!(
                crate::conv::equal_values(&arena, prefix.head.left, unit),
                crate::conv::Convertibility::Convertible
            );
            assert_eq!(
                crate::conv::equal_values(&arena, prefix.head.right, unit),
                crate::conv::Convertibility::Convertible
            );
            let mut wrong = evidence.clone();
            wrong.right.0.push(ConversionDecision::Decompose);
            assert!(matches!(
                field.observe(&mut arena, input, &wrong, budget),
                Err(HigherError::Replay(KernelVerdict::Declined(_)))
            ));
            wrong.right = evidence.right.clone();
            wrong.higher = Codata {
                nodes: vec![Layer::Redirect(HigherId(0))],
                root: HigherId(0),
            };
            assert!(matches!(
                field.observe(&mut arena, input, &wrong, budget),
                Err(HigherError::NonProductive(HigherId(0)))
            ));
        }
    }
    // Identity observations do not alter the structural conversion boundary.
    assert_eq!(
        crate::conv::equal_values(&arena, left, right),
        crate::conv::Convertibility::Distinct
    );
    let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
    let returned = arena.computation_return(variable);
    let lambda = arena.computation_lambda(returned);
    let id = arena.value_thunk(lambda);
    let other = equivalence(&mut arena, boolean, id, id);
    let other = unfold(&mut arena, left, other, budget.replay).expect("identity map certificate");
    let evidence = PointwiseEvidence {
        left: reduction(&mut arena, boolean.not, boolean.truth, boolean.falsity),
        right: reduction(&mut arena, id, boolean.truth, boolean.truth),
        identity: unit,
        higher: higher(unit),
    };
    assert!(matches!(
        other
            .forward
            .observe(&mut arena, boolean.truth, &evidence, budget),
        Err(HigherError::Relation(RelationError::Typing(_)))
    ));
    let classifier = arena.value_type_path_universe(boolean.code, boolean.code);
    let missing = arena.value_path_equiv(
        classifier,
        boolean.not,
        boolean.not,
        alloc::sync::Arc::default(),
    );
    assert!(
        matches!(unfold(&mut arena, left, missing, budget.replay), Err(HigherError::Relation(RelationError::Typing(error))) if matches!(*error, KernelError::Path(PathError::Coverage(_))))
    );
    let refl = arena.value_path_refl(boolean.code);
    assert!(matches!(
        unfold(&mut arena, left, refl, budget.replay),
        Err(HigherError::ExpectedEquivalence)
    ));
    let unit_type = arena.value_type_unit();
    let unit_code = arena.value_quote(unit_type);
    let other = arena.value_path_refl(unit_code);
    assert!(matches!(
        unfold(&mut arena, left, other, budget.replay),
        Err(HigherError::Boundary)
    ));
}
