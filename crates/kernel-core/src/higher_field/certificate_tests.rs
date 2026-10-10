//! Certificate observations share the parent's independent engine fixtures.

use alloc::vec;

use gandr_kernel_conversion_trace::ConversionDecision;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::ValueId;

use super::apply;
use super::boolean;
use super::engine;
use super::equivalence;
use super::inlined_triple_negation;
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
use crate::path_universe::Path;
use crate::path_universe::PathError;
use crate::path_universe::Paths;
use crate::path_universe::RoundTrips;
use crate::path_universe::convert;
use crate::replay::EngineClaim;
use crate::replay::KernelVerdict;
use crate::replay::ReplayBudget;

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
/// - ensures: the trace comes from the separate conversion engine.
/// - panics: if the fixed fixture fails in that engine.
///
/// # Adequacy
/// - hypothesis: L3 — the kernel independently replays each proposed output.
/// - witness: `path_universe::tests::higher_field_tests::certificate_identity_unfolds`
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
/// - ensures: the engine evaluates both translators against the input.
/// - panics: if the fixed round trip fails in that engine.
///
/// # Adequacy
/// - hypothesis: L3 — both composed legs remain in the replay obligation.
/// - witness: `path_universe::tests::higher_field_tests::certificate_identity_unfolds`
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
    let mut paths = Paths::new();
    let left = equivalence(&mut arena, &mut paths, &boolean, boolean.not, boolean.not);
    let right = equivalence(&mut arena, &mut paths, &boolean, boolean.not, thrice);
    let budget = ObservationBudget {
        depth: Depth(6),
        replay: ReplayBudget::DEFAULT,
    };
    let identity =
        unfold(&mut arena, &paths, left, right, budget.replay).expect("record identity type");
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
        convert(&arena, &paths, left, right, budget.replay).expect("structural comparison"),
        KernelVerdict::NotConvertible
    );
    let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
    let returned = arena.computation_return(variable);
    let lambda = arena.computation_lambda(returned);
    let id = arena.value_thunk(lambda);
    let other = equivalence(&mut arena, &mut paths, &boolean, id, id);
    let other =
        unfold(&mut arena, &paths, left, other, budget.replay).expect("identity map certificate");
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
    let missing = paths
        .push(Path::Equiv {
            source: boolean.code,
            target: boolean.code,
            forward: boolean.not,
            backward: boolean.not,
            round_trips: RoundTrips::default(),
        })
        .expect("raw missing dialogues");
    assert!(
        matches!(unfold(&mut arena, &paths, left, missing, budget.replay), Err(HigherError::Path(error)) if matches!(*error, PathError::Coverage(_)))
    );
    let refl = paths.push(Path::Refl(boolean.code)).expect("raw refl");
    assert!(matches!(
        unfold(&mut arena, &paths, left, refl, budget.replay),
        Err(HigherError::ExpectedEquivalence)
    ));
    let unit_type = arena.value_type_unit();
    let unit_code = arena.value_quote(unit_type);
    let other = paths.push(Path::Refl(unit_code)).expect("other endpoints");
    assert!(matches!(
        unfold(&mut arena, &paths, left, other, budget.replay),
        Err(HigherError::Boundary)
    ));
}
