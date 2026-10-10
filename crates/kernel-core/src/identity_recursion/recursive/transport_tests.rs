//! Independent engine evidence for the lifted Bool negation map.

use alloc::vec;
use alloc::vec::Vec;

use gandr_kernel_term::TermArena;

use super::apply;
use super::boolean;
use super::engine;
use super::equivalence;
use crate::higher_field::Depth;
use crate::higher_field::HigherError;
use crate::identity_recursion::recursive::ListEquivalence;
use crate::identity_recursion::recursive::Progress;
use crate::identity_recursion::recursive::Steps;
use crate::identity_recursion::recursive::TransportEvidence;
use crate::identity_recursion::recursive::tests::list;
use crate::path_universe::Dialogue;
use crate::replay::EngineClaim;
use crate::replay::ReplayBudget;

#[test]
fn negation_transport_computes()
{
    let mut arena = TermArena::new();
    let boolean = boolean(&mut arena);
    let negation = equivalence(&mut arena, boolean, boolean.not, boolean.not);
    let budget = ReplayBudget::from(256_u64);
    let lifted =
        ListEquivalence::form(&mut arena, negation, budget).expect("round trips at formation");
    for (source, target, depth, steps) in [
        (vec![], vec![], 1, 2),
        (vec![boolean.truth], vec![boolean.falsity], 2, 4),
        (
            vec![boolean.falsity, boolean.truth, boolean.falsity],
            vec![boolean.truth, boolean.falsity, boolean.truth],
            4,
            8,
        ),
    ] {
        let heads: Vec<Dialogue> = source
            .iter()
            .zip(&target)
            .map(|(&input, &output)| {
                let applied = apply(&mut arena, boolean.not, input);
                let returned = arena.computation_return(output);
                let (claim, dialogue) = engine(&arena, applied, returned);
                assert_eq!(claim, EngineClaim::Convertible);
                dialogue
            })
            .collect();
        let input = list(&mut arena, &source);
        let output = list(&mut arena, &target);
        let evidence = TransportEvidence {
            output: &output,
            heads: &heads,
        };
        let observed = lifted
            .replay(&mut arena, &input, evidence, budget)
            .expect("map not computes");
        assert_eq!(observed, Progress {
            depth: Depth(depth),
            steps: Steps(steps)
        });
        if !source.is_empty() {
            let wrong = TransportEvidence {
                output: &input,
                heads: &heads,
            };
            assert!(matches!(
                lifted
                    .replay(&mut arena, &input, wrong, budget)
                    .expect_err("wrong output")
                    .reason,
                HigherError::Replay(_)
            ));
            let missing = TransportEvidence {
                output: &output,
                heads: &[],
            };
            assert!(matches!(
                lifted
                    .replay(&mut arena, &input, missing, budget)
                    .expect_err("missing head")
                    .reason,
                HigherError::Boundary
            ));
            let mut corrupt = heads.clone();
            for dialogue in &mut corrupt {
                dialogue
                    .0
                    .push(gandr_kernel_conversion_trace::ConversionDecision::Decompose);
            }
            let corrupt = TransportEvidence {
                output: &output,
                heads: &corrupt,
            };
            assert!(matches!(
                lifted
                    .replay(&mut arena, &input, corrupt, budget)
                    .expect_err("corrupt trace")
                    .reason,
                HigherError::Replay(_)
            ));
        }
        let extra = vec![Dialogue::default(); source.len().saturating_add(1)];
        let extra = TransportEvidence {
            output: &output,
            heads: &extra,
        };
        assert!(matches!(
            lifted
                .replay(&mut arena, &input, extra, budget)
                .expect_err("excess evidence")
                .reason,
            HigherError::Boundary
        ));
    }
    let long_input = list(&mut arena, &vec![boolean.truth; 128]);
    let long_output = list(&mut arena, &vec![boolean.falsity; 128]);
    let applied = apply(&mut arena, boolean.not, boolean.truth);
    let returned = arena.computation_return(boolean.falsity);
    let (claim, dialogue) = engine(&arena, applied, returned);
    assert_eq!(claim, EngineClaim::Convertible);
    let heads = vec![dialogue; 128];
    let evidence = TransportEvidence {
        output: &long_output,
        heads: &heads,
    };
    let refused = lifted
        .replay(
            &mut arena,
            &long_input,
            evidence,
            ReplayBudget::from(256_u64),
        )
        .expect_err("finite observation cap");
    assert!(matches!(refused.reason, HigherError::DepthBound));
    assert_eq!(refused.progress, Progress {
        depth: Depth(128),
        steps: Steps(256)
    });
    assert_eq!(
        lifted
            .replay(
                &mut arena,
                &long_input,
                evidence,
                ReplayBudget::from(258_u64)
            )
            .expect("exact cap"),
        Progress {
            depth: Depth(129),
            steps: Steps(258)
        }
    );
    let nil = list(&mut arena, &[]);
    let mismatch = TransportEvidence {
        output: &nil,
        heads: &heads,
    };
    let refused = lifted
        .replay(&mut arena, &long_input, mismatch, budget)
        .expect_err("constructor mismatch");
    assert!(matches!(refused.reason, HigherError::Boundary));
    assert_eq!(refused.progress, Progress {
        depth: Depth(0),
        steps: Steps(2)
    });
    let classifier = arena.value_type_path_universe(boolean.code, boolean.code);
    let bad = arena.value_path_equiv(
        classifier,
        boolean.not,
        boolean.not,
        alloc::sync::Arc::default(),
    );
    assert!(matches!(
        ListEquivalence::form(&mut arena, bad, budget),
        Err(HigherError::Relation(_))
    ));
    let returned = arena.computation_return(boolean.truth);
    let constant = arena.computation_lambda(returned);
    let constant = arena.value_thunk(constant);
    let bad = equivalence(&mut arena, boolean, constant, constant);
    assert!(matches!(
        ListEquivalence::form(&mut arena, bad, budget),
        Err(HigherError::Relation(_))
    ));
}
