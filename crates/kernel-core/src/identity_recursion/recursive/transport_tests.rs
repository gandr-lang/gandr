//! Independent engine evidence for the lifted Bool negation map, and native
//! element transport in a List motive.

use alloc::vec;
use alloc::vec::Vec;

use gandr_kernel_strata::Level;
use gandr_kernel_term::Computation;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;

use super::apply;
use super::boolean;
use super::engine;
use super::equivalence;
use super::offer;
use crate::element_identity::ElementTransport;
use crate::element_identity::transport_beta;
use crate::encoding::ContentTable;
use crate::env::Environment;
use crate::higher_field::Depth;
use crate::higher_field::HigherError;
use crate::identity_recursion::recursive::ListEquivalence;
use crate::identity_recursion::recursive::Progress;
use crate::identity_recursion::recursive::Steps;
use crate::identity_recursion::recursive::TransportEvidence;
use crate::identity_recursion::recursive::tests::list;
use crate::path_universe::Dialogue;
use crate::path_universe::Reduction;
use crate::replay::EngineClaim;
use crate::replay::KernelVerdict;
use crate::replay::ReplayBudget;
use crate::replay::ReplayDecline;
use crate::replay::ReplaySides;
use crate::replay::Unfoldings;

/// A native list of `values`, built from its last cell.
///
/// # Specification
/// trivial.
fn cells(
    arena: &mut TermArena,
    values: &[ValueId],
) -> ValueId
{
    let mut list = arena.value_list_nil();
    for &value in values.iter().rev() {
        list = arena.value_list_cons(value, list);
    }
    list
}

/// Replay `transport` against `reduct` with an empty dialogue under `budget`:
/// every step the claim needs is a search-free reduction.
///
/// # Specification
/// trivial.
fn moved(
    arena: &mut TermArena,
    transport: ComputationId,
    reduct: ComputationId,
    budget: ReplayBudget,
) -> KernelVerdict
{
    crate::replay::replay(
        arena,
        &Unfoldings::default(),
        ReplaySides::Computations(transport, reduct),
        EngineClaim::Convertible,
        core::iter::empty(),
        budget,
    )
}

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

#[test]
fn negation_moves_a_list_one_cell_at_a_time()
{
    // The motive `x. List(El x)` checks along an identity at the universe:
    // the input at the source endpoint's list, the result at the target's.
    let mut environment = Environment::new();
    let admitted = offer(&mut environment, |arena| {
        let boolean = boolean(arena);
        let universe = arena.value_type_universe(GroundSort::Value, Level::zero());
        let identity = arena.value_type_path(universe, boolean.code, boolean.code);
        let list_type = arena.value_type_list(boolean.ty);
        let result = arena.comp_type_returner(list_type);
        let arrow = arena.comp_type_arrow(identity, result);
        let declared = arena.value_type_thunk(arrow);
        let endpoint = arena.value_variable(DeBruijnIndex::from(0_u32));
        let element = arena.value_type_element(endpoint, Level::zero());
        let motive = arena.value_type_list(element);
        let input = cells(arena, &[boolean.truth, boolean.falsity]);
        let path = arena.value_variable(DeBruijnIndex::from(0_u32));
        let body = arena.computation_path_transport(motive, path, input);
        let body = arena.computation_lambda(body);
        (declared, arena.value_thunk(body))
    });
    assert!(admitted.is_ok(), "{admitted:?}");

    let mut arena = TermArena::new();
    let boolean = boolean(&mut arena);
    let negation = equivalence(&mut arena, boolean, boolean.not, boolean.not);
    let endpoint = arena.value_variable(DeBruijnIndex::from(0_u32));
    let element = arena.value_type_element(endpoint, Level::zero());
    let motive = arena.value_type_list(element);
    let (truth, falsity) = (boolean.truth, boolean.falsity);
    for (source, target) in [
        (vec![], vec![]),
        (vec![truth], vec![falsity]),
        (vec![truth, falsity, truth], vec![falsity, truth, falsity]),
    ] {
        let input = cells(&mut arena, &source);
        let output = cells(&mut arena, &target);
        let transport = arena.computation_path_transport(motive, negation, input);
        let expected = arena.computation_return(output);
        assert_eq!(
            moved(&mut arena, transport, expected, ReplayBudget::DEFAULT),
            KernelVerdict::Convertible
        );
        if !source.is_empty() {
            let unmoved = arena.computation_return(input);
            assert_ne!(
                moved(&mut arena, transport, unmoved, ReplayBudget::DEFAULT),
                KernelVerdict::Convertible
            );
        }
    }

    // One step unfolds one cell: the reduct transports the head and binds a
    // transport of the tail as it stands, so an open tail is never read.
    let tail = arena.value_variable(DeBruijnIndex::from(0_u32));
    let open = arena.value_list_cons(truth, tail);
    let mut table = ContentTable::new();
    let mut memo = gandr_kernel_check_memo::NullMemo;
    let step = transport_beta(&mut arena, &mut table, &mut memo, ElementTransport {
        motive,
        path: negation,
        value: open,
    });
    let Ok(Reduction::Reduced(reduct)) = step
    else {
        panic!("a cell reduces: {step:?}");
    };
    let Some(&Computation::Bind(head, rest)) = arena.computation(reduct)
    else {
        panic!("the head is bound first");
    };
    assert!(matches!(
        arena.computation(head),
        Some(&Computation::PathTransport { motive: part, path, value })
            if part == element && path == negation && value == truth
    ));
    let Some(&Computation::Bind(rest, _)) = arena.computation(rest)
    else {
        panic!("the tail is bound second");
    };
    assert!(matches!(
        arena.computation(rest),
        Some(&Computation::PathTransport { value, .. })
            if arena.value(value) == Some(&Value::Variable(DeBruijnIndex::from(1_u32)))
    ));

    // A list costs the replay its length: past the budget the transport
    // declines, never refutes.
    let long_source = cells(&mut arena, &vec![truth; 64]);
    let long_target = cells(&mut arena, &vec![falsity; 64]);
    let transport = arena.computation_path_transport(motive, negation, long_source);
    let expected = arena.computation_return(long_target);
    assert_eq!(
        moved(&mut arena, transport, expected, ReplayBudget::DEFAULT),
        KernelVerdict::Convertible
    );
    assert_eq!(
        moved(&mut arena, transport, expected, ReplayBudget::from(64_u64)),
        KernelVerdict::Declined(ReplayDecline::Budget)
    );
}
