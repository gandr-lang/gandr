//! Explanations and their replay: each true explanation replays, and each
//! forged step meets its own refusal.

use alloc::vec::Vec;

use gandr_theory_coherent_resolutions::Operation;
use gandr_theory_coherent_resolutions::TermPlace;
use gandr_theory_coherent_resolutions::TermTable;
use gandr_theory_e_graphs::Direction;
use gandr_theory_e_graphs::EGraph;
use gandr_theory_e_graphs::EGraphError;
use gandr_theory_e_graphs::EquationPlace;
use gandr_theory_e_graphs::Explanation;
use gandr_theory_e_graphs::Position;
use gandr_theory_e_graphs::ProofPlace;
use gandr_theory_e_graphs::Refusal;
use gandr_theory_e_graphs::StepPlace;
use gandr_theory_e_graphs::StepReason;

use crate::fixtures::op;

/// The operations: three constants, then `f`, then `g`.
const F: usize = 3;
/// The operation `g`.
const G: usize = 4;

/// The terms of the explanation tests.
struct Terms
{
    /// The constant `a`.
    a: TermPlace,
    /// The constant `c`.
    c: TermPlace,
    /// `f(a)`.
    fa: TermPlace,
    /// `f(c)`.
    fc: TermPlace,
    /// `g(f(a))`.
    gfa: TermPlace,
    /// `g(f(c))`.
    gfc: TermPlace,
    /// A constant that no equation names.
    alone: TermPlace,
}

/// The chain `a = b`, `b = c` under `g(f(_))`, rebuilt, with its terms.
///
/// # Specification
/// trivial.
fn chained() -> (EGraph, Terms)
{
    let mut table = TermTable::default();
    let a = op(&mut table, Operation::from(0), &[]);
    let b = op(&mut table, Operation::from(1), &[]);
    let c = op(&mut table, Operation::from(2), &[]);
    let fa = op(&mut table, Operation::from(F), &[a]);
    let fc = op(&mut table, Operation::from(F), &[c]);
    let gfa = op(&mut table, Operation::from(G), &[fa]);
    let gfc = op(&mut table, Operation::from(G), &[fc]);
    let alone = op(&mut table, Operation::from(5), &[]);
    let mut graph = EGraph::new(table, ());
    for term in [gfa, gfc, alone] {
        let _class = graph.add(term).expect("a table term");
    }
    let ab = graph.equation(a, b).expect("a ground equation");
    let cb = graph.equation(c, b).expect("a ground equation");
    for equation in [ab, cb] {
        let _joined = graph.apply(equation, Vec::new()).expect("an instance");
    }
    graph.rebuild().expect("a rebuild");
    (graph, Terms {
        a,
        c,
        fa,
        fc,
        gfa,
        gfc,
        alone,
    })
}

#[test]
fn each_explanation_replays()
{
    let (graph, terms) = chained();
    for (left, right) in [
        (terms.a, terms.c),
        (terms.c, terms.a),
        (terms.fa, terms.fc),
        (terms.gfa, terms.gfc),
        (terms.gfc, terms.gfa),
        (terms.a, terms.a),
    ] {
        let explanation = graph.explain(left, right).expect("one class");
        assert_eq!(
            explanation.replay(graph.table(), graph.equations(), (left, right)),
            Ok(()),
            "{left:?} {right:?}"
        );
    }
    // `c = b` is read backward on the way from `a` to `c`.
    let explanation = graph.explain(terms.a, terms.c).expect("one class");
    let directions: Vec<Direction> = explanation
        .proofs
        .iter()
        .flat_map(|proof| &proof.steps)
        .filter_map(|step| match step.reason {
            StepReason::Input { direction, .. } => Some(direction),
            StepReason::Congruence { .. } => None,
        })
        .collect();
    assert_eq!(directions, [Direction::Forward, Direction::Backward]);
}

/// The explanation of `g(f(a)) = g(f(c))`, with the place of its first proof
/// that holds an input step and the place of its last proof, one congruence
/// whose argument's proof joins `f(a)` to `f(c)`.
///
/// # Specification
/// trivial.
fn nested(
    graph: &EGraph,
    terms: &Terms,
) -> (Explanation, ProofPlace, ProofPlace)
{
    let explanation = graph.explain(terms.gfa, terms.gfc).expect("one class");
    let input = explanation
        .proofs
        .iter()
        .position(|proof| {
            proof
                .steps
                .iter()
                .any(|step| matches!(step.reason, StepReason::Input { .. }))
        })
        .expect("a proof with an input step");
    let last = explanation.proofs.len().checked_sub(1).expect("a proof");
    assert!(
        matches!(
            explanation.proofs[last].steps.as_slice(),
            [step] if matches!(step.reason, StepReason::Congruence { .. })
        ),
        "the last proof is one congruence"
    );
    (explanation, ProofPlace::from(input), ProofPlace::from(last))
}

/// The reason of the first step of the proof at `proof`.
///
/// # Specification
/// trivial.
fn first_reason(
    forged: &mut Explanation,
    proof: ProofPlace,
) -> &mut StepReason
{
    &mut forged.proofs[usize::from(proof)].steps[0].reason
}

#[test]
fn a_forged_step_is_refused_by_name()
{
    let (graph, terms) = chained();
    let (table, equations) = (graph.table(), graph.equations());
    let ends = (terms.gfa, terms.gfc);
    let (truth, input_proof, congruence_proof) = nested(&graph, &terms);
    assert_eq!(truth.replay(table, equations, ends), Ok(()));
    let (input, congruence) = (usize::from(input_proof), usize::from(congruence_proof));
    let first = StepPlace::from(0_usize);
    let forge = |change: &dyn Fn(&mut Explanation)| {
        let mut forged = truth.clone();
        change(&mut forged);
        forged.replay(table, equations, ends)
    };
    assert_eq!(
        Explanation::default().replay(table, equations, ends),
        Err(Refusal::Empty)
    );
    assert_eq!(
        truth.replay(table, equations, (terms.gfa, terms.alone)),
        Err(Refusal::Ends)
    );
    assert_eq!(
        forge(&|forged| {
            if let &mut StepReason::Input {
                ref mut equation, ..
            } = first_reason(forged, input_proof)
            {
                *equation = EquationPlace::from(9_usize);
            }
        }),
        Err(Refusal::UnknownEquation {
            proof: input_proof,
            step: first,
        })
    );
    assert_eq!(
        forge(&|forged| {
            if let &mut StepReason::Input {
                ref mut direction, ..
            } = first_reason(forged, input_proof)
            {
                *direction = direction.flipped();
            }
        }),
        Err(Refusal::NotAnInstance {
            proof: input_proof,
            step: first,
        }),
        "a step read from the wrong side"
    );
    assert_eq!(
        forge(&|forged| {
            if let &mut StepReason::Input {
                ref mut equation, ..
            } = first_reason(forged, input_proof)
            {
                *equation = EquationPlace::from(1_usize - usize::from(*equation));
            }
        }),
        Err(Refusal::NotAnInstance {
            proof: input_proof,
            step: first,
        }),
        "a step that cites the other equation"
    );
    assert_eq!(
        forge(&|forged| forged.proofs[input].to = terms.alone),
        Err(Refusal::Broken { proof: input_proof })
    );
    assert_eq!(
        forge(&|forged| forged.proofs[congruence].steps[0].to = terms.alone),
        Err(Refusal::Incongruent {
            proof: congruence_proof,
            step: first,
        })
    );
    assert_eq!(
        forge(&|forged| {
            if let &mut StepReason::Congruence { ref mut children } =
                first_reason(forged, congruence_proof)
            {
                children[0] = ProofPlace::from(congruence);
            }
        }),
        Err(Refusal::Forward {
            proof: congruence_proof,
            step: first,
            position: Position::from(0_usize),
        })
    );
    assert_eq!(
        forge(&|forged| {
            if let &mut StepReason::Congruence { ref mut children } =
                first_reason(forged, congruence_proof)
            {
                children[0] = ProofPlace::from(input);
            }
        }),
        Err(Refusal::ChildUnexplained {
            proof: congruence_proof,
            step: first,
            position: Position::from(0_usize),
        }),
        "a congruence that cites a proof of other terms"
    );
}

#[test]
fn terms_in_two_classes_have_no_explanation()
{
    let (graph, terms) = chained();
    assert_eq!(
        graph.explain(terms.a, terms.alone),
        Err(EGraphError::Apart(terms.a, terms.alone))
    );
    let unheld = TermPlace::from(99_usize);
    assert_eq!(
        graph.explain(terms.a, unheld),
        Err(EGraphError::Unheld(unheld))
    );
}
