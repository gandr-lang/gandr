//! The precedence DAG: the specification builder's refusals, the strict
//! relation and the reflexive associativity cases, the virtual bounds, cycle
//! evidence, the fingerprint and the linear extension.

use alloc::collections::BTreeSet;
use core::error::Error;

use anodized::spec;
use gandr_theory_graphs::Assoc;
use gandr_theory_graphs::Bound;
use gandr_theory_graphs::NodeCount;
use gandr_theory_graphs::Prec;
use gandr_theory_graphs::PrecCycle;
use gandr_theory_graphs::PrecDag;
use gandr_theory_graphs::PrecDagError;
use gandr_theory_graphs::PrecGroupCount;
use gandr_theory_graphs::PrecIndex;
use gandr_theory_graphs::PrecSpec;
use gandr_theory_graphs::PrecSpecError;
use proptest::prelude::*;

/// Builds the diamond `tight > left-mid, right-mid > loose`, with the two
/// middle groups left- and right-associative.
///
/// # Specification
/// - requires: nothing.
/// - ensures: returns the DAG and its groups in the order loose, left-mid,
///   right-mid, tight.
/// - fails: never for this fixed relation.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For this fixed four-group fixture, the output observer checks
///   dense identities, associations and every diamond edge. L3 pair, name and
///   boundary observations distinguish a chain mistaken for a diamond or
///   swapped middle groups. The witness is finite and does not establish
///   behavior of arbitrary precedence relations.
/// - witness: `tests::prec::prec_dag_contract`
/// - witness: `tests::prec::prec_dag_size_and_boundary_contract`
#[spec(ensures: |ref result| result.as_ref().is_ok_and(|&(ref dag, [loose, left_mid, right_mid, tight])|
    usize::from(dag.len()) == 4
    && [loose, left_mid, right_mid, tight].into_iter().map(|prec| u16::from(prec.index())).eq(0_u16..4)
    && dag.assoc(loose) == Some(Assoc::Non) && dag.assoc(left_mid) == Some(Assoc::Left)
    && dag.assoc(right_mid) == Some(Assoc::Right) && dag.assoc(tight) == Some(Assoc::Non)
    && dag.edges().eq([(left_mid, loose), (right_mid, loose), (tight, left_mid), (tight, right_mid)])))]
fn diamond() -> Result<(PrecDag, [Prec; 4]), Box<dyn Error>>
{
    let mut spec = PrecSpec::new();
    let loose = spec.insert("loose", Assoc::Non)?;
    let left_mid = spec.insert("left-mid", Assoc::Left)?;
    let right_mid = spec.insert("right-mid", Assoc::Right)?;
    let tight = spec.insert("tight", Assoc::Non)?;
    spec.add_edge(tight, left_mid)?;
    spec.add_edge(tight, right_mid)?;
    spec.add_edge(left_mid, loose)?;
    spec.add_edge(right_mid, loose)?;
    let dag = PrecDag::build(&spec)?;
    Ok((dag, [loose, left_mid, right_mid, tight]))
}

/// Builds a chain of groups `p0 < p1 < …`, one per associativity given, each
/// tighter than the one before.
///
/// # Specification
/// - requires: the association count fits the group-identity capacity.
/// - ensures: returns the DAG and its groups in insertion order.
/// - fails: a builder refuses the fixture.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For association sequences within group capacity, the predicate
///   observes dense identities, each association, the complete chain and
///   reverse linear extension. L3 integer-chain and L2 generated association
///   comparisons distinguish omitted links and an incorrect reflexive policy.
///   Allocation refusal and sequences beyond the fixture domain are not
///   generated.
/// - witness: `tests::prec::prec_integer_chain_oracle`
/// - witness: `tests::prec::lt_gt_duality_for_distinct_chain_nodes`
/// - witness: `tests::prec::associativity_affects_reflexive_pairs_only`
#[spec(
    requires: assocs.len() <= usize::from(u16::MAX).saturating_add(1),
    ensures: |ref result| result.as_ref().is_ok_and(|pair| pair.1.len() == assocs.len()
        && usize::from(pair.0.len()) == assocs.len()
        && pair.1.iter().enumerate().all(|(position, &prec)| usize::from(u16::from(prec.index())) == position
            && pair.0.assoc(prec) == assocs.get(position).copied())
        && pair.0.edges().eq(pair.1.iter().copied().zip(pair.1.iter().copied().skip(1)).map(|(looser, tighter)| (tighter, looser)))
        && pair.0.linear_extension().iter().copied().eq(pair.1.iter().rev().copied())),
)]
fn integer_chain(assocs: &[Assoc]) -> Result<(PrecDag, Vec<Prec>), Box<dyn Error>>
{
    let mut spec = PrecSpec::new();
    let mut nodes = Vec::new();
    for (index, &assoc) in assocs.iter().enumerate() {
        nodes.push(spec.insert(format!("p{index}"), assoc)?);
    }
    for (looser, tighter) in nodes.iter().copied().zip(nodes.iter().copied().skip(1)) {
        spec.add_edge(tighter, looser)?;
    }
    let dag = PrecDag::build(&spec)?;
    Ok((dag, nodes))
}

/// Builds a specification that must be refused as cyclic and returns the
/// cycle.
///
/// # Specification
/// - requires: the specification's relation is cyclic.
/// - ensures: returns the cycle the refusal carries.
/// - panics: when the specification builds or is refused for another reason,
///   which is a fixture defect.
///
/// # Adequacy
/// - hypothesis: For cyclic fixtures, L3 self and longer cycles observe closure
///   and adjacency of the returned refusal evidence. An acyclic fixture is also
///   checked to fail rather than fabricate a witness. This helper does not
///   independently establish cycle absence or distinguish allocator failures.
/// - witness: `tests::prec::prec_cycle_witness_contract`
/// - witness: `tests::prec::cycle_observers_refuse_invalid_evidence`
#[spec(ensures: |ref cycle| cycle.witness.len() >= 2 && cycle.witness.first() == cycle.witness.last()
    && cycle.witness.windows(2).all(|pair| matches!(*pair, [source, target] if spec.edges().any(|edge| edge == (source, target)))))]
fn expect_cycle(spec: &PrecSpec) -> PrecCycle
{
    match PrecDag::build(spec) {
        | Err(PrecDagError::Cycle(cycle)) => cycle,
        | Err(other) => panic!("expected a cycle, got {other}"),
        | Ok(_) => panic!("a cyclic relation must be refused"),
    }
}

/// Asserts that a witness is a closed walk over the given edges.
///
/// # Specification
/// - requires: nothing.
/// - ensures: returns only when the witness has two or more groups, closes, and
///   every consecutive pair is an edge.
/// - panics: when any of those fails.
///
/// # Adequacy
/// - hypothesis: For arbitrary claimed cycles and edge lists, the normal-return
///   observer checks length, closure and every adjacency. L3 valid self and
///   longer cycles plus empty, open and foreign-edge refusals distinguish a
///   no-op checker and partial validation. It does not require a simple cycle
///   or prove that the edge list is the whole graph.
/// - witness: `tests::prec::prec_cycle_witness_contract`
/// - witness: `tests::prec::cycle_observers_refuse_invalid_evidence`
#[spec(ensures: |_| witness.len() >= 2 && witness.first() == witness.last()
    && witness.windows(2).all(|pair| matches!(*pair, [source, target] if edges.contains(&(source, target)))))]
fn assert_closed_adjacent_cycle(
    witness: &[Prec],
    edges: &[(Prec, Prec)],
)
{
    assert!(
        witness.len() >= 2,
        "cycle witness must be closed and non-empty"
    );
    assert_eq!(witness.first(), witness.last(), "cycle witness must close");
    let edge_set = edges.iter().copied().collect::<BTreeSet<_>>();
    for (&from, &to) in witness.iter().zip(witness.iter().skip(1)) {
        assert!(
            edge_set.contains(&(from, to)),
            "each consecutive pair of the witness must be an input edge"
        );
    }
}

#[test]
fn prec_dag_size_and_boundary_contract() -> Result<(), Box<dyn Error>>
{
    let first = Prec::new(PrecIndex::from(0));
    let empty_dag = PrecDag::build(&PrecSpec::new())?;
    assert_eq!(PrecGroupCount::from(0), empty_dag.len());
    assert!(bool::from(empty_dag.is_empty()));
    assert_eq!(None, empty_dag.name(first));
    assert_eq!(None, empty_dag.assoc(first));
    assert!(!bool::from(empty_dag.lt(first, first, Assoc::Non)));
    assert!(!bool::from(empty_dag.gt(first, first, Assoc::Non)));
    assert!(!bool::from(empty_dag.eq(first, first, Assoc::Non)));
    assert!(!bool::from(empty_dag.comparable(first, first)));

    let mut single_spec = PrecSpec::new();
    let only = single_spec.insert("only", Assoc::Non)?;
    let single_dag = PrecDag::build(&single_spec)?;
    assert_eq!(PrecGroupCount::from(1), single_dag.len());
    assert!(!bool::from(single_dag.is_empty()));
    assert_eq!(Some("only"), single_dag.name(only).map(<&str>::from));
    assert_eq!(Some(Assoc::Non), single_dag.assoc(only));
    assert_eq!(None, single_dag.name(Prec::new(PrecIndex::from(1))));
    assert_eq!(None, single_dag.assoc(Prec::new(PrecIndex::from(1))));

    let (dag, [loose, left_mid, right_mid, tight]) = diamond()?;
    assert_eq!(PrecGroupCount::from(4), dag.len());
    assert!(!bool::from(dag.is_empty()));
    assert_eq!(Some("tight"), dag.name(tight).map(<&str>::from));
    assert_eq!(Some(Assoc::Right), dag.assoc(right_mid));
    assert!(bool::from(dag.lt(loose, tight, Assoc::Non)));
    let last_valid = Prec::new(PrecIndex::from(3));
    let one_past = Prec::new(PrecIndex::from(4));
    assert_eq!(Some("tight"), dag.name(last_valid).map(<&str>::from));
    assert_eq!(Some(Assoc::Non), dag.assoc(last_valid));
    assert_eq!(None, dag.name(one_past));
    assert_eq!(None, dag.assoc(one_past));
    assert!(!bool::from(dag.lt(one_past, tight, Assoc::Non)));
    assert!(!bool::from(dag.gt(tight, one_past, Assoc::Non)));
    assert!(!bool::from(dag.eq(one_past, one_past, Assoc::Non)));
    assert!(!bool::from(dag.comparable(one_past, left_mid)));
    assert!(bool::from(dag.bound_lt(
        Bound::Bottom,
        Bound::Value(last_valid),
        Assoc::Non
    )));
    assert!(!bool::from(dag.bound_lt(
        Bound::Bottom,
        Bound::Value(one_past),
        Assoc::Non
    )));
    assert!(bool::from(
        dag.bound_comparable(Bound::Value(last_valid), Bound::Root)
    ));
    assert!(!bool::from(
        dag.bound_comparable(Bound::Value(one_past), Bound::Root)
    ));
    Ok(())
}

#[test]
fn prec_dag_contract() -> Result<(), Box<dyn Error>>
{
    let (dag, [loose, left_mid, right_mid, tight]) = diamond()?;
    let unknown = Prec::new(PrecIndex::from(u16::MAX));

    assert!(bool::from(dag.lt(loose, left_mid, Assoc::Non)));
    assert!(bool::from(dag.lt(loose, right_mid, Assoc::Left)));
    assert!(bool::from(dag.lt(left_mid, tight, Assoc::Right)));
    assert!(bool::from(dag.lt(right_mid, tight, Assoc::Non)));
    assert!(bool::from(dag.lt(loose, tight, Assoc::Non)));
    assert!(bool::from(dag.gt(tight, loose, Assoc::Non)));

    assert!(!bool::from(dag.lt(left_mid, right_mid, Assoc::Non)));
    assert!(!bool::from(dag.gt(left_mid, right_mid, Assoc::Non)));
    assert!(!bool::from(dag.comparable(left_mid, right_mid)));
    assert!(bool::from(dag.comparable(loose, tight)));
    assert!(bool::from(dag.comparable(left_mid, left_mid)));

    assert!(bool::from(dag.gt(left_mid, left_mid, Assoc::Left)));
    assert!(!bool::from(dag.gt(left_mid, left_mid, Assoc::Non)));
    assert!(bool::from(dag.lt(right_mid, right_mid, Assoc::Right)));
    assert!(!bool::from(dag.lt(right_mid, right_mid, Assoc::Left)));
    assert!(bool::from(dag.eq(loose, loose, Assoc::Non)));
    assert!(!bool::from(dag.eq(loose, loose, Assoc::Right)));
    assert!(!bool::from(dag.eq(left_mid, left_mid, Assoc::Non)));

    assert_eq!(Some("left-mid"), dag.name(left_mid).map(<&str>::from));
    assert_eq!(Some(Assoc::Right), dag.assoc(right_mid));
    assert_eq!(None, dag.name(unknown));
    assert_eq!(None, dag.assoc(unknown));
    assert!(!bool::from(dag.lt(unknown, loose, Assoc::Non)));
    assert!(!bool::from(dag.comparable(unknown, loose)));

    let groups = dag
        .groups()
        .map(|(prec, name, assoc)| (prec, <&str>::from(name), assoc))
        .collect::<Vec<_>>();
    assert_eq!(
        &[
            (loose, "loose", Assoc::Non),
            (left_mid, "left-mid", Assoc::Left),
            (right_mid, "right-mid", Assoc::Right),
            (tight, "tight", Assoc::Non),
        ],
        groups.as_slice()
    );
    assert_eq!(
        vec![
            (left_mid, loose),
            (right_mid, loose),
            (tight, left_mid),
            (tight, right_mid),
        ],
        dag.edges().collect::<Vec<_>>()
    );
    Ok(())
}

#[test]
fn prec_cycle_witness_contract() -> Result<(), Box<dyn Error>>
{
    let mut self_spec = PrecSpec::new();
    let node = self_spec.insert("self", Assoc::Non)?;
    self_spec.add_edge(node, node)?;
    let self_cycle = expect_cycle(&self_spec);
    assert_eq!(self_cycle.witness, vec![node, node]);
    assert_closed_adjacent_cycle(&self_cycle.witness, &self_spec.edges().collect::<Vec<_>>());

    let mut spec = PrecSpec::new();
    let a = spec.insert("a", Assoc::Non)?;
    let b = spec.insert("b", Assoc::Non)?;
    let c = spec.insert("c", Assoc::Non)?;
    spec.add_edge(a, b)?;
    spec.add_edge(b, c)?;
    spec.add_edge(c, a)?;
    let cycle = expect_cycle(&spec);
    assert_eq!(cycle.witness, vec![a, b, c, a]);
    assert_closed_adjacent_cycle(&cycle.witness, &spec.edges().collect::<Vec<_>>());
    assert_eq!("precedence cycle 0 1 2 0", format!("{cycle}"));
    Ok(())
}

#[test]
fn virtual_bound_comparisons() -> Result<(), Box<dyn Error>>
{
    let (dag, nodes) = integer_chain(&[Assoc::Non, Assoc::Non, Assoc::Non])?;
    let &[loose, _, tight] = nodes.as_slice()
    else {
        panic!("a three-group chain has three groups");
    };
    let unknown = Prec::new(PrecIndex::from(99));

    assert!(bool::from(dag.bound_lt(
        Bound::Bottom,
        Bound::Value(loose),
        Assoc::Non
    )));
    assert!(bool::from(dag.bound_lt(
        Bound::Value(loose),
        Bound::Value(tight),
        Assoc::Non
    )));
    assert!(bool::from(dag.bound_lt(
        Bound::Value(tight),
        Bound::Root,
        Assoc::Non
    )));
    assert!(bool::from(dag.bound_lt(
        Bound::Bottom,
        Bound::Root,
        Assoc::Non
    )));
    assert!(!bool::from(dag.bound_lt(
        Bound::Root,
        Bound::Value(tight),
        Assoc::Non
    )));
    assert!(bool::from(dag.bound_gt(
        Bound::Root,
        Bound::Value(tight),
        Assoc::Non
    )));
    assert!(bool::from(dag.bound_gt(
        Bound::Root,
        Bound::Bottom,
        Assoc::Non
    )));
    assert!(!bool::from(dag.bound_gt(
        Bound::Bottom,
        Bound::Value(loose),
        Assoc::Non
    )));
    assert!(!bool::from(dag.bound_gt(
        Bound::Root,
        Bound::Value(unknown),
        Assoc::Non
    )));
    assert!(bool::from(dag.bound_eq(
        Bound::Bottom::<Prec>,
        Bound::Bottom,
        Assoc::Non
    )));
    assert!(bool::from(dag.bound_eq(
        Bound::Root::<Prec>,
        Bound::Root,
        Assoc::Left
    )));
    assert!(!bool::from(dag.bound_eq(
        Bound::Bottom::<Prec>,
        Bound::Root,
        Assoc::Non
    )));
    assert!(!bool::from(dag.bound_eq(
        Bound::Root::<Prec>,
        Bound::Bottom,
        Assoc::Non
    )));
    assert!(!bool::from(dag.bound_eq(
        Bound::Bottom,
        Bound::Value(loose),
        Assoc::Non
    )));
    assert!(!bool::from(dag.bound_eq(
        Bound::Value(loose),
        Bound::Bottom,
        Assoc::Non
    )));
    assert!(!bool::from(dag.bound_eq(
        Bound::Root,
        Bound::Value(tight),
        Assoc::Non
    )));
    assert!(!bool::from(dag.bound_eq(
        Bound::Value(tight),
        Bound::Root,
        Assoc::Non
    )));
    assert!(bool::from(
        dag.bound_comparable(Bound::Bottom, Bound::Value(loose))
    ));
    assert!(bool::from(
        dag.bound_comparable(Bound::Value(tight), Bound::Root)
    ));
    assert!(bool::from(
        dag.bound_comparable(Bound::Bottom::<Prec>, Bound::Root)
    ));
    assert!(!bool::from(
        dag.bound_comparable(Bound::Value(unknown), Bound::Root)
    ));
    Ok(())
}

#[test]
fn prec_integer_chain_oracle() -> Result<(), Box<dyn Error>>
{
    let (dag, nodes) = integer_chain(&[Assoc::Non, Assoc::Left, Assoc::Right])?;
    let &[loose, left_assoc, right_assoc] = nodes.as_slice()
    else {
        panic!("a three-group chain has three groups");
    };
    assert!(bool::from(dag.eq(loose, loose, Assoc::Non)));
    assert!(bool::from(dag.gt(left_assoc, left_assoc, Assoc::Left)));
    assert!(bool::from(dag.lt(right_assoc, right_assoc, Assoc::Right)));
    let chain = [loose, left_assoc, right_assoc];
    let expected_lt = [[false, true, true], [false, false, true], [
        false, false, false,
    ]];
    let expected_gt = [[false, false, false], [true, false, false], [
        true, true, false,
    ]];
    for ((left, lt_row), gt_row) in chain.into_iter().zip(expected_lt).zip(expected_gt) {
        for ((right, lt_expected), gt_expected) in chain.into_iter().zip(lt_row).zip(gt_row) {
            assert_eq!(lt_expected, bool::from(dag.lt(left, right, Assoc::Non)));
            assert_eq!(gt_expected, bool::from(dag.gt(left, right, Assoc::Non)));
            assert!(bool::from(dag.comparable(left, right)));
        }
    }
    Ok(())
}

#[test]
fn prec_spec_size_and_boundary_contract() -> Result<(), Box<dyn Error>>
{
    let empty = PrecSpec::new();
    assert_eq!(PrecGroupCount::from(0), empty.len());
    assert!(bool::from(empty.is_empty()));
    assert_eq!(None, empty.name(Prec::new(PrecIndex::from(0))));
    assert_eq!(None, empty.assoc(Prec::new(PrecIndex::from(0))));

    let mut spec = PrecSpec::new();
    let first = spec.insert("first", Assoc::Left)?;
    let second = spec.insert("second", Assoc::Non)?;

    assert_eq!(PrecGroupCount::from(2), spec.len());
    assert!(!bool::from(spec.is_empty()));
    assert_eq!(Some("first"), spec.name(first).map(<&str>::from));
    assert_eq!(Some(Assoc::Left), spec.assoc(first));
    assert_eq!(Some("second"), spec.name(second).map(<&str>::from));
    assert_eq!(Some(Assoc::Non), spec.assoc(second));

    let last_valid = Prec::new(PrecIndex::from(1));
    let one_past = Prec::new(PrecIndex::from(2));
    assert_eq!(Some("second"), spec.name(last_valid).map(<&str>::from));
    assert_eq!(None, spec.name(one_past));
    assert_eq!(None, spec.assoc(one_past));
    assert_eq!(
        Err(PrecSpecError::InvalidEdge {
            tighter: one_past,
            looser: first,
            node_count: NodeCount::from(2),
        }),
        spec.add_edge(one_past, first)
    );
    assert_eq!(
        Err(PrecSpecError::InvalidEdge {
            tighter: first,
            looser: one_past,
            node_count: NodeCount::from(2),
        }),
        spec.add_edge(first, one_past)
    );
    spec.add_edge(last_valid, first)?;
    Ok(())
}

#[test]
fn duplicate_edge_canonicalization_and_invalid_edges() -> Result<(), Box<dyn Error>>
{
    let mut spec = PrecSpec::new();
    let loose = spec.insert("loose", Assoc::Non)?;
    let tight = spec.insert("tight", Assoc::Non)?;
    spec.add_edge(tight, loose)?;
    spec.add_edge(tight, loose)?;
    assert_eq!(vec![(tight, loose)], spec.edges().collect::<Vec<_>>());
    let before_refusal = spec.clone();
    assert_eq!(
        Err(PrecSpecError::InvalidEdge {
            tighter: Prec::new(PrecIndex::from(99)),
            looser: loose,
            node_count: NodeCount::from(2),
        }),
        spec.add_edge(Prec::new(PrecIndex::from(99)), loose)
    );
    assert_eq!(spec, before_refusal);
    assert_eq!(
        Err(PrecSpecError::DuplicateName {
            name: "tight".to_owned(),
        }),
        spec.insert("tight", Assoc::Left)
    );
    assert_eq!(spec, before_refusal);
    assert_eq!(PrecGroupCount::from(2), spec.len());
    let dag = PrecDag::build(&spec)?;
    assert_eq!(vec![(tight, loose)], dag.edges().collect::<Vec<_>>());
    Ok(())
}

#[test]
fn capacity_beyond_u16_is_typed() -> Result<(), Box<dyn Error>>
{
    let mut spec = PrecSpec::new();
    for index in 0_u32 ..= u32::from(u16::MAX) {
        let id = spec.insert(format!("p{index}"), Assoc::Non)?;
        assert_eq!(index, u32::from(id.index()));
    }
    assert_eq!(
        Err(PrecSpecError::CapacityExceeded),
        spec.insert("overflow", Assoc::Non)
    );
    assert_eq!(
        Err(PrecSpecError::DuplicateName {
            name: "p0".to_owned()
        }),
        spec.insert("p0", Assoc::Right)
    );
    assert_eq!(spec.assoc(Prec::new(PrecIndex::from(0))), Some(Assoc::Non));
    assert_eq!(PrecGroupCount::from(0x1_0000_usize), spec.len());
    Ok(())
}

#[test]
fn bound_value_reflexive_association_tracks_direction() -> Result<(), Box<dyn Error>>
{
    let mut left_spec = PrecSpec::new();
    let left_p = left_spec.insert("p", Assoc::Left)?;
    let neutral = left_spec.insert("neutral", Assoc::Non)?;
    let left_dag = PrecDag::build(&left_spec)?;

    assert!(bool::from(left_dag.gt(left_p, left_p, Assoc::Left)));
    assert!(bool::from(left_dag.bound_gt(
        Bound::Value(left_p),
        Bound::Value(left_p),
        Assoc::Left
    )));
    assert!(!bool::from(left_dag.lt(left_p, left_p, Assoc::Left)));
    assert!(!bool::from(left_dag.bound_lt(
        Bound::Value(left_p),
        Bound::Value(left_p),
        Assoc::Left
    )));
    assert!(bool::from(left_dag.bound_eq(
        Bound::Value(neutral),
        Bound::Value(neutral),
        Assoc::Non
    )));
    assert!(!bool::from(left_dag.bound_eq(
        Bound::Value(left_p),
        Bound::Value(left_p),
        Assoc::Left
    )));

    let mut right_spec = PrecSpec::new();
    let right_p = right_spec.insert("p", Assoc::Right)?;
    let right_dag = PrecDag::build(&right_spec)?;

    assert!(bool::from(right_dag.lt(right_p, right_p, Assoc::Right)));
    assert!(bool::from(right_dag.bound_lt(
        Bound::Value(right_p),
        Bound::Value(right_p),
        Assoc::Right
    )));
    assert!(!bool::from(right_dag.gt(right_p, right_p, Assoc::Right)));
    assert!(!bool::from(right_dag.bound_gt(
        Bound::Value(right_p),
        Bound::Value(right_p),
        Assoc::Right
    )));
    assert!(!bool::from(right_dag.bound_eq(
        Bound::Value(right_p),
        Bound::Value(right_p),
        Assoc::Right
    )));
    Ok(())
}

#[test]
fn stable_fingerprint_sensitivity() -> Result<(), Box<dyn Error>>
{
    let mut left = PrecSpec::new();
    let a = left.insert("a", Assoc::Non)?;
    let b = left.insert("b", Assoc::Left)?;
    let c = left.insert("c", Assoc::Right)?;
    left.add_edge(c, b)?;
    left.add_edge(b, a)?;
    left.add_edge(c, b)?;

    let mut reordered = PrecSpec::new();
    let ar = reordered.insert("a", Assoc::Non)?;
    let br = reordered.insert("b", Assoc::Left)?;
    let cr = reordered.insert("c", Assoc::Right)?;
    reordered.add_edge(br, ar)?;
    reordered.add_edge(cr, br)?;

    let mut renamed = PrecSpec::new();
    let an = renamed.insert("a-renamed", Assoc::Non)?;
    let bn = renamed.insert("b", Assoc::Left)?;
    let cn = renamed.insert("c", Assoc::Right)?;
    renamed.add_edge(cn, bn)?;
    renamed.add_edge(bn, an)?;

    let mut assoc_changed = PrecSpec::new();
    let assoc_loose = assoc_changed.insert("a", Assoc::Non)?;
    let assoc_middle = assoc_changed.insert("b", Assoc::Non)?;
    let assoc_tight = assoc_changed.insert("c", Assoc::Right)?;
    assoc_changed.add_edge(assoc_tight, assoc_middle)?;
    assoc_changed.add_edge(assoc_middle, assoc_loose)?;

    let mut relation_changed = PrecSpec::new();
    let arel = relation_changed.insert("a", Assoc::Non)?;
    let brel = relation_changed.insert("b", Assoc::Left)?;
    let crel = relation_changed.insert("c", Assoc::Right)?;
    relation_changed.add_edge(crel, arel)?;
    relation_changed.add_edge(brel, arel)?;

    let left_hash = PrecDag::build(&left)?.fingerprint();
    assert_eq!(left_hash, PrecDag::build(&reordered)?.fingerprint());
    assert_ne!(left_hash, PrecDag::build(&renamed)?.fingerprint());
    assert_ne!(left_hash, PrecDag::build(&assoc_changed)?.fingerprint());
    assert_ne!(left_hash, PrecDag::build(&relation_changed)?.fingerprint());
    Ok(())
}

#[test]
fn fingerprint_stream_is_pinned() -> Result<(), Box<dyn Error>>
{
    let mut spec = PrecSpec::new();
    let a = spec.insert("a", Assoc::Non)?;
    let b = spec.insert("b", Assoc::Left)?;
    let c = spec.insert("c", Assoc::Right)?;
    spec.add_edge(c, b)?;
    spec.add_edge(b, a)?;
    assert_eq!(
        0xae2e_d8a4_6f3a_5e26_u64,
        u64::from(PrecDag::build(&spec)?.fingerprint())
    );
    Ok(())
}

#[test]
fn deterministic_linear_extension_uses_smallest_ready_id() -> Result<(), Box<dyn Error>>
{
    let mut spec = PrecSpec::new();
    let a = spec.insert("a", Assoc::Non)?;
    let b = spec.insert("b", Assoc::Non)?;
    let c = spec.insert("c", Assoc::Non)?;
    let d = spec.insert("d", Assoc::Non)?;
    spec.add_edge(d, a)?;
    spec.add_edge(c, d)?;
    let dag = PrecDag::build(&spec)?;
    assert_eq!(&[b, c, d, a], dag.linear_extension());
    Ok(())
}

proptest! {
    #[test]
    fn lt_gt_duality_for_distinct_chain_nodes(
        chain_size in 2_usize..8,
        alpha_draw in 0_usize..8,
        omega_draw in 0_usize..8,
    ) {
        let (dag, nodes) = integer_chain(&vec![Assoc::Non; chain_size]).expect("a chain builds");
        let alpha = alpha_draw.checked_rem(chain_size).expect("the chain is non-empty");
        let omega = omega_draw.checked_rem(chain_size).expect("the chain is non-empty");
        prop_assume!(alpha != omega);
        prop_assert_eq!(
            dag.lt(nodes[alpha], nodes[omega], Assoc::Non),
            dag.gt(nodes[omega], nodes[alpha], Assoc::Left)
        );
    }

    #[test]
    fn comparable_is_symmetric_and_rejects_invalid_boundaries(
        chain_size in 1_usize..8,
        alpha_draw in 0_usize..8,
        omega_draw in 0_usize..8,
    ) {
        let (dag, nodes) = integer_chain(&vec![Assoc::Non; chain_size]).expect("a chain builds");
        let alpha = nodes[alpha_draw.checked_rem(chain_size).expect("the chain is non-empty")];
        let omega = nodes[omega_draw.checked_rem(chain_size).expect("the chain is non-empty")];
        let unknown = Prec::new(PrecIndex::from(u16::MAX));
        prop_assert_eq!(dag.comparable(alpha, omega), dag.comparable(omega, alpha));
        prop_assert!(bool::from(dag.bound_comparable(Bound::Bottom, Bound::Value(alpha))));
        prop_assert!(bool::from(dag.bound_comparable(Bound::Value(omega), Bound::Root)));
        prop_assert!(!bool::from(dag.comparable(unknown, alpha)));
        prop_assert!(!bool::from(dag.bound_comparable(Bound::Value(unknown), Bound::Bottom)));
    }

    #[test]
    fn associativity_affects_reflexive_pairs_only(
        chain_size in 2_usize..8,
        alpha_draw in 0_usize..8,
        omega_draw in 0_usize..8,
    ) {
        let assocs = [Assoc::Non, Assoc::Left, Assoc::Right]
            .into_iter()
            .cycle()
            .take(chain_size)
            .collect::<Vec<_>>();
        let (dag, nodes) = integer_chain(&assocs).expect("a chain builds");
        let alpha = alpha_draw.checked_rem(chain_size).expect("the chain is non-empty");
        let omega = omega_draw.checked_rem(chain_size).expect("the chain is non-empty");
        let (alpha_node, omega_node) = (nodes[alpha], nodes[omega]);
        if alpha == omega {
            let declared = assocs[alpha];
            prop_assert_eq!(declared == Assoc::Non, bool::from(dag.eq(alpha_node, alpha_node, declared)));
            prop_assert_eq!(declared == Assoc::Left, bool::from(dag.gt(alpha_node, alpha_node, declared)));
            prop_assert_eq!(declared == Assoc::Right, bool::from(dag.lt(alpha_node, alpha_node, declared)));
        }
        else {
            let lt = dag.lt(alpha_node, omega_node, Assoc::Non);
            prop_assert_eq!(lt, dag.lt(alpha_node, omega_node, Assoc::Left));
            prop_assert_eq!(lt, dag.lt(alpha_node, omega_node, Assoc::Right));
            let gt = dag.gt(alpha_node, omega_node, Assoc::Non);
            prop_assert_eq!(gt, dag.gt(alpha_node, omega_node, Assoc::Left));
            prop_assert_eq!(gt, dag.gt(alpha_node, omega_node, Assoc::Right));
        }
    }
}

#[test]
fn cycle_observers_refuse_invalid_evidence()
{
    let a = Prec::new(PrecIndex::from(0));
    let b = Prec::new(PrecIndex::from(1));
    let c = Prec::new(PrecIndex::from(2));
    let edges = [(a, b), (b, a)];
    for witness in [vec![], vec![a, b], vec![a, c, a]] {
        assert!(
            std::panic::catch_unwind(|| assert_closed_adjacent_cycle(&witness, &edges)).is_err()
        );
    }
    assert!(std::panic::catch_unwind(|| expect_cycle(&PrecSpec::new())).is_err());
}
