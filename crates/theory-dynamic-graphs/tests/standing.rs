//! Public standing-state witnesses across independent insertion calls.

#[cfg(test)]
mod tests
{
    use anodized::spec;
    use gandr_theory_dynamic_graphs::AcyclicityMaintenance;
    use gandr_theory_dynamic_graphs::ConstraintVerdict;
    use gandr_theory_dynamic_graphs::EdgeVerdict;
    use gandr_theory_dynamic_graphs::MaintenanceError;
    use gandr_theory_dynamic_graphs::Offset;
    use gandr_theory_dynamic_graphs::Potential;
    use gandr_theory_dynamic_graphs::PotentialAbsence;
    use gandr_theory_dynamic_graphs::PotentialError;
    use gandr_theory_dynamic_graphs::PotentialMaintenance;
    use gandr_theory_graphs::EdgeId;
    use gandr_theory_graphs::EdgeSource as _;
    use gandr_theory_graphs::NodeCount;
    use gandr_theory_graphs::NodeId;
    use quenchant_shape::shape::Maybe;

    /// Construct a fixture edge.
    ///
    /// # Specification
    /// trivial.
    fn edge(
        source: NodeId,
        target: NodeId,
    ) -> EdgeId
    {
        EdgeId::new(source, target)
    }

    #[test]
    fn a_standing_graph_preserves_prefixes_across_calls()
    {
        let [a, b, c, d] = [0_u32, 1, 2, 3].map(NodeId::from);
        let mut graph =
            AcyclicityMaintenance::with_nodes(NodeCount::from(4_u32)).expect("finite node domain");
        assert_eq!(
            graph.insert_edge(edge(c, b)),
            Ok(EdgeVerdict::AdmittedAfterRepair)
        );
        assert_eq!(graph.insert_edge(edge(b, d)), Ok(EdgeVerdict::Admitted));
        assert_eq!(
            graph.insert_edge(edge(d, a)),
            Ok(EdgeVerdict::AdmittedAfterRepair)
        );
        let verdict = graph.insert_edge(edge(a, c)).expect("finite insertion");
        let EdgeVerdict::Refused(cycle) = verdict
        else {
            panic!("prefix closes this cycle")
        };
        assert_eq!(cycle.nodes, [c, b, d, a, c]);
        assert_eq!(cycle.edges, [
            edge(c, b),
            edge(b, d),
            edge(d, a),
            edge(a, c)
        ]);
        assert_eq!(graph.nodes_in_order().collect::<Vec<_>>(), [c, b, d, a]);
        assert_eq!(graph.successors(c).collect::<Vec<_>>(), [b]);
        assert_eq!(graph.successors(a).collect::<Vec<_>>(), []);
        assert_eq!(graph.insert_edge(edge(c, a)), Ok(EdgeVerdict::Admitted));
        assert_eq!(u64::from(graph.admitted_edges()), 4);
        assert_eq!(graph.compare(c, a), Ok(core::cmp::Ordering::Less));
        assert_eq!(graph.compare(a, a), Ok(core::cmp::Ordering::Equal));
        assert_eq!(
            graph.compare(a, NodeId::from(9_u32)),
            Err(MaintenanceError::NodeCapacity)
        );
        assert!(bool::from(graph.order_is_topological()));
    }

    #[test]
    fn an_overflowing_propagation_restores_values_and_admitted_constraints()
    {
        let [a, b, c] = [0_u32, 1, 2].map(NodeId::from);
        let mut system = PotentialMaintenance::new();
        assert_eq!(
            system.value(c),
            Maybe::Absent(PotentialAbsence::UnknownNode(c))
        );
        assert_eq!(
            system.insert_constraint(edge(b, c), Offset::from(i64::MAX)),
            Ok(ConstraintVerdict::SatisfiedAfterRaise)
        );
        assert_eq!(
            system.insert_constraint(edge(a, b), Offset::from(1_i64)),
            Err(PotentialError::ValueOverflow)
        );
        assert_eq!(system.value(a), Maybe::Present(Potential::from(0_i64)));
        assert_eq!(system.value(b), Maybe::Present(Potential::from(0_i64)));
        assert_eq!(system.value(c), Maybe::Present(Potential::from(i64::MAX)));
        assert_eq!(u64::from(system.admitted_constraints()), 1);
        assert!(bool::from(system.valuation_is_feasible()));
        assert_eq!(
            system.insert_constraint(edge(a, b), Offset::from(0_i64)),
            Ok(ConstraintVerdict::Satisfied)
        );
        assert_eq!(u64::from(system.admitted_constraints()), 2);
    }

    #[test]
    fn parallel_offsets_do_not_exhaust_a_node_only_propagation_budget()
    {
        let [a, b, c] = [0_u32, 1, 2].map(NodeId::from);
        let mut system = PotentialMaintenance::new();
        for offset in 0_i64 .. 20 {
            system
                .insert_constraint(edge(b, c), Offset::from(offset))
                .expect("acyclic constraints");
        }
        assert_eq!(
            system.insert_constraint(edge(a, b), Offset::from(100_i64)),
            Ok(ConstraintVerdict::SatisfiedAfterRaise)
        );
        assert_eq!(system.value(b), Maybe::Present(Potential::from(100_i64)));
        assert_eq!(system.value(c), Maybe::Present(Potential::from(119_i64)));
        assert_eq!(u64::from(system.admitted_constraints()), 21);
        assert!(bool::from(system.valuation_is_feasible()));
    }

    /// The independent finite relaxation oracle's two semantic outcomes.
    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum BatchVerdict
    {
        Feasible,
        PositiveCycle,
    }

    /// Decide three-node constraints by full Bellman–Ford sweeps from zero.
    ///
    /// # Specification
    /// - requires: three-node endpoints and unit-magnitude offsets.
    /// - ensures: detects a positive cycle exactly when a third full sweep
    ///   still raises a value; otherwise the finite system is feasible.
    /// - panics: none within the stated fixture domain.
    ///
    /// # Adequacy
    /// - hypothesis: L2 exhaustive three-offer streams distinguish wrong signs,
    ///   lost admitted constraints, false cycle refusals, and incomplete
    ///   rollback.
    /// - witness: `standing::tests::three_offer_systems_agree_with_independent_relaxation`
    #[spec(requires: constraints.iter().all(|&(edge, offset)| u32::from(edge.source) < 3 && u32::from(edge.target) < 3 && (-1..=1).contains(&i64::from(offset))))]
    fn batch_verdict(constraints: &[(EdgeId, Offset)]) -> BatchVerdict
    {
        let mut values = [0_i64; 3];
        for _ in 0_u32 .. 3 {
            let mut changed = false;
            for &(edge, offset) in constraints {
                let source = usize::try_from(u32::from(edge.source)).expect("bounded source");
                let target = usize::try_from(u32::from(edge.target)).expect("bounded target");
                let demand = values[source]
                    .checked_add(i64::from(offset))
                    .expect("bounded fixture sum");
                if values[target] < demand {
                    values[target] = demand;
                    changed = true;
                }
            }
            if !changed {
                return BatchVerdict::Feasible;
            }
        }
        BatchVerdict::PositiveCycle
    }

    #[test]
    fn three_offer_systems_agree_with_independent_relaxation()
    {
        let nodes = [0_u32, 1, 2].map(NodeId::from);
        let mut catalog = Vec::new();
        for source in nodes {
            for target in nodes {
                for offset in [-1_i64, 0, 1] {
                    catalog.push((edge(source, target), Offset::from(offset)));
                }
            }
        }
        for &first in &catalog {
            for &second in &catalog {
                for &third in &catalog {
                    let mut system = PotentialMaintenance::new();
                    system
                        .insert_constraint(edge(nodes[2], nodes[2]), Offset::from(0_i64))
                        .expect("create the complete fixture domain");
                    let mut admitted = Vec::with_capacity(3);
                    for offer in [first, second, third] {
                        let before = nodes.map(|node| system.value(node));
                        admitted.push(offer);
                        let expected = batch_verdict(&admitted);
                        let actual = system
                            .insert_constraint(offer.0, offer.1)
                            .expect("bounded fixture values fit");
                        assert_eq!(
                            matches!(actual, ConstraintVerdict::Refuted(_)),
                            expected == BatchVerdict::PositiveCycle,
                            "{admitted:?}"
                        );
                        if let ConstraintVerdict::Refuted(cycle) = actual {
                            assert_eq!(cycle.nodes.first(), cycle.nodes.last());
                            assert!(cycle.edges.contains(&offer.0));
                            let walked: Vec<_> = cycle
                                .nodes
                                .array_windows::<2>()
                                .map(|&[source, target]| edge(source, target))
                                .collect();
                            assert_eq!(walked, cycle.edges);
                            let weight: i64 = cycle
                                .edges
                                .iter()
                                .map(|step| {
                                    admitted
                                        .iter()
                                        .filter_map(|&(candidate, offset)| {
                                            (candidate == *step).then_some(i64::from(offset))
                                        })
                                        .max()
                                        .expect("witness edge belongs to the candidate")
                                })
                                .sum();
                            assert!(weight > 0, "{admitted:?}: {cycle:?}");
                            assert_eq!(nodes.map(|node| system.value(node)), before);
                            admitted.pop();
                        }
                        for &(constraint, offset) in &admitted {
                            let Maybe::Present(source) = system.value(constraint.source)
                            else {
                                panic!("admitted source exists")
                            };
                            let Maybe::Present(target) = system.value(constraint.target)
                            else {
                                panic!("admitted target exists")
                            };
                            assert!(i64::from(target) >= i64::from(source) + i64::from(offset));
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn an_unrepresentable_node_count_is_refused_before_growth()
    {
        let invalid = edge(NodeId::from(u32::MAX), NodeId::from(0_u32));
        let mut graph = AcyclicityMaintenance::new().expect("order identity");
        assert_eq!(
            graph.insert_edge(invalid),
            Err(MaintenanceError::NodeCapacity)
        );
        assert_eq!(graph.nodes(), NodeCount::from(0_u32));
        let mut valuation = PotentialMaintenance::new();
        assert_eq!(
            valuation.insert_constraint(invalid, Offset::from(1_i64)),
            Err(PotentialError::NodeCapacity)
        );
        assert_eq!(valuation.nodes(), NodeCount::from(0_u32));
    }
}
