use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use gandr_core_term::CoreArena;
use gandr_core_term::Zone;
use gandr_kernel_strata::Level;
use gandr_kernel_term::DeBruijnIndex;

use super::CoreTerm;
use super::FreeFault;
use super::FreeIndices;
use super::Lowering;
use super::Membership;
use super::Outward;
use super::Reached;

#[test]
fn lowered_union_agrees_with_a_set_model()
{
    let universe = [0_u32, 1, 3, u32::MAX];
    for held_mask in 0_u8 .. 16 {
        for other_mask in 0_u8 .. 16 {
            for lowering in [0_u32, 1, 2, u32::MAX] {
                let held: Vec<_> = universe
                    .iter()
                    .copied()
                    .enumerate()
                    .filter_map(|(bit, count)| (held_mask & (1 << bit) != 0).then_some(count))
                    .collect();
                let other: Vec<_> = universe
                    .iter()
                    .copied()
                    .enumerate()
                    .filter_map(|(bit, count)| (other_mask & (1 << bit) != 0).then_some(count))
                    .collect();
                let expected: BTreeSet<_> = held
                    .iter()
                    .copied()
                    .chain(other.iter().filter_map(|count| count.checked_sub(lowering)))
                    .collect();
                let mut actual = Outward { counts: held };
                actual.join_lowered(&Outward { counts: other }, Lowering(lowering));
                assert_eq!(expected.iter().copied().collect::<Vec<_>>(), actual.counts);
                for count in [0_u32, 1, 2, 3, u32::MAX - 1, u32::MAX] {
                    let membership = if expected.contains(&count) {
                        Membership::Held
                    }
                    else {
                        Membership::Absent
                    };
                    assert_eq!(membership, actual.holds(count));
                }
            }
        }
    }
}

#[test]
fn a_fork_binds_one_endpoint_in_each_half()
{
    use gandr_core_term::session::SessionAction;
    let mut core = CoreArena::new();
    let unit = core.value_unit();
    let protocol = core.value_type_unit();
    // Inside the child its own end is 0 and the outer endpoint 1.
    let to_outer = core.computation_session(SessionAction::Send {
        endpoint: DeBruijnIndex::from(1_u32),
        payload: unit,
    });
    let own_close = core.computation_session(SessionAction::Close {
        endpoint: DeBruijnIndex::from(0_u32),
    });
    let child = core.computation_bind(to_outer, own_close);
    let parent = core.computation_session(SessionAction::Close {
        endpoint: DeBruijnIndex::from(0_u32),
    });
    let fork = core.computation_session(SessionAction::Fork {
        protocol,
        child,
        parent,
    });
    let mut analysis = FreeIndices::default();
    assert_eq!(
        Ok([DeBruijnIndex::from(0_u32), DeBruijnIndex::from(1_u32)].as_slice()),
        analysis.linear(&core, CoreTerm::Computation(child)),
        "the child reads its own end and the outer endpoint"
    );
    assert_eq!(
        Ok([DeBruijnIndex::from(0_u32)].as_slice()),
        analysis.linear(&core, CoreTerm::Computation(fork)),
        "the fork binds both ends and reads the outer endpoint one lower"
    );
    let carried = core.value_variable(Zone::Linear, DeBruijnIndex::from(3_u32));
    let delegate = core.computation_session(SessionAction::Send {
        endpoint: DeBruijnIndex::from(2_u32),
        payload: carried,
    });
    assert_eq!(
        Ok([DeBruijnIndex::from(2_u32), DeBruijnIndex::from(3_u32)].as_slice()),
        analysis.linear(&core, CoreTerm::Computation(delegate)),
        "a send reads its endpoint and its payload's"
    );
}

#[test]
fn binders_lower_only_their_own_intuitionistic_occurrences()
{
    let mut core = CoreArena::new();
    let near = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let far = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(2_u32));
    let linear = core.value_variable(Zone::Linear, DeBruijnIndex::from(2_u32));
    let decoded = core.value_type_element(far, Level::zero());
    let quote = core.value_quote(decoded);
    let shared = core.value_tuple(&[quote, linear]);
    let body = core.value_tuple(&[near, shared]);
    let returned = core.computation_return(body);
    let lambda = core.computation_lambda(returned);
    let static_lambda = core.value_static_lambda(body);
    let mut analysis = FreeIndices::default();
    for term in [
        CoreTerm::Computation(lambda),
        CoreTerm::Value(static_lambda),
    ] {
        let free = analysis
            .of(&core, term)
            .expect("a live open term has free indices");
        assert_eq!([DeBruijnIndex::from(1_u32)], free.intuitionistic.counts());
        assert_eq!([DeBruijnIndex::from(2_u32)], free.linear.counts());
    }
    let free = analysis
        .of(&core, CoreTerm::Value(far))
        .expect("the shared answer remains");
    assert_eq!([DeBruijnIndex::from(2_u32)], free.intuitionistic.counts());
    assert!(free.linear.counts().is_empty());
    let free = analysis
        .of(&core, CoreTerm::Value(linear))
        .expect("the linear leaf remains");
    assert_eq!([DeBruijnIndex::from(2_u32)], free.linear.counts());
    assert!(free.intuitionistic.counts().is_empty());
    let unit = core.value_unit();
    let free = analysis
        .of(&core, CoreTerm::Value(unit))
        .expect("unit is closed");
    assert!(free.intuitionistic.counts().is_empty());
    assert!(free.linear.counts().is_empty());
}

#[test]
fn a_quoted_dependent_arrow_binds_only_its_codomain()
{
    let mut core = CoreArena::new();
    let near = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let far = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(2_u32));
    let domain = core.value_type_element(far, Level::zero());
    let bound = core.value_type_element(near, Level::zero());
    let product = core.value_type_product(&[bound, domain]);
    let result = core.comp_type_returner(product);
    let arrow = core.comp_type_pi(domain, result);
    let quote = core.value_quote_computation(arrow);
    let mut analysis = FreeIndices::default();
    let free = analysis
        .of(&core, CoreTerm::Value(quote))
        .expect("quoted types are traversed");
    assert_eq!(
        [DeBruijnIndex::from(1_u32), DeBruijnIndex::from(2_u32)],
        free.intuitionistic.counts()
    );
    assert!(free.linear.counts().is_empty());
}

#[test]
fn missing_nodes_and_unanswered_children_have_distinct_refusals()
{
    let mut core = CoreArena::new();
    let child = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(3_u32));
    let parent = core.computation_return(child);
    let reached = Reached::Term(CoreTerm::Value(child));
    let mut analysis = FreeIndices::default();
    assert_eq!(Err(FreeFault::MachineInvariant), analysis.read(reached));
    assert_eq!(
        Err(FreeFault::MachineInvariant),
        analysis.assemble(&core, Reached::Term(CoreTerm::Computation(parent)))
    );
    let free = analysis
        .of(&core, CoreTerm::Computation(parent))
        .expect("postorder answers children");
    assert_eq!([DeBruijnIndex::from(3_u32)], free.intuitionistic.counts());
    assert_eq!(
        [DeBruijnIndex::from(3_u32)],
        analysis
            .read(reached)
            .expect("the child was answered")
            .intuitionistic
            .counts()
    );
    let empty = CoreArena::new();
    let mut missing = FreeIndices::default();
    assert_eq!(
        Err(FreeFault::Dangling),
        missing.of(&empty, CoreTerm::Value(child))
    );
    assert_eq!(Err(FreeFault::Dangling), missing.assemble(&empty, reached));
}

#[test]
fn control_scopes_keep_only_ambient_indices()
{
    use gandr_core_term::control::EffectClause;
    use gandr_core_term::control::StackFrame;
    use gandr_core_term::effect::EffectName;
    use gandr_core_term::effect::EffectOp;
    use gandr_core_term::effect::EffectSig;
    use gandr_core_term::effect::OperationName;
    let mut core = CoreArena::new();
    let zero = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(0_u32));
    let one = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(1_u32));
    let two = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(2_u32));
    let three = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(3_u32));
    let four = core.value_variable(Zone::Intuitionistic, DeBruijnIndex::from(4_u32));
    let unit = core.value_type_unit();
    let decoded = core.value_type_element(four, Level::zero());
    let operation = OperationName::from("get");
    let signature = EffectSig::new(EffectName::from("State"), [EffectOp {
        name: operation.clone(),
        payload: unit,
        reply: decoded,
    }])
    .unwrap();
    let performed = core.computation_perform(signature.clone(), operation.clone(), two);
    let on_return = core.computation_return(one);
    let pair = core.value_tuple(&[one, three]);
    let clause = core.computation_return(pair);
    let handled = core.computation_handle(
        signature,
        performed,
        on_return,
        alloc::sync::Arc::from([EffectClause {
            operation,
            body: clause,
        }]),
    );
    let pair = core.value_tuple(&[zero, four]);
    let body = core.computation_return(pair);
    let stack = core.value_reify(alloc::sync::Arc::from([
        StackFrame::Apply(two),
        StackFrame::Bind(body),
        StackFrame::Project(gandr_kernel_term::Side::Left),
    ]));
    let body = core.computation_return(four);
    let resumed = core.computation_resume(zero, body);
    let shifted = core.computation_shift(resumed);
    let reset = core.computation_reset(shifted);
    let mut analysis = FreeIndices::default();
    for (term, expected) in [
        (CoreTerm::Computation(handled), &[0_u32, 1, 2, 4][..]),
        (CoreTerm::Value(stack), &[2_u32, 3][..]),
        (CoreTerm::Computation(reset), &[3_u32][..]),
    ] {
        let free = analysis.of(&core, term).unwrap();
        assert_eq!(
            free.intuitionistic
                .counts()
                .iter()
                .copied()
                .map(u32::from)
                .collect::<alloc::vec::Vec<_>>(),
            expected
        );
        assert!(free.linear.counts().is_empty());
    }
}
