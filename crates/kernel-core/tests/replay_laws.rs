//! Unit-law goldens, composition, replay purity and the refusal vocabulary.
//!
//! Replay laws exercised through the public kernel API.

use anodized::spec;
use gandr_kernel_conversion_trace::ConversionDecision;
use gandr_kernel_core::EngineClaim;
use gandr_kernel_core::KernelVerdict;
use gandr_kernel_core::ParameterCount;
use gandr_kernel_core::RefusalClass;
use gandr_kernel_core::ReplayBudget;
use gandr_kernel_core::ReplayDecline;
use gandr_kernel_core::ReplayNode;
use gandr_kernel_core::ReplayRefusal;
use gandr_kernel_core::ReplaySides;
use gandr_kernel_core::TracePosition;
use gandr_kernel_core::Unfoldable;
use gandr_kernel_core::Unfoldings;
use gandr_kernel_core::replay;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::TermArena;
use proptest::prelude::ProptestConfig;
use proptest::prelude::prop_assert_eq;
use proptest::prelude::proptest;
use proptest::test_runner::TestCaseError;

/// The unit dialogue, independent of arena identifiers.
const SHARED: ConversionDecision<ReplayNode> = ConversionDecision::ComparedShared {
    left: ReplayNode::Other,
    right: ReplayNode::Other,
};

/// Replay twice in place and once in an independent clone.
///
/// # Specification
/// - requires: the sides and unfolding bodies belong to `arena`.
/// - ensures: returns their common verdict only if all three runs agree and
///   each restores its entry watermark.
/// - fails: `TestCaseError` on disagreement or a changed watermark.
/// - panics: none.
///
/// # Errors
/// Returns the property assertion that failed.
///
/// # Adequacy
/// - hypothesis: L3 — repeated and cloned executions distinguish retained
///   allocation or call-local state; unit-law goldens distinguish a common
///   wrong verdict that self-agreement alone would miss.
/// - witness: `tests::replay_laws::replay_is_pure_across_repeated_and_cloned_arenas`
#[spec(captures: before = arena.watermark(), ensures: |ret| ret.is_err() || arena.watermark() == before)]
fn repeat_and_clone(
    arena: &mut TermArena,
    unfoldings: &Unfoldings,
    sides: ReplaySides,
    claim: EngineClaim,
    trace: &[ConversionDecision<ReplayNode>],
    budget: ReplayBudget,
) -> Result<KernelVerdict, TestCaseError>
{
    let mark = arena.watermark();
    let mut cloned = arena.clone();
    let first = replay(
        arena,
        unfoldings,
        sides,
        claim,
        trace.iter().copied(),
        budget,
    );
    prop_assert_eq!(arena.watermark(), mark);
    let second = replay(
        arena,
        unfoldings,
        sides,
        claim,
        trace.iter().copied(),
        budget,
    );
    prop_assert_eq!(arena.watermark(), mark);
    let independent = replay(
        &mut cloned,
        unfoldings,
        sides,
        claim,
        trace.iter().copied(),
        budget,
    );
    prop_assert_eq!(cloned.watermark(), mark);
    prop_assert_eq!(first, second);
    prop_assert_eq!(first, independent);
    Ok(first)
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    #[test]
    fn replay_is_pure_across_repeated_and_cloned_arenas(
        index in 0_u32 .. 4,
        branches in proptest::collection::vec(proptest::bool::ANY, 0 .. 8),
        apart in proptest::bool::ANY,
        mutation in 0_u8 .. 4,
        budget in 0_u64 .. 96,
    ) {
        let mut arena = TermArena::new();
        let unit = arena.value_unit();
        let mut left = arena.value_variable(DeBruijnIndex::from(index));
        let mut right = arena.value_variable(DeBruijnIndex::from(if apart { 4 } else { index }));
        for branch in branches {
            if branch {
                left = arena.value_tuple(&[left, unit]);
                right = arena.value_tuple(&[right, unit]);
            } else {
                left = arena.value_tuple(&[unit, left]);
                right = arena.value_tuple(&[unit, right]);
            }
        }
        let bound = arena.value_variable(DeBruijnIndex::from(0));
        let returned = arena.computation_return(bound);
        let identity = arena.computation_lambda(returned);
        let applied = arena.computation_application(identity, left);
        let target = arena.computation_return(right);
        let forced = arena.computation_force(bound);
        let self_applied = arena.computation_application(forced, bound);
        let lambda = arena.computation_lambda(self_applied);
        let suspended = arena.value_thunk(lambda);
        let omega = arena.computation_application(lambda, suspended);
        let constant = ConstantIndex::from(0_usize);
        let head = arena.value_constant(constant);
        let instance = arena.value_static_application(head, left);
        let unfoldings = Unfoldings::new(vec![Unfoldable::Operator {
            parameters: ParameterCount::from(1),
            body: bound,
        }]);
        let unfolding = [
            ConversionDecision::Unfold { constant: ReplayNode::Constant(constant) },
            ConversionDecision::ReduceLeft { redex: ReplayNode::Constant(constant) },
            SHARED,
        ];
        let unit_trace = [SHARED];
        for (sides, trace, divergent) in [
            (ReplaySides::Values(left, right), unit_trace.as_slice(), false),
            (ReplaySides::Computations(applied, target), unit_trace.as_slice(), false),
            (ReplaySides::Values(instance, right), unfolding.as_slice(), false),
            (ReplaySides::Computations(omega, target), unit_trace.as_slice(), true),
        ] {
            let claim = if apart { EngineClaim::NotConvertible } else { EngineClaim::Convertible };
            let expected = if divergent {
                KernelVerdict::Declined(ReplayDecline::Budget)
            } else if apart {
                KernelVerdict::NotConvertible
            } else {
                KernelVerdict::Convertible
            };
            let golden = repeat_and_clone(
                &mut arena, &unfoldings, sides, claim, trace, ReplayBudget::from(256),
            )?;
            prop_assert_eq!(golden, expected);
            let mut varied = trace.to_vec();
            match mutation {
                | 0 => {},
                | 1 => varied.clear(),
                | 2 => varied.push(SHARED),
                | _ => varied.insert(0, ConversionDecision::Force { thunk: ReplayNode::Other }),
            }
            for claim in [EngineClaim::Convertible, EngineClaim::NotConvertible, EngineClaim::Declined] {
                let _verdict = repeat_and_clone(
                    &mut arena, &unfoldings, sides, claim, &varied, ReplayBudget::from(budget),
                )?;
            }
        }
    }
}

#[test]
fn every_replay_refusal_carries_its_pinned_class()
{
    let mut arena = TermArena::new();
    let unit = arena.value_unit();
    let bound = arena.value_variable(DeBruijnIndex::from(0));
    let constant = ConstantIndex::from(0_usize);
    let named = arena.value_constant(constant);
    let mark = arena.watermark();
    let dangling = arena.value_unit();
    arena.truncate_to(mark);
    let unfoldings = Unfoldings::new(vec![Unfoldable::Body(unit)]);
    let units = ReplaySides::Values(unit, unit);
    let defined = ReplaySides::Values(named, bound);
    let force = ConversionDecision::Force {
        thunk: ReplayNode::Other,
    };
    let shortcut = ConversionDecision::ConstShortcut {
        constant: ReplayNode::Constant(constant),
    };
    let at = TracePosition::from(0_usize);
    let rows: [(_, _, &[ConversionDecision<ReplayNode>], _, _); 6] = [
        (
            ReplaySides::Values(dangling, unit),
            EngineClaim::Convertible,
            &[],
            ReplayRefusal::Unreadable,
            RefusalClass::IllFormedQuery,
        ),
        (
            defined,
            EngineClaim::Convertible,
            &[force],
            ReplayRefusal::Inapplicable { at },
            RefusalClass::ForeignAnswer,
        ),
        (
            defined,
            EngineClaim::NotConvertible,
            &[shortcut],
            ReplayRefusal::NonAuthoritative { at },
            RefusalClass::ForeignAnswer,
        ),
        (
            units,
            EngineClaim::NotConvertible,
            &[],
            ReplayRefusal::Contradicted { at },
            RefusalClass::PathDisagreement,
        ),
        (
            defined,
            EngineClaim::Convertible,
            &[],
            ReplayRefusal::Exhausted,
            RefusalClass::PathDisagreement,
        ),
        (
            units,
            EngineClaim::Convertible,
            &[force],
            ReplayRefusal::Leftover { at },
            RefusalClass::PathDisagreement,
        ),
    ];
    let mut covered = [false; 6];
    for (sides, claim, trace, reason, class) in rows {
        let row = match reason {
            ReplayRefusal::Unreadable => 0,
            ReplayRefusal::Inapplicable { .. } => 1,
            ReplayRefusal::NonAuthoritative { .. } => 2,
            ReplayRefusal::Contradicted { .. } => 3,
            ReplayRefusal::Exhausted => 4,
            ReplayRefusal::Leftover { .. } => 5,
        };
        covered[row] = true;
        assert_eq!(
            replay(
                &mut arena,
                &unfoldings,
                sides,
                claim,
                trace.iter().copied(),
                ReplayBudget::DEFAULT
            ),
            KernelVerdict::Declined(ReplayDecline::Refused(reason)),
            "{class:?} keeps {reason:?}",
        );
        assert_eq!(reason.class(), class, "{reason:?} is {class:?}");
        assert_eq!(arena.watermark(), mark);
    }
    assert_eq!(covered, [true; 6]);
}

#[test]
fn an_ill_formed_query_and_a_path_disagreement_are_two_diagnostics()
{
    let mut arena = TermArena::new();
    let unit = arena.value_unit();
    let bound = arena.value_variable(DeBruijnIndex::from(0));
    let named = arena.value_constant(ConstantIndex::from(0_usize));
    let mark = arena.watermark();
    let dangling = arena.value_unit();
    arena.truncate_to(mark);
    let unfoldings = Unfoldings::new(vec![Unfoldable::Body(unit)]);
    let mut diagnostic = |sides| match replay(
        &mut arena,
        &unfoldings,
        sides,
        EngineClaim::Convertible,
        [],
        ReplayBudget::DEFAULT,
    ) {
        KernelVerdict::Declined(decline @ ReplayDecline::Refused(_)) => decline.to_string(),
        verdict @ (KernelVerdict::Convertible
        | KernelVerdict::NotConvertible
        | KernelVerdict::Declined(_)) => panic!("the claim is refused: {verdict:?}"),
    };
    assert_eq!(
        diagnostic(ReplaySides::Values(dangling, unit)),
        "an ill-formed query: the replay reached a term the arena does not resolve or no rule \
         reads",
        "a side the arena does not hold is a question with no answer"
    );
    assert_eq!(
        diagnostic(ReplaySides::Values(named, bound)),
        "a path disagreement: the trace ended while a goal still needed a decision",
        "a well-posed goal the trace stops short of is a dialogue that reaches no verdict"
    );
}

#[test]
fn a_pair_replays_as_its_components_traces_in_order()
{
    let mut arena = TermArena::new();
    let unit = arena.value_unit();
    let (first, second) = (ConstantIndex::from(0_usize), ConstantIndex::from(1_usize));
    let unfoldings = Unfoldings::new(vec![Unfoldable::Body(unit), Unfoldable::Body(unit)]);
    let (left, right) = (arena.value_constant(first), arena.value_constant(second));
    let unfold = |constant| {
        [
            ConversionDecision::Unfold {
                constant: ReplayNode::Constant(constant),
            },
            ConversionDecision::ReduceLeft {
                redex: ReplayNode::Constant(constant),
            },
        ]
    };
    let (first_trace, second_trace) = (unfold(first), unfold(second));
    let verdict = |arena: &mut TermArena, sides, trace: &[ConversionDecision<ReplayNode>]| {
        replay(
            arena,
            &unfoldings,
            sides,
            EngineClaim::Convertible,
            trace.iter().copied(),
            ReplayBudget::DEFAULT,
        )
    };
    for (sides, trace) in [
        (ReplaySides::Values(left, unit), first_trace.as_slice()),
        (ReplaySides::Values(right, unit), second_trace.as_slice()),
    ] {
        assert_eq!(
            verdict(&mut arena, sides, trace),
            KernelVerdict::Convertible,
            "each component's trace certifies it"
        );
    }
    let pair = ReplaySides::Values(
        arena.value_tuple(&[left, right]),
        arena.value_tuple(&[unit, unit]),
    );
    let composite = [first_trace, second_trace].concat();
    assert_eq!(
        verdict(&mut arena, pair, &composite),
        KernelVerdict::Convertible,
        "the components' traces, first component first, certify the pair"
    );
    let swapped = [second_trace, first_trace].concat();
    assert_eq!(
        verdict(&mut arena, pair, &swapped),
        KernelVerdict::Declined(ReplayDecline::Refused(ReplayRefusal::Inapplicable {
            at: TracePosition::from(1_usize)
        })),
        "the second component's trace read first answers a goal it is not"
    );
    let same = ReplaySides::Values(
        arena.value_tuple(&[left, unit]),
        arena.value_tuple(&[left, unit]),
    );
    assert_eq!(
        verdict(&mut arena, same, &[SHARED]),
        KernelVerdict::Convertible,
        "an alpha-equal pair closes whole on the unit dialogue"
    );
    assert_eq!(
        verdict(&mut arena, same, &[SHARED, SHARED]),
        KernelVerdict::Declined(ReplayDecline::Refused(ReplayRefusal::Leftover {
            at: TracePosition::from(1_usize)
        })),
        "and leaves a second component's unit unread"
    );
}
