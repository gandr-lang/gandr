//! Witnesses for certificate replay: the engine claims, the refusals and
//! declines, and the bounded walks over presented terms.

use alloc::vec::Vec;

use gandr_kernel_check_memo::ContentDigest;
use gandr_kernel_conversion_trace::ConversionDecision;
use gandr_kernel_conversion_trace::ConversionSide;
use gandr_kernel_conversion_trace::SubgoalPosition;
use gandr_kernel_strata::Level;
use gandr_kernel_term::AnyNode;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::Component;
use gandr_kernel_term::ComputationId;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::ConstructorTag;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::FixpointEvidence;
use gandr_kernel_term::GroundSort;
use gandr_kernel_term::LevelSignature;
use gandr_kernel_term::Presentation;
use gandr_kernel_term::PresentedRule;
use gandr_kernel_term::RuleNode;
use gandr_kernel_term::RuleVariable;
use gandr_kernel_term::Side;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::ValueId;

use super::EngineClaim;
use super::KernelVerdict;
use super::ParameterCount;
use super::ReplayBudget;
use super::ReplayDecline;
use super::ReplayNode;
use super::ReplayRefusal;
use super::ReplaySides;
use super::TracePosition;
use super::Unfoldable;
use super::Unfoldings;
use super::convert;
use super::convert_unfolding;
use super::replay;
use crate::encoding::content_digest;
use crate::env::Environment;
use crate::generated::generated;
use crate::generated::program;
use crate::presented::Presentations;

/// Replay `trace` for `sides` under the default budget.
///
/// # Specification
/// trivial.
fn run(
    arena: &mut TermArena,
    unfoldings: &Unfoldings,
    sides: ReplaySides,
    claim: EngineClaim,
    trace: &[ConversionDecision<ReplayNode>],
) -> KernelVerdict
{
    replay(
        arena,
        unfoldings,
        sides,
        claim,
        trace.iter().copied(),
        ReplayBudget::default(),
    )
}

/// The verdict a refused trace declines with.
///
/// # Specification
/// trivial.
const fn refused(refusal: ReplayRefusal) -> KernelVerdict
{
    KernelVerdict::Declined(ReplayDecline::Refused(refusal))
}

/// The decision closing a goal on two shared nodes.
const SHARED: ConversionDecision<ReplayNode> = ConversionDecision::ComparedShared {
    left: ReplayNode::Other,
    right: ReplayNode::Other,
};

/// A decision forcing a thunk.
const FORCE: ConversionDecision<ReplayNode> = ConversionDecision::Force {
    thunk: ReplayNode::Other,
};

#[test]
fn native_list_fold_reduces_without_capturing_outer_variables()
{
    let mut arena = TermArena::new();
    let unit_type = arena.value_type_unit();
    let list_type = arena.value_type_list(unit_type);
    let nil = arena.value_list_nil();
    let outer = arena.value_variable(DeBruijnIndex::from(0_u32));
    let second = arena.value_variable(DeBruijnIndex::from(1_u32));
    let tail = arena.value_list_cons(second, nil);
    let list = arena.value_list_cons(outer, tail);
    let head = arena.value_variable(DeBruijnIndex::from(1_u32));
    let folded = arena.value_variable(DeBruijnIndex::from(0_u32));
    let cell = arena.value_list_cons(head, folded);
    let on_cons = arena.computation_return(cell);
    let on_nil = arena.computation_return(nil);
    for input in [nil, list] {
        let fold = arena.computation_list_fold(unit_type, list_type, input, on_nil, on_cons);
        let expected = arena.computation_return(input);
        assert_eq!(
            run(
                &mut arena,
                &Unfoldings::default(),
                ReplaySides::Computations(fold, expected),
                EngineClaim::Convertible,
                &[]
            ),
            KernelVerdict::Convertible
        );
    }
    let unit = arena.value_unit();
    let on_nil = arena.computation_return(unit);
    let on_cons = arena.computation_return(head);
    let fold = arena.computation_list_fold(unit_type, unit_type, list, on_nil, on_cons);
    let expected = arena.computation_return(outer);
    assert_eq!(
        run(
            &mut arena,
            &Unfoldings::default(),
            ReplaySides::Computations(fold, expected),
            EngineClaim::Convertible,
            &[]
        ),
        KernelVerdict::Convertible
    );
}

#[test]
fn a_compared_pair_closes_on_alpha_equality_or_rigid_separation()
{
    let mut arena = TermArena::new();
    let none = Unfoldings::default();
    let unit = arena.value_unit();
    let near = arena.value_variable(DeBruijnIndex::from(0));
    let far = arena.value_variable(DeBruijnIndex::from(1));
    let left = arena.value_tuple(&[unit, near]);
    let same = arena.value_tuple(&[unit, near]);
    let apart = arena.value_tuple(&[unit, far]);
    let pairs = |right| ReplaySides::Values(left, right);
    let mark = arena.watermark();

    assert_eq!(
        run(&mut arena, &none, pairs(same), EngineClaim::Convertible, &[
            SHARED
        ]),
        KernelVerdict::Convertible
    );
    assert_eq!(
        run(
            &mut arena,
            &none,
            pairs(apart),
            EngineClaim::NotConvertible,
            &[SHARED]
        ),
        KernelVerdict::NotConvertible
    );
    let after = refused(ReplayRefusal::Contradicted {
        at: TracePosition::from(1),
    });
    assert_eq!(
        run(
            &mut arena,
            &none,
            pairs(same),
            EngineClaim::NotConvertible,
            &[SHARED]
        ),
        after
    );
    assert_eq!(
        run(
            &mut arena,
            &none,
            pairs(apart),
            EngineClaim::Convertible,
            &[SHARED]
        ),
        after
    );

    assert_eq!(arena.watermark(), mark);

    // A thunk and a defined constant can still reduce, so their
    // α-distinctness separates nothing and the closing does not apply.
    let first = arena.computation_return(unit);
    let second = arena.computation_return(near);
    let thunk = arena.value_thunk(first);
    let other_thunk = arena.value_thunk(second);
    let defined = Unfoldings::new(Vec::from([Unfoldable::Body(unit)]));
    let constant = arena.value_constant(ConstantIndex::from(0_usize));
    let open = refused(ReplayRefusal::Inapplicable {
        at: TracePosition::from(0),
    });
    for sides in [
        ReplaySides::Values(thunk, other_thunk),
        ReplaySides::Values(constant, near),
    ] {
        assert_eq!(
            run(&mut arena, &defined, sides, EngineClaim::NotConvertible, &[
                SHARED
            ]),
            open
        );
    }
}

#[test]
fn a_compared_pair_reads_a_returned_endpoint_the_engine_read_through_695()
{
    // #695: the engine compares a returned endpoint by what it returns, so a
    // call of a defined constant, `f(x)`, and the same call over
    // `⟨(λy. return y) x⟩` are one shared pair to it; the kernel closes the
    // closing once the endpoint set aside is read, without unfolding `f`, and
    // not when the endpoint returns another variable.
    let mut arena = TermArena::new();
    let near = arena.value_variable(DeBruijnIndex::from(0));
    let far = arena.value_variable(DeBruijnIndex::from(1));
    let bound = arena.value_variable(DeBruijnIndex::from(0));
    let returner = arena.computation_return(bound);
    let identity = arena.computation_lambda(returner);
    let body = arena.value_thunk(identity);
    let defined = Unfoldings::new(Vec::from([Unfoldable::Body(body)]));
    let function = arena.value_constant(ConstantIndex::from(0_usize));
    let returned = |arena: &mut TermArena, argument| {
        let applied = arena.computation_application(identity, argument);
        arena.value_returned(applied)
    };
    let held = |arena: &mut TermArena, argument| {
        let forced = arena.computation_force(function);
        arena.computation_application(forced, argument)
    };
    let left = held(&mut arena, near);
    let read_alike = returned(&mut arena, near);
    let alike = held(&mut arena, read_alike);
    let read_apart = returned(&mut arena, far);
    let apart = held(&mut arena, read_apart);
    let mark = arena.watermark();

    assert_eq!(
        run(
            &mut arena,
            &defined,
            ReplaySides::Computations(left, alike),
            EngineClaim::Convertible,
            &[SHARED]
        ),
        KernelVerdict::Convertible,
        "the endpoint reads as the variable it returns"
    );
    assert_eq!(
        run(
            &mut arena,
            &defined,
            ReplaySides::Computations(left, apart),
            EngineClaim::Convertible,
            &[SHARED]
        ),
        refused(ReplayRefusal::Inapplicable {
            at: TracePosition::from(0),
        }),
        "and one returning another variable is no shared pair"
    );
    assert_eq!(arena.watermark(), mark);
}

#[test]
fn the_replay_reduces_before_it_reads_a_decision()
{
    let mut arena = TermArena::new();
    let none = Unfoldings::default();
    let unit = arena.value_unit();
    let bound = arena.value_variable(DeBruijnIndex::from(0));
    let returned_bound = arena.computation_return(bound);
    let returned_unit = arena.computation_return(unit);
    let identity = arena.computation_lambda(returned_bound);
    let applied = arena.computation_application(identity, unit);
    let sequenced = arena.computation_bind(returned_unit, returned_bound);
    let pair = arena.value_tuple(&[unit, unit]);
    let returned_pair = arena.computation_return(pair);
    let injected = arena.value_injection(Side::Right.into(), unit);
    let cased = arena.computation_case(injected, &[returned_pair, returned_bound]);
    let mark = arena.watermark();

    for redex in [applied, sequenced, cased] {
        let sides = ReplaySides::Computations(redex, returned_unit);
        assert_eq!(
            run(&mut arena, &none, sides, EngineClaim::Convertible, &[]),
            KernelVerdict::Convertible
        );
    }
    let refutation = [ConversionDecision::NegativeSubgoal {
        position: SubgoalPosition::from(0),
    }];
    let sides = ReplaySides::Computations(applied, returned_pair);
    assert_eq!(
        run(
            &mut arena,
            &none,
            sides,
            EngineClaim::NotConvertible,
            &refutation
        ),
        KernelVerdict::NotConvertible
    );
    assert_eq!(arena.watermark(), mark, "every reduct is truncated away");
}

#[test]
fn an_unfolding_fires_only_where_the_trace_names_its_head()
{
    let mut arena = TermArena::new();
    let unit = arena.value_unit();
    let first = ConstantIndex::from(0_usize);
    let second = ConstantIndex::from(1_usize);
    let defined = arena.value_constant(first);
    let opaque = arena.value_constant(second);
    let unfoldings = Unfoldings::new(Vec::from([Unfoldable::Body(unit)]));
    let unfold = |constant, reduce: fn(ReplayNode) -> ConversionDecision<ReplayNode>| {
        [
            ConversionDecision::Unfold {
                constant: ReplayNode::Constant(constant),
            },
            reduce(ReplayNode::Constant(constant)),
        ]
    };
    let left = |redex| ConversionDecision::ReduceLeft { redex };
    let right = |redex| ConversionDecision::ReduceRight { redex };
    let sides = ReplaySides::Values(defined, unit);
    let at = |position| {
        refused(ReplayRefusal::Inapplicable {
            at: TracePosition::from(position),
        })
    };

    assert_eq!(
        run(
            &mut arena,
            &unfoldings,
            sides,
            EngineClaim::Convertible,
            &unfold(first, left)
        ),
        KernelVerdict::Convertible
    );
    assert_eq!(
        run(&mut arena, &unfoldings, sides, EngineClaim::Convertible, &[
        ]),
        refused(ReplayRefusal::Exhausted)
    );
    assert_eq!(
        run(
            &mut arena,
            &unfoldings,
            sides,
            EngineClaim::Convertible,
            &unfold(first, right)
        ),
        at(1)
    );
    assert_eq!(
        run(
            &mut arena,
            &unfoldings,
            sides,
            EngineClaim::Convertible,
            &unfold(second, left)
        ),
        at(1)
    );

    // Past the list a constant is opaque: compared by name, never
    // unfolded, so its leaf decides before any decision is read.
    assert_eq!(unfoldings.unfolding(second), Unfoldable::Opaque);
    let opaque_sides = ReplaySides::Values(opaque, unit);
    assert_eq!(
        run(
            &mut arena,
            &unfoldings,
            opaque_sides,
            EngineClaim::NotConvertible,
            &[]
        ),
        KernelVerdict::NotConvertible
    );
    assert_eq!(
        run(
            &mut arena,
            &unfoldings,
            opaque_sides,
            EngineClaim::Convertible,
            &unfold(second, left)
        ),
        refused(ReplayRefusal::Contradicted {
            at: TracePosition::from(0),
        })
    );
}

#[test]
fn two_reflexivities_decompose_to_their_points()
{
    let mut arena = TermArena::new();
    let unit = arena.value_unit();
    let first = ConstantIndex::from(0_usize);
    let defined = arena.value_constant(first);
    let declared = arena.value_here(defined);
    let written = arena.value_here(unit);
    let unfoldings = Unfoldings::new(Vec::from([Unfoldable::Body(unit)]));
    let sides = ReplaySides::Values(declared, written);
    let unfolded = |reduce: ConversionDecision<ReplayNode>| {
        [
            ConversionDecision::Decompose,
            ConversionDecision::Unfold {
                constant: ReplayNode::Constant(first),
            },
            reduce,
        ]
    };
    let redex = ReplayNode::Constant(first);

    assert_eq!(
        run(
            &mut arena,
            &unfoldings,
            sides,
            EngineClaim::Convertible,
            &unfolded(ConversionDecision::ReduceLeft { redex })
        ),
        KernelVerdict::Convertible,
        "the reflexivities convert by their points, one unfolding apart"
    );
    assert_eq!(
        run(
            &mut arena,
            &unfoldings,
            sides,
            EngineClaim::Convertible,
            &unfolded(ConversionDecision::ReduceRight { redex })
        ),
        refused(ReplayRefusal::Inapplicable {
            at: TracePosition::from(2),
        }),
        "the unfolding read on the other point does not apply"
    );
}

#[test]
fn an_operator_unfolds_by_instantiating_its_parameters_in_order()
{
    let mut arena = TermArena::new();
    let operator = ConstantIndex::from(0_usize);
    let alias = ConstantIndex::from(1_usize);
    // `F := λA. λB. ⌜El A × El B⌝` with its binders stripped: `A` is
    // index 1 and `B` index 0.
    let outer = arena.value_variable(DeBruijnIndex::from(1));
    let inner = arena.value_variable(DeBruijnIndex::from(0));
    let outer_type = arena.value_type_element(outer, Level::zero());
    let inner_type = arena.value_type_element(inner, Level::zero());
    let parameters = arena.value_type_product(&[outer_type, inner_type]);
    let body = arena.value_quote(parameters);
    let head = arena.value_constant(operator);
    let unfoldings = Unfoldings::new(Vec::from([
        Unfoldable::Operator {
            parameters: ParameterCount::from(2),
            body,
        },
        Unfoldable::Body(head),
    ]));
    let integer = arena.value_type_base(BaseType::Integer);
    let string = arena.value_type_base(BaseType::String);
    let integer_code = arena.value_quote(integer);
    let string_code = arena.value_quote(string);
    let in_order_type = arena.value_type_product(&[integer, string]);
    let in_order = arena.value_quote(in_order_type);
    let swapped_type = arena.value_type_product(&[string, integer]);
    let swapped = arena.value_quote(swapped_type);
    let partial = arena.value_static_application(head, integer_code);
    let instance = arena.value_static_application(partial, string_code);
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

    // The last argument meets the innermost binder.
    assert_eq!(
        run(
            &mut arena,
            &unfoldings,
            ReplaySides::Values(instance, in_order),
            EngineClaim::Convertible,
            &unfold(operator)
        ),
        KernelVerdict::Convertible
    );
    assert_eq!(
        run(
            &mut arena,
            &unfoldings,
            ReplaySides::Values(instance, swapped),
            EngineClaim::NotConvertible,
            &unfold(operator)
        ),
        KernelVerdict::NotConvertible
    );

    // An argument open in the ambient context is carried past the outer
    // parameter: `F(⌜Integer⌝, x)` is `⌜Integer × El x⌝`, where an
    // uncarried `x` would be captured as `A` and give `Integer × Integer`.
    let ambient = arena.value_variable(DeBruijnIndex::from(0));
    let open_instance = arena.value_static_application(partial, ambient);
    let ambient_type = arena.value_type_element(ambient, Level::zero());
    let open_type = arena.value_type_product(&[integer, ambient_type]);
    let open = arena.value_quote(open_type);
    assert_eq!(
        run(
            &mut arena,
            &unfoldings,
            ReplaySides::Values(open_instance, open),
            EngineClaim::Convertible,
            &unfold(operator)
        ),
        KernelVerdict::Convertible
    );

    // A body standing at a static spine keeps the spine over it.
    let alias_head = arena.value_constant(alias);
    let alias_partial = arena.value_static_application(alias_head, integer_code);
    let alias_instance = arena.value_static_application(alias_partial, string_code);
    let mut through_alias = Vec::from(unfold(alias));
    through_alias.extend(unfold(operator));
    assert_eq!(
        run(
            &mut arena,
            &unfoldings,
            ReplaySides::Values(alias_instance, in_order),
            EngineClaim::Convertible,
            &through_alias
        ),
        KernelVerdict::Convertible
    );

    // An operator short of its arguments has no δβ-reduct.
    assert_eq!(
        run(
            &mut arena,
            &unfoldings,
            ReplaySides::Values(partial, in_order),
            EngineClaim::Convertible,
            &unfold(operator)
        ),
        refused(ReplayRefusal::Unreadable)
    );
}

#[test]
fn a_refutation_follows_its_negative_subgoal()
{
    let mut arena = TermArena::new();
    let none = Unfoldings::default();
    let unit = arena.value_unit();
    let bound = arena.value_variable(DeBruijnIndex::from(0));
    let left = arena.value_tuple(&[unit, unit]);
    let right = arena.value_tuple(&[unit, bound]);
    let sides = ReplaySides::Values(left, right);
    let negative = |position| {
        [ConversionDecision::NegativeSubgoal {
            position: SubgoalPosition::from(position),
        }]
    };

    assert_eq!(
        run(
            &mut arena,
            &none,
            sides,
            EngineClaim::NotConvertible,
            &negative(1)
        ),
        KernelVerdict::NotConvertible
    );
    assert_eq!(
        run(
            &mut arena,
            &none,
            sides,
            EngineClaim::NotConvertible,
            &negative(0)
        ),
        refused(ReplayRefusal::Contradicted {
            at: TracePosition::from(1),
        })
    );
    assert_eq!(
        run(
            &mut arena,
            &none,
            sides,
            EngineClaim::NotConvertible,
            &negative(2)
        ),
        refused(ReplayRefusal::Inapplicable {
            at: TracePosition::from(0),
        })
    );
    assert_eq!(
        run(&mut arena, &none, sides, EngineClaim::NotConvertible, &[]),
        refused(ReplayRefusal::Exhausted)
    );
    assert_eq!(
        run(&mut arena, &none, sides, EngineClaim::Convertible, &[]),
        refused(ReplayRefusal::Contradicted {
            at: TracePosition::from(0),
        })
    );
}

#[test]
fn a_frozen_branch_cannot_carry_a_refutation()
{
    let mut arena = TermArena::new();
    let unit = arena.value_unit();
    let pair = arena.value_tuple(&[unit, unit]);
    let first = ConstantIndex::from(0_usize);
    let second = ConstantIndex::from(1_usize);
    let third = ConstantIndex::from(2_usize);
    let named_first = arena.value_constant(first);
    let named_second = arena.value_constant(second);
    let named_third = arena.value_constant(third);
    let unfoldings = Unfoldings::new(Vec::from([
        Unfoldable::Body(unit),
        Unfoldable::Body(named_first),
        Unfoldable::Body(pair),
    ]));
    let node = ReplayNode::Constant;
    let unfold_second = [
        ConversionDecision::Unfold {
            constant: node(second),
        },
        ConversionDecision::ReduceLeft {
            redex: node(second),
        },
    ];
    let shortcut = ConversionDecision::ConstShortcut {
        constant: node(first),
    };
    let chain = ReplaySides::Values(named_second, named_first);

    // Convertibility through either branch: freeze the right's head and
    // unfold the left's, or postpone the right's and unfold the left's.
    for branch in [
        ConversionDecision::Freeze {
            constant: node(first),
            side: ConversionSide::Right,
        },
        ConversionDecision::Postpone {
            constant: node(first),
        },
    ] {
        let trace = [branch, unfold_second[0], unfold_second[1], shortcut];
        assert_eq!(
            run(
                &mut arena,
                &unfoldings,
                chain,
                EngineClaim::Convertible,
                &trace
            ),
            KernelVerdict::Convertible
        );
    }

    // A refutation through a freeze or a shortcut is refused; through the
    // two unfoldings it is certified.
    let apart = ReplaySides::Values(named_first, named_third);
    let unauthorised = refused(ReplayRefusal::NonAuthoritative {
        at: TracePosition::from(0),
    });
    let frozen = ConversionDecision::Freeze {
        constant: node(first),
        side: ConversionSide::Left,
    };
    for decision in [frozen, shortcut] {
        assert_eq!(
            run(
                &mut arena,
                &unfoldings,
                apart,
                EngineClaim::NotConvertible,
                &[decision]
            ),
            unauthorised
        );
    }
    let unfolded = [
        ConversionDecision::Unfold {
            constant: node(first),
        },
        ConversionDecision::ReduceLeft { redex: node(first) },
        ConversionDecision::Unfold {
            constant: node(third),
        },
        ConversionDecision::ReduceRight { redex: node(third) },
    ];
    assert_eq!(
        run(
            &mut arena,
            &unfoldings,
            apart,
            EngineClaim::NotConvertible,
            &unfolded
        ),
        KernelVerdict::NotConvertible
    );
}

#[test]
fn anchor_free_constant_decisions_read_their_constant_off_the_shapes()
{
    let mut arena = TermArena::new();
    let unit = arena.value_unit();
    let pair = arena.value_tuple(&[unit, unit]);
    let first = ConstantIndex::from(0_usize);
    let second = ConstantIndex::from(1_usize);
    let third = ConstantIndex::from(2_usize);
    let named_first = arena.value_constant(first);
    let named_second = arena.value_constant(second);
    let named_third = arena.value_constant(third);
    let unfoldings = Unfoldings::new(Vec::from([
        Unfoldable::Body(unit),
        Unfoldable::Body(named_first),
        Unfoldable::Body(pair),
    ]));
    let other = ReplayNode::Other;
    let unfold_left = [
        ConversionDecision::Unfold { constant: other },
        ConversionDecision::ReduceLeft { redex: other },
    ];
    let shortcut = ConversionDecision::ConstShortcut { constant: other };
    let postpone = ConversionDecision::Postpone { constant: other };
    let freeze = |side| ConversionDecision::Freeze {
        constant: other,
        side,
    };
    let at = |position| {
        refused(ReplayRefusal::Inapplicable {
            at: TracePosition::from(position),
        })
    };
    let chain = ReplaySides::Values(named_second, named_first);

    // Both branches of the anchored chain replay with no constant named:
    // the freeze takes the right's head, the postponement the head
    // opposite the unfolding, the shortcut the head both sides share.
    for branch in [freeze(ConversionSide::Right), postpone] {
        let trace = [branch, unfold_left[0], unfold_left[1], shortcut];
        assert_eq!(
            run(
                &mut arena,
                &unfoldings,
                chain,
                EngineClaim::Convertible,
                &trace
            ),
            KernelVerdict::Convertible
        );
    }

    // Freezing the left leaves its head no unfolding: the reduction that
    // names it refuses.
    let wrong_freeze = [freeze(ConversionSide::Left), unfold_left[0], unfold_left[1]];
    assert_eq!(
        run(
            &mut arena,
            &unfoldings,
            chain,
            EngineClaim::Convertible,
            &wrong_freeze
        ),
        at(2)
    );

    // A side with no defined head offers no constant to freeze, to
    // postpone against, or to share.
    let bare = ReplaySides::Values(named_first, unit);
    assert_eq!(
        run(&mut arena, &unfoldings, bare, EngineClaim::Convertible, &[
            freeze(ConversionSide::Right)
        ]),
        at(0)
    );
    assert_eq!(
        run(&mut arena, &unfoldings, bare, EngineClaim::Convertible, &[
            postpone,
            unfold_left[0],
            unfold_left[1]
        ]),
        at(2)
    );

    // Two different defined heads share no constant to shortcut.
    assert_eq!(
        run(
            &mut arena,
            &unfoldings,
            ReplaySides::Values(named_second, named_third),
            EngineClaim::Convertible,
            &[shortcut]
        ),
        at(0)
    );
}

#[test]
fn eta_and_force_open_the_suspended_sides()
{
    let mut arena = TermArena::new();
    let none = Unfoldings::default();
    let free = arena.value_variable(DeBruijnIndex::from(0));
    let free_under_binder = arena.value_variable(DeBruijnIndex::from(1));
    let bound = arena.value_variable(DeBruijnIndex::from(0));
    let forced = arena.computation_force(free_under_binder);
    let applied = arena.computation_application(forced, bound);
    let lambda = arena.computation_lambda(applied);
    let expanded = arena.value_thunk(lambda);
    let sides = ReplaySides::Values(expanded, free);
    let eta = |side| ConversionDecision::EtaExpand {
        side,
        variable: ReplayNode::Other,
    };

    assert_eq!(
        run(&mut arena, &none, sides, EngineClaim::Convertible, &[
            FORCE,
            FORCE,
            eta(ConversionSide::Right)
        ]),
        KernelVerdict::Convertible
    );
    assert_eq!(
        run(&mut arena, &none, sides, EngineClaim::Convertible, &[
            FORCE, FORCE
        ]),
        refused(ReplayRefusal::Exhausted)
    );
    assert_eq!(
        run(&mut arena, &none, sides, EngineClaim::Convertible, &[
            FORCE,
            FORCE,
            eta(ConversionSide::Left)
        ]),
        refused(ReplayRefusal::Inapplicable {
            at: TracePosition::from(2),
        })
    );
    assert_eq!(
        run(&mut arena, &none, sides, EngineClaim::Convertible, &[
            FORCE,
            eta(ConversionSide::Right)
        ]),
        refused(ReplayRefusal::Inapplicable {
            at: TracePosition::from(1),
        })
    );
}

#[test]
fn the_laws_of_bind_replay_by_name()
{
    let mut arena = TermArena::new();
    let none = Unfoldings::default();
    let return_eta = |side| ConversionDecision::ReturnEta { side };
    let reassociate = |side| ConversionDecision::Reassociate { side };
    let negative = |position: u32| ConversionDecision::NegativeSubgoal {
        position: SubgoalPosition::from(position),
    };
    let variable =
        |arena: &mut TermArena, index: u32| arena.value_variable(DeBruijnIndex::from(index));

    // F-η: `force f` against `force f to x. return x`, `f` free.
    let function = variable(&mut arena, 0);
    let held = arena.computation_force(function);
    let bound = variable(&mut arena, 0);
    let returned = arena.computation_return(bound);
    let expanded = arena.computation_bind(held, returned);
    let eta = ReplaySides::Computations(held, expanded);
    let flipped = ReplaySides::Computations(expanded, held);
    assert_eq!(
        run(&mut arena, &none, eta, EngineClaim::Convertible, &[
            return_eta(ConversionSide::Left)
        ]),
        KernelVerdict::Convertible
    );
    assert_eq!(
        run(&mut arena, &none, flipped, EngineClaim::Convertible, &[
            return_eta(ConversionSide::Right)
        ]),
        KernelVerdict::Convertible
    );
    assert_eq!(
        run(&mut arena, &none, eta, EngineClaim::Convertible, &[]),
        refused(ReplayRefusal::Exhausted)
    );
    for wrong in [
        return_eta(ConversionSide::Right),
        reassociate(ConversionSide::Left),
        ConversionDecision::Decompose,
    ] {
        assert_eq!(
            run(&mut arena, &none, eta, EngineClaim::Convertible, &[wrong]),
            refused(ReplayRefusal::Inapplicable {
                at: TracePosition::from(0),
            })
        );
    }

    // Not pointwise: `force f` against `force f to x. force x`, whose
    // continuation reads what the call returned. The refutation runs through
    // the law, never past it.
    let read = variable(&mut arena, 0);
    let forced = arena.computation_force(read);
    let apart = arena.computation_bind(held, forced);
    let apart = ReplaySides::Computations(held, apart);
    assert_eq!(
        run(&mut arena, &none, apart, EngineClaim::NotConvertible, &[
            return_eta(ConversionSide::Left),
            negative(0)
        ]),
        KernelVerdict::NotConvertible
    );
    assert_eq!(
        run(&mut arena, &none, apart, EngineClaim::NotConvertible, &[
            negative(0)
        ]),
        refused(ReplayRefusal::Inapplicable {
            at: TracePosition::from(0),
        })
    );

    // Associativity: `(force f to x. g x) to y. g y` against
    // `force f to x. (g x to y. g y)`, `f` and `g` free; the outer
    // continuation's `g` moves past the new binder.
    let applied = |arena: &mut TermArena, function: u32| {
        let function = variable(arena, function);
        let forced = arena.computation_force(function);
        let argument = variable(arena, 0);
        arena.computation_application(forced, argument)
    };
    let function = variable(&mut arena, 1);
    let head = arena.computation_force(function);
    let first = applied(&mut arena, 1);
    let inner = arena.computation_bind(head, first);
    let nested = arena.computation_bind(inner, first);
    let shifted = applied(&mut arena, 2);
    let fused = arena.computation_bind(first, shifted);
    let reassociated = arena.computation_bind(head, fused);
    let associativity = ReplaySides::Computations(nested, reassociated);
    assert_eq!(
        run(
            &mut arena,
            &none,
            associativity,
            EngineClaim::Convertible,
            &[reassociate(ConversionSide::Left)]
        ),
        KernelVerdict::Convertible
    );
    assert_eq!(
        run(
            &mut arena,
            &none,
            ReplaySides::Computations(reassociated, nested),
            EngineClaim::Convertible,
            &[reassociate(ConversionSide::Right)]
        ),
        KernelVerdict::Convertible
    );
    assert_eq!(
        run(
            &mut arena,
            &none,
            associativity,
            EngineClaim::Convertible,
            &[reassociate(ConversionSide::Right)]
        ),
        refused(ReplayRefusal::Inapplicable {
            at: TracePosition::from(0),
        })
    );

    // Without the shift the outer continuation would read `x` for `g`:
    // that twin is apart, and its refutation names the continuation.
    let unshifted = arena.computation_bind(first, first);
    let unshifted = arena.computation_bind(head, unshifted);
    assert_eq!(
        run(
            &mut arena,
            &none,
            ReplaySides::Computations(nested, unshifted),
            EngineClaim::NotConvertible,
            &[reassociate(ConversionSide::Left), negative(0), negative(1)]
        ),
        KernelVerdict::NotConvertible
    );

    // Two stacked twins decompose position by position, but the law owes
    // their reassociation first: a decomposition there is refused.
    let twin = arena.computation_bind(head, first);
    let twin = arena.computation_bind(twin, first);
    assert_eq!(
        run(
            &mut arena,
            &none,
            ReplaySides::Computations(nested, twin),
            EngineClaim::Convertible,
            &[ConversionDecision::Decompose]
        ),
        refused(ReplayRefusal::Inapplicable {
            at: TracePosition::from(0),
        })
    );
}

#[test]
fn an_unread_call_replays_as_its_continuation()
{
    let mut arena = TermArena::new();
    let none = Unfoldings::default();
    let discard = |side| ConversionDecision::Discard { side };
    let negative = |position: u32| ConversionDecision::NegativeSubgoal {
        position: SubgoalPosition::from(position),
    };
    let variable =
        |arena: &mut TermArena, index: u32| arena.value_variable(DeBruijnIndex::from(index));

    // `force f to x. return g` against `return g`, `f` and `g` free: the
    // call never reads what `f` returns, so it is `return g`.
    let function = variable(&mut arena, 0);
    let called = arena.computation_force(function);
    let under = variable(&mut arena, 2);
    let after = arena.computation_return(under);
    let unread = arena.computation_bind(called, after);
    let outside = variable(&mut arena, 1);
    let returned = arena.computation_return(outside);
    let dropped = ReplaySides::Computations(unread, returned);
    assert_eq!(
        run(&mut arena, &none, dropped, EngineClaim::Convertible, &[
            discard(ConversionSide::Left)
        ]),
        KernelVerdict::Convertible
    );
    assert_eq!(
        run(
            &mut arena,
            &none,
            ReplaySides::Computations(returned, unread),
            EngineClaim::Convertible,
            &[discard(ConversionSide::Right)]
        ),
        KernelVerdict::Convertible
    );
    assert_eq!(
        run(&mut arena, &none, dropped, EngineClaim::Convertible, &[
            discard(ConversionSide::Right)
        ]),
        refused(ReplayRefusal::Inapplicable {
            at: TracePosition::from(0),
        }),
        "the side named holds no call"
    );
    assert_eq!(
        convert(&mut arena, &none, dropped, ReplayBudget::default()),
        KernelVerdict::Convertible,
        "the kernel's own reading drops the call unread"
    );

    // Against `return h`, the pair is apart only once the call is dropped:
    // a refutation that decomposes past it is refused.
    let other = variable(&mut arena, 2);
    let elsewhere = arena.computation_return(other);
    let apart = ReplaySides::Computations(unread, elsewhere);
    assert_eq!(
        run(&mut arena, &none, apart, EngineClaim::NotConvertible, &[
            discard(ConversionSide::Left),
            negative(0)
        ]),
        KernelVerdict::NotConvertible
    );
    assert_eq!(
        run(&mut arena, &none, apart, EngineClaim::NotConvertible, &[
            negative(0)
        ]),
        refused(ReplayRefusal::Inapplicable {
            at: TracePosition::from(0),
        })
    );
}

#[test]
fn a_held_call_replays_as_its_continuation_at_its_endpoint()
{
    let mut arena = TermArena::new();
    let none = Unfoldings::default();
    let hold = |side| ConversionDecision::Hold { side };
    let variable =
        |arena: &mut TermArena, index: u32| arena.value_variable(DeBruijnIndex::from(index));
    let call = |arena: &mut TermArena, function: u32, argument: ValueId| {
        let function = variable(arena, function);
        let forced = arena.computation_force(function);
        arena.computation_application(forced, argument)
    };

    // `force t ⟨force h z⟩` against `force h z to y. force t y`, `t`, `h`
    // and `z` free: the call's value is its returned endpoint, so the bind
    // is `force t` over that endpoint (#3824).
    let argument = variable(&mut arena, 0);
    let called = call(&mut arena, 1, argument);
    let endpoint = arena.value_returned(called);
    let written = call(&mut arena, 2, endpoint);
    let bound_variable = variable(&mut arena, 0);
    let passed = call(&mut arena, 3, bound_variable);
    let bound = arena.computation_bind(called, passed);
    let held = ReplaySides::Computations(written, bound);
    assert_eq!(
        run(&mut arena, &none, held, EngineClaim::Convertible, &[hold(
            ConversionSide::Right
        )]),
        KernelVerdict::Convertible
    );
    assert_eq!(
        run(
            &mut arena,
            &none,
            ReplaySides::Computations(bound, written),
            EngineClaim::Convertible,
            &[hold(ConversionSide::Left)]
        ),
        KernelVerdict::Convertible
    );
    assert_eq!(
        run(&mut arena, &none, held, EngineClaim::Convertible, &[hold(
            ConversionSide::Left
        )]),
        refused(ReplayRefusal::Inapplicable {
            at: TracePosition::from(0),
        }),
        "the side named holds no call"
    );
    assert_eq!(
        convert(&mut arena, &none, held, ReplayBudget::default()),
        KernelVerdict::Convertible,
        "the kernel's own reading holds the call"
    );

    // Passed to another function `g`, the held call stands apart.
    let elsewhere = call(&mut arena, 4, bound_variable);
    let other = arena.computation_bind(called, elsewhere);
    assert_eq!(
        run(
            &mut arena,
            &none,
            ReplaySides::Computations(written, other),
            EngineClaim::NotConvertible,
            &[hold(ConversionSide::Right)]
        ),
        KernelVerdict::NotConvertible
    );
}

#[test]
fn the_kernel_converts_by_the_forced_rules_alone()
{
    let mut arena = TermArena::new();
    let variable =
        |arena: &mut TermArena, index: u32| arena.value_variable(DeBruijnIndex::from(index));
    let function = variable(&mut arena, 0);
    let held = arena.computation_force(function);
    let bound = variable(&mut arena, 0);
    let returned = arena.computation_return(bound);
    let expanded = arena.computation_bind(held, returned);
    let other = variable(&mut arena, 2);
    let constant = arena.computation_return(other);
    let apart = arena.computation_bind(held, constant);
    // The thunks of both, so the forces fire unread too.
    let suspended = arena.value_thunk(held);
    let suspended_expanded = arena.value_thunk(expanded);
    let watermark = arena.watermark();

    for sides in [
        ReplaySides::Computations(held, expanded),
        ReplaySides::Computations(expanded, held),
        ReplaySides::Values(suspended, suspended_expanded),
    ] {
        assert_eq!(
            convert(
                &mut arena,
                &Unfoldings::default(),
                sides,
                ReplayBudget::default()
            ),
            KernelVerdict::Convertible
        );
    }
    // A pair apart declines: the kernel's own conversion certifies no
    // refutation, so an engine-free judgement never reads one.
    assert!(matches!(
        convert(
            &mut arena,
            &Unfoldings::default(),
            ReplaySides::Computations(held, apart),
            ReplayBudget::default()
        ),
        KernelVerdict::Declined(_)
    ));
    assert_eq!(arena.watermark(), watermark);
}

#[test]
fn the_kernel_unfolds_a_defined_head_within_its_budget()
{
    let mut arena = TermArena::new();
    let unit = arena.value_unit();
    let returned = arena.computation_return(unit);
    // `one = thunk(return unit)` and `spin = thunk(force spin)`.
    let one_body = arena.value_thunk(returned);
    let spin = arena.value_constant(ConstantIndex::from(1_usize));
    let spun = arena.computation_force(spin);
    let spin_body = arena.value_thunk(spun);
    let unfoldings = Unfoldings::new(Vec::from([
        Unfoldable::Body(one_body),
        Unfoldable::Body(spin_body),
    ]));
    let one = arena.value_constant(ConstantIndex::from(0_usize));
    let forced = arena.computation_force(one);
    let other_unit = arena.value_unit();
    let expected = arena.computation_return(other_unit);
    let watermark = arena.watermark();
    let met = ReplaySides::Computations(forced, expected);

    assert_eq!(
        convert_unfolding(&mut arena, &unfoldings, met, ReplayBudget::default()),
        KernelVerdict::Convertible,
        "a definition run at the head is read by what it computes"
    );
    assert!(
        matches!(
            convert(&mut arena, &unfoldings, met, ReplayBudget::default()),
            KernelVerdict::Declined(_)
        ),
        "the δ-free conversion compares the definition by its name and declines"
    );
    assert_eq!(
        convert_unfolding(
            &mut arena,
            &unfoldings,
            ReplaySides::Computations(spun, expected),
            ReplayBudget::from(64_u64)
        ),
        KernelVerdict::Declined(ReplayDecline::Budget),
        "a definition that unfolds to itself runs past the budget and is declined as \
             such, never read as apart"
    );
    assert_eq!(arena.watermark(), watermark);
}

#[test]
fn the_replay_refuses_a_trace_that_does_not_replay()
{
    let mut arena = TermArena::new();
    let unit = arena.value_unit();
    let other_unit = arena.value_unit();
    let first = ConstantIndex::from(0_usize);
    let named = arena.value_constant(first);
    let unfoldings = Unfoldings::new(Vec::from([Unfoldable::Body(unit)]));
    let units = ReplaySides::Values(unit, other_unit);
    let stray = ConversionDecision::ReduceLeft {
        redex: ReplayNode::Constant(first),
    };

    // A leaf decides silently, so a decision past it is left over.
    assert_eq!(
        run(&mut arena, &unfoldings, units, EngineClaim::Convertible, &[
            SHARED, SHARED
        ]),
        refused(ReplayRefusal::Leftover {
            at: TracePosition::from(1),
        })
    );
    assert_eq!(
        run(&mut arena, &unfoldings, units, EngineClaim::Convertible, &[
            stray
        ]),
        refused(ReplayRefusal::Leftover {
            at: TracePosition::from(0),
        })
    );

    // A reduction is read only after its unfolding, and a postponement
    // only before one.
    let defined = ReplaySides::Values(named, unit);
    assert_eq!(
        run(
            &mut arena,
            &unfoldings,
            defined,
            EngineClaim::Convertible,
            &[stray]
        ),
        refused(ReplayRefusal::Inapplicable {
            at: TracePosition::from(0),
        })
    );
    let postponed = [
        ConversionDecision::Postpone {
            constant: ReplayNode::Constant(first),
        },
        FORCE,
    ];
    assert_eq!(
        run(
            &mut arena,
            &unfoldings,
            defined,
            EngineClaim::Convertible,
            &postponed
        ),
        refused(ReplayRefusal::Inapplicable {
            at: TracePosition::from(1),
        })
    );
}

#[test]
fn an_engine_decline_and_an_exhausted_budget_decline()
{
    let mut arena = TermArena::new();
    let none = Unfoldings::default();
    let unit = arena.value_unit();
    let returned_unit = arena.computation_return(unit);

    let units = ReplaySides::Values(unit, unit);
    assert_eq!(
        run(&mut arena, &none, units, EngineClaim::Declined, &[SHARED]),
        KernelVerdict::Declined(ReplayDecline::EngineDeclined)
    );

    // Ω: a self-application that reduces to itself forever.
    let bound = arena.value_variable(DeBruijnIndex::from(0));
    let forced = arena.computation_force(bound);
    let self_applied = arena.computation_application(forced, bound);
    let lambda = arena.computation_lambda(self_applied);
    let suspended = arena.value_thunk(lambda);
    let omega = arena.computation_application(lambda, suspended);
    let mark = arena.watermark();
    for sides in [
        ReplaySides::Computations(omega, returned_unit),
        ReplaySides::Computations(returned_unit, omega),
        ReplaySides::Computations(omega, omega),
    ] {
        for claim in [EngineClaim::Convertible, EngineClaim::NotConvertible] {
            let verdict = replay(
                &mut arena,
                &none,
                sides,
                claim,
                [SHARED],
                ReplayBudget::from(64_u64),
            );
            assert_eq!(verdict, KernelVerdict::Declined(ReplayDecline::Budget));
            assert_eq!(arena.watermark(), mark, "every reduct is truncated away");
        }
    }
}

#[test]
fn budget_exhaustion_survives_the_counter_ceiling()
{
    let mut arena = TermArena::new();
    let unfoldings = Unfoldings::default();
    for (spent, budget, expected, after) in [
        (u64::MAX, u64::MAX, Err(super::Stop::Budget), u64::MAX),
        (0, 0, Err(super::Stop::Budget), 0),
        (0, 1, Ok(()), 1),
        (u64::MAX.saturating_sub(1), u64::MAX, Ok(()), u64::MAX),
    ] {
        let mut run = super::Replay {
            arena: &mut arena,
            unfoldings: &unfoldings,
            evaluator: &unfoldings,
            trace: core::iter::empty().peekable(),
            reading: super::Reading::Recorded,
            position: 0,
            spent,
            budget: u64::from(ReplayBudget::from(budget)),
            table: crate::ContentTable::new(),
            memo: gandr_kernel_check_memo::NullMemo,
            owed: Vec::new(),
        };
        assert_eq!(run.charge(), expected);
        assert_eq!(run.spent, after);
        assert_eq!(run.charge(), Err(super::Stop::Budget));
        assert_eq!(run.spent, after);
    }
}

#[test]
fn trace_consumption_preserves_the_end_and_position_ceiling()
{
    let mut arena = TermArena::new();
    let unfoldings = Unfoldings::default();
    for position in [0, usize::MAX] {
        let mut replay = super::Replay {
            arena: &mut arena,
            unfoldings: &unfoldings,
            evaluator: &unfoldings,
            trace: core::iter::once(SHARED).peekable(),
            reading: super::Reading::Recorded,
            position,
            spent: 0,
            budget: 1,
            table: crate::ContentTable::new(),
            memo: gandr_kernel_check_memo::NullMemo,
            owed: Vec::new(),
        };
        assert_eq!(replay.peek(), super::Next::Decision(SHARED));
        assert_eq!(replay.peek(), super::Next::Decision(SHARED));
        assert_eq!(usize::from(replay.at()), position);
        replay.take();
        assert_eq!(usize::from(replay.at()), position.saturating_add(1));
        assert_eq!(replay.peek(), super::Next::End);
        replay.take();
        assert_eq!(usize::from(replay.at()), position.saturating_add(1));
        assert_eq!(replay.peek(), super::Next::End);
    }
}

#[test]
fn frozen_heads_are_side_local_and_opacity_takes_precedence()
{
    let mut arena = TermArena::new();
    let unit = arena.value_unit();
    let unfoldings = Unfoldings::new(Vec::from([
        Unfoldable::Body(unit),
        Unfoldable::Operator {
            parameters: ParameterCount::from(0),
            body: unit,
        },
        Unfoldable::Opaque,
    ]));
    let replay = super::Replay {
        arena: &mut arena,
        unfoldings: &unfoldings,
        evaluator: &unfoldings,
        trace: core::iter::empty().peekable(),
        reading: super::Reading::Recorded,
        position: 0,
        spent: 0,
        budget: 1,
        table: crate::ContentTable::new(),
        memo: gandr_kernel_check_memo::NullMemo,
        owed: Vec::new(),
    };
    for (index, initial) in [
        (0, super::Status::Defined),
        (1, super::Status::Defined),
        (2, super::Status::Opaque),
        (3, super::Status::Opaque),
        (usize::MAX, super::Status::Opaque),
    ] {
        let constant = ConstantIndex::from(index);
        for side in [ConversionSide::Left, ConversionSide::Right] {
            let mut frozen = super::Frozen::default();
            assert_eq!(
                replay.head(constant, &frozen, side),
                super::Head::Constant(constant, initial)
            );
            frozen.freeze(side, constant);
            let expected = if initial == super::Status::Opaque {
                initial
            }
            else {
                super::Status::Frozen
            };
            assert_eq!(
                replay.head(constant, &frozen, side),
                super::Head::Constant(constant, expected)
            );
            assert_eq!(
                replay.head(constant, &frozen, super::opposite(side)),
                super::Head::Constant(constant, initial)
            );
        }
    }
}

#[test]
fn rule_dispatch_respects_constant_priority_and_eta_side()
{
    let mut arena = TermArena::new();
    let unit = arena.value_unit();
    let body = arena.computation_return(unit);
    let name = ConstantIndex::from(0);
    let shapes = [
        super::Shape::Former,
        super::Shape::Thunk(body),
        super::Shape::Lambda(body),
        super::Shape::Return(unit),
        super::Shape::Neutral(super::Head::Variable(DeBruijnIndex::from(0)), Vec::new()),
        super::Shape::Neutral(
            super::Head::Constant(name, super::Status::Opaque),
            Vec::new(),
        ),
        super::Shape::Neutral(
            super::Head::Constant(name, super::Status::Frozen),
            Vec::new(),
        ),
        super::Shape::Neutral(
            super::Head::Constant(name, super::Status::Defined),
            Vec::new(),
        ),
        super::Shape::With(alloc::boxed::Box::from([body, body])),
    ];
    for (left_kind, left) in shapes.iter().enumerate() {
        for (right_kind, right) in shapes.iter().enumerate() {
            let expected = match (left_kind, right_kind) {
                (7, _) | (_, 7) => super::Rule::Constants,
                (1, 1 | 4 ..= 6) | (4 ..= 6, 1) => super::Rule::Force,
                (2, 4 ..= 6) => super::Rule::Eta(ConversionSide::Right),
                (4 ..= 6, 2) => super::Rule::Eta(ConversionSide::Left),
                (8, 4 ..= 6) => super::Rule::ProductEta(ConversionSide::Right),
                (4 ..= 6, 8) => super::Rule::ProductEta(ConversionSide::Left),
                _ => super::Rule::Structural,
            };
            assert_eq!(
                super::rule(left, right),
                expected,
                "shape classes {left_kind}, {right_kind}"
            );
        }
    }
}

#[test]
fn a_projection_runs_its_side_of_a_pairing()
{
    let mut arena = TermArena::new();
    let none = Unfoldings::default();
    let unit = arena.value_unit();
    let free = arena.value_variable(DeBruijnIndex::from(0));
    let left = arena.computation_return(unit);
    let right = arena.computation_return(free);
    let pairing = arena.computation_with(&[left, right]);
    let first = arena.computation_project(Component::from(0_usize), pairing);
    let second = arena.computation_project(Component::from(1_usize), pairing);
    let negative = ConversionDecision::NegativeSubgoal {
        position: SubgoalPosition::from(0_u32),
    };

    // Each projection runs its own side and no decision is read.
    assert_eq!(
        run(
            &mut arena,
            &none,
            ReplaySides::Computations(first, left),
            EngineClaim::Convertible,
            &[]
        ),
        KernelVerdict::Convertible
    );
    assert_eq!(
        run(
            &mut arena,
            &none,
            ReplaySides::Computations(second, right),
            EngineClaim::Convertible,
            &[]
        ),
        KernelVerdict::Convertible
    );
    assert_eq!(
        run(
            &mut arena,
            &none,
            ReplaySides::Computations(second, left),
            EngineClaim::NotConvertible,
            &[negative]
        ),
        KernelVerdict::NotConvertible
    );

    // A projection stuck on a neutral keeps its frame over the reduct of
    // what it projects, and observes a fixpoint at its gate.
    let neutral = arena.computation_force(free);
    let suspended = arena.value_thunk(neutral);
    let forced = arena.computation_force(suspended);
    let reducible = arena.computation_project(Component::from(0_usize), forced);
    let stuck = arena.computation_project(Component::from(0_usize), neutral);
    let other_side = arena.computation_project(Component::from(1_usize), neutral);
    assert_eq!(
        run(
            &mut arena,
            &none,
            ReplaySides::Computations(reducible, stuck),
            EngineClaim::Convertible,
            &[]
        ),
        KernelVerdict::Convertible
    );
    assert_eq!(
        run(
            &mut arena,
            &none,
            ReplaySides::Computations(reducible, other_side),
            EngineClaim::NotConvertible,
            &[]
        ),
        KernelVerdict::NotConvertible
    );
    let partial = arena.computation_fixpoint(pairing, FixpointEvidence::Partial);
    let observed = arena.computation_project(Component::from(0_usize), partial);
    assert_eq!(
        run(
            &mut arena,
            &none,
            ReplaySides::Computations(observed, left),
            EngineClaim::Convertible,
            &[]
        ),
        KernelVerdict::Declined(ReplayDecline::PartialFixpoint)
    );
}

/// #2833: a partial fixpoint whose body never reads its own binder is a
/// definition, and unfolds at its gate. `isZero`, with no recursive call, at
/// `Zero` converts with `return unit`; the same fixpoint naming itself in its
/// zero arm still declines.
#[test]
fn a_partial_fixpoint_that_never_reads_itself_unfolds_at_its_gate_2833()
{
    let mut arena = TermArena::new();
    let none = Unfoldings::default();
    let nat = arena.value_type_data(ConstantIndex::from(0_usize), Vec::new());
    let zero = arena.value_constructor(nat, ConstructorTag::from(0_usize), Vec::new());
    let unit = arena.value_unit();
    let motive = arena.comp_type_returner(nat);
    let returns_unit = arena.computation_return(unit);
    let on_successor = arena.computation_lambda(returns_unit);
    let argument = arena.value_variable(DeBruijnIndex::from(0_u32));
    let cases =
        arena.computation_data_case(argument, motive, alloc::vec![returns_unit, on_successor]);
    let body = arena.computation_lambda(cases);
    let unread = arena.computation_fixpoint(body, FixpointEvidence::Partial);
    let applied = arena.computation_application(unread, zero);
    assert_eq!(
        run(
            &mut arena,
            &none,
            ReplaySides::Computations(applied, returns_unit),
            EngineClaim::Convertible,
            &[]
        ),
        KernelVerdict::Convertible
    );
    // Under the fixpoint's lambda its own binder is index 1.
    let own = arena.value_variable(DeBruijnIndex::from(1_u32));
    let again = arena.computation_force(own);
    let again = arena.computation_application(again, zero);
    let reading = arena.computation_data_case(argument, motive, alloc::vec![again, on_successor]);
    let reading = arena.computation_lambda(reading);
    let read = arena.computation_fixpoint(reading, FixpointEvidence::Partial);
    let applied = arena.computation_application(read, zero);
    assert_eq!(
        run(
            &mut arena,
            &none,
            ReplaySides::Computations(applied, returns_unit),
            EngineClaim::Convertible,
            &[]
        ),
        KernelVerdict::Declined(ReplayDecline::PartialFixpoint)
    );
}

#[test]
fn a_fixpoint_at_a_returned_endpoint_runs_the_endpoint_first()
{
    // `pred ⟨return S(Z)⟩`, with `pred` a structural fixpoint, is
    // `return Z`: the gate reads what the endpoint returns.
    let mut arena = TermArena::new();
    let none = Unfoldings::default();
    let nat = arena.value_type_data(ConstantIndex::from(0_usize), Vec::new());
    let zero = arena.value_constructor(nat, ConstructorTag::from(0_usize), Vec::new());
    let one = arena.value_constructor(nat, ConstructorTag::from(1_usize), alloc::vec![zero]);
    let motive = arena.comp_type_returner(nat);
    let on_zero = arena.computation_return(zero);
    let field = arena.value_variable(DeBruijnIndex::from(0_u32));
    let on_successor = arena.computation_return(field);
    let on_successor = arena.computation_lambda(on_successor);
    let argument = arena.value_variable(DeBruijnIndex::from(0_u32));
    let cases = arena.computation_data_case(argument, motive, alloc::vec![on_zero, on_successor]);
    let body = arena.computation_lambda(cases);
    let pred = arena.computation_fixpoint(body, FixpointEvidence::StructuralDescent);
    let returns_one = arena.computation_return(one);
    let endpoint = arena.value_returned(returns_one);
    let applied = arena.computation_application(pred, endpoint);
    let returns_zero = arena.computation_return(zero);
    assert_eq!(
        run(
            &mut arena,
            &none,
            ReplaySides::Computations(applied, returns_zero),
            EngineClaim::Convertible,
            &[]
        ),
        KernelVerdict::Convertible
    );
    assert_ne!(
        run(
            &mut arena,
            &none,
            ReplaySides::Computations(applied, returns_one),
            EngineClaim::Convertible,
            &[]
        ),
        KernelVerdict::Convertible
    );
}

#[test]
fn a_stuck_fixpoint_compares_its_leading_arguments_626()
{
    // `count = fix. λacc. λb. case b { Z ⇒ return acc; S(x) ⇒ count (S acc)
    // x }`, staged at its second binder. At a free `x`, `count (S Z) x`
    // meets `count Z (S x)` once the right side unfolds, both stuck on `x`
    // past the accumulator `S Z`; with another accumulator they stand apart.
    // Short of its staged argument, `count Z` stands at no gate and compares
    // by its body and its leading argument.
    let mut arena = TermArena::new();
    let nat = arena.value_type_data(ConstantIndex::from(0_usize), Vec::new());
    let zero = arena.value_constructor(nat, ConstructorTag::from(0_usize), Vec::new());
    let one = arena.value_constructor(nat, ConstructorTag::from(1_usize), alloc::vec![zero]);
    let motive = arena.comp_type_returner(nat);
    let accumulated = arena.value_variable(DeBruijnIndex::from(1_u32));
    let on_zero = arena.computation_return(accumulated);
    let recursive = arena.value_variable(DeBruijnIndex::from(3_u32));
    let forced = arena.computation_force(recursive);
    let accumulator = arena.value_variable(DeBruijnIndex::from(2_u32));
    let grown =
        arena.value_constructor(nat, ConstructorTag::from(1_usize), alloc::vec![accumulator]);
    let leading = arena.computation_application(forced, grown);
    let field = arena.value_variable(DeBruijnIndex::from(0_u32));
    let call = arena.computation_application(leading, field);
    let on_successor = arena.computation_lambda(call);
    let cases = arena.computation_data_case(field, motive, alloc::vec![on_zero, on_successor]);
    let staged = arena.computation_lambda(cases);
    let body = arena.computation_lambda(staged);
    let count = arena.computation_fixpoint(body, FixpointEvidence::Staged {
        position: gandr_kernel_term::StagedPosition::from(1_usize),
    });
    let free = arena.value_variable(DeBruijnIndex::from(0_u32));
    let successor = arena.value_constructor(nat, ConstructorTag::from(1_usize), alloc::vec![free]);
    let from_one = arena.computation_application(count, one);
    let stuck = arena.computation_application(from_one, free);
    let from_zero = arena.computation_application(count, zero);
    let unfolding = arena.computation_application(from_zero, successor);
    let apart = arena.computation_application(from_zero, free);
    let again = arena.computation_application(count, zero);
    let none = Unfoldings::default();

    // The kernel's own conversion relates the first two pairs; a claim that
    // the others convert closes against the leading arguments they differ in.
    for (left, right) in [(stuck, unfolding), (from_zero, again)] {
        assert_eq!(
            convert(
                &mut arena,
                &none,
                ReplaySides::Computations(left, right),
                ReplayBudget::default()
            ),
            KernelVerdict::Convertible
        );
    }
    for (left, right) in [(stuck, apart), (from_zero, from_one)] {
        assert_eq!(
            run(
                &mut arena,
                &none,
                ReplaySides::Computations(left, right),
                EngineClaim::Convertible,
                &[]
            ),
            refused(ReplayRefusal::Contradicted {
                at: TracePosition::from(0),
            })
        );
    }
}

#[test]
fn a_staged_fixpoint_unfolds_the_constant_at_its_staged_argument_3387()
{
    // `k = fix. λa. λb. case b { Z ⇒ return a; S(x) ⇒ k a x }`, staged at its
    // second binder, applied to `Z` and the defined `one = S(Z)`: stuck at
    // its gate on `one`, past the leading `Z`. The dialogue unfolds `one`
    // there, so `k Z one` reads as `k Z S(Z)` and runs to `return Z`; a
    // δ-step landing on the leading `Z` would leave `k S(Z) one` stuck at
    // `one`, apart from `return Z`.
    let mut arena = TermArena::new();
    let nat = arena.value_type_data(ConstantIndex::from(0_usize), Vec::new());
    let zero = arena.value_constructor(nat, ConstructorTag::from(0_usize), Vec::new());
    let successor = arena.value_constructor(nat, ConstructorTag::from(1_usize), alloc::vec![zero]);
    let motive = arena.comp_type_returner(nat);
    let leading = arena.value_variable(DeBruijnIndex::from(1_u32));
    let on_zero = arena.computation_return(leading);
    let recursive = arena.value_variable(DeBruijnIndex::from(3_u32));
    let forced = arena.computation_force(recursive);
    let kept = arena.value_variable(DeBruijnIndex::from(2_u32));
    let applied = arena.computation_application(forced, kept);
    let field = arena.value_variable(DeBruijnIndex::from(0_u32));
    let call = arena.computation_application(applied, field);
    let on_successor = arena.computation_lambda(call);
    let cases = arena.computation_data_case(field, motive, alloc::vec![on_zero, on_successor]);
    let staged = arena.computation_lambda(cases);
    let body = arena.computation_lambda(staged);
    let k = arena.computation_fixpoint(body, FixpointEvidence::Staged {
        position: gandr_kernel_term::StagedPosition::from(1_usize),
    });
    let one = ConstantIndex::from(1_usize);
    let named = arena.value_constant(one);
    let unfoldings = Unfoldings::new(Vec::from([Unfoldable::Opaque, Unfoldable::Body(successor)]));
    let from_zero = arena.computation_application(k, zero);
    let stuck = arena.computation_application(from_zero, named);
    let returned = arena.computation_return(zero);

    assert_eq!(
        run(
            &mut arena,
            &unfoldings,
            ReplaySides::Computations(stuck, returned),
            EngineClaim::Convertible,
            &[
                ConversionDecision::Unfold {
                    constant: ReplayNode::Constant(one),
                },
                ConversionDecision::ReduceLeft {
                    redex: ReplayNode::Constant(one),
                },
                SHARED,
            ]
        ),
        KernelVerdict::Convertible
    );
}

#[test]
fn an_endpoint_reads_a_bind_through_its_stuck_call()
{
    // `⟨pred x to n. return S(n)⟩` against `S(⟨pred x⟩)`, `pred` a
    // structural fixpoint stuck at the free `x`: `wind(Loop(x))` against
    // `S(wind(x))`. The endpoint's computation is pure, so its bind reads
    // as the continuation over the held call, and no decision names it. As
    // a computation goal of its own, which may be effectful, the bind and
    // the returner stay apart.
    let mut arena = TermArena::new();
    let nat = arena.value_type_data(ConstantIndex::from(0_usize), Vec::new());
    let zero = arena.value_constructor(nat, ConstructorTag::from(0_usize), Vec::new());
    let motive = arena.comp_type_returner(nat);
    let on_zero = arena.computation_return(zero);
    let field = arena.value_variable(DeBruijnIndex::from(0_u32));
    let on_successor = arena.computation_return(field);
    let on_successor = arena.computation_lambda(on_successor);
    let cases = arena.computation_data_case(field, motive, alloc::vec![on_zero, on_successor]);
    let body = arena.computation_lambda(cases);
    let pred = arena.computation_fixpoint(body, FixpointEvidence::StructuralDescent);
    let stuck = arena.computation_application(pred, field);
    let successor = arena.value_constructor(nat, ConstructorTag::from(1_usize), alloc::vec![field]);
    let continuation = arena.computation_return(successor);
    let bound = arena.computation_bind(stuck, continuation);
    let endpoint = arena.value_returned(bound);
    let call = arena.value_returned(stuck);
    let expected = arena.value_constructor(nat, ConstructorTag::from(1_usize), alloc::vec![call]);
    let returned = arena.computation_return(expected);
    let watermark = arena.watermark();

    assert_eq!(
        convert(
            &mut arena,
            &Unfoldings::default(),
            ReplaySides::Values(endpoint, expected),
            ReplayBudget::default()
        ),
        KernelVerdict::Convertible
    );
    assert!(matches!(
        convert(
            &mut arena,
            &Unfoldings::default(),
            ReplaySides::Computations(bound, returned),
            ReplayBudget::default()
        ),
        KernelVerdict::Declined(_)
    ));
    assert_eq!(arena.watermark(), watermark);
}

#[test]
fn an_endpoint_reads_a_bind_handing_its_stuck_call_to_a_definition_761()
{
    // `⟨pred x to n. succ n⟩` against `S(⟨pred x⟩)`, `succ = λy. return
    // S(y)` a definition: `double(S(m))`'s arm `twice(double(m))` in
    // miniature. The continuation stops at `succ`'s call over the held
    // call, so the endpoint reads as that call, and the conversion unfolds
    // `succ` to meet the constructor. Before, the reading kept the bind
    // whole and the sides stood apart.
    let mut arena = TermArena::new();
    let nat = arena.value_type_data(ConstantIndex::from(0_usize), Vec::new());
    let zero = arena.value_constructor(nat, ConstructorTag::from(0_usize), Vec::new());
    let motive = arena.comp_type_returner(nat);
    let on_zero = arena.computation_return(zero);
    let field = arena.value_variable(DeBruijnIndex::from(0_u32));
    let on_successor = arena.computation_return(field);
    let on_successor = arena.computation_lambda(on_successor);
    let cases = arena.computation_data_case(field, motive, alloc::vec![on_zero, on_successor]);
    let body = arena.computation_lambda(cases);
    let pred = arena.computation_fixpoint(body, FixpointEvidence::StructuralDescent);
    let stuck = arena.computation_application(pred, field);
    let successor = arena.value_constructor(nat, ConstructorTag::from(1_usize), alloc::vec![field]);
    let wrapped = arena.computation_return(successor);
    let wrapping = arena.computation_lambda(wrapped);
    let wrapping = arena.value_thunk(wrapping);
    let unfoldings = Unfoldings::new(alloc::vec![Unfoldable::Opaque, Unfoldable::Body(wrapping)]);
    let succ = arena.value_constant(ConstantIndex::from(1_usize));
    let forced = arena.computation_force(succ);
    let continuation = arena.computation_application(forced, field);
    let bound = arena.computation_bind(stuck, continuation);
    let endpoint = arena.value_returned(bound);
    let call = arena.value_returned(stuck);
    let expected = arena.value_constructor(nat, ConstructorTag::from(1_usize), alloc::vec![call]);
    let unfold = [
        ConversionDecision::Unfold {
            constant: ReplayNode::Constant(ConstantIndex::from(1_usize)),
        },
        ConversionDecision::ReduceLeft {
            redex: ReplayNode::Constant(ConstantIndex::from(1_usize)),
        },
    ];

    assert_eq!(
        run(
            &mut arena,
            &unfoldings,
            ReplaySides::Values(endpoint, expected),
            EngineClaim::Convertible,
            &unfold
        ),
        KernelVerdict::Convertible
    );
}

#[test]
fn an_endpoint_reads_a_bind_handing_its_stuck_call_to_a_binder_2773()
{
    // `⟨pred x to n. p n⟩` against `⟨p ⟨pred x⟩⟩`, `p` a binder: a
    // specification's `post((), s + 1)`, bound ahead, against the call a fold
    // handing `post` the sum held reads to, in miniature. The continuation
    // stops at `p`'s call over the held call, so the endpoint reads as that
    // call and meets the written one with no decision; against the binder
    // `q`'s call it refutes at the head. Before, the reading kept the bind
    // whole and the first pair stood apart.
    let mut arena = TermArena::new();
    let nat = arena.value_type_data(ConstantIndex::from(0_usize), Vec::new());
    let zero = arena.value_constructor(nat, ConstructorTag::from(0_usize), Vec::new());
    let motive = arena.comp_type_returner(nat);
    let on_zero = arena.computation_return(zero);
    let field = arena.value_variable(DeBruijnIndex::from(0_u32));
    let on_successor = arena.computation_return(field);
    let on_successor = arena.computation_lambda(on_successor);
    let cases = arena.computation_data_case(field, motive, alloc::vec![on_zero, on_successor]);
    let body = arena.computation_lambda(cases);
    let pred = arena.computation_fixpoint(body, FixpointEvidence::StructuralDescent);
    let stuck = arena.computation_application(pred, field);
    let applied = |arena: &mut TermArena, head: u32, argument| {
        let head = arena.value_variable(DeBruijnIndex::from(head));
        let forced = arena.computation_force(head);
        arena.computation_application(forced, argument)
    };
    let continuation = applied(&mut arena, 2_u32, field);
    let bound = arena.computation_bind(stuck, continuation);
    let endpoint = arena.value_returned(bound);
    let call = arena.value_returned(stuck);
    let written = applied(&mut arena, 1_u32, call);
    let written = arena.value_returned(written);
    let other = applied(&mut arena, 2_u32, call);
    let other = arena.value_returned(other);

    assert_eq!(
        convert(
            &mut arena,
            &Unfoldings::default(),
            ReplaySides::Values(endpoint, written),
            ReplayBudget::default()
        ),
        KernelVerdict::Convertible
    );
    assert_eq!(
        run(
            &mut arena,
            &Unfoldings::default(),
            ReplaySides::Values(endpoint, other),
            EngineClaim::Convertible,
            &[]
        ),
        refused(ReplayRefusal::Contradicted {
            at: TracePosition::from(0),
        })
    );
}

#[test]
fn an_endpoint_read_twice_runs_its_call_once_1747()
{
    // `x ← ⟨tag u⟩.0; y ← ⟨tag u⟩.1; return y` against `return t`, `tag =
    // λb. return (b, t)` a definition: a reading carried between two
    // carriers, which takes both components of the pair its moved argument
    // returns, in miniature. The endpoint's call waits on `tag`, so it is
    // bound once over both projections and one recorded unfold serves both.
    // Before, each projection ran the call again and wanted an unfold of its
    // own, which the producer, keeping one unfolding per held endpoint, never
    // recorded.
    use alloc::string::String;

    use gandr_kernel_term::Literal;
    use gandr_kernel_term::StringLiteral;

    let mut arena = TermArena::new();
    let unit = arena.value_unit();
    let text = arena.value_literal(Literal::Text(StringLiteral::new(String::from("t"))));
    let bound = arena.value_variable(DeBruijnIndex::from(0_u32));
    let pair = arena.value_tuple(&[bound, text]);
    let returns_pair = arena.computation_return(pair);
    let body = arena.computation_lambda(returns_pair);
    let body = arena.value_thunk(body);
    let unfoldings = Unfoldings::new(alloc::vec![Unfoldable::Body(body)]);
    let tag = arena.value_constant(ConstantIndex::from(0_usize));
    let forced = arena.computation_force(tag);
    let call = arena.computation_application(forced, unit);
    let endpoint = arena.value_returned(call);
    let first = arena.computation_tuple_projection(endpoint, Component::from(0_usize));
    let second = arena.computation_tuple_projection(endpoint, Component::from(1_usize));
    let returns_second = arena.computation_return(bound);
    let rest = arena.computation_bind(second, returns_second);
    let read = arena.computation_bind(first, rest);
    let expected = arena.computation_return(text);
    let unfold = [
        ConversionDecision::Unfold {
            constant: ReplayNode::Constant(ConstantIndex::from(0_usize)),
        },
        ConversionDecision::ReduceLeft {
            redex: ReplayNode::Constant(ConstantIndex::from(0_usize)),
        },
    ];
    let shared = ConversionDecision::ComparedShared {
        left: ReplayNode::Other,
        right: ReplayNode::Other,
    };
    let sides = ReplaySides::Computations(read, expected);
    let once = [unfold[0], unfold[1], shared];
    assert_eq!(
        run(
            &mut arena,
            &unfoldings,
            sides,
            EngineClaim::Convertible,
            &once
        ),
        KernelVerdict::Convertible
    );
    let twice = [unfold[0], unfold[1], unfold[0], unfold[1], shared];
    assert_ne!(
        run(
            &mut arena,
            &unfoldings,
            sides,
            EngineClaim::Convertible,
            &twice
        ),
        KernelVerdict::Convertible,
        "the shared call runs once: a second unfold finds nothing to unfold"
    );
}

#[test]
fn an_endpoint_passes_over_a_bind_its_own_elimination_built()
{
    // `⟨pred ⟨pred x⟩ to n. return S(n)⟩` against `S(⟨pred ⟨pred x⟩⟩)`:
    // `spin(wind(Loop(x)))`'s arm in miniature. The outer `pred` meets the
    // returned endpoint at its gate and binds it, `pred x to y. pred y`;
    // read through, that bind's continuation meets the endpoint again and
    // binds it again, so the reading passes over it and reads the bind
    // out, over both, as `S` over the call.
    let mut arena = TermArena::new();
    let nat = arena.value_type_data(ConstantIndex::from(0_usize), Vec::new());
    let zero = arena.value_constructor(nat, ConstructorTag::from(0_usize), Vec::new());
    let motive = arena.comp_type_returner(nat);
    let on_zero = arena.computation_return(zero);
    let field = arena.value_variable(DeBruijnIndex::from(0_u32));
    let on_successor = arena.computation_return(field);
    let on_successor = arena.computation_lambda(on_successor);
    let cases = arena.computation_data_case(field, motive, alloc::vec![on_zero, on_successor]);
    let body = arena.computation_lambda(cases);
    let pred = arena.computation_fixpoint(body, FixpointEvidence::StructuralDescent);
    let stuck = arena.computation_application(pred, field);
    let inner = arena.value_returned(stuck);
    let outer = arena.computation_application(pred, inner);
    let successor = arena.value_constructor(nat, ConstructorTag::from(1_usize), alloc::vec![field]);
    let continuation = arena.computation_return(successor);
    let bound = arena.computation_bind(outer, continuation);
    let endpoint = arena.value_returned(bound);
    let call = arena.value_returned(outer);
    let expected = arena.value_constructor(nat, ConstructorTag::from(1_usize), alloc::vec![call]);

    assert_eq!(
        convert(
            &mut arena,
            &Unfoldings::default(),
            ReplaySides::Values(endpoint, expected),
            ReplayBudget::default()
        ),
        KernelVerdict::Convertible
    );
}

#[test]
fn an_endpoint_stays_over_the_eta_expansion_of_its_stuck_call_473()
{
    // `⟨f a⟩` against `⟨x ← f Z; force x⟩`, `f` opaque: one bind short, the
    // left takes the η-rule of `F` to `x ← f a; return x`. Read through,
    // that bind is `return ⟨f a⟩`, the goal reads it back as `f a` and
    // expands it again until the budget declines; staying over its call,
    // the two binds compare and the calls stand apart long before the
    // budget.
    let mut arena = TermArena::new();
    let nat = arena.value_type_data(ConstantIndex::from(1_usize), Vec::new());
    let zero = arena.value_constructor(nat, ConstructorTag::from(0_usize), Vec::new());
    let opaque = arena.value_constant(ConstantIndex::from(0_usize));
    let forced = arena.computation_force(opaque);
    let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
    let held = arena.computation_application(forced, variable);
    let at_zero = arena.computation_application(forced, zero);
    let bound = arena.value_variable(DeBruijnIndex::from(0_u32));
    let eliminated = arena.computation_force(bound);
    let right = arena.computation_bind(at_zero, eliminated);
    let left = arena.value_returned(held);
    let right = arena.value_returned(right);

    let verdict = convert(
        &mut arena,
        &Unfoldings::default(),
        ReplaySides::Values(left, right),
        ReplayBudget::default(),
    );
    assert_ne!(verdict, KernelVerdict::Declined(ReplayDecline::Budget));
    assert_ne!(verdict, KernelVerdict::Convertible);
}

#[test]
fn an_endpoint_stays_over_the_run_of_its_transported_operand_473()
{
    // `⟨tr(z. Path(N, Z, z), p, ⟨f Z⟩)⟩` against itself, `f` opaque and
    // `p` a variable: the operand runs first, `y ← f Z; tr(P↑, p↑, y)`.
    // Read through, that bind's continuation is the transport of the
    // returned call again, which runs it again until the budget
    // declines; staying over its call, the two sides are one bind each
    // and convert.
    let mut arena = TermArena::new();
    let nat = arena.value_type_data(ConstantIndex::from(1_usize), Vec::new());
    let zero = arena.value_constructor(nat, ConstructorTag::from(0_usize), Vec::new());
    let opaque = arena.value_constant(ConstantIndex::from(0_usize));
    let forced = arena.computation_force(opaque);
    let endpoint = arena.value_variable(DeBruijnIndex::from(0_u32));
    let family = arena.value_type_path(nat, zero, endpoint);
    let path = arena.value_variable(DeBruijnIndex::from(0_u32));
    let mut sides = [zero; 2];
    for side in &mut sides {
        let call = arena.computation_application(forced, zero);
        let operand = arena.value_returned(call);
        let transported = arena.computation_path_transport(family, path, operand);
        *side = arena.value_returned(transported);
    }
    let [left, right] = sides;

    assert_eq!(
        convert(
            &mut arena,
            &Unfoldings::default(),
            ReplaySides::Values(left, right),
            ReplayBudget::default()
        ),
        KernelVerdict::Convertible
    );
}

/// `el`, the decoder of one arrow code in miniature, as an admitted
/// definition at constant 0: `thunk (λu. force C u to x. force C u to y.
/// return ⌜El(x) → F El(y)⌝)`, the calls on `u` held at the opaque
/// constant 1 as the decoder's recursive calls are held on a binder.
///
/// # Specification
/// trivial.
fn decoder(arena: &mut TermArena) -> Unfoldings
{
    let opaque = arena.value_constant(ConstantIndex::from(1_usize));
    let forced = arena.computation_force(opaque);
    let code = arena.value_variable(DeBruijnIndex::from(0_u32));
    let first = arena.computation_application(forced, code);
    let code = arena.value_variable(DeBruijnIndex::from(1_u32));
    let second = arena.computation_application(forced, code);
    let x = arena.value_variable(DeBruijnIndex::from(1_u32));
    let y = arena.value_variable(DeBruijnIndex::from(0_u32));
    let quote = arrow_quote(arena, x, y);
    let returned = arena.computation_return(quote);
    let inner = arena.computation_bind(second, returned);
    let outer = arena.computation_bind(first, inner);
    let lambda = arena.computation_lambda(outer);
    let body = arena.value_thunk(lambda);
    Unfoldings::new(alloc::vec![Unfoldable::Body(body)])
}

/// `⌜El(x) → F El(y)⌝` over the two codes.
///
/// # Specification
/// trivial.
fn arrow_quote(
    arena: &mut TermArena,
    x: gandr_kernel_term::ValueId,
    y: gandr_kernel_term::ValueId,
) -> gandr_kernel_term::ValueId
{
    let domain = arena.value_type_element(x, Level::zero());
    let codomain = arena.value_type_element(y, Level::zero());
    let returner = arena.comp_type_returner(codomain);
    let arrow = arena.comp_type_arrow(domain, returner);
    let thunk = arena.value_type_thunk(arrow);
    arena.value_quote(thunk)
}

#[test]
fn a_decode_reads_as_the_quote_its_code_returns()
{
    // `⟨el v⟩` for a free `v` reads through the decoder's two binds, the
    // second a continuation stuck at a bind of its own, to the quote over
    // the calls they hold: `⌜El(⟨C v⟩) → F El(⟨C v⟩)⌝`. A quote of anything
    // else is refused by name, and a decode set aside against a type is
    // read the same way.
    let mut arena = TermArena::new();
    let unfoldings = decoder(&mut arena);
    let el = arena.value_constant(ConstantIndex::from(0_usize));
    let el = arena.computation_force(el);
    let v = arena.value_variable(DeBruijnIndex::from(0_u32));
    let decode = arena.computation_application(el, v);
    let decode = arena.value_returned(decode);
    let opaque = arena.value_constant(ConstantIndex::from(1_usize));
    let opaque = arena.computation_force(opaque);
    let held = arena.computation_application(opaque, v);
    let held = arena.value_returned(held);
    let quote = arrow_quote(&mut arena, held, held);
    let Some(&gandr_kernel_term::Value::Quote(decoded)) = arena.value(quote)
    else {
        panic!("an arrow quote is a quote");
    };
    let unit = arena.value_type_unit();
    let forged = arena.value_quote(unit);
    let watermark = arena.watermark();

    assert_eq!(
        super::read_step(
            &mut arena,
            &unfoldings,
            decode,
            quote,
            ReplayBudget::DEFAULT
        ),
        KernelVerdict::Convertible
    );
    assert_eq!(
        super::read_step(
            &mut arena,
            &unfoldings,
            decode,
            forged,
            ReplayBudget::DEFAULT
        ),
        KernelVerdict::Declined(ReplayDecline::Refused(ReplayRefusal::Contradicted {
            at: TracePosition::default(),
        }))
    );
    assert_eq!(
        super::read_step(
            &mut arena,
            &Unfoldings::default(),
            decode,
            quote,
            ReplayBudget::DEFAULT
        ),
        KernelVerdict::Declined(ReplayDecline::Refused(ReplayRefusal::Contradicted {
            at: TracePosition::default(),
        })),
        "with `el` not admitted, the decode stays its call"
    );
    for (other, reading) in [
        (decoded, super::EndpointReading::Converts),
        (unit, super::EndpointReading::Apart),
    ] {
        assert_eq!(
            super::read_endpoints(
                &mut arena,
                &unfoldings,
                &[crate::conv::SetAside::Decoded {
                    code: decode,
                    other
                }],
                ReplayBudget::DEFAULT,
                super::StuckEndpoints::Structural,
            ),
            reading
        );
    }
    assert_eq!(arena.watermark(), watermark);
}

#[test]
fn a_returned_leaf_of_a_presented_term_reads_before_the_rules()
{
    // `loop(⟨force wound⟩)`, `wound` defined as `thunk(return
    // unloop(base))`, is `base` over the presented circle: the leaf returns
    // `unloop(base)` and `loop(unloop(x))` rewrites to `x`. Over a free
    // circle the leaf is not read and the sides stay apart.
    let (base, looped, unlooped) = (
        ConstructorTag::from(0_usize),
        ConstructorTag::from(1_usize),
        ConstructorTag::from(2_usize),
    );
    let x = RuleNode::Variable(RuleVariable::from(0_u32));
    let rules = Presentation::new(alloc::vec![
        PresentedRule::new(
            [
                RuleNode::Constructor(looped),
                RuleNode::Constructor(unlooped),
                x
            ]
            .into(),
            [x].into(),
        ),
        PresentedRule::new(
            [
                RuleNode::Constructor(unlooped),
                RuleNode::Constructor(looped),
                x
            ]
            .into(),
            [x].into(),
        ),
    ]);
    let verdict = |presentation: Presentation| {
        let mut environment = Environment::new();
        let mut staging = environment.stage();
        let kind = staging
            .arena()
            .value_type_universe(GroundSort::Value, Level::zero());
        let own = staging
            .arena()
            .value_type_data(ConstantIndex::from(0_usize), Vec::new());
        let staged = staging
            .data(
                LevelSignature::monomorphic(),
                Vec::new(),
                alloc::vec![alloc::vec![], alloc::vec![own], alloc::vec![own]],
                kind,
            )
            .presented(presentation);
        let _circle = environment.add_decl(staged).expect("the circle admits");
        let mut arena = environment.arena().clone();
        let own = arena.value_type_data(ConstantIndex::from(0_usize), Vec::new());
        let at_base = arena.value_constructor(own, base, Vec::new());
        let back = arena.value_constructor(own, unlooped, alloc::vec![at_base]);
        let returns_back = arena.computation_return(back);
        let wound = arena.value_thunk(returns_back);
        let named = arena.value_constant(ConstantIndex::from(1_usize));
        let forced = arena.computation_force(named);
        let leaf = arena.value_returned(forced);
        let word = arena.value_constructor(own, looped, alloc::vec![leaf]);
        let unfoldings = Unfoldings::new(alloc::vec![Unfoldable::Opaque, Unfoldable::Body(wound)])
            .presenting(Presentations::of(environment.entries()));
        run(
            &mut arena,
            &unfoldings,
            ReplaySides::Values(word, at_base),
            EngineClaim::Convertible,
            &[SHARED],
        )
    };
    assert_eq!(verdict(rules), KernelVerdict::Convertible);
    assert_ne!(verdict(Presentation::default()), KernelVerdict::Convertible);
}

#[test]
fn a_compared_pair_reads_presented_points_by_their_rules_1723()
{
    // #1723: `here(loop(x))` and `here(loop(unloop(loop(x))))` over the
    // presented circle are one shared pair to the engine, their points one
    // normal form; the kernel closes the closing once the points set aside
    // are read by the rules, and not over a free circle, nor against
    // `here(unloop(x))`, whose point no rule relates to `loop(x)`.
    let (looped, unlooped) = (ConstructorTag::from(1_usize), ConstructorTag::from(2_usize));
    let x = RuleNode::Variable(RuleVariable::from(0_u32));
    let rules = Presentation::new(alloc::vec![
        PresentedRule::new(
            [
                RuleNode::Constructor(looped),
                RuleNode::Constructor(unlooped),
                x
            ]
            .into(),
            [x].into(),
        ),
        PresentedRule::new(
            [
                RuleNode::Constructor(unlooped),
                RuleNode::Constructor(looped),
                x
            ]
            .into(),
            [x].into(),
        ),
    ]);
    let verdict = |presentation: Presentation, peaked: bool| {
        let mut environment = Environment::new();
        let mut staging = environment.stage();
        let kind = staging
            .arena()
            .value_type_universe(GroundSort::Value, Level::zero());
        let own = staging
            .arena()
            .value_type_data(ConstantIndex::from(0_usize), Vec::new());
        let staged = staging
            .data(
                LevelSignature::monomorphic(),
                Vec::new(),
                alloc::vec![alloc::vec![], alloc::vec![own], alloc::vec![own]],
                kind,
            )
            .presented(presentation);
        let _circle = environment.add_decl(staged).expect("the circle admits");
        let mut arena = environment.arena().clone();
        let own = arena.value_type_data(ConstantIndex::from(0_usize), Vec::new());
        let point = arena.value_variable(DeBruijnIndex::from(0_u32));
        let word = arena.value_constructor(own, looped, alloc::vec![point]);
        let left = arena.value_here(word);
        let right = if peaked {
            let back = arena.value_constructor(own, unlooped, alloc::vec![word]);
            let peak = arena.value_constructor(own, looped, alloc::vec![back]);
            arena.value_here(peak)
        }
        else {
            let other = arena.value_constructor(own, unlooped, alloc::vec![point]);
            arena.value_here(other)
        };
        let unfoldings = Unfoldings::new(alloc::vec![Unfoldable::Opaque])
            .presenting(Presentations::of(environment.entries()));
        let mark = arena.watermark();
        let verdict = run(
            &mut arena,
            &unfoldings,
            ReplaySides::Values(left, right),
            EngineClaim::Convertible,
            &[SHARED],
        );
        assert_eq!(
            arena.watermark(),
            mark,
            "the reading mints nothing it keeps"
        );
        verdict
    };
    let apart = refused(ReplayRefusal::Contradicted {
        at: TracePosition::from(1),
    });
    assert_eq!(
        verdict(rules.clone(), true),
        KernelVerdict::Convertible,
        "the points read to one normal form"
    );
    assert_eq!(
        verdict(Presentation::default(), true),
        apart,
        "over a free circle the points stay apart"
    );
    assert_eq!(
        verdict(rules, false),
        apart,
        "and no rule relates loop(x) to unloop(x)"
    );
}

#[test]
fn a_cong_chain_composing_to_the_identity_replays_as_its_path()
{
    // `run q <- cong(inner, p); cong(outer, q)` against `return p`, read
    // engine-free as a respect obligation is: the rules δ-free, the two
    // functions `looped` (constant 1) and `unlooped` (constant 2) read
    // only by the chain's composite.
    let (base, looped, unlooped) = (
        ConstructorTag::from(0_usize),
        ConstructorTag::from(1_usize),
        ConstructorTag::from(2_usize),
    );
    let x = RuleNode::Variable(RuleVariable::from(0_u32));
    let rules = Presentation::new(alloc::vec![
        PresentedRule::new(
            [
                RuleNode::Constructor(looped),
                RuleNode::Constructor(unlooped),
                x
            ]
            .into(),
            [x].into(),
        ),
        PresentedRule::new(
            [
                RuleNode::Constructor(unlooped),
                RuleNode::Constructor(looped),
                x
            ]
            .into(),
            [x].into(),
        ),
    ]);
    let verdict = |presentation: Presentation,
                   inner: usize,
                   outer: usize,
                   against: bool,
                   (along_bound, at_here, left_fixed): (bool, bool, bool)| {
        let mut environment = Environment::new();
        let mut staging = environment.stage();
        let kind = staging
            .arena()
            .value_type_universe(GroundSort::Value, Level::zero());
        let own = staging
            .arena()
            .value_type_data(ConstantIndex::from(0_usize), Vec::new());
        let staged = staging
            .data(
                LevelSignature::monomorphic(),
                Vec::new(),
                alloc::vec![alloc::vec![], alloc::vec![own], alloc::vec![own]],
                kind,
            )
            .presented(presentation);
        let _circle = environment.add_decl(staged).expect("the circle admits");
        let mut arena = environment.arena().clone();
        let own = arena.value_type_data(ConstantIndex::from(0_usize), Vec::new());
        let letter = |arena: &mut TermArena, tag| {
            let occurrence = arena.value_variable(DeBruijnIndex::from(0_u32));
            let word = arena.value_constructor(own, tag, alloc::vec![occurrence]);
            let returned = arena.computation_return(word);
            let lambda = arena.computation_lambda(returned);
            arena.value_thunk(lambda)
        };
        let functions = [letter(&mut arena, looped), letter(&mut arena, unlooped)];
        let at_base = arena.value_constructor(own, base, Vec::new());
        let path = arena.value_variable(DeBruijnIndex::from(0_u32));
        let cong = |arena: &mut TermArena, function: usize, (along_bound, at_here, left_fixed)| {
            let named = arena.value_constant(ConstantIndex::from(function));
            let forced = arena.computation_force(named);
            let application = arena.computation_application(forced, path);
            let image = arena.value_returned(application);
            let left = if left_fixed { at_base } else { path };
            let motive = arena.value_type_path(own, left, image);
            let along = if along_bound {
                path
            }
            else {
                arena.value_variable(DeBruijnIndex::from(1_u32))
            };
            let reflexivity = if at_here {
                arena.value_here(at_base)
            }
            else {
                at_base
            };
            arena.computation_path_transport(motive, along, reflexivity)
        };
        let first = cong(&mut arena, inner, (true, true, left_fixed));
        let second = cong(&mut arena, outer, (along_bound, at_here, true));
        let chain = arena.computation_bind(first, second);
        let other = if against {
            arena.computation_return(path)
        }
        else {
            chain
        };
        let unfoldings = Unfoldings::new(alloc::vec![
            Unfoldable::Opaque,
            Unfoldable::Body(functions[0]),
            Unfoldable::Body(functions[1])
        ])
        .presenting(Presentations::of(environment.entries()));
        convert(
            &mut arena,
            &unfoldings,
            ReplaySides::Computations(chain, other),
            ReplayBudget::default(),
        )
    };
    let fused = (true, true, true);
    assert_eq!(
        verdict(rules.clone(), 2, 1, true, fused),
        KernelVerdict::Convertible,
        "`looped ∘ unlooped` is the identity under the rules, so the chain is its path"
    );
    for (unfused, what) in [
        (
            (false, true, true),
            "a continuation transporting along another path",
        ),
        (
            (true, false, true),
            "a continuation transporting another value than reflexivity",
        ),
        ((true, true, false), "a link whose left endpoint moves"),
    ] {
        assert_ne!(
            verdict(rules.clone(), 2, 1, true, unfused),
            KernelVerdict::Convertible,
            "{what} does not fuse"
        );
    }
    assert_ne!(
        verdict(rules, 1, 1, true, fused),
        KernelVerdict::Convertible,
        "a chain composing to `looped ∘ looped` is not its path"
    );
    assert_ne!(
        verdict(Presentation::default(), 2, 1, true, fused),
        KernelVerdict::Convertible,
        "over a free circle `loop(unloop(y))` is not `y`"
    );
    assert_eq!(
        verdict(Presentation::default(), 1, 1, false, fused),
        KernelVerdict::Convertible,
        "a chain that does not fuse is still itself, closed before its transport is read"
    );
}

#[test]
fn a_lazy_pairing_meets_a_neutral_by_its_projections()
{
    let mut arena = TermArena::new();
    let none = Unfoldings::default();
    let head = arena.value_variable(DeBruijnIndex::from(0));
    let neutral = arena.computation_force(head);
    let first = arena.computation_project(Component::from(0_usize), neutral);
    let second = arena.computation_project(Component::from(1_usize), neutral);
    let expanded = arena.computation_with(&[first, second]);
    let crossed = arena.computation_with(&[first, first]);
    let first_again = arena.computation_project(Component::from(0_usize), neutral);
    let second_again = arena.computation_project(Component::from(1_usize), neutral);
    let rebuilt = arena.computation_with(&[first_again, second_again]);
    let negative = |position| ConversionDecision::NegativeSubgoal {
        position: SubgoalPosition::from(position),
    };

    // The pairing of a neutral's projections is that neutral, on either
    // side, with no decision for the η step; two pairings compare
    // componentwise.
    for sides in [
        ReplaySides::Computations(expanded, neutral),
        ReplaySides::Computations(neutral, expanded),
        ReplaySides::Computations(expanded, rebuilt),
    ] {
        assert_eq!(
            run(&mut arena, &none, sides, EngineClaim::Convertible, &[]),
            KernelVerdict::Convertible
        );
    }

    // The arrow's decision is never read at the step, so it is left over;
    // a structural marker there is refused where it stands.
    let sides = ReplaySides::Computations(expanded, neutral);
    assert_eq!(
        run(&mut arena, &none, sides, EngineClaim::Convertible, &[
            ConversionDecision::EtaExpand {
                side: ConversionSide::Right,
                variable: ReplayNode::Other,
            }
        ]),
        refused(ReplayRefusal::Leftover {
            at: TracePosition::from(0),
        })
    );
    assert_eq!(
        run(&mut arena, &none, sides, EngineClaim::Convertible, &[
            ConversionDecision::Decompose
        ]),
        refused(ReplayRefusal::Inapplicable {
            at: TracePosition::from(0),
        })
    );

    // A pairing projecting the first component twice is refuted by its second
    // premise only, and only through the decision naming it.
    for sides in [
        ReplaySides::Computations(crossed, neutral),
        ReplaySides::Computations(neutral, crossed),
        ReplaySides::Computations(rebuilt, crossed),
    ] {
        assert_eq!(
            run(&mut arena, &none, sides, EngineClaim::NotConvertible, &[
                negative(1_u32)
            ]),
            KernelVerdict::NotConvertible
        );
        assert_eq!(
            run(&mut arena, &none, sides, EngineClaim::NotConvertible, &[
                negative(0_u32)
            ]),
            refused(ReplayRefusal::Contradicted {
                at: TracePosition::from(1),
            })
        );
        assert_eq!(
            run(&mut arena, &none, sides, EngineClaim::NotConvertible, &[]),
            refused(ReplayRefusal::Exhausted)
        );
        assert_eq!(
            run(&mut arena, &none, sides, EngineClaim::Convertible, &[]),
            refused(ReplayRefusal::Contradicted {
                at: TracePosition::from(0),
            })
        );
    }
}

/// A tuple of a neutral's own projections is that neutral, on either side, and
/// a record of its own fields likewise, with no decision for the η step; a
/// tuple projecting the second component first is refuted by its first
/// premise only, through the decision naming it (#715).
#[test]
fn a_tuple_meets_a_neutral_by_its_projections_715()
{
    use alloc::collections::BTreeMap;
    use alloc::string::String;

    use gandr_kernel_term::Component;
    use gandr_kernel_term::FieldLabel;
    let mut arena = TermArena::new();
    let none = Unfoldings::default();
    let neutral = arena.value_variable(DeBruijnIndex::from(0));
    let projected = |arena: &mut TermArena, position: usize| {
        let projection = arena.computation_tuple_projection(neutral, Component::from(position));
        arena.value_returned(projection)
    };
    let first = projected(&mut arena, 0_usize);
    let second = projected(&mut arena, 1_usize);
    let expanded = arena.value_tuple(&[first, second]);
    let swapped = arena.value_tuple(&[second, first]);
    let label = |name: &str| FieldLabel::from(String::from(name));
    let left = arena.computation_record_projection(neutral, label("l"));
    let left = arena.value_returned(left);
    let right = arena.computation_record_projection(neutral, label("r"));
    let right = arena.value_returned(right);
    let record = arena.value_record(BTreeMap::from([(label("l"), left), (label("r"), right)]));
    let negative = |position| ConversionDecision::NegativeSubgoal {
        position: SubgoalPosition::from(position),
    };

    for sides in [
        ReplaySides::Values(expanded, neutral),
        ReplaySides::Values(neutral, expanded),
        ReplaySides::Values(record, neutral),
        ReplaySides::Values(neutral, record),
    ] {
        assert_eq!(
            run(&mut arena, &none, sides, EngineClaim::Convertible, &[]),
            KernelVerdict::Convertible,
            "{sides:?}"
        );
    }

    for sides in [
        ReplaySides::Values(swapped, neutral),
        ReplaySides::Values(neutral, swapped),
    ] {
        assert_eq!(
            run(&mut arena, &none, sides, EngineClaim::NotConvertible, &[
                negative(0_u32)
            ]),
            KernelVerdict::NotConvertible,
            "{sides:?}"
        );
        assert_eq!(
            run(&mut arena, &none, sides, EngineClaim::Convertible, &[]),
            refused(ReplayRefusal::Contradicted {
                at: TracePosition::from(0),
            }),
            "{sides:?}"
        );
    }
}

#[test]
fn neutral_spines_keep_subgoal_order_and_reject_kind_mismatches()
{
    let mut arena = TermArena::new();
    let none = Unfoldings::default();
    let head = arena.value_variable(DeBruijnIndex::from(0));
    let different = arena.value_variable(DeBruijnIndex::from(1));
    let unit = arena.value_unit();
    let same_branch = arena.computation_return(unit);
    let differing_branch = arena.computation_return(different);
    let left_case = arena.computation_case(head, &[same_branch, same_branch]);
    let right_case = arena.computation_case(head, &[same_branch, differing_branch]);
    let left = arena.computation_application(left_case, unit);
    let right = arena.computation_application(right_case, unit);
    let negative = |position| ConversionDecision::NegativeSubgoal {
        position: SubgoalPosition::from(position),
    };
    let sides = ReplaySides::Computations(left, right);
    assert_eq!(
        run(&mut arena, &none, sides, EngineClaim::NotConvertible, &[
            negative(1_u32),
            negative(0_u32)
        ]),
        KernelVerdict::NotConvertible
    );
    assert_eq!(
        run(&mut arena, &none, sides, EngineClaim::NotConvertible, &[
            negative(0_u32),
            negative(0_u32)
        ]),
        refused(ReplayRefusal::Contradicted {
            at: TracePosition::from(2)
        })
    );
    assert_eq!(
        run(&mut arena, &none, sides, EngineClaim::NotConvertible, &[
            negative(2_u32)
        ]),
        refused(ReplayRefusal::Contradicted {
            at: TracePosition::from(1)
        })
    );
    assert_eq!(
        run(&mut arena, &none, sides, EngineClaim::NotConvertible, &[
            negative(3_u32)
        ]),
        refused(ReplayRefusal::Inapplicable {
            at: TracePosition::from(0)
        })
    );
    // An application against a bind that returns what it bound: the spines
    // differ in kind at one length. A bind that never read its value would be
    // dropped instead.
    let forced = arena.computation_force(head);
    let applied = arena.computation_application(forced, unit);
    let bound_value = arena.value_variable(DeBruijnIndex::from(0));
    let returned = arena.computation_return(bound_value);
    let bound = arena.computation_bind(forced, returned);
    for other in [forced, bound] {
        assert_eq!(
            run(
                &mut arena,
                &none,
                ReplaySides::Computations(applied, other),
                EngineClaim::NotConvertible,
                &[]
            ),
            KernelVerdict::NotConvertible
        );
    }
    assert_eq!(
        run(
            &mut arena,
            &none,
            ReplaySides::Values(head, head),
            EngineClaim::Convertible,
            &[]
        ),
        KernelVerdict::Convertible
    );
}

#[test]
fn reduced_heads_retain_application_and_bind_frames()
{
    let mut arena = TermArena::new();
    let none = Unfoldings::default();
    let unit = arena.value_unit();
    let ambient = arena.value_variable(DeBruijnIndex::from(0));
    let beneath_binder = arena.value_variable(DeBruijnIndex::from(1));
    let opened_head = arena.computation_force(ambient);
    let body = arena.computation_force(beneath_binder);
    let lambda = arena.computation_lambda(body);
    let redex = arena.computation_application(lambda, unit);
    let continuation = arena.computation_return(ambient);
    let applied_redex = arena.computation_application(redex, unit);
    let applied_normal = arena.computation_application(opened_head, unit);
    let bound_redex = arena.computation_bind(redex, continuation);
    let bound_normal = arena.computation_bind(opened_head, continuation);
    let mark = arena.watermark();
    for (left, right) in [(applied_redex, applied_normal), (bound_redex, bound_normal)] {
        assert_eq!(
            run(
                &mut arena,
                &none,
                ReplaySides::Computations(left, right),
                EngineClaim::Convertible,
                &[]
            ),
            KernelVerdict::Convertible
        );
        assert_eq!(arena.watermark(), mark);
    }
}

#[test]
fn engine_decline_and_zero_budget_do_not_read_the_trace()
{
    let mut arena = TermArena::new();
    let none = Unfoldings::default();
    let unit = arena.value_unit();
    for (claim, budget, expected, consumed) in [
        (
            EngineClaim::Declined,
            0_u64,
            KernelVerdict::Declined(ReplayDecline::EngineDeclined),
            0,
        ),
        (
            EngineClaim::Convertible,
            0,
            KernelVerdict::Declined(ReplayDecline::Budget),
            0,
        ),
        (EngineClaim::Convertible, 1, KernelVerdict::Convertible, 1),
        (
            EngineClaim::NotConvertible,
            1,
            refused(ReplayRefusal::Contradicted {
                at: TracePosition::from(1),
            }),
            1,
        ),
    ] {
        let observed = core::cell::Cell::new(0_u32);
        let trace =
            core::iter::once(SHARED).inspect(|_| observed.set(observed.get().saturating_add(1)));
        assert_eq!(
            replay(
                &mut arena,
                &none,
                ReplaySides::Values(unit, unit),
                claim,
                trace,
                ReplayBudget::from(budget)
            ),
            expected
        );
        assert_eq!(observed.get(), consumed);
    }
}

#[test]
fn a_ride_unfolds_its_flow_where_the_dialogue_names_it()
{
    let mut arena = TermArena::new();
    let unit_type = arena.value_type_unit();
    let code = arena.value_quote(unit_type);
    let stay = arena.value_stay(code);
    let unfoldings = Unfoldings::new(Vec::from([Unfoldable::Body(stay)]));
    let named = arena.value_constant(ConstantIndex::from(0_usize));
    let decoded = arena.value_variable(DeBruijnIndex::from(0_u32));
    let motive = arena.value_type_element(decoded, Level::zero());
    let unit = arena.value_unit();
    let rode = arena.computation_ride(motive, named, unit);
    let returned = arena.computation_return(unit);
    let sides = ReplaySides::Computations(rode, returned);
    let unfold = |reduce: fn(ReplayNode) -> ConversionDecision<ReplayNode>| {
        [
            ConversionDecision::Unfold {
                constant: ReplayNode::Other,
            },
            reduce(ReplayNode::Other),
        ]
    };
    let left = |redex| ConversionDecision::ReduceLeft { redex };
    let right = |redex| ConversionDecision::ReduceRight { redex };

    // The flow heads the ride: its side's unfolding reaches `stay`, and
    // the ride returns its value.
    assert_eq!(
        run(
            &mut arena,
            &unfoldings,
            sides,
            EngineClaim::Convertible,
            &unfold(left)
        ),
        KernelVerdict::Convertible
    );
    // Read on the other side, or not at all, the unfolding is refused.
    assert_eq!(
        run(
            &mut arena,
            &unfoldings,
            sides,
            EngineClaim::Convertible,
            &unfold(right)
        ),
        refused(ReplayRefusal::Inapplicable {
            at: TracePosition::from(1)
        })
    );
    assert_eq!(
        run(&mut arena, &unfoldings, sides, EngineClaim::Convertible, &[
        ]),
        refused(ReplayRefusal::Exhausted)
    );

    // Two rides along one neutral flow compare their motives, then their
    // values.
    let flow = arena.value_variable(DeBruijnIndex::from(0_u32));
    let injected = arena.value_injection(Side::Left.into(), unit);
    let one = arena.computation_ride(motive, flow, unit);
    let same = arena.computation_ride(motive, flow, unit);
    let apart = arena.computation_ride(motive, flow, injected);
    let negative = |position: u32| ConversionDecision::NegativeSubgoal {
        position: SubgoalPosition::from(position),
    };
    assert_eq!(
        run(
            &mut arena,
            &unfoldings,
            ReplaySides::Computations(one, same),
            EngineClaim::Convertible,
            &[]
        ),
        KernelVerdict::Convertible
    );
    let rides = ReplaySides::Computations(one, apart);
    assert_eq!(
        run(
            &mut arena,
            &unfoldings,
            rides,
            EngineClaim::NotConvertible,
            &[negative(1)]
        ),
        KernelVerdict::NotConvertible
    );
    assert_eq!(
        run(
            &mut arena,
            &unfoldings,
            rides,
            EngineClaim::NotConvertible,
            &[negative(0)]
        ),
        refused(ReplayRefusal::Contradicted {
            at: TracePosition::from(1)
        })
    );
}

#[test]
fn a_path_transport_unfolds_its_path_where_the_dialogue_names_it()
{
    // `tr(y. El(y), p, ())` along a defined `p = refl(⌜Unit⌝)`: the
    // transport stands on its path, so the trace's unfolding reaches the
    // reflexivity and the transport returns its value.
    let mut arena = TermArena::new();
    let unit_type = arena.value_type_unit();
    let code = arena.value_quote(unit_type);
    let reflexivity = arena.value_path_refl(code);
    let unfoldings = Unfoldings::new(Vec::from([Unfoldable::Body(reflexivity)]));
    let named = arena.value_constant(ConstantIndex::from(0_usize));
    let decoded = arena.value_variable(DeBruijnIndex::from(0_u32));
    let motive = arena.value_type_element(decoded, Level::zero());
    let unit = arena.value_unit();
    let moved = arena.computation_path_transport(motive, named, unit);
    let returned = arena.computation_return(unit);
    let sides = ReplaySides::Computations(moved, returned);
    let unfold = |reduce: fn(ReplayNode) -> ConversionDecision<ReplayNode>| {
        [
            ConversionDecision::Unfold {
                constant: ReplayNode::Other,
            },
            reduce(ReplayNode::Other),
        ]
    };
    let left = |redex| ConversionDecision::ReduceLeft { redex };
    let right = |redex| ConversionDecision::ReduceRight { redex };
    assert_eq!(
        run(
            &mut arena,
            &unfoldings,
            sides,
            EngineClaim::Convertible,
            &unfold(left)
        ),
        KernelVerdict::Convertible
    );
    // Read on the other side, or not at all, the unfolding is refused.
    assert_eq!(
        run(
            &mut arena,
            &unfoldings,
            sides,
            EngineClaim::Convertible,
            &unfold(right)
        ),
        refused(ReplayRefusal::Inapplicable {
            at: TracePosition::from(1)
        })
    );
    assert_eq!(
        run(&mut arena, &unfoldings, sides, EngineClaim::Convertible, &[
        ]),
        refused(ReplayRefusal::Exhausted)
    );
}

#[test]
fn a_held_path_runs_over_its_operand_as_it_was_3734()
{
    // `tr(y. Path(Unit, (), y), ⟨force g⟩, ⟨force d⟩)` against `return ⟨force
    // d⟩`, `g = thunk (return here(()))` and `d = thunk (force o)` definitions
    // and `o` opaque: `assoc(f, g, h) then ⟨whiskerRight(…)⟩` in miniature.
    // The append runs `d` through its definition to `o`, where it sticks, so
    // the operand stays `⟨force d⟩` and the transport stands on its held
    // path. The dialogue unfolds `g`, the transport along reflexivity
    // returns the operand as it was, and the two sides are one shared node.
    // Kept as the run left it, the operand is `⟨force o⟩`, and the shared
    // comparison the dialogue names finds the sides apart.
    let mut arena = TermArena::new();
    let unit_type = arena.value_type_unit();
    let unit = arena.value_unit();
    let reflexivity = arena.value_here(unit);
    let returned = arena.computation_return(reflexivity);
    let path_body = arena.value_thunk(returned);
    let opaque = arena.value_constant(ConstantIndex::from(2_usize));
    let forced = arena.computation_force(opaque);
    let operand_body = arena.value_thunk(forced);
    let unfoldings = Unfoldings::new(Vec::from([
        Unfoldable::Body(path_body),
        Unfoldable::Body(operand_body),
        Unfoldable::Opaque,
    ]));
    let path = arena.value_constant(ConstantIndex::from(0_usize));
    let path = arena.computation_force(path);
    let path = arena.value_returned(path);
    let operand = arena.value_constant(ConstantIndex::from(1_usize));
    let operand = arena.computation_force(operand);
    let operand = arena.value_returned(operand);
    let moving = arena.value_variable(DeBruijnIndex::from(0_u32));
    let motive = arena.value_type_path(unit_type, unit, moving);
    let moved = arena.computation_path_transport(motive, path, operand);
    let kept = arena.computation_return(operand);
    let sides = ReplaySides::Computations(moved, kept);
    assert_eq!(
        run(&mut arena, &unfoldings, sides, EngineClaim::Convertible, &[
            ConversionDecision::Unfold {
                constant: ReplayNode::Other,
            },
            ConversionDecision::ReduceLeft {
                redex: ReplayNode::Other,
            },
            SHARED,
        ]),
        KernelVerdict::Convertible,
        "a run stuck past a definition leaves the operand as it was"
    );
}

#[test]
fn two_stuck_path_transports_compare_by_motive_and_value()
{
    // `tr(y. Path(Unit, (), y), q, v)` over one variable path `q`, as
    // two definitions' composites `p then q` leave it: the motives,
    // minted apart, compare as codes, then the values.
    let mut arena = TermArena::new();
    let unfoldings = Unfoldings::new(Vec::new());
    let unit_type = arena.value_type_unit();
    let unit = arena.value_unit();
    let endpoint = arena.value_variable(DeBruijnIndex::from(0_u32));
    let one_motive = arena.value_type_path(unit_type, unit, endpoint);
    let other_motive = arena.value_type_path(unit_type, unit, endpoint);
    let path = arena.value_variable(DeBruijnIndex::from(0_u32));
    let injected = arena.value_injection(Side::Left.into(), unit);
    let one = arena.computation_path_transport(one_motive, path, unit);
    let same = arena.computation_path_transport(other_motive, path, unit);
    let apart = arena.computation_path_transport(other_motive, path, injected);
    assert_eq!(
        run(
            &mut arena,
            &unfoldings,
            ReplaySides::Computations(one, same),
            EngineClaim::Convertible,
            &[]
        ),
        KernelVerdict::Convertible,
        "two transports along one path whose premises agree are one"
    );
    let transports = ReplaySides::Computations(one, apart);
    let negative = |position: u32| ConversionDecision::NegativeSubgoal {
        position: SubgoalPosition::from(position),
    };
    assert_eq!(
        run(
            &mut arena,
            &unfoldings,
            transports,
            EngineClaim::NotConvertible,
            &[negative(1)]
        ),
        KernelVerdict::NotConvertible,
        "the values refute at the second premise"
    );
    assert_eq!(
        run(
            &mut arena,
            &unfoldings,
            transports,
            EngineClaim::NotConvertible,
            &[negative(0)]
        ),
        refused(ReplayRefusal::Contradicted {
            at: TracePosition::from(1)
        }),
        "the motives agree, so a refutation there is contradicted"
    );
}

#[test]
fn two_stuck_telescope_transports_compare_by_motive_start_over_and_value()
{
    // `transport((y : N, z : N) => Path(N, y, z), p, s, o, v)` along one
    // variable path `p`, as an associator by based path induction leaves
    // it: a family reading both entries keeps it stuck. The motives, minted
    // apart, compare as codes, then the starts, the paths over and the
    // values, in the order the engine's spines compare them.
    let mut arena = TermArena::new();
    let unfoldings = Unfoldings::new(Vec::new());
    let nat = arena.value_type_data(ConstantIndex::from(1_usize), Vec::new());
    let unit = arena.value_unit();
    let motive = |arena: &mut TermArena| {
        let outer = arena.value_variable(DeBruijnIndex::from(1_u32));
        let inner = arena.value_variable(DeBruijnIndex::from(0_u32));
        let family = arena.value_type_path(nat, outer, inner);
        let returner = arena.comp_type_returner(family);
        let second = arena.comp_type_pi(nat, returner);
        arena.comp_type_pi(nat, second)
    };
    let one_motive = motive(&mut arena);
    let other_motive = motive(&mut arena);
    let path = arena.value_variable(DeBruijnIndex::from(0_u32));
    let over = arena.value_here(unit);
    let injected = arena.value_injection(Side::Left.into(), unit);
    let one = arena.computation_telescope_transport(one_motive, path, unit, over, unit);
    let same = arena.computation_telescope_transport(other_motive, path, unit, over, unit);
    let apart = arena.computation_telescope_transport(other_motive, path, unit, over, injected);
    assert_eq!(
        run(
            &mut arena,
            &unfoldings,
            ReplaySides::Computations(one, same),
            EngineClaim::Convertible,
            &[]
        ),
        KernelVerdict::Convertible,
        "two telescope transports along one path whose premises agree are one"
    );
    let transports = ReplaySides::Computations(one, apart);
    let negative = |position: u32| ConversionDecision::NegativeSubgoal {
        position: SubgoalPosition::from(position),
    };
    assert_eq!(
        run(
            &mut arena,
            &unfoldings,
            transports,
            EngineClaim::NotConvertible,
            &[negative(3)]
        ),
        KernelVerdict::NotConvertible,
        "the values refute at the fourth premise"
    );
    assert_eq!(
        run(
            &mut arena,
            &unfoldings,
            transports,
            EngineClaim::NotConvertible,
            &[negative(1)]
        ),
        refused(ReplayRefusal::Contradicted {
            at: TracePosition::from(1)
        }),
        "the starts agree, so a refutation there is contradicted"
    );
}

/// The forced loop compares a former's children, or an elimination
/// spine's, only where its own shape agrees: labels, literals, levels,
/// branch counts, components.
#[test]
fn the_forced_loop_compares_children_only_where_the_shapes_agree()
{
    use alloc::collections::BTreeMap;
    use alloc::string::String;

    use gandr_kernel_strata::LevelConstant;
    use gandr_kernel_term::Component;
    use gandr_kernel_term::FieldLabel;
    use gandr_kernel_term::Literal;
    use gandr_kernel_term::StringLiteral;

    let mut arena = TermArena::new();
    let label = |name: &str| FieldLabel::from(String::from(name));
    let unit = arena.value_unit();
    let unit_type = arena.value_type_unit();
    let returner = arena.comp_type_returner(unit_type);
    let returned = arena.computation_return(unit);
    let neutral = arena.value_variable(DeBruijnIndex::from(0_u32));
    let record = |arena: &mut TermArena, name: &str| {
        arena.value_record(BTreeMap::from([(label(name), unit)]))
    };
    let text = |arena: &mut TermArena, text: &str| {
        arena.value_literal(Literal::Text(StringLiteral::new(String::from(text))))
    };
    let lift = |arena: &mut TermArena, at: u64| {
        arena.value_lift(Level::constant(LevelConstant::from(at)), unit)
    };
    let data_case = |arena: &mut TermArena, count: usize| {
        arena.computation_data_case(neutral, returner, alloc::vec![returned; count])
    };
    let by_label = |arena: &mut TermArena, name: &str| {
        arena.computation_record_projection(neutral, label(name))
    };
    let by_component = |arena: &mut TermArena, component: usize| {
        arena.computation_tuple_projection(neutral, Component::from(component))
    };
    let values = [
        (
            record(&mut arena, "a"),
            record(&mut arena, "b"),
            record(&mut arena, "a"),
            "records",
        ),
        (
            text(&mut arena, "a"),
            text(&mut arena, "b"),
            text(&mut arena, "a"),
            "literals",
        ),
        (
            lift(&mut arena, 0),
            lift(&mut arena, 1),
            lift(&mut arena, 0),
            "lifts",
        ),
    ]
    .map(|(left, apart, twin, what)| {
        (
            ReplaySides::Values(left, apart),
            ReplaySides::Values(left, twin),
            what,
        )
    });
    let spines = [
        (
            data_case(&mut arena, 1),
            data_case(&mut arena, 2),
            data_case(&mut arena, 1),
            "data cases",
        ),
        (
            by_label(&mut arena, "a"),
            by_label(&mut arena, "b"),
            by_label(&mut arena, "a"),
            "record projections",
        ),
        (
            by_component(&mut arena, 0),
            by_component(&mut arena, 1),
            by_component(&mut arena, 0),
            "tuple projections",
        ),
    ]
    .map(|(left, apart, twin, what)| {
        (
            ReplaySides::Computations(left, apart),
            ReplaySides::Computations(left, twin),
            what,
        )
    });
    for (apart, twin, what) in values.into_iter().chain(spines) {
        let none = Unfoldings::default();
        assert_ne!(
            convert(&mut arena, &none, apart, ReplayBudget::DEFAULT),
            KernelVerdict::Convertible,
            "{what} of another shape are apart"
        );
        assert_eq!(
            convert(&mut arena, &none, twin, ReplayBudget::DEFAULT),
            KernelVerdict::Convertible,
            "{what} of one shape convert"
        );
    }
}

/// A bind rule reassociates or η-expands only between one head that no
/// δ-rule moves.
#[test]
fn a_bind_rule_rewrites_only_under_one_settled_head()
{
    use super::BindRule;
    use super::Elimination;
    use super::Head;
    use super::Shape;
    use super::Status;
    use super::bind_rule;

    let mut arena = TermArena::new();
    let unit = arena.value_unit();
    let continuation = arena.computation_return(unit);
    let stacked = alloc::vec![
        Elimination::Bind(continuation),
        Elimination::Bind(continuation),
    ];
    let neutral = |head, spine: &[Elimination]| Shape::Neutral(head, spine.to_vec());
    let variable = |index: u32| Head::Variable(DeBruijnIndex::from(index));
    let constant = |status| Head::Constant(ConstantIndex::from(0_usize), status);
    assert_eq!(
        bind_rule(&neutral(variable(0), &stacked), &neutral(variable(0), &[])),
        BindRule::Reassociate(ConversionSide::Left)
    );
    assert_eq!(
        bind_rule(
            &neutral(constant(Status::Opaque), &stacked),
            &neutral(constant(Status::Opaque), &[])
        ),
        BindRule::Reassociate(ConversionSide::Left)
    );
    for (left, right, what) in [
        (variable(0), variable(1), "two heads"),
        (
            constant(Status::Defined),
            constant(Status::Defined),
            "a δ-rule's head",
        ),
    ] {
        assert_eq!(
            bind_rule(&neutral(left, &stacked), &neutral(right, &[])),
            BindRule::Normal,
            "{what}"
        );
    }
}

/// A refutation reaching a term of a presented type, on either side, is
/// not authoritative; over a free type it is.
#[test]
fn a_refutation_at_a_presented_term_is_not_authoritative()
{
    let (base, looped) = (ConstructorTag::from(0_usize), ConstructorTag::from(1_usize));
    let x = RuleNode::Variable(RuleVariable::from(0_u32));
    let rules = Presentation::new(alloc::vec![PresentedRule::new(
        [
            RuleNode::Constructor(looped),
            RuleNode::Constructor(looped),
            x
        ]
        .into(),
        [x].into(),
    )]);
    let verdicts = |presentation: Presentation| {
        let mut environment = Environment::new();
        let mut staging = environment.stage();
        let kind = staging
            .arena()
            .value_type_universe(GroundSort::Value, Level::zero());
        let own = staging
            .arena()
            .value_type_data(ConstantIndex::from(0_usize), Vec::new());
        let staged = staging
            .data(
                LevelSignature::monomorphic(),
                Vec::new(),
                alloc::vec![alloc::vec![], alloc::vec![own]],
                kind,
            )
            .presented(presentation);
        let _sort = environment.add_decl(staged).expect("the sort admits");
        let mut arena = environment.arena().clone();
        let own = arena.value_type_data(ConstantIndex::from(0_usize), Vec::new());
        let at_base = arena.value_constructor(own, base, Vec::new());
        let word = arena.value_constructor(own, looped, alloc::vec![at_base]);
        let unit = arena.value_unit();
        let unfoldings = Unfoldings::new(alloc::vec![Unfoldable::Opaque])
            .presenting(Presentations::of(environment.entries()));
        [
            ReplaySides::Values(word, at_base),
            ReplaySides::Values(at_base, word),
            ReplaySides::Values(word, unit),
            ReplaySides::Values(unit, word),
        ]
        .map(|sides| {
            run(
                &mut arena,
                &unfoldings,
                sides,
                EngineClaim::NotConvertible,
                &[],
            )
        })
    };
    let not_authoritative = refused(ReplayRefusal::NonAuthoritative {
        at: TracePosition::from(0),
    });
    assert_eq!(verdicts(rules), [not_authoritative; 4]);
    assert_eq!(
        verdicts(Presentation::default()),
        [KernelVerdict::NotConvertible; 4]
    );
}

/// A λ, a lazy pairing or a return under an elimination it cannot take is
/// unreadable, never a top-level shape.
#[test]
fn an_introduction_under_a_spine_is_unreadable()
{
    type Stuck = fn(&mut TermArena) -> gandr_kernel_term::ComputationId;
    let bound_lambda: Stuck = |arena| {
        let unit = arena.value_unit();
        let returned = arena.computation_return(unit);
        let lambda = arena.computation_lambda(returned);
        arena.computation_bind(lambda, returned)
    };
    let bound_pairing: Stuck = |arena| {
        let unit = arena.value_unit();
        let returned = arena.computation_return(unit);
        let with = arena.computation_with(&[returned, returned]);
        arena.computation_bind(with, returned)
    };
    let applied_return: Stuck = |arena| {
        let unit = arena.value_unit();
        let returned = arena.computation_return(unit);
        arena.computation_application(returned, unit)
    };
    let mut arena = TermArena::new();
    for (stuck, what) in [
        (bound_lambda, "a bound λ"),
        (bound_pairing, "a bound pairing"),
        (applied_return, "an applied return"),
    ] {
        let left = stuck(&mut arena);
        let right = stuck(&mut arena);
        assert_eq!(
            convert(
                &mut arena,
                &Unfoldings::default(),
                ReplaySides::Computations(left, right),
                ReplayBudget::DEFAULT
            ),
            refused(ReplayRefusal::Unreadable),
            "{what}"
        );
    }
}

/// An endpoint's continuation is spent only once it returns with nothing
/// left to take: a return still applied keeps its application.
#[test]
fn an_endpoint_continuation_is_spent_only_with_its_frames()
{
    let mut arena = TermArena::new();
    let unit = arena.value_unit();
    let call = |arena: &mut TermArena| {
        let opaque = arena.value_constant(ConstantIndex::from(0_usize));
        let forced = arena.computation_force(opaque);
        let x = arena.value_variable(DeBruijnIndex::from(0_u32));
        arena.computation_application(forced, x)
    };
    let y = arena.value_variable(DeBruijnIndex::from(0_u32));
    let returns_y = arena.computation_return(y);
    let applied = arena.computation_application(returns_y, unit);
    let first = call(&mut arena);
    let kept = arena.computation_bind(first, applied);
    let kept = arena.value_returned(kept);
    let second = call(&mut arena);
    let spent = arena.computation_bind(second, returns_y);
    let spent = arena.value_returned(spent);
    assert_ne!(
        convert(
            &mut arena,
            &Unfoldings::new(alloc::vec![Unfoldable::Opaque]),
            ReplaySides::Values(kept, spent),
            ReplayBudget::DEFAULT
        ),
        KernelVerdict::Convertible
    );
}

/// A returned endpoint that reduces and then sticks reads as what it
/// reduced to.
#[test]
fn a_stuck_endpoint_reads_as_what_it_reduced_to()
{
    let mut arena = TermArena::new();
    let x = arena.value_variable(DeBruijnIndex::from(0_u32));
    let stuck = |arena: &mut TermArena| {
        let opaque = arena.value_constant(ConstantIndex::from(0_usize));
        let forced = arena.computation_force(opaque);
        arena.computation_application(forced, x)
    };
    let body = stuck(&mut arena);
    let lambda = arena.computation_lambda(body);
    let redex = arena.computation_application(lambda, x);
    let redex = arena.value_returned(redex);
    let call = stuck(&mut arena);
    let call = arena.value_returned(call);
    assert_eq!(
        super::read_endpoints(
            &mut arena,
            &Unfoldings::new(alloc::vec![Unfoldable::Opaque]),
            &[crate::conv::SetAside::Values(redex, call)],
            ReplayBudget::DEFAULT,
            super::StuckEndpoints::Structural,
        ),
        super::EndpointReading::Converts
    );
}

/// Two endpoints stuck at a transport along a variable path read alike when
/// the endpoints they transport do: one through a definition's δ-step, one
/// through a β-redex (#698). A transported endpoint that reads to another
/// call keeps the pair apart.
#[test]
fn endpoints_a_stuck_endpoint_carries_are_read_in_turn_698()
{
    let mut arena = TermArena::new();
    let path = arena.value_variable(DeBruijnIndex::from(1_u32));
    let y = arena.value_variable(DeBruijnIndex::from(0_u32));
    // `h(y)` for the opaque `h`, constant 0, or `k`, constant 2.
    let call = |arena: &mut TermArena, constant: usize, argument| {
        let head = arena.value_constant(ConstantIndex::from(constant));
        let forced = arena.computation_force(head);
        arena.computation_application(forced, argument)
    };
    // `g`, constant 1, is `thunk { λz. h(z) }`.
    let bound = arena.value_variable(DeBruijnIndex::from(0_u32));
    let body = call(&mut arena, 0, bound);
    let lambda = arena.computation_lambda(body);
    let defined = arena.value_thunk(lambda);
    let unfoldings = Unfoldings::new(alloc::vec![
        Unfoldable::Opaque,
        Unfoldable::Body(defined),
        Unfoldable::Opaque,
    ]);
    let transported = |arena: &mut TermArena, carried| {
        let carried = arena.value_returned(carried);
        let transport = arena.computation_transport(path, carried);
        arena.value_returned(transport)
    };
    let through_definition = call(&mut arena, 1, y);
    let through_definition = transported(&mut arena, through_definition);
    let redex = arena.computation_application(lambda, y);
    let through_redex = transported(&mut arena, redex);
    let elsewhere = call(&mut arena, 2, y);
    let elsewhere = transported(&mut arena, elsewhere);
    let read = |arena: &mut TermArena, left, right| {
        super::read_endpoints(
            arena,
            &unfoldings,
            &[crate::conv::SetAside::Values(left, right)],
            ReplayBudget::DEFAULT,
            super::StuckEndpoints::Structural,
        )
    };
    assert_eq!(
        read(&mut arena, through_definition, through_redex),
        super::EndpointReading::Converts,
        "the transported endpoints read alike"
    );
    assert_eq!(
        read(&mut arena, through_definition, elsewhere),
        super::EndpointReading::Apart,
        "a transported endpoint reading to another call stays apart"
    );
}

/// A step's own reading converts two endpoints stuck on a variable whose arms
/// differ by a definition one side holds and the other runs, and the
/// structural reading a relation takes keeps them apart (#2831). An arm
/// calling another definition stays apart either way.
#[test]
fn a_step_reads_a_call_a_stuck_arm_holds_by_its_unfolding_2831()
{
    let mut arena = TermArena::new();
    // `f(a)` for the constant `f` at `constant`.
    let call = |arena: &mut TermArena, constant: usize, argument| {
        let head = arena.value_constant(ConstantIndex::from(constant));
        let forced = arena.computation_force(head);
        arena.computation_application(forced, argument)
    };
    // `g`, constant 1, is `thunk { λz. h(z) }` for the opaque `h`, constant 0,
    // and `k`, constant 2, is opaque.
    let bound = arena.value_variable(DeBruijnIndex::from(0_u32));
    let body = call(&mut arena, 0, bound);
    let lambda = arena.computation_lambda(body);
    let defined = arena.value_thunk(lambda);
    let unfoldings = Unfoldings::new(alloc::vec![
        Unfoldable::Opaque,
        Unfoldable::Body(defined),
        Unfoldable::Opaque,
    ]);
    // `returned(case x { _ => f(y) ; _ => return () })`, stuck on `x`.
    let stuck = |arena: &mut TermArena, constant: usize| {
        let x = arena.value_variable(DeBruijnIndex::from(0_u32));
        let y = arena.value_variable(DeBruijnIndex::from(1_u32));
        let arm = call(arena, constant, y);
        let unit = arena.value_unit();
        let other = arena.computation_return(unit);
        let cased = arena.computation_case(x, &[arm, other]);
        arena.value_returned(cased)
    };
    let held = stuck(&mut arena, 1);
    let run = stuck(&mut arena, 0);
    let elsewhere = stuck(&mut arena, 2);
    let read = |arena: &mut TermArena, left, right, reading| {
        super::read_endpoints(
            arena,
            &unfoldings,
            &[crate::conv::SetAside::Values(left, right)],
            ReplayBudget::DEFAULT,
            reading,
        )
    };
    assert_eq!(
        read(&mut arena, held, run, super::StuckEndpoints::Unfolding),
        super::EndpointReading::Converts,
        "the held call reads as the call it runs to"
    );
    assert_eq!(
        read(&mut arena, held, run, super::StuckEndpoints::Structural),
        super::EndpointReading::Apart,
        "a relation's reading compares the stuck endpoints by structure"
    );
    assert_eq!(
        read(
            &mut arena,
            held,
            elsewhere,
            super::StuckEndpoints::Unfolding
        ),
        super::EndpointReading::Apart,
        "a call reading to another definition stays apart"
    );
}

/// A definition whose parameters stand ahead of its fixpoint reads its own
/// call under a binder as the call its source wrote, its parameters applied
/// outermost first (#3733). `c`, constant 1, is `thunk { λd. λe. fix f. λn.
/// case n { Z ⇒ return (d, e); S(m) ⇒ return thunk { λz. f(m) } } }` over
/// the naturals at constant 0. A step's own reading runs `c(d, e, S(m))` to
/// the thunk over `c(d, e, m)`, and that thunk stays apart from the one over
/// `c(e, d, m)`.
#[test]
fn a_recursion_under_its_parameters_reads_as_its_call_3733()
{
    let mut arena = TermArena::new();
    let nat = arena.value_type_data(ConstantIndex::from(0_usize), Vec::new());
    let unit_type = arena.value_type_unit();
    let motive = arena.comp_type_returner(unit_type);
    // Under `n`, `f`, `e` and `d`: `d` is 3 and `e` is 2.
    let d = arena.value_variable(DeBruijnIndex::from(3_u32));
    let e = arena.value_variable(DeBruijnIndex::from(2_u32));
    let parameters = arena.value_tuple(&[d, e]);
    let on_zero = arena.computation_return(parameters);
    // Under `z`, `m`, `n`, `f`, `e` and `d`: `f` is 3 and `m` is 1.
    let recursive = arena.value_variable(DeBruijnIndex::from(3_u32));
    let forced = arena.computation_force(recursive);
    let m = arena.value_variable(DeBruijnIndex::from(1_u32));
    let recurse = arena.computation_application(forced, m);
    let under = arena.computation_lambda(recurse);
    let suspended = arena.value_thunk(under);
    let on_successor = arena.computation_return(suspended);
    let on_successor = arena.computation_lambda(on_successor);
    let n = arena.value_variable(DeBruijnIndex::from(0_u32));
    let cases = arena.computation_data_case(n, motive, alloc::vec![on_zero, on_successor]);
    let body = arena.computation_lambda(cases);
    let fixpoint = arena.computation_fixpoint(body, FixpointEvidence::StructuralDescent);
    let under_e = arena.computation_lambda(fixpoint);
    let under_d = arena.computation_lambda(under_e);
    let defined = arena.value_thunk(under_d);
    let unfoldings = Unfoldings::new(alloc::vec![Unfoldable::Opaque, Unfoldable::Body(defined)]);
    // `c(x, y, w)` for the variables at `x`, `y` and `w`.
    let call = |arena: &mut TermArena, [x, y]: [u32; 2], w: ValueId| {
        let head = arena.value_constant(ConstantIndex::from(1_usize));
        let mut called = arena.computation_force(head);
        for index in [x, y] {
            let parameter = arena.value_variable(DeBruijnIndex::from(index));
            called = arena.computation_application(called, parameter);
        }
        arena.computation_application(called, w)
    };
    // `⟨c(d, e, S(m))⟩` for the free `d` 2, `e` 1 and `m` 0.
    let m = arena.value_variable(DeBruijnIndex::from(0_u32));
    let successor = arena.value_constructor(nat, ConstructorTag::from(1_usize), alloc::vec![m]);
    let run = call(&mut arena, [2, 1], successor);
    let run = arena.value_returned(run);
    // `thunk { λz. c(x, y, m) }`, the free variables one binder deeper.
    let refolded = |arena: &mut TermArena, parameters: [u32; 2]| {
        let m = arena.value_variable(DeBruijnIndex::from(1_u32));
        let called = call(arena, parameters, m);
        let under = arena.computation_lambda(called);
        arena.value_thunk(under)
    };
    let written = refolded(&mut arena, [3, 2]);
    let swapped = refolded(&mut arena, [2, 3]);

    assert_eq!(
        super::read_step(&mut arena, &unfoldings, run, written, ReplayBudget::DEFAULT),
        KernelVerdict::Convertible,
        "the recursion reads as the call `c(d, e, m)` its source wrote"
    );
    assert_eq!(
        super::read_step(&mut arena, &unfoldings, run, swapped, ReplayBudget::DEFAULT),
        KernelVerdict::Declined(ReplayDecline::Refused(ReplayRefusal::Contradicted {
            at: TracePosition::default(),
        })),
        "the parameters apply outermost first"
    );
}

/// A step's own reading converts two endpoints stuck on a variable whose arms
/// differ by a definition one side holds and the other runs, when what it
/// runs to is a record type over a call: the held arm's δ-step returns
/// `⌜{ok : El(⟨e(inj₀ ())⟩), v : 1}⌝` and the run arm `⌜{ok : 1, v : 1}⌝`,
/// the inner call run too, and the two codes read alike once the decode is
/// read. A run arm whose decode reads to another type stays apart. The
/// kernel's conversion with definitions unfolding relates the held call and
/// the run arm alone the same way.
#[test]
fn a_step_reads_a_record_code_a_stuck_arm_returns_3045()
{
    use alloc::collections::BTreeMap;
    use alloc::string::String;

    use gandr_kernel_term::FieldLabel;

    let mut arena = TermArena::new();
    // `f(a)` for the constant `f` at `constant`.
    let call = |arena: &mut TermArena, constant: usize, argument| {
        let head = arena.value_constant(ConstantIndex::from(constant));
        let forced = arena.computation_force(head);
        arena.computation_application(forced, argument)
    };
    let unit = arena.value_unit();
    let unit_type = arena.value_type_unit();
    let integer = arena.value_type_base(BaseType::Integer);
    let returns_code = |arena: &mut TermArena, quoted| {
        let code = arena.value_quote(quoted);
        arena.computation_return(code)
    };
    // `e`, constant 0, is `thunk { λh. case h { _ => return ⌜1⌝ ; _ => return
    // ⌜Integer⌝ } }`.
    let h = arena.value_variable(DeBruijnIndex::from(0_u32));
    let to_unit = returns_code(&mut arena, unit_type);
    let to_integer = returns_code(&mut arena, integer);
    let picked = arena.computation_case(h, &[to_unit, to_integer]);
    let picked = arena.computation_lambda(picked);
    let e = arena.value_thunk(picked);
    // `{ok : ok, v : 1}`.
    let record = |arena: &mut TermArena, ok| {
        arena.value_type_record(BTreeMap::from([
            (FieldLabel::from(String::from("ok")), ok),
            (FieldLabel::from(String::from("v")), unit_type),
        ]))
    };
    // `inner`, constant 1, is `thunk { λh. return ⌜{ok : El(⟨e(h)⟩), v : 1}⌝ }`.
    let at_e = call(&mut arena, 0, h);
    let at_e = arena.value_returned(at_e);
    let owed = arena.value_type_element(at_e, Level::zero());
    let owed = record(&mut arena, owed);
    let returns_record = returns_code(&mut arena, owed);
    let inner = arena.computation_lambda(returns_record);
    let inner = arena.value_thunk(inner);
    let unfoldings = Unfoldings::new(alloc::vec![Unfoldable::Body(e), Unfoldable::Body(inner)]);
    // `returned(case x { _ => return ⌜1⌝ ; _ => arm })`, stuck on `x`.
    let stuck = |arena: &mut TermArena, arm| {
        let x = arena.value_variable(DeBruijnIndex::from(0_u32));
        let other = returns_code(arena, unit_type);
        let cased = arena.computation_case(x, &[other, arm]);
        arena.value_returned(cased)
    };
    let empty = arena.value_injection(Side::Left.into(), unit);
    let held_call = call(&mut arena, 1, empty);
    let held = stuck(&mut arena, held_call);
    let ran_record = record(&mut arena, unit_type);
    let ran_code = returns_code(&mut arena, ran_record);
    let ran = stuck(&mut arena, ran_code);
    let elsewhere_record = record(&mut arena, integer);
    let elsewhere_code = returns_code(&mut arena, elsewhere_record);
    let elsewhere = stuck(&mut arena, elsewhere_code);
    let read = |arena: &mut TermArena, left, right| {
        super::read_endpoints(
            arena,
            &unfoldings,
            &[crate::conv::SetAside::Values(left, right)],
            ReplayBudget::DEFAULT,
            super::StuckEndpoints::Unfolding,
        )
    };
    let unfold = |arena: &mut TermArena, right| {
        convert_unfolding(
            arena,
            &unfoldings,
            ReplaySides::Computations(held_call, right),
            ReplayBudget::DEFAULT,
        )
    };
    let mark = arena.watermark();
    assert_eq!(
        read(&mut arena, held, ran),
        super::EndpointReading::Converts,
        "the held call's record code reads as the record the checker ran"
    );
    assert_eq!(
        read(&mut arena, held, elsewhere),
        super::EndpointReading::Apart,
        "a decode reading to another type stays apart"
    );
    assert_eq!(
        unfold(&mut arena, ran_code),
        KernelVerdict::Convertible,
        "the conversion reads the record code it owes"
    );
    assert_eq!(
        unfold(&mut arena, elsewhere_code),
        KernelVerdict::Declined(ReplayDecline::Refused(ReplayRefusal::Unreadable)),
        "an owed code reading to another type declines"
    );
    assert_eq!(
        mark,
        arena.watermark(),
        "the reading mints nothing it keeps"
    );
}

/// Every elimination meeting a returned endpoint runs the endpoint and
/// eliminates what it returns.
#[test]
fn each_elimination_runs_the_returned_endpoint_it_meets()
{
    use alloc::collections::BTreeMap;
    use alloc::string::String;

    use gandr_kernel_term::Component;
    use gandr_kernel_term::FieldLabel;
    use gandr_kernel_term::Literal;
    use gandr_kernel_term::StringLiteral;

    let mut arena = TermArena::new();
    let unit = arena.value_unit();
    let unit_type = arena.value_type_unit();
    let x = arena.value_literal(Literal::Text(StringLiteral::new(String::from("x"))));
    let label = FieldLabel::from(String::from("l"));
    let returned = |arena: &mut TermArena, value| {
        let returns = arena.computation_return(value);
        arena.value_returned(returns)
    };
    let record = arena.value_record(BTreeMap::from([(label.clone(), unit)]));
    let record = returned(&mut arena, record);
    let pair = arena.value_tuple(&[unit, x]);
    let pair = returned(&mut arena, pair);
    let nil = arena.value_list_nil();
    let nil = returned(&mut arena, nil);
    let inner = arena.value_variable(DeBruijnIndex::from(0_u32));
    let returns_inner = arena.computation_return(inner);
    let returns_x = arena.computation_return(x);
    let returns_unit = arena.computation_return(unit);
    let motive = arena.comp_type_returner(unit_type);
    let cases = [
        (
            arena.computation_record_projection(record, label),
            returns_unit,
            "a record projection",
        ),
        (
            arena.computation_tuple_projection(pair, Component::from(1_usize)),
            returns_x,
            "a tuple projection",
        ),
        (
            arena.computation_sigma_split(pair, motive, returns_inner),
            returns_x,
            "a dependent split",
        ),
        (
            arena.computation_list_fold(unit_type, unit_type, nil, returns_x, returns_unit),
            returns_x,
            "a list fold",
        ),
    ];
    for (elimination, expected, what) in cases {
        assert_eq!(
            convert(
                &mut arena,
                &Unfoldings::default(),
                ReplaySides::Computations(elimination, expected),
                ReplayBudget::DEFAULT
            ),
            KernelVerdict::Convertible,
            "{what}"
        );
    }
}

/// An elimination meeting a returned endpoint reads the endpoint's
/// computation as an endpoint: a bind over a call stuck at a variable reads
/// through, so `π₀ ⟨h(x) to y. return ("a", y)⟩` is `"a"` and `π₁` of it is
/// the call itself.
#[test]
fn an_eliminated_endpoint_reads_a_bind_through_its_stuck_call()
{
    use alloc::string::String;

    use gandr_kernel_term::Component;
    use gandr_kernel_term::Literal;
    use gandr_kernel_term::StringLiteral;

    let mut arena = TermArena::new();
    let function = arena.value_variable(DeBruijnIndex::from(1_u32));
    let point = arena.value_variable(DeBruijnIndex::from(0_u32));
    let forced = arena.computation_force(function);
    let call = arena.computation_application(forced, point);
    let first = arena.value_literal(Literal::Text(StringLiteral::new(String::from("a"))));
    let bound = arena.value_variable(DeBruijnIndex::from(0_u32));
    let pair = arena.value_tuple(&[first, bound]);
    let returns_pair = arena.computation_return(pair);
    let binds = arena.computation_bind(call, returns_pair);
    let endpoint = arena.value_returned(binds);
    let returns_first = arena.computation_return(first);
    let projections = [
        (
            Component::from(0_usize),
            returns_first,
            "the first component",
        ),
        (Component::from(1_usize), call, "the call itself"),
    ];
    for (component, expected, what) in projections {
        let projection = arena.computation_tuple_projection(endpoint, component);
        assert_eq!(
            convert(
                &mut arena,
                &Unfoldings::default(),
                ReplaySides::Computations(projection, expected),
                ReplayBudget::DEFAULT
            ),
            KernelVerdict::Convertible,
            "{what}"
        );
    }
}

#[test]
fn a_forced_applied_endpoint_converts_with_a_bind_over_its_call_2326()
{
    // `⟨force k s to f. force f s⟩` against `⟨force ⟨force k s⟩ s⟩`, under
    // `k` (index 1) and `s` (index 0): `bound(k, s)` against `apply(k(s), s)`
    // unfolded. The forced endpoint runs as `force k s to x. force x s`, the
    // application moved under the binder with the force, so both sides are
    // binds over one call. Before, the application stayed outside the bind
    // and the two contradicted.
    let mut arena = TermArena::new();
    let k = arena.value_variable(DeBruijnIndex::from(1_u32));
    let s = arena.value_variable(DeBruijnIndex::from(0_u32));
    let forced = arena.computation_force(k);
    let call = arena.computation_application(forced, s);
    let bound = arena.value_variable(DeBruijnIndex::from(0_u32));
    let s_under = arena.value_variable(DeBruijnIndex::from(1_u32));
    let forced_bound = arena.computation_force(bound);
    let applied_bound = arena.computation_application(forced_bound, s_under);
    let binds = arena.computation_bind(call, applied_bound);
    let left = arena.value_returned(binds);
    let returned = arena.value_returned(call);
    let forced_returned = arena.computation_force(returned);
    let applied_returned = arena.computation_application(forced_returned, s);
    let right = arena.value_returned(applied_returned);
    assert_eq!(
        convert(
            &mut arena,
            &Unfoldings::default(),
            ReplaySides::Values(left, right),
            ReplayBudget::DEFAULT,
        ),
        KernelVerdict::Convertible,
        "the forced, applied endpoint is the bind over its call"
    );
}

/// What reducing a term came to: the weak head's content or the stop, and the
/// charges spent.
#[derive(Debug, PartialEq)]
struct Reduced
{
    /// The weak head's content, or why the reduction stopped.
    reached: Result<ContentDigest, super::Stop>,
    /// The charges spent.
    spent: u64,
}

/// What reducing `term` as `reduction` says, its environment unloaded as
/// `unloading` says, came to.
///
/// # Specification
/// trivial.
fn reduced(
    arena: &mut TermArena,
    term: ComputationId,
    reduction: super::Reduction,
    unloading: super::Unloading,
) -> Reduced
{
    let unfoldings = Unfoldings::default();
    let mut run = super::Replay {
        arena,
        unfoldings: &unfoldings,
        evaluator: &unfoldings,
        trace: core::iter::empty().peekable(),
        reading: super::Reading::Recorded,
        position: 0,
        spent: 0,
        budget: 384,
        table: crate::ContentTable::new(),
        memo: gandr_kernel_check_memo::NullMemo,
        owed: Vec::new(),
    };
    let reached = run
        .reduce(super::Term::Computation(term), reduction, unloading)
        .and_then(|reached| match reached {
            super::Term::Computation(head) => {
                Ok(content_digest(run.arena, AnyNode::Computation(head)))
            },
            super::Term::Value(_) => Err(super::Stop::Refused(ReplayRefusal::Unreadable)),
        });
    Reduced {
        reached,
        spent: run.spent,
    }
}

proptest::proptest! {
    #![proptest_config(proptest::prelude::ProptestConfig::with_cases(1024))]

    /// The environment reduction against the substituting one, which
    /// unloads after every step: over generated terms, each read plain and
    /// as an endpoint, the two reach weak heads of one content or stop alike,
    /// after the same charges.
    #[test]
    fn the_environment_reduction_agrees_with_the_substituting_one(program in program()) {
        for reduction in [super::Reduction::Plain, super::Reduction::Endpoint] {
            let mut arena = TermArena::new();
            let term = generated(&mut arena, &program);
            let at_the_head = reduced(&mut arena, term, reduction, super::Unloading::AtTheHead);
            let every_step = reduced(&mut arena, term, reduction, super::Unloading::EveryStep);
            proptest::prop_assert_eq!(at_the_head, every_step);
        }
    }
}

#[test]
fn a_chain_of_beta_steps_walks_its_reduct_once()
{
    /// `λ…λ. return (x₀, …, xₖ₋₁)` under `links` binders, applied to as many
    /// units, reduced as `unloading` says: the head's content, and a
    /// computation minted after it, whose position counts the computations
    /// the reduction minted.
    ///
    /// # Specification
    /// trivial.
    fn chain(unloading: super::Unloading) -> (Result<ContentDigest, super::Stop>, ComputationId)
    {
        let links = 24_u32;
        let mut arena = TermArena::new();
        let read: Vec<ValueId> = (0 .. links)
            .map(|index| arena.value_variable(DeBruijnIndex::from(index)))
            .collect();
        let tuple = arena.value_tuple(&read);
        let mut term = arena.computation_return(tuple);
        for _binder in 0 .. links {
            term = arena.computation_lambda(term);
        }
        for _argument in 0 .. links {
            let unit = arena.value_unit();
            term = arena.computation_application(term, unit);
        }
        let Reduced { reached: head, .. } =
            reduced(&mut arena, term, super::Reduction::Plain, unloading);
        let unit = arena.value_unit();
        (head, arena.computation_return(unit))
    }
    let (once, minted_once) = chain(super::Unloading::AtTheHead);
    let (every, minted_every) = chain(super::Unloading::EveryStep);
    assert_eq!(once, every, "both reach one weak head");
    assert!(
        minted_once < minted_every,
        "the head is walked once, where every step walks the reduct left"
    );
}
