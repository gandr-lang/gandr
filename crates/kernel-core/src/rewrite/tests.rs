//! Witnesses for the rewrite machines: shifts and substitutions, their
//! memo keys, and the rebuild each former makes only where a child changed.

use alloc::string::String;

use anodized::spec;
use gandr_kernel_check_memo::CheckMemo as _;
use gandr_kernel_check_memo::ContentAgreement;
use gandr_kernel_check_memo::MemoEntryCount;
use gandr_kernel_check_memo::MemoKey as _;
use gandr_kernel_check_memo::NullMemo;
use gandr_kernel_strata::Level;
use gandr_kernel_term::AnyNode;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::CompType;
use gandr_kernel_term::Computation;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::Literal;
use gandr_kernel_term::StringLiteral;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueId;
use gandr_kernel_term::ValueType;
use quenchant_arith::arith;

use super::BinderDepth;
use super::ContentTable;
use super::RewriteMemo;
use super::RewritePlane;
use super::RewriteSupport;
use super::shift_computation;
use super::shift_value;
use super::shift_value_type;
use super::substitute_comp_type;
use super::substitute_value;
use super::substitute_value_type;
use crate::encoding::RewriteGoal;
use crate::encoding::content_digest;

/// A fixture's chain length, as its own quantity rather than a bare count.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ChainLength(u32);

/// The de Bruijn index at `depth` binders out.
///
/// # Specification
/// trivial.
fn index(depth: BinderDepth) -> DeBruijnIndex
{
    DeBruijnIndex::from(u32::from(depth))
}

#[test]
fn a_zero_shift_reuses_its_code_carrying_subject()
{
    let mut arena = TermArena::new();
    let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
    let subject = arena.value_type_element(variable, Level::zero());
    let before = arena.watermark();
    let shifted = shift_value_type(
        &mut arena,
        &mut ContentTable::new(),
        &mut RewriteMemo::new(),
        subject,
        BinderDepth::NONE,
        BinderDepth::NONE,
    );
    assert_eq!(shifted, subject);
    assert_eq!(arena.watermark(), before);
}

#[test]
fn a_saturated_variable_shift_reuses_the_unchanged_occurrence()
{
    let mut arena = TermArena::new();
    let subject = arena.value_variable(DeBruijnIndex::from(u32::MAX));
    let before = arena.watermark();
    let shifted = shift_value(
        &mut arena,
        &mut ContentTable::new(),
        &mut RewriteMemo::new(),
        subject,
        BinderDepth::NONE,
        BinderDepth::from(1_u32),
    );
    assert_eq!(shifted, subject);
    assert_eq!(arena.watermark(), before);
}

#[test]
fn shifting_raises_free_indices_and_spares_bound_ones()
{
    let mut arena = TermArena::new();
    let free = arena.value_variable(index(BinderDepth::from(0_u32)));
    let mut table = ContentTable::new();
    let mut memo = RewriteMemo::new();
    let raised = shift_value(
        &mut arena,
        &mut table,
        &mut memo,
        free,
        BinderDepth::NONE,
        BinderDepth::from(2_u32),
    );
    assert_eq!(
        Some(&Value::Variable(index(BinderDepth::from(2_u32)))),
        arena.value(raised),
        "a free index at the cutoff rises by the amount"
    );
    let spared = shift_value(
        &mut arena,
        &mut table,
        &mut memo,
        free,
        BinderDepth::from(1_u32),
        BinderDepth::from(2_u32),
    );
    assert_eq!(
        free, spared,
        "an index below the cutoff is bound outside the rewrite and is returned unchanged"
    );
}

#[test]
fn an_abstraction_replaces_its_constant_by_a_variable_under_binders()
{
    let mut arena = TermArena::new();
    let decoder = gandr_kernel_term::ConstantIndex::from(1_usize);
    let other = gandr_kernel_term::ConstantIndex::from(2_usize);
    // `El(c x)`, `c` the constant and `x` the variable `at`.
    let decode = |arena: &mut TermArena, constant, at: u32| {
        let head = arena.value_constant(constant);
        let forced = arena.computation_force(head);
        let argument = arena.value_variable(DeBruijnIndex::from(at));
        let call = arena.computation_application(forced, argument);
        let code = arena.value_returned(call);
        arena.value_type_element(code, Level::zero())
    };
    // `U (El(el x) → F (El(el y)))`, the codomain under the arrow's binder.
    let domain = decode(&mut arena, decoder, 0);
    let codomain = decode(&mut arena, decoder, 1);
    let returner = arena.comp_type_returner(codomain);
    let pi = arena.comp_type_pi(domain, returner);
    let subject = arena.value_type_thunk(pi);
    let mut table = ContentTable::new();
    let mut memo = RewriteMemo::new();
    let read = super::abstract_constant_value_type(
        &mut arena,
        &mut table,
        &mut memo,
        subject,
        (decoder, DeBruijnIndex::from(5_u32)),
    );
    // The decoder's head and argument in `El(head argument)`.
    let call = |arena: &TermArena, decoded| {
        let Some(&ValueType::Element { code, .. }) = arena.value_type(decoded)
        else {
            panic!("a decode");
        };
        let Some(&Value::Returned(call)) = arena.value(code)
        else {
            panic!("a returned call");
        };
        let Some(&Computation::Application(forced, argument)) = arena.computation(call)
        else {
            panic!("an application");
        };
        let Some(&Computation::Force(head)) = arena.computation(forced)
        else {
            panic!("a forced head");
        };
        (arena.value(head).cloned(), arena.value(argument).cloned())
    };
    let variable = |at: u32| Some(Value::Variable(DeBruijnIndex::from(at)));
    let Some(&ValueType::Thunk(pi)) = arena.value_type(read)
    else {
        panic!("a thunk");
    };
    let Some(&CompType::Pi { domain, codomain }) = arena.comp_type(pi)
    else {
        panic!("an arrow");
    };
    let Some(&CompType::Returner(result)) = arena.comp_type(codomain)
    else {
        panic!("a returner");
    };
    // The domain stands under no binder: the variable at the index. The
    // codomain stands under the arrow's: one past it. The arguments stand.
    assert_eq!(call(&arena, domain), (variable(5), variable(0)));
    assert_eq!(call(&arena, result), (variable(6), variable(1)));
    let unrelated = decode(&mut arena, other, 0);
    // A fresh session: a memo may answer with an equal node minted earlier.
    assert_eq!(
        super::abstract_constant_value_type(
            &mut arena,
            &mut ContentTable::new(),
            &mut RewriteMemo::new(),
            unrelated,
            (decoder, DeBruijnIndex::from(5_u32)),
        ),
        unrelated,
        "a type naming another constant is kept"
    );
}

#[test]
fn a_binder_spares_what_it_binds()
{
    let mut arena = TermArena::new();
    let inner = arena.value_variable(index(BinderDepth::from(0_u32)));
    let outer = arena.value_variable(index(BinderDepth::from(1_u32)));
    let pair = arena.value_tuple(&[inner, outer]);
    let body = arena.computation_return(pair);
    let lambda = arena.computation_lambda(body);
    let mut table = ContentTable::new();
    let mut memo = RewriteMemo::new();
    let shifted = shift_computation(
        &mut arena,
        &mut table,
        &mut memo,
        lambda,
        BinderDepth::NONE,
        BinderDepth::from(3_u32),
    );
    let Some(&Computation::Lambda(shifted_body)) = arena.computation(shifted)
    else {
        panic!("a shifted lambda is a lambda");
    };
    let Some(&Computation::Return(shifted_pair)) = arena.computation(shifted_body)
    else {
        panic!("its body is a returner");
    };
    let Some(&[first, second]) = arena.value(shifted_pair).and_then(Value::components)
    else {
        panic!("and the returner carries the pair");
    };
    assert_eq!(
        Some(&Value::Variable(index(BinderDepth::from(0_u32)))),
        arena.value(first),
        "the lambda's own binder is spared"
    );
    assert_eq!(
        Some(&Value::Variable(index(BinderDepth::from(4_u32)))),
        arena.value(second),
        "and the index reaching past it rises by the amount"
    );
}

#[test]
fn substitution_replaces_lowers_and_spares()
{
    let mut arena = TermArena::new();
    let replacement = arena.value_literal(Literal::Text(StringLiteral::new(String::from("r"))));
    let bound_inside = arena.value_variable(index(BinderDepth::from(0_u32)));
    let substituted = arena.value_variable(index(BinderDepth::from(1_u32)));
    let outside = arena.value_variable(index(BinderDepth::from(2_u32)));
    let inner_pair = arena.value_tuple(&[bound_inside, substituted]);
    let pair = arena.value_tuple(&[inner_pair, outside]);
    let body = arena.computation_return(pair);
    let lambda = arena.computation_lambda(body);
    let thunk = arena.value_thunk(lambda);
    let mut table = ContentTable::new();
    let mut memo = RewriteMemo::new();
    let result = substitute_value(&mut arena, &mut table, &mut memo, thunk, replacement);

    let Some(&Value::Thunk(result_lambda)) = arena.value(result)
    else {
        panic!("a substituted thunk is a thunk");
    };
    let Some(&Computation::Lambda(result_body)) = arena.computation(result_lambda)
    else {
        panic!("holding a lambda");
    };
    let Some(&Computation::Return(result_pair)) = arena.computation(result_body)
    else {
        panic!("whose body returns");
    };
    let Some(&[result_inner, result_outside]) =
        arena.value(result_pair).and_then(Value::components)
    else {
        panic!("a pair");
    };
    let Some(&[result_bound, result_substituted]) =
        arena.value(result_inner).and_then(Value::components)
    else {
        panic!("over a pair");
    };
    assert_eq!(
        Some(&Value::Variable(index(BinderDepth::from(0_u32)))),
        arena.value(result_bound),
        "an index bound inside the walk stands"
    );
    assert_eq!(
        arena.value(replacement).cloned(),
        arena.value(result_substituted).cloned(),
        "the index the walk's depth names becomes the replacement"
    );
    assert_eq!(
        Some(&Value::Variable(index(BinderDepth::from(1_u32)))),
        arena.value(result_outside),
        "and an index outside the vanished binder lowers by one"
    );
}

/// A replacement with a free index is carried under the binders the walk
/// crossed, which is the half of substitution that capture-avoidance is.
#[test]
fn a_replacement_is_carried_under_the_binders_it_crosses()
{
    let mut arena = TermArena::new();
    let replacement = arena.value_variable(index(BinderDepth::from(0_u32)));
    let occurrence = arena.value_variable(index(BinderDepth::from(1_u32)));
    let body = arena.computation_return(occurrence);
    let lambda = arena.computation_lambda(body);
    let thunk = arena.value_thunk(lambda);
    let mut table = ContentTable::new();
    let mut memo = RewriteMemo::new();
    let result = substitute_value(&mut arena, &mut table, &mut memo, thunk, replacement);
    let Some(&Value::Thunk(result_lambda)) = arena.value(result)
    else {
        panic!("a substituted thunk is a thunk");
    };
    let Some(&Computation::Lambda(result_body)) = arena.computation(result_lambda)
    else {
        panic!("holding a lambda");
    };
    let Some(&Computation::Return(carried)) = arena.computation(result_body)
    else {
        panic!("whose body returns");
    };
    assert_eq!(
        Some(&Value::Variable(index(BinderDepth::from(1_u32)))),
        arena.value(carried),
        "the replacement's own free index rises past the binder it was carried under"
    );
}

/// Every type is closed at a vocabulary where no former is indexed by a
/// value term, so both rewrites hand back the node they were given — the
/// sharing-preserving reuse, exhibited where it is total.
#[test]
fn a_closed_type_shifts_to_itself()
{
    let mut arena = TermArena::new();
    let base = arena.value_type_base(BaseType::Integer);
    let unit = arena.value_type_unit();
    let product = arena.value_type_product(&[base, unit]);
    let returner = arena.comp_type_returner(product);
    let dependent = arena.comp_type_pi(unit, returner);
    let thunk = arena.value_type_thunk(dependent);
    let before = arena.watermark();
    let mut table = ContentTable::new();
    let mut memo = RewriteMemo::new();
    let shifted = shift_value_type(
        &mut arena,
        &mut table,
        &mut memo,
        thunk,
        BinderDepth::NONE,
        BinderDepth::from(3_u32),
    );
    assert_eq!(thunk, shifted, "a closed type shifts to the very same node");
    assert_eq!(
        before,
        arena.watermark(),
        "and the rewrite mints nothing, so the arena does not grow by a copy"
    );
}

#[test]
fn a_closed_type_instantiates_to_itself()
{
    let mut arena = TermArena::new();
    let unit = arena.value_type_unit();
    let returner = arena.comp_type_returner(unit);
    let dependent = arena.comp_type_pi(unit, returner);
    let replacement = arena.value_unit();
    let before = arena.watermark();
    let mut table = ContentTable::new();
    let mut memo = RewriteMemo::new();
    let instantiated =
        substitute_comp_type(&mut arena, &mut table, &mut memo, dependent, replacement);
    assert_eq!(
        dependent, instantiated,
        "instantiating a closed dependent arrow is the identity on its node"
    );
    let inner = substitute_value_type(&mut arena, &mut table, &mut memo, unit, replacement);
    assert_eq!(unit, inner, "and so is instantiating a closed value type");
    assert_eq!(
        before,
        arena.watermark(),
        "neither mints, so no intermediate outlives the verdict"
    );
}

/// A type carrying a code shifts and instantiates like the term it carries,
/// which is the whole of what "types in the context stop being closed"
/// means operationally.
#[test]
fn a_code_carrying_type_rewrites_through_its_code()
{
    let mut arena = TermArena::new();
    let zero = Level::zero();
    let code = arena.value_variable(index(BinderDepth::from(0_u32)));
    let element = arena.value_type_element(code, zero);
    let returner = arena.comp_type_returner(element);
    let mut table = ContentTable::new();
    let mut memo = RewriteMemo::new();

    let shifted = shift_value_type(
        &mut arena,
        &mut table,
        &mut memo,
        element,
        BinderDepth::NONE,
        BinderDepth::from(2_u32),
    );
    let Some(&ValueType::Element { code: raised, .. }) = arena.value_type(shifted)
    else {
        panic!("a shifted code-carrying type still carries a code");
    };
    assert_eq!(
        Some(&Value::Variable(index(BinderDepth::from(2_u32)))),
        arena.value(raised),
        "the code's free index rose with the type it sits in"
    );

    // And a dependent codomain instantiates: the returner under the binder
    // reads index zero, so instantiating it at a replacement replaces the
    // code outright.
    let replacement = arena.value_unit();
    let instantiated =
        substitute_comp_type(&mut arena, &mut table, &mut memo, returner, replacement);
    let Some(&CompType::Returner(result)) = arena.comp_type(instantiated)
    else {
        panic!("an instantiated returner is a returner");
    };
    let Some(&ValueType::Element { code: planted, .. }) = arena.value_type(result)
    else {
        panic!("over a code-carrying type");
    };
    assert_eq!(
        replacement, planted,
        "the codomain's code became the argument"
    );
}

/// The differential the memo's soundness rests on: the same function at two
/// type parameters answers alike.
///
/// The workload shares one subterm across many occurrences, so the memoized
/// run records one entry per distinct `(content, depth)` pair while the
/// memoless run recomputes each occurrence — and both produce the same
/// rewritten node.
#[test]
fn the_memoized_rewrite_agrees_with_the_memoless_one()
{
    /// Build a self-similar value whose expansion is exponential in `depth`
    /// and whose distinct-node count is linear in it.
    ///
    /// # Specification
    /// - provides: a shared pair spine with exactly `levels` links.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 at twelve shared pair levels; content equality between
    ///   memo modes, thirteen distinct supports and shared versus duplicated
    ///   children separate a collapsed fixture and a sharing-insensitive walk.
    /// - witness: `rewrite::tests::the_memoized_rewrite_agrees_with_the_memoless_one`
    #[spec(ensures: |ret| if levels.0 == 0 {
            arena.value(ret) == Some(&Value::Variable(DeBruijnIndex::from(0_u32)))
        } else {
            matches!(arena.value(ret).and_then(Value::components), Some(&[left, right]) if left == right)
        })]
    fn shared_composite(
        arena: &mut TermArena,
        levels: ChainLength,
    ) -> ValueId
    {
        let mut node = arena.value_variable(index(BinderDepth::from(0_u32)));
        let mut remaining = levels.0;
        while remaining > 0 {
            node = arena.value_tuple(&[node, node]);
            remaining = u32::from(arith::sub(
                arith::Int::from(remaining),
                arith::Int::from(1_u32),
            ));
        }
        node
    }

    let mut arena = TermArena::new();
    let root = shared_composite(&mut arena, ChainLength(12));

    let mut memoless_table = ContentTable::new();
    let mut memoless = NullMemo;
    let memoless_result = shift_value(
        &mut arena,
        &mut memoless_table,
        &mut memoless,
        root,
        BinderDepth::NONE,
        BinderDepth::from(1_u32),
    );

    let mut table = ContentTable::new();
    let mut memo = RewriteMemo::new();
    let memoized_result = shift_value(
        &mut arena,
        &mut table,
        &mut memo,
        root,
        BinderDepth::NONE,
        BinderDepth::from(1_u32),
    );

    // Content, not identity: the two runs answer with the same *term*, and
    // the memoized one answers with a shared spelling of it while the
    // memoless one answers with the expansion. Comparing ids here would
    // assert the opposite of the property under test.
    assert_eq!(
        content_digest(&arena, AnyNode::Value(memoless_result)),
        content_digest(&arena, AnyNode::Value(memoized_result)),
        "the memoized and memoless rewrites produce the same term"
    );
    assert_eq!(
        MemoEntryCount::from(13_usize),
        memo.plane_entry_count(RewritePlane::Shift),
        "one entry per distinct node of the composite, not one per occurrence"
    );
    assert_eq!(
        MemoEntryCount::from(0_usize),
        memo.plane_entry_count(RewritePlane::Substitute),
        "and the substitution plane accounts nothing, so neither plane hides behind the other"
    );

    // The anti-vacuity half, exhibited rather than counted: the memoized
    // answer shares its two children on one node, and the memoless answer
    // does not, so the workload cannot silently stop being shared and keep
    // this case passing.
    let Some(&[memoized_left, memoized_right]) =
        arena.value(memoized_result).and_then(Value::components)
    else {
        panic!("the composite rewrites to a pair");
    };
    assert_eq!(
        memoized_left, memoized_right,
        "the memoized rewrite answers once for the one distinct subject"
    );
    let Some(&[memoless_left, memoless_right]) =
        arena.value(memoless_result).and_then(Value::components)
    else {
        panic!("and so does the memoless one");
    };
    assert_ne!(
        memoless_left, memoless_right,
        "while the memoless rewrite answers once per occurrence, which is the cost the memo \
             removes"
    );
}

#[test]
fn two_rewrites_of_one_subject_are_two_supports()
{
    let mut arena = TermArena::new();
    let subject = arena.value_variable(index(BinderDepth::from(0_u32)));
    let replacement = arena.value_unit();
    let mut table = ContentTable::new();
    let shift = RewriteSupport::build(&mut table, &arena, RewriteGoal::Shift {
        subject: AnyNode::Value(subject),
        depth: BinderDepth::NONE,
        cutoff: BinderDepth::NONE,
        amount: BinderDepth::from(1_u32),
    });
    let substitute = RewriteSupport::build(&mut table, &arena, RewriteGoal::Substitute {
        subject: AnyNode::Value(subject),
        depth: BinderDepth::NONE,
        replacement,
    });
    assert_eq!(RewritePlane::Shift, shift.plane());
    assert_eq!(RewritePlane::Substitute, substitute.plane());
    assert_eq!(
        ContentAgreement::Differ,
        shift.agreement(&substitute),
        "two rewrites of one subject are two questions"
    );
    let deeper = RewriteSupport::build(&mut table, &arena, RewriteGoal::Shift {
        subject: AnyNode::Value(subject),
        depth: BinderDepth::from(1_u32),
        cutoff: BinderDepth::NONE,
        amount: BinderDepth::from(1_u32),
    });
    assert_eq!(
        ContentAgreement::Differ,
        shift.agreement(&deeper),
        "and one subject at two binder depths is two questions"
    );
    assert_ne!(
        shift.digest(),
        deeper.digest(),
        "and the memo files the two questions under different buckets"
    );
    assert_ne!(
        shift.digest(),
        substitute.digest(),
        "as it does the two rewrites"
    );
}

#[test]
fn session_rewrites_preserve_graph_evidence_and_native_children()
{
    use gandr_kernel_term::session::Evidence;
    use gandr_kernel_term::session::Graph;
    use gandr_kernel_term::session::Node;
    use gandr_kernel_term::session::State;
    let mut arena = TermArena::new();
    let variable = arena.value_variable(DeBruijnIndex::from(0_u32));
    let element = arena.value_type_element(variable, Level::zero());
    let unit = arena.value_type_unit();
    let payloads = arena.value_type_product(&[element]);
    let graph = alloc::sync::Arc::new(Graph {
        root: State(0),
        nodes: alloc::vec![Node::End],
    });
    let evidence = alloc::sync::Arc::new(Evidence::default());
    let session = arena.value_type_session(alloc::sync::Arc::clone(&graph), payloads);
    let code = arena.value_quote(session);
    let classifier = arena.value_type_path_universe(code, code);
    let path = arena.value_session_path(classifier, alloc::sync::Arc::clone(&evidence), variable);
    let mut table = ContentTable::new();
    let mut memo = RewriteMemo::new();
    let shifted = super::shift_value(
        &mut arena,
        &mut table,
        &mut memo,
        path,
        BinderDepth::NONE,
        BinderDepth::from(1_u32),
    );
    let Some(&Value::SessionPath {
        path_type,
        payload_paths,
        evidence: ref actual,
    }) = arena.value(shifted)
    else {
        panic!("session path retained")
    };
    assert_eq!(actual, &evidence);
    assert_eq!(
        arena.value(payload_paths),
        Some(&Value::Variable(DeBruijnIndex::from(1_u32)))
    );
    let Some(&ValueType::PathUniverse(source, target)) = arena.value_type(path_type)
    else {
        panic!("classifier retained")
    };
    assert_eq!(
        crate::conv::equal_values(&arena, source, target),
        crate::Convertibility::Convertible
    );
    let Some(&Value::Quote(ty)) = arena.value(source)
    else {
        panic!("quoted code")
    };
    let Some(&ValueType::Session {
        graph: ref actual,
        payloads,
    }) = arena.value_type(ty)
    else {
        panic!("session code")
    };
    assert_eq!(actual, &graph);
    let Some(&[field]) = arena
        .value_type(payloads)
        .and_then(ValueType::product_parts)
    else {
        panic!("one payload in the telescope")
    };
    let Some(&ValueType::Element { code, .. }) = arena.value_type(field)
    else {
        panic!("open payload code")
    };
    assert_eq!(
        arena.value(code),
        Some(&Value::Variable(DeBruijnIndex::from(1_u32)))
    );
    let replacement = arena.value_quote(unit);
    let substituted = super::substitute_value(&mut arena, &mut table, &mut memo, path, replacement);
    let Some(&Value::SessionPath {
        path_type,
        payload_paths,
        evidence: ref actual,
    }) = arena.value(substituted)
    else {
        panic!("substituted session path")
    };
    assert_eq!(payload_paths, replacement);
    assert_eq!(actual, &evidence);
    let Some(&ValueType::PathUniverse(source, _)) = arena.value_type(path_type)
    else {
        panic!("classifier")
    };
    let Some(&Value::Quote(ty)) = arena.value(source)
    else {
        panic!("quoted code")
    };
    let Some(&ValueType::Session {
        graph: ref actual,
        payloads,
    }) = arena.value_type(ty)
    else {
        panic!("session code")
    };
    assert_eq!(actual, &graph);
    assert_eq!(
        arena.value_type(payloads),
        Some(&ValueType::Product(alloc::boxed::Box::from([unit])))
    );
    let before = arena.watermark();
    assert_eq!(
        super::shift_value(
            &mut arena,
            &mut table,
            &mut memo,
            substituted,
            BinderDepth::NONE,
            BinderDepth::from(1_u32)
        ),
        substituted
    );
    assert_eq!(arena.watermark(), before);
}

#[test]
fn binder_counts_saturate_at_the_representable_boundary()
{
    for (raw, successor, machine) in [
        (0_u32, 1_u32, 0_usize),
        (7, 8, 7),
        (u32::MAX.saturating_sub(1), u32::MAX, 0xffff_fffe),
        (u32::MAX, u32::MAX, 0xffff_ffff),
    ] {
        let depth = BinderDepth::from(raw);
        assert_eq!(u32::from(depth.deeper()), successor);
        assert_eq!(u32::from(BinderDepth::past(depth)), successor);
        assert_eq!(usize::from(depth), machine);
    }
}

#[test]
fn outcome_projections_keep_matching_ids_and_decline_other_families()
{
    let mut arena = TermArena::new();
    let value = arena.value_unit();
    let other_value = arena.value_variable(DeBruijnIndex::from(3_u32));
    let computation = arena.computation_return(value);
    let other_computation = arena.computation_force(other_value);
    let value_type = arena.value_type_unit();
    let other_value_type = arena.value_type_base(BaseType::Integer);
    let comp_type = arena.comp_type_returner(value_type);
    let other_comp_type = arena.comp_type_arrow(value_type, comp_type);
    for (outcome, expected_value, expected_computation, expected_value_type, expected_comp_type) in [
        (
            super::RewriteOutcome::Value(other_value),
            other_value,
            computation,
            value_type,
            comp_type,
        ),
        (
            super::RewriteOutcome::Computation(other_computation),
            value,
            other_computation,
            value_type,
            comp_type,
        ),
        (
            super::RewriteOutcome::ValueType(other_value_type),
            value,
            computation,
            other_value_type,
            comp_type,
        ),
        (
            super::RewriteOutcome::CompType(other_comp_type),
            value,
            computation,
            value_type,
            other_comp_type,
        ),
    ] {
        assert_eq!(outcome.value_or(value), expected_value);
        assert_eq!(outcome.computation_or(computation), expected_computation);
        assert_eq!(outcome.value_type_or(value_type), expected_value_type);
        assert_eq!(outcome.comp_type_or(comp_type), expected_comp_type);
    }
}

#[test]
fn result_stack_preserves_order_and_falls_back_only_when_empty()
{
    let mut arena = TermArena::new();
    let value = arena.value_unit();
    let value_type = arena.value_type_unit();
    let original = AnyNode::Value(value);
    let first = super::RewriteOutcome::ValueType(value_type);
    let second = super::RewriteOutcome::Value(value);
    let mut results = alloc::vec![first, second];
    assert_eq!(super::popped(&mut results, original), second);
    assert_eq!(results.as_slice(), &[first]);
    assert_eq!(super::popped(&mut results, original), first);
    assert_eq!(super::popped(&mut results, original), second);
    assert!(results.is_empty());
}

#[test]
fn rewrite_agreement_ignores_colliding_digest_buckets()
{
    let mut arena = TermArena::new();
    let subject = AnyNode::Value(arena.value_variable(DeBruijnIndex::from(0_u32)));
    let mut table = ContentTable::new();
    let left = RewriteSupport::build(&mut table, &arena, RewriteGoal::Shift {
        subject,
        depth: BinderDepth::NONE,
        cutoff: BinderDepth::NONE,
        amount: BinderDepth::from(1_u32),
    });
    let mut right = RewriteSupport::build(&mut table, &arena, RewriteGoal::Shift {
        subject,
        depth: BinderDepth::from(1_u32),
        cutoff: BinderDepth::NONE,
        amount: BinderDepth::from(1_u32),
    });
    let mut same = left.clone();
    same.digest = right.digest;
    assert_eq!(left.agreement(&same), ContentAgreement::Agree);
    right.digest = left.digest;
    assert_eq!(left.agreement(&right), ContentAgreement::Differ);
}

#[test]
fn unreadable_subjects_rewrite_to_their_original_ids()
{
    let mut arena = TermArena::new();
    let replacement = arena.value_unit();
    let floor = arena.watermark();
    let first = arena.value_variable(DeBruijnIndex::from(0_u32));
    let second = arena.value_variable(DeBruijnIndex::from(1_u32));
    let computation = arena.computation_return(first);
    let value_type = arena.value_type_unit();
    let comp_type = arena.comp_type_returner(value_type);
    arena.truncate_to(floor);
    let mut results = alloc::vec![];
    let step = super::Rewrite::Shift {
        cutoff: BinderDepth::NONE,
        amount: BinderDepth::from(1_u32),
    };
    assert_eq!(
        super::close_value(&mut arena, step, first, BinderDepth::NONE, &mut results),
        first
    );
    assert_eq!(
        super::close_computation(&mut arena, computation, &mut results),
        computation
    );
    assert_eq!(
        super::close_value_type(&mut arena, value_type, &mut results),
        value_type
    );
    assert_eq!(
        super::close_comp_type(&mut arena, comp_type, &mut results),
        comp_type
    );
    let mut table = ContentTable::new();
    let mut memo = RewriteMemo::new();
    for root in [
        AnyNode::Value(first),
        AnyNode::Value(second),
        AnyNode::Computation(computation),
        AnyNode::ValueType(value_type),
        AnyNode::CompType(comp_type),
    ] {
        for rewrite in [
            super::Rewrite::Shift {
                cutoff: BinderDepth::NONE,
                amount: BinderDepth::from(1_u32),
            },
            super::Rewrite::Substitute { replacement },
        ] {
            assert_eq!(
                super::run_rewrite(
                    &mut arena,
                    &mut table,
                    &mut memo,
                    rewrite,
                    root,
                    super::BinderDepth::NONE
                ),
                super::outcome_of(root)
            );
            assert_eq!(arena.watermark(), floor);
        }
    }
}

#[test]
fn bind_and_case_rewrites_distinguish_binding_positions()
{
    let mut arena = TermArena::new();
    let inner = arena.value_variable(DeBruijnIndex::from(0_u32));
    let outer = arena.value_variable(DeBruijnIndex::from(1_u32));
    let bound = arena.computation_return(inner);
    let left = arena.computation_return(inner);
    let right = arena.computation_return(outer);
    let sequence = arena.computation_bind(bound, left);
    let case = arena.computation_case(inner, &[left, right]);
    let mut table = ContentTable::new();
    let mut memo = RewriteMemo::new();
    let shifted = shift_computation(
        &mut arena,
        &mut table,
        &mut memo,
        sequence,
        BinderDepth::NONE,
        BinderDepth::from(3_u32),
    );
    let Some(&Computation::Bind(shifted_bound, shifted_body)) = arena.computation(shifted)
    else {
        panic!("expected bind");
    };
    let Some(&Computation::Return(raised)) = arena.computation(shifted_bound)
    else {
        panic!("expected returned outer variable");
    };
    assert_eq!(
        arena.value(raised),
        Some(&Value::Variable(DeBruijnIndex::from(3_u32)))
    );
    assert_eq!(
        arena.computation(shifted_body),
        Some(&Computation::Return(inner))
    );
    let shifted = shift_computation(
        &mut arena,
        &mut table,
        &mut memo,
        case,
        BinderDepth::NONE,
        BinderDepth::from(3_u32),
    );
    let Some(&Computation::Case {
        scrutinee,
        ref branches,
    }) = arena.computation(shifted)
    else {
        panic!("expected case");
    };
    let &[on_left, on_right] = &**branches
    else {
        panic!("expected case");
    };
    assert_eq!(
        arena.value(scrutinee),
        Some(&Value::Variable(DeBruijnIndex::from(3_u32)))
    );
    assert_eq!(
        arena.computation(on_left),
        Some(&Computation::Return(inner))
    );
    let Some(&Computation::Return(raised)) = arena.computation(on_right)
    else {
        panic!("expected returned external variable");
    };
    assert_eq!(
        arena.value(raised),
        Some(&Value::Variable(DeBruijnIndex::from(4_u32)))
    );
}

#[test]
fn a_dependent_pair_and_its_split_bind_where_they_scope()
{
    let mut arena = TermArena::new();
    let base = arena.value_type_base(BaseType::Integer);
    let zero = arena.value_variable(DeBruijnIndex::from(0_u32));
    let one = arena.value_variable(DeBruijnIndex::from(1_u32));
    let two = arena.value_variable(DeBruijnIndex::from(2_u32));
    let first = arena.value_type_path(base, zero, zero);
    let second = arena.value_type_path(base, zero, one);
    let sigma = arena.value_type_sigma(first, second);
    let motive = arena.comp_type_returner(second);
    let body = arena.computation_return(two);
    let split = arena.computation_sigma_split(zero, motive, body);
    let mut table = ContentTable::new();
    let mut memo = RewriteMemo::new();
    let three = BinderDepth::from(3_u32);
    let variable = |at: u32| Value::Variable(DeBruijnIndex::from(at));
    let shifted = shift_value_type(
        &mut arena,
        &mut table,
        &mut memo,
        sigma,
        BinderDepth::NONE,
        three,
    );
    let Some(&ValueType::Sigma {
        first: moved_first,
        second: moved_second,
    }) = arena.value_type(shifted)
    else {
        panic!("expected a dependent pair");
    };
    let Some(&ValueType::Path { left, right, .. }) = arena.value_type(moved_first)
    else {
        panic!("expected the first factor's path");
    };
    assert_eq!(arena.value(left), Some(&variable(3)));
    assert_eq!(arena.value(right), Some(&variable(3)));
    let Some(&ValueType::Path { left, right, .. }) = arena.value_type(moved_second)
    else {
        panic!("expected the second factor's path");
    };
    assert_eq!(
        arena.value(left),
        Some(&variable(0)),
        "the second factor's binder is spared"
    );
    assert_eq!(arena.value(right), Some(&variable(4)));
    let shifted = shift_computation(
        &mut arena,
        &mut table,
        &mut memo,
        split,
        BinderDepth::NONE,
        three,
    );
    let Some(&Computation::SigmaSplit {
        scrutinee,
        motive: moved_motive,
        body: moved_body,
    }) = arena.computation(shifted)
    else {
        panic!("expected a dependent split");
    };
    assert_eq!(arena.value(scrutinee), Some(&variable(3)));
    let Some(&CompType::Returner(answer)) = arena.comp_type(moved_motive)
    else {
        panic!("expected the motive's returner");
    };
    let Some(&ValueType::Path { left, right, .. }) = arena.value_type(answer)
    else {
        panic!("expected the motive's path");
    };
    assert_eq!(
        arena.value(left),
        Some(&variable(0)),
        "the motive's binder is spared"
    );
    assert_eq!(arena.value(right), Some(&variable(4)));
    let Some(&Computation::Return(answered)) = arena.computation(moved_body)
    else {
        panic!("expected the body's return");
    };
    assert_eq!(
        arena.value(answered),
        Some(&variable(5)),
        "the body sits under both components"
    );
}

#[test]
fn carrying_refusals_follow_rule_precedence()
{
    let mut arena = TermArena::new();
    let replacement = arena.value_unit();
    let zero = arena.value_variable(DeBruijnIndex::from(0_u32));
    let one = arena.value_variable(DeBruijnIndex::from(1_u32));
    let computation = arena.computation_return(zero);
    let floor = arena.watermark();
    let unreadable = arena.value_unit();
    arena.truncate_to(floor);
    let shift = super::Rewrite::Shift {
        cutoff: BinderDepth::NONE,
        amount: BinderDepth::from(1_u32),
    };
    let substitute = super::Rewrite::Substitute { replacement };
    let crossed = BinderDepth::from(1_u32);
    for (rewrite, root, depth, expected) in [
        (
            shift,
            AnyNode::Value(unreadable),
            crossed,
            super::Maybe::Absent(super::carrying::Absent::Shift),
        ),
        (
            substitute,
            AnyNode::Value(unreadable),
            BinderDepth::NONE,
            super::Maybe::Absent(super::carrying::Absent::NoCrossedBinders),
        ),
        (
            substitute,
            AnyNode::Computation(computation),
            crossed,
            super::Maybe::Absent(super::carrying::Absent::DifferentOccurrence),
        ),
        (
            substitute,
            AnyNode::Value(unreadable),
            crossed,
            super::Maybe::Absent(super::carrying::Absent::UnreadableValue),
        ),
        (
            substitute,
            AnyNode::Value(zero),
            crossed,
            super::Maybe::Absent(super::carrying::Absent::DifferentOccurrence),
        ),
        (
            substitute,
            AnyNode::Value(one),
            crossed,
            super::Maybe::Present(replacement),
        ),
    ] {
        assert_eq!(
            super::carried_occurrence(&arena, rewrite, root, depth),
            expected
        );
    }
}

/// A child slot of a former, numbered in the order [`build`] asks for
/// them.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Slot(usize);

/// A former's children as [`build`] asks for them, each closed or the one
/// open slot reading the free variable `index`, which no former here binds
/// deep enough to capture.
///
/// # Specification
/// trivial.
struct Children
{
    /// The slot that reads the variable, if any.
    open: Option<Slot>,
    /// How many slots have been asked for.
    next: usize,
    /// The variable the open slot reads.
    index: DeBruijnIndex,
}

impl Children
{
    /// Every slot closed.
    ///
    /// # Specification
    /// trivial.
    fn closed() -> Self
    {
        Self {
            open: None,
            next: 0,
            index: DeBruijnIndex::from(0_u32),
        }
    }

    /// Slot `open` reading `index`, every other slot closed.
    ///
    /// # Specification
    /// trivial.
    const fn opening(
        open: Slot,
        index: DeBruijnIndex,
    ) -> Self
    {
        Self {
            open: Some(open),
            next: 0,
            index,
        }
    }

    /// The variable the next slot reads, or `None` for a closed one.
    ///
    /// # Specification
    /// trivial.
    fn read(&mut self) -> Option<DeBruijnIndex>
    {
        let slot = Slot(self.next);
        self.next = self.next.saturating_add(1);
        (self.open == Some(slot)).then_some(self.index)
    }

    /// The next slot as a value: the variable, or the unit.
    ///
    /// # Specification
    /// trivial.
    fn value(
        &mut self,
        arena: &mut TermArena,
    ) -> ValueId
    {
        match self.read() {
            Some(index) => arena.value_variable(index),
            None => arena.value_unit(),
        }
    }

    /// The next slot as a value type: the variable's element type, or the
    /// unit type.
    ///
    /// # Specification
    /// trivial.
    fn value_type(
        &mut self,
        arena: &mut TermArena,
    ) -> gandr_kernel_term::ValueTypeId
    {
        match self.read() {
            Some(index) => {
                let code = arena.value_variable(index);
                arena.value_type_element(code, Level::zero())
            },
            None => arena.value_type_unit(),
        }
    }

    /// The next slot as a computation returning [`Children::value`]'s.
    ///
    /// # Specification
    /// trivial.
    fn computation(
        &mut self,
        arena: &mut TermArena,
    ) -> gandr_kernel_term::ComputationId
    {
        let value = self.value(arena);
        arena.computation_return(value)
    }

    /// The next slot as the returner of [`Children::value_type`]'s.
    ///
    /// # Specification
    /// trivial.
    fn comp_type(
        &mut self,
        arena: &mut TermArena,
    ) -> gandr_kernel_term::CompTypeId
    {
        let value_type = self.value_type(arena);
        arena.comp_type_returner(value_type)
    }
}

/// Every former with children, each named by its family and node.
#[derive(Clone, Copy, Debug)]
enum Former
{
    Constructor,
    Record,
    SessionPath,
    SessionFlow,
    Stay,
    ForwardFlow,
    FunctionFlow,
    Then,
    FlowProduct,
    PathRefl,
    PathProduct,
    PathEquiv,
    Here,
    Returned,
    Higher,
    HigherEvaluation,
    QuantifiedEvaluation,
    Tuple,
    Injection,
    ListCons,
    Thunk,
    Lift,
    Quote,
    QuoteComputation,
    StaticApplication,
    DataCase,
    RecordProjection,
    TupleProjection,
    Lambda,
    Application,
    Return,
    Bind,
    Force,
    Case,
    SigmaSplit,
    ListFold,
    Transport,
    PathTransport,
    TelescopeTransport,
    Ride,
    TelescopeRide,
    RelatedApplication,
    With,
    Project,
    Fixpoint,
    DataType,
    RecordType,
    SessionType,
    PathUniverse,
    FlowUniverse,
    PathType,
    FlowType,
    ProductType,
    SigmaType,
    SumType,
    ListType,
    ThunkType,
    LiftType,
    ElementType,
    StagedType,
    StaticPiType,
    Returner,
    Arrow,
    Pi,
    ElementComp,
    WithType,
}

/// Every [`Former`].
const FORMERS: &[Former] = &[
    Former::Constructor,
    Former::Record,
    Former::SessionPath,
    Former::SessionFlow,
    Former::Stay,
    Former::ForwardFlow,
    Former::FunctionFlow,
    Former::Then,
    Former::FlowProduct,
    Former::PathRefl,
    Former::PathProduct,
    Former::PathEquiv,
    Former::Here,
    Former::Returned,
    Former::Higher,
    Former::HigherEvaluation,
    Former::QuantifiedEvaluation,
    Former::Tuple,
    Former::Injection,
    Former::ListCons,
    Former::Thunk,
    Former::Lift,
    Former::Quote,
    Former::QuoteComputation,
    Former::StaticApplication,
    Former::DataCase,
    Former::RecordProjection,
    Former::TupleProjection,
    Former::Lambda,
    Former::Application,
    Former::Return,
    Former::Bind,
    Former::Force,
    Former::Case,
    Former::SigmaSplit,
    Former::ListFold,
    Former::Transport,
    Former::PathTransport,
    Former::TelescopeTransport,
    Former::Ride,
    Former::TelescopeRide,
    Former::RelatedApplication,
    Former::With,
    Former::Project,
    Former::Fixpoint,
    Former::DataType,
    Former::RecordType,
    Former::SessionType,
    Former::PathUniverse,
    Former::FlowUniverse,
    Former::PathType,
    Former::FlowType,
    Former::ProductType,
    Former::SigmaType,
    Former::SumType,
    Former::ListType,
    Former::ThunkType,
    Former::LiftType,
    Former::ElementType,
    Former::StagedType,
    Former::StaticPiType,
    Former::Returner,
    Former::Arrow,
    Former::Pi,
    Former::ElementComp,
    Former::WithType,
];

/// `former` in `arena`, each child as `children` hands it out.
///
/// # Specification
/// trivial.
#[expect(
    clippy::too_many_lines,
    reason = "one arm per former, each its constructor call"
)]
fn build(
    arena: &mut TermArena,
    former: Former,
    children: &mut Children,
) -> AnyNode
{
    use alloc::boxed::Box;
    use alloc::collections::BTreeMap;
    use alloc::sync::Arc;
    use alloc::vec::Vec;

    use gandr_kernel_term::Component;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::ConstructorTag;
    use gandr_kernel_term::EvaluationComponent;
    use gandr_kernel_term::FieldLabel;
    use gandr_kernel_term::FixpointEvidence;
    use gandr_kernel_term::HigherDepth;
    use gandr_kernel_term::HigherProgram;
    use gandr_kernel_term::LayerPosition;
    use gandr_kernel_term::PathEvidence;
    use gandr_kernel_term::Seam;
    use gandr_kernel_term::Side;
    use gandr_kernel_term::Stage;
    use gandr_kernel_term::StageId;
    use gandr_kernel_term::Summand;
    use gandr_kernel_term::session::Evidence;
    use gandr_kernel_term::session::Graph;
    use gandr_kernel_term::session::Node;
    use gandr_kernel_term::session::State;

    let label = |name: &str| FieldLabel::from(String::from(name));
    let c = children;
    match former {
        Former::Constructor => {
            let datatype = c.value_type(arena);
            let fields = Vec::from([c.value(arena), c.value(arena)]);
            AnyNode::Value(arena.value_constructor(datatype, ConstructorTag::from(0_usize), fields))
        },
        Former::Record => {
            let fields =
                BTreeMap::from([(label("a"), c.value(arena)), (label("b"), c.value(arena))]);
            AnyNode::Value(arena.value_record(fields))
        },
        Former::SessionPath => {
            let classifier = c.value_type(arena);
            let paths = c.value(arena);
            AnyNode::Value(arena.value_session_path(
                classifier,
                Arc::new(Evidence::default()),
                paths,
            ))
        },
        Former::SessionFlow => {
            let classifier = c.value_type(arena);
            let paths = c.value(arena);
            AnyNode::Value(arena.value_session_flow(
                classifier,
                Arc::new(Evidence::default()),
                paths,
            ))
        },
        Former::Stay => {
            let point = c.value(arena);
            AnyNode::Value(arena.value_stay(point))
        },
        Former::ForwardFlow => {
            let classifier = c.value_type(arena);
            let translator = c.value(arena);
            let outputs = Box::from([c.value(arena), c.value(arena)]);
            AnyNode::Value(arena.value_forward_flow(classifier, translator, outputs, Arc::from([])))
        },
        Former::FunctionFlow => {
            let classifier = c.value_type(arena);
            let (domain, codomain) = (c.value(arena), c.value(arena));
            AnyNode::Value(arena.value_function_flow(classifier, domain, codomain))
        },
        Former::Then => {
            let (first, second) = (c.value(arena), c.value(arena));
            AnyNode::Value(arena.value_then(first, second, Seam::Sequence))
        },
        Former::FlowProduct => {
            let (first, second) = (c.value(arena), c.value(arena));
            AnyNode::Value(arena.value_flow_product(first, second))
        },
        Former::PathRefl => {
            let code = c.value(arena);
            AnyNode::Value(arena.value_path_refl(code))
        },
        Former::PathProduct => {
            let (first, second) = (c.value(arena), c.value(arena));
            AnyNode::Value(arena.value_path_product(first, second))
        },
        Former::PathEquiv => {
            let classifier = c.value_type(arena);
            let (forward, backward) = (c.value(arena), c.value(arena));
            let evidence = Arc::new(PathEvidence::default());
            AnyNode::Value(arena.value_path_equiv(classifier, forward, backward, evidence))
        },
        Former::Here => {
            let point = c.value(arena);
            AnyNode::Value(arena.value_here(point))
        },
        Former::Returned => {
            let computation = c.computation(arena);
            AnyNode::Value(arena.value_returned(computation))
        },
        Former::Higher => {
            let program = Arc::new(HigherProgram {
                depth: HigherDepth(1),
                root: LayerPosition(0),
                layers: Vec::new(),
            });
            let evidence = Box::from([c.value(arena), c.value(arena)]);
            AnyNode::Value(arena.value_higher(program, evidence))
        },
        Former::HigherEvaluation => {
            let mut component = |arena: &mut TermArena| EvaluationComponent {
                left: c.value(arena),
                right: c.value(arena),
                evidence: c.value(arena),
            };
            let components = Box::from([component(arena), component(arena)]);
            AnyNode::Value(arena.value_higher_evaluation(Arc::from([]), components))
        },
        Former::QuantifiedEvaluation => {
            let children = Box::from([c.value(arena), c.value(arena)]);
            AnyNode::Value(arena.value_quantified_evaluation(Arc::from([]), children))
        },
        Former::Tuple => {
            let components = [c.value(arena), c.value(arena)];
            AnyNode::Value(arena.value_tuple(&components))
        },
        Former::Injection => {
            let body = c.value(arena);
            AnyNode::Value(arena.value_injection(Summand::from(0_usize), body))
        },
        Former::ListCons => {
            let (head, tail) = (c.value(arena), c.value(arena));
            AnyNode::Value(arena.value_list_cons(head, tail))
        },
        Former::Thunk => {
            let body = c.computation(arena);
            AnyNode::Value(arena.value_thunk(body))
        },
        Former::Lift => {
            let body = c.value(arena);
            AnyNode::Value(arena.value_lift(Level::zero(), body))
        },
        Former::Quote => {
            let quoted = c.value_type(arena);
            AnyNode::Value(arena.value_quote(quoted))
        },
        Former::QuoteComputation => {
            let quoted = c.comp_type(arena);
            AnyNode::Value(arena.value_quote_computation(quoted))
        },
        Former::StaticApplication => {
            let (head, argument) = (c.value(arena), c.value(arena));
            AnyNode::Value(arena.value_static_application(head, argument))
        },
        Former::DataCase => {
            let scrutinee = c.value(arena);
            let motive = c.comp_type(arena);
            let branches = Vec::from([c.computation(arena), c.computation(arena)]);
            AnyNode::Computation(arena.computation_data_case(scrutinee, motive, branches))
        },
        Former::RecordProjection => {
            let record = c.value(arena);
            AnyNode::Computation(arena.computation_record_projection(record, label("a")))
        },
        Former::TupleProjection => {
            let tuple = c.value(arena);
            AnyNode::Computation(
                arena.computation_tuple_projection(tuple, Component::from(0_usize)),
            )
        },
        Former::Lambda => {
            let body = c.computation(arena);
            AnyNode::Computation(arena.computation_lambda(body))
        },
        Former::Application => {
            let head = c.computation(arena);
            let argument = c.value(arena);
            AnyNode::Computation(arena.computation_application(head, argument))
        },
        Former::Return => {
            let value = c.value(arena);
            AnyNode::Computation(arena.computation_return(value))
        },
        Former::Bind => {
            let (bound, body) = (c.computation(arena), c.computation(arena));
            AnyNode::Computation(arena.computation_bind(bound, body))
        },
        Former::Force => {
            let value = c.value(arena);
            AnyNode::Computation(arena.computation_force(value))
        },
        Former::Case => {
            let scrutinee = c.value(arena);
            let branches = [c.computation(arena), c.computation(arena)];
            AnyNode::Computation(arena.computation_case(scrutinee, &branches))
        },
        Former::SigmaSplit => {
            let scrutinee = c.value(arena);
            let motive = c.comp_type(arena);
            let body = c.computation(arena);
            AnyNode::Computation(arena.computation_sigma_split(scrutinee, motive, body))
        },
        Former::ListFold => {
            let (element, result) = (c.value_type(arena), c.value_type(arena));
            let list = c.value(arena);
            let (on_nil, on_cons) = (c.computation(arena), c.computation(arena));
            AnyNode::Computation(
                arena.computation_list_fold(element, result, list, on_nil, on_cons),
            )
        },
        Former::Transport => {
            let (path, value) = (c.value(arena), c.value(arena));
            AnyNode::Computation(arena.computation_transport(path, value))
        },
        Former::PathTransport => {
            let motive = c.value_type(arena);
            let (path, value) = (c.value(arena), c.value(arena));
            AnyNode::Computation(arena.computation_path_transport(motive, path, value))
        },
        Former::TelescopeTransport => {
            let motive = c.comp_type(arena);
            let (path, start) = (c.value(arena), c.value(arena));
            let (over, value) = (c.value(arena), c.value(arena));
            AnyNode::Computation(
                arena.computation_telescope_transport(motive, path, start, over, value),
            )
        },
        Former::Ride => {
            let motive = c.value_type(arena);
            let (flow, value) = (c.value(arena), c.value(arena));
            AnyNode::Computation(arena.computation_ride(motive, flow, value))
        },
        Former::TelescopeRide => {
            let motive = c.comp_type(arena);
            let (flow, start) = (c.value(arena), c.value(arena));
            let (over, value) = (c.value(arena), c.value(arena));
            AnyNode::Computation(arena.computation_telescope_ride(motive, flow, start, over, value))
        },
        Former::RelatedApplication => {
            let path = c.value(arena);
            let arguments = (c.value(arena), c.value(arena));
            let evidence = c.value(arena);
            let body = c.computation(arena);
            AnyNode::Computation(
                arena.computation_related_application(path, arguments, evidence, body),
            )
        },
        Former::With => {
            let (left, right) = (c.computation(arena), c.computation(arena));
            AnyNode::Computation(arena.computation_with(left, right))
        },
        Former::Project => {
            let pair = c.computation(arena);
            AnyNode::Computation(arena.computation_project(Side::Left, pair))
        },
        Former::Fixpoint => {
            let body = c.computation(arena);
            AnyNode::Computation(arena.computation_fixpoint(body, FixpointEvidence::Partial))
        },
        Former::DataType => {
            let arguments = Vec::from([c.value(arena), c.value(arena)]);
            AnyNode::ValueType(arena.value_type_data(ConstantIndex::from(0_usize), arguments))
        },
        Former::RecordType => {
            let fields = BTreeMap::from([
                (label("a"), c.value_type(arena)),
                (label("b"), c.value_type(arena)),
            ]);
            AnyNode::ValueType(arena.value_type_record(fields))
        },
        Former::SessionType => {
            let graph = Arc::new(Graph {
                root: State(0),
                nodes: alloc::vec![Node::End],
            });
            let payloads = c.value_type(arena);
            AnyNode::ValueType(arena.value_type_session(graph, payloads))
        },
        Former::PathUniverse => {
            let (source, target) = (c.value(arena), c.value(arena));
            AnyNode::ValueType(arena.value_type_path_universe(source, target))
        },
        Former::FlowUniverse => {
            let (source, target) = (c.value(arena), c.value(arena));
            AnyNode::ValueType(arena.value_type_flow_universe(source, target))
        },
        Former::PathType => {
            let domain = c.value_type(arena);
            let (left, right) = (c.value(arena), c.value(arena));
            AnyNode::ValueType(arena.value_type_path(domain, left, right))
        },
        Former::FlowType => {
            let domain = c.value_type(arena);
            let (source, target) = (c.value(arena), c.value(arena));
            AnyNode::ValueType(arena.value_type_flow(domain, source, target))
        },
        Former::ProductType => {
            let components = [c.value_type(arena), c.value_type(arena)];
            AnyNode::ValueType(arena.value_type_product(&components))
        },
        Former::SigmaType => {
            let (first, second) = (c.value_type(arena), c.value_type(arena));
            AnyNode::ValueType(arena.value_type_sigma(first, second))
        },
        Former::SumType => {
            let summands = [c.value_type(arena), c.value_type(arena)];
            AnyNode::ValueType(arena.value_type_sum(&summands))
        },
        Former::ListType => {
            let element = c.value_type(arena);
            AnyNode::ValueType(arena.value_type_list(element))
        },
        Former::ThunkType => {
            let body = c.comp_type(arena);
            AnyNode::ValueType(arena.value_type_thunk(body))
        },
        Former::LiftType => {
            let inner = c.value_type(arena);
            AnyNode::ValueType(arena.value_type_lift(inner, Level::zero()))
        },
        Former::ElementType => {
            let code = c.value(arena);
            AnyNode::ValueType(arena.value_type_element(code, Level::zero()))
        },
        Former::StagedType => {
            let base = c.value_type(arena);
            AnyNode::ValueType(arena.value_type_staged(base, Stage::At(StageId::from(0_usize))))
        },
        Former::StaticPiType => {
            let (domain, codomain) = (c.value_type(arena), c.value_type(arena));
            AnyNode::ValueType(arena.value_type_static_pi(domain, codomain))
        },
        Former::Returner => {
            let result = c.value_type(arena);
            AnyNode::CompType(arena.comp_type_returner(result))
        },
        Former::Arrow => {
            let domain = c.value_type(arena);
            let codomain = c.comp_type(arena);
            AnyNode::CompType(arena.comp_type_arrow(domain, codomain))
        },
        Former::Pi => {
            let domain = c.value_type(arena);
            let codomain = c.comp_type(arena);
            AnyNode::CompType(arena.comp_type_pi(domain, codomain))
        },
        Former::ElementComp => {
            let code = c.value(arena);
            AnyNode::CompType(arena.comp_type_element(code, Level::zero()))
        },
        Former::WithType => {
            let (left, right) = (c.comp_type(arena), c.comp_type(arena));
            AnyNode::CompType(arena.comp_type_with(left, right))
        },
    }
}

/// `node` shifted by one past no cutoff, under a memo that keeps nothing,
/// so every node's rebuild decision runs.
///
/// # Specification
/// trivial.
fn shifted(
    arena: &mut TermArena,
    node: AnyNode,
) -> AnyNode
{
    let mut table = ContentTable::new();
    let memo = &mut NullMemo;
    let (cutoff, amount) = (BinderDepth::NONE, BinderDepth::from(1_u32));
    match node {
        AnyNode::Value(id) => {
            AnyNode::Value(shift_value(arena, &mut table, memo, id, cutoff, amount))
        },
        AnyNode::Computation(id) => AnyNode::Computation(shift_computation(
            arena, &mut table, memo, id, cutoff, amount,
        )),
        AnyNode::ValueType(id) => AnyNode::ValueType(shift_value_type(
            arena, &mut table, memo, id, cutoff, amount,
        )),
        AnyNode::CompType(id) => AnyNode::CompType(super::shift_comp_type(
            arena, &mut table, memo, id, cutoff, amount,
        )),
    }
}

/// Every former rebuilds exactly where a child changed: an unchanged
/// former is returned as itself, minting nothing, and a change in any one
/// child is carried into the fresh node whichever child it is.
#[test]
fn every_former_rebuilds_exactly_where_a_child_changed()
{
    for &former in FORMERS {
        let mut arena = TermArena::new();
        let mut closed = Children::closed();
        let subject = build(&mut arena, former, &mut closed);
        let before = arena.watermark();
        assert_eq!(
            shifted(&mut arena, subject),
            subject,
            "{former:?} reads no variable, so it shifts to itself"
        );
        assert_eq!(
            arena.watermark(),
            before,
            "and {former:?} mints nothing on the way"
        );
        for slot in (0 .. closed.next).map(Slot) {
            let subject = build(
                &mut arena,
                former,
                &mut Children::opening(slot, DeBruijnIndex::from(10_u32)),
            );
            let expected = build(
                &mut arena,
                former,
                &mut Children::opening(slot, DeBruijnIndex::from(11_u32)),
            );
            let result = shifted(&mut arena, subject);
            assert_eq!(
                content_digest(&arena, result),
                content_digest(&arena, expected),
                "{former:?}'s {slot:?} alone reads the variable, and its rise is carried"
            );
        }
    }
}
