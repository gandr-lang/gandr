//! The tests of `rewrite` that build their fixtures with the judgement: each
//! one admits through `Environment` or reads through conversion, which stand
//! above the record, so it runs in this crate.

//! Witnesses for the rewrite machines: shifts and substitutions, their
//! memo keys, and the rebuild each former makes only where a child changed.

use gandr_kernel_strata::Level;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::Value;
use gandr_kernel_term::ValueType;

use crate::encoding::ContentTable;
use crate::rewrite::BinderDepth;
use crate::rewrite::RewriteMemo;

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
    let mut table = ContentTable::named();
    let mut memo = RewriteMemo::new();
    let shifted = crate::rewrite::shift_value(
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
    let substituted =
        crate::rewrite::substitute_value(&mut arena, &mut table, &mut memo, path, replacement);
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
        crate::rewrite::shift_value(
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
