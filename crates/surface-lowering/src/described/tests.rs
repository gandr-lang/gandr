//! Each described node at the role and the type its member states.

use alloc::string::String;
use alloc::vec::Vec;

use gandr_core_term::CoreArena;
use gandr_core_term::ValueType;
use gandr_surface_syntax::ByteOffset;
use gandr_surface_syntax::ByteSpan;
use gandr_surface_syntax::SourceText;

use super::DescribedRole;
use super::DescribedType;
use super::DescribedTypes;
use crate::LoweringBudget;
use crate::fixture::grammar;
use crate::fixture::parsed;
use crate::lower_module;
use crate::namespace::Recognition;

/// The described types of `source`, with the arena they were minted into.
///
/// # Specification
/// trivial.
fn described(source: SourceText<'_>) -> (DescribedTypes, CoreArena)
{
    let grammar = grammar();
    let tree = parsed(&grammar, source);
    let mut arena = CoreArena::new();
    let module = lower_module(
        &grammar,
        &tree,
        &mut arena,
        LoweringBudget::DEFAULT,
        Recognition::default(),
    )
    .unwrap();
    let types = module.described_types(&mut arena);
    (types, arena)
}

/// The bytes of the first `inner` in the first `around` of `source`.
///
/// # Specification
/// trivial.
fn at(
    source: SourceText<'_>,
    around: SourceText<'_>,
    inner: SourceText<'_>,
) -> ByteSpan
{
    let text = <&str>::from(source);
    let around = <&str>::from(around);
    let inner = <&str>::from(inner);
    let outer = text.find(around).expect("the surrounding text is written");
    let start = text
        .get(outer ..)
        .and_then(|rest| rest.find(inner))
        .map(|offset| outer.saturating_add(offset))
        .expect("the node is written inside it");
    ByteSpan::new(
        ByteOffset::from(start),
        ByteOffset::from(start.saturating_add(inner.len())),
    )
    .unwrap()
}

/// The one entry of `types` at `span` in `role`.
///
/// # Specification
/// trivial.
fn entry(
    types: &DescribedTypes,
    span: ByteSpan,
    role: DescribedRole,
) -> DescribedType
{
    let found: Vec<&DescribedType> = types
        .entries
        .iter()
        .filter(|entry| entry.span == span && entry.role == role)
        .collect();
    let [found] = *found.as_slice()
    else {
        panic!("one {role:?} entry at {span:?}: {found:?}");
    };
    *found
}

/// The names of the context `entry` is read in.
///
/// # Specification
/// trivial.
fn context(
    types: &DescribedTypes,
    entry: DescribedType,
) -> Vec<String>
{
    types.contexts[usize::from(entry.context)]
        .iter()
        .map(|name| String::from(name.as_ref()))
        .collect()
}

/// The value type an operation's type `ty` returns, read through its thunk
/// and every function former.
///
/// # Specification
/// trivial.
fn returned(
    arena: &CoreArena,
    ty: gandr_core_term::ValueTypeId,
) -> Option<ValueType>
{
    let Some(&ValueType::Thunk(mut comp)) = arena.value_type(ty)
    else {
        return None;
    };
    loop {
        match *arena.comp_type(comp)? {
            gandr_core_term::CompType::Returner { result, .. } => {
                return arena.value_type(result).cloned();
            },
            gandr_core_term::CompType::Arrow { codomain, .. }
            | gandr_core_term::CompType::Pi { codomain, .. } => comp = codomain,
            gandr_core_term::CompType::Element { .. }
            | gandr_core_term::CompType::Unknown
            | gandr_core_term::CompType::With(..)
            | gandr_core_term::CompType::Codata { .. } => return None,
        }
    }
}

#[test]
fn a_theory_answers_at_every_member()
{
    let source = SourceText::from(
        "theory Cat {\n  sort Ob : Type;\n  sort Hom(dom : Ob, cod : Ob) : Type;\n  oper id : (a \
         : Ob) --> Hom(a, a);\n  oper comp : (f : Hom(a, b), g : Hom(b, c)) --> Hom(a, c);\n  \
         rule unitL : comp(id(a), f) ==> f;\n}\ntheory Add {\n  sort Nat : Type;\n  oper add : \
         (Nat, Nat) --> Nat;\n  rule cong1 : (rule p : x ==> x′, data x : Nat, data y : Nat) \
         ==> (z : Nat) {\n    node : p(x) ==> (x′);\n    node : add(x′, y) --> (z);\n  };\n}\n",
    );
    let span = |around: &'static str, inner: &'static str| {
        at(source, SourceText::from(around), SourceText::from(inner))
    };
    let (types, arena) = described(source);
    let ty = |entry: DescribedType| arena.value_type(entry.ty).cloned();

    let ob = entry(&types, span("sort Ob", "Ob"), DescribedRole::Name);
    assert!(
        matches!(ty(ob), Some(ValueType::Universe { .. })),
        "an unindexed sort is a type"
    );
    assert_eq!(context(&types, ob), Vec::<String>::new());
    let hom = entry(&types, span("sort Hom", "Hom"), DescribedRole::Name);
    assert!(
        matches!(ty(hom), Some(ValueType::Thunk(_))),
        "an indexed sort is a family"
    );
    assert_eq!(context(&types, hom), ["Ob"], "under the sorts before it");
    let comp = entry(&types, span("oper comp", "comp"), DescribedRole::Name);
    assert!(matches!(ty(comp), Some(ValueType::Thunk(_))));
    assert_eq!(context(&types, comp), ["Ob", "Hom", "id"]);
    assert!(
        matches!(returned(&arena, comp.ty), Some(ValueType::Element { .. })),
        "an operation with one result returns its sort, not a tuple of it"
    );
    let law = entry(&types, span("unitL", "unitL"), DescribedRole::Name);
    assert!(matches!(ty(law), Some(ValueType::Thunk(_))));
    assert_eq!(context(&types, law), ["Ob", "Hom", "id", "comp"]);

    let classifier = entry(&types, span("Ob : Type", "Type"), DescribedRole::Type);
    assert!(matches!(ty(classifier), Some(ValueType::Universe { .. })));
    assert_ne!(
        ty(classifier),
        ty(ob),
        "the classifier is a universe above the sorts'"
    );
    let port = entry(&types, span("(a : Ob)", "a"), DescribedRole::Name);
    assert!(
        matches!(ty(port), Some(ValueType::Element { .. })),
        "decoded from its sort"
    );
    let element = |entry: DescribedType| match arena.value_type(entry.ty) {
        Some(&ValueType::Element { code, .. }) => arena.value(code).cloned(),
        _ => None,
    };
    let index = entry(&types, span("--> Hom(a, a)", "a"), DescribedRole::Term);
    assert!(
        element(index).is_some(),
        "an index variable at its binder's sort"
    );
    let sort = entry(&types, span("(a : Ob)", "Ob"), DescribedRole::Type);
    assert!(
        matches!(ty(sort), Some(ValueType::Universe { .. })),
        "a written sort"
    );

    let applied = entry(&types, span("id(a)", "id(a)"), DescribedRole::Term);
    assert!(
        matches!(ty(applied), Some(ValueType::Element { .. })),
        "at the result sort"
    );
    let head = entry(&types, span("comp(id(a)", "id"), DescribedRole::Term);
    let declared = entry(&types, span("oper id", "id"), DescribedRole::Name);
    assert_eq!(ty(head), ty(declared), "a head at its operation's type");
    assert_eq!(context(&types, head), context(&types, declared));
    let variable = entry(&types, span("f) ==>", "f"), DescribedRole::Term);
    assert!(
        matches!(element(variable), Some(gandr_core_term::Value::Returned(_))),
        "a law's variable at its own binder's sort, `Hom` applied, not another binder's `Ob`"
    );
    assert!(matches!(ty(variable), Some(ValueType::Element { .. })));

    let nat = entry(&types, span("sort Nat", "Nat"), DescribedRole::Name);
    let wire = entry(&types, span("(x′)", "x′"), DescribedRole::Term);
    let joined = entry(&types, span("==> x′", "x′"), DescribedRole::Term);
    let code = |entry: DescribedType| match arena.value_type(entry.ty) {
        Some(&ValueType::Element { code, .. }) => arena.value(code).cloned(),
        _ => None,
    };
    assert!(code(wire).is_some(), "an element of a sort");
    assert_eq!(code(wire), code(joined), "a rewrite's sides share a sort");
    assert_eq!(context(&types, wire), ["Nat", "add"]);
    let output = entry(&types, span("--> (z)", "z"), DescribedRole::Term);
    assert_eq!(
        code(output),
        code(wire),
        "an operation's output wire at its sort"
    );
    assert!(
        matches!(ty(nat), Some(ValueType::Universe { .. })),
        "the sort's kind"
    );
}

#[test]
fn a_binder_answers_at_its_sort_and_its_operation_nowhere()
{
    let source = SourceText::from(
        "theory IdentityReturn {\n  sort VTy : Type;\n  sort CTy : Type;\n  sort VTm(a : VTy) : \
         Type+;\n  sort CTm(b : CTy) : Type;\n  oper f : (a : VTy) --> CTy;\n  oper arrow : (a \
         : VTy, b : CTy) --> CTy;\n  oper ret : (a : VTy, t : VTm(a)) --> CTm(f(a));\n  oper \
         lam : (a : VTy, b : CTy, t : pi+ (x : VTm(a)) . CTm(b)) --> CTm(arrow(a, b));\n}\n",
    );
    let span = |around: &'static str, inner: &'static str| {
        at(source, SourceText::from(around), SourceText::from(inner))
    };
    let (types, arena) = described(source);
    let ty = |entry: DescribedType| arena.value_type(entry.ty).cloned();

    let binder = entry(&types, span("(x :", "x"), DescribedRole::Name);
    assert!(
        matches!(ty(binder), Some(ValueType::Element { .. })),
        "a binder at its sort"
    );
    assert_eq!(
        context(&types, binder),
        ["VTy", "CTy", "VTm", "CTm", "f", "arrow", "ret", "a", "b"],
        "under the members and the ports before it"
    );
    let domain = entry(&types, span("(x : VTm", "VTm(a)"), DescribedRole::Type);
    assert!(
        matches!(ty(domain), Some(ValueType::Universe { .. })),
        "the binder's sort at its universe"
    );
    let index = entry(&types, span("(x : VTm(a)", "a"), DescribedRole::Term);
    assert!(
        matches!(ty(index), Some(ValueType::Element { .. })),
        "the binder's index at its port's sort"
    );
    let body = entry(&types, span(". CTm(b)", "CTm(b)"), DescribedRole::Type);
    assert!(
        matches!(ty(body), Some(ValueType::Universe { .. })),
        "the bound port's sort at its universe"
    );
    for applied in [
        span("--> CTm(f(a))", "f(a)"),
        span("--> CTm(arrow(a, b))", "arrow(a, b)"),
    ] {
        assert!(
            matches!(
                ty(entry(&types, applied, DescribedRole::Term)),
                Some(ValueType::Element { .. })
            ),
            "an index application at its operation's result, first-order or not"
        );
    }
    for unstated in [span("oper lam", "lam"), span("t : pi+", "t")] {
        assert!(
            types.entries.iter().all(|held| held.span != unstated),
            "no component states a binding operation or its bound port"
        );
    }
}

/// #668: a constant applied in a law, `pt()`, answers at its sort as every
/// other application there does.
#[test]
fn a_nullary_operation_in_a_law_answers_at_its_sort_668()
{
    let source = SourceText::from(
        "theory Pointed {\n  sort P : Type;\n  oper pt : P;\n  oper flip : (p : P) --> P;\n  rule \
         flipPt : flip(pt()) <=> pt();\n}\n",
    );
    let span = |around: &'static str, inner: &'static str| {
        at(source, SourceText::from(around), SourceText::from(inner))
    };
    let (types, arena) = described(source);
    let code = |entry: DescribedType| match arena.value_type(entry.ty) {
        Some(&ValueType::Element { code, .. }) => arena.value(code).cloned(),
        _ => None,
    };
    let applied = entry(
        &types,
        span("flip(pt())", "flip(pt())"),
        DescribedRole::Term,
    );
    let inner = entry(&types, span("flip(pt())", "pt()"), DescribedRole::Term);
    let right = entry(&types, span("<=> pt()", "pt()"), DescribedRole::Term);
    assert!(code(applied).is_some(), "an application at its sort");
    assert_eq!(code(inner), code(applied), "the argument at the same sort");
    assert_eq!(
        code(right),
        code(applied),
        "the right side at the same sort"
    );
}

#[test]
fn a_circuit_wire_takes_its_sort_from_whichever_reading_reaches_it()
{
    let source = SourceText::from(
        "theory Wired {\n  sort Nat : Type;\n  sort Bool : Type;\n  oper add : (Nat, Nat) --> \
         Nat;\n  oper isz : (Nat) --> Bool;\n  rule late : (rule p : u ==> u2, data x : Nat, \
         data y : Nat) ==> (z : Nat) {\n    node : p(tt) ==> (tlate);\n    node : add(x, y) \
         --> (tt);\n  };\n  rule side : (rule q : x ==> wside, data x : Nat) ==> (o : Nat) {\n    \
         node : q(x) ==> (o);\n  };\n  rule tests : (data x : Nat) ==> (ob : Bool) {\n    node : \
         isz(x) --> (bout);\n  };\n}\n",
    );
    let span = |around: &'static str, inner: &'static str| {
        at(source, SourceText::from(around), SourceText::from(inner))
    };
    let (types, arena) = described(source);
    let element = |entry: DescribedType| match arena.value_type(entry.ty) {
        Some(&ValueType::Element { code, .. }) => arena.value(code).cloned(),
        _ => None,
    };
    let late = entry(&types, span("(tlate)", "tlate"), DescribedRole::Term);
    assert!(
        element(late).is_some(),
        "a wire sorted only once a later line has sorted its input"
    );
    let side = entry(&types, span("==> wside", "wside"), DescribedRole::Term);
    assert!(
        element(side).is_some(),
        "a rewrite's side sorted by the side it rewrites"
    );
    let bout = entry(&types, span("(bout)", "bout"), DescribedRole::Term);
    let ob = entry(&types, span("(ob : Bool)", "ob"), DescribedRole::Name);
    assert_eq!(
        element(bout),
        element(ob),
        "an operation's output wire at that operation's result sort"
    );
}

#[test]
fn a_data_rule_answers_each_node_at_its_sort()
{
    let source = SourceText::from(
        "data NatDiv : Type {\n  Zero : NatDiv;\n  Succ : (n : NatDiv) --> NatDiv;\n  oper \
         divmod(m : NatDiv, n : NatDiv) -> (quot : NatDiv, rem : NatDiv);\n  oper half(h : \
         NatDiv) -> NatDiv;\n  rule divmod(m, Succ(d)) ==> (Zero, m);\n}\n",
    );
    let span = |around: &'static str, inner: &'static str| {
        at(source, SourceText::from(around), SourceText::from(inner))
    };
    let (types, arena) = described(source);
    let ty = |entry: DescribedType| arena.value_type(entry.ty).cloned();

    let zero = entry(&types, span("Zero :", "Zero"), DescribedRole::Name);
    assert!(
        matches!(ty(zero), Some(ValueType::Data { .. })),
        "a constant at its family"
    );
    let succ = entry(&types, span("Succ :", "Succ"), DescribedRole::Name);
    assert!(
        matches!(ty(succ), Some(ValueType::Thunk(_))),
        "a constructor over its field"
    );
    let field = entry(&types, span("(n : NatDiv) -->", "n"), DescribedRole::Name);
    assert_eq!(ty(field), ty(zero), "a field at its sort");
    let field_sort = entry(
        &types,
        span("(n : NatDiv) -->", "NatDiv"),
        DescribedRole::Type,
    );
    assert!(
        matches!(ty(field_sort), Some(ValueType::Universe { .. })),
        "a field's written sort at its family's universe"
    );
    let operation = entry(&types, span("oper divmod", "divmod"), DescribedRole::Name);
    assert!(matches!(ty(operation), Some(ValueType::Thunk(_))));
    let half = entry(&types, span("oper half", "half"), DescribedRole::Name);
    assert_eq!(
        returned(&arena, half.ty),
        ty(zero),
        "an operation with one output returns its family, not a tuple of it"
    );
    let output = entry(&types, span("quot", "quot"), DescribedRole::Name);
    assert_eq!(ty(output), ty(zero));

    let head = entry(&types, span("rule divmod", "divmod"), DescribedRole::Term);
    assert_eq!(
        ty(head),
        ty(operation),
        "a rule's head at its operation's type"
    );
    let call = entry(
        &types,
        span("divmod(m, Succ(d))", "divmod(m, Succ(d))"),
        DescribedRole::Term,
    );
    assert!(
        matches!(ty(call), Some(ValueType::Product(_))),
        "at the operation's results"
    );
    let pattern = entry(&types, span("(m, Succ", "m"), DescribedRole::Term);
    assert_eq!(ty(pattern), ty(zero), "a variable at its position's sort");
    let nested = entry(&types, span("Succ(d)", "d"), DescribedRole::Term);
    assert_eq!(
        ty(nested),
        ty(zero),
        "under a constructor, at its field's sort"
    );
    let results = entry(&types, span("(Zero, m)", "(Zero, m)"), DescribedRole::Term);
    assert_eq!(ty(results), ty(call), "the right side at the left's sort");
    let used = entry(&types, span(", m)", "m"), DescribedRole::Term);
    assert_eq!(
        ty(used),
        ty(zero),
        "a variable used at the sort it was bound at"
    );
    assert!(
        types
            .entries
            .iter()
            .all(|entry| usize::from(entry.context) == 0)
    );
}

#[test]
fn a_parameterised_constructor_answers_under_its_parameters()
{
    let source = SourceText::from(
        "data Maybe(a : Type) : Type {\n  None : Maybe(a);\n  Some : (x : a) --> Maybe(a);\n}\n",
    );
    let span = |around: &'static str, inner: &'static str| {
        at(source, SourceText::from(around), SourceText::from(inner))
    };
    let (types, arena) = described(source);
    let ty = |entry: DescribedType| arena.value_type(entry.ty).cloned();

    let none = entry(&types, span("None :", "None"), DescribedRole::Name);
    assert!(
        matches!(ty(none), Some(ValueType::Data { ref arguments, .. }) if arguments.len() == 1),
        "a constant at its family applied to its parameter"
    );
    assert_eq!(context(&types, none), ["a"], "under the parameters");
    let some = entry(&types, span("Some :", "Some"), DescribedRole::Name);
    assert!(
        matches!(ty(some), Some(ValueType::Thunk(_))),
        "a constructor over its field"
    );
    assert_eq!(context(&types, some), ["a"]);
    let field = entry(&types, span("(x : a)", "x"), DescribedRole::Name);
    assert!(ty(field).is_some(), "a field at its type");
    let result = entry(
        &types,
        span("--> Maybe(a)", "Maybe(a)"),
        DescribedRole::Type,
    );
    assert!(
        matches!(ty(result), Some(ValueType::Universe { .. })),
        "the result at the family's universe"
    );
    let argument = entry(&types, span("(a);\n}", "a"), DescribedRole::Type);
    assert!(
        matches!(ty(argument), Some(ValueType::Universe { .. })),
        "an argument at its parameter's classifier"
    );
    assert_eq!(
        ty(argument),
        ty(result),
        "`a : Type` and `Maybe(a) : Type` share the family's universe"
    );
}

#[test]
fn a_family_the_native_reading_owns_answers_at_its_signature()
{
    let source = SourceText::from(
        "data Two : Type { L : Two; R : Two; }\ndata Tree : Type {\n  Leaf : Tree;\n  Node : (f : +U (Two -> -F Tree)) --> Tree;\n}\n",
    );
    let span = |around: &'static str, inner: &'static str| {
        at(source, SourceText::from(around), SourceText::from(inner))
    };
    let (types, arena) = described(source);
    let ty = |entry: DescribedType| arena.value_type(entry.ty).cloned();

    let leaf = entry(&types, span("Leaf :", "Leaf"), DescribedRole::Name);
    assert!(
        matches!(ty(leaf), Some(ValueType::Data { ref arguments, .. }) if arguments.is_empty()),
        "a constant at its family"
    );
    let node = entry(&types, span("Node :", "Node"), DescribedRole::Name);
    assert!(
        matches!(ty(node), Some(ValueType::Thunk(_))),
        "a constructor over its function field"
    );
    let field = entry(&types, span("(f :", "f"), DescribedRole::Name);
    assert!(
        matches!(ty(field), Some(ValueType::Thunk(_))),
        "the field at its function type"
    );
    let result = entry(&types, span("--> Tree", "Tree"), DescribedRole::Type);
    assert!(
        matches!(ty(result), Some(ValueType::Universe { .. })),
        "the result at the family's universe"
    );
}
