//! Each described node at the role and the type its member states.

use alloc::string::String;
use alloc::vec::Vec;

use gandr_core_term::CompType;
use gandr_core_term::CoreArena;
use gandr_core_term::Sort;
use gandr_core_term::ValueType;
use gandr_kernel_term::GroundSort;
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
fn a_stated_law_answers_at_its_statement_2356()
{
    let source = SourceText::from(
        "theory Decision {\n  sort C : Type;\n  oper eq : (a : C, b : C) --> Bool;\n  law refl \
         : (a : C) => Path(Bool, eq(a, a), true);\n  law flip : (a : C, b : C, p : Path(Bool, \
         eq(a, b), true)) => Path(Bool, eq(b, a), true);\n}\n",
    );
    let span = |around: &'static str, inner: &'static str| {
        at(source, SourceText::from(around), SourceText::from(inner))
    };
    let (types, arena) = described(source);
    let ty = |entry: DescribedType| arena.value_type(entry.ty).cloned();

    let refl = entry(&types, span("law refl", "refl"), DescribedRole::Name);
    assert!(
        matches!(returned(&arena, refl.ty), Some(ValueType::Path { .. })),
        "a law's name at the function into the path it concludes"
    );
    assert_eq!(context(&types, refl), ["C", "eq"]);
    let statement = "(a : C) => Path(Bool, eq(a, a), true)";
    let written = entry(&types, span("law refl", statement), DescribedRole::Type);
    assert!(matches!(ty(written), Some(ValueType::Universe { .. })));
    let binder = entry(&types, span("(a : C) =>", "a"), DescribedRole::Name);
    assert!(
        matches!(ty(binder), Some(ValueType::Element { .. })),
        "a binder at its sort"
    );
    // `Bool`, the sum of two units, by shape: the arena keeps each minting.
    let boolean = |entry: DescribedType| {
        match ty(entry) {
        Some(ValueType::Sum(summands)) => {
            summands.len() == 2
                && summands.iter().all(|&summand| {
                    matches!(arena.value_type(summand), Some(ValueType::Product(units)) if units.is_empty())
                })
        },
        _ => false,
    }
    };
    let applied = entry(&types, span("law refl", "eq(a, a)"), DescribedRole::Term);
    assert!(boolean(applied), "an application at the operation's result");
    let literal = entry(&types, span("law refl", "true"), DescribedRole::Term);
    assert!(boolean(literal), "the literal at the path's carrier");
    let carrier = entry(&types, span("law refl", "Bool"), DescribedRole::Type);
    assert!(matches!(ty(carrier), Some(ValueType::Universe { .. })));

    let hypothesis = entry(&types, span("C, p : Path", "p"), DescribedRole::Name);
    assert!(
        matches!(ty(hypothesis), Some(ValueType::Path { .. })),
        "a hypothesis at the path it assumes"
    );
    assert_eq!(context(&types, hypothesis), ["C", "eq", "a", "b"]);
    let assumed = entry(&types, span("p : ", "eq(a, b)"), DescribedRole::Term);
    assert!(boolean(assumed), "a hypothesis's side at its sort");
}

/// A port that binds a variable answers at the thunked function from it, as
/// `Model(S)` states the operation's component, and its variable at its sort.
#[test]
fn a_binding_port_answers_at_the_function_from_its_variables_765()
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
    let port = entry(&types, span("t : pi+", "t"), DescribedRole::Name);
    let Some(ValueType::Thunk(function)) = ty(port)
    else {
        panic!("the bound port at a thunk: {:?}", ty(port));
    };
    assert!(
        matches!(
            arena.comp_type(function).cloned(),
            Some(CompType::Arrow { .. })
        ),
        "the function from its variable, which its sort does not name"
    );
    assert_eq!(
        context(&types, port),
        ["VTy", "CTy", "VTm", "CTm", "f", "arrow", "ret", "a", "b"],
        "under the members and the ports before it"
    );
    let operation = entry(&types, span("oper lam", "lam"), DescribedRole::Name);
    assert!(
        matches!(ty(operation), Some(ValueType::Thunk(_))),
        "the operation at the type its component states"
    );
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

/// A rule a `derive` declaration states over a theory answers as the theory's
/// own rules do: each application and variable of either side at the sort
/// the theory writes, and each operation applied at its type.
#[test]
fn a_derived_rule_answers_each_side_node_at_its_sort()
{
    let source = SourceText::from(
        "theory Grp {\n  sort G : Type;\n  oper e : G;\n  oper inv : (x : G) --> G;\n  oper mul \
         : (x : G, y : G) --> G;\n  rule unitL : mul(e(), x) <=> x;\n  rule assoc : mul(mul(x, \
         y), z) <=> mul(x, mul(y, z));\n  rule invL : mul(inv(x), x) <=> e();\n}\nderive invMul \
         : inv(mul(x, y)) <=> mul(inv(y), inv(x)) in Grp\n",
    );
    let span = |around: &'static str, inner: &'static str| {
        at(source, SourceText::from(around), SourceText::from(inner))
    };
    let (types, arena) = described(source);
    let code = |entry: DescribedType| match arena.value_type(entry.ty) {
        Some(&ValueType::Element { code, .. }) => arena.value(code).cloned(),
        _ => None,
    };
    let left = entry(
        &types,
        span("invMul : ", "inv(mul(x, y))"),
        DescribedRole::Term,
    );
    assert!(code(left).is_some(), "the left side at its sort");
    for (around, inner) in [
        ("inv(mul(x, y))", "mul(x, y)"),
        ("inv(mul(x, y))", "x"),
        ("<=> mul(inv(y)", "mul(inv(y), inv(x))"),
        ("<=> mul(inv(y)", "inv(y)"),
        ("inv(x)) in", "x"),
    ] {
        assert_eq!(
            code(entry(&types, span(around, inner), DescribedRole::Term)),
            code(left),
            "`{inner}` in `{around}` at the group's one sort"
        );
    }
    let applied = entry(&types, span(": inv(mul(x, y))", "inv"), DescribedRole::Term);
    let declared = entry(&types, span("oper inv", "inv"), DescribedRole::Name);
    assert_eq!(applied.ty, declared.ty, "a head at its operation's type");
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
fn an_indexed_family_s_operation_answers_at_its_index_2940()
{
    let source = SourceText::from(
        "data N : Type {\n  Z : N;\n  S : (n : N) --> N;\n}\ndata Skip : N -> Type {\n  Halt : \
         Skip(Z);\n  oper skip(k : Skip(Z)) -> Skip(Z);\n  oper climb(c : Skip(Z)) -> \
         Skip(S(Z));\n  rule skip(k) ==> k;\n}\n",
    );
    let span = |around: &'static str, inner: &'static str| {
        at(source, SourceText::from(around), SourceText::from(inner))
    };
    let (types, arena) = described(source);
    let ty = |entry: DescribedType| arena.value_type(entry.ty).cloned();
    let constructor = |value| match arena.value(value) {
        Some(&gandr_core_term::Value::Constructor {
            tag, ref fields, ..
        }) => Some((usize::from(tag), fields.clone())),
        Some(_) | None => None,
    };
    let natural = ty(entry(&types, span("Z :", "Z"), DescribedRole::Name));

    let port = entry(&types, span("(k :", "k"), DescribedRole::Name);
    let Some(ValueType::Data { ref arguments, .. }) = ty(port)
    else {
        panic!("a port answers at its family");
    };
    let [index] = **arguments
    else {
        panic!("the family at its one index");
    };
    assert_eq!(
        constructor(index),
        Some((0_usize, Vec::new())),
        "the index the port writes, `Z`"
    );
    let written = entry(&types, span("skip(k : Skip(Z)", "Z"), DescribedRole::Term);
    assert_eq!(ty(written), natural, "the index term at its own family");
    let sort = entry(
        &types,
        span("skip(k : Skip(Z)", "Skip(Z)"),
        DescribedRole::Type,
    );
    assert!(
        matches!(ty(sort), Some(ValueType::Universe { .. })),
        "the port's sort at its universe"
    );

    let climb = entry(&types, span("oper climb", "climb"), DescribedRole::Name);
    let Some(ValueType::Data { ref arguments, .. }) = returned(&arena, climb.ty)
    else {
        panic!("the operation returns its family");
    };
    let [index] = **arguments
    else {
        panic!("the family at its one index");
    };
    let Some((1_usize, ref fields)) = constructor(index)
    else {
        panic!("the result's index is `S` applied");
    };
    let [field] = **fields
    else {
        panic!("`S` takes one field");
    };
    assert_eq!(constructor(field), Some((0_usize, Vec::new())), "`S(Z)`");
    let applied = entry(&types, span("Skip(S(Z))", "S(Z)"), DescribedRole::Term);
    assert_eq!(ty(applied), natural, "a nested index term at its family");

    let operation = entry(&types, span("oper skip", "skip"), DescribedRole::Name);
    let head = entry(&types, span("rule skip", "skip"), DescribedRole::Term);
    assert_eq!(ty(head), ty(operation), "the rule's head at the operation");
    // Each port mints its own index values, so a family is compared by the
    // constructors its index values are.
    let at_index = |entry: DescribedType| match ty(entry) {
        Some(ValueType::Data {
            declaration,
            ref arguments,
        }) => Some((
            declaration,
            arguments
                .iter()
                .map(|&argument| constructor(argument))
                .collect::<Vec<_>>(),
        )),
        Some(_) | None => None,
    };
    let call = entry(&types, span("rule skip", "skip(k)"), DescribedRole::Term);
    assert_eq!(
        at_index(call),
        at_index(port),
        "the call at the family at its index"
    );
    let result = entry(&types, span("==> k", "k"), DescribedRole::Term);
    assert_eq!(
        at_index(result),
        at_index(port),
        "the rule's right side at its sort"
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

#[test]
fn a_codata_observation_s_type_answers_at_its_universe()
{
    let source = SourceText::from(
        "codata Stream(a : Type) : Type[-] {\n  head : a;\n  tail : Stream(a);\n}\ncodata Spot : Type[-] {\n  x : Integer;\n  depth : Integer;\n}\n",
    );
    let span = |around: &'static str, inner: &'static str| {
        at(source, SourceText::from(around), SourceText::from(inner))
    };
    let (types, arena) = described(source);
    let ty = |entry: DescribedType| arena.value_type(entry.ty).cloned();
    let value = |ty: Option<ValueType>| {
        matches!(
            ty,
            Some(ValueType::Universe {
                sort: Sort::Ground(GroundSort::Value),
                ..
            })
        )
    };

    let head = entry(&types, span(": a;", "a"), DescribedRole::Type);
    assert!(value(ty(head)), "a parameter read as a type at `Type`");
    assert_eq!(context(&types, head), ["a"], "under the parameters");
    let tail = entry(
        &types,
        span("tail : Stream(a)", "Stream(a)"),
        DescribedRole::Type,
    );
    assert!(
        matches!(
            ty(tail),
            Some(ValueType::Universe {
                sort: Sort::Ground(GroundSort::Computation),
                ..
            })
        ),
        "the family itself at its kind, `Type[-]`"
    );
    let argument = entry(&types, span("(a);", "a"), DescribedRole::Type);
    assert_eq!(
        ty(argument),
        ty(head),
        "the family's argument at its parameter's classifier"
    );
    let integer = entry(&types, span("x : Integer", "Integer"), DescribedRole::Type);
    assert!(value(ty(integer)), "a base type at `Type`");
    assert_eq!(context(&types, integer), Vec::<String>::new());
}

/// A law relating a term at a binding port, which no `Model(S)` component
/// states, answers each node at the sort the theory writes for it: the
/// application, the variable at a first-order port and the instantiation at
/// `Tm`; the operation's head at the type its component states; the variable
/// the binding port binds answers nowhere, as no field of it is written.
#[test]
fn a_second_order_law_answers_at_its_written_sorts()
{
    let source = SourceText::from(
        "theory Let {\n  sort Tm : Type+;\n  oper let : (u : Tm, t : pi+ (x : Tm) . Tm) --> \
         Tm;\n  rule zeta : let(u, t) <=> t(u);\n}\n",
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
        span("zeta : let(u, t)", "let(u, t)"),
        DescribedRole::Term,
    );
    assert!(code(applied).is_some(), "an application at its sort");
    for (around, inner) in [("let(u,", "u"), ("<=> t(u)", "t(u)"), ("t(u);", "u")] {
        assert_eq!(
            code(entry(&types, span(around, inner), DescribedRole::Term)),
            code(applied),
            "`{inner}` in `{around}` at the same sort"
        );
    }
    let head = entry(&types, span("zeta : let", "let"), DescribedRole::Term);
    let declared = entry(&types, span("oper let", "let"), DescribedRole::Name);
    assert_eq!(head.ty, declared.ty, "a head at its operation's type");
    for unstated in [span("u, t)", "t"), span("<=> t(u)", "t")] {
        assert!(
            types.entries.iter().all(|held| held.span != unstated),
            "the variable a binding port binds, written without its field, answers nowhere"
        );
    }
}

/// A law over an abstracting port answers the variable its abstraction holds
/// at the port's sort, on both sides, as a first-order port's variable
/// answers, and the atom it abstracts at the atom sort the port abstracts;
/// the abstraction itself answers nowhere, as its port does, whose declared
/// atom answers at that atom sort.
#[test]
fn a_variable_under_an_abstraction_answers_at_its_port()
{
    let source = SourceText::from(
        "theory Scope {\n  sort Name : Atom;\n  sort Proc : Type;\n  oper par : (p : Proc, q : \
         Proc) --> Proc;\n  oper nu : (p : bind (a : Name) . Proc) --> Proc;\n  rule scope : \
         par(nu(bind a . p), q) <=> nu(bind a . par(p, q));\n}\n",
    );
    let span = |around: &'static str, inner: &'static str| {
        at(source, SourceText::from(around), SourceText::from(inner))
    };
    let (types, arena) = described(source);
    let code = |entry: DescribedType| match arena.value_type(entry.ty) {
        Some(&ValueType::Element { code, .. }) => arena.value(code).cloned(),
        _ => None,
    };
    let process = code(entry(&types, span(", q)", "q"), DescribedRole::Term));
    assert!(
        process.is_some(),
        "a first-order variable at its port's sort"
    );
    for around in [". p)", "(p, q))"] {
        assert_eq!(
            code(entry(&types, span(around, "p"), DescribedRole::Term)),
            process,
            "`p` in `{around}` at the abstracting port's sort"
        );
    }
    let [left, right] = ["(bind a . p)", "nu(bind a . par"]
        .map(|around| code(entry(&types, span(around, "a"), DescribedRole::Name)));
    assert!(left.is_some(), "an abstraction's atom answers");
    assert_eq!(left, right, "both sides' atoms at the port's one atom sort");
    assert_ne!(left, process, "an atom at the atom sort, not the body's");
    let abstraction = span("nu(bind a . p)", "bind a . p");
    assert!(
        types.entries.iter().all(|held| held.span != abstraction),
        "an abstraction answers nowhere"
    );
    let declared = entry(&types, span("bind (a :", "a"), DescribedRole::Name);
    assert!(
        code(declared).is_some(),
        "the port's declared atom at its atom sort"
    );
    assert_eq!(
        context(&types, declared),
        ["Name", "Proc", "par"],
        "under the members before its operation"
    );
    let port = span("(p : bind", "p");
    assert!(
        types.entries.iter().all(|held| held.span != port),
        "an abstracting port's name answers nowhere"
    );
}

/// An atom named inside the abstraction that binds it answers at the sort of
/// the port it stands at, the atom sort its abstraction abstracts.
#[test]
fn an_occurrence_answers_at_its_port()
{
    let source = SourceText::from(
        "theory Unheard {\n  sort Name : Atom;\n  sort Proc : Type;\n  oper nil : () --> Proc;\n  \
         oper out : (c : Name, p : Proc) --> Proc;\n  oper nu : (p : bind (a : Name) . Proc) \
         --> Proc;\n  rule unheard : nu(bind a . out(a, p)) ==> nil();\n}\n",
    );
    let span = |around: &'static str, inner: &'static str| {
        at(source, SourceText::from(around), SourceText::from(inner))
    };
    let (types, arena) = described(source);
    let code = |entry: DescribedType| match arena.value_type(entry.ty) {
        Some(&ValueType::Element { code, .. }) => arena.value(code).cloned(),
        _ => None,
    };
    let [binder, occurrence] = ["bind a .", "out(a,"]
        .map(|around| code(entry(&types, span(around, "a"), DescribedRole::Name)));
    assert!(occurrence.is_some(), "the occurrence answers");
    assert_eq!(
        occurrence, binder,
        "at the atom sort its abstraction abstracts"
    );
    assert_ne!(
        occurrence,
        code(entry(&types, span(", p)", "p"), DescribedRole::Term)),
        "not at the process sort beside it"
    );
}

/// #2360: a law over fields answers each node inside them. An instantiation
/// whose variable no side writes bare answers at the sort of the port it
/// stands at; each field's variable, where `bind` names it and where an
/// instantiation takes it, at the representable sort its port binds; and a
/// variable written under a field without taking it, `q` in `new(bind x .
/// q)`, at the port's sort, as a first-order variable.
#[test]
fn a_field_s_variable_and_an_instantiation_under_it_answer_2360()
{
    let source = SourceText::from(
        "theory Commute {\n  sort Value : Type;\n  sort Name : Type;\n  sort Digest : Type+;\n  \
         sort Claim : Type+;\n  sort C : Type;\n  oper put : (v : Value, k : pi+ (d : Digest) . \
         C) --> C;\n  oper lookup : (n : Name, k : pi+ (c : Claim) . C) --> C;\n  oper new : \
         (body : pi+ (x : Digest) . C) --> C;\n  rule commute : put(v, bind d . lookup(n, bind \
         c . k(d, c))) <=> lookup(n, bind c . put(v, bind d . k(d, c)));\n  rule gc : new(bind \
         x . q) <=> q;\n}\n",
    );
    let span = |around: &'static str, inner: &'static str| {
        at(source, SourceText::from(around), SourceText::from(inner))
    };
    let (types, arena) = described(source);
    let code = |entry: DescribedType| match arena.value_type(entry.ty) {
        Some(&ValueType::Element { code, .. }) => arena.value(code).cloned(),
        _ => None,
    };
    let carrier = code(entry(
        &types,
        span(
            "commute : put",
            "put(v, bind d . lookup(n, bind c . k(d, c)))",
        ),
        DescribedRole::Term,
    ));
    assert!(carrier.is_some(), "the application answers at `C`");
    for around in ["c . k(d, c))) <=>", "d . k(d, c)));"] {
        assert_eq!(
            code(entry(&types, span(around, "k(d, c)"), DescribedRole::Term)),
            carrier,
            "`k(d, c)` in `{around}` at the port's `C`"
        );
    }
    let [digest, claim] = ["d", "c"].map(|bound| {
        code(entry(
            &types,
            span("k(d, c))) <=>", bound),
            DescribedRole::Name,
        ))
    });
    assert!(digest.is_some(), "a field's variable answers");
    assert_ne!(digest, claim, "each at its own port's sort");
    assert_ne!(digest, carrier, "at the sort it binds, not the body's");
    for (around, bound, sort) in [
        (" d . lookup", "d", &digest),
        (" c . k(d, c))) <=>", "c", &claim),
        ("k(d, c)));", "d", &digest),
        ("k(d, c)));", "c", &claim),
    ] {
        assert_eq!(
            &code(entry(&types, span(around, bound), DescribedRole::Name)),
            sort,
            "`{bound}` in `{around}` at the sort its port binds"
        );
    }
    for around in ["x . q)", "<=> q;"] {
        assert_eq!(
            code(entry(&types, span(around, "q"), DescribedRole::Term)),
            carrier,
            "`q` in `{around}` at the field's `C`"
        );
    }
}

/// Substitution rebuilds every node kind a rule term holds and replaces
/// only the variables the map names, keeping the rest and every atom.
#[test]
fn substitution_rebuilds_every_node_and_replaces_only_mapped_variables()
{
    use alloc::collections::BTreeMap;

    use gandr_theory_levitation::FreeTerm;
    use gandr_theory_levitation::Name;

    let written = |x: &str| {
        FreeTerm::op("f", [
            FreeTerm::ctor("C", [FreeTerm::var(x), FreeTerm::var("y")]),
            FreeTerm::results([FreeTerm::var(x)]),
            FreeTerm::inst("t", [FreeTerm::var(x)]),
            FreeTerm::abs(
                "a",
                FreeTerm::op("g", [FreeTerm::var(x), FreeTerm::var("a")]),
            ),
        ])
    };
    let x = Name::from("x");
    let by = BTreeMap::from([(&x, FreeTerm::var("z"))]);
    assert!(
        super::substitute(&written("x"), &by) == written("z"),
        "every `x` under every node kind reads `z`; `y` and the atom stay"
    );
    assert!(
        super::substitute(&written("x"), &BTreeMap::new()) == written("x"),
        "an empty map leaves the term as written"
    );
}
