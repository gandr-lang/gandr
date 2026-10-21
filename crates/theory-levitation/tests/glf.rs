//! The generalized logical framework's first rungs: the first-order model a
//! signature code generates, and one evaluation and readback for every
//! simply-sorted signature.
//!
//! This module holds the representability bit's refusal and the first of the
//! four checks, generation: the fold's output is Kaposi and Xie's
//! single-substitution presentation, rule for rule. The other three checks —
//! identification, both views and the kernel — and the three-signature
//! property are in `model`.

use gandr_theory_levitation::Attrs;
use gandr_theory_levitation::BridgeArity;
use gandr_theory_levitation::DeclPolarity;
use gandr_theory_levitation::FreeTerm;
use gandr_theory_levitation::Name;
use gandr_theory_levitation::NominalId;
use gandr_theory_levitation::NominalSerial;
use gandr_theory_levitation::OperDesc;
use gandr_theory_levitation::ParamDesc;
use gandr_theory_levitation::Representability;
use gandr_theory_levitation::SortDesc;
use gandr_theory_levitation::SortIndex;
use gandr_theory_levitation::SortRef;
use gandr_theory_levitation::TheoryDesc;
use gandr_theory_levitation::TranslationError;
use gandr_theory_levitation::WfKind;
use gandr_theory_levitation::check_desc;
use gandr_theory_levitation::first_order;
use gandr_theory_levitation::serialize_desc;

mod model;

/// A single-output operation fixture.
///
/// # Specification
/// trivial.
fn op(
    name: impl Into<Name>,
    inputs: Vec<SortRef>,
    output: SortRef,
) -> OperDesc
{
    OperDesc::new(
        name,
        BridgeArity::single_output(inputs, output),
        Attrs::empty(),
    )
}

/// A signature fixture: sorts and operations, no source equations.
///
/// # Specification
/// trivial.
fn signature(
    name: impl Into<Name>,
    sorts: Vec<SortDesc>,
    operations: Vec<OperDesc>,
) -> TheoryDesc<()>
{
    TheoryDesc::new(
        NominalId::new(NominalSerial::from(0_u64), name),
        [],
        [],
        operations,
        [],
        DeclPolarity::Data,
        Attrs::empty(),
    )
    .with_sorts(sorts)
}

/// The binding and application signature of pure λ-calculus syntax.
///
/// # Specification
/// trivial.
fn lc() -> TheoryDesc<()>
{
    signature(
        "LC",
        vec![SortDesc::new("Tm", DeclPolarity::Data).representable()],
        vec![
            op(
                "lam",
                vec![SortRef::new("t", "Tm").pi_plus([SortIndex::new("x", "Tm")])],
                SortRef::new("", "Tm"),
            ),
            op(
                "app",
                vec![SortRef::new("t", "Tm"), SortRef::new("u", "Tm")],
                SortRef::new("", "Tm"),
            ),
        ],
    )
}

/// The identity-return signature: value and computation types, values
/// indexed by their type (representable), computations indexed by theirs, and
/// `f`, `arrow`, `ret` and `lam : (VTm a ⇒⁺ CTm b) → CTm (arrow a b)`. Its
/// operations and index binders are lowercase, as a `theory` block writes them,
/// so its rendering reparses.
///
/// # Specification
/// trivial.
fn identity_return() -> TheoryDesc<()>
{
    let a = FreeTerm::var("a");
    let b = FreeTerm::var("b");
    signature(
        "IdentityReturn",
        vec![
            SortDesc::new("VTy", DeclPolarity::Data),
            SortDesc::new("CTy", DeclPolarity::Data),
            SortDesc::family("VTm", DeclPolarity::Data, [SortIndex::new("a", "VTy")])
                .representable(),
            SortDesc::family("CTm", DeclPolarity::Data, [SortIndex::new("b", "CTy")]),
        ],
        vec![
            op("f", vec![SortRef::new("a", "VTy")], SortRef::new("", "CTy")),
            op(
                "arrow",
                vec![SortRef::new("a", "VTy"), SortRef::new("b", "CTy")],
                SortRef::new("", "CTy"),
            ),
            op(
                "ret",
                vec![
                    SortRef::new("a", "VTy"),
                    SortRef::new("t", "VTm").applied([a.clone()]),
                ],
                SortRef::new("", "CTm").applied([FreeTerm::op("f", [a.clone()])]),
            ),
            op(
                "lam",
                vec![
                    SortRef::new("a", "VTy"),
                    SortRef::new("b", "CTy"),
                    SortRef::new("t", "CTm")
                        .applied([b.clone()])
                        .pi_plus([SortIndex::new("x", "VTm").applied([a.clone()])]),
                ],
                SortRef::new("", "CTm").applied([FreeTerm::op("arrow", [a, b])]),
            ),
        ],
    )
}

#[test]
fn restricted_binding_requires_representability()
{
    let mut source = lc();
    assert_eq!(check_desc(&source), []);
    assert!(
        serialize_desc(&source)
            .as_ref()
            .contains("t : pi+ (x : Tm) . Tm")
    );
    // An ordinary domain: one refusal, by name, for the one binder.
    source.sorts[0].representability = Representability::Ordinary;
    let kinds: Vec<WfKind> = check_desc(&source)
        .iter()
        .map(|diagnostic| diagnostic.kind)
        .collect();
    assert_eq!(kinds, [WfKind::NonRepresentableBinder]);
    // An undeclared domain is refused by the same name.
    source.sorts[0].representability = Representability::Representable;
    source.opers[0].arity.inputs[0].bindings[0].sort = Name::from("Absent");
    let kinds: Vec<WfKind> = check_desc(&source)
        .iter()
        .map(|diagnostic| diagnostic.kind)
        .collect();
    assert_eq!(kinds, [WfKind::NonRepresentableBinder]);
    // Every offending binder is reported, not only the first.
    let mut twice = lc();
    twice.sorts[0].representability = Representability::Ordinary;
    twice.opers[1].arity.inputs[1] =
        SortRef::new("u", "Tm").pi_plus([SortIndex::new("y", "Tm"), SortIndex::new("z", "Tm")]);
    // A telescope renders outermost binder first.
    assert!(
        serialize_desc(&twice)
            .as_ref()
            .contains("u : pi+ (y : Tm) . pi+ (z : Tm) . Tm")
    );
    let kinds: Vec<WfKind> = check_desc(&twice)
        .iter()
        .map(|diagnostic| diagnostic.kind)
        .collect();
    assert_eq!(kinds, [WfKind::NonRepresentableBinder; 3]);
}

#[test]
fn generation()
{
    // The single-substitution presentation of pure λ-calculus, derived from
    // Kaposi and Xie's Definitions 3–4 by the §6 translation with §7's
    // replacement of parallel substitution by single substitution and lifting:
    // contexts and q/p stay, the four index laws are vacuous for the unindexed
    // `Tm`, and naturality lifts `lam`'s substitution once. β belongs to the
    // source theory, not its binding signature. Three sorts, nine operations,
    // six equations.
    let expected = r#"theory LC$ssc {
        sort $Con : Type;
        sort $Sub(D : $Con, G : $Con) : Type;
        sort Tm(G : $Con) : Type;
        oper $empty : () --> $Con;
        oper $sub_Tm : (G : $Con, D : $Con, t : Tm(G), s : $Sub(D, G)) --> Tm(D);
        oper $extend_Tm : (G : $Con) --> $Con;
        oper $p_Tm : (G : $Con) --> $Sub($extend_Tm(G), G);
        oper $q_Tm : (G : $Con) --> Tm($extend_Tm(G));
        oper $single_Tm : (G : $Con, a : Tm(G)) --> $Sub(G, $extend_Tm(G));
        oper $lift_Tm : (G : $Con, D : $Con, s : $Sub(D, G)) --> $Sub($extend_Tm(D), $extend_Tm(G));
        oper lam : (G : $Con, t : Tm($extend_Tm(G))) --> Tm(G);
        oper app : (G : $Con, t : Tm(G), u : Tm(G)) --> Tm(G);
        rule $sub_Tm($q_Tm, $single_Tm(b)) ==> b;
        rule $sub_Tm($q_Tm, $lift_Tm(s)) ==> $q_Tm;
        rule $sub_Tm($sub_Tm(b, $p_Tm), $lift_Tm(s)) ==> $sub_Tm($sub_Tm(b, s), $p_Tm);
        rule $sub_Tm($sub_Tm(b, $p_Tm), $single_Tm(a)) ==> b;
        rule $sub_Tm(lam(t), s) ==> lam($sub_Tm(t, $lift_Tm(s)));
        rule $sub_Tm(app(t, u), s) ==> app($sub_Tm(t, s), $sub_Tm(u, s)); }"#;
    let model = first_order(&lc()).expect("LC is a finitary signature");
    assert_eq!(
        serialize_desc(&model).as_ref(),
        expected.split_whitespace().collect::<Vec<_>>().join(" ")
    );
    assert_eq!(
        (model.sorts.len(), model.opers.len(), model.rules.len()),
        (3, 9, 6)
    );
    assert_eq!(check_desc(&model), []);
    // §7 prints the eight single-substitution laws for dependent types and
    // terms (`Σ U λTy. Ty ⇒ U⁺`, p. 10:18), not a λ-calculus table: four term
    // laws for `Tm`, then four index laws for the `Ty` that indexes it.
    let source = signature(
        "Dependent",
        vec![
            SortDesc::new("Ty", DeclPolarity::Data),
            SortDesc::family("Tm", DeclPolarity::Data, [SortIndex::new("A", "Ty")]).representable(),
        ],
        vec![],
    );
    let model = first_order(&source).expect("dependent family translates");
    let equations: Vec<String> = model
        .rules
        .iter()
        .map(|rule| format!("{} = {}", rule.lhs, rule.rhs))
        .collect();
    assert_eq!(equations, [
        "$sub_Tm($q_Tm, $single_Tm(b)) = b",
        "$sub_Tm($q_Tm, $lift_Tm(s)) = $q_Tm",
        "$sub_Tm($sub_Tm(b, $p_Tm), $lift_Tm(s)) = $sub_Tm($sub_Tm(b, s), $p_Tm)",
        "$sub_Tm($sub_Tm(b, $p_Tm), $single_Tm(a)) = b",
        "$sub_Ty($sub_Ty(A, $p_Tm), $lift_Tm(s)) = $sub_Ty($sub_Ty(A, s), $p_Tm)",
        "$sub_Ty($sub_Ty(A, $p_Tm), $single_Tm(b)) = A",
        "$sub_Ty($sub_Ty(A, $single_Tm(b)), s) = $sub_Ty($sub_Ty(A, $lift_Tm(s)), $single_Tm($sub_Tm(b, s)))",
        "$sub_Ty($sub_Ty(A, $lift_Tm($p_Tm)), $single_Tm($q_Tm)) = A",
    ]);
    assert_eq!(check_desc(&model), []);
}

#[test]
fn indexed_signature_translates_without_name_cases()
{
    let model = first_order(&identity_return()).expect("identity-return translates");
    assert_eq!(check_desc(&model), []);
    let lam = model
        .opers
        .iter()
        .find(|operation| operation.name.as_ref() == "lam")
        .expect("lambda operation");
    let body = &lam.arity.inputs[3];
    assert_eq!(
        body.arguments
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>(),
        [
            "$extend_VTm(G, a)",
            "$sub_CTy(G, $extend_VTm(G, a), b, $p_VTm(G, a))",
        ]
    );
    assert!(body.bindings.is_empty());
    // Only the representable family gets variables.
    assert!(
        !model
            .opers
            .iter()
            .any(|operation| operation.name.as_ref() == "$q_CTm")
    );
    let renamed = signature(
        "Renamed",
        vec![SortDesc::new("Expression", DeclPolarity::Data).representable()],
        vec![op(
            "abstract",
            vec![SortRef::new("body", "Expression").pi_plus([
                SortIndex::new("outer", "Expression"),
                SortIndex::new("inner", "Expression"),
            ])],
            SortRef::new("", "Expression"),
        )],
    );
    let renamed = first_order(&renamed).expect("names do not select translation cases");
    assert_eq!(
        renamed.rules.last().expect("naturality").rhs.to_string(),
        "abstract($sub_Expression(body, $lift_Expression($lift_Expression(s))))"
    );
}

#[test]
fn translation_refuses_non_signatures()
{
    let mut source = lc();
    source.sorts[0].representability = Representability::Ordinary;
    let diagnostics = check_desc(&source);
    assert_eq!(
        first_order(&source),
        Err(TranslationError::Malformed(diagnostics))
    );
    // A well-formed description with constructors is data, not an operation
    // signature.
    assert_eq!(
        first_order(&gandr_theory_levitation::bool_desc::<()>()),
        Err(TranslationError::NonSignatureMembers)
    );
    let reserved = signature(
        "Reserved",
        vec![SortDesc::new("$Con", DeclPolarity::Data)],
        vec![],
    );
    assert_eq!(
        first_order(&reserved),
        Err(TranslationError::ReservedName(Name::from("$Con")))
    );
    let unknown = signature(
        "Unknown",
        vec![SortDesc::family("Tm", DeclPolarity::Data, [
            SortIndex::new("A", "Missing"),
        ])],
        vec![],
    );
    assert_eq!(
        first_order(&unknown),
        Err(TranslationError::UnknownIndexSort(Name::from("Missing")))
    );
    // Each product condition refused alone, on well-formed arities of `app`.
    let mut outputs = lc();
    outputs.opers[1].arity.outputs = Box::from([SortRef::new("v", "Tm"), SortRef::new("w", "Tm")]);
    let mut monomials = lc();
    monomials.opers[1].arity.factors = Box::from([1_u32, 1]);
    monomials.opers[1].arity.dest = Box::from([0_u32, 0]);
    let mut reindexed = lc();
    reindexed.opers[1].arity.source = Box::from([1_u32, 0]);
    for nonproduct in [outputs, monomials, reindexed] {
        assert_eq!(check_desc(&nonproduct), []);
        assert_eq!(
            first_order(&nonproduct),
            Err(TranslationError::NonProductOperation(Name::from("app")))
        );
    }
    // A parameter alone is a non-signature member too.
    let mut parameterised = lc();
    parameterised.params = Box::from([ParamDesc::new("a", (), Attrs::empty())]);
    assert_eq!(check_desc(&parameterised), []);
    assert_eq!(
        first_order(&parameterised),
        Err(TranslationError::NonSignatureMembers)
    );
    // A port abstracting an atom has no context extension in the model.
    let mut abstracting = lc();
    abstracting.sorts = Box::from([abstracting.sorts[0].clone(), SortDesc {
        representability: Representability::Atom,
        ..SortDesc::new("Name", DeclPolarity::Data)
    }]);
    abstracting.opers[1].arity.inputs[0] =
        SortRef::new("t", "Tm").abstracting([SortIndex::new("a", "Name")]);
    assert_eq!(check_desc(&abstracting), []);
    assert_eq!(
        first_order(&abstracting),
        Err(TranslationError::AtomAbstraction(Name::from("app")))
    );
}
