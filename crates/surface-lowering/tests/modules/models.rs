//! Modules ascribed the model signature a theory derives, `: Model(S)`, and
//! type families, lowered: each derived component asserted against the
//! signature a module writes out by hand, and each component a module does
//! not supply refused by name.

use gandr_core_term::CertificateEquality;
use gandr_core_term::equal_type_syntax;
use gandr_surface_lowering::FragmentBoundary;
use gandr_surface_lowering::FragmentSort;
use gandr_surface_lowering::LoweringRefusal;
use gandr_surface_lowering::OperandCount;
use gandr_surface_lowering::TelescopeFault;
use gandr_surface_lowering::model::ModelFault;

use super::Amounts;
use super::Judgement;
use super::Role;
use super::declared_type_of;
use super::lower;
use super::name;
use super::row;
use super::rows;
use super::span_of;
use super::verdicts;

/// The `CatShape` theory: a category's objects, morphisms, identities,
/// composition and its three laws.
const SIGN: &str = "theory CatShape {\n  sort Ob : Type;\n  sort Hom(dom: Ob, cod: Ob) : Type;\n  oper id : (a : Ob) --> Hom(a, a);\n  oper comp : (f : Hom(a, b), g : Hom(b, c)) --> Hom(a, c);\n  rule unitL : comp(id(a), f) ==> f;\n  rule unitR : comp(f, id(b)) ==> f;\n  rule assoc : comp(comp(f, g), h) ==> comp(f, comp(g, h));\n}\n";

/// The category of discrete setoids: types and functions, composition by
/// sequencing, each law holding by computation.
const SETOIDS: &str = "type Ob = Type;\n  type Hom(a : Ob, b : Ob) = +U[ω] (a -> -F b);\n  def ident(t : Type, x : t) -> -F t { return x }\n  def compose(t : Type, u : Type, v : Type, f : +U[ω] (t -> -F u), g : +U[ω] (u -> -F v), x : t) -> -F v {\n    run y <- f(x);\n    become g(y)\n  }\n  def id(t : Type) -> -F (+U[ω] (t -> -F t)) { return thunk { become ident(t) } }\n  def comp(t : Type, u : Type, v : Type, f : +U[ω] (t -> -F u), g : +U[ω] (u -> -F v)) -> -F (+U[ω] (t -> -F v)) {\n    return thunk { become compose(t, u, v, f, g) }\n  }\n  def unitL(p : Type, q : Type, f : +U[ω] (p -> -F q)) -> -F Path((+U[ω] (p -> -F q)), comp(p, p, q, id(p), f), f) { return here(f) }\n  def unitR(p : Type, q : Type, f : +U[ω] (p -> -F q)) -> -F Path((+U[ω] (p -> -F q)), comp(p, q, q, f, id(q)), f) { return here(f) }\n  def assoc(p : Type, q : Type, r : Type, s : Type, f : +U[ω] (p -> -F q), g : +U[ω] (q -> -F r), h : +U[ω] (r -> -F s)) -> -F Path((+U[ω] (p -> -F s)), comp(p, r, s, comp(p, q, r, f, g), h), comp(p, q, s, f, comp(q, r, s, g, h))) {\n    return here(thunk { become compose(p, q, s, f, thunk { become compose(q, r, s, g, h) }) })\n  }\n";

/// The signature `Model(CatShape)` derives, written out by hand, its laws
/// stated over the operations of the module `Derived` so the two signatures
/// name the same constants.
const WRITTEN: &str = "#{ type Ob : Type[+, 1], type Hom : (a : Ob, b : Ob) => Type, id : (a : Ob) => Hom(a, a), comp : (a : Ob, b : Ob, c : Ob, f : Hom(a, b), g : Hom(b, c)) => Hom(a, c), unitL : (a : Ob, b : Ob, f : Hom(a, b)) => Path(Hom(a, b), Derived.comp(a, a, b, Derived.id(a), f), f), unitR : (a : Ob, b : Ob, f : Hom(a, b)) => Path(Hom(a, b), Derived.comp(a, b, b, f, Derived.id(b)), f), assoc : (a : Ob, b : Ob, c : Ob, d : Ob, f : Hom(a, b), g : Hom(b, c), h : Hom(c, d)) => Path(Hom(a, d), Derived.comp(a, c, d, Derived.comp(a, b, c, f, g), h), Derived.comp(a, b, d, f, Derived.comp(b, c, d, g, h))) }";

#[test]
fn a_derived_signature_states_what_the_written_one_does()
{
    let over_derived = SETOIDS
        .replace("comp(p", "Derived.comp(p")
        .replace("comp(q", "Derived.comp(q")
        .replace("id(p)", "Derived.id(p)")
        .replace("id(q)", "Derived.id(q)");
    let source = format!(
        "{SIGN}module Derived : Model(CatShape) {{\n  {SETOIDS}}}\nmodule Written : {WRITTEN} \
         {{\n  {over_derived}}}\n"
    );
    let mut lowered = lower(source.as_str());
    for component in ["id", "comp", "unitL", "unitR", "assoc"] {
        let derived = declared_type_of(&lowered, format!("Derived.{component}"), Role::Declared);
        let written = declared_type_of(&lowered, format!("Written.{component}"), Role::Declared);
        assert_eq!(
            equal_type_syntax(&lowered.arena, derived, written),
            CertificateEquality::Equal,
            "the derived `{component}` is the written one, node for node"
        );
    }
    let judgements = verdicts(&mut lowered);
    assert!(
        judgements
            .iter()
            .all(|&(_, judgement)| matches!(judgement, Judgement::Checked)),
        "and the setoid category checks at both, each law by computation: {judgements:?}"
    );
}

#[test]
fn a_lowered_theory_exposes_its_description_and_its_model()
{
    let source = format!(
        "data Flag : Type {{ Off : Flag; On : Flag; }}\n{SIGN}module Setoids : Model(CatShape) \
         {{\n  {SETOIDS}}}\n"
    );
    let lowered = lower(source.as_str());
    let theories: Vec<_> = lowered.module.theories().collect();
    let [ref theory] = *theories.as_slice()
    else {
        panic!("the theory alone presents a model signature, the family none: {theories:?}");
    };
    assert_eq!(
        theory.named.span,
        span_of(source.as_str(), "CatShape", 0_usize)
    );
    let sorts: Vec<&str> = theory
        .description
        .sorts
        .iter()
        .map(|sort| sort.name.as_ref())
        .collect();
    let operations: Vec<&str> = theory
        .description
        .opers
        .iter()
        .map(|operation| operation.name.as_ref())
        .collect();
    assert_eq!(
        (sorts, operations),
        (vec!["Ob", "Hom"], vec!["id", "comp"]),
        "its description's sorts and generating operations"
    );
    let model = theory.model().unwrap();
    let components: Vec<&str> = model
        .components
        .iter()
        .map(|component| component.name.as_ref())
        .collect();
    assert_eq!(
        components,
        ["Ob", "Hom", "id", "comp", "unitL", "unitR", "assoc"],
        "and the model signature its instance checks against"
    );
}

#[test]
fn a_model_of_an_undeclared_theory_is_refused_by_name()
{
    let source = "module M : Model(Nowhere) { def x = 1; }";
    assert_eq!(
        rows(&lower(source)),
        [row(
            "M",
            Role::Held,
            Amounts::Refused(LoweringRefusal::UnresolvedTypeHead {
                span: span_of(source, "Nowhere", 0_usize),
                name: name("Nowhere"),
                arity: gandr_surface_lowering::HeadArity::Nullary,
            })
        )],
        "a theory nothing declares before the module derives nothing"
    );
}

#[test]
fn a_model_missing_an_operation_is_refused_naming_it()
{
    let source = format!(
        "{SIGN}module Partial : Model(CatShape) {{\n  type Ob = Type;\n  type Hom(a : Ob, b : Ob) = +U[ω] (a -> -F b);\n  def ident(t : Type, x : t) -> -F t {{ return x }}\n  def id(t : Type) -> -F (+U[ω] (t -> -F t)) {{ return thunk {{ become ident(t) }} }}\n}}\n"
    );
    let found = rows(&lower(source.as_str()));
    let missing = Amounts::Refused(LoweringRefusal::UnknownMember {
        span: span_of(source.as_str(), "CatShape", 1_usize),
        module: name("Partial"),
        member: name("comp"),
    });
    assert!(
        found
            .iter()
            .any(|&(ref path, role, amounts)| path == "Partial.comp"
                && role == Role::Held
                && amounts == missing),
        "the missing operation is refused by its name: {found:?}"
    );
}

#[test]
fn an_instance_with_a_wrong_law_endpoint_is_refused_naming_the_law()
{
    // The left-zero semigroup on `Integer`, `comp(f, g) = f` and `id = 0`:
    // `unitR` and `assoc` hold by computation and `unitL` does not.
    let left_zero = |statement: &str| {
        format!(
            "{SIGN}module LeftZero : Model(CatShape) {{\n  type Ob = Type;\n  type Hom(a : Ob, b \
             : Ob) = Integer;\n  def id(a : Type) -> -F Hom(a, a) {{ return 0 }}\n  def comp(a : \
             Type, b : Type, c : Type, f : Hom(a, b), g : Hom(b, c)) -> -F Hom(a, c) {{ return f \
             }}\n  def unitL(a : Type, b : Type, f : Hom(a, b)) -> -F Path(Hom(a, b), \
             {statement}) {{ return here(f) }}\n  def unitR(a : Type, b : Type, f : Hom(a, b)) -> \
             -F Path(Hom(a, b), comp(a, b, b, f, id(b)), f) {{ return here(f) }}\n  def assoc(a : \
             Type, b : Type, c : Type, d : Type, f : Hom(a, b), g : Hom(b, c), h : Hom(c, d)) -> \
             -F Path(Hom(a, d), comp(a, c, d, comp(a, b, c, f, g), h), comp(a, b, d, f, comp(b, \
             c, d, g, h))) {{ return here(f) }}\n}}\n"
        )
    };
    let judged = |source: &str| {
        let mut lowered = lower(source);
        let law = super::declaration(&lowered, "LeftZero.unitL", Role::Declared).constant();
        let stated = super::declaration(&lowered, "LeftZero.unitL", Role::Witness).constant();
        (law, stated, verdicts(&mut lowered))
    };

    let (law, stated, judgements) = judged(&left_zero("comp(a, a, b, id(a), f), f"));
    assert!(
        judgements.contains(&(law, Judgement::Refused))
            && judgements
                .iter()
                .all(|&(constant, judgement)| constant == law || judgement == Judgement::Checked),
        "the law the instance's composite does not reach is refused at its own name, its \
         siblings and its statement checking beside it ({stated:?}): {judgements:?}"
    );

    let (law, stated, judgements) = judged(&left_zero("f, f"));
    assert!(
        judgements.contains(&(law, Judgement::Refused))
            && judgements.contains(&(stated, Judgement::Mismatched))
            && judgements.iter().all(|&(constant, judgement)| {
                constant == law || constant == stated || judgement == Judgement::Checked
            }),
        "a member stating another endpoint than the law's is refused at the law's name: \
         {judgements:?}"
    );
}

#[test]
fn a_family_of_the_wrong_telescope_is_refused()
{
    let short = format!(
        "{SIGN}module Short : Model(CatShape) {{\n  type Ob = Type;\n  type Hom(a : Ob) = +U[ω] (a -> -F a);\n  def ident(t : Type, x : t) -> -F t {{ return x }}\n  def id(t : Type) -> -F (+U[ω] (t -> -F t)) {{ return thunk {{ become ident(t) }} }}\n}}\n"
    );
    let found = rows(&lower(short.as_str()));
    let telescope = Amounts::Refused(LoweringRefusal::FamilyTelescope {
        span: span_of(short.as_str(), "Hom", 5_usize),
        name: name("Hom"),
        fault: TelescopeFault::Arity {
            stated: OperandCount::from(2_usize),
            written: OperandCount::from(1_usize),
        },
    });
    let inherited = Amounts::Refused(LoweringRefusal::UnstatedComponent {
        span: span_of(short.as_str(), "CatShape", 1_usize),
        name: name("id"),
        fault: ModelFault::Inherited,
    });
    assert!(
        found.contains(&row("Short.Hom", Role::Held, telescope))
            && found.contains(&row("Short.id", Role::Declared, inherited)),
        "a family binding one parameter where its sort states two indices is refused at its \
         name, and an operation whose type names it inherits: {found:?}"
    );

    let mistyped = format!(
        "{SIGN}module Mistyped : Model(CatShape) {{\n  type Ob = Type;\n  type Hom(a : Ob, b : Integer) = +U[ω] (a -> -F a);\n}}\n"
    );
    let found = rows(&lower(mistyped.as_str()));
    let index = Amounts::Refused(LoweringRefusal::FamilyTelescope {
        span: span_of(mistyped.as_str(), "Hom", 5_usize),
        name: name("Hom"),
        fault: TelescopeFault::Index(OperandCount::from(2_usize)),
    });
    assert!(
        found.contains(&row("Mistyped.Hom", Role::Held, index)),
        "a family whose second parameter is at another type is refused naming it: {found:?}"
    );
}

#[test]
fn a_written_family_of_the_wrong_telescope_is_refused()
{
    let short = "module M : #{ type Hom : (a : Integer) => Type } { type Hom(a : Integer, b : Integer) \
                 = Integer; }";
    let telescope = Amounts::Refused(LoweringRefusal::FamilyTelescope {
        span: span_of(short, "Hom", 1_usize),
        name: name("Hom"),
        fault: TelescopeFault::Arity {
            stated: OperandCount::from(1_usize),
            written: OperandCount::from(2_usize),
        },
    });
    assert_eq!(
        rows(&lower(short)),
        [row("M.Hom", Role::Held, telescope)],
        "a kind stating one index against a family binding two is refused at the family"
    );

    let mistyped = "module M : #{ type Hom : (a : Integer, b : String) => Type } { type Hom(a : \
                    Integer, b : Integer) = Integer; }";
    let index = Amounts::Refused(LoweringRefusal::FamilyTelescope {
        span: span_of(mistyped, "Hom", 1_usize),
        name: name("Hom"),
        fault: TelescopeFault::Index(OperandCount::from(2_usize)),
    });
    assert_eq!(
        rows(&lower(mistyped)),
        [row("M.Hom", Role::Witness, index)],
        "a kind whose second index is at another type than the family's is refused naming it"
    );

    let agreeing = "module M : #{ type Hom : (a : Integer, b : Integer) => Type } { type Hom(a : \
                    Integer, b : Integer) = Integer; }";
    let mut lowered = lower(agreeing);
    assert_eq!(
        rows(&lowered),
        [row("M.Hom", Role::Witness, Amounts::Completed)],
        "and a kind that agrees checks the family at it"
    );
    assert!(
        verdicts(&mut lowered)
            .iter()
            .all(|&(_, judgement)| judgement == Judgement::Checked),
        "which the checker admits"
    );
}

#[test]
fn a_family_applied_to_too_few_indices_is_refused()
{
    let source = "module M { type Ob = Type; type Hom(a : Ob, b : Ob) = +U[ω] (a -> -F b); def f : Hom(Integer); }";
    let found = rows(&lower(source));
    assert!(
        found.iter().any(|&(ref path, _, amounts)| path == "M.f"
            && amounts
                == Amounts::Refused(LoweringRefusal::OutOfFragment {
                    span: span_of(source, "Hom(Integer)", 0_usize),
                    form: gandr_surface_lowering::FormName::from(gandr_surface_grammar::NamedKind(
                        "type_application"
                    )),
                    sort: FragmentSort::ValueType,
                    boundary: FragmentBoundary::Arity(OperandCount::from(1_usize)),
                })),
        "a family is applied to as many indices as it binds: {found:?}"
    );
}
