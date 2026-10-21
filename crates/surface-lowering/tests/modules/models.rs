//! Modules ascribed the model signature a theory derives, `: Model(S)`, and
//! type families, lowered: each derived component asserted against the
//! signature a module writes out by hand, and each component a module does
//! not supply refused by name.

use gandr_core_term::CertificateEquality;
use gandr_core_term::Value;
use gandr_core_term::equal_type_syntax;
use gandr_surface_lowering::FormName;
use gandr_surface_lowering::FragmentBoundary;
use gandr_surface_lowering::FragmentSort;
use gandr_surface_lowering::LoweringRefusal;
use gandr_surface_lowering::OperandCount;
use gandr_surface_lowering::TelescopeFault;
use gandr_surface_lowering::model::ModelFault;

use super::Amounts;
use super::Judgement;
use super::NamedKind;
use super::Role;
use super::body_of;
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

/// `Model(S) with sort x = A` fixes the sort `x` to `A`: a model need not
/// define it and a model sealed at the signature reads its constant at `A`,
/// where a model sealed at `Model(S)` alone keeps the sort abstract; a sort `S`
/// does not present is refused by name.
#[test]
fn a_manifest_sort_is_the_type_the_model_type_names_1226()
{
    let sealed = |manifest: &str, ratio: &str| {
        format!(
            "theory Metering {{\n  sort Ratio : Type;\n  oper scale : Ratio;\n}}\nmodule Sealed :> \
             Model(Metering){manifest} {{\n  {ratio}\n  def scale = 2;\n}}\ndef read : () => \
             Integer ;\ndef read = thunk {{ return Sealed.scale }} ;\n"
        )
    };

    let manifest = sealed(" with sort Ratio = Integer", "");
    let mut lowered = lower(manifest.as_str());
    let judgements = verdicts(&mut lowered);
    assert!(
        !judgements.is_empty()
            && !judgements.iter().any(|&(_, judgement)| {
                matches!(judgement, Judgement::Refused | Judgement::Mismatched)
            }),
        "the manifest sort is the integers through the seal: {judgements:?}"
    );

    let abstracted = sealed("", "type Ratio = Integer;");
    let mut lowered = lower(abstracted.as_str());
    let judgements = verdicts(&mut lowered);
    assert!(
        judgements
            .iter()
            .any(|&(_, judgement)| judgement == Judgement::Mismatched),
        "without the manifest the seal keeps the sort abstract: {judgements:?}"
    );

    let unknown = "theory Metering {\n  sort Ratio : Type;\n  oper scale : Ratio;\n}\nmodule M : \
                   Model(Metering) with sort Rate = Integer {\n  def scale = 2;\n}\n";
    assert!(
        rows(&lower(unknown)).contains(&row(
            "M",
            Role::Held,
            Amounts::Refused(LoweringRefusal::UnknownMember {
                span: span_of(unknown, "Rate", 0_usize),
                module: name("Metering"),
                member: name("Rate"),
            })
        )),
        "a manifest sort the theory does not present is refused by name"
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

/// `oper z : T` is a constant: a model gives it by a value of the carrier, and
/// a function of no inputs, what `oper z : () --> T` derives, is mismatched at
/// the constant's witness.
#[test]
fn a_constant_is_a_value_of_its_type_1226()
{
    let pointed = |member: &str| {
        format!(
            "theory Pointed {{\n  sort T : Type;\n  oper z : T;\n}}\nmodule Zero : \
             Model(Pointed) {{\n  type T = Integer;\n  {member}\n}}\n"
        )
    };

    let given = pointed("def z = 0;");
    let mut value = lower(given.as_str());
    let stated = super::declaration(&value, "Zero.z", Role::Declared).constant();
    let judgements = verdicts(&mut value);
    assert!(
        judgements.contains(&(stated, Judgement::Checked))
            && !judgements.iter().any(|&(_, judgement)| {
                matches!(judgement, Judgement::Refused | Judgement::Mismatched)
            }),
        "a value of the carrier gives the constant: {judgements:?}"
    );

    let called = pointed("def z() -> -F Integer { return 0 }");
    let mut function = lower(called.as_str());
    let stated = super::declaration(&function, "Zero.z", Role::Witness).constant();
    let judgements = verdicts(&mut function);
    assert!(
        judgements.contains(&(stated, Judgement::Mismatched)),
        "a function of no inputs does not give a constant: {judgements:?}"
    );
}

/// A port at a builtin type the theory does not declare reads that type: a
/// model's `read` returning an integer checks, and one returning a string is
/// mismatched at the operation's witness.
#[test]
fn an_operation_at_a_builtin_type_derives_it_1226()
{
    let counter = |member: &str| {
        format!(
            "theory Counter {{\n  sort T : Type;\n  oper read : (x : T) --> Integer;\n}}\nmodule \
             Count : Model(Counter) {{\n  type T = Integer;\n  {member}\n}}\n"
        )
    };

    let integer = counter("def read(n : Integer) -> -F Integer { return n }");
    let mut lowered = lower(integer.as_str());
    let judgements = verdicts(&mut lowered);
    assert!(
        !judgements.is_empty()
            && !judgements.iter().any(|&(_, judgement)| {
                matches!(judgement, Judgement::Refused | Judgement::Mismatched)
            }),
        "an integer result gives the operation: {judgements:?}"
    );

    let string = counter("def read(n : Integer) -> -F String { return \"n\" }");
    let mut lowered = lower(string.as_str());
    let stated = super::declaration(&lowered, "Count.read", Role::Witness).constant();
    let judgements = verdicts(&mut lowered);
    assert!(
        judgements.contains(&(stated, Judgement::Mismatched)),
        "a string result does not: {judgements:?}"
    );
}

/// `oper inner : Model(Answering)` is answered by a nested module ascribed
/// `Model(Answering)`, read through the outer model; a model sealed at the
/// outer theory seals the nested model too; a nested module ascribed no
/// model, and a value, are the wrong sort at the component; a nested module
/// the parser repaired answers for the component by its parse error alone.
#[test]
fn a_nested_model_is_a_module_ascribed_its_theory_1226()
{
    let faceted = |inner: &str| {
        format!(
            "theory Answering {{\n  oper answer : Integer;\n}}\ntheory Faceted {{\n  oper inner : \
             Model(Answering);\n}}\nmodule Facts : Model(Faceted) {{\n  {inner}\n}}\ndef read : () \
             => Integer ;\ndef read = thunk {{ return Facts.inner.answer }} ;\n"
        )
    };

    let ascribed = faceted("module inner : Model(Answering) { def answer = 41; }");
    let mut lowered = lower(ascribed.as_str());
    let judgements = verdicts(&mut lowered);
    assert!(
        !judgements.is_empty()
            && !judgements.iter().any(|&(_, judgement)| {
                matches!(judgement, Judgement::Refused | Judgement::Mismatched)
            }),
        "a nested module ascribed the theory answers the nested model: {judgements:?}"
    );

    let sealed = "theory Carrier {\n  sort T : Type;\n  oper zero : T;\n}\ntheory Outer {\n  oper \
                  inner : Model(Carrier);\n}\nmodule Sealed :> Model(Outer) {\n  module inner : \
                  Model(Carrier) { type T = Integer; def zero = 0; }\n}\ndef leaked : Integer ;\ndef \
                  leaked = Sealed.inner.zero ;\n";
    let mut lowered = lower(sealed);
    let judgements = verdicts(&mut lowered);
    assert!(
        judgements
            .iter()
            .any(|&(_, judgement)| judgement == Judgement::Mismatched),
        "the outer seal keeps the nested model's sort abstract: {judgements:?}"
    );

    for wrong in ["module inner { def answer = 41; }", "def inner = 41;"] {
        let source = faceted(wrong);
        let refused = row(
            "Facts.inner",
            Role::Held,
            Amounts::Refused(LoweringRefusal::OutOfFragment {
                span: span_of(source.as_str(), "Faceted", 1_usize),
                form: gandr_surface_lowering::FormName::MODULE,
                sort: FragmentSort::Module,
                boundary: FragmentBoundary::WrongSort,
            }),
        );
        let found = rows(&lower(source.as_str()));
        assert!(
            found.contains(&refused),
            "`{wrong}` does not answer the nested model: {found:?}"
        );
    }

    let malformed = "theory Answering {\n  oper answer : Integer;\n}\ntheory Faceted {\n  oper inner \
                     : Model(Answering);\n}\nmodule Facts : Model(Faceted) {\n  module inner ";
    let found = rows(&super::repaired(malformed));
    let refusals = found
        .iter()
        .filter(|found| found.0 == "Facts.inner" && found.1 == Role::Held)
        .count();
    assert_eq!(
        refusals, 1_usize,
        "a repaired nested module is refused by its parse error, never again at the \
         component: {found:?}"
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
fn a_refused_member_of_a_model_is_refused_once_1081()
{
    let source = "theory Toggle {\n  sort T : Type;\n  oper flip : (t : T) --> T;\n}\nmodule Bits : \
                  Model(Toggle) {\n  type T = Bool;\n  def flip(b : Bool) -> -F Bool {\n    case b \
                  {\n      true => return false,\n      false => return true\n    }\n  }\n}\n";
    let found = rows(&lower(source));
    let refusals: Vec<LoweringRefusal<'_>> = found
        .iter()
        .filter_map(|&(_, _, amounts)| {
            if let Amounts::Refused(refusal) = amounts {
                Some(refusal)
            }
            else {
                None
            }
        })
        .collect();
    assert!(
        matches!(*refusals.as_slice(), [
            LoweringRefusal::OutOfFragment { .. }
        ]),
        "a member the lowering refuses is refused where it is written, and the model's witness \
         of it is not refused again: {found:?}"
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

/// Each derived type beside the type written for it, node for node.
///
/// # Specification
/// - requires: every name in `pairs` declares a type in `source`.
/// - ensures: nothing beyond the assertions.
/// - fails: never.
/// - panics: when a derived type differs from its written one.
/// - executable: none — the helper returns nothing; its assertions are the
///   relation it checks.
///
/// # Adequacy
/// - hypothesis: L3 — the caller's pairs.
/// - witness: `tests::modules::models::a_model_type_is_the_record_its_theory_derives`
fn states_the_written_types<Source, Name>(
    source: Source,
    pairs: &[(Name, Name)],
) where
    Source: AsRef<str>,
    Name: AsRef<str>,
{
    let lowered = lower(source.as_ref());
    for &(ref derived, ref written) in pairs {
        let (derived, written) = (derived.as_ref(), written.as_ref());
        let derived_type = declared_type_of(&lowered, derived, Role::Declared);
        let written_type = declared_type_of(&lowered, written, Role::Declared);
        assert_eq!(
            equal_type_syntax(&lowered.arena, derived_type, written_type),
            CertificateEquality::Equal,
            "`{derived}` is `{written}`, node for node"
        );
    }
}

/// `Model(Toggle)` is the dependent record its signature states: the carrier
/// bound by `Σ` and read by the start, the step and the reading, the labels
/// erased as a written dependent record erases them. A theory of no sorts,
/// whose fields read nothing, is the record keyed by its operations.
#[test]
fn a_model_type_is_the_record_its_theory_derives()
{
    states_the_written_types(
        "theory Toggle {\n  sort T : Type;\n  oper start : T;\n  oper step : (t : T) --> T;\n  \
         oper read : (t : T) --> Bool;\n}\ntheory Based {\n  oper base : Integer;\n  oper double : \
         Integer;\n}\ndef derived : Model(Toggle) ;\ndef written : #{t : Type, start : t, step : t \
         => t, read : t => Bool} ;\ndef based : Model(Based) ;\ndef plain : #{base : Integer, \
         double : Integer} ;\n",
        &[("derived", "written"), ("based", "plain")],
    );
}

/// A law is a `Path` field over the rule's variables whose endpoints apply the
/// fields before it, so a constant and an operation a law names bind.
#[test]
fn a_law_bearing_model_type_reads_its_operations()
{
    states_the_written_types(
        "theory Unital {\n  sort M : Type;\n  oper e : M;\n  oper mul : (x : M, y : M) --> M;\n  \
         rule unitL : mul(e(), x) ==> x;\n}\ndef derived : Model(Unital) ;\ndef written : #{m : \
         Type, e : m, mul : (x : m, y : m) => m, unitL : (x : m) => Path(m, mul(e, x), x)} ;\n",
        &[("derived", "written")],
    );
}

/// An indexed sort is a function from its indices into the universe, and a
/// later field reads it applied: the edges of a graph over two vertices, and
/// a loop at a vertex an edge from it to itself.
#[test]
fn a_family_sort_is_a_function_into_the_universe()
{
    states_the_written_types(
        "theory Graph {\n  sort V : Type;\n  sort E(s : V, t : V) : Type;\n  oper loop : (v : V) \
         --> E(v, v);\n}\ndef derived : Model(Graph) ;\ndef written : #{v : Type, e : (s : v, t : \
         v) => Type, loop : (x : v) => e(x, x)} ;\n",
        &[("derived", "written")],
    );
}

/// A family read at an index that applies an operation runs that call first,
/// as a written family call does: the terms of a context extended by one, and
/// the variable the extension binds.
#[test]
fn a_family_over_an_applied_index_runs_the_call_first()
{
    states_the_written_types(
        "theory Scoped {\n  sort C : Type;\n  sort T(g : C) : Type;\n  oper ext : (g : C) --> C;\n  \
         oper top : (g : C) --> T(ext(g));\n}\ndef derived : Model(Scoped) ;\ndef written : #{c : \
         Type, t : (g : c) => Type, ext : (g : c) => c, top : (g : c) => t(ext(g))} ;\n",
        &[("derived", "written")],
    );
}

/// A theory's `oper x : Model(T)` is a field holding `Model(T)`'s own record.
#[test]
fn a_nesting_model_type_bundles_the_inner_one()
{
    states_the_written_types(
        "theory Pointed {\n  sort T : Type;\n  oper z : T;\n}\ntheory Outer {\n  oper inner : \
         Model(Pointed);\n}\ndef derived : Model(Outer) ;\ndef written : #{inner : #{t : Type, z : \
         t}} ;\n",
        &[("derived", "written")],
    );
}

#[test]
fn a_model_type_of_an_undeclared_theory_is_refused()
{
    let source = "def m : Model(Nowhere) ;";
    assert_eq!(
        rows(&lower(source)),
        [row(
            "m",
            Role::Declared,
            Amounts::Refused(LoweringRefusal::UnresolvedTypeHead {
                span: span_of(source, "Nowhere", 0_usize),
                name: name("Nowhere"),
                arity: gandr_surface_lowering::HeadArity::Nullary,
            })
        )],
        "a theory nothing declares before the type derives nothing"
    );
}

/// A counter that starts, steps and reads, and a module giving it on the
/// integers, ascribed transparently.
const COUNTER: &str = "theory Counter {\n  sort C : Type;\n  oper start : () --> C;\n  oper step \
                       : (c : C) --> C;\n  oper read : (c : C) --> Integer;\n}\nmodule Open : \
                       Model(Counter) {\n  type C = Integer;\n  def start() -> -F Integer { 0 \
                       }\n  def step(n : Integer) -> -F Integer { become n + 1 }\n  def read(n : \
                       Integer) -> -F Integer { n }\n}\n";

/// A module packed at its theory's models is the record of its members in
/// signature order, nested as the record nests its fields: the code of its
/// carrier beside its start, its step and its reading. The kernel checks it
/// at `Model(Counter)`.
#[test]
fn a_manifest_module_packs_as_the_record_of_its_members()
{
    let source = format!(
        "{COUNTER}def packed : Model(Counter) ;\ndef packed = pack Open at Model(Counter) ;\n"
    );
    let mut lowered = lower(source.as_str());
    let member =
        |path: &str| Value::Constant(super::declaration(&lowered, path, Role::Declared).constant());
    let (start, step, read) = (
        member("Open.start"),
        member("Open.step"),
        member("Open.read"),
    );
    let value = |id| lowered.arena.value(id).cloned();
    let pair = |id| match value(id) {
        Some(Value::Tuple(ref components)) => match **components {
            [first, rest] => (first, rest),
            ref other => panic!("a pair, not {other:?}"),
        },
        other => panic!("a pair, not {other:?}"),
    };
    let (carrier, rest) = pair(body_of(&lowered, "packed"));
    let (first, rest) = pair(rest);
    let (second, third) = pair(rest);
    assert!(
        matches!(value(carrier), Some(Value::Quote(_)))
            && [value(first), value(second), value(third)] == [Some(start), Some(step), Some(read)],
        "the carrier's code, then each operation the module gives"
    );
    let packed = super::declaration(&lowered, "packed", Role::Declared).constant();
    let judgements = verdicts(&mut lowered);
    assert!(
        judgements.contains(&(packed, Judgement::Checked))
            && !judgements.iter().any(|&(_, judgement)| {
                matches!(judgement, Judgement::Refused | Judgement::Mismatched)
            }),
        "the record checks at the theory's models: {judgements:?}"
    );
}

/// A module that seals its carrier does not pack: the record would name the
/// representation the seal hides, which a package over an abstract type
/// carries instead.
#[test]
fn a_pack_of_a_sealed_sort_is_refused()
{
    let source = format!(
        "{}def packed : Model(Counter) ;\ndef packed = pack Open at Model(Counter) ;\n",
        COUNTER.replace("module Open :", "module Open :>")
    );
    let found = rows(&lower(source.as_str()));
    let refused = Amounts::Refused(LoweringRefusal::OutOfFragment {
        span: span_of(source.as_str(), "pack Open at Model(Counter)", 0_usize),
        form: FormName::from(NamedKind("pack_model_expression")),
        sort: FragmentSort::Value,
        boundary: FragmentBoundary::Unadmitted,
    });
    assert!(
        found
            .iter()
            .any(|&(ref path, role, amounts)| path == "packed"
                && role == Role::Declared
                && amounts == refused),
        "the pack of a sealed carrier is refused at the pack: {found:?}"
    );
}

/// A pack names a module declared before it, and nothing else.
#[test]
fn a_pack_of_no_module_is_refused()
{
    let source = format!(
        "{COUNTER}def packed : Model(Counter) ;\ndef packed = pack Closed at Model(Counter) ;\n"
    );
    let found = rows(&lower(source.as_str()));
    let refused = Amounts::Refused(LoweringRefusal::UnresolvedName {
        span: span_of(source.as_str(), "Closed", 0_usize),
        name: name("Closed"),
    });
    assert!(
        found
            .iter()
            .any(|&(ref path, role, amounts)| path == "packed"
                && role == Role::Declared
                && amounts == refused),
        "a name no module answers is unresolved: {found:?}"
    );
}

/// A pattern at a theory's models names the fields of the record by the
/// components' names, whatever pairs the record nests: a consumer reads the
/// start, the step and the reading of any counter, and reads a packed one.
#[test]
fn a_pattern_at_a_model_type_splits_its_fields()
{
    let source = format!(
        "{COUNTER}def observe(m : Model(Counter)) -> -F Integer {{\n  case m {{\n    #{{.start = s, \
         .step = f, .read = r}} => {{\n      run z <- s();\n      run once <- f(z);\n      become \
         r(once)\n    }}\n  }}\n}}\ndef packed : Model(Counter) ;\ndef packed = pack Open at \
         Model(Counter) ;\ndef observed : () => Integer ;\ndef observed = thunk {{ become \
         observe(packed) }} ;\n"
    );
    let mut lowered = lower(source.as_str());
    let judgements = verdicts(&mut lowered);
    assert!(
        !judgements.is_empty()
            && judgements.iter().all(|&(_, judgement)| matches!(
                judgement,
                Judgement::Checked | Judgement::Declared
            )),
        "the consumer splits the record and reads the packed counter: {judgements:?}"
    );
}
