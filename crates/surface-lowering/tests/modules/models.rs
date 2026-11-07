//! Modules ascribed the model signature a theory derives, `: Model(S)`, and
//! type families, lowered: each derived component asserted against the
//! signature a module writes out by hand, and each component a module does
//! not supply refused by name.

use alloc::collections::BTreeSet;

use gandr_core_term::CertificateEquality;
use gandr_core_term::Value;
use gandr_core_term::equal_type_syntax;
use gandr_kernel_term::GroundSort;
use gandr_surface_lowering::AscriptionForm;
use gandr_surface_lowering::FormFault;
use gandr_surface_lowering::FormName;
use gandr_surface_lowering::FragmentBoundary;
use gandr_surface_lowering::FragmentSort;
use gandr_surface_lowering::Labelled;
use gandr_surface_lowering::LoweringRefusal;
use gandr_surface_lowering::OperandCount;
use gandr_surface_lowering::TelescopeFault;
use gandr_surface_lowering::derive::DeriveFault;
use gandr_surface_lowering::model::ModelFault;

use super::Amounts;
use super::Judgement;
use super::NamedKind;
use super::Role;
use super::body_of;
use super::declared_type_of;
use super::gap;
use super::lower;
use super::name;
use super::row;
use super::rows;
use super::span_of;
use super::strata;
use super::verdicts;

/// The `CatShape` theory: a category's objects, morphisms, identities,
/// composition and its three laws.
const SIGN: &str = include_str!("models/unformatted/sign.gandr");

/// The category of discrete setoids: types and functions, composition by
/// sequencing, each law holding by computation.
const SETOIDS: &str = include_str!("models/unformatted/setoids.gandr");

/// The signature `Model(CatShape)` derives, written out by hand, its laws
/// stated over the operations of the module `Derived` so the two signatures
/// name the same constants.
const WRITTEN: &str = "*{ type Ob : Type[+, 1], type Hom : (a : Ob, b : Ob) -> Type, id : (a : Ob) -> Hom(a, a), comp : (a : Ob, b : Ob, c : Ob, f : Hom(a, b), g : Hom(b, c)) -> Hom(a, c), unitL : (a : Ob, b : Ob, f : Hom(a, b)) -> Path[.A = Hom(a, b)](Derived.comp a a b (Derived.id a) f, f), unitR : (a : Ob, b : Ob, f : Hom(a, b)) -> Path[.A = Hom(a, b)](Derived.comp a b b f (Derived.id b), f), assoc : (a : Ob, b : Ob, c : Ob, d : Ob, f : Hom(a, b), g : Hom(b, c), h : Hom(c, d)) -> Path[.A = Hom(a, d)](Derived.comp a c d (Derived.comp a b c f g) h, Derived.comp a b d f (Derived.comp b c d g h)) }";

#[test]
fn a_derived_signature_states_what_the_written_one_does()
{
    let over_derived = SETOIDS
        .replace("comp p", "Derived.comp p")
        .replace("comp q", "Derived.comp q")
        .replace("id p", "Derived.id p")
        .replace("id q", "Derived.id q");
    let source = format!(
        include_str!(
            "models/unformatted/a-derived-signature-states-what-the-written-one-does.gandr"
        ),
        SIGN = SIGN,
        WRITTEN = WRITTEN,
        SETOIDS = SETOIDS,
        over_derived = over_derived
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
            .all(|&(_, judgement)| matches!(judgement, Judgement::Checked | Judgement::Declared)),
        "and the setoid category checks at both, each law by computation, the `Theory` code \
         declared: {judgements:?}"
    );
}

#[test]
fn a_lowered_theory_exposes_its_description_and_its_model()
{
    let source = format!(
        include_str!(
            "models/unformatted/a-lowered-theory-exposes-its-description-and-its-model.gandr"
        ),
        SIGN = SIGN
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

/// The include subject's base: the semigroup, the monoid, the left zero, the
/// two extensions at once, and the endomorphism monoid.
const INCLUDED: &str = include_str!("../../../../corpus/model/include/monoid.gandr");

#[test]
fn a_model_of_an_extension_stands_where_the_included_model_is_asked()
{
    let source = format!(
        include_str!(
            "models/unformatted/a-model-of-an-extension-stands-where-the-included-model-is-asked.gandr"
        ),
        INCLUDED = INCLUDED
    );
    let mut lowered = lower(source.as_str());
    let listed: BTreeSet<_> = lowered.module.reducts().iter().collect();
    let reducts: Vec<String> = rows(&lowered)
        .into_iter()
        .zip(lowered.module.declarations())
        .filter(|&(_, declaration)| listed.contains(&declaration.constant()))
        .map(|((name, ..), _)| name)
        .collect();
    assert_eq!(
        reducts,
        [
            "Monoid.Semigroup",
            "LeftZero.Semigroup",
            "UnitAndZero.Monoid",
            "UnitAndZero.Semigroup",
            "UnitAndZero.LeftZero"
        ],
        "each theory takes one reduct per theory it includes, directly or through another, the \
         diamond's semigroup once"
    );
    assert_eq!(lowered.module.reducts().len(), reducts.len());
    let judgements = verdicts(&mut lowered);
    assert!(
        judgements.iter().all(|&(_, judgement)| matches!(
            judgement,
            Judgement::Checked | Judgement::Synthesised | Judgement::Declared
        )),
        "every reduct checks, and the monoid stands where the semigroup is asked, by the reduct \
         inserted and by the reduct named: {judgements:?}"
    );
}

/// A model whose unindexed sorts are manifest stands where its theory's model
/// is asked: each theory a manifest model type names takes one forgetting map
/// under its own name, which checks, and the checker inserts it at the carrier
/// the model's type fixes, a type or a bound variable, past a law whose path
/// the solver leaves to the conversion; a theory no manifest type names takes
/// none.
#[test]
fn a_manifest_model_stands_where_its_theory_s_model_is_asked()
{
    let source = include_str!(
        "models/fixtures/a-manifest-model-stands-where-its-theory-s-model-is-asked.gandr"
    );
    let mut lowered = lower(source);
    let forgets: Vec<String> = rows(&lowered)
        .into_iter()
        .filter(|&(_, role, _)| role == Role::Derived)
        .map(|(name, ..)| name)
        .collect();
    assert_eq!(
        forgets,
        ["Counter", "Sg"],
        "each theory a manifest names takes one forgetting map under its own name, the two \
         counters fixing one carrier sharing it, the unnamed theory none"
    );
    assert_eq!(lowered.module.forgets().len(), 2);
    let judgements = verdicts(&mut lowered);
    assert!(
        judgements.iter().all(|&(_, judgement)| matches!(
            judgement,
            Judgement::Checked | Judgement::Synthesised | Judgement::Declared
        )),
        "each forgetting map checks, and a model whose carrier is manifest stands where its \
         theory's model is asked, its carrier a type or a variable, a law or none: \
         {judgements:?}"
    );
}

/// A model fixing some of its theory's sorts stands where the theory's model
/// is asked, as one fixing all of them does: each set of sorts a manifest
/// model type fixes takes its own forgetting map, which puts back those sorts
/// and keeps the others the fields they are (#2132).
#[test]
fn a_model_fixing_some_sorts_stands_where_its_theory_s_model_is_asked_2132()
{
    let source = include_str!(
        "models/fixtures/a-model-fixing-some-sorts-stands-where-its-theory-s-model-is-asked-2132.gandr"
    );
    let mut lowered = lower(source);
    let forgets: Vec<String> = rows(&lowered)
        .into_iter()
        .filter(|&(_, role, _)| role == Role::Derived)
        .map(|(name, ..)| name)
        .collect();
    assert_eq!(
        forgets,
        ["Pairing", "Pairing", "Pairing"],
        "both sorts, the first alone and the second alone take a map each; the first fixed \
         again shares its map"
    );
    let judgements = verdicts(&mut lowered);
    assert!(
        judgements.iter().all(|&(_, judgement)| matches!(
            judgement,
            Judgement::Checked | Judgement::Synthesised | Judgement::Declared
        )),
        "each map checks, and a model fixing both sorts, the first or the second stands where \
         the pairing's model is asked: {judgements:?}"
    );
}

/// A manifest model of an extension stands where an included theory's model
/// is asked: beside the map onto its own theory's models, each set of sorts a
/// manifest model type fixes takes one map per theory a reduct restricts to,
/// forgetting the sorts and then restricting, under that theory's name
/// (#2136).
#[test]
fn a_manifest_model_of_an_extension_stands_where_the_included_model_is_asked_2136()
{
    let source = format!(
        include_str!(
            "models/unformatted/a-manifest-model-of-an-extension-stands-where-the-included-model-is-asked-2136.gandr"
        ),
        INCLUDED = INCLUDED
    );
    let mut lowered = lower(source.as_str());
    let listed: BTreeSet<_> = lowered.module.forgets().iter().collect();
    let forgets: Vec<String> = rows(&lowered)
        .into_iter()
        .zip(lowered.module.declarations())
        .filter(|&(_, declaration)| listed.contains(&declaration.constant()))
        .map(|((name, ..), _)| name)
        .collect();
    assert_eq!(
        forgets,
        [
            "Monoid",
            "Semigroup",
            "UnitAndZero",
            "Monoid",
            "Semigroup",
            "LeftZero"
        ],
        "a manifest monoid takes the map onto the monoids and one onto the semigroups, shared \
         by the second monoid fixing the same carrier; the diamond's takes one onto each theory \
         it reaches"
    );
    let judgements = verdicts(&mut lowered);
    assert!(
        judgements.iter().all(|&(_, judgement)| matches!(
            judgement,
            Judgement::Checked | Judgement::Synthesised | Judgement::Declared
        )),
        "each map checks, and a manifest monoid stands where a semigroup is asked as where a \
         monoid is, the diamond's where a semigroup is: {judgements:?}"
    );
}

/// The forgetting map written out is the map the checker inserts (#2130):
/// `forget[sort B = Unit, sort A = Integer](m) at Model(Pairing)` calls the
/// pairing's map at the carriers in the order the signature states its sorts,
/// whichever order they are written in, so it checks where the inserted map
/// does and shares its slot; the module records each map's sorts in that
/// order. A written map whose model fixes no sort takes the slot it names, so
/// the checker, not the lowering, refuses the model at it.
#[test]
fn a_written_forgetting_map_takes_the_slot_it_names_2130()
{
    let source =
        include_str!("models/fixtures/a-written-forgetting-map-takes-the-slot-it-names-2130.gandr");
    let mut lowered = lower(source);
    let forgets: Vec<String> = rows(&lowered)
        .into_iter()
        .filter(|&(_, role, _)| role == Role::Derived)
        .map(|(name, ..)| name)
        .collect();
    assert_eq!(
        forgets,
        ["Pairing", "Counter"],
        "the written pairing's map shares the inserted one's slot; the written counter's map \
         takes its own"
    );
    let carried: Vec<Vec<&str>> = lowered
        .module
        .forgettings()
        .iter()
        .map(|forgetting| forgetting.sorts.iter().map(AsRef::as_ref).collect())
        .collect();
    assert_eq!(
        carried,
        [vec!["A", "B"], vec!["C"]],
        "each map records the sorts it puts back in signature order, the order of its \
         carriers, whichever order the form writes them in"
    );
    let written = super::declaration(&lowered, "written", Role::Declared).constant();
    let unfixed = super::declaration(&lowered, "unfixed", Role::Declared).constant();
    let judgements = verdicts(&mut lowered);
    assert!(
        judgements
            .iter()
            .all(|&(constant, judgement)| if constant == unfixed {
                judgement == Judgement::Mismatched
            }
            else {
                matches!(
                    judgement,
                    Judgement::Checked | Judgement::Synthesised | Judgement::Declared
                )
            })
            && judgements.contains(&(written, Judgement::Checked)),
        "the written map checks at the carriers in signature order, and a model fixing no sort \
         is mismatched at the map the form names: {judgements:?}"
    );
}

/// A written forgetting map names its theory's own sorts at its theory's
/// models (#2130): a sort the theory does not have is an unknown member of
/// it, a bracket entry that is no binding `sort C = A` is an extra operand,
/// and a type after `at` that is no `Model(T)` puts the `at` out of place.
#[test]
fn a_written_forgetting_map_names_only_its_theory_s_sorts_2130()
{
    let source = include_str!(
        "models/unformatted/a-written-forgetting-map-names-only-its-theory-s-sorts-2130.gandr"
    );
    let found = rows(&lower(source));
    let unknown = Amounts::Refused(LoweringRefusal::UnknownMember {
        span: span_of(source, "D", 0_usize),
        module: name("Counter"),
        member: name("D"),
    });
    assert!(
        found
            .iter()
            .any(|&(ref path, role, ref amounts)| path == "stray"
                && role == Role::Declared
                && *amounts == unknown),
        "a sort the counter does not have is an unknown member of it: {found:?}"
    );
    let extra = Amounts::Refused(LoweringRefusal::MalformedForm {
        span: span_of(source, "Integer", 3_usize),
        form: FormName::from(NamedKind("forget_model_expression")),
        fault: FormFault::ExtraOperand,
    });
    assert!(
        found
            .iter()
            .any(|&(ref path, role, ref amounts)| path == "unbound"
                && role == Role::Declared
                && *amounts == extra),
        "a carrier written without the sort it fixes is an extra operand of the bracket: \
         {found:?}"
    );
    let misplaced = Amounts::Refused(LoweringRefusal::MalformedForm {
        span: span_of(source, "at", 2_usize),
        form: FormName::from(NamedKind("forget_model_expression")),
        fault: FormFault::MisplacedTile,
    });
    assert!(
        found
            .iter()
            .any(|&(ref path, role, ref amounts)| path == "nowhere"
                && role == Role::Declared
                && *amounts == misplaced),
        "a map onto a type that is no model type has its `at` out of place: {found:?}"
    );
}

/// A model binder's sorts read as types (#2131). `a.C` for `a :
/// Model(Counter)` is the carrier `a`'s record holds: a second counter fixing
/// its carrier to `a.C` steps a count of `a`, as any counter steps its own
/// zero, and one whose carrier is its own steps no count of `a`. A carrier
/// `a`'s type fixes is the type it is fixed to, read past the binders
/// between, whether or not another type names `a`. An indexed sort is no
/// type, and a name the theory lacks is refused naming it.
#[test]
fn a_model_binder_s_carrier_is_its_projected_sort_2131()
{
    // The refusal a case expects, built from the source it lowers.
    type Expected<'case> = &'case dyn Fn(&str) -> LoweringRefusal<'static>;

    let counter = include_str!(
        "models/fixtures/a-model-binder-s-carrier-is-its-projected-sort-2131-counter.gandr"
    );
    let stepped = |second: &str, count: &str| {
        let source = format!(
            include_str!(
                "models/unformatted/a-model-binder-s-carrier-is-its-projected-sort-2131-3.gandr"
            ),
            count = count,
            counter = counter,
            second = second
        );
        let mut lowered = lower(source.as_str());
        let step = super::declaration(&lowered, "step", Role::Declared).constant();
        verdicts(&mut lowered)
            .into_iter()
            .find(|&(constant, _)| constant == step)
            .map(|(_, judgement)| judgement)
    };
    assert_eq!(
        stepped("Model(Counter) with sort C = a.C", "c"),
        Some(Judgement::Checked),
        "a counter sharing `a`'s carrier steps a count of `a`"
    );
    assert_eq!(
        stepped("Model(Counter)", "z"),
        Some(Judgement::Checked),
        "a counter steps its own zero"
    );
    assert_eq!(
        stepped("Model(Counter)", "c"),
        Some(Judgement::Mismatched),
        "a counter whose carrier is its own steps no count of `a`"
    );

    states_the_written_types(
        format!(
            include_str!(
                "models/unformatted/a-model-binder-s-carrier-is-its-projected-sort-2131-1.gandr"
            ),
            counter = counter
        ),
        &[
            ("fixed", "fixedWritten"),
            ("open", "openWritten"),
            ("named", "namedWritten"),
        ],
    );

    let cases: [(&str, Expected<'_>, &str); 2] = [
        (
            "E",
            &|source| LoweringRefusal::OutOfFragment {
                span: span_of(source, "g.E", 0_usize),
                form: FormName::from(NamedKind("type_path")),
                sort: FragmentSort::ValueType,
                boundary: FragmentBoundary::WrongSort,
            },
            "an indexed sort is no type",
        ),
        (
            "Nope",
            &|source| LoweringRefusal::UnknownMember {
                span: span_of(source, "Nope", 0_usize),
                module: name("g"),
                member: name("Nope"),
            },
            "a name the theory lacks is refused naming it",
        ),
    ];
    for (member, refusal, why) in cases {
        let source = format!(
            include_str!(
                "models/unformatted/a-model-binder-s-carrier-is-its-projected-sort-2131-2.gandr"
            ),
            member = member
        );
        let found: Vec<_> = rows(&lower(source.as_str()))
            .into_iter()
            .filter(|found| found.0 == "m")
            .collect();
        assert_eq!(
            found,
            [row("m", Role::Declared, Amounts::Refused(refusal(&source)))],
            "{why}"
        );
    }
}

/// A sort a partly manifest model type leaves a field is read off its binder
/// (#2158): `m.B` for `m : Model(Pairing) with sort A = Integer` is the
/// second carrier `m`'s record holds, though the type's application is
/// classified after a later parameter's type would reach it. A pairing fixing
/// its second carrier to `m.B` hands its right where `m`'s second carrier is
/// asked; one whose second carrier is its own field does not.
#[test]
fn a_sort_a_partly_manifest_type_leaves_a_field_is_read_off_its_binder_2158()
{
    let pairing = include_str!(
        "models/fixtures/a-sort-a-partly-manifest-type-leaves-a-field-is-read-off-its-binder-2158-pairing.gandr"
    );
    let handed = |second: &str| {
        let source = format!(
            include_str!(
                "models/unformatted/a-sort-a-partly-manifest-type-leaves-a-field-is-read-off-its-binder-2158.gandr"
            ),
            pairing = pairing,
            second = second
        );
        let mut lowered = lower(source.as_str());
        let keep = super::declaration(&lowered, "keep", Role::Declared).constant();
        let hand = super::declaration(&lowered, "hand", Role::Declared).constant();
        let judgements = verdicts(&mut lowered);
        let of = |constant| {
            judgements
                .iter()
                .find(|&&(judged, _)| judged == constant)
                .map(|&(_, judgement)| judgement)
        };
        (of(keep), of(hand))
    };
    assert_eq!(
        handed("Model(Pairing) with sort A = Integer with sort B = m.B"),
        (Some(Judgement::Checked), Some(Judgement::Checked)),
        "a value of `m.B` is one `m.B` asks for, and a pairing sharing `m`'s second carrier \
         hands its right there"
    );
    assert_eq!(
        handed("Model(Pairing) with sort A = Integer"),
        (Some(Judgement::Checked), Some(Judgement::Mismatched)),
        "a pairing whose second carrier is its own field hands no value of `m`'s"
    );
}

/// A type path through a model binder is written where a reader points (#2182):
/// the head `a` of `a.C` is labelled at `a`'s written type, whether the sort is
/// projected off `a`'s record or fixed by `a`'s type, and a fixed sort, which
/// mints no node at the path, stands in there.
#[test]
fn a_carrier_path_s_head_and_a_fixed_path_answer_2182()
{
    let source =
        include_str!("models/fixtures/a-carrier-path-s-head-and-a-fixed-path-answer-2182.gandr");
    let lowered = lower(source);
    let origins = lowered.module.origins();
    for head in ["a", "b"] {
        let at = span_of(source, format!("{head}.C"), 0_usize);
        assert!(
            origins.labels().iter().any(|label| {
                label.span.start() == at.start()
                    && usize::from(label.span.end()) == usize::from(at.start()).saturating_add(1)
                    && matches!(label.labelled, Labelled::ValueType { .. })
            }),
            "`{head}` in `{head}.C` answers at its binder's type"
        );
    }
    let fixed = span_of(source, "b.C", 0_usize);
    assert!(
        origins
            .stand_ins()
            .iter()
            .any(|&(_, origin)| origin.span() == fixed),
        "the fixed carrier stands in at its path"
    );
}

#[test]
fn a_model_of_an_undeclared_theory_is_refused_by_name()
{
    let source = "module M : Model(Nowhere) where { def x = 1; }";
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
            "theory Metering where {{\n  sort Ratio : Type;\n  oper scale : Ratio;\n}}\nmodule Sealed :> \
             Model(Metering){manifest} where {{\n  {ratio}\n  def scale = 2;\n}}\ndef read : () -> \
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

    let unknown = include_str!(
        "models/fixtures/a-manifest-sort-is-the-type-the-model-type-names-1226-unknown.gandr"
    );
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
        include_str!("models/unformatted/a-model-missing-an-operation-is-refused-naming-it.gandr"),
        SIGN = SIGN
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

/// #2356: a theory's stated laws are components a model proves by a
/// definition at their path type or admits by `law name = ~admitted ;`, which
/// the checker owes as the axiom it is only where the host asserts the law of
/// its primitive (#2302); a model that neither proves nor admits one leaves it
/// to the checker to discharge (#4112), and one admitting a law at its own
/// data type is refused by the checker.
#[test]
fn a_stated_law_is_a_component_a_model_proves_2356()
{
    let source =
        include_str!("models/fixtures/a-stated-law-is-a-component-a-model-proves-2356.gandr");
    let mut lowered = lower(source);
    let found = rows(&lowered);
    for (path, role, amounts) in [
        ("Proved.refl", Role::Declared, Amounts::Completed),
        ("Proved.trans", Role::Declared, Amounts::Completed),
        ("Admitted.refl", Role::Admitted, Amounts::Uncompleted),
        ("Admitted.trans", Role::Admitted, Amounts::Uncompleted),
        ("Short.refl", Role::Admitted, Amounts::Uncompleted),
        ("Short.trans", Role::Discharged, Amounts::Uncompleted),
    ] {
        assert!(
            found.contains(&row(path, role, amounts)),
            "`{path}` is {role:?} {amounts:?}: {found:?}"
        );
    }
    let proved = ["Proved.refl", "Proved.trans"]
        .map(|path| super::declaration(&lowered, path, Role::Declared).constant());
    let admitted = ["Admitted.refl", "Admitted.trans"]
        .map(|path| super::declaration(&lowered, path, Role::Admitted).constant());
    let unasserted = super::declaration(&lowered, "Short.refl", Role::Admitted).constant();
    let judgements = verdicts(&mut lowered);
    assert!(
        proved
            .iter()
            .all(|&law| judgements.contains(&(law, Judgement::Checked)))
            && admitted
                .iter()
                .all(|&law| judgements.contains(&(law, Judgement::Owed)))
            && judgements.contains(&(unasserted, Judgement::Refused)),
        "each proof checks at the law's path, each admission the host asserts is owed as the \
         axiom it is, and one it does not is refused: {judgements:?}"
    );
}

/// A law member admits its law only by the splice `~admitted`: a proof and a
/// splice of another tactic are each refused at the body, and the module does
/// not read.
#[test]
fn a_law_member_admits_only_by_the_splice_of_admitted()
{
    let theory = include_str!(
        "models/unformatted/a-law-member-admits-only-by-the-splice-of-admitted-theory.gandr"
    );
    for (member, out_of_place) in [
        ("law refl = Path.here(true);", "Path.here(true)"),
        ("law refl = ~assumption;", "~assumption"),
    ] {
        let source = format!(
            include_str!(
                "models/unformatted/a-law-member-admits-only-by-the-splice-of-admitted.gandr"
            ),
            member = member,
            theory = theory
        );
        let found = rows(&lower(source.as_str()));
        let refused = Amounts::Refused(LoweringRefusal::MalformedForm {
            span: span_of(&source, out_of_place, 0_usize),
            form: FormName::MODULE,
            fault: FormFault::MisplacedTile,
        });
        assert!(
            found
                .iter()
                .any(|&(ref path, _, ref amounts)| path == "Host" && *amounts == refused)
                && !found.iter().any(|&(_, role, _)| role == Role::Admitted),
            "`{member}` admits nothing and is refused at `{out_of_place}`: {found:?}"
        );
    }
    let admitted = format!(
        include_str!(
            "models/unformatted/a-law-member-admits-only-by-the-splice-of-admitted-admitted.gandr"
        ),
        theory = theory
    );
    assert!(
        rows(&lower(admitted.as_str())).contains(&row(
            "Host.refl",
            Role::Admitted,
            Amounts::Uncompleted
        )),
        "the splice of `admitted` admits the law"
    );
}

/// #4112: a law a model omits is stated at its derived type with no body, and
/// the checker discharges it by `here` at its left side where its sides
/// convert; where they part, the law is refused naming it.
#[test]
fn an_omitted_law_is_discharged_by_the_checker_4112()
{
    let source =
        include_str!("models/fixtures/an-omitted-law-is-discharged-by-the-checker-4112.gandr");
    let mut lowered = lower(source);
    let [converts, parts] = ["Converts.refl", "Parts.refl"]
        .map(|path| super::declaration(&lowered, path, Role::Discharged).constant());
    let judgements = verdicts(&mut lowered);
    assert!(
        judgements.contains(&(converts, Judgement::Checked))
            && judgements.contains(&(parts, Judgement::Refused)),
        "the law whose sides convert is discharged, and the one whose sides part is refused: \
         {judgements:?}"
    );
}

#[test]
fn a_repaired_model_body_owes_no_law_beside_its_parse_error_5142()
{
    let source = include_str!(
        "models/unformatted/a-repaired-model-body-owes-no-law-beside-its-parse-error-5142.gandr"
    );
    let lowered = super::repaired(source);
    let refused: Vec<_> = rows(&lowered)
        .into_iter()
        .filter_map(|(name, _, amounts)| match amounts {
            Amounts::Refused(refusal) => Some((name, refusal)),
            Amounts::Completed
            | Amounts::Uncompleted
            | Amounts::Bodied
            | Amounts::Data
            | Amounts::Codata
            | Amounts::Abstract
            | Amounts::World => None,
        })
        .collect();
    assert!(
        matches!(refused.as_slice(), [(member, LoweringRefusal::MalformedForm {
            fault: FormFault::Repaired(_),
            ..
        })] if member == "Cut.same"),
        "a model body cut inside its member is refused at that member's repair alone, the laws \
         it owes raising nothing beside it: {refused:?}"
    );
}

#[test]
fn an_instance_with_a_wrong_law_endpoint_is_refused_naming_the_law()
{
    // The left-zero semigroup on `Integer`, `comp f g = f` and `id = 0`:
    // `unitR` and `assoc` hold by computation and `unitL` does not.
    let left_zero = |statement: &str| {
        format!(
            "{SIGN}module LeftZero : Model(CatShape) where {{\n  type Ob = Type;\n  type Hom(a : Ob, b \
             : Ob) = Integer;\n  def id(a : Type) -> -F Hom(a, a) {{ return 0 }}\n  def comp(a : \
             Type, b : Type, c : Type, f : Hom(a, b), g : Hom(b, c)) -> -F Hom(a, c) {{ return f \
             }}\n  def unitL(a : Type, b : Type, f : Hom(a, b)) -> -F Path[.A = Hom(a, b)](\
             {statement}) {{ return Path.here f }}\n  def unitR(a : Type, b : Type, f : Hom(a, b)) -> \
             -F Path[.A = Hom(a, b)](comp a b b f (id b), f) {{ return Path.here f }}\n  def assoc(a : \
             Type, b : Type, c : Type, d : Type, f : Hom(a, b), g : Hom(b, c), h : Hom(c, d)) -> \
             -F Path[.A = Hom(a, d)](comp a c d (comp a b c f g) h, comp a b d f (comp b \
             c d g h)) {{ return Path.here f }}\n}}\n"
        )
    };
    let judged = |source: &str| {
        let mut lowered = lower(source);
        let law = super::declaration(&lowered, "LeftZero.unitL", Role::Declared).constant();
        let stated = super::declaration(&lowered, "LeftZero.unitL", Role::Witness).constant();
        (law, stated, verdicts(&mut lowered))
    };

    let (law, stated, judgements) = judged(&left_zero("comp a a b (id a) f, f"));
    assert!(
        judgements.contains(&(law, Judgement::Refused))
            && judgements.iter().all(|&(constant, judgement)| {
                constant == law || matches!(judgement, Judgement::Checked | Judgement::Declared)
            }),
        "the law the instance's composite does not reach is refused at its own name, its \
         siblings and its statement checking beside it ({stated:?}): {judgements:?}"
    );

    let (law, stated, judgements) = judged(&left_zero("f, f"));
    assert!(
        judgements.contains(&(law, Judgement::Refused))
            && judgements.contains(&(stated, Judgement::Mismatched))
            && judgements.iter().all(|&(constant, judgement)| {
                constant == law
                    || constant == stated
                    || matches!(judgement, Judgement::Checked | Judgement::Declared)
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
            "theory Pointed where {{\n  sort T : Type;\n  oper z : T;\n}}\nmodule Zero : \
             Model(Pointed) where {{\n  type T = Integer;\n  {member}\n}}\n"
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
            "theory Counter where {{\n  sort T : Type;\n  oper read : (x : T) --> Integer;\n}}\nmodule \
             Count : Model(Counter) where {{\n  type T = Integer;\n  {member}\n}}\n"
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
            "theory Answering where {{\n  oper answer : Integer;\n}}\ntheory Faceted where {{\n  oper inner : \
             Model(Answering);\n}}\nmodule Facts : Model(Faceted) where {{\n  {inner}\n}}\ndef read : () \
             -> Integer ;\ndef read = thunk {{ return Facts.inner.answer }} ;\n"
        )
    };

    let ascribed = faceted("module inner : Model(Answering) where { def answer = 41; }");
    let mut lowered = lower(ascribed.as_str());
    let judgements = verdicts(&mut lowered);
    assert!(
        !judgements.is_empty()
            && !judgements.iter().any(|&(_, judgement)| {
                matches!(judgement, Judgement::Refused | Judgement::Mismatched)
            }),
        "a nested module ascribed the theory answers the nested model: {judgements:?}"
    );

    let sealed = include_str!(
        "models/unformatted/a-nested-model-is-a-module-ascribed-its-theory-1226-sealed.gandr"
    );
    let mut lowered = lower(sealed);
    let judgements = verdicts(&mut lowered);
    assert!(
        judgements
            .iter()
            .any(|&(_, judgement)| judgement == Judgement::Mismatched),
        "the outer seal keeps the nested model's sort abstract: {judgements:?}"
    );

    for wrong in ["module inner where { def answer = 41; }", "def inner = 41;"] {
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

    let malformed = include_str!(
        "models/unformatted/a-nested-model-is-a-module-ascribed-its-theory-1226-malformed.gandr"
    );
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

/// A sealed nested model's sort is written as a path through the nested
/// model's name, `Sealed.inner.T`, and the nested model's point checks at it;
/// a type the nested model does not export is an unknown member of it, named
/// as the path spells the module.
#[test]
fn a_sealed_nested_model_s_sort_is_spelled_by_its_path_1311()
{
    let sealed = |reader: &str| {
        format!(
            "theory Carrier where {{\n  sort T : Type;\n  oper zero : T;\n}}\ntheory Outer where {{\n  oper \
             inner : Model(Carrier);\n}}\nmodule Sealed :> Model(Outer) where {{\n  module inner : \
             Model(Carrier) where {{ type T = Integer; def zero = 0; }}\n}}\n{reader}\n"
        )
    };

    let kept = sealed(include_str!(
        "models/fixtures/a-sealed-nested-model-s-sort-is-spelled-by-its-path-1311-kept.gandr"
    ));
    let mut lowered = lower(kept.as_str());
    let judgements = verdicts(&mut lowered);
    assert!(
        !judgements.is_empty()
            && !judgements.iter().any(|&(_, judgement)| {
                matches!(judgement, Judgement::Refused | Judgement::Mismatched)
            }),
        "the nested point checks at the nested sort's path: {judgements:?}"
    );

    let lost = sealed(include_str!(
        "models/fixtures/a-sealed-nested-model-s-sort-is-spelled-by-its-path-1311-lost.gandr"
    ));
    let found = rows(&lower(lost.as_str()));
    let unknown = Amounts::Refused(LoweringRefusal::UnknownMember {
        span: span_of(lost.as_str(), "U", 0_usize),
        module: name("inner"),
        member: name("U"),
    });
    assert!(
        found
            .iter()
            .any(|&(ref path, _, ref amounts)| path == "lost" && *amounts == unknown),
        "a type the nested model does not export is an unknown member of it: {found:?}"
    );
}

#[test]
fn a_family_of_the_wrong_telescope_is_refused()
{
    let short = format!(
        include_str!("models/unformatted/a-family-of-the-wrong-telescope-is-refused-short.gandr"),
        SIGN = SIGN
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
        include_str!(
            "models/unformatted/a-family-of-the-wrong-telescope-is-refused-mistyped.gandr"
        ),
        SIGN = SIGN
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
    let short = "module M : *{ type Hom : (a : Integer) -> Type } where { type Hom(a : Integer, b : Integer) \
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

    let mistyped = "module M : *{ type Hom : (a : Integer, b : String) -> Type } where { type Hom(a : \
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

    let agreeing = "module M : *{ type Hom : (a : Integer, b : Integer) -> Type } where { type Hom(a : \
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
    let source =
        include_str!("models/fixtures/a-refused-member-of-a-model-is-refused-once-1081.gandr");
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
    let source = "module M where { type Ob = Type; type Hom(a : Ob, b : Ob) = +U[ω] (a -> -F b); def f : Hom(Integer); }";
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
        include_str!("models/fixtures/a-model-type-is-the-record-its-theory-derives.gandr"),
        &[("derived", "written"), ("based", "plain")],
    );
}

/// A law is a `Path` field over the rule's variables whose endpoints apply the
/// fields before it, so a constant and an operation a law names bind.
#[test]
fn a_law_bearing_model_type_reads_its_operations()
{
    states_the_written_types(
        include_str!("models/fixtures/a-law-bearing-model-type-reads-its-operations.gandr"),
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
        include_str!("models/fixtures/a-family-sort-is-a-function-into-the-universe.gandr"),
        &[("derived", "written")],
    );
}

/// The data a computation carrier wraps.
const MAYBE: &str = include_str!("models/fixtures/maybe.gandr");

/// A `Type[-]` sort is a family, or a type, into the computation types: a
/// module answering it with computation types checks and its model type is the
/// record written at `Type[-]`, apart from the record a `Type` sort's model is;
/// a member landing in the other ground sort is refused at its name, at either
/// classifier and whether it is a family or a type.
#[test]
fn a_computation_sort_is_a_family_into_computation_types_3050()
{
    let carrier = include_str!(
        "models/fixtures/a-computation-sort-is-a-family-into-computation-types-3050-carrier.gandr"
    );
    let plain = include_str!(
        "models/fixtures/a-computation-sort-is-a-family-into-computation-types-3050-plain.gandr"
    );
    let carried = format!(
        include_str!(
            "models/unformatted/a-computation-sort-is-a-family-into-computation-types-3050-carried.gandr"
        ),
        MAYBE = MAYBE,
        carrier = carrier,
        plain = plain
    );
    let mut lowered = lower(carried.as_str());
    let found = rows(&lowered);
    assert!(
        found
            .iter()
            .all(|&(_, _, amounts)| !matches!(amounts, Amounts::Refused(_))),
        "a module answering each computation sort with a computation type is refused nowhere: \
         {found:?}"
    );
    let judged = verdicts(&mut lowered);
    assert!(
        judged.iter().all(|&(_, judgement)| matches!(
            judgement,
            Judgement::Checked | Judgement::Declared | Judgement::Owed
        )),
        "and the checker admits it, the bare signatures owing their bodies: {judged:?}"
    );
    states_the_written_types(carried.as_str(), &[("derived", "written")]);
    assert_ne!(
        equal_type_syntax(
            &lowered.arena,
            declared_type_of(&lowered, "derived", Role::Declared),
            declared_type_of(&lowered, "valued", Role::Declared),
        ),
        CertificateEquality::Equal,
        "a model of the computation sorts is not a model of the value sorts"
    );

    let ground = |source: &str,
                  member: &'static str,
                  stated: GroundSort,
                  written: GroundSort|
     -> Amounts<'static> {
        Amounts::Refused(LoweringRefusal::FamilyTelescope {
            span: span_of(source, member, 1_usize),
            name: name(member),
            fault: TelescopeFault::Ground { stated, written },
        })
    };
    let valued = format!(
        include_str!(
            "models/unformatted/a-computation-sort-is-a-family-into-computation-types-3050-valued.gandr"
        ),
        MAYBE = MAYBE,
        carrier = carrier
    );
    let found = rows(&lower(valued.as_str()));
    let (stated, written) = (GroundSort::Computation, GroundSort::Value);
    assert!(
        found.contains(&row(
            "Valued.Lift",
            Role::Held,
            ground(&valued, "Lift", stated, written)
        )) && found.contains(&row(
            "Valued.Cell",
            Role::Held,
            ground(&valued, "Cell", stated, written)
        )),
        "a value type at a `Type[-]` sort is refused at the member: {found:?}"
    );
    let computed = format!(
        include_str!(
            "models/unformatted/a-computation-sort-is-a-family-into-computation-types-3050-computed.gandr"
        ),
        MAYBE = MAYBE,
        plain = plain
    );
    let found = rows(&lower(computed.as_str()));
    assert!(
        found.contains(&row(
            "Computed.Lift",
            Role::Held,
            ground(&computed, "Lift", written, stated)
        )) && found.contains(&row(
            "Computed.Cell",
            Role::Held,
            ground(&computed, "Cell", written, stated)
        )),
        "and a computation type at a `Type` sort: {found:?}"
    );
}

/// A family read at an index that applies an operation reads that call in
/// place, as a written family call does. A later index whose sort reads the
/// call meets the same value, so `q`'s result `m(ext(g, a), wk(g, a))`
/// checks where `wk(g, a)` stands at `t(ext(g, a))`.
#[test]
fn a_family_over_an_applied_index_reads_the_call_in_place_5051()
{
    states_the_written_types(
        include_str!(
            "models/fixtures/a-family-over-an-applied-index-reads-the-call-in-place-5051.gandr"
        ),
        &[("derived", "written")],
    );
}

/// A port that binds a variable is the thunked function from it: `get`'s
/// continuation takes the state, read as the manifest sort, and `lam`'s body
/// takes a value whose type names the field `a` only that variable's sort
/// names, so `a` binds.
#[test]
fn a_binding_port_is_the_function_from_its_variables_765()
{
    states_the_written_types(
        include_str!("models/fixtures/a-binding-port-is-the-function-from-its-variables-765.gandr"),
        &[("state", "stated"), ("typed", "written")],
    );
}

/// A theory's `oper x : Model(T)` is a field holding `Model(T)`'s own record.
#[test]
fn a_nesting_model_type_bundles_the_inner_one()
{
    states_the_written_types(
        include_str!("models/fixtures/a-nesting-model-type-bundles-the-inner-one.gandr"),
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

/// `Model(Toggle) with sort T = Integer` is the record of the toggle's
/// operations with its carrier read as `Integer`: the sort is no field, so no
/// field binds and the record is keyed by the operations.
#[test]
fn a_manifest_model_type_writes_its_sort_as_its_type()
{
    states_the_written_types(
        include_str!("models/fixtures/a-manifest-model-type-writes-its-sort-as-its-type.gandr"),
        &[("derived", "written")],
    );
}

/// A manifest sort read inside the record stands under the fields that bind
/// before it: `x` is raised past the carrier `A` binds, as the written
/// dependent record reads it. Two sorts fixed in a chain leave neither a
/// field.
#[test]
fn a_manifest_sort_reads_past_the_links_before_it()
{
    states_the_written_types(
        include_str!("models/fixtures/a-manifest-sort-reads-past-the-links-before-it.gandr"),
        &[("derived", "written"), ("both", "bothWritten")],
    );
}

/// #2246: a model type is recorded as the source writes it, the theory's name
/// and each sort it fixes beside the type it fixes it to, in the order
/// written, so a printer spells `Model(T) with sort C = A` rather than the
/// record it lowers to.
#[test]
fn a_written_model_type_is_recorded_as_written_2246()
{
    let source =
        include_str!("models/fixtures/a-written-model-type-is-recorded-as-written-2246.gandr");
    let lowered = lower(source);
    let written = |declaration: &str| {
        let declared = declared_type_of(&lowered, declaration, Role::Declared);
        lowered
            .module
            .origins()
            .models()
            .iter()
            .find(|&&(ty, _)| ty == declared)
            .map(|&(_, ref model)| model.clone())
    };
    let plain = written("plain").expect("`plain`'s type is recorded as written");
    assert_eq!(
        (plain.theory.as_ref(), plain.sorts.as_slice()),
        ("Pair", [].as_slice()),
        "a model type fixing nothing records its theory alone"
    );
    let fixed = written("fixed").expect("`fixed`'s type is recorded as written");
    let sorts: Vec<(&str, CertificateEquality)> = fixed
        .sorts
        .iter()
        .zip(["integer", "empty"])
        .map(|(&(ref sort, carrier), stated)| {
            let stated = declared_type_of(&lowered, stated, Role::Declared);
            (
                sort.as_ref(),
                equal_type_syntax(&lowered.arena, carrier, stated),
            )
        })
        .collect();
    assert_eq!(
        (fixed.theory.as_ref(), sorts.as_slice()),
        (
            "Pair",
            [
                ("B", CertificateEquality::Equal),
                ("A", CertificateEquality::Equal)
            ]
            .as_slice()
        ),
        "a manifest model type records each sort it fixes at its type, in the order written"
    );
}

/// An operation is selected off a model binder (#2246): `m.incr` for `m :
/// Model(Counter)` is the operation `m`'s record holds, at its type with the
/// carrier read as `m`'s, whether the type leaves the carrier a field, so the
/// record nests, or fixes it, so the record is keyed by the operations. A
/// count of `m` steps through `m`'s operations and another counter's count
/// does not; a sort the type fixes is no member a computation reads, and a
/// name the theory lacks is refused naming it.
#[test]
fn an_operation_is_selected_off_a_model_binder_2246()
{
    // The refusal a case expects, built from the source it lowers.
    type Expected<'case> = &'case dyn Fn(&str) -> LoweringRefusal<'static>;

    let counter = include_str!(
        "models/fixtures/a-model-binder-s-carrier-is-its-projected-sort-2131-counter.gandr"
    );
    let stepped = |model: &str, counted: &str| {
        let source = format!(
            include_str!(
                "models/unformatted/an-operation-is-selected-off-a-model-binder-2246.gandr"
            ),
            counted = counted,
            counter = counter,
            model = model
        );
        let mut lowered = lower(source.as_str());
        let step = super::declaration(&lowered, "step", Role::Declared).constant();
        verdicts(&mut lowered)
            .into_iter()
            .find(|&(constant, _)| constant == step)
            .map(|(_, judgement)| judgement)
    };
    for (model, why) in [
        ("Model(Counter)", "its carrier a field"),
        ("Model(Counter) with sort C = Integer", "its carrier fixed"),
    ] {
        assert_eq!(
            stepped(model, "m"),
            Some(Judgement::Checked),
            "a count of `m` steps through `m`'s operations, {why}"
        );
    }
    assert_eq!(
        stepped("Model(Counter)", "n"),
        Some(Judgement::Mismatched),
        "another counter's count is no count of `m`"
    );

    let cases: [(&str, &str, Expected<'_>, &str); 2] = [
        (
            "Model(Counter) with sort C = Integer",
            "C",
            &|source| LoweringRefusal::OutOfFragment {
                span: span_of(source, "m.C", 0_usize),
                form: FormName::from(NamedKind("projection_expression")),
                sort: FragmentSort::Value,
                boundary: FragmentBoundary::WrongSort,
            },
            "a sort the type fixes is no member a value reads",
        ),
        (
            "Model(Counter)",
            "nothing",
            &|source| LoweringRefusal::UnknownMember {
                span: span_of(source, "nothing", 0_usize),
                module: name("m"),
                member: name("nothing"),
            },
            "a name the theory lacks is refused naming it",
        ),
    ];
    for (model, member, refusal, why) in cases {
        let source = format!(
            "{counter}def selected(m : {model}) -> -F Integer {{ let c = m.{member} ; 0 }}\n"
        );
        let found: Vec<_> = rows(&lower(source.as_str()))
            .into_iter()
            .filter(|found| found.0 == "selected")
            .collect();
        assert_eq!(
            found,
            [row(
                "selected",
                Role::Declared,
                Amounts::Refused(refusal(&source))
            )],
            "{why}"
        );
    }
}

/// A member reads off a `let` binder stated at a model type as off a parameter
/// of that type (#4827), its carrier a field or fixed: the binder records the
/// type written beside it.
#[test]
fn a_member_reads_off_a_let_binder_at_a_model_type_4827()
{
    let seeded = include_str!(
        "models/fixtures/a-member-reads-off-a-let-binder-at-a-model-type-4827-seeded.gandr"
    );
    for (model, why) in [
        ("Model(Seeded)", "its carrier a field"),
        ("Model(Seeded) with sort T = Integer", "its carrier fixed"),
    ] {
        let source = format!(
            include_str!(
                "models/unformatted/a-member-reads-off-a-let-binder-at-a-model-type-4827.gandr"
            ),
            model = model,
            seeded = seeded
        );
        let mut lowered = lower(source.as_str());
        let read_off = super::declaration(&lowered, "readOff", Role::Declared).constant();
        assert_eq!(
            verdicts(&mut lowered)
                .into_iter()
                .find(|&(constant, _)| constant == read_off)
                .map(|(_, judgement)| judgement),
            Some(Judgement::Checked),
            "a member reads off a `let` binder at `{model}`, {why}"
        );
    }
}

/// An operation selected off a model binder calls in place (#4818): `m.read(z)`
/// reads as `let r = m.read ; r(z)` does, whether the type leaves the carrier
/// a field or fixes it, and the operation reads only `m`'s carrier. A member
/// that is no operation is called at no function.
#[test]
fn an_operation_selected_off_a_model_binder_calls_in_place_4818()
{
    let counter = include_str!(
        "models/fixtures/an-operation-selected-off-a-model-binder-calls-in-place-4818-counter.gandr"
    );
    let called = |model: &str, call: &str| {
        let source = format!(
            include_str!(
                "models/unformatted/an-operation-selected-off-a-model-binder-calls-in-place-4818.gandr"
            ),
            call = call,
            counter = counter,
            model = model
        );
        let mut lowered = lower(source.as_str());
        let call = super::declaration(&lowered, "call", Role::Declared).constant();
        verdicts(&mut lowered)
            .into_iter()
            .find(|&(constant, _)| constant == call)
            .map(|(_, judgement)| judgement)
    };
    for (model, why) in [
        ("Model(Counter)", "its carrier a field"),
        ("Model(Counter) with sort C = Integer", "its carrier fixed"),
    ] {
        assert_eq!(
            called(model, "m.read(m.zero)"),
            Some(Judgement::Checked),
            "`m`'s reader called at `m`'s zero, {why}"
        );
    }
    assert_eq!(
        called("Model(Counter)", "m.read(n.zero)"),
        Some(Judgement::Mismatched),
        "another counter's zero is no count of `m`"
    );
    assert_eq!(
        called("Model(Counter)", "m.zero(m.zero)"),
        Some(Judgement::Refused),
        "a member that is no operation is called at no function"
    );
}

/// A manifest sort names an unindexed sort of the theory, once: another name
/// is no member of it, an indexed sort is no type to fix, a sort fixed twice
/// is defined twice, and an operand that is no `sort x = A` fixes nothing.
#[test]
fn a_manifest_sort_the_theory_cannot_fix_is_refused()
{
    // The refusal a case expects, built from the source it lowers.
    type Expected<'case> = &'case dyn Fn(&str) -> LoweringRefusal<'static>;
    let theories = include_str!(
        "models/unformatted/a-manifest-sort-the-theory-cannot-fix-is-refused-theories.gandr"
    );
    // The one byte opening the `nth` appearance of `needle`: a sort's name.
    let opening = |source: &str, needle: &str, nth: usize| {
        let span = span_of(source, needle, nth);
        super::ByteSpan::new(
            span.start(),
            super::ByteOffset::from(usize::from(span.start()).saturating_add(1)),
        )
        .expect("the span is ordered")
    };
    let cases: [(&str, Expected<'_>, &str); 4] = [
        (
            "Model(Toggle) with sort Nope = Integer",
            &|source| LoweringRefusal::UnknownMember {
                span: span_of(source, "Nope", 0_usize),
                module: name("Toggle"),
                member: name("Nope"),
            },
            "a name that is no sort of the theory",
        ),
        (
            "Model(Graph) with sort E = Integer",
            &|source| LoweringRefusal::UnreadAscription {
                span: opening(source, "E = ", 0_usize),
                name: name("E"),
                form: AscriptionForm::Parameterized,
            },
            "an indexed sort",
        ),
        (
            "Model(Toggle) with sort T = Integer with sort T = Integer",
            &|source| LoweringRefusal::DuplicateDefinition {
                span: opening(source, "T = ", 1_usize),
                name: name("T"),
                first: opening(source, "T = ", 0_usize),
            },
            "a sort fixed twice",
        ),
        (
            "Model(Toggle) with Integer",
            &|source| LoweringRefusal::MalformedForm {
                span: span_of(source, "Integer", 0_usize),
                form: FormName::from(NamedKind("manifest_type")),
                fault: FormFault::ExtraOperand,
            },
            "an operand that is no binding",
        ),
    ];
    for (written, refusal, why) in cases {
        let source = format!("{theories}def m : {written} ;\n");
        let declared: Vec<_> = rows(&lower(source.as_str()))
            .into_iter()
            .filter(|declared| declared.0 == "m")
            .collect();
        assert_eq!(
            declared,
            [row("m", Role::Declared, Amounts::Refused(refusal(&source)))],
            "{why}"
        );
    }
}

/// Manifest sorts close `Model` alone: after any other head the application
/// refuses the first sort, and a `with` after no application is misplaced.
#[test]
fn a_manifest_sort_after_another_head_is_refused()
{
    let source = "def m : List(Integer) with sort T = Integer ;";
    assert_eq!(
        rows(&lower(source)),
        [row(
            "m",
            Role::Declared,
            Amounts::Refused(LoweringRefusal::MalformedForm {
                span: span_of(source, "T", 0_usize),
                form: FormName::from(NamedKind("type_application")),
                fault: FormFault::MisplacedTile,
            })
        )],
        "a head other than `Model`"
    );
    let source = "def m : Integer with sort T = Integer ;";
    assert_eq!(
        rows(&lower(source)),
        [row(
            "m",
            Role::Declared,
            Amounts::Refused(LoweringRefusal::MalformedForm {
                span: span_of(source, "with", 0_usize),
                form: FormName::from(NamedKind("manifest_type")),
                fault: FormFault::MisplacedTile,
            })
        )],
        "no application"
    );
}

/// A counter that starts, steps and reads, and a module giving it on the
/// integers, ascribed transparently.
const COUNTER: &str = include_str!("models/unformatted/counter.gandr");

/// A module packed at its theory's models is the record of its members in
/// signature order, nested as the record nests its fields: the code of its
/// carrier beside its start, its step and its reading. The kernel checks it
/// at `Model(Counter)`.
#[test]
fn a_manifest_module_packs_as_the_record_of_its_members()
{
    let source = format!(
        include_str!(
            "models/unformatted/a-manifest-module-packs-as-the-record-of-its-members.gandr"
        ),
        COUNTER = COUNTER
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
        include_str!("models/unformatted/a-pack-of-a-sealed-sort-is-refused.gandr"),
        COUNTER.replace("module Open :", "module Open :>")
    );
    let found = rows(&lower(source.as_str()));
    let refused = Amounts::Refused(LoweringRefusal::OutOfFragment {
        span: span_of(source.as_str(), "pack Open at Model(Counter)", 0_usize),
        form: FormName::from(NamedKind("pack_model_expression")),
        sort: FragmentSort::Value,
        boundary: FragmentBoundary::Unadmitted(gandr_surface_lowering::Unbuilt::PackModel),
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
        include_str!("models/unformatted/a-pack-of-no-module-is-refused.gandr"),
        COUNTER = COUNTER
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

/// #4485: a module's name read as a value is its model, the record `pack`
/// builds at the model type its header ascribes, as a definition's body and
/// as an argument, and both check.
#[test]
fn a_module_named_where_a_value_is_read_is_its_model_4485()
{
    // `Open` names a constructor the prelude declares, which answers before a
    // module does, so the module takes a name nothing else answers.
    let source = format!(
        include_str!(
            "models/unformatted/a-module-named-where-a-value-is-read-is-its-model-4485.gandr"
        ),
        COUNTER.replace("module Open :", "module Opened :")
    );
    let mut lowered = lower(source.as_str());
    let leaves = |root| {
        let mut leaves = Vec::new();
        let mut pending = vec![root];
        while let Some(id) = pending.pop() {
            match lowered.arena.value(id).cloned() {
                Some(Value::Tuple(ref components)) => pending.extend(components.iter().rev()),
                Some(Value::Quote(_)) => leaves.push(None),
                other => leaves.push(other),
            }
        }
        leaves
    };
    assert_eq!(
        leaves(body_of(&lowered, "bare")),
        leaves(body_of(&lowered, "packed")),
        "the name packs as `pack Opened at Model(Counter)` does"
    );
    let checked = ["bare", "passed"]
        .map(|path| super::declaration(&lowered, path, Role::Declared).constant());
    let judgements = verdicts(&mut lowered);
    assert!(
        checked
            .iter()
            .all(|&constant| judgements.contains(&(constant, Judgement::Checked))),
        "the name checks as a body and as an argument: {judgements:?}"
    );
}

/// #4826: a module packed or named where a model type fixing its carrier is
/// asked, a definition's signature or a parameter's type, packs without the
/// carrier the type fixes, and checks there; a module whose carrier is
/// another type is refused at the type it gives.
#[test]
fn a_module_packs_at_a_model_type_fixing_its_sorts_4826()
{
    let source = format!(
        include_str!(
            "models/unformatted/a-module-packs-at-a-model-type-fixing-its-sorts-4826.gandr"
        ),
        COUNTER.replace("module Open :", "module Opened :")
    );
    let mut lowered = lower(source.as_str());
    let carried = |path| {
        let mut pending = vec![body_of(&lowered, path)];
        let mut codes = 0_usize;
        while let Some(id) = pending.pop() {
            match lowered.arena.value(id) {
                Some(&Value::Tuple(ref components)) => pending.extend(components.iter()),
                Some(&Value::Quote(_)) => codes = codes.saturating_add(1),
                _ => {},
            }
        }
        codes
    };
    assert_eq!(
        ["packed", "bare", "whole"].map(carried),
        [0_usize, 0_usize, 1_usize],
        "a pack at the fixed type carries no code of its carrier, and one at the theory's models \
         does"
    );
    let [packed, bare, passed, wrong, whole] = ["packed", "bare", "passed", "wrong", "whole"]
        .map(|path| super::declaration(&lowered, path, Role::Declared).constant());
    let judgements = verdicts(&mut lowered);
    assert!(
        [packed, bare, passed, whole]
            .iter()
            .all(|&constant| judgements.contains(&(constant, Judgement::Checked)))
            && judgements.contains(&(wrong, Judgement::Mismatched)),
        "each pack checks at the type it is asked at, and a carrier of strings does not: \
         {judgements:?}"
    );
}

/// #4485: only a module declared before the name and ascribed a model type
/// is read as a value; any other name stays unresolved.
#[test]
fn a_module_no_model_type_ascribes_is_no_value_4485()
{
    let counter = COUNTER.replace("module Open :", "module Opened :");
    let (theory, module) = counter
        .split_once("module Opened")
        .expect("the counter declares its theory before its module");
    let source = format!(
        include_str!("models/unformatted/a-module-no-model-type-ascribes-is-no-value-4485.gandr"),
        module = module,
        theory = theory
    );
    let found = rows(&lower(source.as_str()));
    for (path, module, at) in [("early", "Opened", 0_usize), ("plain", "Plain", 1_usize)] {
        let refused = Amounts::Refused(LoweringRefusal::UnresolvedName {
            span: span_of(source.as_str(), module, at),
            name: name(module),
        });
        assert!(
            found
                .iter()
                .any(|&(ref written, role, amounts)| written == path
                    && role == Role::Declared
                    && amounts == refused),
            "`{module}` is no value at `{path}`: {found:?}"
        );
    }
}

/// A theory one of whose components is a model of another packs the module
/// giving it with the member module its component names, and the record
/// checks at the outer theory's models.
#[test]
fn a_pack_reads_a_nested_model_from_its_member_module()
{
    let source =
        include_str!("models/fixtures/a-pack-reads-a-nested-model-from-its-member-module.gandr");
    let mut lowered = lower(source);
    let packed = super::declaration(&lowered, "packed", Role::Declared).constant();
    let judgements = verdicts(&mut lowered);
    assert!(
        judgements.contains(&(packed, Judgement::Checked)),
        "the nested record checks at the outer theory's models: {judgements:?}"
    );
}

/// A pack of a module that gives no member a component of the theory names
/// is refused naming that component: an operation, the carrier sort, or the
/// member module of a nested model.
#[test]
fn a_pack_of_a_module_missing_a_component_is_refused_naming_it()
{
    let counter = include_str!(
        "models/fixtures/a-pack-of-a-module-missing-a-component-is-refused-naming-it-counter.gandr"
    );
    let faceted = include_str!(
        "models/fixtures/a-pack-of-a-module-missing-a-component-is-refused-naming-it-faceted.gandr"
    );
    for (theory, module, model, missing) in [
        (
            counter,
            include_str!(
                "models/fixtures/a-pack-of-a-module-missing-a-component-is-refused-naming-it-1.gandr"
            ),
            "Counter",
            "start",
        ),
        (
            counter,
            include_str!(
                "models/fixtures/a-pack-of-a-module-missing-a-component-is-refused-naming-it-2.gandr"
            ),
            "Counter",
            "C",
        ),
        (
            faceted,
            include_str!(
                "models/fixtures/a-pack-of-a-module-missing-a-component-is-refused-naming-it-3.gandr"
            ),
            "Faceted",
            "inner",
        ),
    ] {
        let source = format!(
            include_str!(
                "models/unformatted/a-pack-of-a-module-missing-a-component-is-refused-naming-it-4.gandr"
            ),
            model = model,
            module = module,
            theory = theory
        );
        let found = rows(&lower(source.as_str()));
        let refused = Amounts::Refused(LoweringRefusal::UnknownMember {
            span: span_of(source.as_str(), "Bare", 1_usize),
            module: name("Bare"),
            member: name(missing),
        });
        assert!(
            found
                .iter()
                .any(|&(ref path, role, amounts)| path == "packed"
                    && role == Role::Declared
                    && amounts == refused),
            "a module giving no `{missing}` does not pack: {found:?}"
        );
    }
}

/// A pattern at a theory's models names the fields of the record by the
/// components' names, whatever pairs the record nests: a consumer reads the
/// start, the step and the reading of any counter, and reads a packed one.
#[test]
fn a_pattern_at_a_model_type_splits_its_fields()
{
    let source = format!(
        include_str!("models/unformatted/a-pattern-at-a-model-type-splits-its-fields.gandr"),
        COUNTER = COUNTER
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

/// A group presented by three laws, whose completion derives the inverse of a
/// product.
const GROUP: &str = include_str!("models/unformatted/group.gandr");

/// `rule Grp.invMul` takes nine slots, one for each of the eight rules
/// completion derives on the way to it and then its own, each stating its law
/// over every model of the group with the model's operations and laws read
/// off it, and each proof checks; a later declaration reads the rule through
/// the theory's path.
#[test]
fn a_derived_rule_reads_the_model_it_quantifies_over()
{
    let source = format!(
        include_str!("models/unformatted/a-derived-rule-reads-the-model-it-quantifies-over.gandr"),
        GROUP = GROUP
    );
    let mut lowered = lower(source.as_str());
    let found = rows(&lowered);
    // The theory's forgetting map is derived too, from its block.
    let forgets: BTreeSet<_> = lowered.module.forgets().iter().collect();
    let derived: Vec<_> = found
        .iter()
        .zip(lowered.module.declarations())
        .filter(|&(&(_, role, _), declaration)| {
            role == Role::Derived && !forgets.contains(&declaration.constant())
        })
        .map(|(row, _)| row)
        .collect();
    let paths: Vec<&str> = derived
        .iter()
        .map(|&&(ref path, ..)| path.as_str())
        .collect();
    assert!(
        derived.len() == 9_usize
            && derived
                .iter()
                .all(|&&(_, _, amounts)| amounts == Amounts::Completed),
        "the statement and the lemmas below it each lower to a type and a proof: {found:?}"
    );
    assert_eq!(
        paths.split_last(),
        Some((&"Grp.invMul", &["invMul"; 8][..])),
        "the statement is named as a later declaration reads it, under its theory"
    );
    let judgements = verdicts(&mut lowered);
    assert!(
        judgements
            .iter()
            .all(|&(_, judgement)| matches!(judgement, Judgement::Checked | Judgement::Declared)),
        "every lemma, the statement and its use check: {judgements:?}"
    );
}

#[test]
fn an_empty_derived_rule_side_is_missing_operand_5950()
{
    for (written, empty) in [
        (
            "rule Grp.invMul : inv (mul x y) <=>;",
            "rule Grp.invMul : inv (mul x y) <=>".len(),
        ),
        (
            "rule Grp.invMul : <=> mul (inv y) (inv x);",
            "rule Grp.invMul : ".len(),
        ),
    ] {
        let source = format!("{GROUP}{written}\n");
        let start = source.find(written).expect("the rule is appended");
        let at = start.checked_add(empty).expect("the gap follows the rule");
        assert_eq!(
            rows(&lower(source.as_str())).last(),
            Some(&row(
                "rule",
                Role::Held,
                Amounts::Refused(LoweringRefusal::MalformedForm {
                    span: gap(at),
                    form: FormName::DERIVED_RULE_DECLARATION,
                    fault: FormFault::MissingOperand,
                })
            )),
            "the empty side is refused at its gap"
        );
    }
}

/// A statement the group's completion rewrites to two normal forms is no rule
/// the group derives: commutativity is refused by name, under the rule's own.
#[test]
fn a_rule_the_theory_does_not_derive_is_refused()
{
    let written = "rule Grp.comm : mul x y <=> mul y x;";
    let source = format!("{GROUP}{written}\n");
    let found = rows(&lower(source.as_str()));
    assert_eq!(
        found.last(),
        Some(&row(
            "comm",
            Role::Held,
            Amounts::Refused(LoweringRefusal::UnderivedRule {
                span: span_of(source.as_str(), written, 0_usize),
                rule: name("comm"),
                theory: name("Grp"),
                fault: DeriveFault::Apart,
            })
        )),
        "the two sides normalise apart: {found:?}"
    );
}

/// #4106: the associator of four is a filler the monoid derives, so a model
/// writing a component of its name is refused there, naming the derivation,
/// whether the model stands before the derived rule or after it; a model
/// writing only its rules' witnesses holds no such refusal.
#[test]
fn a_model_writing_a_derived_rule_is_refused_naming_it_4106()
{
    let theory = include_str!(
        "models/fixtures/a-model-writing-a-derived-rule-is-refused-naming-it-4106-theory.gandr"
    );
    let derivation = "rule Mon.assoc4 : mul (mul (mul a b) c) d <=> mul a (mul b (mul c d));";
    let model = |module: &str, extra: &str| {
        format!(
            "module {module} : Model(Mon) with sort M = Integer where {{\n  def e = 0;\n  def mul(x : \
             Integer, y : Integer) -> Integer {{ x }}\n{extra}}}\n"
        )
    };
    let written = "  def assoc4(a : Integer) -> Integer { a }\n";
    let source = format!(
        include_str!(
            "models/unformatted/a-model-writing-a-derived-rule-is-refused-naming-it-4106.gandr"
        ),
        model("Before", written),
        model("After", written),
        model("Only", ""),
        derivation = derivation,
        theory = theory
    );
    let found = rows(&lower(source.as_str()));
    let refused = |occurrence: usize| {
        Amounts::Refused(LoweringRefusal::DerivedComponent {
            span: span_of(source.as_str(), "assoc4", occurrence),
            member: name("assoc4"),
            theory: name("Mon"),
            derivation: span_of(source.as_str(), derivation, 0_usize),
        })
    };
    let amounts = |path: &str| {
        found
            .iter()
            .filter(|&&(ref at, ..)| at == path)
            .map(|&(_, _, amounts)| amounts)
            .collect::<Vec<_>>()
    };
    assert_eq!(
        (amounts("Before.assoc4"), amounts("After.assoc4")),
        (Vec::from([refused(0_usize)]), Vec::from([refused(2_usize)])),
        "each written associator is refused at its name, naming the derivation: {found:?}"
    );
    assert!(
        !found
            .iter()
            .any(|&(ref path, _, amounts)| path.starts_with("Only.")
                && matches!(
                    amounts,
                    Amounts::Refused(LoweringRefusal::DerivedComponent { .. })
                )),
        "a model writing only its rules' witnesses owes the derivation nothing: {found:?}"
    );
}

/// #2333: `include Seven` in a model of a theory including `Pointed` takes
/// `Seven`'s members as the module's own, so the model's reduct at `Pointed`
/// is `Seven` itself: `Pair` exports `Seven`'s `point`, the one constant,
/// beside its own `other`, and a client reads it through `Pair`.
#[test]
fn an_included_model_lends_its_members_2333()
{
    let source = include_str!("models/fixtures/an-included-model-lends-its-members-2333.gandr");
    let mut lowered = lower(source);
    let strata = strata(&lowered);
    let point = |path: &str| {
        strata
            .iter()
            .filter(|stratum| stratum.path == path)
            .flat_map(|stratum| stratum.values.iter())
            .find(|&&(ref component, _)| component == "point")
            .map(|&(_, position)| position)
    };
    assert!(
        point("Seven").is_some() && point("Seven") == point("Pair"),
        "`Pair` exports `Seven`'s own `point`: {strata:?}"
    );
    let judgements = verdicts(&mut lowered);
    assert!(
        !judgements.is_empty()
            && !judgements.iter().any(|&(_, judgement)| {
                matches!(judgement, Judgement::Refused | Judgement::Mismatched)
            }),
        "and the client reading it through `Pair` checks: {judgements:?}"
    );
}

/// #2333: an include names a module; a name no module answers is refused at
/// the include, under the including module.
#[test]
fn an_include_naming_no_module_is_refused_2333()
{
    let source = include_str!("models/fixtures/an-include-naming-no-module-is-refused-2333.gandr");
    let found = rows(&lower(source));
    assert!(
        found.contains(&row(
            "M",
            Role::Held,
            Amounts::Refused(LoweringRefusal::UnresolvedName {
                span: span_of(source, "Nowhere", 0_usize),
                name: name("Nowhere"),
            })
        )),
        "the include names nothing: {found:?}"
    );
}

/// #2333: a member the module writes under a name an include also lends is a
/// second definition of it, refused at the include, where the member it would
/// shadow is named.
#[test]
fn a_member_an_include_also_lends_is_refused_2333()
{
    let source =
        include_str!("models/fixtures/a-member-an-include-also-lends-is-refused-2333.gandr");
    let found = rows(&lower(source));
    assert!(
        found.contains(&row(
            "Pair",
            Role::Held,
            Amounts::Refused(LoweringRefusal::DuplicateDefinition {
                span: span_of(source, "Seven", 1_usize),
                name: name("point"),
                first: span_of(source, "point", 1_usize),
            })
        )),
        "`Pair` writes `point` and includes it: {found:?}"
    );
}

/// #3029: a model's component for an operation its theory marks `@[ inert ]`
/// is read only by another inert component: a model's version read from
/// another's stands, and the name read by its path, by a content member of
/// its own model, or off a model binder is refused at the read.
#[test]
fn an_inert_field_is_read_only_by_another_3029()
{
    let source = include_str!("models/fixtures/an-inert-field-is-read-only-by-another-3029.gandr");
    let found = rows(&lower(source));
    let refused = |path: &str| {
        found
            .iter()
            .find(|&&(ref written, ..)| written == path)
            .map(|&(_, _, amounts)| amounts)
    };
    let read = |member: &'static str, reached: &'static str, written: &str, at: usize| {
        Some(Amounts::Refused(LoweringRefusal::InertRead {
            span: span_of(source, written, at),
            member: name(member),
            reached: name(reached),
        }))
    };
    assert!(
        !matches!(refused("Hello.version"), Some(Amounts::Refused(_))),
        "an inert component reads another: {found:?}"
    );
    assert_eq!(
        refused("Hello.greeting"),
        read("greeting", "name", "name", 2_usize)
    );
    assert_eq!(
        refused("named"),
        read("named", "name", "Hello.name", 0_usize)
    );
    assert_eq!(
        refused("versionOf"),
        read("versionOf", "version", "r.version", 0_usize)
    );
}

/// A unital magma's signature, its two unit laws its rules.
const MAG: &str = include_str!("models/fixtures/mag.gandr");

/// #4143: `Terms(S)` mints one data declaration per theory, before the first
/// declaration asking for it, and it is the data block written by hand: one
/// constructor per operation and the theory's rules its presentation. A
/// monoid's associativity presents no type, so the checker refuses its
/// terms and every declaration asking for them.
#[test]
fn a_theory_s_terms_are_its_operations_over_its_rules_4143()
{
    let askers = include_str!(
        "models/fixtures/a-theory-s-terms-are-its-operations-over-its-rules-4143-askers.gandr"
    );
    let by_hand = include_str!(
        "models/fixtures/a-theory-s-terms-are-its-operations-over-its-rules-4143-by-hand.gandr"
    );
    let source = format!("{MAG}{by_hand}{askers}");
    let mut lowered = lower(source.as_str());
    let found = rows(&lowered);
    let termed: Vec<_> = found
        .iter()
        .filter(|&&(_, role, _)| role == Role::Terms)
        .cloned()
        .collect();
    assert_eq!(
        termed,
        [row("Terms(Mag)", Role::Terms, Amounts::Data)],
        "the three askers share one declaration of the terms: {found:?}"
    );
    let at = |path: &str| found.iter().position(|&(ref written, ..)| written == path);
    assert!(
        at("Terms(Mag)") < at("neutral"),
        "the terms are minted before their first asker: {found:?}"
    );
    let signature = |role: Role| {
        let outcome = lowered
            .module
            .declarations()
            .iter()
            .find(|declaration| {
                declaration.role() == role
                    && (role == Role::Terms || declaration.name().as_ref() == "MagTerms")
            })
            .map(gandr_surface_lowering::LoweredDeclaration::outcome);
        let Some(gandr_surface_lowering::DeclarationOutcome::Data(index)) = outcome
        else {
            panic!("a data declaration in {role:?}: {found:?}");
        };
        let quenchant_shape::shape::Maybe::Present(signature) = lowered.module.data(index)
        else {
            panic!("a data declaration keeps its signature: {index:?}");
        };
        alloc::sync::Arc::clone(signature)
    };
    let (derived, written) = (signature(Role::Terms), signature(Role::Declared));
    let arities = |signature: &gandr_core_term::DataSignature| {
        signature
            .constructors()
            .iter()
            .map(Vec::len)
            .collect::<Vec<_>>()
    };
    assert_eq!(
        (arities(&derived), derived.parameters().len()),
        (vec![0_usize, 2_usize], 0_usize),
        "one constructor per operation, at its arity, and no parameter"
    );
    assert_eq!(
        arities(&derived),
        arities(&written),
        "the derived constructors are the written ones"
    );
    assert_eq!(
        derived.presentation(),
        written.presentation(),
        "the theory's rules present the terms as the written rules present `MagTerms`"
    );
    let judged = verdicts(&mut lowered);
    assert!(
        judged
            .iter()
            .all(|&(_, judgement)| matches!(judgement, Judgement::Checked | Judgement::Declared)),
        "the terms declare and every asker checks: {judged:?}"
    );

    let monoid = format!(
        "{}{askers}",
        MAG.replace(
            include_str!("models/fixtures/a-theory-s-terms-are-its-operations-over-its-rules-4143-monoid.gandr"),
            include_str!("models/fixtures/a-theory-s-terms-are-its-operations-over-its-rules-4143.gandr")
        )
    );
    let mut refused = lower(monoid.as_str());
    let judged = verdicts(&mut refused);
    let termed: Vec<_> = refused
        .module
        .declarations()
        .iter()
        .filter(|declaration| declaration.role() == Role::Terms)
        .map(gandr_surface_lowering::LoweredDeclaration::constant)
        .collect();
    let [terms] = *termed
    else {
        panic!("the monoid's terms are declared once: {judged:?}");
    };
    assert!(
        judged
            .iter()
            .filter(|&&(constant, _)| constant >= terms)
            .all(|&(_, judgement)| judgement == Judgement::Refused),
        "the checker refuses the monoid's terms and every asker: {judged:?}"
    );
}

/// #4143: a theory outside one plain sort, or one stating a law, has no
/// terms: the type asking for them is refused where it is written, naming
/// the issue that would build them, and no declaration of them is minted.
#[test]
fn the_terms_of_a_theory_outside_one_plain_sort_are_refused_4143()
{
    let rows_of = [
        (
            include_str!(
                "models/fixtures/the-terms-of-a-theory-outside-one-plain-sort-are-refused-4143-rows-of.gandr"
            ),
            "paired",
            "Terms(Pair)",
            gandr_surface_lowering::Unbuilt::TermsType,
        ),
        (
            include_str!(
                "models/fixtures/the-terms-of-a-theory-outside-one-plain-sort-are-refused-4143.gandr"
            ),
            "doubled",
            "Terms(Idem)",
            gandr_surface_lowering::Unbuilt::LawTerms,
        ),
    ];
    for (source, asker, written, unbuilt) in rows_of {
        let found = rows(&lower(source));
        assert!(
            found.iter().all(|&(_, role, _)| role != Role::Terms),
            "no terms are minted: {found:?}"
        );
        assert!(
            found.iter().any(|&(ref path, _, amounts)| path == asker
                && amounts
                    == Amounts::Refused(LoweringRefusal::OutOfFragment {
                        span: span_of(source, written, 0_usize),
                        form: FormName::from(NamedKind("type_application")),
                        sort: FragmentSort::ValueType,
                        boundary: FragmentBoundary::Unadmitted(unbuilt),
                    })),
            "`{written}` is refused at the type as {unbuilt:?}: {found:?}"
        );
    }
}
