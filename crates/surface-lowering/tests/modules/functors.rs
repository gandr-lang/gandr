//! Generative functors, lowered: a functor is a template no declaration
//! reaches the kernel from, each application binds an instance whose abstract
//! types are its own, and every way out of that discipline is refused by name.

use gandr_core_term::ValueType;
use gandr_surface_lowering::AscriptionForm;
use gandr_surface_lowering::Container;
use gandr_surface_lowering::DeclarationOutcome;
use gandr_surface_lowering::LoweredStructure;
use gandr_surface_lowering::LoweringRefusal;
use gandr_surface_lowering::Stratum;

use super::Amounts;
use super::Judgement;
use super::Role;
use super::declaration;
use super::declared_type_of;
use super::judged;
use super::lower;
use super::name;
use super::row;
use super::rows;
use super::span_of;
use super::verdicts;

/// A sealed counter seed: an abstract type, a value of it and a step on it.
const SEED: &str = "module Seed :> #{ type T, seed : T, next : +U[ω] (T -> -F T) } {\n  type T = \
                    Integer ;\n  def seed = 0 ;\n  def next = thunk { fn (n) { return n } } ;\n}\n";

/// The counter functor: over any seed, a sealed seed of its own type, so an
/// instance is itself an argument.
const COUNTER: &str = "module MkCounter(S : #{ type T, seed : T, next : +U[ω] (T -> -F T) }) :> #{ \
                       type T, seed : T, next : +U[ω] (T -> -F T) } {\n  type T = S.T ;\n  def \
                       seed = S.seed ;\n  def next = S.next ;\n}\n";

/// The counter applied twice to the seed, each instance used at its own type.
const PAIR: &str = "module A = MkCounter(Seed) ;\nmodule B = MkCounter(Seed) ;\ndef a : A.T ;\ndef \
                    a = A.seed ;\ndef b : B.T ;\ndef b = B.seed ;\n";

/// The rows the seed, the counter and [`PAIR`] lower to, in admission order.
///
/// # Specification
/// trivial.
fn pair_rows() -> Vec<(String, Role, Amounts<'static>)>
{
    let mut expected = Vec::from([
        row("Seed.T", Role::Abstract, Amounts::Abstract),
        row("Seed.seed", Role::Declared, Amounts::Completed),
        row("Seed.next", Role::Declared, Amounts::Completed),
    ]);
    for instance in ["A", "B"] {
        expected.extend([
            row(format!("{instance}.T"), Role::Witness, Amounts::Completed),
            row(
                format!("{instance}.seed"),
                Role::Witness,
                Amounts::Completed,
            ),
            row(
                format!("{instance}.next"),
                Role::Witness,
                Amounts::Completed,
            ),
            row(format!("{instance}.T"), Role::Abstract, Amounts::Abstract),
            row(
                format!("{instance}.seed"),
                Role::Declared,
                Amounts::Completed,
            ),
            row(
                format!("{instance}.next"),
                Role::Declared,
                Amounts::Completed,
            ),
        ]);
    }
    expected.extend([
        row("a", Role::Declared, Amounts::Completed),
        row("b", Role::Declared, Amounts::Completed),
    ]);
    expected
}

#[test]
fn the_classic_functor_pair_checks()
{
    let source = [SEED, COUNTER, PAIR].concat();
    let mut lowered = lower(source.as_str());
    assert_eq!(
        rows(&lowered),
        pair_rows(),
        "each application matches the seed against the parameter, one witness per component, \
         then mints its own image of the body"
    );
    let judgements = verdicts(&mut lowered);
    assert_eq!(judgements.len(), 17_usize, "every declaration is judged");
    assert!(
        judgements
            .iter()
            .all(|&(_, judgement)| matches!(judgement, Judgement::Checked | Judgement::Declared)),
        "and every one checks: {judgements:?}"
    );
}

#[test]
fn two_applications_mint_distinct_atoms()
{
    let source = [
        SEED,
        COUNTER,
        PAIR,
        "def mixed : A.T ;\ndef mixed = B.seed ;\n",
    ]
    .concat();
    let mut lowered = lower(source.as_str());
    let atom = |path: &str| {
        let found = declaration(&lowered, path, Role::Abstract);
        let DeclarationOutcome::Abstract(sealing) = found.outcome()
        else {
            panic!("`{path}` is an abstract type");
        };
        (found.constant(), sealing.sealing)
    };
    let (first, first_site) = atom("A.T");
    let (second, second_site) = atom("B.T");
    assert_ne!(first, second, "each application mints its own atom");
    assert_ne!(
        first_site, second_site,
        "sealed at a site of its own, the application's image"
    );
    for (path, sealed) in [("A.seed", first), ("B.seed", second)] {
        assert_eq!(
            lowered
                .arena
                .value_type(declared_type_of(&lowered, path, Role::Declared)),
            Some(&ValueType::Abstract(sealed)),
            "`{path}` is stated at its own instance's atom"
        );
    }
    let mixed = declaration(&lowered, "mixed", Role::Declared).constant();
    assert!(
        verdicts(&mut lowered).contains(&judged(mixed, Judgement::Mismatched)),
        "so a value of one instance is no value of the other"
    );
}

#[test]
fn a_functor_body_never_reaches_the_kernel()
{
    let unapplied = [SEED, COUNTER].concat();
    assert_eq!(
        rows(&lower(unapplied.as_str())),
        [
            row("Seed.T", Role::Abstract, Amounts::Abstract),
            row("Seed.seed", Role::Declared, Amounts::Completed),
            row("Seed.next", Role::Declared, Amounts::Completed),
        ],
        "a functor no application names yields no declaration"
    );

    let source = [SEED, COUNTER, PAIR].concat();
    let lowered = lower(source.as_str());
    let structures = lowered.module.structures();
    assert!(
        structures
            .iter()
            .any(|structure| matches!(structure.stratum(), Stratum::Functor(_))),
        "the functor's body is a structure of its own stratum"
    );
    for declared in lowered.module.declarations() {
        let stratum = match declared.container() {
            Container::TopLevel(_) => Stratum::Module,
            Container::Module(index) => structures
                .get(usize::from(index))
                .map_or(Stratum::Module, LoweredStructure::stratum),
        };
        assert!(
            matches!(stratum, Stratum::Module | Stratum::Instance(_)),
            "`{}` is declared by a module or an instance, never by the template",
            declared.name()
        );
    }
}

#[test]
fn an_application_is_bound_before_anything_projects_from_it()
{
    let projected = [
        SEED,
        COUNTER,
        "def direct : Integer ;\ndef direct = MkCounter(Seed).seed ;\ndef typed : \
         MkCounter(Seed).T ;\n",
    ]
    .concat();
    let found = rows(&lower(projected.as_str()));
    for (path, occurrence) in [("direct", 0_usize), ("typed", 1_usize)] {
        assert!(
            found.contains(&row(
                path,
                Role::Declared,
                Amounts::Refused(LoweringRefusal::ProjectionFromApplication {
                    span: span_of(projected.as_str(), "MkCounter(Seed)", occurrence),
                    functor: name("MkCounter"),
                })
            )),
            "`{path}` projects from an application, refused naming the functor: {found:?}"
        );
    }
}

#[test]
fn an_argument_is_matched_against_the_parameter()
{
    let thin = [
        COUNTER,
        "module Thin :> #{ type T, seed : T } { type T = Integer ; def seed = 0 ; }\nmodule A = \
         MkCounter(Thin) ;\n",
    ]
    .concat();
    let found = rows(&lower(thin.as_str()));
    assert!(
        found.iter().any(|&(ref path, _, amounts)| path == "A"
            && amounts
                == Amounts::Refused(LoweringRefusal::UnknownMember {
                    span: span_of(thin.as_str(), "Thin", 1_usize),
                    module: name("Thin"),
                    member: name("next"),
                })),
        "an argument missing a component refuses the binding, naming the component: {found:?}"
    );

    let mistyped = [
        COUNTER,
        "module Wrong :> #{ type T, seed : Integer, next : +U[ω] (T -> -F T) } { type T = Integer \
         ; def seed = 0 ; def next = thunk { fn (n) { return n } } ; }\nmodule A = \
         MkCounter(Wrong) ;\n",
    ]
    .concat();
    let mut lowered = lower(mistyped.as_str());
    let witness = declaration(&lowered, "A.seed", Role::Witness).constant();
    assert!(
        verdicts(&mut lowered).contains(&judged(witness, Judgement::Mismatched)),
        "a component at another type than the parameter states is refused at its witness"
    );

    let misspelled = [SEED, COUNTER, "module A = MkTally(Seed) ;\n"].concat();
    assert!(
        rows(&lower(misspelled.as_str())).contains(&row(
            "A",
            Role::Held,
            Amounts::Refused(LoweringRefusal::NotAFunctor {
                span: span_of(misspelled.as_str(), "MkTally", 0_usize),
                name: name("MkTally"),
            })
        )),
        "a head naming no functor is refused by its name"
    );
}

#[test]
fn a_parameter_reads_only_types_and_values()
{
    for (component, form) in [
        ("type F : (a : Type) => Type", AscriptionForm::Kinded),
        ("type F : Type -> Type", AscriptionForm::Kinded),
        ("type F(a : Type) = a", AscriptionForm::Parameterized),
    ] {
        let source = format!("module Over(S : #{{ {component} }}) {{ def x = 1 ; }}\n");
        let found = rows(&lower(source.as_str()));
        assert!(
            found.contains(&row(
                "Over.S.F",
                Role::Held,
                Amounts::Refused(LoweringRefusal::UnreadAscription {
                    span: span_of(source.as_str(), "F", 0_usize),
                    name: name("F"),
                    form,
                })
            )),
            "a parameter's `{component}` is refused at its name: {found:?}"
        );
    }
}

#[test]
fn an_instance_can_be_an_argument()
{
    let source = [
        SEED,
        COUNTER,
        PAIR,
        "module AA = MkCounter(A) ;\ndef aa : AA.T ;\ndef aa = AA.seed ;\ndef crossed : A.T \
         ;\ndef crossed = AA.seed ;\n",
    ]
    .concat();
    let mut lowered = lower(source.as_str());
    let aa = declaration(&lowered, "aa", Role::Declared).constant();
    let crossed = declaration(&lowered, "crossed", Role::Declared).constant();
    let judgements = verdicts(&mut lowered);
    assert!(
        judgements.contains(&judged(aa, Judgement::Checked)),
        "an instance applied again is a seed like any other: {judgements:?}"
    );
    assert!(
        judgements.contains(&judged(crossed, Judgement::Mismatched)),
        "and the new instance's type is not its argument's"
    );
}

#[test]
fn a_transparent_result_reads_the_argument_through()
{
    let source = [
        SEED,
        "module Keep(S : #{ type T, seed : T }) : #{ type T = S.T, seed : T } { def seed = \
         S.seed ; }\nmodule K = Keep(Seed) ;\nmodule KK = Keep(K) ;\ndef k : Seed.T ;\ndef k = \
         K.seed ;\ndef kk : Seed.T ;\ndef kk = KK.seed ;\n",
    ]
    .concat();
    let mut lowered = lower(source.as_str());
    let k = declaration(&lowered, "k", Role::Declared).constant();
    let kk = declaration(&lowered, "kk", Role::Declared).constant();
    let judgements = verdicts(&mut lowered);
    assert!(
        judgements.contains(&judged(k, Judgement::Checked))
            && judgements.contains(&judged(kk, Judgement::Checked)),
        "a manifest result names the argument's own type, through two applications: \
         {judgements:?}"
    );
}

#[test]
fn a_parameter_is_read_only_inside_its_functor()
{
    let source = [
        SEED,
        COUNTER,
        "def outside : Integer ;\ndef outside = S.seed ;\n",
    ]
    .concat();
    let found = rows(&lower(source.as_str()));
    assert!(
        found
            .iter()
            .any(|&(ref path, _, amounts)| path == "outside"
                && matches!(amounts, Amounts::Refused(_))),
        "the parameter's name binds nothing outside its functor: {found:?}"
    );

    let missing = [
        SEED,
        "module Peek(S : #{ type T, seed : T }) { def wrong = S.missing ; }\nmodule P = \
         Peek(Seed) ;\n",
    ]
    .concat();
    let found = rows(&lower(missing.as_str()));
    assert!(
        found.iter().any(|&(_, _, amounts)| amounts
            == Amounts::Refused(LoweringRefusal::UnknownMember {
                span: span_of(missing.as_str(), "missing", 0_usize),
                module: name("S"),
                member: name("missing"),
            })),
        "and inside it reads only what the parameter states: {found:?}"
    );
}
