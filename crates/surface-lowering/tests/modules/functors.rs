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
    for instance in ["A", "B"] {
        assert!(
            !structures
                .iter()
                .any(|structure| structure.path() == [name(instance), name("S")]),
            "`{instance}` images the template's nested modules, never the parameter it was \
             applied at"
        );
    }
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
fn a_type_member_never_reads_its_parameter_s_value()
{
    let pinned = "module Pinned(S : #{ type T, z : T }) :> #{ type P, q : P } {\n  type P = \
                  Path(S.T, S.z, S.z);\n  def q = here(S.z);\n}\n";
    let found = rows(&lower(pinned));
    let phase = LoweringRefusal::PhaseDependence {
        span: span_of(pinned, "S.z", 0_usize),
        member: name("P"),
        reached: name("z"),
    };
    assert!(
        found.iter().any(
            |&(_, role, ref amounts)| role == Role::Held && *amounts == Amounts::Refused(phase)
        ),
        "a type member reading the parameter's value is refused at the value: {found:?}"
    );
    let squared = [
        SEED,
        "module Square(S : #{ type T, seed : T }) :> #{ type U, w : U } {\n  type U = S.T * \
         S.T;\n  def w = (S.seed, S.seed);\n}\nmodule Squared = Square(Seed) ;\n",
    ]
    .concat();
    let mut lowered = lower(squared.as_str());
    let applied = rows(&lowered);
    assert!(
        applied
            .iter()
            .all(|&(_, _, ref amounts)| !matches!(*amounts, Amounts::Refused(_))),
        "one reading only the parameter's type is read: {applied:?}"
    );
    assert!(
        verdicts(&mut lowered)
            .iter()
            .all(|&(_, judgement)| matches!(judgement, Judgement::Checked | Judgement::Declared)),
        "and its application checks"
    );
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

/// A magma and a model of it, the integers under multiplication.
const MAGMA: &str = "theory Mag {\n  sort M : Type;\n  oper mul : (x : M, y : M) --> M;\n}\nmodule \
                     Times : Model(Mag) {\n  type M = Integer;\n  def mul(a : Integer, b : \
                     Integer) -> -F Integer { return a * b }\n}\n";

/// Squaring in any magma: the parameter's signature is the one the magma
/// derives.
const SQUARE: &str = "module Square(S : Model(Mag)) {\n  def square(x : S.M) -> -F S.M { become \
                      S.mul(x, x) }\n}\n";

#[test]
fn a_functor_over_a_model_applies_to_one_1226()
{
    let source = [MAGMA, SQUARE, "module Squared = Square(Times) ;\n"].concat();
    let mut lowered = lower(source.as_str());
    let found = rows(&lowered);
    for witness in ["Squared.M", "Squared.mul"] {
        assert!(
            found.contains(&row(witness, Role::Witness, Amounts::Completed)),
            "the model is matched against the derived parameter at `{witness}`: {found:?}"
        );
    }
    let judgements = verdicts(&mut lowered);
    assert!(
        judgements
            .iter()
            .all(|&(_, judgement)| matches!(judgement, Judgement::Checked | Judgement::Declared)),
        "and the application checks: {judgements:?}"
    );

    let halved = [
        MAGMA,
        SQUARE,
        "module Halves {\n  type M = Integer;\n  def mul(a : Integer) -> -F Integer { return a \
         }\n}\nmodule Squared = Square(Halves) ;\n",
    ]
    .concat();
    let mut lowered = lower(halved.as_str());
    let witness = declaration(&lowered, "Squared.mul", Role::Witness).constant();
    assert!(
        verdicts(&mut lowered).contains(&judged(witness, Judgement::Mismatched)),
        "an operation at another type than the theory derives is refused at its witness"
    );
}

/// A semigroup, its law over its own multiplication.
const SEMI: &str = "theory Semi {\n  sort M : Type;\n  oper mul : (x : M, y : M) --> M;\n  rule \
                    assoc : mul(mul(x, y), z) ==> mul(x, mul(y, z));\n}\n";

/// Associativity turned round at any model, read off the parameter's law.
const REASSOCIATING: &str = "module Reassociating(S : Model(Semi)) {\n  def reassoc(x : S.M, y : \
                             S.M, z : S.M) -> -F Path(S.M, S.mul(x, S.mul(y, z)), \
                             S.mul(S.mul(x, y), z)) { back(S.assoc(x, y, z)) }\n}\n";

/// The one-point semigroup, its law by computation.
const ONE_POINT: &str = "module OnePoint : Model(Semi) {\n  type M = Unit;\n  def mul(a : Unit, \
                         b : Unit) -> -F Unit { unit }\n  def assoc(x : Unit, y : Unit, z : \
                         Unit) -> -F Path(Unit, mul(mul(x, y), z), mul(x, mul(y, z))) { \
                         here(unit) }\n}\n";

#[test]
fn a_functor_reads_the_laws_of_its_model_parameter_1764()
{
    let source = [
        SEMI,
        REASSOCIATING,
        ONE_POINT,
        "module Turned = Reassociating(OnePoint) ;\n",
    ]
    .concat();
    let mut lowered = lower(source.as_str());
    let found = rows(&lowered);
    assert!(
        found.contains(&row("Turned.assoc", Role::Witness, Amounts::Completed)),
        "the argument's law is matched against the law the parameter states: {found:?}"
    );
    let judgements = verdicts(&mut lowered);
    assert!(
        judgements
            .iter()
            .all(|&(_, judgement)| matches!(judgement, Judgement::Checked | Judgement::Declared)),
        "and the body reading the law checks at the instance: {judgements:?}"
    );
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

    let deeper = [
        SEED,
        "module Dig(S : #{ type T, seed : T }) { def wrong = S.seed.inner ; def typed : S.T.U \
         ; }\nmodule D = Dig(Seed) ;\n",
    ]
    .concat();
    let found = rows(&lower(deeper.as_str()));
    for member in ["seed", "T"] {
        assert!(
            found.iter().any(|&(_, _, amounts)| matches!(
                amounts,
                Amounts::Refused(LoweringRefusal::UnknownMember { module, member: selected, .. })
                    if module == name("S") && selected == name(member)
            )),
            "a parameter states no module, so a path past `S.{member}` is refused at that \
             link: {found:?}"
        );
    }

    let reached = [
        SEED,
        "module Reach(S : #{ type T, seed : T }) { def other = Seed.next ; }\nmodule R = \
         Reach(Seed) ;\n",
    ]
    .concat();
    let found = rows(&lower(reached.as_str()));
    assert!(
        !found
            .iter()
            .any(|&(_, _, amounts)| matches!(amounts, Amounts::Refused(_))),
        "only the parameter's own name reads through the parameter; another module is read \
         as itself: {found:?}"
    );
}

#[test]
fn an_argument_naming_a_functor_is_unresolved()
{
    let source = [SEED, COUNTER, "module A = MkCounter(MkCounter) ;\n"].concat();
    let found = rows(&lower(source.as_str()));
    assert!(
        found.iter().any(|&(ref path, _, amounts)| path == "A"
            && amounts
                == Amounts::Refused(LoweringRefusal::UnresolvedName {
                    span: span_of(source.as_str(), "MkCounter", 2_usize),
                    name: name("MkCounter"),
                })),
        "a functor is no module, so an argument naming one names nothing: {found:?}"
    );
}

#[test]
fn a_dotted_argument_reads_the_nested_module_it_names()
{
    let source = [
        COUNTER,
        "module Outer { module Other { def seed = 1 ; } module Seed :> #{ type T, seed : T, next \
         : +U[ω] (T -> -F T) } { type T = Integer ; def seed = 0 ; def next = thunk { fn (n) { \
         return n } } ; } }\nmodule A = MkCounter(Outer.Seed) ;\nmodule B = \
         MkCounter(Outer.Nope) ;\n",
    ]
    .concat();
    let found = rows(&lower(source.as_str()));
    assert!(
        found.contains(&row("A.seed", Role::Witness, Amounts::Completed)),
        "`Outer.Seed` binds the nested module of that name, not its sibling before it: \
         {found:?}"
    );
    assert!(
        found.iter().any(|&(ref path, _, amounts)| path == "B"
            && amounts
                == Amounts::Refused(LoweringRefusal::UnknownMember {
                    span: span_of(source.as_str(), "Nope", 0_usize),
                    module: name("Outer"),
                    member: name("Nope"),
                })),
        "and a segment naming no nested module is refused at that segment: {found:?}"
    );
}

#[test]
fn a_type_component_binds_the_argument_type_of_its_own_name()
{
    let source = [
        COUNTER,
        "module Two :> #{ type U, type T, seed : T, next : +U[ω] (T -> -F T) } { type U = String \
         ; type T = Integer ; def seed = 0 ; def next = thunk { fn (n) { return n } } ; }\nmodule \
         A = MkCounter(Two) ;\n",
    ]
    .concat();
    let mut lowered = lower(source.as_str());
    let judgements = verdicts(&mut lowered);
    assert!(
        judgements
            .iter()
            .all(|&(_, judgement)| matches!(judgement, Judgement::Checked | Judgement::Declared)),
        "the parameter's `T` is the argument's `T`, not the type exported before it: \
         {judgements:?}"
    );
}

#[test]
fn a_manifest_parameter_component_reads_the_arguments_type()
{
    let source = "module Plain { type T = Integer ; def seed = 1 ; }\nmodule Over(S : #{ type T = \
                  Integer, seed : T }) { def get = S.seed ; }\nmodule O = Over(Plain) ;\ndef g : \
                  Integer ;\ndef g = O.get ;\n";
    let mut lowered = lower(source);
    let g = declaration(&lowered, "g", Role::Declared).constant();
    let judgements = verdicts(&mut lowered);
    assert!(
        judgements.contains(&judged(g, Judgement::Checked))
            && judgements.iter().all(|&(_, judgement)| matches!(
                judgement,
                Judgement::Checked | Judgement::Synthesised | Judgement::Declared
            )),
        "a manifest component `T = Integer` reads the argument's `T`, so the seed is an \
         integer: {judgements:?}"
    );
}

#[test]
fn an_application_copies_the_modules_nested_in_its_body()
{
    let source = "module Plain { type T = Integer ; def seed = 1 ; }\nmodule Over(S : #{ type T, \
                  seed : T }) { module inner { module deeper { def kept = S.seed ; } } }\nmodule \
                  O = Over(Plain) ;\ndef g : Plain.T ;\ndef g = O.inner.deeper.kept ;\n";
    let mut lowered = lower(source);
    let g = declaration(&lowered, "g", Role::Declared).constant();
    let judgements = verdicts(&mut lowered);
    assert!(
        judgements.contains(&judged(g, Judgement::Checked)),
        "the instance's nested modules project, two deep, to the argument's seed: \
         {judgements:?}"
    );
}

#[test]
fn an_application_named_twice_is_refused_naming_the_first()
{
    let source = "module Plain { type T = Integer ; def seed = 1 ; }\nmodule Over(S : #{ type T, \
                  seed : T }) { def get = S.seed ; }\nmodule O = Over(Plain) ;\nmodule O = \
                  Over(Plain) ;\n";
    let found = rows(&lower(source));
    assert!(
        found.iter().any(|&(_, _, amounts)| amounts
            == Amounts::Refused(LoweringRefusal::DuplicateDefinition {
                span: span_of(source, "O", 3_usize),
                name: name("O"),
                first: span_of(source, "O", 1_usize),
            })),
        "the second application of `O` is refused at its name: {found:?}"
    );
}
